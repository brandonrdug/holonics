use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::{blob, read_blob};
use crate::native_ecology::constitutive_fibre::{
    GeneratorNeighborhoodRest, NormalWaveRelationRest,
};
use std::io::{Read, Take, Write};
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct ContactHeader {
    id: u64,
    member: usize,
}
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    epoch: u64,
    neighborhood_base: u64,
    next_contact: u64,
    active_member: Option<usize>,
    contacts: Vec<ContactHeader>,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super) struct CoupledRestData {
    header: Header,
    neighborhood: GeneratorNeighborhoodRest,
    family: NormalWaveFamilyRest,
    relations: BTreeMap<u64, NormalWaveRelationRest>,
}
impl CoupledRestData {
    pub(in super::super) fn members(&self)->usize{self.neighborhood.members()}
    pub(in super::super) fn epoch(&self) -> u64 {
        self.header.epoch
    }
    pub(in super::super) fn passages(&self) -> u64 {
        self.family.passages()
    }
    pub(in super::super) fn validate(
        &self,
        bank: &NormalWaveRest,
    ) -> Result<(), ConstitutiveFibreError> {
        self.neighborhood.validate()?;
        self.family.validate()?;
        let n = bank.material().roots();
        let delta = self
            .header
            .epoch
            .checked_sub(bank.normal_bank_epoch())
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.family.roots() != n
            || self.family.grain() != bank.material().grain()
            || self.family.source_transport() != bank.transport()
            || self.header.next_contact == 0
            || self.family.passages() != delta
            || self.family.current_epoch()? != self.header.epoch
            || self.header.neighborhood_base.checked_add(delta) != Some(self.neighborhood.epoch())
            || self.header.contacts.len() != self.relations.len()
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        for law in self.neighborhood.laws() {
            if law.target_width() != 2 * n
                || !matches!(law.source_chart(),ConstitutiveSourceChart::BilinearContact{source_complex,..} if source_complex==3*n)
            {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        match (
            self.header.active_member,
            self.family.last_relation(),
            delta,
        ) {
            (None, None, 0) => {}
            (Some(j), Some(last), d) if d > 0 => {
                let law = self
                    .neighborhood
                    .laws()
                    .get(j)
                    .ok_or(ConstitutiveFibreError::Shape)?;
                if last.roots() != n || last.relation_cut() != law.occurrences() {
                    return Err(ConstitutiveFibreError::Shape);
                }
            }
            _ => return Err(ConstitutiveFibreError::Shape),
        }
        let mut ids = std::collections::BTreeSet::new();
        for c in &self.header.contacts {
            let law = self
                .neighborhood
                .laws()
                .get(c.member)
                .ok_or(ConstitutiveFibreError::Shape)?;
            let relation = self
                .relations
                .get(&c.id)
                .ok_or(ConstitutiveFibreError::Shape)?;
            relation.validate()?;
            if c.id == 0
                || c.id >= self.header.next_contact
                || !ids.insert(c.id)
                || relation.roots() != n
                || relation.relation_cut() != law.occurrences()
            {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        Ok(())
    }
    pub(in super::super) fn write(
        &self,
        out: &mut impl Write,
    ) -> Result<(), ConstitutiveFibreError> {
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        let mut bytes = Vec::new();
        self.neighborhood.write(&mut bytes)?;
        blob(out, &bytes)?;
        bytes.clear();
        self.family.write(&mut bytes)?;
        blob(out, &bytes)?;
        for c in &self.header.contacts {
            bytes.clear();
            self.relations[&c.id].write(&mut bytes)?;
            blob(out, &bytes)?;
        }
        Ok(())
    }
    pub(in super::super) fn read(
        input: &mut Take<impl Read>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let header: Header = serde_json::from_slice(&read_blob(input)?).map_err(invalid)?;
        let bytes = read_blob(input)?;
        let neighborhood =
            GeneratorNeighborhoodRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        let bytes = read_blob(input)?;
        let family = NormalWaveFamilyRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
        if header.contacts.len() as u64 > input.limit() / 8 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut relations = BTreeMap::new();
        for c in &header.contacts {
            let bytes = read_blob(input)?;
            let relation = NormalWaveRelationRest::read(&mut bytes.as_slice(), bytes.len() as u64)?;
            if relations.insert(c.id, relation).is_some() {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        Ok(Self {
            header,
            neighborhood,
            family,
            relations,
        })
    }
}
impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    pub fn rest(&self) -> Result<NormalWaveRest, ConstitutiveFibreError> {
        let mode = &self.continuation;
        let mut contacts = Vec::new();
        let mut relations = BTreeMap::new();
        for (id, b) in &mode.bindings {
            contacts.push(ContactHeader {
                id: *id,
                member: b.member,
            });
            relations.insert(*id, b.relation.rest()?);
        }
        let data = CoupledRestData {
            header: Header {
                epoch: mode.epoch,
                neighborhood_base: mode.neighborhood_base,
                next_contact: mode.next_contact,
                active_member: mode.active_member,
                contacts,
            },
            neighborhood: mode.neighborhood.rest()?,
            family: mode.current.rest()?,
            relations,
        };
        let mut rest = self.rest_normal_bank()?;
        data.validate(&rest)?;
        rest.coupled = Some(Box::new(data));
        Ok(rest)
    }
}
impl NormalWaveRest {
    pub fn remount_coupled<'c>(
        mut self,
        s: &'c ResidentSurface<'c>,
        progress: impl FnMut(u64),
    ) -> Result<ResidentNormalWave<'c, NormalWaveCoupled<'c>>, ConstitutiveFibreError> {
        let data = *self.coupled.take().ok_or(ConstitutiveFibreError::Shape)?;
        data.validate(&self)?;
        let base = self.remount(s, progress)?;
        let neighborhood = data.neighborhood.remount(s)?;
        let mut family = data.family.remount(s)?;
        if let Some(j) = data.header.active_member {
            let receiver = family
                .last_relation()
                .ok_or(ConstitutiveFibreError::Shape)?
                .source_receiver();
            let mut relation =
                neighborhood.read_wave_relation_in_chart(j, base.material.roots, receiver, None)?;
            if let Some(observed) = family.last_relation().and_then(|v| v.observed_next()) {
                relation = relation.read_observed_next(observed)?;
            } else if let Some(contact) = family.last_relation().and_then(|v| v.source_contact()) {
                relation =
                    relation.read_source_contact(neighborhood.generator(j)?, contact.source())?;
                if let Some(row) = contact.source_row() {
                    relation = relation.with_source_row(row);
                }
            }
            family.rebind_decoded_relation(Rc::new(relation))?;
        }
        family.read_receiver()?.require_supported()?;
        let current = Rc::new(family);
        let mut bindings = BTreeMap::new();
        for c in data.header.contacts {
            let relation = neighborhood.read_wave_relation_in_chart(
                c.member,
                base.material.roots,
                data.relations[&c.id].source_receiver(),
                None,
            )?;
            if relation.rest()? != data.relations[&c.id] {
                return Err(invalid(
                    "contact map does not derive from its restored member/condition",
                ));
            }
            bindings.insert(
                c.id,
                Rc::new(CoupledBinding {
                    member: c.member,
                    epoch: data.header.epoch,
                    neighborhood_epoch: neighborhood.epoch(),
                    source: Rc::clone(&current),
                    relation: Rc::new(relation),
                }),
            );
        }
        Ok(base.with_continuation(NormalWaveCoupled {
            neighborhood,
            current,
            epoch: data.header.epoch,
            neighborhood_base: data.header.neighborhood_base,
            next_contact: data.header.next_contact,
            active_member: data.header.active_member,
            bindings,
        }))
    }
}
