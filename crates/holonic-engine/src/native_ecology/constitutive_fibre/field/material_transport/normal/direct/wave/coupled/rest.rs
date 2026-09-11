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
struct PendingHeader {
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
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pending: Vec<PendingHeader>,
}
#[derive(Debug, PartialEq, Eq)]
struct PendingRest {
    member: usize,
    source: NormalWaveFamilyRest,
    produced: NormalWaveFamilyRest,
}
#[derive(Debug, PartialEq, Eq)]
pub(in super::super) struct CoupledRestData {
    header: Header,
    neighborhood: GeneratorNeighborhoodRest,
    family: NormalWaveFamilyRest,
    relations: BTreeMap<u64, NormalWaveRelationRest>,
    pending: BTreeMap<u64, PendingRest>,
}
impl CoupledRestData {
    pub(in super::super) fn members(&self) -> usize {
        self.neighborhood.members()
    }
    pub(in super::super) fn epoch(&self) -> u64 {
        self.header.epoch
    }
    pub(in super::super) fn passages(&self) -> u64 {
        self.family.passages()
    }
    pub(in super::super) fn has_pending(&self) -> bool {
        !self.pending.is_empty()
    }
    pub(in super::super) fn pending_count(&self) -> usize {
        self.pending.len()
    }
    pub(in super::super) fn has_pending_id(&self, id: u64) -> bool {
        self.pending.contains_key(&id)
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
        let mut pending_ids = std::collections::BTreeSet::new();
        if self.header.pending.len() != self.pending.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        for p in &self.header.pending {
            let cut = self
                .pending
                .get(&p.id)
                .ok_or(ConstitutiveFibreError::Shape)?;
            let law = self
                .neighborhood
                .laws()
                .get(p.member)
                .ok_or(ConstitutiveFibreError::Shape)?;
            cut.source.validate()?;
            cut.produced.validate()?;
            if p.id == 0
                || p.id > self.header.epoch
                || !pending_ids.insert(p.id)
                || cut.member != p.member
                || cut.source.roots() != n
                || cut.produced.roots() != n
                || cut.source.grain() != self.family.grain()
                || cut.produced.grain() != self.family.grain()
                || cut.source.source_transport() != self.family.source_transport()
                || cut.produced.source_transport() != self.family.source_transport()
                || cut.source.current_epoch()? != p.id - 1
                || cut.produced.current_epoch()? != p.id
                || p.id <= bank.normal_bank_epoch()
                || cut.produced.last_relation().is_none_or(|r| !r.is_conditional() || r.relation_cut()>law.occurrences() || matches!(law.source_chart(),ConstitutiveSourceChart::BilinearContact{condition_complex,..} if r.condition_components()!=2*condition_complex))
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
        for p in &self.header.pending {
            let cut = self
                .pending
                .get(&p.id)
                .ok_or(ConstitutiveFibreError::Shape)?;
            bytes.clear();
            cut.source.write(&mut bytes)?;
            blob(out, &bytes)?;
            bytes.clear();
            cut.produced.write(&mut bytes)?;
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
        if header.pending.len() as u64 > input.limit()/16 {return Err(ConstitutiveFibreError::Shape);}
        let mut pending = BTreeMap::new();
        for p in &header.pending {
            let source = read_blob(input)?;
            let source = NormalWaveFamilyRest::read(&mut source.as_slice(), source.len() as u64)?;
            let produced = read_blob(input)?;
            let produced =
                NormalWaveFamilyRest::read(&mut produced.as_slice(), produced.len() as u64)?;
            if pending
                .insert(
                    p.id,
                    PendingRest {
                        member: p.member,
                        source,
                        produced,
                    },
                )
                .is_some()
            {
                return Err(invalid("duplicate pending producing cut"));
            }
        }
        Ok(Self {
            header,
            neighborhood,
            family,
            relations,
            pending,
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
        let mut pending_meta = Vec::new();
        let mut pending = BTreeMap::new();
        for (id, cut) in &mode.pending {
            pending_meta.push(PendingHeader {
                id: *id,
                member: cut.member,
            });
            pending.insert(
                *id,
                PendingRest {
                    member: cut.member,
                    source: cut.source.rest()?,
                    produced: cut.produced.rest()?,
                },
            );
        }
        let data = CoupledRestData {
            header: Header {
                epoch: mode.epoch,
                neighborhood_base: mode.neighborhood_base,
                next_contact: mode.next_contact,
                active_member: mode.active_member,
                contacts,
                pending: pending_meta,
            },
            neighborhood: mode.neighborhood.rest()?,
            family: mode.current.rest()?,
            relations,
            pending,
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
        let mut pending = BTreeMap::new();
        for (id, cut) in data.pending {
            let source = cut.source.remount(s)?;
            let stored = cut.produced.remount(s)?;
            let law = stored
                .last_relation_shared()
                .ok_or(ConstitutiveFibreError::Shape)?;
            if law.source_contact().is_some() || law.observed_next().is_some() {
                return Err(invalid("pending producing map is not conditional"));
            }
            let rebuilt = source.read_through(law)?;
            rebuilt.read_receiver()?.require_supported()?;
            if rebuilt.rest()? != stored.rest()? {
                return Err(invalid(
                    "pending produced family does not derive from its source",
                ));
            }
            pending.insert(
                id,
                Rc::new(super::comparison::CoupledProducingCut {
                    member: cut.member,
                    source: Rc::new(source),
                    produced: Rc::new(rebuilt),
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
            pending,
        }))
    }
}

#[cfg(test)]
mod pending_tests {
    use super::*;
    use crate::{embedding_fiber::ResidentReadout,native_ecology::constitutive_fibre::ConditionContactMetric};
    use super::super::super::comparison_tests::{point,current};
    use super::super::super::family::tests::law;
    fn body<'c>(s:&'c ResidentSurface<'c>,p:i64)->ResidentNormalWave<'c,NormalWaveCoupled<'c>>{
        let a=point(s,&[p,0]);let c=point(s,&[2,1]);let h=point(s,&[1,0]);
        let local=ResidentGeneratorNeighborhood::with_shared_condition(vec![law(s,true)],current(&h),ConditionContactMetric::UnitAdmittanceRealification).unwrap();
        ResidentNormalMaterial::found(s,1,1,ResidentGrain(32)).unwrap().into_applied_difference_wave(current(&a),current(&c)).unwrap().with_neighborhood(local).unwrap()
    }
    #[test]
    #[ignore="requires CUDA; equal projected endpoints do not validate a substituted producing source"]
    fn pending_comparison_rest_rejects_equal_endpoint_source_substitution(){
        let ro=ResidentReadout::new().unwrap();let s=ResidentSurface::on(&ro).unwrap();let mut wave=body(&s,1);
        let contact=wave.admit_contact(0).unwrap();let pred=wave.predict_contact(&contact).unwrap();
        let mut other=body(&s,5);let source=other.current().rest().unwrap();let contact=other.admit_contact(0).unwrap();other.advance_contact(&contact).unwrap();
        assert_eq!(wave.current().read_receiver().unwrap().inspect().unwrap().projected_joint,other.current().read_receiver().unwrap().inspect().unwrap().projected_joint);
        let mut rest=wave.rest().unwrap();let mut valid=Vec::new();rest.write(&mut valid).unwrap();
        let magic=b"HOLONIC-NORMAL-WAVE";
        // The normal-wave prefix is checked by the actual reader; change only its version octet.
        assert!(valid.starts_with(magic));let prefix=magic.len();assert_eq!(valid[prefix],8);
        let mut legacy=valid.clone();legacy[prefix]=7;
        assert!(NormalWaveRest::read(&mut legacy.as_slice(),legacy.len() as u64).is_err());
        rest.coupled.as_mut().unwrap().pending.get_mut(&pred.handle.id()).unwrap().source=source;
        let mut altered=Vec::new();rest.write(&mut altered).unwrap();
        let read=NormalWaveRest::read(&mut altered.as_slice(),altered.len() as u64).unwrap();
        match read.remount_coupled(&s, |_|{}) {
            Ok(_)=>panic!("substituted source was accepted"),
            Err(error)=>assert!(error.to_string().contains("pending produced family does not derive from its source"),"{error}"),
        }
    }
}
