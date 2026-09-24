//! **The rest of the coupled continuation** (current wave rest v7 and v12).
//!
//! A v12 pending comparison retains its source family, member and source chart beside the
//! contemporary family and constitution. Its produced family and relation word are reconstructed
//! when read at the contemporary cut. A state without pending or historical current writes v7.

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
    /// The admitted source chart of this pending operand.
    chart: WaveSourceReceiver,
}
#[derive(Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    epoch: u64,
    neighborhood_base: u64,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    current_neighborhood_epoch: Option<u64>,
    next_contact: u64,
    active_member: Option<usize>,
    contacts: Vec<ContactHeader>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pending: Vec<PendingHeader>,
}
/// The retained producing operands of one pending prediction.
#[derive(Debug, PartialEq, Eq)]
struct PendingRest {
    member: usize,
    chart: WaveSourceReceiver,
    source: NormalWaveFamilyRest,
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
    pub(in super::super) fn has_historical_current(&self) -> bool {
        self.header.current_neighborhood_epoch.is_some()
    }
    /// The frame version this state writes.
    pub(in super::super) fn version(&self) -> u8 {
        if self.has_historical_current() || !self.pending.is_empty() {
            12
        } else {
            7
        }
    }
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
            || self
                .header
                .current_neighborhood_epoch
                .is_some_and(|e| e >= self.neighborhood.epoch())
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
        match (self.header.active_member, self.family.last_relation(), delta) {
            (None, None, 0) => {}
            (Some(j), Some(last), d) if d > 0 => {
                let cut = self.neighborhood.action_cut(j)?;
                if last.roots() != n
                    || last.relation_cut() > cut
                    || (!self.has_historical_current() && last.relation_cut() != cut)
                {
                    return Err(ConstitutiveFibreError::Shape);
                }
            }
            _ => return Err(ConstitutiveFibreError::Shape),
        }
        let mut ids = std::collections::BTreeSet::new();
        for c in &self.header.contacts {
            let relation = self
                .relations
                .get(&c.id)
                .ok_or(ConstitutiveFibreError::Shape)?;
            relation.validate()?;
            if c.id == 0
                || c.id >= self.header.next_contact
                || !ids.insert(c.id)
                || relation.roots() != n
                || relation.relation_cut() != self.neighborhood.action_cut(c.member)?
            {
                return Err(ConstitutiveFibreError::Shape);
            }
        }
        if self.header.pending.len() != self.pending.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut pending_ids = std::collections::BTreeSet::new();
        for p in &self.header.pending {
            let cut = self
                .pending
                .get(&p.id)
                .ok_or(ConstitutiveFibreError::Shape)?;
            cut.source.validate()?;
            if p.id == 0
                || p.id > self.header.epoch
                || p.id <= bank.normal_bank_epoch()
                || !pending_ids.insert(p.id)
                || cut.member != p.member
                || p.chart != cut.chart
                || p.member >= self.neighborhood.members()
                || cut.source.roots() != n
                || cut.source.grain() != self.family.grain()
                || cut.source.source_transport() != self.family.source_transport()
                || cut.source.current_epoch()? != p.id - 1
            {
                return Err(ConstitutiveFibreError::Shape);
            }
            // The source is a state of this same wave: it shares the contemporary origin.
            if !cut.source.same_origin(&self.family) {
                return Err(invalid("pending source does not share the wave's origin"));
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
        }
        Ok(())
    }
    pub(in super::super) fn read(
        input: &mut Take<impl Read>,
        version: u8,
    ) -> Result<Self, ConstitutiveFibreError> {
        if version != 7 && version != 12 {
            return Err(invalid("coupled wave rest version"));
        }
        let header: Header = serde_json::from_slice(&read_blob(input)?).map_err(invalid)?;
        if version == 7 && (!header.pending.is_empty()
            || header.current_neighborhood_epoch.is_some())
        {
            return Err(invalid("pending or historical coupled state requires wave rest v12"));
        }
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
        if header.pending.len() as u64 > input.limit() / 16 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut pending = BTreeMap::new();
        for p in &header.pending {
            let source = read_blob(input)?;
            let source = NormalWaveFamilyRest::read(&mut source.as_slice(), source.len() as u64)?;
            let chart = p.chart;
            if pending
                .insert(
                    p.id,
                    PendingRest {
                        member: p.member,
                        chart,
                        source,
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
                chart: cut.chart,
            });
            pending.insert(
                *id,
                PendingRest {
                    member: cut.member,
                    chart: cut.chart,
                    source: cut.source.rest()?,
                },
            );
        }
        let data = CoupledRestData {
            header: Header {
                epoch: mode.epoch,
                neighborhood_base: mode.neighborhood_base,
                current_neighborhood_epoch: (mode.current_neighborhood_epoch
                    != mode.neighborhood.epoch())
                .then_some(mode.current_neighborhood_epoch),
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
        let current_neighborhood_epoch = data
            .header
            .current_neighborhood_epoch
            .unwrap_or(neighborhood.epoch());
        let mut family = data.family.remount(s)?;
        // A material-only return leaves the historical producing map on the family.
        // Current contact admissions still derive from contemporary standing below.
        if let Some(j) = data
            .header
            .active_member
            .filter(|_| data.header.current_neighborhood_epoch.is_none())
        {
            let receiver = family
                .last_relation()
                .ok_or(ConstitutiveFibreError::Shape)?
                .source_receiver();
            let mut relation =
                neighborhood.read_wave_relation_in_chart(j, base.material.roots(), receiver, None)?;
            if let Some(observed) = family.last_relation().and_then(|v| v.observed_next()) {
                relation = relation.read_observed_next(observed)?;
            } else if let Some(contact) = family.last_relation().and_then(|v| v.source_contact()) {
                relation =
                    relation.read_source_contact(neighborhood.action(j)?, contact.source())?;
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
                base.material.roots(),
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
            pending.insert(
                id,
                Rc::new(super::comparison::CoupledProducingCut {
                    member: cut.member,
                    chart: cut.chart,
                    source: Rc::new(cut.source.remount(s)?),
                }),
            );
        }
        Ok(base.with_continuation(NormalWaveCoupled {
            current_neighborhood_epoch,
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
    use super::super::super::comparison_tests::{current, point};
    use super::super::super::family::tests::law;
    use super::*;
    use crate::{
        embedding_fiber::ResidentReadout,
        native_ecology::constitutive_fibre::ConditionContactMetric,
    };
    fn body<'c>(s: &'c ResidentSurface<'c>, p: i64) -> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
        let a = point(s, &[p, 0]);
        let c = point(s, &[2, 1]);
        let h = point(s, &[1, 0]);
        let local = ResidentGeneratorNeighborhood::with_shared_condition(
            vec![law(s, true)],
            current(&h),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
        ResidentNormalMaterial::found(s, 1, 1, ResidentGrain(32))
            .unwrap()
            .into_applied_difference_wave(current(&a), current(&c))
            .unwrap()
            .with_neighborhood(local)
            .unwrap()
    }
    /// The writer-selected v7 empty and v12 pending forms remount. Read-only v8–v10 frames
    /// refuse; a v12 comparison reads through the contemporary family and releases once.
    #[test]
    #[ignore = "requires CUDA; current v7/v12 coupled rests and retired version refusals"]
    fn current_v7_v12_roundtrip_and_retired_frames_refuse() {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let mut wave = body(&s, 1);
        let magic = b"HOLONIC-NORMAL-WAVE";
        let empty = wave.rest().unwrap();
        let mut v7 = Vec::new();
        empty.write(&mut v7).unwrap();
        assert_eq!(v7[magic.len()], 7);
        let remounted = NormalWaveRest::read(&mut v7.as_slice(), v7.len() as u64)
            .unwrap().remount_coupled(&s, |_| {}).unwrap();
        assert_eq!(remounted.rest().unwrap(), empty);

        for _ in 0..2 {
            let contact = wave.admit_contact(0).unwrap();
            let _ = wave.predict_contact(&contact).unwrap();
        }
        let saved = wave.rest().unwrap();
        let mut written = Vec::new();
        saved.write(&mut written).unwrap();
        assert_eq!(written[magic.len()], 12);
        for retired in [8, 9, 10] {
            let mut old = written.clone();
            old[magic.len()] = retired;
            assert!(NormalWaveRest::read(&mut old.as_slice(), old.len() as u64).is_err());
        }
        let mut restored = NormalWaveRest::read(&mut written.as_slice(), written.len() as u64)
            .unwrap().remount_coupled(&s, |_| {}).unwrap();
        assert_eq!(restored.rest().unwrap(), saved);
        let id = *saved.coupled.as_ref().unwrap().pending.keys().next().unwrap();
        let observed = point(&s, &[3, 0]);
        let a = wave.compare_coupled_prediction(id, current(&observed)).unwrap();
        let b = restored.compare_coupled_prediction(id, current(&observed)).unwrap();
        assert_eq!(a.inspect_row(0).unwrap(), b.inspect_row(0).unwrap());
        restored.release_coupled_prediction(id).unwrap();
        assert!(restored.compare_coupled_prediction(id, current(&observed)).is_err());
    }
    #[test]
    #[ignore = "requires CUDA; a pending source must be a state of the same wave"]
    fn pending_rest_rejects_a_source_from_another_origin() {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let mut wave = body(&s, 1);
        let contact = wave.admit_contact(0).unwrap();
        let (id, _) = wave.predict_contact(&contact).unwrap();
        let other = body(&s, 5);
        let mut rest = wave.rest().unwrap();
        rest.coupled.as_mut().unwrap().pending.get_mut(&id).unwrap().source =
            other.current().rest().unwrap();
        let mut altered = Vec::new();
        assert!(rest.write(&mut altered).is_err());
        let data = rest.coupled.as_ref().unwrap();
        let error = data.validate(&rest).unwrap_err();
        assert!(error.to_string().contains("does not share the wave's origin"), "{error}");
    }
}
