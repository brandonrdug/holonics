//! One continuing field shared explicitly by local conditional generators. Relevance follows
//! their actual learned dependence on that field; co-membership does not add a coefficient.
//! No source codec, input history, token lookup or alternative learning law lives here.
use super::*;
use std::rc::Rc;

mod rest;
pub use rest::{GeneratorNeighborhoodRest, NeighborhoodEvidenceRest};

pub struct ResidentGeneratorNeighborhood<'c> {
    laws: Vec<ResidentConstitutiveFibre<'c>>,
    condition: ResidentConditionCurrent<'c>,
    epoch: u64,
    evidence: Option<NeighborhoodEvidence<'c>>,
    owner: Rc<()>,
    usable: bool,
}

/// The latest received fibre at its producing local-law cut. It is not a cumulative
/// world-belief assertion or an archive; a later observation replaces this single entry.
pub struct NeighborhoodEvidence<'c> {
    pub member: usize,
    pub epoch: u64,
    pub family: ResidentConditionPreimage<'c>,
}

/// The actual source and observation remain borrowed during inspection of this complete
/// passage. Its prediction is a receiver family, not a selected response or an inferred cause.
pub struct GeneratorNeighborhoodStep<'input, 'c> {
    owner: Rc<()>,
    pub member: usize,
    pub predecessor_epoch: u64,
    pub successor_epoch: u64,
    pub prediction: ResidentConstitutiveReturn<'c>,
    pub prior_condition: ResidentConditionStanding<'c>,
    pub contact: Option<ResidentConditionContact<'c>>,
    pub formation: Option<ResidentConstitutiveReturn<'c>>,
    source: ResidentConstitutiveCurrent<'input, 'c>,
    observed: Option<ResidentConstitutiveCurrent<'input, 'c>>,
}

/// Complete neighborhood successor held before publication.  The wave coordinator can retain
/// this object while preparing its own successor; dropping it leaves both live predecessors.
pub(crate) struct PreparedNeighborhoodAdvance<'input, 'c> {
    owner: Rc<()>,
    member: usize,
    predecessor_epoch: u64,
    successor_epoch: u64,
    prediction: ResidentConstitutiveReturn<'c>,
    prior_condition: ResidentConditionStanding<'c>,
    source: ResidentConstitutiveCurrent<'input, 'c>,
    observed: Option<ResidentConstitutiveCurrent<'input, 'c>>,
    condition: Option<PreparedConditionContact<'c>>,
    formation: Option<PreparedConstitutiveFormation<'c>>,
}
impl<'input, 'c> GeneratorNeighborhoodStep<'input, 'c> {
    pub fn source(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.source
    }
    pub fn observed(&self) -> Option<ResidentConstitutiveCurrent<'_, 'c>> {
        self.observed
    }
    pub fn belongs_to(&self, body: &ResidentGeneratorNeighborhood<'c>) -> bool {
        Rc::ptr_eq(&self.owner, &body.owner)
    }
}

impl<'c> ResidentGeneratorNeighborhood<'c> {
    /// The caller declares a common condition chart for these already-founded generators.
    /// This binds actual shared standing; it does not infer a connection from equal output.
    pub fn with_shared_condition(
        laws: Vec<ResidentConstitutiveFibre<'c>>,
        initial: ResidentConstitutiveCurrent<'_, 'c>,
        metric: ConditionContactMetric,
    ) -> Result<Self, ConstitutiveFibreError> {
        let first = laws.first().ok_or(ConstitutiveFibreError::Shape)?;
        if !matches!(
            first.source_chart,
            ConstitutiveSourceChart::BilinearContact { .. }
        ) || laws.iter().any(|law| {
            !law.usable
                || law.source_chart != first.source_chart
                || !std::ptr::eq(law.surface, first.surface)
        }) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let condition = first.retain_condition_current(initial, metric)?;
        Ok(Self {
            laws,
            condition,
            epoch: 0,
            evidence: None,
            owner: Rc::new(()),
            usable: true,
        })
    }
    pub(crate) fn require_usable(&self) -> Result<(), ConstitutiveFibreError> {
        if self.usable {
            Ok(())
        } else {
            Err(ConstitutiveFibreError::Uncertain)
        }
    }
    pub fn members(&self) -> usize {
        self.laws.len()
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn last_received_evidence(&self) -> Option<&NeighborhoodEvidence<'c>> {
        self.evidence.as_ref()
    }
    pub fn condition(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.condition.current()
    }
    pub fn generator(
        &self,
        member: usize,
    ) -> Result<&ResidentConstitutiveFibre<'c>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        self.laws.get(member).ok_or(ConstitutiveFibreError::Shape)
    }

    #[cfg(test)]
    pub(crate) fn read_wave_relation(
        &self,
        member: usize,
        roots: usize,
        proposed: Option<&PreparedNeighborhoodAdvance<'_, 'c>>,
    ) -> Result<ResidentWaveRelation<'c>, ConstitutiveFibreError> {
        self.read_wave_relation_in_chart(member, roots, WaveSourceReceiver::Direct, proposed)
    }
    pub(crate) fn read_wave_relation_in_chart(
        &self,
        member: usize,
        roots: usize,
        receiver: WaveSourceReceiver,
        proposed: Option<&PreparedNeighborhoodAdvance<'_, 'c>>,
    ) -> Result<ResidentWaveRelation<'c>, ConstitutiveFibreError> {
        if let Some(p) = proposed {
            if !self.can_commit_advance(p) {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            let condition = p
                .condition
                .as_ref()
                .map_or_else(|| self.condition.current(), |v| v.successor());
            if p.member == member {
                if let Some(formation) = &p.formation {
                    return formation.read_wave_relation(condition, roots, receiver);
                }
            }
            self.generator(member)?
                .read_wave_relation_in_chart(condition, roots, receiver)
        } else {
            self.generator(member)?.read_wave_relation_in_chart(
                self.condition.current(),
                roots,
                receiver,
            )
        }
    }
    pub(crate) fn can_publish_wave_read(&self, epoch: u64) -> bool {
        self.usable && self.epoch == epoch && self.epoch.checked_add(1).is_some()
    }
    pub(crate) fn publish_wave_read(&mut self, epoch: u64) {
        debug_assert!(self.can_publish_wave_read(epoch));
        self.epoch = epoch + 1;
    }
    pub fn read(
        &self,
        member: usize,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.generator(member)?
            .read_bilinear(source, self.condition.current())
    }
    /// Ordinary occurrence. A received current first meets the old compatible condition
    /// family through the existing contact law. The proposed condition then participates in
    /// the existing observation-founded local relation return. Both complete before commit.
    /// With no received current, this reads conduct and advances the neighborhood epoch only.
    pub fn advance<'i>(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'i, 'c>>,
    ) -> Result<GeneratorNeighborhoodStep<'i, 'c>, ConstitutiveFibreError> {
        let prepared = self.prepare_advance(member, source, observed)?;
        Ok(self.publish_advance(prepared))
    }

    pub(crate) fn prepare_advance<'i>(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'i, 'c>>,
    ) -> Result<PreparedNeighborhoodAdvance<'i, 'c>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let next = self
            .epoch
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let law = self
            .laws
            .get_mut(member)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let prior_condition = self.condition.standing();
        let prediction = law.read_bilinear(source, prior_condition.current())?;
        let (condition, formation) = if let Some(observed) = observed {
            let family = law.read_condition_preimage(source, observed)?;
            let proposed = self.condition.prepare_contact(&family)?;
            if !self.condition.can_commit(&proposed) {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            self.usable = false;
            let prepared =
                match law.prepare_bilinear_contact(source, proposed.successor(), Some(observed)) {
                    Ok(value) => value,
                    Err(error) => {
                        self.usable = law.usable;
                        return Err(error);
                    }
                };
            if !law.can_commit_formation(&prepared) {
                self.usable = true;
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            self.usable = true;
            (Some(proposed), Some(prepared))
        } else {
            (None, None)
        };
        Ok(PreparedNeighborhoodAdvance {
            owner: Rc::clone(&self.owner),
            member,
            predecessor_epoch: self.epoch,
            successor_epoch: next,
            prediction,
            prior_condition,
            source,
            observed,
            condition,
            formation,
        })
    }

    pub(crate) fn can_commit_advance(
        &self,
        prepared: &PreparedNeighborhoodAdvance<'_, 'c>,
    ) -> bool {
        self.usable
            && Rc::ptr_eq(&self.owner, &prepared.owner)
            && self.epoch == prepared.predecessor_epoch
            && prepared
                .condition
                .as_ref()
                .map_or(true, |c| self.condition.can_commit(c))
            && prepared
                .formation
                .as_ref()
                .map_or(true, |f| self.laws[prepared.member].can_commit_formation(f))
    }

    pub(crate) fn publish_advance<'i>(
        &mut self,
        prepared: PreparedNeighborhoodAdvance<'i, 'c>,
    ) -> GeneratorNeighborhoodStep<'i, 'c> {
        debug_assert!(self.can_commit_advance(&prepared));
        let contact = prepared
            .condition
            .map(|c| self.condition.publish_prepared(c));
        let formation = prepared
            .formation
            .map(|f| self.laws[prepared.member].publish_formation(f));
        self.usable = true;
        if let Some(contact) = &contact {
            self.evidence = Some(NeighborhoodEvidence {
                member: prepared.member,
                epoch: prepared.successor_epoch,
                family: ResidentConditionPreimage {
                    inner: Rc::clone(&contact.family().inner),
                },
            });
        }
        self.epoch = prepared.successor_epoch;
        GeneratorNeighborhoodStep {
            owner: Rc::clone(&self.owner),
            member: prepared.member,
            predecessor_epoch: prepared.predecessor_epoch,
            successor_epoch: prepared.successor_epoch,
            prediction: prepared.prediction,
            prior_condition: prepared.prior_condition,
            contact,
            formation,
            source: prepared.source,
            observed: prepared.observed,
        }
    }
}
#[cfg(test)]
mod tests;
