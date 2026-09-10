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
        let (contact, formation) = if let Some(observed) = observed {
            let family = law.read_condition_preimage(source, observed)?;
            let proposed = self.condition.prepare_contact(&family)?;
            if !self.condition.can_commit(&proposed) {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            // Declaration failures and known arithmetic refusal preserve the law; uncertain
            // device completion poisons this owner rather than permitting a partial replay.
            self.usable = false;
            let formed =
                match law.advance_bilinear_contact(source, proposed.successor(), Some(observed)) {
                    Ok(formed) => formed,
                    Err(error) => {
                        self.usable = law.usable;
                        return Err(error);
                    }
                };
            // Exclusive neighborhood ownership and the completed law operation leave the
            // preflighted condition predecessor untouched. Publication cannot now fail.
            let contact = self.condition.publish_prepared(proposed);
            self.usable = true;
            self.evidence = Some(NeighborhoodEvidence {
                member,
                epoch: next,
                family: ResidentConditionPreimage {
                    inner: Rc::clone(&contact.family().inner),
                },
            });
            (Some(contact), Some(formed))
        } else {
            (None, None)
        };
        let predecessor_epoch = self.epoch;
        self.epoch = next;
        Ok(GeneratorNeighborhoodStep {
            owner: Rc::clone(&self.owner),
            member,
            predecessor_epoch,
            successor_epoch: next,
            prediction,
            prior_condition,
            contact,
            formation,
            source,
            observed,
        })
    }
}
#[cfg(test)]
mod tests;
