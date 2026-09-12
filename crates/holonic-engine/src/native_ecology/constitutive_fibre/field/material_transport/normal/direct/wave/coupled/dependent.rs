//! Owned executable continuation of a dependent constitutive return. The full generator,
//! original domain and historical joins are the state; a receiver assignment is only its chart.
use super::*;

/// One owner of the complete family-valued successor. The prior wave is moved into immutable
/// generator substrate; it is not exposed as a competing continuing ecology. Evaluation stages
/// only conditional material, using the existing native contact/formation law.
pub struct ResidentCoupledConstitutive<'c> {
    base: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    comparison: NormalCoupledComparison<'c>,
    receiver: ResidentSection<'c>,
    sources: Vec<ConstitutiveSourcePassage<'c>>,
    epoch: u64,
}
struct ConstitutiveSourcePassage<'c> {
    member: usize,
    chart: WaveSourceReceiver,
    source: ResidentSection<'c>,
}
/// Failed ownership transfer returns every supplied owner and packet recoverably.
pub struct CoupledConstitutiveRefusal<'c> {
    pub wave: ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
    pub comparison: NormalCoupledComparison<'c>,
    pub receiver: ResidentSection<'c>,
    pub reason: ConstitutiveFibreError,
}
impl std::fmt::Debug for CoupledConstitutiveRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}
pub struct ConstitutiveSourceRefusal<'c> {
    pub source: ResidentSection<'c>,
    pub reason: ConstitutiveFibreError,
}
impl std::fmt::Debug for ConstitutiveSourceRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}

impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Publish the entire executable return family by ownership transfer. No theta-dependent
    /// condition or material matrix is installed as a common value. The caller explicitly names
    /// a receiver section; its supported (possibly plural) output witnesses this scoped admission.
    /// Other source assignments remain executable through evaluate().
    pub fn into_constitutive_continuation(
        mut self,
        comparison: NormalCoupledComparison<'c>,
        receiver: ResidentSection<'c>,
    ) -> Result<ResidentCoupledConstitutive<'c>, CoupledConstitutiveRefusal<'c>> {
        let prepared = (|| {
            let next = self
                .epoch()
                .checked_add(1)
                .ok_or(ConstitutiveFibreError::Shape)?;
            let mut family = self.read_coupled_constitutive_family(&comparison)?;
            let proposed = family.evaluate(&receiver)?;
            proposed
                .successor_section()
                .read_receiver()?
                .require_supported()?;
            Ok::<_, ConstitutiveFibreError>(next)
        })();
        match prepared {
            Ok(epoch) => Ok(ResidentCoupledConstitutive {
                base: self,
                comparison,
                receiver,
                sources: Vec::new(),
                epoch,
            }),
            Err(reason) => Err(CoupledConstitutiveRefusal {
                wave: self,
                comparison,
                receiver,
                reason,
            }),
        }
    }
}

impl<'c> ResidentCoupledConstitutive<'c> {
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn consumed_prediction(&self) -> u64 {
        self.comparison.prediction_id()
    }
    pub fn source_parameters(&self) -> usize {
        self.comparison.parameter_rows() - 1
    }
    pub fn source_passages(&self) -> usize {
        self.sources.len()
    }
    pub fn receiver(&self) -> &ResidentSection<'c> {
        &self.receiver
    }
    pub fn producing_comparison(&self) -> &NormalCoupledComparison<'c> {
        &self.comparison
    }
    /// The consumed cut remains a causal witness inside the generator's frozen substrate, not
    /// an active pending return. There is no operation that remounts that substrate as this owner.
    pub fn pending_prediction_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.base
            .pending_coupled_prediction_ids()
            .filter(|id| *id != self.consumed_prediction())
    }
    pub fn pending_prediction(
        &self,
        id: u64,
    ) -> Result<NormalCoupledProducingHandle, ConstitutiveFibreError> {
        if id == self.consumed_prediction() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.base.pending_coupled_prediction(id)
    }
    fn evaluate_parts<'p, 'j>(
        base: &mut ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
        comparison: &'j NormalCoupledComparison<'c>,
        sources: &[ConstitutiveSourcePassage<'c>],
        parameters: &'p ResidentSection<'c>,
    ) -> Result<CoupledConstitutiveAlternative<'p, 'j, 'c>, ConstitutiveFibreError> {
        let mut value = base
            .read_coupled_constitutive_family(comparison)?
            .evaluate(parameters)?;
        for passage in sources {
            let other = if passage.member == comparison.member() {
                None
            } else {
                Some(base.neighborhood().generator(passage.member)?)
            };
            value.actuate_source(
                passage.member,
                other,
                passage.chart,
                ResidentConstitutiveCurrent::rational(&passage.source)?,
            )?;
        }
        Ok(value)
    }
    pub fn evaluate<'p, 'j>(
        &'j mut self,
        parameters: &'p ResidentSection<'c>,
    ) -> Result<CoupledConstitutiveAlternative<'p, 'j, 'c>, ConstitutiveFibreError> {
        Self::evaluate_parts(&mut self.base, &self.comparison, &self.sources, parameters)
    }
    /// A declared source-section receiver of this complete generator. This is not asserted to
    /// equal a minimum-norm projection over its entire non-affine source/condition graph.
    pub fn read_receiver(
        &mut self,
    ) -> Result<CoupledConstitutiveAlternative<'_, '_, 'c>, ConstitutiveFibreError> {
        Self::evaluate_parts(
            &mut self.base,
            &self.comparison,
            &self.sources,
            &self.receiver,
        )
    }
    /// Ordinary next occurrence, applied to every conditional material/current realization.
    /// Stage and inspect the declared receiver before appending the complete source operation.
    /// No host numerical section readout or selection by an expected response occurs here.
    pub fn actuate_source(
        &mut self,
        member: usize,
        chart: WaveSourceReceiver,
        source: ResidentSection<'c>,
    ) -> Result<(), ConstitutiveSourceRefusal<'c>> {
        let prepared = (|| {
            let next = self
                .epoch
                .checked_add(1)
                .ok_or(ConstitutiveFibreError::Shape)?;
            self.sources
                .try_reserve(1)
                .map_err(|_| ConstitutiveFibreError::Shape)?;
            let mut value = Self::evaluate_parts(
                &mut self.base,
                &self.comparison,
                &self.sources,
                &self.receiver,
            )?;
            let other = if member == self.comparison.member() {
                None
            } else {
                Some(self.base.neighborhood().generator(member)?)
            };
            value.actuate_source(
                member,
                other,
                chart,
                ResidentConstitutiveCurrent::rational(&source)?,
            )?;
            value
                .successor_section()
                .read_receiver()?
                .require_supported()?;
            Ok::<_, ConstitutiveFibreError>(next)
        })();
        match prepared {
            Ok(next) => {
                self.sources.push(ConstitutiveSourcePassage {
                    member,
                    chart,
                    source,
                });
                self.epoch = next;
                Ok(())
            }
            Err(reason) => Err(ConstitutiveSourceRefusal { source, reason }),
        }
    }
}

mod rest;
pub use rest::CoupledConstitutiveRest;
#[cfg(test)]
mod tests;
