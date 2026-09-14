//! Empirical normal formation at a retained producing cut. This uses the
//! declared source family and its bounds, never an inverse selected by a target.
use super::*;
use crate::native_ecology::constitutive_fibre::resident::PredictiveMaterial;
#[cfg(test)]
mod tests;

/// Resident comparison of a later observation with its original prediction.
/// Balls are outer receiver bounds; the full original source/produced relation
/// remains on the cut. A dependent body returns this receipt at its declared
/// parameter receiver while retaining the operation over its whole generator.
pub struct NormalCoupledObservation<'c> {
    id: u64,
    cut: Rc<CoupledProducingCut<'c>>,
    source: ResidentNormalEnclosure<'c>,
    observed: ResidentNormalEnclosure<'c>,
    target: ResidentNormalEnclosure<'c>,
    discrepancy: ResidentNormalEnclosure<'c>,
    continuation: Vec<NormalContinuationJoin<'c>>,
    pub predecessor_observations: u64,
    pub successor_observations: u64,
}
impl<'c> NormalCoupledObservation<'c> {
    pub fn prediction_id(&self) -> u64 {
        self.id
    }
    pub fn member(&self) -> usize {
        self.cut.member
    }
    pub fn source_family(&self) -> &NormalWaveFamily<'c> {
        &self.cut.source
    }
    pub fn produced_family(&self) -> &NormalWaveFamily<'c> {
        &self.cut.produced
    }
    pub fn source(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.source.view()
    }
    pub fn observed(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.observed.view()
    }
    pub fn target_increment(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.target.view()
    }
    pub fn discrepancy(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.discrepancy.view()
    }
    pub fn continuation(&self) -> &[NormalContinuationJoin<'c>] {
        &self.continuation
    }
    pub(super) fn with_continuation(mut self, joins: Vec<NormalContinuationJoin<'c>>) -> Self {
        self.continuation = joins;
        self
    }
    pub(super) fn prepare(
        id: u64,
        cut: Rc<CoupledProducingCut<'c>>,
        observed: ResidentNormalInput<'_, 'c>,
        material: &PredictiveMaterial<'c>,
    ) -> Result<(Self, PredictiveMaterial<'c>), ConstitutiveFibreError> {
        let relation = cut
            .produced
            .last_relation()
            .ok_or(ConstitutiveFibreError::Shape)?;
        if relation.source_contact().is_some() || relation.observed_next().is_some() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let n = relation.roots();
        let r = n.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let grain = material.material.grain();
        if observed.width() != r {
            return Err(ConstitutiveFibreError::Shape);
        }
        let paired = cut.source.read_receiver()?.enclosure(grain)?;
        let produced = cut.produced.read_receiver()?.enclosure(grain)?;
        if paired.view().components() != 2 * r || produced.view().components() != 2 * r {
            return Err(ConstitutiveFibreError::Shape);
        }
        let current = paired.view().restrict(r..2 * r)?;
        let prediction = produced.view().restrict(r..2 * r)?;
        let source = paired.difference_source_in_chart(relation.source_receiver())?;
        let observed = observed.enclosure(cut.source.origin().fibre().surface, grain)?;
        let target = observed.view().difference(current.view())?;
        let discrepancy = observed.view().difference(prediction.view())?;
        let next =
            material.stage_enclosed(source.view(), relation.fixed_condition(), target.view())?;
        let receipt = Self {
            id,
            cut,
            source,
            observed,
            target,
            discrepancy,
            continuation: Vec::new(),
            predecessor_observations: material.material.observations(),
            successor_observations: next.material.observations(),
        };
        Ok((receipt, next))
    }
}
impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Consume one pending prediction as an empirical observation. This updates
    /// only normal predictive material. The wave clock/current, compatibility
    /// law and condition are unchanged; later contact reads the returned M.
    pub fn observe_coupled_prediction<'a>(
        &mut self,
        h: &NormalCoupledProducingHandle,
        observed: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<NormalCoupledObservation<'c>, ConstitutiveFibreError>
    where
        'c: 'a,
    {
        let cut = Rc::clone(self.coupled_producing_cut(h)?);
        let material = self
            .neighborhood()
            .material(cut.member)?
            .predictive
            .as_ref()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let epoch = self.neighborhood().epoch();
        epoch.checked_add(1).ok_or(ConstitutiveFibreError::Shape)?;
        let base = self
            .continuation
            .neighborhood_base
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let (receipt, next) =
            NormalCoupledObservation::prepare(h.id(), Rc::clone(&cut), observed.into(), material)?;
        self.continuation
            .neighborhood
            .publish_predictive(cut.member, epoch, next);
        self.continuation.neighborhood_base = base;
        self.continuation.bindings.clear();
        self.continuation.pending.remove(&h.id());
        self.prune_coupled_transport();
        Ok(receipt)
    }
}
