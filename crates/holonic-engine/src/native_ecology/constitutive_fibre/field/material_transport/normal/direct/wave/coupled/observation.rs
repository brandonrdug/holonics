//! Empirical normal formation of a pending prediction, read at the contemporary cut. This uses
//! the retained source family and its bounds, never an inverse selected by a target.
use super::*;
use crate::native_ecology::constitutive_fibre::resident::PredictiveMaterial;
#[cfg(test)]
mod tests;

/// Resident comparison of a later observation with its prediction, read through the
/// contemporary member law and condition (phase 12b, one cut). Balls are outer receiver bounds;
/// the retained source family and its contemporary produced family remain on the receipt.
pub struct NormalCoupledObservation<'c> {
    id: u64,
    cut: Rc<CoupledProducingCut<'c>>,
    produced: Rc<NormalWaveFamily<'c>>,
    source: ResidentNormalEnclosure<'c>,
    observed: ResidentNormalEnclosure<'c>,
    target: ResidentNormalEnclosure<'c>,
    discrepancy: ResidentNormalEnclosure<'c>,
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
    /// The source family read through the member law at the observation's (contemporary) cut.
    pub fn produced_family(&self) -> &NormalWaveFamily<'c> {
        &self.produced
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
    fn prepare(
        id: u64,
        cut: Rc<CoupledProducingCut<'c>>,
        produced: Rc<NormalWaveFamily<'c>>,
        observed: ResidentNormalInput<'_, 'c>,
        material: &PredictiveMaterial<'c>,
    ) -> Result<(Self, PredictiveMaterial<'c>), ConstitutiveFibreError> {
        let relation = produced
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
        let forward = produced.read_receiver()?.enclosure(grain)?;
        if paired.view().components() != 2 * r || forward.view().components() != 2 * r {
            return Err(ConstitutiveFibreError::Shape);
        }
        let current = paired.view().restrict(r..2 * r)?;
        let prediction = forward.view().restrict(r..2 * r)?;
        let source = paired.difference_source_in_chart(relation.source_receiver())?;
        let observed = observed.enclosure(cut.source.origin().fibre().surface, grain)?;
        let target = observed.view().difference(current.view())?;
        let discrepancy = observed.view().difference(prediction.view())?;
        let next =
            material.stage_enclosed(source.view(), relation.fixed_condition(), target.view())?;
        let receipt = Self {
            id,
            cut,
            produced,
            source,
            observed,
            target,
            discrepancy,
            predecessor_observations: material.material.observations(),
            successor_observations: next.material.observations(),
        };
        Ok((receipt, next))
    }
}
impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    /// Consume one pending prediction as an empirical observation, read at the contemporary
    /// cut: the retained source family, the contemporary member law and condition. This updates
    /// only normal predictive material; the wave clock and current are unchanged, and later
    /// contact reads the returned M.
    pub fn observe_coupled_prediction<'a>(
        &mut self,
        id: impl std::borrow::Borrow<u64>,
        observed: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<NormalCoupledObservation<'c>, ConstitutiveFibreError>
    where
        'c: 'a,
    {
        let id = *id.borrow();
        let cut = Rc::clone(self.coupled_producing_cut(id)?);
        let produced = self.read_contemporary_produced(&cut)?;
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
        let (receipt, next) = NormalCoupledObservation::prepare(
            id,
            Rc::clone(&cut),
            produced,
            observed.into(),
            material,
        )?;
        self.continuation
            .neighborhood
            .publish_predictive(cut.member, epoch, next);
        self.continuation.neighborhood_base = base;
        self.continuation.bindings.clear();
        self.continuation.pending.remove(&id);
        Ok(receipt)
    }
}
