//! An observed difference remains jointly parameterized with its actual producing family.
//! This carrier is not a point source or a span of independently observed alternative rows.
use super::*;
mod joint;
mod constitutive;
pub use constitutive::{CoupledConstitutiveFamily, CoupledConstitutiveAlternative};
pub use joint::{CompiledCoupledJoint, CoupledJointEvaluation, CoupledJointReading};

pub(super) struct CoupledProducingCut<'c> {
    pub(super) member: usize,
    pub(super) source: Rc<NormalWaveFamily<'c>>,
    pub(super) produced: Rc<NormalWaveFamily<'c>>,
}
pub struct NormalCoupledProducingHandle {
    owner: Rc<()>,
    id: u64,
}
impl NormalCoupledProducingHandle {
    pub fn id(&self) -> u64 {
        self.id
    }
}
pub struct NormalCoupledPrediction<'c> {
    pub step: NormalCoupledStep<'c>,
    pub handle: NormalCoupledProducingHandle,
}
#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct NormalFamilyComparisonRow {
    /// None is the affine origin; Some(i) is the original source's i-th generator coefficient.
    pub source_direction: Option<usize>,
    pub features: Vec<Rat>,
    pub observed_difference: Vec<Rat>,
}
pub struct NormalCoupledComparison<'c> {
    id: u64,
    cut: Rc<CoupledProducingCut<'c>>,
    features: usize,
    coefficients: ResidentSection<'c>,
    observed: ResidentSection<'c>,
}
impl<'c> NormalCoupledComparison<'c> {
    pub fn prediction_id(&self) -> u64 {
        self.id
    }
    pub fn member(&self) -> usize {
        self.cut.member
    }
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        &self.cut.source
    }
    pub fn produced(&self) -> &NormalWaveFamily<'c> {
        &self.cut.produced
    }
    pub fn feature_components(&self) -> usize {
        self.features
    }
    pub fn parameter_rows(&self) -> usize {
        self.coefficients.rows()
    }
    pub fn relation(&self) -> &ResidentWaveRelation<'c> {
        self.cut
            .produced
            .last_relation()
            .expect("producing conditional map")
    }
    pub fn observed(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent::rational(&self.observed)
            .expect("admitted comparison observation")
    }
    /// Paired coefficient images use the *same* original source generators and anchor constraint.
    /// Row zero is not a point-current operand; other rows are not independent observations.
    pub fn coefficients(&self) -> &ResidentSection<'c> {
        &self.coefficients
    }
    pub fn inspect_row(
        &self,
        row: usize,
    ) -> Result<NormalFamilyComparisonRow, ConstitutiveFibreError> {
        let s = self.cut.source.origin().fibre().surface;
        let v = wides(&s.read_out_row(&self.coefficients, row)?)?;
        let den = *v.last().ok_or(ConstitutiveFibreError::Shape)?;
        if den <= 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        let values = v[..v.len() - 1]
            .iter()
            .map(|x| Rat::new((*x).into(), den.into()))
            .collect::<Vec<_>>();
        Ok(NormalFamilyComparisonRow {
            source_direction: row.checked_sub(1),
            features: values[..self.features].to_vec(),
            observed_difference: values[self.features..].to_vec(),
        })
    }
}
impl<'c> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    pub fn pending_coupled_predictions(&self) -> usize {
        self.continuation.pending.len()
    }
    pub fn pending_coupled_prediction_ids(&self) -> impl Iterator<Item = u64> + '_ {
        self.continuation.pending.keys().copied()
    }
    pub fn pending_coupled_prediction(
        &self,
        id: u64,
    ) -> Result<NormalCoupledProducingHandle, ConstitutiveFibreError> {
        if !self.continuation.pending.contains_key(&id) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        Ok(NormalCoupledProducingHandle {
            owner: Rc::clone(&self.owner),
            id,
        })
    }
    pub(super) fn coupled_producing_cut(
        &self,
        h: &NormalCoupledProducingHandle,
    ) -> Result<&Rc<CoupledProducingCut<'c>>, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&self.owner, &h.owner) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.continuation
            .pending
            .get(&h.id)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)
    }
    pub fn release_coupled_prediction(
        &mut self,
        h: &NormalCoupledProducingHandle,
    ) -> Result<(), ConstitutiveFibreError> {
        self.coupled_producing_cut(h)?;
        self.continuation.pending.remove(&h.id);
        self.prune_coupled_transport();
        Ok(())
    }
    pub fn predict_contact(
        &mut self,
        contact: &NormalCoupledContact<'c>,
    ) -> Result<NormalCoupledPrediction<'c>, ConstitutiveFibreError> {
        let step = self.advance_contact(contact)?;
        let id = step.successor_epoch;
        // publish_coupled already appended this map when another return was pending. A first
        // prediction starts the retained word here, at its actual producing source.
        self.continuation.transport.entry(id).or_insert_with(|| {
            vec![step.successor.last_relation_shared().expect("producing map")]
        });
        self.continuation.pending.insert(
            id,
            Rc::new(CoupledProducingCut {
                member: contact.member(),
                source: Rc::clone(&contact.binding.source),
                produced: Rc::clone(&step.successor),
            }),
        );
        Ok(NormalCoupledPrediction {
            step,
            handle: NormalCoupledProducingHandle {
                owner: Rc::clone(&self.owner),
                id,
            },
        })
    }
    /// Prepare the complete paired source/observed-difference family at this producing cut.
    /// Pending ownership and contemporary state remain unchanged until a later material return
    /// is actually bound, or the caller explicitly releases the comparison.
    pub fn compare_coupled_prediction(
        &self,
        h: &NormalCoupledProducingHandle,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NormalCoupledComparison<'c>, ConstitutiveFibreError> {
        let cut = Rc::clone(self.coupled_producing_cut(h)?);
        let relation = cut
            .produced
            .last_relation()
            .ok_or(ConstitutiveFibreError::Shape)?;
        if relation.source_contact().is_some() || relation.observed_next().is_some() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let n = relation.roots();
        let k = relation.condition_complex();
        let s = cut.source.origin().fibre().surface;
        let t = n
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let features = (3 * n)
            .checked_mul(k)
            .and_then(|v| v.checked_add(3 * n)?.checked_add(k)?.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let width = features
            .checked_add(2 * n)
            .and_then(|v| v.checked_add(1)?.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let coefficients = s.fresh_section(t + 1, width, ResidentGrain(0))?;
        let snapshot = s.fresh_section(1, 2 * n + 1, ResidentGrain(0))?;
        let family = cut.source.affine_relation();
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_family_comparison(
                &lane,
                family.report(),
                family.source_width(),
                n,
                relation.fixed_condition(),
                observed,
                relation.source_receiver(),
                &coefficients,
                &snapshot,
            )?;
        }
        p.close(0, &coefficients, 64)?;
        let result = p.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "producing family comparison: {:?}",
                result.obstruction
            )));
        }
        Ok(NormalCoupledComparison {
            id: h.id,
            cut,
            features,
            coefficients,
            observed: snapshot,
        })
    }
}

#[cfg(test)]
mod tests;
