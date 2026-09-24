//! **A pending coupled prediction and its comparison, read at the contemporary cut.**
//!
//! [definition; agent-inferred] The retained quotient of a coupled prediction is its producing
//! operands `(source family, member, source chart)` addressed by its epoch. A comparison reads
//! the source family through the *contemporary* member law and condition — the produced family
//! is that contemporary read, not the family produced at the prediction's epoch — and pairs its
//! coefficient images with the observation. The comparison records the neighborhood cut it was
//! read at; a consumer at a later cut refuses it (re-read it), so no comparison acts as a frozen
//! producing cut. An observed difference remains jointly parameterized with its source family;
//! it is not a point source or a span of independently observed alternative rows.
use super::*;
mod constitutive;
pub(super) mod joint;
pub(super) use constitutive::read_return_operands;
pub use constitutive::{CoupledConstitutiveAlternative, CoupledConstitutiveFamily};
pub use joint::{CompiledCoupledJoint, CoupledJointEvaluation};

/// The producing operands a pending coupled prediction retains (see the module header).
pub(super) struct CoupledProducingCut<'c> {
    pub(super) member: usize,
    pub(super) chart: WaveSourceReceiver,
    pub(super) source: Rc<NormalWaveFamily<'c>>,
}
/// The comparison of an observation with a pending prediction, read at one neighborhood cut.
pub struct NormalCoupledComparison<'c> {
    id: u64,
    cut: Rc<CoupledProducingCut<'c>>,
    produced: Rc<NormalWaveFamily<'c>>,
    read_at: u64,
    features: usize,
    coefficients: ResidentSection<'c>,
    observed: ResidentSection<'c>,
}
impl<'c> NormalCoupledComparison<'c> {
    pub(super) fn cut(&self) -> &Rc<CoupledProducingCut<'c>> {
        &self.cut
    }
    pub fn prediction_id(&self) -> u64 {
        self.id
    }
    pub fn member(&self) -> usize {
        self.cut.member
    }
    /// The retained source family (the producing operand).
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        &self.cut.source
    }
    /// The source family read through the member law at the comparison's cut.
    pub fn produced(&self) -> &NormalWaveFamily<'c> {
        &self.produced
    }
    /// The neighborhood cut this comparison was read at.
    pub fn read_at(&self) -> u64 {
        self.read_at
    }
    pub fn feature_components(&self) -> usize {
        self.features
    }
    pub fn parameter_rows(&self) -> usize {
        self.coefficients.rows()
    }
    pub fn relation(&self) -> &ResidentWaveRelation<'c> {
        self.produced
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
    /// Whether `id` is a pending coupled prediction of this owner (including after a remount).
    pub fn has_pending_coupled_prediction(&self, id: u64) -> bool {
        self.continuation.pending.contains_key(&id)
    }
    /// Resolve an address in this owner's pending coupled population (including after a
    /// validated remount); an arbitrary id refuses.
    pub fn pending_coupled_prediction(&self, id: u64) -> Result<u64, ConstitutiveFibreError> {
        self.coupled_producing_cut(id).map(|_| id)
    }
    pub(super) fn coupled_producing_cut(
        &self,
        id: impl std::borrow::Borrow<u64>,
    ) -> Result<&Rc<CoupledProducingCut<'c>>, ConstitutiveFibreError> {
        self.continuation
            .pending
            .get(id.borrow())
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)
    }
    pub fn release_coupled_prediction(
        &mut self,
        id: impl std::borrow::Borrow<u64>,
    ) -> Result<(), ConstitutiveFibreError> {
        let id = *id.borrow();
        self.coupled_producing_cut(id)?;
        self.continuation.pending.remove(&id);
        Ok(())
    }
    /// Advance through an admitted contact and retain the producing operands as a pending coupled
    /// prediction, addressed by the successor epoch.
    pub fn predict_contact<'a>(
        &mut self,
        contact: &NormalCoupledContact<'c>,
    ) -> Result<(u64, NormalCoupledStep<'a, 'c>), ConstitutiveFibreError> {
        let step = self.advance_contact(contact)?;
        let id = step.successor_epoch;
        self.continuation.pending.insert(
            id,
            Rc::new(CoupledProducingCut {
                member: contact.member(),
                chart: contact.relation().source_receiver(),
                source: Rc::clone(&contact.binding.source),
            }),
        );
        Ok((id, step))
    }
    /// The retained source read through the member law at the contemporary cut.
    pub(super) fn read_contemporary_produced(
        &self,
        cut: &CoupledProducingCut<'c>,
    ) -> Result<Rc<NormalWaveFamily<'c>>, ConstitutiveFibreError> {
        let relation = self.neighborhood().read_wave_relation_in_chart(
            cut.member,
            self.material.roots(),
            cut.chart,
            None,
        )?;
        Ok(Rc::new(cut.source.read_through(Rc::new(relation))?))
    }
    /// Read the complete paired source/observed-difference family of a pending prediction at the
    /// contemporary constitution. Pending ownership and the contemporary state are unchanged.
    pub fn compare_coupled_prediction(
        &self,
        id: impl std::borrow::Borrow<u64>,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NormalCoupledComparison<'c>, ConstitutiveFibreError> {
        let id = *id.borrow();
        self.neighborhood().require_usable()?;
        let cut = Rc::clone(self.coupled_producing_cut(id)?);
        let produced = self.read_contemporary_produced(&cut)?;
        NormalCoupledComparison::read(id, cut, produced, self.neighborhood().epoch(), observed)
    }
    /// Whether a comparison of this owner was read at the contemporary cut.
    pub(super) fn is_contemporary(
        &self,
        comparison: &NormalCoupledComparison<'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        let pending = self.coupled_producing_cut(comparison.id)?;
        if !Rc::ptr_eq(pending, &comparison.cut) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        if comparison.read_at != self.neighborhood().epoch() {
            return Err(ConstitutiveFibreError::Rest(
                "the comparison was read at an earlier cut; re-read it at the contemporary constitution"
                    .into(),
            ));
        }
        Ok(())
    }
    /// **The one-cut return** of a pending prediction: read its comparison at the contemporary
    /// constitution, evaluate the source family's `θ`-face operands `(x(θ), η(θ))` — at the
    /// declared `parameters`, or at the source family's own receiver — and publish them as one
    /// constitutive passage (condition contact, member formation and predictive deposit) that
    /// moves the contemporary family through the updated law. Refusal leaves the owner unchanged.
    pub fn return_coupled_prediction(
        &mut self,
        id: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
        parameters: Option<&ResidentSection<'c>>,
    ) -> Result<(), ConstitutiveFibreError> {
        let comparison = self.compare_coupled_prediction(id, observed)?;
        self.publish_return(&comparison, parameters)
    }
    pub(super) fn publish_return(
        &mut self,
        comparison: &NormalCoupledComparison<'c>,
        parameters: Option<&ResidentSection<'c>>,
    ) -> Result<(), ConstitutiveFibreError> {
        self.is_contemporary(comparison)?;
        let receiver;
        let parameters = match parameters {
            Some(p) => p,
            None => {
                receiver = comparison
                    .source()
                    .receiver_coordinates()?
                    .into_coordinates();
                &receiver
            }
        };
        let (source, difference, _) = read_return_operands(comparison, parameters)?;
        let (member, chart) = (comparison.member(), comparison.cut.chart);
        self.with_admitted(member, chart, |wave, contact| {
            wave.check_contact(contact)?;
            let next = wave
                .epoch()
                .checked_add(1)
                .ok_or(ConstitutiveFibreError::Shape)?;
            wave.develop_contact_source(
                contact,
                next,
                ResidentConstitutiveCurrent::rational(&source)?,
                ResidentConstitutiveCurrent::rational(&difference)?,
            )
            .map(|_| ())
        })?;
        self.continuation.pending.remove(&comparison.id);
        Ok(())
    }
}
impl<'c> NormalCoupledComparison<'c> {
    fn read(
        id: u64,
        cut: Rc<CoupledProducingCut<'c>>,
        produced: Rc<NormalWaveFamily<'c>>,
        read_at: u64,
        observed: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let relation = produced
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
            id,
            cut,
            produced,
            read_at,
            features,
            coefficients,
            observed: snapshot,
        })
    }
}
