//! Source-qualified reaction views over the continuing neighborhood.
//!
//! Forecasts read the applied action at an explicit producing condition. Local source/target
//! examples and source-qualified proximal responses use the existing normal moment owner.
//! A derived proximal target is a material-update operand, not another exterior observation;
//! the public model counts actual output targets separately.

use super::*;
mod rest;
pub use rest::FieldReactionEnclosureRest;

/// Owned source-qualified result of an enclosed family read. Source, producing condition, output
/// and material snapshot remain separate; the output is never treated as an observation.
pub struct FieldReactionEnclosure<'c> {
    source: ResidentNormalEnclosure<'c>,
    producing_condition: ResidentSection<'c>,
    output: ResidentNormalEnclosure<'c>,
    pub(crate) material: ResidentNormalMaterialView<'c>,
    owner: Rc<()>,
    member: usize,
}

/// Unpublished local material response; the continuing owner is never copied.
pub struct PreparedFieldReaction<'c> {
    owner: Rc<()>,
    member: usize,
    before_epoch: u64,
    after_epoch: u64,
    material: PredictiveMaterial<'c>,
}

impl<'c> FieldReactionEnclosure<'c> {
    pub fn source_view(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.source.view()
    }
    pub fn output_view(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.output.view()
    }
    pub fn producing_condition(
        &self,
    ) -> Result<ResidentConstitutiveCurrent<'_, 'c>, ConstitutiveFibreError> {
        ResidentConstitutiveCurrent::rational(&self.producing_condition)
    }

    /// Apply the same producing reaction to the boundary of a joint current and leave
    /// its internal coordinates coupled to that boundary through one source enclosure.
    pub fn apply_joint_current(
        &self,
        source: ResidentNormalEnclosureView<'_, 'c>,
        external: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        self.material.read_applied_bilinear_joint(
            source,
            self.source.view().components(),
            self.producing_condition()?,
            external,
        )
    }

    /// The identity and local reaction act on the same retained incoming current.
    pub fn incoming_with_reaction(
        &self,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        self.material
            .read_applied_bilinear_identity(self.source.view(), self.producing_condition()?)
    }

    pub fn material_observations(&self) -> u64 {
        self.material.observations
    }
}

impl<'c> ResidentGeneratorNeighborhood<'c> {
    /// Form an actual source/condition/target passage while keeping the supplied producing
    /// condition separate from contemporary condition standing. Predictive and compatibility
    /// formation both use `producing_condition`; contact formation receives the complete
    /// preimage through the neighborhood's current standing. Preparation and publication remain
    /// one atomic successor.
    pub fn receive_reaction_observation_at<'i>(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        producing_condition: ResidentConstitutiveCurrent<'i, 'c>,
        observed: ResidentConstitutiveCurrent<'i, 'c>,
    ) -> Result<GeneratorNeighborhoodStep<'i, 'c>, ConstitutiveFibreError>
    where
        'c: 'i,
    {
        let consequence = self.prepare_consequence_with(
            member,
            source,
            Some(observed),
            Some(producing_condition),
            ConsequenceCondition::Producing,
        )?;
        if !self.can_commit_consequence(&consequence) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        Ok(self.publish_consequence(consequence, source, Some(observed)))
    }

    /// Read one staged reaction at the supplied producing condition. The condition is an actual
    /// source operand; the neighborhood's contemporary condition is not substituted.
    pub fn forecast_reaction_at_condition(
        &self,
        member: usize,
        source: ResidentConstitutiveCurrent<'_, 'c>,
        producing_condition: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentConstitutiveReturn<'c>, ConstitutiveFibreError> {
        self.action(member)?
            .read_bilinear(source, producing_condition)
    }

    /// Read an attached normal action from an enclosed source family and explicit point condition.
    /// The stored coefficient map is the executed reaction law, matching the attached action.
    /// The complete normal material and its distinct fit/reference bounds remain in the receipt;
    /// source uncertainty and arithmetic error still belong to the generated output.
    pub fn forecast_enclosed_reaction(
        &self,
        member: usize,
        source: ResidentNormalEnclosureView<'_, 'c>,
        producing_condition: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<FieldReactionEnclosure<'c>, ConstitutiveFibreError> {
        let material = self
            .material(member)?
            .predictive
            .as_ref()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let source_owned = source.to_owned()?;
        let producing_condition_owned = producing_condition.to_owned(source.surface)?;
        let condition_view = ResidentConstitutiveCurrent::rational(&producing_condition_owned)?;
        let output = match material.material.source_chart() {
            NormalSourceChart::Features { .. } => material
                .material
                .retained_view()
                .read_applied_bilinear(source_owned.view(), condition_view)?,
            NormalSourceChart::Wave { .. } => material
                .material
                .read_applied(source_owned.view())?
                .into_forward(),
        };
        Ok(FieldReactionEnclosure {
            source: source_owned,
            producing_condition: producing_condition_owned,
            output,
            material: material.material.retained_view(),
            owner: Rc::clone(&self.owner),
            member,
        })
    }

    /// Incorporate an actual point source/target example through the existing neighborhood
    /// observation law. The observed current is supplied by the caller and is never synthesized
    /// from the forecast.
    pub fn observe_reaction<'i>(
        &mut self,
        member: usize,
        source: ResidentConstitutiveCurrent<'i, 'c>,
        observed: ResidentConstitutiveCurrent<'i, 'c>,
    ) -> Result<GeneratorNeighborhoodStep<'i, 'c>, ConstitutiveFibreError> {
        self.advance(member, source, Some(observed))
    }

    /// Prepare an actual enclosed source/target example through the normal material owner. The
    /// returned successor is unpublished so a caller can commit it with other field changes.
    pub fn prepare_enclosed_material(
        &self,
        member: usize,
        source: ResidentNormalEnclosureView<'_, 'c>,
        producing_condition: ResidentConstitutiveCurrent<'_, 'c>,
        observed: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<PreparedFieldReaction<'c>, ConstitutiveFibreError> {
        self.require_usable()?;
        let after_epoch = self
            .epoch
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let predictive = self
            .material(member)?
            .predictive
            .as_ref()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let next = predictive.stage_enclosed(source, producing_condition, observed)?;
        Ok(PreparedFieldReaction {
            owner: Rc::clone(&self.owner),
            member,
            before_epoch: self.epoch,
            after_epoch,
            material: next,
        })
    }

    /// Prepare the local material response to an output cotangent.  The cotangent is represented
    /// by an admitted enclosure and is added to the predicted output on the resident surface;
    /// the resulting target is staged but not published, so a field update can commit atomically.
    pub fn prepare_reaction_target(
        &self,
        member: usize,
        receipt: &FieldReactionEnclosure<'c>,
        output_cotangent: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<PreparedFieldReaction<'c>, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&self.owner, &receipt.owner) || receipt.member != member {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let target = receipt.output.view().sum_same_shape(output_cotangent)?;
        self.prepare_enclosed_material(
            member,
            receipt.source.view(),
            receipt.producing_condition()?,
            target.view(),
        )
    }

    /// Stage the complete feature/target section on the existing shared normal owner.
    /// The caller's source feature construction retains its source/condition relation.
    pub fn prepare_feature_section_material(
        &self,
        member: usize,
        features: &crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection<'c>,
        observed: &crate::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection<'c>,
    ) -> Result<PreparedFieldReaction<'c>, ConstitutiveFibreError> {
        self.require_usable()?;
        let after_epoch = self
            .epoch
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let prior = self
            .material(member)?
            .predictive
            .as_ref()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let next = prior
            .material
            .stage_receive_enclosed_section(features, observed)?;
        let material = PredictiveMaterial::new(next, &prior.action)?;
        Ok(PreparedFieldReaction {
            owner: Rc::clone(&self.owner),
            member,
            before_epoch: self.epoch,
            after_epoch,
            material,
        })
    }

    pub fn can_commit_field_reaction(&self, prepared: &PreparedFieldReaction<'c>) -> bool {
        self.usable
            && Rc::ptr_eq(&self.owner, &prepared.owner)
            && self.epoch == prepared.before_epoch
            && prepared.member < self.laws.len()
    }

    pub fn commit_field_reaction(
        &mut self,
        prepared: PreparedFieldReaction<'c>,
    ) -> Result<(), ConstitutiveFibreError> {
        if !self.can_commit_field_reaction(&prepared) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.laws[prepared.member].predictive = Some(prepared.material);
        self.epoch = prepared.after_epoch;
        Ok(())
    }
}
