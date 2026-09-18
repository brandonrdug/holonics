//! A section of source-conditioned cuts shares one field and one local material.
//! The collective observation adapts M through the fixed producing D; it does not create
//! one ecology/parameter matrix per receiving position or replay a sequence of token emissions.
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::{
    ResidentConstitutiveSection, ResidentNormalEnclosureSection,
};

struct FieldSectionPreparation<'c> {
    source: NativeFieldCurrentSource<'c>,
    features: ResidentNormalEnclosureSection<'c>,
    reaction: ResidentNormalEnclosureSection<'c>,
    incoming: ResidentNormalEnclosureSection<'c>,
    output: ResidentNormalEnclosureSection<'c>,
}

impl<'c> FieldModel<'c> {
    fn prepare_rows(
        &mut self,
        inputs: ResidentConstitutiveSection<'_, 'c>,
        conditions: ResidentConstitutiveSection<'_, 'c>,
    ) -> Result<FieldSectionPreparation<'c>, NativeSessionError> {
        if self.reaction_port != NativeFieldReactionPort::IncomingBoundary
            || inputs.components() != self.width
            || conditions.components() != self.condition_width
            || inputs.rows() != conditions.rows()
        {
            return Err(invalid("field section source/condition chart mismatch"));
        }
        let source = self.field.read_current_source()?;
        let material = self.reaction.predictive_material(self.member)?
            .ok_or_else(|| invalid("field section requires the attached material"))?;
        let joined = inputs.bilinear_features(self.field.surface(), conditions)?;
        let features = joined.features();
        let reaction = material.read_applied_section(features)?;
        let inputs = ResidentNormalEnclosureSection::from_points(inputs, source.enclosure().grain())?;
        let incoming = inputs.sum_same_shape(&reaction)?;
        let output = source.reflect_section(&incoming)?.into_output();
        let features = ResidentNormalEnclosureSection::from_points(features, source.enclosure().grain())?;
        Ok(FieldSectionPreparation { source, features, reaction, incoming, output })
    }

    fn preview_rows(
        &mut self,
        inputs: ResidentConstitutiveSection<'_, 'c>,
        conditions: ResidentConstitutiveSection<'_, 'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, NativeSessionError> {
        Ok(self.prepare_rows(inputs, conditions)?.output)
    }

    fn observe_rows(
        &mut self,
        inputs: ResidentConstitutiveSection<'_, 'c>,
        conditions: ResidentConstitutiveSection<'_, 'c>,
        targets: ResidentConstitutiveSection<'_, 'c>,
        held: &[bool],
        step_bits: u32,
    ) -> Result<Value, NativeSessionError> {
        if targets.rows() != inputs.rows() || targets.components() != self.width
            || held.len() != self.width / 2 || step_bits > 120
        {
            return Err(invalid("field section target/receiver chart mismatch"));
        }
        let next = self.epoch.checked_add(1).ok_or_else(|| invalid("field epoch exhausted"))?;
        let actual_targets = self.targets.checked_add(1).ok_or_else(|| invalid("field target count exhausted"))?;
        let prepared = self.prepare_rows(inputs, conditions)?;
        let targets = ResidentNormalEnclosureSection::from_points(targets, prepared.source.enclosure().grain())?;
        let reflected = prepared.source.reflect_section(&prepared.incoming)?;
        let mask = self.field.surface().mount_section_rest(&ResidentSectionRest::found(
            1, held.len(), ResidentGrain(0), 64,
            held.iter().map(|v| {let v=i64::from(*v);(v,v)}).collect()).map_err(invalid)?).map_err(invalid)?;
        let covectors = reflected.input_covectors(&targets, Some(&mask), step_bits)?;
        let boundary_covectors = covectors.restrict_components(0..self.width)?;
        let reaction_targets = prepared.reaction.sum_same_shape(&boundary_covectors)?;
        if held.iter().all(|v| *v) {
            return Ok(json!({"scope":"shared-field-section-observation","rows":inputs.rows(),
                "parameter_update":"zero: receiver is completely held","epoch":self.epoch}));
        }
        let staged = self.reaction.prepare_feature_section_material(
            self.member, &prepared.features, &reaction_targets)?;
        if !self.reaction.can_commit_field_reaction(&staged) {
            return Err(invalid("stale shared field material"));
        }
        let result = json!({"scope":"shared-field-section-observation","rows":inputs.rows(),
            "before_epoch":self.epoch,"after_epoch":next,
            "material_scope":"shared reaction M through full fixed-D input adjoint",
            "source_complex":self.width/2,"condition_complex":self.condition_width/2,
            "step_denominator_power":step_bits});
        self.reaction.commit_field_reaction(staged)?;
        self.targets = actual_targets;
        self.epoch = next;
        Ok(result)
    }
}

impl<'c> NativeCoupledBody<'c> {
    /// Apply the same producing field to co-present source rows. The supplied source/condition
    /// incidence defines their relation; no separate model or per-row commit is constructed.
    pub fn preview_field_rows(
        &mut self,
        inputs: ResidentConstitutiveSection<'_, 'c>,
        conditions: ResidentConstitutiveSection<'_, 'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, NativeSessionError> {
        self.field_model()?.preview_rows(inputs, conditions)
    }

    /// An actual complete source/target observation at the current producing cut. D remains
    /// the supplied constitutive coupling; M receives all row contributions in one update.
    pub fn observe_field_rows(
        &mut self,
        inputs: ResidentConstitutiveSection<'_, 'c>,
        conditions: ResidentConstitutiveSection<'_, 'c>,
        targets: ResidentConstitutiveSection<'_, 'c>,
        held: &[bool],
        step_bits: u32,
    ) -> Result<Value, NativeSessionError> {
        self.field_model()?.observe_rows(inputs, conditions, targets, held, step_bits)
    }
}
