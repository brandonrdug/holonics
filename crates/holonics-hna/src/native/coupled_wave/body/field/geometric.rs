//! Joint geometric participation/refinement through the same constituted field and reaction M.
//! Every stage uses one fixed producing D/M cut; all local normal targets are staged together
//! after the complete paired return. Immutable stage carriers retain the nonlinear operands.
use super::*;
use crate::native::field_geometry::CompiledFieldGeometry;
use holonic_engine::{
    ExactWavePhaseTransport,
    native_ecology::constitutive_fibre::{
        NativePhaseParticipation, ResidentConstitutiveSection, ResidentNormalEnclosureSection,
    },
    resident_section::{Dyadic, SeriesAperture},
};

struct GeometricGroupStep<'c> {
    phase: NativePhaseParticipation<'c>,
    condition: ResidentNormalEnclosureSection<'c>,
    features: ResidentNormalEnclosureSection<'c>,
    reaction: ResidentNormalEnclosureSection<'c>,
    incoming: ResidentNormalEnclosureSection<'c>,
}
struct GeometricWord<'c> {
    source: NativeFieldCurrentSource<'c>,
    output: Rc<ResidentNormalEnclosureSection<'c>>,
    steps: Vec<Vec<GeometricGroupStep<'c>>>,
}
fn identity_phases(n: usize) -> Vec<ExactWavePhaseTransport> {
    vec![ExactWavePhaseTransport::identity(); n]
}

impl<'c> FieldModel<'c> {
    fn geometric_zero(
        &self,
        rows: usize,
    ) -> Result<ResidentNormalEnclosureSection<'c>, NativeSessionError> {
        let length = rows
            .checked_mul(self.width)
            .ok_or_else(|| invalid("geometric section extent"))?;
        let raw = self
            .field
            .surface()
            .mount_section_rest(
                &ResidentSectionRest::found(
                    rows,
                    self.width,
                    ResidentGrain(0),
                    64,
                    vec![(0, 0); length],
                )
                .map_err(invalid)?,
            )
            .map_err(invalid)?;
        Ok(ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&raw)?,
            self.reaction
                .predictive_material(self.member)?
                .ok_or_else(|| invalid("geometric material grain"))?
                .grain(),
        )?)
    }
    fn geometric_word(
        &mut self,
        layout: &CompiledFieldGeometry,
        seed: Rc<ResidentNormalEnclosureSection<'c>>,
        held: &[bool],
    ) -> Result<GeometricWord<'c>, NativeSessionError> {
        if self.reaction_port != NativeFieldReactionPort::IncomingBoundary
            || seed.rows() != layout.rows
            || seed.components() != self.width
            || self.condition_width != 2 * layout.condition_complex
            || Some(held.len()) != layout.rows.checked_mul(self.width / 2)
        {
            return Err(invalid("geometric field source/condition chart"));
        }
        let _placement =
            layout.certify_placement(self.field.surface(), self.width, self.condition_width)?;
        let source = self.field.read_current_source()?;
        let material = self
            .reaction
            .predictive_material(self.member)?
            .ok_or_else(|| invalid("geometric field material"))?;
        let mut current = seed.clone();
        let mut steps = Vec::new();
        steps.try_reserve(layout.steps).map_err(invalid)?;
        for stage_index in 0..layout.steps {
            let mut groups = Vec::with_capacity(layout.groups.len());
            let mut joined: Option<ResidentNormalEnclosureSection<'c>> = None;
            for (group_index, group) in layout.groups.iter().enumerate() {
                let query = Rc::new(
                    current
                        .gather_phase_rows(
                            &group.receivers,
                            &identity_phases(group.receivers.len()),
                            self.width,
                        )
                        .map_err(|e| {
                            invalid(format!(
                                "geometric stage {stage_index} group {group_index} query: {e}"
                            ))
                        })?,
                );
                let neighbors = Rc::new(
                    current
                        .gather_phase_rows(&group.sources, &group.phases, self.width)
                        .map_err(|e| {
                            invalid(format!(
                                "geometric stage {stage_index} group {group_index} neighbors: {e}"
                            ))
                        })?,
                );
                let phase = query.phase_participation(
                    neighbors,
                    group.neighbors,
                    Dyadic {
                        significand: layout.beta_significand,
                        exponent: layout.beta_exponent,
                    },
                    SeriesAperture(layout.series_terms),
                )?;
                let local_rows: Vec<_> = (0..group.receivers.len()).collect();
                let condition = phase.participation().gather_phase_rows(
                    &local_rows,
                    &identity_phases(local_rows.len()),
                    self.condition_width,
                )?;
                let features = phase.output().bilinear_enclosed_features(&condition)?;
                let reaction = material.read_applied_bilinear_enclosed_pair(
                    phase.output(),
                    &condition,
                    false,
                )?;
                let incoming = material.read_applied_bilinear_enclosed_pair(
                    phase.output(),
                    &condition,
                    true,
                )?;
                let reflected = source
                    .reflect_section(&incoming)?
                    .into_output()
                    .restrict_components(0..self.width)?;
                let scattered = reflected.scatter_phase_adjoint(
                    &group.receivers,
                    &identity_phases(group.receivers.len()),
                    layout.rows,
                )?;
                joined = Some(match joined {
                    Some(previous) => previous.sum_same_shape(&scattered)?,
                    None => scattered,
                });
                groups.push(GeometricGroupStep {
                    phase,
                    condition,
                    features,
                    reaction,
                    incoming,
                });
            }
            let generated =
                joined.ok_or_else(|| invalid("geometric field has no receiving group"))?;
            current = Rc::new(generated.held_refinement(&seed, held, layout.relaxation_bits)?);
            steps.push(groups);
        }
        Ok(GeometricWord {
            source,
            output: current,
            steps,
        })
    }
    fn geometric_return(
        &self,
        layout: &CompiledFieldGeometry,
        word: &GeometricWord<'c>,
        target: &ResidentNormalEnclosureSection<'c>,
        held: &[bool],
        observed: &[bool],
        step_bits: u32,
    ) -> Result<
        (
            ResidentNormalEnclosureSection<'c>,
            Vec<ResidentNormalEnclosureSection<'c>>,
        ),
        NativeSessionError,
    > {
        if target.rows() != layout.rows
            || target.components() != self.width
            || held.len() != observed.len()
            || step_bits > 120
        {
            return Err(invalid("geometric receiving target/step"));
        }
        let zero = self.geometric_zero(layout.rows)?;
        let row_ids: Vec<_> = (0..layout.rows).collect();
        let minus = ExactWavePhaseTransport::new(
            num_rational::BigRational::from_integer((-1).into()),
            num_rational::BigRational::from_integer(0.into()),
        )
        .map_err(invalid)?;
        let neg_output =
            word.output
                .gather_phase_rows(&row_ids, &vec![minus; layout.rows], self.width)?;
        let difference = target.sum_same_shape(&neg_output)?;
        let receiving_mask: Vec<_> = held
            .iter()
            .zip(observed)
            .map(|(fixed, seen)| *fixed || !*seen)
            .collect();
        let mut gradient = difference.held_refinement(&zero, &receiving_mask, step_bits)?;
        let mut seed_gradient: Option<ResidentNormalEnclosureSection<'c>> = None;
        let mut reaction_targets = Vec::new();
        let material = self
            .reaction
            .predictive_material(self.member)?
            .ok_or_else(|| invalid("geometric producing material"))?;
        for groups in word.steps.iter().rev() {
            let seed_part = zero.held_refinement(&gradient, held, layout.relaxation_bits)?;
            seed_gradient = Some(match seed_gradient {
                Some(g) => g.sum_same_shape(&seed_part)?,
                None => seed_part,
            });
            let returned = gradient.held_refinement(&zero, held, layout.relaxation_bits)?;
            let mut previous: Option<ResidentNormalEnclosureSection<'c>> = None;
            for (group, stage) in layout.groups.iter().zip(groups) {
                let g = returned.gather_phase_rows(
                    &group.receivers,
                    &identity_phases(group.receivers.len()),
                    self.width,
                )?;
                let joint_width =
                    word.source.boundary_components() + word.source.internal_components();
                let ids: Vec<_> = (0..g.rows()).collect();
                let joint = g.gather_phase_rows(&ids, &identity_phases(ids.len()), joint_width)?;
                let reflection = word.source.reflect_section(&stage.incoming)?;
                let incoming_covector = reflection
                    .reflect_joint_section(&joint)?
                    .restrict_components(0..self.width)?;
                let feature_covector = material.pull_back_enclosed_section(&incoming_covector)?;
                let (source_covector, condition_covector) = stage
                    .phase
                    .output()
                    .bilinear_enclosed_pullback(&stage.condition, &feature_covector)?;
                let gy = source_covector.sum_same_shape(&incoming_covector)?;
                let gp = condition_covector.restrict_components(0..2 * group.neighbors)?;
                let phase_return = stage.phase.pull_back(&gy, Some(&gp))?;
                let query = phase_return.query().scatter_phase_adjoint(
                    &group.receivers,
                    &identity_phases(group.receivers.len()),
                    layout.rows,
                )?;
                let neighbors = phase_return.transported_neighbors().scatter_phase_adjoint(
                    &group.sources,
                    &group.phases,
                    layout.rows,
                )?;
                let group_return = query.sum_same_shape(&neighbors)?;
                previous = Some(match previous {
                    Some(g) => g.sum_same_shape(&group_return)?,
                    None => group_return,
                });
                reaction_targets.push(stage.reaction.sum_same_shape(&incoming_covector)?);
            }
            gradient = previous.ok_or_else(|| invalid("geometric return has no group"))?;
        }
        let seed_gradient =
            seed_gradient.ok_or_else(|| invalid("geometric return has no stage"))?;
        Ok((seed_gradient.sum_same_shape(&gradient)?, reaction_targets))
    }
}
impl<'c> NativeCoupledBody<'c> {
    pub(crate) fn preview_geometric_rows(
        &mut self,
        layout: &CompiledFieldGeometry,
        seed: Rc<ResidentNormalEnclosureSection<'c>>,
        held: &[bool],
    ) -> Result<Rc<ResidentNormalEnclosureSection<'c>>, NativeSessionError> {
        Ok(self
            .field_model()?
            .geometric_word(layout, seed, held)?
            .output)
    }
    pub(crate) fn observe_geometric_rows(
        &mut self,
        layout: &CompiledFieldGeometry,
        seed: Rc<ResidentNormalEnclosureSection<'c>>,
        target: &ResidentNormalEnclosureSection<'c>,
        held: &[bool],
        observed: &[bool],
        step_bits: u32,
        commit: bool,
    ) -> Result<(Value, ResidentNormalEnclosureSection<'c>), NativeSessionError> {
        let model = self.field_model()?;
        let word = model.geometric_word(layout, seed, held)?;
        let (source_covector, targets) =
            model.geometric_return(layout, &word, target, held, observed, step_bits)?;
        if !commit
            || !held
                .iter()
                .zip(observed)
                .any(|(fixed, seen)| !*fixed && *seen)
        {
            return Ok((
                json!({"scope":"geometric-field-paired-return","material_deposited":false,"steps":layout.steps}),
                source_covector,
            ));
        }
        let features: Vec<_> = word
            .steps
            .iter()
            .rev()
            .flat_map(|groups| groups.iter().map(|g| &g.features))
            .collect();
        let target_refs: Vec<_> = targets.iter().collect();
        let features = ResidentNormalEnclosureSection::concatenate_rows(&features)?;
        let targets = ResidentNormalEnclosureSection::concatenate_rows(&target_refs)?;
        let epoch = model
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("field epoch exhausted"))?;
        let observations = model
            .targets
            .checked_add(1)
            .ok_or_else(|| invalid("field target count exhausted"))?;
        let staged =
            model
                .reaction
                .prepare_feature_section_material(model.member, &features, &targets)?;
        if !model.reaction.can_commit_field_reaction(&staged) {
            return Err(invalid("stale geometric material"));
        }
        let value = json!({"scope":"geometric-field-observation","material_deposited":true,"before_epoch":model.epoch,"after_epoch":epoch,
            "steps":layout.steps,"geometric_rows":layout.rows,"participation_complex":layout.condition_complex,
            "material_scope":"one shared M normal return after the complete nonlinear fixed-D paired word","normal_rows":features.rows()});
        model.reaction.commit_field_reaction(staged)?;
        model.targets = observations;
        model.epoch = epoch;
        Ok((value, source_covector))
    }
}
