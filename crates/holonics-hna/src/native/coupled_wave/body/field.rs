//! Direct model composition on the operative field. No wave surrogate or host semantic replay.
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::{
    ConstitutiveSourceChart, FieldReactionEnclosure, GeneratorNeighborhoodRest,
    NativeConstitutiveField, NativeFieldCurrentSource, NativeFieldRest,
    ResidentGeneratorNeighborhood, ResidentNormalEnclosure, ResidentNormalEnclosureView,
};
use std::{collections::BTreeMap, rc::Rc};

struct FieldProducingSection<'c> {
    source: NativeFieldCurrentSource<'c>,
    reaction: FieldReactionEnclosure<'c>,
    input: ResidentNormalEnclosure<'c>,
    full_output: ResidentNormalEnclosure<'c>,
    outward: ResidentNormalEnclosure<'c>,
    epoch: u64,
}

/// The generated boundary and its retained joint construction. Sharing this immutable result
/// shares no continuing ecology. The comparison identifier is local to its model owner.
pub struct NativeFieldGeneratedSection<'c> {
    producing: Rc<FieldProducingSection<'c>>,
    comparison: Option<u64>,
}
impl<'c> NativeFieldGeneratedSection<'c> {
    pub fn output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.producing.outward.view()
    }
    pub fn joint_output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.producing.full_output.view()
    }
    pub fn comparison_id(&self) -> Option<u64> {
        self.comparison
    }
    pub fn producing_epoch(&self) -> u64 {
        self.producing.epoch
    }
    pub fn inspect(&self) -> Result<Value, NativeSessionError> {
        Ok(
            json!({"scope":"constituted-field-joint","producing_epoch":self.producing.epoch,
            "field_source_cut":self.producing.source.field_cut(),"comparison":self.comparison,
            "boundary":self.output().inspect()?,"joint":self.joint_output().inspect()?}),
        )
    }
}

/// A failed attachment returns both live components, rather than dropping a trained field.
pub struct NativeFieldAttachRefusal<'c> {
    pub field: NativeConstitutiveField<'c>,
    pub reaction: ResidentGeneratorNeighborhood<'c>,
    pub reason: NativeSessionError,
}
impl std::fmt::Debug for NativeFieldAttachRefusal<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeFieldAttachRefusal")
            .field("reason", &self.reason)
            .finish_non_exhaustive()
    }
}

pub(super) struct FieldModel<'c> {
    field: NativeConstitutiveField<'c>,
    reaction: ResidentGeneratorNeighborhood<'c>,
    member: usize,
    width: usize,
    condition_width: usize,
    epoch: u64,
    generations: u64,
    next_comparison: u64,
    targets: u64,
    pending: BTreeMap<u64, Rc<FieldProducingSection<'c>>>,
}
impl<'c> FieldModel<'c> {
    pub(super) fn new(
        mut field: NativeConstitutiveField<'c>,
        reaction: ResidentGeneratorNeighborhood<'c>,
        member: usize,
    ) -> Result<Self, NativeFieldAttachRefusal<'c>> {
        let checked = (|| -> Result<(usize, usize), NativeSessionError> {
            field.enable_operative_contacts()?;
            let source = field.read_current_source()?;
            let width = source.boundary_components();
            let ConstitutiveSourceChart::BilinearContact {
                source_complex,
                condition_complex,
            } = reaction.generator(member)?.source_chart()
            else {
                return Err(invalid(
                    "field reaction requires its bilinear source/condition chart",
                ));
            };
            let material = reaction
                .predictive_material(member)?
                .ok_or_else(|| invalid("field reaction requires predictive material"))?;
            if source_complex.checked_mul(2) != Some(width)
                || material.targets().checked_mul(2) != Some(width)
                || material.grain() != source.enclosure().grain()
            {
                return Err(invalid("field/reaction port or grain mismatch"));
            }
            let condition_width = condition_complex
                .checked_mul(2)
                .ok_or_else(|| invalid("condition width overflow"))?;
            Ok((width, condition_width))
        })();
        let (width, condition_width) = match checked {
            Ok(v) => v,
            Err(reason) => {
                return Err(NativeFieldAttachRefusal {
                    field,
                    reaction,
                    reason,
                })
            }
        };
        Ok(Self {
            field,
            reaction,
            member,
            width,
            condition_width,
            epoch: 0,
            generations: 0,
            next_comparison: 0,
            targets: 0,
            pending: BTreeMap::new(),
        })
    }
    pub(super) fn epoch(&self) -> u64 {
        self.epoch
    }
    pub(super) fn roots(&self) -> usize {
        self.field.nodes()
    }
    pub(super) fn members(&self) -> usize {
        self.reaction.members()
    }
    pub(super) fn passages(&self) -> u64 {
        self.generations
    }
    pub(super) fn pending(&self) -> usize {
        self.pending.len()
    }
    pub(super) fn pending_ids(&self) -> Vec<u64> {
        self.pending.keys().copied().collect()
    }
    pub(super) fn observations(&self) -> Option<u64> {
        self.reaction
            .predictive_material(self.member)
            .ok()
            .flatten()
            .map(|m| m.observations())
    }
    pub(super) fn release(&mut self, id: u64) -> Result<(), NativeSessionError> {
        self.pending
            .remove(&id)
            .map(|_| ())
            .ok_or_else(|| invalid("unknown field producing comparison"))
    }
    pub(super) fn inspect(&mut self) -> Result<Value, NativeSessionError> {
        let source = self.field.read_current_source()?;
        Ok(
            json!({"scope":"constituted-field-joint","epoch":self.epoch,"actual_targets":self.targets,
            "current":source.enclosure().inspect()?,"contacts":source.births(),
            "material":source.material()?.map(|m|m.inspect()).transpose()?,
            "reaction":self.reaction.predictive_material(self.member)?.map(|m|m.inspect()).transpose()?,
            "pending":self.pending_ids()}),
        )
    }
    pub(super) fn inspect_material(&self) -> Result<Value, NativeSessionError> {
        Ok(
            json!({"scope":"constituted-field-reaction","epoch":self.epoch,
            "predictive_material":self.reaction.predictive_material(self.member)?.map(|m|m.inspect()).transpose()?}),
        )
    }
    fn prepare(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        commit: bool,
    ) -> Result<FieldProducingSection<'c>, NativeSessionError> {
        if input.width() != self.width || condition.components() != self.condition_width {
            return Err(invalid("field generation source/condition shape mismatch"));
        }
        let source = self.field.read_current_source()?;
        let boundary = source.enclosure().restrict(0..self.width)?;
        let reaction =
            self.reaction
                .forecast_enclosed_reaction(self.member, boundary.view(), condition)?;
        let external = input.enclosure(self.field.surface(), source.enclosure().grain())?;
        let entering = external.view().sum_same_shape(reaction.output_view())?;
        let input = if source.internal_components() == 0 {
            entering
        } else {
            entering.view().join(
                source
                    .enclosure()
                    .restrict(self.width..source.enclosure().components())?
                    .view(),
            )?
        };
        let reflected = source.reflect(input.view())?;
        let full_output = reflected.output().to_owned()?;
        let outward = full_output.view().restrict(0..self.width)?;
        if commit {
            self.field.commit_reflection(&reflected)?;
        }
        drop(reflected);
        Ok(FieldProducingSection {
            source,
            reaction,
            input,
            full_output,
            outward,
            epoch: self.epoch,
        })
    }
    pub(super) fn generate(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        commit: bool,
        retain: bool,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        if retain && !commit {
            return Err(invalid(
                "retained field comparison requires a committed generation",
            ));
        }
        let next = self
            .epoch
            .checked_add(u64::from(commit))
            .ok_or_else(|| invalid("field model epoch exhausted"))?;
        let generations = self
            .generations
            .checked_add(u64::from(commit))
            .ok_or_else(|| invalid("field generation clock exhausted"))?;
        let comparison = retain.then_some(self.next_comparison);
        let next_id = if retain {
            self.next_comparison
                .checked_add(1)
                .ok_or_else(|| invalid("field comparison identifiers exhausted"))?
        } else {
            self.next_comparison
        };
        let prepared = self.prepare(input, condition, commit)?;
        let producing = Rc::new(prepared);
        if let Some(id) = comparison {
            self.pending.insert(id, Rc::clone(&producing));
        }
        self.next_comparison = next_id;
        self.epoch = next;
        self.generations = generations;
        Ok(NativeFieldGeneratedSection {
            producing,
            comparison,
        })
    }
    pub(super) fn train_reaction(
        &mut self,
        source: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        target: ResidentNormalInput<'_, 'c>,
    ) -> Result<(), NativeSessionError> {
        let next = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("field model epoch exhausted"))?;
        let material = self
            .reaction
            .predictive_material(self.member)?
            .ok_or_else(|| invalid("absent reaction material"))?;
        let grain = material.grain();
        let source = source.enclosure(self.field.surface(), grain)?;
        let target = target.enclosure(self.field.surface(), grain)?;
        let prepared = self.reaction.prepare_enclosed_material(
            self.member,
            source.view(),
            condition,
            target.view(),
        )?;
        self.reaction.commit_field_reaction(prepared)?;
        self.epoch = next;
        Ok(())
    }
    pub(super) fn observe(
        &mut self,
        id: u64,
        target: ResidentNormalInput<'_, 'c>,
        step_bits: u32,
    ) -> Result<Value, NativeSessionError> {
        let producing = Rc::clone(
            self.pending
                .get(&id)
                .ok_or_else(|| invalid("unknown field producing comparison"))?,
        );
        let next = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("field model epoch exhausted"))?;
        let targets = self
            .targets
            .checked_add(1)
            .ok_or_else(|| invalid("field target count exhausted"))?;
        let target =
            target.enclosure(self.field.surface(), producing.source.enclosure().grain())?;
        let reflection = producing.source.reflect(producing.input.view())?;
        let returned = reflection.compare_target(target.view(), step_bits)?;
        let reaction_covector = returned.input_covector().restrict(0..self.width)?;
        let reaction = self.reaction.prepare_reaction_target(
            self.member,
            &producing.reaction,
            reaction_covector.view(),
        )?;
        if !self.reaction.can_commit_field_reaction(&reaction) {
            return Err(invalid("stale prepared reaction"));
        }
        // Read requested evidence before publication; this is the application receiver, not a
        // numerical operand in the model's update. All arithmetic above remained resident.
        let evidence = json!({"scope":"constituted-field-target","comparison":id,
            "producing_epoch":producing.epoch,"before_epoch":self.epoch,"after_epoch":next,
            "predicted":producing.outward.view().inspect()?,"target":target.view().inspect()?,
            "descending_input_covector":returned.input_covector().inspect()?,
            "step_denominator_power":step_bits,"reaction_update":"source-qualified normal proximal response"});
        self.field.apply_reflection_target(&returned,
            holonic_engine::native_ecology::constitutive_fibre::NativeContactRealization::DyadicDeposit)?;
        // &mut self excludes any intervening neighborhood update after its freshness check.
        self.reaction.commit_field_reaction(reaction)?;
        self.pending.remove(&id);
        self.targets = targets;
        self.epoch = next;
        Ok(evidence)
    }
    pub(super) fn rest(&self) -> Result<NativeFieldModelRest, NativeSessionError> {
        if !self.pending.is_empty() {
            return Err(invalid("field model rest currently requires its pending target comparisons to be resolved; they remain live"));
        }
        Ok(NativeFieldModelRest {
            field: self.field.rest(&[], &[])?,
            reaction: self.reaction.rest()?,
            member: self.member,
            epoch: self.epoch,
            generations: self.generations,
            next_comparison: self.next_comparison,
            targets: self.targets,
        })
    }
}

/// Native field and reaction material using their existing cold owners. This first local rest
/// has no outstanding target comparisons; it does not pretend to be the whole-session format.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeFieldModelRest {
    field: NativeFieldRest,
    reaction: GeneratorNeighborhoodRest,
    member: usize,
    epoch: u64,
    generations: u64,
    next_comparison: u64,
    targets: u64,
}
impl NativeFieldModelRest {
    pub(super) fn roots(&self) -> usize {
        self.field.nodes()
    }
    pub(super) fn members(&self) -> usize {
        self.reaction.members()
    }
    pub(super) fn epoch(&self) -> u64 {
        self.epoch
    }
    pub(super) fn write(&self, out: &mut impl Write) -> Result<(), NativeSessionError> {
        for value in [
            self.member as u64,
            self.epoch,
            self.generations,
            self.next_comparison,
            self.targets,
        ] {
            out.write_all(&value.to_le_bytes())?;
        }
        let mut field = Vec::new();
        self.field.write(&mut field)?;
        let mut reaction = Vec::new();
        self.reaction.write(&mut reaction)?;
        for data in [&field, &reaction] {
            out.write_all(&(data.len() as u64).to_le_bytes())?;
            out.write_all(data)?;
        }
        Ok(())
    }
    pub(super) fn read(input: &mut impl Read, octets: u64) -> Result<Self, NativeSessionError> {
        let mut input = input.take(octets);
        let number = |input: &mut dyn Read| -> Result<u64, NativeSessionError> {
            let mut bytes = [0u8; 8];
            input.read_exact(&mut bytes)?;
            Ok(u64::from_le_bytes(bytes))
        };
        let member = usize::try_from(number(&mut input)?).map_err(invalid)?;
        let epoch = number(&mut input)?;
        let generations = number(&mut input)?;
        let next_comparison = number(&mut input)?;
        let targets = number(&mut input)?;
        let count = number(&mut input)?;
        if count > input.limit() {
            return Err(invalid("truncated field model rest"));
        }
        let field = NativeFieldRest::read(&mut input, count)?;
        let count = number(&mut input)?;
        if count > input.limit() {
            return Err(invalid("truncated reaction rest"));
        }
        let reaction = GeneratorNeighborhoodRest::read(&mut input, count)?;
        if input.limit() != 0 {
            return Err(invalid("trailing field model rest bytes"));
        }
        Ok(Self {
            field,
            reaction,
            member,
            epoch,
            generations,
            next_comparison,
            targets,
        })
    }
    pub(super) fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<FieldModel<'c>, NativeSessionError> {
        let (field, _, _) = NativeConstitutiveField::remount(surface, self.field)?;
        let mut model = FieldModel::new(field, self.reaction.remount(surface)?, self.member)
            .map_err(|r| r.reason)?;
        model.epoch = self.epoch;
        model.generations = self.generations;
        model.next_comparison = self.next_comparison;
        model.targets = self.targets;
        Ok(model)
    }
}

impl<'c> NativeCoupledBody<'c> {
    /// Attach the actual operative field and its local learned reaction. Generation executes
    /// stored D and M, retaining normal-reference/gradient defects as separate comparisons.
    /// The first section contract has fixed incidence and an explicitly supplied point condition.
    pub fn from_field(
        field: NativeConstitutiveField<'c>,
        reaction: ResidentGeneratorNeighborhood<'c>,
        member: usize,
    ) -> Result<Self, NativeFieldAttachRefusal<'c>> {
        Ok(Self {
            state: Some(BodyState::Field(FieldModel::new(field, reaction, member)?)),
        })
    }
    fn field_model(&mut self) -> Result<&mut FieldModel<'c>, NativeSessionError> {
        match self.state_mut()? {
            BodyState::Field(field) => Ok(field),
            _ => Err(invalid("operation requires the constituted field body")),
        }
    }
    pub fn generate_field(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        retain: bool,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        self.field_model()?.generate(input, condition, true, retain)
    }
    pub fn preview_field(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        self.field_model()?.generate(input, condition, false, false)
    }
    pub fn train_field_reaction(
        &mut self,
        source: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        target: ResidentNormalInput<'_, 'c>,
    ) -> Result<(), NativeSessionError> {
        self.field_model()?
            .train_reaction(source, condition, target)
    }
    pub fn observe_field(
        &mut self,
        id: u64,
        target: ResidentNormalInput<'_, 'c>,
        step_bits: u32,
    ) -> Result<Value, NativeSessionError> {
        self.field_model()?.observe(id, target, step_bits)
    }
}
