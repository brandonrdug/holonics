//! Direct model composition on the operative field. No wave surrogate or host semantic replay.
use super::*;
pub mod formation;
mod geometric;
pub mod incident;
mod section;
use holonic_engine::native_ecology::constitutive_fibre::{
    ConstitutiveSourceChart, FieldReactionEnclosure, GeneratorNeighborhoodRest,
    NativeConstitutiveField, NativeFieldCurrentSource, NativeFieldRest,
    ResidentConstitutiveCurrent, ResidentContextualSection, ResidentGeneratorNeighborhood,
    ResidentHeldSection, ResidentNormalEnclosure, ResidentNormalEnclosureView,
};
use holonic_engine::resident_section::{ResidentGrain, ResidentSectionRest};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, rc::Rc};

/// Declared restriction supplying the local reaction. The incoming boundary and the
/// continuing outgoing boundary are different physical operands of the same field model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeFieldReactionPort {
    ContinuingBoundary,
    IncomingBoundary,
}

/// One field section read at one cut: the field source it was reflected through, the reaction
/// forecast, the joint input and output, and the optional held receiver. A generation returns it
/// to its caller as a reading; a comparison's return rebuilds it at the contemporary cut. The
/// model never retains it.
struct FieldProducingSection<'c> {
    source: NativeFieldCurrentSource<'c>,
    reaction: FieldReactionEnclosure<'c>,
    input: ResidentNormalEnclosure<'c>,
    full_output: ResidentNormalEnclosure<'c>,
    outward: ResidentNormalEnclosure<'c>,
    receiver: Option<ResidentHeldSection<'c>>,
    received: Option<ResidentNormalEnclosure<'c>>,
    epoch: u64,
}

/// [definition] **A retained field comparison**: its producing operands at the boundary port —
/// the supplied input, the producing condition and the receiver's held mask — and the epoch it
/// was produced at. The field (its operative `D` and continuing current) and the reaction
/// material are read at the contemporary cut when it returns (the retention law,
/// `Holon/Retention.lean::delayed_read_eq_immediate`); no producing cut is kept.
struct FieldComparison<'c> {
    input: ResidentNormalEnclosure<'c>,
    condition: ResidentSection<'c>,
    held: Option<Vec<bool>>,
    epoch: u64,
}

/// The generated boundary and its joint construction at the generation's cut. Sharing this
/// immutable reading shares no continuing ecology. The comparison identifier is local to its
/// model owner, which retains only the comparison's producing operands.
pub struct NativeFieldGeneratedSection<'c> {
    producing: Rc<FieldProducingSection<'c>>,
    comparison: Option<u64>,
}
impl<'c> NativeFieldGeneratedSection<'c> {
    pub fn output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.producing.outward.view()
    }
    /// The requested affine receiving face; the raw boundary and joint field stay available.
    pub fn received_output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.producing
            .received
            .as_ref()
            .map_or_else(|| self.output(), |s| s.view())
    }
    pub fn joint_output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.producing.full_output.view()
    }
    /// Output of the learned local reaction at the producing source and condition. This is
    /// distinct from the reflected field boundary and remains available for source-qualified
    /// inspection by a continuing field consumer.
    pub fn reaction_output(&self) -> ResidentNormalEnclosureView<'_, 'c> {
        self.producing.reaction.output_view()
    }
    pub fn comparison_id(&self) -> Option<u64> {
        self.comparison
    }
    pub fn producing_epoch(&self) -> u64 {
        self.producing.epoch
    }
    pub fn inspect(&self) -> Result<Value, NativeSessionError> {
        let mut result = json!({"scope":"constituted-field-joint","producing_epoch":self.producing.epoch,
            "field_source_cut":self.producing.source.field_cut(),"comparison":self.comparison,
            "boundary":self.output().inspect()?,"joint":self.joint_output().inspect()?});
        if let Some(receiver) = &self.producing.receiver {
            result["received_boundary"] = json!(self.received_output().inspect()?);
            result["held_coordinates"] = json!(receiver.held());
        }
        Ok(result)
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
    reaction_port: NativeFieldReactionPort,
    epoch: u64,
    generations: u64,
    next_comparison: u64,
    targets: u64,
    pending: BTreeMap<u64, FieldComparison<'c>>,
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
                });
            }
        };
        Ok(Self {
            field,
            reaction,
            member,
            width,
            condition_width,
            reaction_port: NativeFieldReactionPort::ContinuingBoundary,
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
    /// The field section of a supplied boundary input at the contemporary field and reaction
    /// material. A generation and a comparison's return are this one computation.
    fn prepare(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        commit: bool,
        held: Option<&[bool]>,
    ) -> Result<FieldProducingSection<'c>, NativeSessionError> {
        if input.width() != self.width || condition.components() != self.condition_width {
            return Err(invalid("field generation source/condition shape mismatch"));
        }
        let source = self.field.read_current_source()?;
        let external = input.enclosure(self.field.surface(), source.enclosure().grain())?;
        self.prepare_at(source, external, condition, commit, held)
    }
    fn prepare_at(
        &mut self,
        source: NativeFieldCurrentSource<'c>,
        external: ResidentNormalEnclosure<'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        commit: bool,
        held: Option<&[bool]>,
    ) -> Result<FieldProducingSection<'c>, NativeSessionError> {
        if external.view().components() != self.width
            || condition.components() != self.condition_width
        {
            return Err(invalid("field generation source/condition shape mismatch"));
        }
        let receiver = held
            .map(|mask| ResidentHeldSection::found(external.view(), mask))
            .transpose()?;
        let reaction_source = match self.reaction_port {
            NativeFieldReactionPort::ContinuingBoundary => {
                source.enclosure().restrict(0..self.width)?
            }
            NativeFieldReactionPort::IncomingBoundary => external.view().to_owned()?,
        };
        let reaction = self.reaction.forecast_enclosed_reaction(
            self.member,
            reaction_source.view(),
            condition,
        )?;
        let input = match self.reaction_port {
            NativeFieldReactionPort::ContinuingBoundary => {
                reaction.apply_joint_current(source.enclosure(), external.view())?
            }
            NativeFieldReactionPort::IncomingBoundary => {
                let entering = reaction.incoming_with_reaction()?;
                if source.internal_components() == 0 {
                    entering
                } else {
                    // The new external boundary is independent of the continuing interior;
                    // the previously emitted outward current is not re-entered by this port.
                    entering.view().join(
                        source
                            .enclosure()
                            .restrict(self.width..source.enclosure().components())?
                            .view(),
                    )?
                }
            }
        };
        let reflected = source.reflect(input.view())?;
        let full_output = reflected.output().to_owned()?;
        let outward = full_output.view().restrict(0..self.width)?;
        let received = receiver
            .as_ref()
            .map(|r| r.receive(outward.view()))
            .transpose()?;
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
            receiver,
            received,
            epoch: self.epoch,
        })
    }
    pub(super) fn generate(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        commit: bool,
        retain: bool,
        held: Option<&[bool]>,
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
        if input.width() != self.width || condition.components() != self.condition_width {
            return Err(invalid("field generation source/condition shape mismatch"));
        }
        let source = self.field.read_current_source()?;
        let external = input.enclosure(self.field.surface(), source.enclosure().grain())?;
        // The comparison retains its producing operands only; its return re-reads the field.
        let retained = match comparison {
            Some(_) => Some(FieldComparison {
                input: external.view().to_owned()?,
                condition: condition.to_owned(self.field.surface())?,
                held: held.map(<[bool]>::to_vec),
                epoch: self.epoch,
            }),
            None => None,
        };
        let producing = Rc::new(self.prepare_at(source, external, condition, commit, held)?);
        if let (Some(id), Some(retained)) = (comparison, retained) {
            self.pending.insert(id, retained);
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
    /// Return comparison `id` at the contemporary cut: its retained operands (input, producing
    /// condition, held mask) are read through the current field `D`, continuing current and
    /// reaction material, the target is compared at that section, and its covector returns
    /// through those same operands. A delayed return therefore equals an immediate return of a
    /// comparison with the same operands at the same constitution, number for number.
    pub(super) fn observe(
        &mut self,
        id: u64,
        target: ResidentNormalInput<'_, 'c>,
        step_bits: u32,
    ) -> Result<Value, NativeSessionError> {
        let comparison = self
            .pending
            .remove(&id)
            .ok_or_else(|| invalid("unknown field producing comparison"))?;
        let returned = self.observe_comparison(id, &comparison, target, step_bits);
        if returned.is_err() {
            self.pending.insert(id, comparison);
        }
        returned
    }
    fn observe_comparison(
        &mut self,
        id: u64,
        comparison: &FieldComparison<'c>,
        target: ResidentNormalInput<'_, 'c>,
        step_bits: u32,
    ) -> Result<Value, NativeSessionError> {
        let next = self
            .epoch
            .checked_add(1)
            .ok_or_else(|| invalid("field model epoch exhausted"))?;
        let targets = self
            .targets
            .checked_add(1)
            .ok_or_else(|| invalid("field target count exhausted"))?;
        let source = self.field.read_current_source()?;
        let producing = self.prepare_at(
            source,
            comparison.input.view().to_owned()?,
            ResidentConstitutiveCurrent::rational(&comparison.condition)?,
            false,
            comparison.held.as_deref(),
        )?;
        let target =
            target.enclosure(self.field.surface(), producing.source.enclosure().grain())?;
        let reflection = producing.source.reflect(producing.input.view())?;
        if step_bits > 120 {
            return Err(invalid("target step leaves the native dyadic carrier"));
        }
        if target.view().components() == 0 || target.view().components() % 2 != 0 {
            return Err(invalid("target must retain complete complex coordinates"));
        }
        let predicted = producing.received.as_ref().unwrap_or(&producing.outward);
        let held_difference = if let Some(receiver) = &producing.receiver {
            let given = receiver.given().inspect()?;
            let t = target.inspect()?;
            let differences = given
                .center
                .iter()
                .zip(&t.center)
                .zip(receiver.held())
                .enumerate()
                .filter_map(|(i, ((a, b), held))| {
                    held.then(|| json!({"coordinate":i,"difference":b.subtract(a)}))
                })
                .collect::<Vec<_>>();
            let radius = if differences.is_empty() {
                given.radius.clone() - given.radius
            } else {
                given.radius + t.radius
            };
            json!({"coordinates":differences,"radius":radius,"scope":"target minus supplied fixed source; only target-covered held coordinates"})
        } else {
            Value::Null
        };
        // A target observing only fixed source coordinates has no D/M derivative.
        if producing.receiver.as_ref().is_some_and(|r| {
            target.view().components() <= self.width
                && r.held()[..target.view().components() / 2]
                    .iter()
                    .all(|v| *v)
        }) {
            let evidence = json!({"scope":"constituted-field-target","comparison":id,"producing_epoch":comparison.epoch,
                "comparison_cut":"contemporary",
                "before_epoch":self.epoch,"after_epoch":next,"predicted":predicted.inspect()?,"target":target.inspect()?,
                "held_difference":held_difference,"parameter_update":"zero: target covers fixed receiving coordinates"});
            self.targets = targets;
            self.epoch = next;
            return Ok(evidence);
        }
        let returned = match &producing.receiver {
            Some(receiver) => {
                reflection.compare_received_target(target.view(), step_bits, receiver)?
            }
            None => reflection.compare_target(target.view(), step_bits)?,
        };
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
        let mut evidence = json!({"scope":"constituted-field-target","comparison":id,
            "producing_epoch":comparison.epoch,"comparison_cut":"contemporary",
            "before_epoch":self.epoch,"after_epoch":next,
            "predicted":predicted.inspect()?,"target":target.view().inspect()?,
            "descending_input_covector":returned.input_covector().inspect()?,
            "step_denominator_power":step_bits,"reaction_update":"source-qualified normal proximal response"});
        if producing.receiver.is_some() {
            evidence["held_difference"] = held_difference;
        }
        self.field.apply_reflection_target(&returned,
            holonic_engine::native_ecology::constitutive_fibre::NativeContactRealization::DyadicDeposit)?;
        // &mut self excludes any intervening neighborhood update after its freshness check.
        self.reaction.commit_field_reaction(reaction)?;
        self.targets = targets;
        self.epoch = next;
        Ok(evidence)
    }
    pub(super) fn rest(&self) -> Result<NativeFieldModelRest, NativeSessionError> {
        let pending = self
            .pending
            .iter()
            .map(|(id, p)| {
                Ok(FieldPendingRest {
                    id: *id,
                    epoch: p.epoch,
                    input: p.input.rest()?,
                    condition: self
                        .field
                        .surface()
                        .detach_section(&p.condition, 64)
                        .map_err(invalid)?,
                    held: p.held.clone(),
                })
            })
            .collect::<Result<Vec<_>, NativeSessionError>>()?;
        Ok(NativeFieldModelRest {
            field: self.field.rest(&[], &[])?,
            reaction: self.reaction.rest()?,
            member: self.member,
            reaction_port: self.reaction_port,
            epoch: self.epoch,
            generations: self.generations,
            next_comparison: self.next_comparison,
            targets: self.targets,
            pending,
        })
    }
}

/// One current-format outstanding comparison at rest. Extension `4` stores only its producing
/// operands; extensions `2` and `3` stored a frozen producing cut and are superseded formats.
#[derive(Debug, PartialEq, Eq)]
struct FieldPendingRest {
    id: u64,
    epoch: u64,
    input: ResidentSectionRest,
    condition: ResidentSectionRest,
    held: Option<Vec<bool>>,
}

/// Native field, reaction and outstanding producing comparisons using their existing cold
/// owners. Session codecs and transport cursors belong to the exterior field-session rest.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeFieldModelRest {
    field: NativeFieldRest,
    reaction: GeneratorNeighborhoodRest,
    member: usize,
    reaction_port: NativeFieldReactionPort,
    epoch: u64,
    generations: u64,
    next_comparison: u64,
    targets: u64,
    pending: Vec<FieldPendingRest>,
}
fn field_blob(out: &mut impl Write, bytes: &[u8]) -> Result<(), NativeSessionError> {
    out.write_all(&(bytes.len() as u64).to_le_bytes())?;
    out.write_all(bytes)?;
    Ok(())
}
impl NativeFieldModelRest {
    pub(super) fn has_prediction(&self, id: u64) -> bool {
        self.pending.iter().any(|p| p.id == id)
    }
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
            field_blob(out, data)?;
        }
        // Absent extension retains the original continuing-boundary model bytes.
        if self.pending.is_empty() {
            if self.reaction_port == NativeFieldReactionPort::IncomingBoundary {
                out.write_all(&[1])?;
            }
        } else {
            out.write_all(&[
                4,
                u8::from(self.reaction_port == NativeFieldReactionPort::IncomingBoundary),
            ])?;
            out.write_all(&(self.pending.len() as u64).to_le_bytes())?;
            for pending in &self.pending {
                out.write_all(&pending.id.to_le_bytes())?;
                out.write_all(&pending.epoch.to_le_bytes())?;
                field_blob(out, &pending.input.canonical_bytes().map_err(invalid)?)?;
                field_blob(out, &pending.condition.canonical_bytes().map_err(invalid)?)?;
                let mask = pending.held
                    .as_ref()
                    .map(|mask| mask.iter().map(|v| u8::from(*v)).collect::<Vec<_>>())
                    .unwrap_or_default();
                field_blob(out, &mask)?;
            }
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
        let mut pending = Vec::new();
        let reaction_port = if input.limit() == 0 {
            NativeFieldReactionPort::ContinuingBoundary
        } else {
            let mut mode = [0];
            input.read_exact(&mut mode)?;
            match mode[0] {
                1 if input.limit() == 0 => NativeFieldReactionPort::IncomingBoundary,
                4 => {
                    input.read_exact(&mut mode)?;
                    let port = match mode[0] {
                        0 => NativeFieldReactionPort::ContinuingBoundary,
                        1 => NativeFieldReactionPort::IncomingBoundary,
                        _ => return Err(invalid("field reaction port")),
                    };
                    let count = number(&mut input)?;
                    if count > input.limit() / 48 {
                        return Err(invalid("pending field extent"));
                    }
                    let mut seen = std::collections::BTreeSet::new();
                    for _ in 0..count {
                        let id = number(&mut input)?;
                        let producing_epoch = number(&mut input)?;
                        if id >= next_comparison || producing_epoch > epoch || !seen.insert(id) {
                            return Err(invalid("pending field identity/epoch"));
                        }
                        let mut blobs = Vec::new();
                        for _ in 0..3 {
                            let count = number(&mut input)?;
                            if count > input.limit() {
                                return Err(invalid("truncated pending field"));
                            }
                            let mut bytes = Vec::new();
                            bytes
                                .try_reserve_exact(usize::try_from(count).map_err(invalid)?)
                                .map_err(invalid)?;
                            bytes.resize(count as usize, 0);
                            input.read_exact(&mut bytes)?;
                            blobs.push(bytes);
                        }
                        let held = if blobs[2].is_empty() {
                            None
                        } else if blobs[2].iter().all(|b| *b <= 1) {
                            Some(blobs[2].iter().map(|b| *b == 1).collect())
                        } else {
                            return Err(invalid("pending field receiver mask"));
                        };
                        pending.push(FieldPendingRest {
                            id,
                            epoch: producing_epoch,
                            input: ResidentSectionRest::read(&blobs[0]).map_err(invalid)?,
                            condition: ResidentSectionRest::read(&blobs[1]).map_err(invalid)?,
                            held,
                        });
                    }
                    if input.limit() != 0 {
                        return Err(invalid("trailing pending field bytes"));
                    }
                    port
                }
                _ => return Err(invalid("field model rest extension")),
            }
        };
        Ok(Self {
            field,
            reaction,
            member,
            reaction_port,
            epoch,
            generations,
            next_comparison,
            targets,
            pending,
        })
    }
    pub(super) fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
    ) -> Result<FieldModel<'c>, NativeSessionError> {
        let (field, _, _) = NativeConstitutiveField::remount(surface, self.field)?;
        let mut model = FieldModel::new(field, self.reaction.remount(surface)?, self.member)
            .map_err(|r| r.reason)?;
        model.reaction_port = self.reaction_port;
        model.epoch = self.epoch;
        model.generations = self.generations;
        model.next_comparison = self.next_comparison;
        model.targets = self.targets;
        let grain = model.field.read_current_source()?.enclosure().grain();
        for p in self.pending {
            let input = ResidentNormalEnclosure::remount(surface, p.input, grain)?;
            let condition = surface.mount_section_rest(&p.condition).map_err(invalid)?;
            let comparison = FieldComparison {
                input,
                condition,
                held: p.held,
                epoch: p.epoch,
            };
            if comparison.input.view().components() != model.width
                || comparison
                    .held
                    .as_ref()
                    .is_some_and(|mask| mask.len() != model.width / 2)
            {
                return Err(invalid("pending field operand chart"));
            }
            model.pending.insert(p.id, comparison);
        }
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
    /// Found the same field with an explicit incoming or continuing reaction source.
    pub fn from_field_with_reaction_port(
        field: NativeConstitutiveField<'c>,
        reaction: ResidentGeneratorNeighborhood<'c>,
        member: usize,
        port: NativeFieldReactionPort,
    ) -> Result<Self, NativeFieldAttachRefusal<'c>> {
        let mut model = FieldModel::new(field, reaction, member)?;
        model.reaction_port = port;
        Ok(Self {
            state: Some(BodyState::Field(model)),
        })
    }
    pub fn field_dimensions(
        &self,
    ) -> Result<(usize, usize, ResidentGrain, NativeFieldReactionPort), NativeSessionError> {
        match self.state()? {
            BodyState::Field(field) => Ok((
                field.width,
                field.condition_width,
                field
                    .reaction
                    .predictive_material(field.member)?
                    .ok_or_else(|| invalid("absent reaction material"))?
                    .grain(),
                field.reaction_port,
            )),
            _ => Err(invalid("operation requires constituted field body")),
        }
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
        self.field_model()?
            .generate(input, condition, true, retain, None)
    }

    /// Generate from the condition currently held by the field neighborhood. The point current
    /// is snapshotted in resident material before the mutable field passage begins.
    pub fn generate_field_standing(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        commit: bool,
        retain: bool,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        self.field_model()?
            .generate_standing(input, commit, retain, None)
    }
    pub fn preview_field(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        self.field_model()?
            .generate(input, condition, false, false, None)
    }
    /// Generate the raw field and its declared affine receiver without changing field publication.
    pub fn generate_received_field(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        held: &[bool],
        commit: bool,
        retain: bool,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        self.field_model()?
            .generate(input, condition, commit, retain, Some(held))
    }

    /// Standing-condition counterpart to [`Self::generate_received_field`].
    pub fn generate_received_field_standing(
        &mut self,
        input: ResidentNormalInput<'_, 'c>,
        held: &[bool],
        commit: bool,
        retain: bool,
    ) -> Result<NativeFieldGeneratedSection<'c>, NativeSessionError> {
        self.field_model()?
            .generate_standing(input, commit, retain, Some(held))
    }

    /// Read the actual condition current that the field neighborhood will use next.
    pub fn field_standing_condition(
        &self,
    ) -> Result<ResidentConstitutiveCurrent<'_, 'c>, NativeSessionError> {
        match self.state()? {
            BodyState::Field(field) => field.standing_condition(),
            _ => Err(invalid("operation requires constituted field body")),
        }
    }

    /// Derive the fixed-source contextual relation at an exact resident source current.
    pub fn field_contextual_section(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentContextualSection<'c>, NativeSessionError> {
        match self.state()? {
            BodyState::Field(field) => field.contextual_section(source),
            _ => Err(invalid("operation requires constituted field body")),
        }
    }

    /// Transport the latest retained condition fibre through this member at a new source.
    /// Its joint image keeps the supported condition/output correlation and domain coverage.
    pub fn field_condition_image(
        &self,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<
        holonic_engine::native_ecology::constitutive_fibre::ResidentConditionImage<'c>,
        NativeSessionError,
    > {
        match self.state()? {
            BodyState::Field(field) => {
                let evidence = field
                    .reaction
                    .last_received_evidence()
                    .ok_or_else(|| invalid("no received field condition family"))?;
                Ok(field
                    .reaction
                    .generator(field.member)?
                    .read_condition_image(source, &evidence.family)?)
            }
            _ => Err(invalid("operation requires constituted field body")),
        }
    }

    /// Form one actual source/condition/target passage through the same neighborhood used by
    /// field generation. The receipt separates the original producing condition from the
    /// contemporary standing and retains the complete returned condition family.
    pub fn form_field_reaction_at<'a>(
        &mut self,
        source: ResidentConstitutiveCurrent<'a, 'c>,
        condition: ResidentConstitutiveCurrent<'a, 'c>,
        target: ResidentConstitutiveCurrent<'a, 'c>,
    ) -> Result<NativeFieldFormation<'a, 'c>, NativeSessionError>
    where
        'c: 'a,
    {
        self.field_model()?.form_reaction(source, condition, target)
    }

    /// The latest condition-family evidence published by the field neighborhood.
    pub fn field_last_evidence(
        &self,
    ) -> Option<&holonic_engine::native_ecology::constitutive_fibre::NeighborhoodEvidence<'c>> {
        match self.state.as_ref()? {
            BodyState::Field(field) => field.last_evidence(),
            BodyState::Affine(_) | BodyState::Constitutive(_) | BodyState::Incident(_) => None,
        }
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

#[cfg(test)]
mod field_tests {
    use super::*;
    use holonic_engine::embedding_fiber::ResidentReadout;
    use holonic_engine::native_ecology::constitutive_fibre::{
        ConditionContactMetric, NativeFieldOccurrence, NativeJunctionSeed, NativePhaseCurrent,
        ResidentConstitutiveFibre, ResidentNormalMaterial,
    };

    fn current_field_body<'c>(surface: &'c ResidentSurface<'c>) -> NativeCoupledBody<'c> {
        let nodes = 2;
        let context = 2;
        let source_complex = 3 * nodes;
        let features = source_complex * context + source_complex + context;
        let grain = ResidentGrain(32);
        let seed = NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        let mut field = NativeConstitutiveField::found_with_enclosed_junction(
            surface,
            vec![seed; nodes],
            grain,
        )
        .unwrap();
        let first = field
            .advance_resident(&mut NativeFieldOccurrence::entering(vec![
                NativePhaseCurrent::unit();
                nodes
            ]))
            .unwrap();
        field
            .advance_resident(&mut NativeFieldOccurrence::through(
                first.source,
                vec![NativePhaseCurrent::new(0, 1, 1).unwrap(); nodes],
            ))
            .unwrap();
        let initial = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    2 * context,
                    ResidentGrain(0),
                    64,
                    vec![(0, 0); 2 * context],
                )
                .unwrap(),
            )
            .unwrap();
        let law = ResidentConstitutiveFibre::found_bilinear_contact(
            surface,
            source_complex,
            context,
            source_complex,
        )
        .unwrap();
        let material = ResidentNormalMaterial::found_features(
            surface,
            features,
            source_complex,
            grain,
        )
        .unwrap();
        let mut reaction = ResidentGeneratorNeighborhood::with_shared_condition(
            vec![law],
            ResidentConstitutiveCurrent::integers(&initial).unwrap(),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
        reaction.attach_normal_prediction(0, material).map_err(|r| r.reason).unwrap();
        NativeCoupledBody::from_field_with_reaction_port(
            field,
            reaction,
            0,
            NativeFieldReactionPort::IncomingBoundary,
        )
        .map_err(|r| r.reason)
        .unwrap()
    }

    fn point<'c>(surface: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
        surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    v.len(),
                    ResidentGrain(0),
                    64,
                    v.iter().map(|x| (*x, *x)).collect(),
                )
                .unwrap(),
            )
            .unwrap()
    }
    fn saved(body: &NativeCoupledBody<'_>) -> Vec<u8> {
        let mut bytes = Vec::new();
        body.rest().unwrap().write(&mut bytes).unwrap();
        bytes
    }
    fn reopen<'c>(surface: &'c ResidentSurface<'c>, bytes: &[u8]) -> NativeCoupledBody<'c> {
        SavedCoupledBody::read(&mut &bytes[..], bytes.len() as u64)
            .unwrap()
            .remount(surface)
            .unwrap()
    }
    /// Return `id` against `target` and read what the return did: its evidence without the
    /// comparison's own identity and producing epoch, and the field and reaction after it.
    fn returned<'c>(
        surface: &'c ResidentSurface<'c>,
        bytes: &[u8],
        id: u64,
        target: &[i64],
    ) -> (Value, Value, Value) {
        let mut body = reopen(surface, bytes);
        let target = point(surface, target);
        let mut evidence = body
            .observe_field(
                id,
                ResidentConstitutiveCurrent::integers(&target).unwrap().into(),
                3,
            )
            .unwrap();
        for key in ["comparison", "producing_epoch"] {
            evidence.as_object_mut().unwrap().remove(key);
        }
        let mut current = body.inspect_current().unwrap();
        current.as_object_mut().unwrap().remove("pending");
        (evidence, current, body.inspect_predictive_material(0).unwrap())
    }

    /// **Retention law, constituted field.** A comparison retains its input, producing condition
    /// and held mask. After the field and its reaction material move, its delayed return equals,
    /// number for number, the return of a fresh comparison of the same operands produced at the
    /// latest cut: both are read through the contemporary `D`, continuing current and `M`.
    #[test]
    #[ignore = "requires CUDA; a delayed field return equals an immediate return of the same operands at the same constitution"]
    fn delayed_field_return_equals_an_immediate_return_at_the_same_constitution() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let mut body = current_field_body(&surface);
        fn generate<'c>(
            surface: &'c ResidentSurface<'c>,
            body: &mut NativeCoupledBody<'c>,
            [a, b]: [i64; 2],
        ) -> u64 {
            let (width, condition_width, _, _) = body.field_dimensions().unwrap();
            let pattern = [a, b, -b, a, a + b, b - a];
            let input = (0..width)
                .map(|index| pattern[index % pattern.len()])
                .collect::<Vec<_>>();
            let condition = (0..condition_width)
                .map(|index| [a, b][index % 2])
                .collect::<Vec<_>>();
            let (x, c) = (
                point(surface, &input),
                point(surface, &condition),
            );
            body.generate_field(
                ResidentConstitutiveCurrent::integers(&x).unwrap().into(),
                ResidentConstitutiveCurrent::integers(&c).unwrap(),
                true,
            )
            .unwrap()
            .comparison_id()
            .unwrap()
        }
        let delayed = generate(&surface, &mut body, [1, 0]);
        // The constitution moves: another comparison is produced and returned.
        let other = generate(&surface, &mut body, [0, 1]);
        let (width, _, _, _) = body.field_dimensions().unwrap();
        let target_pattern = [-1, 0, 0, 1, -1, 1];
        let target_values = (0..width)
            .map(|index| target_pattern[index % target_pattern.len()])
            .collect::<Vec<_>>();
        let t = point(&surface, &target_values);
        body.observe_field(
            other,
            ResidentConstitutiveCurrent::integers(&t).unwrap().into(),
            3,
        )
        .unwrap();
        let immediate = generate(&surface, &mut body, [1, 0]);
        let cut = saved(&body);
        let final_pattern = [0, 1, -1, 0, -1, -1];
        let target = (0..width)
            .map(|index| final_pattern[index % final_pattern.len()])
            .collect::<Vec<_>>();
        let delayed = returned(&surface, &cut, delayed, &target);
        let immediate = returned(&surface, &cut, immediate, &target);
        assert_eq!(delayed.0, immediate.0, "returned evidence at the one cut");
        assert_eq!(delayed.1, immediate.1, "the field after the return");
        assert_eq!(delayed.2, immediate.2, "the reaction material after the return");
    }

}
