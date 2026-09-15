//! Direct model composition on the operative field. No wave surrogate or host semantic replay.
use super::*;
use serde::{Serialize,Deserialize};
use holonic_engine::resident_section::{ResidentGrain,ResidentSectionRest};
use holonic_engine::native_ecology::constitutive_fibre::{
    ConstitutiveSourceChart, FieldReactionEnclosure, GeneratorNeighborhoodRest,
    NativeConstitutiveField, NativeFieldCurrentSource, NativeFieldCurrentSourceRest, NativeFieldRest, FieldReactionEnclosureRest,
    ResidentGeneratorNeighborhood, ResidentNormalEnclosure, ResidentNormalEnclosureView,
};
use std::{collections::BTreeMap, rc::Rc};

/// Declared restriction supplying the local reaction. The incoming boundary and the
/// continuing outgoing boundary are different physical operands of the same field model.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all="kebab-case")]
pub enum NativeFieldReactionPort { ContinuingBoundary, IncomingBoundary }

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
    reaction_port: NativeFieldReactionPort,
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
        let external = input.enclosure(self.field.surface(), source.enclosure().grain())?;
        let reaction_source = match self.reaction_port {
            NativeFieldReactionPort::ContinuingBoundary => source.enclosure().restrict(0..self.width)?,
            NativeFieldReactionPort::IncomingBoundary => external.view().to_owned()?,
        };
        let reaction = self.reaction.forecast_enclosed_reaction(self.member, reaction_source.view(), condition)?;
        let input = match self.reaction_port {
            NativeFieldReactionPort::ContinuingBoundary => reaction.apply_joint_current(source.enclosure(), external.view())?,
            NativeFieldReactionPort::IncomingBoundary => {
                let entering=reaction.incoming_with_reaction()?;
                if source.internal_components()==0 { entering } else {
                    // The new external boundary is independent of the continuing interior;
                    // the previously emitted outward current is not re-entered by this port.
                    entering.view().join(source.enclosure().restrict(self.width..source.enclosure().components())?.view())?
                }
            }
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
        let pending=self.pending.iter().map(|(id,p)|Ok(FieldPendingRest{id:*id,epoch:p.epoch,
            source:p.source.rest()?,reaction:p.reaction.rest()?,input:p.input.rest()?,output:p.full_output.rest()?})).collect::<Result<Vec<_>,NativeSessionError>>()?;
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

#[derive(Debug, PartialEq, Eq)]
struct FieldPendingRest { id:u64,epoch:u64,source:NativeFieldCurrentSourceRest,reaction:FieldReactionEnclosureRest,input:ResidentSectionRest,output:ResidentSectionRest }

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
impl NativeFieldModelRest {
    pub(super) fn has_prediction(&self,id:u64)->bool{self.pending.iter().any(|p|p.id==id)}
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
        // Absent extension retains the original continuing-boundary model bytes.
        if self.pending.is_empty() {
            if self.reaction_port==NativeFieldReactionPort::IncomingBoundary { out.write_all(&[1])?; }
        } else {
            out.write_all(&[2,u8::from(self.reaction_port==NativeFieldReactionPort::IncomingBoundary)])?;
            out.write_all(&(self.pending.len() as u64).to_le_bytes())?;
            for pending in &self.pending {
                out.write_all(&pending.id.to_le_bytes())?;out.write_all(&pending.epoch.to_le_bytes())?;
                let mut source=Vec::new();pending.source.write(&mut source)?;
                let mut reaction=Vec::new();pending.reaction.write(&mut reaction)?;
                for bytes in [source,reaction,pending.input.canonical_bytes().map_err(invalid)?,pending.output.canonical_bytes().map_err(invalid)?] {
                    out.write_all(&(bytes.len() as u64).to_le_bytes())?;out.write_all(&bytes)?;
                }
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
        let mut pending=Vec::new();
        let reaction_port=if input.limit()==0 {NativeFieldReactionPort::ContinuingBoundary} else {
            let mut mode=[0];input.read_exact(&mut mode)?;
            match mode[0] {
                1 if input.limit()==0=>NativeFieldReactionPort::IncomingBoundary,
                2=>{
                    input.read_exact(&mut mode)?;
                    let port=match mode[0]{0=>NativeFieldReactionPort::ContinuingBoundary,1=>NativeFieldReactionPort::IncomingBoundary,_=>return Err(invalid("field reaction port"))};
                    let count=number(&mut input)?;
                    if count>input.limit()/48{return Err(invalid("pending field extent"));}
                    let mut seen=std::collections::BTreeSet::new();
                    for _ in 0..count {
                        let id=number(&mut input)?;let producing_epoch=number(&mut input)?;
                        if id>=next_comparison || producing_epoch>epoch || !seen.insert(id){return Err(invalid("pending field identity/epoch"));}
                        let mut parts=Vec::new();for _ in 0..4 {
                            let count=number(&mut input)?;
                            if count>input.limit(){return Err(invalid("truncated pending field"));}
                            let mut bytes=Vec::new();bytes.try_reserve_exact(usize::try_from(count).map_err(invalid)?).map_err(invalid)?;bytes.resize(count as usize,0);input.read_exact(&mut bytes)?;parts.push(bytes);
                        }
                        pending.push(FieldPendingRest{id,epoch:producing_epoch,
                            source:NativeFieldCurrentSourceRest::read(&mut parts[0].as_slice(),parts[0].len() as u64)?,
                            reaction:FieldReactionEnclosureRest::read(&mut parts[1].as_slice(),parts[1].len() as u64)?,
                            input:ResidentSectionRest::read(&parts[2]).map_err(invalid)?,output:ResidentSectionRest::read(&parts[3]).map_err(invalid)?});
                    }
                    if input.limit()!=0{return Err(invalid("trailing pending field bytes"));}
                    port
                },
                _=>return Err(invalid("field model rest extension")),
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
        for p in self.pending {
            let source=model.field.remount_current_source(p.source)?;
            let grain=source.enclosure().grain();
            let reaction=model.reaction.remount_field_reaction(model.member,p.reaction)?;
            let input=ResidentNormalEnclosure::remount(surface,p.input,grain)?;
            let full_output=ResidentNormalEnclosure::remount(surface,p.output,grain)?;
            let reflected=source.reflect(input.view())?;
            if reflected.output().inspect()?!=full_output.inspect()? {return Err(invalid("pending output differs from producing field"));}
            drop(reflected);
            let outward=full_output.view().restrict(0..model.width)?;
            model.pending.insert(p.id,Rc::new(FieldProducingSection{source,reaction,input,full_output,outward,epoch:p.epoch}));
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
    pub fn from_field_with_reaction_port(field:NativeConstitutiveField<'c>, reaction:ResidentGeneratorNeighborhood<'c>,
        member:usize, port:NativeFieldReactionPort) -> Result<Self,NativeFieldAttachRefusal<'c>> {
        let mut model=FieldModel::new(field,reaction,member)?;
        model.reaction_port=port;
        Ok(Self{state:Some(BodyState::Field(model))})
    }
    pub fn field_dimensions(&self)->Result<(usize,usize,ResidentGrain,NativeFieldReactionPort),NativeSessionError>{
        match self.state()? {
            BodyState::Field(field)=>Ok((field.width,field.condition_width,
                field.reaction.predictive_material(field.member)?.ok_or_else(||invalid("absent reaction material"))?.grain(),field.reaction_port)),
            _=>Err(invalid("operation requires constituted field body")),
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

#[cfg(test)]
mod compatibility_tests {
    use super::*;
    use holonic_engine::embedding_fiber::ResidentReadout;

    #[test]
    #[ignore = "requires CUDA; reopens the previously delivered field model wire"]
    fn original_one_pass_field_model_remains_readable() {
        let bytes = include_bytes!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../research/experiments/athena_field/one-pass/athena-field.rest"
        ));
        let expected: Value = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../research/experiments/athena_field/one-pass/return.json"
        )))
        .unwrap();
        let rest = SavedCoupledBody::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let mut body = rest.remount(&surface).unwrap();
        assert_eq!(body.inspect_current().unwrap(), expected["model_state"]);
    }
}
