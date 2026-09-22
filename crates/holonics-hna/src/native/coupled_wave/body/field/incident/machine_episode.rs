//! Ordered source entering the fixed generator machine as phase-carried moments.
//!
//! Each occurrence advances every site by its declared finite action and injects its encoded
//! increment, `q⁺ ← U_step(q⁺) + I E(u_k)` (`MachineSourceMaps::apply`). No incident word runs
//! between occurrences. Unrolled, the accumulated field is `U^N q₀ + Σ_k U^(N−1−k) I E(u_k)`: the
//! source moment carried to the final phase. Directed contacts and declared ordered offsets enter
//! as one pooled linear condition `c`. The nonlinear incident word then acts once on
//! `(q₀ + I m, b₀; c)`.
//!
//! The accumulation runs in closed form (`MachineSourceMaps::accumulate`): each cell passes once
//! through its composite phase `L^(N−1−k)` and the standing through `U^N`, which is the same
//! value as `N` applications of the per-step map with one enclosure widening per row. Its
//! adjoint returns `g_k = I* (L^(N−1−k))* g_anchor` for every occurrence from the same
//! coefficients, so no intermediate state exists to retain. A comparison keeps
//! its producing operands (accumulated field, pooled condition, clock witnesses, binding and
//! material cut id); when it is observed, the one word is read through the contemporary material
//! and field, never through a replay of earlier material versions.
use super::machine_source::{GeneratorSourceClockWitness, MachineSourceMaps};
use super::machine_source_contacts::{
    GeneratorSourceContact, pooled_source_condition, pull_back_pooled_source_condition,
    source_ports,
};
use super::*;

/// The binding, clock origin and declared relation of one ordered source passage. Its size is
/// independent of the passage except for the recorded directed contacts it names.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct GeneratorSourceMomentMeta {
    pub binding: GeneratorSourceBinding,
    pub start: u64,
    pub rows: usize,
    pub components: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub contacts: Vec<GeneratorSourceContact>,
    /// Declared ordered offsets δ, each one condition port after the contact kinds.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub offsets: Vec<usize>,
}

/// What a generated word keeps of its source: the declaration and the clock witnesses at which
/// the passage was read. The accumulated field is the word's anchor and the pooled condition is
/// its external condition; neither encoded rows nor any per-occurrence state is held.
#[derive(Clone, Debug)]
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) struct GeneratorSourceMoment {
    pub(super) meta: GeneratorSourceMomentMeta,
    witnesses: Vec<GeneratorSourceClockWitness>,
}

/// Read-only producing operands of a generator comparison, for observer readings.
#[allow(dead_code)] // read by the observer-reading consumer outside this owner
pub(crate) struct GeneratorMomentOperands<'a, 'c> {
    pub binding: &'a GeneratorSourceBinding,
    pub start: u64,
    pub rows: usize,
    pub offsets: &'a [usize],
    pub contacts: &'a [GeneratorSourceContact],
    /// First/last clock exponent of every site: the phases at which the passage was read.
    pub clock_witnesses: &'a [GeneratorSourceClockWitness],
    /// `U^N q₀ + Σ_k U^(N−1−k) I E(u_k)` joined with `b₀`, projected to the real-coded image.
    pub accumulated: ResidentNormalEnclosureView<'a, 'c>,
    /// Pooled directed contact and offset condition, `G × 12P`.
    pub condition: Option<&'a ResidentNormalEnclosureSection<'c>>,
    /// Material cut id: the incident epoch at which the word was produced.
    pub material_cut: u64,
}

fn injection_indices(
    machine: &crate::native::field_geometry::machine::CompiledGeneratorMachine,
    binding: &GeneratorSourceBinding,
) -> Result<Vec<usize>, NativeSessionError> {
    binding
        .injection_sites
        .iter()
        .map(|id| {
            machine
                .sites()
                .iter()
                .position(|site| site.id() == id)
                .ok_or_else(|| invalid("source injection site"))
        })
        .collect()
}

impl<'c> IncidentFieldModel<'c> {
    fn source_machine(
        &self,
    ) -> Result<
        &Rc<crate::native::field_geometry::machine::CompiledGeneratorMachine>,
        NativeSessionError,
    > {
        self.layout
            .machine
            .as_ref()
            .ok_or_else(|| invalid("ordered generator source requires its machine"))
    }

    /// Validate a moment declaration against this machine and return its clock witnesses.
    pub(super) fn validate_source_moment(
        &self,
        meta: &GeneratorSourceMomentMeta,
    ) -> Result<GeneratorSourceMoment, NativeSessionError> {
        let machine = self.source_machine()?;
        let witnesses = meta
            .binding
            .validate_scope(machine, meta.start, meta.rows)?;
        let ports = source_ports(&meta.binding.contact_kinds, &meta.offsets)?;
        if ports.len() != self.layout.source_condition_ports {
            return Err(invalid(
                "source contrast and offset ports differ from declared machine conditions",
            ));
        }
        if meta.components
            != meta
                .binding
                .injection_sites
                .len()
                .checked_mul(6)
                .unwrap_or(0)
        {
            return Err(invalid("generator source moment width"));
        }
        Ok(GeneratorSourceMoment {
            meta: meta.clone(),
            witnesses,
        })
    }

    /// Accumulate the passage through the source maps alone and run the incident word once.
    pub(super) fn evaluate_generator_moment(
        &self,
        source: &NativeFieldCurrentSource<'c>,
        material: &[ResidentNormalMaterialView<'c>],
        encoded: &ResidentNormalEnclosureSection<'c>,
        meta: GeneratorSourceMomentMeta,
        epoch: u64,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let machine = self.source_machine()?;
        let count = encoded.rows();
        if count == 0 || count != meta.rows || encoded.components() != meta.components {
            return Err(invalid("generator source moment rows"));
        }
        let moment = self.validate_source_moment(&meta)?;
        let maps = MachineSourceMaps::new_with_enclosure(
            self.field.surface(),
            machine,
            &meta.binding,
            meta.start,
            count,
            encoded.grain(),
            self.spec.enclosure_propagation(),
        )?;
        let injections = injection_indices(machine, &meta.binding)?;
        let ports = source_ports(&meta.binding.contact_kinds, &meta.offsets)?;
        let condition = pooled_source_condition(
            encoded,
            &injections,
            machine.sites().len(),
            &ports,
            &meta.contacts,
        )?
        .map(Rc::new);
        // Ingestion reads every cell once. The closed form applies each cell's composite
        // phase `L^(N−1−k)` directly; it equals `N` applications of `maps.apply`.
        let accumulated = maps.accumulate(source.enclosure(), encoded)?.into_output();
        let anchor = Rc::new(
            self.project_machine(accumulated.view().as_section()?)?
                .row(0)?
                .to_owned()?,
        );
        let held = vec![false; anchor.view().components() / 2];
        let admitted = self
            .layout
            .sites
            .iter()
            .map(|s| vec![true; s.sources.len()])
            .collect::<Vec<_>>();
        let (steps, output) = self.evaluate(
            source,
            material,
            &anchor,
            &held,
            &admitted,
            condition.as_deref(),
        )?;
        Ok(IncidentWord {
            source_moment: Some(moment),
            external_condition: condition,
            machine: self.layout.machine.clone(),
            source: source.retained_clone(),
            material: material.to_vec(),
            anchor,
            held,
            admitted,
            steps,
            output,
            epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
        })
    }

    /// The form a comparison retains. A moment word keeps its producing operands only: the
    /// solver iterates and the producing material views are dropped, because observation reads
    /// the word through contemporary material. Other words keep their recorded contract.
    pub(super) fn retained_comparison(
        &self,
        word: &Rc<IncidentWord<'c>>,
    ) -> Result<Rc<IncidentWord<'c>>, NativeSessionError> {
        let Some(moment) = &word.source_moment else {
            return Ok(Rc::clone(word));
        };
        Ok(Rc::new(IncidentWord {
            source_moment: Some(moment.clone()),
            external_condition: word.external_condition.clone(),
            machine: word.machine.clone(),
            source: word.source.retained_clone(),
            material: Vec::new(),
            anchor: Rc::clone(&word.anchor),
            held: word.held.clone(),
            admitted: word.admitted.clone(),
            steps: Vec::new(),
            output: word.output.view().to_owned()?,
            epoch: word.epoch,
            solver: word.solver,
            solve_steps: word.solve_steps,
            enclosure_propagation: word.enclosure_propagation,
        }))
    }

    /// Rebuild a retained moment comparison from its operands; `source` is the contemporary
    /// field and is used only for its chart extents until observation.
    pub(super) fn remount_moment_comparison(
        &self,
        meta: GeneratorSourceMomentMeta,
        source: NativeFieldCurrentSource<'c>,
        anchor: Rc<ResidentNormalEnclosure<'c>>,
        output: ResidentNormalEnclosure<'c>,
        condition: Option<ResidentNormalEnclosureSection<'c>>,
        held: Vec<bool>,
        admitted: Vec<Vec<bool>>,
        epoch: u64,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let moment = self.validate_source_moment(&meta)?;
        let joint = source.boundary_components() + source.internal_components();
        if anchor.view().components() != joint
            || output.view().components() != joint
            || held.len() != joint / 2
            || held.iter().any(|v| *v)
            || (self.layout.source_condition_ports == 0) != condition.is_none()
            || condition.as_ref().is_some_and(|c| {
                c.rows() != self.layout.sites.len()
                    || c.components() != self.layout.width * self.layout.source_condition_ports
            })
        {
            return Err(invalid("generator moment comparison chart"));
        }
        Ok(IncidentWord {
            source_moment: Some(moment),
            external_condition: condition.map(Rc::new),
            machine: self.layout.machine.clone(),
            source,
            material: Vec::new(),
            anchor,
            held,
            admitted,
            steps: Vec::new(),
            output,
            epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
        })
    }

    /// The word an observation pulls back through. A moment comparison is re-read through the
    /// contemporary field and material at its producing operands; when nothing was published in
    /// between, this is the producing word itself. Other words keep their frozen producing cut.
    pub(super) fn observed_word(
        &mut self,
        word: &Rc<IncidentWord<'c>>,
    ) -> Result<Rc<IncidentWord<'c>>, NativeSessionError> {
        let Some(moment) = &word.source_moment else {
            return Ok(Rc::clone(word));
        };
        let source = self.field.read_current_source()?;
        if source.boundary_components() + source.internal_components()
            != word.anchor.view().components()
        {
            return Err(invalid(
                "contemporary field differs from the comparison chart",
            ));
        }
        let material = self
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let (steps, output) = self.evaluate(
            &source,
            &material,
            &word.anchor,
            &word.held,
            &word.admitted,
            word.external_condition.as_deref(),
        )?;
        Ok(Rc::new(IncidentWord {
            source_moment: Some(moment.clone()),
            external_condition: word.external_condition.clone(),
            machine: self.layout.machine.clone(),
            source,
            material,
            anchor: Rc::clone(&word.anchor),
            held: word.held.clone(),
            admitted: word.admitted.clone(),
            steps,
            output,
            epoch: word.epoch,
            solver: self.spec.solver(),
            solve_steps: self.spec.solve_steps(),
            enclosure_propagation: self.spec.enclosure_propagation(),
        }))
    }

    /// The one word's adjoint, then the transposed closed-form accumulation (one covector per
    /// occurrence from the composite coefficients), plus the pooled condition transpose.
    pub(super) fn pull_back(
        &self,
        word: &IncidentWord<'c>,
        covector: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<IncidentPullback<'c>, NativeSessionError> {
        let mut returned = self.pull_back_word(word, covector)?;
        let Some(moment) = &word.source_moment else {
            return Ok(returned);
        };
        let meta = &moment.meta;
        let machine = self.source_machine()?;
        let grain = word.anchor.view().grain();
        let maps = MachineSourceMaps::new_with_enclosure(
            self.field.surface(),
            machine,
            &meta.binding,
            meta.start,
            meta.rows,
            grain,
            self.spec.enclosure_propagation(),
        )?;
        let (gradient, mut source_return) = maps
            .transposed_moment(word.anchor.view().components(), grain)?
            .pull_back(returned.anchor.view())?;
        let ports = source_ports(&meta.binding.contact_kinds, &meta.offsets)?;
        if !ports.is_empty() {
            let condition = returned
                .external_covector
                .take()
                .ok_or_else(|| invalid("source condition covector absent"))?;
            source_return = source_return.sum_same_shape(&pull_back_pooled_source_condition(
                &condition,
                meta.rows,
                &injection_indices(machine, &meta.binding)?,
                machine.sites().len(),
                &ports,
                &meta.contacts,
            )?)?;
        }
        returned.source_covector = Some(source_return);
        returned.anchor = gradient;
        Ok(returned)
    }
}

impl<'c> NativeCoupledBody<'c> {
    /// Prepare a complete ordered source passage without changing current or material.
    /// `encoded` has one original complex source row per occurrence. Its count changes the
    /// ingestion reads and the returned source covector, never the machine topology or the
    /// retained comparison. Publication uses the ordinary incident transaction.
    pub fn prepare_generator_episode(
        &mut self,
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        binding: GeneratorSourceBinding,
        start: u64,
        contacts: Vec<GeneratorSourceContact>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let offsets = binding.offsets.clone();
        self.prepare_generator_episode_with_offsets(encoded, binding, offsets, start, contacts)
    }

    /// As `prepare_generator_episode`, with declared ordered offsets δ as extra condition ports.
    pub fn prepare_generator_episode_with_offsets(
        &mut self,
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        binding: GeneratorSourceBinding,
        offsets: Vec<usize>,
        start: u64,
        contacts: Vec<GeneratorSourceContact>,
    ) -> Result<NativeIncidentGenerated<'c>, NativeSessionError> {
        let BodyState::Incident(model) = self.state_mut()? else {
            return Err(invalid(
                "generator source episode requires its incident body",
            ));
        };
        let source = model.field.read_current_source()?;
        let material = model
            .materials
            .iter()
            .map(ResidentNormalMaterial::retained_view)
            .collect::<Vec<_>>();
        let meta = GeneratorSourceMomentMeta {
            binding,
            start,
            rows: encoded.rows(),
            components: encoded.components(),
            contacts,
            offsets,
        };
        let word =
            model.evaluate_generator_moment(&source, &material, &encoded, meta, model.epoch)?;
        Ok(NativeIncidentGenerated {
            word: Rc::new(word),
            comparison: None,
        })
    }
}

#[cfg_attr(not(test), allow(dead_code))]
impl<'c> NativeIncidentGenerated<'c> {
    /// Recorded directed contacts of the source passage.
    pub fn generator_source_contacts(&self) -> Option<&[GeneratorSourceContact]> {
        self.word
            .source_moment
            .as_ref()
            .map(|m| m.meta.contacts.as_slice())
    }
    pub fn generator_source_binding(&self) -> Option<(&GeneratorSourceBinding, u64, usize, usize)> {
        self.word.source_moment.as_ref().map(|m| {
            (
                &m.meta.binding,
                m.meta.start,
                m.meta.rows,
                m.meta.components,
            )
        })
    }
    /// The producing operands of a generator word or comparison.
    pub(crate) fn generator_moment_operands(&self) -> Option<GeneratorMomentOperands<'_, 'c>> {
        self.word
            .source_moment
            .as_ref()
            .map(|m| GeneratorMomentOperands {
                binding: &m.meta.binding,
                start: m.meta.start,
                rows: m.meta.rows,
                offsets: &m.meta.offsets,
                contacts: &m.meta.contacts,
                clock_witnesses: &m.witnesses,
                accumulated: self.word.anchor.view(),
                condition: self.word.external_condition.as_deref(),
                material_cut: self.word.epoch,
            })
    }
    /// Resident sections and octets this word holds as producing operands, and the counts of
    /// solver iterates and material views it keeps. Octets are canonical rest bytes.
    pub(crate) fn retained_operand_census(&self) -> Result<Value, NativeSessionError> {
        let mut octets = self
            .word
            .anchor
            .rest()?
            .canonical_bytes()
            .map_err(invalid)?
            .len()
            + self
                .word
                .output
                .rest()?
                .canonical_bytes()
                .map_err(invalid)?
                .len();
        let mut sections = 2usize;
        if let Some(condition) = &self.word.external_condition {
            octets += condition.rest()?.canonical_bytes().map_err(invalid)?.len();
            sections += 1;
        }
        Ok(json!({"sections": sections, "octets": octets,
            "solver_iterates": self.word.steps.len(),
            "material_views": self.word.material.len(),
            "source_rows": self.word.source_moment.as_ref().map(|m| m.meta.rows)}))
    }
}

#[cfg(test)]
mod tests;
