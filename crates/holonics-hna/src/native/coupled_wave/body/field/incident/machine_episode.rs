//! Ordered source-driven recurrence over the same fixed-machine word.
//!
//! An occurrence advances the previous boundary in each declared generator clock,
//! adds its encoded current increments, and executes the ordinary nonlinear incident word.
//! We retain that ordered producing tape until a comparison returns. No moment descent or
//! source-length-independent ingestion/pending cost is asserted.
use super::machine_source::{GeneratorInjection, MachineSourceMaps};
use super::machine_source_contacts::{GeneratorSourceContact, GeneratorSourceContacts};
use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct GeneratorEpisodeMeta {
    pub binding: GeneratorSourceBinding,
    pub start: u64,
    pub rows: usize,
    pub components: usize,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub contacts: Vec<GeneratorSourceContact>,
}
pub(super) struct GeneratorEpisodeStage<'c> {
    word: IncidentWord<'c>,
    injection: GeneratorInjection<'c>,
}
pub(super) struct GeneratorEpisodeTape<'c> {
    pub meta: GeneratorEpisodeMeta,
    pub encoded: Rc<ResidentNormalEnclosureSection<'c>>,
    prefix: Vec<GeneratorEpisodeStage<'c>>,
    last: GeneratorInjection<'c>,
    contacts: Option<GeneratorSourceContacts<'c>>,
}

impl<'c> IncidentFieldModel<'c> {
    /// One baseline D and one producing material cut serve every ordered occurrence.
    /// This same routine reconstructs the tape at its frozen rest cut.
    pub(super) fn evaluate_generator_episode(
        &self,
        source: &NativeFieldCurrentSource<'c>,
        material: &[ResidentNormalMaterialView<'c>],
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        binding: GeneratorSourceBinding,
        start: u64,
        epoch: u64,
        contacts: Vec<GeneratorSourceContact>,
    ) -> Result<IncidentWord<'c>, NativeSessionError> {
        let machine = self
            .layout
            .machine
            .as_ref()
            .ok_or_else(|| invalid("ordered generator source requires its machine"))?;
        let count = encoded.rows();
        if count == 0 {
            return Err(invalid("empty generator source episode"));
        }
        let maps = MachineSourceMaps::new(
            self.field.surface(),
            machine,
            &binding,
            start,
            count,
            encoded.grain(),
        )?;
        if binding.contact_kinds.len() != self.layout.source_condition_ports {
            return Err(invalid(
                "source contrast ports differ from declared machine conditions",
            ));
        }
        let injection_indices = binding
            .injection_sites
            .iter()
            .map(|id| {
                machine
                    .sites()
                    .iter()
                    .position(|site| site.id() == id)
                    .ok_or_else(|| invalid("source injection site"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let contact_map = GeneratorSourceContacts::new(
            encoded.clone(),
            &injection_indices,
            machine.sites().len(),
            &binding.contact_kinds,
            &contacts,
        )?;
        let meta = GeneratorEpisodeMeta {
            binding,
            start,
            rows: count,
            components: encoded.components(),
            contacts,
        };
        let mut previous = source.enclosure().to_owned()?;
        let held = vec![false; previous.view().components() / 2];
        let admitted = self
            .layout
            .sites
            .iter()
            .map(|s| vec![true; s.sources.len()])
            .collect::<Vec<_>>();
        let mut prefix = Vec::new();
        prefix.try_reserve(count - 1).map_err(invalid)?;
        for k in 0..count {
            let row = Rc::new(encoded.row(k)?.as_section()?);
            let injection = maps.apply(previous.view(), row)?;
            let anchor = Rc::new(
                self.project_machine(injection.output().as_section()?)?
                    .row(0)?
                    .to_owned()?,
            );
            let external_condition = contact_map
                .as_ref()
                .map(|map| map.output(k).map(Rc::new))
                .transpose()?;
            let (steps, output) = self.evaluate(
                source,
                material,
                &anchor,
                &held,
                &admitted,
                external_condition.as_deref(),
            )?;
            let mut word = IncidentWord {
                source_episode: None,
                external_condition,
                machine: self.layout.machine.clone(),
                source: source.retained_clone(),
                material: material.to_vec(),
                anchor,
                held: held.clone(),
                admitted: admitted.clone(),
                steps,
                output,
                epoch,
                solver: self.spec.solver(),
                solve_steps: self.spec.solve_steps(),
            };
            if k + 1 == count {
                word.source_episode = Some(GeneratorEpisodeTape {
                    meta,
                    encoded,
                    prefix,
                    last: injection,
                    contacts: contact_map,
                });
                return Ok(word);
            }
            previous = word.output.view().to_owned()?;
            prefix.push(GeneratorEpisodeStage { word, injection });
        }
        Err(invalid("empty generator source episode"))
    }

    /// Compose the full fixed-word adjoint with every preceding injection and word.
    /// Normal feature/covector rows are accumulated before contemporary material is staged.
    pub(super) fn pull_back(
        &self,
        word: &IncidentWord<'c>,
        covector: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<IncidentPullback<'c>, NativeSessionError> {
        let mut returned = self.pull_back_word(word, covector)?;
        if let Some(tape) = &word.source_episode {
            let (mut previous, last_source) = tape.last.pull_back(returned.anchor.view())?;
            let mut source_rows = vec![last_source];
            let mut condition_rows = Vec::new();
            if tape.contacts.is_some() {
                condition_rows.push(
                    returned
                        .external_covector
                        .take()
                        .ok_or_else(|| invalid("source condition covector absent"))?,
                );
            }
            for stage in tape.prefix.iter().rev() {
                let mut stage_return = self.pull_back_word(&stage.word, previous.view())?;
                if tape.contacts.is_some() {
                    condition_rows.push(
                        stage_return
                            .external_covector
                            .take()
                            .ok_or_else(|| invalid("source condition covector absent"))?,
                    );
                }
                for (all, mut rows) in returned.material.iter_mut().zip(stage_return.material) {
                    all.append(&mut rows);
                }
                returned.contacts.extend(stage_return.contacts);
                let (before, source) = stage.injection.pull_back(stage_return.anchor.view())?;
                previous = before;
                source_rows.push(source);
            }
            source_rows.reverse();
            let mut source_return = ResidentNormalEnclosureSection::concatenate_rows(
                &source_rows.iter().collect::<Vec<_>>(),
            )?;
            if let Some(contacts) = &tape.contacts {
                condition_rows.reverse();
                let covectors = ResidentNormalEnclosureSection::concatenate_rows(
                    &condition_rows.iter().collect::<Vec<_>>(),
                )?;
                source_return = source_return.sum_same_shape(&contacts.pull_back(&covectors)?)?;
            }
            returned.source_covector = Some(source_return);
            returned.anchor = previous;
        }
        Ok(returned)
    }
}

impl<'c> NativeCoupledBody<'c> {
    /// Prepare a complete ordered source episode without changing current or material.
    /// `encoded` has one original complex source row per occurrence. Its count changes the
    /// ingestion/reverse tape, never the machine topology. Publication uses the ordinary
    /// incident transaction, and source covectors return from that same comparison.
    pub fn prepare_generator_episode(
        &mut self,
        encoded: Rc<ResidentNormalEnclosureSection<'c>>,
        binding: GeneratorSourceBinding,
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
        let word = model.evaluate_generator_episode(
            &source,
            &material,
            encoded,
            binding,
            start,
            model.epoch,
            contacts,
        )?;
        Ok(NativeIncidentGenerated {
            word: Rc::new(word),
            comparison: None,
        })
    }
}

impl NativeIncidentGenerated<'_> {
    /// Source clock and encoded chart of the retained episode, without reading numeric rows.
    pub fn generator_source_contacts(&self) -> Option<&[GeneratorSourceContact]> {
        self.word
            .source_episode
            .as_ref()
            .map(|t| t.meta.contacts.as_slice())
    }
    pub fn generator_source_binding(&self) -> Option<(&GeneratorSourceBinding, u64, usize, usize)> {
        self.word.source_episode.as_ref().map(|t| {
            (
                &t.meta.binding,
                t.meta.start,
                t.meta.rows,
                t.meta.components,
            )
        })
    }
}

#[cfg(test)]
mod tests;
