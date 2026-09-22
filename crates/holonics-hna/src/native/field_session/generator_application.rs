//! Ordered source and shared phase reception on the fixed generator body.
use super::boundary::BoundaryMaterial;
use super::incident_encoder::{IncidentEncoded, IncidentEncoder};
use super::incident_receiver::{IncidentTextForward, phase::GeneratorTextReceiver};
use super::*;
use crate::native::{
    GeneratorIncidentFieldSpec, GeneratorPhaseReceiverBinding, GeneratorSourceBinding,
    GeneratorSourceContact, GeneratorSourceContactKind, NativeGeneratorPhaseReception,
};
use holonic_engine::native_ecology::constitutive_fibre::{
    BoundaryMaterialSeed, ResidentNormalEnclosureSection,
};
use holonic_engine::resident_section::SeriesAperture;
use std::rc::Rc;
mod codec;
mod rest;
#[cfg(test)]
mod tests;
pub(super) use rest::GeneratorPresentationRest;

/// The source and receiving clocks are declared boundaries of one fixed machine. The last
/// receiving row supplies termination at the largest admitted text length; it is not another
/// independently learned support parameter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorSessionOptions {
    pub field: GeneratorIncidentFieldSpec,
    pub source: GeneratorSourceBinding,
    pub receiver: GeneratorPhaseReceiverBinding,
    pub material_seed: u64,
}
pub(super) struct GeneratorPending<'c> {
    preparation: IncidentPreparation,
    encoded: IncidentEncoded<'c>,
    phases: NativeGeneratorPhaseReception<'c>,
    received: IncidentTextForward<'c>,
    start: u64,
}
/// Read-only producing operands of an outstanding generator comparison.
#[cfg_attr(not(test), allow(dead_code))]
impl<'c> GeneratorPending<'c> {
    /// Receiving phases read from the generated boundary; its binding names the phase ports.
    pub(super) fn response_phases(&self) -> &NativeGeneratorPhaseReception<'c> {
        &self.phases
    }
    /// Text/stop faces produced at those phases.
    pub(super) fn received(&self) -> &IncidentTextForward<'c> {
        &self.received
    }
    /// First source clock event and passage length at which the request was read.
    pub(super) fn source_clock(&self) -> (u64, usize) {
        (self.start, self.encoded.rows.rows())
    }
}
pub(super) struct GeneratorPresentation<'c> {
    encoder: IncidentEncoder<'c>,
    receiver: GeneratorTextReceiver<'c>,
    pub(super) pending: BTreeMap<u64, GeneratorPending<'c>>,
    next_event: u64,
}

fn receiver_boundary<'c>(
    surface: &'c ResidentSurface<'c>,
    spec: &FieldSessionSpec,
    class_count: Option<usize>,
) -> Result<BoundaryMaterial<'c>> {
    let options = spec
        .generator
        .as_ref()
        .ok_or_else(|| invalid("generator session options"))?;
    let mut receiver_spec = spec.clone();
    if let Some(count) = class_count {
        if count == 0 || count > spec.symbols.len() {
            return Err(invalid("generator producing codec extent"));
        }
        receiver_spec.symbols.truncate(count);
    }
    let local = options
        .receiver
        .ports
        .len()
        .checked_mul(6)
        .ok_or_else(|| invalid("generator receiving chart extent"))?;
    BoundaryMaterial::found(
        surface,
        receiver_spec.chart()?,
        local,
        1,
        ResidentGrain(spec.fractional_bits),
        BoundaryMaterialSeed::new(options.material_seed, spec.fractional_bits),
    )
}

fn source_contacts(preparation: &IncidentPreparation) -> Vec<GeneratorSourceContact> {
    preparation
        .contacts
        .iter()
        .map(|c| GeneratorSourceContact {
            from: c.from_cell,
            to: c.to_cell,
            kind: match c.kind {
                IncidentContactKind::IntraPart => GeneratorSourceContactKind::IntraPart,
                IncidentContactKind::DirectJoin { .. } => GeneratorSourceContactKind::DirectJoin,
                IncidentContactKind::RecordedParent { .. } => {
                    GeneratorSourceContactKind::RecordedParent
                }
                IncidentContactKind::RecordedReply { .. } => {
                    GeneratorSourceContactKind::RecordedReply
                }
            },
        })
        .collect()
}

impl<'c> NativeFieldSession<'c> {
    pub(super) fn found_generator(
        surface: &'c ResidentSurface<'c>,
        spec: &FieldSessionSpec,
    ) -> Result<Self> {
        let chart = spec.chart()?;
        let options = spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session options"))?;
        let grain = ResidentGrain(spec.fractional_bits);
        let body = NativeCoupledBody::found_generator_field(surface, options.field.clone(), grain)?;
        let source_width = options
            .source
            .injection_sites
            .len()
            .checked_mul(3)
            .ok_or_else(|| invalid("generator source material extent"))?;
        let seed = BoundaryMaterialSeed::new(options.material_seed, grain.0);
        let source_maps = seed
            .initial_maps(spec.symbols.len(), source_width)
            .map_err(invalid)?;
        let encoder = IncidentEncoder::found_with_seed(surface, &source_maps, grain, seed)?;
        let receiver =
            GeneratorTextReceiver::found(surface, receiver_boundary(surface, spec, None)?)?;
        Ok(Self {
            surface,
            body,
            incident: None,
            generator: Some(GeneratorPresentation {
                encoder,
                receiver,
                pending: BTreeMap::new(),
                next_event: 0,
            }),
            presentation: FieldTextPresentation {
                spec: spec.clone(),
                chart,
                compiled_geometry: None,
                pending_extents: BTreeMap::new(),
                retained_shared: BTreeMap::new(),
                issued_shared: 0,
                exposure: None,
            },
        })
    }

    pub(super) fn generator_request(&mut self, request: &FieldSectionRequest) -> Result<Value> {
        let started = Instant::now();
        let preparation = IncidentPreparation::from_request(&self.presentation.spec, request)?;
        let options = self
            .presentation
            .spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session options"))?;
        let model = self
            .generator
            .as_mut()
            .ok_or_else(|| invalid("generator presentation"))?;
        let count = u64::try_from(preparation.source_extent).map_err(invalid)?;
        let next_event = model
            .next_event
            .checked_add(count)
            .ok_or_else(|| invalid("generator source clock exhausted"))?;
        let symbols = preparation
            .source_cells
            .iter()
            .map(|c| c.symbol_index)
            .collect::<Vec<_>>();
        let encoded = model.encoder.encode(&symbols)?;
        let encoded_rows = Rc::new(ResidentNormalEnclosureSection::concatenate_rows(&[
            &encoded.rows,
        ])?);
        let contacts = source_contacts(&preparation);
        let generated = self.body.prepare_generator_episode_with_offsets(
            encoded_rows,
            options.source.clone(),
            options.source.offsets.clone(),
            model.next_event,
            contacts,
        )?;
        let phases = generated.receive_generator_phases(options.receiver.clone())?;
        let received = model
            .receiver
            .forward(phases.output(), SeriesAperture(options.field.series_terms))?;
        let selected = model.receiver.select_text(&received)?;
        let stop = model.receiver.choose_stop(&received)?;
        if stop > selected.len()
            || selected
                .iter()
                .any(|i| *i >= self.presentation.spec.symbols.len())
        {
            return Err(invalid("generator receiver left its declared text chart"));
        }
        let text = selected[..stop]
            .iter()
            .map(|&i| self.presentation.spec.symbols[i].as_str())
            .collect::<String>();
        let mut result = json!({"schema":"org.holonics.hna.field-section.v1", "scope":"incident-field-joint",
            "source_chart":"generator-machine", "codec":"unicode-scalars", "text":text,
            "symbols":selected[..stop].iter().map(|&i| &self.presentation.spec.symbols[i]).collect::<Vec<_>>(),
            "support":stop, "response_aperture":options.receiver.aperture-1,
            "source_cells":preparation.source_extent, "source_contacts":preparation.contacts.len(),
            "field_sites":options.field.machine.sites().len(), "local_complex":6,
            "source_clock_start":model.next_event, "source_clock_end":next_event,
            "receiver_binding":options.receiver, "producing_epoch":generated.producing_epoch(),
            "material_update":false, "committed":request.commit,
            "generation_us":started.elapsed().as_micros(),
            "native_receipt":{"device":self.surface.device_name(),"kernel_sha256":self.surface.ptx_sha256(),"census":self.surface.census()}});
        let generated = self.body.publish_incident_field(
            generated,
            request.commit,
            request.retain_comparison,
        )?;
        if request.commit {
            model.next_event = next_event;
        }
        if let Some(id) = generated.comparison_id() {
            // Reception was prepared before publication; its word is the same immutable source.
            model.pending.insert(
                id,
                GeneratorPending {
                    preparation: preparation.clone(),
                    encoded,
                    phases,
                    received,
                    start: next_event - count,
                },
            );
            self.presentation.retained_shared.insert(
                id,
                RetainedSharedSource {
                    request: request.clone(),
                    held: preparation.held_mask.clone(),
                    output_symbols: preparation.request_extent + preparation.response_aperture,
                    producing_epoch: generated.producing_epoch(),
                    exposure_pairing: None,
                },
            );
            result["comparison"] = json!(id);
        }
        Ok(result)
    }

    pub(super) fn generator_observe(
        &mut self,
        id: u64,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        let target = self
            .presentation
            .spec
            .symbols_of(&self.presentation.chart, text)?
            .into_iter()
            .map(|s| s.0 as usize)
            .collect::<Vec<_>>();
        let options = self
            .presentation
            .spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session options"))?;
        let model = self
            .generator
            .as_mut()
            .ok_or_else(|| invalid("generator presentation"))?;
        let pending = model
            .pending
            .get(&id)
            .ok_or_else(|| invalid("unknown generator comparison"))?;
        let old_classes = pending
            .received
            .text_cohorts
            .iter()
            .map(|c| c.class_count)
            .sum::<usize>();
        let retro = if target.iter().any(|c| *c >= old_classes) {
            Some(model.receiver.retro_forward(
                &pending.received,
                SeriesAperture(options.field.series_terms),
            )?)
        } else {
            None
        };
        let returned = model.receiver.compare(
            retro.as_ref().unwrap_or(&pending.received),
            &target,
            SeriesAperture(options.field.series_terms),
            step_bits,
        )?;
        let phase_rows = returned
            .boundary_covector
            .split_components(options.receiver.aperture)?;
        let joint = pending.phases.pull_back_joint(&phase_rows)?;
        let field_return =
            self.body
                .prepare_incident_material_return(id, joint.view(), step_bits)?;
        let source_covector = field_return
            .source_covector()
            .ok_or_else(|| invalid("generator source moment return absent"))?;
        let encoder_return =
            model
                .encoder
                .prepare_return(&pending.encoded, source_covector, step_bits)?;
        // All fallible source/receiver/field preparation precedes the one publication boundary.
        self.body.publish_incident_material_return(field_return)?;
        model.encoder.publish(encoder_return);
        model.receiver.publish(returned.successor);
        model.pending.remove(&id);
        self.presentation.retained_shared.remove(&id);
        Ok(
            json!({"scope":"incident-field-joint", "source_chart":"generator-machine", "comparison":id,
            "observed_symbols":target.len(), "material_update":true, "field_sites":options.field.machine.sites().len()}),
        )
    }
}
