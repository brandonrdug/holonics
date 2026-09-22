//! Cold rest for the fixed generator source/phase presentation.
//!
//! The body owns the ordered source tape and its producing q/b stages.  This packet owns the
//! E/R material cuts, encoded source rows needed to reconstruct ordinary pending records, and
//! the tagged receiving binding used to rebuild each frozen producing face.

use super::super::incident_encoder::{IncidentEncoded, IncidentEncoder};
use super::super::incident_receiver::{IncidentTextCohort, phase::GeneratorTextReceiver};
use super::*;
use crate::native::{GeneratorPhaseReceiverBinding, NativeGeneratorPhaseReception};
use holonic_engine::native_ecology::constitutive_fibre::{
    NormalMaterialRest, ResidentNormalEnclosureSection,
};
use holonic_engine::resident_section::ResidentGrain;
use serde::{Deserialize, Serialize};
use std::io::Cursor;

fn material_bytes(material: &NormalMaterialRest) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    material.write(&mut bytes).map_err(invalid)?;
    Ok(bytes)
}

fn read_material(bytes: &[u8]) -> Result<NormalMaterialRest> {
    NormalMaterialRest::read(&mut Cursor::new(bytes), bytes.len() as u64).map_err(invalid)
}

fn section_bytes(section: &ResidentNormalEnclosureSection<'_>) -> Result<Vec<u8>> {
    section
        .rest()
        .map_err(invalid)?
        .canonical_bytes()
        .map_err(invalid)
}

fn read_section(bytes: &[u8]) -> Result<holonic_engine::resident_section::ResidentSectionRest> {
    holonic_engine::resident_section::ResidentSectionRest::read(bytes).map_err(invalid)
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorPendingRest {
    pub id: u64,
    pub preparation: IncidentPreparation,
    pub encoded_symbols: Vec<usize>,
    pub encoded_rows: Vec<u8>,
    pub encoded_row_count: usize,
    pub encoded_width: usize,
    pub grain_bits: u32,
    pub encoded_producing_material: Vec<Vec<u8>>,
    pub frozen_text: Vec<u8>,
    pub frozen_support: Vec<u8>,
    pub frozen_cohorts: Vec<IncidentTextCohort>,
    pub frozen_cohort_material: Vec<Vec<u8>>,
    pub receiver_binding: GeneratorPhaseReceiverBinding,
    pub start: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorPresentationRest {
    pub encoder_material: Vec<Vec<u8>>,
    pub encoder_identities: Vec<usize>,
    pub receiver_text: Vec<u8>,
    pub receiver_support: Vec<u8>,
    pub receiver_cohorts: Vec<IncidentTextCohort>,
    pub receiver_cohort_material: Vec<Vec<u8>>,
    pub pending: Vec<GeneratorPendingRest>,
    pub next_event: u64,
}

impl<'c> GeneratorPresentation<'c> {
    pub(crate) fn rest(&self) -> Result<GeneratorPresentationRest> {
        let (encoder_material, encoder_identities) = self.encoder.rest_with_identities()?;
        let receiver = self.receiver.inner();
        let pending = self
            .pending
            .iter()
            .map(|(&id, pending)| {
                Ok(GeneratorPendingRest {
                    id,
                    preparation: pending.preparation.clone(),
                    encoded_symbols: pending.encoded.symbols.clone(),
                    encoded_rows: section_bytes(&pending.encoded.rows)?,
                    encoded_row_count: pending.encoded.rows.rows(),
                    encoded_width: pending.encoded.rows.components(),
                    grain_bits: pending.encoded.rows.grain().0,
                    encoded_producing_material: pending
                        .encoded
                        .producing
                        .iter()
                        .map(|material| {
                            material
                                .rest()
                                .map_err(invalid)
                                .and_then(|rest| material_bytes(&rest))
                        })
                        .collect::<Result<Vec<_>>>()?,
                    frozen_text: material_bytes(&receiver.producing_text_rest(&pending.received)?)?,
                    frozen_support: material_bytes(
                        &receiver.producing_support_rest(&pending.received)?,
                    )?,
                    frozen_cohorts: pending.received.text_cohorts.clone(),
                    frozen_cohort_material: receiver
                        .producing_text_cohort_rests(&pending.received)?
                        .iter()
                        .map(material_bytes)
                        .collect::<Result<Vec<_>>>()?,
                    receiver_binding: pending.phases.binding().clone(),
                    start: pending.start,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(GeneratorPresentationRest {
            encoder_material: encoder_material
                .iter()
                .map(material_bytes)
                .collect::<Result<_>>()?,
            encoder_identities,
            receiver_text: material_bytes(&receiver.text_rest()?)?,
            receiver_support: material_bytes(&receiver.support_rest()?)?,
            receiver_cohorts: receiver.cohorts().to_vec(),
            receiver_cohort_material: receiver
                .text_cohort_rests()?
                .iter()
                .map(material_bytes)
                .collect::<Result<Vec<_>>>()?,
            pending,
            next_event: self.next_event,
        })
    }
}

impl GeneratorPresentationRest {
    pub(crate) fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
        spec: &FieldSessionSpec,
        body: &NativeCoupledBody<'c>,
    ) -> Result<GeneratorPresentation<'c>> {
        let options = spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation rest requires generator spec"))?;
        let body_spec = body.generator_field_spec()?;
        if body_spec != &options.field {
            return Err(invalid("generator body/spec rest mismatch"));
        }
        let (rows, width, grain, _) = body.incident_dimensions()?;
        let expected_width = 12usize;
        if rows != options.field.machine.sites().len()
            || width != expected_width
            || grain != ResidentGrain(spec.fractional_bits)
        {
            return Err(invalid("generator presentation rest layout"));
        }
        let source_width = options
            .source
            .injection_sites
            .len()
            .checked_mul(6)
            .ok_or_else(|| invalid("generator source rest width"))?;
        let encoder_material = self
            .encoder_material
            .iter()
            .map(|bytes| read_material(bytes))
            .collect::<Result<Vec<_>>>()?;
        if encoder_material.is_empty()
            || encoder_material
                .iter()
                .any(|material| material.targets() != source_width / 2)
        {
            return Err(invalid("generator encoder source width"));
        }
        let mut encoder = IncidentEncoder::remount_with_identities(
            surface,
            encoder_material,
            self.encoder_identities,
        )?;
        encoder.bind_seed(BoundaryMaterialSeed::new(
            options.material_seed,
            spec.fractional_bits,
        ));
        let current_boundary = super::receiver_boundary(surface, spec, None)?;
        let receiver_cohorts = self.receiver_cohorts;
        let receiver_codec_version = receiver_cohorts
            .last()
            .map_or(0, |cohort| cohort.codec_version);
        let receiver = GeneratorTextReceiver::remount_with_cohorts(
            surface,
            current_boundary,
            read_material(&self.receiver_text)?,
            read_material(&self.receiver_support)?,
            receiver_cohorts,
            self.receiver_cohort_material
                .iter()
                .map(|bytes| read_material(bytes))
                .collect::<Result<Vec<_>>>()?,
            receiver_codec_version,
        )?;
        let mut presentation = GeneratorPresentation {
            encoder,
            receiver,
            pending: std::collections::BTreeMap::new(),
            next_event: self.next_event,
        };
        for pending in self.pending {
            pending.preparation.validate(spec)?;
            if pending.receiver_binding != options.receiver
                || pending.encoded_row_count != pending.preparation.source_extent
                || pending.encoded_width != source_width
                || pending.grain_bits != grain.0
                || pending.encoded_symbols
                    != pending
                        .preparation
                        .source_cells
                        .iter()
                        .map(|cell| cell.symbol_index)
                        .collect::<Vec<_>>()
                || pending.start > presentation.next_event
                || pending
                    .start
                    .checked_add(pending.encoded_row_count as u64)
                    .is_none()
            {
                return Err(invalid("generator pending source/receiver chart"));
            }
            let generated = body.incident_comparison(pending.id)?;
            if generated.generator_source_binding()
                != Some((
                    &options.source,
                    pending.start,
                    pending.encoded_row_count,
                    pending.encoded_width,
                ))
                || generated.generator_source_contacts()
                    != Some(source_contacts(&pending.preparation).as_slice())
            {
                return Err(invalid("generator pending body/source binding mismatch"));
            }
            let phases: NativeGeneratorPhaseReception<'c> =
                generated.receive_generator_phases(pending.receiver_binding.clone())?;
            let old_class_count = pending
                .frozen_cohorts
                .iter()
                .map(|cohort| cohort.class_count)
                .sum::<usize>();
            let frozen_boundary = super::receiver_boundary(surface, spec, Some(old_class_count))?;
            let frozen_receiver = GeneratorTextReceiver::remount_with_cohorts(
                surface,
                frozen_boundary,
                read_material(&pending.frozen_text)?,
                read_material(&pending.frozen_support)?,
                pending.frozen_cohorts.clone(),
                pending
                    .frozen_cohort_material
                    .iter()
                    .map(|bytes| read_material(bytes))
                    .collect::<Result<Vec<_>>>()?,
                pending
                    .frozen_cohorts
                    .last()
                    .map_or(0, |cohort| cohort.codec_version),
            )?;
            let received = frozen_receiver.forward(
                phases.output(),
                holonic_engine::resident_section::SeriesAperture(options.field.series_terms),
            )?;
            let encoded_rows = ResidentNormalEnclosureSection::remount(
                surface,
                read_section(&pending.encoded_rows)?,
                pending.encoded_row_count,
                pending.encoded_width,
                ResidentGrain(pending.grain_bits),
            )?;
            let producing = pending
                .encoded_producing_material
                .iter()
                .map(|bytes| {
                    read_material(bytes)?
                        .remount(surface)
                        .map_err(invalid)
                        .map(|material| material.retained_view())
                })
                .collect::<Result<Vec<_>>>()?;
            let encoded = IncidentEncoded {
                rows: encoded_rows,
                symbols: pending.encoded_symbols,
                producing,
            };
            presentation.pending.insert(
                pending.id,
                GeneratorPending {
                    preparation: pending.preparation,
                    encoded,
                    phases,
                    received,
                    start: pending.start,
                },
            );
        }
        Ok(presentation)
    }
}
