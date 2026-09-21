//! Cold rest for the incident presentation boundary.
//!
//! Material maps are serialized through their existing binary NormalMaterialRest
//! codec. Resident sections are explicit packets; no live receiver map is used to
//! reconstruct a frozen producing comparison.

use super::boundary::BoundaryMaterial;
use super::incident_encoder::{IncidentEncoded, IncidentEncoder};
use super::incident_receiver::{IncidentTextCohort, IncidentTextReceiver};
use super::*;
use crate::native::NativeIncidentGenerated;
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
pub struct IncidentPendingRest {
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
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentPresentationRest {
    pub encoder_material: Vec<Vec<u8>>,
    pub encoder_identities: Vec<usize>,
    pub receiver_text: Vec<u8>,
    pub receiver_support: Vec<u8>,
    pub receiver_cohorts: Vec<IncidentTextCohort>,
    pub receiver_cohort_material: Vec<Vec<u8>>,
    pub pending: Vec<IncidentPendingRest>,
    pub slot_rows: Vec<usize>,
    pub rows: usize,
    pub width: usize,
    pub series: u32,
}

impl<'c> IncidentPresentation<'c> {
    pub(crate) fn rest(&self) -> Result<IncidentPresentationRest> {
        let (encoder, identities) = self.encoder.rest_with_identities()?;
        let receiver_text = material_bytes(&self.receiver.text_rest()?)?;
        let receiver_support = material_bytes(&self.receiver.support_rest()?)?;
        let receiver_cohort_material = self
            .receiver
            .text_cohort_rests()?
            .iter()
            .map(material_bytes)
            .collect::<Result<Vec<_>>>()?;
        let pending = self
            .pending
            .iter()
            .map(|(&id, pending)| {
                Ok(IncidentPendingRest {
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
                    frozen_text: material_bytes(
                        &self.receiver.producing_text_rest(&pending.received)?,
                    )?,
                    frozen_support: material_bytes(
                        &self.receiver.producing_support_rest(&pending.received)?,
                    )?,
                    frozen_cohorts: pending.received.text_cohorts.clone(),
                    frozen_cohort_material: self
                        .receiver
                        .producing_text_cohort_rests(&pending.received)?
                        .iter()
                        .map(material_bytes)
                        .collect::<Result<Vec<_>>>()?,
                })
            })
            .collect::<Result<Vec<_>>>()?;
        Ok(IncidentPresentationRest {
            encoder_material: encoder.iter().map(material_bytes).collect::<Result<_>>()?,
            encoder_identities: identities,
            receiver_text,
            receiver_support,
            receiver_cohorts: self.receiver.cohorts().to_vec(),
            receiver_cohort_material,
            pending,
            slot_rows: self.slot_rows.clone(),
            rows: self.rows,
            width: self.width,
            series: self.series,
        })
    }
}

impl IncidentPresentationRest {
    pub(crate) fn remount<'c>(
        self,
        surface: &'c ResidentSurface<'c>,
        spec: &FieldSessionSpec,
        body: &NativeCoupledBody<'c>,
    ) -> Result<IncidentPresentation<'c>> {
        let (rows, width, grain, slot_rows) = body.incident_dimensions()?;
        if rows != self.rows || width != self.width || slot_rows != self.slot_rows {
            return Err(invalid("incident presentation rest layout"));
        }
        let boundary_spec = spec
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident material declaration"))?;
        let chart = spec.chart()?;
        let boundary = BoundaryMaterial::found(
            surface,
            chart,
            width / 2,
            boundary_spec.response_aperture,
            grain,
            BoundaryMaterialSeed::new(boundary_spec.material_seed, grain.0),
        )?;
        let encoder_rests = self
            .encoder_material
            .iter()
            .map(|bytes| read_material(bytes))
            .collect::<Result<Vec<_>>>()?;
        let mut encoder = IncidentEncoder::remount_with_identities(
            surface,
            encoder_rests,
            self.encoder_identities,
        )?;
        encoder.bind_seed(BoundaryMaterialSeed::new(
            boundary_spec.material_seed,
            grain.0,
        ));
        let receiver_cohorts = self.receiver_cohorts;
        let receiver_codec_version = receiver_cohorts
            .last()
            .map_or(0, |cohort| cohort.codec_version);
        let receiver = IncidentTextReceiver::remount_with_cohorts(
            surface,
            boundary,
            read_material(&self.receiver_text)?,
            read_material(&self.receiver_support)?,
            receiver_cohorts,
            self.receiver_cohort_material
                .iter()
                .map(|bytes| read_material(bytes))
                .collect::<Result<Vec<_>>>()?,
            receiver_codec_version,
        )?;
        let mut presentation = IncidentPresentation {
            encoder,
            receiver,
            pending: BTreeMap::new(),
            slot_rows,
            rows,
            width,
            series: self.series,
        };
        for pending in self.pending {
            pending.preparation.validate(spec)?;
            if pending.encoded_row_count != pending.preparation.source_extent
                || pending.encoded_width != width
                || pending.grain_bits != grain.0
                || pending.encoded_symbols
                    != pending
                        .preparation
                        .source_cells
                        .iter()
                        .map(|cell| cell.symbol_index)
                        .collect::<Vec<_>>()
            {
                return Err(invalid("incident pending source chart"));
            }
            let generated: NativeIncidentGenerated<'c> = body.incident_comparison(pending.id)?;
            let boundary_rows = generated.boundary()?.view().split_rows(rows, width)?;
            let response_sites = super::incident_response_slots(
                spec,
                &pending.preparation,
                &presentation.slot_rows,
            )?;
            let response = boundary_rows.gather_phase_rows(
                &response_sites,
                &vec![ExactWavePhaseTransport::identity(); response_sites.len()],
                width,
            )?;
            let frozen_boundary = BoundaryMaterial::found(
                surface,
                spec.chart()?,
                width / 2,
                boundary_spec.response_aperture,
                grain,
                BoundaryMaterialSeed::new(boundary_spec.material_seed, grain.0),
            )?;
            let frozen_cohorts = pending.frozen_cohorts.clone();
            let frozen_receiver = IncidentTextReceiver::remount_with_cohorts(
                surface,
                frozen_boundary,
                read_material(&pending.frozen_text)?,
                read_material(&pending.frozen_support)?,
                frozen_cohorts.clone(),
                pending
                    .frozen_cohort_material
                    .iter()
                    .map(|bytes| read_material(bytes))
                    .collect::<Result<Vec<_>>>()?,
                frozen_cohorts
                    .last()
                    .map_or(0, |cohort| cohort.codec_version),
            )?;
            let received = frozen_receiver.forward(&response, SeriesAperture(self.series))?;
            let rows_rest = read_section(&pending.encoded_rows)?;
            let encoded_rows = ResidentNormalEnclosureSection::remount(
                surface,
                rows_rest,
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
                IncidentPending {
                    preparation: pending.preparation,
                    encoded,
                    received,
                },
            );
        }
        Ok(presentation)
    }
}
