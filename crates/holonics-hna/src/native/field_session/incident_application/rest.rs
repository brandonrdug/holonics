//! Cold rest for the incident presentation boundary.
//!
//! Material maps are serialized through their existing binary NormalMaterialRest codec. An
//! outstanding comparison is not part of this rest: its request is the session's
//! `RetainedSharedSource` and its boundary operands are the body's; both are read at the
//! contemporary constitution when it returns.

use super::boundary::BoundaryMaterial;
use super::incident_encoder::IncidentEncoder;
use super::incident_receiver::{IncidentTextCohort, IncidentTextReceiver};
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::NormalMaterialRest;
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IncidentPresentationRest {
    pub encoder_material: Vec<Vec<u8>>,
    pub encoder_identities: Vec<usize>,
    pub receiver_text: Vec<u8>,
    pub receiver_support: Vec<u8>,
    pub receiver_cohorts: Vec<IncidentTextCohort>,
    pub receiver_cohort_material: Vec<Vec<u8>>,
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
        Ok(IncidentPresentationRest {
            encoder_material: encoder.iter().map(material_bytes).collect::<Result<_>>()?,
            encoder_identities: identities,
            receiver_text,
            receiver_support,
            receiver_cohorts: self.receiver.cohorts().to_vec(),
            receiver_cohort_material,
            slot_rows: self.slot_rows.clone(),
            rows: self.rows,
            width: self.width,
            series: self.series,
        })
    }
}

impl IncidentPresentationRest {
    /// Remount the current presentation materials and receiver chart.
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
        if body.incident_solver()? != (boundary_spec.solver, boundary_spec.solve_steps) {
            return Err(invalid("incident presentation rest solver declaration"));
        }
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
        Ok(IncidentPresentation {
            encoder,
            receiver,
            slot_rows,
            rows,
            width,
            series: self.series,
        })
    }
}
