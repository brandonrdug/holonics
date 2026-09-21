//! One explicit resident mathematical batch entering the incident field.
//!
//! Operator handles and retained products live only for this request.  The field remains the
//! continuing owner; no mathematical product is serialized through the host or installed as a
//! second learner.

use super::*;
use holonic_engine::{
    DimensionalWaveModeId, ExactWavePhaseTransport,
    native_ecology::constitutive_fibre::ResidentNormalEnclosureSection,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FieldMathematicalRequest {
    pub operations: Vec<MathematicalRequest>,
    pub source: MathematicalInputWire,
    /// Canonical global complex coordinates: `site * local_complex + channel`.
    pub source_coordinates: Vec<usize>,
    pub receiver_coordinates: Vec<usize>,
    pub geometry_mode: DimensionalWaveModeId,
    #[serde(default)]
    pub commit: bool,
}

fn phases(count: usize) -> Vec<ExactWavePhaseTransport> {
    vec![ExactWavePhaseTransport::identity(); count]
}

fn unique_coordinates(label: &str, coordinates: &[usize], global_complex: usize) -> Result<()> {
    if coordinates.is_empty() {
        return Err(invalid(format!("{label} coordinates must be nonempty")));
    }
    if coordinates
        .iter()
        .any(|&coordinate| coordinate >= global_complex)
    {
        return Err(invalid(format!(
            "{label} coordinate is outside the global complex boundary"
        )));
    }
    let unique = coordinates.iter().copied().collect::<BTreeSet<_>>();
    if unique.len() != coordinates.len() {
        return Err(invalid(format!("{label} coordinates contain duplicates")));
    }
    Ok(())
}

impl<'c> NativeFieldSession<'c> {
    pub fn mathematical_request(&mut self, request: &FieldMathematicalRequest) -> Result<Value> {
        let start = std::time::Instant::now();
        if self.presentation.spec.source_chart != FieldSourceChart::IncidentField {
            return Err(invalid(
                "structured mathematical field batches require incident-field mode",
            ));
        }
        let geometry = self
            .presentation
            .spec
            .geometry
            .as_ref()
            .ok_or_else(|| invalid("incident mathematical batch requires declared geometry"))?;
        if geometry.mode != request.geometry_mode {
            return Err(invalid(
                "mathematical batch geometry mode does not match the field",
            ));
        }

        let (rows, width, grain, _) = self.body.incident_dimensions()?;
        if width == 0 || width % 2 != 0 {
            return Err(invalid(
                "incident field has an invalid complex boundary width",
            ));
        }
        let local_complex = width / 2;
        let global_complex = rows
            .checked_mul(local_complex)
            .ok_or_else(|| invalid("incident global complex extent"))?;
        unique_coordinates("source", &request.source_coordinates, global_complex)?;
        unique_coordinates("receiver", &request.receiver_coordinates, global_complex)?;

        let mut mathematical = NativeMathematicalSession::on(self.surface);
        let mut operation_results = Vec::with_capacity(request.operations.len());
        for operation in &request.operations {
            operation_results.push(mathematical.request(operation)?);
        }

        let source_coordinates = &request.source_coordinates;
        let receiver_coordinates = &request.receiver_coordinates;
        let source_coordinate_count = source_coordinates.len();
        let expected_source_width = source_coordinate_count
            .checked_mul(2)
            .ok_or_else(|| invalid("mathematical source width"))?;
        let expected_source_packet_width = expected_source_width
            .checked_add(1)
            .ok_or_else(|| invalid("mathematical source packet width"))?;
        let response_aperture = receiver_coordinates.len();

        let (generated, receiver_ball, generated_epoch) =
            mathematical.with_resident_input(&request.source, |section| {
                if section.rows() != 1 || section.width() != expected_source_packet_width {
                    return Err(invalid(
                        "mathematical source must be one common-denominator rational row",
                    ));
                }
                let rational = ResidentConstitutiveSection::rationals(section)?;
                if rational.rows() != 1 || rational.components() != expected_source_width {
                    return Err(invalid("mathematical source coordinate chart"));
                }
                let source_points = ResidentNormalEnclosureSection::from_points(rational, grain)?;
                let source_points = source_points.split_components(source_coordinate_count)?;
                let source_flat = source_points.scatter_phase_adjoint(
                    source_coordinates,
                    &phases(source_coordinate_count),
                    global_complex,
                )?;
                let source = source_flat.pack_components(local_complex)?;

                let mut held = vec![false; global_complex];
                for &coordinate in source_coordinates {
                    held[coordinate] = true;
                }
                let current = self
                    .body
                    .incident_current_boundary()?
                    .view()
                    .split_rows(rows, width)?;
                let anchor = current
                    .held_refinement(&source, &held, 0)?
                    .pack_components(rows)?
                    .row(0)?
                    .to_owned()?;
                let generated = self.body.prepare_incident_field(anchor.view(), &held)?;
                let generated_epoch = generated.producing_epoch();

                let boundary = generated
                    .boundary()?
                    .view()
                    .split_rows(rows, width)?
                    .split_components(local_complex)?;
                let receiver = boundary.gather_phase_rows(
                    receiver_coordinates,
                    &phases(response_aperture),
                    2,
                )?;
                let receiver_ball = receiver
                    .pack_components(response_aperture)?
                    .row(0)?
                    .inspect()?;
                Ok((generated, receiver_ball, generated_epoch))
            })?;

        let mut value = json!({
            "schema": "org.holonics.hna.field-mathematical.v1",
            "scope": "incident-field-structured-mathematical-batch",
            "batch_scope": "operators-and-products-live-only-during-this-request",
            "operation_results": operation_results,
            "geometry_mode": request.geometry_mode,
            "source_coordinates": source_coordinates,
            "receiver_coordinates": receiver_coordinates,
            "source_binding": {
                "global_complex_extent": global_complex,
                "local_complex": local_complex,
                "source_width": expected_source_width,
                "held_coordinates": source_coordinates,
            },
            "receiver_binding": {
                "coordinates": receiver_coordinates,
                "aperture": response_aperture,
                "ball": receiver_ball,
            },
            "generated_scope": {
                "producing_epoch": generated_epoch,
                "producing_field_cut": generated.producing_field_cut(),
                "producing_material_observations": generated.producing_material_observations(),
                "current_epoch": generated_epoch,
                "commit": request.commit,
                "retain_comparison": false,
            },
            "generation_us": start.elapsed().as_micros(),
            "native_receipt": {
                "device": self.surface.device_name(),
                "kernel_sha256": self.surface.ptx_sha256(),
                "census_before_publication": self.surface.census(),
            },
            "material_update": false,
            "operator_bounds": generated.operator_bounds()?,
        });
        self.body
            .publish_incident_field(generated, request.commit, false)?;
        value["generated_scope"]["current_epoch"] = json!(self.body.epoch());
        value["native_receipt"]["census_after_publication"] = json!(self.surface.census());
        Ok(value)
    }
}
