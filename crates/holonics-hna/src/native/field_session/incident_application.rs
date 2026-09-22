//! Athena's incident-field application binding. The same exposure cursor and public session
//! call prepare source rows, execute one joint field word, and receive its text/support faces.
use super::boundary::BoundaryMaterial;
use super::incident_encoder::{IncidentEncoded, IncidentEncoder};
use super::incident_receiver::{IncidentTextForward, IncidentTextReceiver};
use super::*;
use holonic_engine::{
    native_ecology::constitutive_fibre::{BoundaryMaterialSeed, ResidentNormalEnclosureSection},
    resident_section::SeriesAperture,
    ExactWavePhaseTransport,
};
mod codec;
mod rest;
#[cfg(test)]
#[path = "incident_application_tests.rs"]
mod tests;
pub(super) use rest::IncidentPresentationRest;

pub(super) struct IncidentPending<'c> {
    preparation: IncidentPreparation,
    encoded: IncidentEncoded<'c>,
    received: IncidentTextForward<'c>,
}
pub(super) struct IncidentPresentation<'c> {
    encoder: IncidentEncoder<'c>,
    receiver: IncidentTextReceiver<'c>,
    pub(super) pending: BTreeMap<u64, IncidentPending<'c>>,
    slot_rows: Vec<usize>,
    rows: usize,
    width: usize,
    series: u32,
}
fn phases(n: usize) -> Vec<ExactWavePhaseTransport> {
    vec![ExactWavePhaseTransport::identity(); n]
}

pub(super) fn incident_response_slots(
    spec: &FieldSessionSpec,
    preparation: &IncidentPreparation,
    slot_rows: &[usize],
) -> Result<Vec<usize>> {
    let options = spec
        .incident
        .as_ref()
        .ok_or_else(|| invalid("incident material declaration"))?;
    let start = options
        .response_port_start
        .unwrap_or(preparation.source_extent);
    let end = start
        .checked_add(preparation.response_aperture)
        .ok_or_else(|| invalid("incident response port extent"))?;
    if preparation.response_aperture != options.response_aperture
        || preparation.source_extent > start
        || end > spec.section_symbols
        || end > slot_rows.len()
    {
        return Err(invalid("incident source crosses fixed response port"));
    }
    Ok(slot_rows[start..end].to_vec())
}

fn section_radius_receipt(section: &ResidentNormalEnclosureSection<'_>) -> Result<Value> {
    let faces = section.inspect_radii().map_err(invalid)?;
    let rows = faces
        .into_iter()
        .map(|radius| json!({"radius": radius.to_string(), "components": section.components() / 2}))
        .collect::<Vec<_>>();
    Ok(json!({"rows": rows, "row_count": section.rows(), "components": section.components()}))
}
fn section_face_receipt(section: &ResidentNormalEnclosureSection<'_>) -> Result<Value> {
    let faces = section.inspect_rows().map_err(invalid)?;
    let rows = faces
        .into_iter()
        .map(|face| {
            json!({
                "center": face.center.iter().map(|value| json!({"real": value.real.to_string(), "imaginary": value.imaginary.to_string()})).collect::<Vec<_>>(),
                "radius": face.radius.to_string(),
            })
        })
        .collect::<Vec<_>>();
    Ok(json!({"rows": rows, "row_count": section.rows(), "components": section.components()}))
}

impl<'c> NativeFieldSession<'c> {
    /// Select the numerical proposal for subsequent incident words. Outstanding comparisons
    /// retain their solver, so this change is admitted only after they have returned/released.
    pub fn configure_incident_solver(
        &mut self,
        solver: super::super::IncidentFieldSolver,
        steps: usize,
    ) -> Result<()> {
        if self.presentation.spec.incident.is_none() {
            return Err(invalid("incident solver requires its model chart"));
        }
        self.body.configure_incident_solver(solver, steps)?;
        let options = self.presentation.spec.incident.as_mut().unwrap();
        options.solver = solver;
        options.solve_steps = steps;
        Ok(())
    }
    /// Cold readout of the actual source columns and text receiving maps, including their
    /// normal statistics, prior and enclosure. This does not execute a field word or alter
    /// material/current. The aperture-wide support matrix is not expanded by this readout.
    pub fn inspect_incident_boundary_material(&self) -> Result<Value> {
        let incident = self
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident session state"))?;
        Ok(json!({
            "codec_symbols": self.presentation.spec.symbols,
            "codec_revision": incident.receiver.codec_version(),
            "encoder": incident.encoder.inspect_columns()?,
            "text_receiver": incident.receiver.inspect_text_materials()?,
            "material_return_bounds": self.body.inspect_incident_material_return_bounds()?,
        }))
    }

    /// Read the frozen receiving operands of an outstanding incident comparison. These are
    /// the produced features/potentials/faces, not a recomputation with contemporary material.
    pub fn inspect_incident_comparison(&self, id: u64) -> Result<Value> {
        let pending = self
            .incident
            .as_ref()
            .and_then(|incident| incident.pending.get(&id))
            .ok_or_else(|| invalid("missing incident comparison"))?;
        let forward = &pending.received;
        Ok(json!({
            "comparison": id,
            "encoded_source": section_face_receipt(&pending.encoded.rows)?,
            "text_features": section_face_receipt(&forward.text_features)?,
            "text_logits": section_face_receipt(&forward.text_logits)?,
            "text_normalized": section_face_receipt(forward.text_face.participation())?,
            "support_logits": section_face_receipt(&forward.support_logits)?,
            "support_normalized": section_face_receipt(forward.support_face.participation())?,
        }))
    }

    pub(super) fn found_incident(
        surface: &'c ResidentSurface<'c>,
        spec: &FieldSessionSpec,
    ) -> Result<Self> {
        let mut effective_spec = spec.clone();
        let options = effective_spec
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident material declaration"))?;
        let response_port_start = options.response_port_start.unwrap_or_else(|| {
            effective_spec
                .section_symbols
                .saturating_sub(options.response_aperture)
        });
        if options.response_aperture == 0
            || response_port_start
                .checked_add(options.response_aperture)
                .is_none_or(|end| end > effective_spec.section_symbols)
        {
            return Err(invalid("incident response port binding"));
        }
        effective_spec
            .incident
            .as_mut()
            .unwrap()
            .response_port_start = Some(response_port_start);
        let chart = effective_spec.chart()?;
        let options = effective_spec.incident.as_ref().unwrap();
        let geometry = effective_spec
            .geometry
            .as_ref()
            .ok_or_else(|| invalid("incident geometric declaration"))?;
        let body = NativeCoupledBody::found_incident_field(
            surface,
            super::super::IncidentFieldSpec {
                participation: options.participation,
                geometry: geometry.clone(),
                local_roots: options.local_roots,
                material_owners: options.material_owners.clone(),
                solve_steps: options.solve_steps,
                solver: options.solver,
            },
            ResidentGrain(effective_spec.fractional_bits),
        )?;
        let (rows, width, grain, slot_rows) = body.incident_dimensions()?;
        if effective_spec.section_symbols > slot_rows.len()
            || options.response_aperture > spec.section_symbols
        {
            return Err(invalid(
                "incident source/response slots exceed the declared geometry",
            ));
        }
        let boundary = BoundaryMaterial::found(
            surface,
            effective_spec.chart()?,
            width / 2,
            options.response_aperture,
            grain,
            BoundaryMaterialSeed::new(options.material_seed, grain.0),
        )?;
        let encoder = IncidentEncoder::found_with_seed(
            surface,
            boundary.maps(),
            grain,
            BoundaryMaterialSeed::new(options.material_seed, effective_spec.fractional_bits),
        )?;
        let receiver = IncidentTextReceiver::found(surface, boundary)?;
        Ok(Self {
            surface,
            body,
            incident: Some(IncidentPresentation {
                encoder,
                receiver,
                pending: BTreeMap::new(),
                slot_rows,
                rows,
                width,
                series: geometry.series_terms,
            }),
            presentation: FieldTextPresentation {
                spec: effective_spec,
                chart,
                compiled_geometry: None,
                pending_extents: BTreeMap::new(),
                retained_shared: BTreeMap::new(),
                issued_shared: 0,
                exposure: None,
            },
        })
    }
    pub(super) fn incident_request(&mut self, request: &FieldSectionRequest) -> Result<Value> {
        let start = Instant::now();
        let preparation = IncidentPreparation::from_request(&self.presentation.spec, request)?;
        let incident = self
            .incident
            .as_mut()
            .ok_or_else(|| invalid("incident session state"))?;
        let aperture = self
            .presentation
            .spec
            .incident
            .as_ref()
            .unwrap()
            .response_aperture;
        if preparation.response_aperture != aperture {
            return Err(invalid(format!(
                "complete incident source and response require {}+{} sites; declared slots={}, response aperture={}",
                preparation.source_extent,
                preparation.response_aperture,
                incident.slot_rows.len(),
                aperture
            )));
        }
        let response_sites =
            incident_response_slots(&self.presentation.spec, &preparation, &incident.slot_rows)?;
        let symbols = preparation
            .source_cells
            .iter()
            .map(|s| s.symbol_index)
            .collect::<Vec<_>>();
        let encoded = incident.encoder.encode(&symbols)?;
        let source_sites = &incident.slot_rows[..preparation.source_extent];
        let source = encoded.rows.scatter_phase_adjoint(
            source_sites,
            &phases(source_sites.len()),
            incident.rows,
        )?;
        let current = self
            .body
            .incident_current_boundary()?
            .view()
            .split_rows(incident.rows, incident.width)?;
        let mut held = vec![false; incident.rows * (incident.width / 2)];
        for &site in source_sites {
            held[site * (incident.width / 2)..(site + 1) * (incident.width / 2)].fill(true);
        }
        let anchor = current
            .held_refinement(&source, &held, 0)?
            .pack_components(incident.rows)?
            .row(0)?
            .to_owned()?;
        let contacts = preparation
            .contacts
            .iter()
            .map(|c| (source_sites[c.from_cell], source_sites[c.to_cell]))
            .collect::<Vec<_>>();
        let generated = self.body.prepare_incident_field_restricted(
            anchor.view(),
            &held,
            source_sites,
            &contacts,
        )?;
        let boundary = generated
            .boundary()?
            .view()
            .split_rows(incident.rows, incident.width)?;
        let response =
            boundary.gather_phase_rows(&response_sites, &phases(aperture), incident.width)?;
        let received = incident
            .receiver
            .forward(&response, SeriesAperture(incident.series))?;
        let selections = incident.receiver.select_text_receipts(&received)?;
        let selected = selections.iter().map(|s| s.selected).collect::<Vec<_>>();
        let support_selection = incident.receiver.select_support_receipt(&received)?;
        let support = support_selection.selected;
        if support > aperture
            || selected.len() != aperture
            || selected
                .iter()
                .any(|i| *i >= self.presentation.spec.symbols.len())
        {
            return Err(invalid(
                "incident receiver left its declared codec/support chart",
            ));
        }
        let text = selected[..support]
            .iter()
            .map(|&i| self.presentation.spec.symbols[i].as_str())
            .collect::<String>();
        let response_section = response.pack_components(aperture)?.row(0)?.inspect()?;
        let text_logits_receipt = section_radius_receipt(&received.text_logits)?;
        let support_logits_receipt = section_face_receipt(&received.support_logits)?;
        let text_face_receipt = section_radius_receipt(received.text_face.participation())?;
        let support_face_receipt = section_face_receipt(received.support_face.participation())?;
        let receiver_material_cuts = incident.receiver.material_observations();
        let encoder_material_cuts = incident.encoder.material_observations();
        let producing_encoder_cuts = encoded
            .producing
            .iter()
            .map(|material| material.observations())
            .collect::<Vec<_>>();
        let producing_receiver_cuts = json!({
            "text": received.text_material.observations(),
            "support": received.support_material.observations(),
            "text_cohorts": received.text_materials.iter().map(|material| material.observations()).collect::<Vec<_>>(),
        });
        let pending_before = self.body.pending_ids()?;
        let current_cut_before = self.body.epoch();
        let mut value = json!({"schema":"org.holonics.hna.field-section.v1","scope":"incident-field-joint","source_chart":"incident-field",
            "codec":"unicode-scalars","codec_symbols":self.presentation.spec.symbols,"codec_revision":incident.receiver.codec_version(),
            "text":text,"symbols":selected[..support].iter().map(|&i|&self.presentation.spec.symbols[i]).collect::<Vec<_>>(),
            "support":support,"response_aperture":aperture,"output_symbols":preparation.request_extent+aperture,
            "selections":selections,"support_selection":support_selection,"selection_chart":"real-receiver-potentials",
            "response_section":response_section,"receiver_faces":{"support_logits":support_logits_receipt,"support_normalized":support_face_receipt},
            "uncertainty":{"text_logits_radius":text_logits_receipt,"text_normalized_radius":text_face_receipt},
            "source_bindings":source_sites,"receiver_bindings":response_sites,
            "material_cuts":{"encoder":encoder_material_cuts,"receiver":receiver_material_cuts,"producing_encoder":producing_encoder_cuts,"producing_receiver":producing_receiver_cuts},
            "producing_cut":{"epoch":generated.producing_epoch(),"field_cut":generated.producing_field_cut(),"material_observations":generated.producing_material_observations()},
            "operator_bounds":generated.operator_bounds()?,
            "solver":self.presentation.spec.incident.as_ref().map(|o| json!({"method":o.solver,"steps":o.solve_steps})),
            "current_cut_before":current_cut_before,"pending_before":pending_before,
            "material_update":false,
            "source_cells":preparation.source_extent,"context_cells":preparation.context_extent,"source_contacts":contacts.len(),
            "field_sites":incident.rows,"local_complex":incident.width/2,"producing_epoch":generated.producing_epoch(),
            "native_receipt":{"device":self.surface.device_name(),"kernel_sha256":self.surface.ptx_sha256(),"census_before_publication":self.surface.census()},
            "generation_us":start.elapsed().as_micros(),"committed":request.commit});
        let generated = self.body.publish_incident_field(
            generated,
            request.commit,
            request.retain_comparison,
        )?;
        value["current_cut_after"] = json!(self.body.epoch());
        value["native_receipt"]["census_after_publication"] = json!(self.surface.census());
        if let Some(id) = generated.comparison_id() {
            incident.pending.insert(
                id,
                IncidentPending {
                    preparation: preparation.clone(),
                    encoded,
                    received,
                },
            );
            self.presentation.retained_shared.insert(
                id,
                RetainedSharedSource {
                    request: request.clone(),
                    held,
                    output_symbols: preparation.request_extent + aperture,
                    producing_epoch: generated.producing_epoch(),
                    exposure_pairing: None,
                },
            );
            value["comparison"] = json!(id);
        }
        Ok(value)
    }
    pub(super) fn incident_observe(
        &mut self,
        id: u64,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        let started = Instant::now();
        let incident = self
            .incident
            .as_mut()
            .ok_or_else(|| invalid("incident session state"))?;
        let pending = incident
            .pending
            .get(&id)
            .ok_or_else(|| invalid("unknown incident boundary comparison"))?;
        let target = self
            .presentation
            .spec
            .symbols_of(&self.presentation.chart, text)?
            .into_iter()
            .map(|s| s.0 as usize)
            .collect::<Vec<_>>();
        let source_classes = pending
            .preparation
            .source_cells
            .iter()
            .map(|c| c.symbol_index)
            .collect::<Vec<_>>();
        let old_classes = pending
            .received
            .text_cohorts
            .iter()
            .map(|c| c.class_count)
            .sum::<usize>();
        let retro = if target.iter().any(|&i| i >= old_classes) {
            Some(
                incident
                    .receiver
                    .retro_forward(&pending.received, SeriesAperture(incident.series))?,
            )
        } else {
            None
        };
        let comparison = retro.as_ref().unwrap_or(&pending.received);
        let returned = incident
            .receiver
            .compare_with_codec(
                comparison,
                &target,
                target.len(),
                &pending.encoded.rows,
                &source_classes,
                SeriesAperture(incident.series),
                step_bits,
            )
            .map_err(|error| invalid(format!("incident receiver comparison: {error}")))?;
        let receiver_returned = Instant::now();
        let response_sites = incident_response_slots(
            &self.presentation.spec,
            &pending.preparation,
            &incident.slot_rows,
        )?;
        let response_covector = returned
            .boundary_covector
            .split_components(pending.preparation.response_aperture)?;
        let boundary = response_covector
            .scatter_phase_adjoint(
                &response_sites,
                &phases(response_sites.len()),
                incident.rows,
            )?
            .pack_components(incident.rows)?;
        let generated = self.body.incident_comparison(id)?;
        let full =
            boundary.gather_phase_rows(&[0], &phases(1), generated.joint_output().components())?;
        let field = self
            .body
            .prepare_incident_material_return(id, full.row(0)?, step_bits)
            .map_err(|error| invalid(format!("incident field material return: {error}")))?;
        let field_returned = Instant::now();
        let source_sites = &incident.slot_rows[..pending.preparation.source_extent];
        let anchor = field
            .anchor_covector()
            .restrict(0..generated.boundary_components())?
            .view()
            .split_rows(incident.rows, incident.width)?;
        let source_covector =
            anchor.gather_phase_rows(source_sites, &phases(source_sites.len()), incident.width)?;
        let source_covector = source_covector.sum_same_shape(
            returned
                .source_covector
                .as_ref()
                .ok_or_else(|| invalid("missing codec source return"))?,
        )?;
        let encoder = incident
            .encoder
            .prepare_return(&pending.encoded, &source_covector, step_bits)
            .map_err(|error| invalid(format!("incident encoder return: {error}")))?;
        let encoder_returned = Instant::now();
        let boundary_return_receipt = section_face_receipt(&returned.boundary_covector)?;
        let text_return_receipt = returned
            .text_covector
            .as_ref()
            .map(section_face_receipt)
            .transpose()?;
        let encoder_cuts_before = incident.encoder.material_observations();
        let receiver_cuts_before = incident.receiver.material_observations();
        let producing_encoder_cuts = pending
            .encoded
            .producing
            .iter()
            .map(|material| material.observations())
            .collect::<Vec<_>>();
        let producing_receiver_cuts = json!({
            "text": comparison.text_material.observations(),
            "support": comparison.support_material.observations(),
            "text_cohorts": comparison.text_materials.iter().map(|material| material.observations()).collect::<Vec<_>>(),
        });
        let current_cut_before = self.body.epoch();
        let pending_before = self.body.pending_ids()?;
        let value = json!({"scope":"incident-field-observation","comparison":id,"producing_epoch":generated.producing_epoch(),
            "observed_response_symbols":target.len(),"material_deposited":true,"whole_joint_return":true,
            "retro_receiver":comparison.retro_provenance,"original_face_supports_target":retro.is_none(),
            "return_receipts":{"boundary_covector":boundary_return_receipt,"text_covector":text_return_receipt},
            "producing_cut":{"epoch":generated.producing_epoch(),"field_cut":generated.producing_field_cut(),"material_observations":generated.producing_material_observations()},
            "operator_bounds":generated.operator_bounds()?,
            "current_cut_before":current_cut_before,"pending_before":pending_before,
            "native_receipt":{"device":self.surface.device_name(),"kernel_sha256":self.surface.ptx_sha256(),"census_before_publication":self.surface.census()},
            "material_cuts_before":{"encoder":encoder_cuts_before,"receiver":receiver_cuts_before}});
        let mut value = value;
        value["native_receipt"]["stage_us"] = json!({
            "receiver_return": receiver_returned.duration_since(started).as_micros(),
            "field_return": field_returned.duration_since(receiver_returned).as_micros(),
            "encoder_return": encoder_returned.duration_since(field_returned).as_micros(),
            "receipt": encoder_returned.elapsed().as_micros(),
        });
        value["producing_material_cuts"] =
            json!({"encoder":producing_encoder_cuts,"receiver":producing_receiver_cuts});
        self.body.publish_incident_material_return(field)?;
        incident.encoder.publish(encoder);
        incident.receiver.publish(returned.successor);
        incident.pending.remove(&id);
        self.presentation.retained_shared.remove(&id);
        value["current_cut_after"] = json!(self.body.epoch());
        value["native_receipt"]["census_after_publication"] = json!(self.surface.census());
        value["material_cuts_after"] = json!({
            "encoder": incident.encoder.material_observations(),
            "receiver": incident.receiver.material_observations(),
        });
        value["material_update"] = json!(true);
        Ok(value)
    }
}
