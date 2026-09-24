//! Athena's incident-field application binding. The same exposure cursor and public session
//! call prepare source rows, execute one joint field word, and receive its text/support faces.
use super::boundary::BoundaryMaterial;
use super::incident_encoder::{IncidentEncoded, IncidentEncoder};
use super::incident_receiver::{IncidentTextForward, IncidentTextReceiver};
use super::*;
use holonic_engine::{
    ExactWavePhaseTransport,
    native_ecology::constitutive_fibre::{BoundaryMaterialSeed, ResidentNormalEnclosureSection},
    resident_section::SeriesAperture,
};
mod codec;
mod rest;
pub(super) use rest::IncidentPresentationRest;

/// The incident chart's presentation boundary: its encoder, text receiver and fixed slots. An
/// outstanding comparison is the session's `RetainedSharedSource` (the request that re-derives
/// its source cells) beside the body's retained boundary operands; both are read at the
/// contemporary constitution when the comparison returns, so this presentation keeps no
/// per-comparison producing state.
pub(super) struct IncidentPresentation<'c> {
    encoder: IncidentEncoder<'c>,
    receiver: IncidentTextReceiver<'c>,
    slot_rows: Vec<usize>,
    rows: usize,
    width: usize,
    series: u32,
}

/// One incident source at the contemporary cut: its cells encoded through the current encoder
/// and held on their source sites of the current boundary, with the fixed response sites. A
/// request prepares its word from it; an observe or inspection re-reads a retained comparison
/// from it, so production and return are one computation.
struct IncidentBoundaryCut<'c> {
    encoded: IncidentEncoded<'c>,
    anchor: holonic_engine::native_ecology::constitutive_fibre::ResidentNormalEnclosure<'c>,
    held: Vec<bool>,
    source_sites: Vec<usize>,
    response_sites: Vec<usize>,
    contacts: Vec<(usize, usize)>,
}

/// The receiving face of one incident word: its fixed response rows and the text/support
/// receiver read at the contemporary receiver material.
struct IncidentReading<'c> {
    response: ResidentNormalEnclosureSection<'c>,
    received: IncidentTextForward<'c>,
}
fn phases(n: usize) -> Vec<ExactWavePhaseTransport> {
    vec![ExactWavePhaseTransport::identity(); n]
}

pub(super) fn incident_response_slots(
    spec: &FieldSessionSpec,
    preparation: &IncidentPreparation,
    slot_rows: &[usize],
) -> Result<Vec<usize>> {
    let aperture = spec.response_aperture()?;
    let options = spec
        .incident
        .as_ref()
        .ok_or_else(|| invalid("incident material declaration"))?;
    let start = options
        .response_port_start
        .unwrap_or(preparation.source_extent);
    let end = start
        .checked_add(aperture)
        .ok_or_else(|| invalid("incident response port extent"))?;
    if preparation.response_aperture != aperture
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
        if let Some(options) = self.presentation.spec.generator.as_mut() {
            self.body.configure_incident_solver(solver, steps)?;
            options.field.solver = solver;
            options.field.solve_steps = steps;
            return Ok(());
        }
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

    /// Read an outstanding incident comparison at the contemporary constitution: its source
    /// cells encoded through the current encoder onto the current boundary, its word through the
    /// current field and material, and its text/support faces through the current receiver. This
    /// is the reading an immediate comparison of the same request would give at this cut; it
    /// changes after an intervening update, and nothing is committed, deposited or published.
    pub fn inspect_incident_comparison(&mut self, id: u64) -> Result<Value> {
        let retained = self
            .presentation
            .retained_shared
            .get(&id)
            .cloned()
            .filter(|_| self.incident.is_some())
            .ok_or_else(|| invalid("missing incident comparison"))?;
        let preparation = IncidentPreparation::from_request(&self.presentation.spec, &retained.request)?;
        let cut = self.incident_boundary(&preparation)?;
        if cut.held != retained.held {
            return Err(invalid("incident retained receiver chart differs"));
        }
        let word = self
            .body
            .contemporary_incident_comparison_at(id, cut.anchor.view(), &cut.held)?;
        let reading = self.incident_reading(&word, &cut)?;
        let forward = &reading.received;
        Ok(json!({
            "comparison": id,
            "comparison_cut": "contemporary",
            "producing_epoch": retained.producing_epoch,
            "read_epoch": word.producing_epoch(),
            "encoded_source": section_face_receipt(&cut.encoded.rows)?,
            "text_features": section_face_receipt(&forward.text_features)?,
            "text_logits": section_face_receipt(&forward.text_logits)?,
            "text_normalized": section_face_receipt(forward.text_face.participation())?,
            "support_logits": section_face_receipt(&forward.support_logits)?,
            "support_normalized": section_face_receipt(forward.support_face.participation())?,
        }))
    }

    /// The incident source of `preparation` at the contemporary cut (see `IncidentBoundaryCut`).
    fn incident_boundary(
        &mut self,
        preparation: &IncidentPreparation,
    ) -> Result<IncidentBoundaryCut<'c>> {
        let incident = self
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident session state"))?;
        let response_sites =
            incident_response_slots(&self.presentation.spec, preparation, &incident.slot_rows)?;
        let symbols = preparation
            .source_cells
            .iter()
            .map(|s| s.symbol_index)
            .collect::<Vec<_>>();
        let encoded = incident.encoder.encode(&symbols)?;
        let source_sites = incident.slot_rows[..preparation.source_extent].to_vec();
        let source = encoded.rows.scatter_phase_adjoint(
            &source_sites,
            &phases(source_sites.len()),
            incident.rows,
        )?;
        let (rows, width) = (incident.rows, incident.width);
        let current = self
            .body
            .incident_current_boundary()?
            .view()
            .split_rows(rows, width)?;
        let mut held = vec![false; rows * (width / 2)];
        for &site in &source_sites {
            held[site * (width / 2)..(site + 1) * (width / 2)].fill(true);
        }
        let anchor = current
            .held_refinement(&source, &held, 0)?
            .pack_components(rows)?
            .row(0)?
            .to_owned()?;
        let contacts = preparation
            .contacts
            .iter()
            .map(|c| (source_sites[c.from_cell], source_sites[c.to_cell]))
            .collect::<Vec<_>>();
        Ok(IncidentBoundaryCut {
            encoded,
            anchor,
            held,
            source_sites,
            response_sites,
            contacts,
        })
    }

    /// The response rows of `word` on the fixed response sites and their faces at the current
    /// receiver material.
    fn incident_reading(
        &self,
        word: &crate::native::NativeIncidentGenerated<'c>,
        cut: &IncidentBoundaryCut<'c>,
    ) -> Result<IncidentReading<'c>> {
        let incident = self
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident session state"))?;
        let boundary = word
            .boundary()?
            .view()
            .split_rows(incident.rows, incident.width)?;
        let response = boundary.gather_phase_rows(
            &cut.response_sites,
            &phases(cut.response_sites.len()),
            incident.width,
        )?;
        let received = incident
            .receiver
            .forward(&response, SeriesAperture(incident.series))?;
        Ok(IncidentReading { response, received })
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
            generator: None,
            incident: Some(IncidentPresentation {
                encoder,
                receiver,
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
        let aperture = self
            .presentation
            .spec
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident material declaration"))?
            .response_aperture;
        if preparation.response_aperture != aperture {
            let slots = self
                .incident
                .as_ref()
                .ok_or_else(|| invalid("incident session state"))?
                .slot_rows
                .len();
            return Err(invalid(format!(
                "complete incident source and response require {}+{} sites; declared slots={}, response aperture={}",
                preparation.source_extent, preparation.response_aperture, slots, aperture
            )));
        }
        let cut = self.incident_boundary(&preparation)?;
        let generated = self.body.prepare_incident_field_restricted(
            cut.anchor.view(),
            &cut.held,
            &cut.source_sites,
            &cut.contacts,
        )?;
        let IncidentReading { response, received } = self.incident_reading(&generated, &cut)?;
        let incident = self
            .incident
            .as_ref()
            .ok_or_else(|| invalid("incident session state"))?;
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
        let producing_receiver_cuts = json!({
            "text": received.text_material.observations(),
            "support": received.support_material.observations(),
            "text_cohorts": received.text_materials.iter().map(|material| material.observations()).collect::<Vec<_>>(),
        });
        let codec_revision = incident.receiver.codec_version();
        let (rows, width) = (incident.rows, incident.width);
        let pending_before = self.body.pending_ids()?;
        let current_cut_before = self.body.epoch();
        let mut value = json!({"schema":"org.holonics.hna.field-section.v1","scope":"incident-field-joint","source_chart":"incident-field",
            "codec":"unicode-scalars","codec_symbols":self.presentation.spec.symbols,"codec_revision":codec_revision,
            "text":text,"symbols":selected[..support].iter().map(|&i|&self.presentation.spec.symbols[i]).collect::<Vec<_>>(),
            "support":support,"response_aperture":aperture,"output_symbols":preparation.request_extent+aperture,
            "selections":selections,"support_selection":support_selection,"selection_chart":"real-receiver-potentials",
            "response_section":response_section,"receiver_faces":{"support_logits":support_logits_receipt,"support_normalized":support_face_receipt},
            "uncertainty":{"text_logits_radius":text_logits_receipt,"text_normalized_radius":text_face_receipt},
            "source_bindings":cut.source_sites,"receiver_bindings":cut.response_sites,
            "material_cuts":{"encoder":encoder_material_cuts,"receiver":receiver_material_cuts,"producing_encoder":encoder_material_cuts,"producing_receiver":producing_receiver_cuts},
            "producing_cut":{"epoch":generated.producing_epoch(),"field_cut":generated.producing_field_cut(),"material_observations":generated.producing_material_observations()},
            "operator_bounds":generated.operator_bounds()?,
            "solver":self.presentation.spec.incident.as_ref().map(|o| json!({"method":o.solver,"steps":o.solve_steps})),
            "current_cut_before":current_cut_before,"pending_before":pending_before,
            "material_update":false,
            "source_cells":preparation.source_extent,"context_cells":preparation.context_extent,"source_contacts":cut.contacts.len(),
            "field_sites":rows,"local_complex":width/2,"producing_epoch":generated.producing_epoch(),
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
            // The comparison keeps its request (which re-derives its source cells) and its
            // receiver mask; the body keeps its boundary operands. Both are read again at the
            // contemporary constitution when it returns.
            self.presentation.retained_shared.insert(
                id,
                RetainedSharedSource {
                    request: request.clone(),
                    held: cut.held,
                    output_symbols: preparation.request_extent + aperture,
                    producing_epoch: generated.producing_epoch(),
                    exposure_pairing: None,
                },
            );
            value["comparison"] = json!(id);
        }
        Ok(value)
    }

    /// Observe a retained incident comparison at one contemporary cut: its source cells are
    /// encoded through the current encoder onto the current boundary, its word is read through
    /// the current field and material, its faces through the current receiver, and the ratio's
    /// covector returns through those same operands to the receiver, the field and the encoder.
    /// A delayed observe therefore equals an immediate observe of the same request made at the
    /// same constitution, number for number (`delayed_incident_observe_equals_an_immediate_one`).
    pub(super) fn incident_observe(
        &mut self,
        id: u64,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        let started = Instant::now();
        let retained = self
            .presentation
            .retained_shared
            .get(&id)
            .cloned()
            .filter(|_| self.incident.is_some())
            .ok_or_else(|| invalid("unknown incident boundary comparison"))?;
        let preparation = IncidentPreparation::from_request(&self.presentation.spec, &retained.request)?;
        let target = self
            .presentation
            .spec
            .symbols_of(&self.presentation.chart, text)?
            .into_iter()
            .map(|s| s.0 as usize)
            .collect::<Vec<_>>();
        let source_classes = preparation
            .source_cells
            .iter()
            .map(|c| c.symbol_index)
            .collect::<Vec<_>>();
        let cut = self.incident_boundary(&preparation)?;
        if cut.held != retained.held {
            return Err(invalid("incident retained receiver chart differs"));
        }
        let word = self
            .body
            .contemporary_incident_comparison_at(id, cut.anchor.view(), &cut.held)?;
        let IncidentReading { received, .. } = self.incident_reading(&word, &cut)?;
        let incident = self
            .incident
            .as_mut()
            .ok_or_else(|| invalid("incident session state"))?;
        let returned = incident
            .receiver
            .compare_with_codec(
                &received,
                &target,
                target.len(),
                &cut.encoded.rows,
                &source_classes,
                SeriesAperture(incident.series),
                step_bits,
            )
            .map_err(|error| invalid(format!("incident receiver comparison: {error}")))?;
        let receiver_returned = Instant::now();
        let response_covector = returned
            .boundary_covector
            .split_components(preparation.response_aperture)?;
        let boundary = response_covector
            .scatter_phase_adjoint(
                &cut.response_sites,
                &phases(cut.response_sites.len()),
                incident.rows,
            )?
            .pack_components(incident.rows)?;
        let full = boundary.gather_phase_rows(&[0], &phases(1), word.joint_output().components())?;
        let field = self
            .body
            .prepare_contemporary_material_return(&word, full.row(0)?, step_bits, &[])
            .map_err(|error| invalid(format!("incident field material return: {error}")))?;
        let field_returned = Instant::now();
        let anchor = field
            .anchor_covector()
            .restrict(0..word.boundary_components())?
            .view()
            .split_rows(incident.rows, incident.width)?;
        let source_covector = anchor.gather_phase_rows(
            &cut.source_sites,
            &phases(cut.source_sites.len()),
            incident.width,
        )?;
        let source_covector = source_covector.sum_same_shape(
            returned
                .source_covector
                .as_ref()
                .ok_or_else(|| invalid("missing codec source return"))?,
        )?;
        let encoder = incident
            .encoder
            .prepare_return(&cut.encoded, &source_covector, step_bits)
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
        let current_cut_before = self.body.epoch();
        let pending_before = self.body.pending_ids()?;
        let mut value = json!({"scope":"incident-field-observation","comparison":id,"producing_epoch":retained.producing_epoch,
            "comparison_cut":"contemporary",
            "observed_response_symbols":target.len(),"material_deposited":true,"whole_joint_return":true,
            "return_receipts":{"boundary_covector":boundary_return_receipt,"text_covector":text_return_receipt},
            "read_cut":{"epoch":word.producing_epoch(),"field_cut":word.producing_field_cut(),"material_observations":word.producing_material_observations()},
            "operator_bounds":word.operator_bounds()?,
            "current_cut_before":current_cut_before,"pending_before":pending_before,
            "native_receipt":{"device":self.surface.device_name(),"kernel_sha256":self.surface.ptx_sha256(),"census_before_publication":self.surface.census()},
            "material_cuts_before":{"encoder":encoder_cuts_before,"receiver":receiver_cuts_before}});
        value["native_receipt"]["stage_us"] = json!({
            "receiver_return": receiver_returned.duration_since(started).as_micros(),
            "field_return": field_returned.duration_since(receiver_returned).as_micros(),
            "encoder_return": encoder_returned.duration_since(field_returned).as_micros(),
            "receipt": encoder_returned.elapsed().as_micros(),
        });
        self.body.publish_incident_material_return(field)?;
        let incident = self
            .incident
            .as_mut()
            .ok_or_else(|| invalid("incident session state"))?;
        incident.encoder.publish(encoder);
        incident.receiver.publish(returned.successor);
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
