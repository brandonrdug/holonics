use super::*;
use holonic_engine::native_ecology::constitutive_fibre::ResidentNormalEnclosureSection;
#[path = "../../../../examples/support/generator_machine.rs"]
mod generator_machine;

fn request(text: &str, commit: bool) -> FieldSectionRequest {
    FieldSectionRequest {
        text: text.into(),
        partial: None,
        output_symbols: None,
        context: vec![],
        incident_preparation: None,
        commit,
        retain_comparison: true,
    }
}
fn release_preview(session: &mut NativeFieldSession<'_>) -> Result<()> {
    let clock = session.generator.as_ref().unwrap().next_event;
    let preview = session.request(&request("a", false))?;
    let id = preview["comparison"].as_u64().unwrap();
    session.release(id)?;
    assert!(session.generator.as_ref().unwrap().pending.is_empty());
    assert!(session.retained_shared_comparisons().is_empty());
    assert_eq!(session.body.pending_coupled_predictions(), 0);
    assert_eq!(session.generator.as_ref().unwrap().next_event, clock);
    Ok(())
}
/// The contemporary reading of an outstanding comparison without its clock origin, which only
/// names witnesses: two comparisons of the same passage read at one cut must agree on it.
fn snapshot(session: &mut NativeFieldSession<'_>, id: u64) -> Value {
    let mut reading = session.generator_contemporary_reading(id).unwrap();
    reading.as_object_mut().unwrap().remove("start");
    reading
}

#[test]
fn generator_source_aperture_is_not_machine_population_or_legacy_slots() {
    let short = generator_machine::generator_session_spec(2, 4, 2).unwrap();
    let long = generator_machine::generator_session_spec(2, 1000, 2).unwrap();
    assert_eq!(
        short.generator.as_ref().unwrap().field.machine,
        long.generator.as_ref().unwrap().field.machine
    );
    assert_eq!(short.response_aperture().unwrap(), 2);
    assert_eq!(short.generator.as_ref().unwrap().receiver.aperture, 3);
    assert!(short.geometry.is_none() && short.incident.is_none());
    short.chart().unwrap();
    long.chart().unwrap();
    let wire = serde_json::to_value(&short).unwrap();
    assert_eq!(wire["source_chart"], "generator-machine");
    assert_eq!(wire["generator"]["receiver"]["kind"], "generator-phases");
    assert_eq!(
        wire["generator"]["field"]["enclosure_propagation"],
        "joint-ball"
    );
    let mut older = wire.clone();
    older["generator"]["field"]
        .as_object_mut()
        .unwrap()
        .remove("enclosure_propagation");
    let older: FieldSessionSpec = serde_json::from_value(older).unwrap();
    assert_eq!(
        older.generator.unwrap().field.enclosure_propagation,
        crate::native::NativeEnclosurePropagation::ComponentIntervals
    );
    assert_eq!(
        serde_json::from_value::<FieldSessionSpec>(wire).unwrap(),
        short
    );
}

#[test]
#[ignore = "requires CUDA; public ordered source moment, one-cut delayed reading, codec growth and restart"]
fn generator_session_returns_the_ordered_source_and_reopens_its_moment_comparison() {
    let directory = tempfile::tempdir().unwrap();
    let pending_path = directory.path().join("pending.hna");
    let direct_path = directory.path().join("direct.hna");
    let resumed_path = directory.path().join("resumed.hna");
    let spec = generator_machine::generator_session_spec(2, 6, 2).unwrap();
    let mut first = request("b", false);
    first.context = vec!["a".into()];
    let (id, contemporary) = super::super::with_field_session(&spec, |session| {
        let initial = session.inspect_current()?;
        let result = session.request(&first)?;
        assert_eq!(result["field_sites"], 2);
        assert_eq!(result["source_cells"], 2);
        assert_eq!(result["source_contacts"], 1);
        assert_eq!(result["response_aperture"], 2);
        assert_eq!(session.inspect_current()?, initial);
        assert_eq!(session.generator.as_ref().unwrap().next_event, 0);
        let id = result["comparison"].as_u64().unwrap();
        let pending = &session.generator.as_ref().unwrap().pending[&id];
        assert_eq!(pending.source_clock(), (0, 2));
        // Fixed in N: the alphabet binding only (occurrences of each admitted codec identity).
        assert_eq!(pending.symbol_counts().iter().sum::<usize>(), 2);
        assert_eq!(
            pending.pending_relation_words(),
            session.presentation.spec.symbols.len()
        );
        let produced = snapshot(session, id);
        session.admit_incident_source_texts(&["c".into()])?;
        // The intervening passage shares a symbol with the held one: its encoder column develops
        // too, and the held comparison is read through the contemporary encoder table.
        let second = session.request(&request("ba", true))?;
        assert_eq!(session.generator.as_ref().unwrap().next_event, 2);
        session.observe(second["comparison"].as_u64().unwrap(), "a", 8)?;
        // One cut: after an intervening update the outstanding comparison is read at the
        // contemporary constitution, not at its producing cut ...
        let contemporary = snapshot(session, id);
        assert_ne!(contemporary["text"], produced["text"]);
        // ... and equals a fresh reading of the same passage at that same cut.
        let fresh = session.request(&first)?;
        let fresh_id = fresh["comparison"].as_u64().unwrap();
        assert_eq!(snapshot(session, fresh_id), contemporary);
        session.release(fresh_id)?;
        let material = session
            .generator
            .as_ref()
            .unwrap()
            .receiver
            .inner()
            .support_material();
        assert_eq!(material.targets(), 2);
        assert_eq!(material.source_complex(), 7); // six native channels + homogeneous bias
        session.checkpoint(&pending_path, &HnaStreamState::default())?;
        let returned = session.observe(id, "c", 8)?;
        assert_eq!(returned["material_update"], true);
        assert_eq!(returned["comparison_cut"], "contemporary");
        assert_eq!(session.body.pending_coupled_predictions(), 0);
        release_preview(session)?;
        session.checkpoint(&direct_path, &HnaStreamState::default())?;
        Ok((id, contemporary))
    })
    .unwrap();
    let bytes = std::fs::read(&pending_path).unwrap();
    assert_eq!(&bytes[..GENERATOR_MAGIC.len()], GENERATOR_MAGIC);
    NativeFieldSavedSession::open(&pending_path)
        .unwrap()
        .with_session(|session, _| {
            assert_eq!(snapshot(session, id), contemporary);
            session.observe(id, "c", 8)?;
            release_preview(session)?;
            session.checkpoint(&resumed_path, &HnaStreamState::default())?;
            Ok(())
        })
        .unwrap();
    assert_eq!(
        std::fs::read(direct_path).unwrap(),
        std::fs::read(resumed_path).unwrap()
    );
}

/// A delayed observe and an immediate observe of the same passage at the same cut publish the
/// same continuing state: the delayed comparison is read, compared and pulled back at the
/// contemporary constitution, with nothing of its producing cut.
#[test]
#[ignore = "requires CUDA; delayed observe equals an immediate observe at one cut"]
fn generator_delayed_observe_is_one_cut_equal_to_an_immediate_observe() {
    let spec = generator_machine::generator_session_spec(2, 6, 2).unwrap();
    let state = |session: &mut NativeFieldSession<'_>| -> Result<Value> {
        let current = session.inspect_current()?;
        let rest = session.generator.as_ref().unwrap().rest()?;
        Ok(
            json!({"joint":current["joint"],"operator":current["operator"],
            "encoder":rest.encoder_material,"text":rest.receiver_text,
            "stop":rest.receiver_support}),
        )
    };
    // The intervening passage shares both symbols with the held one: the encoder columns the
    // held passage enters through change before it is observed, and the delayed comparison
    // reads them (and q₀, M, ρ, R) at the contemporary cut.
    let delayed = super::super::with_field_session(&spec, |session| {
        let held = session.request(&request("ab", false))?["comparison"]
            .as_u64()
            .unwrap();
        let update = session.request(&request("ba", true))?["comparison"]
            .as_u64()
            .unwrap();
        session.observe(update, "ab", 8)?;
        session.observe(held, "ba", 8)?;
        state(session)
    })
    .unwrap();
    let immediate = super::super::with_field_session(&spec, |session| {
        let update = session.request(&request("ba", true))?["comparison"]
            .as_u64()
            .unwrap();
        session.observe(update, "ab", 8)?;
        let held = session.request(&request("ab", false))?["comparison"]
            .as_u64()
            .unwrap();
        session.observe(held, "ba", 8)?;
        state(session)
    })
    .unwrap();
    for key in ["joint", "operator", "encoder", "text", "stop"] {
        assert_eq!(delayed[key], immediate[key], "{key}");
    }
}

#[test]
fn generator_pending_rest_refuses_the_pre_moment_wire() {
    let spec = generator_machine::generator_session_spec(2, 6, 2).unwrap();
    let current = rest::GeneratorPendingRest {
        id: 3,
        receiver_binding: spec.generator.as_ref().unwrap().receiver.clone(),
        start: 0,
        cells: 2,
        symbol_counts: vec![1, 1],
        record: GeneratorRetainedRecord {
            request_extent: 2,
            response_aperture: 2,
            output_symbols: 4,
            producing_epoch: 0,
            held_parts: 0,
            held_text_sha256: held_text_digest(""),
            exposure_pairing: None,
        },
    };
    let wire = serde_json::to_value(&current).unwrap();
    assert_eq!(
        serde_json::from_value::<rest::GeneratorPendingRest>(wire.clone()).unwrap(),
        current
    );
    for field in [
        "encoded_rows",
        "frozen_text",
        "encoded_producing_material",
        "preparation",
    ] {
        let mut old = wire.clone();
        old[field] = json!([1, 2, 3]);
        let error = serde_json::from_value::<rest::GeneratorPendingRest>(old)
            .unwrap_err()
            .to_string();
        assert!(error.contains("pre-moment wire"), "{field}: {error}");
    }
}

#[test]
#[ignore = "requires CUDA; observed targets change pair amplitudes without completed-event storage growth"]
fn generator_session_learns_pair_response_without_accumulating_completed_returns() {
    super::super::with_field_session(
        &generator_machine::generator_session_spec(2, 6, 2).unwrap(),
        |session| {
            let mut amplitudes = Vec::new();
            let mut before_change = None;
            for step in 0..6 {
                let entering = session.inspect_current()?;
                eprintln!(
                    "step {step}: radius {}, operator {}",
                    entering["joint"]["radius"], entering["operator"]
                );
                let generated = session
                    .request(&request(if step % 2 == 0 { "ab" } else { "ba" }, true))
                    .map_err(|error| {
                        invalid(format!(
                            "request step {step}: {error}; entering joint {}",
                            entering["joint"]
                        ))
                    })?;
                eprintln!("step {step}: generated {}, target {}", generated["text"], if step % 2 == 0 { "ba" } else { "ab" });
                let id = generated["comparison"].as_u64().unwrap();
                let probe_before = if step == 5 {
                    let probe = session.request(&request("ab", false))?;
                    let probe_id = probe["comparison"].as_u64().unwrap();
                    let phase = snapshot(session, probe_id)["phase"].as_array().unwrap().iter().map(|row| row["center"].clone()).collect::<Vec<_>>();
                    session.release(probe_id)?;
                    Some(phase)
                } else { None };
                let before = session.inspect_current()?;
                session
                    .observe(id, if step % 2 == 0 { "ba" } else { "ab" }, 8)
                    .map_err(|error| invalid(format!("observe step {step}: {error}")))?;
                let after = session.inspect_current()?;
                assert_eq!(
                    before["joint"], after["joint"],
                    "learning must not replay or recommit source current"
                );
                assert_eq!(after["operative_storage"]["returns"], 0);
                assert_eq!(session.body.pending_coupled_predictions(), 0);
                assert!(session.generator.as_ref().unwrap().pending.is_empty());
                assert!(session.retained_shared_comparisons().is_empty());
                let rho = after["operator"]["declared_amplitudes"]
                    .as_array()
                    .expect("pair amplitudes")
                    .clone();
                assert!(!rho.is_empty());
                if before["operator"]["declared_amplitudes"]
                    != after["operator"]["declared_amplitudes"]
                {
                    before_change = Some((
                        before["operator"]["declared_amplitudes"].clone(),
                        after["operator"]["declared_amplitudes"].clone(),
                    ));
                }
                amplitudes.push(rho);
                if let Some(phase_before) = probe_before {
                    let probe = session.request(&request("ab", false))?;
                    let probe_id = probe["comparison"].as_u64().unwrap();
                    assert_ne!(snapshot(session, probe_id)["phase"].as_array().unwrap().iter().map(|row| row["center"].clone()).collect::<Vec<_>>(), phase_before,
                        "published material must change later generation at the same source and clock");
                    eprintln!("post-update same-source probe text: {}", probe["text"]);
                    session.release(probe_id)?;
                }
            }
            assert!(
                amplitudes.windows(2).any(|w| w[0] != w[1]),
                "observed targets must change pair response after boundary material develops"
            );
            let radius: relational_geometry::Rat = serde_json::from_value(session.inspect_current()?["joint"]["radius"].clone()).unwrap();
            eprintln!("final joint radius: {radius}");
            eprintln!(
                "observed pair amplitude change: {:?}",
                before_change.unwrap()
            );
            Ok(())
        },
    )
    .unwrap();
}

/// The session's pending comparison is fixed in the passage length: its rest (clock, length,
/// receiving binding, alphabet binding) and the body's retained source Holon (per-symbol sums).
#[test]
#[ignore = "requires CUDA; prints pending octets against passage length"]
fn generator_pending_is_fixed_in_the_passage_length() {
    let spec = generator_machine::generator_session_spec(2, 128, 2).unwrap();
    super::super::with_field_session(&spec, |session| {
        let mut sizes = Vec::new();
        for n in [2usize, 8, 32, 128] {
            let text = "ab".repeat(n / 2);
            let id = session.request(&request(&text, false))?["comparison"]
                .as_u64()
                .unwrap();
            let rest = session.generator.as_ref().unwrap().rest()?;
            let pending = rest.pending.iter().find(|p| p.id == id).unwrap();
            let session_octets = serde_json::to_vec(pending)?.len();
            let body = session.body.generator_comparison_census(id)?;
            assert!(session.presentation.retained_shared.is_empty());
            // End to end: the whole public checkpoint with the comparison held, minus after its
            // release (the request did not commit, so q/b and material are unchanged).
            let directory = tempfile::tempdir()?;
            let held_path = directory.path().join("held.hna");
            let released_path = directory.path().join("released.hna");
            session.checkpoint(&held_path, &HnaStreamState::default())?;
            session.release(id)?;
            session.checkpoint(&released_path, &HnaStreamState::default())?;
            let checkpoint_octets = std::fs::metadata(&held_path)?.len() as i64
                - std::fs::metadata(&released_path)?.len() as i64;
            eprintln!(
                "PENDING-VS-N {}",
                json!({"cells":n,"session_octets":session_octets,"body":body,
                    "checkpoint_octets":checkpoint_octets})
            );
            sizes.push((session_octets, body["octets"].as_u64().unwrap()));
        }
        assert!(sizes.windows(2).all(|w| w[0].1 == w[1].1), "{sizes:?}");
        // The session rest varies only in the decimal width of `cells`/counts.
        assert!(
            sizes.iter().all(|s| s.0.abs_diff(sizes[0].0) <= 8),
            "{sizes:?}"
        );
        Ok(())
    })
    .unwrap();
}

/// Silent-source control: a passage whose encoder table is zero adds no moment and no
/// condition, so each commit publishes the incident word acting on the standing current alone.
/// Reports the committed current's energy per commit and the ratio to the previous commit.
#[test]
#[ignore = "requires CUDA; prints the committed current's energy under a silent source"]
fn generator_silent_source_commit_energy() {
    let spec = generator_machine::generator_session_spec(2, 6, 2).unwrap();
    super::super::with_field_session(&spec, |session| {
        // Seed a nonzero standing with one ordinary committed passage, then go silent.
        session.request(&FieldSectionRequest {
            retain_comparison: false,
            ..request("ab", true)
        })?;
        let options = spec.generator.as_ref().unwrap().clone();
        let sites = options.field.machine.sites().len();
        let alphabet = session.presentation.spec.symbols.len();
        let width = options.source.injection_sites.len() * 6;
        let mut previous: Option<f64> = None;
        for commit in 0..40u64 {
            let table = Rc::new(
                ResidentNormalEnclosureSection::zeros(
                    session.surface,
                    alphabet,
                    width,
                    ResidentGrain(spec.fractional_bits),
                )
                .map_err(invalid)?,
            );
            let start = session.generator.as_ref().unwrap().next_event;
            let generated = session.body.prepare_generator_symbol_episode(
                table,
                &[0, 1],
                options.source.clone(),
                start,
                Vec::new(),
            )?;
            session
                .body
                .publish_incident_field(generated, true, false)?;
            session.generator.as_mut().unwrap().next_event += 2;
            let current = session.body.inspect_current()?;
            let energies = super::super::measurement::site_energies(&current["joint"], sites);
            let total = energies.iter().flatten().sum::<f64>();
            let radius: relational_geometry::Rat =
                serde_json::from_value(current["joint"]["radius"].clone()).unwrap();
            eprintln!(
                "SILENT {}",
                json!({"commit":commit,"energy":total,"sites":energies,
                    "ratio":previous.map(|p| total / p),"radius":radius.to_string(),
                    "rebase":current.get("rebase_residual")})
            );
            previous = Some(total);
        }
        Ok(())
    })
    .unwrap();
}
