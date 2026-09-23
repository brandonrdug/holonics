use super::*;
use crate::native::GeometricFieldSpec;
use holonic_engine::ExactComplexWaveCurrent;
use num_rational::BigRational as Rat;
use std::path::PathBuf;

#[path = "../../../examples/support/linked_torus_field.rs"]
mod linked_torus_field;

fn spec() -> FieldSessionSpec {
    FieldSessionSpec {
        symbols: vec!["a".into(), "b".into(), "c".into()],
        section_symbols: 7,
        context_symbols: 1,
        region_offsets: vec![],
        source_chart: FieldSourceChart::IncidentField,
        geometry: Some(linked_torus_field::linked_torus_field_spec(1, 2, 1).unwrap()),
        incident: Some(IncidentFieldOptions {
            participation: Default::default(),
            local_roots: 1,
            material_seed: 0x91_22_7a,
            response_aperture: 2,
            response_port_start: None,
            material_owners: vec![],
            solve_steps: 128,
            solver: crate::native::IncidentFieldSolver::Richardson,
        }),
        generator: None,
        codec: FieldTextCodec::UnicodeScalars,
        fractional_bits: 24,
    }
}

fn request(retain: bool) -> FieldSectionRequest {
    FieldSectionRequest {
        text: "ab".into(),
        partial: None,
        output_symbols: Some(4),
        context: vec!["c".into()],
        incident_preparation: None,
        commit: false,
        retain_comparison: retain,
    }
}

#[test]
fn incident_response_port_helper_preserves_legacy_and_rejects_overlap() {
    let legacy = spec();
    let preparation = IncidentPreparation::from_request(&legacy, &request(false)).unwrap();
    assert_eq!(
        incident_response_slots(&legacy, &preparation, &(0..7).collect::<Vec<_>>()).unwrap(),
        vec![3, 4]
    );
    let mut fixed = legacy.clone();
    fixed.incident.as_mut().unwrap().response_port_start = Some(5);
    assert_eq!(
        incident_response_slots(&fixed, &preparation, &(0..7).collect::<Vec<_>>()).unwrap(),
        vec![5, 6]
    );
    fixed.incident.as_mut().unwrap().response_port_start = Some(2);
    assert!(incident_response_slots(&fixed, &preparation, &(0..7).collect::<Vec<_>>()).is_err());
}

#[test]
#[ignore = "requires CUDA; the numerical solver persists in rest and a pending comparison is read with the solver in force"]
fn incident_solver_selection_survives_rest_and_reads_pending_at_the_contemporary_solver() {
    use crate::native::IncidentFieldSolver;
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("chebyshev.session");
    let spec = spec();
    let json = serde_json::to_value(&spec).unwrap();
    assert!(json["incident"].get("solver").is_none());
    let legacy: FieldSessionSpec = serde_json::from_value(json).unwrap();
    assert_eq!(
        legacy.incident.unwrap().solver,
        IncidentFieldSolver::Richardson
    );
    let (id, received) = with_field_session(&spec, |session| {
        let anchor = session.body.incident_current_boundary()?;
        let stale = session
            .body
            .prepare_incident_field(anchor.view(), &vec![false; anchor.view().components() / 2])?;
        session.configure_incident_solver(IncidentFieldSolver::Chebyshev, 128)?;
        // A prepared but unpublished word was produced with the former solver: refused.
        assert!(
            session
                .body
                .publish_incident_field(stale, false, false)
                .is_err()
        );
        let value = session.request(&request(true))?;
        let id = value["comparison"].as_u64().unwrap();
        let received = session.inspect_incident_comparison(id)?;
        // The pending comparison keeps no producing word, so it no longer pins the solver: it
        // is read with the solver in force, and reads the same again at the same solver.
        session.configure_incident_solver(IncidentFieldSolver::Richardson, 128)?;
        session.inspect_incident_comparison(id)?;
        session.configure_incident_solver(IncidentFieldSolver::Chebyshev, 128)?;
        assert_eq!(session.inspect_incident_comparison(id)?, received);
        session.checkpoint(&path, &HnaStreamState::default())?;
        Ok((id, received))
    })
    .unwrap();
    NativeFieldSavedSession::open(path)
        .unwrap()
        .with_session(|session, _| {
            assert_eq!(
                session.spec().incident.as_ref().unwrap().solver,
                IncidentFieldSolver::Chebyshev
            );
            assert_eq!(session.inspect_incident_comparison(id)?, received);
            session.observe(id, "ba", 3)?;
            let current = session.inspect_current()?;
            session.configure_incident_solver(IncidentFieldSolver::Richardson, 128)?;
            assert_eq!(session.inspect_current()?, current);
            Ok(())
        })
        .unwrap();
}

/// The keys of an observe that depend on the comparison's identity, its producing epoch or
/// the apparatus, not on what was read and returned at the cut.
fn at_the_cut(mut value: Value) -> Value {
    let object = value.as_object_mut().unwrap();
    for key in [
        "comparison",
        "producing_epoch",
        "native_receipt",
        "pending_before",
    ] {
        object.remove(key);
    }
    value
}

#[test]
#[ignore = "requires CUDA; a delayed incident comparison is read at the contemporary constitution, equals an immediate one there, and survives rest"]
fn public_incident_session_reads_a_delayed_comparison_at_the_contemporary_constitution() {
    let directory = tempfile::tempdir().unwrap();
    let path: PathBuf = directory.path().join("incident.session");
    let spec = spec();
    let mut short_request = request(false);
    short_request.text = "a".into();
    short_request.context.clear();
    short_request.output_symbols = Some(3);
    with_field_session(&spec, |session| {
        assert_eq!(
            session
                .spec()
                .incident
                .as_ref()
                .unwrap()
                .response_port_start,
            Some(5)
        );
        let long = session.request(&request(false))?;
        let short = session.request(&short_request)?;
        assert_eq!(long["receiver_bindings"], short["receiver_bindings"]);
        for returned in [&long, &short] {
            assert!(
                returned["receiver_bindings"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .all(|site| !returned["source_bindings"]
                        .as_array()
                        .unwrap()
                        .contains(site))
            );
        }
        assert!(
            long["source_bindings"].as_array().unwrap().len()
                > short["source_bindings"].as_array().unwrap().len()
        );
        Ok(())
    })
    .unwrap();
    // Save after a real receiver/material update and a codec admission while the first
    // comparison remains pending. Its reading follows the contemporary constitution.
    let saved = with_field_session(&spec, |session| {
        let first = session
            .request(&FieldSectionRequest {
                commit: true,
                ..request(true)
            })
            .expect("first committed request");
        let second = session
            .request(&request(true))
            .expect("second preview request");
        assert_eq!(first["source_cells"], 3);
        assert_eq!(first["response_aperture"], 2);
        assert_eq!(first["local_complex"], 3);
        let first_id = first["comparison"].as_u64().unwrap();
        let second_id = second["comparison"].as_u64().unwrap();
        let before_update = session.inspect_incident_comparison(first_id)?;
        let material_before = session.inspect_incident_boundary_material()?;
        session.admit_incident_source_texts(&["λ".to_owned()])?;
        let returned = session
            .observe(second_id, "λa", 3)
            .expect("second material return");
        assert_eq!(returned["comparison_cut"], "contemporary");
        assert_ne!(
            session.inspect_incident_boundary_material()?,
            material_before
        );
        // The delayed comparison is read through the updated encoder, field and receiver.
        let after_update = session.inspect_incident_comparison(first_id)?;
        assert_ne!(after_update["text_logits"], before_update["text_logits"]);
        assert_eq!(after_update["comparison_cut"], "contemporary");
        // Reading is not a publication.
        let current = session.inspect_current()?;
        let material = session.inspect_incident_boundary_material()?;
        assert_eq!(session.inspect_incident_comparison(first_id)?, after_update);
        assert_eq!(session.inspect_current()?, current);
        assert_eq!(session.inspect_incident_boundary_material()?, material);
        session
            .checkpoint(&path, &HnaStreamState::default())
            .expect("pending session checkpoint");
        Ok((first_id, after_update))
    })
    .unwrap();

    let uninterrupted = with_field_session(&spec, |session| {
        let first = session
            .request(&FieldSectionRequest {
                commit: true,
                ..request(true)
            })
            .expect("first committed request");
        let second = session
            .request(&request(true))
            .expect("second preview request");
        session.admit_incident_source_texts(&["λ".to_owned()])?;
        session.observe(second["comparison"].as_u64().unwrap(), "λa", 3)?;
        let returned = session.observe(first["comparison"].as_u64().unwrap(), "ba", 3)?;
        Ok((
            returned,
            session.inspect_current()?,
            session.inspect_incident_boundary_material()?,
        ))
    })
    .unwrap();

    let resumed = NativeFieldSavedSession::open(&path)
        .unwrap()
        .with_session(|session, _| {
            assert_eq!(session.inspect_incident_comparison(saved.0)?, saved.1);
            let before_invalid = session.inspect_current()?;
            assert!(session.observe(saved.0, "abcab", 3).is_err());
            assert_eq!(session.inspect_current()?, before_invalid);
            assert_eq!(session.inspect_incident_comparison(saved.0)?, saved.1);
            let resumed = session.observe(saved.0, "ba", 3)?;
            assert_eq!(resumed["comparison"], saved.0);
            assert!(session.observe(saved.0, "ba", 3).is_err());
            Ok((
                resumed,
                session.inspect_current()?,
                session.inspect_incident_boundary_material()?,
            ))
        })
        .unwrap();
    assert!(
        resumed.0["producing_epoch"].as_u64().unwrap()
            < resumed.0["current_cut_before"].as_u64().unwrap()
    );
    assert_eq!(
        resumed.0["read_cut"]["epoch"],
        resumed.0["current_cut_before"]
    );
    // Restart performs different transfers, but the read and returned relations agree.
    assert_eq!(at_the_cut(resumed.0.clone()), at_the_cut(uninterrupted.0));
    assert_eq!(resumed.1, uninterrupted.1);
    assert_eq!(resumed.2, uninterrupted.2);

    // The delayed return equals an immediate return made at the same constitution: at the saved
    // cut, the same request retained afresh and observed at once reads and returns the same
    // numbers, and leaves the same field, encoder and receiver.
    let immediate = NativeFieldSavedSession::open(&path)
        .unwrap()
        .with_session(|session, _| {
            let fresh = session.request(&request(true))?;
            let fresh_id = fresh["comparison"].as_u64().unwrap();
            assert_ne!(fresh_id, saved.0);
            let mut reading = session.inspect_incident_comparison(fresh_id)?;
            let mut delayed = saved.1.clone();
            for value in [&mut reading, &mut delayed] {
                let object = value.as_object_mut().unwrap();
                object.remove("comparison");
                object.remove("producing_epoch");
            }
            assert_eq!(reading, delayed, "one reading at one cut");
            let returned = session.observe(fresh_id, "ba", 3)?;
            Ok((
                returned,
                session.inspect_current()?,
                session.inspect_incident_boundary_material()?,
            ))
        })
        .unwrap();
    assert_eq!(at_the_cut(immediate.0), at_the_cut(resumed.0));
    assert_eq!(immediate.1, resumed.1);
    assert_eq!(immediate.2, resumed.2);
}

#[test]
#[ignore = "requires CUDA; an existing inferred mathematical product enters and continues the same incident field"]
fn mathematical_product_and_code_share_the_field_native_ports() {
    let fixture = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../research/experiments/native_performance_benchmark/consequences/2026-09-15/math-requests.jsonl"
    ));
    let construction = fixture
        .lines()
        .map(|line| serde_json::from_str::<Value>(line).unwrap())
        .map(|value| value["command"]["request"].clone())
        .find(|value| value["operation"] == "construct-bilinear")
        .unwrap();
    let q = |n: i64, d: i64| json!({"numerator":n.to_string(),"denominator":d.to_string()});
    let request: super::super::FieldMathematicalRequest = serde_json::from_value(json!({
        "operations":[construction,{"operation":"emit-rust","operator":0},
            {"operation":"apply-inputs","operator":0,
             "left":{"kind":"values","values":[q(1,4),q(3,8)]},
             "right":{"kind":"values","values":[q(1,2),q(5,8)]},
             "retain_product":true,"emit_output":false}],
        "source":{"kind":"product-output","product":0},
        "source_coordinates":[0],"receiver_coordinates":[0,3],"geometry_mode":1,"commit":true
    }))
    .unwrap();
    with_field_session(&spec(), |session| {
        let before = session.inspect_current()?;
        let value = session.mathematical_request(&request)?;
        assert_eq!(value["material_update"], false);
        assert_eq!(
            value["generated_scope"]["current_epoch"],
            session.body.epoch()
        );
        assert_eq!(value["operation_results"][1]["status"], "code-emitted");
        assert!(
            value["operation_results"][1]["source"]
                .as_str()
                .unwrap()
                .contains("pub fn holonic_apply")
        );
        let current = session.body.incident_current_boundary()?.view().inspect()?;
        let expected = ExactComplexWaveCurrent::new(
            Rat::new((-7).into(), 64.into()),
            Rat::new(22.into(), 64.into()),
        );
        assert_eq!(current.center[0], expected);
        assert_eq!(
            value["receiver_binding"]["ball"]["center"][0],
            serde_json::to_value(&expected).unwrap()
        );
        assert!(
            current.center[1..]
                .iter()
                .any(|z| z != &ExactComplexWaveCurrent::zero()),
            "the product must participate in the coupled field, beyond its held source face"
        );
        assert_ne!(session.inspect_current()?, before);
        let current = session.inspect_current()?;
        let mut wrong = request.clone();
        wrong.geometry_mode = holonic_engine::DimensionalWaveModeId(99);
        assert!(session.mathematical_request(&wrong).is_err());
        assert_eq!(session.inspect_current()?, current);
        Ok(())
    })
    .unwrap();
}

/// **A pre-12a incident session wire decodes and continues.** Its presentation carried a frozen
/// encoder/receiver cut per pending comparison (`frozen_text`, `frozen_support`,
/// `frozen_cohorts`, producing encoder columns) and its body the `\x01` frozen word. Both
/// decode: the presentation's pending entry is checked against the retained request and
/// dropped, the body's word becomes its boundary operand, and the comparison continues exactly
/// as the live session's at the same cut.
#[test]
#[ignore = "requires CUDA; a pre-12a incident session wire with frozen receiver cuts decodes and continues"]
fn a_pre_12a_incident_session_wire_decodes_and_continues() {
    use super::super::incident_application::rest::IncidentPendingRest;
    let directory = tempfile::tempdir().unwrap();
    let path: PathBuf = directory.path().join("legacy.session");
    let spec = spec();
    let live = with_field_session(&spec, |session| {
        let produced = session.request(&request(true))?;
        let id = produced["comparison"].as_u64().unwrap();
        let reading = session.inspect_incident_comparison(id)?;
        // The retired wire, as a pre-12a build wrote it.
        let incident = session.incident.as_ref().unwrap();
        let retained = session.presentation.retained_shared[&id].clone();
        let preparation = IncidentPreparation::from_request(&session.presentation.spec, &retained.request)?;
        let symbols = preparation
            .source_cells
            .iter()
            .map(|cell| cell.symbol_index)
            .collect::<Vec<_>>();
        let encoded = incident.encoder.encode(&symbols)?;
        let bytes = |rest: holonic_engine::native_ecology::constitutive_fibre::NormalMaterialRest| {
            let mut bytes = Vec::new();
            rest.write(&mut bytes).unwrap();
            bytes
        };
        let mut presentation = incident.rest()?;
        presentation.pending = vec![IncidentPendingRest {
            id,
            encoded_symbols: symbols,
            encoded_rows: encoded.rows.rest()?.canonical_bytes().map_err(invalid)?,
            encoded_row_count: encoded.rows.rows(),
            encoded_width: encoded.rows.components(),
            grain_bits: encoded.rows.grain().0,
            encoded_producing_material: incident
                .encoder
                .rest()?
                .into_iter()
                .map(bytes)
                .collect(),
            frozen_text: bytes(incident.receiver.text_rest()?),
            frozen_support: bytes(incident.receiver.support_rest()?),
            frozen_cohorts: incident.receiver.cohorts().to_vec(),
            frozen_cohort_material: incident
                .receiver
                .text_cohort_rests()?
                .into_iter()
                .map(bytes)
                .collect(),
            preparation,
        }];
        let header = serde_json::to_vec(&FieldSessionHeader {
            spec: session.presentation.spec.clone(),
            state: HnaStreamState::default(),
            pending_extents: BTreeMap::new(),
            retained_shared: session.presentation.retained_shared.clone(),
            issued_shared: session.presentation.issued_shared,
            exposure: None,
            incident: Some(presentation),
            generator: None,
        })?;
        let body = session.body.legacy_frozen_incident_rest()?;
        assert_eq!(&body[1..20], b"HNA-INCIDENT-FIELD\x01");
        let mut wire = INCIDENT_MAGIC.to_vec();
        for part in [&header, &body] {
            wire.extend((part.len() as u64).to_le_bytes());
            wire.extend(part.iter());
        }
        std::fs::write(&path, &wire)?;
        let returned = session.observe(id, "ba", 3)?;
        Ok((
            id,
            reading,
            returned,
            session.inspect_current()?,
            session.inspect_incident_boundary_material()?,
        ))
    })
    .unwrap();
    let (id, reading, returned, current, material) = live;
    NativeFieldSavedSession::open(&path)
        .unwrap()
        .with_session(|session, _| {
            assert_eq!(session.inspect_incident_comparison(id)?, reading);
            let again = session.observe(id, "ba", 3)?;
            assert_eq!(at_the_cut(again), at_the_cut(returned.clone()));
            assert_eq!(session.inspect_current()?, current);
            assert_eq!(session.inspect_incident_boundary_material()?, material);
            Ok(())
        })
        .unwrap();
}
