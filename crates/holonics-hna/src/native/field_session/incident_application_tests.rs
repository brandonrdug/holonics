use super::*;
use crate::native::GeometricFieldSpec;
use holonic_engine::{
    ExactComplexWaveCurrent, native_ecology::constitutive_fibre::ResidentNormalEnclosureSection,
};
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
            local_roots: 1,
            material_seed: 0x91_22_7a,
            response_aperture: 2,
            response_port_start: None,
            material_owners: vec![],
            solve_steps: 128,
        }),
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

type SectionSnapshot = Vec<(Vec<ExactComplexWaveCurrent>, Rat)>;

fn snapshot(section: &ResidentNormalEnclosureSection<'_>) -> SectionSnapshot {
    (0..section.rows())
        .map(|row| {
            let face = section.row(row).unwrap().inspect().unwrap();
            (face.center, face.radius)
        })
        .collect()
}

fn pending_snapshot(
    session: &NativeFieldSession<'_>,
    id: u64,
) -> (SectionSnapshot, SectionSnapshot, SectionSnapshot) {
    let pending = session.incident.as_ref().unwrap().pending.get(&id).unwrap();
    (
        snapshot(&pending.encoded.rows),
        snapshot(&pending.received.text_logits),
        snapshot(&pending.received.support_logits),
    )
}

#[test]
#[ignore = "requires CUDA; public incident session generation, delayed frozen receiver rest and reopen"]
fn public_incident_session_reopens_frozen_receiver_after_intervening_update() {
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
    // Save after a real receiver/material update while the first producing
    // comparison remains pending. Capture its frozen encoder/receiver faces.
    let (saved, frozen_before_update) = with_field_session(&spec, |session| {
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
        let frozen_before_update = pending_snapshot(session, first_id);
        session.admit_incident_source_texts(&["λ".to_owned()])?;
        let retro = session
            .observe(second_id, "λa", 3)
            .expect("second material return");
        assert_eq!(retro["original_face_supports_target"], false);
        assert_eq!(pending_snapshot(session, first_id), frozen_before_update);
        let current = session.inspect_current()?;
        session
            .checkpoint(&path, &HnaStreamState::default())
            .expect("pending session checkpoint");
        Ok(((first_id, current), frozen_before_update))
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
        Ok((returned, session.inspect_current()?))
    })
    .unwrap();

    let resumed = NativeFieldSavedSession::open(&path)
        .unwrap()
        .with_session(|session, _| {
            assert_eq!(pending_snapshot(session, saved.0), frozen_before_update);
            let before_invalid = session.inspect_current()?;
            let before_invalid_faces = pending_snapshot(session, saved.0);
            assert!(session.observe(saved.0, "abcab", 3).is_err());
            assert_eq!(session.inspect_current()?, before_invalid);
            assert_eq!(pending_snapshot(session, saved.0), before_invalid_faces);
            let later_cohort = session
                .incident
                .as_ref()
                .unwrap()
                .receiver
                .text_cohort_rests()?;
            let resumed = session.observe(saved.0, "ba", 3)?;
            assert_eq!(
                session
                    .incident
                    .as_ref()
                    .unwrap()
                    .receiver
                    .text_cohort_rests()?,
                later_cohort,
                "an old comparison must not add observations to later receiver rows"
            );
            assert_eq!(resumed["comparison"], saved.0);
            assert!(session.observe(saved.0, "ba", 3).is_err());
            Ok((resumed, session.inspect_current()?))
        })
        .unwrap();
    assert!(
        resumed.0["producing_cut"]["epoch"].as_u64().unwrap()
            < resumed.0["current_cut_before"].as_u64().unwrap()
    );
    let semantic_return = |mut value: Value| {
        // Restart performs different transfers, but the producing and returned relations agree.
        value.as_object_mut().unwrap().remove("native_receipt");
        value
    };
    assert_eq!(semantic_return(resumed.0), semantic_return(uninterrupted.0));
    assert_eq!(resumed.1, uninterrupted.1);
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
