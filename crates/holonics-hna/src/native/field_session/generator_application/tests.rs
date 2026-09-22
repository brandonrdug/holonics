use super::*;
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
fn snapshot(session: &NativeFieldSession<'_>, id: u64) -> Value {
    let pending = &session.generator.as_ref().unwrap().pending[&id];
    json!({"source":pending.encoded.rows.inspect_rows().unwrap(),
        "phase":pending.phases.output().inspect_rows().unwrap(),
        "text":pending.received.text_logits.inspect_rows().unwrap(),
        "stop":pending.received.support_logits.inspect_rows().unwrap(),
        "binding":pending.phases.binding(),"start":pending.start})
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
        serde_json::from_value::<FieldSessionSpec>(wire).unwrap(),
        short
    );
}

#[test]
#[ignore = "requires CUDA; public ordered source, phase stop, codec growth and frozen restart"]
fn generator_session_returns_the_ordered_source_and_reopens_its_frozen_comparison() {
    let directory = tempfile::tempdir().unwrap();
    let pending_path = directory.path().join("pending.hna");
    let direct_path = directory.path().join("direct.hna");
    let resumed_path = directory.path().join("resumed.hna");
    let spec = generator_machine::generator_session_spec(2, 6, 2).unwrap();
    let (id, frozen) = super::super::with_field_session(&spec, |session| {
        let initial = session.inspect_current()?;
        let mut first = request("b", false);
        first.context = vec!["a".into()];
        let result = session.request(&first)?;
        assert_eq!(result["field_sites"], 2);
        assert_eq!(result["source_cells"], 2);
        assert_eq!(result["source_contacts"], 1);
        assert_eq!(result["response_aperture"], 2);
        assert_eq!(session.inspect_current()?, initial);
        assert_eq!(session.generator.as_ref().unwrap().next_event, 0);
        let id = result["comparison"].as_u64().unwrap();
        let frozen = snapshot(session, id);
        session.admit_incident_source_texts(&["c".into()])?;
        let second = session.request(&request("ba", true))?;
        assert_eq!(session.generator.as_ref().unwrap().next_event, 2);
        session.observe(second["comparison"].as_u64().unwrap(), "a", 8)?;
        assert_eq!(snapshot(session, id), frozen);
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
        assert_eq!(session.body.pending_coupled_predictions(), 0);
        release_preview(session)?;
        session.checkpoint(&direct_path, &HnaStreamState::default())?;
        Ok((id, frozen))
    })
    .unwrap();
    let bytes = std::fs::read(&pending_path).unwrap();
    assert_eq!(&bytes[..GENERATOR_MAGIC.len()], GENERATOR_MAGIC);
    NativeFieldSavedSession::open(&pending_path)
        .unwrap()
        .with_session(|session, _| {
            assert_eq!(snapshot(session, id), frozen);
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
