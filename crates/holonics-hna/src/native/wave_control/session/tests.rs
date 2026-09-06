use super::*;
const WAVE: &[u8] = include_bytes!(
    "../../../../../../applications/holonics-workbench/examples/native/wave-control.json"
);
fn spec() -> WaveControlSpec {
    serde_json::from_slice(WAVE).unwrap()
}
fn snapshot(app: &WaveApplication) -> Vec<u8> {
    serde_json::to_vec(app).unwrap()
}

#[test]
#[ignore = "requires CUDA; whole application/model split and subsequent exact world consequences"]
fn paired_application_cut_preserves_all_world_cycles_and_the_complete_artifact() {
    let dir = tempfile::tempdir().unwrap();
    let spec = spec();
    let whole_path = dir.path().join("whole.hna");
    let whole = run_wave_control_with_options(
        &spec,
        &WaveRunOptions {
            cycles: None,
            checkpoint: Some(whole_path.clone()),
        },
    )
    .unwrap();
    assert!(whole.complete && whole.persistent);
    assert!(whole.interruption.is_none());
    let cut_path = dir.path().join("cut.hna");
    let first = run_wave_control_with_options(
        &spec,
        &WaveRunOptions {
            cycles: Some(3),
            checkpoint: Some(cut_path.clone()),
        },
    )
    .unwrap();
    assert!(!first.complete && first.persistent);
    assert_eq!(first.next_cycle, 3);
    let next_path = dir.path().join("next.hna");
    let next = resume_wave_control(
        &cut_path,
        &WaveRunOptions {
            cycles: None,
            checkpoint: Some(next_path.clone()),
        },
    )
    .unwrap();
    assert!(next.complete && next.persistent);
    assert_eq!(next.cycles.len(), 5);
    let mut cycles = first.cycles;
    cycles.extend(next.cycles);
    assert_eq!(
        serde_json::to_value(cycles).unwrap(),
        serde_json::to_value(whole.cycles).unwrap()
    );
    assert_eq!(next.final_world_state, whole.final_world_state);
    assert_eq!(next.final_unactuated_state, whole.final_unactuated_state);
    assert_eq!(
        std::fs::read(whole_path).unwrap(),
        std::fs::read(next_path).unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; partial interventions and enacted world effects are not replayed"]
fn partial_intervention_and_pending_world_effect_remount_at_their_exact_boundaries() {
    let dir = tempfile::tempdir().unwrap();
    let mut spec = spec();
    spec.cycles = 2;
    spec.interventions = vec![
        WaveIntervention {
            before_cycle: 0,
            change: WaveChange::Rechart {
                gauges: vec![CurrentWire::integers(0, 1), CurrentWire::integers(1, 0)],
            },
        },
        WaveIntervention {
            before_cycle: 0,
            change: WaveChange::ReplaceIncidence {
                node: 1,
                transport: CurrentWire::integers(-1, 0),
            },
        },
    ];
    let cut = dir.path().join("one-intervention.hna");
    with_native_session(&spec.model, |session| {
        let mut app = WaveApplication::found(&spec, session)?;
        app.advance_boundary(session)?;
        assert_eq!(app.boundary(), WaveBoundary::Intervention);
        assert_eq!(app.intervention_cursor(), 1);
        assert_eq!(session.inspect().frame, 1);
        app.checkpoint(session, &cut)?;
        Ok(())
    })
    .unwrap();
    let pending = dir.path().join("world-enacted.hna");
    let pending_snapshot = WaveSavedApplication::read(&cut)
        .unwrap()
        .with_application(|session, app| {
            app.advance_boundary(session)?;
            assert_eq!(session.inspect().frame, 1, "first gauge was not repeated");
            assert_eq!(app.intervention_cursor(), 2);
            assert_eq!(app.boundary(), WaveBoundary::World);
            let cycle = app.advance_boundary(session)?.unwrap();
            assert_eq!(app.world_state(), &cycle.world_state);
            assert_eq!(app.boundary(), WaveBoundary::Reception);
            assert_eq!(session.occurrence_count(), 1);
            app.checkpoint(session, &pending)?;
            Ok(snapshot(app))
        })
        .unwrap();
    let final_path = dir.path().join("continued.hna");
    WaveSavedApplication::read(&pending)
        .unwrap()
        .with_application(|session, app| {
            assert_eq!(snapshot(app), pending_snapshot);
            let world = app.world_state().clone();
            let control = app.unactuated_state().clone();
            assert!(app.advance_boundary(session)?.is_none());
            assert_eq!(app.world_state(), &world);
            assert_eq!(app.unactuated_state(), &control);
            assert_eq!(session.occurrence_count(), 2);
            execute(
                app,
                session,
                &WaveRunOptions {
                    cycles: None,
                    checkpoint: Some(final_path.clone()),
                },
            )?;
            Ok(())
        })
        .unwrap();
    let whole = dir.path().join("whole.hna");
    run_wave_control_with_options(
        &spec,
        &WaveRunOptions {
            cycles: None,
            checkpoint: Some(whole.clone()),
        },
    )
    .unwrap();
    assert_eq!(
        std::fs::read(whole).unwrap(),
        std::fs::read(final_path).unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; a refused native reception retains its prior exterior effect across process-capable rest"]
fn exact_aperture_refusal_remains_pending_without_repeating_the_world() {
    let dir = tempfile::tempdir().unwrap();
    let mut spec = spec();
    spec.cycles = 2;
    spec.interventions.clear();
    spec.world.couplings[0] = CurrentWire::integers(i64::MAX, 0);
    let first_path = dir.path().join("pending.hna");
    let first = run_wave_control_with_options(
        &spec,
        &WaveRunOptions {
            cycles: None,
            checkpoint: Some(first_path.clone()),
        },
    )
    .unwrap();
    assert_eq!(first.cycles.len(), 1);
    assert!(first.persistent && !first.complete);
    assert_eq!(first.boundary, WaveBoundary::Reception);
    assert_eq!(first.anatomy.occurrences, 1);
    let next_path = dir.path().join("pending-again.hna");
    let next = resume_wave_control(
        &first_path,
        &WaveRunOptions {
            cycles: None,
            checkpoint: Some(next_path.clone()),
        },
    )
    .unwrap();
    assert!(next.cycles.is_empty());
    assert_eq!(next.final_world_state, first.final_world_state);
    assert_eq!(next.final_unactuated_state, first.final_unactuated_state);
    assert_eq!(next.anatomy.occurrences, 1);
    assert!(next.persistent);
    assert_eq!(
        std::fs::read(first_path).unwrap(),
        std::fs::read(next_path).unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; application/native mismatches refuse without learner or world effects"]
fn corrupted_application_boundary_and_plain_session_usage_are_refused() {
    let dir = tempfile::tempdir().unwrap();
    let spec = spec();
    let path = dir.path().join("app.hna");
    with_native_session(&spec.model, |session| {
        let mut app = WaveApplication::found(&spec, session)?;
        app.cycle = usize::MAX;
        assert!(app.validate().is_err());
        app.cycle = 0;
        app.checkpoint(session, &path)?;
        session.receive(&CurrentWire::integers(1, 0), None)?;
        assert!(app.advance_boundary(session).is_err());
        Ok(())
    })
    .unwrap();
    assert!(NativeSavedSession::read(&path)
        .unwrap()
        .with_session::<()>(|_, _| panic!("application owner discarded"))
        .is_err());
    let saved = NativeSavedSession::read(&path).unwrap();
    let mut app: serde_json::Value =
        serde_json::from_slice(saved.application_state().unwrap()).unwrap();
    app["step"]["source"] = 999.into();
    let wrong = dir.path().join("wrong.hna");
    saved
        .with_application_session(|session, stream, _| {
            session.checkpoint_application(&wrong, stream.state(), &serde_json::to_vec(&app)?)?;
            Ok(())
        })
        .unwrap();
    assert!(WaveSavedApplication::read(&wrong).is_err());
}
