//! **These `#[ignore]`d tests mount a CUDA context; run them serially.**
//! `ResidentSurface::on` calibrates the allocator grain from `cuMemGetInfo_v2`, which reports the
//! **whole device's** free extent. Another allocation on the card between its samples — a second
//! test thread, a second cargo test process, any other GPU program — enters the difference and the
//! calibration refuses with `one-word charge … and restored free extent … do not close`. That is
//! apparatus, not the law under test. Run `-- --include-ignored --test-threads=1` with the card
//! otherwise idle; see `docs/DEVELOPMENT.md`'s verification cadence.

use super::*;
mod boundary;
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ResidentConstitutiveCurrent, ResidentConstitutiveFibre,
        ResidentGeneratorNeighborhood, ResidentNormalMaterial,
    },
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest},
};
fn point<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            v.len(),
            ResidentGrain(0),
            64,
            v.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn current<'a, 'c>(v: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(v).unwrap()
}
// An exterior exact operator specimen for session mechanics, not a conversation learner.
fn session<'c>(s: &'c ResidentSurface<'c>) -> NativeCoupledWaveSession<'c> {
    session_law(s, false)
}

// Measured complex source/condition specimens for the generic numerical HNN owner.
// All compatibility formation and normal fitting use public native owners.
fn numerical_predictive_body<'c>(s: &'c ResidentSurface<'c>) -> NativeCoupledBody<'c> {
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(s,3,1,1).unwrap();
    let mut normal = ResidentNormalMaterial::found_features(s,7,1,ResidentGrain(8)).unwrap();
    let mut inputs = vec![[0;6]];
    for coordinate in 0..6 {let mut source=[0;6];source[coordinate]=1;inputs.push(source);}
    for a in inputs {
        for h in [[0,0],[1,0],[0,1]] {
            let measured=[a[0]*h[0]-a[1]*h[1],a[0]*h[1]+a[1]*h[0]];
            let a=point(s,&a);let h=point(s,&h);let y=point(s,&measured);
            law.advance_bilinear_contact(current(&a),current(&h),Some(current(&y))).unwrap();
            normal=normal.stage_bilinear_observation(current(&a),current(&h),current(&y)).unwrap();
        }
    }
    let h=point(s,&[1,0]);
    let mut neighborhood=ResidentGeneratorNeighborhood::with_shared_condition(vec![law],current(&h),
        ConditionContactMetric::UnitAdmittanceRealification).unwrap();
    neighborhood.attach_normal_prediction(0,normal).unwrap_or_else(|(_,e)|panic!("{e:?}"));
    let p=point(s,&[1,0]);let c=point(s,&[2,1]);
    let wave=ResidentNormalMaterial::found(s,1,1,ResidentGrain(8)).unwrap()
        .into_applied_difference_wave(current(&p),current(&c)).unwrap()
        .with_neighborhood(neighborhood).unwrap();
    NativeCoupledBody::from_wave(wave)
}

#[test]
#[ignore = "requires CUDA; actual numerical coupled consumer keeps fitted material and producing conditions through out-of-order returns"]
fn fitted_material_reaches_the_numerical_hnn_and_delayed_return() {
    type Q=num_rational::BigRational;
    let q=|n:i64|Q::from_integer(n.into());
    let read_q=|v:&Value|serde_json::from_value::<Q>(v.clone()).unwrap();
    let read_current=|v:&Value,state:usize| {
        v["states"][state]["projection"]["current"].as_array().unwrap().iter()
            .map(|v|Q::new(v["numerator"].as_str().unwrap().parse().unwrap(),v["denominator"].as_str().unwrap().parse().unwrap()))
            .collect::<Vec<_>>()
    };
    let ro=ResidentReadout::new().unwrap();let s=ResidentSurface::on(&ro).unwrap();
    let mut body=numerical_predictive_body(&s);
    let initial=body.inspect_predictive_material(0).unwrap();
    let initial_hh=read_q(&initial["predictive_material"]["state"]["source_normal"][3][3]["real"]);
    let first=body.advance(0,WaveSourceReceiver::Direct,true).unwrap().unwrap();
    let second=body.advance(0,WaveSourceReceiver::Direct,true).unwrap().unwrap();
    let returned=point(&s,&[7,4]);
    body.incorporate(second,current(&returned)).unwrap();
    let old_return=point(&s,&[5,-2]);
    body.incorporate(first,current(&old_return)).unwrap();
    assert!(body.incorporate(first,current(&old_return)).is_err());
    let material=body.inspect_predictive_material(0).unwrap();
    assert_eq!(material["predictive_material"]["observations"],23);
    // Both pending predictions were made under h=1. The current condition changed after the
    // second return, but must not be substituted into the older first return's normal moments.
    let hh=read_q(&material["predictive_material"]["state"]["source_normal"][3][3]["real"]);
    assert_eq!(hh,initial_hh+q(2));

    // The final observed return has original (p,c)=(1,2+i), eta=3-3i. The compatibility
    // condition therefore becomes h=(3-3i)/(1+i)=-3i. It is formed inside the HNN body.
    // Independently contract the returned stored M with every step's full (a,h,h*a).
    let coefficients=material["predictive_material"]["state"]["material"]["coefficients"][0]
        .as_array().unwrap().iter().map(|z|[read_q(&z["real"]),read_q(&z["imaginary"])])
        .collect::<Vec<_>>();
    let word=[(0,WaveSourceReceiver::Direct);2];
    let epoch=body.epoch();
    let forecast=body.inspect_prospective(&word,true).unwrap();
    assert_eq!(body.epoch(),epoch);
    assert_eq!(forecast["receiver_representation"],"generated-point-word");
    for state in 0..2 {
        let previous=forecast["states"][state]["projection"]["previous"].as_array().unwrap().iter()
            .map(|v|Q::new(v["numerator"].as_str().unwrap().parse().unwrap(),v["denominator"].as_str().unwrap().parse().unwrap())).collect::<Vec<_>>();
        let c=read_current(&forecast,state);
        let a=[[&c[0]-&previous[0],&c[1]-&previous[1]],[c[0].clone(),c[1].clone()],[previous[0].clone(),previous[1].clone()]];
        let mut u=a.to_vec();u.push([q(0),q(-3)]);
        for x in &a {u.push([q(3)*&x[1],q(-3)*&x[0]]);}
        let mut expected=c;
        for (m,x) in coefficients.iter().zip(u) {
            expected[0]+=&m[0]*&x[0]-&m[1]*&x[1];
            expected[1]+=&m[0]*&x[1]+&m[1]*&x[0];
        }
        assert_eq!(read_current(&forecast,state+1),expected);
    }
    // Existing complete body persistence carries the new local material through its owner.
    let rest=body.rest().unwrap();let mut bytes=Vec::new();rest.write(&mut bytes).unwrap();
    let mut restored=SavedCoupledBody::read(&mut bytes.as_slice(),bytes.len() as u64).unwrap().remount(&s).unwrap();
    assert_eq!(restored.inspect_predictive_material(0).unwrap(),material);
    assert_eq!(restored.inspect_prospective(&word,true).unwrap(),forecast);
}
fn session_law<'c>(s: &'c ResidentSurface<'c>, conditional: bool) -> NativeCoupledWaveSession<'c> {
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(s, 6, 1, 2).unwrap();
    let mut sources = vec![vec![0; 12]];
    for i in 0..12 {
        let mut a = vec![0; 12];
        a[i] = 1;
        sources.push(a);
    }
    for a in sources {
        for h in [[0, 0], [1, 0], [0, 1]] {
            let d = [a[6] - a[4], a[7] - a[5]];
            let d = if conditional {
                [d[0] * h[0] - d[1] * h[1], d[0] * h[1] + d[1] * h[0]]
            } else {
                d
            };
            let eta = [d[0], d[1], -d[0], -d[1]];
            let a = point(s, &a);
            let h = point(s, &h);
            let y = point(s, &eta);
            law.advance_bilinear_contact(current(&a), current(&h), Some(current(&y)))
                .unwrap();
        }
    }
    let p = point(s, &[1, 0, 0, 0]);
    let c = point(s, &[0, 0, 1, 0]);
    let h = point(s, &[1, 0]);
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let wave = ResidentNormalMaterial::found(s, 2, 2, ResidentGrain(32))
        .unwrap()
        .into_applied_difference_wave(current(&p), current(&c))
        .unwrap()
        .with_neighborhood(neighborhood)
        .unwrap();
    NativeCoupledWaveSession::from_wave(
        s,
        wave,
        SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'b']).unwrap()),
        0,
        WaveSourceReceiver::Direct,
    )
    .unwrap()
}

#[test]
#[ignore = "requires CUDA; one prospective word uses the actual learned affine/dependent body and leaves it unpublished"]
fn prospective_word_uses_returned_generator_with_one_shared_source() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut developed = session_law(&s, true);
    let mut control = session_law(&s, true);
    let read = |value: &Value, state: usize| -> Vec<num_rational::BigRational> {
        let wire: Vec<super::super::RationalWire> =
            serde_json::from_value(value["states"][state]["projection"]["current"].clone())
                .unwrap();
        wire.iter().map(|x| x.rational().unwrap()).collect()
    };
    let expected = |values: &[i64]| {
        values
            .iter()
            .map(|v| num_rational::BigRational::from_integer((*v).into()))
            .collect::<Vec<_>>()
    };
    let saved = developed.wave.rest().unwrap();
    let cursor = developed.inspect();
    let mut stream = HnaStream::new();
    let request=json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"predict-continuation","word":[0,0,0],"full_family":true}}).to_string()+"\n";
    let mut output = Vec::new();
    stream
        .pump_coupled_wave(
            &mut developed,
            &mut std::io::Cursor::new(request),
            &mut output,
        )
        .unwrap();
    let event: Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(event["event"], "prospective", "{event}");
    let forecast = &event["value"];
    assert_eq!(forecast["action_committed"], false);
    assert_eq!(forecast["source_scope"], "projected-family-joint");
    assert_eq!(forecast["reading"]["state_count"], 4);
    assert_eq!(forecast["text"], "aba", "{forecast}");
    for (index, values) in [[0, 0, 1, 0], [1, 0, 0, 0], [0, 0, 1, 0], [1, 0, 0, 0]]
        .iter()
        .enumerate()
    {
        assert_eq!(read(forecast, index), expected(values));
    }
    assert_eq!(developed.wave.rest().unwrap(), saved);
    assert_eq!(developed.inspect(), cursor);
    assert!(developed.predict_continuation(&[], false).is_err());
    assert!(developed
        .predict_continuation(&[usize::MAX], false)
        .is_err());
    assert_eq!(developed.wave.rest().unwrap(), saved);

    let predicted = developed.predict_symbol(false).unwrap();
    control.predict_symbol(false).unwrap();
    developed
        .incorporate_symbol(predicted["action"]["prediction"].as_u64().unwrap(), "b")
        .unwrap();
    // Match the prepared (p,c) of both bodies. Only the actual returned condition/material
    // differs; the dependent body must not fall back to its frozen normal/affine substrate.
    control.receive_next_symbol("a").unwrap();
    developed.receive_next_symbol("b").unwrap();
    control.receive_next_symbol("b").unwrap();
    let saved = developed.wave.rest().unwrap();
    let forecast = developed.predict_continuation(&[0, 0, 0], true).unwrap();
    let old = control.predict_continuation(&[0, 0, 0], false).unwrap();
    assert_eq!(forecast["source_scope"], "declared-source-section");
    assert_eq!(forecast["text"], "bbb", "{forecast}");
    assert_eq!(old["text"], "aba", "{old}");
    assert_eq!(forecast["action_committed"], false);
    assert_eq!(read(&forecast, 0), read(&old, 0));
    assert_eq!(
        forecast["states"][0]["projection"]["previous"],
        old["states"][0]["projection"]["previous"]
    );
    for index in 1..=3 {
        assert_eq!(read(&forecast, index), expected(&[0, 0, 1, 0]));
    }
    assert_eq!(read(&old, 1), expected(&[1, 0, 0, 0]));
    assert_eq!(read(&old, 2), expected(&[0, 0, 1, 0]));
    assert_eq!(read(&old, 3), expected(&[1, 0, 0, 0]));
    assert_eq!(developed.wave.rest().unwrap(), saved);
    println!(
        "{}",
        json!({"scope":"shared-source prospective word control",
        "initial_preview":event["value"]["text"],"matched_control_preview":old["text"],
        "after_native_return":forecast["text"],"source_scope":forecast["source_scope"],
        "joint_states":forecast["states"],"action_committed":forecast["action_committed"]})
    );
}

#[test]
#[ignore = "requires CUDA; streamed return publishes the full generator and following text uses its changed condition"]
fn coupled_session_incorporates_observed_symbol_and_continues() {
    const CHILD: &str = "HOLONICS_HNN_CONSTITUTIVE_SESSION_RESUME";
    if let Some(directory) = std::env::var_os(CHILD) {
        let directory = std::path::PathBuf::from(directory);
        NativeCoupledWaveSavedSession::read(directory.join("before.session"))
            .unwrap()
            .with_session(|loaded, stream| {
                assert_eq!(loaded.wave.scope(), "declared-source-section");
                let id = loaded.wave.pending_ids()?.into_iter().next().unwrap();
                assert_eq!(
                    loaded.compare_symbol(id, "b", Some(0))?["scope"],
                    "dependent-producing-family-section"
                );
                let value = loaded.next_symbol(false)?;
                std::fs::write(directory.join("result.json"), serde_json::to_vec(&value)?)?;
                loaded.checkpoint_stream(directory.join("after.session"), stream.state())?;
                Ok(())
            })
            .unwrap();
        return;
    }
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session_law(&s, true);
    let mut control = session_law(&s, true);
    let predicted = session.predict_symbol(false).unwrap();
    assert_eq!(control.predict_symbol(false).unwrap()["text"], "a");
    assert_eq!(predicted["text"], "a");
    let id = predicted["action"]["prediction"].as_u64().unwrap();
    let before = session.wave.rest().unwrap();
    assert!(session.incorporate_symbol(id + 100, "b").is_err());
    assert_eq!(session.wave.rest().unwrap(), before);
    let mut stream = HnaStream::new();
    let command=json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"observe-symbol","source":id,"text":"b"}}).to_string()+"\n";
    let reads = s.census().section_read_outs;
    let mut output = Vec::new();
    stream
        .pump_coupled_wave(
            &mut session,
            &mut std::io::Cursor::new(command),
            &mut output,
        )
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let event: Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(event["value"]["return_published"], true, "{event}");
    assert_eq!(session.wave.pending_coupled_predictions(), 0);
    assert_eq!(session.wave.scope(), "declared-source-section");
    let published = session.wave.rest().unwrap();
    assert!(session.incorporate_symbol(id, "b").is_err());
    assert_eq!(session.wave.rest().unwrap(), published);
    // Match the complete (p,c) source before the compared prediction: both first reach
    // (a,a), then the actual observation b gives (a,b). Only the return changed h.
    control.receive_next_symbol("a").unwrap();
    session.receive_next_symbol("b").unwrap();
    control.receive_next_symbol("b").unwrap();
    let new = session.next_symbol(true).unwrap();
    let old = control.next_symbol(true).unwrap();
    assert_eq!(new["text"], "b");
    assert_eq!(old["text"], "a");
    // Generation and re-entry remain ordinary operations of the returned body.
    let another = session.predict_symbol(false).unwrap();
    let new_id = another["action"]["prediction"].as_u64().unwrap();
    assert_eq!(another["text"], "b");
    assert!(!another["reentry"].is_null());
    assert_eq!(session.wave.pending_coupled_predictions(), 1);
    let comparison = session.compare_symbol(new_id, "b", Some(0)).unwrap();
    assert_eq!(comparison["scope"], "dependent-producing-family-section");
    // A second actual return reacts through the material formed by the first. The original
    // h=1 control and the twice-returned session now agree under matched complete sources.
    let command=json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"observe-symbol","source":new_id,"text":"a"}}).to_string()+"\n";
    let reads = s.census().section_read_outs;
    let mut output = Vec::new();
    stream
        .pump_coupled_wave(
            &mut session,
            &mut std::io::Cursor::new(command),
            &mut output,
        )
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let event: Value = serde_json::from_slice(&output).unwrap();
    assert_eq!(event["value"]["return_published"], true, "{event}");
    assert_eq!(event["value"]["material_returns"], 2);
    assert_eq!(session.wave.pending_coupled_predictions(), 0);
    let after_second = session.wave.rest().unwrap();
    assert!(session.incorporate_symbol(new_id, "a").is_err());
    assert_eq!(session.wave.rest().unwrap(), after_second);
    for text in ["a", "b"] {
        session.receive_next_symbol(text).unwrap();
        control.receive_next_symbol(text).unwrap();
    }
    assert_eq!(session.next_symbol(true).unwrap()["text"], "a");
    assert_eq!(control.next_symbol(true).unwrap()["text"], "a");
    let third = session.predict_symbol(false).unwrap();
    let new_id = third["action"]["prediction"].as_u64().unwrap();
    assert_eq!(session.wave.pending_coupled_predictions(), 1);
    let directory = path("constitutive-return");
    std::fs::create_dir(&directory).unwrap();
    let saved = directory.join("before.session");
    session.checkpoint_stream(&saved, stream.state()).unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact","native::coupled_wave::tests::coupled_session_incorporates_observed_symbol_and_continues","--ignored","--test-threads=1"])
        .env(CHILD,&directory).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    let expected = session.next_symbol(false).unwrap();
    let rest = session.wave.rest().unwrap();
    let child_result: Value =
        serde_json::from_slice(&std::fs::read(directory.join("result.json")).unwrap()).unwrap();
    assert_eq!(child_result, expected);
    assert_eq!(
        NativeCoupledWaveSavedSession::read(directory.join("after.session"))
            .unwrap()
            .rest,
        rest
    );
    NativeCoupledWaveSavedSession::read(&saved)
        .unwrap()
        .with_session(|loaded, _| {
            assert_eq!(loaded.wave.scope(), "declared-source-section");
            assert_eq!(
                loaded.compare_symbol(new_id, "b", Some(0))?["source_epoch"],
                new_id - 1
            );
            assert_eq!(loaded.next_symbol(false)?, expected);
            assert_eq!(loaded.wave.rest()?, rest);
            loaded.release_symbol_comparison(new_id)?;
            assert!(loaded.compare_symbol(new_id, "b", None).is_err());
            Ok(())
        })
        .unwrap();
    eprintln!(
        "HNN old={} returned={} receiver={}",
        old["text"],
        new["text"],
        session.wave.scope()
    );
}
fn path(label: &str) -> std::path::PathBuf {
    std::env::temp_dir().join(format!(
        "holonics-coupled-{label}-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ))
}
#[test]
#[ignore = "requires CUDA; conditional generation emits and actual symbol pairs re-enter the same owner"]
fn coupled_session_generates_and_reenters_without_self_deposition() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session(&s);
    assert!(session.inspect_relation().is_err());
    session
        .wave
        .admit_test_contact(session.member, session.receiver)
        .unwrap();
    let before = session.wave.rest().unwrap();
    assert_eq!(
        session.inspect_relation().unwrap()["reading"]["support"],
        "Supported"
    );
    assert_eq!(session.wave.rest().unwrap(), before);
    let projection = session.project_current(true).unwrap();
    assert_eq!(projection["text"], "b");
    assert_eq!(session.wave.rest().unwrap(), before);
    let first = session.next_symbol(true).unwrap();
    assert_eq!(first["text"], "a");
    assert!(first["reentry"].is_null());
    assert_eq!(session.wave.epoch(), 1);
    let second = session.next_symbol(true).unwrap();
    assert_eq!(second["text"], "b");
    assert_eq!(session.wave.epoch(), 3);
    assert_eq!(
        session
            .wave
            .affine_wave()
            .unwrap()
            .neighborhood()
            .generator(0)
            .unwrap()
            .occurrences(),
        39
    );
    assert_eq!(session.wave.normal_observations(), Some(0));
    assert_eq!(session.inspect()["emission_ordinal"], 2);
    let saved = path("live");
    session
        .checkpoint_stream(&saved, &HnaStreamState::default())
        .unwrap();
    let checked = NativeCoupledWaveSavedSession::read(&saved).unwrap();
    let mut stale = checked.header.clone();
    stale.last.as_mut().unwrap().generation = 0;
    assert!(NativeCoupledWaveSavedSession::validate(&stale, &checked.rest).is_err());
    stale.last.as_mut().unwrap().generation = 1;
    assert!(NativeCoupledWaveSavedSession::validate(&stale, &checked.rest).is_err());
    let next = session.next_symbol(false).unwrap();
    let rest = session.wave.rest().unwrap();
    NativeCoupledWaveSavedSession::read(&saved)
        .unwrap()
        .with_session(|loaded, _| {
            assert_eq!(loaded.next_symbol(false)?, next);
            assert_eq!(loaded.wave.rest()?, rest);
            Ok(())
        })
        .unwrap();
}
#[test]
#[ignore = "requires CUDA; pending selection and re-entry resume without regenerating their source"]
fn coupled_session_pending_phases_retain_the_producing_cut() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session(&s);
    session.chart =
        SymbolCurrentChart::recharted(SymbolAlphabet::from_chars(&['a', 'b']).unwrap(), vec![1, 0])
            .unwrap();
    assert!(session.predict_symbol(false).is_err());
    assert_eq!(session.wave.pending_coupled_predictions(), 1);
    assert!(session.release_symbol_comparison(1).is_err());
    assert_eq!(session.wave.epoch(), 1);
    assert!(matches!(
        session.cursor,
        Cursor::AwaitSelection { generation: 1, .. }
    ));
    session.chart = SymbolCurrentChart::declared(SymbolAlphabet::from_chars(&['a', 'b']).unwrap());
    let pending = path("selection");
    session
        .checkpoint_stream(&pending, &HnaStreamState::default())
        .unwrap();
    NativeCoupledWaveSavedSession::read(&pending)
        .unwrap()
        .with_session(|loaded, _| {
            assert_eq!(loaded.next_symbol(false)?["text"], "a");
            assert_eq!(loaded.wave.epoch(), 1);
            Ok(())
        })
        .unwrap();
    assert_eq!(session.next_symbol(false).unwrap()["text"], "a");
    session
        .wave
        .advance(session.member, session.receiver, false)
        .unwrap();
    let emission = session
        .chart
        .emit_family(session.wave.read_basis_face(&session.basis).unwrap())
        .unwrap();
    session.cursor = Cursor::AwaitReentry {
        generation: session.wave.epoch(),
        action: Action {
            ordinal: 2,
            generation: session.wave.epoch(),
            symbol: emission.symbol(),
            prediction: None,
        },
    };
    let pending = path("reentry");
    session
        .checkpoint_stream(&pending, &HnaStreamState::default())
        .unwrap();
    let expected = session.next_symbol(false).unwrap();
    let rest = session.wave.rest().unwrap();
    NativeCoupledWaveSavedSession::read(&pending)
        .unwrap()
        .with_session(|loaded, _| {
            assert_eq!(loaded.next_symbol(false)?, expected);
            assert_eq!(loaded.wave.rest()?, rest);
            Ok(())
        })
        .unwrap();
}
#[test]
#[ignore = "requires CUDA; partial output delivery survives process exit without repeating native generation"]
fn coupled_session_process_resume_drains_the_pending_emission_once() {
    const CHILD: &str = "HOLONICS_COUPLED_EMISSION_CHILD";
    if let Some(directory) = std::env::var_os(CHILD) {
        let directory = std::path::PathBuf::from(directory);
        NativeCoupledWaveSavedSession::read(directory.join("saved.session"))
            .unwrap()
            .with_session(|session, stream| {
                stream.open_new_connection();
                let mut input = std::io::Cursor::new(Vec::<u8>::new());
                let mut output = Vec::new();
                stream
                    .pump_coupled_wave(session, &mut input, &mut output)
                    .map_err(invalid)?;
                std::fs::write(directory.join("delivered.jsonl"), output)?;
                session.checkpoint_stream(directory.join("resumed.session"), stream.state())?;
                Ok(())
            })
            .unwrap();
        return;
    }
    struct Broken;
    impl Write for Broken {
        fn write(&mut self, _: &[u8]) -> io::Result<usize> {
            Err(io::Error::new(io::ErrorKind::BrokenPipe, "test writer"))
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session(&s);
    let mut stream = HnaStream::new();
    let request=b"{\"schema\":\"org.holonics.hna.stream-request.v1\",\"command\":{\"action\":\"emit-symbol\"}}\n";
    assert!(stream
        .pump_coupled_wave(
            &mut session,
            &mut std::io::Cursor::new(request),
            &mut Broken
        )
        .is_err());
    assert_eq!(session.wave.epoch(), 1);
    let native = session.wave.rest().unwrap();
    let frame = stream.state().output.clone().unwrap();
    let directory = path("process");
    std::fs::create_dir(&directory).unwrap();
    session
        .checkpoint_stream(directory.join("saved.session"), stream.state())
        .unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact","native::coupled_wave::tests::coupled_session_process_resume_drains_the_pending_emission_once","--ignored","--test-threads=1"]).env(CHILD,&directory).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    assert_eq!(
        std::fs::read(directory.join("delivered.jsonl")).unwrap(),
        frame
    );
    NativeCoupledWaveSavedSession::read(directory.join("resumed.session"))
        .unwrap()
        .with_session(|loaded, stream| {
            assert_eq!(loaded.wave.rest()?, native);
            assert_eq!(loaded.emission_ordinal, 1);
            assert!(stream.state().output.is_none());
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; actual observations enter the same coupled owner and persist through the public stream"]
fn coupled_session_observed_next_is_distinct_from_unpaired_source_and_correction() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session(&s);
    let mut stream = HnaStream::default();
    let mut output = Vec::new();
    let requests = [
        json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"receive-next-symbol","text":"a"}}),
        json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"receive-next-symbol","text":"b"}}),
        json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"emit-symbol"}}),
    ];
    let input = requests
        .iter()
        .map(|v| format!("{v}\n"))
        .collect::<String>();
    stream
        .pump_coupled_wave(&mut session, &mut std::io::Cursor::new(input), &mut output)
        .unwrap();
    let values = String::from_utf8(output)
        .unwrap()
        .lines()
        .map(|v| serde_json::from_str::<Value>(v).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(values[0]["event"], "next-symbol-received");
    assert_eq!(values[1]["event"], "next-symbol-received");
    assert_eq!(values[2]["value"]["text"], "a");
    assert_eq!(session.wave.epoch(), 3);
    assert_eq!(
        session
            .wave
            .affine_wave()
            .unwrap()
            .neighborhood()
            .generator(0)
            .unwrap()
            .occurrences(),
        39
    );
    let checkpoint = path("observation");
    session
        .checkpoint_stream(&checkpoint, stream.state())
        .unwrap();
    let expected = session.next_symbol(false).unwrap();
    let rest = session.wave.rest().unwrap();
    NativeCoupledWaveSavedSession::read(checkpoint)
        .unwrap()
        .with_session(|loaded, _| {
            assert_eq!(loaded.next_symbol(false)?, expected);
            assert_eq!(loaded.wave.rest()?, rest);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; producing comparisons stay pending through later emissions and complete rest"]
fn coupled_session_keeps_and_compares_its_producing_family() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session(&s);
    let first = session.predict_symbol(false).unwrap();
    let id = first["action"]["prediction"].as_u64().unwrap();
    assert_eq!(session.wave.pending_coupled_predictions(), 1);
    session.next_symbol(false).unwrap();
    let before = session.wave.rest().unwrap();
    let comparison = session.compare_symbol(id, "b", Some(0)).unwrap();
    assert_eq!(comparison["material_deposited"], false);
    assert_eq!(comparison["source_epoch"], 0);
    assert_eq!(comparison["contemporary_epoch"], 3);
    assert_eq!(session.wave.rest().unwrap(), before);
    let saved = path("producing-family");
    session
        .checkpoint_stream(&saved, &HnaStreamState::default())
        .unwrap();
    NativeCoupledWaveSavedSession::read(saved).unwrap().with_session(|loaded,stream|{
        assert_eq!(loaded.compare_symbol(id,"b",Some(0))?,comparison);
        let input=json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"compare-symbol","source":id,"text":"b","coefficient_row":0}}).to_string()+"\n";
        let mut out=Vec::new();stream.pump_coupled_wave(loaded,&mut std::io::Cursor::new(input),&mut out).unwrap();
        let event:Value=serde_json::from_slice(&out).unwrap();assert_eq!(event["event"],"symbol-comparison");assert_eq!(event["value"],comparison);
        loaded.release_symbol_comparison(id)?;assert!(loaded.compare_symbol(id,"b",None).is_err());
        assert_eq!(loaded.wave().pending_coupled_predictions(),0);Ok(())
    }).unwrap();
}

#[test]
#[ignore = "requires CUDA; v3 sessions keep the legacy affine checkpoint reader"]
fn coupled_session_reads_legacy_affine_frames() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session(&s);
    session.predict_symbol(false).unwrap();
    let native = session.wave.rest().unwrap();
    let current = session.project_current(true).unwrap();
    let fresh = path("v3-source");
    session
        .checkpoint_stream(&fresh, &HnaStreamState::default())
        .unwrap();
    let saved = NativeCoupledWaveSavedSession::read(&fresh).unwrap();
    let header = serde_json::to_vec(&saved.header).unwrap();
    for magic in [MAGIC, MAGIC_V2] {
        let legacy = path("legacy-reader");
        let mut file = File::create(&legacy).unwrap();
        file.write_all(magic).unwrap();
        file.write_all(&(header.len() as u64).to_le_bytes())
            .unwrap();
        file.write_all(&header).unwrap();
        let SavedCoupledBody::Affine(rest) = &native else {
            panic!("expected affine fixture")
        };
        rest.write(&mut file).unwrap();
        drop(file);
        NativeCoupledWaveSavedSession::read(&legacy)
            .unwrap()
            .with_session(|loaded, _| {
                assert_eq!(loaded.wave.rest()?, native);
                assert_eq!(loaded.project_current(true)?, current);
                Ok(())
            })
            .unwrap();
    }
}

#[test]
#[ignore = "requires CUDA; a base prediction returns through the stream after publication and process exit"]
fn coupled_session_returns_original_base_prediction_after_restart() {
    const CHILD: &str = "HOLONICS_HNN_BASE_RETURN_RESUME";
    fn receive_base(
        session: &mut NativeCoupledWaveSession<'_>,
        stream: &mut HnaStream,
        id: u64,
    ) -> Value {
        let command=json!({"schema":crate::HNA_STREAM_REQUEST_SCHEMA,"command":{"action":"observe-symbol","source":id,"text":"b"}}).to_string()+"\n";
        let reads = session.surface.census().section_read_outs;
        let mut output = Vec::new();
        stream
            .pump_coupled_wave(session, &mut std::io::Cursor::new(command), &mut output)
            .unwrap();
        assert_eq!(session.surface.census().section_read_outs, reads);
        let event: Value = serde_json::from_slice(&output).unwrap();
        assert_eq!(event["value"]["return_published"], true, "{event}");
        assert_eq!(session.wave.pending_coupled_predictions(), 0);
        assert!(session.incorporate_symbol(id, "b").is_err());
        for text in ["a", "b"] {
            session.receive_next_symbol(text).unwrap();
        }
        let emitted = session.next_symbol(true).unwrap();
        assert_eq!(emitted["text"], "a");
        json!({"received":event,"emitted":emitted})
    }
    if let Some(directory) = std::env::var_os(CHILD) {
        let directory = std::path::PathBuf::from(directory);
        NativeCoupledWaveSavedSession::read(directory.join("before.session"))
            .unwrap()
            .with_session(|loaded, stream| {
                let id = loaded.wave.pending_ids()?.into_iter().next().unwrap();
                assert_eq!(
                    loaded.compare_symbol(id, "b", Some(0))?["scope"],
                    "dependent-producing-family-section"
                );
                let result = receive_base(loaded, stream, id);
                std::fs::write(directory.join("result.json"), serde_json::to_vec(&result)?)?;
                loaded.checkpoint_stream(directory.join("after.session"), stream.state())?;
                Ok(())
            })
            .unwrap();
        return;
    }
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut session = session_law(&s, true);
    let first = session.predict_symbol(false).unwrap();
    let second = session.predict_symbol(false).unwrap();
    assert_eq!(first["text"], "a");
    assert_eq!(second["text"], "b");
    let root = first["action"]["prediction"].as_u64().unwrap();
    let remaining = second["action"]["prediction"].as_u64().unwrap();
    session.incorporate_symbol(root, "b").unwrap();
    for text in ["a", "b"] {
        session.receive_next_symbol(text).unwrap();
    }
    let before = session.next_symbol(true).unwrap();
    assert_eq!(before["text"], "b");
    let directory = path("base-return");
    std::fs::create_dir(&directory).unwrap();
    let mut stream = HnaStream::new();
    session
        .checkpoint_stream(directory.join("before.session"), stream.state())
        .unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact","native::coupled_wave::tests::coupled_session_returns_original_base_prediction_after_restart","--ignored","--test-threads=1"])
        .env(CHILD,&directory).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    let result = receive_base(&mut session, &mut stream, remaining);
    assert_eq!(
        serde_json::from_slice::<Value>(&std::fs::read(directory.join("result.json")).unwrap())
            .unwrap(),
        result
    );
    assert_eq!(
        NativeCoupledWaveSavedSession::read(directory.join("after.session"))
            .unwrap()
            .rest,
        session.wave.rest().unwrap()
    );
    eprintln!(
        "old base prediction returned after first publication: before={} after={}",
        before["text"], result["emitted"]["text"]
    );
}
