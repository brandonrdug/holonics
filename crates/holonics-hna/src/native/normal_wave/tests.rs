use super::*;
use holonic_engine::{
    native_ecology::constitutive_fibre::ResidentNormalMaterial,
    resident_section::{ResidentGrain, ResidentSectionRest},
};
use std::io::Cursor as Input;

fn session<'c>(s: &'c ResidentSurface<'c>) -> NativeWaveSession<'c> {
    let n = 2;
    let values = vec![0, 0, 0, 0, 1, 0, 2, 0];
    let points = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                2,
                2 * n,
                ResidentGrain(0),
                64,
                values.into_iter().map(|v| (v, v)).collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let input = ResidentConstitutiveSection::integers(&points).unwrap();
    let m = ResidentNormalMaterial::found(s, n, n, ResidentGrain(64)).unwrap();
    let wave = m
        .into_applied_difference_wave(input.row(0).unwrap(), input.row(1).unwrap())
        .unwrap();
    let alphabet = SymbolAlphabet::from_chars(&['a', 'β']).unwrap();
    NativeWaveSession::from_wave(s, wave, SymbolCurrentChart::declared(alphabet)).unwrap()
}
fn emit_request(retain: bool) -> Vec<u8> {
    format!("{{\"schema\":\"{}\",\"command\":{{\"action\":\"emit-symbol\",\"retain_comparison\":{retain}}}}}\n",crate::HNA_STREAM_REQUEST_SCHEMA).into_bytes()
}

#[test]
fn source_seed_checks_actual_symbols_and_schema_before_mounting() {
    let spec = NativeWaveSeedSpec {
        schema: NATIVE_WAVE_SEED_SCHEMA.into(),
        symbols: vec!['a', 'b'],
        seed: "az".into(),
        grain: 64,
    };
    assert!(with_seeded_wave_session(&spec, |_| Ok(())).is_err());
    let mut spec = spec;
    spec.seed = "a".into();
    assert!(with_seeded_wave_session(&spec, |_| Ok(())).is_err());
}

#[test]
#[ignore = "requires CUDA; categorical receiver uses c+delta at producing cut and preserves native covectors"]
fn normalized_next_current_uses_pre_update_prediction_and_actual_symbol_mass() {
    use num_rational::BigRational as Rat;
    let q = |n: i64, d: i64| Rat::new(n.into(), d.into());
    let spec = NativeWaveSeedSpec {
        schema: NATIVE_WAVE_SEED_SCHEMA.into(),
        symbols: vec!['a', 'b'],
        seed: "ab".into(),
        grain: 64,
    };
    with_seeded_wave_session(&spec, |session| {
        let input=session.chart.mount(session.surface,&session.chart.decode_text("a")?)?;
        let reads=session.surface.census().section_read_outs;
        let received=session.wave.receive(ResidentConstitutiveSection::integers(&input)?.row(0)?)?;
        let normalized=received.normalized_return(2,SeriesAperture(20))?;
        assert_eq!(session.surface.census().section_read_outs,reads,"all comparison operands remain resident");
        let reading=normalized.inspect()?;
        // Initial delta=0 but c=e_b: uniform probabilities would omit the current anchor.
        assert!(reading.prediction[0].lower>q(1,4));
        assert!(reading.prediction[0].upper<q(1,3));
        assert!(reading.prediction[1].lower>q(2,3));
        assert!(reading.prediction[1].upper<q(3,4));
        for p in &reading.prediction { assert!(&p.upper-&p.lower<q(1,1024)); }
        assert_eq!(reading.observation[0].lower,q(1,1));
        assert_eq!(reading.observation[0].upper,q(1,1));
        assert_eq!(reading.observation[1].lower,q(0,1));
        assert_eq!(reading.observation[1].upper,q(0,1));
        assert!(reading.returned_difference[0].lower>q(0,1));
        assert!(reading.returned_difference[1].upper<q(0,1));
        assert!(reading.potential_pullback[0].lower>q(0,1));
        assert!(reading.potential_pullback[1].upper<q(0,1));
        assert_eq!(reading.source,0);
        assert_eq!(reading.receiving,1);
        assert!(std::ptr::eq(*normalized.origin(),&received));
        let before=session.wave.fibre().material_observations;
        assert!(session.receive_next_symbol_distribution("b",0).is_err());
        assert_eq!(session.wave.fibre().material_observations,before);
        let mut stream=HnaStream::new();
        let request=format!("{{\"schema\":\"{}\",\"command\":{{\"action\":\"receive-next-symbol-distribution\",\"text\":\"b\",\"series_terms\":20}}}}\n",crate::HNA_STREAM_REQUEST_SCHEMA);
        let mut response=Vec::new();
        stream.pump_wave(session,&mut Input::new(request),&mut response).map_err(invalid)?;
        let response:Value=serde_json::from_slice(&response)?;
        assert_eq!(response["event"],"next-symbol-received","{response}");
        assert_eq!(response["value"]["observation_committed"],true);
        assert_eq!(response["value"]["distribution"]["status"],"returned","{response}");
        assert_eq!(response["value"]["distribution"]["reading"]["source"],1);
        assert_eq!(response["value"]["distribution"]["reading"]["receiving"],2);
        assert_eq!(session.wave.fibre().material_observations,before+1);
        assert_eq!(normalized.inspect()?.prediction,reading.prediction,
            "the earlier source-qualified receiver survives another observation without cloning the ecology");
        Ok(())
    }).unwrap();
}

#[test]
#[ignore = "requires CUDA; next-symbol development reads the actual resident preparation"]
fn actual_next_symbol_uses_prepared_context_without_guessed_emission() {
    let spec = NativeWaveSeedSpec {
        schema: NATIVE_WAVE_SEED_SCHEMA.into(),
        symbols: vec!['a', 'b', 'x'],
        seed: "ax".into(),
        grain: 64,
    };
    with_seeded_wave_session(&spec, |session| {
        let mut stream=HnaStream::new();
        for _ in 0..8 {
            for (prefix,observed) in [("ax","a"),("bx","b")] {
                session.actuate_text(prefix)?;
                let request=format!("{{\"schema\":\"{}\",\"command\":{{\"action\":\"receive-next-symbol\",\"text\":\"{observed}\"}}}}\n",crate::HNA_STREAM_REQUEST_SCHEMA);
                let mut response=Vec::new();
                stream.pump_wave(session,&mut Input::new(request),&mut response).map_err(invalid)?;
                let result:Value=serde_json::from_slice(&response)?;
                assert_eq!(result["event"],"next-symbol-received","{result}");
            }
        }
        assert_eq!(session.wave.fibre().material_observations,16);
        assert_eq!(session.emission_ordinal,0,"development did not emit a guessed source");
        let mut results=Vec::new();
        for (prefix,expected) in [("aax","a"),("bbx","b")] {
            session.actuate_text(prefix)?;
            let prediction=session.next_symbol(true)?;
            eprintln!("contextual prediction {prefix:?} -> {prediction}");
            results.push((prediction["text"].as_str().unwrap_or("").to_owned(),expected));
        }
        assert_eq!(results,vec![("a".to_owned(),"a"),("b".to_owned(),"b")]);
        Ok(())
    }).unwrap();
}

#[test]
#[ignore = "requires CUDA; native emission re-enters as actual source without a self-target deposit"]
fn emission_reentry_has_actual_effect_and_no_deposit() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut session = session(&s);
    let material = serde_json::to_value(session.wave.fibre().inspect_material().unwrap()).unwrap();
    let first = session.next_symbol(true).unwrap();
    assert_eq!(first["octets"], json!("β".as_bytes()));
    assert!(first["reentry"].is_null());
    let second = session.next_symbol(true).unwrap();
    assert_eq!(second["action"]["generation"], 2);
    assert_eq!(second["successor_epoch"], 3);
    assert_eq!(second["reentry"]["first"]["generation"], 1);
    assert_eq!(second["reentry"]["second"]["generation"], 2);
    assert_eq!(
        session.wave.current().view().inspect().unwrap().center[1].real,
        num_rational::BigRational::from_integer(3.into())
    );
    assert_eq!(
        serde_json::to_value(session.wave.fibre().inspect_material().unwrap()).unwrap(),
        material
    );
    assert_eq!(session.wave.pending_predictions(), 0);
    let predicted = session.predict_symbol(false).unwrap();
    let id = predicted["action"]["prediction"].as_u64().unwrap();
    assert_eq!(session.wave.pending_predictions(), 1);
    session.receive_symbol(id, "a").unwrap();
    assert_eq!(session.wave.pending_predictions(), 0);
    assert_eq!(session.wave.fibre().material_observations, 1);
}

#[test]
#[ignore = "requires CUDA; selection failure is resumed at the same native generation"]
fn pending_selection_rest_retries_without_regeneration() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut session = session(&s);
    session.basis = NormalWaveBasisChart::identity(&s, 1).unwrap(); // receiver fault at its native boundary
    assert!(session.next_symbol(false).is_err());
    assert_eq!(session.wave.epoch(), 1);
    assert!(session.actuate_text("aβ").is_err());
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("pending.hna");
    session
        .checkpoint_stream(&path, &HnaStreamState::default())
        .unwrap();
    session.basis = session.chart.receiver(&s).unwrap();
    let expected = session.next_symbol(true).unwrap();
    let rest = session.wave.rest().unwrap();
    let saved = NativeWaveSavedSession::read(&path).unwrap();
    saved
        .with_session(|resumed, _| {
            assert_eq!(resumed.wave.epoch(), 1);
            assert_eq!(resumed.next_symbol(true)?, expected);
            assert_eq!(resumed.wave.rest()?, rest);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; a late re-entry refusal preserves the selected action and native cut"]
fn pending_reentry_refusal_does_not_regenerate() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let foreign_readout = ResidentReadout::new().unwrap();
    let foreign = ResidentSurface::on(&foreign_readout).unwrap();
    let mut session = session(&s);
    session.next_symbol(false).unwrap();
    // Inject a real source-placement mismatch AFTER a valid emission. The model and its
    // receiver remain on s, while the next re-entry source is mounted on another surface.
    session.surface = &foreign;
    assert!(session.next_symbol(false).is_err());
    assert_eq!(session.wave.epoch(), 2);
    let state = session.inspect();
    let rest = session.wave.rest().unwrap();
    assert!(matches!(session.cursor, Cursor::AwaitReentry { .. }));
    assert!(session.next_symbol(false).is_err());
    assert_eq!(session.inspect(), state);
    assert_eq!(session.wave.rest().unwrap(), rest);
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("refused.hna");
    session
        .checkpoint_stream(&path, &HnaStreamState::default())
        .unwrap();
    session.surface = &s;
    let expected = session.next_symbol(true).unwrap();
    let completed = session.wave.rest().unwrap();
    NativeWaveSavedSession::read(path)
        .unwrap()
        .with_session(|resumed, _| {
            assert_eq!(resumed.inspect(), state);
            assert_eq!(resumed.next_symbol(true)?, expected);
            assert_eq!(resumed.wave.rest()?, completed);
            Ok(())
        })
        .unwrap();
}

struct BrokenWriter {
    bytes: Vec<u8>,
    remaining: usize,
}
impl Write for BrokenWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        if self.remaining == 0 {
            return Err(io::Error::other("declared writer interruption"));
        }
        let n = self.remaining.min(bytes.len());
        self.bytes.extend_from_slice(&bytes[..n]);
        self.remaining -= n;
        Ok(n)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
#[test]
#[ignore = "requires CUDA; shared delivery replays a result without repeating native execution"]
fn broken_delivery_and_checkpoint_keep_next_conduct() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut session = session(&s);
    let mut stream = HnaStream::new();
    let mut input = Input::new(emit_request(false));
    let mut broken = BrokenWriter {
        bytes: vec![],
        remaining: 7,
    };
    assert!(stream
        .pump_wave(&mut session, &mut input, &mut broken)
        .is_err());
    assert_eq!(session.wave.epoch(), 1);
    assert_eq!(session.emission_ordinal, 1);
    let pending = stream.state().output.clone().unwrap();
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("delivery.hna");
    session.checkpoint_stream(&path, stream.state()).unwrap();
    let mut tail = Vec::new();
    stream.drain_pending(&mut tail).unwrap();
    let mut complete = broken.bytes;
    complete.extend(tail);
    assert_eq!(complete, pending);
    let expected = session.next_symbol(true).unwrap();
    let expected_rest = session.wave.rest().unwrap();
    NativeWaveSavedSession::read(path)
        .unwrap()
        .with_session(|resumed, delivery| {
            let before = resumed.wave.epoch();
            delivery.open_new_connection();
            let mut replay = Vec::new();
            delivery.drain_pending(&mut replay).map_err(invalid)?;
            assert_eq!(replay, pending);
            assert_eq!(resumed.wave.epoch(), before);
            assert_eq!(resumed.next_symbol(true)?, expected);
            assert_eq!(resumed.wave.rest()?, expected_rest);
            Ok(())
        })
        .unwrap();
}

#[test]
#[ignore = "requires CUDA; persisted receiver rechart carries both emission and source re-entry"]
fn recharted_codec_survives_session_rest() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let chart =
        SymbolCurrentChart::recharted(SymbolAlphabet::from_chars(&['a', 'β']).unwrap(), vec![1, 0])
            .unwrap();
    let points = chart.mount(&s, &[Symbol(0), Symbol(1)]).unwrap();
    let values = ResidentConstitutiveSection::integers(&points).unwrap();
    let material = ResidentNormalMaterial::found(&s, 2, 2, ResidentGrain(64)).unwrap();
    let wave = material
        .into_applied_difference_wave(values.row(0).unwrap(), values.row(1).unwrap())
        .unwrap();
    let mut session = NativeWaveSession::from_wave(&s, wave, chart).unwrap();
    assert_eq!(
        session.next_symbol(false).unwrap()["octets"],
        json!("β".as_bytes())
    );
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("recharted.hna");
    session
        .checkpoint_stream(&path, &HnaStreamState::default())
        .unwrap();
    let next = session.next_symbol(true).unwrap();
    let rest = session.wave.rest().unwrap();
    NativeWaveSavedSession::read(path)
        .unwrap()
        .with_session(|resumed, _| {
            assert_eq!(resumed.next_symbol(true)?, next);
            assert_eq!(resumed.wave.rest()?, rest);
            Ok(())
        })
        .unwrap();
}
