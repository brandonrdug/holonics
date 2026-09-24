use super::*;

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
