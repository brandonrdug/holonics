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

#[test]
fn exact_bit_counts_use_reduced_numerators_and_denominators() {
    let mut count = ExactBitCount::default();
    count.dyadic(0, 48);
    count.dyadic(1 << 47, 48); // 1/2: 1 + 1 + 2
    count.dyadic(-3, 2); // -3/4: 2 + 1 + 3
    assert_eq!(count.values, 3);
    assert_eq!(count.bits, 2 + 4 + 6);
    let mut json = ExactBitCount::default();
    json.json(&json!({"a":["1/2","-3/4","0"],"id":"g0","n":7}));
    let wire = serde_json::to_value(Rat::new((-6).into(), 8.into())).unwrap();
    json.json(&json!({"centre":[wire]}));
    assert_eq!(json.values, 4);
    assert_eq!(json.bits, 4 + 6 + 2 + 6);
}

#[test]
fn exposure_code_lengths_are_exterior_counts() {
    let mut stream = crate::alpha::exposure::ExposureCodeLength::default();
    stream.ingest(&[0, 1, 0, 1], None);
    assert!((stream.order0_bits() - 4.0).abs() < 1e-12);
    // Contexts: None->0, 0->1, 1->0, 0->1: only the 0 context has two occurrences, both 1.
    assert!(stream.order1_bits().abs() < 1e-12);
    let (zero, one) = stream.predictive_bits(&[1], Some(0), 2);
    assert!((zero - 1.0).abs() < 1e-12);
    assert!((one - (4.0f64 / 3.0).log2()).abs() < 1e-12);
}

/// The six-cycle control of `generator_application/tests.rs`, reconstructed through the public
/// request/observe calls and read by the exterior observer. The printed JSON lines are the
/// "before" numbers of the moment-accumulation campaign; nothing is asserted about their values.
#[test]
#[ignore = "requires CUDA; prints the six-cycle exterior return readings"]
fn six_cycle_control_return_readings() {
    super::super::with_field_session(
        &generator_machine::generator_session_spec(2, 6, 2).unwrap(),
        |session| {
            let mut observer = ExteriorReturnObserver::default();
            for step in 0..6 {
                let (source, target) = if step % 2 == 0 {
                    ("ab", "ba")
                } else {
                    ("ba", "ab")
                };
                let generated = session.measured_request(&request(source, true), &mut observer)?;
                let id = generated["comparison"].as_u64().unwrap();
                let (_, reading) = session.read_return(id, target, 8, &mut observer)?;
                assert!(reading.target.model.centre_bits.is_finite());
                assert_eq!(reading.target.receiving_rows, 3);
                // The ratio's phase part is read at every row through the target Holon, the
                // pending operands are fixed-size resident sections, and every ring reports.
                assert!(reading.target.phase_excess_bits.is_some());
                assert!(reading.target.rows.iter().all(|row| row.stop.produced_phase.is_some()
                    && row.stop.target_phase.is_some()));
                assert!(reading.state.pending_body_octets > 0);
                assert_eq!(reading.navigation.sites.len(), 2);
                assert!(!reading.navigation.contacts.is_empty());
                eprintln!(
                    "SIX-CYCLE-SUMMARY {}",
                    json!({"cycle":step,"generated":generated["text"],
                        "model_bits":reading.target.model.centre_bits,
                        "phase_excess_bits":reading.target.phase_excess_bits,
                        "d_model_bits":reading.target.model_bits_per_observation,
                        "d_phase_bits":reading.target.phase_excess_bits_per_observation,
                        "gain_uniform":reading.target.gain_uniform_bits,
                        "gain_order0":reading.target.gain_order0_bits,
                        "support":reading.target.support,
                        "pending_octets":reading.state.pending_octets,
                        "pending_body_sections":reading.state.pending_body_sections,
                        "pending_relation_words":reading.state.pending_relation_words,
                        "state_bits":reading.state.state_bits,
                        "rebase_residual":reading.state.rebase_residual,
                        "erasure_bits":reading.work.erasure_bits,
                        "observe_launches":reading.work.observe_launches,
                        "phase_descent_bits":reading.target.phase_descent_bits,
                        "observe_seconds":reading.observe_seconds,
                        "sites":reading.navigation.sites.iter().map(|s| json!({"site":s.site,
                            "ticks":s.ticks,"phase_exponent":s.phase_exponent,
                            "windings":s.committed_windings,"energy":s.current_energy,
                            "d_energy_per_tick":s.energy_increment_per_tick,
                            "energy_increment_variance":s.energy_increment_variance})).collect::<Vec<_>>(),
                        "contacts":reading.navigation.contacts.iter().map(|c| json!({"arc":c.arc,
                            "amplitude":c.amplitude,"contrast":c.interface_contrast})).collect::<Vec<_>>()})
                );
                eprintln!(
                    "SIX-CYCLE {}",
                    json!({"cycle":step,"source":source,"target":target,
                        "generated":generated["text"],"reading":reading})
                );
            }
            Ok(())
        },
    )
    .unwrap();
}
