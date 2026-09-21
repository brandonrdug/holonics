use super::*;

fn q(value: i64) -> Rat {
    Rat::from_integer(value.into())
}

#[test]
fn phase_restriction_is_exact_transport_minus_receiver() {
    let source = AnalyticFieldJunctionId(1);
    let receiver = AnalyticFieldJunctionId(2);
    let indices = BTreeMap::from([(source, 0usize), (receiver, 1usize)]);
    let incoming = [NativeFieldIncomingArc {
        arc: AnalyticFieldArcId(7),
        from: source,
        to: receiver,
        mode: DimensionalWaveModeId(3),
        delay: 1,
        phase: ExactWavePhaseTransport::new(q(0), q(1)).unwrap(),
    }];
    let matrix = condition_matrix(&incoming, &indices, 1, 4, 2).unwrap();
    assert_eq!(
        matrix.to_rows(),
        vec![
            vec![q(0), q(-1), q(-1), q(0)],
            vec![q(1), q(0), q(0), q(-1)],
        ]
    );
}

#[test]
fn identity_self_comparison_is_recorded_as_omitted_provenance() {
    let phase = ExactWavePhaseTransport::identity();
    assert!(phase.is_unit());
    let omitted = NativeFieldOmittedSelfComparison {
        receiver: AnalyticFieldJunctionId(4),
        phase,
        reason: "identity self comparison has zero contrast".into(),
        arc: None,
    };
    assert_eq!(omitted.reason, "identity self comparison has zero contrast");
}
