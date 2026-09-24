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
