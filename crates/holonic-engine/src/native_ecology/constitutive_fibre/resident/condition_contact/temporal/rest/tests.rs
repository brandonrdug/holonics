use super::*;
use num_rational::BigRational as Rat;

fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}

fn section(words: Vec<i64>) -> ResidentSectionRest {
    ResidentSectionRest::found(
        1,
        words.len(),
        ResidentGrain(0),
        64,
        words.into_iter().map(|value| (value, value)).collect(),
    )
    .unwrap()
}

fn wide_set(intervals: &mut [(i64, i64)], at: usize, value: i128) {
    let low = value as i64;
    let high = (value >> 64) as i64;
    intervals[2 * at] = (low, low);
    intervals[2 * at + 1] = (high, high);
}

fn valid_rest() -> ResidentTemporalConditionRest {
    let chart = TemporalResponseChart {
        receiver: PhaseCurrentReceiverId(7),
        origin: q(0, 100),
        sample_step: q(1, 100),
        phase_extent: 4,
        raw_extent: 1,
    };
    let initial = section(vec![1, 0, 2]);
    let mut initial_ball_words = vec![(0, 0); 6];
    wide_set(&mut initial_ball_words, 0, 4);
    wide_set(&mut initial_ball_words, 1, 0);
    wide_set(&mut initial_ball_words, 2, 0);
    let initial_ball = ResidentSectionRest::found(
        1,
        initial_ball_words.len(),
        ResidentGrain(0),
        64,
        initial_ball_words,
    )
    .unwrap();

    let dimension = 2;
    let stride = dimension + 1;
    let tail = 8 * stride;
    let total = tail + dimension * dimension + dimension + 3;
    let mut report_words = vec![(0, 0); total * 2];
    wide_set(&mut report_words, 0, 4);
    wide_set(&mut report_words, stride, 4);
    wide_set(&mut report_words, 3 * stride, 4);
    wide_set(&mut report_words, 6 * stride + dimension, 1);
    wide_set(&mut report_words, 7 * stride + dimension, 1);
    wide_set(
        &mut report_words,
        tail + dimension * dimension + dimension,
        1,
    );
    wide_set(
        &mut report_words,
        tail + dimension * dimension + dimension + 1,
        1,
    );
    wide_set(
        &mut report_words,
        tail + dimension * dimension + dimension + 2,
        1,
    );
    let report =
        ResidentSectionRest::found(1, report_words.len(), ResidentGrain(0), 64, report_words)
            .unwrap();

    ResidentTemporalConditionRest {
        header: Header {
            chart,
            metric: ConditionContactMetric::UnitAdmittanceRealification,
            grain: 3,
            initial_lineage: PhaseCurrentLineageId(10),
            contacts: vec![ContactHeader {
                cut: 1,
                at: 3 * stride,
                lineage: PhaseCurrentLineageId(11),
            }],
        },
        initial,
        initial_ball,
        reports: vec![report],
    }
}

fn encoded(rest: &ResidentTemporalConditionRest) -> Vec<u8> {
    let mut bytes = Vec::new();
    rest.write(&mut bytes).unwrap();
    bytes
}

fn mounted<'c>(surface: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                values.len(),
                ResidentGrain(0),
                64,
                values.iter().map(|value| (*value, *value)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
}

fn phase_view<'a, 'c>(
    chart: &TemporalResponseChart,
    section: &'a ResidentSection<'c>,
    raw_extent: usize,
    lineage: u64,
) -> ResidentPhaseCurrentView<'a, 'c> {
    ResidentPhaseCurrentView::new(
        ResidentConstitutiveCurrent::rational(section).unwrap(),
        chart.receiver,
        PhaseCurrentLineageId(lineage),
        chart.origin.clone(),
        chart.sample_step.clone(),
        chart.phase_extent,
        raw_extent,
    )
    .unwrap()
}

#[test]
fn canonical_roundtrip_preserves_temporal_chain() {
    let original = valid_rest();
    original.validate().unwrap();
    let mut bytes = Vec::new();
    original.write(&mut bytes).unwrap();
    let decoded =
        ResidentTemporalConditionRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(decoded, original);
    assert_eq!(decoded.chart(), original.chart());
    assert_eq!(decoded.grain(), 3);
    assert_eq!(decoded.contacts(), 1);
    assert_eq!(
        decoded.metric(),
        ConditionContactMetric::UnitAdmittanceRealification
    );
}

#[test]
fn malformed_temporal_chain_and_wire_are_refused() {
    let mut malformed = valid_rest();
    malformed.reports[0].intervals[3 * 2] = (5, 5);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    malformed.reports[0].intervals[2 * (24 + 1)] = (1, 1);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    // The two residual carriers have their own positive scalar denominators, after the
    // D-dimensional signed numerator vector.  A zero denominator is never a valid report.
    malformed.reports[0].intervals[2 * (6 * 3 + 2)] = (0, 0);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    malformed.reports[0].intervals[2 * (7 * 3 + 2)] = (0, 0);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    // A radius change must agree with the staged normal/difference radius algebra.
    malformed.reports[0].intervals[2 * (3 * 3 + 2)] = (1, 1);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    // Make a symmetric zero Gram block with a nonzero cross term.  PSD admission must
    // reject the zero pivot instead of silently accepting an indefinite matrix.
    let tail = 8 * 3;
    malformed.reports[0].intervals[2 * (tail + 1)] = (1, 1);
    malformed.reports[0].intervals[2 * (tail + 2)] = (1, 1);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    // The initial dyadic lift is a certificate of the exact point, not an unrelated ball.
    malformed.initial_ball.intervals[0] = (5, 5);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    malformed.reports[0].intervals[2 * 32] = (0, 0);
    assert!(malformed.validate().is_err());

    let mut malformed = valid_rest();
    malformed.initial_ball.intervals[4] = (-1, -1);
    assert!(malformed.validate().is_err());

    let original = valid_rest();
    let mut bytes = encoded(&original);
    bytes.pop();
    assert!(
        ResidentTemporalConditionRest::read(&mut bytes.as_slice(), bytes.len() as u64).is_err()
    );

    let mut bytes = encoded(&original);
    bytes.push(0);
    assert!(
        ResidentTemporalConditionRest::read(&mut bytes.as_slice(), bytes.len() as u64).is_err()
    );
}

#[test]
#[ignore = "requires native GPU; remount preserves the temporal owner without replaying contact"]
fn remount_preserves_cold_response_and_contact_cut() {
    use crate::embedding_fiber::ResidentReadout;

    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let rest = valid_rest();
    let current = ResidentTemporalConditionCurrent::remount(&surface, rest).unwrap();
    let reading = current.snapshot().inspect(&surface).unwrap();
    assert_eq!(current.contacts(), 1);
    assert_eq!(
        reading.response,
        vec![ExactComplexWaveCurrent::new(q(1, 2), q(0, 1))]
    );
}

#[test]
#[ignore = "requires native GPU; remount must accept the next contact as the same continuing owner"]
fn remount_then_next_contact_matches_uninterrupted_owner() {
    use crate::embedding_fiber::ResidentReadout;

    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let chart = TemporalResponseChart {
        receiver: PhaseCurrentReceiverId(19),
        origin: q(0, 100),
        sample_step: q(1, 100),
        phase_extent: 4,
        raw_extent: 2,
    };
    let mut uninterrupted = ResidentTemporalConditionCurrent::retain(
        &surface,
        mounted(&surface, &[1, 0, -1, 2, 5]),
        chart.clone(),
        PhaseCurrentLineageId(60),
        5,
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let initial = uninterrupted.snapshot();
    let source = mounted(&surface, &[2, 1, -1, 3, 0, -2, 7]);
    let observed = mounted(&surface, &[3, -1, 2, 4, 11]);
    let forward = convolve_enclosed_resident(
        &surface,
        phase_view(&chart, &source, 3, 61),
        initial.view(),
        chart.receiver,
        PhaseCurrentLineageId(62),
    )
    .unwrap();
    let difference = compare_enclosed_resident(
        &surface,
        forward.view(),
        phase_view(&chart, &observed, 2, 63),
        PhaseCurrentLineageId(64),
    )
    .unwrap();
    let family =
        ResidentTemporalConditionPreimage::from_return(&initial, &forward, &difference).unwrap();
    uninterrupted
        .contact(family, PhaseCurrentLineageId(65))
        .unwrap();

    let rest = uninterrupted.rest().unwrap();
    // Build independent source/observed return charts for the two producing cuts.  The
    // remounted family must use its own immutable standing while retaining the same exact data.
    let source_next = mounted(&surface, &[1, -2, 2, 1, 0, 3, 8]);
    let observed_next = mounted(&surface, &[4, 1, -3, 2, 13]);
    let uninterrupted_snapshot = uninterrupted.snapshot();
    let uninterrupted_forward = convolve_enclosed_resident(
        &surface,
        phase_view(&chart, &source_next, 3, 66),
        uninterrupted_snapshot.view(),
        chart.receiver,
        PhaseCurrentLineageId(67),
    )
    .unwrap();
    let uninterrupted_difference = compare_enclosed_resident(
        &surface,
        uninterrupted_forward.view(),
        phase_view(&chart, &observed_next, 2, 68),
        PhaseCurrentLineageId(69),
    )
    .unwrap();
    let uninterrupted_family = ResidentTemporalConditionPreimage::from_return(
        &uninterrupted_snapshot,
        &uninterrupted_forward,
        &uninterrupted_difference,
    )
    .unwrap();

    uninterrupted
        .contact(uninterrupted_family, PhaseCurrentLineageId(70))
        .unwrap();
    let expected_reading = uninterrupted.snapshot().inspect(&surface).unwrap();
    let expected_ball = uninterrupted.snapshot().view().inspect(&surface).unwrap();
    let expected_rest = uninterrupted.rest().unwrap();
    drop(uninterrupted);
    // Only now transfer the earlier saved cut into a new move owner. The reference trajectory
    // above has ended; immutable producing carriers may remain borrowed by its old receipts.
    let mut remounted = ResidentTemporalConditionCurrent::remount(&surface, rest).unwrap();
    let remounted_snapshot = remounted.snapshot();
    let remounted_forward = convolve_enclosed_resident(
        &surface,
        phase_view(&chart, &source_next, 3, 66),
        remounted_snapshot.view(),
        chart.receiver,
        PhaseCurrentLineageId(67),
    )
    .unwrap();
    let remounted_difference = compare_enclosed_resident(
        &surface,
        remounted_forward.view(),
        phase_view(&chart, &observed_next, 2, 68),
        PhaseCurrentLineageId(69),
    )
    .unwrap();
    let remounted_family = ResidentTemporalConditionPreimage::from_return(
        &remounted_snapshot,
        &remounted_forward,
        &remounted_difference,
    )
    .unwrap();

    remounted
        .contact(remounted_family, PhaseCurrentLineageId(70))
        .unwrap();
    assert_eq!(
        remounted.snapshot().inspect(&surface).unwrap(),
        expected_reading
    );
    assert_eq!(
        remounted.snapshot().view().inspect(&surface).unwrap(),
        expected_ball
    );
    assert_eq!(remounted.rest().unwrap(), expected_rest);
}
