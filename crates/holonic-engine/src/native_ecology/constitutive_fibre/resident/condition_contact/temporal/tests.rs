use super::*;
use crate::{
    dimensional_wave::ExactComplexWaveCurrent,
    embedding_fiber::ResidentReadout,
    resident_section::{ResidentGrain, ResidentSection, ResidentSectionRest},
};
use num_rational::BigRational as Rat;
use num_traits::Zero;

fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}

fn mount<'c>(surface: &'c ResidentSurface<'c>, words: &[i64]) -> ResidentSection<'c> {
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                words.len(),
                ResidentGrain(0),
                64,
                words.iter().map(|value| (*value, *value)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
}

fn view<'a, 'c>(
    section: &'a ResidentSection<'c>,
    raw_extent: usize,
    origin: i64,
    receiver: u64,
    lineage: u64,
) -> ResidentPhaseCurrentView<'a, 'c> {
    ResidentPhaseCurrentView::new(
        ResidentConstitutiveCurrent::rational(section).unwrap(),
        PhaseCurrentReceiverId(receiver),
        PhaseCurrentLineageId(lineage),
        q(origin, 100),
        q(1, 100),
        4,
        raw_extent,
    )
    .unwrap()
}

fn complex(values: &[(i64, i64)], denominator: i64) -> Vec<ExactComplexWaveCurrent> {
    values
        .iter()
        .map(|(real, imaginary)| {
            ExactComplexWaveCurrent::new(q(*real, denominator), q(*imaginary, denominator))
        })
        .collect()
}

fn realify(values: &[ExactComplexWaveCurrent]) -> Vec<Rat> {
    values
        .iter()
        .flat_map(|value| [value.real.clone(), value.imaginary.clone()])
        .collect()
}

fn complexify(values: &[Rat]) -> Vec<ExactComplexWaveCurrent> {
    values
        .chunks_exact(2)
        .map(|pair| ExactComplexWaveCurrent::new(pair[0].clone(), pair[1].clone()))
        .collect()
}

fn overlap(
    source: &[ExactComplexWaveCurrent],
    response: &[ExactComplexWaveCurrent],
    start: usize,
    length: usize,
) -> Vec<ExactComplexWaveCurrent> {
    convolution(source, response)[start..start + length].to_vec()
}

fn convolution(
    source: &[ExactComplexWaveCurrent],
    response: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    let mut result = vec![ExactComplexWaveCurrent::zero(); source.len() + response.len() - 1];
    for (source_index, source_value) in source.iter().enumerate() {
        for (response_index, response_value) in response.iter().enumerate() {
            result[source_index + response_index] =
                result[source_index + response_index].add(&source_value.multiply(response_value));
        }
    }
    result
}

fn adjoint(
    source: &[ExactComplexWaveCurrent],
    output: &[ExactComplexWaveCurrent],
    prediction_from: usize,
    response_extent: usize,
) -> Vec<ExactComplexWaveCurrent> {
    (0..response_extent)
        .map(|response_index| {
            output
                .iter()
                .enumerate()
                .filter_map(|(offset, value)| {
                    let prediction_index = prediction_from + offset;
                    prediction_index
                        .checked_sub(response_index)
                        .filter(|source_index| *source_index < source.len())
                        .map(|source_index| source[source_index].conjugate().multiply(value))
                })
                .fold(ExactComplexWaveCurrent::zero(), |sum, value| {
                    sum.add(&value)
                })
        })
        .collect()
}

fn sum_norm(values: &[ExactComplexWaveCurrent]) -> Rat {
    values
        .iter()
        .map(ExactComplexWaveCurrent::norm_square)
        .fold(Rat::zero(), |sum, value| sum + value)
}

#[test]
#[ignore = "requires native GPU; exact temporal contact and cold affine-fibre observation"]
fn exact_temporal_contact_preserves_full_fibre_and_cold_projection() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let chart = TemporalResponseChart {
        receiver: PhaseCurrentReceiverId(9),
        origin: q(0, 100),
        sample_step: q(1, 100),
        phase_extent: 4,
        raw_extent: 2,
    };
    let initial = mount(&surface, &[1, 2, -3, 4, 5]);
    let mut current = ResidentTemporalConditionCurrent::retain(
        &surface,
        initial,
        chart.clone(),
        PhaseCurrentLineageId(1),
        5,
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let initial_snapshot = current.snapshot();
    let initial_reading = initial_snapshot.inspect(&surface).unwrap();
    assert_eq!(initial_reading.response, complex(&[(1, 2), (-3, 4)], 5));
    assert!(initial_reading.prior.is_none());

    let source_section = mount(&surface, &[2, 1, -1, 3, 4, -2, 0, 0, 7]);
    let observed_section = mount(&surface, &[7, 2, 3, -4, 11]);
    let source_values = complex(&[(2, 1), (-1, 3), (4, -2)], 7);
    let observed_values = complex(&[(7, 2), (3, -4)], 11);
    let source = view(&source_section, 3, 0, 9, 11);
    let before_forward = surface.census();
    let forward = convolve_enclosed_resident(
        &surface,
        source,
        initial_snapshot.view(),
        chart.receiver,
        PhaseCurrentLineageId(12),
    )
    .unwrap();
    assert_eq!(
        surface.census().section_read_outs,
        before_forward.section_read_outs
    );
    assert!(
        forward
            .view()
            .inspect(&surface)
            .unwrap()
            .contains(&convolution(&source_values, &initial_reading.response,))
    );

    let observed = view(&observed_section, 2, 2, 9, 13);
    let difference = compare_enclosed_resident(
        &surface,
        forward.view(),
        observed,
        PhaseCurrentLineageId(14),
    )
    .unwrap();
    assert_eq!(difference.support().predicted, 2..4);
    assert_eq!(difference.support().observed, 0..2);
    let exact_prediction = convolution(&source_values, &initial_reading.response);
    let exact_difference: Vec<_> = observed_values
        .iter()
        .zip(&exact_prediction[2..4])
        .map(|(observed, predicted)| observed.subtract(predicted))
        .collect();
    assert!(
        difference
            .view()
            .inspect(&surface)
            .unwrap()
            .contains(&exact_difference)
    );

    let family =
        ResidentTemporalConditionPreimage::from_return(&initial_snapshot, &forward, &difference)
            .unwrap();
    let alternate_section = mount(&surface, &[2, -1, 1, 3, 5]);
    let alternate = enclose_resident(&surface, view(&alternate_section, 2, 0, 9, 16), 5).unwrap();
    let before_fibre = surface.census();
    let incoming_e = family
        .unexplained_for(&surface, initial_snapshot.view(), PhaseCurrentLineageId(17))
        .unwrap();
    let alternate_e = family
        .unexplained_for(&surface, alternate.view(), PhaseCurrentLineageId(18))
        .unwrap();
    assert_eq!(
        surface.census().section_read_outs,
        before_fibre.section_read_outs
    );
    let alternate_ball = alternate.view().inspect(&surface).unwrap();
    assert_ne!(alternate_ball.center, initial_reading.response);
    assert!(
        incoming_e
            .view()
            .inspect(&surface)
            .unwrap()
            .contains(&exact_difference)
    );
    let alternate_prediction = convolution(&source_values, &complex(&[(2, -1), (1, 3)], 5));
    let alternate_difference: Vec<_> = observed_values
        .iter()
        .zip(&alternate_prediction[2..4])
        .map(|(observed, predicted)| observed.subtract(predicted))
        .collect();
    assert!(
        alternate_e
            .view()
            .inspect(&surface)
            .unwrap()
            .contains(&alternate_difference)
    );
    let before_contact = surface.census();
    let contact = current.contact(family, PhaseCurrentLineageId(15)).unwrap();
    assert_eq!(
        surface.census().section_read_outs,
        before_contact.section_read_outs
    );
    let successor_snapshot = current.snapshot();
    let successor_reading = successor_snapshot.inspect(&surface).unwrap();
    assert!(
        contact
            .successor()
            .inspect(&surface)
            .unwrap()
            .contains(&successor_reading.response)
    );
    assert_eq!(
        successor_reading.prior.as_deref(),
        Some(initial_reading.response.as_slice())
    );

    let gram = successor_reading.gram.as_ref().unwrap();
    let raw_xy = successor_reading.raw_xy.as_ref().unwrap();
    let px = successor_reading.px.as_ref().unwrap();
    let py = successor_reading.py.as_ref().unwrap();
    let cden = successor_reading.cden.as_ref().unwrap();
    let prior = successor_reading.prior.as_ref().unwrap();
    let h = &successor_reading.response;
    let h_real = realify(h);
    let prior_real = realify(prior);
    let raw_real = realify(raw_xy);
    for row in 0..h_real.len() {
        let left = gram[row]
            .iter()
            .enumerate()
            .map(|(column, value)| value * &h_real[column])
            .fold(Rat::zero(), |sum, value| sum + value)
            + cden * &h_real[row];
        let right = cden * &prior_real[row] + (px / py) * &raw_real[row];
        assert_eq!(left, right);
    }
    let matrix = |gram: &[Vec<Rat>]| {
        let mut matrix = gram.to_vec();
        for (row, values) in matrix.iter_mut().enumerate() {
            values[row] += cden;
        }
        matrix
    };
    let u_rhs: Vec<_> = raw_real.iter().map(|value| (px / py) * value).collect();
    let v_rhs: Vec<_> = prior_real.iter().map(|value| cden * value).collect();
    let u = complexify(&super::inspect::solve_exact(matrix(gram), u_rhs).unwrap());
    let v = complexify(&super::inspect::solve_exact(matrix(gram), v_rhs).unwrap());
    let h_from_normals: Vec<_> = u.iter().zip(&v).map(|(u, v)| u.add(v)).collect();
    assert_eq!(h_from_normals, *h);
    let u_error: Vec<_> = observed_values
        .iter()
        .zip(overlap(&source_values, &u, 2, 2))
        .map(|(observed, predicted)| observed.subtract(&predicted))
        .collect();
    let h_error: Vec<_> = observed_values
        .iter()
        .zip(overlap(&source_values, h, 2, 2))
        .map(|(observed, predicted)| observed.subtract(&predicted))
        .collect();
    let prior_minus_v: Vec<_> = prior
        .iter()
        .zip(&v)
        .map(|(prior, v)| prior.subtract(v))
        .collect();
    let x_v = convolution(&source_values, &v);
    assert!(
        contact
            .incoming_normal_h()
            .inspect(&surface)
            .unwrap()
            .contains(&u)
    );
    assert!(
        contact
            .returned_normal_h()
            .inspect(&surface)
            .unwrap()
            .contains(&prior_minus_v)
    );
    assert!(
        contact.difference_h().inspect(&surface).unwrap().contains(
            &h.iter()
                .zip(prior)
                .map(|(h, prior)| h.subtract(prior))
                .collect::<Vec<_>>()
        )
    );
    assert!(
        contact
            .incoming_normal_e()
            .inspect(&surface)
            .unwrap()
            .contains(&u_error)
    );
    assert!(
        contact
            .unexplained()
            .inspect(&surface)
            .unwrap()
            .contains(&h_error)
    );
    assert!(
        contact
            .returned_normal_e()
            .full
            .inspect(&surface)
            .unwrap()
            .contains(&x_v)
    );
    let prior_energy = sum_norm(prior) + sum_norm(&u) + sum_norm(&u_error);
    let returned_energy =
        sum_norm(h) + sum_norm(&h_error) + sum_norm(&prior_minus_v) + sum_norm(&x_v[2..4]);
    assert_eq!(prior_energy, returned_energy);
    assert_eq!(adjoint(&source_values, &u_error, 2, 2), u);
    assert_eq!(adjoint(&source_values, &x_v[2..4], 2, 2), prior_minus_v);
}

#[test]
#[ignore = "requires native GPU; producing cuts, owner identity, and prediction identity are native boundaries"]
fn stale_cut_uses_current_prior_and_foreign_or_equal_prediction_refuses_atomically() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let chart = TemporalResponseChart {
        receiver: PhaseCurrentReceiverId(3),
        origin: q(0, 100),
        sample_step: q(1, 100),
        phase_extent: 4,
        raw_extent: 2,
    };
    let initial = mount(&surface, &[1, 0, 2, 1, 3]);
    let mut current = ResidentTemporalConditionCurrent::retain(
        &surface,
        initial,
        chart.clone(),
        PhaseCurrentLineageId(20),
        5,
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let snapshot = current.snapshot();
    let source_section = mount(&surface, &[2, 0, 1, 1, 0, 0, 5]);
    let observed_section = mount(&surface, &[3, 1, 1, -1, 7]);
    let forward = convolve_enclosed_resident(
        &surface,
        view(&source_section, 3, 0, 3, 21),
        snapshot.view(),
        chart.receiver,
        PhaseCurrentLineageId(22),
    )
    .unwrap();
    let difference = compare_enclosed_resident(
        &surface,
        forward.view(),
        view(&observed_section, 2, 2, 3, 23),
        PhaseCurrentLineageId(24),
    )
    .unwrap();
    let family =
        ResidentTemporalConditionPreimage::from_return(&snapshot, &forward, &difference).unwrap();
    let first = current.contact(family, PhaseCurrentLineageId(25)).unwrap();
    assert_eq!(current.contacts(), 1);
    let first_reading = current.snapshot().inspect(&surface).unwrap();
    let stale_family =
        ResidentTemporalConditionPreimage::from_return(&snapshot, &forward, &difference).unwrap();
    let second = current
        .contact(stale_family, PhaseCurrentLineageId(26))
        .unwrap();
    assert_eq!(second.current_cut(), 1);
    assert_eq!(current.contacts(), 2);
    let reading = current.snapshot().inspect(&surface).unwrap();
    assert_eq!(reading.prior, Some(first_reading.response));

    let other_initial = mount(&surface, &[2, 0, 1, 1, 3]);
    let mut other = ResidentTemporalConditionCurrent::retain(
        &surface,
        other_initial,
        chart.clone(),
        PhaseCurrentLineageId(30),
        5,
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let before = other.contacts();
    let foreign =
        ResidentTemporalConditionPreimage::from_return(&snapshot, &forward, &difference).unwrap();
    assert!(other.contact(foreign, PhaseCurrentLineageId(31)).is_err());
    assert_eq!(other.contacts(), before);

    let equal_forward = convolve_enclosed_resident(
        &surface,
        view(&source_section, 3, 0, 3, 21),
        snapshot.view(),
        chart.receiver,
        PhaseCurrentLineageId(32),
    )
    .unwrap();
    let equal_difference = compare_enclosed_resident(
        &surface,
        equal_forward.view(),
        view(&observed_section, 2, 2, 3, 23),
        PhaseCurrentLineageId(33),
    )
    .unwrap();
    assert!(matches!(
        ResidentTemporalConditionPreimage::from_return(&snapshot, &forward, &equal_difference),
        Err(ResidentPhaseCurrentError::PredictionMismatch)
    ));
    let _ = first;
}

#[test]
#[ignore = "requires native GPU; zero source leaves all response directions free and retains observation tails"]
fn zero_source_preserves_current_and_separates_support_from_padding() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let chart = TemporalResponseChart {
        receiver: PhaseCurrentReceiverId(3),
        origin: q(0, 1),
        sample_step: q(1, 100),
        phase_extent: 4,
        raw_extent: 3,
    };
    let mut current = ResidentTemporalConditionCurrent::retain(
        &surface,
        mount(&surface, &[1, -2, 3, 4, -5, 6, 7]),
        chart,
        PhaseCurrentLineageId(40),
        40,
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let before = current.snapshot();
    let exact = before.inspect(&surface).unwrap().response;
    let x = mount(&surface, &[0, 0, 0, 0, 0, 0, 1]);
    let y = mount(
        &surface,
        &[8, 1, 2, -3, 4, 5, -6, 7, 8, 9, 10, -11, 0, 0, 13],
    );
    let prediction = convolve_enclosed_resident(
        &surface,
        view(&x, 2, 0, 1, 41),
        before.view(),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(42),
    )
    .unwrap();
    let difference = compare_enclosed_resident(
        &surface,
        prediction.view(),
        view(&y, 6, -1, 3, 43),
        PhaseCurrentLineageId(44),
    )
    .unwrap();
    assert_eq!(difference.support().predicted, 0..4);
    assert_eq!(difference.support().observed, 1..5);
    assert_eq!(
        difference.support().unpredicted_observation,
        vec![0..1, 5..6]
    );
    let family =
        ResidentTemporalConditionPreimage::from_return(&before, &prediction, &difference).unwrap();
    let census = surface.census();
    let contact = current.contact(family, PhaseCurrentLineageId(45)).unwrap();
    assert_eq!(surface.census().section_read_outs, census.section_read_outs);
    assert_eq!(
        current.snapshot().inspect(&surface).unwrap().response,
        exact
    );
    assert!(
        contact
            .unexplained()
            .inspect(&surface)
            .unwrap()
            .contains(&complex(&[(2, -3), (4, 5), (-6, 7), (8, 9)], 13))
    );
    let returned = contact.returned_normal_e().full.inspect(&surface).unwrap();
    assert_eq!(returned.radius, Rat::zero());
    assert_eq!(returned.center, vec![ExactComplexWaveCurrent::zero(); 4]);
}

#[test]
#[ignore = "requires native GPU; arithmetic refusal leaves the sole continuing response unchanged"]
fn projection_aperture_refusal_preserves_current_and_producing_cut() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let chart = TemporalResponseChart {
        receiver: PhaseCurrentReceiverId(3),
        origin: q(0, 1),
        sample_step: q(1, 100),
        phase_extent: 4,
        raw_extent: 2,
    };
    let mut current = ResidentTemporalConditionCurrent::retain(
        &surface,
        mount(&surface, &[1, 0, 0, 0, 1]),
        chart,
        PhaseCurrentLineageId(50),
        72,
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let before = current.snapshot();
    let exact = before.inspect(&surface).unwrap().response;
    let x = mount(&surface, &[1, 0, i64::MAX]);
    let y = mount(&surface, &[1, 0, 1]);
    let prediction = convolve_enclosed_resident(
        &surface,
        view(&x, 1, 0, 1, 51),
        before.view(),
        PhaseCurrentReceiverId(3),
        PhaseCurrentLineageId(52),
    )
    .unwrap();
    let difference = compare_enclosed_resident(
        &surface,
        prediction.view(),
        view(&y, 1, 0, 3, 53),
        PhaseCurrentLineageId(54),
    )
    .unwrap();
    let family =
        ResidentTemporalConditionPreimage::from_return(&before, &prediction, &difference).unwrap();
    let census = surface.census();
    assert!(current.contact(family, PhaseCurrentLineageId(55)).is_err());
    assert_eq!(surface.census().section_read_outs, census.section_read_outs);
    assert_eq!(current.contacts(), 0);
    let after = current.snapshot();
    assert!(std::ptr::eq(
        before.view().section(),
        after.view().section()
    ));
    assert_eq!(after.inspect(&surface).unwrap().response, exact);
}
