use super::*;
use crate::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::ResidentConstitutiveCurrent,
    resident_section::{ResidentGrain, ResidentSectionRest},
};
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
    receiver: u64,
    lineage: u64,
    origin: i64,
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

fn complex(values: &[Rat]) -> Vec<ExactComplexWaveCurrent> {
    values
        .chunks_exact(2)
        .map(|pair| ExactComplexWaveCurrent::new(pair[0].clone(), pair[1].clone()))
        .collect()
}

fn cold_convolution(
    source: &[ExactComplexWaveCurrent],
    response: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    let mut output = vec![ExactComplexWaveCurrent::zero(); source.len() + response.len() - 1];
    for (i, left) in source.iter().enumerate() {
        for (j, right) in response.iter().enumerate() {
            output[i + j] = output[i + j].add(&left.multiply(right));
        }
    }
    output
}

#[test]
#[ignore = "requires native GPU; enclosure lift keeps a point centre and zero radius resident"]
fn point_lift_inspects_exact_dyadic_ball_without_point_port() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let point_section = mount(&surface, &[1, 2, -3, 4, 4]);
    let point = view(&point_section, 2, 1, 2, 0);
    let before = surface.census();
    let enclosure = enclose_resident(&surface, point, 3).unwrap();
    let after = surface.census();
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(after.ingress_octets, before.ingress_octets);
    let inspected = enclosure.view().inspect(&surface).unwrap();
    assert_eq!(
        inspected.center,
        complex(&[q(1, 4), q(2, 4), q(-3, 4), q(4, 4)])
    );
    assert_eq!(inspected.radius, Rat::zero());
    assert_eq!(enclosure.view().raw_extent(), 2);
}

#[test]
#[ignore = "requires native GPU; enclosed convolution preserves the exact cold polynomial"]
fn enclosed_convolution_contains_non_dyadic_cold_result_and_retains_inputs() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let source_section = mount(&surface, &[1, 2, 2, -1, 3]);
    let response_section = mount(&surface, &[2, -1, 1, 3, 3]);
    let source = view(&source_section, 2, 1, 2, 0);
    let response = enclose_resident(&surface, view(&response_section, 2, 3, 4, 0), 5).unwrap();
    let before = surface.census();
    let result = convolve_enclosed_resident(
        &surface,
        source,
        response.view(),
        PhaseCurrentReceiverId(7),
        PhaseCurrentLineageId(8),
    )
    .unwrap();
    let after = surface.census();
    assert_eq!(after.section_read_outs, before.section_read_outs);
    assert_eq!(after.ingress_octets, before.ingress_octets);
    let expected = cold_convolution(
        &complex(&[q(1, 3), q(2, 3), q(2, 3), q(-1, 3)]),
        &complex(&[q(2, 3), q(-1, 3), q(1, 3), q(3, 3)]),
    );
    assert!(result.view().inspect(&surface).unwrap().contains(&expected));
    assert_eq!(result.source().raw_extent(), 2);
    assert_eq!(result.response().raw_extent(), 2);
    assert_eq!(result.view().raw_extent(), 3);
}

#[test]
#[ignore = "requires native GPU; zero source annihilates the enclosed response"]
fn zero_source_annihilates_enclosed_response() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let source_section = mount(&surface, &[0, 0, 0, 0, 1]);
    let response_section = mount(&surface, &[2, -1, 1, 3, 3]);
    let response = enclose_resident(&surface, view(&response_section, 2, 3, 4, 0), 5).unwrap();
    let result = convolve_enclosed_resident(
        &surface,
        view(&source_section, 2, 1, 2, 0),
        response.view(),
        PhaseCurrentReceiverId(7),
        PhaseCurrentLineageId(8),
    )
    .unwrap();
    let ball = result.view().inspect(&surface).unwrap();
    assert_eq!(ball.radius, Rat::zero());
    assert_eq!(
        ball.center,
        vec![
            ExactComplexWaveCurrent::zero(),
            ExactComplexWaveCurrent::zero(),
            ExactComplexWaveCurrent::zero(),
        ]
    );
}

#[test]
#[ignore = "requires native GPU; shifted exact support retains excluded tails and oriented difference"]
fn enclosed_difference_preserves_shifted_support_and_full_prediction() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let predicted_section = mount(&surface, &[1, 0, 2, 0, 1]);
    let observed_section = mount(&surface, &[4, 0, 1, 0, 3]);
    let predicted = enclose_resident(&surface, view(&predicted_section, 2, 1, 2, 0), 4).unwrap();
    let observed = view(&observed_section, 2, 1, 5, 1);
    let difference = compare_enclosed_resident(
        &surface,
        predicted.view(),
        observed,
        PhaseCurrentLineageId(6),
    )
    .unwrap();
    assert_eq!(difference.support().predicted, 1..2);
    assert_eq!(difference.support().observed, 0..1);
    assert_eq!(difference.support().unobserved_prediction, vec![0..1]);
    assert_eq!(difference.support().unpredicted_observation, vec![1..2]);
    let expected = vec![ExactComplexWaveCurrent::new(q(-2, 3), Rat::zero())];
    assert!(
        difference
            .view()
            .inspect(&surface)
            .unwrap()
            .contains(&expected)
    );
}

#[test]
#[ignore = "requires native GPU; malformed enclosure radius is refused by the cold decoder"]
fn malformed_radius_is_refused_without_a_point_reinterpretation() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let malformed = mount(&surface, &[0, 0, 0, 0, -1, -1]);
    let view = ResidentPhaseEnclosureView::new(
        &malformed,
        0,
        4,
        PhaseCurrentReceiverId(1),
        PhaseCurrentLineageId(2),
        Rat::zero(),
        q(1, 100),
        4,
        1,
    )
    .unwrap();
    assert!(view.inspect(&surface).is_err());
}

#[test]
fn malformed_grain_and_overflow_are_refused_before_native_work() {
    assert!(matches!(
        wire_words(usize::MAX),
        Err(ResidentPhaseCurrentError::Chart(
            PhaseCurrentError::CarrierOverflow
        ))
    ));
}
