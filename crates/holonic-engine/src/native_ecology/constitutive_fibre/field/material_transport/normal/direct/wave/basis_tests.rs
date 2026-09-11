//! CUDA tests for the native unit-basis receiver.
use super::comparison_tests::point;
use super::comparison_tests::witness;
use super::*;
use crate::embedding_fiber::ResidentReadout;

fn basis_body<'c>(
    surface: &'c ResidentSurface<'c>,
    current_values: &[i64],
) -> ResidentNormalWave<'c> {
    let material = ResidentNormalMaterial::found(surface, 2, 2, ResidentGrain(u32::BITS)).unwrap();
    let previous = point(surface, &[0, 0, 0, 0]);
    let current = point(surface, current_values);
    material
        .into_applied_difference_wave(
            ResidentConstitutiveCurrent::integers(&previous).unwrap(),
            ResidentConstitutiveCurrent::integers(&current).unwrap(),
        )
        .unwrap()
}

#[test]
#[ignore = "requires CUDA; exact centre ties remain distinct from robust interval separation"]
fn exact_centre_ties_keep_the_shared_score_radius() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let body = basis_body(&surface, &[1, 0, 1, 0]);
    let chart = NormalWaveBasisChart::identity(&surface, 2).unwrap();
    let face = body.read_basis_face(&chart).unwrap();
    let reading = face.inspect().unwrap();
    assert_eq!(reading.coordinates, vec![0, 1]);
    assert_eq!(reading.selection.selected, 0);
    assert_eq!(reading.selection.selected_coordinate, 0);
    assert_eq!(reading.selection.centre_score, Rat::one());
    assert_eq!(reading.selection.centre_ties, 2);
    assert!(!reading.selection.robust);
    assert_eq!(reading.scores[0].centre, Rat::one());
    assert_eq!(reading.scores[1].centre, Rat::one());
    assert_eq!(reading.scores[0].lower, reading.scores[1].lower);
    assert_eq!(reading.scores[0].upper, reading.scores[1].upper);
}

#[test]
#[ignore = "requires CUDA; receiver chart permutation changes addresses, not the current"]
fn source_and_receiver_permutation_selects_declared_coordinate() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let body = basis_body(&surface, &[1, 0, 2, 0]);
    let chart = NormalWaveBasisChart::from_permutation(&surface, &[1, 0]).unwrap();
    let face = body.read_basis_face(&chart).unwrap();
    let reading = face.inspect().unwrap();
    assert_eq!(reading.coordinates, vec![1, 0]);
    assert_eq!(reading.selection.selected, 0);
    assert_eq!(reading.selection.selected_coordinate, 1);
    assert_eq!(reading.selection.centre_score, Rat::new(2.into(), 1.into()));
    assert_eq!(reading.selection.centre_ties, 1);
    assert!(reading.selection.robust);
    assert_eq!(reading.scores[0].centre, Rat::new(2.into(), 1.into()));
    assert_eq!(reading.scores[1].centre, Rat::one());
}

#[test]
#[ignore = "requires CUDA; score reads real unit coordinates and retains imaginary phase"]
fn negative_real_score_beats_no_coordinate_even_with_large_imaginary_phase() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let body = basis_body(&surface, &[-1, 1_000_000, 0, 2_000_000]);
    let chart = NormalWaveBasisChart::identity(&surface, 2).unwrap();
    let reading = body.read_basis_face(&chart).unwrap().inspect().unwrap();
    assert_eq!(reading.selection.selected_coordinate, 1);
    assert_eq!(reading.selection.centre_score, Rat::zero());
    assert_eq!(reading.scores[0].centre, Rat::new((-1).into(), 1.into()));
    assert_eq!(reading.scores[1].centre, Rat::zero());
}

#[test]
#[ignore = "requires CUDA; foreign charts and malformed dimensions refuse without publishing"]
fn foreign_or_wrong_shape_chart_leaves_body_and_current_unchanged() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let foreign_readout = ResidentReadout::new().unwrap();
    let foreign_surface = ResidentSurface::on(&foreign_readout).unwrap();
    let body = basis_body(&surface, &[1, 0, 1, 0]);
    let held = body.current().snapshot();
    let before = body.rest().unwrap();
    let foreign = NormalWaveBasisChart::identity(&foreign_surface, 2).unwrap();
    assert!(body.read_basis_face(&foreign).is_err());
    let wrong = NormalWaveBasisChart::identity(&surface, 1).unwrap();
    assert!(body.read_basis_face(&wrong).is_err());
    drop(foreign);
    drop(wrong);
    assert!(body.current().same_occurrence(&held));
    assert_eq!(body.rest().unwrap(), before);
    assert_eq!(body.fibre().transport, NormalWaveTransport::Applied);
}

#[test]
#[ignore = "requires CUDA; a nonzero-radius joint is received as one shared family"]
fn correlated_joint_radius_is_retained_without_host_selection() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = witness(&surface);
    body.advance().unwrap();
    let chart = NormalWaveBasisChart::identity(&surface, 1).unwrap();
    let reads = surface.census().section_read_outs;
    let face = body.read_basis_face(&chart).unwrap();
    assert_eq!(surface.census().section_read_outs, reads);
    drop(chart);
    let reading = face.inspect().unwrap();
    assert!(reading.selection.robust);
    assert!(reading.selection.score_radius > Rat::zero());
    assert_eq!(reading.scores.len(), 1);
    assert_eq!(
        &reading.scores[0].upper - &reading.scores[0].lower,
        &reading.selection.score_radius + &reading.selection.score_radius
    );
    assert_eq!(reading.epoch, Some(body.epoch()));
}

#[test]
#[ignore = "requires CUDA; exact differences and interval endpoints can exceed a source word"]
fn extreme_shared_enclosure_keeps_selection_and_exact_interval_decoder() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let m = ResidentNormalMaterial::found(&s, 2, 2, ResidentGrain(64)).unwrap();
    let max = i128::MAX;
    let values = [0i128, 0, 0, 0, -max, 0, max, 0, max];
    let words: Vec<_> = values
        .into_iter()
        .flat_map(|v| [v as i64, (v >> 64) as i64])
        .map(|v| (v, v))
        .collect();
    let joint = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap();
    let body = m.into_joint_wave(Rc::new(joint), 0).unwrap();
    let chart = NormalWaveBasisChart::identity(&s, 2).unwrap();
    let held = body.current().snapshot();
    let face = body.read_basis_face(&chart).unwrap();
    let reading = face.inspect().unwrap();
    assert_eq!(reading.selection.selected, 1);
    assert_eq!(reading.selection.centre_ties, 1);
    assert!(!reading.selection.robust); // gap equals two radii, not strict separation
    assert!(
        &reading.scores[1].upper * Rat::from_integer(BigInt::one() << 64)
            > Rat::from_integer(max.into())
    );
    assert!(face.source().same_occurrence(&held));
    assert_eq!(
        face.source().view().inspect().unwrap().radius,
        reading.selection.score_radius
    );
}

#[test]
#[ignore = "requires CUDA; passive coordinate transport moves source and receiver together"]
fn source_and_basis_rechart_preserve_the_action() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let a = basis_body(&s, &[1, 0, 2, 0]);
    let b = basis_body(&s, &[2, 0, 1, 0]);
    let ca = NormalWaveBasisChart::identity(&s, 2).unwrap();
    let cb = NormalWaveBasisChart::from_permutation(&s, &[1, 0]).unwrap();
    let fa = a.read_basis_face(&ca).unwrap().inspect().unwrap();
    let fb = b.read_basis_face(&cb).unwrap().inspect().unwrap();
    assert_eq!(fa.selection.selected, fb.selection.selected);
    assert_eq!(fa.scores, fb.scores);
}
