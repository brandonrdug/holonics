use super::super::comparison_tests::{current, point, wave, witness};
use super::*;
use crate::embedding_fiber::ResidentReadout;

#[test]
#[ignore = "requires CUDA; step and source use one immutable origin and its actual metadata"]
fn step_and_joint_source_share_one_canonical_current_receipt() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = witness(&s);
    let step = body.advance().unwrap();
    let source = body.joint_source();
    assert!(step.previous().same_occurrence(source.previous()));
    assert!(step.current().same_occurrence(source.current()));
    assert!(Rc::ptr_eq(&step.joint, &source.joint));
    assert!(Rc::ptr_eq(&step.metadata, &source.metadata));
    assert!(Rc::ptr_eq(&step.fibre().material, &source.fibre().material));
    assert_eq!(
        serde_json::to_value(step.inspect().unwrap()).unwrap(),
        serde_json::to_value(source.inspect().unwrap()).unwrap()
    );
    let saved = source.snapshot();
    let before = serde_json::to_value(saved.inspect().unwrap()).unwrap();
    body.advance().unwrap();
    assert!(saved.current().same_occurrence(body.previous()));
    assert!(!saved.current().same_occurrence(body.current()));
    assert_eq!(
        serde_json::to_value(saved.inspect().unwrap()).unwrap(),
        before
    );
    // The lift is a reading of the saved point; the point keeps its occurrences.
    saved.read_source().unwrap();
    assert!(saved.current().same_occurrence(step.current()));
}

#[test]
#[ignore = "requires CUDA; source lift preserves the actual joint rather than independent marginals"]
fn source_lift_keeps_joint_occurrences_and_correlated_plane() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let m = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(32)).unwrap();
    let p = point(&s, &[2, 1]);
    let c = point(&s, &[5, -1]);
    let mut body = m
        .into_applied_difference_wave(current(&p), current(&c))
        .unwrap();
    let reads = s.census().section_read_outs;
    let state = body.joint_source();
    let source = state.read_source().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(state.previous().same_occurrence(body.previous()));
    assert!(state.current().same_occurrence(body.current()));
    let seen = source.inspect().unwrap();
    assert_eq!(
        seen.center,
        vec![wave(3, -2, 1), wave(5, -1, 1), wave(2, 1, 1)]
    );
    assert_eq!(seen.radius, Rat::zero());
    body.advance().unwrap();
    assert!(state.current().same_occurrence(body.previous()));
    assert_eq!(state.fibre().epoch, 0);
    assert_eq!(source.inspect().unwrap().center, seen.center);
}

#[test]
#[ignore = "requires CUDA; nonzero joint uncertainty survives the derived source enclosure"]
fn bounded_source_lift_retains_radius_and_no_material_change() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = witness(&s);
    body.advance().unwrap();
    let before = body.rest().unwrap();
    let reads = s.census().section_read_outs;
    let state = body.joint_source();
    let source = state.read_source().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let joint = state.joint().inspect().unwrap();
    let lifted = source.inspect().unwrap();
    assert!(joint.radius > Rat::zero());
    assert_eq!(lifted.radius, &joint.radius + &joint.radius);
    assert_eq!(lifted.center[0], joint.center[1].subtract(&joint.center[0]));
    assert_eq!(lifted.center[1], joint.center[1]);
    assert_eq!(lifted.center[2], joint.center[0]);
    assert_eq!(body.rest().unwrap(), before);
}
