use super::super::comparison_tests::{current, point, wave, witness};
use super::*;
use crate::embedding_fiber::ResidentReadout;

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
    let source = body.read_source().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(source.previous().same_occurrence(body.previous()));
    assert!(source.current().same_occurrence(body.current()));
    let seen = source.enclosure().inspect().unwrap();
    assert_eq!(
        seen.center,
        vec![wave(3, -2, 1), wave(5, -1, 1), wave(2, 1, 1)]
    );
    assert_eq!(seen.radius, Rat::zero());
    body.advance().unwrap();
    assert!(source.current().same_occurrence(body.previous()));
    assert_eq!(source.fibre().epoch, 0);
    assert_eq!(source.enclosure().inspect().unwrap().center, seen.center);
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
    let source = body.read_source().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let joint = source.joint().inspect().unwrap();
    let lifted = source.enclosure().inspect().unwrap();
    assert!(joint.radius > Rat::zero());
    assert_eq!(lifted.radius, &joint.radius + &joint.radius);
    assert_eq!(lifted.center[0], joint.center[1].subtract(&joint.center[0]));
    assert_eq!(lifted.center[1], joint.center[1]);
    assert_eq!(lifted.center[2], joint.center[0]);
    assert_eq!(body.rest().unwrap(), before);
}
