use super::super::contact_tests::{current, points};
use super::*;
use crate::embedding_fiber::ResidentReadout;
use num_traits::Zero;

const METRIC: ConditionContactMetric = ConditionContactMetric::UnitAdmittanceRealification;
fn rats(v: &[i64], d: i64) -> Vec<Rat> {
    v.iter().map(|n| Rat::new((*n).into(), d.into())).collect()
}
fn norm(v: &[Rat]) -> Rat {
    v.iter().map(|x| x * x).sum()
}
fn check_balance(r: &AffineContactReading) {
    assert_eq!(
        norm(&r.predecessor) + norm(&r.incoming_normal),
        norm(&r.successor) + norm(&r.returned_normal)
    );
    for j in 0..r.predecessor.len() {
        assert_eq!(r.successor[j].clone() - &r.predecessor[j], r.difference[j]);
        assert_eq!(
            r.incoming_normal[j].clone() - &r.returned_normal[j],
            r.difference[j]
        );
    }
}

// Public relation deposits for the exact algebra control y=(n dot c,0), independent of s.
// This helper is a test fixture, never the production learner or example's world.
fn plane<'c>(s: &'c ResidentSurface<'c>, n: [i64; 2]) -> ResidentConstitutiveFibre<'c> {
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(s, 1, 1, 1).unwrap();
    for (x, c) in [
        ([0, 0], [1, 0]),
        ([0, 0], [0, 1]),
        ([1, 0], [0, 0]),
        ([0, 1], [0, 0]),
        ([1, 0], [1, 0]),
        ([0, 1], [1, 0]),
    ] {
        let y = [n[0] * c[0] + n[1] * c[1], 0];
        let x = points(s, &x);
        let c = points(s, &c);
        let y = points(s, &y);
        body.advance_bilinear_contact(current(&x), current(&c), Some(current(&y)))
            .unwrap();
    }
    body
}

/// Host/device parity (condition-contact kernel): the device contact is the exact projection onto
/// c₁ + c₂ = 2 and satisfies the lossless two-port balance ‖h‖² + ‖n_in‖² = ‖h′‖² + ‖n_ret‖².
#[test]
#[ignore = "requires CUDA; oblique contact preserves free current, phase and exact two-port balance"]
fn oblique_family_preserves_tangent_and_returns_normal_current() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = plane(&s, [1, 1]);
    let z = points(&s, &[0, 0]);
    let y = points(&s, &[2, 0]);
    let h = points(&s, &[7, 4]);
    let f = body
        .read_condition_preimage(current(&z), current(&y))
        .unwrap();
    let mut held = body.retain_condition_current(current(&h), METRIC).unwrap();
    let before = body.census();
    let contact = held.contact(&f).unwrap();
    let carried = body
        .advance_bilinear_contact(current(&z), held.current(), None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(body.census().ingress_octets - before.ingress_octets, 4);
    assert_eq!(
        carried.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::Unique {
            current: rats(&[2, 0], 1)
        }
    );
    let read = contact.inspect().unwrap();
    assert_eq!(read.successor, rats(&[5, -1], 2));
    assert_eq!(read.incoming_normal, rats(&[1, 1], 1));
    assert_eq!(read.returned_normal, rats(&[11, 11], 2));
    assert_eq!(read.difference, rats(&[-9, -9], 2));
    check_balance(&read);
    let again = held.contact(&f).unwrap();
    assert_eq!(again.inspect().unwrap().difference, vec![Rat::zero(); 2]);
    assert_eq!(contact.inspect().unwrap(), read);
    assert_eq!(held.contacts(), 2);
    assert!(
        matches!(f.inspect().unwrap(),ConditionPreimageReading::Compatible{directions,..} if directions.len()==1)
    );
}
