use super::super::contact_tests::{calibrate, current, points, world};
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
fn check_balance(r: &ConditionContactReading) {
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

#[test]
#[ignore = "requires CUDA; a phase rotation carries the current and affine constraints together"]
fn quarter_turn_commutes_with_the_declared_metric_contact() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let body = plane(&s, [-1, 1]);
    let z = points(&s, &[0, 0]);
    let y = points(&s, &[2, 0]);
    let h = points(&s, &[-4, 7]);
    let f = body
        .read_condition_preimage(current(&z), current(&y))
        .unwrap();
    let mut held = body.retain_condition_current(current(&h), METRIC).unwrap();
    let read = held.contact(&f).unwrap().inspect().unwrap();
    assert_eq!(read.successor, rats(&[1, 5], 2));
    assert_eq!(read.incoming_normal, rats(&[-1, 1], 1));
    assert_eq!(read.returned_normal, rats(&[-11, 11], 2));
    check_balance(&read);
}

#[test]
#[ignore = "requires CUDA; free evidence permits generation and empty evidence preserves actual standing"]
fn free_and_empty_families_do_not_gate_actual_generation() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 1, 1).unwrap();
    calibrate(&s, &mut body, &mut world(&s), None);
    let z = points(&s, &[0, 0]);
    let one = points(&s, &[1, 0]);
    let h = points(&s, &[3, 4, 5]);
    let mut held = body
        .retain_condition_current(ResidentConstitutiveCurrent::rational(&h).unwrap(), METRIC)
        .unwrap();
    let free = body
        .read_condition_preimage(current(&z), current(&z))
        .unwrap();
    let empty = body
        .read_condition_preimage(current(&z), current(&one))
        .unwrap();
    let before = body.census();
    let a = held.contact(&free).unwrap();
    let b = held.contact(&empty).unwrap();
    let generated = body
        .advance_bilinear_contact(current(&one), held.current(), None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(
        generated.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::Unique {
            current: rats(&[3, 4], 5)
        }
    );
    for c in [&a, &b] {
        let read = c.inspect().unwrap();
        assert_eq!(read.successor, rats(&[3, 4], 5));
        assert_eq!(read.difference, vec![Rat::zero(); 2]);
        check_balance(&read);
    }
    assert_eq!(
        a.inspect().unwrap().status,
        ConditionContactStatus::Compatible
    );
    assert_eq!(
        b.inspect().unwrap().status,
        ConditionContactStatus::OutsideRepresentedRelation
    );
    assert!(matches!(
        b.family().inspect().unwrap(),
        ConditionPreimageReading::OutsideRepresentedRelation { .. }
    ));
    // Actual later evidence changes the retained current; old evidence stays free/empty.
    let target = points(&s, &[-5, 12, 13]);
    let fixed = body
        .read_condition_preimage(
            current(&one),
            ResidentConstitutiveCurrent::rational(&target).unwrap(),
        )
        .unwrap();
    let read = held.contact(&fixed).unwrap().inspect().unwrap();
    assert_eq!(read.successor, rats(&[-5, 12], 13));
    check_balance(&read);
    assert_eq!(a.inspect().unwrap().successor, rats(&[3, 4], 5));
}

#[test]
#[ignore = "requires CUDA; late arithmetic refusal and foreign charts preserve the continuing current"]
fn refused_contact_preserves_the_move_owned_successor() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let other = ResidentSurface::on(&r).unwrap();
    let mut body = plane(&s, [1, 1]);
    let z = points(&s, &[0, 0]);
    let y = points(&s, &[i64::MAX, 0]);
    let h = points(&s, &[-i64::MAX, -i64::MAX]);
    let f = body
        .read_condition_preimage(current(&z), current(&y))
        .unwrap();
    let mut held = body.retain_condition_current(current(&h), METRIC).unwrap();
    // All supplied words fit; the full returned difference does not fit its common wire.
    assert!(held.contact(&f).is_err());
    assert_eq!(held.contacts(), 0);
    let small = points(&s, &[0, 0]);
    let f = body
        .read_condition_preimage(current(&z), current(&small))
        .unwrap();
    let read = held.contact(&f).unwrap().inspect().unwrap();
    assert_eq!(read.predecessor, rats(&[-i64::MAX, -i64::MAX], 1));
    assert_eq!(read.successor, rats(&[0, 0], 1));
    check_balance(&read);
    let bad = points(&s, &[0, 0, 0]);
    assert!(
        body.retain_condition_current(ResidentConstitutiveCurrent::rational(&bad).unwrap(), METRIC)
            .is_err()
    );
    let other_body = plane(&other, [1, 1]);
    let oz = points(&other, &[0, 0]);
    let foreign = other_body
        .read_condition_preimage(current(&oz), current(&oz))
        .unwrap();
    assert!(held.contact(&foreign).is_err());
    assert_eq!(held.contacts(), 1);
    let generated = body
        .advance_bilinear_contact(current(&z), held.current(), None)
        .unwrap();
    assert_eq!(
        generated.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::Unique {
            current: rats(&[0, 0], 1)
        }
    );
}

#[test]
#[ignore = "requires CUDA; two coherent condition ports retain their relative current"]
fn multiport_condition_contact_preserves_relative_phase_current() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let mut body = ResidentConstitutiveFibre::found_bilinear_contact(&s, 1, 2, 1).unwrap();
    let mut rows = Vec::new();
    for coordinate in 0..4 {
        let mut c = [0; 4];
        c[coordinate] = 1;
        rows.push(([0, 0], c));
    }
    for x in [[1, 0], [0, 1]] {
        rows.push((x, [0; 4]));
        for coordinate in [0, 2] {
            let mut c = [0; 4];
            c[coordinate] = 1;
            rows.push((x, c));
        }
    }
    for (x, c) in rows {
        let y = points(&s, &[c[0] + c[2], c[1] + c[3]]);
        let x = points(&s, &x);
        let c = points(&s, &c);
        body.advance_bilinear_contact(current(&x), current(&c), Some(current(&y)))
            .unwrap();
    }
    let z = points(&s, &[0, 0]);
    let y = points(&s, &[2, -3]);
    let h = points(&s, &[7, 4, -1, 8]);
    let f = body
        .read_condition_preimage(current(&z), current(&y))
        .unwrap();
    let mut held = body.retain_condition_current(current(&h), METRIC).unwrap();
    let before = body.census();
    let receipt = held.contact(&f).unwrap();
    let next = body
        .advance_bilinear_contact(current(&z), held.current(), None)
        .unwrap();
    assert_eq!(body.census().section_read_outs, before.section_read_outs);
    assert_eq!(
        next.inspect().unwrap().predecessor_reading,
        ConstitutiveReading::Unique {
            current: rats(&[2, -3], 1)
        }
    );
    let read = receipt.inspect().unwrap();
    assert_eq!(read.successor, rats(&[10, -7, -6, 1], 2));
    assert_eq!(
        &read.successor[0] - &read.successor[2],
        Rat::from_integer(8.into())
    );
    assert_eq!(
        &read.successor[1] - &read.successor[3],
        Rat::from_integer((-4).into())
    );
    check_balance(&read);
}

#[test]
#[ignore = "requires CUDA; changing an affine origin or basis scale cannot change native contact"]
fn affine_origin_and_direction_scale_are_not_selected_as_actual_cause() {
    let r = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&r).unwrap();
    let body = plane(&s, [1, 1]);
    let z = points(&s, &[0, 0]);
    let y = points(&s, &[2, 0]);
    let h = points(&s, &[7, 4]);
    let mut f = body
        .read_condition_preimage(current(&z), current(&y))
        .unwrap();
    let expected = {
        let mut held = body.retain_condition_current(current(&h), METRIC).unwrap();
        held.contact(&f).unwrap().inspect().unwrap()
    };
    // Cold test-only change of coordinates of the SAME affine set. Original graph/RHS remain
    // valid. No production API accepts this host rewrite as evidence or a learned condition.
    let inner = Rc::get_mut(&mut f.inner).unwrap();
    let p = inner.returned.source_width;
    let c = inner.returned.target_width;
    let mut rest = s.detach_section(&inner.returned.report, 64).unwrap();
    let den = rest.intervals[p + c].0;
    let direction = rest.intervals[p + c + 4..]
        .chunks_exact(c)
        .find(|v| v.iter().any(|(n, _)| *n != 0))
        .unwrap()
        .to_vec();
    for j in 0..c {
        let v = rest.intervals[p + j].0 + 7 * den * direction[j].0;
        rest.intervals[p + j] = (v, v);
    }
    for pair in &mut rest.intervals[p + c + 4..] {
        pair.0 *= -3;
        pair.1 = pair.0;
    }
    inner.returned.report = s.mount_section_rest(&rest).unwrap();
    let mut held = body.retain_condition_current(current(&h), METRIC).unwrap();
    assert_eq!(held.contact(&f).unwrap().inspect().unwrap(), expected);
}
