use super::super::comparison_tests::{current, point};
use super::*;
use crate::{
    embedding_fiber::ResidentReadout, native_ecology::constitutive_fibre::ResidentConstitutiveFibre,
};

// Exact exterior operator specimens for testing this native algebraic pullback only.
fn law<'c>(s: &'c ResidentSurface<'c>, cancel: bool) -> ResidentConstitutiveFibre<'c> {
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(s, 3, 1, 1).unwrap();
    let mut sources = vec![[0i64; 6]];
    for j in 0..6 {
        let mut a = [0; 6];
        a[j] = 1;
        sources.push(a);
    }
    for a in sources {
        for h in [[0, 0], [1, 0], [0, 1]] {
            let eta = if cancel {
                [-a[2], -a[3]]
            } else {
                [a[0] * h[0] - a[1] * h[1], a[0] * h[1] + a[1] * h[0]]
            };
            let x = point(s, &a);
            let hs = point(s, &h);
            let y = point(s, &eta);
            law.advance_bilinear_contact(current(&x), current(&hs), Some(current(&y)))
                .unwrap();
        }
    }
    law
}
fn body<'c>(s: &'c ResidentSurface<'c>) -> ResidentNormalWave<'c> {
    let m = ResidentNormalMaterial::found(s, 1, 1, ResidentGrain(32)).unwrap();
    let p = point(s, &[1, 0]);
    let c = point(s, &[2, 1]);
    m.into_applied_difference_wave(current(&p), current(&c))
        .unwrap()
}
fn rows(f: &NormalWaveFamily<'_>) -> (Vec<Rat>, Vec<Vec<Rat>>) {
    match f.affine_relation().inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Plural {
            particular,
            directions,
        } => (particular, directions),
        other => panic!("expected anchored family: {other:?}"),
    }
}
#[test]
#[ignore = "requires CUDA; exact conditional graphs transport the correlated joint and fixed condition"]
fn anchored_family_composes_two_conditional_passages_without_point_conversion() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let body = body(&s);
    let law = law(&s, false);
    let h = point(&s, &[1, 0]);
    let before = body.rest().unwrap();
    let reads = s.census().section_read_outs;
    let first = body.read_family().unwrap();
    let relation = Rc::new(law.read_wave_relation(current(&h), 1).unwrap());
    let second = first.read_through(Rc::clone(&relation)).unwrap();
    let third = second.read_through(relation).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(third.passages(), 2);
    assert_eq!(body.rest().unwrap(), before);
    for (f, pcoef, ccoef) in [(&second, 1i64, 2i64), (&third, 2, 3)] {
        let (origin, dirs) = rows(f);
        assert_eq!(origin[0], Rat::one());
        assert_eq!(dirs.len(), 4);
        for v in std::iter::once(&origin).chain(dirs.iter()) {
            for j in 0..2 {
                assert_eq!(
                    v[8 + j],
                    Rat::from_integer(ccoef.into()) * &v[4 + j]
                        - Rat::from_integer(pcoef.into()) * &v[2 + j]
                );
            }
        }
    }
    assert_eq!(
        first.anchor().inspect().unwrap(),
        third.anchor().inspect().unwrap()
    );
}
#[test]
#[ignore = "requires CUDA; vertical output directions continue and a later relation can annihilate their current image"]
fn anchored_free_response_continues_into_a_fixed_future_receiver() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let body = body(&s);
    let mut free = law(&s, false);
    let zero = point(&s, &[0, 0, 0, 0, 0, 0]);
    let h0 = point(&s, &[0, 0]);
    for y in [[1, 0], [0, 1]] {
        let y = point(&s, &y);
        free.advance_bilinear_contact(current(&zero), current(&h0), Some(current(&y)))
            .unwrap();
    }
    let cancel = law(&s, true);
    let h = point(&s, &[1, 0]);
    let start = body.read_family().unwrap();
    let plural = start
        .read_through(Rc::new(free.read_wave_relation(current(&h), 1).unwrap()))
        .unwrap();
    let (_, dirs) = rows(&plural);
    assert!(
        dirs.iter()
            .any(|v| v[2..6].iter().all(|x| *x == Rat::zero())
                && v[8..10].iter().any(|x| *x != Rat::zero()))
    );
    let later = plural
        .read_through(Rc::new(cancel.read_wave_relation(current(&h), 1).unwrap()))
        .unwrap();
    let (origin, dirs) = rows(&later);
    for v in std::iter::once(&origin).chain(dirs.iter()) {
        assert!(v[8..10].iter().all(|x| *x == Rat::zero()));
    }
    assert!(
        dirs.iter()
            .any(|v| v[6..8].iter().any(|x| *x != Rat::zero()))
    );
}

#[test]
#[ignore = "requires CUDA; complex condition phase changes the whole joint map and an absent domain remains explicit"]
fn anchored_condition_phase_and_missing_contact_domain_are_distinct() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let body = body(&s);
    let learned = law(&s, false);
    let h = point(&s, &[0, 1]);
    let initial = body.read_family().unwrap();
    let relation = Rc::new(learned.read_wave_relation(current(&h), 1).unwrap());
    let seen = initial.read_through(relation).unwrap();
    let (origin, dirs) = rows(&seen);
    for v in std::iter::once(&origin).chain(dirs.iter()) {
        assert_eq!(v[8], &v[4] - &v[5] + &v[3]);
        assert_eq!(v[9], &v[5] + &v[4] - &v[2]);
    }
    let absent = ResidentConstitutiveFibre::found_bilinear_contact(&s, 3, 1, 1).unwrap();
    let outside = initial
        .read_through(Rc::new(absent.read_wave_relation(current(&h), 1).unwrap()))
        .unwrap();
    assert!(matches!(
        outside
            .affine_relation()
            .inspect()
            .unwrap()
            .predecessor_reading,
        ConstitutiveReading::OutsideDomain { .. }
    ));
    assert_eq!(
        outside.anchor().inspect().unwrap(),
        initial.anchor().inspect().unwrap()
    );
}
