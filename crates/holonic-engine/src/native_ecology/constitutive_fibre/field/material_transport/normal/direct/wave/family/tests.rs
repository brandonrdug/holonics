use super::super::comparison_tests::{current, point};
use super::*;
use crate::{
    embedding_fiber::ResidentReadout, native_ecology::constitutive_fibre::ResidentConstitutiveFibre,
};

// Exact exterior operator specimens for testing this native algebraic pullback only.
pub(in super::super) fn law<'c>(s: &'c ResidentSurface<'c>, cancel: bool) -> ResidentConstitutiveFibre<'c> {
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
pub(in super::super) fn body<'c>(s: &'c ResidentSurface<'c>) -> ResidentNormalWave<'c> {
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

#[test]
#[ignore = "requires CUDA; a later source constraint retains joined pairs through a vertical relation"]
fn later_source_pullback_keeps_pairs_instead_of_reexpanding_their_marginal() {
    let ro=ResidentReadout::new().unwrap();
    let s=ResidentSurface::on(&ro).unwrap();
    let body=body(&s);
    let mut free=law(&s,false);
    let zero=point(&s,&[0,0,0,0,0,0]);
    let h0=point(&s,&[0,0]);
    for y in [[1,0],[0,1]] {
        let y=point(&s,&y);
        free.advance_bilinear_contact(current(&zero),current(&h0),Some(current(&y))).unwrap();
    }
    let h=point(&s,&[1,0]);
    let transport=free.read_wave_relation(current(&h),1).unwrap();
    let source=body.read_family().unwrap();
    // A second admitted relation provides the later source constraint c=0. Its original
    // anchor is the same object; the join is through actual transport, not matching counts.
    let cancel=law(&s,true);
    let target=source.read_through(Rc::new(cancel.read_wave_relation(current(&h),1).unwrap())).unwrap();
    let standing=free.rest().unwrap();
    let reads=s.census().section_read_outs;
    let joined=source.read_pullback(&transport,&target).unwrap();
    let reexpanded=transport.read_image(joined.supported_source().affine_relation()).unwrap();
    assert_eq!(s.census().section_read_outs,reads);
    assert!(std::ptr::eq(joined.source(),&source));
    assert!(std::ptr::eq(joined.target(),&target));
    assert!(std::ptr::eq(joined.transport(),&transport));
    let ConstitutiveReading::Plural {particular,directions}=joined.joint().inspect().unwrap().predecessor_reading else {panic!("joined source family")};
    assert_eq!(directions.len(),4);
    for v in std::iter::once(&particular).chain(directions.iter()) {
        // Both full anchored wave states are present. The passed p is the earlier c;
        // the later c is constrained even though R itself has a free output there.
        assert_eq!(&v[2..6],&v[12..16]);
        assert_eq!(&v[4..6],&v[16..18]);
        assert!(v[18..20].iter().all(|x|*x==Rat::zero()));
    }
    let ConstitutiveReading::Plural {directions,..}=reexpanded.output().inspect().unwrap().predecessor_reading else {panic!("reexpanded relation")};
    assert!(directions.iter().any(|v|v[8..10].iter().any(|x|*x!=Rat::zero())));
    assert_eq!(joined.supported_source().passages(),source.passages());
    assert_eq!(joined.supported_target().passages(),target.passages());
    assert_eq!(joined.supported_source().anchor().inspect().unwrap(),source.anchor().inspect().unwrap());
    joined.supported_source().read_receiver().unwrap().require_supported().unwrap();
    joined.supported_target().read_receiver().unwrap().require_supported().unwrap();
    assert_eq!(free.rest().unwrap(),standing);
}

#[test]
#[ignore = "requires CUDA; a missing transport leaves the complete joint residual and original families"]
fn later_source_pullback_retains_an_incompatible_relation() {
    let ro=ResidentReadout::new().unwrap();
    let s=ResidentSurface::on(&ro).unwrap();
    let body=body(&s);
    let source=body.read_family().unwrap();
    let learned=law(&s,false);
    let h=point(&s,&[1,0]);
    let target=source.read_through(Rc::new(learned.read_wave_relation(current(&h),1).unwrap())).unwrap();
    let absent=ResidentConstitutiveFibre::found_bilinear_contact(&s,3,1,1).unwrap();
    let map=absent.read_wave_relation(current(&h),1).unwrap();
    let reads=s.census().section_read_outs;
    let joined=map.read_pullback(source.affine_relation(),target.affine_relation()).unwrap();
    assert_eq!(s.census().section_read_outs,reads);
    assert!(matches!(joined.joint().inspect().unwrap().predecessor_reading,ConstitutiveReading::OutsideDomain {..}));
    assert!(matches!(joined.supported_source().inspect().unwrap().predecessor_reading,ConstitutiveReading::OutsideDomain {..}));
    assert!(matches!(joined.supported_target().inspect().unwrap().predecessor_reading,ConstitutiveReading::OutsideDomain {..}));
}

#[test]
#[ignore = "requires CUDA; affine join feasibility cannot replace the original bounded source"]
fn later_source_pullback_keeps_original_bound_and_frame() {
    let ro=ResidentReadout::new().unwrap();
    let s=ResidentSurface::on(&ro).unwrap();
    let body=body(&s);
    let source=body.read_family().unwrap();
    let h=point(&s,&[1,0]);
    let learned=law(&s,false);
    let cancel=law(&s,true);
    let transport=learned.read_wave_relation(current(&h),1).unwrap();
    let cancel_map=Rc::new(cancel.read_wave_relation(current(&h),1).unwrap());
    let target=source.read_through(Rc::clone(&cancel_map)).unwrap();
    // c_next=2c-p intersects c_next=0 as an affine carrier, but the actual zero-radius
    // anchor (p,c)=(1,2+i) is outside that intersection.
    let joined=source.read_pullback(&transport,&target).unwrap();
    assert!(matches!(joined.joint().inspect().unwrap().predecessor_reading,ConstitutiveReading::Plural {..}));
    assert!(joined.supported_source().read_receiver().unwrap().require_supported().is_err());
    assert!(joined.supported_target().read_receiver().unwrap().require_supported().is_err());
    assert_eq!(joined.supported_source().anchor().inspect().unwrap(),source.anchor().inspect().unwrap());
    let foreign=body.read_family().unwrap().read_through(cancel_map).unwrap();
    assert!(source.read_pullback(&transport,&foreign).is_err());
}
