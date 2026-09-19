use super::*;
use crate::{
    embedding_fiber::ResidentReadout, native_ecology::constitutive_fibre::ConstitutiveReturnRest,
};

// Explicit exact constrained-family specimens, independent of the receiver algorithm.
fn specimen<'c>(
    s: &'c ResidentSurface<'c>,
    m: [i64; 4],
    radius: i64,
    grain: u32,
    origin: [i64; 10],
    directions: Vec<[i64; 10]>,
    empty: bool,
) -> NormalWaveFamily<'c> {
    let material = ResidentNormalMaterial::found(s, 1, 1, ResidentGrain(grain)).unwrap();
    let words: Vec<_> = m
        .into_iter()
        .chain([radius])
        .flat_map(|v| {
            let v = (v as i128) * (1i128 << grain);
            [v as i64, (v >> 64) as i64]
        })
        .map(|v| (v, v))
        .collect();
    let joint = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap();
    let body = material.into_joint_wave(Rc::new(joint), 0).unwrap();
    let mut family = body.read_family().unwrap();
    let t = 10;
    let w = t + 1;
    let mut words = vec![0i64; w + 4 + t * t];
    words[1..w].copy_from_slice(&origin);
    // The homogeneous lambda numerator carries the common affine denominator.
    words[w] = if origin[0] > 0 { origin[0] } else { 1 };
    words[w + 1] = if empty {
        1
    } else if directions.is_empty() {
        0
    } else {
        2
    };
    words[w + 2] = -1;
    words[w + 3] = directions.len() as i64;
    for (i, row) in directions.iter().enumerate() {
        words[w + 4 + i * t..w + 4 + (i + 1) * t].copy_from_slice(row);
    }
    let rest:ConstitutiveReturnRest=serde_json::from_value(serde_json::json!({
        "schema":"holonics.constitutive-return.v1","source_width":1,"target_width":t,
        "occurrence":0,"source_occurrence":null,"source_chart":ConstitutiveSourceChart::Linear,"words":words
    })).unwrap();
    family.relation = rest.remount(s).unwrap();
    family
}
fn rat(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn hyperplane<'c>(s: &'c ResidentSurface<'c>, x: i64, grain: u32) -> NormalWaveFamily<'c> {
    let mut origin = [0; 10];
    origin[0] = 1;
    origin[2] = x;
    origin[8] = 5;
    let mut dirs = Vec::new();
    for j in [3, 4, 5, 9] {
        let mut d = [0; 10];
        d[j] = 1;
        dirs.push(d);
    }
    specimen(s, [0, 0, 0, 0], 1, grain, origin, dirs, false)
}

#[test]
#[ignore = "requires CUDA; a learned word shares the same bounded source across all future frames"]
fn prospective_word_keeps_learned_phase_and_does_not_advance_the_body() {
    use super::super::super::comparison_tests::{current, point};
    use super::super::tests::{body, law};
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let body = body(&s);
    let member = law(&s, false);
    let h = point(&s, &[1, 0]);
    let map = Rc::new(member.read_wave_relation(current(&h), 1).unwrap());
    let source = body.read_family().unwrap();
    let before = body.rest().unwrap();
    let reads = s.census().section_read_outs;
    let predicted = source
        .read_prospective(vec![Rc::clone(&map), Rc::clone(&map), map])
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let reading = predicted.inspect().unwrap();
    assert_eq!(reading.support, NormalFamilySupport::Supported);
    assert_eq!((reading.state_width, reading.state_count), (10, 4));
    for (index, values) in [[1, 0, 2, 1], [2, 1, 3, 2], [3, 2, 4, 3], [4, 3, 5, 4]]
        .iter()
        .enumerate()
    {
        assert_eq!(
            reading.projected_state(index).unwrap(),
            values.map(|n| rat(n, 1))
        );
    }
    assert!(reading.projected_state(4).is_none());
    assert_eq!(
        predicted.image().unwrap().inspect().unwrap().coverage,
        crate::native_ecology::constitutive_fibre::ConditionCoverage::Complete
    );
    assert_eq!(body.rest().unwrap(), before);
    assert_eq!(
        predicted.source().anchor().inspect().unwrap(),
        source.anchor().inspect().unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; genuine vertical freedom is retained but intermediate future variables are shared"]
fn prospective_word_keeps_vertical_modes_without_independent_future_marginals() {
    use super::super::super::comparison_tests::{current, point};
    use super::super::tests::{body, law};
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let body = body(&s);
    let mut free = law(&s, false);
    free.advance_bilinear_contact(
        current(&point(&s, &[0; 6])),
        current(&point(&s, &[0; 2])),
        Some(current(&point(&s, &[1, 0]))),
    )
    .unwrap();
    let cancel = law(&s, true);
    let h = point(&s, &[1, 0]);
    let first = Rc::new(free.read_wave_relation(current(&h), 1).unwrap());
    let second = Rc::new(cancel.read_wave_relation(current(&h), 1).unwrap());
    let source = body.read_family().unwrap();
    let predicted = source.read_prospective(vec![first, second]).unwrap();
    let affine = predicted
        .inspect_affine_relation()
        .unwrap();
    let ConstitutiveReading::Plural {
        particular,
        directions,
    } = affine
    else {
        panic!("full affine joint must retain its source and vertical modes")
    };
    // Frame1.c and frame2.p are the SAME variable. Frame2.c is zero after cancellation.
    for v in std::iter::once(&particular).chain(directions.iter()) {
        assert_eq!(&v[18..20], &v[26..28]);
        assert!(v[28..30].iter().all(|x| *x == Rat::zero()));
    }
    assert!(directions
        .iter()
        .any(|v| v[..10].iter().all(|x| *x == Rat::zero()) && v[18] != Rat::zero()));
    let reading = predicted.inspect().unwrap();
    assert_eq!(reading.support, NormalFamilySupport::Supported);
    assert_eq!(
        &reading.projected_state(1).unwrap()[2..],
        &reading.projected_state(2).unwrap()[..2]
    );
}

#[test]
#[ignore = "requires CUDA; a point word can outgrow generic projection scratch without selecting a source representative"]
fn point_word_retains_a_long_joint_beyond_projection_scratch() {
    use super::super::super::comparison_tests::{current, point};
    use super::super::tests::law;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let member = law(&s, false);
    let h = point(&s, &[1, 0]);
    let map = Rc::new(member.read_wave_relation(current(&h), 1).unwrap());
    let origin = [1, 0, 1, 0, 2, 1, 1, 0, 2, 1];
    let source = specimen(&s, [1, 0, 2, 1], 0, 8, origin, vec![], false);
    let before = source.affine_relation().inspect().unwrap();
    let steps = s.declaration().max_sectiond_bytes as usize / 960 + 1;
    assert!(source.check_prospective_extent(steps).is_err());
    let reads = s.census().section_read_outs;
    let future = source.read_prospective(vec![Rc::clone(&map); steps]).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(future.point_word().unwrap().len(), steps);
    assert!(future.affine_relation().is_none());
    let reading = future.inspect().unwrap();
    assert_eq!(reading.state_count, steps + 1);
    for k in 0..=steps {
        let k = k as i64;
        assert_eq!(reading.projected_state(k as usize).unwrap(),
            [rat(1+k,1),rat(k,1),rat(2+k,1),rat(1+k,1)]);
    }
    assert_eq!(source.affine_relation().inspect().unwrap(), before);

    // The same resource change does not authorize evaluating an unresolved source at its centre.
    // `hyperplane` keeps a direction above the anchor block, so one output coordinate is still
    // free at a fixed anchor and the factored word refuses it rather than reading a point of it
    // (`the_word_refuses_a_genuine_vertical_fibre_rather_than_standing_in`).
    let plural = hyperplane(&s, 0, 8);
    assert!(plural.read_prospective(vec![map; steps]).is_err());
}

#[test]
#[ignore = "requires CUDA; the prospective affine graph never replaces the original anchor-ball constraint"]
fn prospective_word_keeps_anchor_miss_and_empty_family_distinct() {
    use super::super::super::comparison_tests::{current, point};
    use super::super::tests::law;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let member = law(&s, false);
    let h = point(&s, &[1, 0]);
    let map = Rc::new(member.read_wave_relation(current(&h), 1).unwrap());
    let miss = hyperplane(&s, 2, 32);
    let result = miss
        .read_prospective(vec![Rc::clone(&map), Rc::clone(&map)])
        .unwrap();
    let reading = result.inspect().unwrap();
    assert_eq!(reading.support, NormalFamilySupport::OutsideAnchorBall);
    assert!(reading.projected_joint.is_none());
    let empty = specimen(&s, [0; 4], 1, 32, [0; 10], vec![], true);
    let reading = empty
        .read_prospective(vec![Rc::clone(&map), map])
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(reading.support, NormalFamilySupport::EmptyAffineRelation);
    assert!(reading.nearest_anchor.is_none());
}
#[test]
#[ignore = "requires CUDA; exact ball tangency is supported while an affine miss returns its oriented witness"]
fn bounded_receiver_distinguishes_tangent_miss_and_empty_affine() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let tangent = hyperplane(&s, 1, 96);
    let reads = s.census().section_read_outs;
    let r = tangent.read_receiver().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let view = r.inspect().unwrap();
    assert_eq!(view.support, NormalFamilySupport::Supported);
    assert_eq!(
        view.nearest_anchor.unwrap(),
        vec![rat(1, 1), rat(0, 1), rat(0, 1), rat(0, 1)]
    );
    assert_eq!(
        view.projected_joint.unwrap(),
        vec![rat(0, 1), rat(0, 1), rat(5, 1), rat(0, 1)]
    );
    assert_eq!(
        view.anchor_independent_free,
        vec![false, false, false, true]
    );
    let miss = hyperplane(&s, 2, 96);
    let view = miss.read_receiver().unwrap().inspect().unwrap();
    assert_eq!(view.support, NormalFamilySupport::OutsideAnchorBall);
    assert!(view.projected_joint.is_none());
    assert_eq!(
        view.anchor_difference.unwrap(),
        vec![rat(2, 1), rat(0, 1), rat(0, 1), rat(0, 1)]
    );
    let empty = specimen(&s, [0; 4], 1, 32, [0; 10], vec![], true);
    let view = empty.read_receiver().unwrap().inspect().unwrap();
    assert_eq!(view.support, NormalFamilySupport::EmptyAffineRelation);
    assert!(view.nearest_anchor.is_none());
    assert!(view.projected_joint.is_none());
    assert!(empty
        .read_receiver()
        .unwrap()
        .inspect_vertical_directions()
        .unwrap()
        .intervals
        .iter()
        .all(|(lo, hi)| *lo == 0 && *hi == 0));
}
#[test]
#[ignore = "requires CUDA; nonorthogonal anchor and vertical joint projections use exact rational geometry"]
fn bounded_receiver_projects_both_nonorthogonal_spaces() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut origin = [0; 10];
    origin[0] = 1;
    origin[6] = 1;
    origin[8] = 3;
    let mut a = [0; 10];
    a[2] = 1;
    a[3] = 1;
    a[8] = 2;
    let mut v = [0; 10];
    v[6] = 1;
    v[7] = 1;
    let family = specimen(&s, [1, 0, 0, 0], 1, 64, origin, vec![a, v], false);
    let before = family.affine_relation().rest().unwrap();
    let reads = s.census().section_read_outs;
    let receiver = family.read_receiver().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let view = receiver.inspect().unwrap();
    assert_eq!(view.support, NormalFamilySupport::Supported);
    assert_eq!(
        view.nearest_anchor.unwrap(),
        vec![rat(1, 2), rat(1, 2), rat(0, 1), rat(0, 1)]
    );
    assert_eq!(
        view.anchor_difference.unwrap(),
        vec![rat(-1, 2), rat(1, 2), rat(0, 1), rat(0, 1)]
    );
    assert_eq!(
        view.projected_joint.unwrap(),
        vec![rat(1, 2), rat(-1, 2), rat(4, 1), rat(0, 1)]
    );
    assert_eq!(view.anchor_independent_free, vec![true, true, false, false]);
    assert_eq!(
        serde_json::to_value(family.affine_relation().rest().unwrap()).unwrap(),
        serde_json::to_value(before).unwrap()
    );
}
#[test]
#[ignore = "requires CUDA; a normal family receiver keeps the actual joint at its anchor without replacing its enclosure"]
fn initial_family_receiver_preserves_joint_and_radius() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut origin = [0; 10];
    origin[0] = 1;
    let mut dirs = Vec::new();
    for j in 0..4 {
        let mut d = [0; 10];
        d[2 + j] = 1;
        d[6 + j] = 1;
        dirs.push(d);
    }
    let family = specimen(&s, [1, 2, 3, 4], 2, 64, origin, dirs, false);
    let view = family.read_receiver().unwrap().inspect().unwrap();
    assert_eq!(view.support, NormalFamilySupport::Supported);
    assert_eq!(
        view.projected_joint.unwrap(),
        vec![rat(1, 1), rat(2, 1), rat(3, 1), rat(4, 1)]
    );
    assert_eq!(view.anchor_difference.unwrap(), vec![Rat::zero(); 4]);
    assert_eq!(family.anchor().inspect().unwrap().radius, rat(2, 1));
}

#[test]
#[ignore = "requires CUDA; passive unit-phase transport carries anchor, joint and the receiver metric together"]
fn family_receiver_is_covariant_under_a_unit_phase_rechart() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut origin = [0; 10];
    origin[0] = 1;
    origin[6] = 1;
    origin[8] = 3;
    let mut a = [0; 10];
    a[2] = 1;
    a[3] = 1;
    a[8] = 2;
    let mut v = [0; 10];
    v[6] = 1;
    v[7] = 1;
    let rotate = |mut row: [i64; 10]| {
        for j in (2..10).step_by(2) {
            let re = row[j];
            row[j] = -row[j + 1];
            row[j + 1] = re;
        }
        row
    };
    let left = specimen(&s, [1, 0, 0, 0], 1, 64, origin, vec![a, v], false);
    let right = specimen(
        &s,
        [0, 1, 0, 0],
        1,
        64,
        rotate(origin),
        vec![rotate(a), rotate(v)],
        false,
    );
    let l = left.read_receiver().unwrap().inspect().unwrap();
    let r = right.read_receiver().unwrap().inspect().unwrap();
    assert_eq!(l.support, r.support);
    let rotate_rational = |v: Vec<Rat>| {
        v.chunks_exact(2)
            .flat_map(|p| [-p[1].clone(), p[0].clone()])
            .collect::<Vec<_>>()
    };
    assert_eq!(
        rotate_rational(l.nearest_anchor.unwrap()),
        r.nearest_anchor.unwrap()
    );
    assert_eq!(
        rotate_rational(l.projected_joint.unwrap()),
        r.projected_joint.unwrap()
    );
    assert_eq!(
        rotate_rational(l.anchor_difference.unwrap()),
        r.anchor_difference.unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; an optional source-image bound may refuse while the full anchored family continues"]
fn source_bound_refusal_does_not_block_the_anchored_family() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let material = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(64)).unwrap();
    let values = [0i128, 0, 0, 0, i128::MAX];
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
    let body = material.into_joint_wave(Rc::new(joint), 0).unwrap();
    assert!(body.read_source().is_err());
    let family = body.read_family().unwrap();
    let seen = family.read_receiver().unwrap().inspect().unwrap();
    assert_eq!(seen.support, NormalFamilySupport::Supported);
    assert_eq!(seen.projected_joint.unwrap(), vec![Rat::zero(); 4]);
    let mut wire = Vec::new();
    family.rest().unwrap().write(&mut wire).unwrap();
    let restored = NormalWaveFamilyRest::read(&mut wire.as_slice(), wire.len() as u64)
        .unwrap()
        .remount(&s)
        .unwrap();
    assert_eq!(
        restored.anchor().inspect().unwrap(),
        family.anchor().inspect().unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; bounded projected family enclosure returns an outer resident ball"]
fn enclosure_identity_retains_unit_anchor_radius_without_host_readout() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut origin = [0; 10]; origin[0] = 1;
    let directions = (0..4).map(|i| { let mut d=[0;10]; d[2+i]=1; d[6+i]=1; d }).collect();
    let family = specimen(&s, [0;4], 1, 72, origin, directions, false);
    let receiver = family.read_receiver().unwrap();
    let before = s.census().section_read_outs;
    let enclosure = receiver.enclosure(ResidentGrain(72)).unwrap();
    assert_eq!(s.census().section_read_outs, before);
    let reading = enclosure.inspect().unwrap();
    assert_eq!(reading.center, vec![ExactComplexWaveCurrent::zero(); 2]);
    assert_eq!(reading.radius, rat(1, 1));
}

#[test]
#[ignore = "requires CUDA; projected rank-one family carries an exact fractional radius"]
fn enclosure_scaled_rank_one_rounds_out_the_negative_fractional_image() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut d=[0;10]; d[2]=3; d[6]=-1;
    let mut origin=[0;10]; origin[0]=1;
    let family=specimen(&s,[0;4],1,72,origin,vec![d],false);
    let receiver=family.read_receiver().unwrap();
    let enclosure=receiver.enclosure(ResidentGrain(8)).unwrap();
    let radius=enclosure.inspect().unwrap().radius;
    assert!(radius >= rat(1,3));
    assert!(radius <= rat(1,3)+rat(1,256));
}

#[test]
#[ignore = "requires CUDA; unresolved vertical output directions refuse outer enclosure formation"]
fn enclosure_refuses_vertical_output_while_receiver_remains_supported() {
    let ro=ResidentReadout::new().unwrap(); let s=ResidentSurface::on(&ro).unwrap();
    let mut origin=[0;10]; origin[0]=1;
    let mut vertical=[0;10]; vertical[6]=1;
    let family=specimen(&s,[0;4],1,72,origin,vec![vertical],false);
    let receiver=family.read_receiver().unwrap();
    assert_eq!(receiver.inspect().unwrap().support, NormalFamilySupport::Supported);
    assert!(receiver.enclosure(ResidentGrain(72)).is_err());
}

#[test]
#[ignore = "requires CUDA; a source outside the retained anchor ball has no bounded enclosure"]
fn enclosure_refuses_an_affine_family_outside_its_anchor_ball() {
    let ro=ResidentReadout::new().unwrap(); let s=ResidentSurface::on(&ro).unwrap();
    let mut origin=[0;10]; origin[0]=1; origin[2]=2;
    let family=specimen(&s,[0;4],1,72,origin,vec![],false);
    let receiver=family.read_receiver().unwrap();
    assert_eq!(receiver.inspect().unwrap().support, NormalFamilySupport::OutsideAnchorBall);
    assert!(receiver.enclosure(ResidentGrain(72)).is_err());
}

#[test]
#[ignore = "requires CUDA; partial anchor projection retains the joint projected centre and bound"]
fn enclosure_partial_anchor_matches_projected_joint_centre() {
    let ro=ResidentReadout::new().unwrap(); let s=ResidentSurface::on(&ro).unwrap();
    let mut origin=[0;10]; origin[0]=1; origin[6]=1; origin[8]=3;
    let mut anchor=[0;10]; anchor[2]=1; anchor[3]=1; anchor[8]=2;
    let family=specimen(&s,[1,0,0,0],1,72,origin,vec![anchor],false);
    let receiver=family.read_receiver().unwrap();
    let expected=receiver.inspect().unwrap().projected_joint.unwrap();
    let enclosure=receiver.enclosure(ResidentGrain(72)).unwrap();
    let reading=enclosure.inspect().unwrap();
    let actual=reading.center.iter().flat_map(|z| [z.real.clone(),z.imaginary.clone()]).collect::<Vec<_>>();
    assert_eq!(actual,expected);
    assert_eq!(actual,vec![rat(1,1),rat(0,1),rat(4,1),rat(0,1)]);
    // AP_U maps (x,y,0,0) to (0,0,x+y,0): max row/column norm is 2.
    assert_eq!(reading.radius,rat(2,1));
}

#[test]
#[ignore = "requires CUDA; a non-dyadic projected centre remains covered after high-grain rounding"]
fn enclosure_non_dyadic_centre_keeps_positive_rounding_radius() {
    let ro=ResidentReadout::new().unwrap(); let s=ResidentSurface::on(&ro).unwrap();
    let mut origin=[0;10]; origin[0]=3; origin[6]=1;
    let family=specimen(&s,[0;4],0,72,origin,vec![],false);
    let receiver=family.read_receiver().unwrap();
    assert_eq!(receiver.inspect().unwrap().projected_joint.unwrap()[0],rat(1,3));
    for grain in [8,72] {
        let before=s.census().section_read_outs;
        let enclosure=receiver.enclosure(ResidentGrain(grain)).unwrap();
        assert_eq!(s.census().section_read_outs,before);
        let reading=enclosure.inspect().unwrap();
        let unit=Rat::new(1.into(),num_bigint::BigInt::from(1)<<grain);
        assert_eq!(reading.radius,unit);
        assert!(reading.center[0].real<=rat(1,3));
        assert!(reading.center[0].real.clone()+reading.radius>=rat(1,3));
    }
}

#[test]
#[ignore = "requires CUDA; generated point words retain the rounding error of their whole joint output"]
fn enclosure_point_word_keeps_non_dyadic_rounding() {
    use super::super::super::comparison_tests::{current,point};
    use super::super::tests::law;
    let ro=ResidentReadout::new().unwrap();let s=ResidentSurface::on(&ro).unwrap();
    let member=law(&s,false);let h=point(&s,&[1,0]);
    let map=Rc::new(member.read_wave_relation(current(&h),1).unwrap());
    let mut origin=[0;10];origin[0]=3;origin[6]=1;
    let family=specimen(&s,[0;4],0,72,origin,vec![],false);
    let receiver=family.read_point_word(vec![map]).unwrap();
    let exact=receiver.inspect().unwrap().projected_joint.unwrap();
    let before=s.census().section_read_outs;
    let enclosure=receiver.enclosure(ResidentGrain(8)).unwrap();
    assert_eq!(s.census().section_read_outs,before);
    let reading=enclosure.inspect().unwrap();
    assert!(reading.radius>Rat::zero());
    let mut error=Rat::zero();
    for (a,b) in reading.center.iter().flat_map(|z|[&z.real,&z.imaginary]).zip(exact) {
        let e=a-b;error+=if e<Rat::zero(){-e}else{e};
    }
    assert!(error<=reading.radius);
}

#[test]
#[ignore = "requires CUDA; the expanded composite and the retained word are two charts of one relation"]
fn rebase_and_expansion_read_the_same_future() {
    use super::super::super::comparison_tests::{current, point};
    use super::super::tests::law;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let member = law(&s, false);
    let h = point(&s, &[1, 0]);
    let map = Rc::new(member.read_wave_relation(current(&h), 1).unwrap());
    // A PLURAL family that is a graph over its anchor block: both retained directions carry a
    // pivot inside the anchor coordinates 2..6, so nothing is free once the anchor is fixed.
    let mut origin = [0; 10];
    origin[0] = 1;
    origin[2] = 1;
    origin[6] = 2;
    origin[8] = 1;
    let family = specimen(
        &s,
        [0, 0, 0, 0],
        4,
        8,
        origin,
        vec![
            [0, 0, 1, 0, 0, 0, 3, 1, 0, 2],
            [0, 0, 0, 1, 0, 0, 1, 0, 2, 1],
        ],
        false,
    );
    match family.affine_relation().inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Plural { ref directions, .. } => assert_eq!(directions.len(), 2),
        ref other => panic!("the specimen must be plural: {other:?}"),
    }
    let word = vec![Rc::clone(&map), Rc::clone(&map), map];
    // The expanded chart: one composite relation carried in the i64 affine wire.
    let expanded = family.read_prospective(word.clone()).unwrap();
    assert!(expanded.point_word().is_none() && expanded.affine_relation().is_some());
    // The factored chart: the same relation as its retained ordered word over this family's
    // own receiver point, transported in the wide carrier with no composite materialized.
    let factored = family.read_point_word(word).unwrap();
    assert!(factored.point_word().is_some() && factored.affine_relation().is_none());
    let (a, b) = (expanded.inspect().unwrap(), factored.inspect().unwrap());
    assert_eq!(a.support, NormalFamilySupport::Supported);
    assert!(a.anchor_independent_free.iter().all(|free| !free));
    // Every reading the receiver returns is identical: the rebase has no residual.
    assert_eq!(
        serde_json::to_value(&a).unwrap(),
        serde_json::to_value(&b).unwrap(),
        "the factored word and the expanded composite must read the same future"
    );
    assert_eq!((b.state_width, b.state_count), (10, 4));
    // Bounded step over step across a word of three factors: the octaves of a state never
    // exceed the previous state's plus the factor's own. An elimination that carried the
    // pivots it was reduced through would grow with the length of the word instead.
    let factor = match family.affine_relation().inspect().unwrap().predecessor_reading {
        ConstitutiveReading::Plural { ref directions, .. } => directions
            .iter()
            .flatten()
            .map(|v| v.numer().bits().max(v.denom().bits()))
            .max()
            .unwrap_or(0),
        ref other => panic!("the specimen must be plural: {other:?}"),
    };
    let octaves = |state: usize| {
        b.projected_state(state)
            .unwrap()
            .iter()
            .map(|v| v.numer().bits().max(v.denom().bits()))
            .max()
            .unwrap_or(0)
    };
    for state in 0..4 {
        assert_eq!(a.projected_state(state), b.projected_state(state));
        if state > 0 {
            assert!(
                octaves(state) <= octaves(state - 1) + factor,
                "factor {state} added more than its own octave: {} -> {} through {factor}",
                octaves(state - 1),
                octaves(state)
            );
        }
    }
    // The word's first state is this family's own receiver, not another point of it.
    let alone = family.read_receiver().unwrap().inspect().unwrap();
    assert_eq!(alone.nearest_anchor, b.nearest_anchor);
    assert_eq!(alone.projected_joint.unwrap(), b.projected_state(0).unwrap());
}

#[test]
#[ignore = "requires CUDA; a real vertical output fibre is not answered by a point of it"]
fn the_word_refuses_a_genuine_vertical_fibre_rather_than_standing_in() {
    use super::super::super::comparison_tests::{current, point};
    use super::super::tests::law;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let member = law(&s, false);
    let h = point(&s, &[1, 0]);
    let map = Rc::new(member.read_wave_relation(current(&h), 1).unwrap());
    // hyperplane retains a direction at coordinate 9, above the anchor block: the joint
    // minimum norm over (z0, L z0) is then NOT the image of this family's own receiver,
    // so the factored chart refuses and the expanded composite remains the only reading.
    let vertical = hyperplane(&s, 0, 8);
    assert!(vertical
        .read_receiver()
        .unwrap()
        .inspect()
        .unwrap()
        .anchor_independent_free
        .iter()
        .any(|free| *free));
    assert!(vertical.read_point_word(vec![Rc::clone(&map)]).is_err());
    // The expanded chart still answers it, so the refusal is the word's scope, not a loss.
    assert_eq!(
        vertical
            .read_prospective(vec![map])
            .unwrap()
            .inspect()
            .unwrap()
            .support,
        NormalFamilySupport::Supported
    );
}
