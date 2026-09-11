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
    words[w] = 1;
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
    assert!(
        empty
            .read_receiver()
            .unwrap()
            .inspect_vertical_directions()
            .unwrap()
            .intervals
            .iter()
            .all(|(lo, hi)| *lo == 0 && *hi == 0)
    );
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
