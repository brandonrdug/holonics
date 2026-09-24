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

/// Parity law (normal family receiver kernel): the device anchor and joint projections of a
/// declared exact affine family equal the exact rational projections computed by hand.
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
