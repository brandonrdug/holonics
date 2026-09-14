use super::*;
use crate::embedding_fiber::ResidentReadout;

fn point<'c>(s: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            values.len(),
            ResidentGrain(0),
            64,
            values.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn ball<'c>(s: &'c ResidentSurface<'c>, values: &[i128]) -> ResidentSection<'c> {
    let words = values
        .iter()
        .flat_map(|v| [*v as i64, (*v >> 64) as i64])
        .map(|v| (v, v))
        .collect();
    s.mount_section_rest(
        &ResidentSectionRest::found(1, values.len() * 2, ResidentGrain(0), 64, words).unwrap(),
    )
    .unwrap()
}
fn view<'a, 'c>(
    s: &'c ResidentSurface<'c>,
    section: &'a ResidentSection<'c>,
    width: usize,
    grain: u32,
) -> ResidentNormalEnclosureView<'a, 'c> {
    ResidentNormalEnclosureView {
        surface: s,
        section,
        offset: 0,
        width,
        grain: ResidentGrain(grain),
    }
}

#[test]
#[ignore = "requires CUDA; wide target coordinates and radius enter the exact moment-error convention without readout"]
fn enclosed_target_radius_survives_and_changes_target_error_without_receive_readout() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let scale = 1i128 << 72;
    let x = point(&s, &[1, 0, 0, 0, 0, 0]);
    let y = ball(&s, &[2 * scale, -scale, scale / 4]);
    let mut m = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(72)).unwrap();
    let reads = s.census().section_read_outs;
    let returned = m
        .receive(
            ResidentConstitutiveCurrent::integers(&x).unwrap(),
            view(&s, &y, 2, 72),
        )
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let r = returned.inspect_after().unwrap().unwrap();
    let q = |n: i64, d: i64| Rat::new(n.into(), d.into());
    assert_eq!(
        r.observed.center,
        vec![ExactComplexWaveCurrent::new(q(2, 1), q(-1, 1))]
    );
    assert_eq!(r.observed.radius, q(1, 4));
    let square = BigInt::from(5) * BigInt::from(scale).pow(2);
    let mut upper = square.sqrt();
    if &upper * &upper < square {
        upper += 1;
    }
    let e = BigInt::from(scale / 4);
    let expected = (2 * upper + &e) * &e;
    assert_eq!(
        r.increments,
        [
            q(0, 1),
            q(1, 4),
            q(5, 1),
            Rat::new(expected, BigInt::from(scale).pow(2))
        ]
    );
}

#[test]
#[ignore = "requires CUDA; zero-radius enclosed observation agrees with the established point path"]
fn zero_radius_enclosed_target_agrees_with_point_target() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let x = point(&s, &[1, 0, 0, 0, 0, 0]);
    let y = point(&s, &[2, -1]);
    let packed = ball(&s, &[2i128 << 72, -(1i128 << 72), 0]);
    let mut a = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(72)).unwrap();
    let mut b = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(72)).unwrap();
    let p = a
        .receive(
            ResidentConstitutiveCurrent::integers(&x).unwrap(),
            ResidentConstitutiveCurrent::integers(&y).unwrap(),
        )
        .unwrap()
        .inspect_after()
        .unwrap()
        .unwrap();
    let e = b
        .receive(
            ResidentConstitutiveCurrent::integers(&x).unwrap(),
            view(&s, &packed, 2, 72),
        )
        .unwrap()
        .inspect_after()
        .unwrap()
        .unwrap();
    assert_eq!(p.observed, e.observed);
    assert_eq!(p.increments, e.increments);
    assert_eq!(a.rest().unwrap(), b.rest().unwrap());
}

#[test]
#[ignore = "requires CUDA; paired and difference receivers retain bounds and exact self-cancellation"]
fn joined_source_keeps_bound_and_same_source_cancellation() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let a = ball(&s, &[512, -256, 32]);
    let b = ball(&s, &[256, 768, 64]);
    let av = view(&s, &a, 2, 8);
    let bv = view(&s, &b, 2, 8);
    let reads = s.census().section_read_outs;
    let joint = av.join(bv).unwrap();
    let delta = bv.difference(av).unwrap();
    let zero = av.difference(av).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let q = |n: i64, d: i64| Rat::new(n.into(), d.into());
    assert_eq!(joint.inspect().unwrap().radius, q(3, 8));
    assert_eq!(
        delta.inspect().unwrap().center,
        vec![ExactComplexWaveCurrent::new(q(-1, 1), q(4, 1))]
    );
    assert_eq!(delta.inspect().unwrap().radius, q(3, 8));
    assert_eq!(zero.inspect().unwrap().radius, q(0, 1));
    assert_eq!(
        zero.inspect().unwrap().center,
        vec![ExactComplexWaveCurrent::zero()]
    );
}
