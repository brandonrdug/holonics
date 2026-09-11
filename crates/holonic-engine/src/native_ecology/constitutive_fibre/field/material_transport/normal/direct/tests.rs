use super::*;
use crate::embedding_fiber::ResidentReadout;

fn point<'c>(s: &'c ResidentSurface<'c>, v: &[i64]) -> ResidentSection<'c> {
    s.mount_section_rest(
        &ResidentSectionRest::found(
            1,
            v.len(),
            ResidentGrain(0),
            i64::BITS,
            v.iter().map(|v| (*v, *v)).collect(),
        )
        .unwrap(),
    )
    .unwrap()
}
fn current<'a, 'c>(s: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(s).unwrap()
}
fn q(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn wave(r: i64, i: i64, d: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(q(r, d), q(i, d))
}
fn contains(ball: &NativeFieldCurrentBall, expected: &[ExactComplexWaveCurrent]) {
    let error: Rat = ball
        .center
        .iter()
        .zip(expected)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(
        error <= &ball.radius * &ball.radius,
        "outside retained ball: {error} > radius² {}",
        &ball.radius * &ball.radius
    );
}

#[test]
#[ignore = "requires CUDA; actual differing observations retain fit discrepancy without growing source history"]
fn differing_returns_accumulate_geometry_and_keep_fit_distinct_from_solve_error() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let x = point(&s, &[1, 0, 0, 0, 0, 0]);
    let positive = point(&s, &[1, 0]);
    let negative = point(&s, &[-1, 0]);
    let shape = body.state_wire().unwrap().intervals.len();
    let reads = s.census().section_read_outs;
    let first = body.receive(current(&x), current(&positive)).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    contains(&first.inspect_before().unwrap().forward, &[wave(0, 0, 1)]);
    contains(
        &first.inspect_after().unwrap().unwrap().forward,
        &[wave(1, 0, 2)],
    );
    drop(first);
    body.receive(current(&x), current(&negative)).unwrap();
    let state = body.inspect().unwrap();
    assert_eq!(state.source_normal[0][0], wave(3, 0, 1));
    assert_eq!(state.cross_source[0][0], wave(0, 0, 1));
    assert_eq!(state.target_energy, q(2, 1));
    let objective = state.objective().unwrap();
    assert_eq!(objective.nominal_regularized_objective, q(1, 1));
    assert_eq!(objective.solve_gap_upper, q(0, 1));
    let before = body.state_wire().unwrap();
    let later = body.read(current(&x)).unwrap();
    contains(&later.inspect_before().unwrap().forward, &[wave(0, 0, 1)]);
    assert_eq!(body.state_wire().unwrap(), before);
    assert_eq!(shape, before.intervals.len());
    assert_eq!(body.observations(), 2);
}

#[test]
#[ignore = "requires CUDA; complex normal transport retains oriented cross-source phase and rational source family"]
fn complex_cross_geometry_and_nondyadic_source_keep_their_complete_bounds() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let imaginary = point(&s, &[0, 1, 0, 0, 0, 0]);
    let real = point(&s, &[1, 0]);
    body.receive(current(&imaginary), current(&real)).unwrap();
    assert_eq!(body.inspect().unwrap().cross_source[0][0], wave(0, -1, 1));
    let probe = point(&s, &[1, 0, 0, 0, 0, 0]);
    contains(
        &body
            .read(current(&probe))
            .unwrap()
            .inspect_before()
            .unwrap()
            .forward,
        &[wave(0, -1, 2)],
    );

    let mut rational = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let third = point(&s, &[1, 0, 0, 0, 0, 0, 3]);
    let two = point(&s, &[2, 0]);
    let returned = rational
        .receive(
            ResidentConstitutiveCurrent::rational(&third).unwrap(),
            current(&two),
        )
        .unwrap();
    contains(
        &returned.inspect_after().unwrap().unwrap().forward,
        &[wave(1, 0, 5)],
    );
    let state = rational.inspect().unwrap();
    assert!(state.source_normal_error > Rat::zero());
    let objective = state.objective().unwrap();
    assert!(objective.family_minimum.lower <= q(9, 5) && objective.family_minimum.upper >= q(9, 5));
}

#[test]
#[ignore = "requires CUDA; a failed direct return leaves all continuing moments and chronology unchanged"]
fn malformed_current_and_arithmetic_refusal_do_not_publish_partial_material() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let x = point(&s, &[1, 0, 0, 0, 0, 0]);
    let y = point(&s, &[1, 0]);
    body.receive(current(&x), current(&y)).unwrap();
    let before = body.state_wire().unwrap();
    let bad = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), i64::BITS, vec![(0, 1), (0, 0)])
                .unwrap(),
        )
        .unwrap();
    assert!(body.receive(current(&x), current(&bad)).is_err());
    assert_eq!(body.state_wire().unwrap(), before);
    assert_eq!(body.observations(), 1);
    let mut wide = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(120)).unwrap();
    let before_wide = wide.state_wire().unwrap();
    let large = point(&s, &[i64::MAX, 0, 0, 0, 0, 0]);
    assert!(wide.receive(current(&large), current(&y)).is_err());
    assert_eq!(wide.state_wire().unwrap(), before_wide);
    assert_eq!(wide.observations(), 0);
    body.receive(current(&x), current(&y)).unwrap();
    assert_eq!(body.observations(), 2);
}

#[test]
#[ignore = "requires CUDA; a learned resident generator supplies normal-source current without a numeric read or remount"]
fn a_learned_generator_enters_the_normal_response_on_device() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    // Calibrate the declared identity receiver on the three complex port axes. This source
    // chart is independent of a medium, and the relation is formed by the public native owner.
    let port_components = 2 * 3;
    let mut generator =
        ResidentConstitutiveFibre::found(&s, port_components, port_components).unwrap();
    for at in 0..port_components {
        let mut coordinates = vec![0; port_components];
        coordinates[at] = 1;
        let basis = point(&s, &coordinates);
        generator
            .advance_resident(current(&basis), Some(current(&basis)))
            .unwrap();
    }
    let x = point(&s, &[1, 0, 0, 1, -1, 0]);
    let y = point(&s, &[0, 1]);
    let mut normal = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let reads = s.census().section_read_outs;
    let source = generator.read_resident(current(&x)).unwrap();
    let returned = normal.receive(source.current(), current(&y)).unwrap();
    let subsequent = normal.read(source.current()).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    contains(
        &returned.inspect_after().unwrap().unwrap().forward,
        &[wave(0, 3, 4)],
    );
    contains(
        &subsequent.inspect_before().unwrap().forward,
        &[wave(0, 3, 4)],
    );
    assert_eq!(normal.observations(), 1);
}

#[test]
#[ignore = "requires CUDA; complete forward enclosures conduct repeatedly without a source-history chain or numeric readout"]
fn bounded_forward_current_continues_with_fixed_residency() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = ResidentNormalMaterial::found(&s, 1, 3, ResidentGrain(u32::BITS)).unwrap();
    for channel in 0..3 {
        let mut v = [0; 6];
        v[2 * channel] = 1;
        let x = point(&s, &v);
        body.receive(current(&x), current(&x)).unwrap();
    }
    let x = point(&s, &[1, 0, 0, 1, -1, 0]);
    let mut carried = body.read(current(&x)).unwrap().into_forward();
    drop(x);
    let before = s.census();
    let mut denominator = 2;
    for _ in 0..16 {
        let next = body.read(carried.view()).unwrap().into_forward();
        carried = next;
        denominator *= 2;
        assert_eq!(s.census().resident_octets_now, before.resident_octets_now);
    }
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    contains(
        &carried.inspect().unwrap(),
        &[
            wave(1, 0, denominator),
            wave(0, 1, denominator),
            wave(-1, 0, denominator),
        ],
    );
    assert_eq!(body.observations(), 3);
}

#[test]
#[ignore = "requires CUDA; receiving an enclosed source pays its whole uncertainty and an incompatible grain refuses before mutation"]
fn enclosed_source_uncertainty_enters_the_normal_geometry() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut producer = ResidentNormalMaterial::found(&s, 1, 3, ResidentGrain(u32::BITS)).unwrap();
    let x = point(&s, &[1, 0, 0, 0, 0, 0]);
    producer.receive(current(&x), current(&x)).unwrap();
    let incoming = producer.read(current(&x)).unwrap().into_forward();
    assert!(incoming.inspect().unwrap().radius > Rat::zero());
    let y = point(&s, &[1, 0]);
    let mut receiver = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let reads = s.census().section_read_outs;
    receiver.receive(incoming.view(), current(&y)).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(receiver.inspect().unwrap().source_normal_error > Rat::zero());
    let mut wrong = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS / 2)).unwrap();
    let before = wrong.state_wire().unwrap();
    assert!(wrong.receive(incoming.view(), current(&y)).is_err());
    assert_eq!(wrong.state_wire().unwrap(), before);
    assert_eq!(wrong.observations(), 0);
}

#[test]
#[ignore = "requires CUDA; unit-prior target energy bounds the reference without a carrier raise"]
fn target_energy_caps_a_large_source_family_and_keeps_legacy_rest() {
    use num_traits::ToPrimitive;
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let grain = ResidentGrain(64);
    let scale = 1i128 << grain.0;
    // This is a declared source aperture, not a material capacity. The old residual/source
    // product overflows on its response; the energy bound remains valid for the entire ball.
    let radius = (1i128 << 27) * scale;
    let values = [scale,0,scale,0,0,0,radius];
    let words = values.into_iter().flat_map(|v| [v as i64,(v >> 64) as i64])
        .map(|v| (v,v)).collect();
    let source = s.mount_section_rest(&ResidentSectionRest::found(
        1,14,ResidentGrain(0),64,words).unwrap()).unwrap();
    let input = ResidentNormalEnclosureView {
        surface: &s, section: &source, offset:0, width:6, grain,
    };
    let target = point(&s,&[1,0]);
    let mut body = ResidentNormalMaterial::found(&s,1,1,grain).unwrap();
    let reads = s.census().section_read_outs;
    body.receive(input,current(&target)).unwrap();
    assert_eq!(s.census().section_read_outs,reads);
    let state = body.inspect().unwrap();
    let norm: Rat = state.material.coefficients.iter().flatten()
        .map(|v| v.real.abs()+v.imaginary.abs()).sum();
    let residual: Rat = state.normal_residual().unwrap().iter().flatten()
        .map(|v| v.real.abs()+v.imaginary.abs()).sum();
    let legacy = residual + &norm * &state.source_normal_error + &state.cross_source_error;
    assert!(state.material.radius < legacy);
    assert!(state.material.radius <= &norm + Rat::one());
    assert_eq!(state.target_energy,Rat::one());
    assert!(state.target_energy_error.is_zero());
    let rest = body.rest().unwrap();
    rest.validate().unwrap();
    let mut legacy_state = rest.state().clone();
    let raw = legacy * Rat::from_integer(BigInt::one() << grain.0);
    let floor = raw.numer() / raw.denom();
    let ceil = if raw.numer() % raw.denom() == BigInt::zero() { floor } else { floor+1 };
    let old_error = ceil.to_i128().unwrap();
    let at = 2 * NormalLayout::new(1,1).unwrap().cross_values;
    legacy_state.intervals[at]=(old_error as i64,old_error as i64);
    legacy_state.intervals[at+1]=((old_error >> 64) as i64,(old_error >> 64) as i64);
    NormalMaterialRest::from_state_data(1,1,grain,1,legacy_state).unwrap();
}
