use super::*;
use holonics::exact_linear::ExactRatMatrix;
use crate::{embedding_fiber::ResidentReadout, native_ecology::constitutive_fibre::ConditionContactMetric};
fn point<'c>(surface: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                values.len(),
                ResidentGrain(0),
                i64::BITS,
                values.iter().map(|v| (*v, *v)).collect(),
            )
            .unwrap(),
        )
        .unwrap()
}
fn current<'a, 'c>(section: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(section).unwrap()
}
// Exact exterior bilinear contact law y = a·h on the complex source port.
fn law<'c>(s: &'c ResidentSurface<'c>) -> ResidentConstitutiveFibre<'c> {
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(s, 3, 1, 1).unwrap();
    let mut sources = vec![[0i64; 6]];
    for j in 0..6 {
        let mut a = [0; 6];
        a[j] = 1;
        sources.push(a);
    }
    for a in sources {
        for h in [[0, 0], [1, 0], [0, 1]] {
            let eta = [a[0] * h[0] - a[1] * h[1], a[0] * h[1] + a[1] * h[0]];
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
fn r(v: i64) -> Rat {
    Rat::from_integer(v.into())
}
// Exterior reference witnesses only. No source or material values leave the device inside
// the compiler/evaluator; these cold solves construct explicit test parameter occurrences.
fn parameters(
    comparison: &NormalCoupledComparison<'_>,
    material: &ResidentConstitutiveFibre<'_>,
    anchor: &[i64],
) -> Vec<Rat> {
    parameters_at(comparison, material, anchor, anchor)
}
fn parameters_at(
    comparison: &NormalCoupledComparison<'_>,
    material: &ResidentConstitutiveFibre<'_>,
    anchor: &[i64],
    joint: &[i64],
) -> Vec<Rat> {
    let theta = source_parameters_at(comparison, anchor, joint);
    let s = comparison.source().origin().fibre().surface;
    let mut paired = comparison.inspect_row(0).unwrap();
    paired.features.extend(paired.observed_difference);
    let mut g = paired.features;
    for (i, coefficient) in theta.iter().enumerate() {
        let mut row = comparison.inspect_row(i + 1).unwrap();
        row.features.extend(row.observed_difference);
        for (to, from) in g.iter_mut().zip(row.features) {
            *to += coefficient * from;
        }
    }
    let w = g.len();
    let values = s.read_out(&material.basis).unwrap();
    let basis = ExactRatMatrix::new(
        values
            .chunks_exact(w)
            .map(|row| {
                row.iter()
                    .map(|(a, b)| {
                        assert_eq!(a, b);
                        r(*a)
                    })
                    .collect()
            })
            .collect(),
    )
    .unwrap();
    let (witnesses, _) = basis
        .transpose()
        .unwrap()
        .preimage_fibre(&g)
        .unwrap()
        .unwrap();
    let mut result = theta;
    let fixed = comparison.relation().fixed_condition();
    let words = s.read_out(fixed.section).unwrap();
    let den = words[fixed.denominator.unwrap()].0;
    result.extend(
        words[fixed.offset..fixed.offset + fixed.width]
            .iter()
            .map(|(a, b)| {
                assert_eq!(a, b);
                Rat::new((*a).into(), den.into())
            }),
    );
    result.extend(witnesses);
    result
}
fn source_parameters_at(
    comparison: &NormalCoupledComparison<'_>, anchor: &[i64], joint: &[i64],
) -> Vec<Rat> {
    let family = comparison.source().affine_relation();
    let s = comparison.source().origin().fibre().surface;
    let raw = s.read_out(family.report()).unwrap();
    assert!(raw.iter().all(|(a, b)| a == b));
    let raw = raw.iter().map(|v| v.0).collect::<Vec<_>>();
    let ps = family.source_width();
    let t = family.target_width();
    let pk = ps + t;
    let origin = raw[ps..pk]
        .iter()
        .map(|v| Rat::new((*v).into(), raw[pk].into()))
        .collect::<Vec<_>>();
    let dirs = ExactRatMatrix::new(
        raw[pk + 4..]
            .chunks_exact(t)
            .map(|v| v.iter().map(|n| r(*n)).collect())
            .collect(),
    )
    .unwrap();
    let mut desired = vec![r(1), r(0)];
    desired.extend(anchor.iter().map(|v| r(*v)));
    desired.extend(joint.iter().map(|v| r(*v)));
    let rhs = desired
        .iter()
        .zip(origin)
        .map(|(a, b)| a - b)
        .collect::<Vec<_>>();
    let (theta, _) = dirs
        .transpose()
        .unwrap()
        .preimage_fibre(&rhs)
        .unwrap()
        .unwrap();
    theta
}

/// Parity law (coupled joint compiler): the compiled device evaluator returns zero relation and
/// producing-condition residuals at exact host-solved parameter points, and its anchor predicate
/// agrees with the exact point inside or outside the anchor ball.
#[test]
#[ignore = "requires CUDA; non-dyadic producing condition and observation stay exact through native compilation"]
fn compiled_joint_keeps_rational_condition_and_observation_denominators() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let h = s
        .mount_exact_rational_packet(&[Rat::new(1.into(), 2.into()), Rat::new(1.into(), 3.into())])
        .unwrap();
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law(&s)],
        ResidentConstitutiveCurrent::rational(&h).unwrap(),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut wave = body(&s).with_neighborhood(neighborhood).unwrap();
    let contact = wave.admit_contact(0).unwrap();
    let pred = wave.predict_contact(&contact).unwrap();
    let v = s
        .mount_exact_rational_packet(&[
            Rat::new(13.into(), 6.into()),
            Rat::new(11.into(), 6.into()),
        ])
        .unwrap();
    let cmp = wave
        .compare_coupled_prediction(
            &pred.0,
            ResidentConstitutiveCurrent::rational(&v).unwrap(),
        )
        .unwrap();
    let inside = parameters(
        &cmp,
        wave.neighborhood().generator(0).unwrap(),
        &[1, 0, 2, 1],
    );
    let outside = parameters(
        &cmp,
        wave.neighborhood().generator(0).unwrap(),
        &[10, 2, 5, 3],
    );
    let compiled = wave.compile_coupled_joint(&cmp).unwrap();
    for (theta, inside) in [(inside, true), (outside, false)] {
        let packet = s.mount_exact_rational_packet(&theta).unwrap();
        let reads = s.census().section_read_outs;
        let result = compiled.evaluate(&packet).unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        let got = result.inspect().unwrap();
        assert_eq!(got.within_anchor, inside);
        assert!(got.relation_residual.iter().all(Zero::is_zero));
        assert!(got.producing_condition_residual.iter().all(Zero::is_zero));
    }
}
