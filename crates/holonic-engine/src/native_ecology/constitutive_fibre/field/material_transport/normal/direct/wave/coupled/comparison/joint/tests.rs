use super::super::super::super::comparison_tests::{current, point};
use super::super::super::super::family::tests::{body, law};
use super::*;
use crate::{
    embedding_fiber::ResidentReadout,
    exact_linear::ExactRatMatrix,
    native_ecology::constitutive_fibre::{ConditionContactMetric, WaveSourceReceiver},
};
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
pub(in super::super::super) fn source_parameters_at(
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
fn wave<'c>(s: &'c ResidentSurface<'c>) -> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    let h = point(s, &[1, 0]);
    let n = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law(s, false)],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    body(s).with_neighborhood(n).unwrap()
}
#[test]
#[ignore = "requires CUDA; real pending comparisons compile with original source, condition and anchor"]
fn pending_comparison_compiles_joint_equations_without_freeing_its_anchor() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    for receiver in [WaveSourceReceiver::Direct, WaveSourceReceiver::UnitRealSum] {
        let (mut wave, inside_anchor, outside_anchor, observed_values) = if receiver
            == WaveSourceReceiver::Direct
        {
            (wave(&s), vec![1, 0, 2, 1], vec![5, 4, 4, 3], vec![3, 2])
        } else {
            let p = point(&s, &[4, 0, 1, 0]);
            let c = point(&s, &[1, 0, 4, 0]);
            let h = point(&s, &[1, 0]);
            let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
                vec![super::super::super::tests::unit_swap(&s)],
                current(&h),
                ConditionContactMetric::UnitAdmittanceRealification,
            )
            .unwrap();
            let body = crate::native_ecology::constitutive_fibre::ResidentNormalMaterial::found(
                &s,
                2,
                2,
                ResidentGrain(32),
            )
            .unwrap()
            .into_applied_difference_wave(current(&p), current(&c))
            .unwrap()
            .with_neighborhood(neighborhood)
            .unwrap();
            (
                body,
                vec![4, 0, 1, 0, 1, 0, 4, 0],
                vec![6, 0, 3, 0, 3, 0, 6, 0],
                vec![2, 0, -1, 0],
            )
        };
        let contact = wave.admit_contact_in_chart(0, receiver).unwrap();
        let prediction = wave.predict_contact(&contact).unwrap();
        let observed = point(&s, &observed_values);
        let comparison = wave
            .compare_coupled_prediction(&prediction.handle, current(&observed))
            .unwrap();
        let inside = parameters(
            &comparison,
            wave.neighborhood().generator(0).unwrap(),
            &inside_anchor,
        );
        let outside = parameters(
            &comparison,
            wave.neighborhood().generator(0).unwrap(),
            &outside_anchor,
        );
        let before = wave.rest().unwrap();
        let reads = s.census().section_read_outs;
        let compiled = wave.compile_coupled_joint(&comparison).unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        assert_eq!(compiled.parameter_count(), inside.len());
        for (values, within) in [(inside.clone(), true), (outside, false)] {
            let packet = s.mount_exact_rational_packet(&values).unwrap();
            let reads = s.census().section_read_outs;
            let evaluated = compiled.evaluate(&packet).unwrap();
            assert_eq!(s.census().section_read_outs, reads);
            let got = evaluated.inspect().unwrap();
            eprintln!("joint receiver={receiver:?} expected_inside={within} reading={got:?}");
            assert_eq!(got.within_anchor, within);
            assert!(got.relation_residual.iter().all(Zero::is_zero));
            assert!(got.producing_condition_residual.iter().all(Zero::is_zero));
            assert!(std::ptr::eq(evaluated.parameters(), &packet));
        }
        let mut wrong_condition = inside;
        wrong_condition[compiled.source_parameters()] = r(2);
        let packet = s.mount_exact_rational_packet(&wrong_condition).unwrap();
        let got = compiled.evaluate(&packet).unwrap().inspect().unwrap();
        assert_eq!(got.producing_condition_residual, vec![r(1), r(0)]);
        assert!(got.within_anchor);
        assert_eq!(wave.rest().unwrap(), before);
        assert_eq!(wave.pending_coupled_predictions(), 1);
    }
}
#[test]
#[ignore = "requires CUDA; delayed and remounted compilation preserves the original condition and pending lineage"]
fn delayed_joint_compilation_uses_current_material_and_the_original_producing_condition() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = wave(&s);
    let contact = wave.admit_contact(0).unwrap();
    let prediction = wave.predict_contact(&contact).unwrap();
    let v = point(&s, &[3, 2]);
    let cmp = wave
        .compare_coupled_prediction(&prediction.handle, current(&v))
        .unwrap();
    let old = wave.compile_coupled_joint(&cmp).unwrap();
    let old_cut = old.material_cut();
    let source = point(&s, &[1, 0, 1, 0, 0, 0]);
    let eta = point(&s, &[2, 0]);
    let contact = wave.admit_contact(0).unwrap();
    wave.receive_contact_source(&contact, current(&source), current(&eta))
        .unwrap();
    let values = parameters(
        &cmp,
        wave.neighborhood().generator(0).unwrap(),
        &[1, 0, 2, 1],
    );
    let packet = s.mount_exact_rational_packet(&values).unwrap();
    let new = wave.compile_coupled_joint(&cmp).unwrap();
    assert!(new.material_cut() > old_cut);
    assert!(!old.matches_material(wave.neighborhood().generator(0).unwrap()));
    let expected = new.evaluate(&packet).unwrap().inspect().unwrap();
    assert!(expected.relation_residual.iter().all(Zero::is_zero));
    assert!(
        expected
            .producing_condition_residual
            .iter()
            .all(Zero::is_zero)
    );
    let saved = wave.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let restored = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
        .unwrap()
        .remount_coupled(&s, |_| {})
        .unwrap();
    let handle = restored
        .pending_coupled_prediction(prediction.handle.id())
        .unwrap();
    let cmp2 = restored
        .compare_coupled_prediction(&handle, current(&v))
        .unwrap();
    let actual = restored
        .compile_coupled_joint(&cmp2)
        .unwrap()
        .evaluate(&packet)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(actual, expected);
    assert!(restored.compile_coupled_joint(&cmp).is_err());
    wave.release_coupled_prediction(&prediction.handle).unwrap();
    assert!(wave.compile_coupled_joint(&cmp).is_err());
}

#[test]
#[ignore = "requires CUDA; source-current directions at a fixed anchor remain a genuine family"]
fn compiled_joint_retains_free_current_directions_inside_one_anchor() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut local = law(&s, false);
    let zero = point(&s, &[0, 0, 0, 0, 0, 0]);
    let h = point(&s, &[1, 0]);
    let vertical = point(&s, &[1, 0]);
    local
        .advance_bilinear_contact(current(&zero), current(&h), Some(current(&vertical)))
        .unwrap();
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![local],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut wave = body(&s).with_neighborhood(neighborhood).unwrap();
    let first = wave.admit_contact(0).unwrap();
    wave.advance_contact(&first).unwrap();
    let next = wave.admit_contact(0).unwrap();
    let pred = wave.predict_contact(&next).unwrap();
    let observed = point(&s, &[7, 3]);
    let comparison = wave
        .compare_coupled_prediction(&pred.handle, current(&observed))
        .unwrap();
    let a = parameters_at(
        &comparison,
        wave.neighborhood().generator(0).unwrap(),
        &[1, 0, 2, 1],
        &[2, 1, 3, 2],
    );
    let b = parameters_at(
        &comparison,
        wave.neighborhood().generator(0).unwrap(),
        &[1, 0, 2, 1],
        &[2, 1, 9, 2],
    );
    assert_ne!(a, b);
    let compiled = wave.compile_coupled_joint(&comparison).unwrap();
    for theta in [a, b] {
        let packet = s.mount_exact_rational_packet(&theta).unwrap();
        let reads = s.census().section_read_outs;
        let result = compiled.evaluate(&packet).unwrap();
        assert_eq!(s.census().section_read_outs, reads);
        let got = result.inspect().unwrap();
        assert!(got.within_anchor);
        assert!(got.anchor_difference.iter().all(Zero::is_zero));
        assert!(got.relation_residual.iter().all(Zero::is_zero));
        assert!(got.producing_condition_residual.iter().all(Zero::is_zero));
    }
}

#[test]
#[ignore = "requires CUDA; non-dyadic producing condition and observation stay exact through native compilation"]
fn compiled_joint_keeps_rational_condition_and_observation_denominators() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let h = s
        .mount_exact_rational_packet(&[Rat::new(1.into(), 2.into()), Rat::new(1.into(), 3.into())])
        .unwrap();
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law(&s, false)],
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
            &pred.handle,
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
