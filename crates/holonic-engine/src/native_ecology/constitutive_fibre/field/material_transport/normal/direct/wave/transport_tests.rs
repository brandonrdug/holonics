use super::comparison_tests::{current, point, witness};
use super::*;
use crate::embedding_fiber::ResidentReadout;

#[test]
#[ignore = "requires CUDA; exact first power and dyadic operator transport retain source error"]
fn first_power_pays_actual_rounding_and_dyadic_source_transport() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let seed = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, 3, ResidentGrain(0), 64, vec![(1, 1), (0, 0), (3, 3)])
                .unwrap(),
        )
        .unwrap();
    let rational = ResidentConstitutiveCurrent::rational(&seed).unwrap();
    let mut body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(32))
        .unwrap()
        .into_difference_wave(rational, rational)
        .unwrap();
    body.set_transport(NormalWaveTransport::Applied).unwrap();
    let scale = BigInt::one() << 32usize;
    assert_eq!(
        body.joint_source().joint().inspect().unwrap().radius,
        Rat::new(2.into(), scale.clone())
    );
    let reads = s.census().section_read_outs;
    let result = body.advance().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let reading = result.inspect().unwrap();
    assert_eq!(reading.uniform_power_equation_defect, Rat::zero());
    assert_eq!(reading.operator_word_error, Rat::zero());
    // Q=[0,1;0,1] has norm sqrt(2), not its integer ceiling 2.
    assert_eq!(reading.joint_current.radius, Rat::new(3.into(), scale));
    super::comparison_tests::contains(
        &reading.joint_current,
        &[
            super::comparison_tests::wave(1, 0, 3),
            super::comparison_tests::wave(1, 0, 3),
        ],
    );
}

#[test]
#[ignore = "requires CUDA; complex Gram contraction precedes absolute row bounds"]
fn gram_transport_keeps_cancellation_before_its_bound() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let material = ResidentNormalMaterial::found(&s, 2, 2, ResidentGrain(32)).unwrap();
    let mut state = material.state_wire().unwrap();
    let layout = NormalLayout::new(2, 2).unwrap();
    let mut values = wides(&state.intervals[..layout.matrix_words]).unwrap();
    let scale = 1i128 << 32;
    // A declared applied operator, not training data or a fixture-local learner:
    // G=[0,I;A,0], A=3/4*[1,i;1,-i]. Its Gram is diagonal, norm²=9/8.
    values[2 * 2] = -scale;
    values[2 * 4] = 3 * scale / 4;
    values[2 * 5 + 1] = 3 * scale / 4;
    values[2 * (6 + 3)] = -scale;
    values[2 * (6 + 4)] = 3 * scale / 4;
    values[2 * (6 + 5) + 1] = -3 * scale / 4;
    // The zero-statistic minimizer is zero: these exact L1 M/residual bounds
    // enclose this declared dyadic realization without claiming it was fitted.
    for v in &mut values[layout.cross_values..layout.cross_values + 3] {
        *v = 5 * scale;
    }
    for (i, value) in values.into_iter().enumerate() {
        let bytes = value.to_le_bytes();
        let lo = i64::from_le_bytes(bytes[..8].try_into().unwrap());
        let hi = i64::from_le_bytes(bytes[8..].try_into().unwrap());
        state.intervals[2 * i] = (lo, lo);
        state.intervals[2 * i + 1] = (hi, hi);
    }
    let material = NormalMaterialRest::from_state_data(2, 2, ResidentGrain(32), 0, state)
        .unwrap()
        .remount(&s)
        .unwrap();
    let seed = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                1,
                5,
                ResidentGrain(0),
                64,
                vec![(1, 1), (0, 0), (1, 1), (0, 0), (3, 3)],
            )
            .unwrap(),
        )
        .unwrap();
    let rational = ResidentConstitutiveCurrent::rational(&seed).unwrap();
    let mut body = material.into_difference_wave(rational, rational).unwrap();
    body.set_transport(NormalWaveTransport::Applied).unwrap();
    let reading = body.advance().unwrap().inspect().unwrap();
    // Four seed rounding units, transported by sqrt(9/8), round up to five;
    // all four real/imaginary bottom components incur one actual rounding unit.
    assert_eq!(
        reading.joint_current.radius,
        Rat::new(9.into(), BigInt::from(scale))
    );
    assert_eq!(reading.operator_word_error, Rat::zero());
    super::comparison_tests::contains(
        &reading.joint_current,
        &[
            super::comparison_tests::wave(1, 0, 3),
            super::comparison_tests::wave(1, 0, 3),
            super::comparison_tests::wave(1, 1, 4),
            super::comparison_tests::wave(1, -1, 4),
        ],
    );
}

#[test]
#[ignore = "requires CUDA; normal-reference comparison is a separate pure receiver"]
fn applied_transport_retains_reference_without_reinjecting_it() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut applied = witness(&s);
    applied.set_transport(NormalWaveTransport::Applied).unwrap();
    let before = applied.rest().unwrap();
    let mut wire = Vec::new();
    before.write(&mut wire).unwrap();
    assert_eq!(wire[b"HOLONIC-NORMAL-WAVE".len()], 6);
    let restored = NormalWaveRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    assert_eq!(restored.transport(), NormalWaveTransport::Applied);
    assert_eq!(restored.pending_count(), 0);
    assert_eq!(
        restored.remount(&s, |_| {}).unwrap().rest().unwrap(),
        before
    );
    let source = applied.current().snapshot();
    let reads = s.census().section_read_outs;
    let reference = applied.reference_next().unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(applied.rest().unwrap(), before);
    assert!(applied.current().same_occurrence(&source));
    let comparison = reference.inspect().unwrap();
    assert_eq!(comparison.producing_transport, NormalWaveTransport::Applied);
    let next = comparison.produced_joint.unwrap();
    let result = applied.advance().unwrap().inspect().unwrap();
    assert_eq!(result.joint_current.center, next.center);
    assert!(result.joint_current.radius < next.radius);
    assert!(applied.fibre().inspect_material().unwrap().material.radius > Rat::zero());
}

#[test]
#[ignore = "requires CUDA; changing future scope never narrows the held source enclosure"]
fn transport_change_keeps_the_held_family_and_mixed_pending_scopes() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut body = witness(&s);
    let (old, _) = body.predict().unwrap();
    let held = body.current().snapshot();
    let before = serde_json::to_value(held.view().inspect().unwrap()).unwrap();
    let epoch = body.epoch();
    let change = body.set_transport(NormalWaveTransport::Applied).unwrap();
    assert_eq!(
        change.predecessor_fibre.transport,
        NormalWaveTransport::NormalReference
    );
    assert_eq!(change.successor_fibre.transport, NormalWaveTransport::Applied);
    assert!(body.current().same_occurrence(&held));
    assert_eq!(body.epoch(), epoch);
    assert_eq!(
        serde_json::to_value(body.current().view().inspect().unwrap()).unwrap(),
        before
    );
    let (newer, _) = body.predict().unwrap();
    let mut bytes = Vec::new();
    body.rest().unwrap().write(&mut bytes).unwrap();
    // One-cut pending sources: wave rest v11 (the transport header, then source joints).
    assert_eq!(bytes[b"HOLONIC-NORMAL-WAVE".len()], 11);
    let rest = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(rest.transport(), NormalWaveTransport::Applied);
    assert_eq!(rest.pending_count(), 2);
    let mut restored = rest.remount(&s, |_| {}).unwrap();
    let target = point(&s, &[3, 0]);
    // One cut: both returns read the contemporary (Applied) transport, whatever transport
    // was in force when each prediction was made.
    for id in [old, newer] {
        let x = body.pullback(id, current(&target)).unwrap().inspect().unwrap();
        let y = restored
            .pullback(id, current(&target))
            .unwrap()
            .inspect()
            .unwrap();
        assert_eq!(x.producing_transport, NormalWaveTransport::Applied);
        assert_eq!(x.successor_transport, NormalWaveTransport::Applied);
        assert_eq!(
            serde_json::to_value(x).unwrap(),
            serde_json::to_value(y).unwrap()
        );
    }
    assert_eq!(body.rest().unwrap(), restored.rest().unwrap());
}

#[test]
#[ignore = "requires CUDA; applying M changes no coefficients and keeps actual source uncertainty"]
fn applied_source_and_return_preserve_material_and_pay_rounding() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut reference = witness(&s);
    let mut applied = witness(&s);
    applied.set_transport(NormalWaveTransport::Applied).unwrap();
    let field = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                3,
                2,
                ResidentGrain(0),
                64,
                vec![(0, 0), (0, 0), (1, 1), (0, 0), (2, 2), (0, 0)],
            )
            .unwrap(),
        )
        .unwrap();
    let section = ResidentConstitutiveSection::integers(&field).unwrap();
    let material = applied.material.rest().unwrap();
    let a = applied
        .actuate_section(section)
        .unwrap()
        .after()
        .unwrap()
        .inspect()
        .unwrap();
    let r = reference
        .actuate_section(section)
        .unwrap()
        .after()
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(a.center, r.center);
    assert!(a.radius <= r.radius);
    assert_eq!(applied.material.rest().unwrap(), material);
    let (pa, _) = applied.predict().unwrap();
    let (pr, _) = reference.predict().unwrap();
    let y = point(&s, &[3, 0]);
    applied.pullback(pa, current(&y)).unwrap();
    reference.pullback(pr, current(&y)).unwrap();
    let aa = applied.material.inspect().unwrap();
    let rr = reference.material.inspect().unwrap();
    assert_eq!(aa.material.coefficients, rr.material.coefficients);
    assert!(aa.source_normal_error <= rr.source_normal_error);
    assert!(aa.source_normal_error > Rat::zero());
    assert!(aa.material.radius > Rat::zero());
}
