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
fn wave(r: i64, i: i64, d: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(Rat::new(r.into(), d.into()), Rat::new(i.into(), d.into()))
}
fn contains(ball: &NativeFieldCurrentBall, expected: &[ExactComplexWaveCurrent]) {
    let square: Rat = ball
        .center
        .iter()
        .zip(expected)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert!(
        square <= &ball.radius * &ball.radius,
        "outside current enclosure"
    );
}
fn material<'c>(s: &'c ResidentSurface<'c>, imaginary: i64) -> ResidentNormalMaterial<'c> {
    let mut body = ResidentNormalMaterial::found(s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    // One unit observation on each independent complex source port. This declares the
    // source operator before restricting it to the difference/comparand plane.
    for port in 0..3 {
        let mut x = [0; 6];
        x[2 * port] = 1;
        let x = point(s, &x);
        let y = point(s, &if port == 1 { [-1, imaginary] } else { [0, 0] });
        body.receive(current(&x), current(&y)).unwrap();
    }
    body
}

#[test]
#[ignore = "requires CUDA; a fixed learned generator unfolds without source history, retains the actual join and pays its full operator-word remainder"]
fn learned_decay_keeps_the_join_and_complete_joint_current() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let body = material(&s, 0);
    let p = point(&s, &[7, 2]);
    let c = point(&s, &[3, 4, 5]);
    let mut generator = body
        .into_difference_wave(
            current(&p),
            ResidentConstitutiveCurrent::rational(&c).unwrap(),
        )
        .unwrap();
    drop(p);
    drop(c);
    let reads = s.census().section_read_outs;
    let residency = s.census().resident_octets_now;
    let mut denominator = 5;
    for at in 1..=32 {
        let joining = generator.current().snapshot();
        let returned = generator.advance().unwrap();
        assert!(returned.previous.same_occurrence(&joining));
        assert!(generator.previous().same_occurrence(&joining));
        assert!(!returned.current.same_occurrence(&joining));
        assert_eq!(returned.current.at(), Some(at));
        assert_eq!(s.census().section_read_outs, reads + (at - 1) * 3);
        denominator *= 2;
        let reading = returned.inspect().unwrap();
        contains(
            &returned.current.view().inspect().unwrap(),
            &[wave(3, 4, denominator)],
        );
        assert_eq!(reading.steps, at);
        assert!(reading.maximum_computed_power_norm >= Rat::one());
        drop(returned);
        drop(joining);
        assert_eq!(s.census().resident_octets_now, residency);
    }
    assert_eq!(generator.fibre().material_observations, 3);
    assert_eq!(generator.fibre().initial().rows(), 2);
}

#[test]
#[ignore = "requires CUDA; current phase is generated and fixed faces remain distinct occurrences"]
fn rotation_and_equal_faces_are_not_source_identity() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let p = point(&s, &[0, 0]);
    let c = point(&s, &[1, 0]);
    let mut generator = material(&s, 1)
        .into_difference_wave(current(&p), current(&c))
        .unwrap();
    let expected = [wave(1, 1, 2), wave(0, 1, 2), wave(-1, 1, 4), wave(-1, 0, 4)];
    for value in expected {
        let returned = generator.advance().unwrap();
        contains(&returned.current.view().inspect().unwrap(), &[value]);
    }
    let body = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let mut zero = body.into_difference_wave(current(&p), current(&p)).unwrap();
    let previous = zero.current().snapshot();
    let returned = zero.advance().unwrap();
    assert!(!previous.same_occurrence(&returned.current));
    assert_eq!(
        returned.current.view().inspect().unwrap().radius,
        Rat::zero()
    );
    contains(
        &returned.current.view().inspect().unwrap(),
        &[wave(0, 0, 1)],
    );
}

#[test]
#[ignore = "requires CUDA; invalid seeds return their material owner and a later arithmetic refusal preserves the actual wave successor"]
fn refused_seed_and_wave_step_preserve_their_owners() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let body = material(&s, 0);
    let before = body.state_wire().unwrap();
    let p = point(&s, &[0, 0]);
    let bad = point(&s, &[1]);
    let refused = body
        .into_difference_wave(current(&p), current(&bad))
        .err()
        .unwrap();
    assert_eq!(refused.material.state_wire().unwrap(), before);
    let c = point(&s, &[1, 0]);
    let mut generator = refused
        .material
        .into_difference_wave(current(&p), current(&c))
        .unwrap();
    // A declared corrupted cache is a test-only fault injection; a production caller cannot
    // obtain mutable access to it. The actual existing current must not be replaced on refusal.
    let mut wire = s.detach_section(&generator.power, i64::BITS).unwrap();
    // The lower source row is consumed by this generator; its upper row is a forgotten lag.
    let at = 4 * 2;
    wire.intervals[at] = (i64::MAX, i64::MAX);
    wire.intervals[at + 1] = (i64::MAX, i64::MAX);
    generator.power = s.mount_section_rest(&wire).unwrap();
    let prior = generator.current().snapshot();
    assert!(generator.advance().is_err());
    assert!(generator.current().same_occurrence(&prior));
    assert_eq!(generator.steps(), 0);
}

#[test]
#[ignore = "requires CUDA; rest stores the generator and seed, and its decoder restores the actual next bounded return"]
fn generator_rest_decodes_the_word_and_rejoins_the_next_return() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let p = point(&s, &[0, 0]);
    let c = point(&s, &[3, 4, 5]);
    let mut original = material(&s, 1)
        .into_difference_wave(
            current(&p),
            ResidentConstitutiveCurrent::rational(&c).unwrap(),
        )
        .unwrap();
    for _ in 0..7 {
        original.advance().unwrap();
    }
    let saved = original.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let expected = original.advance().unwrap();
    let old_current = expected.current.snapshot();
    let expected = serde_json::to_value(expected.inspect().unwrap()).unwrap();
    drop(original);
    let loaded = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(loaded, saved);
    let mut decoded = 0;
    let mut resumed = loaded.remount(&s, |step| decoded = step).unwrap();
    assert_eq!(decoded, 7);
    let returned = resumed.advance().unwrap();
    assert_eq!(
        serde_json::to_value(returned.inspect().unwrap()).unwrap(),
        expected
    );
    assert!(!returned.current.same_occurrence(&old_current));
}
