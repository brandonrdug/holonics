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
    assert_eq!(ball.center.len(), expected.len());
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
    let mut residency = s.census().resident_octets_now;
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
        // The initial word aliases its seed bound. Its first generated joint is one
        // additional fixed-size cache; subsequent steps must not accumulate more.
        if at == 1 {
            residency = s.census().resident_octets_now;
        }
        assert_eq!(s.census().resident_octets_now, residency);
    }
    assert_eq!(generator.fibre().material_observations, 3);
    assert_eq!(generator.fibre().initial().unwrap().rows(), 2);
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

#[test]
#[ignore = "requires CUDA; actual reception changes reusable material, preserves the join and retains the shared source/target family"]
fn reception_changes_the_next_generator_without_archiving_its_past() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let p = point(&s, &[0, 0]);
    let c = point(&s, &[1, 0]);
    let v = point(&s, &[2, 0]);
    let mut body = material(&s, 0)
        .into_difference_wave(current(&p), current(&c))
        .unwrap();
    body.advance().unwrap();
    let joining = body.current().snapshot();
    let before = s.census();
    let received = body.receive(current(&v)).unwrap();
    assert_eq!(s.census().section_read_outs, before.section_read_outs);
    assert_eq!(s.census().ingress_octets, before.ingress_octets);
    assert!(body.previous().same_occurrence(&joining));
    assert!(received.previous.same_occurrence(&joining));
    assert_eq!(body.steps(), 0);
    assert_eq!(body.epoch(), 2);
    assert_eq!(received.current.at(), Some(2));
    assert_eq!(received.predecessor_fibre.material_observations, 3);
    assert_eq!(received.successor_fibre.material_observations, 4);
    assert!(received.successor_fibre.initial().is_none());
    let reading = received.inspect().unwrap();
    contains(&reading.source_joint, &[wave(1, 0, 1), wave(1, 0, 2)]);
    contains(
        reading.comparison.source_current.as_ref().unwrap(),
        &[wave(-1, 0, 2), wave(1, 0, 2), wave(1, 0, 1)],
    );
    contains(&reading.comparison.observed, &[wave(3, 0, 2)]);
    assert!(reading.comparison.observed.radius > Rat::zero());
    let old = received.predecessor_fibre.inspect_material().unwrap();
    let new = received.successor_fibre.inspect_material().unwrap();
    assert_ne!(old.cross_source, new.cross_source);
    // H=2I+xx*, B=(0,-1,0)+(3/2)x*: its exact response has coefficients
    // (-1/4,-1/4,1/2), so the next current is 2-5/8=11/8.
    let next = body.advance().unwrap();
    assert!(next.previous.same_occurrence(&received.current));
    contains(&next.current.view().inspect().unwrap(), &[wave(11, 0, 8)]);
    assert_eq!(next.current.at(), Some(3));
    // Saved evidence refers to immutable producing material, even after further development.
    let evidence = serde_json::to_value(received.inspect().unwrap()).unwrap();
    body.receive(current(&c)).unwrap();
    assert_eq!(
        serde_json::to_value(received.inspect().unwrap()).unwrap(),
        evidence
    );
    drop(received);
    drop(next);
    drop(joining);
    let residency = s.census().resident_octets_now;
    for _ in 0..4 {
        body.advance().unwrap();
        body.receive(current(&v)).unwrap();
        assert_eq!(s.census().resident_octets_now, residency);
    }
}

#[test]
#[ignore = "requires CUDA; bounded reception rest restores the next generated and received operations; refusal changes no live state"]
fn received_seed_rest_and_atomic_refusal_preserve_the_whole_successor() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let p = point(&s, &[0, 0]);
    let c = point(&s, &[3, 4, 5]);
    let v = point(&s, &[-1, 1]);
    let mut body = material(&s, 1)
        .into_difference_wave(
            current(&p),
            ResidentConstitutiveCurrent::rational(&c).unwrap(),
        )
        .unwrap();
    for _ in 0..3 {
        body.advance().unwrap();
    }
    body.receive(current(&v)).unwrap();
    for _ in 0..2 {
        body.advance().unwrap();
    }
    let saved = body.rest().unwrap();
    let joining = body.current().snapshot();
    let bad = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), 64, vec![(0, 1), (0, 0)]).unwrap(),
        )
        .unwrap();
    assert!(body.receive(current(&bad)).is_err());
    assert_eq!(body.rest().unwrap(), saved);
    assert!(body.current().same_occurrence(&joining));
    // Enlarge only the private numerical joint cache to a valid but unrepresentably broad
    // source image. Seed preparation succeeds; the later 2*radius calculation must refuse.
    let fine_joint = Rc::clone(&body.joint);
    let mut broad = s.detach_section(&body.joint, i64::BITS).unwrap();
    let radius = 2 * (2 * body.current.width);
    broad.intervals[radius] = (-1, -1);
    broad.intervals[radius + 1] = (i64::MAX, i64::MAX);
    body.joint = Rc::new(s.mount_section_rest(&broad).unwrap());
    assert!(body.receive(current(&v)).is_err());
    assert_eq!(body.rest().unwrap(), saved);
    assert!(body.current().same_occurrence(&joining));
    assert_eq!(s.detach_section(&body.joint, i64::BITS).unwrap(), broad);
    body.joint = fine_joint;
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    assert_eq!(saved.seed_kind(), NormalWaveSeedKind::ReceivedCurrent);
    assert_eq!(saved.epoch(), 6);
    let expected = serde_json::to_value(body.advance().unwrap().inspect().unwrap()).unwrap();
    let expected_receive =
        serde_json::to_value(body.receive(current(&p)).unwrap().inspect().unwrap()).unwrap();
    let expected_rest = body.rest().unwrap();
    drop(body);
    let loaded = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(loaded, saved);
    let mut resumed = loaded.remount(&s, |_| {}).unwrap();
    assert_eq!(resumed.epoch(), 6);
    assert_eq!(
        serde_json::to_value(resumed.advance().unwrap().inspect().unwrap()).unwrap(),
        expected
    );
    assert_eq!(
        serde_json::to_value(resumed.receive(current(&p)).unwrap().inspect().unwrap()).unwrap(),
        expected_receive
    );
    assert_eq!(resumed.rest().unwrap(), expected_rest);
    // Version refusal occurs at the cold wire boundary before mounting any state.
    bytes[b"HOLONIC-NORMAL-WAVE".len()] = u8::MAX;
    assert!(NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).is_err());
}

#[test]
#[ignore = "requires CUDA; section development keeps current identity, changes its next conduct and rests the joint seed"]
fn a_measured_section_develops_the_continuing_generator() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let p = point(&s, &[0, 0]);
    let c = point(&s, &[1, 0]);
    let mut body = material(&s, 0)
        .into_difference_wave(current(&p), current(&c))
        .unwrap();
    body.advance().unwrap();
    let previous = body.previous().snapshot();
    let joining = body.current().snapshot();
    let measured = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                3,
                2,
                ResidentGrain(0),
                i64::BITS,
                [1, 0, 2, 0, 4, 0].into_iter().map(|v| (v, v)).collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let field = ResidentConstitutiveSection::integers(&measured)
        .unwrap()
        .differences(&s)
        .unwrap();
    let reads = s.census().section_read_outs;
    let developed = body
        .develop_section(field.source(), field.observed())
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(body.previous().same_occurrence(&previous));
    assert!(body.current().same_occurrence(&joining));
    assert!(developed.rebased_joint_enclosure);
    assert_eq!(body.epoch(), 1);
    assert_eq!(body.steps(), 0);
    assert_eq!(developed.successor_fibre.material_observations, 4);
    assert_eq!(developed.predecessor_fibre.material_observations, 3);
    assert!(developed.successor_fibre.initial_joint().is_some());
    let saved = body.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    assert_eq!(bytes[b"HOLONIC-NORMAL-WAVE".len()], 3);
    let next = body.advance().unwrap();
    assert!(next.previous.same_occurrence(&joining));
    // The source (1,2,1), target 2 changes (0,-1/2,0) into (3/8,1/4,3/8).
    // On the actual source (-1/2,1/2,1), the change is 5/16 and current is 13/16.
    contains(&next.current.view().inspect().unwrap(), &[wave(13, 0, 16)]);
    let expected = serde_json::to_value(next.inspect().unwrap()).unwrap();
    drop(next);
    drop(developed);
    drop(body);
    let loaded = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(loaded, saved);
    let mut resumed = loaded.remount(&s, |_| {}).unwrap();
    assert_eq!(
        serde_json::to_value(resumed.advance().unwrap().inspect().unwrap()).unwrap(),
        expected
    );
    let changed = resumed
        .develop_section(field.source(), field.observed())
        .unwrap();
    assert!(changed.rebased_joint_enclosure);
    drop(changed);
    let before = resumed.rest().unwrap();
    let bad = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), i64::BITS, vec![(0, 1), (0, 0)])
                .unwrap(),
        )
        .unwrap();
    assert!(
        resumed
            .develop_section(
                field.source(),
                ResidentConstitutiveSection::integers(&bad).unwrap()
            )
            .is_err()
    );
    assert_eq!(resumed.rest().unwrap(), before);
    let untouched = resumed.current().snapshot();
    let developed = resumed
        .develop_section(field.source(), field.observed())
        .unwrap();
    assert!(!developed.rebased_joint_enclosure);
    assert!(resumed.current().same_occurrence(&untouched));
    drop(developed);
    let residency = s.census().resident_octets_now;
    for _ in 0..4 {
        resumed
            .develop_section(field.source(), field.observed())
            .unwrap();
        assert_eq!(s.census().resident_octets_now, residency);
    }
    resumed.advance().unwrap();
    let before = resumed.rest().unwrap();
    let mut corrupt = s.detach_section(&resumed.joint, i64::BITS).unwrap();
    let last = corrupt.intervals.len() - 1;
    corrupt.intervals[last] = (-1, -1);
    resumed.joint = Rc::new(s.mount_section_rest(&corrupt).unwrap());
    assert!(
        resumed
            .develop_section(field.source(), field.observed())
            .is_err()
    );
    assert_eq!(resumed.rest().unwrap(), before);
}
