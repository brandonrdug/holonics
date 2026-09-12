//! Regression witness for a delayed coupled return after two different intermediate paths.
//!
//! This specifies the native
//! separating case for the continuation owner: the pending source and producing family are
//! identical, while the contemporary current has retained `+r` on one path and `-r` on the
//! other.  Marginal receiver readings therefore cannot recover the joint.
use super::super::comparison_tests::{current, point};
use super::super::family::tests::body;
use super::*;
use crate::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConditionContactMetric, ResidentConstitutiveFibre, WaveSourceReceiver,
    },
};

fn calibrated<'c>(s: &'c ResidentSurface<'c>, mode: usize) -> ResidentConstitutiveFibre<'c> {
    let mut result = ResidentConstitutiveFibre::found_bilinear_contact(s, 3, 1, 1).unwrap();
    let mut sources = vec![[0i64; 6]];
    for j in 0..6 {
        let mut a = [0; 6];
        a[j] = 1;
        sources.push(a);
    }
    for a in sources {
        for h in [[0, 0], [1, 0], [0, 1]] {
            let eta = match mode {
                0 => [a[0] * h[0] - a[1] * h[1], a[0] * h[1] + a[1] * h[0]],
                1 => [0, 0],
                _ => [-2 * a[2], 0],
            };
            result
                .advance_bilinear_contact(
                    current(&point(s, &a)),
                    current(&point(s, &h)),
                    Some(current(&point(s, &eta))),
                )
                .unwrap();
        }
    }
    // Member zero additionally admits the pure-real vertical source-null direction.
    if mode == 0 {
        result
            .advance_bilinear_contact(
                current(&point(s, &[0, 0, 0, 0, 0, 0])),
                current(&point(s, &[1, 0])),
                Some(current(&point(s, &[1, 0]))),
            )
            .unwrap();
    }
    result
}

fn world<'c>(s: &'c ResidentSurface<'c>) -> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![calibrated(s, 0), calibrated(s, 1), calibrated(s, 2)],
        current(&point(s, &[1, 0])),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    body(s).with_neighborhood(neighborhood).unwrap()
}

fn affine(w: &NormalWaveFamily<'_>) -> ConstitutiveReading {
    w.affine_relation().inspect().unwrap().predecessor_reading
}

#[test]
#[ignore = "requires CUDA; continuation owner must retain ordered intermediate joint paths"]
fn delayed_joint_separates_same_marginals_after_member_paths_diverge() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut plus = world(&s);
    let mut minus = world(&s);

    // The producing source and produced family are the same before either path diverges.
    let p0 = plus
        .admit_contact_in_chart(0, WaveSourceReceiver::Direct)
        .unwrap();
    let m0 = minus
        .admit_contact_in_chart(0, WaveSourceReceiver::Direct)
        .unwrap();
    plus.advance_contact(&p0).unwrap();
    minus.advance_contact(&m0).unwrap();
    let p1 = plus.admit_contact(1).unwrap();
    let m1 = minus.admit_contact(1).unwrap();
    let pp = plus.predict_contact(&p1).unwrap();
    let mp = minus.predict_contact(&m1).unwrap();
    assert_eq!(
        pp.step.source().rest().unwrap(),
        mp.step.source().rest().unwrap()
    );
    assert_eq!(
        pp.step.successor().rest().unwrap(),
        mp.step.successor().rest().unwrap()
    );
    let handle_p = pp.handle;
    let handle_m = mp.handle;

    // Both worlds retain the same pending producing cut, then choose different successors.
    let p1 = plus.admit_contact(1).unwrap();
    plus.advance_contact(&p1).unwrap();
    let m2 = minus.admit_contact(2).unwrap();
    minus.advance_contact(&m2).unwrap();
    assert_eq!(
        plus.pending_coupled_prediction_ids().collect::<Vec<_>>(),
        vec![handle_p.id()]
    );
    assert_eq!(
        minus.pending_coupled_prediction_ids().collect::<Vec<_>>(),
        vec![handle_m.id()]
    );

    // The same contemporary observation closes both paths.  The final marginals agree, but
    // the retained pending-source/current joint must distinguish +r from -r.
    let observed = point(&s, &[5, 0]);
    let pc = plus.admit_contact(1).unwrap();
    let mc = minus.admit_contact(1).unwrap();
    plus.receive_contact_next(&pc, current(&observed)).unwrap();
    minus.receive_contact_next(&mc, current(&observed)).unwrap();
    assert_eq!(affine(plus.current()), affine(minus.current()));
    assert_ne!(
        plus.rest().unwrap(),
        minus.rest().unwrap(),
        "pending source/current orientation was lost"
    );
    let word_p = plus.pending_coupled_continuation(&handle_p).unwrap();
    let word_m = minus.pending_coupled_continuation(&handle_m).unwrap();
    assert_eq!(word_p.passages(), 3);
    assert_eq!(
        word_p.factors().map(|(e, _)| e).collect::<Vec<_>>(),
        vec![2, 3, 4]
    );
    assert_ne!(
        word_p.factors().nth(1).unwrap().1.rest().unwrap(),
        word_m.factors().nth(1).unwrap().1.rest().unwrap()
    );
    let saved = plus.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let restored = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
        .unwrap()
        .remount_coupled(&s, |_| {})
        .unwrap();
    assert_eq!(restored.rest().unwrap(), saved);
    assert!(restored.pending_coupled_continuation(&handle_p).is_err());
    let restored_handle = restored.pending_coupled_prediction(handle_p.id()).unwrap();
    assert_eq!(
        restored
            .pending_coupled_continuation(&restored_handle)
            .unwrap()
            .factors()
            .count(),
        3
    );
    plus.release_coupled_prediction(&handle_p).unwrap();
    assert!(plus.continuation.transport.is_empty());
    assert!(plus.pending_coupled_continuation(&handle_p).is_err());
}

#[test]
#[ignore = "requires CUDA; one source-field occurrence retains all internal maps in the pending joint"]
fn pending_continuation_retains_internal_factors_and_prunes_only_released_prefix() {
    use crate::native_ecology::constitutive_fibre::ResidentConstitutiveSection;
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = world(&s);
    let contact = wave.admit_contact(1).unwrap();
    let first = wave.predict_contact(&contact).unwrap().handle;
    let source = s
        .mount_section_rest(
            &ResidentSectionRest::found(
                4,
                2,
                ResidentGrain(0),
                64,
                [0, 0, 1, 0, 2, 0, 1, 0]
                    .into_iter()
                    .map(|v| (v, v))
                    .collect(),
            )
            .unwrap(),
        )
        .unwrap();
    let contact = wave.admit_contact(0).unwrap();
    let reads = s.census().section_read_outs;
    wave.actuate_contact_section(
        &contact,
        ResidentConstitutiveSection::integers(&source).unwrap(),
    )
    .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    let word = wave.pending_coupled_continuation(&first).unwrap();
    assert_eq!(word.passages(), 2);
    assert_eq!(
        word.factors().map(|(e, _)| e).collect::<Vec<_>>(),
        vec![1, 2, 2, 2]
    );
    assert_eq!(
        word.factors()
            .skip(1)
            .map(|(_, m)| m.source_contact().unwrap().source_row())
            .collect::<Vec<_>>(),
        vec![Some(0), Some(1), Some(2)]
    );
    let contact = wave.admit_contact(1).unwrap();
    let second = wave.predict_contact(&contact).unwrap().handle;
    let saved = wave.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let mut restored = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
        .unwrap()
        .remount_coupled(&s, |_| {})
        .unwrap();
    assert_eq!(restored.rest().unwrap(), saved);
    wave.release_coupled_prediction(&first).unwrap();
    assert_eq!(
        wave.continuation
            .transport
            .keys()
            .copied()
            .collect::<Vec<_>>(),
        vec![3]
    );
    assert_eq!(
        wave.pending_coupled_continuation(&second)
            .unwrap()
            .factors()
            .count(),
        1
    );
    let h = restored.pending_coupled_prediction(first.id()).unwrap();
    restored.release_coupled_prediction(&h).unwrap();
    assert_eq!(restored.rest().unwrap(), wave.rest().unwrap());
}
