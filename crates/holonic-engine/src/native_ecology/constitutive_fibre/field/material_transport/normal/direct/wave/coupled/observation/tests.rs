use super::super::super::comparison_tests::{current, point};
use super::super::super::family::tests::{body, law};
use super::*;
use crate::native_ecology::constitutive_fibre::ConditionContactMetric;
use crate::{ExactComplexWaveCurrent, embedding_fiber::ResidentReadout};

fn z(re: i64, im: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(Rat::from_integer(re.into()), Rat::from_integer(im.into()))
}
fn world<'c>(
    s: &'c ResidentSurface<'c>,
    features: bool,
) -> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    let material = if features {
        ResidentNormalMaterial::found_features(s, 7, 1, ResidentGrain(32)).unwrap()
    } else {
        ResidentNormalMaterial::found(s, 1, 1, ResidentGrain(32)).unwrap()
    };
    let compatibility = material.read_applied_bilinear_relation(3, 1).unwrap();
    let laws = if features {
        vec![compatibility, law(s, false)]
    } else {
        vec![compatibility]
    };
    let h = point(s, &[1, 0]);
    let mut local = ResidentGeneratorNeighborhood::with_shared_condition(
        laws,
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    local
        .attach_normal_prediction(0, material)
        .unwrap_or_else(|(_, e)| panic!("{e}"));
    body(s).with_neighborhood(local).unwrap()
}
fn restored<'c>(
    s: &'c ResidentSurface<'c>,
    wave: &ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
) -> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    let saved = wave.rest().unwrap();
    let mut wire = Vec::new();
    saved.write(&mut wire).unwrap();
    NormalWaveRest::read(&mut wire.as_slice(), wire.len() as u64)
        .unwrap()
        .remount_coupled(s, |_| {})
        .unwrap()
}
#[test]
#[ignore = "requires CUDA; an observed mismatch forms normal material at its original source without a wave tick"]
fn observation_changes_normal_geometry_and_preserves_the_historical_current() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = world(&s, false);
    let contact = wave.admit_contact(0).unwrap();
    let predicted = wave.predict_contact(&contact).unwrap();
    let stale = wave.admit_contact(0).unwrap();
    let held = wave.current().rest().unwrap();
    let epoch = wave.epoch();
    let old_law = wave.neighborhood().generator(0).unwrap().rest().unwrap();
    let y = point(&s, &[7, 4]);
    let reads = s.census().section_read_outs;
    let receipt = wave
        .observe_coupled_prediction(&predicted.handle, current(&y))
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(wave.epoch(), epoch);
    assert_eq!(wave.current().rest().unwrap(), held);
    assert_eq!(
        wave.neighborhood().generator(0).unwrap().rest().unwrap(),
        old_law
    );
    assert!(wave.read_contact(&stale).is_err());
    assert_eq!(wave.pending_coupled_predictions(), 0);
    assert_eq!(
        (
            receipt.predecessor_observations,
            receipt.successor_observations
        ),
        (0, 1)
    );
    assert_eq!(
        receipt.source().inspect().unwrap().center,
        vec![z(1, 1), z(2, 1), z(1, 0)]
    );
    assert_eq!(
        receipt.target_increment().inspect().unwrap().center,
        vec![z(5, 3)]
    );
    assert_eq!(
        receipt.discrepancy().inspect().unwrap().center,
        vec![z(5, 3)]
    );
    assert_eq!(receipt.discrepancy().inspect().unwrap().radius, Rat::zero());
    let material = wave
        .neighborhood()
        .predictive_material(0)
        .unwrap()
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(material.cross_source[0], vec![z(8, -2), z(13, 1), z(5, 3)]);
    assert_eq!(material.target_energy, Rat::from_integer(34.into()));
    let mut resumed = restored(&s, &wave);
    assert_eq!(resumed.current().rest().unwrap(), held);
    let a = [z(0, 0), z(2, 1), z(2, 1)];
    let expected = material.material.coefficients[0]
        .iter()
        .zip(&a)
        .fold(z(2, 1), |v, (m, a)| v.add(&m.multiply(a)));
    for body in [&mut wave, &mut resumed] {
        let contact = body.admit_contact(0).unwrap();
        body.advance_contact(&contact).unwrap();
        let actual = body
            .current()
            .read_receiver()
            .unwrap()
            .inspect()
            .unwrap()
            .projected_joint
            .unwrap();
        assert_eq!(
            &actual[2..],
            &[expected.real.clone(), expected.imaginary.clone()]
        );
    }
    assert_eq!(
        wave.current().rest().unwrap(),
        resumed.current().rest().unwrap()
    );
}
#[test]
#[ignore = "requires CUDA; later and earlier observations retain different original source moments"]
fn delayed_observations_use_their_own_sources_across_material_rest() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = world(&s, false);
    let c = wave.admit_contact(0).unwrap();
    let first = wave.predict_contact(&c).unwrap();
    let c = wave.admit_contact(0).unwrap();
    let second = wave.predict_contact(&c).unwrap();
    let y = point(&s, &[9, -3]);
    let receipt = wave
        .observe_coupled_prediction(&second.handle, current(&y))
        .unwrap();
    assert_eq!(
        receipt.source().inspect().unwrap().center,
        vec![z(0, 0), z(2, 1), z(2, 1)]
    );
    assert_eq!(
        receipt.target_increment().inspect().unwrap().center,
        vec![z(7, -4)]
    );
    assert_eq!(wave.pending_coupled_predictions(), 1);
    let mut resumed = restored(&s, &wave);
    let y = point(&s, &[7, 4]);
    let id = first.handle.id();
    for body in [&mut wave, &mut resumed] {
        let epoch = body.epoch();
        let h = body.pending_coupled_prediction(id).unwrap();
        let receipt = body.observe_coupled_prediction(&h, current(&y)).unwrap();
        assert_eq!(
            receipt.source().inspect().unwrap().center,
            vec![z(1, 1), z(2, 1), z(1, 0)]
        );
        assert_eq!(
            receipt.discrepancy().inspect().unwrap().center,
            vec![z(5, 3)]
        );
        assert_eq!(body.epoch(), epoch);
        assert_eq!(body.pending_coupled_predictions(), 0);
        let state = body
            .neighborhood()
            .predictive_material(0)
            .unwrap()
            .unwrap()
            .inspect()
            .unwrap();
        // (5+3i)*conj(a_first) + (7-4i)*conj(a_second).
        assert_eq!(
            state.cross_source[0],
            vec![z(8, -2), z(23, -14), z(15, -12)]
        );
    }
    assert_eq!(wave.rest().unwrap(), resumed.rest().unwrap());
}
#[test]
#[ignore = "requires CUDA; empirical feature formation retains h from the producing cut after condition contact"]
fn observation_features_use_the_original_condition() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = world(&s, true);
    let contact = wave.admit_contact(0).unwrap();
    let predicted = wave.predict_contact(&contact).unwrap();
    let source = point(&s, &[1, 0, 1, 0, 0, 0]);
    let target = point(&s, &[2, 0]);
    let contact = wave.admit_contact(1).unwrap();
    wave.receive_contact_source(&contact, current(&source), current(&target))
        .unwrap();
    let h = wave.neighborhood().condition();
    let values = s.read_out(h.section).unwrap();
    assert_ne!(
        values[h.offset].0,
        values[h.denominator.unwrap()].0,
        "the condition contact must change h before the delayed return"
    );
    let y = point(&s, &[7, 4]);
    let receipt = wave
        .observe_coupled_prediction(&predicted.handle, current(&y))
        .unwrap();
    let state = wave
        .neighborhood()
        .predictive_material(0)
        .unwrap()
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(
        receipt.target_increment().inspect().unwrap().center,
        vec![z(5, 3)]
    );
    assert_eq!(state.cross_source[0][3], z(5, 3)); // h was exactly 1 at production.
    assert_eq!(&state.cross_source[0][4..], &state.cross_source[0][..3]);
}

#[test]
#[ignore = "requires CUDA; fixed complex condition features and unit-real-sum source charts preserve their bounds"]
fn enclosed_features_keep_complex_phase_and_source_chart_offsets() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let grain = ResidentGrain(8);
    let words = [512i128, -256, 64]
        .into_iter()
        .flat_map(|v| [v as i64, (v >> 64) as i64])
        .map(|v| (v, v))
        .collect::<Vec<_>>();
    let section = s
        .mount_section_rest(
            &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words).unwrap(),
        )
        .unwrap();
    let source = ResidentNormalEnclosureView {
        surface: &s,
        section: &section,
        offset: 0,
        width: 2,
        grain,
    };
    let hr = Rat::new((-1).into(), 3.into());
    let hi = Rat::new(2.into(), 3.into());
    let h = s
        .mount_exact_rational_packet(&[hr.clone(), hi.clone()])
        .unwrap();
    let hc = ExactComplexWaveCurrent::new(hr, hi);
    let features = source
        .bilinear_features(ResidentConstitutiveCurrent::rational(&h).unwrap())
        .unwrap()
        .inspect()
        .unwrap();
    for (re, im) in [(1, 0), (-1, 0), (0, 1), (0, -1)] {
        let a = ExactComplexWaveCurrent::new(
            Rat::from_integer(2.into()) + Rat::new(re.into(), 4.into()),
            Rat::from_integer((-1).into()) + Rat::new(im.into(), 4.into()),
        );
        let exact = [a.clone(), hc.clone(), hc.multiply(&a)];
        let error = exact
            .iter()
            .zip(&features.center)
            .map(|(a, b)| {
                let e = a.subtract(b);
                &e.real * &e.real + &e.imaginary * &e.imaginary
            })
            .sum::<Rat>();
        assert!(error <= &features.radius * &features.radius);
    }
    let p = [2, 1, 0, 0, -1, 0, 5, 0, 0, 3, 1, -2];
    let mut shifted = p;
    for j in (0..6).step_by(2) {
        shifted[j] += 5;
        shifted[6 + j] -= 7;
    }
    let first = ResidentNormalInput::from(current(&point(&s, &p)))
        .enclosure(&s, grain)
        .unwrap();
    let second = ResidentNormalInput::from(current(&point(&s, &shifted)))
        .enclosure(&s, grain)
        .unwrap();
    let a = first
        .difference_source_in_chart(WaveSourceReceiver::UnitRealSum)
        .unwrap()
        .inspect()
        .unwrap();
    let b = second
        .difference_source_in_chart(WaveSourceReceiver::UnitRealSum)
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(a, b);
    assert!(a.radius > Rat::zero());
}
