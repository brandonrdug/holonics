use super::super::super::comparison_tests::{current, point};
use super::super::super::family::tests::{body, law};
use super::super::comparison::joint::tests::source_parameters_at;
use super::*;
use crate::{
    embedding_fiber::ResidentReadout, native_ecology::constitutive_fibre::ConditionContactMetric,
};
fn r(n: i64, d: i64) -> Rat {
    Rat::new(n.into(), d.into())
}
fn world<'c>(
    s: &'c ResidentSurface<'c>,
    free: bool,
) -> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    let h = point(s, &[1, 0]);
    let mut local = law(s, false);
    if free {
        local
            .advance_bilinear_contact(
                current(&point(s, &[0; 6])),
                current(&h),
                Some(current(&point(s, &[1, 0]))),
            )
            .unwrap();
    }
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![local],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    body(s).with_neighborhood(neighborhood).unwrap()
}
fn face(model: &mut ResidentCoupledConstitutive<'_>) -> Vec<Rat> {
    model
        .read_receiver()
        .unwrap()
        .successor_section()
        .read_receiver()
        .unwrap()
        .inspect()
        .unwrap()
        .projected_joint
        .unwrap()
}
#[test]
#[ignore = "requires CUDA; owned dependent return persists and the next source uses its actual changed material/current"]
fn owned_constitutive_cycle_publishes_consumes_and_continues() {
    const CHILD: &str = "HOLONICS_OWNED_CONSTITUTIVE_RESUME";
    if let Some(path) = std::env::var_os(CHILD) {
        let directory = std::path::PathBuf::from(path);
        let mut file = std::fs::File::open(directory.join("before.family")).unwrap();
        let len = file.metadata().unwrap().len();
        let saved = CoupledConstitutiveRest::read(&mut file, len).unwrap();
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let mut model = saved.remount(&s).unwrap();
        assert_eq!(
            face(&mut model),
            vec![r(31, 5), r(0, 1), r(82, 5), r(-4, 1)]
        );
        let source = s
            .mount_exact_rational_packet(&[1, 0, 2, 0, 1, 0].map(|v| r(v, 1)))
            .unwrap();
        model
            .actuate_source(0, WaveSourceReceiver::Direct, source)
            .unwrap();
        assert_eq!(
            face(&mut model),
            vec![r(43, 10), r(0, 1), r(63, 5), r(-4, 1)]
        );
        model
            .rest()
            .unwrap()
            .write(&mut std::fs::File::create(directory.join("after.family")).unwrap())
            .unwrap();
        return;
    }
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = world(&s, false);
    let contact = wave.admit_contact(0).unwrap();
    let handle = wave.predict_contact(&contact).unwrap().handle;
    let observation = point(&s, &[4, 3]);
    let comparison = wave
        .compare_coupled_prediction(&handle, current(&observation))
        .unwrap();
    let contact = wave.admit_contact(0).unwrap();
    wave.receive_contact_next(&contact, current(&point(&s, &[10, 0])))
        .unwrap();
    let theta = source_parameters_at(&comparison, &[1, 0, 2, 1], &[1, 0, 2, 1]);
    let receiver = s.mount_exact_rational_packet(&theta).unwrap();
    let old_epoch = wave.epoch();
    let reads = s.census().section_read_outs;
    let mut model = wave
        .into_constitutive_continuation(comparison, receiver)
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(model.epoch(), old_epoch + 1);
    assert_eq!(model.consumed_prediction(), handle.id());
    assert!(model.pending_prediction(handle.id()).is_err());
    assert_eq!(model.pending_prediction_ids().count(), 0);
    assert_eq!(
        face(&mut model),
        vec![r(10, 1), r(0, 1), r(24, 1), r(-4, 1)]
    );
    let before = model.rest().unwrap();
    assert_eq!(
        face(&mut model),
        vec![r(10, 1), r(0, 1), r(24, 1), r(-4, 1)]
    );
    assert_eq!(model.rest().unwrap(), before);
    let source = s
        .mount_exact_rational_packet(&[1, 0, 2, 0, 1, 0].map(|v| r(v, 1)))
        .unwrap();
    let reads = s.census().section_read_outs;
    model
        .actuate_source(0, WaveSourceReceiver::Direct, source)
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    // Existing passive union: x=(1,0,2,0), y=(2,0,4,0), D=20,
    // A=I-(x-y)(x-y)^T/10; y+A(10,0,24,-4)=(31/5,0,82/5,-4).
    let expected = vec![r(31, 5), r(0, 1), r(82, 5), r(-4, 1)];
    assert_eq!(face(&mut model), expected);
    assert_eq!(model.epoch(), old_epoch + 2);
    assert_eq!(model.source_passages(), 1);
    let saved = model.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let mut remounted = CoupledConstitutiveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
        .unwrap()
        .remount(&s)
        .unwrap();
    assert_eq!(remounted.rest().unwrap(), saved);
    assert_eq!(face(&mut remounted), expected);
    let directory = std::env::temp_dir().join(format!(
        "holonics-owned-constitutive-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&directory).unwrap();
    saved
        .write(&mut std::fs::File::create(directory.join("before.family")).unwrap())
        .unwrap();
    let child=std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact","native_ecology::constitutive_fibre::field::material_transport::normal::direct::wave::coupled::dependent::tests::owned_constitutive_cycle_publishes_consumes_and_continues","--ignored","--test-threads=1"])
        .env(CHILD,&directory).output().unwrap();
    assert!(
        child.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&child.stdout),
        String::from_utf8_lossy(&child.stderr)
    );
    let source = s
        .mount_exact_rational_packet(&[1, 0, 2, 0, 1, 0].map(|v| r(v, 1)))
        .unwrap();
    remounted
        .actuate_source(0, WaveSourceReceiver::Direct, source)
        .unwrap();
    let mut after = std::fs::File::open(directory.join("after.family")).unwrap();
    let len = after.metadata().unwrap().len();
    let child_rest = CoupledConstitutiveRest::read(&mut after, len).unwrap();
    assert_eq!(child_rest, remounted.rest().unwrap());
    assert_eq!(
        face(&mut remounted),
        vec![r(43, 10), r(0, 1), r(63, 5), r(-4, 1)]
    );
    let after_second = remounted.rest().unwrap();
    assert!(remounted.pending_prediction(handle.id()).is_err());
    let bad = s
        .mount_exact_rational_packet(&[1, 0, 2, 0, 0, 0].map(|v| r(v, 1)))
        .unwrap();
    let refused = remounted
        .actuate_source(0, WaveSourceReceiver::Direct, bad)
        .unwrap_err();
    assert!(matches!(
        refused.reason,
        ConstitutiveFibreError::Arithmetic(_)
    ));
    assert_eq!(remounted.rest().unwrap(), after_second);
    eprintln!(
        "owned dependent epoch={} source_passages={} next={expected:?}",
        model.epoch(),
        model.source_passages()
    );
}

#[test]
#[ignore = "requires CUDA; the unit-sum chart remains a unit-sum family after constitutive publication"]
fn owned_constitutive_cycle_keeps_unit_sum_receiver() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let p = point(&s, &[1, 0, 0, 0]);
    let c = point(&s, &[0, 0, 1, 0]);
    let h = point(&s, &[1, 0]);
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![super::super::tests::unit_swap(&s)],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut wave = ResidentNormalMaterial::found(&s, 2, 2, ResidentGrain(32))
        .unwrap()
        .into_applied_difference_wave(current(&p), current(&c))
        .unwrap()
        .with_neighborhood(neighborhood)
        .unwrap();
    let contact = wave
        .admit_contact_in_chart(0, WaveSourceReceiver::UnitRealSum)
        .unwrap();
    let handle = wave.predict_contact(&contact).unwrap().handle;
    let comparison = wave
        .compare_coupled_prediction(&handle, current(&c))
        .unwrap();
    let next_contact=wave.admit_contact_in_chart(0,WaveSourceReceiver::UnitRealSum).unwrap();
    let other_pending=wave.predict_contact(&next_contact).unwrap().handle;
    let coords = [1, 0, 0, 0, 0, 0, 1, 0];
    let theta = source_parameters_at(&comparison, &coords, &coords);
    let receiver = s.mount_exact_rational_packet(&theta).unwrap();
    let mut model = wave
        .into_constitutive_continuation(comparison, receiver)
        .unwrap();
    assert_eq!(model.pending_prediction_ids().collect::<Vec<_>>(),vec![other_pending.id()]);
    assert!(model.pending_prediction(other_pending.id()).is_ok());
    let view = face(&mut model);
    assert_eq!(&view[0] + &view[2], r(1, 1));
    assert_eq!(&view[4] + &view[6], r(1, 1));
    let saved = model.rest().unwrap();
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let mut restored = CoupledConstitutiveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
        .unwrap()
        .remount(&s)
        .unwrap();
    assert_eq!(face(&mut restored), view);
    assert_eq!(restored.pending_prediction_ids().collect::<Vec<_>>(),vec![other_pending.id()]);
}
#[test]
#[ignore = "requires CUDA; publication retains the non-affine family beyond its explicitly declared receiver"]
fn owned_constitutive_cycle_retains_other_source_sections() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = world(&s, true);
    let contact = wave.admit_contact(0).unwrap();
    wave.advance_contact(&contact).unwrap();
    let contact = wave.admit_contact(0).unwrap();
    let handle = wave.predict_contact(&contact).unwrap().handle;
    let observation = point(&s, &[7, 4]);
    let comparison = wave
        .compare_coupled_prediction(&handle, current(&observation))
        .unwrap();
    let a = source_parameters_at(&comparison, &[1, 0, 2, 1], &[2, 1, 3, 2]);
    let b = source_parameters_at(&comparison, &[1, 0, 2, 1], &[2, 1, 4, 2]);
    let outside = source_parameters_at(&comparison, &[9, 0, 2, 1], &[2, 1, 3, 2]);
    let before = wave.rest().unwrap();
    let bad = s.mount_exact_rational_packet(&outside).unwrap();
    let refusal = match wave.into_constitutive_continuation(comparison, bad) {
        Ok(_) => panic!("outside-anchor receiver was admitted"),
        Err(refusal) => refusal,
    };
    assert_eq!(refusal.wave.rest().unwrap(), before);
    let receiver = s.mount_exact_rational_packet(&a).unwrap();
    let mut model = refusal
        .wave
        .into_constitutive_continuation(refusal.comparison, receiver)
        .unwrap();
    assert_eq!(
        model
            .read_receiver()
            .unwrap()
            .inspect_condition()
            .unwrap()
            .successor,
        vec![r(3, 2), r(1, 2)]
    );
    let saved = model.rest().unwrap();
    let alternate = s.mount_exact_rational_packet(&b).unwrap();
    assert_eq!(
        model
            .evaluate(&alternate)
            .unwrap()
            .inspect_condition()
            .unwrap()
            .successor,
        vec![r(6, 5), r(2, 5)]
    );
    assert_eq!(model.rest().unwrap(), saved);
    let mut bytes = Vec::new();
    saved.write(&mut bytes).unwrap();
    let mut restored = CoupledConstitutiveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
        .unwrap()
        .remount(&s)
        .unwrap();
    assert_eq!(
        restored
            .evaluate(&alternate)
            .unwrap()
            .inspect_condition()
            .unwrap()
            .successor,
        vec![r(6, 5), r(2, 5)]
    );
    assert_eq!(restored.rest().unwrap(), model.rest().unwrap());
}
