use super::super::comparison_tests::{current, point};
use super::super::family::tests::{body, law};
use super::*;
use crate::{
    embedding_fiber::ResidentReadout, native_ecology::constitutive_fibre::ConditionContactMetric,
};
fn coupled<'c>(s: &'c ResidentSurface<'c>) -> ResidentNormalWave<'c, NormalWaveCoupled<'c>> {
    let h = point(s, &[1, 0]);
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law(s, false)],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    body(s).with_neighborhood(neighborhood).unwrap()
}
fn face(w: &NormalWaveFamily<'_>) -> Vec<Rat> {
    w.read_receiver()
        .unwrap()
        .inspect()
        .unwrap()
        .projected_joint
        .unwrap()
}
fn r(n: i64) -> Rat {
    Rat::from_integer(n.into())
}
#[test]
#[ignore = "requires CUDA; coupled generation follows L on the complete family, preserving one owner and the M bank"]
fn coupled_generation_owns_its_family_and_expires_source_admissions() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = coupled(&s);
    let bank = wave.material.rest().unwrap();
    let h = wave.admit_contact(0).unwrap();
    let reads = s.census().section_read_outs;
    let step = wave.advance_contact(&h).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(std::ptr::eq(step.successor(), wave.current()));
    assert_eq!(wave.epoch(), 1);
    assert_eq!(face(wave.current()), vec![r(2), r(1), r(3), r(2)]);
    assert_eq!(wave.material.rest().unwrap(), bank);
    assert_eq!(wave.normal_source_epoch(), 0);
    assert!(wave.advance_contact(&h).is_err());
    let foreign = coupled(&s);
    assert!(foreign.read_contact(&h).is_err());
    let h = wave.admit_contact(0).unwrap();
    wave.advance_contact(&h).unwrap();
    assert_eq!(face(wave.current()), vec![r(3), r(2), r(4), r(3)]);
}
#[test]
#[ignore = "requires CUDA; a real point source changes condition and successor together without normal deposition"]
fn coupled_source_return_changes_condition_and_joint_atomically() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = coupled(&s);
    let contact = wave.admit_contact(0).unwrap();
    let x = point(&s, &[1, 0, 1, 0, 0, 0]);
    let eta = point(&s, &[2, 0]);
    let bank = wave.material.rest().unwrap();
    let before = wave.neighborhood().rest().unwrap();
    let reads = s.census().section_read_outs;
    let returned = wave
        .receive_contact_source(&contact, current(&x), current(&eta))
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(returned.step.successor_epoch, 1);
    assert!(std::ptr::eq(wave.current(), returned.step.successor()));
    assert_eq!(face(wave.current()), vec![r(2), r(1), r(4), r(3)]);
    assert_ne!(wave.neighborhood().rest().unwrap(), before);
    assert_eq!(wave.material.rest().unwrap(), bank);
    assert!(wave
        .current()
        .last_relation()
        .unwrap()
        .same_producing_cut(&wave.neighborhood().read_wave_relation(0, 1, None).unwrap()));
}
#[test]
#[ignore = "requires CUDA; a late arithmetic refusal discards both prepared condition and member material"]
fn coupled_late_refusal_preserves_both_predecessors() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = coupled(&s);
    let contact = wave.admit_contact(0).unwrap();
    let x = point(&s, &[1, 0, 1, 0, 0, 0]);
    let eta = point(&s, &[i64::MAX, 0]);
    let bank = wave.material.rest().unwrap();
    let neighborhood = wave.neighborhood().rest().unwrap();
    let family = serde_json::to_vec(&wave.current().affine_relation().rest().unwrap()).unwrap();
    let error = wave
        .receive_contact_source(&contact, current(&x), current(&eta))
        .err()
        .expect("wide coupled composition must refuse");
    assert!(
        matches!(error, ConstitutiveFibreError::Arithmetic(_)),
        "{error:?}"
    );
    assert_eq!(wave.epoch(), 0);
    assert_eq!(wave.neighborhood().rest().unwrap(), neighborhood);
    assert_eq!(wave.material.rest().unwrap(), bank);
    assert_eq!(
        serde_json::to_vec(&wave.current().affine_relation().rest().unwrap()).unwrap(),
        family
    );
    wave.advance_contact(&contact).unwrap();
    assert_eq!(wave.epoch(), 1);
}

fn wire(w: &ResidentNormalWave<'_, NormalWaveCoupled<'_>>) -> Vec<u8> {
    let mut out = Vec::new();
    w.rest().unwrap().write(&mut out).unwrap();
    out
}
#[test]
#[ignore = "requires CUDA; complete coupled rest binds live contacts to the restored member and actual current"]
fn coupled_rest_retains_contacts_and_the_next_whole_successor() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut wave = coupled(&s);
    let h = wave.admit_contact(0).unwrap();
    wave.advance_contact(&h).unwrap();
    let h = wave.admit_contact(0).unwrap();
    let bytes = wire(&wave);
    let rest = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert!(rest.is_coupled());
    assert_eq!(rest.epoch(), 1);
    assert!(NormalWaveRest::read_normal(&mut bytes.as_slice(), bytes.len() as u64).is_err());
    let mut restored = rest.remount_coupled(&s, |_| {}).unwrap();
    assert_eq!(wire(&restored), bytes);
    assert!(restored.advance_contact(&h).is_err());
    let rh = restored.contact(h.id()).unwrap();
    wave.advance_contact(&h).unwrap();
    restored.advance_contact(&rh).unwrap();
    assert_eq!(wire(&wave), wire(&restored));
    assert_eq!(face(wave.current()), face(restored.current()));
}
#[test]
#[ignore = "requires CUDA; unsupported contact and a malformed observed source preserve the complete body"]
fn coupled_domain_and_source_plane_refusals_preserve_complete_rest() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let h = point(&s, &[1, 0]);
    let unlearned=crate::native_ecology::constitutive_fibre::ResidentConstitutiveFibre::found_bilinear_contact(&s,3,1,1).unwrap();
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![unlearned],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut absent = body(&s).with_neighborhood(neighborhood).unwrap();
    let contact = absent.admit_contact(0).unwrap();
    let before = wire(&absent);
    let proposed = absent.read_contact(&contact).unwrap();
    assert_eq!(
        proposed.read_receiver().unwrap().inspect().unwrap().support,
        NormalFamilySupport::EmptyAffineRelation
    );
    assert!(absent.advance_contact(&contact).is_err());
    assert_eq!(wire(&absent), before);
    let mut wave = coupled(&s);
    let contact = wave.admit_contact(0).unwrap();
    let before = wire(&wave);
    let malformed = point(&s, &[2, 0, 1, 0, 0, 0]);
    let eta = point(&s, &[1, 0]);
    assert!(wave
        .receive_contact_source(&contact, current(&malformed), current(&eta))
        .is_err());
    assert_eq!(wire(&wave), before);
}
#[test]
#[ignore = "requires CUDA; a process restores both pending normal comparisons and current conditional admissions"]
fn coupled_rest_crosses_process_exit_with_pending_normal_and_conditional_returns() {
    const INPUT: &str = "HOLONICS_COUPLED_REST_INPUT";
    const OUTPUT: &str = "HOLONICS_COUPLED_REST_OUTPUT";
    fn follow<'c>(
        s: &'c ResidentSurface<'c>,
        wave: &mut ResidentNormalWave<'c, NormalWaveCoupled<'c>>,
        contact_id: u64,
        normal_id: u64,
    ) {
        let x = point(s, &[1, 0, 1, 0, 0, 0]);
        let eta = point(s, &[2, 0]);
        let observed = point(s, &[3, 2]);
        let h = wave.contact(contact_id).unwrap();
        wave.receive_contact_source(&h, current(&x), current(&eta))
            .unwrap();
        let epoch = wave.epoch();
        let family = Rc::clone(&wave.continuation.current);
        let normal = wave.pending_prediction(normal_id).unwrap();
        wave.receive_prediction(&normal, current(&observed))
            .unwrap();
        assert_eq!(wave.epoch(), epoch);
        assert!(Rc::ptr_eq(&family, &wave.continuation.current));
        let h = wave.admit_contact(0).unwrap();
        wave.advance_contact(&h).unwrap();
    }
    if let Some(path) = std::env::var_os(INPUT) {
        let bytes = std::fs::read(path).unwrap();
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let mut wave = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
            .unwrap()
            .remount_coupled(&s, |_| {})
            .unwrap();
        follow(
            &s,
            &mut wave,
            std::env::var("HOLONICS_COUPLED_CONTACT")
                .unwrap()
                .parse()
                .unwrap(),
            std::env::var("HOLONICS_COUPLED_NORMAL")
                .unwrap()
                .parse()
                .unwrap(),
        );
        std::fs::write(std::env::var_os(OUTPUT).unwrap(), wire(&wave)).unwrap();
        return;
    }
    let (before, expected, contact_id, normal_id) = {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let mut base = body(&s);
        let normal = base.predict().unwrap().handle;
        let h = point(&s, &[1, 0]);
        let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
            vec![law(&s, false)],
            current(&h),
            ConditionContactMetric::UnitAdmittanceRealification,
        )
        .unwrap();
        let mut wave = base.with_neighborhood(neighborhood).unwrap();
        let c = wave.admit_contact(0).unwrap();
        let before = wire(&wave);
        follow(&s, &mut wave, c.id(), normal.id());
        (before, wire(&wave), c.id(), normal.id())
    };
    let dir = std::env::temp_dir().join(format!("holonics-coupled-process-{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let input = dir.join("input.wave");
    let output = dir.join("output.wave");
    std::fs::write(&input, before).unwrap();
    let status=std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact","native_ecology::constitutive_fibre::field::material_transport::normal::direct::wave::coupled::tests::coupled_rest_crosses_process_exit_with_pending_normal_and_conditional_returns","--ignored","--test-threads=1"])
        .env(INPUT,&input).env(OUTPUT,&output).env("HOLONICS_COUPLED_CONTACT",contact_id.to_string()).env("HOLONICS_COUPLED_NORMAL",normal_id.to_string()).output().unwrap();
    assert!(
        status.status.success(),
        "child: {}\n{}",
        String::from_utf8_lossy(&status.stdout),
        String::from_utf8_lossy(&status.stderr)
    );
    assert_eq!(std::fs::read(&output).unwrap(), expected);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
#[ignore = "requires CUDA; changed condition affects a dependent future while preserving an independent receiver at the same source"]
fn coupled_condition_return_separates_dependent_and_independent_receivers() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let h = point(&s, &[1, 0]);
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![law(&s, false), law(&s, true)],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut wave = body(&s).with_neighborhood(neighborhood).unwrap();
    let dependent = wave.admit_contact(0).unwrap();
    let independent = wave.admit_contact(1).unwrap();
    let before_dep = wave.read_contact(&dependent).unwrap();
    let before_ind = wave.read_contact(&independent).unwrap();
    let source = Rc::clone(&wave.continuation.current);
    let x = point(&s, &[1, 0, 1, 0, 0, 0]);
    let eta = point(&s, &[2, 0]);
    wave.receive_contact_source(&dependent, current(&x), current(&eta))
        .unwrap();
    let after_dep = source
        .read_through(Rc::new(
            wave.neighborhood().read_wave_relation(0, 1, None).unwrap(),
        ))
        .unwrap();
    let after_ind = source
        .read_through(Rc::new(
            wave.neighborhood().read_wave_relation(1, 1, None).unwrap(),
        ))
        .unwrap();
    assert_ne!(face(&before_dep), face(&after_dep));
    assert_eq!(face(&before_ind), face(&after_ind));
    assert_eq!(
        before_ind.affine_relation().rest().unwrap(),
        after_ind.affine_relation().rest().unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; actual source reception forms a new local row and admits its bounded successor from an empty relation"]
fn coupled_reception_forms_material_before_admitting_the_new_current() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let h = point(&s, &[1, 0]);
    let unlearned=crate::native_ecology::constitutive_fibre::ResidentConstitutiveFibre::found_bilinear_contact(&s,3,1,1).unwrap();
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![unlearned],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut wave = body(&s).with_neighborhood(neighborhood).unwrap();
    let contact = wave.admit_contact(0).unwrap();
    let x = point(&s, &[1, 1, 2, 1, 1, 0]);
    let eta = point(&s, &[1, 0]);
    assert_eq!(wave.neighborhood().rest().unwrap().laws()[0].rank(), 0);
    assert!(wave.advance_contact(&contact).is_err());
    let bank = wave.material.rest().unwrap();
    let returned = wave
        .receive_contact_source(&contact, current(&x), current(&eta))
        .unwrap();
    assert_eq!(wave.neighborhood().rest().unwrap().laws()[0].rank(), 1);
    assert_eq!(face(wave.current()), vec![r(2), r(1), r(3), r(1)]);
    assert_eq!(wave.material.rest().unwrap(), bank);
    assert!(!returned
        .step
        .contact
        .relation()
        .same_producing_cut(returned.step.applied_relation()));
    let saved = wire(&wave);
    let restored = NormalWaveRest::read(&mut saved.as_slice(), saved.len() as u64)
        .unwrap()
        .remount_coupled(&s, |_| {})
        .unwrap();
    assert_eq!(wire(&restored), saved);
}

// This local specimen is learned from actual declared unit-source rows; the receiver chart
// must lift its response to raw currents with different common real offsets.
fn unit_swap<'c>(
    s: &'c ResidentSurface<'c>,
) -> crate::native_ecology::constitutive_fibre::ResidentConstitutiveFibre<'c> {
    use crate::native_ecology::constitutive_fibre::ResidentConstitutiveFibre;
    let mut law = ResidentConstitutiveFibre::found_bilinear_contact(s, 6, 1, 2).unwrap();
    let h = point(s, &[1, 0]);
    for p in [[1, 0, 0, 0], [0, 0, 1, 0]] {
        for c in [[1, 0, 0, 0], [0, 0, 1, 0]] {
            let mut source = [0; 12];
            for j in 0..4 {
                source[j] = c[j] - p[j];
                source[4 + j] = c[j];
                source[8 + j] = p[j];
            }
            let x = point(s, &source);
            let eta = point(s, &[c[2] - c[0], 0, c[0] - c[2], 0]);
            law.advance_bilinear_contact(current(&x), current(&h), Some(current(&eta)))
                .unwrap();
        }
    }
    law
}
#[test]
#[ignore = "requires CUDA; declared unit-real-sum chart transports the full offset fibre and survives rest"]
fn coupled_unit_real_sum_lifts_source_offsets_and_retains_chart() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let material = ResidentNormalMaterial::found(&s, 2, 2, ResidentGrain(32)).unwrap();
    let p = point(&s, &[4, 0, 2, 0]);
    let c = point(&s, &[7, 0, 3, 0]);
    let h = point(&s, &[1, 0]);
    let body = material
        .into_applied_difference_wave(current(&p), current(&c))
        .unwrap();
    let neighborhood = ResidentGeneratorNeighborhood::with_shared_condition(
        vec![unit_swap(&s)],
        current(&h),
        ConditionContactMetric::UnitAdmittanceRealification,
    )
    .unwrap();
    let mut wave = body.with_neighborhood(neighborhood).unwrap();
    let direct = wave.admit_contact(0).unwrap();
    let before = wave.rest().unwrap();
    assert!(wave.advance_contact(&direct).is_err());
    assert_eq!(wave.rest().unwrap(), before);
    let contact = wave
        .admit_contact_in_chart(0, WaveSourceReceiver::UnitRealSum)
        .unwrap();
    let reads = s.census().section_read_outs;
    wave.advance_contact(&contact).unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert_eq!(
        face(wave.current()),
        vec![r(7), r(0), r(3), r(0), r(3), r(0), r(7), r(0)]
    );
    let chart = wave.current().last_relation().unwrap();
    assert_eq!(chart.source_receiver(), WaveSourceReceiver::UnitRealSum);
    chart.rest().unwrap().validate().unwrap();
    // Every affine row has the same swap law, including directions that vary the raw offset.
    let inspected = wave.current().affine_relation().inspect().unwrap();
    if let ConstitutiveReading::Plural {
        particular,
        directions,
    } = inspected.predecessor_reading
    {
        for row in std::iter::once(&particular).chain(directions.iter()) {
            assert_eq!(row[14], row[8]);
            assert_eq!(row[16], row[6]);
            assert_eq!(row[10], row[6]);
            assert_eq!(row[12], row[8]);
        }
    } else {
        panic!("expected complete affine family");
    }
    let mut bytes = Vec::new();
    wave.rest().unwrap().write(&mut bytes).unwrap();
    let restored = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    let mut restored = restored.remount_coupled(&s, |_| {}).unwrap();
    assert_eq!(face(restored.current()), face(wave.current()));
    let next = restored
        .admit_contact_in_chart(0, WaveSourceReceiver::UnitRealSum)
        .unwrap();
    restored.advance_contact(&next).unwrap();
    assert_eq!(
        face(restored.current()),
        vec![r(3), r(0), r(7), r(0), r(7), r(0), r(3), r(0)]
    );
    // Invalid observed source, and a valid source with nonconserving return, both preserve owner.
    let next = restored
        .admit_contact_in_chart(0, WaveSourceReceiver::UnitRealSum)
        .unwrap();
    let before = restored.rest().unwrap();
    let wrong = point(&s, &[0; 12]);
    let eta = point(&s, &[1, 0, 0, 0]);
    assert!(restored
        .receive_contact_source(&next, current(&wrong), current(&eta))
        .is_err());
    assert_eq!(restored.rest().unwrap(), before);
    let source = point(&s, &[0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]);
    assert!(restored
        .receive_contact_source(&next, current(&source), current(&eta))
        .is_err());
    assert_eq!(restored.rest().unwrap(), before);
}
