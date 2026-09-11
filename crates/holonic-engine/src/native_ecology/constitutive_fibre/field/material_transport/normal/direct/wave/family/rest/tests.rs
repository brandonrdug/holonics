use super::super::super::comparison_tests::{current, point};
use super::super::tests::{body, law};
use super::*;
use crate::embedding_fiber::ResidentReadout;
fn bytes(f: &NormalWaveFamily<'_>) -> Vec<u8> {
    let mut b = Vec::new();
    f.rest().unwrap().write(&mut b).unwrap();
    b
}
#[test]
#[ignore = "requires CUDA; saved anchored family restores its next conditional passage and receiver"]
fn family_rest_retains_next_passage_and_complete_receiver() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let mut body = super::super::super::comparison_tests::witness(&s);
    body.advance().unwrap();
    body.set_transport(NormalWaveTransport::Applied).unwrap();
    let learned = law(&s, false);
    let h = point(&s, &[0, 1]);
    let start = body.read_family().unwrap();
    let step = start
        .read_through(Rc::new(learned.read_wave_relation(current(&h), 1).unwrap()))
        .unwrap();
    let wire = bytes(&step);
    let rest = NormalWaveFamilyRest::read(&mut wire.as_slice(), wire.len() as u64).unwrap();
    let restored = rest.remount(&s).unwrap();
    assert_eq!(bytes(&restored), wire);
    let a = step.read_receiver().unwrap().inspect().unwrap();
    let b = restored.read_receiver().unwrap().inspect().unwrap();
    assert_eq!(
        serde_json::to_value(a).unwrap(),
        serde_json::to_value(b).unwrap()
    );
    let next = step
        .read_through(Rc::clone(step.last_relation.as_ref().unwrap()))
        .unwrap();
    let next_restored = restored
        .read_through(Rc::clone(restored.last_relation.as_ref().unwrap()))
        .unwrap();
    assert_eq!(bytes(&next), bytes(&next_restored));
    let initial = bytes(&start);
    let initial_restored =
        NormalWaveFamilyRest::read(&mut initial.as_slice(), initial.len() as u64)
            .unwrap()
            .remount(&s)
            .unwrap();
    assert_eq!(bytes(&initial_restored), initial);
}
#[test]
#[ignore = "requires CUDA; decoded free response remains a family and source-ball forgery is rejected"]
fn family_rest_keeps_free_directions_and_checks_anchor_origin() {
    let ro = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&ro).unwrap();
    let body = body(&s);
    let mut learned = law(&s, false);
    let x = point(&s, &[0; 6]);
    let h = point(&s, &[0, 0]);
    for y in [[1, 0], [0, 1]] {
        let y = point(&s, &y);
        learned
            .advance_bilinear_contact(current(&x), current(&h), Some(current(&y)))
            .unwrap();
    }
    let family = body
        .read_family()
        .unwrap()
        .read_through(Rc::new(learned.read_wave_relation(current(&h), 1).unwrap()))
        .unwrap();
    let wire = bytes(&family);
    let restored = NormalWaveFamilyRest::read(&mut wire.as_slice(), wire.len() as u64)
        .unwrap()
        .remount(&s)
        .unwrap();
    let observed = restored.read_receiver().unwrap().inspect().unwrap();
    assert!(observed.anchor_independent_free[2..].iter().all(|v| *v));
    assert!(matches!(
        restored
            .affine_relation()
            .inspect()
            .unwrap()
            .predecessor_reading,
        ConstitutiveReading::Plural { .. }
    ));
    let mut forged = family.rest().unwrap();
    forged.anchor.intervals[0].0 += 1;
    forged.anchor.intervals[0].1 += 1;
    assert!(forged.remount(&s).is_err());
    assert_eq!(bytes(&family), wire);
}

#[test]
#[ignore = "requires CUDA; a fresh process continues only from the complete saved family"]
fn family_rest_continues_after_process_exit() {
    const INPUT: &str = "HOLONICS_FAMILY_PROCESS_INPUT";
    const OUTPUT: &str = "HOLONICS_FAMILY_PROCESS_OUTPUT";
    if let Some(input) = std::env::var_os(INPUT) {
        let wire = std::fs::read(input).unwrap();
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let family = NormalWaveFamilyRest::read(&mut wire.as_slice(), wire.len() as u64)
            .unwrap()
            .remount(&s)
            .unwrap();
        let next = family
            .read_through(Rc::clone(family.last_relation.as_ref().unwrap()))
            .unwrap();
        let output = std::path::PathBuf::from(std::env::var_os(OUTPUT).unwrap());
        std::fs::write(&output, bytes(&next)).unwrap();
        std::fs::write(
            output.with_extension("json"),
            serde_json::to_vec(&next.read_receiver().unwrap().inspect().unwrap()).unwrap(),
        )
        .unwrap();
        return;
    }
    let (wire, expected, receiver) = {
        let ro = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&ro).unwrap();
        let body = body(&s);
        let learned = law(&s, false);
        let h = point(&s, &[1, 0]);
        let first = body
            .read_family()
            .unwrap()
            .read_through(Rc::new(learned.read_wave_relation(current(&h), 1).unwrap()))
            .unwrap();
        let second = first
            .read_through(Rc::clone(first.last_relation.as_ref().unwrap()))
            .unwrap();
        (
            bytes(&first),
            bytes(&second),
            serde_json::to_vec(&second.read_receiver().unwrap().inspect().unwrap()).unwrap(),
        )
    };
    let dir = std::env::temp_dir().join(format!("holonics-family-process-{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let input = dir.join("input.family");
    let output = dir.join("output.family");
    std::fs::write(&input, wire).unwrap();
    let result=std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact","native_ecology::constitutive_fibre::field::material_transport::normal::direct::wave::family::rest::tests::family_rest_continues_after_process_exit","--ignored","--test-threads=1"])
        .env(INPUT,&input).env(OUTPUT,&output).output().unwrap();
    assert!(
        result.status.success(),
        "child stderr: {}\nstdout: {}",
        String::from_utf8_lossy(&result.stderr),
        String::from_utf8_lossy(&result.stdout)
    );
    assert_eq!(std::fs::read(&output).unwrap(), expected);
    assert_eq!(
        std::fs::read(output.with_extension("json")).unwrap(),
        receiver
    );
    std::fs::remove_dir_all(&dir).unwrap();
}
