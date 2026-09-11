//! CUDA checks for the addressed producing comparison.
//!
//! These are deliberately kept beside (rather than folded into) the ordinary wave tests: a
//! correction addressed to a prediction has a different source joint from a later `receive`.
use super::*;
use crate::embedding_fiber::ResidentReadout;

pub(super) fn point<'c>(surface: &'c ResidentSurface<'c>, values: &[i64]) -> ResidentSection<'c> {
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

fn rational<'c>(
    surface: &'c ResidentSurface<'c>,
    values: &[i64],
    denominator: i64,
) -> ResidentSection<'c> {
    let mut words = values.iter().map(|v| (*v, *v)).collect::<Vec<_>>();
    words.push((denominator, denominator));
    surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), i64::BITS, words)
                .unwrap(),
        )
        .unwrap()
}

pub(super) fn current<'a, 'c>(section: &'a ResidentSection<'c>) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::integers(section).unwrap()
}

fn rational_current<'a, 'c>(
    section: &'a ResidentSection<'c>,
) -> ResidentConstitutiveCurrent<'a, 'c> {
    ResidentConstitutiveCurrent::rational(section).unwrap()
}

pub(super) fn wave(real: i64, imaginary: i64, denominator: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(
        Rat::new(real.into(), denominator.into()),
        Rat::new(imaginary.into(), denominator.into()),
    )
}

pub(super) fn contains(ball: &NativeFieldCurrentBall, expected: &[ExactComplexWaveCurrent]) {
    let error: Rat = ball
        .center
        .iter()
        .zip(expected)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum();
    assert_eq!(ball.center.len(), expected.len());
    assert!(
        error <= &ball.radius * &ball.radius,
        "expected current is outside retained ball"
    )
}

/// The small three-port witness from the construction record: one prior `(1,1,0) -> 3/2`
/// observation, a `0 -> 1` seed, and a generated `2` before the addressed return `3`.
pub(super) fn witness<'c>(surface: &'c ResidentSurface<'c>) -> ResidentNormalWave<'c> {
    let mut material =
        ResidentNormalMaterial::found(surface, 1, 1, ResidentGrain(u32::BITS)).unwrap();
    let phi = point(surface, &[1, 0, 1, 0, 0, 0]);
    let eta = rational(surface, &[3, 0], 2);
    material
        .receive(current(&phi), rational_current(&eta))
        .unwrap();
    let p0 = point(surface, &[0, 0]);
    let c1 = point(surface, &[1, 0]);
    material
        .into_difference_wave(current(&p0), current(&c1))
        .unwrap()
}

#[test]
#[ignore = "requires CUDA; addressed return uses the retained producing cut"]
fn addressed_return_uses_producing_cut_witness() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = witness(&surface);
    let reads_before_predict = surface.census().section_read_outs;
    let prediction = body.predict().unwrap();
    assert_eq!(surface.census().section_read_outs, reads_before_predict);
    contains(
        &prediction.step.current.view().inspect().unwrap(),
        &[wave(2, 0, 1)],
    );
    let held = body.current().snapshot();
    let previous = body.previous().snapshot();
    let handle = prediction.handle;
    assert_eq!(body.pending_predictions(), 1);
    let observed = rational(&surface, &[3, 0], 1);
    let reads = surface.census().section_read_outs;
    let comparison = body
        .receive_prediction(&handle, rational_current(&observed))
        .unwrap();
    assert_eq!(surface.census().section_read_outs, reads);
    assert!(body.current().same_occurrence(&held));
    assert!(body.previous().same_occurrence(&previous));
    let reading = comparison.inspect().unwrap();
    assert_eq!(reading.prediction_id, handle.id());
    assert_eq!(reading.producing_epoch, 0);
    contains(
        &reading
            .comparison
            .contemporary_source_forward
            .as_ref()
            .unwrap(),
        &[wave(1, 0, 1)],
    );
    contains(&reading.comparison.forward, &[wave(7, 0, 5)]);
    assert!(reading.comparison.source_current.is_some());
    assert_eq!(body.pending_predictions(), 0);
    contains(
        &body.advance().unwrap().current.view().inspect().unwrap(),
        &[wave(41, 0, 10)],
    );
    let mut next_current = witness(&surface);
    next_current.advance().unwrap();
    next_current.receive(rational_current(&observed)).unwrap();
    contains(
        &next_current
            .advance()
            .unwrap()
            .current
            .view()
            .inspect()
            .unwrap(),
        &[wave(35, 0, 8)],
    );
}

#[test]
#[ignore = "requires CUDA; stale addressed handles refuse atomically"]
fn producing_handles_are_single_use_and_body_local() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut left = witness(&surface);
    let mut right = witness(&surface);
    let left_prediction = left.predict().unwrap();
    let right_prediction = right.predict().unwrap();
    let observed = point(&surface, &[3, 0]);
    let right_rest = right.rest().unwrap();
    assert!(
        right
            .receive_prediction(&left_prediction.handle, current(&observed))
            .is_err()
    );
    assert_eq!(right.pending_predictions(), 1);
    assert_eq!(right.rest().unwrap(), right_rest);
    let malformed = surface
        .mount_section_rest(
            &ResidentSectionRest::found(1, 2, ResidentGrain(0), i64::BITS, vec![(3, 4), (0, 0)])
                .unwrap(),
        )
        .unwrap();
    let before = left.rest().unwrap();
    assert!(
        left.receive_prediction(&left_prediction.handle, current(&malformed))
            .is_err()
    );
    assert_eq!(left.rest().unwrap(), before);
    let _ = left
        .receive_prediction(&left_prediction.handle, current(&observed))
        .unwrap();
    assert!(
        left.receive_prediction(&left_prediction.handle, current(&observed))
            .is_err()
    );
    assert_eq!(right_prediction.handle.id(), 1);
    assert_eq!(right.pending_predictions(), 1);
}

#[test]
#[ignore = "requires CUDA; delayed returns compose with contemporary material"]
fn delayed_return_survives_intervening_development() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = witness(&surface);
    let prediction = body.predict().unwrap();
    let intervening = point(&surface, &[0, 0, 1, 0, 0, 0]);
    let intervening_target = point(&surface, &[0, 0]);
    body.develop_section(
        ResidentConstitutiveSection::integers(&intervening).unwrap(),
        ResidentConstitutiveSection::integers(&intervening_target).unwrap(),
    )
    .unwrap();
    let before = body.fibre().material_observations;
    let observed = point(&surface, &[3, 0]);
    let comparison = body
        .receive_prediction(&prediction.handle, current(&observed))
        .unwrap();
    assert_eq!(
        comparison.inspect().unwrap().prediction_id,
        prediction.handle.id()
    );
    assert_eq!(body.fibre().material_observations, before + 1);
    let reading = comparison.inspect().unwrap();
    contains(
        reading
            .comparison
            .contemporary_source_forward
            .as_ref()
            .unwrap(),
        &[wave(1, 0, 1)],
    );
    contains(&reading.comparison.forward, &[wave(21, 0, 16)]);
}

#[test]
#[ignore = "requires CUDA; pending producing cuts survive rest/remount"]
fn pending_prediction_rest_retains_the_next_return() {
    let readout = ResidentReadout::new().unwrap();
    let surface = ResidentSurface::on(&readout).unwrap();
    let mut body = witness(&surface);
    let prediction = body.predict().unwrap();
    let rest = body.rest().unwrap();
    let mut bytes = Vec::new();
    rest.write(&mut bytes).unwrap();
    let loaded = NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64).unwrap();
    assert_eq!(loaded.pending_count(), 1);
    let mut remounted = loaded.remount(&surface, |_| {}).unwrap();
    let handle = remounted
        .pending_prediction(prediction.handle.id())
        .unwrap();
    assert_eq!(handle.id(), prediction.handle.id());
    let observed = point(&surface, &[3, 0]);
    let a = body
        .receive_prediction(&prediction.handle, current(&observed))
        .unwrap()
        .inspect()
        .unwrap();
    let b = remounted
        .receive_prediction(&handle, current(&observed))
        .unwrap()
        .inspect()
        .unwrap();
    assert_eq!(
        serde_json::to_value(a).unwrap(),
        serde_json::to_value(b).unwrap()
    );
    assert_eq!(body.rest().unwrap(), remounted.rest().unwrap());
    assert_eq!(
        serde_json::to_value(body.advance().unwrap().inspect().unwrap()).unwrap(),
        serde_json::to_value(remounted.advance().unwrap().inspect().unwrap()).unwrap()
    );
}

#[test]
#[ignore = "requires CUDA; the target and source retain one nonzero-radius producing family"]
fn enclosed_producing_joint_is_not_a_point_target() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut m = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(32)).unwrap();
    let phi = point(&s, &[1, 0, 1, 0, 0, 0]);
    let one = point(&s, &[1, 0]);
    let zero = point(&s, &[0, 0]);
    m.receive(current(&phi), current(&one)).unwrap();
    let mut body = m
        .into_difference_wave(current(&zero), current(&one))
        .unwrap();
    body.advance().unwrap();
    let p = body.predict().unwrap();
    let observed = point(&s, &[3, 0]);
    let reads = s.census().section_read_outs;
    let returned = body
        .receive_prediction(&p.handle, current(&observed))
        .unwrap();
    assert_eq!(s.census().section_read_outs, reads);
    assert!(returned.source_joint().inspect().unwrap().radius > Rat::zero());
    let state = body.material.inspect().unwrap();
    assert!(state.source_normal_error > Rat::zero());
    assert!(state.target_energy_error > Rat::zero());
    state.objective().unwrap();
    body.advance().unwrap();
}

#[test]
#[ignore = "requires CUDA; source and receiving chart rotate together"]
fn producing_comparison_transports_a_unit_phase() {
    let readout = ResidentReadout::new().unwrap();
    let s = ResidentSurface::on(&readout).unwrap();
    let mut material = ResidentNormalMaterial::found(&s, 1, 1, ResidentGrain(32)).unwrap();
    let phi = point(&s, &[0, 1, 0, 1, 0, 0]);
    let eta = rational(&s, &[0, 3], 2);
    material
        .receive(current(&phi), rational_current(&eta))
        .unwrap();
    let p = point(&s, &[0, 0]);
    let c = point(&s, &[0, 1]);
    let mut body = material
        .into_difference_wave(current(&p), current(&c))
        .unwrap();
    let prediction = body.predict().unwrap();
    let observed = point(&s, &[0, 3]);
    body.receive_prediction(&prediction.handle, current(&observed))
        .unwrap();
    contains(
        &body.advance().unwrap().current.view().inspect().unwrap(),
        &[wave(0, 41, 10)],
    );
}

#[test]
#[ignore = "requires CUDA; a pending comparison continues after the producing process exits"]
fn pending_comparison_survives_process_exit() {
    const MODE: &str = "HOLONICS_PRODUCING_TEST_MODE";
    const ARTIFACTS: &str = "HOLONICS_PRODUCING_TEST_PATH";
    if let Ok(mode) = std::env::var(MODE) {
        let path = std::path::PathBuf::from(std::env::var_os(ARTIFACTS).unwrap());
        let readout = ResidentReadout::new().unwrap();
        let s = ResidentSurface::on(&readout).unwrap();
        let mut body = if mode == "produce" {
            let mut body = witness(&s);
            body.predict().unwrap();
            let mut bytes = Vec::new();
            body.rest().unwrap().write(&mut bytes).unwrap();
            std::fs::write(path.join("pending.wave"), bytes).unwrap();
            body
        } else {
            assert_eq!(mode, "resume");
            let bytes = std::fs::read(path.join("pending.wave")).unwrap();
            NormalWaveRest::read(&mut bytes.as_slice(), bytes.len() as u64)
                .unwrap()
                .remount(&s, |_| {})
                .unwrap()
        };
        let handle = body.pending_prediction(1).unwrap();
        let observed = point(&s, &[3, 0]);
        let comparison = body
            .receive_prediction(&handle, current(&observed))
            .unwrap()
            .inspect()
            .unwrap();
        let next = body.advance().unwrap().inspect().unwrap();
        let mut rest = Vec::new();
        body.rest().unwrap().write(&mut rest).unwrap();
        std::fs::write(
            path.join(format!("{mode}.json")),
            serde_json::to_vec(&(comparison, next, rest)).unwrap(),
        )
        .unwrap();
        return;
    }
    let path = std::env::temp_dir().join(format!(
        "holonics-producing-return-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&path).unwrap();
    for mode in ["produce", "resume"] {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .arg("pending_comparison_survives_process_exit")
            .args(["--ignored", "--test-threads=1"])
            .env(MODE, mode)
            .env(ARTIFACTS, &path)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{mode}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    assert_eq!(
        std::fs::read(path.join("produce.json")).unwrap(),
        std::fs::read(path.join("resume.json")).unwrap()
    );
}
