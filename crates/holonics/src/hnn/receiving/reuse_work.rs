//! Test-only exterior call counters; no native retention or publication authority.
use super::*;
use crate::compression::landmark::context::LandmarkFace;
use crate::ratio::{integer, rat};
use std::time::Instant;
std::thread_local! {
    static COUNTS: std::cell::Cell<[u64;3]> = const { std::cell::Cell::new([0;3]) };
}
fn note(at: usize) {
    COUNTS.with(|c| {
        let mut n = c.get();
        n[at] += 1;
        c.set(n);
    });
}
pub(super) fn score() {
    note(0);
}
pub(super) fn mass() {
    note(1);
}
pub(super) fn weight() {
    note(2);
}
fn reset() {
    COUNTS.with(|c| c.set([0; 3]));
    crate::ratio::algebraic::LOG2_OBSERVATION_CALLS.with(|c| c.set(0));
}
fn counts() -> [u64; 4] {
    let n = COUNTS.with(|c| c.get());
    [
        n[0],
        n[1],
        n[2],
        crate::ratio::algebraic::LOG2_OBSERVATION_CALLS.with(|c| c.get()),
    ]
}
fn operands() -> (PortPopulation, Faces, Vec<LandmarkFace>, Vec<usize>) {
    let tree = LandmarkFace {
        grain: 4,
        probabilities: vec![rat(3, 8), rat(1, 8), rat(3, 8), rat(1, 8)],
        exponents: vec![(-6).into(), (-12).into(), (-6).into(), (-12).into()],
    };
    let targets = vec![0, 1, 2, 3, 3, 2, 1, 0];
    let trees = vec![tree; targets.len()];
    let reads = trees
        .iter()
        .enumerate()
        .map(|(n, t)| {
            ReceivingRead::combined(
                vec![
                    rat(n as i64, 1024),
                    integer(0),
                    rat(1, 512),
                    integer(0),
                    rat(-1, 512),
                    integer(0),
                    rat(-(n as i64), 1024),
                    integer(0),
                ],
                t,
                4,
            )
            .unwrap()
        })
        .collect::<Vec<_>>();
    (
        receiving_population(),
        Faces::of_reads(&reads, 4).unwrap(),
        trees,
        targets,
    )
}
fn without_work(mut r: RetainedSectionReturn) -> RetainedSectionReturn {
    r.section_score_evaluations = 0;
    r.station_mass_evaluations = 0;
    r.station_weight_evaluations = 0;
    r
}
#[test]
fn producer_reuse_exact_identity_refinement_chronology_and_measured_work() {
    let (population, faces, trees, targets) = operands();
    let bits = crate::ratio::exponentiated::READING_BITS;
    let mut old_times = Vec::new();
    let mut new_times = Vec::new();
    let mut old_counts = Vec::new();
    let mut new_counts = Vec::new();
    for _ in 0..5 {
        reset();
        let t = Instant::now();
        let old_score = score_at_law(
            ReceivingLaw::RetainedFibreV1,
            &population,
            2,
            &faces,
            &trees,
            &targets,
            bits,
        )
        .unwrap();
        let old_return =
            RetainedSectionReturn::at(&population, 2, &faces, &trees, &targets).unwrap();
        old_times.push(t.elapsed().as_nanos());
        old_counts.push(counts());
        reset();
        let t = Instant::now();
        let (new_score, new_return) =
            prepare_retained_section(&population, 2, &faces, &trees, &targets, bits).unwrap();
        new_times.push(t.elapsed().as_nanos());
        new_counts.push(counts());
        assert_eq!(old_score, new_score);
        assert_eq!(without_work(old_return), without_work(new_return));
        let populations = new_score
            .face_readings
            .iter()
            .map(|r| match r {
                SelectedFaceReading::Retained(r) => &r.population,
                _ => panic!("retained"),
            })
            .collect::<Vec<_>>();
        assert_ne!(
            populations[0], populations[1],
            "chronological mixture operands must stay distinct"
        );
        for (old, new) in old_score.face_readings.iter().zip(&new_score.face_readings) {
            let (SelectedFaceReading::Retained(old), SelectedFaceReading::Retained(new)) =
                (old, new)
            else {
                panic!("law")
            };
            let old = old.masses_at(bits).unwrap();
            let new = new.masses_at(bits).unwrap();
            assert_eq!(old, new);
            assert_eq!(
                crate::receiver::release::draw(&old, &rat(1, 2)).unwrap(),
                crate::receiver::release::draw(&new, &rat(1, 2)).unwrap()
            );
        }
    }
    assert!(
        old_counts
            .iter()
            .all(|c| c[0] == 2 && c[1] == 24 && c[2] == 32)
    );
    assert!(
        new_counts
            .iter()
            .all(|c| c[0] == 1 && c[1] == 8 && c[2] == 8)
    );
    assert!(old_counts.iter().zip(&new_counts).all(|(a, b)| a[3] > b[3]));
    // Producer32 must refine from the SAME immutable operands to return-ladder64,
    // preserving the actual initial score32 and complete returned foil/beta/error.
    let old32 = score_at_law(
        ReceivingLaw::RetainedFibreV1,
        &population,
        2,
        &faces,
        &trees,
        &targets,
        32,
    )
    .unwrap();
    let legacy_return =
        RetainedSectionReturn::at(&population, 2, &faces, &trees, &targets).unwrap();
    let (new32, refined_return) =
        prepare_retained_section(&population, 2, &faces, &trees, &targets, 32).unwrap();
    assert_eq!(old32, new32);
    assert_eq!(without_work(legacy_return), without_work(refined_return));
    // Concurrent/default parallel library tests cannot contaminate this thread's counters.
    reset();
    std::thread::spawn(|| {
        for _ in 0..16 {
            crate::ratio::algebraic::log2_enclosure_at(&rat(1, 2), 64).unwrap();
            score();
            mass();
            weight();
        }
        assert_eq!(counts(), [16; 4]);
    })
    .join()
    .unwrap();
    assert_eq!(counts(), [0; 4]);
    let producer =
        selected::ProducedRetainedSection::at(&population, 2, &faces, &trees, &targets, bits)
            .unwrap();
    assert!(
        producer
            .validate(&population, 1, &faces, &trees, &targets)
            .is_err()
    );
    let mut changed = faces.clone();
    changed.logits[0][0] += rat(1, 8);
    assert!(
        producer
            .validate(&population, 2, &changed, &trees, &targets)
            .is_err()
    );
    let mut wrong_targets = targets.clone();
    wrong_targets[0] = 1;
    assert!(
        producer
            .validate(&population, 2, &faces, &trees, &wrong_targets)
            .is_err()
    );
    let mut changed_population = population.clone();
    changed_population
        .receive(&producer.scored().steps[0].faces())
        .unwrap();
    assert!(
        producer
            .validate(&changed_population, 2, &faces, &trees, &targets)
            .is_err()
    );
    let refined = producer.observations_at(bits * 2).unwrap();
    let original = producer.observations_at(bits).unwrap();
    for ((r, old), reading) in refined
        .iter()
        .zip(original)
        .zip(&producer.scored().face_readings)
    {
        let SelectedFaceReading::Retained(reading) = reading else {
            panic!("law")
        };
        assert_eq!(r.masses(), reading.combined_masses_at(bits * 2).unwrap());
        assert_eq!(old.masses(), reading.combined_masses_at(bits).unwrap());
        assert!(
            r.read_at(
                &reading.receiver,
                &ReceivingRead::combined(vec![integer(0); 8], &trees[0], 4).unwrap(),
                bits
            )
            .is_err()
        );
    }
    let beyond_spread = new_times.iter().max() < old_times.iter().min();
    println!(
        "V93_IMMUTABLE_OBSERVATION_REUSE score_mass_weight_log_old={old_counts:?} score_mass_weight_log_new={new_counts:?} uncached_ns={old_times:?} reused_ns={new_times:?} reused_max_below_uncached_min={beyond_spread} samples=5 stations=8 source_cells=8 counter_scope=current_test_thread producer32_return64_exact=true concurrent_counter_isolation=true predictive_gain_claim=false ordinary_producer_reuse=true full_return_error_and_foil_equal=true"
    );
}
