//! Endpoint and full-receipt parity against the former independent comparison/score passes.

use super::*;
use crate::hnn::ratio::{HolonRatio, TargetPhases};
use crate::ratio::rat;
use crate::receiver::face::grain_exponent;

const GRAIN: u64 = 4;

fn tree(probabilities: Vec<Rat>) -> LandmarkFace {
    let exponents = probabilities
        .iter()
        .map(|p| {
            grain_exponent(
                &BigUint::try_from(p.numer().clone()).unwrap(),
                &BigUint::try_from(p.denom().clone()).unwrap(),
                GRAIN,
            )
            .unwrap()
        })
        .collect();
    LandmarkFace {
        grain: GRAIN,
        probabilities,
        exponents,
    }
}

fn faces(real: &[Vec<Rat>], imaginary: &Rat) -> Faces {
    let reads: Vec<_> = real
        .iter()
        .map(|row| {
            ReceivingRead::of_logits(
                row.iter()
                    .flat_map(|x| [x.clone(), imaginary.clone()])
                    .collect(),
                GRAIN,
            )
        })
        .collect();
    Faces::of_reads(&reads, GRAIN).unwrap()
}

fn fixture() -> (
    Faces,
    Vec<LandmarkFace>,
    Faces,
    Vec<LandmarkFace>,
    Vec<usize>,
) {
    let before = faces(
        &[
            vec![rat(0, 1), rat(1, 3), rat(-1, 2), rat(3, 4)],
            vec![rat(-1, 3), rat(1, 2), rat(0, 1), rat(1, 4)],
            vec![rat(1, 4), rat(0, 1), rat(-1, 3), rat(1, 2)],
        ],
        &rat(0, 1),
    );
    let after = faces(
        &[
            vec![rat(0, 1), rat(2, 3), rat(-1, 2), rat(3, 4)],
            vec![rat(1, 3), rat(1, 2), rat(0, 1), rat(1, 4)],
            vec![rat(1, 4), rat(0, 1), rat(1, 3), rat(1, 2)],
        ],
        &rat(0, 1),
    );
    let before_trees = vec![
        tree(vec![rat(1, 3), rat(1, 6), rat(1, 4), rat(1, 4)]),
        tree(vec![rat(1, 4), rat(1, 4), rat(1, 4), rat(1, 4)]),
        tree(vec![rat(1, 8), rat(1, 8), rat(1, 4), rat(1, 2)]),
    ];
    let mut after_trees = before_trees.clone();
    after_trees[1] = tree(vec![rat(1, 8), rat(3, 8), rat(1, 4), rat(1, 4)]);
    (before, before_trees, after, after_trees, vec![1, 0, 2])
}

// Deliberately retained old operation sequence, not the shared scorer engine under test.
#[allow(clippy::too_many_arguments)]
fn legacy_comparison(
    population: &PortPopulation,
    ring: usize,
    before: &Faces,
    before_trees: &[LandmarkFace],
    after: &Faces,
    after_trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
) -> Result<ComparedScoresAt, HnnError> {
    let mut window = Vec::with_capacity(targets.len());
    for ((((before, after), before_tree), after_tree), &target) in before
        .faces
        .iter()
        .zip(&after.faces)
        .zip(before_trees)
        .zip(after_trees)
        .zip(targets)
    {
        let before_mass = face_enclosure_at(before, target, bits)?;
        let same_class_face = before.grain() == after.grain()
            && before.cells().len() == after.cells().len()
            && before
                .cells()
                .iter()
                .zip(after.cells())
                .all(|(a, b)| a.carry == b.carry && a.phase == b.phase);
        let wave = if same_class_face {
            ComparedFace::Shared(before_mass)
        } else {
            ComparedFace::Changed {
                before: before_mass,
                after: face_enclosure_at(after, target, bits)?,
            }
        };
        let before_mass = ExactInterval::point(before_tree.probabilities[target].clone());
        let tree = if before_tree.probabilities[target] == after_tree.probabilities[target] {
            ComparedFace::Shared(before_mass)
        } else {
            ComparedFace::Changed {
                before: before_mass,
                after: ExactInterval::point(after_tree.probabilities[target].clone()),
            }
        };
        window.push(vec![tree, wave]);
    }
    let change = population
        .code_change_at(&window, bits)
        .map_err(population_refusal)?;
    let before = legacy_score_at(population, ring, before, before_trees, targets, bits)?;
    let after = legacy_score_at(population, ring, after, after_trees, targets, bits)?;
    Ok(ComparedScoresAt {
        change,
        before,
        after,
    })
}

fn legacy_score_at(
    population: &PortPopulation,
    ring: usize,
    combined: &Faces,
    trees: &[LandmarkFace],
    targets: &[usize],
    bits: u32,
) -> Result<Scored, HnnError> {
    if combined.faces.len() != trees.len() || trees.len() != targets.len() {
        return Err(HnnError::Shape {
            what: "one combined face, one tree face and one target per phase",
            expected: trees.len(),
            found: targets.len(),
        });
    }
    let mut local = population.clone();
    let mut scored = Scored {
        model: Vec::with_capacity(targets.len()),
        tree: Vec::with_capacity(targets.len()),
        steps: Vec::with_capacity(targets.len()),
        face_readings: Vec::with_capacity(targets.len()),
    };
    for ((face, tree), &target) in combined.faces.iter().zip(trees).zip(targets) {
        scored
            .face_readings
            .push(cells::ScoredFaceReading::new(&local, tree, face));
        let q_tree = tree
            .probabilities
            .get(target)
            .ok_or(HnnError::CellOutside {
                code: target,
                alphabet: tree.probabilities.len(),
            })?
            .clone();
        let log = crate::ratio::algebraic::log2_enclosure_at(&q_tree, bits)?;
        scored
            .tree
            .push(ExactInterval::new(-log.upper, -log.lower)?);
        let step = ReceivingStep {
            ring,
            tree: q_tree,
            combined: face_enclosure_at(face, target, bits)?,
        };
        scored.model.push(
            local
                .code_of_at(&step.faces(), bits)
                .map_err(population_refusal)?,
        );
        local.receive(&step.faces()).map_err(population_refusal)?;
        scored.steps.push(step);
    }
    Ok(scored)
}

fn parity(population: &PortPopulation) {
    let (before, bt, after, at, targets) = fixture();
    let original = population.clone();
    for bits in cells::demand_ladder() {
        let expected =
            legacy_comparison(population, 7, &before, &bt, &after, &at, &targets, bits).unwrap();
        let actual =
            compare_scores_at(population, 7, &before, &bt, &after, &at, &targets, bits).unwrap();
        // Includes every model/tree endpoint, ReceivingStep and authentic pre-reception reading.
        assert_eq!(actual, expected);
        assert_eq!(
            score_at(population, 7, &before, &bt, &targets, bits).unwrap(),
            expected.before
        );
        assert_eq!(
            score_at(population, 7, &after, &at, &targets, bits).unwrap(),
            expected.after
        );
        assert_ne!(
            actual.before.steps[0].combined,
            actual.after.steps[0].combined
        );
        assert_ne!(actual.before.steps[1].tree, actual.after.steps[1].tree);
        assert_ne!(actual.before.tree[1], actual.after.tree[1]);
        let unreceived_second = score_at(
            population,
            7,
            &Faces {
                faces: vec![before.faces[1].clone()],
                logits: vec![before.logits[1].clone()],
            },
            &bt[1..2],
            &targets[1..2],
            bits,
        )
        .unwrap();
        assert_ne!(
            actual.before.model[1], unreceived_second.model[0],
            "the second phase must use its own earlier target reception"
        );
        assert_eq!(population, &original);
    }
}

#[test]
fn changed_wave_and_tree_match_every_demand_with_independent_multi_phase_populations() {
    parity(&receiving_population());
}

#[test]
fn uncertain_retained_population_keeps_identical_endpoints_steps_and_face_readings() {
    let mut population = receiving_population();
    population
        .receive(&[
            ExactInterval::point(rat(1, 2)),
            ExactInterval::new(rat(1, 4), rat(5, 16)).unwrap(),
        ])
        .unwrap();
    assert!(population.retained_interval_members() > 0);
    parity(&population);
}

#[test]
fn shared_class_mass_does_not_erase_changed_fibre_or_produced_phase() {
    let before = faces(&[vec![rat(1, 3), rat(0, 1)]], &rat(0, 1));
    // Both real logits stay in their same grain cells, while fibre and produced phase change.
    let after = faces(&[vec![rat(2, 5), rat(1, 10)]], &rat(1, 2));
    assert_ne!(before.faces[0].fibres(), after.faces[0].fibres());
    assert_ne!(before.faces[0].phases(), after.faces[0].phases());
    let trees = vec![tree(vec![rat(1, 3), rat(2, 3)])];
    let target = TargetPhases {
        branch: 0.into(),
        phases: vec![rat(0, 1)],
    };
    let before_phase = HolonRatio::compare(before.clone(), &[0], &target)
        .unwrap()
        .excess();
    let after_phase = HolonRatio::compare(after.clone(), &[0], &target)
        .unwrap()
        .excess();
    assert_ne!(before_phase, after_phase);
    for bits in cells::demand_ladder() {
        let expected = legacy_comparison(
            &receiving_population(),
            0,
            &before,
            &trees,
            &after,
            &trees,
            &[0],
            bits,
        )
        .unwrap();
        let actual = compare_scores_at(
            &receiving_population(),
            0,
            &before,
            &trees,
            &after,
            &trees,
            &[0],
            bits,
        )
        .unwrap();
        assert_eq!(actual, expected);
        assert_eq!(actual.change, ExactInterval::point(rat(0, 1)));
        assert_eq!(actual.before.steps, actual.after.steps);
        assert_ne!(actual.before.face_readings, actual.after.face_readings);
        let phase_delta = &after_phase - &before_phase;
        let total = ExactInterval::new(
            actual.change.lower + &phase_delta,
            actual.change.upper + &phase_delta,
        )
        .unwrap();
        assert_eq!(total, ExactInterval::point(phase_delta));
    }
}

fn same_refusal(a: Result<ComparedScoresAt, HnnError>, b: Result<ComparedScoresAt, HnnError>) {
    assert_eq!(
        format!("{:?}", a.unwrap_err()),
        format!("{:?}", b.unwrap_err())
    );
}

#[test]
fn target_and_shape_refusals_preserve_error_order_and_leave_population_unchanged() {
    let (before, bt, after, at, targets) = fixture();
    let population = receiving_population();
    let original = population.clone();
    for bits in cells::demand_ladder() {
        let mut invalid = targets.clone();
        invalid[0] = 4;
        same_refusal(
            compare_scores_at(&population, 0, &before, &bt, &after, &at, &invalid, bits),
            legacy_comparison(&population, 0, &before, &bt, &after, &at, &invalid, bits),
        );
        let mut short = after.clone();
        short.faces.pop();
        short.logits.pop();
        same_refusal(
            compare_scores_at(&population, 0, &before, &bt, &short, &at, &targets, bits),
            legacy_comparison(&population, 0, &before, &bt, &short, &at, &targets, bits),
        );
        assert_eq!(population, original);
    }
}

#[test]
fn coupled_population_refusal_precedes_absolute_tree_log_refusal() {
    let before = faces(&[vec![rat(0, 1), rat(0, 1)]], &rat(0, 1));
    let mut zero_tree = tree(vec![rat(1, 2), rat(1, 2)]);
    zero_tree.probabilities[0] = rat(0, 1);
    let trees = vec![zero_tree];
    let population = PortPopulation::new(&[0]).unwrap(); // one family cannot read the two-family window
    let original = population.clone();
    for bits in cells::demand_ladder() {
        let legacy =
            legacy_comparison(&population, 0, &before, &trees, &before, &trees, &[0], bits);
        let actual =
            compare_scores_at(&population, 0, &before, &trees, &before, &trees, &[0], bits);
        assert!(matches!(
            &actual,
            Err(HnnError::Shape {
                what: "the receiver's population: faces in the unit interval, some family alive",
                ..
            })
        ));
        same_refusal(actual, legacy);
        assert_eq!(population, original);
    }
    // With a valid population, the later absolute tree logarithm's native zero refusal propagates.
    let population = receiving_population();
    same_refusal(
        compare_scores_at(&population, 0, &before, &trees, &before, &trees, &[0], 64),
        legacy_comparison(&population, 0, &before, &trees, &before, &trees, &[0], 64),
    );
}

#[test]
fn malformed_tree_target_is_a_fatal_typed_refusal_without_population_change() {
    let before = faces(&[vec![rat(0, 1), rat(0, 1)]], &rat(0, 1));
    let trees = vec![tree(vec![rat(1, 1)])];
    let population = receiving_population();
    let original = population.clone();
    let error =
        compare_scores_at(&population, 0, &before, &trees, &before, &trees, &[1], 64).unwrap_err();
    assert!(matches!(
        error,
        HnnError::CellOutside {
            code: 1,
            alphabet: 1
        }
    ));
    assert_eq!(population, original);
    // observed::epoch::receiving_restage_permitted matches only named Unadmitted reasons;
    // this CellOutside cannot enter receiving/joint candidate-domain fallback.
    assert!(!matches!(error, HnnError::Unadmitted { .. }));
}

// Exact public-source v27 frozen-R receipt: v23 cell 0, target class 0.
// This fixture documents an existing law, not a proposed rounding correction.
// See the private audit's pinned control.log SHA and selected receipt JSON.
fn v27_first_frozen_receipt() -> (LandmarkFace, Vec<Rat>) {
    let q = |n: &str, d: &str| Rat::new(n.parse().unwrap(), d.parse().unwrap());
    let tree = tree(vec![
        q("79528309465489328205", "1180591620717411303424"),
        q("1098187783814926579635", "1180591620717411303424"),
        q("3483812087109724143", "4722366482869645213696"),
        q("8018297660871858193", "4722366482869645213696"),
    ]);
    let wave = vec![
        rat(-111, 65536),
        rat(113, 65536),
        rat(1, 2048),
        rat(5, 4096),
        rat(9, 16384),
        rat(259, 65536),
        rat(11, 32768),
        rat(5, 4096),
    ];
    (tree, wave)
}

#[test]
fn actual_v27_tiny_negative_wave_borrows_a_full_grain_and_positive_wave_stays_in_cell() {
    let (tree, wave) = v27_first_frozen_receipt();
    assert_eq!(tree.probabilities.iter().sum::<Rat>(), rat(1, 1));
    let before = ReceivingRead::combined(vec![rat(0, 1); 8], &tree, GRAIN).unwrap();
    let after = ReceivingRead::combined(wave.clone(), &tree, GRAIN).unwrap();
    assert_eq!(before.cells[0].carry, BigInt::from(-4));
    assert_eq!(before.cells[0].phase, 0);
    assert_eq!(after.cells[0].carry, BigInt::from(-5));
    assert_eq!(after.cells[0].phase, 3);
    assert_eq!(
        after.cells[0].representative(GRAIN),
        before.cells[0].representative(GRAIN) - rat(1, 4)
    );
    for class in 1..4 {
        assert!(wave[2 * class] > rat(0, 1) && wave[2 * class] < rat(1, 4));
        assert_eq!(after.cells[class].carry, before.cells[class].carry);
        assert_eq!(after.cells[class].phase, before.cells[class].phase);
    }
    // An arbitrarily smaller same-sign wave still has the same magnitude face here.
    let tiny = ReceivingRead::combined(
        wave.iter().map(|x| x / rat(1024, 1)).collect(),
        &tree,
        GRAIN,
    )
    .unwrap();
    for (native, tiny) in after.cells.iter().zip(&tiny.cells) {
        assert_eq!(native.carry, tiny.carry);
        assert_eq!(native.phase, tiny.phase);
    }
    let mut positive_wave = wave;
    positive_wave[0] = -positive_wave[0].clone();
    let positive = ReceivingRead::combined(positive_wave, &tree, GRAIN).unwrap();
    for (old, new) in before.cells.iter().zip(&positive.cells) {
        assert_eq!(old.carry, new.carry);
        assert_eq!(old.phase, new.phase);
    }
    let before = Face::of_read(&before, GRAIN).unwrap();
    let after = Face::of_read(&after, GRAIN).unwrap();
    let tiny = Face::of_read(&tiny, GRAIN).unwrap();
    let positive = Face::of_read(&positive, GRAIN).unwrap();
    for bits in cells::demand_ladder() {
        let old_mass = face_enclosure_at(&before, 0, bits).unwrap();
        let new_mass = face_enclosure_at(&after, 0, bits).unwrap();
        assert!(new_mass.upper < old_mass.lower);
        assert_eq!(new_mass, face_enclosure_at(&tiny, 0, bits).unwrap());
        assert_eq!(old_mass, face_enclosure_at(&positive, 0, bits).unwrap());
    }
}

#[test]
fn existing_native_objective_can_improve_phase_while_magnitude_class_code_worsens() {
    let (tree, actual_wave) = v27_first_frozen_receipt();
    // The magnitude operands are from that actual receipt. The two imaginary rows below form
    // an explicit algebraic control, not a claim about an executed training candidate.
    let mut before_wave = vec![rat(0, 1); 8];
    before_wave[1] = rat(2, 1); // produced target phase=1 turn
    let mut after_wave = actual_wave;
    for row in (1..8).step_by(2) {
        after_wave[row] = rat(0, 1);
    }
    let before_read = ReceivingRead::combined(before_wave, &tree, GRAIN).unwrap();
    let after_read = ReceivingRead::combined(after_wave, &tree, GRAIN).unwrap();
    let before = Faces::of_reads(&[before_read], GRAIN).unwrap();
    let after = Faces::of_reads(&[after_read], GRAIN).unwrap();
    let target = TargetPhases {
        branch: 0.into(),
        phases: vec![rat(0, 1)],
    };
    let before_phase = HolonRatio::compare(before.clone(), &[0], &target)
        .unwrap()
        .excess();
    let after_phase = HolonRatio::compare(after.clone(), &[0], &target)
        .unwrap()
        .excess();
    assert_eq!(before_phase, rat(1, 2));
    assert_eq!(after_phase, rat(0, 1));
    for bits in cells::demand_ladder() {
        let scored = compare_scores_at(
            &receiving_population(),
            2,
            &before,
            std::slice::from_ref(&tree),
            &after,
            std::slice::from_ref(&tree),
            &[0],
            bits,
        )
        .unwrap();
        assert!(
            scored.change.lower > rat(0, 1),
            "magnitude class code is strictly worse"
        );
        assert!(scored.change.upper < rat(1, 4));
        let delta = &after_phase - &before_phase;
        let objective =
            ExactInterval::new(scored.change.lower + &delta, scored.change.upper + &delta).unwrap();
        assert!(
            objective.upper < rat(0, 1),
            "class-code-plus-phase objective is strictly better"
        );
    }
}
