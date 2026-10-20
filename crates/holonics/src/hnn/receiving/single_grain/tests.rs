use super::*;
use crate::compression::landmark::context::{BaseMeasure, Capacity, StopPrior};
use crate::ratio::rat;

fn split_face(numerator: u64, grain: u64) -> LandmarkFace {
    let declaration = LandmarkDeclaration {
        alphabet: 2,
        depth: 0,
        forced: 0,
        population: 16,
        grain,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
        mass: 1,
        base: BaseMeasure::Even,
    };
    LandmarkFace::of_splits(
        &declaration,
        &Splits {
            face_bits: 3,
            numerators: vec![numerator],
        },
        grain,
    )
    .unwrap()
}

fn exponent(cell: &ReceivingCell, grain: u64) -> BigInt {
    &cell.carry * BigInt::from(grain) + BigInt::from(cell.phase)
}

fn legacy(wave: &[Rat], tree: &LandmarkFace) -> ReceivingRead {
    ReceivingRead::of_logits(
        wave.iter()
            .zip(grain_logits(tree))
            .map(|(w, k)| w + k)
            .collect(),
        tree.grain,
    )
}

#[test]
fn zero_wave_keeps_executed_cells_masses_codes_and_population_steps() {
    for numerator in [1, 3, 6, 7] {
        for grain in [1, 4, 8] {
            let tree = split_face(numerator, grain);
            let wave = vec![Rat::zero(); 4];
            let corrected = ReceivingRead::combined(wave.clone(), &tree, grain).unwrap();
            let old = legacy(&wave, &tree);
            for ((a, b), k) in corrected.cells.iter().zip(&old.cells).zip(&tree.exponents) {
                assert_eq!(a.carry, b.carry);
                assert_eq!(a.phase, b.phase);
                assert_eq!(exponent(a, grain), *k);
            }
            let new_faces = Faces::of_reads(&vec![corrected; 3], grain).unwrap();
            let old_faces = Faces::of_reads(&vec![old; 3], grain).unwrap();
            let mut population = receiving_population();
            population
                .receive(&[
                    ExactInterval::point(rat(1, 2)),
                    ExactInterval::new(rat(1, 3), rat(3, 8)).unwrap(),
                ])
                .unwrap();
            let trees = vec![tree; 3];
            for bits in cells::demand_ladder() {
                let new = score_at(&population, 2, &new_faces, &trees, &[0, 1, 0], bits).unwrap();
                let old = score_at(&population, 2, &old_faces, &trees, &[0, 1, 0], bits).unwrap();
                assert_eq!(new.model, old.model);
                assert_eq!(new.tree, old.tree);
                assert_eq!(new.steps, old.steps);
                for (a, b) in new_faces.faces.iter().zip(&old_faces.faces) {
                    assert!(a.same_mass_face(b));
                    for class in 0..2 {
                        assert_eq!(
                            face_enclosure_at(a, class, bits).unwrap(),
                            face_enclosure_at(b, class, bits).unwrap()
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn exact_tree_fibre_decides_upward_and_downward_crossings_symmetrically() {
    let grain = 8;
    for (n, k, up, down) in [(6, -4, -3, -4), (7, -2, -2, -3)] {
        let tree = split_face(n, grain);
        let zero = ReceivingRead::combined(vec![rat(0, 1); 4], &tree, grain).unwrap();
        let positive = ReceivingRead::combined(
            vec![rat(1, 16), rat(0, 1), rat(0, 1), rat(0, 1)],
            &tree,
            grain,
        )
        .unwrap();
        let negative = ReceivingRead::combined(
            vec![rat(-1, 16), rat(0, 1), rat(0, 1), rat(0, 1)],
            &tree,
            grain,
        )
        .unwrap();
        assert_eq!(exponent(&zero.cells[0], grain), BigInt::from(k));
        assert_eq!(exponent(&positive.cells[0], grain), BigInt::from(up));
        assert_eq!(exponent(&negative.cells[0], grain), BigInt::from(down));
        let fibre = zero.cells[0].fibre.enclosure_at(64).unwrap();
        if n == 6 {
            assert!(fibre.lower > rat(1, 16));
        } else {
            assert!(fibre.upper < rat(1, 16));
        }
        assert!(matches!(
            zero.cells[0].fibre,
            ReceivingFibre::Logarithmic(_)
        ));
        assert!(zero.cells[0].fibre.as_rational().is_none());
        let coarse = zero.cells[0].fibre.enclosure_at(0).unwrap();
        assert!(coarse.lower >= rat(0, 1) && coarse.upper <= rat(1, 8));
        assert!(
            coarse.upper > rat(0, 1),
            "the irrational fibre is not replaced by exact zero"
        );
        assert_eq!(
            positive.logits[0],
            rat(1, 16),
            "rational port coordinate remains the wave"
        );
    }
}

#[test]
fn actual_v27_tiny_wave_no_longer_discards_the_tree_fibre_before_graining() {
    let value = |n: &str, d: &str| Rat::new(n.parse().unwrap(), d.parse().unwrap());
    let probabilities = vec![
        value("79528309465489328205", "1180591620717411303424"),
        value("1098187783814926579635", "1180591620717411303424"),
        value("3483812087109724143", "4722366482869645213696"),
        value("8018297660871858193", "4722366482869645213696"),
    ];
    let grain = 4;
    let exponents = probabilities
        .iter()
        .map(|p| {
            crate::receiver::face::grain_exponent(
                &BigUint::try_from(p.numer().clone()).unwrap(),
                &BigUint::try_from(p.denom().clone()).unwrap(),
                grain,
            )
            .unwrap()
        })
        .collect();
    let tree = LandmarkFace {
        grain,
        probabilities,
        exponents,
    };
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
    let corrected = ReceivingRead::combined(wave.clone(), &tree, grain).unwrap();
    let founding = ReceivingRead::combined(vec![rat(0, 1); 8], &tree, grain).unwrap();
    let old = legacy(&wave, &tree);
    assert_eq!(exponent(&old.cells[0], grain), BigInt::from(-17));
    assert_eq!(exponent(&corrected.cells[0], grain), BigInt::from(-16));
    let corrected = Face::of_read(&corrected, grain).unwrap();
    let founding = Face::of_read(&founding, grain).unwrap();
    assert!(corrected.same_mass_face(&founding));
    assert_ne!(
        corrected, founding,
        "authentic fibres and produced phases remain distinct"
    );
    for bits in cells::demand_ladder() {
        let before = Faces {
            faces: vec![founding.clone()],
            logits: vec![vec![rat(0, 1); 8]],
        };
        let after = Faces {
            faces: vec![corrected.clone()],
            logits: vec![wave.clone()],
        };
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
        assert_eq!(scored.change, ExactInterval::point(Rat::zero()));
    }
    for bits in cells::demand_ladder() {
        for class in 0..4 {
            assert_eq!(
                face_enclosure_at(&corrected, class, bits).unwrap(),
                face_enclosure_at(&founding, class, bits).unwrap()
            );
        }
    }
}

#[test]
fn powers_of_two_keep_exact_rational_edges_negative_carries_and_fibres() {
    let tree = split_face(2, 8); // q0=1/4, log2 q0=-2 exactly
    for (wave, m, fibre) in [
        (rat(1, 8), -15, rat(0, 1)),
        (rat(-1, 8), -17, rat(0, 1)),
        (rat(-1, 16), -17, rat(1, 16)),
    ] {
        let read = ReceivingRead::combined(
            vec![wave.clone(), rat(0, 1), rat(0, 1), rat(0, 1)],
            &tree,
            8,
        )
        .unwrap();
        let cell = &read.cells[0];
        assert_eq!(exponent(cell, 8), BigInt::from(m));
        assert_eq!(cell.fibre.as_rational(), Some(&fibre));
        assert_eq!(cell.rational_value(8), Some(rat(-2, 1) + wave));
        assert_eq!(
            cell.fibre.enclosure_at(0).unwrap(),
            ExactInterval::point(fibre)
        );
        if m == -17 {
            assert_eq!(cell.carry, BigInt::from(-3));
            assert_eq!(cell.phase, 7);
        }
    }
}

#[test]
fn unresolved_edge_refines_beyond_fixed_population_precision_without_choosing_an_endpoint() {
    let denominator = BigInt::one() << 256usize;
    let probability = Rat::new(&denominator - BigInt::one(), denominator);
    let initial = log2_enclosure_at(&probability, 192).unwrap();
    assert_ne!(
        (&initial.lower * integer(8)).floor(),
        (&initial.upper * integer(8)).floor()
    );
    let cell = read_cell(&probability, &Rat::zero(), 8).unwrap();
    assert_eq!(exponent(&cell, 8), BigInt::from(-1));
    let fibre = cell.fibre.enclosure_at(512).unwrap();
    assert!(fibre.lower > rat(0, 1) && fibre.upper < rat(1, 8));
}

#[test]
fn phase_only_change_has_exact_zero_mass_comparison_and_unchanged_pullback_phase() {
    let tree = split_face(6, 8);
    let before = ReceivingRead::combined(vec![rat(0, 1); 4], &tree, 8).unwrap();
    let after =
        ReceivingRead::combined(vec![rat(0, 1), rat(1, 3), rat(0, 1), rat(-1, 5)], &tree, 8)
            .unwrap();
    assert_eq!(after.phases, vec![rat(1, 6), rat(-1, 10)]);
    let before = Faces::of_reads(&[before], 8).unwrap();
    let after = Faces::of_reads(&[after], 8).unwrap();
    assert!(before.faces[0].same_mass_face(&after.faces[0]));
    assert_ne!(before.faces[0], after.faces[0]);
    for bits in cells::demand_ladder() {
        let compared = compare_scores_at(
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
        assert_eq!(compared.change, ExactInterval::point(Rat::zero()));
    }
}

#[test]
fn invalid_logarithm_and_forged_fibre_cell_refuse_without_a_fallback_value() {
    let mut tree = split_face(6, 8);
    tree.probabilities[0] = Rat::zero();
    let error = ReceivingRead::combined(vec![rat(0, 1); 4], &tree, 8).unwrap_err();
    assert!(matches!(error, HnnError::Exact(_)));
    let tree = split_face(6, 8);
    let mut read = ReceivingRead::combined(vec![rat(0, 1); 4], &tree, 8).unwrap();
    read.cells[0].carry += BigInt::one();
    assert!(
        Face::of_read(&read, 8).is_err(),
        "sealed fibre does not authenticate a different cell"
    );
    assert!(ReceivingRead::combined(vec![rat(0, 1); 4], &tree, 4).is_err());
}

#[test]
fn mirrored_near_power_boundaries_cross_in_both_directions_by_exact_integer_inequalities() {
    let make = |numerator| {
        let probability = rat(numerator, 1024);
        let probabilities = vec![probability.clone(), rat(1, 1) - probability];
        let exponents = probabilities
            .iter()
            .map(|p| {
                crate::receiver::face::grain_exponent(
                    &BigUint::try_from(p.numer().clone()).unwrap(),
                    &BigUint::try_from(p.denom().clone()).unwrap(),
                    4,
                )
                .unwrap()
            })
            .collect();
        LandmarkFace {
            grain: 4,
            probabilities,
            exponents,
        }
    };
    // Independent exact threshold certificates: (2*q)^256 compared with the rational power 2.
    assert!(rat(2, 1) * rat(511, 512).pow(256) > rat(1, 1));
    assert!(rat(513, 512).pow(256) < rat(2, 1));
    for (numerator, wave, before, after) in
        [(511, rat(1, 256), -5, -4), (513, rat(-1, 256), -4, -5)]
    {
        let tree = make(numerator);
        let zero = ReceivingRead::combined(vec![rat(0, 1); 4], &tree, 4).unwrap();
        let crossed =
            ReceivingRead::combined(vec![wave, rat(0, 1), rat(0, 1), rat(0, 1)], &tree, 4).unwrap();
        assert_eq!(exponent(&zero.cells[0], 4), BigInt::from(before));
        assert_eq!(exponent(&crossed.cells[0], 4), BigInt::from(after));
    }
    let tree = split_face(2, 4); // exact log2(1/4)+1/4=-7/4 lies exactly on the new boundary
    let edge = ReceivingRead::combined(vec![rat(1, 4), rat(0, 1), rat(0, 1), rat(0, 1)], &tree, 4)
        .unwrap();
    assert_eq!(exponent(&edge.cells[0], 4), BigInt::from(-7));
    assert_eq!(edge.cells[0].fibre.as_rational(), Some(&Rat::zero()));
}

#[test]
fn retained_fibre_receiver_recovers_exact_tree_masses_and_is_common_offset_invariant() {
    let tree = split_face(3, 4); // 3/8 and 5/8: neither class probability is a power of two.
    let receiver = RetainedFibreReceiver::declare(4).unwrap();
    let zero = ReceivingRead::combined(vec![rat(0, 1); 4], &tree, 4).unwrap();
    let masses = receiver.masses_at(&zero, 64).unwrap();
    for (mass, probability) in masses.iter().zip(&tree.probabilities) {
        assert_eq!(*mass, ExactInterval::point(probability.clone()));
    }

    // A common fractional real-wave offset cancels after normalization, while the exterior
    // enclosures still contain the exact tree probabilities.
    let offset =
        ReceivingRead::combined(vec![rat(1, 3), rat(0, 1), rat(1, 3), rat(0, 1)], &tree, 4)
            .unwrap();
    for (mass, probability) in receiver
        .masses_at(&offset, 64)
        .unwrap()
        .iter()
        .zip(&tree.probabilities)
    {
        assert!(mass.lower <= *probability && *probability <= mass.upper);
    }
}

#[test]
fn retained_fibre_mass_preserves_a_wave_hidden_inside_identical_coarse_cells() {
    let tree = split_face(4, 1); // equal 1/2 tree masses
    let read = ReceivingRead::combined(vec![rat(0, 1), rat(0, 1), rat(1, 10), rat(0, 1)], &tree, 1)
        .unwrap();
    assert_eq!(read.cells[0].carry, read.cells[1].carry);
    assert_eq!(read.cells[0].phase, read.cells[1].phase);
    let masses = RetainedFibreReceiver::declare(1)
        .unwrap()
        .masses_at(&read, 64)
        .unwrap();
    assert!(masses[1].lower > masses[0].upper);
}

#[test]
fn retained_fibre_receiver_refuses_bad_declarations_and_malformed_read_identity() {
    assert!(RetainedFibreReceiver::declare(0).is_err());
    let tree = split_face(3, 4);
    let read = ReceivingRead::combined(vec![rat(0, 1); 4], &tree, 4).unwrap();
    assert!(
        RetainedFibreReceiver::declare(8)
            .unwrap()
            .masses_at(&read, 64)
            .is_err()
    );
    assert!(
        RetainedFibreReceiver::declare(4)
            .unwrap()
            .masses_at(&read, 0)
            .is_err()
    );
    let mut wrong_phase = read.clone();
    wrong_phase.phases[0] = rat(1, 3);
    assert!(
        RetainedFibreReceiver::declare(4)
            .unwrap()
            .masses_at(&wrong_phase, 64)
            .is_err()
    );
    let mut wrong_fibre = read.clone();
    if let ReceivingFibre::Logarithmic(fibre) = &mut wrong_fibre.cells[0].fibre {
        fibre.wave += rat(1, 2);
    } else {
        panic!("non-power-of-two tree probability retains a logarithmic fibre");
    }
    assert!(
        RetainedFibreReceiver::declare(4)
            .unwrap()
            .masses_at(&wrong_fibre, 64)
            .is_err()
    );
    let mut wrong_shape = read;
    wrong_shape.cells.pop();
    assert!(
        RetainedFibreReceiver::declare(4)
            .unwrap()
            .masses_at(&wrong_shape, 64)
            .is_err()
    );
}
