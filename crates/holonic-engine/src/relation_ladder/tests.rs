//! Tests for the relation ladder.
//!
//! [definition] Every theorem of
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/RelationLadder.lean` is mirrored
//! here, counterexamples included, together with the negative tests the executable owner owes
//! for every caller-declared size.

use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::One;

use super::*;

// -------------------------------------------------------------------------------------------
// Small exact carriers used by the counterexamples
// -------------------------------------------------------------------------------------------

fn rat(numerator: i64) -> BigRational {
    BigRational::from(BigInt::from(numerator))
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

/// `ThreeSource` of `Foundation/CausalRelevance.lean`: three exact rationals.
type ThreeSource = (BigRational, BigRational, BigRational);

fn three_swap(source: &ThreeSource) -> ThreeSource {
    (source.1.clone(), source.0.clone(), source.2.clone())
}

fn three_flip(source: &ThreeSource) -> ThreeSource {
    (source.0.clone(), source.1.clone(), -source.2.clone())
}

/// `Foundation/CausalRelevance.lean::threeStep` with `firstReceiver`, packaged as a situation.
fn three_situation() -> Situation<ThreeSource, BigRational> {
    Situation::declare(
        vec![
            NamedGenerator::new("swap", |source: &ThreeSource| Ok(three_swap(source))),
            NamedGenerator::new("flip-third", |source: &ThreeSource| Ok(three_flip(source))),
        ],
        vec![NamedReceiver::new("first", |source: &ThreeSource| {
            Ok(source.0.clone())
        })],
        3,
    )
    .expect("the three-step declaration is inside every ceiling")
}

/// `Foundation/RelationLadder.lean::blindStep`: one fixed point and one two-cycle.
fn blind_step(occurrence: &u8) -> u8 {
    match occurrence {
        0 => 0,
        1 => 2,
        2 => 1,
        other => *other,
    }
}

fn blind_situation() -> Situation<u8, ()> {
    Situation::declare(
        vec![NamedGenerator::new("blind-step", |occurrence: &u8| {
            Ok(blind_step(occurrence))
        })],
        vec![NamedReceiver::new("blind", |_: &u8| Ok(()))],
        4,
    )
    .expect("the blind declaration is inside every ceiling")
}

fn blind_bool_situation() -> Situation<bool, ()> {
    Situation::declare(
        vec![NamedGenerator::new("stay", |value: &bool| Ok(*value))],
        vec![NamedReceiver::new("blind", |_: &bool| Ok(()))],
        3,
    )
    .expect("the blind bool declaration is inside every ceiling")
}

fn faithful_bool_situation() -> Situation<bool, bool> {
    Situation::declare(
        vec![NamedGenerator::new("stay", |value: &bool| Ok(*value))],
        vec![NamedReceiver::new("faithful", |value: &bool| Ok(*value))],
        3,
    )
    .expect("the faithful bool declaration is inside every ceiling")
}

/// The declared lineage of the continuation counterexample: one exact step forward.
fn rational_step_situation() -> Situation<BigRational, BigRational> {
    Situation::declare(
        vec![NamedGenerator::new("plus-one", |value: &BigRational| {
            Ok(value + BigRational::one())
        })],
        vec![NamedReceiver::new("value", |value: &BigRational| {
            Ok(value.clone())
        })],
        3,
    )
    .expect("the rational declaration is inside every ceiling")
}

// -------------------------------------------------------------------------------------------
// The typed scale: the order laws, decided over all seven rungs
// -------------------------------------------------------------------------------------------

/// Lean: `entails_refl`, `entails_trans`, `entails_antisymm`.
#[test]
fn the_rung_order_is_a_partial_order() {
    for left in Rung::ALL {
        assert!(left.entails(left), "{left:?} must entail itself");
        for right in Rung::ALL {
            if left.entails(right) && right.entails(left) {
                assert_eq!(left, right, "{left:?} and {right:?} entail each other");
            }
            for third in Rung::ALL {
                if left.entails(right) && right.entails(third) {
                    assert!(
                        left.entails(third),
                        "{left:?} -> {right:?} -> {third:?} must compose"
                    );
                }
            }
        }
    }
}

/// Lean: `entails_is_not_total`. A lineage and a face are different declarations.
#[test]
fn the_rung_order_is_not_total() {
    assert!(!Rung::Continuation.entails(Rung::ReceiverEqual));
    assert!(!Rung::ReceiverEqual.entails(Rung::Continuation));
    assert!(!Rung::Continuation.entails(Rung::EqualPotential));
    assert!(!Rung::EqualPotential.entails(Rung::Continuation));
    assert_eq!(
        rung_meet(Rung::Continuation, Rung::ReceiverEqual),
        Rung::NoRelation
    );
}

/// Lean: `no_rung_below_identity_entails_identity`.
#[test]
fn no_rung_below_identity_entails_identity() {
    for rung in Rung::ALL {
        if rung != Rung::Identity {
            assert!(
                !rung.entails(Rung::Identity),
                "{rung:?} must not ascend to identity"
            );
        }
    }
}

/// Lean: `rungMeet_comm`, `rungMeet_lower`, `rungMeet_greatest`.
#[test]
fn the_rung_meet_is_the_greatest_lower_bound() {
    for left in Rung::ALL {
        for right in Rung::ALL {
            let meet = rung_meet(left, right);
            assert_eq!(meet, rung_meet(right, left));
            assert!(left.entails(meet));
            assert!(right.entails(meet));
            for below in Rung::ALL {
                if left.entails(below) && right.entails(below) {
                    assert!(
                        meet.entails(below),
                        "{meet:?} must be the greatest lower bound of {left:?} and {right:?}"
                    );
                }
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// The transport word is the Lean list
// -------------------------------------------------------------------------------------------

/// `transportWord T (g :: w) x = T g (transportWord T w x)`: the head is applied last.
#[test]
fn a_transport_word_applies_its_head_last() {
    let situation: Situation<BigRational, BigRational> = Situation::declare(
        vec![
            NamedGenerator::new("plus-one", |value: &BigRational| {
                Ok(value + BigRational::one())
            }),
            NamedGenerator::new("times-two", |value: &BigRational| Ok(value * rat(2))),
        ],
        vec![NamedReceiver::new("value", |value: &BigRational| {
            Ok(value.clone())
        })],
        3,
    )
    .expect("declared inside every ceiling");
    // [plus-one, times-two] applied to 3 is plus-one(times-two(3)) = 7.
    let carried = situation
        .transport_word(&[0, 1], &rat(3))
        .expect("no refusal");
    assert_eq!(carried, rat(7));
    // The other order is times-two(plus-one(3)) = 8.
    let other = situation
        .transport_word(&[1, 0], &rat(3))
        .expect("no refusal");
    assert_eq!(other, rat(8));
}

// -------------------------------------------------------------------------------------------
// The constructed counterexamples, mirrored from Lean
// -------------------------------------------------------------------------------------------

/// Lean: `receiverEqualityWithoutEqualPotential` (the three-step example, cited).
#[test]
fn receiver_equality_without_equal_potential() {
    let situation = three_situation();
    let left: ThreeSource = (rat(0), rat(0), rat(0));
    let right: ThreeSource = (rat(0), rat(1), rat(0));

    assert!(
        situation
            .present_agreement(&left, &right)
            .expect("no refusal")
            .is_none(),
        "the declared receiver agrees now"
    );

    let verdict = situation
        .search_separator(&left, &right)
        .expect("no refusal");
    let PotentialVerdict::Separated(separator) = verdict else {
        panic!("one swap must separate them");
    };
    assert_eq!(separator.word_names, vec!["swap".to_owned()]);
    assert_eq!(separator.receiver_name, "first");
    assert_eq!(separator.left_face, rat(0));
    assert_eq!(separator.right_face, rat(1));
}

/// Lean: `equalPotentialWithoutIsomorphism`. The Lean statement is `IsEmpty`; over this finite
/// carrier the executable form is complete — **all six** bijections of the carrier are checked and
/// none both commutes with the generator and carries `0` to `1`.
#[test]
fn equal_potential_without_isomorphism() {
    let situation = blind_situation();
    let probe = [0u8, 1, 2];

    // Nothing any declared receiver will ever read separates 0 from 1.
    let verdict = situation.search_separator(&0u8, &1u8).expect("no refusal");
    assert!(
        matches!(verdict, PotentialVerdict::NotSeparatedWithinBound { .. }),
        "the blind receiver separates nothing"
    );

    const PERMUTATIONS: [[u8; 3]; 6] = [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ];
    let mut carrying = 0usize;
    for permutation in PERMUTATIONS {
        let mut inverse = [0u8; 3];
        for (source, &target) in permutation.iter().enumerate() {
            inverse[target as usize] = source as u8;
        }
        let candidate = SituationAutomorphism::new(
            format!("{permutation:?}"),
            move |occurrence: &u8| Ok(permutation[*occurrence as usize]),
            move |occurrence: &u8| Ok(inverse[*occurrence as usize]),
        );
        let reading = situation
            .check_automorphism(&candidate, &probe)
            .expect("no refusal");
        let carries = permutation[0] == 1;
        if carries {
            carrying += 1;
            assert!(
                !matches!(reading, EquivarianceReading::HeldOnProbe { .. }),
                "no symmetry commuting with the generator carries 0 to 1: {permutation:?}"
            );
            assert!(matches!(
                reading,
                EquivarianceReading::GeneratorSquareFails { .. }
            ));
        }
    }
    assert_eq!(carrying, 2, "two of the six bijections carry 0 to 1");
}

/// Lean: `isomorphismWithoutIdentity`, and the one sound executable route to rung 5.
#[test]
fn isomorphism_without_identity() {
    let situation = blind_bool_situation();
    let probe = [false, true];
    let negation = SituationAutomorphism::new(
        "not",
        |value: &bool| Ok(!*value),
        |value: &bool| Ok(!*value),
    );
    let reading = situation
        .check_automorphism(&negation, &probe)
        .expect("no refusal");
    assert_eq!(reading, EquivarianceReading::HeldOnProbe { probe: 2 });

    let declared = Declarations {
        automorphism: Some(AutomorphismClaim {
            automorphism: &negation,
            probe: &probe,
            probe_is_the_whole_carrier: true,
        }),
        tolerance: None,
    };
    let classification = situation
        .classify(&false, &true, &declared)
        .expect("no refusal");
    assert_eq!(classification.strongest, Rung::Isomorphism);
    assert!(classification.established.contains(&Rung::EqualPotential));
    assert_eq!(classification.next_rung, Some(Rung::Identity));
    assert!(!classification.established.contains(&Rung::Identity));
}

/// A probe stays a probe: the same check with an unclaimed carrier establishes nothing at rung 3.
#[test]
fn a_probe_that_is_not_the_carrier_does_not_establish_the_isomorphism() {
    let situation = blind_bool_situation();
    let probe = [false];
    let negation = SituationAutomorphism::new(
        "not",
        |value: &bool| Ok(!*value),
        |value: &bool| Ok(!*value),
    );
    let declared = Declarations {
        automorphism: Some(AutomorphismClaim {
            automorphism: &negation,
            probe: &probe,
            probe_is_the_whole_carrier: false,
        }),
        tolerance: None,
    };
    let classification = situation
        .classify(&false, &true, &declared)
        .expect("no refusal");
    assert_eq!(classification.strongest, Rung::ReceiverEqual);
    assert!(
        classification
            .notes
            .contains(&ClassificationNote::IsomorphismOnlyOnAProbe)
    );
    assert!(!classification.established.contains(&Rung::EqualPotential));
}

#[test]
fn declaring_a_probe_complete_does_not_supply_its_missing_futures() {
    let situation = Situation::declare(
        vec![NamedGenerator::new("next-pair", |x: &u8| Ok(x.wrapping_add(2)))],
        vec![NamedReceiver::new("distinguishes-next-pair", |x: &u8| Ok(*x == 3))],
        0,
    ).unwrap();
    let symmetry = SituationAutomorphism::new("pair-swap", |x: &u8| Ok(x ^ 1), |x: &u8| Ok(x ^ 1));
    // Both generator squares and receiver triangles hold on [0,1], but the next occurrences
    // 2 and 3 are outside it and the receiver separates those. A caller's `true` cannot certify
    // all futures just because this situation's separator search was requested only at depth 0.
    for probe in [&[][..], &[0u8][..], &[0u8, 1][..]] {
        let result = situation.classify(&0, &1, &Declarations {
            automorphism: Some(AutomorphismClaim {
                automorphism: &symmetry, probe, probe_is_the_whole_carrier: true,
            }),
            tolerance: None,
        }).unwrap();
        assert_eq!(result.strongest, Rung::ReceiverEqual);
        assert!(result.notes.contains(&ClassificationNote::AutomorphismCarrierNotClosed));
        assert!(!result.established.contains(&Rung::EqualPotential));
    }
}

#[test]
fn a_checked_finite_invariant_carrier_establishes_all_its_futures() {
    let situation = Situation::declare(
        vec![NamedGenerator::new("swap", |x: &u8| Ok(x ^ 1))],
        vec![NamedReceiver::new("pair", |x: &u8| Ok(x / 2))],
        0,
    ).unwrap();
    let symmetry = SituationAutomorphism::new("pair-swap", |x: &u8| Ok(x ^ 1), |x: &u8| Ok(x ^ 1));
    let result = situation.classify(&0, &1, &Declarations {
        automorphism: Some(AutomorphismClaim {
            automorphism: &symmetry, probe: &[0, 1], probe_is_the_whole_carrier: true,
        }),
        tolerance: None,
    }).unwrap();
    // This is an invariant subcarrier of u8, sufficient for every word from these endpoints.
    assert_eq!(result.strongest, Rung::Isomorphism);
    assert!(result.established.contains(&Rung::EqualPotential));
}

/// Lean: `continuationWithoutAnyEqualFace`. The lineage is real and every rung below it fails.
#[test]
fn continuation_without_any_equal_face() {
    let situation = rational_step_situation();
    let reached = situation.reaches(&rat(0), &rat(1)).expect("no refusal");
    let ContinuationVerdict::Reached { word, word_names } = reached else {
        panic!("one step forward reaches 1 from 0");
    };
    assert_eq!(word, vec![0]);
    assert_eq!(word_names, vec!["plus-one".to_owned()]);

    assert!(
        situation
            .present_agreement(&rat(0), &rat(1))
            .expect("no refusal")
            .is_some(),
        "the declared receiver separates them now"
    );
    let verdict = situation
        .search_separator(&rat(0), &rat(1))
        .expect("no refusal");
    assert!(matches!(verdict, PotentialVerdict::Separated(_)));

    let reading = ToleranceReading::declare(
        "value",
        |value: &BigRational| Ok(value.clone()),
        ratio(1, 2),
    )
    .expect("a non-negative tolerance");
    assert!(!reading.holds(&rat(0), &rat(1)).expect("no refusal"));
}

/// Lean: `lossyContinuationIsNotAnIsomorphism`. The `Transition` law holds, the transported map
/// is not injective, and the residual is what separates.
#[test]
fn lossy_continuation_is_not_an_isomorphism() {
    type Pair = (BigRational, BigRational);
    let apply = |pair: &Pair| pair.0.clone();
    let residual = |pair: &Pair| pair.1.clone();
    let reopen = |face: BigRational, kept: BigRational| (face, kept);

    let left: Pair = (rat(0), rat(0));
    let right: Pair = (rat(0), rat(1));

    // `reopen_apply`: the transported face together with the residual is exactly the source.
    assert_eq!(reopen(apply(&left), residual(&left)), left);
    assert_eq!(reopen(apply(&right), residual(&right)), right);

    // Two distinct occurrences continue to one face: the passage is lossy, not invertible.
    assert_ne!(left, right);
    assert_eq!(apply(&left), apply(&right));
    // And the residual is exactly what a later finer receiver would need.
    assert_ne!(residual(&left), residual(&right));

    // Read as a situation, the coarse receiver agrees and the finer one separates.
    let coarse: Situation<Pair, BigRational> = Situation::declare(
        vec![NamedGenerator::new("stay", |pair: &Pair| Ok(pair.clone()))],
        vec![NamedReceiver::new("first", |pair: &Pair| Ok(pair.0.clone()))],
        2,
    )
    .expect("declared inside every ceiling");
    assert!(
        coarse
            .present_agreement(&left, &right)
            .expect("no refusal")
            .is_none()
    );
    let fine: Situation<Pair, BigRational> = Situation::declare(
        vec![NamedGenerator::new("stay", |pair: &Pair| Ok(pair.clone()))],
        vec![NamedReceiver::new("second", |pair: &Pair| Ok(pair.1.clone()))],
        2,
    )
    .expect("declared inside every ceiling");
    assert!(
        fine.present_agreement(&left, &right)
            .expect("no refusal")
            .is_some()
    );
}

/// Lean: `receiverEquivarianceIsNecessary`. The generator square holds and the receiver triangle
/// does not, and the potentials differ.
#[test]
fn receiver_equivariance_is_necessary() {
    let situation = faithful_bool_situation();
    let negation = SituationAutomorphism::new(
        "not",
        |value: &bool| Ok(!*value),
        |value: &bool| Ok(!*value),
    );
    let reading = situation
        .check_automorphism(&negation, &[false, true])
        .expect("no refusal");
    match reading {
        EquivarianceReading::ReceiverTriangleFails { receiver, .. } => {
            assert_eq!(receiver, "faithful");
        }
        other => panic!("the receiver triangle must be what fails: {other:?}"),
    }
    let verdict = situation
        .search_separator(&false, &true)
        .expect("no refusal");
    let PotentialVerdict::Separated(separator) = verdict else {
        panic!("the faithful receiver separates at the empty history");
    };
    assert!(separator.word.is_empty());
}

/// Lean: `generatorEquivarianceIsNecessary`. The receiver triangle holds and the generator square
/// does not, and the potentials differ.
#[test]
fn generator_equivariance_is_necessary() {
    let situation = three_situation();
    let shift_second = SituationAutomorphism::new(
        "shift-second",
        |source: &ThreeSource| {
            Ok((
                source.0.clone(),
                &source.1 + BigRational::one(),
                source.2.clone(),
            ))
        },
        |source: &ThreeSource| {
            Ok((
                source.0.clone(),
                &source.1 - BigRational::one(),
                source.2.clone(),
            ))
        },
    );
    let probe = [
        (rat(0), rat(0), rat(0)),
        (rat(1), rat(0), rat(0)),
        (rat(0), rat(1), rat(0)),
    ];
    let reading = situation
        .check_automorphism(&shift_second, &probe)
        .expect("no refusal");
    match reading {
        EquivarianceReading::GeneratorSquareFails { generator, .. } => {
            assert_eq!(generator, "swap");
        }
        other => panic!("the generator square must be what fails: {other:?}"),
    }
    // And the symmetry does carry (0,0,0) to (0,1,0), whose potentials differ.
    let carried = shift_second
        .forward(&(rat(0), rat(0), rat(0)))
        .expect("no refusal");
    assert_eq!(carried, (rat(0), rat(1), rat(0)));
    assert!(matches!(
        situation
            .search_separator(&(rat(0), rat(0), rat(0)), &(rat(0), rat(1), rat(0)))
            .expect("no refusal"),
        PotentialVerdict::Separated(_)
    ));
}

/// Lean: `toleranceIsNotTransitive` and `toleranceIsWithoutIdentification`.
#[test]
fn a_tolerance_is_not_transitive_and_identifies_nothing() {
    let reading =
        ToleranceReading::declare("value", |value: &BigRational| Ok(value.clone()), rat(1))
            .expect("a non-negative tolerance");
    assert!(reading.holds(&rat(0), &rat(1)).expect("no refusal"));
    assert!(reading.holds(&rat(1), &rat(2)).expect("no refusal"));
    assert!(!reading.holds(&rat(0), &rat(2)).expect("no refusal"));
    // Reflexive and symmetric, which is all it is.
    assert!(reading.holds(&rat(5), &rat(5)).expect("no refusal"));
    assert!(reading.holds(&rat(2), &rat(1)).expect("no refusal"));
    // And it identifies nothing: a receiver equality would have.
    assert_ne!(rat(0), rat(1));
}

/// Lean: `withinToleranceIterate`. An `n`-step chain lies inside `n * epsilon` and the bound
/// degrades linearly.
#[test]
fn a_tolerance_chain_degrades_linearly() {
    let steps = 4i64;
    let epsilon = rat(1);
    for step in 0..steps {
        let near = ToleranceReading::declare(
            "value",
            |value: &BigRational| Ok(value.clone()),
            epsilon.clone(),
        )
        .expect("a non-negative tolerance");
        assert!(
            near.holds(&rat(step), &rat(step + 1)).expect("no refusal"),
            "each step is inside epsilon"
        );
    }
    let widened = ToleranceReading::declare(
        "value",
        |value: &BigRational| Ok(value.clone()),
        BigRational::from(BigInt::from(steps)) * epsilon.clone(),
    )
    .expect("a non-negative tolerance");
    assert!(widened.holds(&rat(0), &rat(steps)).expect("no refusal"));
    let unwidened =
        ToleranceReading::declare("value", |value: &BigRational| Ok(value.clone()), epsilon)
            .expect("a non-negative tolerance");
    assert!(
        !unwidened.holds(&rat(0), &rat(steps)).expect("no refusal"),
        "the chain does not close at the original tolerance"
    );
}

/// Lean: `noRungBelowIdentityAscendsToIdentity`. Each of rungs 2–6 is inhabited by a pair that is
/// not identical.
#[test]
fn no_rung_below_identity_ascends_to_identity() {
    // Rung 2: a continuation whose endpoints are not identical.
    let stepping = rational_step_situation();
    assert!(matches!(
        stepping.reaches(&rat(0), &rat(1)).expect("no refusal"),
        ContinuationVerdict::Reached { .. }
    ));
    assert_ne!(rat(0), rat(1));

    // Rung 3: an isomorphism whose endpoints are not identical.
    let blind = blind_bool_situation();
    let negation = SituationAutomorphism::new(
        "not",
        |value: &bool| Ok(!*value),
        |value: &bool| Ok(!*value),
    );
    assert_eq!(
        blind
            .check_automorphism(&negation, &[false, true])
            .expect("no refusal"),
        EquivarianceReading::HeldOnProbe { probe: 2 }
    );
    assert_ne!(false, true);

    // Rung 4: receiver equality without identity.
    let three = three_situation();
    assert!(
        three
            .present_agreement(&(rat(0), rat(0), rat(0)), &(rat(0), rat(1), rat(0)))
            .expect("no refusal")
            .is_none()
    );
    assert_ne!(
        (rat(0), rat(0), rat(0)),
        (rat(0), rat(1), rat(0)) as ThreeSource
    );

    // Rung 5: equal potential (established by the exhaustive symmetry) without identity.
    let classification = blind
        .classify(
            &false,
            &true,
            &Declarations {
                automorphism: Some(AutomorphismClaim {
                    automorphism: &negation,
                    probe: &[false, true],
                    probe_is_the_whole_carrier: true,
                }),
                tolerance: None,
            },
        )
        .expect("no refusal");
    assert!(classification.established.contains(&Rung::EqualPotential));
    assert_ne!(classification.strongest, Rung::Identity);

    // Rung 6: a tolerance without identity.
    let reading =
        ToleranceReading::declare("value", |value: &BigRational| Ok(value.clone()), rat(1))
            .expect("a non-negative tolerance");
    assert!(reading.holds(&rat(0), &rat(1)).expect("no refusal"));
    assert_ne!(rat(0), rat(1));
}

// -------------------------------------------------------------------------------------------
// Worked instance (a): `Expression` against `eval`
// -------------------------------------------------------------------------------------------

/// Lean: `fourAndTwoSquaredAgreeUnderEval` and `fourAndTwoSquaredAreNotIdentical`.
#[test]
fn four_and_two_squared_agree_under_eval_and_are_not_identical() {
    assert_eq!(
        eval(&four()).expect("inside every ceiling"),
        eval(&two_squared()).expect("inside every ceiling")
    );
    assert_eq!(eval(&four()).expect("inside every ceiling"), BigUint::from(4u32));
    assert_ne!(four(), two_squared());
}

/// Lean: `bumpExponentSeparatesThem`. The equality belongs to the scalar receiver and does not
/// ascend: one construction generator separates the two formulations.
#[test]
fn the_construction_generator_separates_four_from_two_squared() {
    let situation = construction_situation().expect("declared inside every ceiling");
    let verdict = situation
        .search_separator(&four(), &two_squared())
        .expect("no refusal");
    let PotentialVerdict::Separated(separator) = verdict else {
        panic!("bumping the exponent must separate them");
    };
    assert_eq!(separator.word_names, vec!["bump-exponent".to_owned()]);
    assert_eq!(separator.left_face, BigUint::from(4u32));
    assert_eq!(separator.right_face, BigUint::from(8u32));
}

/// Lean: `postcomposeFamilyGivesEqualPotential`, in its honest executable form. Under a generator
/// family that only post-composes `eval`, the bounded search finds no separator — and that is
/// reported as its own return and **never** as equal potential.
#[test]
fn not_separated_within_the_bound_is_never_reported_as_equal_potential() {
    let situation = value_situation().expect("declared inside every ceiling");
    let verdict = situation
        .search_separator(&four(), &two_squared())
        .expect("no refusal");
    match verdict {
        PotentialVerdict::NotSeparatedWithinBound {
            history_length,
            histories_examined,
            receivers,
        } => {
            assert_eq!(history_length, 4);
            // sum_{k=0..4} 2^k = 31 ordered histories.
            assert_eq!(histories_examined, 31);
            assert_eq!(receivers, 1);
        }
        PotentialVerdict::Separated(separator) => {
            panic!("the value-only family cannot reach the construction: {separator:?}")
        }
    }
    let classification = situation
        .classify(&four(), &two_squared(), &Declarations::default())
        .expect("no refusal");
    assert_eq!(classification.strongest, Rung::ReceiverEqual);
    assert!(
        !classification.established.contains(&Rung::EqualPotential),
        "an exhausted bound establishes no potential equality"
    );
    assert!(
        classification
            .notes
            .contains(&ClassificationNote::NotSeparatedWithinBound)
    );
    assert_eq!(classification.next_rung, Some(Rung::EqualPotential));
}

/// Lean: `enlargingTheGeneratorFamilyRefines` and `equalPotentialAntitone`. Adding a generator can
/// only split a potential class, never merge it.
#[test]
fn enlarging_the_generator_family_refines_the_potential_class() {
    let small = value_situation().expect("declared inside every ceiling");
    let large = joint_expression_situation().expect("declared inside every ceiling");
    assert!(matches!(
        small
            .search_separator(&four(), &two_squared())
            .expect("no refusal"),
        PotentialVerdict::NotSeparatedWithinBound { .. }
    ));
    let verdict = large
        .search_separator(&four(), &two_squared())
        .expect("no refusal");
    let PotentialVerdict::Separated(separator) = verdict else {
        panic!("the enlarged family separates");
    };
    assert_eq!(separator.word_names, vec!["bump-exponent".to_owned()]);
}

/// The classifier reports rung 2 beside the chain, because it is relative to a lineage.
#[test]
fn the_classifier_reports_continuation_beside_the_chain() {
    let situation = rational_step_situation();
    let classification = situation
        .classify(&rat(0), &rat(1), &Declarations::default())
        .expect("no refusal");
    assert_eq!(classification.strongest, Rung::NoRelation);
    assert!(classification.established.contains(&Rung::Continuation));
    assert!(matches!(
        classification.continuation,
        ContinuationVerdict::Reached { .. }
    ));
    assert!(
        classification
            .notes
            .contains(&ClassificationNote::NoToleranceDeclared)
    );
}

/// Lean: `equalPotentialWithoutAGeneratorContinuation`. Rung 5 and rung 2 are genuinely
/// incomparable: the transports never reach.
#[test]
fn equal_potential_without_a_generator_continuation() {
    let situation = blind_situation();
    assert!(matches!(
        situation.search_separator(&0u8, &1u8).expect("no refusal"),
        PotentialVerdict::NotSeparatedWithinBound { .. }
    ));
    assert!(matches!(
        situation.reaches(&0u8, &1u8).expect("no refusal"),
        ContinuationVerdict::NotReachedWithinBound { .. }
    ));
}

// -------------------------------------------------------------------------------------------
// Worked instance (b): the same song
// -------------------------------------------------------------------------------------------

/// Lean: `theTwoEnactmentsAgreeMusically`.
#[test]
fn the_two_enactments_agree_musically() {
    let first = first_enactment().expect("declared inside every ceiling");
    let second = second_enactment().expect("declared inside every ceiling");
    assert_eq!(musical_face(&first), musical_face(&second));
    assert_eq!(
        musical_face(&first),
        (vec![rat(2), rat(2)], vec![rat(1), rat(1)])
    );
}

/// Lean: `admissibleTransformationsAreMusicallyInvisible`.
#[test]
fn every_admissible_transformation_is_musically_invisible() {
    let first = first_enactment().expect("declared inside every ceiling");
    for transformation in [
        Admissible::Transpose(rat(7)),
        Admissible::Transpose(ratio(-3, 2)),
        Admissible::ScaleTempo(rat(2)),
        Admissible::ScaleTempo(ratio(1, 3)),
        Admissible::Revoice(9),
    ] {
        let carried = enact(&transformation, &first).expect("admissible");
        assert_eq!(
            musical_face(&carried),
            musical_face(&first),
            "{transformation:?} must be musically invisible"
        );
    }
}

/// Lean: `theAbsoluteReceiverSeparatesThem` and `theSongIsTheFamilyNotOneEnactment`.
#[test]
fn the_song_is_the_family_not_one_enactment() {
    let first = first_enactment().expect("declared inside every ceiling");
    let second = second_enactment().expect("declared inside every ceiling");
    assert_ne!(first, second);
    assert_ne!(absolute_face(&first), absolute_face(&second));

    let song = song_situation().expect("declared inside every ceiling");
    assert!(
        song.present_agreement(&first, &second)
            .expect("no refusal")
            .is_none(),
        "the musical receiver reads one class"
    );
    assert!(
        matches!(
            song.search_separator(&first, &second).expect("no refusal"),
            PotentialVerdict::NotSeparatedWithinBound { .. }
        ),
        "no admissible history separates them"
    );

    let absolute = absolute_situation().expect("declared inside every ceiling");
    let verdict = absolute
        .search_separator(&first, &second)
        .expect("no refusal");
    let PotentialVerdict::Separated(separator) = verdict else {
        panic!("the richer receiver separates the two enactments");
    };
    assert!(separator.word.is_empty(), "it separates them already now");
    assert_eq!(separator.receiver_name, "absolute");
}

/// The musical receiver is exactly transposition- and tempo-invariant, and nothing more.
#[test]
fn the_musical_receiver_is_exactly_the_declared_invariance() {
    let first = first_enactment().expect("declared inside every ceiling");
    let uneven = Enactment::declare(
        vec![rat(0), rat(2), rat(5)],
        vec![rat(0), rat(1), rat(2)],
        0,
    )
    .expect("declared inside every ceiling");
    assert_ne!(
        musical_face(&first),
        musical_face(&uneven),
        "a different interval contour is a different class"
    );
    let stretched = Enactment::declare(
        vec![rat(0), rat(2), rat(4)],
        vec![rat(0), rat(1), rat(3)],
        0,
    )
    .expect("declared inside every ceiling");
    assert_ne!(
        musical_face(&first),
        musical_face(&stretched),
        "a different rhythm-ratio contour is a different class"
    );
}

// -------------------------------------------------------------------------------------------
// Hostile input: every caller-declared size is checked before it is used
// -------------------------------------------------------------------------------------------

#[test]
fn a_situation_with_no_receiver_is_refused() {
    let refusal = Situation::<u8, ()>::declare(Vec::new(), Vec::new(), 1)
        .expect_err("a situation with no receiver declares nothing");
    assert_eq!(refusal, LadderRefusal::NoReceiverDeclared);
}

#[test]
fn an_oversized_generator_family_is_refused() {
    let generators: Vec<NamedGenerator<u8>> = (0..=GENERATOR_CEILING)
        .map(|index| NamedGenerator::new(format!("g{index}"), |value: &u8| Ok(*value)))
        .collect();
    let refusal = Situation::<u8, ()>::declare(
        generators,
        vec![NamedReceiver::new("blind", |_: &u8| Ok(()))],
        1,
    )
    .expect_err("above the generator ceiling");
    assert_eq!(
        refusal,
        LadderRefusal::GeneratorFamilyTooLarge {
            declared: GENERATOR_CEILING + 1,
            ceiling: GENERATOR_CEILING,
        }
    );
}

#[test]
fn an_oversized_receiver_family_is_refused() {
    let receivers: Vec<NamedReceiver<u8, ()>> = (0..=RECEIVER_CEILING)
        .map(|index| NamedReceiver::new(format!("r{index}"), |_: &u8| Ok(())))
        .collect();
    let refusal = Situation::<u8, ()>::declare(Vec::new(), receivers, 1)
        .expect_err("above the receiver ceiling");
    assert_eq!(
        refusal,
        LadderRefusal::ReceiverFamilyTooLarge {
            declared: RECEIVER_CEILING + 1,
            ceiling: RECEIVER_CEILING,
        }
    );
}

#[test]
fn an_oversized_history_ceiling_is_refused() {
    let refusal = Situation::<u8, ()>::declare(
        Vec::new(),
        vec![NamedReceiver::new("blind", |_: &u8| Ok(()))],
        HISTORY_LENGTH_CEILING + 1,
    )
    .expect_err("above the history-length ceiling");
    assert_eq!(
        refusal,
        LadderRefusal::HistoryLengthTooLarge {
            declared: HISTORY_LENGTH_CEILING + 1,
            ceiling: HISTORY_LENGTH_CEILING,
        }
    );
}

/// The combinatorial family is never materialized: its population is computed with checked
/// arithmetic and refused before any walk begins.
#[test]
fn an_oversized_history_population_is_refused_before_enumeration() {
    let generators: Vec<NamedGenerator<u8>> = (0..8)
        .map(|index| NamedGenerator::new(format!("g{index}"), |value: &u8| Ok(*value)))
        .collect();
    let refusal = Situation::<u8, ()>::declare(
        generators,
        vec![NamedReceiver::new("blind", |_: &u8| Ok(()))],
        HISTORY_LENGTH_CEILING,
    )
    .expect_err("8^20 ordered histories are far above the ceiling");
    match refusal {
        LadderRefusal::HistoryPopulationTooLarge {
            generators, length, ..
        } => {
            assert_eq!(generators, 8);
            assert_eq!(length, HISTORY_LENGTH_CEILING);
        }
        other => panic!("the population must be what refuses: {other}"),
    }
}

#[test]
fn a_negative_tolerance_is_refused() {
    let refusal = ToleranceReading::declare(
        "value",
        |value: &BigRational| Ok(value.clone()),
        rat(-1),
    )
    .expect_err("a negative tolerance names no aperture");
    assert_eq!(refusal, LadderRefusal::NegativeTolerance);
}

#[test]
fn an_oversized_automorphism_probe_is_refused() {
    let situation = blind_situation();
    let probe = vec![0u8; AUTOMORPHISM_PROBE_CEILING + 1];
    let identity =
        SituationAutomorphism::new("identity", |value: &u8| Ok(*value), |value: &u8| Ok(*value));
    let refusal = situation
        .check_automorphism(&identity, &probe)
        .expect_err("above the probe ceiling");
    assert_eq!(
        refusal,
        LadderRefusal::OccurrenceProbeTooLarge {
            declared: AUTOMORPHISM_PROBE_CEILING + 1,
            ceiling: AUTOMORPHISM_PROBE_CEILING,
        }
    );
}

#[test]
fn an_unpaired_or_oversized_enactment_is_refused() {
    let refusal = Enactment::declare(vec![rat(0), rat(1)], vec![rat(0)], 0)
        .expect_err("a note needs both a pitch and an onset");
    assert_eq!(
        refusal,
        LadderRefusal::UnpairedEnactment {
            pitches: 2,
            onsets: 1
        }
    );
    let long = vec![rat(0); SEQUENCE_CEILING + 1];
    let refusal = Enactment::declare(long.clone(), long, 0).expect_err("above the sequence ceiling");
    assert_eq!(
        refusal,
        LadderRefusal::SequenceTooLong {
            declared: SEQUENCE_CEILING + 1,
            ceiling: SEQUENCE_CEILING,
        }
    );
}

#[test]
fn a_zero_tempo_factor_is_not_admissible() {
    let first = first_enactment().expect("declared inside every ceiling");
    let refusal = enact(&Admissible::ScaleTempo(rat(0)), &first)
        .expect_err("a zero factor collapses every onset");
    assert_eq!(refusal, LadderRefusal::ZeroTempoFactor);
}

#[test]
fn eval_refuses_an_exponent_above_the_ceiling() {
    let wild = Expression::Pow(
        Box::new(Expression::lit(2)),
        Box::new(Expression::Lit(BigUint::from(EXPONENT_CEILING + 1))),
    );
    let refusal = eval(&wild).expect_err("above the exponent ceiling");
    assert_eq!(
        refusal,
        LadderRefusal::ExponentTooLarge {
            ceiling: EXPONENT_CEILING
        }
    );
}

#[test]
fn eval_refuses_a_value_wider_than_the_ceiling() {
    let wide = Expression::Pow(
        Box::new(Expression::lit(1000)),
        Box::new(Expression::lit(4000)),
    );
    let refusal = eval(&wide).expect_err("above the value bit ceiling");
    assert!(matches!(refusal, LadderRefusal::ValueTooWide { .. }));
}

/// A product doubles the width, so `eval` bounds it before forming it: a depth-bounded tree of
/// products would otherwise amplify exponentially.
#[test]
fn eval_refuses_a_product_or_literal_wider_than_the_ceiling() {
    let wide_literal = Expression::Lit(BigUint::one() << (VALUE_BIT_CEILING + 1));
    assert!(matches!(
        eval(&wide_literal).expect_err("a literal is itself a declared size"),
        LadderRefusal::ValueTooWide { .. }
    ));

    let half = Expression::Lit(BigUint::one() << (VALUE_BIT_CEILING / 2 + 8));
    let product = Expression::Mul(Box::new(half.clone()), Box::new(half));
    assert!(matches!(
        eval(&product).expect_err("the product is wider than the ceiling"),
        LadderRefusal::ValueTooWide { .. }
    ));

    // A doubling chain: each product is checked before it is formed, so the chain refuses rather
    // than allocating.
    let mut doubling = Expression::Lit(BigUint::one() << 1024);
    for _ in 0..8 {
        doubling = Expression::Mul(Box::new(doubling.clone()), Box::new(doubling));
    }
    assert!(matches!(
        eval(&doubling).expect_err("the doubling chain is refused"),
        LadderRefusal::ValueTooWide { .. }
    ));
}

#[test]
fn eval_refuses_an_expression_deeper_than_the_ceiling() {
    let mut deep = Expression::lit(1);
    for _ in 0..(EXPRESSION_DEPTH_CEILING + 2) {
        deep = Expression::Add(Box::new(deep), Box::new(Expression::lit(0)));
    }
    let refusal = eval(&deep).expect_err("above the depth ceiling");
    assert_eq!(
        refusal,
        LadderRefusal::ExpressionTooDeep {
            ceiling: EXPRESSION_DEPTH_CEILING
        }
    );
}

/// A refusal inside a generator or a receiver propagates as a typed refusal of the whole search;
/// it never becomes a wrong verdict.
#[test]
fn a_refusing_receiver_refuses_the_whole_search() {
    let situation: Situation<Expression, BigUint> = Situation::declare(
        vec![NamedGenerator::new("stay", |expression: &Expression| {
            Ok(expression.clone())
        })],
        vec![NamedReceiver::new("eval", |expression: &Expression| {
            eval(expression)
        })],
        1,
    )
    .expect("declared inside every ceiling");
    let wild = Expression::Pow(
        Box::new(Expression::lit(2)),
        Box::new(Expression::Lit(BigUint::from(EXPONENT_CEILING + 1))),
    );
    let refusal = situation
        .search_separator(&four(), &wild)
        .expect_err("the receiver refuses, so the search refuses");
    assert_eq!(
        refusal,
        LadderRefusal::ExponentTooLarge {
            ceiling: EXPONENT_CEILING
        }
    );
}

/// The declared history population is exactly `sum_{k=0..L} |G|^k`, and it is what the walk
/// examines.
#[test]
fn the_declared_history_population_is_what_the_walk_examines() {
    let situation = value_situation().expect("declared inside every ceiling");
    assert_eq!(situation.history_ceiling(), 4);
    assert_eq!(situation.history_population(), 31);
    let PotentialVerdict::NotSeparatedWithinBound {
        histories_examined, ..
    } = situation
        .search_separator(&four(), &four())
        .expect("no refusal")
    else {
        panic!("one occurrence never separates from itself");
    };
    assert_eq!(histories_examined, situation.history_population());
}

/// A history naming a generator the situation does not declare is refused by name; it never
/// indexes out of bounds and never silently truncates.
#[test]
fn an_undeclared_generator_index_is_refused() {
    let situation = rational_step_situation();
    let refusal = situation
        .transport_word(&[0, 99], &rat(0))
        .expect_err("the history names an undeclared generator");
    assert_eq!(
        refusal,
        LadderRefusal::UndeclaredGenerator {
            index: 99,
            declared: 1
        }
    );
    // The declared indices still transport exactly.
    assert_eq!(
        situation.transport_word(&[0, 0], &rat(0)).expect("no refusal"),
        rat(2)
    );
}
