//! Tests for [`crate::bridge`]. Every test names the Lean declaration of `Foundation/Bridge.lean`
//! it mirrors; the grade and status laws are checked exhaustively over the finite carriers, which
//! is the executable form of Lean's `decide`.

use num_bigint::{BigInt, BigUint};
use num_traits::CheckedSub;

use super::*;
use crate::continuing_tower::{CoarseGrain, ExactShift, NoResidual, Transition};
use crate::grain_tower::{Grain, GrainAddress, GrainFace, GrainPair, GrainSelection};
use crate::physical_constraint_complex::ContactClass;

// -------------------------------------------------------------------------------------------
// The grade algebra
// -------------------------------------------------------------------------------------------

/// Lean: `composeGrade_comm`, checked over all 121 pairs.
#[test]
fn compose_grade_is_symmetric() {
    for a in EpistemicGrade::ALL {
        for b in EpistemicGrade::ALL {
            assert_eq!(
                compose_grade(a, b),
                compose_grade(b, a),
                "composition of {a:?} and {b:?} must not depend on the order"
            );
        }
    }
}

/// Lean: `composeGrade_assoc`, checked over all 1331 triples.
#[test]
fn compose_grade_is_associative() {
    for a in EpistemicGrade::ALL {
        for b in EpistemicGrade::ALL {
            for c in EpistemicGrade::ALL {
                let left = compose_grade(a, b).and_then(|ab| compose_grade(ab, c));
                let right = compose_grade(b, c).and_then(|bc| compose_grade(a, bc));
                assert_eq!(left, right, "{a:?}, {b:?}, {c:?}");
            }
        }
    }
}

/// Lean: `composeGrade_support_le`. The composite never claims more support than either link.
#[test]
fn compose_grade_never_exceeds_either_support() {
    for a in EpistemicGrade::ALL {
        for b in EpistemicGrade::ALL {
            let Some(g) = compose_grade(a, b) else {
                continue;
            };
            let (sa, sb, sg) = (
                a.support().expect("a composed grade has support"),
                b.support().expect("a composed grade has support"),
                g.support().expect("the composite has support"),
            );
            assert!(sg.rank() <= sa.rank() && sg.rank() <= sb.rank(), "{a:?} {b:?}");
        }
    }
}

/// Lean: `counterexample_does_not_compose` and `historical_does_not_compose`. A refutation is not a
/// link, and preserved provenance does not govern construction.
#[test]
fn a_counterexample_or_historical_link_composes_with_nothing() {
    for b in EpistemicGrade::ALL {
        assert_eq!(compose_grade(EpistemicGrade::Counterexample, b), None);
        assert_eq!(compose_grade(EpistemicGrade::Historical, b), None);
        assert_eq!(compose_grade(b, EpistemicGrade::Counterexample), None);
        assert_eq!(compose_grade(b, EpistemicGrade::Historical), None);
    }
}

/// The support reading is a declared reading of each grade, not an ordering of the canon's grades.
/// It is total on the nine grades that are support and absent on the two that are dispositions.
#[test]
fn the_support_reading_is_declared_for_exactly_nine_grades() {
    let supported = EpistemicGrade::ALL
        .into_iter()
        .filter(|g| g.support().is_some())
        .count();
    assert_eq!(supported, 9);
    assert!(EpistemicGrade::Counterexample.support().is_none());
    assert!(EpistemicGrade::Historical.support().is_none());
    for level in SupportLevel::ALL {
        assert_eq!(
            level.representative().support(),
            Some(level),
            "each level's representative reads back at that level"
        );
    }
}

// -------------------------------------------------------------------------------------------
// The status order
// -------------------------------------------------------------------------------------------

/// Lean: `entails_refl`, `entails_trans`, `entails_antisymm`. Checked over all 8, 512 and 64 cases.
#[test]
fn entailment_is_a_partial_order() {
    for a in BridgeStatus::ALL {
        assert!(a.entails(a), "{a:?} entails itself");
        for b in BridgeStatus::ALL {
            if a.entails(b) && b.entails(a) {
                assert_eq!(a, b, "antisymmetry: {a:?} and {b:?}");
            }
            for c in BridgeStatus::ALL {
                if a.entails(b) && b.entails(c) {
                    assert!(a.entails(c), "transitivity: {a:?} {b:?} {c:?}");
                }
            }
        }
    }
}

/// Lean: `equivalence_entails_map`, `naturalFamily_entails_structurePreserving`,
/// `sharedReceiverFace_entails_coPresence`.
#[test]
fn the_implications_that_hold() {
    assert!(BridgeStatus::Equivalence.entails(BridgeStatus::StructurePreservingMap));
    assert!(BridgeStatus::StructurePreservingMap.entails(BridgeStatus::ActualMap));
    assert!(BridgeStatus::ActualMap.entails(BridgeStatus::CoPresence));
    assert!(BridgeStatus::NaturalFamily.entails(BridgeStatus::StructurePreservingMap));
    assert!(BridgeStatus::SharedReceiverFace.entails(BridgeStatus::CoPresence));
    assert!(BridgeStatus::NumericalResemblance.entails(BridgeStatus::CoPresence));
}

/// Lean: `sharedReceiverFace_not_actualMap` and `sharedReceiverFace_supplies_no_map`. The witness
/// is `Foundation/Receiver.lean`'s insufficiency: a blind reading identifies two occurrences a
/// faithful reading separates, so **no** function of the shared face returns the faithful one.
#[test]
fn a_shared_receiver_face_does_not_yield_a_map() {
    assert!(!BridgeStatus::SharedReceiverFace.entails(BridgeStatus::ActualMap));

    let blind = |_x: u8| 0u8;
    let faithful = |x: u8| x;
    assert_eq!(blind(0), blind(1), "the shared face identifies them");
    assert_ne!(faithful(0), faithful(1), "the later receiver separates them");
    // A function `g` with `g(blind(x)) = faithful(x)` would have to return both 0 and 1 at the one
    // entering face, so there is none.
}

/// Lean: `actualMap_not_structurePreserving` and `actualMap_does_not_preserve_structure`. An
/// `ExactShift` is a perfectly good map with zero residual whose square with a doubling
/// restriction does not commute.
#[test]
fn an_actual_map_need_not_preserve_structure() {
    assert!(!BridgeStatus::ActualMap.entails(BridgeStatus::StructurePreservingMap));

    let shift = ExactShift::new(BigInt::from(1));
    let double = |x: &BigInt| x * BigInt::from(2);
    let x = BigInt::from(3);
    assert_ne!(
        double(&shift.apply(&x)),
        shift.apply(&double(&x)),
        "a map that is not natural in the restriction preserves no diagram"
    );
}

/// Lean: `equivalence_not_naturalFamily` and `equivalence_does_not_give_a_natural_family`. The
/// witness is the same shift read as an equivalence: componentwise invertibility says nothing about
/// naturality in the parameter.
#[test]
fn an_equivalence_does_not_give_a_natural_family() {
    assert!(!BridgeStatus::Equivalence.entails(BridgeStatus::NaturalFamily));

    let rebase = ExactRebase::new(BigInt::from(1));
    assert_eq!(
        rebase.check_reopen(&BigInt::from(9)),
        Ok(crate::continuing_tower::ReopenReceipt {
            sources_reopened: 1
        }),
        "the rebase is invertible: its residual is one-valued"
    );
    let double = |x: &BigInt| x * BigInt::from(2);
    let x = BigInt::from(3);
    assert_ne!(double(&rebase.apply(&x)), rebase.apply(&double(&x)));
}

/// Lean: `numericalResemblance_not_sharedReceiverFace` and
/// `numericalResemblance_does_not_identify`. Exact integers: `3` and `4` resemble within tolerance
/// `1`, and the identity receiver separates them. A tolerance is an aperture, never an
/// identification.
#[test]
fn numerical_resemblance_does_not_identify() {
    assert!(!BridgeStatus::NumericalResemblance.entails(BridgeStatus::SharedReceiverFace));
    let (a, b) = (BigInt::from(3), BigInt::from(4));
    assert!((&a - &b).magnitude() <= &BigUint::from(1u32));
    assert_ne!(a, b);
}

/// Lean: `coPresence_gives_nothing`.
#[test]
fn co_presence_gives_nothing() {
    assert!(!BridgeStatus::CoPresence.entails(BridgeStatus::NumericalResemblance));
    assert!(!BridgeStatus::CoPresence.entails(BridgeStatus::SharedReceiverFace));
    assert!(!BridgeStatus::CoPresence.entails(BridgeStatus::ActualMap));
}

/// Lean: `speculativeAnalogy_is_off_the_order`. It entails nothing but itself, and nothing else
/// entails it.
#[test]
fn a_speculative_analogy_is_off_the_order() {
    for other in BridgeStatus::ALL {
        if other == BridgeStatus::SpeculativeAnalogy {
            continue;
        }
        assert!(!BridgeStatus::SpeculativeAnalogy.entails(other));
        assert!(!other.entails(BridgeStatus::SpeculativeAnalogy));
        assert_eq!(status_meet(BridgeStatus::SpeculativeAnalogy, other), None);
        assert_eq!(status_meet(other, BridgeStatus::SpeculativeAnalogy), None);
    }
}

/// Lean: `statusMeet_comm`, `statusMeet_lower`, `statusMeet_greatest`, checked exhaustively.
#[test]
fn the_meet_is_the_greatest_lower_bound() {
    for a in BridgeStatus::ALL {
        for b in BridgeStatus::ALL {
            assert_eq!(status_meet(a, b), status_meet(b, a));
            let Some(m) = status_meet(a, b) else {
                continue;
            };
            assert!(a.entails(m) && b.entails(m), "{a:?} ∧ {b:?} = {m:?}");
            for c in BridgeStatus::ALL {
                if a.entails(c) && b.entails(c) {
                    assert!(m.entails(c), "{a:?} ∧ {b:?} = {m:?} is not greatest against {c:?}");
                }
            }
        }
    }
}

/// Lean: `statusMeet_of_the_incomparable_pairs`.
#[test]
fn the_two_incomparable_pairs_meet_where_the_plan_says() {
    assert_eq!(
        status_meet(
            BridgeStatus::SharedReceiverFace,
            BridgeStatus::ActualMap
        ),
        Some(BridgeStatus::CoPresence)
    );
    assert_eq!(
        status_meet(BridgeStatus::Equivalence, BridgeStatus::NaturalFamily),
        Some(BridgeStatus::StructurePreservingMap)
    );
}

/// The entailment census audits the order from outside: exactly one status entails a speculative
/// analogy, and every status but that one entails co-presence.
#[test]
fn the_entailment_census_audits_the_order() {
    let census = entailment_census();
    assert_eq!(census[&BridgeStatus::CoPresence], 7);
    assert_eq!(census[&BridgeStatus::SpeculativeAnalogy], 1);
    assert_eq!(census[&BridgeStatus::StructurePreservingMap], 3);
}

// -------------------------------------------------------------------------------------------
// The bridge, and composition
// -------------------------------------------------------------------------------------------

/// Lean: the `passage_of_map` field. A status at or above `ActualMap` cannot be declared without a
/// passage: the status is a typed claim, not a word.
#[test]
fn a_map_claim_without_a_passage_is_refused() {
    for status in BridgeStatus::ALL {
        let declared = Bridge::<ExactRebase>::declare(
            "claim",
            status,
            None,
            PreservationClaim::stated("nothing"),
            EpistemicGrade::Conjecture,
        );
        if status.claims_a_map() {
            assert_eq!(
                declared.expect_err("a map claim owes a passage"),
                BridgeRefusal::MapClaimedWithoutPassage { status }
            );
        } else {
            let bridge = declared.expect("a status below ActualMap owes no passage");
            assert!(bridge.respects_its_map_claim());
        }
    }
}

/// Lean: `comp_at_meet` and `composedBridge_status_grade`. Composition takes the meet of the
/// statuses and the composition of the grades.
#[test]
fn composition_takes_the_meet_of_status_and_grade() {
    let equivalence = rebase_bridge(BigInt::from(3));
    let natural_family = Bridge::declare(
        "naturalFamily",
        BridgeStatus::NaturalFamily,
        Some(ExactRebase::new(BigInt::from(5))),
        PreservationClaim::discharged("commutes with restriction at every index"),
        EpistemicGrade::EstablishedBounded,
    )
    .expect("declared with its passage");

    match Bridge::compose(natural_family, equivalence) {
        BridgeComposition::Composed(bridge) => {
            assert_eq!(bridge.status(), BridgeStatus::StructurePreservingMap);
            assert_eq!(bridge.grade(), EpistemicGrade::EstablishedBounded);
            assert!(bridge.respects_its_map_claim());
            let passage = bridge.passage().expect("the composite carries a passage");
            assert_eq!(passage.apply(&BigInt::from(1)), BigInt::from(9));
        }
        other => panic!("expected a composed bridge, got {other:?}"),
    }
}

/// Lean: `composedPassage_of_both` and `Transition.comp_residual`. **The composite's residual is
/// the pair of component residuals, in the order they were dropped**, and the pair reopens the
/// source exactly.
#[test]
fn composition_composes_residuals_through_transition() {
    let outer = Bridge::declare(
        "coarseGrain(3)",
        BridgeStatus::StructurePreservingMap,
        Some(CoarseGrain::new(BigUint::from(3u32)).expect("positive modulus")),
        PreservationClaim::discharged("coarseGrain_comp_apply"),
        EpistemicGrade::ProvedDerived,
    )
    .expect("declared with its passage");
    let inner = Bridge::declare(
        "coarseGrain(2)",
        BridgeStatus::StructurePreservingMap,
        Some(CoarseGrain::new(BigUint::from(2u32)).expect("positive modulus")),
        PreservationClaim::discharged("coarseGrain_comp_apply"),
        EpistemicGrade::ProvedDerived,
    )
    .expect("declared with its passage");

    let BridgeComposition::Composed(bridge) = Bridge::compose(outer, inner) else {
        panic!("two structure-preserving maps compose");
    };
    let passage = bridge.passage().expect("both passages were present");
    let source = BigUint::from(29u32);
    assert_eq!(passage.apply(&source), BigUint::from(4u32), "29 / 2 / 3 = 4");
    assert_eq!(
        passage.residual(&source),
        (BigUint::from(2u32), BigUint::from(1u32)),
        "the composite residual is the pair (29/2 % 3, 29 % 2)"
    );
    passage
        .check_reopen(&source)
        .expect("the pair reopens the source exactly");
}

/// Lean: `Bridge.comp`'s `statusIncomparable` arm. A speculative analogy composes with nothing, and
/// the refusal is returned as content.
#[test]
fn composing_through_a_speculative_analogy_is_refused_as_content() {
    let speculative = Bridge::declare(
        "speculative",
        BridgeStatus::SpeculativeAnalogy,
        None::<ExactRebase>,
        PreservationClaim::stated("nothing"),
        EpistemicGrade::Interpretation,
    )
    .expect("a speculative analogy owes no passage");
    let equivalence = rebase_bridge(BigInt::from(1));

    match Bridge::compose(equivalence, speculative) {
        BridgeComposition::StatusIncomparable { left, right } => {
            assert_eq!(left, BridgeStatus::SpeculativeAnalogy);
            assert_eq!(right, BridgeStatus::Equivalence);
        }
        other => panic!("expected a status refusal, got {other:?}"),
    }
}

/// Lean: `Bridge.comp`'s `gradeIncomparable` arm.
#[test]
fn composing_through_a_counterexample_grade_is_refused_as_content() {
    let refuting = Bridge::declare(
        "refutation",
        BridgeStatus::Equivalence,
        Some(ExactRebase::new(BigInt::from(1))),
        PreservationClaim::discharged("the refuted statement and its witness"),
        EpistemicGrade::Counterexample,
    )
    .expect("declared with its passage");
    let equivalence = rebase_bridge(BigInt::from(2));

    match Bridge::compose(refuting, equivalence) {
        BridgeComposition::GradeIncomparable { left, right } => {
            assert_eq!(left, EpistemicGrade::ProvedDerived);
            assert_eq!(right, EpistemicGrade::Counterexample);
        }
        other => panic!("expected a grade refusal, got {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------
// Proposed bridges and promotion
// -------------------------------------------------------------------------------------------

/// Lean: `proteinEmbeddingProposal_claims_nothing`. The proposal is a candidate: it carries no
/// passage, its status entails only itself and its grade is `Interpretation`.
#[test]
fn the_protein_embedding_proposal_claims_nothing() {
    let proposal = protein_embedding_proposal();
    assert_eq!(
        proposal.candidate.status(),
        BridgeStatus::SpeculativeAnalogy
    );
    assert_eq!(proposal.candidate.grade(), EpistemicGrade::Interpretation);
    assert!(proposal.candidate.passage().is_none());
    assert_eq!(proposal.required_hypotheses.len(), 3);
    assert!(proposal.required_hypotheses.iter().all(|h| !h.discharged));
    assert!(!proposal.falsifier.is_empty(), "a falsifier that can fire");
    assert_eq!(proposal.supporting_receivers.len(), 1);
}

/// Lean: `false_hypothesis_blocks_promotion` and
/// `proteinEmbeddingProposal_blocked_by_a_merging_face`.
#[test]
fn an_undischarged_hypothesis_blocks_promotion() {
    let proposal = protein_embedding_proposal();
    let first = proposal.required_hypotheses[0].statement.clone();
    assert_eq!(
        proposal.promote(BridgeStatus::SpeculativeAnalogy),
        Err(PromotionRefusal::HypothesisUndischarged { statement: first })
    );
}

/// Lean: `counterexample_blocks_promotion`. A recorded counterexample blocks promotion by type,
/// before any hypothesis is even read.
#[test]
fn a_recorded_counterexample_blocks_promotion() {
    let mut proposal = protein_embedding_proposal();
    for hypothesis in &mut proposal.required_hypotheses {
        hypothesis.discharged = true;
    }
    proposal.counterexamples.push(RecordedCounterexample {
        statement: "two contact complexes with different faces share one embedding coordinate"
            .to_string(),
    });
    let statement = proposal.counterexamples[0].statement.clone();
    assert_eq!(
        proposal.promote(BridgeStatus::SpeculativeAnalogy),
        Err(PromotionRefusal::CounterexampleRecorded { statement })
    );
}

/// Lean: `missing_passage_blocks_promotion` and
/// `proteinEmbeddingProposal_not_promotable_to_a_map`.
#[test]
fn promotion_to_a_map_requires_a_passage() {
    let mut proposal = protein_embedding_proposal();
    for hypothesis in &mut proposal.required_hypotheses {
        hypothesis.discharged = true;
    }
    // The target must first entail the candidate's declared status; a speculative analogy entails
    // only itself, so every stronger target is refused before the passage is even consulted.
    assert_eq!(
        proposal.clone().promote(BridgeStatus::ActualMap),
        Err(PromotionRefusal::TargetNotStronger {
            target: BridgeStatus::ActualMap,
            candidate: BridgeStatus::SpeculativeAnalogy
        })
    );

    // A candidate that *is* on the order still cannot be promoted to a map without one.
    let mut owed = proposal;
    owed.candidate = Bridge::declare(
        "co-present only",
        BridgeStatus::CoPresence,
        None::<NoPassage>,
        PreservationClaim::stated("nothing"),
        EpistemicGrade::Conjecture,
    )
    .expect("co-presence owes no passage");
    assert_eq!(
        owed.promote(BridgeStatus::ActualMap),
        Err(PromotionRefusal::PassageMissing {
            target: BridgeStatus::ActualMap
        })
    );
}

/// A proposal whose hypotheses are all discharged and whose candidate carries a passage promotes,
/// and only the status changes.
#[test]
fn a_discharged_proposal_promotes_and_changes_only_the_status() {
    let proposal = ProposedBridge {
        candidate: Bridge::declare(
            "residue restriction",
            BridgeStatus::ActualMap,
            Some(ResidueRestriction::new(BigUint::from(8u32)).expect("positive modulus")),
            PreservationClaim::discharged("reopen(apply(x), residual(x)) = x"),
            EpistemicGrade::ProvedDerived,
        )
        .expect("declared with its passage"),
        required_hypotheses: vec![Hypothesis {
            statement: "the reopening is exact on the declared aperture".to_string(),
            discharged: true,
        }],
        supporting_receivers: Vec::new(),
        counterexamples: Vec::new(),
        falsifier: "a source the retained residual does not reopen".to_string(),
    };
    let promoted = proposal
        .promote(BridgeStatus::StructurePreservingMap)
        .expect("all obligations discharged");
    assert_eq!(promoted.status(), BridgeStatus::StructurePreservingMap);
    assert_eq!(promoted.grade(), EpistemicGrade::ProvedDerived);
    assert!(promoted.passage().is_some());
}

// -------------------------------------------------------------------------------------------
// The bridges that really exist in this tree
// -------------------------------------------------------------------------------------------

/// Lean: `rebaseBridge_residual_subsingleton`. An equivalence drops nothing: its residual type has
/// one value.
#[test]
fn the_rebase_bridge_is_an_equivalence_that_drops_nothing() {
    let bridge = rebase_bridge(BigInt::from(4));
    assert_eq!(bridge.status(), BridgeStatus::Equivalence);
    assert_eq!(bridge.grade(), EpistemicGrade::ProvedDerived);
    assert!(bridge.preserved().discharged);
    let passage = bridge.passage().expect("an equivalence carries its passage");
    assert_eq!(passage.residual(&BigInt::from(11)), NoResidual);
    passage
        .check_reopen(&BigInt::from(11))
        .expect("an invertible passage reopens exactly");
}

/// **The rebase passage is total outside the image of `apply`.** `Transition`'s contract makes
/// `reopen` total — outside the image it returns whatever the implementation supplies, and that is
/// all the contract says — so a target below the offset must be answered, not aborted. It used to
/// be `target - offset` over `BigUint`, which panicked on exactly these inputs and was reachable
/// through the public trait. The passage is now `ExactShift` over `BigInt`, where translation is a
/// genuine equivalence, and the answer off the image is the exact signed difference.
#[test]
fn the_rebase_passage_reopens_below_its_offset_without_panicking() {
    let bridge = rebase_bridge(BigInt::from(4));
    let passage = bridge.passage().expect("an equivalence carries its passage");
    // Below the offset: this is the input that used to panic. The old implementation computed
    // `target - offset` in `BigUint`, and that value does not exist there — which is exactly why
    // it aborted rather than answering.
    assert!(
        BigUint::from(0u32)
            .checked_sub(&BigUint::from(4u32))
            .is_none(),
        "the subtraction the old reopen performed has no BigUint value, so it panicked"
    );
    assert_eq!(passage.reopen(&BigInt::from(0), &NoResidual), BigInt::from(-4));
    assert_eq!(passage.reopen(&BigInt::from(3), &NoResidual), BigInt::from(-1));
    // And it is still an inverse everywhere, which is what `Equivalence` claims: the source that
    // `reopen` names really does `apply` back to the target.
    for target in -6i64..6 {
        let target = BigInt::from(target);
        let reopened = passage.reopen(&target, &NoResidual);
        assert_eq!(passage.apply(&reopened), target);
        passage
            .check_reopen(&reopened)
            .expect("the reopened source reopens exactly");
    }
}

/// The other bridge passages of this module are total on the same inputs: a `BigUint` subtraction,
/// an index or an unwrap outside the image of `apply` would be the same defect elsewhere.
/// `ResidueRestriction` refuses a zero modulus at construction, so its `%` and `/` are total and
/// its `reopen` only ever adds and multiplies; `NoPassage` clones.
#[test]
fn every_bridge_passage_reopens_off_its_image_without_panicking() {
    let residue = ResidueRestriction::new(BigUint::from(9u32)).expect("nine is positive");
    // `9` is not in the image of `x -> x % 9`, and `40` is not a residual this restriction of a
    // bounded source would produce; both are answered rather than refused or aborted.
    assert_eq!(
        residue.reopen(&BigUint::from(9u32), &BigUint::from(40u32)),
        BigUint::from(369u32)
    );
    assert_eq!(residue.residual(&BigUint::zero()), BigUint::zero());
    assert!(ResidueRestriction::new(BigUint::zero()).is_none());

    let none = NoPassage;
    assert_eq!(none.reopen(&Vec::new(), &vec![1u32, 2, 3]), vec![1u32, 2, 3]);
    assert_eq!(none.residual(&Vec::new()), Vec::<u32>::new());
}

/// Lean: `padicHalfBridge_preserves` and `padicHalfBridge_is_not_an_equivalence`. The restriction
/// is lossy at every level above one and its retained digit block reopens the source exactly.
#[test]
fn the_residue_restriction_bridge_is_lossy_and_reopens_exactly() {
    let bridge =
        residue_restriction_bridge(BigUint::from(9u32)).expect("nine is a positive modulus");
    assert_eq!(bridge.status(), BridgeStatus::StructurePreservingMap);
    let passage = bridge.passage().expect("declared with its passage");
    assert_eq!(
        passage.apply(&BigUint::from(4u32)),
        passage.apply(&BigUint::from(13u32)),
        "the face merges two sources, so it is not an equivalence"
    );
    assert_ne!(
        passage.residual(&BigUint::from(4u32)),
        passage.residual(&BigUint::from(13u32)),
        "and the retained digit block is exactly what still separates them"
    );
    for source in 0u32..40 {
        passage
            .check_reopen(&BigUint::from(source))
            .expect("the digit block reopens the source with no remainder");
    }
}

/// Hostile input: a zero modulus carries no level at all and is refused, with no allocation.
#[test]
fn the_residue_restriction_refuses_a_zero_modulus() {
    assert!(ResidueRestriction::new(BigUint::from(0u32)).is_none());
    assert!(residue_restriction_bridge(BigUint::from(0u32)).is_none());
}

/// Lean: `grainBridge_preserves`, discharged by
/// `GrainRestriction.grain_residual_reopens_the_source`. The alpha-carbon selection is a lossy
/// structure-preserving bridge whose round trip through its residual is exact.
#[test]
fn the_grain_restriction_bridge_reopens_the_atom_face_exactly() {
    let selection = GrainSelection::declare(
        "label_atom_id == CA",
        Grain::Residue,
        Grain::Atom,
        [
            GrainAddress::new(0, 0, 0),
            GrainAddress::new(0, 1, 0),
            GrainAddress::new(0, 2, 0),
        ],
    )
    .expect("one representative per residue");

    let cell = |residue: u32, atom: u32| GrainAddress::new(0, residue, atom).cell(Grain::Atom);
    let pair = |r1: u32, a1: u32, r2: u32, a2: u32| {
        GrainPair::new(cell(r1, a1), cell(r2, a2)).expect("distinct atom cells")
    };
    let atom_face = GrainFace::founded(
        Grain::Atom,
        [
            (pair(0, 0, 1, 0), ContactClass::Inside),
            (pair(0, 1, 2, 1), ContactClass::Inside),
            (pair(1, 0, 2, 0), ContactClass::Open),
        ],
    )
    .expect("no reading is Outside");

    let bridge = grain_restriction_bridge(selection);
    assert_eq!(bridge.status(), BridgeStatus::StructurePreservingMap);
    assert_eq!(bridge.grade(), EpistemicGrade::EstablishedBounded);

    let (coarse, residual, reopened) =
        grain_bridge_receipt(&bridge, &atom_face).expect("the bridge carries its passage");
    assert_eq!(coarse.grain(), Grain::Residue);
    assert_eq!(coarse.inside(), 1);
    assert_eq!(coarse.open(), 1);
    assert_eq!(
        residual.retained(),
        1,
        "exactly the fine-only contact the selection never looked at"
    );
    assert_eq!(
        reopened, atom_face,
        "the round trip through the residual is exact"
    );

    bridge
        .passage()
        .expect("declared with its passage")
        .check_reopen(&atom_face)
        .expect("Transition::check_reopen returns the same receipt");
}
