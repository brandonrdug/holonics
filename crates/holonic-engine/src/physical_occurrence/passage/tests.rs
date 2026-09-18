//! The laws of B6 — the typed passage, its exact deltas, its composition and its residual — and
//! the measured M5 binding exhibition.
//!
//! The synthetic tests state what the Lean owner
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean` proves in its
//! B6 section, and they run everywhere with no fixture and no environment variable. The fixture
//! test reproduces the authenticated release and **fails** when it is absent.

use num_bigint::BigUint;

use super::*;
use crate::continuing_tower::{ReversePassageReceipt, Transition};
use crate::physical_constraint_complex::ContactClass;
use crate::physical_occurrence::fixture::{
    absent_structure_root_message, complete_environment, complete_environment_with,
    m5_situated_families, structure_root, synthetic_family, synthetic_family_named,
};
use crate::presentation_cost::Axis;

const F: ContactClass = ContactClass::Inside;
const X: ContactClass = ContactClass::Outside;
const P: ContactClass = ContactClass::Open;

/// The typed environment passage between two environments, accounting for every divergent axis.
fn env_passage(from: &Environment, to: &Environment) -> EnvironmentPassage {
    let names = from.disagreement(to).names();
    EnvironmentPassage::declare(
        "the synthetic fixture admits this transport and names every axis it crosses",
        from.clone(),
        to.clone(),
        names,
    )
    .expect("every divergent axis is accounted for")
}

// ---------------------------------------------------------------------------------------------
// The three vertical events, each with its own evidence
// ---------------------------------------------------------------------------------------------

#[test]
fn an_environment_change_needs_a_typed_passage_and_leaves_the_object_alone() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    let source = synthetic_family(1, &first, &[F, X, P]);
    let target = synthetic_family(2, &second, &[F, F, P]);

    let passage =
        Passage::environment_change(&source, &target, env_passage(&first, &second)).expect("a move");
    assert_eq!(passage.steps().len(), 1);
    assert_eq!(passage.from().occurrence, OccurrenceId(1));
    assert_eq!(passage.to().occurrence, OccurrenceId(2));
    assert!(passage.joining().is_empty(), "an elementary passage joins nothing");
    assert_eq!(passage.axis_label(), Vertical::LABEL);
    assert_eq!(passage.events()[0].label(), "environment-change");
    assert!(passage.events()[0].environment_passage().is_some());

    // A passage that does not leave this claim's environment is refused by name.
    let third = complete_environment("third", "other", "2").expect("complete");
    assert!(matches!(
        Passage::environment_change(&source, &target, env_passage(&third, &second)),
        Err(PassageRefusal::Environment(
            EnvironmentRefusal::PassageDoesNotLeaveThisEnvironment { .. }
        ))
    ));
    assert!(matches!(
        Passage::environment_change(&source, &target, env_passage(&first, &third)),
        Err(PassageRefusal::Environment(
            EnvironmentRefusal::PassageDoesNotArriveAtThisEnvironment { .. }
        ))
    ));

    // Changing the object along the vertical axis is refused: that is a horizontal move.
    let mut mutated = target.clone();
    mutated.left_sequence = vec!["GLY".to_owned()];
    assert!(matches!(
        Passage::environment_change(&source, &mutated, env_passage(&first, &second)),
        Err(PassageRefusal::ObjectChangedAlongTheVerticalAxis {
            left: OccurrenceId(1),
            right: OccurrenceId(2)
        })
    ));
}

#[test]
fn a_binding_must_actually_add_its_partner_to_the_oligomeric_state() {
    let free = complete_environment_with("free", "free", "0", &[("SYN", 1)], None).expect("complete");
    let bound = complete_environment_with(
        "bound",
        "bound",
        "1",
        &[("SYN", 1), ("PARTNER", 1)],
        None,
    )
    .expect("complete");
    let source = synthetic_family(1, &free, &[X, X, F]);
    let target = synthetic_family(2, &bound, &[F, X, F]);

    let passage = Passage::binding(&source, &target, env_passage(&free, &bound), "PARTNER")
        .expect("the partner really enters the oligomeric state");
    match passage.events()[0] {
        PassageEvent::Binding {
            partner,
            added_copies,
            ..
        } => {
            assert_eq!(partner, "PARTNER");
            assert_eq!(*added_copies, 1, "the exact copy difference, not a flag");
        }
        other => panic!("{other:?}"),
    }

    // A partner that does not enter is not a binding.
    assert!(matches!(
        Passage::binding(&source, &target, env_passage(&free, &bound), "ABSENT"),
        Err(PassageRefusal::BindingDoesNotAddThePartner {
            before: 0,
            after: 0,
            ..
        })
    ));
    // Nor is the reverse move.
    assert!(matches!(
        Passage::binding(&target, &source, env_passage(&bound, &free), "PARTNER"),
        Err(PassageRefusal::BindingDoesNotAddThePartner {
            before: 1,
            after: 0,
            ..
        })
    ));
}

#[test]
fn a_protonation_must_actually_move_the_acidity_axis_and_cannot_rest_on_an_undeclared_one() {
    let acidic = complete_environment_with(
        "acidic",
        "one",
        "0",
        &[("SYN", 1)],
        Some((5, "the catalytic histidine is protonated")),
    )
    .expect("complete");
    let neutral = complete_environment_with(
        "neutral",
        "one",
        "1",
        &[("SYN", 1)],
        Some((7, "the catalytic histidine is neutral")),
    )
    .expect("complete");
    let silent = complete_environment("silent", "one", "2").expect("complete");

    let source = synthetic_family(1, &acidic, &[F, X, P]);
    let target = synthetic_family(2, &neutral, &[X, X, P]);
    let passage = Passage::protonation(&source, &target, env_passage(&acidic, &neutral))
        .expect("the acidity axis really moves");
    match passage.events()[0] {
        PassageEvent::Protonation {
            from_assumption,
            to_assumption,
            ..
        } => {
            assert_eq!(from_assumption, "the catalytic histidine is protonated");
            assert_eq!(to_assumption, "the catalytic histidine is neutral");
        }
        other => panic!("{other:?}"),
    }

    // The same assumption on both sides is not a protonation.
    let same = synthetic_family(3, &acidic, &[X, X, P]);
    let mut relabelled = acidic.clone();
    relabelled.lineage = "acidic again".to_owned();
    let same_again = synthetic_family(4, &relabelled, &[X, X, P]);
    assert!(matches!(
        Passage::protonation(&same, &same_again, env_passage(&acidic, &relabelled)),
        Err(PassageRefusal::ProtonationDoesNotMoveTheAcidity { .. })
    ));

    // An undeclared acidity axis is not the evidence for an event about it.
    let undeclared = synthetic_family(5, &silent, &[X, X, P]);
    assert!(matches!(
        Passage::protonation(&source, &undeclared, env_passage(&acidic, &silent)),
        Err(PassageRefusal::AxisUndeclaredForThisEvent {
            name: CoordinateName::Acidity,
            ..
        })
    ));
}

#[test]
fn a_mutation_is_horizontal_and_is_typed_apart_from_the_three_vertical_moves() {
    let environment = complete_environment("one", "free", "0").expect("complete");
    let before = synthetic_family_named(
        1,
        &environment,
        &[F, X, P],
        &["ALA".to_owned(), "GLY".to_owned()],
    );
    let after = synthetic_family_named(
        2,
        &environment,
        &[X, X, P],
        &["ALA".to_owned(), "SER".to_owned()],
    );

    let passage = Passage::mutation(&before, &after, 2).expect("exactly one site moves");
    assert_eq!(passage.axis_label(), Horizontal::LABEL);
    assert_ne!(
        Horizontal::LABEL,
        Vertical::LABEL,
        "the two axes are two types and two labels; there is no coercion between them"
    );
    match passage.events()[0] {
        PassageEvent::Mutation {
            site,
            from_monomer,
            to_monomer,
        } => {
            assert_eq!(*site, 2);
            assert_eq!(from_monomer, "GLY");
            assert_eq!(to_monomer, "SER");
        }
        other => panic!("{other:?}"),
    }
    assert!(
        passage.events()[0].environment_passage().is_none(),
        "a mutation is a move at one environment and carries no environment passage"
    );

    // A mutation that also moves the environment is two events.
    let elsewhere = complete_environment("elsewhere", "bound", "1").expect("complete");
    let moved = synthetic_family_named(
        3,
        &elsewhere,
        &[X, X, P],
        &["ALA".to_owned(), "SER".to_owned()],
    );
    assert!(matches!(
        Passage::mutation(&before, &moved, 2),
        Err(PassageRefusal::MutationAlsoMovesTheEnvironment { .. })
    ));
    // A declared site the sequences do not actually differ at.
    assert!(matches!(
        Passage::mutation(&before, &after, 1),
        Err(PassageRefusal::MutationDoesNotChangeExactlyTheSite {
            site: 1,
            ..
        })
    ));
    // A change of the target component.
    let mut target_changed = after.clone();
    target_changed.right_sequence[0] = "ZZZ".to_owned();
    assert!(matches!(
        Passage::mutation(&before, &target_changed, 2),
        Err(PassageRefusal::MutationChangesTheTarget)
    ));
    // An indel rather than a substitution.
    let longer = synthetic_family_named(
        4,
        &environment,
        &[X, X, P],
        &["ALA".to_owned(), "SER".to_owned(), "THR".to_owned()],
    );
    assert!(matches!(
        Passage::mutation(&before, &longer, 2),
        Err(PassageRefusal::MutationChangesTheSequenceLength {
            before: 2,
            after: 3
        })
    ));
}

// ---------------------------------------------------------------------------------------------
// The exact delta in K
// ---------------------------------------------------------------------------------------------

#[test]
fn the_constraint_delta_is_computed_exactly_from_the_two_complexes() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    let source = synthetic_family(1, &first, &[X, F, F, P, F, X, P]);
    let target = synthetic_family(2, &second, &[F, X, P, F, F, X, P]);
    let delta = ConstraintDelta::between(&source, &target).expect("both address the same contacts");

    assert_eq!(delta.contacts(), 7);
    assert!(!delta.is_empty());
    assert_eq!(delta.formed(), vec![(1, 1)], "excluded became formed");
    assert_eq!(delta.broken(), vec![(1, 2)], "formed became excluded");
    assert_eq!(delta.opened(), vec![(1, 3)], "a decided reading opened");
    assert_eq!(
        delta.closed(),
        vec![((1, 4), ContactClass::Inside)],
        "an open reading closed, with the class it closed to"
    );
    assert_eq!(delta.retained(ContactClass::Inside), vec![(1, 5)]);
    assert_eq!(delta.retained(ContactClass::Outside), vec![(1, 6)]);
    assert_eq!(delta.retained(ContactClass::Open), vec![(1, 7)]);
    assert_eq!(
        delta.changed(),
        vec![(1, 1), (1, 2), (1, 3), (1, 4)],
        "exactly the four contacts whose class moved"
    );
    // The complete three-by-three census counts every contact exactly once.
    assert_eq!(delta.census().iter().flatten().sum::<usize>(), 7);
    assert_eq!(census_table(&delta).values().sum::<usize>(), 7);

    // Hostile input: two faces that do not address the same contacts have no delta.
    let mut shorter = target.clone();
    shorter.readings.truncate(3);
    assert!(matches!(
        ConstraintDelta::between(&source, &shorter),
        Err(PassageRefusal::PairPopulationDisagrees { .. })
    ));
    let mut reordered = target.clone();
    reordered.readings.reverse();
    assert!(matches!(
        ConstraintDelta::between(&source, &reordered),
        Err(PassageRefusal::PairOrderDisagrees { .. })
    ));
}

#[test]
fn delta_composition_is_exact_and_associative() {
    let first = complete_environment("first", "a", "0").expect("complete");
    let second = complete_environment("second", "b", "1").expect("complete");
    let third = complete_environment("third", "c", "2").expect("complete");
    let fourth = complete_environment("fourth", "d", "3").expect("complete");
    let a = synthetic_family(1, &first, &[X, F, P, F]);
    let b = synthetic_family(2, &second, &[F, X, F, F]);
    let c = synthetic_family(3, &third, &[F, F, X, X]);
    let d = synthetic_family(4, &fourth, &[P, X, X, F]);

    let ab = ConstraintDelta::between(&a, &b).expect("a delta");
    let bc = ConstraintDelta::between(&b, &c).expect("a delta");
    let cd = ConstraintDelta::between(&c, &d).expect("a delta");
    let ad = ConstraintDelta::between(&a, &d).expect("a delta");

    // Composition is exact: composing the steps gives the delta between the endpoints.
    let composed = ab
        .compose(&bc)
        .expect("they meet")
        .compose(&cd)
        .expect("they meet");
    assert_eq!(composed, ad, "composition of deltas is exact");

    // And associative.
    let left = ab.compose(&bc).expect("meet").compose(&cd).expect("meet");
    let right = ab
        .compose(&bc.compose(&cd).expect("meet"))
        .expect("meet");
    assert_eq!(left, right);

    // A class that moves away and back collapses into a retention rather than being counted twice.
    let there_and_back = ConstraintDelta::between(&a, &b)
        .expect("a delta")
        .compose(&ConstraintDelta::between(&b, &a).expect("a delta"))
        .expect("they meet");
    assert!(there_and_back.changed().is_empty());
    assert_eq!(there_and_back, ConstraintDelta::identity_on(&a));

    // The identity laws.
    assert_eq!(
        ConstraintDelta::identity_on(&a).compose(&ab).expect("meet"),
        ab
    );
    assert_eq!(
        ab.compose(&ConstraintDelta::identity_on(&b)).expect("meet"),
        ab
    );

    // Two deltas that do not meet are refused at the contact where they part.
    assert!(matches!(
        ab.compose(&cd),
        Err(PassageRefusal::DeltaEndpointsDisagree { .. })
    ));
    let mut shorter = a.clone();
    shorter.readings.truncate(2);
    assert!(matches!(
        ab.compose(&ConstraintDelta::identity_on(&shorter)),
        Err(PassageRefusal::DeltaPopulationDisagrees {
            first: 4,
            second: 2
        })
    ));
}

#[test]
fn the_environment_delta_is_the_complete_divergence_and_composes_exactly() {
    let first = complete_environment("first", "a", "0").expect("complete");
    let second = complete_environment("second", "b", "1").expect("complete");
    let third = complete_environment("third", "c", "2").expect("complete");

    let ab = EnvironmentDelta::between(&first, &second);
    assert_eq!(
        ab.names(),
        first.disagreement(&second).names(),
        "the delta's divergence is the owner's own complete disagreement set"
    );
    assert!(ab.names().contains(&CoordinateName::Conformation));
    assert!(ab.retained.contains(&CoordinateName::Species));
    assert_eq!(
        ab.names().len() + ab.retained.len(),
        CoordinateName::ALL.len(),
        "every axis is either divergent or retained"
    );

    let bc = EnvironmentDelta::between(&second, &third);
    let composed = ab.compose(&bc).expect("they meet");
    assert_eq!(
        composed,
        EnvironmentDelta::between(&first, &third),
        "the composite is recomputed from the endpoints, so an axis that moved and moved back is \
         not double counted"
    );
    assert!(matches!(
        bc.compose(&ab),
        Err(PassageRefusal::EnvironmentDeltaEndpointsDisagree { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// Serial composition
// ---------------------------------------------------------------------------------------------

fn three_vertical_steps() -> (
    Passage<Vertical>,
    Passage<Vertical>,
    Passage<Vertical>,
    [crate::physical_occurrence::SituatedFamily; 4],
) {
    let first = complete_environment("first", "a", "0").expect("complete");
    let second = complete_environment("second", "b", "1").expect("complete");
    let third = complete_environment("third", "c", "2").expect("complete");
    let fourth = complete_environment("fourth", "d", "3").expect("complete");
    let a = synthetic_family(1, &first, &[X, F, P, F]);
    let b = synthetic_family(2, &second, &[F, X, F, F]);
    let c = synthetic_family(3, &third, &[F, F, X, X]);
    let d = synthetic_family(4, &fourth, &[P, X, X, F]);
    let p = Passage::environment_change(&a, &b, env_passage(&first, &second)).expect("a move");
    let q = Passage::environment_change(&b, &c, env_passage(&second, &third)).expect("a move");
    let r = Passage::environment_change(&c, &d, env_passage(&third, &fourth)).expect("a move");
    (p, q, r, [a, b, c, d])
}

#[test]
fn serial_composition_retains_the_joining_occurrence_and_is_exactly_associative() {
    let (p, q, r, faces) = three_vertical_steps();

    let pq = p.then(&q).expect("they join");
    assert_eq!(pq.steps().len(), 2);
    assert_eq!(pq.from().occurrence, OccurrenceId(1));
    assert_eq!(pq.to().occurrence, OccurrenceId(3));
    assert_eq!(
        pq.joining()
            .iter()
            .map(|end| end.occurrence)
            .collect::<Vec<_>>(),
        vec![OccurrenceId(2)],
        "the joining occurrence is retained, not quotiented away by the endpoints matching"
    );
    assert_eq!(
        pq.joining()[0].environment.lineage,
        "second",
        "and it carries its own environment and lineage"
    );

    // Associativity is exact equality of values, not agreement at the endpoints.
    let left = pq.then(&r).expect("they join");
    let right = p.then(&q.then(&r).expect("they join")).expect("they join");
    assert_eq!(left, right, "serial composition is associative exactly");
    assert_eq!(left.steps().len(), 3);
    assert_eq!(left.cost(), right.cost());
    assert_eq!(
        left.constraint_delta().expect("the composite delta"),
        ConstraintDelta::between(&faces[0], &faces[3]).expect("a delta"),
        "the composite delta is exactly the delta between the composite's own endpoints"
    );
    assert_eq!(
        left.environment_delta().expect("the composite delta"),
        EnvironmentDelta::between(&faces[0].environment, &faces[3].environment)
    );

    // Equal endpoints do not preserve lineage by themselves: a passage that ends at another
    // occurrence entirely is refused even when the classes would compose.
    let (other_p, _, _, _) = three_vertical_steps();
    let mut relabelled = faces[1].clone();
    relabelled.occurrence = OccurrenceId(99);
    let strange = Passage::environment_change(
        &relabelled,
        &faces[2],
        env_passage(&faces[1].environment, &faces[2].environment),
    )
    .expect("a move");
    assert!(matches!(
        other_p.then(&strange),
        Err(PassageRefusal::JoiningOccurrenceDiffers { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// The residual and the reverse passage
// ---------------------------------------------------------------------------------------------

#[test]
fn a_passage_is_not_invertible_and_the_retained_residual_reopens_its_source_exactly() {
    let (p, q, _, faces) = three_vertical_steps();
    let source = OccurrenceFace::of(&faces[0]);

    // The residual reopens the source exactly, which is `Transition::reopen_apply` at this
    // instance.
    let receipt = p.check_reopen(&source).expect("the residual is exact");
    assert_eq!(receipt.sources_reopened, 1);
    assert_eq!(
        p.reopen(&p.apply(&source), &Transition::residual(&p, &source)),
        source
    );
    assert_eq!(
        p.retained_residual().occurrence,
        OccurrenceId(1),
        "the retained residual is the source face itself, and the passage carries it"
    );

    // The transported face determines nothing about the source: two different sources of the same
    // passage are merged by `apply`, so the reverse exists only with the residual.
    let mut other = source.clone();
    other.classes[0].1 = ContactClass::Open;
    assert_ne!(other, source);
    assert_eq!(p.apply(&other), p.apply(&source));
    match p.reverse_passage(&[source.clone(), other.clone()]) {
        ReversePassageReceipt::OnlyWithTheResidual {
            merged_left,
            merged_right,
        } => {
            assert_eq!(merged_left, source);
            assert_eq!(merged_right, other);
        }
        other => panic!(
            "a passage whose transported face merges two sources has no reverse from the face \
             alone: {other:?}"
        ),
    }
    // And the two residuals are exactly what still tells them apart.
    let (left, right) = p
        .separating_residuals(&source, &other)
        .expect("two merged sources");
    assert_ne!(left, right);
    assert_eq!(left, Transition::residual(&p, &source));

    // A single-face population is not merged, so the receipt says so rather than claiming a
    // reverse that the general statement does not license.
    assert_eq!(
        p.reverse_passage(std::slice::from_ref(&source)),
        ReversePassageReceipt::FromTheFaceAlone { faces_checked: 1 }
    );

    // The composite reopens its source from the first step's residual.
    let pq = p.then(&q).expect("they join");
    assert_eq!(
        pq.check_reopen(&source)
            .expect("the composite residual is exact")
            .sources_reopened,
        1
    );
}

#[test]
fn the_cost_receipt_is_exact_accounted_and_composes_serially() {
    let (p, q, _, _) = three_vertical_steps();
    let cost = p.cost();
    assert!(
        cost.is_accounted(),
        "every coordinate is measured off the delta or derived from measured counts"
    );
    assert_eq!(*cost.count(Axis::DecodeWork), BigUint::from(4_u32));
    assert_eq!(
        *cost.count(Axis::UpdateWork),
        BigUint::from(p.constraint_delta().expect("a delta").changed().len())
    );
    assert_eq!(*cost.count(Axis::CertificateWork), BigUint::from(4_u32));
    // The residual axis is `code_bits(3^4) = code_bits(81) = 7`: the exact code size of the class
    // word at four addressed contacts.
    assert_eq!(*cost.count(Axis::Residual), BigUint::from(7_u32));
    assert_eq!(*cost.count(Axis::Bytes), BigUint::from(1_u32));

    let composite = p.then(&q).expect("they join").cost();
    for axis in Axis::ALL {
        assert_eq!(
            *composite.count(axis),
            p.cost().count(axis) + q.cost().count(axis),
            "serial composition adds coordinatewise at {}",
            axis.name()
        );
    }
    assert!(composite.is_accounted());
}

#[test]
fn an_exact_class_fibre_refuses_above_its_declared_contact_ceiling() {
    // The residual axis is `code_bits(3^contacts)`, and `3^contacts` is a real integer that must be
    // built. The guard is taken before the exponentiation, so a hostile or merely enormous contact
    // population is a typed refusal rather than a truncated exponent or a floating-point estimate.
    assert!(exact_class_fibre_admits(EXACT_CLASS_FIBRE_CEILING).is_ok());
    assert!(matches!(
        exact_class_fibre_admits(EXACT_CLASS_FIBRE_CEILING + 1),
        Err(PassageRefusal::ContactPopulationTooWideForAnExactCodeSize {
            ceiling: EXACT_CLASS_FIBRE_CEILING,
            ..
        })
    ));
    assert!(matches!(
        exact_class_fibre_admits(usize::MAX),
        Err(PassageRefusal::ContactPopulationTooWideForAnExactCodeSize { .. })
    ));
    // And the passages actually built here are far below it.
    let (p, _, _, _) = three_vertical_steps();
    assert!(
        exact_class_fibre_admits(p.constraint_delta().expect("a delta").contacts()).is_ok()
    );
}

#[test]
fn the_class_fibre_exponent_refuses_rather_than_narrowing_to_zero() {
    // `step_cost` takes the exponent of `3^contacts` from this guard. A population that does not
    // convert exactly to the `u32` that `BigUint::pow` takes is a typed refusal; narrowing it to
    // `0` would cost a passage over an enormous population as though it addressed no contact and
    // its class fibre were the one-element fibre.
    assert_eq!(exact_class_fibre_exponent(0), Ok(0));
    assert_eq!(exact_class_fibre_exponent(7), Ok(7));
    assert_eq!(
        exact_class_fibre_exponent(EXACT_CLASS_FIBRE_CEILING),
        Ok(1_000_000)
    );
    for contacts in [
        EXACT_CLASS_FIBRE_CEILING + 1,
        usize::from(u16::MAX) << 20,
        usize::MAX,
    ] {
        assert_eq!(
            exact_class_fibre_exponent(contacts),
            Err(PassageRefusal::ContactPopulationTooWideForAnExactCodeSize {
                contacts,
                ceiling: EXACT_CLASS_FIBRE_CEILING,
            }),
            "a population of {contacts} addressed contacts must be refused by name and never \
             narrowed to the zero exponent"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// The measured M5 exhibition: free RBX1 -> CUL1-bound RBX1 is a binding passage
// ---------------------------------------------------------------------------------------------

#[test]
fn the_m5_free_to_cul1_bound_move_is_a_binding_passage_with_its_exact_contact_delta() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(
            &root,
            "The binding, delta, composition and residual laws themselves are checked without any \
             fixture by a_binding_must_actually_add_its_partner_to_the_oligomeric_state, \
             the_constraint_delta_is_computed_exactly_from_the_two_complexes, \
             serial_composition_retains_the_joining_occurrence_and_is_exactly_associative and \
             a_passage_is_not_invertible_and_the_retained_residual_reopens_its_source_exactly."
        )
    );

    let families = m5_situated_families();
    let free = &families[1];
    let bound = &families[2];
    let passage = Passage::binding(
        free,
        bound,
        env_passage(&free.environment, &bound.environment),
        "CUL1",
    )
    .expect("CUL1 really enters the oligomeric state between the two releases");

    match passage.events()[0] {
        PassageEvent::Binding {
            partner,
            added_copies,
            environment,
        } => {
            assert_eq!(partner, "CUL1");
            assert_eq!(*added_copies, 1);
            assert!(
                environment.accounts_for(CoordinateName::OligomericState),
                "the typed environment passage names the axis the binding moves"
            );
            assert!(environment.accounts_for(CoordinateName::Conformation));
            assert!(environment.accounts_for(CoordinateName::Assay));
        }
        other => panic!("{other:?}"),
    }

    let delta = passage.constraint_delta().expect("the exact contact delta");
    assert_eq!(delta.contacts(), 10_368);
    eprintln!(
        "passage fixture | M5 free -> CUL1-bound binding | census {:?} | formed {} | broken {} | \
         opened {} | closed {}",
        census_table(&delta),
        delta.formed().len(),
        delta.broken().len(),
        delta.opened().len(),
        delta.closed().len()
    );
    assert_eq!(
        delta.census().iter().flatten().sum::<usize>(),
        10_368,
        "every addressed contact is counted exactly once"
    );
    // [established-bounded; measured] Binding CUL1 breaks 19 alpha-carbon contacts of the binder
    // against RBX1 and forms 5, with no reading opening and none closing: both Protenix
    // presentations decide every one of the 10,368 addressed pairs, so the open class is empty on
    // this passage and the whole change is a decided rearrangement of the interface. The complete
    // census is 40 contacts retained formed, 10,304 retained excluded, 19 broken and 5 formed.
    assert_eq!(
        (
            delta.formed().len(),
            delta.broken().len(),
            delta.opened().len(),
            delta.closed().len(),
            delta.changed().len(),
        ),
        (5, 19, 0, 0, 24),
        "the M5 binding passage's exact contact delta"
    );
    assert_eq!(delta.retained(ContactClass::Inside).len(), 40);
    assert_eq!(delta.retained(ContactClass::Outside).len(), 10_304);
    assert!(
        delta.retained(ContactClass::Open).is_empty(),
        "neither Protenix presentation leaves a reading open at the 8 angstrom aperture"
    );

    let environment_delta = passage.environment_delta().expect("the coordinate delta");
    eprintln!(
        "passage fixture | M5 binding environment delta | moved {:?} | retained {:?}",
        environment_delta.names(),
        environment_delta.retained
    );
    assert!(environment_delta.names().contains(&CoordinateName::OligomericState));
    assert!(
        environment_delta.retained.contains(&CoordinateName::Species),
        "both releases are about the same species and homolog"
    );

    // The residual reopens the free presentation exactly, and without it the bound face determines
    // nothing about which presentation it came from.
    let source = OccurrenceFace::of(free);
    assert_eq!(
        passage
            .check_reopen(&source)
            .expect("the residual is exact")
            .sources_reopened,
        1
    );
    let designed_face = OccurrenceFace::of(&families[0]);
    let mut restated = designed_face.clone();
    restated.environment = source.environment.clone();
    restated.occurrence = source.occurrence;
    assert_ne!(restated, source, "two different faces of the same object");
    assert_eq!(
        passage.apply(&restated),
        passage.apply(&source),
        "the transported face is the same, so the reverse needs the residual"
    );

    let cost = passage.cost();
    assert!(cost.is_accounted());
    eprintln!(
        "passage fixture | M5 binding cost | bytes {} | decode {} | update {} | certificate {} | \
         residual bits {}",
        cost.count(Axis::Bytes),
        cost.count(Axis::DecodeWork),
        cost.count(Axis::UpdateWork),
        cost.count(Axis::CertificateWork),
        cost.count(Axis::Residual)
    );
    assert_eq!(*cost.count(Axis::UpdateWork), BigUint::from(24_u32));
    assert_eq!(*cost.count(Axis::DecodeWork), BigUint::from(10_368_u32));
}

// ---------------------------------------------------------------------------------------------
// The totality of `apply`, and the citation table
// ---------------------------------------------------------------------------------------------

#[test]
fn apply_reads_the_composite_delta_on_every_composition_and_never_its_fallback() {
    // `Transition::apply` carries a fallback for a composite whose deltas do not meet, and the
    // fallback is unreachable: `Passage::then` refuses such a join, so every constructible passage
    // — one step, two, three, either bracketing — folds to an `Ok` delta. Tests run with
    // `debug_assert!` live, so a reachable fallback would abort here rather than pass silently.
    let (p, q, r, faces) = three_vertical_steps();
    let source = OccurrenceFace::of(&faces[0]);

    for passage in [
        p.clone(),
        p.then(&q).expect("they join"),
        p.then(&q).expect("they join").then(&r).expect("they join"),
        p.then(&q.then(&r).expect("they join")).expect("they join"),
    ] {
        let delta = passage
            .constraint_delta()
            .expect("every constructible passage's step list composes");
        assert_eq!(
            passage.apply(&source).classes,
            delta.after_classes(),
            "apply reads the composite delta, not the source's own classes"
        );
        assert_eq!(passage.apply(&source).occurrence, passage.to().occurrence);
        assert_eq!(
            passage
                .check_reopen(&source)
                .expect("the residual reopens the source exactly")
                .sources_reopened,
            1
        );
    }

    // And a join whose deltas do not meet is refused at composition, which is what keeps the
    // fallback unreachable. `r` starts at the third face; `p` ends at the second.
    assert!(matches!(
        p.then(&r),
        Err(PassageRefusal::JoiningOccurrenceDiffers { .. })
    ));
}

/// The Lean names this module's header correspondence table cites, parsed from the module's own
/// source exactly as an exterior citation test parses it: rows `//! | ` + backticked Lean names +
/// `| ` + the Rust owner, Lean names in the first column.
fn cited_lean_names(module_source: &str) -> Vec<String> {
    module_source
        .lines()
        .map(str::trim_start)
        .filter(|line| line.starts_with("//! | `"))
        .filter_map(|line| line.strip_prefix("//! |"))
        .filter_map(|row| row.split('|').next())
        .flat_map(|cell| {
            cell.split('`')
                .skip(1)
                .step_by(2)
                .map(|name| name.trim().to_owned())
                .collect::<Vec<String>>()
        })
        .collect()
}

/// Whether the Lean owner declares a cited name. Lean writes a declaration unqualified inside its
/// own `namespace`, so a qualified citation such as `Delta.idOn` is resolved by its final segment;
/// structure fields and inductive constructors are declarations too.
fn lean_declares(owner: &str, cited: &str) -> bool {
    let segment = cited.rsplit('.').next().unwrap_or(cited);
    owner.lines().any(|line| {
        let line = line.trim_start();
        let head = [
            "theorem ",
            "lemma ",
            "def ",
            "noncomputable def ",
            "structure ",
            "inductive ",
            "abbrev ",
            "class ",
            "instance ",
            "| ",
        ]
        .iter()
        .find_map(|keyword| line.strip_prefix(keyword))
        .unwrap_or(line);
        [cited, segment].iter().any(|name| {
            head.strip_prefix(*name).is_some_and(|rest| {
                !rest.starts_with(|character: char| {
                    character.is_alphanumeric() || character == '_' || character == '\''
                })
            })
        })
    })
}

#[test]
fn every_lean_name_the_header_cites_is_declared_by_the_lean_owner() {
    let module = include_str!("../passage.rs");
    let owner = include_str!(
        "../../../../../formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean"
    );
    let names = cited_lean_names(module);
    assert!(
        names.len() >= 20,
        "the header's correspondence table went missing: {} names parsed",
        names.len()
    );
    for name in &names {
        assert!(
            lean_declares(owner, name),
            "Foundation/PhysicalOccurrence.lean declares no `{name}`, so the header cites a name \
             that does not exist"
        );
    }
}
