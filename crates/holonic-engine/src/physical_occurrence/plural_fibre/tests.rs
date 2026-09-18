//! The laws of B5 — the plural fibre, the complete separator structure and the exact minimal
//! separating sets — and the measured M5 exhibition.
//!
//! The synthetic tests state what the Lean owner
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/PhysicalOccurrence.lean` proves in its
//! B5 section, and they run everywhere with no fixture and no environment variable. The fixture
//! tests reproduce the authenticated release and **fail** when it is absent: a test that cannot run
//! says so by failing, because cargo discards the output of a passing test.

use std::collections::BTreeSet;

use num_bigint::BigUint;

use super::*;
use crate::physical_constraint_complex::ContactClass;
use crate::physical_occurrence::fixture::{
    absent_structure_root_message, boltz_root, complete_environment, m5_situated_families,
    structure_root, synthetic_family,
};
use crate::physical_occurrence::{HorizontalFamily, StatusRefusal, VerticalFamily};

const F: ContactClass = ContactClass::Inside;
const X: ContactClass = ContactClass::Outside;
const P: ContactClass = ContactClass::Open;

/// The worked synthetic fibre: three members over six addressed contacts.
///
/// | contact | A | B | C | role |
/// |---|---|---|---|---|
/// | 1 | formed | excluded | formed | separating |
/// | 2 | formed | formed | excluded | separating |
/// | 3 | formed | excluded | excluded | separating |
/// | 4 | open | formed | excluded | open-carrying at the family, separating for B against C |
/// | 5 | formed | formed | formed | unanimously formed |
/// | 6 | excluded | excluded | excluded | unanimously excluded |
///
/// The three pairwise separator sets are `{1,3}`, `{2,3}` and `{1,2,4}`: contact 4 is open in A,
/// so it separates nothing A is a party to, but B and C both decided it and it separates them. No
/// single contact separates all three members, and the minimum receiver has two contacts.
fn worked_fibre() -> PluralFibre {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    let a = synthetic_family(1, &first, &[F, F, F, P, F, X]);
    let b = synthetic_family(2, &first, &[X, F, X, F, F, X]);
    let c = synthetic_family(3, &second, &[F, X, X, X, F, X]);
    PluralFibre::over_one_candidate(vec![a, b, c]).expect("three faces over one candidate")
}

fn declared_bound() -> HittingSetBound {
    HittingSetBound::declare(
        4,
        1_000_u32,
        "the worked fibre has three member pairs, so a hitting set never needs more than three \
         contacts; four is the declared ceiling and a thousand nodes bounds the search tree",
    )
    .expect("a stated bound")
}

// ---------------------------------------------------------------------------------------------
// The fibre is the join of the two indices, restricted to one object
// ---------------------------------------------------------------------------------------------

#[test]
fn the_fibre_admits_a_population_neither_existing_family_does() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    // Two seeds at one environment, and a third occurrence at another: several predictors, seeds
    // *and* environments over one candidate, which is exactly the B5 population.
    let members = vec![
        synthetic_family(1, &first, &[F, X]),
        synthetic_family(2, &first, &[X, X]),
        synthetic_family(3, &second, &[F, F]),
    ];

    // The vertical family refuses it: two members sit at the same environment value.
    assert!(matches!(
        VerticalFamily::over_one_object(members.clone()),
        Err(StatusRefusal::EnvironmentRepeatedAlongTheVerticalIndex { .. })
    ));
    // The horizontal family refuses it: the third member sits at a different environment.
    assert!(matches!(
        HorizontalFamily::at_one_environment(members.clone()),
        Err(StatusRefusal::Environment(_))
    ));
    // The fibre admits it.
    let fibre = PluralFibre::over_one_candidate(members).expect("the join of the two indices");
    assert_eq!(fibre.len(), 3);
    assert_eq!(fibre.contacts(), 2);
    assert_eq!(
        fibre.occurrences(),
        vec![OccurrenceId(1), OccurrenceId(2), OccurrenceId(3)]
    );
}

#[test]
fn the_two_existing_families_compose_into_fibres() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    let vertical = VerticalFamily::over_one_object(vec![
        synthetic_family(1, &first, &[F, X]),
        synthetic_family(2, &second, &[F, F]),
    ])
    .expect("two environments over one object");
    assert_eq!(
        PluralFibre::from_vertical(&vertical)
            .expect("the vertical family is a fibre")
            .len(),
        2
    );

    let horizontal = HorizontalFamily::at_one_environment(vec![
        synthetic_family(1, &first, &[F, X]),
        synthetic_family(2, &first, &[X, X]),
    ])
    .expect("two faces at one environment");
    assert_eq!(
        PluralFibre::from_horizontal(&horizontal)
            .expect("this horizontal family happens to be over one object")
            .len(),
        2
    );

    // A horizontal family over *two* candidates is not a fibre, and the refusal names the member.
    let mut other_object = synthetic_family(3, &first, &[F, X]);
    other_object.left_sequence = vec!["GLY".to_owned()];
    let across_objects =
        HorizontalFamily::at_one_environment(vec![synthetic_family(1, &first, &[F, X]), other_object])
            .expect("two objects at one environment");
    assert!(matches!(
        PluralFibre::from_horizontal(&across_objects),
        Err(FibreRefusal::ObjectDiffersInTheFibre {
            occurrence: OccurrenceId(3)
        })
    ));
}

// ---------------------------------------------------------------------------------------------
// The separator sets are complete, and open readings are carried
// ---------------------------------------------------------------------------------------------

#[test]
fn the_separator_set_is_the_complete_set_and_never_a_shortest_witness() {
    let fibre = worked_fibre();
    let ab = fibre.separator_between(0, 1).expect("the first pair");
    assert_eq!(
        ab.separating
            .iter()
            .map(|contact| contact.pair)
            .collect::<Vec<_>>(),
        vec![(1, 1), (1, 3)],
        "both separating contacts are returned, not the first one"
    );
    assert_eq!(
        ab.separating[0],
        SeparatingContact {
            pair: (1, 1),
            left: DecidedClass::Formed,
            right: DecidedClass::Excluded,
        }
    );
    // Contact 4 is open in A, so it is carried and counted on neither side.
    assert_eq!(ab.open_carrying, vec![(1, 4)]);
    assert_eq!(ab.agreeing, 3, "contacts 2, 5 and 6 agree");
    assert_eq!(
        ab.agreeing + ab.separating.len() + ab.open_carrying.len(),
        fibre.contacts(),
        "every addressed contact is counted exactly once"
    );

    let separators = fibre.pairwise_separators().expect("three member pairs");
    assert_eq!(separators.len(), 3);
    assert_eq!(
        separators
            .iter()
            .map(PairwiseSeparator::contacts)
            .collect::<Vec<_>>(),
        vec![
            BTreeSet::from([(1, 1), (1, 3)]),
            BTreeSet::from([(1, 2), (1, 3)]),
            BTreeSet::from([(1, 1), (1, 2), (1, 4)]),
        ],
        "contact 4 is open in A, so it separates neither A-B nor A-C, and it separates B from C, \
         which both decided it. Openness is a property of a reading at a member, not a global veto \
         on a contact"
    );
}

#[test]
fn two_members_are_distinguishable_exactly_when_their_separator_set_is_nonempty() {
    let environment = complete_environment("one", "free", "0").expect("complete");
    let twin_a = synthetic_family(1, &environment, &[F, X, P]);
    let mut twin_b = twin_a.clone();
    twin_b.occurrence = OccurrenceId(2);
    twin_b.lineage = "a second run that read exactly the same thing".to_owned();
    let indistinguishable =
        PluralFibre::over_one_candidate(vec![twin_a.clone(), twin_b]).expect("two faces");
    assert!(
        indistinguishable
            .indistinguishable(0, 1)
            .expect("both members")
    );
    assert!(
        indistinguishable
            .separator_between(0, 1)
            .expect("both members")
            .is_empty()
    );
    assert_eq!(
        indistinguishable.refutes_merge(0, 1).expect("both members"),
        None,
        "nothing refutes the merge at this receiver"
    );

    let distinguishable = PluralFibre::over_one_candidate(vec![
        twin_a,
        synthetic_family(3, &environment, &[X, X, P]),
    ])
    .expect("two faces");
    assert!(!distinguishable.indistinguishable(0, 1).expect("both members"));
    assert_eq!(
        distinguishable.refutes_merge(0, 1).expect("both members"),
        Some(SeparatingContact {
            pair: (1, 1),
            left: DecidedClass::Formed,
            right: DecidedClass::Excluded,
        }),
        "one separating contact refutes the proposed merge, with both decided classes"
    );
}

#[test]
fn the_four_roles_partition_the_contacts_and_open_takes_precedence() {
    let fibre = worked_fibre();
    let partition = fibre.partition();
    assert!(partition.is_a_partition());
    assert_eq!(partition.unanimously_formed, vec![(1, 5)]);
    assert_eq!(partition.unanimously_excluded, vec![(1, 6)]);
    assert_eq!(partition.separating, vec![(1, 1), (1, 2), (1, 3)]);
    assert_eq!(
        partition.open_carrying,
        vec![(1, 4)],
        "contact 4 is open in one member and decided in two; it is never counted as agreeing and \
         never counted as separating"
    );
    assert_eq!(
        partition.unanimous(),
        BTreeSet::from([(1, 5), (1, 6)]),
        "the unanimous set is the decided agreement only"
    );

    match fibre.role_of((1, 4)).expect("an addressed contact") {
        ContactRole::OpenCarrying {
            pair,
            open_at,
            formed_at,
            excluded_at,
        } => {
            assert_eq!(pair, (1, 4));
            assert_eq!(open_at, vec![OccurrenceId(1)]);
            assert_eq!(formed_at, vec![OccurrenceId(2)]);
            assert_eq!(excluded_at, vec![OccurrenceId(3)]);
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(
        fibre.role_of((1, 1)).expect("an addressed contact").label(),
        "separating"
    );
    assert!(matches!(
        fibre.role_of((9, 9)),
        Err(FibreRefusal::ContactNotAddressed { pair: (9, 9) })
    ));
    assert_eq!(role_table(&fibre).len(), 6);
}

// ---------------------------------------------------------------------------------------------
// The central law
// ---------------------------------------------------------------------------------------------

#[test]
fn agreement_narrows_the_fibre_and_does_not_prove_realization() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    // Two faces that read exactly the same thing at this receiver, at two different environments.
    let left = synthetic_family(1, &first, &[F, X, F]);
    let right = synthetic_family(2, &second, &[F, X, F]);
    assert_ne!(left.environment, right.environment, "two distinct sources");
    let fibre = PluralFibre::over_one_candidate(vec![left, right]).expect("two faces");

    let receipt = fibre.unanimity().expect("the receipt");
    assert_eq!(receipt.unanimous_contacts, 3);
    assert_eq!(receipt.separating_contacts, 0);
    assert_eq!(
        receipt.indistinguishable_pairs,
        vec![(OccurrenceId(1), OccurrenceId(2))]
    );
    assert!(
        receipt.stays_plural(),
        "unanimity leaves the preimage fibre plural: the two members are still two"
    );
    // The type-level half: there is no value of `RealizationProof`, so agreement cannot become a
    // claim that the two occurrences are one realized source.
    assert!(receipt.realization_proof().is_none());
    assert_eq!(
        fibre.members()[0].environment.lineage,
        "first",
        "the two sources are retained whole and are never merged into a representative"
    );
    assert_eq!(fibre.members()[1].environment.lineage, "second");

    // A single separating future receiver refutes a proposed merge, and adding the member that
    // carries it removes the pair from the unanimous set.
    let separating = synthetic_family(3, &first, &[X, X, F]);
    let widened = fibre.adjoin(separating).expect("a third face");
    let widened_receipt = widened.unanimity().expect("the receipt");
    assert_eq!(widened_receipt.unanimous_contacts, 2);
    assert_eq!(
        widened_receipt.indistinguishable_pairs,
        vec![(OccurrenceId(1), OccurrenceId(2))],
        "the third member separates from both and the first two remain indistinguishable"
    );
}

#[test]
fn adding_a_member_can_only_shrink_or_preserve_the_unanimous_set() {
    let first = complete_environment("first", "free", "0").expect("complete");
    let second = complete_environment("second", "bound", "1").expect("complete");
    let a = synthetic_family(1, &first, &[F, F, F, P, F, X]);
    let b = synthetic_family(2, &first, &[X, F, X, F, F, X]);
    let c = synthetic_family(3, &second, &[F, X, X, X, F, X]);

    let two = PluralFibre::over_one_candidate(vec![a, b]).expect("two faces");
    let two_unanimous = two.partition().unanimous();
    assert_eq!(
        two_unanimous,
        BTreeSet::from([(1, 2), (1, 5), (1, 6)]),
        "contact 4 is open in one member, so it is carried and not unanimous"
    );

    let three = two.adjoin(c).expect("a third face");
    let three_unanimous = three.partition().unanimous();
    assert_eq!(three_unanimous, BTreeSet::from([(1, 5), (1, 6)]));
    assert!(
        three_unanimous.is_subset(&two_unanimous),
        "monotonicity: adding a member shrinks or preserves the unanimous set"
    );

    // Adjoining a member that agrees everywhere preserves it exactly.
    let mut twin = three.members()[0].clone();
    twin.occurrence = OccurrenceId(4);
    let four = three.adjoin(twin).expect("a fourth face");
    assert_eq!(four.partition().unanimous(), three_unanimous);
}

// ---------------------------------------------------------------------------------------------
// The minimal separating sets
// ---------------------------------------------------------------------------------------------

#[test]
fn the_minimum_separating_receiver_is_exact_and_every_witness_is_returned() {
    let fibre = worked_fibre();
    let bound = declared_bound();
    let minimal = fibre
        .minimal_separating_sets(&bound)
        .expect("the search is within its declared bound");
    match &minimal {
        MinimalSeparation::Minimum { cardinality, sets } => {
            assert_eq!(
                *cardinality, 2,
                "no single contact separates three members: a decided reading takes two values, so \
                 two of any three members agree at every contact"
            );
            assert_eq!(
                sets,
                &vec![
                    vec![(1, 1), (1, 2)],
                    vec![(1, 1), (1, 3)],
                    vec![(1, 2), (1, 3)],
                    vec![(1, 3), (1, 4)],
                ],
                "every minimum receiver is returned, never a representative. The last one names \
                 the contact A leaves open: it separates B from C, and contact 3 separates A from \
                 both, so reading those two contacts tells all three apart"
            );
        }
        other => panic!("{other:?}"),
    }
    assert_eq!(minimal.cardinality(), Some(2));
    assert_eq!(minimal.witnesses(), 4);

    // Every returned receiver really does separate every member pair, and no single contact does.
    for receiver in [
        vec![(1, 1), (1, 2)],
        vec![(1, 1), (1, 3)],
        vec![(1, 2), (1, 3)],
        vec![(1, 3), (1, 4)],
    ] {
        assert!(fibre.separates_every_pair(&receiver).expect("a receiver"));
    }
    for contact in [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] {
        assert!(
            !fibre.separates_every_pair(&[contact]).expect("a receiver"),
            "no single contact separates all three members"
        );
    }
    // The open-carrying contact is a candidate exactly where it is decided: it appears in a
    // minimum receiver, and it never appears in the separator set of a pair that reads it open.
    assert!(
        !fibre
            .separator_between(0, 1)
            .expect("a pair")
            .contacts()
            .contains(&(1, 4))
    );
}

#[test]
fn a_member_pair_no_contact_separates_makes_the_family_unseparable() {
    let environment = complete_environment("one", "free", "0").expect("complete");
    let a = synthetic_family(1, &environment, &[F, X, P]);
    let mut twin = a.clone();
    twin.occurrence = OccurrenceId(2);
    let c = synthetic_family(3, &environment, &[X, X, F]);
    let fibre = PluralFibre::over_one_candidate(vec![a, twin, c]).expect("three faces");
    match fibre
        .minimal_separating_sets(&declared_bound())
        .expect("within the bound")
    {
        MinimalSeparation::Unseparable {
            left,
            right,
            open_carrying,
        } => {
            assert_eq!((left, right), (OccurrenceId(1), OccurrenceId(2)));
            assert_eq!(open_carrying, 1, "the open contact is carried, not counted");
        }
        other => panic!(
            "two members no contact separates must be named, not answered with a receiver: {other:?}"
        ),
    }
}

// ---------------------------------------------------------------------------------------------
// Hostile input: the declared bound and the founding checks
// ---------------------------------------------------------------------------------------------

#[test]
fn the_hitting_set_search_refuses_above_its_declared_bound_rather_than_starting_it() {
    let fibre = worked_fibre();
    // Branching three, depth three. The search restarts once per cardinality, so the rounds visit
    // N(1) = 1+3 = 4, N(2) = 1+3+9 = 13 and N(3) = 1+3+9+27 = 40 nodes: 57 in all. The counting
    // stops at the first round whose running total passes the ceiling, and the receipt says how
    // many rounds it covers.
    let tight = HittingSetBound::declare(3, 10_u32, "a deliberately tight ceiling").expect("stated");
    match fibre.minimal_separating_sets(&tight) {
        Err(FibreRefusal::HittingSetSearchTooWide {
            branching,
            depth,
            worst_case_nodes,
            rounds_counted,
            declared_ceiling,
            ..
        }) => {
            assert_eq!((branching, depth), (3, 3));
            assert_eq!(
                (worst_case_nodes, rounds_counted),
                (BigUint::from(17_u32), 2),
                "4 + 13 over the first two cardinality rounds already passes a ceiling of ten"
            );
            assert_eq!(declared_ceiling, BigUint::from(10_u32));
        }
        other => panic!("an NP-hard search above its ceiling must refuse: {other:?}"),
    }

    // The bound itself refuses a magic number with no ground and a bound that admits nothing.
    assert!(matches!(
        HittingSetBound::declare(3, 10_u32, "   "),
        Err(FibreRefusal::HittingSetGroundNotStated)
    ));
    assert!(matches!(
        HittingSetBound::declare(0, 10_u32, "stated"),
        Err(FibreRefusal::HittingSetBoundIsZero { .. })
    ));
    assert!(matches!(
        HittingSetBound::declare(3, 0_u32, "stated"),
        Err(FibreRefusal::HittingSetBoundIsZero { .. })
    ));

    // A declared cardinality below what the fibre needs returns the shortfall by name rather than
    // an empty answer.
    let shallow = HittingSetBound::declare(1, 1_000_u32, "one contact only").expect("stated");
    assert!(matches!(
        fibre.minimal_separating_sets(&shallow),
        Err(FibreRefusal::NoSeparatingSetWithinCardinality {
            declared: 1,
            searched: 1,
            pairs: 3
        })
    ));
}

#[test]
fn the_guard_counts_every_cardinality_round_and_not_one_search_tree() {
    let fibre = worked_fibre();
    let far = BigUint::from(1_000_000_u32);

    // The exact round counts: branching three, `N(c) = Σ_{i≤c} 3^i` is 4, 13, 40 — and the search
    // runs all three rounds, so its work is 57 nodes and not the 40 of its deepest round alone.
    assert_eq!(search_tree_nodes(3, 1, &far), (BigUint::from(4_u32), 1));
    assert_eq!(search_tree_nodes(3, 2, &far), (BigUint::from(17_u32), 2));
    assert_eq!(search_tree_nodes(3, 3, &far), (BigUint::from(57_u32), 3));
    // At branching one the shortfall of counting one tree is unbounded in the depth: one tree has
    // `depth + 1` nodes where the search visits `depth·(depth+3)/2`. At depth ten, 11 against 65.
    assert_eq!(search_tree_nodes(1, 10, &far), (BigUint::from(65_u32), 10));
    assert_eq!(search_tree_nodes(1, 100, &far), (BigUint::from(5_150_u32), 100));

    // A ceiling of exactly forty is what one depth-three tree costs. The whole search does not fit
    // under it, and the refusal names the sum over every round.
    let one_tree_only = HittingSetBound::declare(
        3,
        40_u32,
        "the node count of the deepest round alone, which is not the work of the search",
    )
    .expect("stated");
    match fibre.minimal_separating_sets(&one_tree_only) {
        Err(FibreRefusal::HittingSetSearchTooWide {
            branching,
            depth,
            worst_case_nodes,
            rounds_counted,
            ..
        }) => {
            assert_eq!(
                (branching, depth, worst_case_nodes, rounds_counted),
                (3, 3, BigUint::from(57_u32), 3),
                "the three cardinality rounds cost 4 + 13 + 40 = 57 nodes together"
            );
        }
        other => panic!("a ceiling of forty admits no search over three rounds: {other:?}"),
    }

    // One ceiling higher — the search's own exact node count — admits it, and the answer is the
    // one the fibre has always had: two contacts, and every one of the four minimum receivers.
    let honest = HittingSetBound::declare(
        3,
        57_u32,
        "the exact node count of every cardinality round of this search, summed",
    )
    .expect("stated");
    let minimal = fibre
        .minimal_separating_sets(&honest)
        .expect("a ceiling equal to the search's own node count admits it");
    assert_eq!(minimal.cardinality(), Some(2));
    assert_eq!(minimal.witnesses(), 4);

    // The rounds are not decoration: no single contact separates all three members, so the answer
    // above was reached only after the cardinality-one round had failed.
    for contact in [(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6)] {
        assert!(!fibre.separates_every_pair(&[contact]).expect("a receiver"));
    }
}

// ---------------------------------------------------------------------------------------------
// The citation table
// ---------------------------------------------------------------------------------------------

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
    let module = include_str!("../plural_fibre.rs");
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

#[test]
fn the_fibre_refuses_a_second_receiver_a_repeated_occurrence_and_a_single_face() {
    let environment = complete_environment("one", "free", "0").expect("complete");
    let a = synthetic_family(1, &environment, &[F, X]);

    assert!(matches!(
        PluralFibre::over_one_candidate(vec![a.clone()]),
        Err(FibreRefusal::NotPlural { members: 1 })
    ));
    assert!(matches!(
        PluralFibre::over_one_candidate(Vec::new()),
        Err(FibreRefusal::NotPlural { members: 0 })
    ));
    assert!(matches!(
        PluralFibre::over_one_candidate(vec![a.clone(), a.clone()]),
        Err(FibreRefusal::OccurrenceRepeatedInTheFibre {
            occurrence: OccurrenceId(1)
        })
    ));

    let mut wider = a.clone();
    wider.occurrence = OccurrenceId(2);
    wider.aperture.lineage = "a twelve angstrom receiver".to_owned();
    assert!(matches!(
        PluralFibre::over_one_candidate(vec![a.clone(), wider]),
        Err(FibreRefusal::ApertureDiffersInTheFibre { .. })
    ));

    let mut shorter = a.clone();
    shorter.occurrence = OccurrenceId(3);
    shorter.readings.truncate(1);
    assert!(matches!(
        PluralFibre::over_one_candidate(vec![a.clone(), shorter]),
        Err(FibreRefusal::PairPopulationDisagrees { .. })
    ));

    let mut reordered = a.clone();
    reordered.occurrence = OccurrenceId(4);
    reordered.readings.reverse();
    assert!(matches!(
        PluralFibre::over_one_candidate(vec![a.clone(), reordered]),
        Err(FibreRefusal::PairOrderDisagrees { .. })
    ));

    let fibre = worked_fibre();
    assert!(matches!(
        fibre.separator_between(0, 9),
        Err(FibreRefusal::MemberIndexAbsent { at: 9 })
    ));
}

// ---------------------------------------------------------------------------------------------
// The measured M5 exhibition
// ---------------------------------------------------------------------------------------------

#[test]
fn the_three_m5_presentations_are_one_plural_fibre_with_its_complete_separator_structure() {
    let root = structure_root();
    assert!(
        root.is_dir(),
        "{}",
        absent_structure_root_message(
            &root,
            "The separator, partition and minimum-receiver laws themselves are checked without \
             any fixture by the_separator_set_is_the_complete_set_and_never_a_shortest_witness, \
             the_four_roles_partition_the_contacts_and_open_takes_precedence and \
             the_minimum_separating_receiver_is_exact_and_every_witness_is_returned."
        )
    );

    let families = m5_situated_families();
    let fibre =
        PluralFibre::over_one_candidate(families.to_vec()).expect("three faces over one candidate");
    assert_eq!(fibre.len(), 3);
    assert_eq!(fibre.contacts(), 10_368, "96 residues against 108");

    let partition = fibre.partition();
    assert!(partition.is_a_partition());
    eprintln!(
        "plural_fibre fixture | M5 three-member fibre | unanimously formed {} | unanimously \
         excluded {} | separating {} | open-carrying {}",
        partition.unanimously_formed.len(),
        partition.unanimously_excluded.len(),
        partition.separating.len(),
        partition.open_carrying.len()
    );
    // [established-bounded; measured] The three presentations agree formed on 38 and excluded on
    // 10,288; 42 contacts are read differently, of which exactly one carries the single open
    // reading the designed presentation leaves at the 8 angstrom aperture. That open contact is
    // carried and is neither an agreement nor a separator, so 41 contacts separate.
    assert_eq!(
        (
            partition.unanimously_formed.len(),
            partition.unanimously_excluded.len(),
            partition.separating.len(),
            partition.open_carrying.len(),
        ),
        (38, 10_288, 41, 1),
        "the M5 three-member fibre partition"
    );

    let separators = fibre.pairwise_separators().expect("three member pairs");
    let measured: Vec<(usize, usize, usize)> = separators
        .iter()
        .map(|separator| {
            (
                separator.agreeing,
                separator.separating.len(),
                separator.open_carrying.len(),
            )
        })
        .collect();
    eprintln!(
        "plural_fibre fixture | M5 pairwise separator sets (agreeing, separating, open-carrying) | \
         designed x free {:?} | designed x bound {:?} | free x bound {:?}",
        measured[0], measured[1], measured[2]
    );
    for (separator, (agreeing, separating, open)) in separators.iter().zip(&measured) {
        assert_eq!(
            agreeing + separating + open,
            10_368,
            "every addressed contact is counted exactly once for {:?} against {:?}",
            separator.left,
            separator.right
        );
    }
    // [established-bounded; measured] The designed structure separates from the free prediction at
    // 29 decided contacts and from the CUL1-bound one at 30, while the two Protenix presentations
    // separate from each other at 24. The single open reading the designed presentation leaves is
    // carried in both pairs it is a party to and is counted in neither.
    assert_eq!(
        measured,
        vec![(10_338, 29, 1), (10_337, 30, 1), (10_344, 24, 0)],
        "the M5 pairwise separator sets"
    );

    // The minimum receiver that tells all three presentations apart.
    let bound = HittingSetBound::declare(
        3,
        100_000_u32,
        "three presentations give three member pairs, so a hitting set never needs more than three \
         contacts; the node ceiling is the declared aperture of an NP-hard search",
    )
    .expect("a stated bound");
    let minimal = fibre
        .minimal_separating_sets(&bound)
        .expect("the search is within its declared bound");
    match &minimal {
        MinimalSeparation::Minimum { cardinality, sets } => {
            eprintln!(
                "plural_fibre fixture | M5 minimum separating receiver | cardinality {cardinality} \
                 | witnesses {} | first {:?}",
                sets.len(),
                sets.first()
            );
            assert_eq!(
                *cardinality, 2,
                "a decided reading takes two values, so two of any three presentations agree at \
                 every single contact and no one-contact receiver separates all three"
            );
            // [established-bounded; measured] 564 distinct two-contact receivers tell the three
            // presentations apart, and the owner returns all of them rather than one.
            assert_eq!(sets.len(), 564, "every minimum receiver, not a representative");
            for set in sets {
                assert!(
                    fibre.separates_every_pair(set).expect("a receiver"),
                    "every returned receiver really separates all three presentations"
                );
            }
        }
        other => panic!("{other:?}"),
    }

    // Unanimity narrows and never realizes: 10,326 contacts on which all three agree leave the
    // three occurrences three.
    let receipt = fibre.unanimity().expect("the receipt");
    assert_eq!(receipt.unanimous_contacts, 10_326);
    assert_eq!(receipt.open_carrying_contacts, 1);
    assert!(receipt.realization_proof().is_none());
    assert!(
        receipt.indistinguishable_pairs.is_empty(),
        "these three presentations are pairwise distinguishable at this receiver"
    );
}

#[test]
fn the_boltz_prediction_is_refused_as_a_member_of_the_rbx1_fibre() {
    let root = boltz_root();
    assert!(
        root.is_dir(),
        "the Boltz-2 smoke prediction root {} is absent, so the hostile-input case cannot be \
         checked and this test refuses to report success without checking it. Set {} to the \
         directory carrying test_model_0.cif and pae_test_model_0.npz. The refusal itself is \
         checked without any fixture by the_two_existing_families_compose_into_fibres.",
        root.display(),
        crate::physical_occurrence::fixture::BOLTZ_ROOT_ENV
    );
    let structures = structure_root();
    assert!(
        structures.is_dir(),
        "{}",
        absent_structure_root_message(
            &structures,
            "The refusal itself is checked without any fixture by \
             the_two_existing_families_compose_into_fibres."
        )
    );

    // [established-bounded; source-inspected] The Boltz-2 smoke prediction is **not** a
    // presentation of RBX1. Its input `.local/boltz-smoke/test.fasta` is a single 330-monomer
    // chain, while the M5 object is a 96-monomer binder against a 108-monomer RBX1. It is
    // therefore usable here only as a hostile input, and the fibre's object check is what refuses
    // it: agreement between faces of two different candidates narrows nothing.
    let presentation = crate::physical_intake::mmcif::StructurePresentation::read(
        &root.join("test_model_0.cif"),
    )
    .expect("the Boltz-2 prediction mounts");
    let residues: Vec<usize> = presentation
        .chains
        .iter()
        .map(|chain| chain.residues.len())
        .collect();
    eprintln!(
        "plural_fibre fixture | boltz-2 test_model_0.cif | chains {} | residues per chain {:?}",
        presentation.chains.len(),
        residues
    );
    assert!(
        !residues.contains(&96) || !residues.contains(&108),
        "the Boltz-2 smoke prediction is not the M5 binder against RBX1; if it ever becomes so \
         this test must be rewritten rather than relaxed"
    );

    let families = m5_situated_families();
    let mut foreign = families[0].clone();
    foreign.occurrence = OccurrenceId(9);
    foreign.lineage = "boltz-2 smoke prediction, a different object entirely".to_owned();
    foreign.left_sequence = presentation.chains[0]
        .residues
        .iter()
        .map(|residue| residue.monomer.clone())
        .collect();
    assert!(matches!(
        PluralFibre::over_one_candidate(vec![families[0].clone(), foreign]),
        Err(FibreRefusal::ObjectDiffersInTheFibre {
            occurrence: OccurrenceId(9)
        })
    ));
}
