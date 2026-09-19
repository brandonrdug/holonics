//! Tests for **B9 — evaluation discipline** and for **B10**'s run receipts.
//!
//! Every theorem of `Foundation/EvaluationDiscipline.lean` appears here as a test. Every
//! fixture-dependent test hard-fails with a message naming the absent path rather than reporting
//! success without checking anything, and every such test is paired with a synthetic test that
//! depends on no file.

use std::path::PathBuf;

use num_bigint::BigInt;
use relational_geometry::Rat;

use super::*;
use crate::design_selection::{
    DeclaredEnvironment, DeclaredReceiver, Design, Sense, UnreadReason,
};
use crate::physical_constraint_complex::ContactClass;
use crate::physical_occurrence::fixture;
use crate::physical_occurrence::{Environment, PluralFibre};

// ---------------------------------------------------------------------------------------------
// Synthetic material, depending on no file
// ---------------------------------------------------------------------------------------------

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn environment(conformation: &str) -> Environment {
    fixture::complete_environment_with(
        "evaluation-discipline synthetic",
        conformation,
        "seed0",
        &[("SYN", 1)],
        Some((7, "the synthetic fixture declares a standard protonation assumption")),
    )
    .expect("every axis is stated")
}

fn one_environment() -> Vec<DeclaredEnvironment> {
    vec![DeclaredEnvironment::declare("assayA", environment("apo")).expect("a stated label")]
}

fn one_receiver() -> Vec<DeclaredReceiver> {
    vec![
        DeclaredReceiver::declare(
            "interface",
            Sense::GreaterIsBetter,
            "declared by the synthetic evaluation fixture",
        )
        .expect("a stated name and ground"),
    ]
}

/// One synthetic design whose object is its monomer sequence, so that two designs a substitution
/// apart really are one mutation apart.
fn design(id: u64, sequence: &[&str], reading: i64) -> Design {
    let environment = environment("apo");
    let classes = [ContactClass::Inside, ContactClass::Outside];
    Design::found(
        DesignId(id),
        format!("synthetic design {id}"),
        [(
            "assayA".to_owned(),
            fixture::synthetic_family_named(
                id,
                &environment,
                &classes,
                &sequence
                    .iter()
                    .map(|monomer| (*monomer).to_owned())
                    .collect::<Vec<_>>(),
            ),
        )],
        [(
            ("interface".to_owned(), "assayA".to_owned()),
            ReceiverReading::at(rat(reading)),
        )],
    )
    .expect("a design over one object founds")
}

/// Four designs: `AAA`, `BAA`, `BBA` — a chain of single-site substitutions — and `CCC`, three
/// substitutions away from every one of them.
fn four_designs() -> DesignFamily {
    DesignFamily::declare(
        vec![
            design(1, &["A", "A", "A"], 40),
            design(2, &["B", "A", "A"], 41),
            design(3, &["B", "B", "A"], 42),
            design(4, &["C", "C", "C"], 39),
        ],
        one_environment(),
        one_receiver(),
    )
    .expect("four distinct objects at one environment found a family")
}

fn radius(sites: usize) -> EditRadius {
    EditRadius::declare(sites, "declared by the synthetic evaluation fixture").expect("a ground")
}

fn classes_at(sites: usize) -> LineageClasses {
    LineageClasses::found(&four_designs(), &[], radius(sites)).expect("the quotient founds")
}

fn keys(targets: &[(u64, &str)]) -> DesignKeys {
    DesignKeys::declare(
        targets
            .iter()
            .map(|(id, target)| (DesignId(*id), KeyAxis::Target, (*target).to_owned())),
    )
    .expect("stated keys")
}

// ---------------------------------------------------------------------------------------------
// 1. Lineage classes
// ---------------------------------------------------------------------------------------------

/// **The declared edit radius changes the quotient, and the radius is never a default.**
#[test]
fn the_declared_edit_radius_decides_the_lineage_classes() {
    assert_eq!(
        classes_at(0).classes().len(),
        4,
        "at radius zero every design is its own lineage"
    );
    assert_eq!(
        classes_at(1).classes().len(),
        2,
        "at radius one the chain AAA-BAA-BBA is one class and CCC is another"
    );
    assert_eq!(
        classes_at(3).classes().len(),
        1,
        "at radius three every pair is inside the radius, so there is one class"
    );
    assert!(
        EditRadius::declare(1, "   ").is_err(),
        "an unstated ground is refused"
    );
    assert!(
        matches!(
            EditRadius::declare(EDIT_RADIUS_CEILING + 1, "a ground"),
            Err(EvaluationRefusal::EditRadiusTooLarge { .. })
        ),
        "a radius above the ceiling is refused by name"
    );
}

/// **The chain between two designs of one class is the chain of mutation passages that joins
/// them**, and it is returned rather than asserted.
#[test]
fn the_chain_between_two_designs_of_one_class_is_returned() {
    let classes = classes_at(1);
    assert!(classes.related(DesignId(1), DesignId(3)).expect("both carried"));
    let chain = classes
        .chain_between(DesignId(1), DesignId(3))
        .expect("both carried")
        .expect("one class is connected");
    assert_eq!(chain.len(), 2, "AAA -> BAA -> BBA is two single-site steps");
    assert_eq!(
        chain.iter().map(LineageEdge::steps).sum::<usize>(),
        2,
        "each step is one substitution"
    );
    assert!(
        classes
            .chain_between(DesignId(1), DesignId(4))
            .expect("both carried")
            .is_none(),
        "CCC is in another class, so no chain joins it"
    );
}

/// **An admitted horizontal mutation passage founds an edge**, so the lineage relation is generated
/// by `physical_occurrence::Passage::<Horizontal>::mutation` and not by a second law.
#[test]
fn an_admitted_mutation_passage_founds_a_lineage_edge() {
    let family = four_designs();
    let mutation = family
        .admit_mutation(DesignId(1), DesignId(2), "assayA", 1)
        .expect("AAA and BAA differ at exactly site 1, so the passage owner admits the mutation");
    // At radius zero the edit-distance edges are all refused, so the only edge is the passage.
    let classes =
        LineageClasses::found(&family, std::slice::from_ref(&mutation), radius(0)).expect("founds");
    assert_eq!(classes.edges().len(), 1);
    assert!(matches!(
        classes.edges()[0],
        LineageEdge::Passage { site: 1, .. }
    ));
    assert_eq!(
        classes.classes().len(),
        3,
        "the passage joins designs 1 and 2 and nothing else joins at radius zero"
    );
}

/// A forged `AdmittedTransformation` naming a design the family does not carry is refused before an
/// edge is founded.
#[test]
fn a_mutation_naming_an_absent_design_is_refused() {
    let family = four_designs();
    let forged = AdmittedTransformation::Mutation {
        from: 0,
        to: 99,
        environment: 0,
        site: 1,
    };
    assert!(matches!(
        LineageClasses::found(&family, &[forged], radius(1)),
        Err(EvaluationRefusal::MutationNamesAnAbsentDesign { index: 99, declared: 4 })
    ));
}

// ---------------------------------------------------------------------------------------------
// 2. The split, and the leakage law
// ---------------------------------------------------------------------------------------------

/// **Lean: `ofClassPredicate_does_not_straddle`.** A split built from a partition of lineage
/// classes cannot separate two members of one class.
#[test]
fn a_split_from_a_partition_of_lineage_classes_cannot_straddle() {
    let classes = classes_at(1);
    for evaluation_classes in [vec![0usize], vec![1usize]] {
        let split = Split::from_class_partition(
            &classes,
            Discipline::LeaveOneTargetOut,
            "the held-out class",
            &evaluation_classes,
        )
        .expect("a partition of classes founds a split");
        assert!(
            !split.straddles(&classes).expect("the check runs"),
            "a split built from whole classes never straddles"
        );
        let mut all: Vec<DesignId> = split.development().to_vec();
        all.extend_from_slice(split.evaluation());
        all.sort_unstable();
        assert_eq!(
            all,
            classes.population().to_vec(),
            "the two sides exhaust the population"
        );
    }
}

/// **Lean: `rawSplit_straddles`.** A split declared on raw designs *can* separate two members of one
/// class, and the constructor refuses it naming the pair and the connecting chain.
#[test]
fn a_raw_split_that_separates_one_lineage_is_refused_naming_the_pair_and_the_chain() {
    let classes = classes_at(1);
    let refusal = Split::from_raw_designs(
        &classes,
        Discipline::LeaveOneGeneratorOut,
        "the held-out generator",
        &[DesignId(3)],
    )
    .expect_err("design 3 is lineage-equivalent to designs 1 and 2, which stay on the other side");
    let EvaluationRefusal::SplitStraddlesALineageClass {
        left,
        right,
        steps,
        ref chain,
        ..
    } = refusal
    else {
        panic!("the refusal names the straddle: {refusal}");
    };
    assert_eq!(right, DesignId(3), "the evaluation-side member is named");
    assert!(
        left == DesignId(1) || left == DesignId(2),
        "the development-side member is named: {left:?}"
    );
    assert!(steps >= 1, "the connecting chain is measured, not asserted");
    assert!(
        chain.contains("differing at sites") || chain.contains("passage"),
        "the connecting chain is exhibited: {chain}"
    );
}

/// **The converse witness, as data.** The same leak is returned rather than refused, which is what
/// `Foundation/EvaluationDiscipline.lean::rawSplit_straddles` exhibits.
#[test]
fn the_leak_of_a_raw_split_is_returned_as_data() {
    let classes = classes_at(1);
    let straddle = classes
        .straddle_of(&[DesignId(3)])
        .expect("the check runs")
        .expect("a leak");
    assert_eq!(straddle.evaluation, DesignId(3));
    assert_eq!(
        straddle.class,
        classes.class_of(DesignId(3)).expect("carried")
    );
    assert!(!straddle.chain.is_empty(), "the chain is exhibited");
    assert!(
        classes
            .straddle_of(&[DesignId(4)])
            .expect("the check runs")
            .is_none(),
        "holding out a whole class leaks nothing"
    );
}

/// **Leave-one-out by a typed key is lifted to lineage classes**, and admits exactly when the key
/// respects lineage.
#[test]
fn leave_one_out_by_a_typed_key_respects_lineage_or_refuses() {
    let classes = classes_at(1);
    // The key agrees with the lineage: CCC alone is held out, and it is a whole class.
    let respectful = keys(&[(1, "RBX1"), (2, "RBX1"), (3, "RBX1"), (4, "CUL1")]);
    let split = Split::leave_one_out(
        &classes,
        &respectful,
        Discipline::LeaveOneTargetOut,
        "CUL1",
    )
    .expect("the held-out key is a whole lineage class");
    assert_eq!(split.evaluation(), [DesignId(4)]);
    assert_eq!(
        split.development(),
        [DesignId(1), DesignId(2), DesignId(3)]
    );
    assert!(!split.straddles(&classes).expect("the check runs"));

    // The key cuts a lineage class: BBA is held out and its close variants are not.
    let leaking = keys(&[(1, "RBX1"), (2, "RBX1"), (3, "CUL1"), (4, "CUL1")]);
    assert!(
        matches!(
            Split::leave_one_out(&classes, &leaking, Discipline::LeaveOneTargetOut, "CUL1"),
            Err(EvaluationRefusal::SplitStraddlesALineageClass { .. })
        ),
        "a key that cuts a lineage class is the leak, and it is refused"
    );
}

/// An axis a design does not state is a typed refusal naming the discipline that needed it, never a
/// default.
#[test]
fn an_unstated_key_is_refused_and_never_defaulted() {
    let classes = classes_at(1);
    let partial = keys(&[(1, "RBX1"), (2, "RBX1"), (3, "RBX1")]);
    assert!(matches!(
        Split::leave_one_out(&classes, &partial, Discipline::LeaveOneTargetOut, "RBX1"),
        Err(EvaluationRefusal::KeyNotStated { .. })
    ));
    assert!(matches!(
        DesignKeys::declare([(DesignId(1), KeyAxis::Target, "  ".to_owned())]),
        Err(EvaluationRefusal::NotStated { .. })
    ));
    assert!(matches!(
        DesignKeys::declare([
            (DesignId(1), KeyAxis::Target, "RBX1".to_owned()),
            (DesignId(1), KeyAxis::Target, "CUL1".to_owned()),
        ]),
        Err(EvaluationRefusal::KeyRepeated { .. })
    ));
}

/// Each of the six disciplines names its own typed axis, and the six axes are distinct.
#[test]
fn the_six_disciplines_split_on_six_distinct_typed_axes() {
    let axes: BTreeSet<KeyAxis> = Discipline::ALL.iter().map(|d| d.axis()).collect();
    assert_eq!(axes.len(), 6, "six disciplines, six axes");
    assert_eq!(
        axes,
        KeyAxis::ALL.iter().copied().collect::<BTreeSet<_>>(),
        "and they are exactly the declared axes"
    );
}

/// A split with an empty side answers nothing and is refused.
#[test]
fn a_split_with_an_empty_side_is_refused() {
    let classes = classes_at(1);
    assert!(matches!(
        Split::from_class_partition(&classes, Discipline::LeaveOneTargetOut, "x", &[]),
        Err(EvaluationRefusal::EmptySide { side: "evaluation" })
    ));
    assert!(matches!(
        Split::from_class_partition(&classes, Discipline::LeaveOneTargetOut, "x", &[0, 1]),
        Err(EvaluationRefusal::EmptySide {
            side: "development"
        })
    ));
    assert!(matches!(
        Split::from_class_partition(&classes, Discipline::LeaveOneTargetOut, "x", &[0, 0]),
        Err(EvaluationRefusal::ClassRepeated { index: 0 })
    ));
    assert!(matches!(
        Split::from_class_partition(&classes, Discipline::LeaveOneTargetOut, "x", &[7]),
        Err(EvaluationRefusal::ClassAbsent { index: 7, .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 3. Leakage through receivers
// ---------------------------------------------------------------------------------------------

fn fitted_on_designs(fitted: &[u64]) -> FittedReceiver {
    FittedReceiver::fitted(
        "affinity-calibrator",
        "surface-plasmon-resonance",
        "fitted by the synthetic evaluation fixture",
        fitted.iter().map(|id| DesignId(*id)),
        Vec::new(),
    )
    .expect("a fitted receiver with a stated ground")
}

/// **Lean: `evaluateAt_refuses_a_fitted_occurrence`.**
#[test]
fn a_fitted_receiver_is_refused_at_an_occurrence_it_was_fitted_on() {
    let classes = classes_at(1);
    let receiver = FittedReceiver::fitted(
        "affinity-calibrator",
        "surface-plasmon-resonance",
        "fitted by the synthetic evaluation fixture",
        Vec::new(),
        [OccurrenceId(7)],
    )
    .expect("a fitted receiver");
    assert!(matches!(
        receiver.evaluate_at(&classes, DesignId(4), OccurrenceId(7)),
        Err(EvaluationRefusal::ReceiverFittedOnThisOccurrence { .. })
    ));
}

/// **Lean: `evaluateAt_refuses_a_lineage_equivalent_occurrence`.** This is the leak the member-level
/// split does not catch: no design crosses the split and the receiver still carries the evaluation
/// side inside it.
#[test]
fn a_fitted_receiver_is_refused_at_a_lineage_equivalent_design() {
    let classes = classes_at(1);
    let receiver = fitted_on_designs(&[1]);
    let refusal = receiver
        .evaluate_at(&classes, DesignId(3), OccurrenceId(30))
        .expect_err("design 3 is a close variant of design 1, which the receiver was fitted on");
    let EvaluationRefusal::ReceiverFittedOnALineageEquivalentDesign {
        fitted,
        evaluated,
        steps,
        ..
    } = refusal
    else {
        panic!("the refusal names the lineage leak: {refusal}");
    };
    assert_eq!((fitted, evaluated), (DesignId(1), DesignId(3)));
    assert_eq!(steps, 2, "AAA -> BAA -> BBA is two substitutions");
}

/// **Lean: `evaluateAt_admits_when_nothing_leaks`.** And the admission cannot be forged: its fields
/// are private and `evaluate_at` is its only constructor.
#[test]
fn a_fitted_receiver_is_admitted_where_nothing_leaks() {
    let classes = classes_at(1);
    let receiver = fitted_on_designs(&[1]);
    let admission = receiver
        .evaluate_at(&classes, DesignId(4), OccurrenceId(40))
        .expect("design 4 is in another lineage class");
    assert_eq!(admission.receiver(), "affinity-calibrator");
    assert_eq!(admission.design(), DesignId(4));
    assert_eq!(admission.occurrence(), OccurrenceId(40));
}

/// A receiver fitted on nothing is not fitted, and an unstated ground is refused.
#[test]
fn a_receiver_fitted_on_nothing_is_refused() {
    assert!(matches!(
        FittedReceiver::fitted("r", "a", "g", Vec::new(), Vec::new()),
        Err(EvaluationRefusal::EmptyPopulation)
    ));
    assert!(matches!(
        FittedReceiver::fitted("r", "a", "  ", [DesignId(1)], Vec::new()),
        Err(EvaluationRefusal::NotStated { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 4. Assay-specific calibration
// ---------------------------------------------------------------------------------------------

fn calibration() -> Calibration {
    Calibration::fitted_within(
        "spr-to-kd",
        "surface-plasmon-resonance",
        "response-units",
        "dissociation-constant",
        "fitted on the synthetic fixture's own assay standards",
    )
    .expect("a stated calibration")
}

/// **Lean: `within_one_assay_needs_no_bridge`, `across_assays_without_a_bridge_is_refused`,
/// `across_assays_with_a_bridge_is_admitted`, `a_bridge_between_other_assays_is_refused`.**
#[test]
fn a_calibration_does_not_cross_an_assay_without_a_bridge() {
    let calibration = calibration();
    let inside = calibration
        .carry_to("surface-plasmon-resonance", None)
        .expect("its own assay needs no bridge");
    assert_eq!(inside.bridge(), None);

    assert!(matches!(
        calibration.carry_to("isothermal-titration-calorimetry", None),
        Err(EvaluationRefusal::CalibrationCrossesAssaysWithoutABridge { .. })
    ));

    let bridge = AssayBridge::declare(
        "spr-to-itc",
        "surface-plasmon-resonance",
        "isothermal-titration-calorimetry",
        "declared by the synthetic fixture with a stated ground",
    )
    .expect("a stated bridge");
    let carried = calibration
        .carry_to("isothermal-titration-calorimetry", Some(&bridge))
        .expect("a bridge that joins the two assays licenses the crossing");
    assert_eq!(carried.bridge(), Some("spr-to-itc"));

    let elsewhere = AssayBridge::declare(
        "cell-to-itc",
        "cell-assay",
        "isothermal-titration-calorimetry",
        "a bridge between two other assays",
    )
    .expect("a stated bridge");
    assert!(matches!(
        calibration.carry_to("isothermal-titration-calorimetry", Some(&elsewhere)),
        Err(EvaluationRefusal::BridgeJoinsOtherAssays { .. })
    ));
}

/// A bridge from an assay to itself states nothing and is refused.
#[test]
fn a_circular_assay_bridge_is_refused() {
    assert!(matches!(
        AssayBridge::declare("x", "spr", "spr", "a ground"),
        Err(EvaluationRefusal::BridgeIsCircular { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 5. A wet or external return is a new receiver occurrence
// ---------------------------------------------------------------------------------------------

fn apparatus() -> ExteriorDeclaration {
    ExteriorDeclaration::declare(
        "a measured dissociation constant from a wet binding assay",
        "the synthetic fixture's declared instrument",
    )
    .expect("a stated declaration")
}

/// **Lean: `the_return_does_not_relabel_the_prediction` and
/// `the_comparison_is_not_at_the_predictions_time`.**
#[test]
fn a_wet_return_does_not_relabel_the_earlier_prediction() {
    let prediction = TimedReading::declared("affinity", 3, &ReceiverReading::at(rat(100)))
        .expect("a decided prediction");
    let before = prediction.clone();
    let external = TimedReading::declared("affinity", 11, &ReceiverReading::at(rat(1200)))
        .expect("a decided return");
    let comparison = ExternalComparison::state(apparatus(), prediction, external, None)
        .expect("the return is later than the prediction");

    assert_eq!(
        comparison.prediction(),
        &before,
        "the earlier prediction's face is an occurrence at its own time and is unchanged"
    );
    assert_eq!(comparison.prediction().occurs_at(), 3);
    assert_eq!(comparison.external_return().occurs_at(), 11);
    assert_eq!(comparison.stated_at(), 11);
    assert!(
        comparison.stated_at() > comparison.prediction().occurs_at(),
        "the comparison carries its own time index, strictly later than the prediction's"
    );
    assert_eq!(
        comparison.rung(),
        Rung::NoRelation,
        "100 against 1200 with no declared tolerance stands on no rung"
    );
    assert_eq!(
        comparison.apparatus().apparatus(),
        "the synthetic fixture's declared instrument"
    );
}

/// The rung is computed from the two exact readings and the declared tolerance, never declared.
#[test]
fn the_comparison_rung_is_computed_from_the_exact_readings() {
    let equal = ExternalComparison::state(
        apparatus(),
        TimedReading::declared("affinity", 1, &ReceiverReading::at(rat(100))).expect("a reading"),
        TimedReading::declared("affinity", 2, &ReceiverReading::at(rat(100))).expect("a reading"),
        None,
    )
    .expect("a later return");
    assert_eq!(equal.rung(), Rung::ReceiverEqual);

    let tolerance = ExactInterval::new(rat(0), rat(2)).expect("an ordered interval");
    let inside = ExternalComparison::state(
        apparatus(),
        TimedReading::declared("affinity", 1, &ReceiverReading::at(rat(100))).expect("a reading"),
        TimedReading::declared("affinity", 2, &ReceiverReading::at(rat(101))).expect("a reading"),
        Some(&tolerance),
    )
    .expect("a later return");
    assert_eq!(inside.rung(), Rung::WithinTolerance);

    let outside = ExternalComparison::state(
        apparatus(),
        TimedReading::declared("affinity", 1, &ReceiverReading::at(rat(100))).expect("a reading"),
        TimedReading::declared("affinity", 2, &ReceiverReading::at(rat(1200))).expect("a reading"),
        Some(&tolerance),
    )
    .expect("a later return");
    assert_eq!(outside.rung(), Rung::NoRelation);
}

/// A return that does not come later is not a later occurrence, and an unread return is not a
/// return.
#[test]
fn a_return_that_is_not_later_and_an_unread_return_are_refused() {
    let prediction =
        TimedReading::declared("affinity", 5, &ReceiverReading::at(rat(100))).expect("a reading");
    let same = TimedReading::declared("affinity", 5, &ReceiverReading::at(rat(100)))
        .expect("a reading");
    assert!(matches!(
        ExternalComparison::state(apparatus(), prediction, same, None),
        Err(EvaluationRefusal::ReturnIsNotLater {
            prediction: 5,
            external: 5
        })
    ));
    let unread = ReceiverReading::Unread(
        UnreadReason::declare("the wet assay did not run").expect("a stated reason"),
    );
    assert!(matches!(
        TimedReading::declared("affinity", 9, &unread),
        Err(EvaluationRefusal::ExternalReturnIsUnread { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 6. Predictor disagreement as a fibre property
// ---------------------------------------------------------------------------------------------

/// Three members over four addressed contacts: one unanimous, two separating, one open-carrying.
fn synthetic_fibre() -> PluralFibre {
    let environment = environment("apo");
    let member = |occurrence: u64, classes: &[ContactClass]| {
        fixture::synthetic_family(occurrence, &environment, classes)
    };
    PluralFibre::over_one_candidate(vec![
        member(
            101,
            &[
                ContactClass::Inside,
                ContactClass::Outside,
                ContactClass::Inside,
                ContactClass::Open,
            ],
        ),
        member(
            102,
            &[
                ContactClass::Inside,
                ContactClass::Inside,
                ContactClass::Inside,
                ContactClass::Outside,
            ],
        ),
        member(
            103,
            &[
                ContactClass::Inside,
                ContactClass::Outside,
                ContactClass::Outside,
                ContactClass::Outside,
            ],
        ),
    ])
    .expect("one object, one aperture, three occurrences")
}

/// **The subsets are the fibre's own partition**, and the open class is carried on neither side.
#[test]
fn the_disagreement_subsets_are_the_fibres_own_partition() {
    let fibre = synthetic_fibre();
    let subsets = disagreement_subsets(&fibre);
    assert!(subsets.is_a_partition(), "the three subsets exhaust and are disjoint");
    assert_eq!(subsets.unanimous, [(1, 1)]);
    assert_eq!(subsets.separating, [(1, 2), (1, 3)]);
    assert_eq!(subsets.open_carrying, [(1, 4)]);
    assert_eq!(
        subsets.class_of((1, 4)),
        Some(DisagreementClass::OpenCarrying)
    );
    assert_eq!(subsets.class_of((9, 9)), None);
}

/// **Lean: `correct_on_the_unanimous_contact_and_wrong_on_the_separating_one`.** Performance on the
/// unanimous subset says nothing about the separating subset: a predictor that answers `Formed`
/// everywhere is perfect on the one and scores zero on the other.
#[test]
fn performance_on_the_unanimous_subset_says_nothing_about_the_separating_subset() {
    let fibre = synthetic_fibre();
    let subsets = disagreement_subsets(&fibre);
    let always_formed = |_pair: (u32, u32)| DecidedClass::Formed;

    let unanimous = performance_on(
        &fibre,
        &subsets,
        DisagreementClass::Unanimous,
        &always_formed,
    )
    .expect("every contact is addressed");
    assert_eq!((unanimous.agreeing, unanimous.disagreeing), (1, 0));

    let separating = performance_on(
        &fibre,
        &subsets,
        DisagreementClass::Separating,
        &always_formed,
    )
    .expect("every contact is addressed");
    assert_eq!(
        (separating.agreeing, separating.disagreeing),
        (0, 2),
        "a separating contact takes two decided values, so no single answer agrees with every \
         member there — which is why a score on the unanimous subset carries no information here"
    );

    let open = performance_on(
        &fibre,
        &subsets,
        DisagreementClass::OpenCarrying,
        &always_formed,
    )
    .expect("every contact is addressed");
    assert_eq!(
        open.carried_open, 1,
        "the one open member reading is carried and counted on neither side"
    );
}

// ---------------------------------------------------------------------------------------------
// 7. What an evaluation may conclude
// ---------------------------------------------------------------------------------------------

fn a_split() -> (LineageClasses, Split) {
    let classes = classes_at(1);
    let split = Split::from_class_partition(
        &classes,
        Discipline::LeaveOneTargetOut,
        "CUL1",
        &[classes.class_of(DesignId(4)).expect("carried")],
    )
    .expect("a partition of classes");
    (classes, split)
}

fn an_admission(classes: &LineageClasses) -> ReceiverAdmission {
    fitted_on_designs(&[1])
        .evaluate_at(classes, DesignId(4), OccurrenceId(40))
        .expect("nothing leaks")
}

/// **A held-out result is established-bounded at its split and its receiver, and nowhere else.**
#[test]
fn a_held_out_result_is_bounded_at_its_split_and_receiver() {
    let (classes, split) = a_split();
    let admission = an_admission(&classes);
    let conclusion = read_held_out(&split, &admission, 7, 0, None);
    assert_eq!(conclusion.label(), "established-bounded");
    assert_eq!(conclusion.scope().1, "affinity-calibrator");
    assert!(
        conclusion.at_another_split(&split.name()).is_some(),
        "it stands at its own split"
    );
    assert!(
        conclusion
            .at_another_split("leave-one-interface-family-out holding out \"loop-3\"")
            .is_none(),
        "and it does not travel to another split"
    );
}

/// **Lean: `no_conclusion_carries_a_universal_claim`.** Rule 2: a bounded evaluation refutes and
/// never affirms.
#[test]
fn a_bounded_evaluation_refutes_and_never_affirms() {
    let (classes, split) = a_split();
    let admission = an_admission(&classes);
    let claim = "this design family binds every homolog of the target";

    let refuted = read_held_out(&split, &admission, 6, 1, Some(claim));
    assert_eq!(refuted.label(), "generalization-refuted");

    let not_refuted = read_held_out(&split, &admission, 7, 0, Some(claim));
    assert_eq!(
        not_refuted.label(),
        "not-refuted-within-this-evaluation",
        "a bounded evaluation that finds no counterexample returns its own return and never an \
         affirmation"
    );

    for conclusion in [refuted, not_refuted] {
        assert!(
            conclusion.universal_claim().is_none(),
            "UniversalClaim is uninhabited, so no conclusion can carry one"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// 8. Run receipts and named clocks
// ---------------------------------------------------------------------------------------------

/// **A run receipt names its tool, version, mode and numerical scope, and its clocks are exact
/// integer nanosecond readings from a declared source.**
#[test]
fn a_run_receipt_records_named_clocks_in_exact_nanoseconds() {
    let mut recorder = RunRecorder::start(
        "holonic-engine::evaluation_discipline (synthetic)",
        "CPU only, exact rational arithmetic",
        "exact BigInt/BigRational throughout; no float decides anything",
    )
    .expect("a stated recorder");
    let watch = Stopwatch::start();
    for name in ClockName::ALL {
        recorder.record(name, &watch).expect("a fresh clock");
    }
    assert!(matches!(
        recorder.record(ClockName::Setup, &watch),
        Err(EvaluationRefusal::ClockRepeated { clock: "setup" })
    ));
    let receipt = recorder
        .finish(&|| ToolVersion::Unavailable {
            why: "the synthetic recorder asks no tool for a version".to_owned(),
        })
        .expect("the end-to-end clock was recorded");
    assert_eq!(receipt.clocks().len(), 4);
    for reading in receipt.clocks() {
        assert_eq!(reading.source(), Stopwatch::SOURCE);
    }
    assert!(receipt.clock(ClockName::EndToEnd).is_some());
    assert!(receipt.version().version().is_none());
    assert!(receipt.render().contains("end_to_end="));
}

/// A receipt that never measured the whole run is refused, and so is an unstated declaration.
#[test]
fn a_receipt_without_an_end_to_end_clock_is_refused() {
    let mut recorder = RunRecorder::start("tool", "mode", "scope").expect("stated");
    let watch = Stopwatch::start();
    recorder.record(ClockName::Setup, &watch).expect("a clock");
    assert!(matches!(
        recorder.finish(&|| ToolVersion::Unavailable {
            why: "none".to_owned()
        }),
        Err(EvaluationRefusal::EndToEndClockAbsent { recorded: 1 })
    ));
    assert!(matches!(
        RunRecorder::start("  ", "mode", "scope"),
        Err(EvaluationRefusal::NotStated { .. })
    ));
}

/// **A version that cannot be read is typed and never guessed.** Hostile input: an absent
/// interpreter, an absent repository, and a package name that is not a distribution name.
#[test]
fn an_unreadable_version_is_typed_and_never_guessed() {
    let absent = PathBuf::from("/nonexistent/interpreter/python");
    assert!(matches!(
        python_package_version(&absent, "boltz"),
        ToolVersion::Unavailable { .. }
    ));
    assert!(matches!(
        python_package_version(&absent, "not a package; rm -rf /"),
        ToolVersion::Unavailable { .. }
    ));
    assert!(matches!(
        git_head(&PathBuf::from("/nonexistent/repository")),
        ToolVersion::Unavailable { .. }
    ));
}

/// **The tools this machine actually carries.** Boltz-2 lives in the virtual environment an earlier
/// session installed under `.local/venv-protein`, and ProteinMPNN is a checkout under
/// `.local/tools/ProteinMPNN`. Where a version can be read it is recorded; where it cannot, the
/// return is `Unavailable` with a reason, and this test asserts the *shape* of the answer either
/// way so that it is never vacuous and never invents a version string.
#[test]
fn the_installed_prediction_tools_report_a_version_or_a_stated_reason() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let interpreter = root.join(".local/venv-protein/bin/python");
    let boltz = python_package_version(&interpreter, "boltz");
    let torch = python_package_version(&interpreter, "torch");
    let mpnn = git_head(&root.join(".local/tools/ProteinMPNN"));
    for (name, version) in [("boltz", &boltz), ("torch", &torch), ("ProteinMPNN", &mpnn)] {
        match version {
            ToolVersion::Read { version, recorded } => {
                assert!(!version.trim().is_empty(), "{name} reported an empty version");
                assert!(
                    !recorded.how().trim().is_empty(),
                    "{name}'s reader records how it asked"
                );
            }
            ToolVersion::Unavailable { why } => {
                assert!(!why.trim().is_empty(), "{name} is unavailable with no reason");
            }
        }
    }
    // Printed so a reader of the test output sees what was actually installed.
    println!("boltz: {}", boltz.render());
    println!("torch: {}", torch.render());
    println!("ProteinMPNN: {}", mpnn.render());
}

#[path = "tests/m5_cascade.rs"]
mod m5_cascade;
