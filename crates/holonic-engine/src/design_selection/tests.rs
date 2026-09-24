//! Tests for **B8 — selection and design equivalence**.
//!
//! Every theorem of `Foundation/DesignSelection.lean` appears here as a test, and every
//! fixture-dependent test hard-fails with a message naming the absent path rather than reporting
//! success without checking anything.

use num_bigint::BigInt;
use holonics::geometry::Rat;

use super::*;
use crate::physical_constraint_complex::ContactClass;
use crate::physical_occurrence::fixture;
use crate::physical_occurrence::{PluralFibre, plural_fibre};
use crate::relation_ladder::{
    AutomorphismClaim, ContinuationVerdict, SituationAutomorphism, ToleranceReading,
};

// ---------------------------------------------------------------------------------------------
// Synthetic material, depending on no file
// ---------------------------------------------------------------------------------------------

fn rat(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn read(value: i64) -> ReceiverReading {
    ReceiverReading::at(rat(value))
}

/// A plural reading: an exact interval that this receiver did not resolve.
fn plural(lower: i64, upper: i64) -> ReceiverReading {
    ReceiverReading::Read(fixture::interval(lower, upper))
}

/// Every axis declared — including the acidity, so that two of these environments diverge in the
/// declared conformation **and nothing else**. An undeclared axis does not agree with itself, so
/// leaving one undeclared would make every passage between two of them account for it.
fn environment(conformation: &str) -> Environment {
    fixture::complete_environment_with(
        "design-selection synthetic",
        conformation,
        "seed0",
        &[("SYN", 1)],
        Some((7, "the synthetic fixture declares a standard protonation assumption")),
    )
    .expect("every axis is stated")
}

/// Two declared environments, `assayA` and `assayB`.
fn two_environments() -> Vec<DeclaredEnvironment> {
    vec![
        DeclaredEnvironment::declare("assayA", environment("apo")).expect("a stated label"),
        DeclaredEnvironment::declare("assayB", environment("holo")).expect("a stated label"),
    ]
}

fn receiver(name: &str, sense: Sense) -> DeclaredReceiver {
    DeclaredReceiver::declare(name, sense, "declared by the synthetic selection fixture")
        .expect("a stated name and ground")
}

/// One synthetic design: its monomer label distinguishes the object, its contact classes per
/// declared environment give it a face, and its readings are stated at every axis.
fn synthetic_design(
    id: u64,
    monomer: &str,
    faces: &[(&str, &Environment, &[ContactClass])],
    readings: &[(&str, &str, ReceiverReading)],
) -> Design {
    Design::found(
        DesignId(id),
        format!("synthetic design {monomer}"),
        faces.iter().map(|(label, env, classes)| {
            (
                (*label).to_owned(),
                fixture::synthetic_family_named(
                    id * 10 + u64::from(label.as_bytes()[label.len() - 1]),
                    env,
                    classes,
                    &[monomer.to_owned()],
                ),
            )
        }),
        readings.iter().map(|(receiver, label, reading)| {
            (((*receiver).to_owned(), (*label).to_owned()), reading.clone())
        }),
    )
    .expect("a design over one object founds")
}

/// The worked synthetic family: three designs, two environments, two receivers.
///
/// Readings at `affinity` (smaller is better) and `interface` (greater is better):
///
/// | design | affinity@A | affinity@B | interface@A | interface@B |
/// |---|---|---|---|---|
/// | 1 | 100 | 100 | 40 | 40 |
/// | 2 | 101 | 1200 | 40 | 40 |
/// | 3 | 50  | 50   | 41 | 41 |
fn worked_family() -> DesignFamily {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let formed = [ContactClass::Inside, ContactClass::Outside, ContactClass::Outside];
    let other = [ContactClass::Outside, ContactClass::Inside, ContactClass::Outside];
    let third = [ContactClass::Outside, ContactClass::Outside, ContactClass::Inside];
    let designs = vec![
        synthetic_design(
            1,
            "ALA",
            &[("assayA", &a, &formed), ("assayB", &b, &formed)],
            &[
                ("affinity", "assayA", read(100)),
                ("affinity", "assayB", read(100)),
                ("interface", "assayA", read(40)),
                ("interface", "assayB", read(40)),
            ],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("assayA", &a, &other), ("assayB", &b, &other)],
            &[
                ("affinity", "assayA", read(101)),
                ("affinity", "assayB", read(1200)),
                ("interface", "assayA", read(40)),
                ("interface", "assayB", read(40)),
            ],
        ),
        synthetic_design(
            3,
            "SER",
            &[("assayA", &a, &third), ("assayB", &b, &third)],
            &[
                ("affinity", "assayA", read(50)),
                ("affinity", "assayB", read(50)),
                ("interface", "assayA", read(41)),
                ("interface", "assayB", read(41)),
            ],
        ),
    ];
    DesignFamily::declare(
        designs,
        environments,
        vec![
            receiver("affinity", Sense::SmallerIsBetter),
            receiver("interface", Sense::GreaterIsBetter),
        ],
    )
    .expect("the worked family declares")
}

/// Two designs agreeing at **every** declared receiver at `assayA` and separated at `assayB`.
fn agreeing_at_a_family() -> DesignFamily {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let one = [ContactClass::Inside];
    let two = [ContactClass::Outside];
    DesignFamily::declare(
        vec![
            synthetic_design(
                1,
                "ALA",
                &[("assayA", &a, &one), ("assayB", &b, &one)],
                &[
                    ("affinity", "assayA", read(100)),
                    ("affinity", "assayB", read(100)),
                ],
            ),
            synthetic_design(
                2,
                "GLY",
                &[("assayA", &a, &two), ("assayB", &b, &two)],
                &[
                    ("affinity", "assayA", read(100)),
                    ("affinity", "assayB", read(1200)),
                ],
            ),
        ],
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the agreeing family declares")
}

// ---------------------------------------------------------------------------------------------
// The family is the rectangle neither existing owner admits
// ---------------------------------------------------------------------------------------------

#[test]
fn a_design_family_is_the_rectangle_neither_existing_family_admits() {
    let family = worked_family();
    // A row is a vertical family: one object, two environments.
    for design in family.designs() {
        design
            .vertical_family()
            .expect("one object across the declared environments is a vertical family");
    }
    // A column is a horizontal family: one environment, three objects.
    let column: Vec<SituatedFamily> = family
        .designs()
        .iter()
        .map(|design| design.face("assayA").expect("a face").clone())
        .collect();
    HorizontalFamily::at_one_environment(column.clone())
        .expect("three objects at one environment is a horizontal family");

    // The rectangle is neither. A vertical family refuses the column (three objects):
    let vertical = VerticalFamily::over_one_object(column.clone());
    assert!(
        matches!(
            vertical,
            Err(StatusRefusal::ObjectDiffersAlongTheVerticalIndex { .. })
        ),
        "the vertical index refuses a second object, got {vertical:?}"
    );
    // A horizontal family refuses a row (two environments):
    let row: Vec<SituatedFamily> = ["assayA", "assayB"]
        .iter()
        .map(|label| {
            family.designs()[0]
                .face(label)
                .expect("a face")
                .clone()
        })
        .collect();
    let horizontal = HorizontalFamily::at_one_environment(row);
    assert!(
        matches!(
            horizontal,
            Err(StatusRefusal::Environment(
                EnvironmentRefusal::EnvironmentsDiffer { .. }
            ))
        ),
        "the horizontal index refuses a second environment, got {horizontal:?}"
    );
    // And the plural fibre refuses the whole rectangle: it is one object at one receiver.
    let fibre = PluralFibre::over_one_candidate(column);
    assert!(
        matches!(fibre, Err(plural_fibre::FibreRefusal::ObjectDiffersInTheFibre { .. })),
        "the plural fibre is one object and refuses a design population, got {fibre:?}"
    );
}

#[test]
fn two_designs_about_one_object_are_refused() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside, ContactClass::Outside];
    let readings = [
        ("affinity", "assayA", read(1)),
        ("affinity", "assayB", read(1)),
    ];
    let designs = vec![
        synthetic_design(1, "ALA", &[("assayA", &a, &classes), ("assayB", &b, &classes)], &readings),
        synthetic_design(2, "ALA", &[("assayA", &a, &classes), ("assayB", &b, &classes)], &readings),
    ];
    let refusal = DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    );
    assert!(
        matches!(refusal, Err(SelectionRefusal::TwoDesignsAreOneObject { .. })),
        "two designs about one object are one object read twice, got {refusal:?}"
    );
}

#[test]
fn a_face_filed_under_the_wrong_label_is_refused() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside];
    // The two faces are at the two declared environments, filed under each other's labels. The
    // design founds — it really is one object at two environments — and the family refuses,
    // because a label addresses an environment and never replaces it.
    let swapped = synthetic_design(
        1,
        "ALA",
        &[("assayA", &b, &classes), ("assayB", &a, &classes)],
        &[
            ("affinity", "assayA", read(1)),
            ("affinity", "assayB", read(1)),
        ],
    );
    let refusal = DesignFamily::declare(
        vec![swapped],
        environments.clone(),
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    );
    assert!(
        matches!(refusal, Err(SelectionRefusal::FaceIsNotAtTheLabelledEnvironment { .. })),
        "a label addresses an environment and never replaces it, got {refusal:?}"
    );

    // And two faces at one environment value are not two points of the vertical index, so the
    // design owner refuses before the family is even declared.
    let repeated = Design::found(
        DesignId(1),
        "two faces at one environment",
        [
            (
                "assayA".to_owned(),
                fixture::synthetic_family_named(1, &a, &classes, &["ALA".to_owned()]),
            ),
            (
                "assayB".to_owned(),
                fixture::synthetic_family_named(2, &a, &classes, &["ALA".to_owned()]),
            ),
        ],
        [],
    );
    assert!(
        matches!(
            repeated,
            Err(SelectionRefusal::Status(
                StatusRefusal::EnvironmentRepeatedAlongTheVerticalIndex { .. }
            ))
        ),
        "a design's faces are the vertical index of one object, got {repeated:?}"
    );
}

#[test]
fn a_missing_reading_is_refused_and_never_defaulted() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside];
    let design = synthetic_design(
        1,
        "ALA",
        &[("assayA", &a, &classes), ("assayB", &b, &classes)],
        &[("affinity", "assayA", read(1))],
    );
    let refusal = DesignFamily::declare(
        vec![design],
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    );
    assert!(
        matches!(refusal, Err(SelectionRefusal::ReadingNotStated { .. })),
        "an unstated axis is refused rather than defaulted, got {refusal:?}"
    );
}

#[test]
fn a_design_population_above_the_ceiling_is_refused_before_any_pass() {
    // The comparison ceiling is checked with checked arithmetic at declaration time. A family
    // whose declared receiver count alone exceeds its ceiling is refused by name.
    let environments = two_environments();
    let receivers: Vec<DeclaredReceiver> = (0..=RECEIVER_CEILING)
        .map(|at| receiver(&format!("receiver{at}"), Sense::SmallerIsBetter))
        .collect();
    let refusal = DesignFamily::declare(Vec::new(), environments.clone(), receivers.clone());
    assert!(matches!(refusal, Err(SelectionRefusal::EmptyFamily)));

    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside];
    let design = synthetic_design(
        1,
        "ALA",
        &[("assayA", &a, &classes), ("assayB", &b, &classes)],
        &[("receiver0", "assayA", read(1))],
    );
    let refusal = DesignFamily::declare(vec![design], environments, receivers);
    assert!(
        matches!(refusal, Err(SelectionRefusal::ReceiverFamilyTooLarge { .. })),
        "a declared size above its ceiling is refused before any pass, got {refusal:?}"
    );
}

// ---------------------------------------------------------------------------------------------
// Stage one: hard constraints
// ---------------------------------------------------------------------------------------------

#[test]
fn a_violated_hard_constraint_removes_the_best_design() {
    let family = worked_family();
    // Design 3 is best at both receivers: lowest affinity and highest interface.
    let no_constraints = family.admit(&[]);
    assert_eq!(
        no_constraints.admitted,
        vec![DesignId(1), DesignId(2), DesignId(3)]
    );
    let frontier = family
        .frontier(&no_constraints.admitted)
        .expect("the frontier runs");
    assert!(frontier.contains(&DesignId(3)), "design 3 is on the frontier");

    let constraint = HardConstraint::declare(
        "the declared expression host is admitted",
        "declared by the synthetic selection fixture",
        |design: &Design| design.id != DesignId(3),
    )
    .expect("a stated name and ground");
    let stage = family.admit(std::slice::from_ref(&constraint));
    assert_eq!(stage.admitted, vec![DesignId(1), DesignId(2)]);
    assert!(
        !stage.admitted.contains(&DesignId(3)),
        "a violated hard constraint removes the design however every receiver reads it"
    );
    assert_eq!(
        stage.refused,
        vec![ConstraintViolation {
            design: DesignId(3),
            constraint: "the declared expression host is admitted".to_owned(),
            ground: "declared by the synthetic selection fixture".to_owned(),
        }],
        "the refusal names the constraint and is not a penalty term"
    );
    // And the refusal survives every weighting, because no weight enters this stage at all.
    for numerator in 1..=5_i64 {
        let weighting = ReceiverWeighting::declare([
            ("affinity".to_owned(), ratio(numerator, 7)),
            ("interface".to_owned(), ratio(6 - numerator, 11)),
        ])
        .expect("nonnegative weights");
        let minimizers = family
            .scalar_minimizers(&stage.admitted, &weighting)
            .expect("the scalar runs on the admitted family");
        assert!(
            !minimizers.contains(&DesignId(3)),
            "the refused design is not in the admitted family at any weighting"
        );
    }
}

#[test]
fn a_plural_reading_has_no_scalar() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside];
    let family = DesignFamily::declare(
        vec![synthetic_design(
            1,
            "ALA",
            &[("assayA", &a, &classes), ("assayB", &b, &classes)],
            &[
                ("affinity", "assayA", plural(1, 9)),
                ("affinity", "assayB", plural(1, 9)),
            ],
        )],
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let weighting =
        ReceiverWeighting::declare([("affinity".to_owned(), rat(1))]).expect("nonnegative");
    assert_eq!(
        family
            .objective(DesignId(1), &weighting)
            .expect("the objective runs"),
        None,
        "a bound of an undecided reading is not a scalar, and no substitute is returned"
    );
    assert!(
        family
            .scalar_minimizers(&[DesignId(1)], &weighting)
            .expect("the scalar runs")
            .is_empty()
    );
}

#[test]
fn a_negative_weight_is_refused() {
    let refusal = ReceiverWeighting::declare([("affinity".to_owned(), rat(-1))]);
    assert!(matches!(
        refusal,
        Err(SelectionRefusal::NegativeWeight { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// Stage two: the frontier
// ---------------------------------------------------------------------------------------------

#[test]
fn the_frontier_keeps_every_nondominated_design_and_drops_the_dominated_one() {
    let family = worked_family();
    let all = vec![DesignId(1), DesignId(2), DesignId(3)];
    let frontier = family.frontier(&all).expect("the frontier runs");
    // Design 3 dominates design 1 and design 2 at every (receiver, environment) axis, so only
    // design 3 survives.
    assert_eq!(frontier, vec![DesignId(3)]);
}

#[test]
fn an_undecided_comparison_never_licenses_a_discard() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside];
    let other = [ContactClass::Outside];
    let designs = vec![
        // Design 1 is decidedly better everywhere except at one axis, where its reading is plural
        // and overlaps design 2's.
        synthetic_design(
            1,
            "ALA",
            &[("assayA", &a, &classes), ("assayB", &b, &classes)],
            &[
                ("affinity", "assayA", read(1)),
                ("affinity", "assayB", plural(1, 9)),
            ],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("assayA", &a, &other), ("assayB", &b, &other)],
            &[
                ("affinity", "assayA", read(5)),
                ("affinity", "assayB", plural(4, 6)),
            ],
        ),
    ];
    let family = DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let frontier = family
        .frontier(&[DesignId(1), DesignId(2)])
        .expect("the frontier runs");
    assert_eq!(
        frontier,
        vec![DesignId(1), DesignId(2)],
        "an undecided comparison leaves the candidate on the frontier; openness is never resolved \
         by a default"
    );
}

#[test]
fn an_unread_axis_never_licenses_a_discard_either() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside];
    let other = [ContactClass::Outside];
    let designs = vec![
        synthetic_design(
            1,
            "ALA",
            &[("assayA", &a, &classes), ("assayB", &b, &classes)],
            &[
                ("affinity", "assayA", read(1)),
                ("affinity", "assayB", read(1)),
            ],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("assayA", &a, &other), ("assayB", &b, &other)],
            &[
                ("affinity", "assayA", read(5)),
                (
                    "affinity",
                    "assayB",
                    ReceiverReading::unread("the assay was not run for this design")
                        .expect("a stated reason"),
                ),
            ],
        ),
    ];
    let family = DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let frontier = family
        .frontier(&[DesignId(1), DesignId(2)])
        .expect("the frontier runs");
    assert_eq!(frontier, vec![DesignId(1), DesignId(2)]);
}

// ---------------------------------------------------------------------------------------------
// Stage three: the worst environment
// ---------------------------------------------------------------------------------------------

#[test]
fn the_worst_is_taken_over_the_declared_environments_and_every_attaining_one_is_returned() {
    let family = worked_family();
    // Design 2 is worst at assayB on affinity (1200 against 101), smaller being better.
    let worst = family
        .worst_over(DesignId(2), "affinity")
        .expect("the worst runs");
    assert_eq!(
        worst,
        WorstVerdict::Worst {
            value: ExactInterval::point(rat(1200)),
            attained: vec!["assayB".to_owned()],
        }
    );
    // Design 1 reads 100 at both, so both environments attain the worst and both are returned.
    let worst = family
        .worst_over(DesignId(1), "affinity")
        .expect("the worst runs");
    assert_eq!(
        worst,
        WorstVerdict::Worst {
            value: ExactInterval::point(rat(100)),
            attained: vec!["assayA".to_owned(), "assayB".to_owned()],
        },
        "every declared environment attaining the worst is returned; a tie is not broken"
    );
    // On a greater-is-better receiver the worst is the smallest reading.
    let worst = family
        .worst_over(DesignId(3), "interface")
        .expect("the worst runs");
    assert_eq!(
        worst,
        WorstVerdict::Worst {
            value: ExactInterval::point(rat(41)),
            attained: vec!["assayA".to_owned(), "assayB".to_owned()],
        }
    );
}

#[test]
fn an_undeclared_environment_is_absent_from_the_worst() {
    let base = worked_family();
    let with_one_environment = {
        let environments = vec![base.environments()[0].clone()];
        let designs: Vec<Design> = base
            .designs()
            .iter()
            .map(|design| {
                Design::found(
                    design.id,
                    design.lineage.clone(),
                    [(
                        "assayA".to_owned(),
                        design.face("assayA").expect("a face").clone(),
                    )],
                    base.receivers().iter().map(|receiver| {
                        (
                            (receiver.name().to_owned(), "assayA".to_owned()),
                            design
                                .reading(receiver.name(), "assayA")
                                .expect("a stated axis")
                                .clone(),
                        )
                    }),
                )
                .expect("a design founds")
            })
            .collect();
        DesignFamily::declare(designs, environments, base.receivers().to_vec())
            .expect("the one-environment family declares")
    };
    // Design 2 reads 1200 at assayB. With assayB undeclared, that reading is ABSENT: it is not a
    // worst case, and it is not a best case either.
    let worst = with_one_environment
        .worst_over(DesignId(2), "affinity")
        .expect("the worst runs");
    assert_eq!(
        worst,
        WorstVerdict::Worst {
            value: ExactInterval::point(rat(101)),
            attained: vec!["assayA".to_owned()],
        },
        "an environment the declaration does not carry contributes nothing at all"
    );
}

#[test]
fn a_design_unread_at_a_declared_environment_is_refused_for_ranking_there() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside];
    let other = [ContactClass::Outside];
    let designs = vec![
        synthetic_design(
            1,
            "ALA",
            &[("assayA", &a, &classes), ("assayB", &b, &classes)],
            &[
                ("affinity", "assayA", read(1)),
                ("affinity", "assayB", read(2)),
            ],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("assayA", &a, &other), ("assayB", &b, &other)],
            &[
                ("affinity", "assayA", read(5)),
                (
                    "affinity",
                    "assayB",
                    ReceiverReading::unread("the cross-species assay was not run")
                        .expect("a stated reason"),
                ),
            ],
        ),
    ];
    let family = DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let worst = family
        .worst_over(DesignId(2), "affinity")
        .expect("the worst runs");
    assert_eq!(
        worst,
        WorstVerdict::UnreadAt {
            environment: "assayB".to_owned(),
            why: "the cross-species assay was not run".to_owned(),
        },
        "an unread declared environment refuses the ranking rather than imputing a value"
    );
    let ranking = family
        .rank_by_worst_environment(&[DesignId(1), DesignId(2)], "affinity")
        .expect("the ranking runs");
    assert_eq!(
        ranking.refused,
        vec![(
            DesignId(2),
            "assayB".to_owned(),
            "the cross-species assay was not run".to_owned()
        )]
    );
    assert!(
        ranking.tiers.is_none(),
        "a refused design leaves no total order to report"
    );
    assert_eq!(
        ranking.best,
        vec![DesignId(1), DesignId(2)],
        "the refused design is not imputed a best case and not imputed a worst case"
    );
}

#[test]
fn ties_are_returned_as_ties_and_never_broken_by_presentation_order() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let one = [ContactClass::Inside, ContactClass::Outside];
    let two = [ContactClass::Outside, ContactClass::Inside];
    let three = [ContactClass::Inside, ContactClass::Inside];
    let equal = [
        ("affinity", "assayA", read(7)),
        ("affinity", "assayB", read(7)),
    ];
    let worse = [
        ("affinity", "assayA", read(9)),
        ("affinity", "assayB", read(9)),
    ];
    let designs = vec![
        synthetic_design(2, "GLY", &[("assayA", &a, &two), ("assayB", &b, &two)], &equal),
        synthetic_design(1, "ALA", &[("assayA", &a, &one), ("assayB", &b, &one)], &equal),
        synthetic_design(
            3,
            "SER",
            &[("assayA", &a, &three), ("assayB", &b, &three)],
            &worse,
        ),
    ];
    let family = DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    // Presented in the order 2, 1, 3.
    let ranking = family
        .rank_by_worst_environment(&[DesignId(2), DesignId(1), DesignId(3)], "affinity")
        .expect("the ranking runs");
    assert_eq!(
        ranking.tiers,
        Some(vec![vec![DesignId(1), DesignId(2)], vec![DesignId(3)]]),
        "the tie is a whole tier sorted by identity, not by the order of presentation"
    );
    assert!(ranking.undecided.is_empty());
    assert_eq!(ranking.best, vec![DesignId(1), DesignId(2)]);
}

#[test]
fn an_undecided_pair_is_returned_rather_than_ordered() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let one = [ContactClass::Inside];
    let two = [ContactClass::Outside];
    let designs = vec![
        synthetic_design(
            1,
            "ALA",
            &[("assayA", &a, &one), ("assayB", &b, &one)],
            &[
                ("affinity", "assayA", plural(1, 9)),
                ("affinity", "assayB", plural(1, 9)),
            ],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("assayA", &a, &two), ("assayB", &b, &two)],
            &[
                ("affinity", "assayA", plural(4, 6)),
                ("affinity", "assayB", plural(4, 6)),
            ],
        ),
    ];
    let family = DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let ranking = family
        .rank_by_worst_environment(&[DesignId(1), DesignId(2)], "affinity")
        .expect("the ranking runs");
    assert_eq!(ranking.undecided, vec![(DesignId(1), DesignId(2))]);
    assert!(
        ranking.tiers.is_none(),
        "an undecided pair leaves no total order to report and is never tie-broken"
    );
}

// ---------------------------------------------------------------------------------------------
// The scalar is one receiver, never the identity of a candidate
// ---------------------------------------------------------------------------------------------

/// The three-point chord family of `PresentationCost.lean::chordFamily`, lifted to designs: two
/// corners and one balanced design, every reading exact, both receivers smaller-is-better.
fn chord_family() -> DesignFamily {
    let environments = vec![
        DeclaredEnvironment::declare("only", environment("apo")).expect("a stated label"),
    ];
    let env = environments[0].environment().clone();
    let one = [ContactClass::Inside, ContactClass::Outside];
    let two = [ContactClass::Outside, ContactClass::Inside];
    let three = [ContactClass::Inside, ContactClass::Inside];
    let designs = vec![
        synthetic_design(
            1,
            "ALA",
            &[("only", &env, &one)],
            &[
                ("bytes", "only", read(0)),
                ("decode", "only", read(10)),
            ],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("only", &env, &two)],
            &[
                ("bytes", "only", read(10)),
                ("decode", "only", read(0)),
            ],
        ),
        synthetic_design(
            3,
            "SER",
            &[("only", &env, &three)],
            &[
                ("bytes", "only", read(6)),
                ("decode", "only", read(6)),
            ],
        ),
    ];
    DesignFamily::declare(
        designs,
        environments,
        vec![
            receiver("bytes", Sense::SmallerIsBetter),
            receiver("decode", Sense::SmallerIsBetter),
        ],
    )
    .expect("the chord family declares")
}

#[test]
fn a_scalar_first_cascade_discards_a_frontier_design_every_stage_above_would_keep() {
    let family = chord_family();
    let all = vec![DesignId(1), DesignId(2), DesignId(3)];

    // Stage one admits all three.
    let admitted = family.admit(&[]);
    assert_eq!(admitted.admitted, all);
    // Stage two keeps all three: the family is an antichain.
    let frontier = family.frontier(&all).expect("the frontier runs");
    assert_eq!(frontier, all, "all three are frontier points");
    // Stage three ranks by the worst environment; the single declared environment is the worst.
    let ranking = family
        .rank_by_worst_environment(&frontier, "bytes")
        .expect("the ranking runs");
    assert_eq!(
        ranking.tiers,
        Some(vec![
            vec![DesignId(1)],
            vec![DesignId(3)],
            vec![DesignId(2)]
        ])
    );
    // Stage five puts each design in its own cluster (their contact faces all separate).
    let clusters = family
        .structural_clusters(&frontier, "only")
        .expect("clustering runs");
    assert_eq!(clusters.components.len(), 3);
    // Stage four therefore keeps one representative per cluster, design 3 among them.
    let diversity = family
        .quality_diversity(&clusters, &ranking)
        .expect("quality-diversity runs");
    assert!(
        diversity
            .representatives
            .iter()
            .any(|(_, best)| best.contains(&DesignId(3))),
        "quality-diversity keeps the balanced design: it is the best of its own cluster"
    );

    // And yet: no weighting putting positive weight on either varying axis selects design 3. This
    // is `PresentationCost.lean::unsupported_not_minimizer` at a design family.
    for bytes in 0..=12_i64 {
        for decode in 0..=12_i64 {
            if bytes == 0 && decode == 0 {
                continue;
            }
            let weighting = ReceiverWeighting::declare([
                ("bytes".to_owned(), ratio(bytes, 13)),
                ("decode".to_owned(), ratio(decode, 13)),
            ])
            .expect("nonnegative weights");
            let minimizers = family
                .scalar_minimizers(&all, &weighting)
                .expect("the scalar runs");
            assert!(
                !minimizers.contains(&DesignId(3)),
                "the balanced design is on the frontier and is a minimizer of no weighting \
                 (bytes={bytes}/13, decode={decode}/13), so a scalar-first cascade loses it"
            );
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Stage five: structural clustering from the exact separator structure
// ---------------------------------------------------------------------------------------------

/// Three designs whose contact faces are decided-inside, open and decided-outside at the one
/// contact: openness makes indistinguishability intransitive.
fn open_chain_family() -> DesignFamily {
    let environments =
        vec![DeclaredEnvironment::declare("only", environment("apo")).expect("a stated label")];
    let env = environments[0].environment().clone();
    let designs = vec![
        synthetic_design(
            1,
            "ALA",
            &[("only", &env, &[ContactClass::Inside])],
            &[("affinity", "only", read(1))],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("only", &env, &[ContactClass::Open])],
            &[("affinity", "only", read(2))],
        ),
        synthetic_design(
            3,
            "SER",
            &[("only", &env, &[ContactClass::Outside])],
            &[("affinity", "only", read(3))],
        ),
    ];
    DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the open-chain family declares")
}

#[test]
fn structural_clusters_come_from_the_exact_separator_structure() {
    let family = open_chain_family();
    let separator = family
        .separator_between(DesignId(1), DesignId(3), "only")
        .expect("the separator runs");
    assert_eq!(separator.separating.len(), 1);
    assert_eq!(separator.separating[0].left, DecidedClass::Formed);
    assert_eq!(separator.separating[0].right, DecidedClass::Excluded);
    assert!(separator.open_carrying.is_empty());

    // The open reading is carried and counted on neither side.
    let with_open = family
        .separator_between(DesignId(1), DesignId(2), "only")
        .expect("the separator runs");
    assert!(with_open.separating.is_empty());
    assert_eq!(with_open.open_carrying, vec![(1, 1)]);
    assert_eq!(with_open.agreeing, 0);
}

#[test]
fn a_component_is_not_an_equivalence_class_of_indistinguishability() {
    let family = open_chain_family();
    let clusters = family
        .structural_clusters(&[DesignId(1), DesignId(2), DesignId(3)], "only")
        .expect("clustering runs");
    assert_eq!(
        clusters.components,
        vec![vec![DesignId(1), DesignId(2), DesignId(3)]],
        "the open reading links the two decided designs into one component"
    );
    assert_eq!(
        clusters.separated_pairs_inside_a_component,
        vec![(DesignId(1), DesignId(3))],
        "and the receiver still separates that pair: a cluster is a component, not a merge"
    );
}

#[test]
fn quality_diversity_keeps_a_cluster_a_top_one_would_lose() {
    let environments =
        vec![DeclaredEnvironment::declare("only", environment("apo")).expect("a stated label")];
    let env = environments[0].environment().clone();
    // Designs 1 and 2 are indistinguishable at the contact receiver and score best; design 3 is a
    // cluster of its own and scores worst. A top-1 by the scalar loses design 3's cluster.
    let shared = [ContactClass::Inside, ContactClass::Outside];
    let apart = [ContactClass::Outside, ContactClass::Inside];
    let designs = vec![
        synthetic_design(
            1,
            "ALA",
            &[("only", &env, &shared)],
            &[("affinity", "only", read(1))],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("only", &env, &shared)],
            &[("affinity", "only", read(2))],
        ),
        synthetic_design(
            3,
            "SER",
            &[("only", &env, &apart)],
            &[("affinity", "only", read(99))],
        ),
    ];
    let family = DesignFamily::declare(
        designs,
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let all = vec![DesignId(1), DesignId(2), DesignId(3)];
    let clusters = family
        .structural_clusters(&all, "only")
        .expect("clustering runs");
    assert_eq!(
        clusters.components,
        vec![vec![DesignId(1), DesignId(2)], vec![DesignId(3)]]
    );
    let ranking = family
        .rank_by_worst_environment(&all, "affinity")
        .expect("the ranking runs");
    let diversity = family
        .quality_diversity(&clusters, &ranking)
        .expect("quality-diversity runs");
    assert_eq!(
        diversity.representatives,
        vec![
            (vec![DesignId(1), DesignId(2)], vec![DesignId(1)]),
            (vec![DesignId(3)], vec![DesignId(3)]),
        ],
        "one representative set per cluster, so the second cluster survives"
    );
    let weighting =
        ReceiverWeighting::declare([("affinity".to_owned(), rat(1))]).expect("nonnegative");
    let minimizers = family
        .scalar_minimizers(&all, &weighting)
        .expect("the scalar runs");
    assert_eq!(
        minimizers,
        vec![DesignId(1)],
        "the top of the scalar is one design and its cluster; the other cluster is lost"
    );
}

// ---------------------------------------------------------------------------------------------
// The merge verdict
// ---------------------------------------------------------------------------------------------

fn worked_situation(
    family: &DesignFamily,
    history_ceiling: usize,
) -> (Vec<AdmittedTransformation>, Situation<SituatedDesign, ReceiverReading>) {
    let change = family
        .admit_environment_change(
            "assayA",
            "assayB",
            "the two assays differ only in the declared target conformation, which this passage \
             accounts for",
            [CoordinateName::Conformation],
        )
        .expect("the environment passage is admitted");
    let transformations = vec![change];
    let situation = family
        .design_situation(&transformations, history_ceiling)
        .expect("the design situation declares");
    (transformations, situation)
}

#[test]
fn not_separated_within_bound_never_coerces_to_a_merge() {
    // Exhaustively: only `EquivalentBy` licenses a merge.
    let verdicts: Vec<MergeVerdict<ReceiverReading>> = vec![
        MergeVerdict::NotSeparatedWithinBound {
            history_length: 3,
            histories_examined: 7,
            receivers: 2,
        },
        MergeVerdict::Refuted {
            separator: Box::new(Separator {
                word: Vec::new(),
                word_names: Vec::new(),
                receiver: 0,
                receiver_name: "affinity".to_owned(),
                left_face: read(1),
                right_face: read(2),
            }),
        },
        MergeVerdict::EquivalentBy {
            isomorphism: "swap".to_owned(),
            probe: 4,
        },
    ];
    for verdict in &verdicts {
        assert_eq!(
            verdict.licenses_merge(),
            matches!(verdict, MergeVerdict::EquivalentBy { .. }),
            "only an exhibited isomorphism licenses a merge, got {verdict:?}"
        );
        let merged = merge(DesignId(1), DesignId(2), verdict);
        assert_eq!(
            merged.is_ok(),
            verdict.licenses_merge(),
            "`merge` has no other constructor, so an unlicensed verdict returns a refusal"
        );
    }

    // And on a real family: the two designs agree at every declared receiver at `assayA`, so at
    // history ceiling 0 the bounded search exhausts and the honest return is
    // NotSeparatedWithinBound — never a merge.
    let family = agreeing_at_a_family();
    let (transformations, at_zero) = worked_situation(&family, 0);
    let left = SituatedDesign {
        design: 0,
        environment: 0,
    };
    let right = SituatedDesign {
        design: 1,
        environment: 0,
    };
    let verdict =
        merge_verdict(&at_zero, &left, &right, &Declarations::default()).expect("the verdict runs");
    assert!(
        matches!(verdict, MergeVerdict::NotSeparatedWithinBound { .. }),
        "a bounded search returns its own value, got {verdict:?}"
    );
    assert!(!verdict.licenses_merge());
    assert!(matches!(
        merge(DesignId(1), DesignId(2), &verdict),
        Err(SelectionRefusal::MergeNotLicensed {
            verdict: "NotSeparatedWithinBound"
        })
    ));

    // Enlarging the declared history ceiling refutes the same pair: `equalPotentialAntitone`,
    // executable.
    let at_one = family
        .design_situation(&transformations, 1)
        .expect("the design situation declares");
    let verdict =
        merge_verdict(&at_one, &left, &right, &Declarations::default()).expect("the verdict runs");
    let MergeVerdict::Refuted { separator } = &verdict else {
        panic!("the environment change separates designs 1 and 2, got {verdict:?}");
    };
    assert_eq!(separator.receiver_name, "affinity");
    assert_eq!(separator.left_face, read(100));
    assert_eq!(separator.right_face, read(1200));
    assert!(!verdict.licenses_merge());
}

#[test]
fn present_receiver_agreement_does_not_imply_environment_agreement() {
    let family = worked_family();
    let (_, situation) = worked_situation(&family, 1);
    let left = SituatedDesign {
        design: 0,
        environment: 0,
    };
    let right = SituatedDesign {
        design: 1,
        environment: 0,
    };
    // Designs 1 and 2 read 100 and 101 at assayA on affinity and 40 on interface, so the present
    // receivers do NOT all agree here. Compare designs 1 and 2 on the interface receiver alone by
    // building the one-receiver family below; for the present-agreement statement use the pair
    // that really agrees now.
    let agreement = situation
        .present_agreement(&left, &right)
        .expect("the receivers read");
    assert!(
        agreement.is_some(),
        "the affinity receiver already separates 100 from 101 at assayA"
    );

    // The statement itself, on a family whose two designs agree at every present receiver and are
    // separated by the declared environment family.
    let agreeing = agreeing_at_a_family();
    let (_, situation) = worked_situation(&agreeing, 1);
    assert!(
        situation
            .present_agreement(&left, &right)
            .expect("the receivers read")
            .is_none(),
        "every declared receiver returns the same face now"
    );
    let verdict = merge_verdict(&situation, &left, &right, &Declarations::default())
        .expect("the verdict runs");
    let MergeVerdict::Refuted { separator } = &verdict else {
        panic!("the declared environment family separates them, got {verdict:?}");
    };
    assert_eq!(separator.word_names, vec!["environment change 0 -> 1"]);
    assert!(!verdict.licenses_merge());
}

#[test]
fn environment_agreement_at_the_declared_environments_does_not_imply_an_undeclared_one() {
    // The same two designs, declared over one environment and over two. At one environment they
    // are not separated within the bound; at two the second environment separates them.
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let one = [ContactClass::Inside];
    let two = [ContactClass::Outside];
    let build = |declared: Vec<DeclaredEnvironment>| {
        let labels: Vec<&str> = declared.iter().map(|d| d.label()).collect();
        let faces_one: Vec<(&str, &Environment, &[ContactClass])> = labels
            .iter()
            .map(|label| {
                let env = if *label == "assayA" { &a } else { &b };
                (*label, env, one.as_slice())
            })
            .collect();
        let faces_two: Vec<(&str, &Environment, &[ContactClass])> = labels
            .iter()
            .map(|label| {
                let env = if *label == "assayA" { &a } else { &b };
                (*label, env, two.as_slice())
            })
            .collect();
        let readings_one: Vec<(&str, &str, ReceiverReading)> = labels
            .iter()
            .map(|label| ("affinity", *label, read(100)))
            .collect();
        let readings_two: Vec<(&str, &str, ReceiverReading)> = labels
            .iter()
            .map(|label| {
                (
                    "affinity",
                    *label,
                    if *label == "assayA" {
                        read(100)
                    } else {
                        read(1200)
                    },
                )
            })
            .collect();
        DesignFamily::declare(
            vec![
                synthetic_design(1, "ALA", &faces_one, &readings_one),
                synthetic_design(2, "GLY", &faces_two, &readings_two),
            ],
            declared,
            vec![receiver("affinity", Sense::SmallerIsBetter)],
        )
        .expect("the family declares")
    };

    let left = SituatedDesign {
        design: 0,
        environment: 0,
    };
    let right = SituatedDesign {
        design: 1,
        environment: 0,
    };

    let one_environment = build(vec![environments[0].clone()]);
    let situation = one_environment
        .design_situation(&[], 1)
        .expect("a situation with no generator still declares");
    let verdict = merge_verdict(&situation, &left, &right, &Declarations::default())
        .expect("the verdict runs");
    assert!(
        matches!(verdict, MergeVerdict::NotSeparatedWithinBound { .. }),
        "over the smaller declaration the bounded search finds nothing — and still licenses \
         nothing, got {verdict:?}"
    );
    assert!(!verdict.licenses_merge());

    let two_environments = build(environments);
    let (_, enlarged) = worked_situation(&two_environments, 1);
    let verdict = merge_verdict(&enlarged, &left, &right, &Declarations::default())
        .expect("the verdict runs");
    assert!(
        matches!(verdict, MergeVerdict::Refuted { .. }),
        "declaring the second environment refines the relation and refutes the collapse, got \
         {verdict:?}"
    );
}

#[test]
fn an_exhibited_equivariant_isomorphism_licenses_the_merge_and_a_separator_refutes_it() {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let one = [ContactClass::Inside];
    let two = [ContactClass::Outside];
    let readings = [
        ("affinity", "assayA", read(100)),
        ("affinity", "assayB", read(200)),
    ];
    let family = DesignFamily::declare(
        vec![
            synthetic_design(
                1,
                "ALA",
                &[("assayA", &a, &one), ("assayB", &b, &one)],
                &readings,
            ),
            synthetic_design(
                2,
                "GLY",
                &[("assayA", &a, &two), ("assayB", &b, &two)],
                &readings,
            ),
        ],
        environments.clone(),
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let (_, situation) = worked_situation(&family, 2);

    let swap = SituationAutomorphism::new(
        "swap the two designs",
        |situated: &SituatedDesign| {
            Ok(SituatedDesign {
                design: 1 - situated.design,
                environment: situated.environment,
            })
        },
        |situated: &SituatedDesign| {
            Ok(SituatedDesign {
                design: 1 - situated.design,
                environment: situated.environment,
            })
        },
    );
    let probe: Vec<SituatedDesign> = (0..2)
        .flat_map(|design| {
            (0..2).map(move |environment| SituatedDesign {
                design,
                environment,
            })
        })
        .collect();
    let declared = Declarations {
        automorphism: Some(AutomorphismClaim {
            automorphism: &swap,
            probe: &probe,
            probe_is_the_whole_carrier: true,
        }),
        tolerance: None,
    };
    let left = SituatedDesign {
        design: 0,
        environment: 0,
    };
    let right = SituatedDesign {
        design: 1,
        environment: 0,
    };
    let verdict = merge_verdict(&situation, &left, &right, &declared).expect("the verdict runs");
    assert!(
        verdict.licenses_merge(),
        "an exhibited equivariant isomorphism over a probe declared exhaustive licenses the \
         merge, got {verdict:?}"
    );
    let merged = merge(DesignId(1), DesignId(2), &verdict).expect("the merge is licensed");
    assert_eq!(merged.members(), [DesignId(1), DesignId(2)]);
    assert_eq!(merged.licensed_by(), "swap the two designs");
    assert_eq!(merged.probe(), 4);

    // Now move one reading so the receivers separate. The same declaration is offered and the
    // separator wins: evidence overrides a declaration.
    let separated = DesignFamily::declare(
        vec![
            synthetic_design(
                1,
                "ALA",
                &[("assayA", &a, &one), ("assayB", &b, &one)],
                &readings,
            ),
            synthetic_design(
                2,
                "GLY",
                &[("assayA", &a, &two), ("assayB", &b, &two)],
                &[
                    ("affinity", "assayA", read(100)),
                    ("affinity", "assayB", read(1200)),
                ],
            ),
        ],
        environments,
        vec![receiver("affinity", Sense::SmallerIsBetter)],
    )
    .expect("the family declares");
    let (_, situation) = worked_situation(&separated, 2);
    let declared = Declarations {
        automorphism: Some(AutomorphismClaim {
            automorphism: &swap,
            probe: &probe,
            probe_is_the_whole_carrier: true,
        }),
        tolerance: None,
    };
    let verdict = merge_verdict(&situation, &left, &right, &declared).expect("the verdict runs");
    assert!(
        matches!(verdict, MergeVerdict::Refuted { .. }),
        "a separator overrides a declared isomorphism, got {verdict:?}"
    );
    assert!(!verdict.licenses_merge());
    assert!(merge(DesignId(1), DesignId(2), &verdict).is_err());
}

// ---------------------------------------------------------------------------------------------
// The empirical pattern the plan records, modelled exactly
// ---------------------------------------------------------------------------------------------

/// The plan's two recorded observations as one synthetic family on exact rationals.
///
/// **These are not measurements.** The mounted M5 release carries three presentations of one
/// object and no dissociation constant, no cross-species assay and no second design; see this
/// module's report and the plan's B8 paragraph.
fn empirical_pattern_family() -> DesignFamily {
    let environments = vec![
        DeclaredEnvironment::declare("human", environment("apo")).expect("a stated label"),
        DeclaredEnvironment::declare("mouse", environment("holo")).expect("a stated label"),
    ];
    let (human, mouse) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let faces = |seed: usize| -> [ContactClass; 4] {
        let mut classes = [ContactClass::Outside; 4];
        classes[seed] = ContactClass::Inside;
        classes
    };
    let designs = vec![
        // Two binders within two per cent on the final dissociation constant at the human assay,
        // qualitatively different at the mouse assay.
        synthetic_design(
            1,
            "ALA",
            &[("human", &human, &faces(0)), ("mouse", &mouse, &faces(0))],
            &[
                ("dissociationConstant", "human", read(100)),
                ("dissociationConstant", "mouse", read(100)),
                ("interfaceContacts", "human", read(40)),
                ("interfaceContacts", "mouse", read(40)),
            ],
        ),
        synthetic_design(
            2,
            "GLY",
            &[("human", &human, &faces(1)), ("mouse", &mouse, &faces(1))],
            &[
                ("dissociationConstant", "human", read(101)),
                ("dissociationConstant", "mouse", read(1200)),
                ("interfaceContacts", "human", read(40)),
                ("interfaceContacts", "mouse", read(40)),
            ],
        ),
        // Two designs with equal predicted interface receivers and a six-fold affinity difference.
        synthetic_design(
            3,
            "SER",
            &[("human", &human, &faces(2)), ("mouse", &mouse, &faces(2))],
            &[
                ("dissociationConstant", "human", read(50)),
                ("dissociationConstant", "mouse", read(50)),
                ("interfaceContacts", "human", read(41)),
                ("interfaceContacts", "mouse", read(41)),
            ],
        ),
        synthetic_design(
            4,
            "THR",
            &[("human", &human, &faces(3)), ("mouse", &mouse, &faces(3))],
            &[
                ("dissociationConstant", "human", read(300)),
                ("dissociationConstant", "mouse", read(300)),
                ("interfaceContacts", "human", read(41)),
                ("interfaceContacts", "mouse", read(41)),
            ],
        ),
        // A design every declared receiver reads exactly as it reads design 1 **at the human
        // assay**, and which the mouse assay separates: present-receiver agreement that the
        // declared environment family refutes.
        synthetic_design(
            5,
            "VAL",
            &[("human", &human, &faces(0)), ("mouse", &mouse, &faces(1))],
            &[
                ("dissociationConstant", "human", read(100)),
                ("dissociationConstant", "mouse", read(900)),
                ("interfaceContacts", "human", read(40)),
                ("interfaceContacts", "mouse", read(40)),
            ],
        ),
    ];
    DesignFamily::declare(
        designs,
        environments,
        vec![
            receiver("dissociationConstant", Sense::SmallerIsBetter),
            receiver("interfaceContacts", Sense::GreaterIsBetter),
        ],
    )
    .expect("the empirical-pattern family declares")
}

#[test]
fn tolerance_closeness_at_a_present_receiver_licenses_nothing() {
    let family = empirical_pattern_family();
    let transformation = family
        .admit_environment_change(
            "human",
            "mouse",
            "the two assays differ only in the declared target conformation",
            [CoordinateName::Conformation],
        )
        .expect("the environment passage is admitted");
    let situation = family
        .design_situation(std::slice::from_ref(&transformation), 1)
        .expect("the design situation declares");

    // Rung 6 at the dissociation-constant receiver at the human assay: |100 - 101| = 1, and two
    // per cent of 100 is 2, so the two binders are inside the declared tolerance.
    let tolerance = ToleranceReading::declare(
        "dissociation constant at the human assay",
        {
            let family = family.clone();
            move |situated: &SituatedDesign| {
                let design = family.designs()[situated.design].id;
                let label = family.environments()[situated.environment].label().to_owned();
                let ReceiverReading::Read(interval) = family
                    .design(design)
                    .expect("the design is in the family")
                    .reading("dissociationConstant", &label)
                    .expect("a stated axis")
                else {
                    unreachable!("every reading in this family is decided");
                };
                Ok(interval.lower.clone())
            }
        },
        rat(2),
    )
    .expect("a nonnegative tolerance");
    let binder_a = SituatedDesign {
        design: 0,
        environment: 0,
    };
    let binder_b = SituatedDesign {
        design: 1,
        environment: 0,
    };
    assert!(
        tolerance
            .holds(&binder_a, &binder_b)
            .expect("the reading runs"),
        "100 and 101 lie inside the declared tolerance of 2"
    );
    assert_eq!(
        tolerance.read(&binder_a).expect("a reading")
            - tolerance.read(&binder_b).expect("a reading"),
        rat(-1),
        "the difference is exact, not a rounded per cent"
    );

    // Rung 6 at that receiver does not even give rung 4 at the **same** receiver at the **same**
    // environment: 100 and 101 are inside the tolerance and are not equal. Tolerance is without
    // identification, which is `RelationLadder.toleranceIsWithoutIdentification`.
    let present = situation
        .present_agreement(&binder_a, &binder_b)
        .expect("the receivers read")
        .expect("the dissociation-constant receiver separates 100 from 101");
    assert_eq!(present.receiver_name, "dissociationConstant");
    assert_eq!(present.left_face, read(100));
    assert_eq!(present.right_face, read(101));

    // And the cross-species reading is a qualitative difference, not a tolerance question: the
    // mouse assay reads 100 against 1200.
    let at_mouse_a = SituatedDesign {
        design: 0,
        environment: 1,
    };
    let at_mouse_b = SituatedDesign {
        design: 1,
        environment: 1,
    };
    assert_eq!(
        situation.receivers()[0]
            .observe(&at_mouse_a)
            .expect("a reading"),
        read(100)
    );
    assert_eq!(
        situation.receivers()[0]
            .observe(&at_mouse_b)
            .expect("a reading"),
        read(1200)
    );
    let verdict = merge_verdict(&situation, &binder_a, &binder_b, &Declarations::default())
        .expect("the verdict runs");
    assert!(
        matches!(verdict, MergeVerdict::Refuted { .. }),
        "closeness inside a declared tolerance licenses no merge, got {verdict:?}"
    );
    assert!(!verdict.licenses_merge());
    assert!(merge(DesignId(1), DesignId(2), &verdict).is_err());

    // The plan's own shape, on the same family: design 5 agrees with design 1 at **every**
    // declared receiver at the human assay, and the mouse assay separates them. The refuting
    // separator is a future receiver and carries the environment-change word.
    let design_one = SituatedDesign {
        design: 0,
        environment: 0,
    };
    let design_five = SituatedDesign {
        design: 4,
        environment: 0,
    };
    assert!(
        situation
            .present_agreement(&design_one, &design_five)
            .expect("the receivers read")
            .is_none(),
        "every declared receiver returns the same face at the human assay"
    );
    let verdict = merge_verdict(&situation, &design_one, &design_five, &Declarations::default())
        .expect("the verdict runs");
    let MergeVerdict::Refuted { separator } = &verdict else {
        panic!("the mouse assay separates them, got {verdict:?}");
    };
    assert_eq!(separator.word_names, vec!["environment change 0 -> 1"]);
    assert_eq!(separator.receiver_name, "dissociationConstant");
    assert_eq!(separator.left_face, read(100));
    assert_eq!(separator.right_face, read(900));
    assert!(!verdict.licenses_merge());
}

#[test]
fn near_identical_interface_receivers_differ_sixfold_in_affinity() {
    let family = empirical_pattern_family();
    let transformation = family
        .admit_environment_change(
            "human",
            "mouse",
            "the two assays differ only in the declared target conformation",
            [CoordinateName::Conformation],
        )
        .expect("the environment passage is admitted");
    let situation = family
        .design_situation(std::slice::from_ref(&transformation), 1)
        .expect("the design situation declares");
    let design_c = SituatedDesign {
        design: 2,
        environment: 0,
    };
    let design_d = SituatedDesign {
        design: 3,
        environment: 0,
    };
    // The interface receiver reads them equal.
    assert_eq!(
        situation.receivers()[1]
            .observe(&design_c)
            .expect("a reading"),
        situation.receivers()[1]
            .observe(&design_d)
            .expect("a reading")
    );
    // The affinity receiver separates them six-fold, now, at the same environment.
    let separator = situation
        .present_agreement(&design_c, &design_d)
        .expect("the receivers read")
        .expect("the affinity receiver separates them");
    assert_eq!(separator.receiver_name, "dissociationConstant");
    assert_eq!(separator.left_face, read(50));
    assert_eq!(separator.right_face, read(300));
    assert_eq!(
        ratio(300, 50),
        rat(6),
        "six-fold, exactly, with no floating point anywhere"
    );
    let verdict = merge_verdict(&situation, &design_c, &design_d, &Declarations::default())
        .expect("the verdict runs");
    assert!(matches!(verdict, MergeVerdict::Refuted { .. }));
}

// ---------------------------------------------------------------------------------------------
// The whole cascade
// ---------------------------------------------------------------------------------------------

#[test]
fn the_cascade_runs_the_five_stages_and_reports_each_one() {
    let family = worked_family();
    let constraint = HardConstraint::declare(
        "the design is expressible in the declared host",
        "declared by the synthetic selection fixture",
        |design: &Design| design.id != DesignId(2),
    )
    .expect("a stated name and ground");
    let report = family
        .cascade(std::slice::from_ref(&constraint), "assayA", "affinity")
        .expect("the cascade runs");
    assert_eq!(report.admitted.admitted, vec![DesignId(1), DesignId(3)]);
    assert_eq!(report.admitted.refused.len(), 1);
    assert_eq!(report.frontier, vec![DesignId(3)]);
    assert_eq!(report.rankings.len(), 2);
    assert_eq!(report.clusters.components, vec![vec![DesignId(3)]]);
    assert_eq!(
        report.diversity.representatives,
        vec![(vec![DesignId(3)], vec![DesignId(3)])]
    );
    assert_eq!(
        report.population,
        [3_u32.into(), 2_u32.into(), 1_u32.into()]
    );
}

#[test]
fn a_situation_with_no_receiver_is_refused_by_the_ladder() {
    let family = worked_family();
    let situation = family.design_situation(&[], 0).expect("it declares");
    assert_eq!(situation.receivers().len(), 2);
    assert_eq!(situation.generators().len(), 0);
    assert_eq!(situation.history_ceiling(), 0);
    // Reachability is still a value, not a claim.
    let reached = situation
        .reaches(
            &SituatedDesign {
                design: 0,
                environment: 0,
            },
            &SituatedDesign {
                design: 1,
                environment: 0,
            },
        )
        .expect("reachability runs");
    assert!(matches!(
        reached,
        ContinuationVerdict::NotReachedWithinBound { .. }
    ));
}

#[test]
fn a_mutation_is_admitted_only_where_the_passage_owner_admits_it() {
    let family = worked_family();
    // Designs 1 and 2 differ at site 1 (ALA against GLY) and sit at the same environment, so the
    // horizontal passage owner admits it.
    let admitted = family
        .admit_mutation(DesignId(1), DesignId(2), "assayA", 1)
        .expect("the mutation passage is admitted");
    assert!(matches!(
        admitted,
        AdmittedTransformation::Mutation { site: 1, .. }
    ));
    // A site the sequences do not differ at is refused by that owner, and the generator with it.
    let refusal = family.admit_mutation(DesignId(1), DesignId(2), "assayA", 2);
    assert!(
        matches!(refusal, Err(SelectionRefusal::Passage(_))),
        "the generator is admitted only where the passage is, got {refusal:?}"
    );
    // The mutation generator carries design 1 to design 2 at that environment and fixes the rest.
    let situation = family
        .design_situation(std::slice::from_ref(&admitted), 1)
        .expect("the design situation declares");
    let moved = situation.generators()[0]
        .apply(&SituatedDesign {
            design: 0,
            environment: 0,
        })
        .expect("the generator is total");
    assert_eq!(
        moved,
        SituatedDesign {
            design: 1,
            environment: 0
        }
    );
    let fixed = situation.generators()[0]
        .apply(&SituatedDesign {
            design: 2,
            environment: 0,
        })
        .expect("the generator is total");
    assert_eq!(
        fixed,
        SituatedDesign {
            design: 2,
            environment: 0
        },
        "a mutation acts where its passage acts and is the identity elsewhere"
    );
}

#[test]
fn an_environment_change_generator_is_admitted_only_where_the_passage_is() {
    let family = worked_family();
    // Accounting for nothing leaves the divergent axes unaccounted, and the passage owner refuses.
    let refusal = family.admit_environment_change("assayA", "assayB", "no axis accounted", []);
    assert!(
        matches!(
            refusal,
            Err(SelectionRefusal::Environment(
                EnvironmentRefusal::CoordinatesUnaccounted { .. }
            ))
        ),
        "an unaccounted divergent axis refuses the transport, got {refusal:?}"
    );
    // An unstated ground is refused too.
    let refusal = family.admit_environment_change(
        "assayA",
        "assayB",
        "   ",
        [CoordinateName::Conformation],
    );
    assert!(matches!(
        refusal,
        Err(SelectionRefusal::Environment(
            EnvironmentRefusal::PassageGroundNotStated
        ))
    ));
}

// ---------------------------------------------------------------------------------------------
// Hostile input: declared sizes, forged receipts and bypassed constructors
// ---------------------------------------------------------------------------------------------

#[test]
fn an_unstated_reason_for_an_unread_axis_is_refused() {
    assert!(matches!(
        UnreadReason::declare("   "),
        Err(SelectionRefusal::NotStated { .. })
    ));
    assert!(matches!(
        ReceiverReading::unread(""),
        Err(SelectionRefusal::NotStated { .. })
    ));
    let stated = ReceiverReading::unread("the assay was not run").expect("a stated reason");
    let ReceiverReading::Unread(reason) = &stated else {
        panic!("an unread axis");
    };
    assert_eq!(reason.statement(), "the assay was not run");
    assert!(stated.value().is_none(), "an unread axis carries no value");
}

#[test]
fn a_design_with_more_faces_than_the_environment_ceiling_is_refused() {
    let classes = [ContactClass::Inside];
    let faces: Vec<(String, SituatedFamily)> = (0..=ENVIRONMENT_CEILING)
        .map(|at| {
            let env = environment(&format!("conformation{at}"));
            (
                format!("label{at}"),
                fixture::synthetic_family_named(at as u64, &env, &classes, &["ALA".to_owned()]),
            )
        })
        .collect();
    let refusal = Design::found(DesignId(1), "too many faces", faces, []);
    assert!(
        matches!(
            refusal,
            Err(SelectionRefusal::EnvironmentFamilyTooLarge { .. })
        ),
        "a design bounds its own face population, got {refusal:?}"
    );
}

#[test]
fn a_candidate_list_above_the_comparison_ceiling_is_refused_by_every_quadratic_stage() {
    let family = worked_family();
    // 16_385^2 * 2 exceeds COMPARISON_CEILING = 2^28, and the check runs before any allocation
    // sized by the list.
    let candidates: Vec<DesignId> = std::iter::repeat_n(DesignId(1), 16_385).collect();
    for refusal in [
        family.frontier(&candidates),
        family
            .rank_by_worst_environment(&candidates, "affinity")
            .map(|_| Vec::new()),
        family
            .structural_clusters(&candidates, "assayA")
            .map(|_| Vec::new()),
    ] {
        assert!(
            matches!(
                refusal,
                Err(SelectionRefusal::ComparisonPopulationTooLarge { .. })
            ),
            "a quadratic stage checks its declared candidate list first, got {refusal:?}"
        );
    }
    let weighting =
        ReceiverWeighting::declare([("affinity".to_owned(), rat(1))]).expect("nonnegative");
    let huge: Vec<DesignId> = std::iter::repeat_n(DesignId(1), (1usize << 28) + 1).collect();
    assert!(matches!(
        family.scalar_minimizers(&huge, &weighting),
        Err(SelectionRefusal::ComparisonPopulationTooLarge { .. })
    ));
}

#[test]
fn a_transformation_naming_an_index_the_family_does_not_carry_is_refused() {
    let family = worked_family();
    let forged = AdmittedTransformation::EnvironmentChange {
        from: 0,
        to: 99,
        ground: "forged".to_owned(),
    };
    assert!(matches!(
        family.design_situation(&[forged], 1),
        Err(SelectionRefusal::EnvironmentAbsent { .. })
    ));
    let forged = AdmittedTransformation::Mutation {
        from: 0,
        to: 99,
        environment: 0,
        site: 1,
    };
    assert!(matches!(
        family.design_situation(&[forged], 1),
        Err(SelectionRefusal::DesignAbsent { .. })
    ));
    let forged_site = AdmittedTransformation::Mutation {
        from: 0,
        to: 1,
        environment: 0,
        site: 99,
    };
    assert!(matches!(
        family.design_situation(&[forged_site], 1),
        Err(SelectionRefusal::Passage(_))
    ));
    let too_many: Vec<AdmittedTransformation> = std::iter::repeat_n(
        AdmittedTransformation::EnvironmentChange {
            from: 0,
            to: 1,
            ground: "forged".to_owned(),
        },
        TRANSFORMATION_CEILING + 1,
    )
    .collect();
    assert!(matches!(
        family.design_situation(&too_many, 1),
        Err(SelectionRefusal::TransformationFamilyTooLarge { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// The authenticated M5 release
// ---------------------------------------------------------------------------------------------

/// The three M5 RBX1 presentations are **one object at three environments**: the vertical index.
/// A design family over them is refused by name, which is the structural reason the mounted
/// release supplies no horizontal material for B8.
#[test]
fn the_three_m5_presentations_are_one_object_and_refuse_a_design_family() {
    let root = fixture::structure_root();
    assert!(
        root.is_dir(),
        "{}",
        fixture::absent_structure_root_message(
            &root,
            "The synthetic tests above check every law of this owner without it."
        )
    );
    let [designed, free, bound] = fixture::m5_situated_families();
    // They are one object.
    assert_eq!(designed.kinship(), free.kinship());
    assert_eq!(designed.kinship(), bound.kinship());
    VerticalFamily::over_one_object(vec![designed.clone(), free.clone(), bound.clone()])
        .expect("one object at three environments is the vertical index");

    // A design family therefore refuses them: they are one object read three times.
    let environments = vec![
        DeclaredEnvironment::declare("designed", designed.environment.clone())
            .expect("a stated label"),
    ];
    let one = Design::found(
        DesignId(1),
        "M5 designed structure",
        [("designed".to_owned(), designed.clone())],
        [(
            ("formedContacts".to_owned(), "designed".to_owned()),
            read(formed_contacts(&designed) as i64),
        )],
    )
    .expect("a design over one object founds");
    let two = Design::found(
        DesignId(2),
        "M5 free prediction",
        [("designed".to_owned(), {
            let mut face = free.clone();
            face.environment = designed.environment.clone();
            face
        })],
        [(
            ("formedContacts".to_owned(), "designed".to_owned()),
            read(formed_contacts(&free) as i64),
        )],
    )
    .expect("a design over one object founds");
    let refusal = DesignFamily::declare(
        vec![one, two],
        environments,
        vec![receiver("formedContacts", Sense::GreaterIsBetter)],
    );
    assert!(
        matches!(refusal, Err(SelectionRefusal::TwoDesignsAreOneObject { .. })),
        "the three M5 presentations are one object, so they are vertical material and not a \
         design population, got {refusal:?}"
    );
}

fn formed_contacts(family: &SituatedFamily) -> usize {
    family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Inside)
        .count()
}

fn open_contacts(family: &SituatedFamily) -> usize {
    family
        .readings
        .iter()
        .filter(|reading| reading.class == ContactClass::Open)
        .count()
}

/// The vertical use of the release: **one** design read at the three real environments, with the
/// worst-environment stage taken over exactly those three and the refusal path exercised on a
/// fourth, undeclared one.
#[test]
fn the_worst_environment_stage_on_the_three_m5_environments() {
    let root = fixture::structure_root();
    assert!(
        root.is_dir(),
        "{}",
        fixture::absent_structure_root_message(
            &root,
            "The synthetic worst-environment tests above check the law without it."
        )
    );
    let [designed, free, bound] = fixture::m5_situated_families();
    let environments = vec![
        DeclaredEnvironment::declare("designed", designed.environment.clone())
            .expect("a stated label"),
        DeclaredEnvironment::declare("free", free.environment.clone()).expect("a stated label"),
        DeclaredEnvironment::declare("cul1Bound", bound.environment.clone())
            .expect("a stated label"),
    ];
    let counts = [
        formed_contacts(&designed),
        formed_contacts(&free),
        formed_contacts(&bound),
    ];
    let opens = [
        open_contacts(&designed),
        open_contacts(&free),
        open_contacts(&bound),
    ];
    // The measured numbers of B4/B5: the designed presentation leaves exactly one pair open at the
    // 8 angstrom aperture and the two predictions leave none.
    assert_eq!(opens, [1, 0, 0], "the measured open readings of the release");
    assert_eq!(
        counts,
        [64, 59, 45],
        "the measured formed alpha-carbon contacts of the three presentations at 8 angstroms"
    );
    assert_eq!(
        designed.readings.len(),
        10_368,
        "the addressed alpha-carbon population of the release"
    );

    let design = Design::found(
        DesignId(1),
        "M5 RBX1 binder, one object at three environments",
        [
            ("designed".to_owned(), designed),
            ("free".to_owned(), free),
            ("cul1Bound".to_owned(), bound),
        ],
        [
            (
                ("formedContacts".to_owned(), "designed".to_owned()),
                read(counts[0] as i64),
            ),
            (
                ("formedContacts".to_owned(), "free".to_owned()),
                read(counts[1] as i64),
            ),
            (
                ("formedContacts".to_owned(), "cul1Bound".to_owned()),
                read(counts[2] as i64),
            ),
        ],
    )
    .expect("one object at three environments founds");
    let family = DesignFamily::declare(
        vec![design],
        environments,
        vec![receiver("formedContacts", Sense::GreaterIsBetter)],
    )
    .expect("the one-design family declares");

    let worst = family
        .worst_over(DesignId(1), "formedContacts")
        .expect("the worst runs");
    let smallest = counts.iter().copied().min().expect("three counts");
    let attained: Vec<String> = ["cul1Bound", "designed", "free"]
        .iter()
        .zip([counts[2], counts[0], counts[1]])
        .filter(|(_, count)| *count == smallest)
        .map(|(label, _)| (*label).to_owned())
        .collect();
    assert_eq!(
        worst,
        WorstVerdict::Worst {
            value: ExactInterval::point(rat(smallest as i64)),
            attained,
        },
        "a greater-is-better receiver's worst over the three declared environments is the \
         smallest reading, with every attaining environment returned (counts {counts:?})"
    );

    // The refusal path, on the same real material: an environment the receiver did not read.
    let unread = Design::found(
        DesignId(1),
        "M5 RBX1 binder, one environment unread",
        family.designs()[0]
            .labels()
            .iter()
            .map(|label| {
                (
                    (*label).to_owned(),
                    family.designs()[0]
                        .face(label)
                        .expect("a face")
                        .clone(),
                )
            })
            .collect::<Vec<_>>(),
        [
            (
                ("formedContacts".to_owned(), "designed".to_owned()),
                read(counts[0] as i64),
            ),
            (
                ("formedContacts".to_owned(), "free".to_owned()),
                ReceiverReading::unread(
                    "no formed-contact reading was taken at the free prediction",
                )
                .expect("a stated reason"),
            ),
            (
                ("formedContacts".to_owned(), "cul1Bound".to_owned()),
                read(counts[2] as i64),
            ),
        ],
    )
    .expect("one object at three environments founds");
    let with_unread = DesignFamily::declare(
        vec![unread],
        family.environments().to_vec(),
        family.receivers().to_vec(),
    )
    .expect("the family declares");
    assert_eq!(
        with_unread
            .worst_over(DesignId(1), "formedContacts")
            .expect("the worst runs"),
        WorstVerdict::UnreadAt {
            environment: "free".to_owned(),
            why: "no formed-contact reading was taken at the free prediction".to_owned(),
        },
        "a design unread at a declared environment is refused for ranking there, on real material"
    );
}

/// The horizontal material the release does not supply, built by **exact perturbation** of the
/// mounted designed structure's contact complex and labelled synthetic throughout.
#[test]
fn synthetic_designs_by_exact_perturbation_of_the_mounted_contact_complex() {
    let root = fixture::structure_root();
    assert!(
        root.is_dir(),
        "{}",
        fixture::absent_structure_root_message(
            &root,
            "The synthetic cascade tests above check every stage without it."
        )
    );
    let faces = fixture::m5_situated_families();
    let labels = ["designed", "free", "cul1Bound"];
    let environments: Vec<DeclaredEnvironment> = labels
        .iter()
        .zip(&faces)
        .map(|(label, face)| {
            DeclaredEnvironment::declare(*label, face.environment.clone())
                .expect("a stated label")
        })
        .collect();

    // Three synthetic designs: the mounted object, and two exact perturbations of it. Each
    // perturbation renames one monomer of the binder's sequence — which is what makes it a
    // different object, and exactly what `Passage::<Horizontal>::mutation` requires — and flips a
    // declared number of decided contact classes. Nothing here is a measurement.
    let perturb = |id: u64, monomer: &str, flips: usize| -> Design {
        let perturbed: Vec<(String, SituatedFamily)> = labels
            .iter()
            .zip(&faces)
            .map(|(label, face)| {
                let mut face = face.clone();
                face.lineage = format!("{} / SYNTHETIC exact perturbation {monomer}", face.lineage);
                face.occurrence = OccurrenceId(id * 1000 + u64::from(label.as_bytes()[0]));
                if let Some(first) = face.left_sequence.first_mut() {
                    *first = monomer.to_owned();
                }
                let mut flipped = 0_usize;
                for reading in &mut face.readings {
                    if flipped == flips {
                        break;
                    }
                    if reading.class == ContactClass::Outside {
                        reading.class = ContactClass::Inside;
                        flipped += 1;
                    }
                }
                ((*label).to_owned(), face)
            })
            .collect();
        let readings: Vec<((String, String), ReceiverReading)> = perturbed
            .iter()
            .map(|(label, face)| {
                (
                    ("formedContacts".to_owned(), label.clone()),
                    read(formed_contacts(face) as i64),
                )
            })
            .collect();
        Design::found(
            DesignId(id),
            format!("SYNTHETIC perturbation of the mounted M5 designed structure ({monomer})"),
            perturbed,
            readings,
        )
        .expect("one object at three environments founds")
    };

    let baseline_monomer = faces[0]
        .left_sequence
        .first()
        .cloned()
        .expect("the binder presents a sequence");
    assert_ne!(baseline_monomer, "SYN1");
    let family = DesignFamily::declare(
        vec![perturb(1, "SYN1", 0), perturb(2, "SYN2", 3), perturb(3, "SYN3", 7)],
        environments,
        vec![receiver("formedContacts", Sense::GreaterIsBetter)],
    )
    .expect("three synthetic designs at the three real environments declare");

    // Horizontal: at each real environment the three designs are a horizontal family, and each
    // design's three faces are a vertical family. That is the rectangle.
    for label in labels {
        HorizontalFamily::at_one_environment(
            family
                .designs()
                .iter()
                .map(|design| design.face(label).expect("a face").clone())
                .collect(),
        )
        .expect("three objects at one real environment is a horizontal family");
    }

    let all = vec![DesignId(1), DesignId(2), DesignId(3)];
    let frontier = family.frontier(&all).expect("the frontier runs");
    assert_eq!(
        frontier,
        vec![DesignId(3)],
        "the most-perturbed design carries strictly more formed contacts at every declared \
         environment, so it dominates"
    );

    // The exact separator structure over the real addressed contacts.
    let separator = family
        .separator_between(DesignId(1), DesignId(3), "designed")
        .expect("the separator runs");
    assert_eq!(
        separator.separating.len(),
        7,
        "exactly the seven contacts the perturbation flipped separate the two designs"
    );
    assert_eq!(
        separator.open_carrying.len(),
        1,
        "the release's single open reading at the designed presentation is carried, never counted"
    );
    let clusters = family
        .structural_clusters(&all, "designed")
        .expect("clustering runs");
    assert_eq!(
        clusters.components,
        vec![vec![DesignId(1)], vec![DesignId(2)], vec![DesignId(3)]],
        "three separated designs are three components"
    );

    // And the mutation passage admits the horizontal move between two of them.
    let admitted = family
        .admit_mutation(DesignId(1), DesignId(2), "designed", 1)
        .expect("the mutation passage is admitted");
    assert!(matches!(
        admitted,
        AdmittedTransformation::Mutation { site: 1, .. }
    ));
}

// ---------------------------------------------------------------------------------------------
// B10 — the cost cascade, read for what it costs
// ---------------------------------------------------------------------------------------------

/// A per-candidate cost meter that charges a declared number of decode steps.
fn meter(presentation: &'static str, steps: u64) -> DesignCost {
    std::sync::Arc::new(move |design: &Design| CostReceipt {
        presentation: format!("{presentation} at design {:?}", design.id),
        bytes: Counted::derived(0_u32, "this stage occupies no presentation of its own"),
        decode_work: Counted::measured(steps, "the declared per-candidate step count of this stage"),
        update_work: Counted::derived(0_u32, "this stage re-presents nothing"),
        certificate_work: Counted::derived(steps, "one comparison per step"),
        residual: Counted::derived(0_u32, "this stage drops nothing"),
    })
}

/// The cheap coarse test: admit a design whose worst `interface` reading is at least `40`.
fn cheap_at_least(bound: i64) -> DesignTest {
    std::sync::Arc::new(move |design: &Design| {
        design
            .reading("interface", "assayA")
            .and_then(ReceiverReading::value)
            .is_some_and(|value| value.lower >= rat(bound))
    })
}

/// The worked cascade family: three designs whose `interface` readings are 39, 40 and 41.
fn cascade_family() -> DesignFamily {
    let environments = two_environments();
    let (a, b) = (
        environments[0].environment().clone(),
        environments[1].environment().clone(),
    );
    let classes = [ContactClass::Inside, ContactClass::Outside];
    let design = |id: u64, monomer: &str, value: i64| {
        synthetic_design(
            id,
            monomer,
            &[("assayA", &a, &classes), ("assayB", &b, &classes)],
            &[
                ("affinity", "assayA", read(10)),
                ("affinity", "assayB", read(10)),
                ("interface", "assayA", read(value)),
                ("interface", "assayB", read(value)),
            ],
        )
    };
    DesignFamily::declare(
        vec![
            design(1, "ALA", 39),
            design(2, "GLY", 40),
            design(3, "SER", 41),
        ],
        environments,
        vec![
            receiver("affinity", Sense::SmallerIsBetter),
            receiver("interface", Sense::GreaterIsBetter),
        ],
    )
    .expect("three distinct objects found a family")
}

/// **Lean: `certified_cascade_preserves_the_frontier`.** With every discarding stage certified, the
/// cascade keeps exactly what the full evaluation keeps.
#[test]
fn a_certified_cascade_keeps_exactly_what_the_full_evaluation_keeps() {
    let family = cascade_family();
    let all: Vec<DesignId> = family.designs().iter().map(|design| design.id).collect();
    let probe: Vec<Design> = family.designs().to_vec();
    // The cheap reading refuses at 40 and the expensive one at 41: the cheap reading therefore
    // refuses only where the expensive one does, which is the certificate.
    let stage = CascadeStage::certified_bound(
        "coarse interface filter",
        "the synthetic cascade fixture",
        "the cheap reading's admission threshold is below the expensive receiver's, so a cheap \
         refusal certifies an expensive refusal",
        StageReadings {
            cheap: cheap_at_least(40),
            expensive: cheap_at_least(41),
            cheap_cost: meter("cheap coarse filter", 1),
            expensive_cost: meter("expensive interface receiver", 100),
        },
        &probe,
    )
    .expect("the certificate holds at every probe candidate");
    assert!(matches!(stage.law(), DiscardLaw::CertifiedBound(_)));
    let DiscardLaw::CertifiedBound(certificate) = stage.law() else {
        unreachable!()
    };
    assert_eq!(certificate.probe(), 3, "the certificate names where it was checked");

    let cascade = CostedCascade::declare(vec![stage]).expect("one stage founds a cascade");
    let cascaded = cascade.run(&family, &all).expect("the cascade runs");
    let full = cascade
        .full_evaluation(&family, &all)
        .expect("the full evaluation runs");
    assert!(
        survivors_agree(&cascaded, &full),
        "a certified cheap filter changes what is computed and never what is kept"
    );
    assert_eq!(cascaded.survivors, vec![DesignId(3)]);

    // And it saves: the expensive receiver ran on one candidate instead of three.
    let saving = cost_saving(&cascaded, &full);
    let decode = saving
        .iter()
        .find(|axis| axis.axis == Axis::DecodeWork)
        .expect("the decode axis");
    assert_eq!(
        decode.direction,
        CostDirection::Saved,
        "the cascade cost strictly less decode work: {decode:?}"
    );
    assert_eq!(
        decode.full,
        num_bigint::BigUint::from(300_u32),
        "the full evaluation ran the 100-step receiver on all three designs"
    );
    assert_eq!(
        decode.cascade,
        num_bigint::BigUint::from(203_u32),
        "the cascade ran the 1-step filter on all three and the 100-step receiver on the two the \
         filter admitted, where the full evaluation ran the 100-step receiver on all three"
    );
}

/// **Lean: `proxyStage_is_not_certified` and `uncertified_proxy_loses_a_frontier_design`.** An
/// uncertified proxy discards nothing under the cascade's law; admitting its discard loses a design
/// the full evaluation keeps.
#[test]
fn an_uncertified_proxy_discards_nothing_and_loses_a_design_when_it_is_let_to() {
    let family = cascade_family();
    let all: Vec<DesignId> = family.designs().iter().map(|design| design.id).collect();
    // A cheap scalar proxy that refuses below 41 while the expensive receiver admits from 40: the
    // cheap reading refuses where the expensive one admits, so it is no bound at all.
    let stage = CascadeStage::uncertified_proxy(
        "a cheap scalar proxy for the interface receiver",
        "the synthetic cascade fixture, with no certificate",
        StageReadings {
            cheap: cheap_at_least(41),
            expensive: cheap_at_least(40),
            cheap_cost: meter("cheap scalar proxy", 1),
            expensive_cost: meter("expensive interface receiver", 100),
        },
    )
    .expect("a stated proxy");
    assert!(matches!(stage.law(), DiscardLaw::UncertifiedProxy { .. }));
    assert!(!stage.law().licenses_a_discard());

    let cascade = CostedCascade::declare(vec![stage]).expect("a cascade");
    let cascaded = cascade.run(&family, &all).expect("the cascade runs");
    let full = cascade
        .full_evaluation(&family, &all)
        .expect("the full evaluation runs");
    assert!(
        survivors_agree(&cascaded, &full),
        "the law does not let an uncertified proxy discard, so nothing is lost"
    );
    assert_eq!(
        cascaded.stages[0].would_have_discarded,
        vec![DesignId(1), DesignId(2)],
        "every discard it would have made is recorded rather than taken"
    );

    let admitted = cascade
        .run_admitting_every_proxy_discard(&family, &all)
        .expect("the exhibition runs");
    assert!(
        !survivors_agree(&admitted, &full),
        "letting the uncertified proxy discard loses a design the full evaluation keeps"
    );
    assert_eq!(admitted.survivors, vec![DesignId(3)]);
    assert_eq!(full.survivors, vec![DesignId(2), DesignId(3)]);
}

/// A certificate refuted at a probe candidate is never minted: [`Certified`] has no other
/// constructor, so the stage cannot exist.
#[test]
fn a_certificate_refuted_at_a_probe_candidate_is_not_minted() {
    let family = cascade_family();
    let probe: Vec<Design> = family.designs().to_vec();
    let refusal = CascadeStage::certified_bound(
        "a proxy claiming to be a bound",
        "the synthetic cascade fixture",
        "a law the data refutes",
        StageReadings {
            cheap: cheap_at_least(41),
            expensive: cheap_at_least(40),
            cheap_cost: meter("cheap", 1),
            expensive_cost: meter("expensive", 100),
        },
        &probe,
    )
    .expect_err("the cheap reading refuses design 2, which the expensive receiver admits");
    assert!(matches!(
        refusal,
        SelectionRefusal::CertificateRefuted {
            design: DesignId(2),
            ..
        }
    ));
}

/// A hard-constraint stage is certified by construction, runs once and is charged once.
#[test]
fn a_hard_constraint_stage_is_certified_and_charged_once() {
    let family = cascade_family();
    let all: Vec<DesignId> = family.designs().iter().map(|design| design.id).collect();
    let constraint = HardConstraint::declare(
        "the interface receiver reads at least 40",
        "the synthetic cascade fixture",
        |design: &Design| {
            design
                .reading("interface", "assayA")
                .and_then(ReceiverReading::value)
                .is_some_and(|value| value.lower >= rat(40))
        },
    )
    .expect("a stated constraint");
    let stage = CascadeStage::hard_constraint(constraint, meter("hard constraint", 2));
    assert!(matches!(stage.law(), DiscardLaw::HardConstraint { .. }));
    assert!(stage.law().licenses_a_discard());
    assert!(stage.cheap_is_expensive());

    let cascade = CostedCascade::declare(vec![stage]).expect("a cascade");
    let run = cascade.run(&family, &all).expect("the cascade runs");
    assert_eq!(run.survivors, vec![DesignId(2), DesignId(3)]);
    assert_eq!(
        run.total.count(Axis::DecodeWork),
        &num_bigint::BigUint::from(6_u32),
        "two steps for each of the three candidates, charged once and not twice"
    );
    assert_eq!(run.stages[0].discarded.len(), 1);
    assert_eq!(run.stages[0].discarded[0].law, "hard-constraint");
}

/// A cascade with a repeated stage name is refused: a discard must be able to name the stage that
/// made it.
#[test]
fn a_repeated_cascade_stage_name_is_refused() {
    let stage = |name: &'static str| {
        CascadeStage::uncertified_proxy(
            name,
            "a ground",
            StageReadings {
                cheap: cheap_at_least(0),
                expensive: cheap_at_least(0),
                cheap_cost: meter("cheap", 1),
                expensive_cost: meter("expensive", 1),
            },
        )
        .expect("a stated proxy")
    };
    assert!(matches!(
        CostedCascade::declare(vec![stage("one"), stage("one")]),
        Err(SelectionRefusal::CascadeStageNameRepeated { .. })
    ));
    assert!(matches!(
        CostedCascade::declare(Vec::new()),
        Err(SelectionRefusal::EmptyFamily)
    ));
}

/// **One cascade, two readings.** The decision reading of `DesignFamily::cascade` and the cost
/// reading of `CostedCascade::run` agree on who survives the hard-constraint stage.
#[test]
fn the_decision_reading_and_the_cost_reading_are_one_cascade() {
    let family = cascade_family();
    let all: Vec<DesignId> = family.designs().iter().map(|design| design.id).collect();
    let admits = |design: &Design| {
        design
            .reading("interface", "assayA")
            .and_then(ReceiverReading::value)
            .is_some_and(|value| value.lower >= rat(40))
    };
    let decision = family.admit(&[HardConstraint::declare(
        "the interface receiver reads at least 40",
        "the synthetic cascade fixture",
        admits,
    )
    .expect("a stated constraint")]);
    let cost = CostedCascade::declare(vec![CascadeStage::hard_constraint(
        HardConstraint::declare(
            "the interface receiver reads at least 40",
            "the synthetic cascade fixture",
            admits,
        )
        .expect("a stated constraint"),
        meter("hard constraint", 2),
    )])
    .expect("a cascade")
    .run(&family, &all)
    .expect("the cascade runs");
    assert_eq!(
        decision.admitted, cost.survivors,
        "the same stage decides the same survivors; the second reading only says what it cost"
    );
}

/// **A bound checked at no design is not a checked bound.** An empty probe passed the certificate
/// loop vacuously and minted a certificate for a cheap test that discards everything the expensive
/// receiver admits. It is now refused by name, and the same readings over a nonempty probe are
/// refuted by the first design.
#[test]
fn a_certified_bound_over_an_empty_probe_is_refused() {
    let readings = || StageReadings {
        cheap: std::sync::Arc::new(|_: &Design| false),
        expensive: std::sync::Arc::new(|_: &Design| true),
        cheap_cost: std::sync::Arc::new(|_: &Design| empty_receipt("cheap")),
        expensive_cost: std::sync::Arc::new(|_: &Design| empty_receipt("expensive")),
    };
    assert!(matches!(
        CascadeStage::certified_bound("bogus", "a ground", "a claimed law", readings(), &[]),
        Err(SelectionRefusal::EmptyCertificateProbe { .. })
    ));
}
