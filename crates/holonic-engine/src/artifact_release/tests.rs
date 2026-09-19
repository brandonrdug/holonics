//! Tests for **T3 — release over an edited artifact family**.
//!
//! [definition] Every Lean theorem of
//! `formal/elementary-holonics/ElementaryHolonics/Transport/ArtifactRelease.lean` appears here as
//! an executable check over the same six-slot role frame. The frame is an **illustration of the
//! law**: six declared positions, a handful of exact integer token codes and two decidable
//! role-agreement rules. It is not a model of English, of grammar or of meaning, and no statistic,
//! corpus or learned parameter appears anywhere in this file.

use std::collections::BTreeSet;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;

use super::*;
use crate::continuing_tower::check_restriction_laws;
use crate::receiver_release::Horizon as ReleaseHorizon;

// -------------------------------------------------------------------------------------------
// The six-slot role frame
// -------------------------------------------------------------------------------------------

const PRONOUN: usize = 0;
const VERB: usize = 1;
const DETERMINER: usize = 2;
const NOUN: usize = 3;
const NAME: usize = 4;
const FRAME: usize = 5;
const SLOTS: usize = 6;

const IT: Token = 10;
const HE: Token = 11;
const HAS: Token = 20;
const A_TOKEN: Token = 30;
const DOG: Token = 40;
const CAT: Token = 41;
const UNNAMED: Token = 50;
const HERMES: Token = 51;
const IS: Token = 60;
const WHY: Token = 61;

fn draft(noun: Token) -> Artifact {
    Artifact::declared(vec![IT, HAS, A_TOKEN, noun, UNNAMED, IS]).expect("a six-slot draft")
}

fn male_draft() -> Artifact {
    Artifact::declared(vec![HE, HAS, A_TOKEN, DOG, UNNAMED, IS]).expect("a six-slot draft")
}

fn named_draft() -> Artifact {
    Artifact::declared(vec![IT, HAS, A_TOKEN, DOG, HERMES, IS]).expect("a six-slot draft")
}

fn family_zero() -> ArtifactFamily {
    ArtifactFamily::Enumerated(
        EnumeratedFamily::declared("role-frame", vec![draft(DOG), draft(CAT)])
            .expect("a two-member family"),
    )
}

fn singleton(artifact: Artifact) -> ArtifactFamily {
    ArtifactFamily::Enumerated(
        EnumeratedFamily::declared("role-frame", vec![artifact]).expect("a one-member family"),
    )
}

/// The declared receiver conditions: a masculine proper name forces the masculine pronoun, and the
/// frame slot must carry a token of copula role.
fn admitted() -> Constraint {
    Constraint::declared(
        "role-agreement",
        vec![
            ConstraintRule::RoleAgreement {
                position: NAME,
                trigger: HERMES,
                dependent: PRONOUN,
                required: HE,
            },
            ConstraintRule::Positionwise {
                position: FRAME,
                admitted: BTreeSet::from([IS]),
            },
        ],
    )
    .expect("a declared constraint")
}

fn region(positions: impl IntoIterator<Item = usize>) -> Region {
    Region::declared(SLOTS, positions).expect("a declared region")
}

fn pronoun_region() -> Region {
    region([PRONOUN])
}

fn name_region() -> Region {
    region([NAME])
}

fn noun_edit() -> Edit {
    Edit::declared(
        "dog->cat",
        EditAction::Substitute {
            position: NOUN,
            from: DOG,
            to: CAT,
        },
    )
    .expect("a declared edit")
}

fn name_edit() -> Edit {
    Edit::declared(
        "name->Hermes",
        EditAction::Set {
            position: NAME,
            token: HERMES,
        },
    )
    .expect("a declared edit")
}

fn pronoun_edit() -> Edit {
    Edit::declared(
        "it->he",
        EditAction::Set {
            position: PRONOUN,
            token: HE,
        },
    )
    .expect("a declared edit")
}

fn frame_edit() -> Edit {
    Edit::declared(
        "is->why",
        EditAction::Substitute {
            position: FRAME,
            from: IS,
            to: WHY,
        },
    )
    .expect("a declared edit")
}

/// The entangled edit: the pronoun is rewritten *from* the name slot. It reads a position it does
/// not write, so it is not chartwise.
fn agreement_edit() -> Edit {
    Edit::declared(
        "agree-pronoun",
        EditAction::Conditioned {
            source: NAME,
            trigger: HERMES,
            target: PRONOUN,
            token: HE,
        },
    )
    .expect("a declared edit")
}

fn swing_of(edit: Edit) -> Swing {
    Swing::single(edit).expect("a single-branch swing")
}

// -------------------------------------------------------------------------------------------
// The artifact, the region and the region tower
// -------------------------------------------------------------------------------------------

#[test]
fn an_artifact_of_zero_positions_is_refused() {
    assert_eq!(
        Artifact::declared(Vec::new()).unwrap_err(),
        ArtifactRefusal::EmptyArtifact
    );
}

#[test]
fn an_artifact_above_the_position_ceiling_is_refused_before_it_is_carried() {
    let refusal = Artifact::declared(vec![0; POSITION_CEILING + 1]).unwrap_err();
    assert!(matches!(
        refusal,
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: POSITION_CEILING,
            ..
        }
    ));
}

#[test]
fn a_region_position_outside_the_artifact_is_refused() {
    assert_eq!(
        Region::declared(SLOTS, [SLOTS]).unwrap_err(),
        ArtifactRefusal::PositionOutsideArtifact {
            position: SLOTS,
            length: SLOTS,
        }
    );
}

#[test]
fn the_region_reads_exactly_the_positions_it_declares() {
    let face = pronoun_region().read(&draft(DOG)).expect("a face");
    assert_eq!(face.values().len(), 1);
    assert_eq!(face.values().get(&PRONOUN), Some(&IT));
}

#[test]
fn a_region_of_another_length_is_refused_a_reading() {
    let short = Artifact::declared(vec![IT, HAS]).expect("a two-slot artifact");
    assert_eq!(
        pronoun_region().read(&short).unwrap_err(),
        ArtifactRefusal::LengthMismatch {
            declared: SLOTS,
            found: 2,
        }
    );
}

#[test]
fn the_region_tower_satisfies_the_restriction_laws() {
    let tower = RegionTower::declared(SLOTS).expect("a region tower");
    let charts = vec![
        region([PRONOUN]),
        region([PRONOUN, NAME]),
        region(0..SLOTS),
    ];
    let faces: Vec<(Region, RegionFace)> = charts
        .iter()
        .map(|chart| {
            (
                chart.clone(),
                chart.read(&draft(DOG)).expect("a declared face"),
            )
        })
        .collect();
    let receipt = check_restriction_laws(&tower, &charts, &faces).expect("the laws hold");
    assert_eq!(receipt.faces_checked, 3);
}

#[test]
fn restricting_to_a_region_that_does_not_refine_is_refused() {
    let tower = RegionTower::declared(SLOTS).expect("a region tower");
    let coarse = region([NAME]);
    let fine = region([PRONOUN]);
    let face = fine.read(&draft(DOG)).expect("a face");
    assert!(tower.restrict(&coarse, &fine, &face).is_err());
}

// -------------------------------------------------------------------------------------------
// The family, enumerated and enclosed
// -------------------------------------------------------------------------------------------

#[test]
fn an_empty_family_is_refused() {
    assert_eq!(
        EnumeratedFamily::declared("empty", Vec::new()).unwrap_err(),
        ArtifactRefusal::EmptyFamily
    );
}

#[test]
fn a_family_above_the_ceiling_is_refused_before_any_member_is_read() {
    let members = vec![draft(DOG); FAMILY_CEILING + 1];
    let refusal = EnumeratedFamily::declared("too-wide", members).unwrap_err();
    assert!(matches!(
        refusal,
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: FAMILY_CEILING,
            ..
        }
    ));
}

#[test]
fn members_of_different_lengths_are_refused() {
    let short = Artifact::declared(vec![IT, HAS]).expect("a two-slot artifact");
    assert_eq!(
        EnumeratedFamily::declared("mixed", vec![draft(DOG), short]).unwrap_err(),
        ArtifactRefusal::LengthMismatch {
            declared: SLOTS,
            found: 2,
        }
    );
}

#[test]
fn the_family_is_a_set_and_deduplicates_its_members() {
    let family = EnumeratedFamily::declared("repeated", vec![draft(DOG), draft(DOG), draft(CAT)])
        .expect("a family");
    assert_eq!(family.len(), 2);
}

#[test]
fn the_enclosure_cardinality_is_exact_and_nothing_is_enumerated() {
    let alphabet: BTreeSet<Token> = (0..1000).collect();
    let enclosed = EnclosedFamily::declared("enclosure", vec![alphabet; 6])
        .expect("a declared enclosure");
    assert_eq!(
        enclosed.cardinality(),
        BigUint::from(1000u32).pow(6),
        "the cardinality is the exact product of the per-position alphabets"
    );
}

#[test]
fn the_enclosure_releases_exactly_the_regions_of_singletons() {
    let admitted = vec![
        BTreeSet::from([IT]),
        BTreeSet::from([HAS]),
        BTreeSet::from([A_TOKEN]),
        BTreeSet::from([DOG, CAT]),
        BTreeSet::from([UNNAMED]),
        BTreeSet::from([IS]),
    ];
    let enclosed = EnclosedFamily::declared("enclosure", admitted).expect("a declared enclosure");
    assert!(
        enclosed
            .region_released(&pronoun_region())
            .expect("a reading")
    );
    assert!(
        !enclosed
            .region_released(&region([NOUN]))
            .expect("a reading")
    );
}

#[test]
fn a_role_agreement_constraint_is_refused_on_an_enclosure_rather_than_approximated() {
    let enclosed = EnclosedFamily::declared(
        "enclosure",
        vec![BTreeSet::from([IT, HE]); SLOTS],
    )
    .expect("a declared enclosure");
    let refusal = enclosed.restricted(&admitted()).unwrap_err();
    assert!(matches!(
        refusal,
        ArtifactRefusal::ConstraintNotPositionwiseOnEnclosure { .. }
    ));
}

#[test]
fn restricting_an_enclosure_to_nothing_is_refused_by_position() {
    let enclosed = EnclosedFamily::declared("enclosure", vec![BTreeSet::from([IT]); SLOTS])
        .expect("a declared enclosure");
    let constraint = Constraint::declared(
        "impossible",
        vec![ConstraintRule::Positionwise {
            position: PRONOUN,
            admitted: BTreeSet::from([HE]),
        }],
    )
    .expect("a declared constraint");
    assert_eq!(
        enclosed.restricted(&constraint).unwrap_err(),
        ArtifactRefusal::EnclosureEmptied { position: PRONOUN }
    );
}

#[test]
fn an_enclosure_position_with_no_admitted_token_is_refused() {
    let admitted = vec![BTreeSet::new(); SLOTS];
    assert_eq!(
        EnclosedFamily::declared("enclosure", admitted).unwrap_err(),
        ArtifactRefusal::EmptyEnclosurePosition { position: 0 }
    );
}

// -------------------------------------------------------------------------------------------
// Release is the width owner's width
// -------------------------------------------------------------------------------------------

#[test]
fn the_pronoun_is_released_in_the_initial_family() {
    assert!(
        family_zero()
            .region_released(&pronoun_region())
            .expect("a reading")
    );
}

#[test]
fn the_region_width_is_the_release_owners_exact_diameter() {
    let width = family_zero()
        .region_width(&region([NOUN]), "noun")
        .expect("a width");
    assert_eq!(
        width.diameter(),
        &Rat::from_integer(BigInt::one()),
        "the noun region reads 40 and 41, so its exact sup-norm diameter is 1"
    );
    assert!(!width.is_zero());
}

#[test]
fn an_enclosure_is_refused_a_region_width_rather_than_materialized() {
    let enclosed = ArtifactFamily::Enclosed(
        EnclosedFamily::declared("enclosure", vec![BTreeSet::from([IT]); SLOTS])
            .expect("a declared enclosure"),
    );
    assert!(matches!(
        enclosed.region_width(&pronoun_region(), "pronoun").unwrap_err(),
        ArtifactRefusal::EnclosureHasNoEnumeratedMembers { .. }
    ));
}

// -------------------------------------------------------------------------------------------
// T5's two-axis horizon, adopted where release over the family needs the transverse axis
// -------------------------------------------------------------------------------------------

#[test]
fn the_region_ladder_is_the_transverse_index_of_the_two_axis_horizon() {
    let family = family_zero();
    assert_eq!(
        family
            .index_distance(&region(0..SLOTS))
            .expect("a distance"),
        0,
        "the whole-artifact chart is at index zero"
    );
    assert_eq!(
        family.index_distance(&pronoun_region()).expect("a distance"),
        SLOTS - 1
    );
    let horizon = family
        .horizon_of(&pronoun_region(), 2)
        .expect("a two-axis horizon");
    assert_eq!(horizon.longitudinal(), 2);
    assert_eq!(horizon.index(), SLOTS - 1);
    assert!(!horizon.is_longitudinal_only());
}

#[test]
fn the_two_axis_width_agrees_with_the_one_axis_width_at_the_regions_own_index() {
    let family = family_zero();
    for target in [pronoun_region(), region([NOUN]), region(0..SLOTS)] {
        let horizon = family.horizon_of(&target, 0).expect("a horizon");
        let two_axis = family
            .region_width_at(&target, "receiver", &horizon)
            .expect("a two-axis width");
        let one_axis = family
            .region_width(&target, "receiver")
            .expect("a one-axis width");
        assert_eq!(two_axis.diameter(), one_axis.diameter());
    }
}

#[test]
fn a_horizon_whose_index_is_not_the_regions_distance_is_refused() {
    let family = family_zero();
    let horizon = ReleaseHorizon::declare(0, 0).expect("a declared horizon");
    let refusal = family
        .region_width_at(&pronoun_region(), "pronoun", &horizon)
        .unwrap_err();
    assert_eq!(
        refusal,
        ArtifactRefusal::HorizonIndexMismatch {
            region: vec![PRONOUN],
            declared: 0,
            actual: SLOTS - 1,
        }
    );
}

#[test]
fn the_two_horizon_coordinates_are_not_one_scale() {
    // `(2, 0)` and `(0, 2)` are incomparable: "how far into the horizon" is a pair, and a region
    // read two steps down the ladder is not further or nearer than a family read two edits along.
    let longitudinal = ReleaseHorizon::declare(2, 0).expect("a declared horizon");
    let transverse = ReleaseHorizon::declare(0, 2).expect("a declared horizon");
    assert!(!longitudinal.comparable(&transverse));
    assert!(longitudinal.contains(&ReleaseHorizon::declare(1, 0).expect("a declared horizon")));
}

// -------------------------------------------------------------------------------------------
// The step `F_{k+1} = T_g(F_k) ∩ C_k`
// -------------------------------------------------------------------------------------------

#[test]
fn the_noun_edit_keeps_the_family_and_the_released_pronoun() {
    let outcome = step(&family_zero(), &swing_of(noun_edit()), &admitted()).expect("a step");
    let family = outcome.family().expect("the family continues");
    assert!(family.region_released(&pronoun_region()).expect("a reading"));
}

#[test]
fn release_is_preserved_by_an_edit_supported_off_the_region() {
    let swing = swing_of(noun_edit());
    assert!(swing.is_supported_off(&pronoun_region()));
    let before = family_zero();
    let outcome = step(&before, &swing, &admitted()).expect("a step");
    let preservation =
        release_after_step(&before, &pronoun_region(), &outcome, "pronoun").expect("a reading");
    match preservation {
        ReleasePreservation::Stands { face } => {
            assert_eq!(face.values().get(&PRONOUN), Some(&IT));
        }
        other => panic!("an edit supported off the region must leave the face standing: {other:?}"),
    }
}

#[test]
fn release_is_preserved_by_a_many_branch_swing_supported_off_the_region() {
    let swing = Swing::declared(
        "noun-swing",
        vec![
            noun_edit(),
            Edit::declared("noun->dog", EditAction::Set { position: NOUN, token: DOG })
                .expect("a declared edit"),
            Edit::declared("noun->42", EditAction::Set { position: NOUN, token: 42 })
                .expect("a declared edit"),
        ],
    )
    .expect("a three-branch swing");
    assert!(swing.is_supported_off(&pronoun_region()));
    let before = family_zero();
    let outcome = step(&before, &swing, &admitted()).expect("a step");
    let after = outcome.family().expect("the family continues");
    assert!(after.cardinality() > before.cardinality());
    assert!(after.region_released(&pronoun_region()).expect("a reading"));
    assert!(matches!(
        release_after_step(&before, &pronoun_region(), &outcome, "pronoun").expect("a reading"),
        ReleasePreservation::Stands { .. }
    ));
}

#[test]
fn an_edit_off_the_region_cannot_change_its_released_face() {
    let before = family_zero();
    let before_face = pronoun_region()
        .read(&before.members().expect("enumerated")[0])
        .expect("a face");
    for edit in [noun_edit(), name_edit(), frame_edit()] {
        let swing = swing_of(edit);
        assert!(swing.is_supported_off(&pronoun_region()));
        let outcome = step(&before, &swing, &Constraint::unconstrained("none")).expect("a step");
        let family = outcome.family().expect("with no constraint nothing is emptied");
        for member in family.members().expect("enumerated") {
            assert_eq!(
                pronoun_region().read(member).expect("a face"),
                before_face,
                "an edit supported off the pronoun cannot change its face"
            );
        }
    }
}

#[test]
fn reopening_a_released_region_from_outside_is_an_emptying() {
    let before = family_zero();
    let swing = swing_of(name_edit());
    assert!(swing.is_supported_off(&pronoun_region()));
    let outcome = step(&before, &swing, &admitted()).expect("a step");
    match &outcome {
        StepOutcome::Emptied {
            swing,
            constraint,
            refused,
        } => {
            assert_eq!(swing, "name->Hermes");
            assert_eq!(constraint, "role-agreement");
            assert_eq!(*refused, 2);
        }
        other => panic!("the name pivot must empty the family: {other:?}"),
    }
    assert!(matches!(
        release_after_step(&before, &pronoun_region(), &outcome, "pronoun").expect("a reading"),
        ReleasePreservation::RefutedByEmptying { .. }
    ));
}

#[test]
fn the_frame_edit_empties_the_family_under_the_role_constraint() {
    let outcome = step(&family_zero(), &swing_of(frame_edit()), &admitted()).expect("a step");
    assert!(matches!(outcome, StepOutcome::Emptied { .. }));
}

#[test]
fn the_correction_restores_the_family_and_releases_the_new_face() {
    let corrected = step(&family_zero(), &swing_of(pronoun_edit()), &admitted()).expect("a step");
    let corrected = corrected.family().expect("the correction is admitted");
    let named = step(corrected, &swing_of(name_edit()), &admitted()).expect("a step");
    let named = named.family().expect("the name pivot is now admitted");
    assert!(named.region_released(&pronoun_region()).expect("a reading"));
    assert_eq!(
        pronoun_region()
            .read(&named.members().expect("enumerated")[0])
            .expect("a face")
            .values()
            .get(&PRONOUN),
        Some(&HE),
        "the released face is the corrected one, reached by an edit supported ON the region"
    );
}

#[test]
fn only_an_edit_on_the_region_changes_its_face() {
    let before = family_zero();
    let outcome = step(&before, &swing_of(pronoun_edit()), &admitted()).expect("a step");
    match release_after_step(&before, &pronoun_region(), &outcome, "pronoun").expect("a reading") {
        ReleasePreservation::Changed { before, after } => {
            assert_eq!(before.values().get(&PRONOUN), Some(&IT));
            assert_eq!(after.values().get(&PRONOUN), Some(&HE));
        }
        other => panic!("an edit supported on the region changes its face: {other:?}"),
    }
}

#[test]
fn the_swing_widens_the_cross_section_and_width_is_not_monotone_along_edits() {
    let before = singleton(male_draft());
    assert!(
        before
            .region_width(&name_region(), "name")
            .expect("a width")
            .is_zero()
    );
    let swing = Swing::declared(
        "name-swing",
        vec![
            Edit::declared("keep", EditAction::Set { position: NAME, token: UNNAMED })
                .expect("a declared edit"),
            name_edit(),
        ],
    )
    .expect("a two-branch swing");
    let outcome = step(&before, &swing, &admitted()).expect("a step");
    let after = outcome.family().expect("the family continues");
    assert_eq!(after.cardinality(), BigUint::from(2u32));
    assert_eq!(
        after.region_width(&name_region(), "name").expect("a width").diameter(),
        &Rat::from_integer(BigInt::one()),
        "the swing opened two admitted fillers, so the name region's width grew from 0 to 1"
    );
}

#[test]
fn pure_restriction_never_widens_the_section() {
    let before = ArtifactFamily::Enumerated(
        EnumeratedFamily::declared(
            "three",
            vec![draft(DOG), draft(CAT), Artifact::declared(vec![IT, HAS, A_TOKEN, 42, UNNAMED, IS]).expect("a draft")],
        )
        .expect("a family"),
    );
    let wide = before
        .region_width(&region([NOUN]), "noun")
        .expect("a width")
        .diameter()
        .clone();
    let constraint = Constraint::declared(
        "noun-in-range",
        vec![ConstraintRule::Positionwise {
            position: NOUN,
            admitted: BTreeSet::from([DOG, CAT]),
        }],
    )
    .expect("a declared constraint");
    let after = restrict_only(&before, &constraint).expect("a restriction");
    let narrow = after
        .family()
        .expect("the family continues")
        .region_width(&region([NOUN]), "noun")
        .expect("a width")
        .diameter()
        .clone();
    assert!(narrow <= wide, "restriction is monotone: {narrow} <= {wide}");
    assert_eq!(narrow, Rat::from_integer(BigInt::one()));
    assert_eq!(wide, Rat::from_integer(BigInt::from(2)));
}

#[test]
fn a_step_work_product_above_the_ceiling_is_refused_before_any_branch_runs() {
    let member = Artifact::declared(vec![0; 32]).expect("a 32-slot artifact");
    let members: Vec<Artifact> = (0..FAMILY_CEILING)
        .map(|index| {
            let mut tokens = member.tokens().to_vec();
            tokens[0] = index as Token;
            Artifact::declared(tokens).expect("a 32-slot artifact")
        })
        .collect();
    let family = ArtifactFamily::Enumerated(
        EnumeratedFamily::declared("wide", members).expect("a family at the ceiling"),
    );
    let branches: Vec<Edit> = (0..SWING_BRANCH_CEILING)
        .map(|index| {
            Edit::declared(
                format!("branch{index}"),
                EditAction::Set {
                    position: 1,
                    token: index as Token,
                },
            )
            .expect("a declared edit")
        })
        .collect();
    let swing = Swing::declared("wide-swing", branches).expect("a swing at the ceiling");
    let refusal = step(&family, &swing, &Constraint::unconstrained("none")).unwrap_err();
    assert!(matches!(
        refusal,
        ArtifactRefusal::DeclarationAboveCeiling {
            what: "a family step work product",
            ceiling: STEP_WORK_CEILING,
            ..
        }
    ));
}

#[test]
fn a_false_support_claim_is_refused_rather_than_repaired() {
    let swing = swing_of(name_edit());
    let refusal = swing
        .check_support(&BTreeSet::from([PRONOUN]), &[draft(DOG)])
        .unwrap_err();
    assert_eq!(
        refusal,
        ArtifactRefusal::SupportClaimRefuted {
            swing: "name->Hermes".to_owned(),
            claimed: vec![PRONOUN],
            position: NAME,
        }
    );
}

#[test]
fn a_true_support_claim_is_checked_on_the_declared_probe() {
    let swing = swing_of(name_edit());
    swing
        .check_support(&BTreeSet::from([NAME]), &[draft(DOG), draft(CAT), male_draft()])
        .expect("the claim holds on the probe");
}

// -------------------------------------------------------------------------------------------
// Independence, entanglement and the two-axis square
// -------------------------------------------------------------------------------------------

#[test]
fn the_independent_and_the_entangled_edit_both_commute_on_the_family() {
    let ArtifactFamily::Enumerated(family) = family_zero() else {
        panic!("the role frame family is enumerated");
    };
    for (left, right) in [
        (noun_edit(), frame_edit()),
        (noun_edit(), name_edit()),
        (name_edit(), frame_edit()),
    ] {
        assert!(
            commutator_verdict(&family, &left, &right)
                .expect("a verdict")
                .commutes()
        );
    }
}

#[test]
fn commuting_does_not_separate_the_independent_from_the_entangled() {
    let ArtifactFamily::Enumerated(family) = family_zero() else {
        panic!("the role frame family is enumerated");
    };
    // `dog -> cat` and `is -> why` are both positionwise substitutions at distinct slots, so they
    // commute and both are chartwise. Only the admitted role constraint separates them.
    assert!(
        commutator_verdict(&family, &noun_edit(), &frame_edit())
            .expect("a verdict")
            .commutes()
    );
    assert!(noun_edit().action().is_chartwise());
    assert!(frame_edit().action().is_chartwise());
    assert!(
        step(&family_zero(), &swing_of(noun_edit()), &admitted())
            .expect("a step")
            .family()
            .is_some()
    );
    assert!(matches!(
        step(&family_zero(), &swing_of(frame_edit()), &admitted()).expect("a step"),
        StepOutcome::Emptied { .. }
    ));
}

#[test]
fn a_genuinely_non_commuting_pair_returns_its_witness() {
    let ArtifactFamily::Enumerated(family) = singleton(named_draft()) else {
        panic!("a singleton family is enumerated");
    };
    let verdict = commutator_verdict(&family, &agreement_edit(), &pronoun_reset())
        .expect("a verdict");
    match verdict {
        CommutatorVerdict::Entangled {
            witness,
            left_then_right,
            right_then_left,
            ..
        } => {
            assert_eq!(witness, named_draft());
            assert_ne!(left_then_right, right_then_left);
        }
        other => panic!("the agreement edit does not commute with a pronoun reset: {other:?}"),
    }
}

fn pronoun_reset() -> Edit {
    Edit::declared(
        "he->it",
        EditAction::Set {
            position: PRONOUN,
            token: IT,
        },
    )
    .expect("a declared edit")
}

#[test]
fn the_entangled_edit_is_not_chartwise() {
    assert!(!agreement_edit().action().is_chartwise());
    assert!(noun_edit().action().is_chartwise());
    let copy = Edit::declared(
        "copy",
        EditAction::CopyFrom {
            source: NAME,
            target: PRONOUN,
        },
    )
    .expect("a declared edit");
    assert!(!copy.action().is_chartwise());
}

#[test]
fn a_positionwise_word_passes_the_two_axis_square() {
    let circuit = RevisionCircuit::declared("positionwise", SLOTS, vec![noun_edit(), frame_edit()])
        .expect("a declared circuit");
    assert!(circuit.is_chartwise());
    let charts = vec![region([NOUN]), region([PRONOUN, NOUN]), region(0..SLOTS)];
    let faces: Vec<(Region, RegionFace)> = charts
        .iter()
        .map(|chart| (chart.clone(), chart.read(&named_draft()).expect("a face")))
        .collect();
    let verdict = circuit_square(&circuit, 0, 1, &charts, &faces).expect("a verdict");
    assert!(
        verdict.commutes(),
        "a positionwise edit commutes with every restriction: {verdict:?}"
    );
}

#[test]
fn the_entangled_edit_fails_the_two_axis_square() {
    let circuit = RevisionCircuit::declared("entangled", SLOTS, vec![agreement_edit(), noun_edit()])
        .expect("a declared circuit");
    assert!(!circuit.is_chartwise());
    let charts = vec![region([PRONOUN]), region(0..SLOTS)];
    let faces: Vec<(Region, RegionFace)> = charts
        .iter()
        .map(|chart| (chart.clone(), chart.read(&named_draft()).expect("a face")))
        .collect();
    let verdict = circuit_square(&circuit, 0, 1, &charts, &faces).expect("a verdict");
    let defect = verdict
        .defect()
        .expect("the chart that cannot see the name slot disagrees with the one that can");
    assert_eq!(defect.coarse(), &region([PRONOUN]));
    assert_ne!(
        defect.transported_then_restricted(),
        defect.restricted_then_transported()
    );
}

#[test]
fn the_commutator_of_the_entangled_pair_is_a_translation() {
    // Two positions over the exact cyclic alphabet `Z/3`: `g` rotates position 0 by one third of a
    // turn and `h` is the shear `y := y + x`, which is the entangled move. The commutator
    // `g⁻¹ h⁻¹ g h` is exactly the translation `y := y − 1`.
    let modulus: Token = 3;
    let rotate = |step: Token| {
        Edit::declared(
            "rotate0",
            EditAction::Rotate {
                position: 0,
                modulus,
                step,
            },
        )
        .expect("a declared edit")
    };
    for x in 0..modulus {
        for y in 0..modulus {
            let start = Artifact::declared(vec![x, y]).expect("a two-slot artifact");
            let sheared = shear(&start, modulus);
            let rotated = rotate(1).apply(&sheared).expect("a rotation");
            let unsheared = unshear(&rotated, modulus);
            let commutator = rotate(modulus - 1).apply(&unsheared).expect("a rotation");
            let expected =
                Artifact::declared(vec![x, (y + modulus - 1) % modulus]).expect("a two-slot artifact");
            assert_eq!(commutator, expected, "the commutator is the translation y := y - 1");
        }
    }
}

fn shear(artifact: &Artifact, modulus: Token) -> Artifact {
    let x = artifact.at(0).expect("position 0");
    let y = artifact.at(1).expect("position 1");
    Artifact::declared(vec![x, (y + x) % modulus]).expect("a two-slot artifact")
}

fn unshear(artifact: &Artifact, modulus: Token) -> Artifact {
    let x = artifact.at(0).expect("position 0");
    let y = artifact.at(1).expect("position 1");
    Artifact::declared(vec![x, (y + modulus - (x % modulus)) % modulus]).expect("a two-slot artifact")
}

// -------------------------------------------------------------------------------------------
// The declared circuit and its holonomy
// -------------------------------------------------------------------------------------------

#[test]
fn a_circuit_whose_intentions_cancel_returns_the_identity() {
    // `Transport/ContinuingTube.lean::tube_circuit_has_no_defect` says a functorial tube carries no
    // holonomy, so the revision cycle is a **declared** circuit. This one composes to the identity
    // at the declared receivers: the intentions cancel.
    let circuit = RevisionCircuit::declared(
        "cancelling",
        2,
        vec![
            Edit::declared(
                "turn",
                EditAction::Rotate {
                    position: 0,
                    modulus: 3,
                    step: 1,
                },
            )
            .expect("a declared edit"),
            Edit::declared(
                "turn-back",
                EditAction::Rotate {
                    position: 0,
                    modulus: 3,
                    step: 2,
                },
            )
            .expect("a declared edit"),
        ],
    )
    .expect("a declared circuit");
    let chart = Region::declared(2, [0, 1]).expect("a region");
    let artifact = Artifact::declared(vec![1, 2]).expect("a two-slot artifact");
    let face = chart.read(&artifact).expect("a face");
    let charts = vec![chart.clone()];
    let verdict = circuit_holonomy(&circuit, &charts, &[(chart, face)]).expect("a verdict");
    assert!(verdict.is_identity(), "the intentions cancel: {verdict:?}");
}

#[test]
fn a_circuit_with_a_residual_returns_its_holonomy() {
    let circuit = RevisionCircuit::declared(
        "winding",
        2,
        vec![
            Edit::declared(
                "turn",
                EditAction::Rotate {
                    position: 0,
                    modulus: 3,
                    step: 1,
                },
            )
            .expect("a declared edit"),
        ],
    )
    .expect("a declared circuit");
    let chart = Region::declared(2, [0, 1]).expect("a region");
    let artifact = Artifact::declared(vec![1, 2]).expect("a two-slot artifact");
    let face = chart.read(&artifact).expect("a face");
    let charts = vec![chart.clone()];
    let verdict = circuit_holonomy(&circuit, &charts, &[(chart, face)]).expect("a verdict");
    let defect = verdict.defect().expect("one turn does not return the face");
    assert_ne!(defect.entered(), defect.returned());
}

#[test]
fn no_defect_within_the_bound_is_not_cancellation() {
    // The circuit returns the face the caller declared and moves one it did not: the receipt is the
    // scope of the check, never a proof that the intentions cancel at an undeclared receiver.
    let circuit = RevisionCircuit::declared(
        "conditional",
        2,
        vec![
            Edit::declared(
                "bump-unless-zero",
                EditAction::Conditioned {
                    source: 0,
                    trigger: 1,
                    target: 1,
                    token: 7,
                },
            )
            .expect("a declared edit"),
        ],
    )
    .expect("a declared circuit");
    let chart = Region::declared(2, [0, 1]).expect("a region");
    let quiet = Artifact::declared(vec![0, 5]).expect("a two-slot artifact");
    let loud = Artifact::declared(vec![1, 5]).expect("a two-slot artifact");
    let quiet_face = chart.read(&quiet).expect("a face");
    let loud_face = chart.read(&loud).expect("a face");
    let charts = vec![chart.clone()];
    let quiet_verdict = circuit_holonomy(&circuit, &charts, &[(chart.clone(), quiet_face)])
        .expect("a verdict");
    assert!(quiet_verdict.is_identity());
    let loud_verdict =
        circuit_holonomy(&circuit, &charts, &[(chart, loud_face)]).expect("a verdict");
    assert!(
        loud_verdict.defect().is_some(),
        "the same circuit has a defect on a face the first check never declared"
    );
}

// -------------------------------------------------------------------------------------------
// Periplus and the revision loop
// -------------------------------------------------------------------------------------------

#[test]
fn the_periplus_residual_is_empty_exactly_when_the_draft_returns() {
    let outward = vec![name_edit()];
    let returning = vec![
        Edit::declared("unname", EditAction::Set { position: NAME, token: UNNAMED })
            .expect("a declared edit"),
    ];
    let residual = periplus_residual(&outward, &returning, &draft(DOG)).expect("a residual");
    assert!(residual.is_zero());

    let marking = vec![
        Edit::declared("unname", EditAction::Set { position: NAME, token: UNNAMED })
            .expect("a declared edit"),
        noun_edit(),
    ];
    let residual = periplus_residual(&outward, &marking, &draft(DOG)).expect("a residual");
    assert!(!residual.is_zero());
    assert_eq!(residual.entries().get(&NOUN), Some(&(DOG, CAT)));
}

#[test]
fn the_visible_face_returns_while_the_residual_is_nonzero() {
    let visible = region([PRONOUN, VERB, DETERMINER, NAME, FRAME]);
    let outward = vec![name_edit()];
    let returning = vec![
        Edit::declared("unname", EditAction::Set { position: NAME, token: UNNAMED })
            .expect("a declared edit"),
        noun_edit(),
    ];
    let start = draft(DOG);
    let residual = periplus_residual(&outward, &returning, &start).expect("a residual");
    assert!(!residual.is_zero(), "the interior binding changed");
    let mut carried = start.clone();
    for edit in outward.iter().chain(returning.iter()) {
        carried = edit.apply(&carried).expect("an edit");
    }
    assert_eq!(
        visible.read(&carried).expect("a face"),
        visible.read(&start).expect("a face"),
        "the visible region returned to its earlier face"
    );
}

#[test]
fn a_periplus_word_above_the_ceiling_is_refused_before_any_edit_runs() {
    let outward = vec![noun_edit(); EDIT_WORD_CEILING];
    let returning = vec![noun_edit()];
    let refusal = periplus_residual(&outward, &returning, &draft(DOG)).unwrap_err();
    assert!(matches!(
        refusal,
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: EDIT_WORD_CEILING,
            ..
        }
    ));
}

#[test]
fn a_traversal_that_changes_the_receiver_face_is_progress_at_rung_two() {
    let visible = region([NOUN]);
    let word = vec![noun_edit()];
    let route = RouteClass::of(&word).expect("a route class");
    let residual = periplus_residual(&word, &[], &draft(DOG)).expect("a residual");
    let after = noun_edit().apply(&draft(DOG)).expect("an edit");
    let outcome = classify_traversal(
        &Traversal {
            visible,
            before: draft(DOG),
            after,
            route_class: route,
            residual,
        },
        &RevisionHistory::new(),
        3,
        "noun",
    )
    .expect("a classification");
    match outcome {
        CircuitOutcome::Progress { rung, .. } => assert_eq!(rung, Rung::Continuation),
        other => panic!("a changed receiver face is progress: {other:?}"),
    }
}

#[test]
fn a_traversal_the_receiver_cannot_see_is_a_neutral_rechart_at_rung_four() {
    let visible = region([PRONOUN]);
    let word = vec![noun_edit()];
    let route = RouteClass::of(&word).expect("a route class");
    let residual = periplus_residual(&word, &[], &draft(DOG)).expect("a residual");
    let after = noun_edit().apply(&draft(DOG)).expect("an edit");
    let outcome = classify_traversal(
        &Traversal {
            visible,
            before: draft(DOG),
            after,
            route_class: route,
            residual,
        },
        &RevisionHistory::new(),
        0,
        "pronoun",
    )
    .expect("a classification");
    match outcome {
        CircuitOutcome::NeutralRechart { rung, receivers } => {
            assert_eq!(rung, Rung::ReceiverEqual);
            assert_eq!(receivers, vec!["pronoun".to_owned()]);
        }
        other => panic!("an unseen change is a neutral rechart: {other:?}"),
    }
}

#[test]
fn a_repeated_route_with_a_nonzero_residual_stops_replaying() {
    let visible = region([PRONOUN]);
    let word = vec![noun_edit()];
    let route = RouteClass::of(&word).expect("a route class");
    let residual = periplus_residual(&word, &[], &draft(DOG)).expect("a residual");
    let mut history = RevisionHistory::new();
    history
        .record(route.clone(), residual.clone())
        .expect("a record");
    history
        .record(route.clone(), residual.clone())
        .expect("a record");
    let after = noun_edit().apply(&draft(DOG)).expect("an edit");
    let outcome = classify_traversal(
        &Traversal {
            visible,
            before: draft(DOG),
            after,
            route_class: route.clone(),
            residual,
        },
        &history,
        2,
        "pronoun",
    )
    .expect("a classification");
    match outcome {
        CircuitOutcome::RevisionLoop(stop) => {
            assert_eq!(stop.route_class, route);
            assert_eq!(stop.traversals, 2);
            assert!(!stop.residual.is_zero());
        }
        other => panic!("a repeated ineffective route stops replaying: {other:?}"),
    }
}

#[test]
fn a_traversal_that_changes_nothing_returns_no_defect_within_the_bound() {
    let visible = region([PRONOUN]);
    let word = vec![noun_edit()];
    let route = RouteClass::of(&word).expect("a route class");
    let residual = periplus_residual(&[], &[], &draft(DOG)).expect("a residual");
    let outcome = classify_traversal(
        &Traversal {
            visible,
            before: draft(DOG),
            after: draft(DOG),
            route_class: route,
            residual,
        },
        &RevisionHistory::new(),
        4,
        "pronoun",
    )
    .expect("a classification");
    assert!(matches!(
        outcome,
        CircuitOutcome::NoDefectWithinBound { bound: 4, .. }
    ));
}

#[test]
fn the_revision_history_ceiling_is_checked_before_the_push() {
    let word = vec![noun_edit()];
    let route = RouteClass::of(&word).expect("a route class");
    let residual = periplus_residual(&[], &[], &draft(DOG)).expect("a residual");
    let mut history = RevisionHistory::new();
    for _ in 0..ROUTE_HISTORY_CEILING {
        history
            .record(route.clone(), residual.clone())
            .expect("a record");
    }
    let refusal = history.record(route, residual).unwrap_err();
    assert!(matches!(
        refusal,
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: ROUTE_HISTORY_CEILING,
            ..
        }
    ));
}

// -------------------------------------------------------------------------------------------
// The typed disposition
// -------------------------------------------------------------------------------------------

fn agreeing_chart() -> DeclaredChart {
    DeclaredChart::declared("role-frame", "role-frame")
}

#[test]
fn an_emptied_step_is_a_refusal_carrying_its_obstruction() {
    let outcome = step(&family_zero(), &swing_of(name_edit()), &admitted()).expect("a step");
    let disposition = disposition(
        &outcome,
        &pronoun_region(),
        &agreeing_chart(),
        "pronoun",
        &Rat::zero(),
    )
    .expect("a disposition");
    match disposition {
        ArtifactDisposition::Refuse(CausalObstruction::EmptyPreimageFibre {
            swing,
            constraint,
            refused,
        }) => {
            assert_eq!(swing, "name->Hermes");
            assert_eq!(constraint, "role-agreement");
            assert_eq!(refused, 2);
        }
        other => panic!("an empty preimage fibre is a refusal: {other:?}"),
    }
}

#[test]
fn a_chart_disagreement_is_a_reframe_carrying_the_migration() {
    let outcome = step(&family_zero(), &swing_of(noun_edit()), &admitted()).expect("a step");
    let chart = DeclaredChart::declared("audience-chart", "role-frame");
    let disposition = disposition(
        &outcome,
        &pronoun_region(),
        &chart,
        "pronoun",
        &Rat::zero(),
    )
    .expect("a disposition");
    match disposition {
        ArtifactDisposition::Reframe(change) => {
            assert_eq!(change.required, "audience-chart");
            assert_eq!(change.present, "role-frame");
            assert_eq!(change.migration, "role-frame -> audience-chart");
        }
        other => panic!("an incompatible chart is a reframe: {other:?}"),
    }
}

#[test]
fn a_released_region_emits_and_a_plural_one_holds() {
    let outcome = step(&family_zero(), &swing_of(noun_edit()), &admitted()).expect("a step");
    assert!(matches!(
        disposition(&outcome, &pronoun_region(), &agreeing_chart(), "pronoun", &Rat::zero())
            .expect("a disposition"),
        ArtifactDisposition::Release(ReleaseReturn::Released { .. })
    ));
    let plural = StepOutcome::Continued(family_zero());
    assert!(matches!(
        disposition(&plural, &region([NOUN]), &agreeing_chart(), "noun", &Rat::zero())
            .expect("a disposition"),
        ArtifactDisposition::Release(ReleaseReturn::Hold)
    ));
}

#[test]
fn a_wider_declared_tolerance_releases_the_same_plural_region() {
    let plural = StepOutcome::Continued(family_zero());
    let tolerance = Rat::from_integer(BigInt::one());
    match disposition(&plural, &region([NOUN]), &agreeing_chart(), "noun", &tolerance)
        .expect("a disposition")
    {
        ArtifactDisposition::Release(ReleaseReturn::Released { width, tolerance }) => {
            assert_eq!(width, Rat::from_integer(BigInt::one()));
            assert_eq!(tolerance, Rat::from_integer(BigInt::one()));
        }
        other => panic!("a width inside the declared tolerance releases: {other:?}"),
    }
}

#[test]
fn no_candidate_carries_the_disposition() {
    // One artifact lies in two families whose dispositions differ, so the disposition is a function
    // of the family and the receivers and is no member of the candidate set.
    let narrow = StepOutcome::Continued(family_zero());
    let wide = StepOutcome::Continued(ArtifactFamily::Enumerated(
        EnumeratedFamily::declared(
            "role-frame",
            vec![draft(DOG), draft(CAT), male_draft()],
        )
        .expect("a family"),
    ));
    let common = draft(DOG);
    assert!(
        narrow
            .family()
            .expect("continued")
            .members()
            .expect("enumerated")
            .contains(&common)
    );
    assert!(
        wide.family()
            .expect("continued")
            .members()
            .expect("enumerated")
            .contains(&common)
    );
    let left = disposition(
        &narrow,
        &pronoun_region(),
        &agreeing_chart(),
        "pronoun",
        &Rat::zero(),
    )
    .expect("a disposition");
    let right = disposition(
        &wide,
        &pronoun_region(),
        &agreeing_chart(),
        "pronoun",
        &Rat::zero(),
    )
    .expect("a disposition");
    assert_ne!(left, right);
    assert!(matches!(
        left,
        ArtifactDisposition::Release(ReleaseReturn::Released { .. })
    ));
    assert!(matches!(
        right,
        ArtifactDisposition::Release(ReleaseReturn::Hold)
    ));
}

#[test]
fn the_disposition_is_a_function_of_the_family_and_receivers() {
    let outcome = step(&family_zero(), &swing_of(noun_edit()), &admitted()).expect("a step");
    let again = step(&family_zero(), &swing_of(noun_edit()), &admitted()).expect("a step");
    assert_eq!(outcome, again);
    assert_eq!(
        disposition(&outcome, &pronoun_region(), &agreeing_chart(), "pronoun", &Rat::zero())
            .expect("a disposition"),
        disposition(&again, &pronoun_region(), &agreeing_chart(), "pronoun", &Rat::zero())
            .expect("a disposition")
    );
}

// -------------------------------------------------------------------------------------------
// Two media, typed differently
// -------------------------------------------------------------------------------------------

#[test]
fn an_editable_draft_may_change_any_position() {
    let draft = EditableDraft::found("paragraph", draft(DOG));
    let revised = draft.revise(&pronoun_edit()).expect("a revision");
    assert_eq!(revised.artifact().at(PRONOUN).expect("a token"), HE);
    assert_eq!(draft.artifact().at(PRONOUN).expect("a token"), IT);
}

#[test]
fn a_correction_never_changes_the_committed_boundary() {
    let utterance =
        IrrevocableUtterance::emitted("speech", vec![IT, HAS, A_TOKEN]).expect("an utterance");
    let corrected = utterance.correct(&[HE, HAS]).expect("a correction");
    assert_eq!(corrected.committed(), utterance.committed());
    assert_eq!(corrected.stream(), vec![IT, HAS, A_TOKEN, HE, HAS]);
}

#[test]
fn no_sequence_of_corrections_changes_the_committed_boundary() {
    let mut utterance =
        IrrevocableUtterance::emitted("speech", vec![IT, HAS, A_TOKEN]).expect("an utterance");
    let original = utterance.committed().to_vec();
    for token in 0..32u32 {
        utterance = utterance.correct(&[token]).expect("a correction");
        assert_eq!(utterance.committed(), original.as_slice());
    }
    assert_eq!(utterance.appended().len(), 32);
}

#[test]
fn the_committed_boundary_is_a_prefix_of_every_later_stream() {
    let utterance =
        IrrevocableUtterance::emitted("speech", vec![IT, HAS, A_TOKEN]).expect("an utterance");
    let corrected = utterance.correct(&[HE]).expect("a correction");
    let stream = corrected.stream();
    assert!(stream.starts_with(utterance.committed()));
    assert_eq!(&stream[..utterance.stream().len()], utterance.stream());
}

#[test]
fn a_correction_stream_above_the_ceiling_is_refused_before_the_append() {
    let utterance = IrrevocableUtterance::emitted("speech", vec![0; POSITION_CEILING])
        .expect("an utterance at the ceiling");
    let refusal = utterance.correct(&[1]).unwrap_err();
    assert!(matches!(
        refusal,
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: POSITION_CEILING,
            ..
        }
    ));
}

// -------------------------------------------------------------------------------------------
// The torus of edit phases
// -------------------------------------------------------------------------------------------

fn torus() -> EditTorus {
    EditTorus::declared("edit-phases", [0, 1], 12, [4, 3]).expect("a declared torus")
}

#[test]
fn the_edit_phases_have_the_declared_orders() {
    assert_eq!(torus().orders(), [3, 4]);
}

#[test]
fn the_two_edit_circuits_commute_on_the_artifact() {
    let torus = torus();
    let start = Artifact::declared(vec![0, 0]).expect("a two-slot artifact");
    let first = torus.turn(0).expect("a turn");
    let second = torus.turn(1).expect("a turn");
    let left = second
        .apply(&first.apply(&start).expect("a turn"))
        .expect("a turn");
    let right = first
        .apply(&second.apply(&start).expect("a turn"))
        .expect("a turn");
    assert_eq!(left, right);
}

#[test]
fn a_nontrivial_winding_returns_the_visible_face() {
    let torus = torus();
    let word = torus.word(3, 0).expect("a word");
    assert_eq!(
        torus.winding(&word).expect("a winding"),
        [BigInt::from(3), BigInt::zero()]
    );
    assert!(
        torus
            .returns_the_visible_face(&word)
            .expect("a face reading")
    );
    let start = Artifact::declared(vec![5, 7]).expect("a two-slot artifact");
    let mut carried = start.clone();
    for edit in &word {
        carried = edit.apply(&carried).expect("a turn");
    }
    assert_eq!(
        carried.at(0).expect("a token"),
        start.at(0).expect("a token") % 12,
        "three turns of the first circuit return the face while the winding is (3, 0)"
    );
}

#[test]
fn one_turn_does_not_return_the_visible_face() {
    let torus = torus();
    let word = torus.word(1, 0).expect("a word");
    assert!(
        !torus
            .returns_the_visible_face(&word)
            .expect("a face reading")
    );
    let word = torus.word(0, 3).expect("a word");
    assert!(
        !torus
            .returns_the_visible_face(&word)
            .expect("a face reading")
    );
    let word = torus.word(3, 4).expect("a word");
    assert!(
        torus
            .returns_the_visible_face(&word)
            .expect("a face reading")
    );
}

#[test]
fn a_torus_step_that_does_not_divide_the_modulus_is_refused() {
    assert!(EditTorus::declared("bad", [0, 1], 12, [5, 3]).is_err());
    assert!(EditTorus::declared("zero", [0, 1], 0, [1, 1]).is_err());
    assert!(EditTorus::declared("same", [0, 0], 12, [4, 3]).is_err());
}

// -------------------------------------------------------------------------------------------
// Rungs, and the hostile declarations
// -------------------------------------------------------------------------------------------

#[test]
fn every_relation_between_two_drafts_states_its_rung() {
    let before = draft(DOG);
    let after = noun_edit().apply(&before).expect("an edit");
    assert_eq!(
        draft_rung(&pronoun_region(), &before, &before).expect("a rung"),
        Rung::Identity
    );
    assert_eq!(
        draft_rung(&pronoun_region(), &before, &after).expect("a rung"),
        Rung::ReceiverEqual
    );
    assert_eq!(
        draft_rung(&region([NOUN]), &before, &after).expect("a rung"),
        Rung::Continuation
    );
    assert!(!Rung::Continuation.entails(Rung::ReceiverEqual));
    assert!(!Rung::ReceiverEqual.entails(Rung::Identity));
}

#[test]
fn a_rotation_of_modulus_zero_is_refused() {
    let refusal = Edit::declared(
        "zero",
        EditAction::Rotate {
            position: 0,
            modulus: 0,
            step: 1,
        },
    )
    .unwrap_err();
    assert!(matches!(refusal, ArtifactRefusal::ZeroModulus { .. }));
}

#[test]
fn an_edit_writing_outside_the_artifact_is_refused_rather_than_panicking() {
    let edit = Edit::declared(
        "far",
        EditAction::Set {
            position: 99,
            token: 0,
        },
    )
    .expect("a declared edit");
    assert_eq!(
        edit.apply(&draft(DOG)).unwrap_err(),
        ArtifactRefusal::PositionOutsideArtifact {
            position: 99,
            length: SLOTS,
        }
    );
}

#[test]
fn an_edit_reading_outside_the_artifact_is_refused_rather_than_panicking() {
    let edit = Edit::declared(
        "far-read",
        EditAction::CopyFrom {
            source: 99,
            target: 0,
        },
    )
    .expect("a declared edit");
    assert!(matches!(
        edit.apply(&draft(DOG)).unwrap_err(),
        ArtifactRefusal::PositionOutsideArtifact { .. }
    ));
}

#[test]
fn a_swing_with_no_branch_is_refused() {
    assert!(matches!(
        Swing::declared("empty", Vec::new()).unwrap_err(),
        ArtifactRefusal::EmptySwing { .. }
    ));
}

#[test]
fn a_swing_above_the_branch_ceiling_is_refused_before_any_branch_is_read() {
    let branches = vec![noun_edit(); SWING_BRANCH_CEILING + 1];
    assert!(matches!(
        Swing::declared("wide", branches).unwrap_err(),
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: SWING_BRANCH_CEILING,
            ..
        }
    ));
}

#[test]
fn an_edit_word_above_the_ceiling_is_refused_before_the_circuit_is_founded() {
    let word = vec![noun_edit(); EDIT_WORD_CEILING + 1];
    assert!(matches!(
        RevisionCircuit::declared("long", SLOTS, word).unwrap_err(),
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: EDIT_WORD_CEILING,
            ..
        }
    ));
    assert!(RevisionCircuit::declared("empty", SLOTS, Vec::new()).is_err());
}

#[test]
fn a_swing_over_an_enclosure_is_refused_rather_than_materialized() {
    let enclosed = ArtifactFamily::Enclosed(
        EnclosedFamily::declared("enclosure", vec![BTreeSet::from([IT, HE]); SLOTS])
            .expect("a declared enclosure"),
    );
    assert!(matches!(
        step(&enclosed, &swing_of(noun_edit()), &admitted()).unwrap_err(),
        ArtifactRefusal::EnclosureHasNoEnumeratedMembers { .. }
    ));
}

#[test]
fn an_enclosure_restricts_positionwise_without_materializing_a_member() {
    let alphabet: BTreeSet<Token> = (0..1000).collect();
    let enclosed = EnclosedFamily::declared("enclosure", vec![alphabet; 4])
        .expect("a declared enclosure");
    let constraint = Constraint::declared(
        "narrow",
        vec![ConstraintRule::Positionwise {
            position: 0,
            admitted: BTreeSet::from([7]),
        }],
    )
    .expect("a declared constraint");
    let narrowed = enclosed.restricted(&constraint).expect("a restriction");
    assert_eq!(
        narrowed.cardinality(),
        BigUint::from(1000u32).pow(3),
        "one position pinned divides the exact cardinality by its alphabet"
    );
    assert!(
        narrowed
            .region_released(&Region::declared(4, [0]).expect("a region"))
            .expect("a reading")
    );
}

#[test]
fn a_constraint_above_the_rule_ceiling_is_refused_before_any_rule_is_read() {
    let rules = vec![
        ConstraintRule::Positionwise {
            position: 0,
            admitted: BTreeSet::from([IT]),
        };
        CONSTRAINT_RULE_CEILING + 1
    ];
    assert!(matches!(
        Constraint::declared("too-many", rules).unwrap_err(),
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: CONSTRAINT_RULE_CEILING,
            ..
        }
    ));
}

#[test]
fn a_support_probe_above_the_ceiling_is_refused_before_any_branch_runs() {
    let swing = swing_of(name_edit());
    let probe = vec![draft(DOG); SUPPORT_PROBE_CEILING + 1];
    assert!(matches!(
        swing
            .check_support(&BTreeSet::from([NAME]), &probe)
            .unwrap_err(),
        ArtifactRefusal::DeclarationAboveCeiling {
            ceiling: SUPPORT_PROBE_CEILING,
            ..
        }
    ));
}

#[test]
fn a_region_declared_from_a_hostile_iterator_is_refused_at_its_first_out_of_range_position() {
    assert_eq!(
        Region::declared(SLOTS, [0usize, 1, usize::MAX]).unwrap_err(),
        ArtifactRefusal::PositionOutsideArtifact {
            position: usize::MAX,
            length: SLOTS,
        }
    );
}

/// **A support claim checked on no artifact is not a checked claim.** An empty probe passed the
/// loop vacuously, even for the claim that the swing writes nothing at all.
#[test]
fn a_support_claim_over_an_empty_probe_is_refused() {
    let swing = swing_of(name_edit());
    assert!(matches!(
        swing.check_support(&BTreeSet::new(), &[]),
        Err(ArtifactRefusal::EmptySupportProbe { .. })
    ));
}
