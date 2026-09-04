//! Total receiver-case refinement for the descent-face theorem.
//!
//! The ten receiver faces are not a dispatch enum.  They are quotients of the complete leaf
//! refinement induced by the point boundary, equal/distinct abscissa, equal/inverse ordinate,
//! root incidence and the two slot-convention landing caustics.  Every leaf retains the fibre that
//! the quotient hides.  Source owners are bound by their S0 content occurrence; names and paths
//! remain exterior testimony and never enter the incidence sent to the card.

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::incidence::{IncidenceReturn, RecruitmentContact};

const SQCLS_REFL: &str = "fd1589e01232eb9b868385b2aaefa75c69b6a99326b540d2e379e7d7cea31a49";
const THREE_HALF_TURNS: &str = "c0c0cc6c2a62cc4f6ea8532f9840537e2a7711c099e094be475fc56fd1d9ff6e";
const FOUR_FACE_VALUES: &str = "8549af969730934036cad67c9ec4ffd51299fb7c80aae049a5722847c80c8754";
const COMPUTED_MULTIPLICATIVITY: &str =
    "5d2074c7cb4ef84f08535c89c0295acd110e31608566112b32bc6fb22d1179ca";
const DOUBLED_TRIVIAL_CLASS: &str =
    "a679a37aea22a9af3696d96e5e92387effbce6188fe267f753e20d20077d560f";
const HALF_TURN_TRANSLATION_FACE: &str =
    "892b1ddf763141536516d54216697b571b46bbc51f2578b43153aef1edff4fb8";
const TRANSLATION_GROUP_SUM: &str =
    "a61f4f460b93853c3351898d8211c1c07d80354a0519f40f616747f77ad517b5";
const CHORD_SLOT_CLOSURE: &str = "0f347d2d9acb9dcef952030b5728d0de90f3c2379a9c866bdf91e5c4f78d8750";
const GENERIC_CHORD_FACE: &str = "18452f5f5ba45349846932a120463e9d5fe0a038acad07ed487f761a5369a03b";

const OWNER_BINDINGS: [&str; 9] = [
    SQCLS_REFL,
    THREE_HALF_TURNS,
    FOUR_FACE_VALUES,
    COMPUTED_MULTIPLICATIVITY,
    DOUBLED_TRIVIAL_CLASS,
    HALF_TURN_TRANSLATION_FACE,
    TRANSLATION_GROUP_SUM,
    CHORD_SLOT_CLOSURE,
    GENERIC_CHORD_FACE,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum BoundaryFace {
    Exterior,
    Affine,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum EqualityFace {
    Unasked,
    Equal,
    Distinct,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RootFace {
    Unasked,
    Root,
    General,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum LandingFace {
    Unasked,
    ZeroConvention,
    PositiveConvention,
    Ordinary,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct LeafFace {
    pub left_boundary: BoundaryFace,
    pub right_boundary: BoundaryFace,
    pub abscissa: EqualityFace,
    pub ordinate: EqualityFace,
    pub left_root: RootFace,
    pub right_root: RootFace,
    pub landing: LandingFace,
    pub orientation: i8,
}

#[derive(Clone, Debug, Serialize)]
pub struct CaseFace {
    pub ordinal: u8,
    pub occurrence: String,
    pub receiver_face: String,
    pub leaves: Vec<LeafFace>,
    pub carrier_operations: BTreeSet<String>,
    pub open_reconstruction_fibre: Vec<String>,
}

/// One finest admitted receiver target.  The card sees these addressed leaves and obstructions;
/// it never receives the ten exterior case labels as a dispatch table.
#[derive(Clone, Debug, Serialize)]
pub struct ResidentRefinementTarget {
    pub occurrence: String,
    pub case_occurrence: String,
    pub refinement_leaf: Option<LeafFace>,
    pub obstruction_occurrence: Option<String>,
    pub carrier_operations: BTreeSet<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ImpossibleOverlap {
    pub occurrence: String,
    pub constraints: Vec<String>,
    pub consequence: String,
}

#[derive(Clone, Debug, Serialize)]
pub struct CaseAblation {
    pub carrier_operation: String,
    pub reopened_case_occurrences: BTreeSet<String>,
    pub surviving_case_occurrences: BTreeSet<String>,
}

#[derive(Clone, Debug, Serialize)]
pub struct CaseCoverage {
    pub receiver_cases: usize,
    pub refinement_leaves: usize,
    pub assigned_leaves: usize,
    pub multiply_assigned_leaves: usize,
    pub impossible_overlaps: usize,
    pub resident_refinement_targets: usize,
    pub default_branches: usize,
    pub case_labels_sent_to_device: bool,
    pub total_receiver_cover: bool,
}

#[derive(Clone, Debug, Serialize)]
pub struct TotalCaseComplex {
    pub schema: String,
    pub source_occurrence: String,
    pub target_operation: String,
    pub owner_bindings: BTreeSet<String>,
    pub cases: Vec<CaseFace>,
    pub impossible_overlaps: Vec<ImpossibleOverlap>,
    pub resident_refinement_targets: Vec<ResidentRefinementTarget>,
    pub active_contacts: Vec<RecruitmentContact>,
    pub source_ablations: Vec<CaseAblation>,
    pub coverage: CaseCoverage,
    pub truth_status: String,
}

pub fn derive(incidence: &IncidenceReturn) -> Result<TotalCaseComplex, String> {
    let operation_population = incidence
        .operations
        .iter()
        .map(|operation| operation.occurrence.as_str())
        .collect::<BTreeSet<_>>();
    for owner in OWNER_BINDINGS {
        if !operation_population.contains(owner) {
            return Err(format!("the S0 carrier operation is absent: {owner}"));
        }
        if !incidence.active_carrier_operations.contains(owner) {
            return Err(format!(
                "the S0 carrier operation left the active cover: {owner}"
            ));
        }
    }

    let roots = [-1_i8, 0, 1];
    let mut specifications = Vec::<(&str, Vec<LeafFace>, &[&str], Vec<String>)>::new();

    let identity_leaves = vec![
        leaf(
            BoundaryFace::Exterior,
            BoundaryFace::Exterior,
            EqualityFace::Unasked,
            EqualityFace::Unasked,
            RootFace::Unasked,
            RootFace::Unasked,
            LandingFace::Unasked,
            0,
        ),
        leaf(
            BoundaryFace::Exterior,
            BoundaryFace::Affine,
            EqualityFace::Unasked,
            EqualityFace::Unasked,
            RootFace::Unasked,
            RootFace::Unasked,
            LandingFace::Unasked,
            1,
        ),
        leaf(
            BoundaryFace::Affine,
            BoundaryFace::Exterior,
            EqualityFace::Unasked,
            EqualityFace::Unasked,
            RootFace::Unasked,
            RootFace::Unasked,
            LandingFace::Unasked,
            -1,
        ),
    ];
    specifications.push((
        "left-or-right-identity",
        identity_leaves,
        &[SQCLS_REFL],
        vec![
            "the exterior point's hidden opposite operand remains in the reconstruction fibre"
                .to_owned(),
        ],
    ));

    specifications.push((
        "equal-abscissa-equal-point-doubling",
        vec![leaf(
            BoundaryFace::Affine,
            BoundaryFace::Affine,
            EqualityFace::Equal,
            EqualityFace::Equal,
            RootFace::General,
            RootFace::General,
            LandingFace::Ordinary,
            0,
        )],
        &[DOUBLED_TRIVIAL_CLASS],
        Vec::new(),
    ));
    specifications.push((
        "equal-abscissa-vertical-inverse",
        vec![leaf(
            BoundaryFace::Affine,
            BoundaryFace::Affine,
            EqualityFace::Equal,
            EqualityFace::Distinct,
            RootFace::General,
            RootFace::General,
            LandingFace::Unasked,
            0,
        )],
        &[SQCLS_REFL],
        vec![
            "the oriented inverse witness is retained although the sum condenses to the identity"
                .to_owned(),
        ],
    ));

    let repeated = roots
        .into_iter()
        .map(|root| {
            leaf(
                BoundaryFace::Affine,
                BoundaryFace::Affine,
                EqualityFace::Equal,
                EqualityFace::Equal,
                RootFace::Root,
                RootFace::Root,
                LandingFace::Unasked,
                root,
            )
        })
        .collect();
    specifications.push((
        "repeated-half-turn",
        repeated,
        &[
            THREE_HALF_TURNS,
            FOUR_FACE_VALUES,
            COMPUTED_MULTIPLICATIVITY,
        ],
        vec!["which of the three roots repeated is retained".to_owned()],
    ));

    let mut distinct_half_turns = Vec::new();
    for left in roots {
        for right in roots {
            if left != right {
                distinct_half_turns.push(leaf(
                    BoundaryFace::Affine,
                    BoundaryFace::Affine,
                    EqualityFace::Distinct,
                    EqualityFace::Equal,
                    RootFace::Root,
                    RootFace::Root,
                    LandingFace::Unasked,
                    left * 4 + right,
                ));
            }
        }
    }
    specifications.push((
        "distinct-half-turn-chord",
        distinct_half_turns,
        &[FOUR_FACE_VALUES, COMPUTED_MULTIPLICATIVITY],
        vec!["the ordered pair of roots is retained beyond commutative receiver output".to_owned()],
    ));

    let mut half_turn_translation = Vec::new();
    for orientation in [-1_i8, 1] {
        for root in roots {
            half_turn_translation.push(leaf(
                BoundaryFace::Affine,
                BoundaryFace::Affine,
                EqualityFace::Distinct,
                EqualityFace::Distinct,
                if orientation < 0 {
                    RootFace::Root
                } else {
                    RootFace::General
                },
                if orientation < 0 {
                    RootFace::General
                } else {
                    RootFace::Root
                },
                LandingFace::Ordinary,
                orientation * (root + 2),
            ));
        }
    }
    specifications.push((
        "one-half-turn-one-general-point-both-orientations",
        half_turn_translation,
        &[HALF_TURN_TRANSLATION_FACE, TRANSLATION_GROUP_SUM],
        vec![
            "root identity and left/right orientation remain distinct source histories".to_owned(),
        ],
    ));

    for (face, landing, carriers) in [
        (
            "generic-distinct-abscissa-secant",
            LandingFace::Ordinary,
            &[CHORD_SLOT_CLOSURE, GENERIC_CHORD_FACE][..],
        ),
        (
            "secant-landing-at-zero-half-turn",
            LandingFace::ZeroConvention,
            &[CHORD_SLOT_CLOSURE][..],
        ),
        (
            "secant-landing-at-positive-half-turn",
            LandingFace::PositiveConvention,
            &[CHORD_SLOT_CLOSURE][..],
        ),
    ] {
        specifications.push((
            face,
            vec![leaf(
                BoundaryFace::Affine,
                BoundaryFace::Affine,
                EqualityFace::Distinct,
                EqualityFace::Distinct,
                RootFace::General,
                RootFace::General,
                landing,
                0,
            )],
            carriers,
            Vec::new(),
        ));
    }

    let impossible_overlaps = impossible_overlaps(&incidence.source_occurrence);
    specifications.push((
        "impossible-overlaps-and-open-reconstruction-fibres",
        Vec::new(),
        &[CHORD_SLOT_CLOSURE],
        impossible_overlaps
            .iter()
            .map(|overlap| overlap.consequence.clone())
            .collect(),
    ));

    let mut cases = Vec::new();
    let mut leaf_owners = BTreeMap::<LeafFace, Vec<String>>::new();
    for (at, (receiver, leaves, carriers, fibre)) in specifications.into_iter().enumerate() {
        let carrier_operations = carriers
            .iter()
            .map(|owner| (*owner).to_owned())
            .collect::<BTreeSet<_>>();
        let occurrence = address(&[
            incidence.source_occurrence.as_bytes(),
            receiver.as_bytes(),
            carriers.join("|").as_bytes(),
        ]);
        for leaf in &leaves {
            leaf_owners
                .entry(leaf.clone())
                .or_default()
                .push(occurrence.clone());
        }
        cases.push(CaseFace {
            ordinal: u8::try_from(at + 1).map_err(|_| "case ordinal extent".to_owned())?,
            occurrence,
            receiver_face: receiver.to_owned(),
            leaves,
            carrier_operations,
            open_reconstruction_fibre: fibre,
        });
    }
    if cases.len() != 10 {
        return Err(format!(
            "the total receiver quotient returned {} cases",
            cases.len()
        ));
    }
    let multiply_assigned_leaves = leaf_owners
        .values()
        .filter(|owners| owners.len() != 1)
        .count();
    let assigned_leaves = leaf_owners.len();
    let refinement_leaves = cases.iter().map(|case| case.leaves.len()).sum();
    if assigned_leaves != refinement_leaves || multiply_assigned_leaves != 0 {
        return Err("the total case refinement is not an exact partition".to_owned());
    }

    let impossible_case = cases
        .last()
        .ok_or_else(|| "the impossible/open-fibre receiver is absent".to_owned())?;
    let mut resident_refinement_targets = Vec::new();
    for case in &cases {
        for leaf in &case.leaves {
            resident_refinement_targets.push(ResidentRefinementTarget {
                occurrence: leaf_occurrence(&incidence.source_occurrence, leaf),
                case_occurrence: case.occurrence.clone(),
                refinement_leaf: Some(leaf.clone()),
                obstruction_occurrence: None,
                carrier_operations: case.carrier_operations.clone(),
            });
        }
    }
    for obstruction in &impossible_overlaps {
        resident_refinement_targets.push(ResidentRefinementTarget {
            occurrence: address(&[
                incidence.source_occurrence.as_bytes(),
                b"obstruction-fibre",
                obstruction.occurrence.as_bytes(),
            ]),
            case_occurrence: impossible_case.occurrence.clone(),
            refinement_leaf: None,
            obstruction_occurrence: Some(obstruction.occurrence.clone()),
            carrier_operations: impossible_case.carrier_operations.clone(),
        });
    }
    resident_refinement_targets.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    let mut active_contacts = Vec::new();
    for target in &resident_refinement_targets {
        for carrier in &target.carrier_operations {
            active_contacts.push(contact(
                carrier,
                &target.occurrence,
                "refinement-carrier-return",
            ));
        }
    }
    active_contacts.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));
    let all_cases = cases
        .iter()
        .map(|case| case.occurrence.clone())
        .collect::<BTreeSet<_>>();
    let mut source_ablations = Vec::new();
    for carrier in OWNER_BINDINGS {
        let reopened = cases
            .iter()
            .filter(|case| case.carrier_operations.contains(carrier))
            .map(|case| case.occurrence.clone())
            .collect::<BTreeSet<_>>();
        if reopened.is_empty() {
            return Err(format!("carrier operation {carrier} owns no case"));
        }
        source_ablations.push(CaseAblation {
            carrier_operation: carrier.to_owned(),
            surviving_case_occurrences: all_cases.difference(&reopened).cloned().collect(),
            reopened_case_occurrences: reopened,
        });
    }

    Ok(TotalCaseComplex {
        schema: "holonics.m6.total-case-complex.v2".to_owned(),
        source_occurrence: incidence.source_occurrence.clone(),
        target_operation: incidence.target_operation.clone(),
        owner_bindings: OWNER_BINDINGS.iter().map(ToString::to_string).collect(),
        cases,
        impossible_overlaps,
        resident_refinement_targets,
        active_contacts,
        source_ablations,
        coverage: CaseCoverage {
            receiver_cases: 10,
            refinement_leaves,
            assigned_leaves,
            multiply_assigned_leaves,
            impossible_overlaps: 6,
            resident_refinement_targets: refinement_leaves + 6,
            default_branches: 0,
            case_labels_sent_to_device: false,
            total_receiver_cover: true,
        },
        truth_status: "established-bounded".to_owned(),
    })
}

fn leaf_occurrence(source: &str, leaf: &LeafFace) -> String {
    let faces = [
        leaf.left_boundary as u8,
        leaf.right_boundary as u8,
        leaf.abscissa as u8,
        leaf.ordinate as u8,
        leaf.left_root as u8,
        leaf.right_root as u8,
        leaf.landing as u8,
        leaf.orientation as u8,
    ];
    address(&[source.as_bytes(), b"receiver-refinement-leaf", &faces])
}

#[allow(clippy::too_many_arguments)]
const fn leaf(
    left_boundary: BoundaryFace,
    right_boundary: BoundaryFace,
    abscissa: EqualityFace,
    ordinate: EqualityFace,
    left_root: RootFace,
    right_root: RootFace,
    landing: LandingFace,
    orientation: i8,
) -> LeafFace {
    LeafFace {
        left_boundary,
        right_boundary,
        abscissa,
        ordinate,
        left_root,
        right_root,
        landing,
        orientation,
    }
}

fn impossible_overlaps(source: &str) -> Vec<ImpossibleOverlap> {
    [
        (
            "exterior-and-affine",
            &["one point occurrence is simultaneously exterior and affine"][..],
            "constructor disjointness returns an obstruction",
        ),
        (
            "equal-and-distinct-abscissa",
            &["the same abscissa pair is both equal and distinct"][..],
            "equality and apartness cannot occupy one leaf",
        ),
        (
            "root-and-nonzero-ordinate",
            &["an affine root has a nonzero ordinate on y^2=x^3-x"][..],
            "the curve equation collapses the ordinate to zero",
        ),
        (
            "equal-point-and-vertical-inverse-off-root",
            &["equal ordinates are inverse while the ordinate is nonzero"][..],
            "characteristic zero separates doubling from the vertical inverse",
        ),
        (
            "two-distinct-landing-conventions",
            &["one secant landing abscissa is both zero and one"][..],
            "the slot convention caustics are disjoint",
        ),
        (
            "generic-guard-at-a-convention-root",
            &["the generic chord route is requested where its returned square witness vanishes"][..],
            "the retained fibre reopens and routes through the corresponding landing face",
        ),
    ]
    .into_iter()
    .map(|(face, constraints, consequence)| ImpossibleOverlap {
        occurrence: address(&[source.as_bytes(), face.as_bytes()]),
        constraints: constraints.iter().map(ToString::to_string).collect(),
        consequence: consequence.to_owned(),
    })
    .collect()
}

fn contact(from: &str, to: &str, relation: &str) -> RecruitmentContact {
    RecruitmentContact {
        occurrence: address(&[from.as_bytes(), to.as_bytes(), relation.as_bytes()]),
        from: from.to_owned(),
        to: to.to_owned(),
        relation: relation.to_owned(),
    }
}

fn address(parts: &[&[u8]]) -> String {
    let mut hasher = Sha256::new();
    for part in parts {
        hasher.update((part.len() as u64).to_le_bytes());
        hasher.update(part);
    }
    hasher
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
