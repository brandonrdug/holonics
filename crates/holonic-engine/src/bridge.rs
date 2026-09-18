//! **Typed bridges: eight statuses, one grade, and a composition that takes the meet.**
//!
//! [definition] This module is the executable owner of item **C7** of
//! `docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`. Its Lean counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/Bridge.lean`
//! (namespace `Soma.Holonics.Foundation.Bridges`), and the correspondence is the deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `EpistemicGrade`, `SupportLevel`, `EpistemicGrade.support` | [`EpistemicGrade`], [`SupportLevel`], [`EpistemicGrade::support`] |
//! | `composeGrade`, `composeGrade_comm`, `composeGrade_assoc` | [`compose_grade`] and its tests |
//! | `BridgeStatus`, `BridgeStatus.entails`, `entails_refl/_trans/_antisymm` | [`BridgeStatus`], [`BridgeStatus::entails`] |
//! | `statusMeet`, `statusMeet_lower`, `statusMeet_greatest` | [`status_meet`] |
//! | `Bridge`, `passage_of_map` | [`Bridge`], [`Bridge::declare`] |
//! | `composedPassage`, `composedPassage_of_both` | [`Bridge::compose`] and `ComposedTransition` |
//! | `BridgeComposition`, `comp_at_meet`, `composedBridge_status_grade` | [`BridgeComposition`] |
//! | `ProposedBridge`, `Promotion`, `counterexample_blocks_promotion` | [`ProposedBridge`], [`ProposedBridge::promote`] |
//! | `rebaseBridge`, `Transition.ofEquiv` | [`rebase_bridge`] over [`ExactRebase`], which **is** [`ExactShift`] |
//! | `padicHalfBridge` | [`residue_restriction_bridge`] over [`ResidueRestriction`] |
//! | `grainBridge` | [`grain_restriction_bridge`] over [`crate::grain_tower::GrainSelection`] |
//! | `proteinEmbeddingProposal` | [`protein_embedding_proposal`] |
//!
//! # Eight statuses that must not share one word
//!
//! [project-postulate] AGENTS.md: "Co-presence is not contact. Contact has a declared interaction;
//! equal receiver output is not source equality." "Everything is connectable" is true only as a
//! typed discipline in which the **kind** of connection is data and the weakest kinds carry no map.
//!
//! [proved-derived] [`BridgeStatus::entails`] is a genuine partial order and it is **not** total.
//! A shared receiver face and an actual map are incomparable; an equivalence and a natural family
//! are incomparable above a structure-preserving map; and a speculative analogy is off the order
//! entirely — it entails nothing and nothing entails it, so [`status_meet`] refuses to compose it.
//!
//! # The grade is the canon's, and the canon declares no order
//!
//! [project-postulate] `docs/canon/EPISTEMIC_GRADES.md` gives eleven truth-status grades and **no
//! ordering among them**. [`compose_grade`] therefore does not rank them: it reads each grade's
//! declared [`SupportLevel`] — how much a composite may inherit from a link carrying that grade —
//! and returns the weaker, refusing `Counterexample` and `Historical`, which are dispositions
//! rather than support. The support reading is declared here and is named as a declared reading
//! wherever it is used.
//!
//! # No floats
//!
//! [implemented-exact] Every passage below is exact: `BigInt`, `BigUint`, or the exact contact
//! faces of [`crate::grain_tower`].

use std::collections::BTreeMap;
use std::fmt::{self, Debug};

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;

use crate::continuing_tower::{ComposedTransition, ExactShift, Transition};
use crate::grain_tower::{GrainFace, GrainSelection, SelectionResidual};

// -------------------------------------------------------------------------------------------
// C7 (a) — the epistemic grade
// -------------------------------------------------------------------------------------------

/// The eleven truth-status grades of `docs/canon/EPISTEMIC_GRADES.md`. A bridge carries exactly
/// one.
///
/// Lean counterpart: `Foundation/Bridge.lean::EpistemicGrade`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EpistemicGrade {
    /// A declared term or construction.
    Definition,
    /// A governing discipline adopted by this project.
    ProjectPostulate,
    /// A standard external theorem in its ordinary scope.
    ProvedStandard,
    /// A theorem derived in the project.
    ProvedDerived,
    /// A factual capability established for a declared construction or receiver family.
    EstablishedBounded,
    /// A conclusion under named hypotheses.
    Conditional,
    /// A proposed structure-preserving correspondence and active theorem-finding program.
    Interpretation,
    /// A precise unproved claim.
    Conjecture,
    /// A construction refuting a stated stronger claim.
    Counterexample,
    /// A named unresolved fibre or missing capability (the canon's `open`).
    OpenObligation,
    /// Preserved provenance that does not govern current construction.
    Historical,
}

/// How much a composite bridge may inherit from a link carrying a given grade. A **declared
/// reading** of the grade, not an ordering of the canon's grades, which declares none.
///
/// Lean counterpart: `Foundation/Bridge.lean::SupportLevel`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SupportLevel {
    /// The link supports nothing downstream.
    Unsupported,
    /// The link supports a conclusion under its own named hypotheses.
    Hypothetical,
    /// The link supports a conclusion inside a declared construction or receiver family.
    Bounded,
    /// The link supports a conclusion outright.
    Proved,
}

impl SupportLevel {
    /// The support order, as a rank.
    ///
    /// Lean counterpart: `SupportLevel.rank`.
    pub fn rank(self) -> u8 {
        match self {
            Self::Unsupported => 0,
            Self::Hypothetical => 1,
            Self::Bounded => 2,
            Self::Proved => 3,
        }
    }

    /// The grade a composite carries when two links of the same support level, but different
    /// grades, meet.
    ///
    /// Lean counterpart: `SupportLevel.representative`.
    pub fn representative(self) -> EpistemicGrade {
        match self {
            Self::Unsupported => EpistemicGrade::OpenObligation,
            Self::Hypothetical => EpistemicGrade::Conditional,
            Self::Bounded => EpistemicGrade::EstablishedBounded,
            Self::Proved => EpistemicGrade::ProvedDerived,
        }
    }

    /// Every level, for exhaustive checking.
    pub const ALL: [SupportLevel; 4] = [
        SupportLevel::Unsupported,
        SupportLevel::Hypothetical,
        SupportLevel::Bounded,
        SupportLevel::Proved,
    ];
}

impl EpistemicGrade {
    /// Every grade, for exhaustive checking.
    pub const ALL: [EpistemicGrade; 11] = [
        EpistemicGrade::Definition,
        EpistemicGrade::ProjectPostulate,
        EpistemicGrade::ProvedStandard,
        EpistemicGrade::ProvedDerived,
        EpistemicGrade::EstablishedBounded,
        EpistemicGrade::Conditional,
        EpistemicGrade::Interpretation,
        EpistemicGrade::Conjecture,
        EpistemicGrade::Counterexample,
        EpistemicGrade::OpenObligation,
        EpistemicGrade::Historical,
    ];

    /// The declared support reading of this grade. `Counterexample` and `Historical` have
    /// **none**: a refutation is not a link, and preserved provenance does not govern
    /// construction, so a composite through either is refused rather than graded.
    ///
    /// Lean counterpart: `EpistemicGrade.support`.
    pub fn support(self) -> Option<SupportLevel> {
        match self {
            Self::Definition | Self::ProjectPostulate | Self::EstablishedBounded => {
                Some(SupportLevel::Bounded)
            }
            Self::ProvedStandard | Self::ProvedDerived => Some(SupportLevel::Proved),
            Self::Conditional | Self::Interpretation => Some(SupportLevel::Hypothetical),
            Self::Conjecture | Self::OpenObligation => Some(SupportLevel::Unsupported),
            Self::Counterexample | Self::Historical => None,
        }
    }
}

/// Compose two grades: the weaker support wins, ties on the same level are canonicalized to that
/// level's representative, and a link with no support reading refuses.
///
/// Lean counterpart: `Foundation/Bridge.lean::composeGrade`, with `composeGrade_comm`,
/// `composeGrade_assoc` and `composeGrade_support_le`.
pub fn compose_grade(left: EpistemicGrade, right: EpistemicGrade) -> Option<EpistemicGrade> {
    let (a, b) = (left.support()?, right.support()?);
    Some(if a.rank() < b.rank() {
        left
    } else if b.rank() < a.rank() {
        right
    } else if left == right {
        left
    } else {
        a.representative()
    })
}

// -------------------------------------------------------------------------------------------
// C7 (b) — the eight statuses
// -------------------------------------------------------------------------------------------

/// The eight distinct statuses a connection claim can carry. They must not share one word.
///
/// Lean counterpart: `Foundation/Bridge.lean::BridgeStatus`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BridgeStatus {
    /// One aperture in which both occur. Owes no map and no equality.
    CoPresence,
    /// Two receivers into a common numeric face, with a tolerance and the aperture.
    NumericalResemblance,
    /// One receiver `ρ` with `ρ a = ρ b`. Owes no source identity.
    SharedReceiverFace,
    /// An actual map with its domain and its residual. Owes no preservation.
    ActualMap,
    /// A map together with the diagram it preserves. Owes no invertibility.
    StructurePreservingMap,
    /// An equivalence with its natural squares. Owes no naturality in a parameter.
    Equivalence,
    /// An indexed family of maps commuting with restriction. Owes no exhaustiveness.
    NaturalFamily,
    /// A candidate with required hypotheses, supporting receivers and counterexamples.
    SpeculativeAnalogy,
}

impl BridgeStatus {
    /// Every status, for exhaustive checking.
    pub const ALL: [BridgeStatus; 8] = [
        BridgeStatus::CoPresence,
        BridgeStatus::NumericalResemblance,
        BridgeStatus::SharedReceiverFace,
        BridgeStatus::ActualMap,
        BridgeStatus::StructurePreservingMap,
        BridgeStatus::Equivalence,
        BridgeStatus::NaturalFamily,
        BridgeStatus::SpeculativeAnalogy,
    ];

    /// Everything this status entails, itself included.
    ///
    /// Lean counterpart: `BridgeStatus.entailed`.
    pub fn entailed(self) -> &'static [BridgeStatus] {
        match self {
            Self::CoPresence => &[BridgeStatus::CoPresence],
            Self::NumericalResemblance => &[
                BridgeStatus::NumericalResemblance,
                BridgeStatus::CoPresence,
            ],
            Self::SharedReceiverFace => {
                &[BridgeStatus::SharedReceiverFace, BridgeStatus::CoPresence]
            }
            Self::ActualMap => &[BridgeStatus::ActualMap, BridgeStatus::CoPresence],
            Self::StructurePreservingMap => &[
                BridgeStatus::StructurePreservingMap,
                BridgeStatus::ActualMap,
                BridgeStatus::CoPresence,
            ],
            Self::Equivalence => &[
                BridgeStatus::Equivalence,
                BridgeStatus::StructurePreservingMap,
                BridgeStatus::ActualMap,
                BridgeStatus::CoPresence,
            ],
            Self::NaturalFamily => &[
                BridgeStatus::NaturalFamily,
                BridgeStatus::StructurePreservingMap,
                BridgeStatus::ActualMap,
                BridgeStatus::CoPresence,
            ],
            Self::SpeculativeAnalogy => &[BridgeStatus::SpeculativeAnalogy],
        }
    }

    /// Whether every claim of this status is also a claim of `other`.
    ///
    /// Lean counterpart: `BridgeStatus.entails`, with `entails_refl`, `entails_trans` and
    /// `entails_antisymm`.
    pub fn entails(self, other: BridgeStatus) -> bool {
        self.entailed().contains(&other)
    }

    /// Whether this status claims a map at all.
    pub fn claims_a_map(self) -> bool {
        self.entails(BridgeStatus::ActualMap)
    }
}

/// The greatest common lower bound of two statuses, when there is one. A speculative analogy has
/// no lower bound in common with anything else, so composing through it is refused.
///
/// Lean counterpart: `Foundation/Bridge.lean::statusMeet`, with `statusMeet_comm`,
/// `statusMeet_lower` and `statusMeet_greatest`.
pub fn status_meet(left: BridgeStatus, right: BridgeStatus) -> Option<BridgeStatus> {
    use BridgeStatus::*;
    match (left, right) {
        (SpeculativeAnalogy, SpeculativeAnalogy) => Some(SpeculativeAnalogy),
        (SpeculativeAnalogy, _) | (_, SpeculativeAnalogy) => None,
        (Equivalence, NaturalFamily) | (NaturalFamily, Equivalence) => {
            Some(StructurePreservingMap)
        }
        (a, b) => Some(if a.entails(b) {
            b
        } else if b.entails(a) {
            a
        } else {
            CoPresence
        }),
    }
}

// -------------------------------------------------------------------------------------------
// C7 (c) — the bridge
// -------------------------------------------------------------------------------------------

/// The diagram a bridge claims to preserve, and whether the claim was discharged.
///
/// Lean counterpart: the `Preserved` and `preserves` fields of `Foundation/Bridge.lean::Bridge`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PreservationClaim {
    /// The diagram, named exactly.
    pub diagram: String,
    /// Whether the claim was discharged, rather than merely stated.
    pub discharged: bool,
}

impl PreservationClaim {
    /// A discharged claim.
    pub fn discharged(diagram: impl Into<String>) -> Self {
        Self {
            diagram: diagram.into(),
            discharged: true,
        }
    }

    /// A stated but undischarged claim.
    pub fn stated(diagram: impl Into<String>) -> Self {
        Self {
            diagram: diagram.into(),
            discharged: false,
        }
    }
}

/// Why a bridge was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BridgeRefusal {
    /// A status at or above `ActualMap` was declared without a passage. The status is a typed
    /// claim, not a word.
    MapClaimedWithoutPassage {
        /// The status that was claimed.
        status: BridgeStatus,
    },
}

impl fmt::Display for BridgeRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MapClaimedWithoutPassage { status } => write!(
                f,
                "{status:?} claims a map at or above ActualMap and no passage was supplied"
            ),
        }
    }
}

impl std::error::Error for BridgeRefusal {}

/// A **bridge**: what kind of connection is claimed, the passage that carries it (a
/// [`Transition`], so a map arrives with the residual it does not transport), the diagram claimed
/// preserved, and exactly one epistemic grade.
///
/// [`Bridge::declare`] is what makes the status a *typed* claim rather than a word: a status at or
/// above [`BridgeStatus::ActualMap`] cannot be declared without supplying the passage.
///
/// Lean counterpart: `Foundation/Bridge.lean::Bridge`, whose `passage_of_map` field is that
/// refusal as a proof obligation.
#[derive(Clone, PartialEq, Eq)]
pub struct Bridge<T: Transition> {
    name: String,
    status: BridgeStatus,
    passage: Option<T>,
    preserved: PreservationClaim,
    grade: EpistemicGrade,
}

impl<T: Transition> Debug for Bridge<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Bridge")
            .field("name", &self.name)
            .field("status", &self.status)
            .field("carries_a_passage", &self.passage.is_some())
            .field("preserved", &self.preserved)
            .field("grade", &self.grade)
            .finish()
    }
}

impl<T: Transition> Bridge<T> {
    /// Declare a bridge. A status at or above [`BridgeStatus::ActualMap`] without a passage is
    /// refused by name.
    pub fn declare(
        name: impl Into<String>,
        status: BridgeStatus,
        passage: Option<T>,
        preserved: PreservationClaim,
        grade: EpistemicGrade,
    ) -> Result<Self, BridgeRefusal> {
        if status.claims_a_map() && passage.is_none() {
            return Err(BridgeRefusal::MapClaimedWithoutPassage { status });
        }
        Ok(Self {
            name: name.into(),
            status,
            passage,
            preserved,
            grade,
        })
    }

    /// The bridge's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Which of the eight is claimed.
    pub fn status(&self) -> BridgeStatus {
        self.status
    }

    /// Exactly one grade from `docs/canon/EPISTEMIC_GRADES.md`.
    pub fn grade(&self) -> EpistemicGrade {
        self.grade
    }

    /// The diagram claimed preserved.
    pub fn preserved(&self) -> &PreservationClaim {
        &self.preserved
    }

    /// The passage, with its residual.
    pub fn passage(&self) -> Option<&T> {
        self.passage.as_ref()
    }

    /// **A bridge never claims a map it does not carry.** This is an invariant of
    /// [`Bridge::declare`], returned here as a receipt.
    ///
    /// Lean counterpart: `comp_respects_map_claim`, which is the `passage_of_map` field.
    pub fn respects_its_map_claim(&self) -> bool {
        !self.status.claims_a_map() || self.passage.is_some()
    }

    /// **Compose two bridges: the meet of the statuses, the composition of the grades, and the
    /// residuals composed through [`Transition`].** The composite's residual is exactly the pair of
    /// component residuals, in the order they were dropped.
    ///
    /// Lean counterpart: `Foundation/Bridge.lean::Bridge.comp`, `comp_at_meet` and
    /// `composedPassage_of_both`.
    pub fn compose<Second>(
        second: Bridge<Second>,
        first: Bridge<T>,
    ) -> BridgeComposition<ComposedTransition<Second, T>>
    where
        Second: Transition<Source = T::Target>,
    {
        let Some(status) = status_meet(first.status, second.status) else {
            return BridgeComposition::StatusIncomparable {
                left: first.status,
                right: second.status,
            };
        };
        let Some(grade) = compose_grade(first.grade, second.grade) else {
            return BridgeComposition::GradeIncomparable {
                left: first.grade,
                right: second.grade,
            };
        };
        let name = format!("{} ∘ {}", second.name, first.name);
        let preserved = PreservationClaim {
            diagram: format!("{} ∧ {}", second.preserved.diagram, first.preserved.diagram),
            discharged: second.preserved.discharged && first.preserved.discharged,
        };
        let passage = match (first.passage, second.passage) {
            (Some(f), Some(s)) => Some(ComposedTransition::new(s, f)),
            _ => None,
        };
        if status.claims_a_map() && passage.is_none() {
            return BridgeComposition::PassageMissing { claimed: status };
        }
        BridgeComposition::Composed(Bridge {
            name,
            status,
            passage,
            preserved,
            grade,
        })
    }
}

/// The lawful returns of an attempted composition. A refusal is returned as content and never
/// raised.
///
/// Lean counterpart: `Foundation/Bridge.lean::BridgeComposition`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BridgeComposition<T: Transition> {
    /// The composite bridge.
    Composed(Bridge<T>),
    /// The two statuses have no common lower bound — a speculative analogy is involved.
    StatusIncomparable {
        /// The first link's status.
        left: BridgeStatus,
        /// The second link's status.
        right: BridgeStatus,
    },
    /// One grade is a disposition rather than a support: `Counterexample` or `Historical`.
    GradeIncomparable {
        /// The first link's grade.
        left: EpistemicGrade,
        /// The second link's grade.
        right: EpistemicGrade,
    },
    /// The meet claims a map and no passage was supplied.
    PassageMissing {
        /// The status the meet claims.
        claimed: BridgeStatus,
    },
}

// -------------------------------------------------------------------------------------------
// C7 (d) — the proposed bridge and its promotion
// -------------------------------------------------------------------------------------------

/// One hypothesis a proposed bridge owes before it may be promoted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Hypothesis {
    /// The hypothesis, stated exactly.
    pub statement: String,
    /// Whether it has been discharged.
    pub discharged: bool,
}

/// A recorded refutation of a stronger claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordedCounterexample {
    /// Exactly what it refutes, and the witness.
    pub statement: String,
}

/// A receiver that reads both sides into one face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SupportingReceiver {
    /// The common face both sides are read into.
    pub face: String,
    /// The reading of the source.
    pub source_reading: String,
    /// The reading of the target.
    pub target_reading: String,
}

/// Why a promotion was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PromotionRefusal {
    /// A required hypothesis has not been discharged.
    HypothesisUndischarged {
        /// Which one.
        statement: String,
    },
    /// A counterexample is on record. It blocks promotion by type.
    CounterexampleRecorded {
        /// Which one.
        statement: String,
    },
    /// The target status is not at least as strong as the candidate's declared status.
    TargetNotStronger {
        /// The requested status.
        target: BridgeStatus,
        /// The candidate's declared status.
        candidate: BridgeStatus,
    },
    /// The target claims a map and the candidate carries none.
    PassageMissing {
        /// The requested status.
        target: BridgeStatus,
    },
}

impl fmt::Display for PromotionRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::HypothesisUndischarged { statement } => {
                write!(f, "the required hypothesis {statement:?} is not discharged")
            }
            Self::CounterexampleRecorded { statement } => {
                write!(f, "a counterexample is on record: {statement}")
            }
            Self::TargetNotStronger { target, candidate } => write!(
                f,
                "{target:?} does not entail the candidate's declared status {candidate:?}"
            ),
            Self::PassageMissing { target } => {
                write!(f, "{target:?} claims a map and the candidate carries none")
            }
        }
    }
}

impl std::error::Error for PromotionRefusal {}

/// A **proposed bridge**: a candidate together with what it owes. An `Interpretation` in
/// `docs/canon/EPISTEMIC_GRADES.md` "must carry explicit maps, limits, preserved diagram, first
/// derivation target, and a falsifier that can fire"; those are exactly these fields.
///
/// Lean counterpart: `Foundation/Bridge.lean::ProposedBridge` and `Promotion`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProposedBridge<T: Transition> {
    /// The candidate connection.
    pub candidate: Bridge<T>,
    /// What must be discharged before it may be promoted.
    pub required_hypotheses: Vec<Hypothesis>,
    /// Receivers that read both sides into one face.
    pub supporting_receivers: Vec<SupportingReceiver>,
    /// Recorded refutations of a stronger claim.
    pub counterexamples: Vec<RecordedCounterexample>,
    /// The test that can fire.
    pub falsifier: String,
}

impl<T: Transition> ProposedBridge<T> {
    /// Promote the candidate to a stronger status. Every required hypothesis must be discharged,
    /// no counterexample may be on record, the target must entail the candidate's declared status,
    /// and a target that claims a map must already have its passage.
    ///
    /// Lean counterpart: `Promotion` and `Promotion.promoted`, with
    /// `counterexample_blocks_promotion`, `false_hypothesis_blocks_promotion` and
    /// `missing_passage_blocks_promotion`.
    pub fn promote(self, target: BridgeStatus) -> Result<Bridge<T>, PromotionRefusal> {
        if let Some(counterexample) = self.counterexamples.first() {
            return Err(PromotionRefusal::CounterexampleRecorded {
                statement: counterexample.statement.clone(),
            });
        }
        if let Some(open) = self.required_hypotheses.iter().find(|h| !h.discharged) {
            return Err(PromotionRefusal::HypothesisUndischarged {
                statement: open.statement.clone(),
            });
        }
        if !target.entails(self.candidate.status) {
            return Err(PromotionRefusal::TargetNotStronger {
                target,
                candidate: self.candidate.status,
            });
        }
        if target.claims_a_map() && self.candidate.passage.is_none() {
            return Err(PromotionRefusal::PassageMissing { target });
        }
        Ok(Bridge {
            name: self.candidate.name,
            status: target,
            passage: self.candidate.passage,
            preserved: self.candidate.preserved,
            grade: self.candidate.grade,
        })
    }
}

// -------------------------------------------------------------------------------------------
// C7 (e) — bridges that really exist in this tree
// -------------------------------------------------------------------------------------------

/// The `p`-adic restriction from level `m + k` to level `m`, presented as a [`Transition`]:
/// transport the residue, retain the digit block above it.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::padicRestrictTransition`, whose residual is
/// `padicDigitGap` and whose reopening is `padicReopenGap` — `padicReopenGap_val` is exactly
/// `target + modulus * residual`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResidueRestriction {
    modulus: BigUint,
}

impl ResidueRestriction {
    /// The restriction modulo `modulus`. A zero modulus is refused: it carries no level at all.
    pub fn new(modulus: BigUint) -> Option<Self> {
        if modulus.is_zero() {
            None
        } else {
            Some(Self { modulus })
        }
    }

    /// The level this restriction reads.
    pub fn modulus(&self) -> &BigUint {
        &self.modulus
    }
}

impl Transition for ResidueRestriction {
    type Source = BigUint;
    type Target = BigUint;
    type Residual = BigUint;

    fn apply(&self, source: &BigUint) -> BigUint {
        source % &self.modulus
    }

    fn residual(&self, source: &BigUint) -> BigUint {
        source / &self.modulus
    }

    fn reopen(&self, target: &BigUint, residual: &BigUint) -> BigUint {
        target + &self.modulus * residual
    }
}

/// The passage of [`rebase_bridge`]: an exact translation, read as an equivalence, which drops
/// nothing.
///
/// [definition] **This is [`ExactShift`], not a second copy of it.** It used to be a separate
/// `BigUint` implementation, and that was wrong twice over. `x -> x + offset` is not a bijection of
/// the unsigned integers — nothing lands below `offset` — so neither the `Equivalence` status
/// [`rebase_bridge`] declares nor the `Transition.ofEquiv` its Lean owner cites actually held; and
/// its `reopen` computed `target - offset` in `BigUint`, which **panics** for every target below
/// the offset, although the [`Transition`] contract makes `reopen` total and merely *unspecified*
/// outside the image of `apply`. Over the signed integers the translation is a genuine equivalence
/// and the reopening is total — which is what [`ExactShift`] already was, so there is now one
/// owner and no duplicate.
///
/// Lean counterpart: `Foundation/Bridge.lean::rebaseBridge`, whose passage is
/// `Transition.ofEquiv R.faceEquiv`, with `rebaseBridge_residual_subsingleton` as the
/// zero-residual law.
pub type ExactRebase = ExactShift;

/// **`rebaseMigration` is an equivalence.** An invertible passage with a one-valued residual,
/// preserving the receive square of `Foundation/Holon.lean::Holon.Rebase`.
///
/// The offset is a `BigInt` and the passage is [`ExactRebase`] — that is, [`ExactShift`] — because
/// translation is an equivalence of the *signed* integers and only of those. See [`ExactRebase`].
///
/// Lean counterpart: `Foundation/Bridge.lean::rebaseBridge`.
pub fn rebase_bridge(offset: BigInt) -> Bridge<ExactRebase> {
    Bridge::declare(
        "rebaseMigration",
        BridgeStatus::Equivalence,
        Some(ExactRebase::new(offset)),
        PreservationClaim::discharged(
            "Holon.Rebase.receive_natural: faceEquiv ∘ left.receive = right.receive ∘ occurrenceEquiv",
        ),
        EpistemicGrade::ProvedDerived,
    )
    .expect("an equivalence declared with its passage")
}

/// **`padicHalfMigration` is a lossy structure-preserving map with a residual.** The chart
/// component transports the residue and retains the digit block it drops.
///
/// Lean counterpart: `Foundation/Bridge.lean::padicHalfBridge`.
pub fn residue_restriction_bridge(modulus: BigUint) -> Option<Bridge<ResidueRestriction>> {
    let passage = ResidueRestriction::new(modulus)?;
    Some(
        Bridge::declare(
            "padicHalfMigration",
            BridgeStatus::StructurePreservingMap,
            Some(passage),
            PreservationClaim::discharged(
                "ResidualMigration.reopen_apply: reopen(face(x), residual(x)) = x at every chart",
            ),
            EpistemicGrade::ProvedDerived,
        )
        .expect("a structure-preserving map declared with its passage"),
    )
}

/// **The grain restriction is a lossy structure-preserving map.** The alpha-carbon selection of
/// [`crate::grain_tower`] read as a bridge: the coarse reading is the passage, every fine reading
/// the selection never looked at is the residual, and the preserved claim is the exact round trip.
///
/// Lean counterpart: `Foundation/Bridge.lean::grainBridge`, over
/// `Foundation/GrainRestriction.lean::selectionTransition`.
pub fn grain_restriction_bridge(selection: GrainSelection) -> Bridge<GrainSelection> {
    Bridge::declare(
        format!("grainRestriction({})", selection.lineage),
        BridgeStatus::StructurePreservingMap,
        Some(selection),
        PreservationClaim::discharged(
            "GrainRestriction.grain_residual_reopens_the_source: the coarse face together with the \
             residual reopens the atom face exactly",
        ),
        EpistemicGrade::EstablishedBounded,
    )
    .expect("a structure-preserving map declared with its passage")
}

/// The passage a proposed bridge does not have. It exists so that a speculative candidate is a
/// well-typed `Bridge` carrying **no** map: the arms are uninhabited in practice because the
/// candidate's `passage` is always `None`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NoPassage;

impl Transition for NoPassage {
    type Source = Vec<u32>;
    type Target = Vec<u32>;
    type Residual = Vec<u32>;

    fn apply(&self, source: &Vec<u32>) -> Vec<u32> {
        source.clone()
    }

    fn residual(&self, source: &Vec<u32>) -> Vec<u32> {
        source.clone()
    }

    fn reopen(&self, _target: &Vec<u32>, residual: &Vec<u32>) -> Vec<u32> {
        residual.clone()
    }
}

/// **The protein contact atlas against a learned embedding atlas**, as one honest
/// [`ProposedBridge`] at speculative status and `Interpretation` grade.
///
/// It is a *candidate*: no passage is supplied, and the three required hypotheses are written out
/// rather than gestured at.
///
/// 1. the contact face separates distinct contact complexes — otherwise the source of the bridge is
///    already a quotient and the bridge is about that quotient, not about the protein;
/// 2. the candidate map carries the contact face to the embedding face exactly — otherwise there is
///    a residual, and the bridge is at best a lossy map with that residual retained;
/// 3. the candidate map is injective — otherwise it is a coarse graining and owes its residual.
///
/// The falsifier fires when two contact complexes with different faces share an embedding
/// coordinate.
///
/// Lean counterpart: `Foundation/Bridge.lean::proteinEmbeddingProposal`.
pub fn protein_embedding_proposal() -> ProposedBridge<NoPassage> {
    ProposedBridge {
        candidate: Bridge::declare(
            "proteinContactAtlas ↔ learnedEmbeddingAtlas",
            BridgeStatus::SpeculativeAnalogy,
            None,
            PreservationClaim::stated(
                "for every presentation x, embeddingFace(candidateMap(x)) = contactFace(x)",
            ),
            EpistemicGrade::Interpretation,
        )
        .expect("a speculative analogy claims no map, so no passage is owed"),
        required_hypotheses: vec![
            Hypothesis {
                statement: "the contact face separates distinct contact complexes: \
                            contactFace(x) = contactFace(y) → x = y"
                    .to_string(),
                discharged: false,
            },
            Hypothesis {
                statement: "the candidate map carries the contact face to the embedding face \
                            exactly: embeddingFace(candidateMap(x)) = contactFace(x)"
                    .to_string(),
                discharged: false,
            },
            Hypothesis {
                statement: "the candidate map is injective; otherwise it is a coarse graining and \
                            owes its residual"
                    .to_string(),
                discharged: false,
            },
        ],
        supporting_receivers: vec![SupportingReceiver {
            face: "exact integer contact count at a declared aperture".to_string(),
            source_reading: "GrainFace::inside on the residue-grain contact complex".to_string(),
            target_reading: "the learned atlas's own declared integer contact readout".to_string(),
        }],
        counterexamples: Vec::new(),
        falsifier: "two contact complexes with different contact faces that share one embedding \
                    coordinate"
            .to_string(),
    }
}

/// The exact grain readings behind a [`grain_restriction_bridge`], for a caller that wants the
/// receipt rather than the bridge: the coarse face, the retained residual and the reopened source.
///
/// Lean counterpart: `grainBridge_preserves`, discharged by
/// `GrainRestriction.grain_residual_reopens_the_source`.
pub fn grain_bridge_receipt(
    bridge: &Bridge<GrainSelection>,
    atom_face: &GrainFace,
) -> Option<(GrainFace, SelectionResidual, GrainFace)> {
    let selection = bridge.passage()?;
    let coarse = selection.apply(atom_face);
    let residual = selection.residual(atom_face);
    let reopened = selection.reopen(&coarse, &residual);
    Some((coarse, residual, reopened))
}

/// The counts a caller can read off a composed bridge without owning the passage's types: how many
/// statuses entail each status. It exists so that the partial order can be audited from outside.
pub fn entailment_census() -> BTreeMap<BridgeStatus, usize> {
    let mut census = BTreeMap::new();
    for target in BridgeStatus::ALL {
        let count = BridgeStatus::ALL
            .into_iter()
            .filter(|source| source.entails(target))
            .count();
        census.insert(target, count);
    }
    census
}

#[cfg(test)]
mod tests;
