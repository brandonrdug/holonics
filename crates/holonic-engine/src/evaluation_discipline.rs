//! **B9 — evaluation discipline, and B10's run receipts.**
//!
//! [definition] This module is the executable owner of item **B9** of
//! `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`, together with the *receipt*
//! half of item **B10**. Its Lean counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/EvaluationDiscipline.lean`
//! (namespace `Soma.Holonics.Foundation.EvaluationDiscipline`), and the correspondence is the
//! deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `Lineage`, `Lineage.setoid`, `Lineage.Class`, `Lineage.cls` | [`LineageClasses`] |
//! | `Lineage.cls_eq_of_rel`, `Lineage.rel_of_cls_eq` | [`LineageClasses::related`] and [`LineageClasses::class_of`] |
//! | `Split`, `Straddles` | [`Split`], [`LineageStraddle`] |
//! | `ofClassPredicate`, `ofClassPredicate_does_not_straddle` | [`Split::from_class_partition`] |
//! | `rawSplit`, `rawSplit_straddles` | [`Split::from_raw_designs`] and [`LineageClasses::straddle_of`] |
//! | `FittedReceiver`, `Leaks`, `evaluateAt` | [`FittedReceiver`], [`FittedReceiver::evaluate_at`] |
//! | `evaluateAt_refuses_a_fitted_occurrence` | [`EvaluationRefusal::ReceiverFittedOnThisOccurrence`] |
//! | `evaluateAt_refuses_a_lineage_equivalent_occurrence` | [`EvaluationRefusal::ReceiverFittedOnALineageEquivalentDesign`] |
//! | `evaluateAt_admits_when_nothing_leaks` | [`ReceiverAdmission`] |
//! | `Calibration`, `AssayBridge`, `transport` | [`Calibration`], [`AssayBridge`], [`Calibration::carry_to`] |
//! | `within_one_assay_needs_no_bridge`, `across_assays_without_a_bridge_is_refused` | [`Calibration::carry_to`] and its tests |
//! | `TimedFace`, `ExternalComparison`, `compare` | [`TimedReading`], [`ExternalComparison`], [`ExternalComparison::state`] |
//! | `the_return_does_not_relabel_the_prediction` | [`ExternalComparison::prediction`] |
//! | `the_comparison_is_not_at_the_predictions_time` | [`ExternalComparison::stated_at`] |
//! | `DisagreementClass`, `classifyContact` | [`DisagreementClass`], [`disagreement_subsets`] |
//! | `correct_on_the_unanimous_contact_and_wrong_on_the_separating_one` | [`performance_on`] and its test |
//! | `UniversalClaim`, `universalClaim_is_uninhabited` | [`UniversalClaim`], uninhabited |
//! | `Conclusion`, `Conclusion.scope`, `Conclusion.atAnotherSplit` | [`EvaluationConclusion`] |
//! | `a_conclusion_does_not_travel_to_another_split` | [`EvaluationConclusion::at_another_split`] |
//! | `evaluation_contract` | the whole module |
//!
//! # Why this is a new owner and not more of `design_selection`
//!
//! [definition] [`crate::design_selection`] owns **the selection**: which designs a cascade keeps,
//! and — since this wave — what that cascade costs. The object here is different: it is **the
//! evaluation of a selection**, whose population is not the designs but the *split*, whose carriers
//! are lineage classes rather than designs, and whose return type is a conclusion with a scope
//! rather than a survivor list. Three facts decide it:
//!
//! 1. **The carrier is the quotient.** A [`Split`] is constructible only from a partition of
//!    [`LineageClasses`], which is the quotient of the design population by the relation the
//!    horizontal [`crate::physical_occurrence::Passage`] mutations generate.
//!    `design_selection`'s stages all read *designs*; none of them has a reason to carry a quotient.
//! 2. **The leak is in the receivers, not in the population.** A fitted receiver carries the
//!    occurrences it was fitted on and refuses an evaluation-side reading. `design_selection`'s
//!    `DeclaredReceiver` is a declared *orientation* and has no fitting history, and giving it one
//!    would make every selection carry an evaluation's bookkeeping.
//! 3. **The return is bounded by construction.** [`EvaluationConclusion`] has no universal arm and
//!    does not travel to another split. That is a statement about *claims*, which the selection
//!    cascade makes none of.
//!
//! The cost cascade itself is **not** here: it is one cascade with two readings, so it extends
//! `design_selection` — [`crate::design_selection::CostedCascade`], [`crate::design_selection::DiscardLaw`]
//! and [`crate::design_selection::cost_saving`] — rather than being founded a second time.
//!
//! # Lineage never straddles a split
//!
//! [proved-derived] The horizontal `Mutation` passages of [`crate::physical_occurrence::passage`]
//! generate the lineage relation: two designs joined by a chain of at most a declared
//! [`EditRadius`] of them are one **lineage class**. [`LineageClasses`] is the quotient, and
//! [`Split::from_class_partition`] is the only constructor that takes a partition of classes — it
//! cannot straddle, because its sides are unions of whole classes. [`Split::from_raw_designs`]
//! takes designs and **refuses** a straddle by name, carrying the pair and the connecting chain;
//! [`LineageClasses::straddle_of`] returns the same leak as data, which is the converse witness.
//!
//! # No floats
//!
//! [implemented-exact] Every reading is an [`holonics::exact_value::ExactInterval`] over
//! `BigRational`, every comparison goes through
//! [`crate::topological_receiver::compare_values`], and every clock reading is an exact integer
//! nanosecond count from a named monotonic source. A decimal appears only in prose and in assertion
//! messages.
//!
//! # Declared sizes are bounded before they are used
//!
//! [implemented-exact] [`LineageClasses::found`] checks the design population against
//! [`POPULATION_CEILING`] and the `pairs · sites` comparison count against [`COMPARISON_CEILING`]
//! with `checked_mul` **before** any pass or allocation sized by it;
//! [`LineageClasses::chain_between`] walks a graph whose node and edge counts were bounded at
//! founding; [`FittedReceiver::fitted`] bounds its fitting sets; and every subprocess a version
//! reader spawns has its captured output truncated at [`VERSION_OUTPUT_CEILING`] bytes.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::path::Path;
use std::time::Instant;

use num_bigint::BigUint;
use serde::Serialize;
use thiserror::Error;

use crate::design_selection::{AdmittedTransformation, DesignFamily, DesignId, ReceiverReading};
use holonics::exact_value::ExactInterval;
use crate::physical_occurrence::{
    DecidedClass, ExteriorDeclaration, OccurrenceId, PassageRefusal, PluralFibre,
};
use holonics::law::receiver::Rung;
use crate::standing::TimedFace;
use crate::topological_receiver::{ValueOrder, compare_values};

// -------------------------------------------------------------------------------------------
// Declared ceilings
// -------------------------------------------------------------------------------------------

/// The largest admitted design population of one evaluation.
pub const POPULATION_CEILING: usize = 4096;
/// The largest admitted declared edit radius.
pub const EDIT_RADIUS_CEILING: usize = 64;
/// The largest admitted `pairs · sites` comparison count of the lineage founding.
pub const COMPARISON_CEILING: usize = 1 << 26;
/// The largest admitted fitting set of one receiver.
pub const FITTING_CEILING: usize = 1 << 16;
/// The largest admitted number of declared keys.
pub const KEY_CEILING: usize = 1 << 16;
/// The most bytes a version reader captures from a subprocess.
pub const VERSION_OUTPUT_CEILING: usize = 4096;

// -------------------------------------------------------------------------------------------
// Typed refusals
// -------------------------------------------------------------------------------------------

/// **Why a supplied bridge cannot carry a calibration across two assays.**
///
/// [definition] Carried in a `Box` inside [`EvaluationRefusal::BridgeJoinsOtherAssays`] so that the
/// refusal family stays small: a refusal is returned by value from every constructor in this owner,
/// and a 144-byte variant would widen every one of those returns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BridgeMismatch {
    /// The bridge's declared name.
    pub bridge: String,
    /// The assay it leaves.
    pub bridge_source: String,
    /// The assay it arrives at.
    pub bridge_target: String,
    /// The calibration that was asked to cross.
    pub calibration: String,
    /// The assay the calibration was fitted within.
    pub fitted: String,
    /// The assay it was asked for at.
    pub asked: String,
}

impl std::fmt::Display for BridgeMismatch {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "bridge {:?} joins {:?} to {:?} and cannot carry calibration {:?} from {:?} to {:?}",
            self.bridge,
            self.bridge_source,
            self.bridge_target,
            self.calibration,
            self.fitted,
            self.asked
        )
    }
}

/// Every way this module declines to answer. A refusal is content; nothing here panics.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum EvaluationRefusal {
    /// A declared name, ground, label or reason is empty, so it states nothing.
    #[error("a declared {what} is empty, so it states nothing")]
    NotStated {
        /// Which declaration.
        what: &'static str,
    },
    /// An evaluation over no design is not an evaluation.
    #[error("an evaluation over no design is not an evaluation")]
    EmptyPopulation,
    /// The design population is above [`POPULATION_CEILING`].
    #[error("the design population is {declared}, above the ceiling {ceiling}")]
    PopulationTooLarge {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The declared edit radius is above [`EDIT_RADIUS_CEILING`].
    #[error("the declared edit radius is {declared} sites, above the ceiling {ceiling}")]
    EditRadiusTooLarge {
        /// What was declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The founding's comparison count is above [`COMPARISON_CEILING`], computed with checked
    /// arithmetic before anything is allocated or walked.
    #[error(
        "founding the lineage over {designs} designs at {sites} sites implies {implied} exact \
         monomer comparisons, above the ceiling {ceiling}"
    )]
    ComparisonPopulationTooLarge {
        /// The implied count, or `usize::MAX` when the computation itself overflowed.
        implied: usize,
        /// The design population.
        designs: usize,
        /// The longest declared sequence.
        sites: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A fitting set is above [`FITTING_CEILING`].
    #[error("receiver {receiver:?} declares a fitting set of {declared}, above the ceiling {ceiling}")]
    FittingSetTooLarge {
        /// Which receiver.
        receiver: String,
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// More keys were declared than [`KEY_CEILING`].
    #[error("{declared} keys were declared, above the ceiling {ceiling}")]
    KeyPopulationTooLarge {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A mutation names a design index the family does not carry.
    #[error("the admitted mutation names design index {index}, and the family carries {declared}")]
    MutationNamesAnAbsentDesign {
        /// The index named.
        index: usize,
        /// How many the family carries.
        declared: usize,
    },
    /// A mutation names an environment index the family does not carry.
    #[error("the admitted mutation names environment index {index}, and the family carries {declared}")]
    MutationNamesAnAbsentEnvironment { index: usize, declared: usize },
    /// A manually assembled mutation failed the same passage law used by design selection.
    #[error("the admitted mutation is not a lawful horizontal passage: {0}")]
    MutationPassageRefused(#[from] PassageRefusal),
    /// A design identity the evaluation's population does not carry.
    #[error("the evaluation carries no design {id:?}")]
    DesignAbsent {
        /// The identity.
        id: DesignId,
    },
    /// A lineage class index the quotient does not carry.
    #[error("the lineage quotient carries no class {index}; it has {declared}")]
    ClassAbsent {
        /// The index asked for.
        index: usize,
        /// How many classes there are.
        declared: usize,
    },
    /// A class index appears twice in a declared partition.
    #[error("the lineage class {index} is declared twice in one side of the split")]
    ClassRepeated {
        /// The repeated index.
        index: usize,
    },
    /// A design appears twice in a declared side.
    #[error("design {id:?} is declared twice in one side of the split")]
    DesignRepeated {
        /// The repeated identity.
        id: DesignId,
    },
    /// One side of the split is empty, so the split answers nothing.
    #[error("the {side} side of the split is empty, so the split answers nothing")]
    EmptySide {
        /// Which side.
        side: &'static str,
    },
    /// **The leakage refusal.** The declared split separates two designs of one lineage class.
    #[error(
        "the split puts design {left:?} on the development side and design {right:?} on the \
         evaluation side, and they are one lineage class ({class}) joined by a chain of {steps} \
         mutation passage(s): {chain}. Close variants of one lineage never straddle a split"
    )]
    SplitStraddlesALineageClass {
        /// The development-side design.
        left: DesignId,
        /// The evaluation-side design.
        right: DesignId,
        /// Which class they share.
        class: usize,
        /// How long the connecting chain is.
        steps: usize,
        /// The connecting chain, rendered.
        chain: String,
    },
    /// A design states no value at an axis the declared discipline splits on.
    #[error("design {id:?} states no {axis} key, and the {discipline} discipline splits on it")]
    KeyNotStated {
        /// The design.
        id: DesignId,
        /// The axis.
        axis: &'static str,
        /// The discipline.
        discipline: &'static str,
    },
    /// A key was declared twice for one design and axis.
    #[error("design {id:?} declares the {axis} key twice")]
    KeyRepeated {
        /// The design.
        id: DesignId,
        /// The axis.
        axis: &'static str,
    },
    /// The held-out value names no design, so the leave-one-out split is empty.
    #[error("no design carries the {axis} key {held_out:?}, so this leave-one-out split is empty")]
    HeldOutValueAbsent {
        /// The axis.
        axis: &'static str,
        /// The value asked for.
        held_out: String,
    },
    /// **The receiver leakage refusal.** The receiver was fitted on this very occurrence.
    #[error(
        "receiver {receiver:?} was fitted on occurrence {occurrence:?}; evaluating it there reads \
         its own developmental material"
    )]
    ReceiverFittedOnThisOccurrence {
        /// Which receiver.
        receiver: String,
        /// Which occurrence.
        occurrence: OccurrenceId,
    },
    /// **The receiver leakage refusal, through lineage.** No member crossed the split and the
    /// receiver still carries the evaluation side inside it.
    #[error(
        "receiver {receiver:?} was fitted on design {fitted:?}, which is lineage-equivalent to the \
         evaluation design {evaluated:?} (class {class}, {steps} mutation passage(s)); a driver may \
         not select developmental material from an evaluation target"
    )]
    ReceiverFittedOnALineageEquivalentDesign {
        /// Which receiver.
        receiver: String,
        /// The design it was fitted on.
        fitted: DesignId,
        /// The design being evaluated.
        evaluated: DesignId,
        /// The class they share.
        class: usize,
        /// How long the connecting chain is.
        steps: usize,
    },
    /// A calibration was applied across assays with no bridge.
    #[error(
        "calibration {calibration:?} was fitted within assay {fitted:?} and was asked for at assay \
         {asked:?} with no bridge; a calibration does not transport silently"
    )]
    CalibrationCrossesAssaysWithoutABridge {
        /// The calibration.
        calibration: String,
        /// The assay it was fitted within.
        fitted: String,
        /// The assay it was asked for at.
        asked: String,
    },
    /// The supplied bridge joins two other assays. Boxed, so that the whole refusal family stays
    /// small enough to return by value.
    #[error("{0}")]
    BridgeJoinsOtherAssays(Box<BridgeMismatch>),
    /// A bridge between one assay and itself states nothing.
    #[error("a bridge from assay {assay:?} to itself states nothing")]
    BridgeIsCircular {
        /// The assay.
        assay: String,
    },
    /// An external return that was not read is not a return.
    #[error("the external return at receiver {receiver:?} is Unread ({why:?}), so it is not a return")]
    ExternalReturnIsUnread {
        /// Which receiver.
        receiver: String,
        /// The stated reason it was unread.
        why: String,
    },
    /// The external return does not come after the prediction it is compared with.
    #[error(
        "the prediction occurs at {prediction} and the external return at {external}; a return that \
         does not come later is not a later occurrence"
    )]
    ReturnIsNotLater {
        /// The prediction's time.
        prediction: usize,
        /// The return's time.
        external: usize,
    },
    /// A contact the fibre's receiver does not address.
    #[error("the fibre's receiver does not address the contact {pair:?}")]
    ContactNotAddressed {
        /// The contact asked for.
        pair: (u32, u32),
    },
    /// A clock name was recorded twice, so the receipt would carry two readings of one clock.
    #[error("the {clock} clock is recorded twice")]
    ClockRepeated {
        /// Which clock.
        clock: &'static str,
    },
    /// A run receipt was finished with no end-to-end clock.
    #[error("a run receipt names its end_to_end clock; this one records {recorded} clock(s) and not that one")]
    EndToEndClockAbsent {
        /// How many clocks were recorded.
        recorded: usize,
    },
    /// The standing owner refused. Its refusal is rendered rather than carried, because
    /// `StandingRefusal` is neither `Clone` nor `Eq` and this family is both.
    #[error("the standing owner refused: {detail}")]
    Standing {
        /// That owner's refusal, rendered.
        detail: String,
    },
}

// -------------------------------------------------------------------------------------------
// The lineage relation and its classes
// -------------------------------------------------------------------------------------------

/// **A declared edit radius**: how many mutation passages may join two designs of one lineage
/// class.
///
/// [definition] Its fields are private and [`EditRadius::declare`] refuses an unstated ground and a
/// radius above [`EDIT_RADIUS_CEILING`]. A radius of `0` is admitted and means exactly what it
/// says: every design is its own lineage, and the leakage law then has nothing to catch. That is a
/// declaration a caller may make, with a ground, and never a default.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EditRadius {
    sites: usize,
    ground: String,
}

impl EditRadius {
    /// Declare the radius. Refuses an unstated ground and a radius above the ceiling.
    pub fn declare(sites: usize, ground: impl Into<String>) -> Result<Self, EvaluationRefusal> {
        let ground = ground.into();
        if ground.trim().is_empty() {
            return Err(EvaluationRefusal::NotStated {
                what: "edit radius ground",
            });
        }
        if sites > EDIT_RADIUS_CEILING {
            return Err(EvaluationRefusal::EditRadiusTooLarge {
                declared: sites,
                ceiling: EDIT_RADIUS_CEILING,
            });
        }
        Ok(Self { sites, ground })
    }

    /// How many sites two designs of one class may differ at.
    pub const fn sites(&self) -> usize {
        self.sites
    }

    /// The ground the radius is declared on.
    pub fn ground(&self) -> &str {
        &self.ground
    }
}

/// One edge of the lineage graph, with the evidence that founds it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum LineageEdge {
    /// An admitted horizontal mutation passage, built by
    /// [`crate::design_selection::DesignFamily::admit_mutation`] and therefore checked by
    /// [`crate::physical_occurrence::Passage::mutation`]'s own evidence law.
    Passage {
        /// One design.
        left: DesignId,
        /// The other.
        right: DesignId,
        /// The site the mutation changes.
        site: u32,
        /// The declared environment both sit at.
        environment: usize,
    },
    /// The two objects' monomer sequences differ at these sites, at most the declared radius many.
    /// The site list **is** the chain of single-site mutation passages that joins them in sequence
    /// space, whether or not the family carries a face for each intermediate.
    EditDistance {
        /// One design.
        left: DesignId,
        /// The other.
        right: DesignId,
        /// The one-based sites they differ at.
        sites: Vec<u32>,
    },
}

impl LineageEdge {
    /// Its two endpoints.
    pub const fn endpoints(&self) -> (DesignId, DesignId) {
        match self {
            Self::Passage { left, right, .. } | Self::EditDistance { left, right, .. } => {
                (*left, *right)
            }
        }
    }

    /// How many single-site mutations the edge stands for.
    pub fn steps(&self) -> usize {
        match self {
            Self::Passage { .. } => 1,
            Self::EditDistance { sites, .. } => sites.len(),
        }
    }

    /// A short rendering, for a refusal.
    pub fn render(&self) -> String {
        match self {
            Self::Passage {
                left,
                right,
                site,
                environment,
            } => format!(
                "passage {left:?} -> {right:?} at site {site}, environment index {environment}"
            ),
            Self::EditDistance { left, right, sites } => {
                format!("{left:?} -> {right:?} differing at sites {sites:?}")
            }
        }
    }
}

/// **The leak**: two lineage-equivalent designs on opposite sides of a split, with the chain that
/// joins them.
///
/// Lean counterpart: `Foundation/EvaluationDiscipline.lean::Straddles`, whose witness
/// `rawSplit_straddles` is this value.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LineageStraddle {
    /// The development-side design.
    pub development: DesignId,
    /// The evaluation-side design.
    pub evaluation: DesignId,
    /// The class they share.
    pub class: usize,
    /// The connecting chain of mutation passages, in order.
    pub chain: Vec<LineageEdge>,
}

impl LineageStraddle {
    /// The chain, rendered for a refusal.
    pub fn render(&self) -> String {
        self.chain
            .iter()
            .map(LineageEdge::render)
            .collect::<Vec<_>>()
            .join("; ")
    }
}

/// **The quotient of a design population by the lineage relation.**
///
/// [definition] The relation is generated by the horizontal mutation passages of
/// [`crate::physical_occurrence::passage`]: an admitted `Passage<Horizontal>` is one edge, and two
/// designs whose monomer sequences differ at no more than the declared [`EditRadius`] many sites
/// are joined by the chain of single-site mutations those sites name. The classes are the connected
/// components of that graph, which is the quotient by the relation's reflexive-symmetric-transitive
/// closure.
///
/// `Deserialize` is deliberately not derived: the classes are founded through
/// [`LineageClasses::found`] and never remounted past its checks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LineageClasses {
    /// The schema this quotient serializes under.
    pub schema: String,
    radius: EditRadius,
    population: Vec<DesignId>,
    class_of: BTreeMap<DesignId, usize>,
    classes: Vec<Vec<DesignId>>,
    edges: Vec<LineageEdge>,
}

impl LineageClasses {
    /// **Found the quotient** from a design family, the admitted horizontal mutations and a
    /// declared edit radius.
    ///
    /// Refuses an empty family, a population above [`POPULATION_CEILING`], a comparison count above
    /// [`COMPARISON_CEILING`] and a mutation naming a design the family does not carry.
    pub fn found(
        family: &DesignFamily,
        mutations: &[AdmittedTransformation],
        radius: EditRadius,
    ) -> Result<Self, EvaluationRefusal> {
        let designs = family.designs();
        if designs.is_empty() {
            return Err(EvaluationRefusal::EmptyPopulation);
        }
        if designs.len() > POPULATION_CEILING {
            return Err(EvaluationRefusal::PopulationTooLarge {
                declared: designs.len(),
                ceiling: POPULATION_CEILING,
            });
        }
        let sites = designs
            .iter()
            .map(|design| design.object().left_sequence.len())
            .max()
            .unwrap_or(0);
        // The pair loop below compares two sequences site by site, so the work is
        // `pairs · sites`. It is computed with checked arithmetic before the loop runs.
        let pairs = designs
            .len()
            .checked_mul(designs.len().saturating_sub(1))
            .map(|product| product / 2);
        let implied = pairs
            .and_then(|pairs| pairs.checked_mul(sites.max(1)))
            .unwrap_or(usize::MAX);
        if implied > COMPARISON_CEILING {
            return Err(EvaluationRefusal::ComparisonPopulationTooLarge {
                implied,
                designs: designs.len(),
                sites,
                ceiling: COMPARISON_CEILING,
            });
        }

        let population: Vec<DesignId> = designs.iter().map(|design| design.id).collect();
        let mut edges: Vec<LineageEdge> = Vec::new();

        // The admitted mutation passages. `AdmittedTransformation`'s fields are public, so a value
        // that did not come from `admit_mutation` can name an index the family does not carry;
        // every index is checked here, before an edge is founded.
        for transformation in mutations {
            if let AdmittedTransformation::Mutation {
                from,
                to,
                environment,
                site,
            } = transformation
            {
                for at in [from, to] {
                    if *at >= designs.len() {
                        return Err(EvaluationRefusal::MutationNamesAnAbsentDesign {
                            index: *at,
                            declared: designs.len(),
                        });
                    }
                }
                if *environment >= family.environments().len() {
                    return Err(EvaluationRefusal::MutationNamesAnAbsentEnvironment {
                        index: *environment,
                        declared: family.environments().len(),
                    });
                }
                family
                    .validate_mutation(*from, *to, *environment, *site)
                    .map_err(|refusal| match refusal {
                        crate::design_selection::SelectionRefusal::Passage(error) => {
                            EvaluationRefusal::MutationPassageRefused(error)
                        }
                        _ => EvaluationRefusal::NotStated {
                            what: "mutation declaration",
                        },
                    })?;
                edges.push(LineageEdge::Passage {
                    left: population[*from],
                    right: population[*to],
                    site: *site,
                    environment: *environment,
                });
            }
        }

        // The edit-distance edges: the chain of single-site mutations that joins two objects in
        // sequence space. A changed target component or a changed sequence length is an indel or a
        // different object, which `Passage::mutation` refuses, so neither founds an edge here.
        for (left_at, left) in designs.iter().enumerate() {
            for (offset, right) in designs[left_at + 1..].iter().enumerate() {
                let right_at = left_at + 1 + offset;
                let left_object = left.object();
                let right_object = right.object();
                if left_object.right_sequence != right_object.right_sequence {
                    continue;
                }
                if left_object.left_sequence.len() != right_object.left_sequence.len() {
                    continue;
                }
                let differing: Vec<u32> = left_object
                    .left_sequence
                    .iter()
                    .zip(&right_object.left_sequence)
                    .enumerate()
                    .filter(|(_, (a, b))| a != b)
                    .map(|(at, _)| at as u32 + 1)
                    .collect();
                if !differing.is_empty() && differing.len() <= radius.sites() {
                    edges.push(LineageEdge::EditDistance {
                        left: population[left_at],
                        right: population[right_at],
                        sites: differing,
                    });
                }
            }
        }

        // The connected components, by union-find over the edges.
        let index: BTreeMap<DesignId, usize> = population
            .iter()
            .enumerate()
            .map(|(at, id)| (*id, at))
            .collect();
        let mut parent: Vec<usize> = (0..population.len()).collect();
        fn root(parent: &mut [usize], mut at: usize) -> usize {
            while parent[at] != at {
                parent[at] = parent[parent[at]];
                at = parent[at];
            }
            at
        }
        for edge in &edges {
            let (left, right) = edge.endpoints();
            let (Some(left), Some(right)) = (index.get(&left), index.get(&right)) else {
                continue;
            };
            let (a, b) = (root(&mut parent, *left), root(&mut parent, *right));
            if a != b {
                parent[a] = b;
            }
        }
        let mut grouped: BTreeMap<usize, Vec<DesignId>> = BTreeMap::new();
        for (at, id) in population.iter().enumerate() {
            let component = root(&mut parent, at);
            grouped.entry(component).or_default().push(*id);
        }
        let mut classes: Vec<Vec<DesignId>> = grouped
            .into_values()
            .map(|mut members| {
                members.sort_unstable();
                members
            })
            .collect();
        classes.sort();
        let mut class_of = BTreeMap::new();
        for (at, class) in classes.iter().enumerate() {
            for id in class {
                class_of.insert(*id, at);
            }
        }

        Ok(Self {
            schema: "holonic-engine.lineage-classes.v1".to_owned(),
            radius,
            population,
            class_of,
            classes,
            edges,
        })
    }

    /// The declared radius.
    pub const fn radius(&self) -> &EditRadius {
        &self.radius
    }

    /// The population, in the family's declaration order.
    pub fn population(&self) -> &[DesignId] {
        &self.population
    }

    /// The classes, each sorted by identity, in ascending order of their first member.
    pub fn classes(&self) -> &[Vec<DesignId>] {
        &self.classes
    }

    /// The edges that founded the relation.
    pub fn edges(&self) -> &[LineageEdge] {
        &self.edges
    }

    /// The class of one design.
    ///
    /// Lean counterpart: `Lineage.cls`.
    pub fn class_of(&self, id: DesignId) -> Result<usize, EvaluationRefusal> {
        self.class_of
            .get(&id)
            .copied()
            .ok_or(EvaluationRefusal::DesignAbsent { id })
    }

    /// **Whether two designs are one lineage class.**
    ///
    /// Lean counterpart: `Lineage.cls_eq_of_rel` and `Lineage.rel_of_cls_eq`, which are the two
    /// directions of this equality.
    pub fn related(&self, left: DesignId, right: DesignId) -> Result<bool, EvaluationRefusal> {
        Ok(self.class_of(left)? == self.class_of(right)?)
    }

    /// **The connecting chain between two designs of one class**, shortest first, or `None` when
    /// they are not related.
    ///
    /// The walk is a breadth-first search over a graph whose node and edge counts were bounded at
    /// founding, so nothing here is sized by an unchecked declaration.
    pub fn chain_between(
        &self,
        left: DesignId,
        right: DesignId,
    ) -> Result<Option<Vec<LineageEdge>>, EvaluationRefusal> {
        self.class_of(left)?;
        self.class_of(right)?;
        if left == right {
            return Ok(Some(Vec::new()));
        }
        let mut adjacency: BTreeMap<DesignId, Vec<usize>> = BTreeMap::new();
        for (at, edge) in self.edges.iter().enumerate() {
            let (a, b) = edge.endpoints();
            adjacency.entry(a).or_default().push(at);
            adjacency.entry(b).or_default().push(at);
        }
        let mut seen: BTreeSet<DesignId> = BTreeSet::from([left]);
        let mut came_from: BTreeMap<DesignId, (DesignId, usize)> = BTreeMap::new();
        let mut queue: VecDeque<DesignId> = VecDeque::from([left]);
        while let Some(here) = queue.pop_front() {
            if here == right {
                let mut chain = Vec::new();
                let mut cursor = right;
                while let Some((previous, edge)) = came_from.get(&cursor) {
                    chain.push(self.edges[*edge].clone());
                    cursor = *previous;
                }
                chain.reverse();
                return Ok(Some(chain));
            }
            for at in adjacency.get(&here).into_iter().flatten() {
                let (a, b) = self.edges[*at].endpoints();
                let next = if a == here { b } else { a };
                if seen.insert(next) {
                    came_from.insert(next, (here, *at));
                    queue.push_back(next);
                }
            }
        }
        Ok(None)
    }

    /// **The leak of a raw design split, returned as data.**
    ///
    /// This is the converse witness of [`Split::from_class_partition`]: a split declared on designs
    /// can separate two members of one class, and this returns the first such pair together with
    /// the chain that joins them. [`Split::from_raw_designs`] refuses on exactly this value.
    ///
    /// Lean counterpart: `rawSplit_straddles`.
    pub fn straddle_of(
        &self,
        evaluation: &[DesignId],
    ) -> Result<Option<LineageStraddle>, EvaluationRefusal> {
        let held: BTreeSet<DesignId> = evaluation.iter().copied().collect();
        for id in &held {
            self.class_of(*id)?;
        }
        for (at, class) in self.classes.iter().enumerate() {
            let inside: Vec<DesignId> = class.iter().copied().filter(|id| held.contains(id)).collect();
            let outside: Vec<DesignId> = class
                .iter()
                .copied()
                .filter(|id| !held.contains(id))
                .collect();
            if let (Some(evaluation_side), Some(development_side)) =
                (inside.first(), outside.first())
            {
                let chain = self
                    .chain_between(*development_side, *evaluation_side)?
                    .unwrap_or_default();
                return Ok(Some(LineageStraddle {
                    development: *development_side,
                    evaluation: *evaluation_side,
                    class: at,
                    chain,
                }));
            }
        }
        Ok(None)
    }
}

// -------------------------------------------------------------------------------------------
// The six disciplines, their typed keys, and the split
// -------------------------------------------------------------------------------------------

/// The typed key a discipline splits on. There are exactly six and no seventh.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum KeyAxis {
    /// Which target the design is against.
    Target,
    /// Which interface family the design's contact surface belongs to.
    InterfaceFamily,
    /// Which generator or predictor lineage produced the design.
    GeneratorLineage,
    /// Which assay the reading was taken in.
    Assay,
    /// Which predictor-disagreement class the design's reading falls in.
    DisagreementClass,
    /// Which positive/negative environment pair the design is read across.
    EnvironmentPair,
}

impl KeyAxis {
    /// Every axis, in declaration order.
    pub const ALL: [KeyAxis; 6] = [
        KeyAxis::Target,
        KeyAxis::InterfaceFamily,
        KeyAxis::GeneratorLineage,
        KeyAxis::Assay,
        KeyAxis::DisagreementClass,
        KeyAxis::EnvironmentPair,
    ];

    /// A short name, for receipts and refusals.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Target => "target",
            Self::InterfaceFamily => "interface-family",
            Self::GeneratorLineage => "generator-lineage",
            Self::Assay => "assay",
            Self::DisagreementClass => "disagreement-class",
            Self::EnvironmentPair => "environment-pair",
        }
    }
}

/// **The six evaluation disciplines the plan names.** Each is a declared partition of a design
/// population by one typed [`KeyAxis`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Discipline {
    /// Hold out every design against one target.
    LeaveOneTargetOut,
    /// Hold out one interface family.
    LeaveOneInterfaceFamilyOut,
    /// Hold out one generator or predictor lineage.
    LeaveOneGeneratorOut,
    /// Calibrate within one assay and evaluate outside it.
    AssaySpecificCalibration,
    /// Evaluate on the subset the predictors disagree about.
    PredictorDisagreementSubset,
    /// Evaluate on a declared positive/negative environment pair.
    PositiveNegativeEnvironmentPair,
}

impl Discipline {
    /// Every discipline, in the plan's order.
    pub const ALL: [Discipline; 6] = [
        Discipline::LeaveOneTargetOut,
        Discipline::LeaveOneInterfaceFamilyOut,
        Discipline::LeaveOneGeneratorOut,
        Discipline::AssaySpecificCalibration,
        Discipline::PredictorDisagreementSubset,
        Discipline::PositiveNegativeEnvironmentPair,
    ];

    /// The axis it splits on.
    pub const fn axis(self) -> KeyAxis {
        match self {
            Self::LeaveOneTargetOut => KeyAxis::Target,
            Self::LeaveOneInterfaceFamilyOut => KeyAxis::InterfaceFamily,
            Self::LeaveOneGeneratorOut => KeyAxis::GeneratorLineage,
            Self::AssaySpecificCalibration => KeyAxis::Assay,
            Self::PredictorDisagreementSubset => KeyAxis::DisagreementClass,
            Self::PositiveNegativeEnvironmentPair => KeyAxis::EnvironmentPair,
        }
    }

    /// A short name, for receipts and refusals.
    pub const fn label(self) -> &'static str {
        match self {
            Self::LeaveOneTargetOut => "leave-one-target-out",
            Self::LeaveOneInterfaceFamilyOut => "leave-one-interface-family-out",
            Self::LeaveOneGeneratorOut => "leave-one-generator-out",
            Self::AssaySpecificCalibration => "assay-specific-calibration",
            Self::PredictorDisagreementSubset => "predictor-disagreement-subset",
            Self::PositiveNegativeEnvironmentPair => "positive-negative-environment-pair",
        }
    }
}

/// **The declared typed key of every design at every axis a split will use.**
///
/// [definition] An axis a design does not state is a typed refusal at split time, never a default:
/// a design with no declared target does not silently join the development side.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DesignKeys {
    /// The schema these keys serialize under.
    pub schema: String,
    keys: BTreeMap<(DesignId, KeyAxis), String>,
}

impl DesignKeys {
    /// Declare the keys. Refuses an empty value, a repeated `(design, axis)` and a population above
    /// [`KEY_CEILING`].
    pub fn declare(
        entries: impl IntoIterator<Item = (DesignId, KeyAxis, String)>,
    ) -> Result<Self, EvaluationRefusal> {
        let mut keys: BTreeMap<(DesignId, KeyAxis), String> = BTreeMap::new();
        for (id, axis, value) in entries {
            if value.trim().is_empty() {
                return Err(EvaluationRefusal::NotStated { what: "key value" });
            }
            if keys.len() >= KEY_CEILING {
                return Err(EvaluationRefusal::KeyPopulationTooLarge {
                    declared: keys.len() + 1,
                    ceiling: KEY_CEILING,
                });
            }
            if keys.insert((id, axis), value).is_some() {
                return Err(EvaluationRefusal::KeyRepeated {
                    id,
                    axis: axis.label(),
                });
            }
        }
        Ok(Self {
            schema: "holonic-engine.design-keys.v1".to_owned(),
            keys,
        })
    }

    /// The value one design states at one axis, or a typed refusal naming the discipline that
    /// needed it.
    pub fn value(
        &self,
        id: DesignId,
        axis: KeyAxis,
        discipline: Discipline,
    ) -> Result<&str, EvaluationRefusal> {
        self.keys
            .get(&(id, axis))
            .map(String::as_str)
            .ok_or(EvaluationRefusal::KeyNotStated {
                id,
                axis: axis.label(),
                discipline: discipline.label(),
            })
    }
}

/// **A declared split of a design population into a development side and an evaluation side.**
///
/// [definition] Its fields are private and there are exactly three constructors. Two of them —
/// [`Split::from_class_partition`] and [`Split::leave_one_out`] — take or produce a partition of
/// **lineage classes**, so a straddle is structurally impossible. The third,
/// [`Split::from_raw_designs`], takes designs and refuses a straddle by name.
///
/// `Deserialize` is not derived: a remount would be a fourth constructor bypassing those checks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Split {
    /// The schema this split serializes under.
    pub schema: String,
    discipline: Discipline,
    held_out: String,
    development: Vec<DesignId>,
    evaluation: Vec<DesignId>,
    development_classes: Vec<usize>,
    evaluation_classes: Vec<usize>,
}

impl Split {
    /// **The structural constructor: a partition of lineage classes.**
    ///
    /// A side is a union of whole classes, so no chain of mutation passages crosses the split. That
    /// is `Foundation/EvaluationDiscipline.lean::ofClassPredicate_does_not_straddle`, and it holds
    /// by construction rather than by a check.
    pub fn from_class_partition(
        classes: &LineageClasses,
        discipline: Discipline,
        held_out: impl Into<String>,
        evaluation_classes: &[usize],
    ) -> Result<Self, EvaluationRefusal> {
        let held_out = held_out.into();
        if held_out.trim().is_empty() {
            return Err(EvaluationRefusal::NotStated {
                what: "held-out value",
            });
        }
        let mut chosen: BTreeSet<usize> = BTreeSet::new();
        for index in evaluation_classes {
            if *index >= classes.classes().len() {
                return Err(EvaluationRefusal::ClassAbsent {
                    index: *index,
                    declared: classes.classes().len(),
                });
            }
            if !chosen.insert(*index) {
                return Err(EvaluationRefusal::ClassRepeated { index: *index });
            }
        }
        let development_classes: Vec<usize> = (0..classes.classes().len())
            .filter(|index| !chosen.contains(index))
            .collect();
        if chosen.is_empty() {
            return Err(EvaluationRefusal::EmptySide { side: "evaluation" });
        }
        if development_classes.is_empty() {
            return Err(EvaluationRefusal::EmptySide {
                side: "development",
            });
        }
        let expand = |indices: &[usize]| -> Vec<DesignId> {
            let mut out: Vec<DesignId> = indices
                .iter()
                .flat_map(|index| classes.classes()[*index].iter().copied())
                .collect();
            out.sort_unstable();
            out
        };
        let evaluation_classes: Vec<usize> = chosen.into_iter().collect();
        Ok(Self {
            schema: "holonic-engine.evaluation-split.v1".to_owned(),
            discipline,
            held_out,
            development: expand(&development_classes),
            evaluation: expand(&evaluation_classes),
            development_classes,
            evaluation_classes,
        })
    }

    /// **The leave-one-out constructor, by a typed key, lifted to lineage classes.**
    ///
    /// The evaluation side is every design whose declared key at the discipline's axis equals
    /// `held_out`. That set must be a **union of lineage classes**: a class carrying both a
    /// held-out design and another is [`EvaluationRefusal::SplitStraddlesALineageClass`], naming
    /// the pair and the connecting chain. This is where the leakage law bites on real material,
    /// because a key and a lineage are two different declarations and nothing makes them agree.
    pub fn leave_one_out(
        classes: &LineageClasses,
        keys: &DesignKeys,
        discipline: Discipline,
        held_out: &str,
    ) -> Result<Self, EvaluationRefusal> {
        if held_out.trim().is_empty() {
            return Err(EvaluationRefusal::NotStated {
                what: "held-out value",
            });
        }
        let axis = discipline.axis();
        let mut evaluation: Vec<DesignId> = Vec::new();
        for id in classes.population() {
            if keys.value(*id, axis, discipline)? == held_out {
                evaluation.push(*id);
            }
        }
        if evaluation.is_empty() {
            return Err(EvaluationRefusal::HeldOutValueAbsent {
                axis: axis.label(),
                held_out: held_out.to_owned(),
            });
        }
        Self::from_raw_designs(classes, discipline, held_out, &evaluation)
    }

    /// **The raw constructor**, which takes designs and refuses a straddle.
    ///
    /// The refusal names the pair and the connecting chain of mutation passages, which is the leak
    /// itself rather than a message about one.
    pub fn from_raw_designs(
        classes: &LineageClasses,
        discipline: Discipline,
        held_out: impl Into<String>,
        evaluation: &[DesignId],
    ) -> Result<Self, EvaluationRefusal> {
        let held_out = held_out.into();
        let mut seen: BTreeSet<DesignId> = BTreeSet::new();
        for id in evaluation {
            classes.class_of(*id)?;
            if !seen.insert(*id) {
                return Err(EvaluationRefusal::DesignRepeated { id: *id });
            }
        }
        if let Some(straddle) = classes.straddle_of(evaluation)? {
            return Err(EvaluationRefusal::SplitStraddlesALineageClass {
                left: straddle.development,
                right: straddle.evaluation,
                class: straddle.class,
                steps: straddle.chain.iter().map(LineageEdge::steps).sum(),
                chain: straddle.render(),
            });
        }
        // Nothing straddles, so the evaluation side *is* a union of whole classes and the split can
        // be founded through the structural constructor, which cannot straddle at all.
        let mut evaluation_classes: Vec<usize> = Vec::new();
        for id in evaluation {
            let class = classes.class_of(*id)?;
            if !evaluation_classes.contains(&class) {
                evaluation_classes.push(class);
            }
        }
        Self::from_class_partition(classes, discipline, held_out, &evaluation_classes)
    }

    /// Which discipline this split enacts.
    pub const fn discipline(&self) -> Discipline {
        self.discipline
    }

    /// The held-out key value.
    pub fn held_out(&self) -> &str {
        &self.held_out
    }

    /// The development-side designs, in ascending identity order.
    pub fn development(&self) -> &[DesignId] {
        &self.development
    }

    /// The evaluation-side designs, in ascending identity order.
    pub fn evaluation(&self) -> &[DesignId] {
        &self.evaluation
    }

    /// The lineage classes on the development side.
    pub fn development_classes(&self) -> &[usize] {
        &self.development_classes
    }

    /// The lineage classes on the evaluation side.
    pub fn evaluation_classes(&self) -> &[usize] {
        &self.evaluation_classes
    }

    /// A name for this split, which is the scope every conclusion drawn from it carries.
    pub fn name(&self) -> String {
        format!("{} holding out {:?}", self.discipline.label(), self.held_out)
    }

    /// Whether this split separates two designs of one lineage class. **Always false**: the two
    /// structural constructors cannot produce one and the raw constructor refuses one. It is
    /// checked rather than asserted, so a future constructor cannot quietly break the law.
    pub fn straddles(&self, classes: &LineageClasses) -> Result<bool, EvaluationRefusal> {
        Ok(classes.straddle_of(&self.evaluation)?.is_some())
    }
}

// -------------------------------------------------------------------------------------------
// Leakage through receivers
// -------------------------------------------------------------------------------------------

mod admission {
    use super::{DesignId, OccurrenceId};

    /// **The token a [`super::ReceiverAdmission`] is made of.**
    ///
    /// [definition] Its fields are private to this module and its only constructor is
    /// `pub(super)`, so no struct literal of this type can be written anywhere. An admission to
    /// read a fitted receiver at an occurrence is therefore obtainable only by calling
    /// [`super::FittedReceiver::evaluate_at`], which checked the leakage law. This is
    /// `receiver_atlas`'s `Recomputed` pattern.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct ReceiverAdmission {
        receiver: String,
        design: DesignId,
        occurrence: OccurrenceId,
    }

    impl ReceiverAdmission {
        pub(super) fn by(receiver: String, design: DesignId, occurrence: OccurrenceId) -> Self {
            Self {
                receiver,
                design,
                occurrence,
            }
        }

        /// Which receiver was admitted.
        pub fn receiver(&self) -> &str {
            &self.receiver
        }

        /// Which design it was admitted at.
        pub const fn design(&self) -> DesignId {
            self.design
        }

        /// Which occurrence it was admitted at.
        pub const fn occurrence(&self) -> OccurrenceId {
            self.occurrence
        }
    }
}

pub use admission::ReceiverAdmission;

/// **A fitted or calibrated receiver, carrying the material it was fitted on.**
///
/// [definition] AGENTS.md: *a driver may not select developmental material from an evaluation
/// target.* A receiver fitted on development-side faces and read on evaluation-side faces is that
/// selection, even when no design crosses the split. This type makes the fitting set part of the
/// receiver, and [`FittedReceiver::evaluate_at`] refuses an evaluation at an occurrence it was
/// fitted on or at a design lineage-equivalent to one it was fitted on.
///
/// `Deserialize` and `Default` are not derived: a remounted receiver with an empty fitting set
/// would be a receiver that claims to have been fitted on nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FittedReceiver {
    /// The schema this receiver serializes under.
    pub schema: String,
    name: String,
    assay: String,
    ground: String,
    fitted_designs: BTreeSet<DesignId>,
    fitted_occurrences: BTreeSet<OccurrenceId>,
}

impl FittedReceiver {
    /// Declare a fitted receiver. Refuses an empty name, assay or ground, an empty fitting set —
    /// a receiver fitted on nothing is not fitted — and a fitting set above [`FITTING_CEILING`].
    pub fn fitted(
        name: impl Into<String>,
        assay: impl Into<String>,
        ground: impl Into<String>,
        designs: impl IntoIterator<Item = DesignId>,
        occurrences: impl IntoIterator<Item = OccurrenceId>,
    ) -> Result<Self, EvaluationRefusal> {
        let name = name.into();
        let assay = assay.into();
        let ground = ground.into();
        for (value, what) in [
            (&name, "fitted receiver name"),
            (&assay, "fitted receiver assay"),
            (&ground, "fitted receiver ground"),
        ] {
            if value.trim().is_empty() {
                return Err(EvaluationRefusal::NotStated { what });
            }
        }
        // The two fitting sets come from caller iterators, so they are bounded **as they are
        // collected** rather than after: a ceiling checked on a materialized collection is not a
        // bound on the allocation that materialized it.
        let mut fitted_designs: BTreeSet<DesignId> = BTreeSet::new();
        for id in designs {
            if fitted_designs.len() >= FITTING_CEILING {
                return Err(EvaluationRefusal::FittingSetTooLarge {
                    receiver: name,
                    declared: fitted_designs.len() + 1,
                    ceiling: FITTING_CEILING,
                });
            }
            fitted_designs.insert(id);
        }
        let mut fitted_occurrences: BTreeSet<OccurrenceId> = BTreeSet::new();
        for occurrence in occurrences {
            if fitted_designs.len() + fitted_occurrences.len() >= FITTING_CEILING {
                return Err(EvaluationRefusal::FittingSetTooLarge {
                    receiver: name,
                    declared: fitted_designs.len() + fitted_occurrences.len() + 1,
                    ceiling: FITTING_CEILING,
                });
            }
            fitted_occurrences.insert(occurrence);
        }
        if fitted_designs.is_empty() && fitted_occurrences.is_empty() {
            return Err(EvaluationRefusal::EmptyPopulation);
        }
        Ok(Self {
            schema: "holonic-engine.fitted-receiver.v1".to_owned(),
            name,
            assay,
            ground,
            fitted_designs,
            fitted_occurrences,
        })
    }

    /// Its declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The assay it was fitted within.
    pub fn assay(&self) -> &str {
        &self.assay
    }

    /// The ground it is declared on.
    pub fn ground(&self) -> &str {
        &self.ground
    }

    /// The designs it was fitted on.
    pub fn fitted_designs(&self) -> &BTreeSet<DesignId> {
        &self.fitted_designs
    }

    /// The occurrences it was fitted on.
    pub fn fitted_occurrences(&self) -> &BTreeSet<OccurrenceId> {
        &self.fitted_occurrences
    }

    /// **Read this receiver at an evaluation-side occurrence, or refuse.**
    ///
    /// Refuses at an occurrence it was fitted on, and at a design lineage-equivalent to one it was
    /// fitted on. Success returns a [`ReceiverAdmission`], whose only constructor is this function,
    /// so an admission cannot be forged.
    ///
    /// Lean counterpart: `evaluateAt`, with `evaluateAt_refuses_a_fitted_occurrence`,
    /// `evaluateAt_refuses_a_lineage_equivalent_occurrence` and
    /// `evaluateAt_admits_when_nothing_leaks`.
    pub fn evaluate_at(
        &self,
        classes: &LineageClasses,
        design: DesignId,
        occurrence: OccurrenceId,
    ) -> Result<ReceiverAdmission, EvaluationRefusal> {
        if self.fitted_occurrences.contains(&occurrence) {
            return Err(EvaluationRefusal::ReceiverFittedOnThisOccurrence {
                receiver: self.name.clone(),
                occurrence,
            });
        }
        let class = classes.class_of(design)?;
        for fitted in &self.fitted_designs {
            // A design the receiver was fitted on that this evaluation does not carry cannot be
            // lineage-equivalent to anything in it, so it is skipped rather than refused.
            let Ok(fitted_class) = classes.class_of(*fitted) else {
                continue;
            };
            if fitted_class == class {
                let steps = classes
                    .chain_between(*fitted, design)?
                    .map(|chain| chain.iter().map(LineageEdge::steps).sum())
                    .unwrap_or(0);
                return Err(EvaluationRefusal::ReceiverFittedOnALineageEquivalentDesign {
                    receiver: self.name.clone(),
                    fitted: *fitted,
                    evaluated: design,
                    class,
                    steps,
                });
            }
        }
        Ok(ReceiverAdmission::by(self.name.clone(), design, occurrence))
    }
}

// -------------------------------------------------------------------------------------------
// Assay-specific calibration
// -------------------------------------------------------------------------------------------

/// **A declared bridge between two assays**, with the ground it is declared on.
///
/// [definition] The assay analogue of [`crate::physical_occurrence::EnvironmentPassage`]: nothing
/// crosses without one, and a bridge between one assay and itself is refused because it states
/// nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssayBridge {
    /// The schema this bridge serializes under.
    pub schema: String,
    name: String,
    source: String,
    target: String,
    ground: String,
}

impl AssayBridge {
    /// Declare a bridge. Refuses an empty name, assay or ground, and a bridge from an assay to
    /// itself.
    pub fn declare(
        name: impl Into<String>,
        source: impl Into<String>,
        target: impl Into<String>,
        ground: impl Into<String>,
    ) -> Result<Self, EvaluationRefusal> {
        let name = name.into();
        let source = source.into();
        let target = target.into();
        let ground = ground.into();
        for (value, what) in [
            (&name, "assay bridge name"),
            (&source, "assay bridge source"),
            (&target, "assay bridge target"),
            (&ground, "assay bridge ground"),
        ] {
            if value.trim().is_empty() {
                return Err(EvaluationRefusal::NotStated { what });
            }
        }
        if source == target {
            return Err(EvaluationRefusal::BridgeIsCircular { assay: source });
        }
        Ok(Self {
            schema: "holonic-engine.assay-bridge.v1".to_owned(),
            name,
            source,
            target,
            ground,
        })
    }

    /// Its declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The assay it leaves.
    pub fn source(&self) -> &str {
        &self.source
    }

    /// The assay it arrives at.
    pub fn target(&self) -> &str {
        &self.target
    }

    /// The ground it is declared on.
    pub fn ground(&self) -> &str {
        &self.ground
    }
}

/// **A calibration: a receiver-to-receiver map fitted within one assay.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Calibration {
    /// The schema this calibration serializes under.
    pub schema: String,
    name: String,
    assay: String,
    from_receiver: String,
    to_receiver: String,
    ground: String,
}

/// **An admitted transport of a calibration to an assay.**
///
/// [definition] Its fields are private and its only constructor is [`Calibration::carry_to`], so a
/// caller cannot hold a transport the law did not license.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CalibrationTransport {
    calibration: String,
    at_assay: String,
    bridge: Option<String>,
}

impl CalibrationTransport {
    /// Which calibration.
    pub fn calibration(&self) -> &str {
        &self.calibration
    }

    /// The assay it was admitted at.
    pub fn at_assay(&self) -> &str {
        &self.at_assay
    }

    /// The bridge that licensed the crossing, when the transport crossed an assay.
    pub fn bridge(&self) -> Option<&str> {
        self.bridge.as_deref()
    }
}

impl Calibration {
    /// Declare a calibration fitted within one assay. Refuses an empty declaration anywhere.
    pub fn fitted_within(
        name: impl Into<String>,
        assay: impl Into<String>,
        from_receiver: impl Into<String>,
        to_receiver: impl Into<String>,
        ground: impl Into<String>,
    ) -> Result<Self, EvaluationRefusal> {
        let name = name.into();
        let assay = assay.into();
        let from_receiver = from_receiver.into();
        let to_receiver = to_receiver.into();
        let ground = ground.into();
        for (value, what) in [
            (&name, "calibration name"),
            (&assay, "calibration assay"),
            (&from_receiver, "calibration source receiver"),
            (&to_receiver, "calibration target receiver"),
            (&ground, "calibration ground"),
        ] {
            if value.trim().is_empty() {
                return Err(EvaluationRefusal::NotStated { what });
            }
        }
        Ok(Self {
            schema: "holonic-engine.assay-calibration.v1".to_owned(),
            name,
            assay,
            from_receiver,
            to_receiver,
            ground,
        })
    }

    /// Its declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The assay it was fitted within.
    pub fn assay(&self) -> &str {
        &self.assay
    }

    /// The receiver it reads.
    pub fn from_receiver(&self) -> &str {
        &self.from_receiver
    }

    /// The receiver it produces.
    pub fn to_receiver(&self) -> &str {
        &self.to_receiver
    }

    /// The ground it is declared on.
    pub fn ground(&self) -> &str {
        &self.ground
    }

    /// **Carry the calibration to an assay.**
    ///
    /// Inside its own assay it needs no bridge. Across assays it is refused unless a bridge that
    /// actually joins the two is supplied — the same law
    /// [`crate::physical_occurrence::EnvironmentPassage`] imposes on environments.
    ///
    /// Lean counterpart: `transport`, with `within_one_assay_needs_no_bridge`,
    /// `across_assays_without_a_bridge_is_refused`, `across_assays_with_a_bridge_is_admitted` and
    /// `a_bridge_between_other_assays_is_refused`.
    pub fn carry_to(
        &self,
        assay: &str,
        bridge: Option<&AssayBridge>,
    ) -> Result<CalibrationTransport, EvaluationRefusal> {
        if assay == self.assay {
            return Ok(CalibrationTransport {
                calibration: self.name.clone(),
                at_assay: assay.to_owned(),
                bridge: None,
            });
        }
        let Some(bridge) = bridge else {
            return Err(EvaluationRefusal::CalibrationCrossesAssaysWithoutABridge {
                calibration: self.name.clone(),
                fitted: self.assay.clone(),
                asked: assay.to_owned(),
            });
        };
        if bridge.source() != self.assay || bridge.target() != assay {
            return Err(EvaluationRefusal::BridgeJoinsOtherAssays(Box::new(
                BridgeMismatch {
                    bridge: bridge.name().to_owned(),
                    bridge_source: bridge.source().to_owned(),
                    bridge_target: bridge.target().to_owned(),
                    calibration: self.name.clone(),
                    fitted: self.assay.clone(),
                    asked: assay.to_owned(),
                },
            )));
        }
        Ok(CalibrationTransport {
            calibration: self.name.clone(),
            at_assay: assay.to_owned(),
            bridge: Some(bridge.name().to_owned()),
        })
    }
}

// -------------------------------------------------------------------------------------------
// A wet or external return is a new receiver occurrence
// -------------------------------------------------------------------------------------------

/// **One exact reading carried at a declared time.**
///
/// [definition] The time is carried by [`crate::standing::TimedFace`], that owner's own object, so
/// there is one owner of "a face at a time" and this module founds no second one. The reading's two
/// exact rational endpoints are the face; a point interval is a decided reading and a wide one
/// stays plural.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimedReading {
    face: TimedFace,
    reading: ExactInterval,
    receiver: String,
}

impl TimedReading {
    /// Declare a reading at a time. Refuses an [`ReceiverReading::Unread`] axis: an unread return
    /// is not a return.
    pub fn declared(
        receiver: impl Into<String>,
        time: usize,
        reading: &ReceiverReading,
    ) -> Result<Self, EvaluationRefusal> {
        let receiver = receiver.into();
        if receiver.trim().is_empty() {
            return Err(EvaluationRefusal::NotStated {
                what: "timed reading receiver",
            });
        }
        let interval = match reading {
            ReceiverReading::Read(interval) => interval.clone(),
            ReceiverReading::Unread(why) => {
                return Err(EvaluationRefusal::ExternalReturnIsUnread {
                    receiver,
                    why: why.statement().to_owned(),
                });
            }
        };
        let face = TimedFace::declared(time, vec![interval.lower.clone(), interval.upper.clone()])
            .map_err(|refusal| EvaluationRefusal::Standing {
                detail: refusal.to_string(),
            })?;
        Ok(Self {
            face,
            reading: interval,
            receiver,
        })
    }

    /// The time it occurs at.
    pub fn occurs_at(&self) -> usize {
        self.face.occurs_at()
    }

    /// The exact reading.
    pub const fn reading(&self) -> &ExactInterval {
        &self.reading
    }

    /// The receiver that produced it.
    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    /// The timed face, which is `standing.rs`'s own object.
    pub const fn face(&self) -> &TimedFace {
        &self.face
    }
}

/// **The comparison between an earlier model output and a later wet or external return.**
///
/// [definition] The return is a **new receiver occurrence**. It does not retroactively relabel the
/// earlier prediction: the prediction's face is an occurrence at its own time and
/// [`ExternalComparison::prediction`] returns it unchanged. What the return produces is a *new
/// relation between two occurrences*, stated on a [`Rung`] of
/// [`crate::relation_ladder`] and carrying its own time index. Cited law:
/// `standing.rs::the_available_face_changes_while_the_source_does_not` — the available face changes
/// while the source does not.
///
/// `Deserialize` is not derived and every field is private.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExternalComparison {
    schema: String,
    apparatus: ExteriorDeclaration,
    prediction: TimedReading,
    external_return: TimedReading,
    stated_at: usize,
    rung: Rung,
}

impl ExternalComparison {
    /// **State the comparison.**
    ///
    /// Refuses a return that does not come after the prediction. The rung is *computed* from the
    /// two exact readings and a declared tolerance, never declared: exactly equal readings are
    /// [`Rung::ReceiverEqual`], readings inside the declared tolerance are
    /// [`Rung::WithinTolerance`], and anything else is [`Rung::NoRelation`].
    ///
    /// Lean counterpart: `compare`, with `the_return_does_not_relabel_the_prediction` and
    /// `the_comparison_is_not_at_the_predictions_time`.
    pub fn state(
        apparatus: ExteriorDeclaration,
        prediction: TimedReading,
        external_return: TimedReading,
        tolerance: Option<&ExactInterval>,
    ) -> Result<Self, EvaluationRefusal> {
        if prediction.occurs_at() >= external_return.occurs_at() {
            return Err(EvaluationRefusal::ReturnIsNotLater {
                prediction: prediction.occurs_at(),
                external: external_return.occurs_at(),
            });
        }
        let rung = match compare_values(prediction.reading(), external_return.reading()) {
            ValueOrder::ExactTie => Rung::ReceiverEqual,
            _ => match tolerance {
                // The declared tolerance is an exact interval whose upper endpoint is the aperture:
                // the two readings are within it when the wider of the two gaps does not exceed it.
                Some(tolerance) => {
                    let left = prediction.reading();
                    let right = external_return.reading();
                    let low = if left.lower <= right.lower {
                        &right.lower - &left.lower
                    } else {
                        &left.lower - &right.lower
                    };
                    let high = if left.upper <= right.upper {
                        &right.upper - &left.upper
                    } else {
                        &left.upper - &right.upper
                    };
                    let gap = if low >= high { low } else { high };
                    if gap <= tolerance.upper {
                        Rung::WithinTolerance
                    } else {
                        Rung::NoRelation
                    }
                }
                None => Rung::NoRelation,
            },
        };
        let stated_at = external_return.occurs_at();
        Ok(Self {
            schema: "holonic-engine.external-return-comparison.v1".to_owned(),
            apparatus,
            prediction,
            external_return,
            stated_at,
            rung,
        })
    }

    /// The schema.
    pub fn schema(&self) -> &str {
        &self.schema
    }

    /// The apparatus the external return was taken on, which
    /// [`crate::physical_occurrence::ExteriorDeclaration`] refuses to leave unnamed.
    pub const fn apparatus(&self) -> &ExteriorDeclaration {
        &self.apparatus
    }

    /// **The earlier prediction, unchanged.** Forming the comparison does not touch it.
    pub const fn prediction(&self) -> &TimedReading {
        &self.prediction
    }

    /// The external return: a new receiver occurrence at its own time.
    pub const fn external_return(&self) -> &TimedReading {
        &self.external_return
    }

    /// **When the comparison itself is stated**, which is strictly after the prediction's time.
    pub const fn stated_at(&self) -> usize {
        self.stated_at
    }

    /// The rung this comparison establishes between the two occurrences.
    pub const fn rung(&self) -> Rung {
        self.rung
    }
}

// -------------------------------------------------------------------------------------------
// Predictor disagreement as a fibre property
// -------------------------------------------------------------------------------------------

/// The three disagreement subsets of a plural fibre.
///
/// [definition] `OpenCarrying` takes precedence, exactly as
/// [`crate::physical_occurrence::FibrePartition`] gives it precedence: an undecided reading is
/// never counted as agreement and never counted as separation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum DisagreementClass {
    /// Every member decided it the same way.
    Unanimous,
    /// Members decided it differently.
    Separating,
    /// At least one member left it undecided.
    OpenCarrying,
}

impl DisagreementClass {
    /// A short name, for receipts.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Unanimous => "unanimous",
            Self::Separating => "separating",
            Self::OpenCarrying => "open-carrying",
        }
    }
}

/// **The disagreement subsets of one plural fibre**, defined by that owner's own separator
/// structure rather than by a second law.
///
/// [definition] This is a **return** and carries no invariant: its fields are public and
/// [`DisagreementSubsets::is_a_partition`] is a check a caller runs rather than a promise the type
/// makes. Nothing is licensed by holding one — [`performance_on`], its only consumer here, looks
/// every contact up in the fibre's own addressed population and returns
/// [`EvaluationRefusal::ContactNotAddressed`] for one the fibre does not carry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DisagreementSubsets {
    /// The schema these subsets serialize under.
    pub schema: String,
    /// The members the subsets are read across.
    pub members: Vec<OccurrenceId>,
    /// How many contacts the fibre's receiver addresses.
    pub contacts: usize,
    /// Contacts every member decided the same way.
    pub unanimous: Vec<(u32, u32)>,
    /// Contacts the members decided differently.
    pub separating: Vec<(u32, u32)>,
    /// Contacts at least one member left undecided.
    pub open_carrying: Vec<(u32, u32)>,
}

impl DisagreementSubsets {
    /// The class of one addressed contact.
    pub fn class_of(&self, pair: (u32, u32)) -> Option<DisagreementClass> {
        if self.unanimous.contains(&pair) {
            Some(DisagreementClass::Unanimous)
        } else if self.separating.contains(&pair) {
            Some(DisagreementClass::Separating)
        } else if self.open_carrying.contains(&pair) {
            Some(DisagreementClass::OpenCarrying)
        } else {
            None
        }
    }

    /// The contacts of one subset.
    pub fn subset(&self, class: DisagreementClass) -> &[(u32, u32)] {
        match class {
            DisagreementClass::Unanimous => &self.unanimous,
            DisagreementClass::Separating => &self.separating,
            DisagreementClass::OpenCarrying => &self.open_carrying,
        }
    }

    /// **The three subsets are disjoint and exhaust the addressed contacts.** Checked rather than
    /// asserted.
    pub fn is_a_partition(&self) -> bool {
        let mut all: BTreeSet<(u32, u32)> = BTreeSet::new();
        let mut counted = 0usize;
        for group in [&self.unanimous, &self.separating, &self.open_carrying] {
            counted += group.len();
            for pair in group {
                all.insert(*pair);
            }
        }
        counted == self.contacts && all.len() == self.contacts
    }
}

/// **The disagreement subsets of a plural fibre.**
///
/// [definition] This is [`crate::physical_occurrence::PluralFibre::partition`]'s own four-way
/// partition read as three evaluation subsets: the two unanimous roles are one subset because an
/// evaluation splits on *whether the predictors agree*, not on what they agreed about. Nothing is
/// recomputed.
pub fn disagreement_subsets(fibre: &PluralFibre) -> DisagreementSubsets {
    let partition = fibre.partition();
    let mut unanimous = partition.unanimously_formed.clone();
    unanimous.extend(partition.unanimously_excluded.iter().copied());
    unanimous.sort_unstable();
    DisagreementSubsets {
        schema: "holonic-engine.predictor-disagreement-subsets.v1".to_owned(),
        members: partition.members.clone(),
        contacts: partition.contacts,
        unanimous,
        separating: partition.separating.clone(),
        open_carrying: partition.open_carrying.clone(),
    }
}

/// What a predictor scored on one disagreement subset.
///
/// [definition] A contact counts as *agreeing* only when the predictor's class equals **every**
/// member's decided class there. On a separating contact that is impossible by definition, which is
/// the whole content of the warning: a score read on the unanimous subset says nothing about the
/// separating subset.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SubsetPerformance {
    /// The schema this reading serializes under.
    pub schema: String,
    /// Which subset.
    pub subset: DisagreementClass,
    /// How many contacts the subset carries.
    pub population: usize,
    /// How many the predictor agrees with every member at.
    pub agreeing: usize,
    /// How many it disagrees with at least one member at.
    pub disagreeing: usize,
    /// How many member readings were open and therefore counted on neither side.
    pub carried_open: usize,
}

/// **Score a predictor on one disagreement subset of a fibre.**
///
/// The predictor is a total map from an addressed contact to a [`DecidedClass`]; an open member
/// reading is carried and counted on neither side, exactly as the fibre carries it.
pub fn performance_on(
    fibre: &PluralFibre,
    subsets: &DisagreementSubsets,
    subset: DisagreementClass,
    predictor: &dyn Fn((u32, u32)) -> DecidedClass,
) -> Result<SubsetPerformance, EvaluationRefusal> {
    let addressed: BTreeMap<(u32, u32), usize> = fibre
        .addressed()
        .into_iter()
        .enumerate()
        .map(|(at, pair)| (pair, at))
        .collect();
    let mut agreeing = 0usize;
    let mut disagreeing = 0usize;
    let mut carried_open = 0usize;
    for pair in subsets.subset(subset) {
        let at = *addressed
            .get(pair)
            .ok_or(EvaluationRefusal::ContactNotAddressed { pair: *pair })?;
        let said = predictor(*pair);
        let mut disagrees = false;
        for member in fibre.members() {
            match DecidedClass::of(member.readings[at].class) {
                None => carried_open += 1,
                Some(class) => {
                    if class != said {
                        disagrees = true;
                    }
                }
            }
        }
        if disagrees {
            disagreeing += 1;
        } else {
            agreeing += 1;
        }
    }
    Ok(SubsetPerformance {
        schema: "holonic-engine.disagreement-subset-performance.v1".to_owned(),
        subset,
        population: subsets.subset(subset).len(),
        agreeing,
        disagreeing,
        carried_open,
    })
}

// -------------------------------------------------------------------------------------------
// What an evaluation may conclude
// -------------------------------------------------------------------------------------------

/// **A proof that a bounded evaluation establishes a universal claim.**
///
/// [definition] This enum has **no constructors**. Nothing in this module produces a value of it,
/// exactly as [`crate::physical_occurrence::plural_fibre::RealizationProof`] has none. A held-out
/// result is established at its split and its receiver; its promotion to a universal claim is not a
/// value anything can hold.
///
/// Lean counterpart: `UniversalClaim`, with `universalClaim_is_uninhabited`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UniversalClaim {}

/// **What an evaluation may return.** Three arms and no fourth.
///
/// [definition] Rule 2 of the roadmap: *a bounded search refutes and never affirms.* There is no
/// arm that affirms a generalization, and [`EvaluationConclusion::at_another_split`] returns `None`
/// at any split but the one the conclusion was drawn at.
///
/// Lean counterpart: `Conclusion`, with `a_conclusion_does_not_travel_to_another_split`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum EvaluationConclusion {
    /// Established at this split, read by this receiver, and nowhere else.
    EstablishedBounded {
        /// The split it was established at.
        split: String,
        /// The receiver that read it.
        receiver: String,
        /// How many evaluation-side candidates it was read over.
        population: BigUint,
        /// How many of them agreed.
        agreeing: BigUint,
    },
    /// A generalization claim this split's evidence refutes, with the counterexample.
    GeneralizationRefuted {
        /// The split.
        split: String,
        /// The receiver.
        receiver: String,
        /// The claim that is refuted.
        claim: String,
        /// The counterexample, written out.
        counterexample: String,
    },
    /// Nothing was refuted inside this evaluation. **Its own return**, and not an affirmation.
    NotRefutedWithinThisEvaluation {
        /// The split.
        split: String,
        /// The receiver.
        receiver: String,
        /// The claim that was not refuted here.
        claim: String,
        /// How many evaluation-side candidates it was read over.
        population: BigUint,
    },
}

impl EvaluationConclusion {
    /// **Always `None`**: [`UniversalClaim`] is uninhabited, so no path in this owner turns a
    /// bounded evaluation into a universal one.
    pub const fn universal_claim(&self) -> Option<UniversalClaim> {
        None
    }

    /// The split and receiver this conclusion holds at.
    pub fn scope(&self) -> (&str, &str) {
        match self {
            Self::EstablishedBounded { split, receiver, .. }
            | Self::GeneralizationRefuted { split, receiver, .. }
            | Self::NotRefutedWithinThisEvaluation { split, receiver, .. } => (split, receiver),
        }
    }

    /// **This conclusion at another split**: `None` unless it is the split it was drawn at.
    pub fn at_another_split(&self, other: &str) -> Option<&Self> {
        if self.scope().0 == other { Some(self) } else { None }
    }

    /// A short name, for receipts.
    pub const fn label(&self) -> &'static str {
        match self {
            Self::EstablishedBounded { .. } => "established-bounded",
            Self::GeneralizationRefuted { .. } => "generalization-refuted",
            Self::NotRefutedWithinThisEvaluation { .. } => "not-refuted-within-this-evaluation",
        }
    }
}

/// **Read a held-out result.**
///
/// [definition] The return type encodes rule 2. With no generalization claim supplied, a held-out
/// result is [`EvaluationConclusion::EstablishedBounded`] at this split and this receiver. With a
/// claim supplied, the only two returns are
/// [`EvaluationConclusion::GeneralizationRefuted`] — when some evaluation-side candidate
/// disagrees — and [`EvaluationConclusion::NotRefutedWithinThisEvaluation`]. **There is no return
/// that affirms the claim.**
///
/// The admission is taken by reference so that a conclusion cannot be drawn without one: a
/// [`ReceiverAdmission`] exists only where [`FittedReceiver::evaluate_at`] admitted the reading.
pub fn read_held_out(
    split: &Split,
    admission: &ReceiverAdmission,
    agreeing: usize,
    disagreeing: usize,
    generalization: Option<&str>,
) -> EvaluationConclusion {
    // Two caller-declared counts: their sum is taken in `BigUint`, where it cannot overflow.
    let population = BigUint::from(agreeing) + BigUint::from(disagreeing);
    match generalization {
        None => EvaluationConclusion::EstablishedBounded {
            split: split.name(),
            receiver: admission.receiver().to_owned(),
            population,
            agreeing: BigUint::from(agreeing),
        },
        Some(claim) if disagreeing > 0 => EvaluationConclusion::GeneralizationRefuted {
            split: split.name(),
            receiver: admission.receiver().to_owned(),
            claim: claim.to_owned(),
            counterexample: format!(
                "{disagreeing} of {population} evaluation-side candidates at design {:?} disagree \
                 with the claim at this receiver",
                admission.design()
            ),
        },
        Some(claim) => EvaluationConclusion::NotRefutedWithinThisEvaluation {
            split: split.name(),
            receiver: admission.receiver().to_owned(),
            claim: claim.to_owned(),
            population,
        },
    }
}

// -------------------------------------------------------------------------------------------
// B10: run receipts and named clocks
// -------------------------------------------------------------------------------------------

mod recording {
    /// **The token a [`super::ToolVersion::Read`] is made of.**
    ///
    /// [definition] Its field is private to this module and its only constructor is `pub(super)`,
    /// so no struct literal of this type can be written anywhere. A read version therefore cannot
    /// be *asserted*: the only way to obtain one is to call a reader that actually asked the tool.
    /// A version that cannot be read is [`super::ToolVersion::Unavailable`], which says why.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Recorded {
        how: String,
    }

    impl Recorded {
        pub(super) fn by(how: String) -> Self {
            Self { how }
        }

        /// How the version was read.
        pub fn how(&self) -> &str {
            &self.how
        }
    }
}

pub use recording::Recorded;

/// **A tool's version, read or explicitly unavailable.** Never guessed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ToolVersion {
    /// Read from the tool itself, with the token recording how.
    Read {
        /// The version string the tool reported.
        version: String,
        /// How it was read. The token has no literal.
        recorded: Recorded,
    },
    /// Not readable here, with the reason. This arm **is** writable as a literal, because stating
    /// that a version could not be read is an honest declaration and guessing one is not.
    Unavailable {
        /// Why it could not be read.
        why: String,
    },
}

impl ToolVersion {
    /// The version string, when one was read.
    pub fn version(&self) -> Option<&str> {
        match self {
            Self::Read { version, .. } => Some(version),
            Self::Unavailable { .. } => None,
        }
    }

    /// A rendering for a receipt.
    pub fn render(&self) -> String {
        match self {
            Self::Read { version, recorded } => format!("{version} (read by {})", recorded.how()),
            Self::Unavailable { why } => format!("version unavailable: {why}"),
        }
    }
}

/// Read the version of a Python distribution from a declared interpreter.
///
/// Returns [`ToolVersion::Unavailable`] with the reason on any failure — an absent interpreter, a
/// package name that is not a plain distribution name, a nonzero exit, empty output. The package
/// name is checked to be a plain distribution name before it reaches the child, and the output is
/// truncated at [`VERSION_OUTPUT_CEILING`] bytes before anything is **retained**. The read itself is
/// `std::process::Command::output`'s, which reads the child to end of file: the interpreter is a
/// caller-declared path and this owner does not claim a bound on what a declared interpreter
/// writes.
pub fn python_package_version(interpreter: &Path, package: &str) -> ToolVersion {
    if !package
        .chars()
        .all(|character| character.is_ascii_alphanumeric() || "._-".contains(character))
    {
        return ToolVersion::Unavailable {
            why: format!("{package:?} is not a plain Python distribution name"),
        };
    }
    if !interpreter.is_file() {
        return ToolVersion::Unavailable {
            why: format!("no interpreter at {}", interpreter.display()),
        };
    }
    let program = format!(
        "import importlib.metadata as metadata; print(metadata.version({package:?}))"
    );
    let output = match std::process::Command::new(interpreter)
        .arg("-c")
        .arg(&program)
        .output()
    {
        Ok(output) => output,
        Err(error) => {
            return ToolVersion::Unavailable {
                why: format!("{} did not run: {error}", interpreter.display()),
            };
        }
    };
    if !output.status.success() {
        return ToolVersion::Unavailable {
            why: format!(
                "{} reported no version for {package}: exit {:?}",
                interpreter.display(),
                output.status.code()
            ),
        };
    }
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    text.truncate(VERSION_OUTPUT_CEILING);
    let version = text.trim().to_owned();
    if version.is_empty() {
        return ToolVersion::Unavailable {
            why: format!("{} printed nothing for {package}", interpreter.display()),
        };
    }
    ToolVersion::Read {
        version,
        recorded: Recorded::by(format!(
            "{} -c \"import importlib.metadata; metadata.version({package:?})\"",
            interpreter.display()
        )),
    }
}

/// Read a checked-out repository's `HEAD` commit as its version.
///
/// Returns [`ToolVersion::Unavailable`] with the reason on any failure. The output is truncated at
/// [`VERSION_OUTPUT_CEILING`] bytes before anything is retained; the read itself is
/// `std::process::Command::output`'s.
pub fn git_head(repository: &Path) -> ToolVersion {
    if !repository.is_dir() {
        return ToolVersion::Unavailable {
            why: format!("no directory at {}", repository.display()),
        };
    }
    let output = match std::process::Command::new("git")
        .arg("-C")
        .arg(repository)
        .arg("rev-parse")
        .arg("HEAD")
        .output()
    {
        Ok(output) => output,
        Err(error) => {
            return ToolVersion::Unavailable {
                why: format!("git did not run at {}: {error}", repository.display()),
            };
        }
    };
    if !output.status.success() {
        return ToolVersion::Unavailable {
            why: format!(
                "git rev-parse HEAD failed at {}: exit {:?}",
                repository.display(),
                output.status.code()
            ),
        };
    }
    let mut text = String::from_utf8_lossy(&output.stdout).into_owned();
    text.truncate(VERSION_OUTPUT_CEILING);
    let version = text.trim().to_owned();
    if version.is_empty() {
        return ToolVersion::Unavailable {
            why: format!("git printed nothing at {}", repository.display()),
        };
    }
    ToolVersion::Read {
        version,
        recorded: Recorded::by(format!("git -C {} rev-parse HEAD", repository.display())),
    }
}

/// **An exact integer nanosecond reading.** No float ever carries a duration in this owner.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct Nanoseconds(u128);

impl Nanoseconds {
    /// The exact count.
    pub const fn count(self) -> u128 {
        self.0
    }
}

/// **The four named clocks.** AGENTS.md: name each clock, and distinguish setup, resident
/// execution, readout and end-to-end delivery.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum ClockName {
    /// Mounting inputs, decoding, founding the material.
    Setup,
    /// The work the run exists to do.
    ResidentExecution,
    /// Reading the result out of the resident representation.
    Readout,
    /// The whole call, from before setup to after readout.
    EndToEnd,
}

impl ClockName {
    /// Every clock, in the order a run passes through them.
    pub const ALL: [ClockName; 4] = [
        ClockName::Setup,
        ClockName::ResidentExecution,
        ClockName::Readout,
        ClockName::EndToEnd,
    ];

    /// A short name, for receipts.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Setup => "setup",
            Self::ResidentExecution => "resident_execution",
            Self::Readout => "readout",
            Self::EndToEnd => "end_to_end",
        }
    }
}

/// **A monotonic stopwatch.** Its source is declared and travels with every reading it produces.
#[derive(Clone, Copy, Debug)]
pub struct Stopwatch {
    started: Instant,
}

impl Stopwatch {
    /// The declared clock source.
    pub const SOURCE: &'static str = "std::time::Instant, the platform monotonic clock";

    /// Start a stopwatch.
    pub fn start() -> Self {
        Self {
            started: Instant::now(),
        }
    }

    /// The exact integer nanoseconds since it started.
    pub fn read(&self) -> Nanoseconds {
        Nanoseconds(self.started.elapsed().as_nanos())
    }
}

/// One clock's reading, with the clock's name and its declared source.
///
/// [definition] Its fields are private and its only constructor is [`RunRecorder::record`], so a
/// reading cannot be written as a literal.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClockReading {
    name: ClockName,
    nanoseconds: Nanoseconds,
    source: &'static str,
}

impl ClockReading {
    /// Which clock.
    pub const fn name(&self) -> ClockName {
        self.name
    }

    /// Its exact integer nanosecond reading.
    pub const fn nanoseconds(&self) -> Nanoseconds {
        self.nanoseconds
    }

    /// The declared source the reading came from.
    pub const fn source(&self) -> &'static str {
        self.source
    }
}

/// **The receipt of one run**: tool, version, mode, numerical scope and named clocks.
///
/// [definition] Its fields are private and its only constructor is [`RunRecorder::finish`], so a
/// receipt cannot be written as a literal and a version inside it cannot be guessed:
/// [`ToolVersion::Read`] carries a [`Recorded`] token with no public constructor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunReceipt {
    schema: String,
    tool: String,
    version: ToolVersion,
    mode: String,
    numerical_scope: String,
    clocks: Vec<ClockReading>,
}

impl RunReceipt {
    /// The schema.
    pub fn schema(&self) -> &str {
        &self.schema
    }

    /// Which tool the run used.
    pub fn tool(&self) -> &str {
        &self.tool
    }

    /// Its version, read or explicitly unavailable.
    pub const fn version(&self) -> &ToolVersion {
        &self.version
    }

    /// The mode it ran in.
    pub fn mode(&self) -> &str {
        &self.mode
    }

    /// The numerical scope it ran under.
    pub fn numerical_scope(&self) -> &str {
        &self.numerical_scope
    }

    /// Every clock it recorded, in the order they were recorded.
    pub fn clocks(&self) -> &[ClockReading] {
        &self.clocks
    }

    /// One clock's exact reading.
    pub fn clock(&self, name: ClockName) -> Option<Nanoseconds> {
        self.clocks
            .iter()
            .find(|reading| reading.name() == name)
            .map(ClockReading::nanoseconds)
    }

    /// A rendering for a report. The nanosecond counts are exact integers; any decimal a reader
    /// forms from them is prose.
    pub fn render(&self) -> String {
        let clocks = self
            .clocks
            .iter()
            .map(|reading| {
                format!(
                    "{}={} ns",
                    reading.name().label(),
                    reading.nanoseconds().count()
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "tool={} version={} mode={} scope={} source={} clocks[{}]",
            self.tool,
            self.version.render(),
            self.mode,
            self.numerical_scope,
            Stopwatch::SOURCE,
            clocks
        )
    }
}

/// **The recorder that produces a [`RunReceipt`].**
///
/// [definition] It is the only route to a receipt. It refuses a repeated clock name and refuses to
/// finish without an [`ClockName::EndToEnd`] reading, so no receipt can claim a run whose whole
/// duration was never measured.
#[derive(Debug)]
pub struct RunRecorder {
    tool: String,
    mode: String,
    numerical_scope: String,
    clocks: Vec<ClockReading>,
}

impl RunRecorder {
    /// Start recording. Refuses an empty tool, mode or numerical scope: a receipt that does not say
    /// what ran, how, and over what numbers is not a receipt.
    pub fn start(
        tool: impl Into<String>,
        mode: impl Into<String>,
        numerical_scope: impl Into<String>,
    ) -> Result<Self, EvaluationRefusal> {
        let tool = tool.into();
        let mode = mode.into();
        let numerical_scope = numerical_scope.into();
        for (value, what) in [
            (&tool, "run receipt tool"),
            (&mode, "run receipt mode"),
            (&numerical_scope, "run receipt numerical scope"),
        ] {
            if value.trim().is_empty() {
                return Err(EvaluationRefusal::NotStated { what });
            }
        }
        Ok(Self {
            tool,
            mode,
            numerical_scope,
            clocks: Vec::with_capacity(ClockName::ALL.len()),
        })
    }

    /// Record one named clock from a stopwatch. Refuses a repeated clock name.
    pub fn record(
        &mut self,
        name: ClockName,
        watch: &Stopwatch,
    ) -> Result<Nanoseconds, EvaluationRefusal> {
        if self.clocks.iter().any(|reading| reading.name() == name) {
            return Err(EvaluationRefusal::ClockRepeated {
                clock: name.label(),
            });
        }
        let nanoseconds = watch.read();
        self.clocks.push(ClockReading {
            name,
            nanoseconds,
            source: Stopwatch::SOURCE,
        });
        Ok(nanoseconds)
    }

    /// The clocks recorded so far.
    pub fn clocks(&self) -> &[ClockReading] {
        &self.clocks
    }

    /// **Finish the receipt**, reading the tool's version through the supplied reader.
    ///
    /// The reader is a function so that the version is *read at finish time* rather than handed in
    /// as a value; and because [`ToolVersion::Read`] carries a token with no public constructor, a
    /// reader that did not ask the tool can only return [`ToolVersion::Unavailable`] with a reason.
    ///
    /// Refuses without an [`ClockName::EndToEnd`] reading.
    pub fn finish(
        self,
        read_version: &dyn Fn() -> ToolVersion,
    ) -> Result<RunReceipt, EvaluationRefusal> {
        if !self
            .clocks
            .iter()
            .any(|reading| reading.name() == ClockName::EndToEnd)
        {
            return Err(EvaluationRefusal::EndToEndClockAbsent {
                recorded: self.clocks.len(),
            });
        }
        Ok(RunReceipt {
            schema: "holonic-engine.run-receipt.v1".to_owned(),
            tool: self.tool,
            version: read_version(),
            mode: self.mode,
            numerical_scope: self.numerical_scope,
            clocks: self.clocks,
        })
    }
}

#[cfg(test)]
#[path = "evaluation_discipline/tests.rs"]
mod tests;
