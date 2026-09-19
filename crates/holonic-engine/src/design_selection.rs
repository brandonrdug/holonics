//! **B8 — selection and design equivalence.**
//!
//! [definition] This module is the executable owner of item **B8** of
//! `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md`. Its Lean counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/DesignSelection.lean`
//! (namespace `Soma.Holonics.Foundation.DesignSelection`), and the correspondence is the
//! deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `MergeVerdict`, `MergeVerdict.licensesMerge` | [`MergeVerdict`], [`MergeVerdict::licenses_merge`] |
//! | `notSeparatedWithinBound_does_not_license_merge`, `refuted_does_not_license_merge` | [`MergeVerdict::licenses_merge`] and its exhaustive test |
//! | `only_equivalentBy_licenses_merge` | [`merge`], whose only success arm is [`MergeVerdict::EquivalentBy`] |
//! | `oneSeparatingFutureReceiverRefutesTheMerge` | [`merge_verdict`] returning [`MergeVerdict::Refuted`] |
//! | `presentAgreementDoesNotImplyEnvironmentAgreement` | the design situation's test |
//! | `declaredEnvironmentAgreementDoesNotImplyUndeclared` | [`DesignFamily::design_situation`] over two declarations |
//! | `toleranceClosenessAtOneReceiverLicensesNothing` | the rung-6 instance in this module's tests |
//! | `interfaceAgreementWithoutAffinityAgreement` | the same instance's second half |
//! | `HardConstraint`, `admitted`, `violations` | [`HardConstraint`], [`DesignFamily::admit`], [`ConstraintViolation`] |
//! | `violating_design_is_never_admitted`, `theBestDesignIsStillRefused` | [`AdmissionStage`] and its tests |
//! | `refusal_names_the_constraint` | [`ConstraintViolation::constraint`] |
//! | `Reading`, `WorstVerdict`, `worstOver` | [`ReceiverReading`], [`WorstVerdict`], [`DesignFamily::worst_over`] |
//! | `worst_is_attained`, `worst_is_an_upper_bound` | [`WorstVerdict::Worst`] carrying every attaining environment |
//! | `undeclared_environment_is_absent` | [`DesignFamily::worst_over`] folding only the declared family |
//! | `unread_at_a_declared_environment_refuses` | [`WorstVerdict::UnreadAt`] |
//! | `scalarFirstDiscardsAFrontierDesign` | [`ReceiverWeighting`], [`DesignFamily::scalar_minimizers`] and its test |
//! | `indistinguishabilityIsNotTransitive`, `aComponentCanContainASeparatedPair` | [`StructuralClusters::separated_pairs_inside_a_component`] |
//! | `selection_contract` | the whole module |
//!
//! **Scope of the formal side.** `DesignSelection.lean` states the worst-environment laws for the
//! smaller-is-better sense over fully decided readings. The greater-is-better sense is the same
//! law on the order dual, and the undecided comparison (plural intervals, an unread axis) is
//! carried here and in `presentation_cost::frontier_by` without a Lean counterpart: those two
//! generalizations are implemented-exact and tested, not formal-checked.
//!
//! # Why this is a new owner and not another `physical_occurrence` submodule
//!
//! [definition] B5 and B6 are submodules of [`crate::physical_occurrence`] because their
//! populations *are* populations of that owner's [`SituatedFamily`]. B8's object is not. Three
//! facts decide it:
//!
//! 1. **The selection cascade consumes the receivers.** `rigidity_receiver`, `hodge_receiver`,
//!    `topological_receiver` and `causal_chord` all read `physical_occurrence`'s complexes, and
//!    [`crate::receiver_atlas`] composes them. A stage that ranks by receiver readings sits
//!    *above* that layer; putting it inside `physical_occurrence` would make the substrate depend
//!    on its own consumers, and on [`crate::relation_ladder`] and [`crate::presentation_cost`]
//!    besides.
//! 2. **The population is a rectangle neither existing family admits.** A design family is
//!    several *objects*, each read at several *environments*.
//!    [`crate::physical_occurrence::VerticalFamily`] refuses two members at one environment and
//!    refuses a member about another object; [`crate::physical_occurrence::HorizontalFamily`]
//!    refuses two environments; [`crate::physical_occurrence::PluralFibre`] is explicitly *one
//!    object at one receiver* and refuses a member of different kinship. [`DesignFamily`] is the
//!    rectangle whose **rows** are `VerticalFamily` and whose **columns** are `HorizontalFamily`,
//!    and [`DesignFamily::declare`] founds exactly those, so the composition is checked rather
//!    than asserted.
//! 3. **The merge question is the relation ladder's, at a situation built from the typed
//!    passages.** [`DesignFamily::design_situation`] is a [`crate::relation_ladder::Situation`]
//!    whose generators are admitted [`crate::physical_occurrence::Passage`]es — vertical
//!    environment changes and horizontal mutations — and whose receivers are the declared receiver
//!    family read at the carrier's environment index. Design equivalence **is**
//!    `RelationLadder.EqualPotential` there; nothing is redefined.
//!
//! # Design equivalence is equal potential, never equal score
//!
//! [proved-derived] Two designs may be merged only when every declared receiver, every declared
//! environment and every admitted future transformation agrees. One separating future receiver
//! refutes the collapse (`RelationLadder.separatorRefutesEqualPotential`).
//!
//! Executably, a bounded search over ordered generator histories can only ever return
//! [`crate::relation_ladder::PotentialVerdict::Separated`] or
//! [`crate::relation_ladder::PotentialVerdict::NotSeparatedWithinBound`], so **a merge is never
//! licensed by a bounded search**. [`merge_verdict`] returns three values and only
//! [`MergeVerdict::EquivalentBy`] — an exhibited equivariant isomorphism whose probe the caller
//! declares exhaustive, checked by [`crate::relation_ladder::Situation::check_automorphism`] —
//! reaches [`merge`]. A separator returned by the bounded search **overrides** a declared
//! isomorphism, because the separator is evidence and the declaration is not.
//!
//! # The cascade, in the plan's order
//!
//! [definition] [`DesignFamily::cascade`] runs the five stages and returns each stage's own
//! result:
//!
//! 1. [`DesignFamily::admit`] — **hard constraints**, a typed [`ConstraintViolation`] per violated
//!    constraint and never a penalty term. No weight enters this stage, so no weight can make a
//!    violated constraint survivable.
//! 2. [`DesignFamily::frontier`] — **Pareto filtering** over the receiver-reading vector, whose
//!    axes are the `(receiver, environment)` pairs, through
//!    [`crate::presentation_cost::frontier_by`]. An undecided comparison never licenses a discard.
//! 3. [`DesignFamily::rank_by_worst_environment`] — **worst-environment ranking**. A design's
//!    reading at one receiver is its worst over the *declared* environments. An environment the
//!    declaration does not carry is **absent** — not a best case, not a worst case — and a design
//!    unread at a declared environment is **refused for ranking** there and never imputed.
//! 4. [`DesignFamily::quality_diversity`] — **the frontier's spread**, one entry per structural
//!    cluster carrying every design that is best inside it. Ties are whole sets.
//! 5. [`DesignFamily::structural_clusters`] — **clusters from the exact separator structure**:
//!    connected components of the indistinguishability graph over the designs' decided contact
//!    classes, computed with `physical_occurrence`'s own [`DecidedClass`] law. Never a float
//!    embedding.
//!
//! [definition] **Any scalar is one receiver among the others and never the identity of a
//! candidate.** [`ReceiverWeighting`] and [`DesignFamily::scalar_minimizers`] exist so that the
//! loss a scalar-first cascade causes can be *exhibited*; no stage of [`DesignFamily::cascade`]
//! calls them. `PresentationCost.unsupported_not_minimizer` is the formal reason, and this
//! module's `a_scalar_first_cascade_discards_a_frontier_design` is its constructed design
//! instance.
//!
//! # No floats, and every ranking comparison is exact
//!
//! [implemented-exact] Every reading is an [`ExactInterval`] over `BigRational`; every comparison
//! goes through [`crate::topological_receiver::compare_values`], whose fourth value is
//! [`ValueOrder::Open`] and is never tie-broken. Ties are returned as ties and never broken by
//! order of presentation: [`WorstVerdict::Worst`] carries *every* attaining environment, a
//! ranking tier carries every design with the exactly equal worst reading, and a pair the exact
//! law does not decide is returned in [`WorstEnvironmentRanking::undecided`] rather than ordered.
//!
//! # Declared sizes are bounded before they are used
//!
//! [implemented-exact] [`DesignFamily::declare`] checks the design, environment and receiver
//! counts against [`DESIGN_CEILING`], [`ENVIRONMENT_CEILING`] and [`RECEIVER_CEILING`], and
//! [`Design::found`] bounds its own face population. Every quadratic stage then recomputes its own
//! comparison count with `checked_mul` from the **candidate list the caller declared** — which is
//! not the family's own population — and refuses above [`COMPARISON_CEILING`] before any pass,
//! allocation or `with_capacity`: [`DesignFamily::frontier`] on `candidates² · receivers ·
//! environments`, [`DesignFamily::rank_by_worst_environment`] on `candidates² · environments`,
//! [`DesignFamily::structural_clusters`] on `candidates² · contacts`,
//! [`DesignFamily::scalar_minimizers`] on `candidates²`, and [`DesignFamily::quality_diversity`]
//! on the supplied receipts' own sizes, because their fields are public and a forged receipt is a
//! caller declaration like any other. [`DesignFamily::design_situation`] bounds the transformation
//! family and checks every transformation's indices against the family before a generator is
//! built, and hands its declared history ceiling to [`Situation::declare`], which checks the
//! implied ordered-history population before anything is enumerated.
//!
//! [implemented-exact] Every refusal is a typed [`SelectionRefusal`]. The `expect`s in this module
//! stand on invariants [`DesignFamily::declare`] established — a face at every declared
//! environment, a reading at every axis — and are unreachable from a declared family; nothing here
//! panics on caller input. An out-of-range carrier handed to a receiver of
//! [`DesignFamily::design_situation`] returns a typed [`LadderRefusal`] rather than indexing.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use num_bigint::BigUint;
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::exact_value::ExactInterval;
use crate::physical_constraint_complex::ContactClass;
use crate::physical_occurrence::{
    CoordinateName, DecidedClass, Environment, EnvironmentPassage, EnvironmentRefusal, Horizontal,
    HorizontalFamily, ObjectKinship, OccurrenceId, Passage, PassageRefusal, SituatedFamily,
    StatusRefusal, Vertical, VerticalFamily,
};
use crate::presentation_cost::{AxisComparison, frontier_by};
use crate::relation_ladder::{
    Classification, Declarations, LadderRefusal, NamedGenerator, NamedReceiver, PotentialVerdict,
    Rung, Separator, Situation,
};
use crate::topological_receiver::{ValueOrder, compare_values};

// -------------------------------------------------------------------------------------------
// Declared ceilings
// -------------------------------------------------------------------------------------------

/// The largest admitted design population.
pub const DESIGN_CEILING: usize = 4096;
/// The largest admitted declared environment family.
pub const ENVIRONMENT_CEILING: usize = 64;
/// The largest admitted declared receiver family.
pub const RECEIVER_CEILING: usize = 64;
/// The largest admitted number of exact comparisons in one stage.
pub const COMPARISON_CEILING: usize = 1 << 28;
/// The largest admitted number of admitted future transformations.
pub const TRANSFORMATION_CEILING: usize = 256;

// -------------------------------------------------------------------------------------------
// Typed refusals
// -------------------------------------------------------------------------------------------

/// Every way this module declines to answer. A refusal is content; nothing here panics.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SelectionRefusal {
    /// A family over no designs is not a selection.
    #[error("a design family over no designs is not a selection")]
    EmptyFamily,
    /// A family declaring no environment has nothing to be worst over.
    #[error("a design family must declare at least one environment")]
    NoEnvironmentDeclared,
    /// A family declaring no receiver declares nothing.
    #[error("a design family must declare at least one receiver")]
    NoReceiverDeclared,
    /// The design population is above [`DESIGN_CEILING`].
    #[error("the declared design population is {declared}, above the ceiling {ceiling}")]
    DesignPopulationTooLarge {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The environment family is above [`ENVIRONMENT_CEILING`].
    #[error("the declared environment family has {declared} members, above the ceiling {ceiling}")]
    EnvironmentFamilyTooLarge {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The receiver family is above [`RECEIVER_CEILING`].
    #[error("the declared receiver family has {declared} members, above the ceiling {ceiling}")]
    ReceiverFamilyTooLarge {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The admitted transformation family is above [`TRANSFORMATION_CEILING`].
    #[error("{declared} admitted transformations were offered, above the ceiling {ceiling}")]
    TransformationFamilyTooLarge {
        /// How many were offered.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The comparison count a stage implies is above [`COMPARISON_CEILING`], computed with checked
    /// arithmetic **before** the stage runs.
    #[error(
        "the {stage} stage implies {implied} exact comparisons over {designs} designs, above the \
         ceiling {ceiling}"
    )]
    ComparisonPopulationTooLarge {
        /// Which stage.
        stage: &'static str,
        /// The implied count, or `usize::MAX` when the computation itself overflowed.
        implied: usize,
        /// The design population.
        designs: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// Two declared environments carry the same label, so a reading cannot name its site.
    #[error("the environment label {label:?} is declared twice")]
    EnvironmentLabelRepeated {
        /// The repeated label.
        label: String,
    },
    /// Two declared receivers carry the same name.
    #[error("the receiver name {name:?} is declared twice")]
    ReceiverNameRepeated {
        /// The repeated name.
        name: String,
    },
    /// Two designs carry the same identity.
    #[error("the design identity {id:?} is declared twice")]
    DesignIdRepeated {
        /// The repeated identity.
        id: DesignId,
    },
    /// An empty declared name, label or ground.
    #[error("a declared {what} is empty, so it states nothing")]
    NotStated {
        /// Which declaration.
        what: &'static str,
    },
    /// A design presented no face at a declared environment.
    #[error("design {design:?} presents no face at the declared environment {label:?}")]
    FaceAbsentAtDeclaredEnvironment {
        /// The design.
        design: DesignId,
        /// The environment label.
        label: String,
    },
    /// A design presented a face at an environment the family does not declare.
    #[error("design {design:?} presents a face at {label:?}, which the family does not declare")]
    FaceAtUndeclaredEnvironment {
        /// The design.
        design: DesignId,
        /// The label.
        label: String,
    },
    /// The face a design filed under a label does not sit at the environment that label names.
    #[error(
        "design {design:?}'s face filed under {label:?} sits at a different environment value; a \
         label addresses an environment and never replaces it"
    )]
    FaceIsNotAtTheLabelledEnvironment {
        /// The design.
        design: DesignId,
        /// The label.
        label: String,
    },
    /// A design stated no reading for a declared `(receiver, environment)` pair. An unread axis is
    /// stated with [`ReceiverReading::Unread`]; it is never left out.
    #[error(
        "design {design:?} states no reading at receiver {receiver:?}, environment {label:?}; an \
         axis a receiver did not read is declared Unread with a reason and never omitted"
    )]
    ReadingNotStated {
        /// The design.
        design: DesignId,
        /// The receiver.
        receiver: String,
        /// The environment label.
        label: String,
    },
    /// Two designs are about the same object, so they are one object read twice and belong to
    /// `VerticalFamily` or `PluralFibre`, not to a design family.
    #[error(
        "designs {left:?} and {right:?} are about the same object, so they are one object read \
         twice; the vertical index and the plural fibre own that population"
    )]
    TwoDesignsAreOneObject {
        /// The first design.
        left: DesignId,
        /// The second.
        right: DesignId,
    },
    /// A design identity the family does not carry.
    #[error("the family carries no design {id:?}")]
    DesignAbsent {
        /// The identity.
        id: DesignId,
    },
    /// An environment label the family does not declare.
    #[error("the family declares no environment {label:?}")]
    EnvironmentAbsent {
        /// The label.
        label: String,
    },
    /// A receiver name the family does not declare.
    #[error("the family declares no receiver {name:?}")]
    ReceiverAbsent {
        /// The name.
        name: String,
    },
    /// Two designs' faces at one environment address different contact populations, so no
    /// separator between them is statable.
    #[error(
        "designs {left:?} and {right:?} address {left_contacts} and {right_contacts} contacts at \
         {label:?}, so no separator between them is statable"
    )]
    ContactPopulationDisagrees {
        /// The first design.
        left: DesignId,
        /// The second.
        right: DesignId,
        /// The environment label.
        label: String,
        /// The first design's contact count.
        left_contacts: usize,
        /// The second design's contact count.
        right_contacts: usize,
    },
    /// Two designs' faces at one environment were classified against different apertures.
    #[error(
        "designs {left:?} and {right:?} were classified against different apertures at {label:?}; \
         separation at one aperture says nothing at another"
    )]
    AperturesDiffer {
        /// The first design.
        left: DesignId,
        /// The second.
        right: DesignId,
        /// The environment label.
        label: String,
    },
    /// A merge was asked of a verdict that did not license it.
    #[error("the verdict {verdict} licenses no merge, so no merged class is returned")]
    MergeNotLicensed {
        /// Which verdict was returned.
        verdict: &'static str,
    },
    /// A declared weight was negative, so a worse design would score better.
    #[error("the weight declared at receiver {receiver:?} is negative")]
    NegativeWeight {
        /// The receiver.
        receiver: String,
    },
    /// The environment owner refused.
    #[error("the environment refused: {0}")]
    Environment(#[from] EnvironmentRefusal),
    /// The family owner refused.
    #[error("the family refused: {0}")]
    Status(#[from] StatusRefusal),
    /// The passage owner refused, so the transformation is not admitted.
    #[error("the passage refused, so the transformation is not admitted: {0}")]
    Passage(#[from] PassageRefusal),
    /// The relation ladder refused.
    #[error("the relation ladder refused: {0}")]
    Ladder(#[from] LadderRefusal),
}

// -------------------------------------------------------------------------------------------
// The declared vocabulary
// -------------------------------------------------------------------------------------------

/// A design's identity in the population. It is an address, never a reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct DesignId(pub u64);

/// Which direction of a declared receiver's exact reading is better. There is no default: a
/// receiver whose orientation is not declared orders nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum Sense {
    /// A smaller exact reading is better — a dissociation constant, a residual, a cost.
    SmallerIsBetter,
    /// A greater exact reading is better — a contact count, a rigidity rank, a persistence.
    GreaterIsBetter,
}

/// One declared receiver of the selection: its name, its orientation and the ground the
/// orientation is declared on.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DeclaredReceiver {
    name: String,
    sense: Sense,
    ground: String,
}

impl DeclaredReceiver {
    /// Declare a receiver. Refuses an empty name or an unstated ground.
    pub fn declare(
        name: impl Into<String>,
        sense: Sense,
        ground: impl Into<String>,
    ) -> Result<Self, SelectionRefusal> {
        let name = name.into();
        let ground = ground.into();
        if name.trim().is_empty() {
            return Err(SelectionRefusal::NotStated {
                what: "receiver name",
            });
        }
        if ground.trim().is_empty() {
            return Err(SelectionRefusal::NotStated {
                what: "receiver orientation ground",
            });
        }
        Ok(Self {
            name,
            sense,
            ground,
        })
    }

    /// Its declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Its declared orientation.
    pub const fn sense(&self) -> Sense {
        self.sense
    }

    /// The ground the orientation is declared on.
    pub fn ground(&self) -> &str {
        &self.ground
    }
}

/// One declared environment of the selection: the label the declaration addresses it by, and the
/// typed [`Environment`] value that label names.
///
/// [definition] The label is an address and never a substitute for the environment value.
/// [`DesignFamily::declare`] checks that every face filed under a label really sits at the
/// environment the label names, so a relabelling cannot move a claim.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DeclaredEnvironment {
    label: String,
    environment: Environment,
}

impl DeclaredEnvironment {
    /// Declare an environment under a label. Refuses an empty label.
    pub fn declare(
        label: impl Into<String>,
        environment: Environment,
    ) -> Result<Self, SelectionRefusal> {
        let label = label.into();
        if label.trim().is_empty() {
            return Err(SelectionRefusal::NotStated {
                what: "environment label",
            });
        }
        Ok(Self { label, environment })
    }

    /// The label.
    pub fn label(&self) -> &str {
        &self.label
    }

    /// The typed environment value it names.
    pub const fn environment(&self) -> &Environment {
        &self.environment
    }
}

/// One exact reading of one design by one declared receiver at one declared environment.
///
/// [definition] A point interval is a decided reading; a wide interval is a **plural** reading and
/// stays plural — two plural readings that overlap without coinciding compare
/// [`ValueOrder::Open`] and are never tie-broken. [`ReceiverReading::Unread`] is a stated absence
/// with its reason and is never a value: it is neither a best case nor a worst case.
///
/// Lean counterpart: `Foundation/DesignSelection.lean::Reading`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ReceiverReading {
    /// The receiver returned this exact reading here.
    Read(ExactInterval),
    /// The receiver did not read this design here, with the stated reason.
    Unread(UnreadReason),
}

/// Why a receiver did not read a design at a declared environment.
///
/// [definition] Its field is private and [`UnreadReason::declare`] refuses an empty statement, so
/// there is no enum-variant field a caller can fill with the empty string: an unread axis always
/// says why. It carries no `Deserialize` and no `Default`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct UnreadReason(String);

impl UnreadReason {
    /// Declare the reason. Refuses an unstated one.
    pub fn declare(why: impl Into<String>) -> Result<Self, SelectionRefusal> {
        let why = why.into();
        if why.trim().is_empty() {
            return Err(SelectionRefusal::NotStated {
                what: "reason a receiver did not read",
            });
        }
        Ok(Self(why))
    }

    /// The stated reason.
    pub fn statement(&self) -> &str {
        &self.0
    }
}

impl ReceiverReading {
    /// Declare an unread axis. Refuses an unstated reason.
    pub fn unread(why: impl Into<String>) -> Result<Self, SelectionRefusal> {
        Ok(Self::Unread(UnreadReason::declare(why)?))
    }

    /// A decided reading at an exact rational.
    pub fn at(value: Rat) -> Self {
        Self::Read(ExactInterval::point(value))
    }

    /// The exact reading, when there is one.
    pub const fn value(&self) -> Option<&ExactInterval> {
        match self {
            Self::Read(interval) => Some(interval),
            Self::Unread(_) => None,
        }
    }
}

/// How one declared receiver's exact law compares two readings, with the receiver's orientation
/// applied. `Undecided` covers both an unread axis and two plural readings that overlap without
/// coinciding, and it **never** licenses a discard.
pub fn compare_readings(
    sense: Sense,
    left: &ReceiverReading,
    right: &ReceiverReading,
) -> AxisComparison {
    let (ReceiverReading::Read(left), ReceiverReading::Read(right)) = (left, right) else {
        return AxisComparison::Undecided;
    };
    match compare_values(left, right) {
        ValueOrder::ExactTie => AxisComparison::Equal,
        ValueOrder::Open => AxisComparison::Undecided,
        ValueOrder::StrictlyBefore => match sense {
            Sense::SmallerIsBetter => AxisComparison::Better,
            Sense::GreaterIsBetter => AxisComparison::Worse,
        },
        ValueOrder::StrictlyAfter => match sense {
            Sense::SmallerIsBetter => AxisComparison::Worse,
            Sense::GreaterIsBetter => AxisComparison::Better,
        },
    }
}

// -------------------------------------------------------------------------------------------
// The design
// -------------------------------------------------------------------------------------------

/// **One design: one object, read at every declared environment by every declared receiver.**
///
/// [definition] `Deserialize` is deliberately not derived, and the fields a constructor establishes
/// are private: a design is founded through [`Design::found`] and admitted through
/// [`DesignFamily::declare`], never remounted past those checks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Design {
    /// The schema this design serializes under.
    pub schema: String,
    /// Its identity in the population.
    pub id: DesignId,
    /// Exterior lineage, retained as testimony.
    pub lineage: String,
    object: ObjectKinship,
    faces: BTreeMap<String, SituatedFamily>,
    readings: BTreeMap<(String, String), ReceiverReading>,
}

impl Design {
    /// Found a design from its faces at the declared environments and its exact readings.
    ///
    /// Refuses an empty face population and a face population about more than one object — the
    /// faces of one design are one object across environments, which is exactly
    /// [`VerticalFamily::over_one_object`]'s law, founded here rather than asserted.
    pub fn found(
        id: DesignId,
        lineage: impl Into<String>,
        faces: impl IntoIterator<Item = (String, SituatedFamily)>,
        readings: impl IntoIterator<Item = ((String, String), ReceiverReading)>,
    ) -> Result<Self, SelectionRefusal> {
        let faces: BTreeMap<String, SituatedFamily> = faces.into_iter().collect();
        if faces.is_empty() {
            return Err(SelectionRefusal::EmptyFamily);
        }
        if faces.len() > ENVIRONMENT_CEILING {
            return Err(SelectionRefusal::EnvironmentFamilyTooLarge {
                declared: faces.len(),
                ceiling: ENVIRONMENT_CEILING,
            });
        }
        let vertical = VerticalFamily::over_one_object(faces.values().cloned().collect())?;
        Ok(Self {
            schema: "holonic-engine.design.v1".to_owned(),
            id,
            lineage: lineage.into(),
            object: vertical.object.clone(),
            faces,
            readings: readings.into_iter().collect(),
        })
    }

    /// The object this design is: its ordered monomer sequences. Two designs with equal kinship
    /// are one object.
    pub const fn object(&self) -> &ObjectKinship {
        &self.object
    }

    /// Its face at one declared environment.
    pub fn face(&self, label: &str) -> Option<&SituatedFamily> {
        self.faces.get(label)
    }

    /// Every environment label it presents a face at.
    pub fn labels(&self) -> Vec<&str> {
        self.faces.keys().map(String::as_str).collect()
    }

    /// Its reading at one `(receiver, environment)` axis.
    pub fn reading(&self, receiver: &str, label: &str) -> Option<&ReceiverReading> {
        self.readings
            .get(&(receiver.to_owned(), label.to_owned()))
    }

    /// The faces as a vertical family: one object, several environments. Refounded rather than
    /// cached, so the law is enforced at every reading.
    pub fn vertical_family(&self) -> Result<VerticalFamily, SelectionRefusal> {
        Ok(VerticalFamily::over_one_object(
            self.faces.values().cloned().collect(),
        )?)
    }
}

// -------------------------------------------------------------------------------------------
// The design family: the rectangle neither existing family admits
// -------------------------------------------------------------------------------------------

/// **Several designs, each read at every declared environment by every declared receiver.**
///
/// [definition] The rows are [`VerticalFamily`] — one design across environments — and the columns
/// are [`HorizontalFamily`] — the designs at one environment. [`DesignFamily::declare`] founds
/// both, so the composition is checked. Neither owner admits the rectangle: a vertical family
/// refuses two members at one environment, a horizontal family refuses two environments, and a
/// [`crate::physical_occurrence::PluralFibre`] refuses a member about another object.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DesignFamily {
    /// The schema this family serializes under.
    pub schema: String,
    environments: Vec<DeclaredEnvironment>,
    receivers: Vec<DeclaredReceiver>,
    designs: Vec<Design>,
}

/// The exact comparison count a quadratic stage implies, with checked arithmetic throughout.
fn comparison_count(designs: usize, axes: usize) -> Option<usize> {
    designs.checked_mul(designs)?.checked_mul(axes)
}

impl DesignFamily {
    /// **Declare the family.** Every declared size is checked here, before any pass or allocation
    /// sized by it, and every structural law is founded rather than assumed.
    ///
    /// Refuses: an empty design, environment or receiver family; a size above its ceiling; a
    /// comparison count above [`COMPARISON_CEILING`]; a repeated environment label, receiver name
    /// or design identity; a design presenting no face at a declared environment or a face at an
    /// undeclared one; a face whose environment value is not the one its label names; a missing
    /// reading at any `(receiver, environment)` axis; two designs about the same object; and any
    /// row or column the vertical and horizontal family owners refuse.
    pub fn declare(
        designs: Vec<Design>,
        environments: Vec<DeclaredEnvironment>,
        receivers: Vec<DeclaredReceiver>,
    ) -> Result<Self, SelectionRefusal> {
        if designs.is_empty() {
            return Err(SelectionRefusal::EmptyFamily);
        }
        if environments.is_empty() {
            return Err(SelectionRefusal::NoEnvironmentDeclared);
        }
        if receivers.is_empty() {
            return Err(SelectionRefusal::NoReceiverDeclared);
        }
        if designs.len() > DESIGN_CEILING {
            return Err(SelectionRefusal::DesignPopulationTooLarge {
                declared: designs.len(),
                ceiling: DESIGN_CEILING,
            });
        }
        if environments.len() > ENVIRONMENT_CEILING {
            return Err(SelectionRefusal::EnvironmentFamilyTooLarge {
                declared: environments.len(),
                ceiling: ENVIRONMENT_CEILING,
            });
        }
        if receivers.len() > RECEIVER_CEILING {
            return Err(SelectionRefusal::ReceiverFamilyTooLarge {
                declared: receivers.len(),
                ceiling: RECEIVER_CEILING,
            });
        }
        let axes = receivers
            .len()
            .checked_mul(environments.len())
            .ok_or(SelectionRefusal::ComparisonPopulationTooLarge {
                stage: "frontier",
                implied: usize::MAX,
                designs: designs.len(),
                ceiling: COMPARISON_CEILING,
            })?;
        let implied = comparison_count(designs.len(), axes).unwrap_or(usize::MAX);
        if implied > COMPARISON_CEILING {
            return Err(SelectionRefusal::ComparisonPopulationTooLarge {
                stage: "frontier",
                implied,
                designs: designs.len(),
                ceiling: COMPARISON_CEILING,
            });
        }

        let mut labels: BTreeSet<&str> = BTreeSet::new();
        for declared in &environments {
            if !labels.insert(declared.label()) {
                return Err(SelectionRefusal::EnvironmentLabelRepeated {
                    label: declared.label().to_owned(),
                });
            }
        }
        let mut names: BTreeSet<&str> = BTreeSet::new();
        for declared in &receivers {
            if !names.insert(declared.name()) {
                return Err(SelectionRefusal::ReceiverNameRepeated {
                    name: declared.name().to_owned(),
                });
            }
        }
        let mut ids: BTreeSet<DesignId> = BTreeSet::new();
        for design in &designs {
            if !ids.insert(design.id) {
                return Err(SelectionRefusal::DesignIdRepeated { id: design.id });
            }
        }

        for design in &designs {
            for label in design.labels() {
                if !labels.contains(label) {
                    return Err(SelectionRefusal::FaceAtUndeclaredEnvironment {
                        design: design.id,
                        label: label.to_owned(),
                    });
                }
            }
            for declared in &environments {
                let Some(face) = design.face(declared.label()) else {
                    return Err(SelectionRefusal::FaceAbsentAtDeclaredEnvironment {
                        design: design.id,
                        label: declared.label().to_owned(),
                    });
                };
                if &face.environment != declared.environment() {
                    return Err(SelectionRefusal::FaceIsNotAtTheLabelledEnvironment {
                        design: design.id,
                        label: declared.label().to_owned(),
                    });
                }
                for receiver in &receivers {
                    if design.reading(receiver.name(), declared.label()).is_none() {
                        return Err(SelectionRefusal::ReadingNotStated {
                            design: design.id,
                            receiver: receiver.name().to_owned(),
                            label: declared.label().to_owned(),
                        });
                    }
                }
            }
            // The row: one object across the declared environments.
            design.vertical_family()?;
        }

        for (at, left) in designs.iter().enumerate() {
            for right in &designs[at + 1..] {
                if left.object() == right.object() {
                    return Err(SelectionRefusal::TwoDesignsAreOneObject {
                        left: left.id,
                        right: right.id,
                    });
                }
            }
        }

        // The columns: the designs at one environment.
        for declared in &environments {
            let column: Vec<SituatedFamily> = designs
                .iter()
                .filter_map(|design| design.face(declared.label()).cloned())
                .collect();
            HorizontalFamily::at_one_environment(column)?;
        }

        Ok(Self {
            schema: "holonic-engine.design-family.v1".to_owned(),
            environments,
            receivers,
            designs,
        })
    }

    /// The declared environments, in declaration order.
    pub fn environments(&self) -> &[DeclaredEnvironment] {
        &self.environments
    }

    /// The declared receivers, in declaration order.
    pub fn receivers(&self) -> &[DeclaredReceiver] {
        &self.receivers
    }

    /// The designs, in declaration order.
    pub fn designs(&self) -> &[Design] {
        &self.designs
    }

    /// One design by identity.
    pub fn design(&self, id: DesignId) -> Result<&Design, SelectionRefusal> {
        self.designs
            .iter()
            .find(|design| design.id == id)
            .ok_or(SelectionRefusal::DesignAbsent { id })
    }

    /// One design's index in the declaration order.
    pub fn design_index(&self, id: DesignId) -> Result<usize, SelectionRefusal> {
        self.designs
            .iter()
            .position(|design| design.id == id)
            .ok_or(SelectionRefusal::DesignAbsent { id })
    }

    /// One declared environment by label.
    pub fn environment(&self, label: &str) -> Result<&DeclaredEnvironment, SelectionRefusal> {
        self.environments
            .iter()
            .find(|declared| declared.label() == label)
            .ok_or_else(|| SelectionRefusal::EnvironmentAbsent {
                label: label.to_owned(),
            })
    }

    /// One declared receiver by name.
    pub fn receiver(&self, name: &str) -> Result<&DeclaredReceiver, SelectionRefusal> {
        self.receivers
            .iter()
            .find(|declared| declared.name() == name)
            .ok_or_else(|| SelectionRefusal::ReceiverAbsent {
                name: name.to_owned(),
            })
    }

    /// The reading of one design at one axis. Total: [`DesignFamily::declare`] checked that every
    /// `(design, receiver, environment)` axis is stated.
    fn axis_reading(&self, design: usize, receiver: usize, environment: usize) -> &ReceiverReading {
        let label = self.environments[environment].label();
        let name = self.receivers[receiver].name();
        self.designs[design]
            .reading(name, label)
            .expect("declare checked that every axis is stated")
    }
}

// -------------------------------------------------------------------------------------------
// Stage one: hard constraints, as typed refusals
// -------------------------------------------------------------------------------------------

/// A hard constraint: a declared name, the ground it is declared on, and a total admission test.
///
/// [definition] It is **not** a weight. [`DesignFamily::admit`] performs no arithmetic at all, so
/// there is no weight anywhere that could make a violated constraint survivable.
///
/// Lean counterpart: `Foundation/DesignSelection.lean::HardConstraint`.
pub struct HardConstraint {
    name: String,
    ground: String,
    #[allow(clippy::type_complexity)]
    admits: Box<dyn Fn(&Design) -> bool + Send + Sync>,
}

impl std::fmt::Debug for HardConstraint {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("HardConstraint")
            .field("name", &self.name)
            .field("ground", &self.ground)
            .finish_non_exhaustive()
    }
}

impl HardConstraint {
    /// Declare a hard constraint. Refuses an empty name or an unstated ground.
    pub fn declare(
        name: impl Into<String>,
        ground: impl Into<String>,
        admits: impl Fn(&Design) -> bool + Send + Sync + 'static,
    ) -> Result<Self, SelectionRefusal> {
        let name = name.into();
        let ground = ground.into();
        if name.trim().is_empty() {
            return Err(SelectionRefusal::NotStated {
                what: "hard constraint name",
            });
        }
        if ground.trim().is_empty() {
            return Err(SelectionRefusal::NotStated {
                what: "hard constraint ground",
            });
        }
        Ok(Self {
            name,
            ground,
            admits: Box::new(admits),
        })
    }

    /// Its declared name, which is what a refusal reports.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The ground it is declared on.
    pub fn ground(&self) -> &str {
        &self.ground
    }

    /// Whether this design satisfies it.
    pub fn admits(&self, design: &Design) -> bool {
        (self.admits)(design)
    }
}

/// One design refused by one hard constraint: a typed refusal naming the constraint, never a
/// penalty added to a score.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConstraintViolation {
    /// Which design.
    pub design: DesignId,
    /// Which constraint it violated, by name.
    pub constraint: String,
    /// The ground that constraint is declared on.
    pub ground: String,
}

/// What the hard-constraint stage returns: the admitted designs and **one refusal per violated
/// constraint**, never a total.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AdmissionStage {
    /// The schema this stage serializes under.
    pub schema: String,
    /// The designs every declared constraint admits, in declaration order.
    pub admitted: Vec<DesignId>,
    /// Every `(design, constraint)` violation, in declaration order.
    pub refused: Vec<ConstraintViolation>,
}

impl DesignFamily {
    /// **Stage one — the hard constraints.** A design violating any declared constraint is absent
    /// from [`AdmissionStage::admitted`], whatever every receiver reads.
    ///
    /// Lean counterpart: `admitted`, `violations`, `violating_design_is_never_admitted`.
    pub fn admit(&self, constraints: &[HardConstraint]) -> AdmissionStage {
        let mut admitted = Vec::new();
        let mut refused = Vec::new();
        for design in &self.designs {
            let mut violated = false;
            for constraint in constraints {
                if !constraint.admits(design) {
                    violated = true;
                    refused.push(ConstraintViolation {
                        design: design.id,
                        constraint: constraint.name().to_owned(),
                        ground: constraint.ground().to_owned(),
                    });
                }
            }
            if !violated {
                admitted.push(design.id);
            }
        }
        AdmissionStage {
            schema: "holonic-engine.design-admission.v1".to_owned(),
            admitted,
            refused,
        }
    }
}

// -------------------------------------------------------------------------------------------
// Stage two: the Pareto frontier over the receiver-reading vector
// -------------------------------------------------------------------------------------------

impl DesignFamily {
    /// **Stage two — the Pareto frontier over the receiver-reading vector.** The axes are the
    /// `(receiver, environment)` pairs: no environment is collapsed here, because collapsing is
    /// stage three's job and doing it first would throw away distinctions the frontier can see.
    ///
    /// The rule is [`crate::presentation_cost::frontier_by`], the same rule
    /// [`crate::presentation_cost::pareto_frontier`] runs on the five cost axes. An
    /// [`AxisComparison::Undecided`] anywhere — a plural reading whose exact intervals overlap
    /// without coinciding, or an axis a receiver did not read — leaves the candidate on the
    /// frontier.
    ///
    /// The `candidates² · receivers · environments` comparison count is checked against
    /// [`COMPARISON_CEILING`] before the pass runs.
    pub fn frontier(&self, candidates: &[DesignId]) -> Result<Vec<DesignId>, SelectionRefusal> {
        let axes = self.receivers.len() * self.environments.len();
        let implied = comparison_count(candidates.len(), axes).unwrap_or(usize::MAX);
        if implied > COMPARISON_CEILING {
            return Err(SelectionRefusal::ComparisonPopulationTooLarge {
                stage: "frontier",
                implied,
                designs: candidates.len(),
                ceiling: COMPARISON_CEILING,
            });
        }
        let indices = candidates
            .iter()
            .map(|id| self.design_index(*id))
            .collect::<Result<Vec<_>, _>>()?;
        let kept = frontier_by(indices.len(), axes, &|rival, candidate, axis| {
            let receiver = axis / self.environments.len();
            let environment = axis % self.environments.len();
            compare_readings(
                self.receivers[receiver].sense(),
                self.axis_reading(indices[rival], receiver, environment),
                self.axis_reading(indices[candidate], receiver, environment),
            )
        });
        Ok(kept.into_iter().map(|at| candidates[at]).collect())
    }
}

// -------------------------------------------------------------------------------------------
// Stage three: the worst reading over the declared environments
// -------------------------------------------------------------------------------------------

/// What the worst-environment stage returns for one design at one receiver.
///
/// Lean counterpart: `Foundation/DesignSelection.lean::WorstVerdict`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum WorstVerdict {
    /// The worst reading is decided, with **every** declared environment attaining it. Ties are
    /// returned as ties and never broken by order of presentation.
    Worst {
        /// The worst exact reading.
        value: ExactInterval,
        /// Every declared environment attaining it, by label, in declaration order.
        attained: Vec<String>,
    },
    /// Several readings are maximal in the bad direction and the exact law does not decide between
    /// them. Retained as a family, never resolved by a default or by presentation order.
    PluralWorst {
        /// Every maximal candidate, by label, with its exact reading.
        candidates: Vec<(String, ExactInterval)>,
    },
    /// The design is unread at this **declared** environment, so it is refused for ranking there.
    /// It is not imputed a best case, a worst case or a default.
    UnreadAt {
        /// The declared environment's label.
        environment: String,
        /// The stated reason the receiver did not read it.
        why: String,
    },
}

impl DesignFamily {
    /// **Stage three — the worst reading over the declared environments.**
    ///
    /// An environment the declaration does not carry is **absent**: this folds the declared family
    /// and nothing else, so an undeclared environment is neither a best case nor a worst case. A
    /// design unread at a declared environment returns [`WorstVerdict::UnreadAt`] — a refusal, not
    /// an imputation.
    ///
    /// Lean counterpart: `worstOver`, with `worst_is_attained`, `worst_is_an_upper_bound`,
    /// `undeclared_environment_is_absent` and `unread_at_a_declared_environment_refuses`.
    pub fn worst_over(
        &self,
        design: DesignId,
        receiver: &str,
    ) -> Result<WorstVerdict, SelectionRefusal> {
        let at = self.design_index(design)?;
        let declared = self.receiver(receiver)?;
        let sense = declared.sense();
        let mut readings: Vec<(String, ExactInterval)> = Vec::new();
        for environment in &self.environments {
            match self.designs[at]
                .reading(declared.name(), environment.label())
                .expect("declare checked that every axis is stated")
            {
                ReceiverReading::Unread(reason) => {
                    return Ok(WorstVerdict::UnreadAt {
                        environment: environment.label().to_owned(),
                        why: reason.statement().to_owned(),
                    });
                }
                ReceiverReading::Read(interval) => {
                    readings.push((environment.label().to_owned(), interval.clone()));
                }
            }
        }
        // The worst is maximal in the bad direction: nothing else is DECIDEDLY worse than it.
        // Openness therefore enlarges the maximal set rather than resolving it.
        let maximal: Vec<(String, ExactInterval)> = readings
            .iter()
            .filter(|(_, candidate)| {
                !readings.iter().any(|(_, rival)| {
                    matches!(
                        compare_readings(
                            sense,
                            &ReceiverReading::Read(rival.clone()),
                            &ReceiverReading::Read(candidate.clone()),
                        ),
                        AxisComparison::Worse
                    )
                })
            })
            .cloned()
            .collect();
        let Some((_, first)) = maximal.first() else {
            return Err(SelectionRefusal::NoEnvironmentDeclared);
        };
        if maximal
            .iter()
            .all(|(_, interval)| compare_values(interval, first) == ValueOrder::ExactTie)
        {
            return Ok(WorstVerdict::Worst {
                value: first.clone(),
                attained: maximal.into_iter().map(|(label, _)| label).collect(),
            });
        }
        Ok(WorstVerdict::PluralWorst { candidates: maximal })
    }
}

/// The ranking of the designs at one declared receiver, by their worst reading over the declared
/// environments.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WorstEnvironmentRanking {
    /// The schema this ranking serializes under.
    pub schema: String,
    /// Which declared receiver.
    pub receiver: String,
    /// Its declared orientation.
    pub sense: Sense,
    /// Each ranked design's worst verdict, in declaration order.
    pub worst: Vec<(DesignId, WorstVerdict)>,
    /// The tiers, best first. Two designs share a tier exactly when their worst readings are
    /// **exactly equal**, and a tier is sorted by design identity — an address, never the order
    /// they were presented in. `None` when some comparison is undecided or some design is refused,
    /// because there is then no total order to report.
    pub tiers: Option<Vec<Vec<DesignId>>>,
    /// Every pair the exact law does not decide, in ascending identity order. Returned, never
    /// broken.
    pub undecided: Vec<(DesignId, DesignId)>,
    /// Every design refused for ranking, with the declared environment it is unread at and the
    /// stated reason.
    pub refused: Vec<(DesignId, String, String)>,
    /// The designs nothing is decidedly better than.
    pub best: Vec<DesignId>,
}

/// Whether the first worst verdict is decidedly better than the second at this orientation, or
/// `None` when the exact law does not decide.
fn decided_better(sense: Sense, left: &WorstVerdict, right: &WorstVerdict) -> Option<bool> {
    let (WorstVerdict::Worst { value: left, .. }, WorstVerdict::Worst { value: right, .. }) =
        (left, right)
    else {
        return None;
    };
    match compare_readings(
        sense,
        &ReceiverReading::Read(left.clone()),
        &ReceiverReading::Read(right.clone()),
    ) {
        AxisComparison::Better => Some(true),
        AxisComparison::Worse => Some(false),
        AxisComparison::Equal => None,
        AxisComparison::Undecided => None,
    }
}

impl DesignFamily {
    /// **Stage three, over the whole candidate family at one receiver.**
    ///
    /// Ties are returned as ties: a tier carries every design whose worst reading is exactly
    /// equal, sorted by identity. A pair the exact law does not decide lands in
    /// [`WorstEnvironmentRanking::undecided`] and is never ordered; a design refused for ranking
    /// lands in [`WorstEnvironmentRanking::refused`] and is never imputed a value.
    pub fn rank_by_worst_environment(
        &self,
        candidates: &[DesignId],
        receiver: &str,
    ) -> Result<WorstEnvironmentRanking, SelectionRefusal> {
        let declared = self.receiver(receiver)?;
        let sense = declared.sense();
        // The pair loop below is quadratic in the caller-declared candidate list and the capacity
        // is sized by it, so the count is checked before either.
        let implied = comparison_count(candidates.len(), self.environments.len().max(1))
            .unwrap_or(usize::MAX);
        if implied > COMPARISON_CEILING {
            return Err(SelectionRefusal::ComparisonPopulationTooLarge {
                stage: "worst-environment ranking",
                implied,
                designs: candidates.len(),
                ceiling: COMPARISON_CEILING,
            });
        }
        let mut worst = Vec::with_capacity(candidates.len());
        let mut refused = Vec::new();
        for id in candidates {
            let verdict = self.worst_over(*id, receiver)?;
            if let WorstVerdict::UnreadAt { environment, why } = &verdict {
                refused.push((*id, environment.clone(), why.clone()));
            }
            worst.push((*id, verdict));
        }

        let mut undecided = Vec::new();
        for (at, (left_id, left)) in worst.iter().enumerate() {
            for (right_id, right) in &worst[at + 1..] {
                let equal = matches!(
                    (left, right),
                    (WorstVerdict::Worst { value: a, .. }, WorstVerdict::Worst { value: b, .. })
                        if compare_values(a, b) == ValueOrder::ExactTie
                );
                if !equal && decided_better(sense, left, right).is_none() {
                    let (low, high) = if left_id <= right_id {
                        (*left_id, *right_id)
                    } else {
                        (*right_id, *left_id)
                    };
                    undecided.push((low, high));
                }
            }
        }
        undecided.sort_unstable();
        undecided.dedup();

        let mut best: Vec<DesignId> = worst
            .iter()
            .filter(|(_, candidate)| {
                !worst
                    .iter()
                    .any(|(_, rival)| decided_better(sense, rival, candidate) == Some(true))
            })
            .map(|(id, _)| *id)
            .collect();
        // By identity, as `tiers` and `undecided` are: the presentation order of the candidates
        // decides nothing in any field of this ranking.
        best.sort_unstable();

        let tiers = if undecided.is_empty() && refused.is_empty() {
            let mut groups: Vec<(ExactInterval, Vec<DesignId>)> = Vec::new();
            for (id, verdict) in &worst {
                let WorstVerdict::Worst { value, .. } = verdict else {
                    // A plural worst is not a tier and not a tie; it left `undecided` nonempty
                    // unless it is the only member, in which case there is nothing to order.
                    groups.clear();
                    break;
                };
                match groups
                    .iter_mut()
                    .find(|(key, _)| compare_values(key, value) == ValueOrder::ExactTie)
                {
                    Some((_, members)) => members.push(*id),
                    None => groups.push((value.clone(), vec![*id])),
                }
            }
            if groups.is_empty() {
                None
            } else {
                // Sound because tiers are built only when every pairwise comparison is decided:
                // a decided `StrictlyBefore` means `left.upper < right.lower`, so ordering by the
                // lower bound agrees with `compare_values` on exactly this family. It is an exact
                // `BigRational` comparison either way.
                groups.sort_by(|(left, _), (right, _)| match sense {
                    Sense::SmallerIsBetter => left.lower.cmp(&right.lower),
                    Sense::GreaterIsBetter => right.lower.cmp(&left.lower),
                });
                Some(
                    groups
                        .into_iter()
                        .map(|(_, mut members)| {
                            members.sort_unstable();
                            members
                        })
                        .collect(),
                )
            }
        } else {
            None
        };

        Ok(WorstEnvironmentRanking {
            schema: "holonic-engine.worst-environment-ranking.v1".to_owned(),
            receiver: declared.name().to_owned(),
            sense,
            worst,
            tiers,
            undecided,
            refused,
            best,
        })
    }
}

// -------------------------------------------------------------------------------------------
// Stage five: structural clustering from the exact separator structure
// -------------------------------------------------------------------------------------------

/// One contact at which two designs read different **decided** classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct SeparatingContact {
    /// The addressed pair.
    pub pair: (u32, u32),
    /// What the first design read there.
    pub left: DecidedClass,
    /// What the second read.
    pub right: DecidedClass,
}

/// The complete separator set between two designs at one declared environment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DesignSeparator {
    /// The first design.
    pub left: DesignId,
    /// The second.
    pub right: DesignId,
    /// The declared environment both faces sit at.
    pub environment: String,
    /// How many contacts the two read the same decided class at.
    pub agreeing: usize,
    /// Every contact at which they read different decided classes. The complete set, never a
    /// shortest witness.
    pub separating: Vec<SeparatingContact>,
    /// Every contact either of them leaves open. Counted on neither side.
    pub open_carrying: Vec<(u32, u32)>,
}

/// The structural clusters of a design family at one declared environment.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct StructuralClusters {
    /// The schema this reading serializes under.
    pub schema: String,
    /// The declared environment the separator structure was read at.
    pub environment: String,
    /// Every pair's complete separator set, in ascending index order.
    pub separators: Vec<DesignSeparator>,
    /// The connected components of the indistinguishability graph, each sorted by identity, the
    /// components themselves in ascending order of their first member.
    pub components: Vec<Vec<DesignId>>,
    /// Pairs inside one component that the receiver nevertheless separates.
    ///
    /// [definition] A component is **not** an equivalence class of indistinguishability: a contact
    /// one design leaves open enters no separator set of a pair that reads it open, so
    /// indistinguishability is intransitive and a chain can link two designs the receiver tells
    /// apart. This field is that fact, returned rather than hidden.
    pub separated_pairs_inside_a_component: Vec<(DesignId, DesignId)>,
}

impl DesignFamily {
    /// The complete separator set between two designs at one declared environment, over their
    /// **decided** contact classes.
    ///
    /// [definition] This is `physical_occurrence`'s own law at a population that owner's
    /// [`crate::physical_occurrence::PluralFibre`] refuses by construction — the fibre is one
    /// object and these are two. [`DecidedClass::of`] is the same guard, cited rather than
    /// rewritten, so a contact either design leaves open is carried and never counted.
    ///
    /// Lean counterpart: `Foundation/PhysicalOccurrence.lean::separatorSet`, with
    /// `mem_separatorSet_iff`.
    pub fn separator_between(
        &self,
        left: DesignId,
        right: DesignId,
        environment: &str,
    ) -> Result<DesignSeparator, SelectionRefusal> {
        let declared = self.environment(environment)?;
        let left_face = self
            .design(left)?
            .face(declared.label())
            .expect("declare checked a face at every declared environment");
        let right_face = self
            .design(right)?
            .face(declared.label())
            .expect("declare checked a face at every declared environment");
        if left_face.readings.len() != right_face.readings.len() {
            return Err(SelectionRefusal::ContactPopulationDisagrees {
                left,
                right,
                label: declared.label().to_owned(),
                left_contacts: left_face.readings.len(),
                right_contacts: right_face.readings.len(),
            });
        }
        if left_face.aperture != right_face.aperture {
            return Err(SelectionRefusal::AperturesDiffer {
                left,
                right,
                label: declared.label().to_owned(),
            });
        }
        let mut agreeing = 0_usize;
        let mut separating = Vec::new();
        let mut open_carrying = Vec::new();
        for (a, b) in left_face.readings.iter().zip(&right_face.readings) {
            match (DecidedClass::of(a.class), DecidedClass::of(b.class)) {
                (Some(left_class), Some(right_class)) => {
                    if left_class == right_class {
                        agreeing += 1;
                    } else {
                        separating.push(SeparatingContact {
                            pair: a.pair,
                            left: left_class,
                            right: right_class,
                        });
                    }
                }
                _ => open_carrying.push(a.pair),
            }
        }
        Ok(DesignSeparator {
            left,
            right,
            environment: declared.label().to_owned(),
            agreeing,
            separating,
            open_carrying,
        })
    }

    /// **Stage five — the structural clusters**, as the connected components of the
    /// indistinguishability graph over the exact separator structure. Never a float embedding, and
    /// never a threshold on a distance.
    ///
    /// The `candidates² · contacts` comparison count is checked against [`COMPARISON_CEILING`]
    /// before the pass runs.
    pub fn structural_clusters(
        &self,
        candidates: &[DesignId],
        environment: &str,
    ) -> Result<StructuralClusters, SelectionRefusal> {
        let declared = self.environment(environment)?;
        let contacts = candidates
            .first()
            .map(|id| {
                self.design(*id).map(|design| {
                    design
                        .face(declared.label())
                        .map_or(0, |face| face.readings.len())
                })
            })
            .transpose()?
            .unwrap_or(0);
        let implied = comparison_count(candidates.len(), contacts).unwrap_or(usize::MAX);
        if implied > COMPARISON_CEILING {
            return Err(SelectionRefusal::ComparisonPopulationTooLarge {
                stage: "structural clustering",
                implied,
                designs: candidates.len(),
                ceiling: COMPARISON_CEILING,
            });
        }

        let mut separators = Vec::new();
        let mut parent: Vec<usize> = (0..candidates.len()).collect();
        fn root(parent: &mut [usize], mut at: usize) -> usize {
            while parent[at] != at {
                parent[at] = parent[parent[at]];
                at = parent[at];
            }
            at
        }
        for left in 0..candidates.len() {
            for right in (left + 1)..candidates.len() {
                let separator =
                    self.separator_between(candidates[left], candidates[right], environment)?;
                if separator.separating.is_empty() {
                    let (a, b) = (root(&mut parent, left), root(&mut parent, right));
                    if a != b {
                        parent[a] = b;
                    }
                }
                separators.push(separator);
            }
        }

        let mut grouped: BTreeMap<usize, Vec<DesignId>> = BTreeMap::new();
        for (at, id) in candidates.iter().enumerate() {
            let component = root(&mut parent, at);
            grouped.entry(component).or_default().push(*id);
        }
        let mut components: Vec<Vec<DesignId>> = grouped
            .into_values()
            .map(|mut members| {
                members.sort_unstable();
                members
            })
            .collect();
        components.sort();

        let mut separated_pairs_inside_a_component = Vec::new();
        for separator in &separators {
            if separator.separating.is_empty() {
                continue;
            }
            if components.iter().any(|component| {
                component.contains(&separator.left) && component.contains(&separator.right)
            }) {
                separated_pairs_inside_a_component.push((separator.left, separator.right));
            }
        }

        Ok(StructuralClusters {
            schema: "holonic-engine.design-structural-clusters.v1".to_owned(),
            environment: declared.label().to_owned(),
            separators,
            components,
            separated_pairs_inside_a_component,
        })
    }
}

// -------------------------------------------------------------------------------------------
// Stage four: quality-diversity
// -------------------------------------------------------------------------------------------

/// What the quality-diversity stage returns: one entry per structural cluster, carrying **every**
/// design that is best inside it at the declared receiver.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct QualityDiversity {
    /// The schema this stage serializes under.
    pub schema: String,
    /// Which receiver the "best inside a cluster" was read at.
    pub receiver: String,
    /// One entry per cluster: the cluster's members and the best designs inside it. Ties are whole
    /// sets, never one representative chosen out of a plural family.
    pub representatives: Vec<(Vec<DesignId>, Vec<DesignId>)>,
}

impl DesignFamily {
    /// **Stage four — keep the frontier's spread.** One representative set per structural cluster,
    /// rather than the top `k` of one scalar: a cluster whose designs all score badly on a scalar
    /// still contributes its own best, which is what a top-`k` loses.
    pub fn quality_diversity(
        &self,
        clusters: &StructuralClusters,
        ranking: &WorstEnvironmentRanking,
    ) -> Result<QualityDiversity, SelectionRefusal> {
        let sense = self.receiver(&ranking.receiver)?.sense();
        // `clusters` and `ranking` are receipts whose fields are public, so their sizes are
        // caller-declared here even though this owner produced them. The quadratic pass below and
        // the capacity are therefore checked against the same ceiling as every other stage.
        let members: usize = clusters.components.iter().map(Vec::len).sum();
        let implied = comparison_count(members.max(ranking.worst.len()), 1).unwrap_or(usize::MAX);
        if implied > COMPARISON_CEILING {
            return Err(SelectionRefusal::ComparisonPopulationTooLarge {
                stage: "quality-diversity",
                implied,
                designs: members,
                ceiling: COMPARISON_CEILING,
            });
        }
        let table: BTreeMap<DesignId, &WorstVerdict> = ranking
            .worst
            .iter()
            .map(|(id, verdict)| (*id, verdict))
            .collect();
        let mut representatives = Vec::with_capacity(clusters.components.len());
        for component in &clusters.components {
            let inside: Vec<DesignId> = component
                .iter()
                .copied()
                .filter(|id| table.contains_key(id))
                .collect();
            let best: Vec<DesignId> = inside
                .iter()
                .copied()
                .filter(|candidate| {
                    let Some(candidate) = table.get(candidate) else {
                        return false;
                    };
                    !inside.iter().any(|rival| {
                        table.get(rival).is_some_and(|rival| {
                            decided_better(sense, rival, candidate) == Some(true)
                        })
                    })
                })
                .collect();
            representatives.push((component.clone(), best));
        }
        Ok(QualityDiversity {
            schema: "holonic-engine.design-quality-diversity.v1".to_owned(),
            receiver: ranking.receiver.clone(),
            representatives,
        })
    }
}

// -------------------------------------------------------------------------------------------
// The scalar, as one receiver among the others
// -------------------------------------------------------------------------------------------

/// A declared nonnegative weight per receiver.
///
/// [definition] This is **one receiver of the reading vector** and never the identity of a design.
/// No stage of [`DesignFamily::cascade`] calls it; it exists so that the loss a scalar-first
/// cascade causes can be exhibited, which is
/// `Foundation/PresentationCost.lean::unsupported_not_minimizer` at a design family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverWeighting {
    weights: BTreeMap<String, Rat>,
}

impl ReceiverWeighting {
    /// Declare a weighting. Refuses a negative weight, under which a worse design would score
    /// better.
    pub fn declare(
        weights: impl IntoIterator<Item = (String, Rat)>,
    ) -> Result<Self, SelectionRefusal> {
        let weights: BTreeMap<String, Rat> = weights.into_iter().collect();
        for (receiver, weight) in &weights {
            if weight < &Rat::from_integer(0.into()) {
                return Err(SelectionRefusal::NegativeWeight {
                    receiver: receiver.clone(),
                });
            }
        }
        Ok(Self { weights })
    }

    /// The weight declared at one receiver, or zero.
    pub fn weight(&self, receiver: &str) -> Rat {
        self.weights
            .get(receiver)
            .cloned()
            .unwrap_or_else(|| Rat::from_integer(0.into()))
    }
}

impl DesignFamily {
    /// The scalar objective of one design: the weighted sum of its worst readings, oriented so
    /// that **smaller is better** on every axis. A design whose worst verdict at some weighted
    /// receiver is refused, plural in the environments, or a **plural reading** has no scalar, and
    /// `None` is returned rather than a bound of an undecided interval.
    pub fn objective(
        &self,
        design: DesignId,
        weighting: &ReceiverWeighting,
    ) -> Result<Option<Rat>, SelectionRefusal> {
        let mut total = Rat::from_integer(0.into());
        for receiver in &self.receivers {
            let weight = weighting.weight(receiver.name());
            if weight == Rat::from_integer(0.into()) {
                continue;
            }
            let WorstVerdict::Worst { value, .. } = self.worst_over(design, receiver.name())?
            else {
                return Ok(None);
            };
            // A plural reading has no scalar. Summing one of its bounds would resolve an undecided
            // reading into a number, which is exactly what this project refuses; the honest return
            // is that this design has no scalar at this weighting.
            if value.lower != value.upper {
                return Ok(None);
            }
            // Orientation: a greater-is-better receiver enters the objective negated, so that the
            // objective is minimized on every axis. The reading itself is untouched.
            let contribution = match receiver.sense() {
                Sense::SmallerIsBetter => value.lower.clone(),
                Sense::GreaterIsBetter => -value.lower.clone(),
            };
            total += weight * contribution;
        }
        Ok(Some(total))
    }

    /// Every candidate minimizing the declared weighting, in ascending identity order. A candidate
    /// with no scalar is absent rather than ordered.
    ///
    /// Lean counterpart: the hypothesis of `PresentationCost.minimizer_isFrontierPoint`, and
    /// `PresentationCost.unsupported_not_minimizer` is why this is never the cascade.
    pub fn scalar_minimizers(
        &self,
        candidates: &[DesignId],
        weighting: &ReceiverWeighting,
    ) -> Result<Vec<DesignId>, SelectionRefusal> {
        let implied = comparison_count(candidates.len(), 1).unwrap_or(usize::MAX);
        if implied > COMPARISON_CEILING {
            return Err(SelectionRefusal::ComparisonPopulationTooLarge {
                stage: "scalar objective",
                implied,
                designs: candidates.len(),
                ceiling: COMPARISON_CEILING,
            });
        }
        let mut scored: Vec<(DesignId, Rat)> = Vec::with_capacity(candidates.len());
        for id in candidates {
            if let Some(value) = self.objective(*id, weighting)? {
                scored.push((*id, value));
            }
        }
        let Some(best) = scored.iter().map(|(_, value)| value.clone()).min() else {
            return Ok(Vec::new());
        };
        let mut minimizers: Vec<DesignId> = scored
            .into_iter()
            .filter(|(_, value)| *value == best)
            .map(|(id, _)| id)
            .collect();
        minimizers.sort_unstable();
        Ok(minimizers)
    }
}

// -------------------------------------------------------------------------------------------
// The design situation and the merge verdict
// -------------------------------------------------------------------------------------------

/// A design situated at one declared environment: the carrier of the design situation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct SituatedDesign {
    /// The design's index in the family's declaration order.
    pub design: usize,
    /// The declared environment's index.
    pub environment: usize,
}

/// One admitted future transformation: a generator of the design situation, and evidence that the
/// passage owner admits it.
///
/// [definition] Every variant is founded by a real [`Passage`]: a vertical environment change
/// through [`DesignFamily::admit_environment_change`], which builds
/// [`Passage::environment_change`] for **every** design in the family so the generator is
/// evidenced wherever it acts, and a horizontal mutation through
/// [`DesignFamily::admit_mutation`], which builds [`Passage::mutation`] and inherits every
/// refusal that constructor makes — an environment that also moved, a changed target, an indel, a
/// site the sequences do not differ at.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum AdmittedTransformation {
    /// The vertical environment-change passage to a declared environment.
    EnvironmentChange {
        /// The declared environment it leaves.
        from: usize,
        /// The declared environment it arrives at.
        to: usize,
        /// The ground the environment passage was admitted on.
        ground: String,
    },
    /// The horizontal mutation passage carrying one design to another at one environment.
    Mutation {
        /// The design it leaves.
        from: usize,
        /// The design it arrives at.
        to: usize,
        /// The declared environment both sit at.
        environment: usize,
        /// The site the mutation changes.
        site: u32,
    },
}

impl AdmittedTransformation {
    /// Its declared name, which is what a separator reports.
    pub fn name(&self) -> String {
        match self {
            Self::EnvironmentChange { from, to, .. } => {
                format!("environment change {from} -> {to}")
            }
            Self::Mutation {
                from,
                to,
                environment,
                site,
            } => format!("mutation {from} -> {to} at site {site}, environment {environment}"),
        }
    }
}

impl DesignFamily {
    /// **Admit a vertical environment change as a generator**, by building the real
    /// [`Passage::environment_change`] for every design in the family.
    ///
    /// Refuses whatever [`EnvironmentPassage::declare`] refuses — a divergent axis the declaration
    /// does not account for, an unstated ground — and whatever [`Passage::environment_change`]
    /// refuses. The generator is admitted only where the passage is.
    pub fn admit_environment_change(
        &self,
        from: &str,
        to: &str,
        ground: impl Into<String>,
        accounted: impl IntoIterator<Item = CoordinateName>,
    ) -> Result<AdmittedTransformation, SelectionRefusal> {
        let ground = ground.into();
        let accounted: Vec<CoordinateName> = accounted.into_iter().collect();
        let from_declared = self.environment(from)?;
        let to_declared = self.environment(to)?;
        let from_at = self
            .environments
            .iter()
            .position(|declared| declared.label() == from)
            .expect("the label was just resolved");
        let to_at = self
            .environments
            .iter()
            .position(|declared| declared.label() == to)
            .expect("the label was just resolved");
        for design in &self.designs {
            let passage = EnvironmentPassage::declare(
                ground.clone(),
                from_declared.environment().clone(),
                to_declared.environment().clone(),
                accounted.iter().copied(),
            )?;
            let source = design
                .face(from)
                .expect("declare checked a face at every declared environment");
            let target = design
                .face(to)
                .expect("declare checked a face at every declared environment");
            Passage::<Vertical>::environment_change(source, target, passage)?;
        }
        Ok(AdmittedTransformation::EnvironmentChange {
            from: from_at,
            to: to_at,
            ground,
        })
    }

    /// **Admit a horizontal mutation as a generator**, by building the real [`Passage::mutation`]
    /// between the two designs' faces at one declared environment.
    ///
    /// Refuses whatever that constructor refuses. A mutation is horizontal and an environment
    /// change is vertical; the passage owner keeps them apart by type and this owner inherits that
    /// separation rather than re-deciding it.
    pub fn admit_mutation(
        &self,
        from: DesignId,
        to: DesignId,
        environment: &str,
        site: u32,
    ) -> Result<AdmittedTransformation, SelectionRefusal> {
        let declared = self.environment(environment)?;
        let environment_at = self
            .environments
            .iter()
            .position(|other| other.label() == declared.label())
            .expect("the label was just resolved");
        let source = self
            .design(from)?
            .face(declared.label())
            .expect("declare checked a face at every declared environment");
        let target = self
            .design(to)?
            .face(declared.label())
            .expect("declare checked a face at every declared environment");
        Passage::<Horizontal>::mutation(source, target, site)?;
        Ok(AdmittedTransformation::Mutation {
            from: self.design_index(from)?,
            to: self.design_index(to)?,
            environment: environment_at,
            site,
        })
    }

    /// **The design situation**: the [`Situation`] whose generators are the admitted future
    /// transformations and whose receivers are the declared receiver family, read at the carrier's
    /// own environment index.
    ///
    /// [definition] Design equivalence **is** `RelationLadder.EqualPotential` here, and nothing is
    /// redefined. A generator acts by the index change its passage performs and is the identity
    /// elsewhere, so it is total: a mutation carries `(from, e)` to `(to, e)` and fixes every other
    /// design, exactly the extension by the identity that makes the horizontal passage a map of the
    /// whole carrier.
    ///
    /// `history_ceiling` is the declared history-length bound the separator search will run under;
    /// [`Situation::declare`] checks the implied ordered-history population with checked arithmetic
    /// before anything is enumerated.
    pub fn design_situation(
        &self,
        transformations: &[AdmittedTransformation],
        history_ceiling: usize,
    ) -> Result<Situation<SituatedDesign, ReceiverReading>, SelectionRefusal> {
        if transformations.len() > TRANSFORMATION_CEILING {
            return Err(SelectionRefusal::TransformationFamilyTooLarge {
                declared: transformations.len(),
                ceiling: TRANSFORMATION_CEILING,
            });
        }
        // `AdmittedTransformation`'s fields are public, so a value that did not come from
        // `admit_environment_change` or `admit_mutation` can name an index this family does not
        // carry. Every index is checked against the family here, before a generator is built.
        for transformation in transformations {
            match transformation {
                AdmittedTransformation::EnvironmentChange { from, to, .. } => {
                    for at in [from, to] {
                        if *at >= self.environments.len() {
                            return Err(SelectionRefusal::EnvironmentAbsent {
                                label: format!("index {at}"),
                            });
                        }
                    }
                }
                AdmittedTransformation::Mutation {
                    from,
                    to,
                    environment,
                    ..
                } => {
                    for at in [from, to] {
                        if *at >= self.designs.len() {
                            return Err(SelectionRefusal::DesignAbsent {
                                id: DesignId(*at as u64),
                            });
                        }
                    }
                    if *environment >= self.environments.len() {
                        return Err(SelectionRefusal::EnvironmentAbsent {
                            label: format!("index {environment}"),
                        });
                    }
                }
            }
        }
        let generators = transformations
            .iter()
            .map(|transformation| {
                let name = transformation.name();
                let transformation = transformation.clone();
                NamedGenerator::new(name, move |situated: &SituatedDesign| {
                    Ok(match &transformation {
                        AdmittedTransformation::EnvironmentChange { from, to, .. } => {
                            if situated.environment == *from {
                                SituatedDesign {
                                    design: situated.design,
                                    environment: *to,
                                }
                            } else {
                                *situated
                            }
                        }
                        AdmittedTransformation::Mutation {
                            from,
                            to,
                            environment,
                            ..
                        } => {
                            if situated.design == *from && situated.environment == *environment {
                                SituatedDesign {
                                    design: *to,
                                    environment: *environment,
                                }
                            } else {
                                *situated
                            }
                        }
                    })
                })
            })
            .collect();

        // The readings are cloned **once** into a shared table the receiver closures hold by
        // reference count, so the situation owns everything it reads without copying the whole
        // reading vector per declared receiver.
        let table: Vec<Vec<Vec<ReceiverReading>>> = self
            .designs
            .iter()
            .map(|design| {
                self.receivers
                    .iter()
                    .map(|receiver| {
                        self.environments
                            .iter()
                            .map(|environment| {
                                design
                                    .reading(receiver.name(), environment.label())
                                    .expect("declare checked that every axis is stated")
                                    .clone()
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let table = Arc::new(table);

        let receivers = self
            .receivers
            .iter()
            .enumerate()
            .map(|(at, receiver)| {
                let table = Arc::clone(&table);
                NamedReceiver::new(receiver.name().to_owned(), move |situated: &SituatedDesign| {
                    // An out-of-range carrier is a typed refusal, never a panic. The relation
                    // ladder's refusal family has no out-of-range-carrier variant, so this names
                    // the index through `UndeclaredGenerator`; the index reported is the design.
                    table
                        .get(situated.design)
                        .and_then(|design| design.get(at))
                        .and_then(|receiver| receiver.get(situated.environment))
                        .cloned()
                        .ok_or(LadderRefusal::UndeclaredGenerator {
                            index: situated.design,
                            declared: table.len(),
                        })
                })
            })
            .collect();

        Ok(Situation::declare(generators, receivers, history_ceiling)?)
    }
}

/// **What a merge question returns.** There are exactly three answers and only one licenses a
/// merge.
///
/// Lean counterpart: `Foundation/DesignSelection.lean::MergeVerdict`, with
/// `only_equivalentBy_licenses_merge`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MergeVerdict<F> {
    /// A separating `(history, receiver)` refutes the collapse. It is returned as content.
    Refuted {
        /// The separator.
        separator: Box<Separator<F>>,
    },
    /// The declared bound was exhausted without a separator. **This licenses nothing**: it is not
    /// equal potential, and it is not a merge.
    NotSeparatedWithinBound {
        /// The history-length ceiling the search ran under.
        history_length: usize,
        /// How many ordered histories were examined.
        histories_examined: usize,
        /// How many receivers each history was read by.
        receivers: usize,
    },
    /// An exhibited equivariant isomorphism of the situation carries one design to the other, over
    /// a probe the caller declared to be the whole carrier and which
    /// [`Situation::check_automorphism`] accepted.
    EquivalentBy {
        /// The isomorphism's declared name.
        isomorphism: String,
        /// How many occurrences the equivariance was checked at.
        probe: usize,
    },
}

impl<F> MergeVerdict<F> {
    /// Whether this verdict licenses a merge. True for [`MergeVerdict::EquivalentBy`] and for
    /// nothing else.
    ///
    /// Lean counterpart: `MergeVerdict.licensesMerge`, with
    /// `notSeparatedWithinBound_does_not_license_merge`.
    pub const fn licenses_merge(&self) -> bool {
        matches!(self, Self::EquivalentBy { .. })
    }

    /// A short name for receipts and refusals.
    pub const fn label(&self) -> &'static str {
        match self {
            Self::Refuted { .. } => "Refuted",
            Self::NotSeparatedWithinBound { .. } => "NotSeparatedWithinBound",
            Self::EquivalentBy { .. } => "EquivalentBy",
        }
    }
}

/// **The merge question, answered from a declared situation.**
///
/// The bounded separator search runs first and its result is read before any declaration, so a
/// separator **overrides** a declared isomorphism: the separator is evidence and the declaration
/// is not. This is [`Situation::classify`]'s own order, and
/// [`crate::relation_ladder::ClassificationNote::IsomorphismContradictedBySeparator`] is the note
/// it records.
///
/// Lean counterpart: `oneSeparatingFutureReceiverRefutesTheMerge` for the refuting arm and
/// `RelationLadder.situationAutoImpliesEqualPotential` for the licensing one.
pub fn merge_verdict<S, F>(
    situation: &Situation<S, F>,
    left: &S,
    right: &S,
    declared: &Declarations<'_, S>,
) -> Result<MergeVerdict<F>, SelectionRefusal>
where
    S: Clone + PartialEq,
    F: Clone + PartialEq,
{
    let classification: Classification<S, F> = situation.classify(left, right, declared)?;
    if let Some(separator) = classification.separator {
        return Ok(MergeVerdict::Refuted {
            separator: Box::new(separator),
        });
    }
    if matches!(
        classification.strongest,
        Rung::Identity | Rung::Isomorphism
    ) {
        let probe = declared
            .automorphism
            .as_ref()
            .map_or(0, |claim| claim.probe.len());
        let isomorphism = declared
            .automorphism
            .as_ref()
            .map_or_else(|| "identity".to_owned(), |claim| claim.automorphism.name().to_owned());
        return Ok(MergeVerdict::EquivalentBy { isomorphism, probe });
    }
    Ok(match classification.potential {
        PotentialVerdict::NotSeparatedWithinBound {
            history_length,
            histories_examined,
            receivers,
        } => MergeVerdict::NotSeparatedWithinBound {
            history_length,
            histories_examined,
            receivers,
        },
        // `classify` returns a separator exactly when the potential verdict is `Separated`, so
        // this arm is unreached; it is written as a refutation rather than a panic so that no
        // future change to that owner can turn a separated verdict into an unwind here.
        PotentialVerdict::Separated(separator) => MergeVerdict::Refuted {
            separator: Box::new(separator),
        },
    })
}

/// A merged class of designs. **There is no other constructor**, so a
/// [`MergeVerdict::NotSeparatedWithinBound`] cannot reach one: the type is the guarantee, not a
/// policy.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MergedClass {
    /// The schema this class serializes under.
    pub schema: String,
    members: Vec<DesignId>,
    licensed_by: String,
    probe: usize,
}

impl MergedClass {
    /// The merged designs, in ascending identity order.
    pub fn members(&self) -> &[DesignId] {
        &self.members
    }

    /// The isomorphism that licensed the merge, by name.
    pub fn licensed_by(&self) -> &str {
        &self.licensed_by
    }

    /// How many occurrences the equivariance was checked at.
    pub const fn probe(&self) -> usize {
        self.probe
    }
}

/// **Merge two designs, if and only if a verdict licensed it.**
///
/// Returns [`SelectionRefusal::MergeNotLicensed`] naming the verdict otherwise — in particular for
/// [`MergeVerdict::NotSeparatedWithinBound`], which a bounded search is the only thing that can
/// return.
pub fn merge<F>(
    left: DesignId,
    right: DesignId,
    verdict: &MergeVerdict<F>,
) -> Result<MergedClass, SelectionRefusal> {
    let MergeVerdict::EquivalentBy { isomorphism, probe } = verdict else {
        return Err(SelectionRefusal::MergeNotLicensed {
            verdict: verdict.label(),
        });
    };
    let mut members = vec![left, right];
    members.sort_unstable();
    members.dedup();
    Ok(MergedClass {
        schema: "holonic-engine.design-merged-class.v1".to_owned(),
        members,
        licensed_by: isomorphism.clone(),
        probe: *probe,
    })
}

// -------------------------------------------------------------------------------------------
// The cascade
// -------------------------------------------------------------------------------------------

/// What the whole cascade returns: each stage's own result, in the plan's order, with nothing
/// collapsed into a single number anywhere.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CascadeReport {
    /// The schema this report serializes under.
    pub schema: String,
    /// Stage one.
    pub admitted: AdmissionStage,
    /// Stage two: the Pareto frontier over the `(receiver, environment)` axes.
    pub frontier: Vec<DesignId>,
    /// Stage three: one ranking per declared receiver, over the frontier.
    pub rankings: Vec<WorstEnvironmentRanking>,
    /// Stage five's clusters, which stage four selects representatives from.
    pub clusters: StructuralClusters,
    /// Stage four, at the receiver the caller named.
    pub diversity: QualityDiversity,
    /// The exact size of the family each stage ran on.
    pub population: [BigUint; 3],
}

impl DesignFamily {
    /// **The cascade, in the plan's order**: hard constraints, Pareto filtering, worst-environment
    /// ranking, quality-diversity, structural clustering.
    ///
    /// Clustering is computed before the quality-diversity selection because that selection is
    /// *per cluster*; the plan's ordering names the stages, and the data dependency is what runs.
    /// No stage reads a scalar: [`DesignFamily::scalar_minimizers`] is not called here.
    pub fn cascade(
        &self,
        constraints: &[HardConstraint],
        clustering_environment: &str,
        diversity_receiver: &str,
    ) -> Result<CascadeReport, SelectionRefusal> {
        let admitted = self.admit(constraints);
        let frontier = self.frontier(&admitted.admitted)?;
        let mut rankings = Vec::with_capacity(self.receivers.len());
        for receiver in &self.receivers {
            rankings.push(self.rank_by_worst_environment(&frontier, receiver.name())?);
        }
        let clusters = self.structural_clusters(&frontier, clustering_environment)?;
        let ranking = self.rank_by_worst_environment(&frontier, diversity_receiver)?;
        let diversity = self.quality_diversity(&clusters, &ranking)?;
        Ok(CascadeReport {
            schema: "holonic-engine.design-cascade.v1".to_owned(),
            population: [
                BigUint::from(self.designs.len()),
                BigUint::from(admitted.admitted.len()),
                BigUint::from(frontier.len()),
            ],
            admitted,
            frontier,
            rankings,
            clusters,
            diversity,
        })
    }
}

/// The occurrence identities of a design's faces, for a receipt.
pub fn design_occurrences(design: &Design) -> Vec<OccurrenceId> {
    let mut out: Vec<OccurrenceId> = design
        .faces
        .values()
        .map(|face| face.occurrence)
        .collect();
    out.sort_unstable_by_key(|id| id.0);
    out.dedup();
    out
}

/// The contact class of one addressed pair in a design's face, for a receipt.
pub fn design_class_at(design: &Design, label: &str, pair: (u32, u32)) -> Option<ContactClass> {
    design
        .face(label)?
        .readings
        .iter()
        .find(|reading| reading.pair == pair)
        .map(|reading| reading.class)
}

#[cfg(test)]
#[path = "design_selection/tests.rs"]
mod tests;
