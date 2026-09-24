//! **Capability, local chart and receiver atlas: an embedding is an atlas of placements.**
//!
//! [definition] This module is the executable owner of item **C6** of
//! `docs/plans/THE_CONTINUING_OBJECT_IS_THE_SHARED_CARRIER.md`. Its Lean counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverAtlas.lean`
//! (namespace `Soma.Holonics.Foundation.Atlas`), and the correspondence is the deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `CapabilityKind` | [`CapabilityKind`] |
//! | `Capability`, `Constituted`, `SuppliedCapability` | [`Capability`], [`SuppliedCapability`] |
//! | `no_operation_from_the_carrier_alone` | [`NoCapability`], whose `Parameters` is uninhabited |
//! | `weightedSquareMetric`, `operation_is_supplied_not_conferred` | [`WeightedSquareMetric`] and `supplied_metric_is_not_conferred_by_the_carrier` |
//! | `LocalChart`, `preimageFibre_subset_fibre`, `reading_none_of_metric_none` | [`LocalChart`] and its `preimage_fibre` / `reading` |
//! | `Cocycle`, `CocycleDefect`, `cocycle_iff_isEmpty_defect` | [`ReceiverAtlas::check_cocycle`], [`CocycleDefect`] |
//! | `CocycleDefect.defect_is_holonomy_not_loss` | [`CocycleDefect::both_routes_reopen`] |
//! | `ChartTransition`, `ChartTransition.residual_reopens` | [`ChartMap`], [`ChartMap::check_reopen`] |
//! | `ReceiverAtlas`, `CoherentPlacement`, `AtlasGluing`, `atlasGluing_total` | [`ReceiverAtlas`], [`CoherentPlacement`], [`AtlasGluing`], [`ReceiverAtlas::glue`] |
//! | `ChartCocycle.placementEquiv` | the `Unique` arm returned for an invertible, cocycle-satisfying atlas |
//! | `ShiftAtlas.theEmbeddingIsNotOneVector` | [`shift_atlas`] and its obstructed return |
//! | `AtlasIndistinguishable`, `indistinguishable_of_refinement` | [`ReceiverAtlas::indistinguishable`] |
//!
//! It additionally owns item **R7** of `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`,
//! the separating atlas theorem, in the same Lean file:
//!
//! | Lean | Rust |
//! |---|---|
//! | `Separates`, `Separates.mono`, `Separates.of_refinement` | [`ReceiverAtlas::is_separating`] and [`SeparatingVerdict`] |
//! | `SeparatingAtlas.fullProbeAtlas`, `fullProbeAtlas_separates` | the `full_probe_atlas` of this module's tests, and [`ReceiverAtlas::separate`] |
//! | `SeparatingAtlas.markov`, `identity_probe_determines_the_operator` | the `k = 1` Markov chart of that atlas |
//! | `SeparatingAtlas.pow_eq_aeval_modByMonic_charpoly`, `markov_truncation` | `every_markov_parameter_is_a_combination_of_the_first_n` |
//! | `SeparatingAtlas.MarkovTwoNSuffices` | **open**: named, not implemented, and not claimed |
//! | `SeparatingAtlas.spectralTopologicalInsufficiency` | [`AtlasInsufficiency`] and `the_spectral_and_topological_atlas_cannot_separate_two_non_isomorphic_complexes` |
//! | `RebaseEquivariant`, `SourceAccountable`, `DeclarationIndependent`, `causalChord_is_rebase_equivariant` | [`AtlasContract`], [`ContractStatus`] and [`contract_ledger`] |
//!
//! # The thesis
//!
//! [project-postulate] **An embedding is an atlas of placements whose content is its transition
//! maps, not one global vector.** The three executable statements that make that exact are
//! [`ReceiverAtlas::glue`] returning `Unique` for an atlas whose transitions are all invertible and
//! satisfy the cocycle; [`shift_atlas`] returning `Obstructed` although every chart reads a
//! nonempty region into an inhabited coordinate; and [`ReceiverAtlas::indistinguishable`] returning
//! `true` for two occurrences one atlas cannot separate and `false` once a richer chart is added.
//!
//! # A structure is supplied, never conferred
//!
//! [definition] `docs/canon/TABLET_THE_MANIFOLD.md` §16: every geometry is a reduction of the
//! structure group, so `GL(n)` is no structure and `O(n)` is a supplied metric. `docs/HOLON.md`: "A
//! gradient, metric, mass, distribution, tensor rank or reversible decoder is additional
//! mathematical structure." A [`LocalChart`] with no [`SuppliedCapability`] returns `None` from
//! [`LocalChart::reading`] — not a zero, and not a default.
//!
//! # No floats
//!
//! [implemented-exact] Nothing here decides or carries a value in floating point. Coordinates are
//! exact integers, `BigInt`, `BigUint` or the exact faces of
//! [`crate::grain_tower`]; the weighted metric is `BigInt`-valued.

use std::collections::{BTreeMap, BTreeSet};
use std::convert::Infallible;
use std::fmt::{self, Debug};
use std::marker::PhantomData;

use num_bigint::BigInt;
use num_traits::{One, Zero};
use holonics::geometry::Rat;

use crate::algebraic::{CausalChain, ComparativeMultiplicity, GradedCausalComplex};
use crate::causal::EventId;
use holonics::causal_chord::{ChordRefusal, Linearization, causal_chord, transfer_function};
use holonics::restriction::tower::Transition;
use holonics::exact_linear::ExactRatMatrix;
use crate::grain_tower::{GrainFace, GrainPair, GrainSelection, SelectionResidual};
use crate::hodge_receiver::{
    BoundaryCondition, HodgeError, HodgeOperator, MetricDeclaration, hodge_decomposition,
    hodge_reading,
};
use crate::junction_law::{
    Interface, JointUnits, JunctionField, JunctionRefusal, JunctionVerdict, ResistiveNetwork, Side,
    check_junction,
};
use crate::physical_constraint_complex::{
    ConstraintComponentId, ConstraintEdge, ConstraintVertexId, ContactClass, CoordinateBox3,
};
use crate::physical_constraint_grading::EdgeProvenance;
use crate::physicochemical_receiver::{
    ClassPair, HydrogenBondWindow, PairPopulation, PairWorkBound, PhysicochemicalRefusal,
    RigidMotion, composition_under_declared_protonation, electrostatic_enclosure,
    hydrogen_bond_candidates, steric_overlaps, worked_presentation,
};
use crate::topological_receiver::{
    ApertureFiltration, Coefficients, FiltrationOrder, OrderLaw, TopologicalError,
    grade_zero_agreement, persistence,
};
use crate::rigidity_receiver::{
    ExactConfiguration, MaxwellCount, RigidityError, RigidityJacobian, RigidityReading,
    TrivialMotionReading, removal_sensitivity, rigidity_reading, verify_removal_sensitivity,
};

// -------------------------------------------------------------------------------------------
// C6 (a) — Capability
// -------------------------------------------------------------------------------------------

/// The four kinds of structure the canon names as supplied rather than conferred.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::CapabilityKind`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CapabilityKind {
    /// Lengths and angles: an `O(n)` or `CO(n)` reduction.
    Metric,
    /// Differentiation: a smooth structure, or a discrete cochain complex with `d`.
    SmoothStructure,
    /// Continuation: a germ and a path.
    AnalyticData,
    /// Scaling exponents: an identified contraction family.
    ScalingFamily,
}

/// A structure that *may* be supplied to a carrier: the parameters it would take, the law they
/// must satisfy, the identities the resulting operation obeys, and the operation itself.
///
/// The operation is binary because a situated reading is always a comparison — AGENTS.md's
/// "difference is the only thing that is real". A unary reading ignores its second argument.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::Capability`.
pub trait Capability {
    /// What the operation reads.
    type Carrier: Clone + Eq + Debug;
    /// What must be supplied.
    type Parameters: Clone + Eq + Debug;
    /// What the operation returns.
    type Value: Clone + Eq + Debug;

    /// Which supplied structure this is.
    fn kind(&self) -> CapabilityKind;

    /// The law the supplied parameters must satisfy.
    ///
    /// Lean counterpart: `Capability.admits`.
    fn admits(&self, parameter: &Self::Parameters) -> bool;

    /// The identities the operation obeys once the parameters are admitted.
    ///
    /// Lean counterpart: `Capability.laws`.
    fn laws_hold(&self, parameter: &Self::Parameters) -> bool;

    /// The operation that becomes available exactly when the law is discharged.
    ///
    /// Lean counterpart: `Capability.operations`.
    fn operate(
        &self,
        parameter: &Self::Parameters,
        left: &Self::Carrier,
        right: &Self::Carrier,
    ) -> Self::Value;
}

/// Why a capability was not constituted.
///
/// Lean counterpart: the `admitted` and `lawful` fields of `Constituted`, which Lean carries as
/// proof obligations. Here they are asked and a failure is returned by name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CapabilityRefusal<P> {
    /// The supplied parameters do not satisfy the capability's admission law.
    ParametersNotAdmitted {
        /// What was supplied.
        parameter: P,
        /// Which structure refused it.
        kind: CapabilityKind,
    },
    /// The parameters are admissible but the identities the operation must obey do not hold.
    LawsNotDischarged {
        /// What was supplied.
        parameter: P,
        /// Which structure refused it.
        kind: CapabilityKind,
    },
}

impl<P: Debug> fmt::Display for CapabilityRefusal<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ParametersNotAdmitted { parameter, kind } => write!(
                f,
                "{kind:?} refuses the supplied parameters {parameter:?}: they are not admissible"
            ),
            Self::LawsNotDischarged { parameter, kind } => write!(
                f,
                "{kind:?} refuses the supplied parameters {parameter:?}: its identities do not hold"
            ),
        }
    }
}

impl<P: Debug> std::error::Error for CapabilityRefusal<P> {}

/// A capability together with the witness that constitutes it. There is no way to build one
/// without discharging both the admission law and the identities, so the operation is available
/// exactly when the witness is.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::SuppliedCapability` and `Constituted`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuppliedCapability<C: Capability> {
    capability: C,
    parameter: C::Parameters,
}

impl<C: Capability> SuppliedCapability<C> {
    /// Supply the structure. A parameter the capability does not admit, or one whose identities do
    /// not hold, is refused by name rather than accepted with a warning.
    pub fn supply(
        capability: C,
        parameter: C::Parameters,
    ) -> Result<Self, CapabilityRefusal<C::Parameters>> {
        if !capability.admits(&parameter) {
            return Err(CapabilityRefusal::ParametersNotAdmitted {
                parameter,
                kind: capability.kind(),
            });
        }
        if !capability.laws_hold(&parameter) {
            return Err(CapabilityRefusal::LawsNotDischarged {
                parameter,
                kind: capability.kind(),
            });
        }
        Ok(Self {
            capability,
            parameter,
        })
    }

    /// Which structure was supplied.
    pub fn kind(&self) -> CapabilityKind {
        self.capability.kind()
    }

    /// What was supplied.
    pub fn parameter(&self) -> &C::Parameters {
        &self.parameter
    }

    /// The operation the witness makes available.
    ///
    /// Lean counterpart: `Constituted.operation`.
    pub fn operation(&self, left: &C::Carrier, right: &C::Carrier) -> C::Value {
        self.capability.operate(&self.parameter, left, right)
    }
}

/// The capability a carrier supplies **by itself**: none. Its `Parameters` type is uninhabited, so
/// no witness can ever be constructed and no operation can ever be read from it.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::emptyCapability` and
/// `no_operation_from_the_carrier_alone`. Here the theorem is the type: `Infallible` has no value,
/// so `SuppliedCapability::<NoCapability<_>>::supply` cannot even be called.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct NoCapability<Z>(PhantomData<Z>);

impl<Z: Clone + Eq + Debug> Capability for NoCapability<Z> {
    type Carrier = Z;
    type Parameters = Infallible;
    type Value = ();

    fn kind(&self) -> CapabilityKind {
        CapabilityKind::Metric
    }

    fn admits(&self, parameter: &Infallible) -> bool {
        match *parameter {}
    }

    fn laws_hold(&self, parameter: &Infallible) -> bool {
        match *parameter {}
    }

    fn operate(&self, parameter: &Infallible, _left: &Z, _right: &Z) {
        match *parameter {}
    }
}

/// A weighted square metric on the exact integer plane: `a·(x₁−y₁)² + b·(x₂−y₂)²`.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::weightedSquareMetric`. The parameters are two
/// strictly positive integer weights and the value is an exact `BigInt`; no float participates.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct WeightedSquareMetric;

impl Capability for WeightedSquareMetric {
    type Carrier = (BigInt, BigInt);
    type Parameters = (BigInt, BigInt);
    type Value = BigInt;

    fn kind(&self) -> CapabilityKind {
        CapabilityKind::Metric
    }

    fn admits(&self, parameter: &Self::Parameters) -> bool {
        parameter.0 > BigInt::zero() && parameter.1 > BigInt::zero()
    }

    fn laws_hold(&self, parameter: &Self::Parameters) -> bool {
        // The identity a metric owes: a point is at distance zero from itself.
        let point = (BigInt::from(7), BigInt::from(-3));
        self.operate(parameter, &point, &point).is_zero()
    }

    fn operate(
        &self,
        parameter: &Self::Parameters,
        left: &Self::Carrier,
        right: &Self::Carrier,
    ) -> BigInt {
        let dx = &left.0 - &right.0;
        let dy = &left.1 - &right.1;
        &parameter.0 * (&dx * &dx) + &parameter.1 * (&dy * &dy)
    }
}

// -------------------------------------------------------------------------------------------
// C6 (b) — LocalChart
// -------------------------------------------------------------------------------------------

/// A **local chart**: where it reads, what it returns, the retained preimage it never drops, and
/// the structure — if any — that was supplied to its coordinate.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::LocalChart`. Lean's `Region : Set X` and
/// `place : Region → Coordinate` are one map here: the chart reads exactly the occurrences its
/// placement map carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalChart<X, Z, M = NoCapability<Z>>
where
    X: Ord + Clone + Debug,
    Z: Clone + Eq + Debug,
    M: Capability<Carrier = Z>,
{
    name: String,
    placements: BTreeMap<X, Z>,
    metric: Option<SuppliedCapability<M>>,
}

impl<X, Z, M> LocalChart<X, Z, M>
where
    X: Ord + Clone + Debug,
    Z: Clone + Eq + Debug,
    M: Capability<Carrier = Z>,
{
    /// Found a chart from its placements and the structure — if any — supplied to its coordinate.
    pub fn founded(
        name: impl Into<String>,
        placements: impl IntoIterator<Item = (X, Z)>,
        metric: Option<SuppliedCapability<M>>,
    ) -> Self {
        Self {
            name: name.into(),
            placements: placements.into_iter().collect(),
            metric,
        }
    }

    /// The chart's declared name. Charts are addressed by name inside an atlas.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Whether this chart reads that occurrence at all.
    ///
    /// Lean counterpart: membership in `LocalChart.Region`.
    pub fn reads(&self, occurrence: &X) -> bool {
        self.placements.contains_key(occurrence)
    }

    /// Where this chart places that occurrence, when it reads it.
    ///
    /// Lean counterpart: `LocalChart.place`.
    pub fn place(&self, occurrence: &X) -> Option<&Z> {
        self.placements.get(occurrence)
    }

    /// Every occurrence in the chart's region.
    pub fn region(&self) -> BTreeSet<X> {
        self.placements.keys().cloned().collect()
    }

    /// The occurrences this chart actually places at one coordinate. The population behind a face
    /// is retained, never dropped.
    ///
    /// Lean counterpart: `LocalChart.preimageFibre` and `preimageFibre_subset_fibre`.
    pub fn preimage_fibre(&self, coordinate: &Z) -> BTreeSet<X> {
        self.placements
            .iter()
            .filter(|(_, z)| *z == coordinate)
            .map(|(x, _)| x.clone())
            .collect()
    }

    /// Which structure, if any, was supplied to this chart's coordinate.
    pub fn supplied(&self) -> Option<CapabilityKind> {
        self.metric.as_ref().map(SuppliedCapability::kind)
    }

    /// The reading the supplied structure makes available. A chart with no supplied structure
    /// returns `None`: not a zero, not a default.
    ///
    /// Lean counterpart: `LocalChart.reading` and `reading_none_of_metric_none`.
    pub fn reading(&self, left: &Z, right: &Z) -> Option<M::Value> {
        self.metric
            .as_ref()
            .map(|supplied| supplied.operation(left, right))
    }
}

// -------------------------------------------------------------------------------------------
// C6 (c/d) — the transition between charts, carrying its residual
// -------------------------------------------------------------------------------------------

/// Why an atlas operation was refused. Every failure is returned as content.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtlasRefusal {
    /// A transition was declared between names the atlas does not carry.
    ChartAbsent {
        /// The name that is not a chart of this atlas.
        name: String,
    },
    /// A transition was declared twice for one ordered pair of charts.
    TransitionAlreadyDeclared {
        /// The source chart.
        from: String,
        /// The target chart.
        to: String,
    },
    /// A chart map was asked for a coordinate it does not read.
    CoordinateNotInChart {
        /// Which map refused.
        map: String,
        /// What kind of coordinate it expects.
        expected: &'static str,
    },
    /// A reopening did not return its source exactly.
    ReopenFailed {
        /// Which map refused.
        map: String,
    },
    /// A declared bounded class is wider than the separating search's ceiling admits.
    DeclaredClassTooWide {
        /// How many members were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The unordered pairs of a declared class do not fit a machine integer.
    DeclaredClassPairsOverflow {
        /// How many members were declared.
        declared: usize,
    },
    /// No transition is declared between two named charts. This is an undiscovered relation, not
    /// a denial: `docs/canon/TABLET_THE_CHART.md` §10.1.
    TransitionUndeclared {
        /// The source chart.
        from: String,
        /// The target chart.
        to: String,
    },
}

impl fmt::Display for AtlasRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ChartAbsent { name } => write!(f, "the atlas carries no chart named {name:?}"),
            Self::TransitionAlreadyDeclared { from, to } => {
                write!(f, "a transition {from:?} -> {to:?} is already declared")
            }
            Self::CoordinateNotInChart { map, expected } => write!(
                f,
                "the chart map {map:?} reads a {expected} coordinate and was given another"
            ),
            Self::ReopenFailed { map } => {
                write!(f, "the chart map {map:?} did not reopen its source exactly")
            }
            Self::DeclaredClassTooWide { declared, ceiling } => write!(
                f,
                "a declared class of {declared} members exceeds the separating search's ceiling \
                 {ceiling}; nothing was allocated"
            ),
            Self::DeclaredClassPairsOverflow { declared } => write!(
                f,
                "the unordered pairs of {declared} declared members overflow the machine integer \
                 counting them"
            ),
            Self::TransitionUndeclared { from, to } => write!(
                f,
                "no transition {from:?} -> {to:?} is declared; the charts are incomparable and the \
                 type says so"
            ),
        }
    }
}

impl std::error::Error for AtlasRefusal {}

/// A transition between two charts of one atlas, carrying the part of the source it does **not**
/// transport. It is not assumed invertible.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::ChartTransition`, whose `transition` field is
/// `Foundation/ContinuingTower.lean::Transition`. The three methods are `apply`, `residual` and
/// `reopen`, and [`ChartMap::check_reopen`] is the executable `reopen_apply`.
pub trait ChartMap {
    /// The atlas's coordinate carrier. One atlas has one coordinate type; a chart that reads only
    /// some of its arms refuses the rest by name.
    type Coordinate: Clone + Eq + Debug;
    /// What the transition does not transport.
    type Residual: Clone + Eq + Debug;

    /// The transition's declared name, for the refusal and the obstruction witness.
    fn name(&self) -> &str;

    /// What the transition transports.
    fn apply(&self, source: &Self::Coordinate) -> Result<Self::Coordinate, AtlasRefusal>;

    /// What it drops, retained.
    fn residual(&self, source: &Self::Coordinate) -> Result<Self::Residual, AtlasRefusal>;

    /// Reconstruct a source from a transported face and the retained residual.
    fn reopen(
        &self,
        target: &Self::Coordinate,
        residual: &Self::Residual,
    ) -> Result<Self::Coordinate, AtlasRefusal>;

    /// Check `reopen(apply(x), residual(x)) = x` at one coordinate.
    ///
    /// Lean counterpart: `ChartTransition.residual_reopens`, which is `Transition.reopen_apply`
    /// and cannot fail there; here it is asked and a failure is [`AtlasRefusal::ReopenFailed`].
    fn check_reopen(&self, source: &Self::Coordinate) -> Result<(), AtlasRefusal> {
        let transported = self.apply(source)?;
        let residual = self.residual(source)?;
        let reopened = self.reopen(&transported, &residual)?;
        if &reopened == source {
            Ok(())
        } else {
            Err(AtlasRefusal::ReopenFailed {
                map: self.name().to_string(),
            })
        }
    }
}

/// A cocycle defect: one coordinate at which the routed and direct passages disagree, with both
/// transported faces retained.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::CocycleDefect`. It is the obstruction returned
/// as content; it is never an error and it is never resolved by choosing a route.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CocycleDefect<Z> {
    /// Where the routes disagree.
    pub source: Z,
    /// What the composite route `a -> b -> c` transports.
    pub routed: Z,
    /// What the declared direct transition `a -> c` transports.
    pub direct: Z,
    /// The three charts, in order.
    pub charts: [String; 3],
}

impl<Z: Clone + Eq + Debug> CocycleDefect<Z> {
    /// **A cocycle defect is holonomy, not loss.** Both routes reopen the same source with no
    /// remainder, so neither dropped anything it failed to record; only the face each route
    /// presents differs.
    ///
    /// Lean counterpart: `CocycleDefect.defect_is_holonomy_not_loss`.
    pub fn both_routes_reopen<M1, M2, M3>(
        &self,
        first: &M1,
        second: &M2,
        direct: &M3,
    ) -> Result<(), AtlasRefusal>
    where
        M1: ChartMap<Coordinate = Z>,
        M2: ChartMap<Coordinate = Z>,
        M3: ChartMap<Coordinate = Z>,
    {
        // The routed leg reopens through its two component residuals, in the order they were
        // dropped — `Transition::comp_residual`.
        let middle = first.apply(&self.source)?;
        let first_residual = first.residual(&self.source)?;
        let second_residual = second.residual(&middle)?;
        let back_to_middle = second.reopen(&self.routed, &second_residual)?;
        let back_to_source = first.reopen(&back_to_middle, &first_residual)?;
        if back_to_source != self.source {
            return Err(AtlasRefusal::ReopenFailed {
                map: second.name().to_string(),
            });
        }
        direct.check_reopen(&self.source)
    }
}

// -------------------------------------------------------------------------------------------
// C6 (e) — the atlas, its coherent placements and the trichotomy
// -------------------------------------------------------------------------------------------

/// One coordinate at every chart the placement reaches, agreeing under every transition the atlas
/// declares between reached charts. This is what "the embedding is one global vector" would mean.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::CoherentPlacement`. Lean's placement is total
/// over the chart index; this one carries the charts it reached and the transitions it checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoherentPlacement<Z> {
    values: BTreeMap<String, Z>,
    checked: Vec<(String, String)>,
}

impl<Z: Clone + Eq + Debug> CoherentPlacement<Z> {
    /// The coordinate presented at one chart.
    pub fn value(&self, chart: &str) -> Option<&Z> {
        self.values.get(chart)
    }

    /// The charts this placement reaches.
    pub fn charts(&self) -> Vec<String> {
        self.values.keys().cloned().collect()
    }

    /// The ordered chart pairs whose declared transition was checked.
    ///
    /// Lean counterpart: `CoherentPlacement.coherent`, as a receipt rather than a proof.
    pub fn checked(&self) -> &[(String, String)] {
        &self.checked
    }
}

/// Why no coherent placement exists.
///
/// Lean counterpart: `no_coherentPlacement_through_defect` locates a cocycle defect;
/// `atlasGluing_obstructed_of_total_defect` returns the obstructed arm when the defect is total.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtlasObstruction<Z> {
    /// Two routes between three charts disagree.
    Cocycle(CocycleDefect<Z>),
    /// A declared transition carried the placement's value at one chart to something other than
    /// its value at the next.
    Incoherent {
        /// The chart the transition leaves.
        from: String,
        /// The chart it arrives at.
        to: String,
        /// What the transition transported.
        transported: Z,
        /// What the placement presented there.
        presented: Z,
    },
    /// Nothing was offered at the base chart.
    NoCandidate,
}

/// The three lawful returns of an attempted global placement.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::AtlasGluing`, whose totality is
/// `atlasGluing_total`. [`ReceiverAtlas::glue`] is the executable totality: it returns one of these
/// three for every atlas and candidate population, and never a representative chosen out of a
/// plural family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AtlasGluing<Z> {
    /// Exactly one global placement over the declared candidates.
    Unique(CoherentPlacement<Z>),
    /// Several. The plurality is the content and is returned whole.
    Plural(Vec<CoherentPlacement<Z>>),
    /// None, although every chart may be inhabited.
    Obstructed(AtlasObstruction<Z>),
}

/// The [`ReceiverAtlas::check_cocycle`] return: how many sources agreed, or the defect that
/// refutes the cocycle, or the atlas's own refusal.
pub type CocycleOutcome<Z> = Result<Result<usize, CocycleDefect<Z>>, AtlasRefusal>;

/// The return of one propagation attempt: the coherent placement, the obstruction that refutes it,
/// or the atlas's own refusal.
pub type PlacementOutcome<Z> = Result<Result<CoherentPlacement<Z>, AtlasObstruction<Z>>, AtlasRefusal>;

/// A **receiver atlas**: the charts an object actually admits, together with the transitions it
/// actually declares between them. An undeclared transition is an undiscovered relation, not a
/// denial.
///
/// The cost of a transition belongs to item **C5** and is deliberately not a field here.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::ReceiverAtlas`.
pub struct ReceiverAtlas<X, Z, R, M = NoCapability<Z>>
where
    X: Ord + Clone + Debug,
    Z: Clone + Eq + Debug,
    R: Clone + Eq + Debug,
    M: Capability<Carrier = Z>,
{
    /// The schema this atlas serializes under.
    pub schema: String,
    charts: BTreeMap<String, LocalChart<X, Z, M>>,
    /// The declared time each chart reads at. A chart admitted through [`ReceiverAtlas::admit`]
    /// reads at time zero; [`ReceiverAtlas::admit_at`] declares another.
    times: BTreeMap<String, usize>,
    transitions: BTreeMap<(String, String), Box<dyn ChartMap<Coordinate = Z, Residual = R>>>,
}

impl<X, Z, R, M> Debug for ReceiverAtlas<X, Z, R, M>
where
    X: Ord + Clone + Debug,
    Z: Clone + Eq + Debug,
    R: Clone + Eq + Debug,
    M: Capability<Carrier = Z>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ReceiverAtlas")
            .field("schema", &self.schema)
            .field("charts", &self.charts.keys().collect::<Vec<_>>())
            .field("transitions", &self.transitions.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl<X, Z, R, M> ReceiverAtlas<X, Z, R, M>
where
    X: Ord + Clone + Debug,
    Z: Clone + Eq + Debug,
    R: Clone + Eq + Debug,
    M: Capability<Carrier = Z>,
{
    /// Found an empty atlas.
    pub fn found(schema: impl Into<String>) -> Self {
        Self {
            schema: schema.into(),
            charts: BTreeMap::new(),
            times: BTreeMap::new(),
            transitions: BTreeMap::new(),
        }
    }

    /// Admit one chart. A chart admitted twice under one name replaces the first, which is why
    /// [`Self::declare_transition`] refuses a duplicate pair rather than the caller having to.
    pub fn admit(&mut self, chart: LocalChart<X, Z, M>) {
        self.admit_at(chart, 0);
    }

    /// Declare a transition between two admitted charts. Both names must already be charts of this
    /// atlas, and no ordered pair may be declared twice.
    pub fn declare_transition(
        &mut self,
        from: impl Into<String>,
        to: impl Into<String>,
        map: Box<dyn ChartMap<Coordinate = Z, Residual = R>>,
    ) -> Result<(), AtlasRefusal> {
        let from = from.into();
        let to = to.into();
        if !self.charts.contains_key(&from) {
            return Err(AtlasRefusal::ChartAbsent { name: from });
        }
        if !self.charts.contains_key(&to) {
            return Err(AtlasRefusal::ChartAbsent { name: to });
        }
        if self.transitions.contains_key(&(from.clone(), to.clone())) {
            return Err(AtlasRefusal::TransitionAlreadyDeclared { from, to });
        }
        self.transitions.insert((from, to), map);
        Ok(())
    }

    /// The charts this atlas admits, in name order.
    pub fn charts(&self) -> Vec<String> {
        self.charts.keys().cloned().collect()
    }

    /// One admitted chart.
    pub fn chart(&self, name: &str) -> Option<&LocalChart<X, Z, M>> {
        self.charts.get(name)
    }

    /// The declared transition between two charts, when there is one.
    pub fn transition(
        &self,
        from: &str,
        to: &str,
    ) -> Option<&dyn ChartMap<Coordinate = Z, Residual = R>> {
        self.transitions
            .get(&(from.to_string(), to.to_string()))
            .map(AsRef::as_ref)
    }

    /// Whether the two charts are related by a declared transition at all.
    pub fn comparable(&self, from: &str, to: &str) -> bool {
        self.transition(from, to).is_some()
    }

    /// **The cocycle check on one triple, with residuals.** The routed passage `a -> b -> c` is
    /// compared with the declared direct passage `a -> c` at every supplied source coordinate; a
    /// disagreement is returned as a [`CocycleDefect`], not raised.
    ///
    /// Lean counterpart: `Foundation/ReceiverAtlas.lean::Cocycle` and `cocycle_iff_isEmpty_defect`.
    pub fn check_cocycle(
        &self,
        a: &str,
        b: &str,
        c: &str,
        sources: &[Z],
    ) -> CocycleOutcome<Z> {
        let ab = self
            .transition(a, b)
            .ok_or_else(|| AtlasRefusal::TransitionUndeclared {
                from: a.to_string(),
                to: b.to_string(),
            })?;
        let bc = self
            .transition(b, c)
            .ok_or_else(|| AtlasRefusal::TransitionUndeclared {
                from: b.to_string(),
                to: c.to_string(),
            })?;
        let ac = self
            .transition(a, c)
            .ok_or_else(|| AtlasRefusal::TransitionUndeclared {
                from: a.to_string(),
                to: c.to_string(),
            })?;
        let mut checked = 0usize;
        for source in sources {
            let routed = bc.apply(&ab.apply(source)?)?;
            let direct = ac.apply(source)?;
            if routed != direct {
                return Ok(Err(CocycleDefect {
                    source: source.clone(),
                    routed,
                    direct,
                    charts: [a.to_string(), b.to_string(), c.to_string()],
                }));
            }
            checked += 1;
        }
        Ok(Ok(checked))
    }

    /// Propagate one candidate coordinate from a base chart through the declared transitions, then
    /// re-check every declared transition among the charts it reached.
    fn extend(&self, base: &str, candidate: &Z) -> PlacementOutcome<Z> {
        let mut values: BTreeMap<String, Z> = BTreeMap::new();
        values.insert(base.to_string(), candidate.clone());
        // Breadth-first over the declared transitions; every chart reached once, deterministically
        // in name order.
        let mut frontier = vec![base.to_string()];
        while let Some(from) = frontier.pop() {
            for target in self.charts.keys() {
                if values.contains_key(target) {
                    continue;
                }
                let Some(map) = self.transition(&from, target) else {
                    continue;
                };
                let source = values.get(&from).expect("frontier chart carries a value");
                let transported = map.apply(source)?;
                values.insert(target.clone(), transported);
                frontier.push(target.clone());
            }
        }
        let mut checked = Vec::new();
        for ((from, to), map) in &self.transitions {
            let (Some(source), Some(presented)) = (values.get(from), values.get(to)) else {
                continue;
            };
            let transported = map.apply(source)?;
            if &transported != presented {
                return Ok(Err(AtlasObstruction::Incoherent {
                    from: from.clone(),
                    to: to.clone(),
                    transported,
                    presented: presented.clone(),
                }));
            }
            checked.push((from.clone(), to.clone()));
        }
        Ok(Ok(CoherentPlacement { values, checked }))
    }

    /// **Attempt a global placement from a declared candidate population at one base chart.**
    /// Returns one of the three lawful arms for every atlas and every population; a plural return
    /// is never collapsed to a representative.
    ///
    /// Candidates that propagate to the *same* placement count once. The arm is decided by how
    /// many placements there are, and Lean's `AtlasGluing.plural` asks for placements that are
    /// provably distinct, so a candidate population that repeats itself returns `Unique` — a
    /// repetition in the caller's list is not plurality in the object. Deduplication compares the
    /// placed coordinates at every chart reached; the coordinate type carries `Eq` and no `Ord`, so
    /// nothing is sorted or hashed.
    ///
    /// Lean counterpart: `Foundation/ReceiverAtlas.lean::AtlasGluing` and `atlasGluing_total`.
    pub fn glue(&self, base: &str, candidates: &[Z]) -> Result<AtlasGluing<Z>, AtlasRefusal> {
        if !self.charts.contains_key(base) {
            return Err(AtlasRefusal::ChartAbsent {
                name: base.to_string(),
            });
        }
        if candidates.is_empty() {
            return Ok(AtlasGluing::Obstructed(AtlasObstruction::NoCandidate));
        }
        let mut coherent: Vec<CoherentPlacement<Z>> = Vec::new();
        let mut first_obstruction = None;
        for candidate in candidates {
            match self.extend(base, candidate)? {
                Ok(placement) => {
                    // Two candidates that propagate to the *same* placement are one placement, and
                    // the arm below is chosen by how many placements there are. Lean's
                    // `AtlasGluing.plural` asks for two placements that are provably distinct
                    // (`¬ Subsingleton`), so a repeated candidate must not manufacture plurality:
                    // `[7, 7]` is `Unique`, not `Plural(vec![p, p])`. `Z` carries `Eq` and no
                    // `Ord`, so the duplicate is located by comparing the placed values themselves
                    // — the coordinates at every chart reached — and never by sorting or hashing.
                    if !coherent
                        .iter()
                        .any(|already| already.values == placement.values)
                    {
                        coherent.push(placement);
                    }
                }
                Err(obstruction) => {
                    if first_obstruction.is_none() {
                        first_obstruction = Some(obstruction);
                    }
                }
            }
        }
        Ok(match coherent.len() {
            0 => AtlasGluing::Obstructed(
                first_obstruction.unwrap_or(AtlasObstruction::NoCandidate),
            ),
            1 => AtlasGluing::Unique(coherent.into_iter().next().expect("length checked")),
            _ => AtlasGluing::Plural(coherent),
        })
    }

    /// **Two occurrences are indistinguishable to this atlas** when every chart that reads both
    /// returns the same coordinate for them.
    ///
    /// Lean counterpart: `Foundation/ReceiverAtlas.lean::AtlasIndistinguishable`. A `true` return
    /// is a fact about this atlas and never about the objects: `indistinguishable_of_refinement`
    /// says a richer atlas may reopen it.
    pub fn indistinguishable(&self, left: &X, right: &X) -> bool {
        self.charts
            .values()
            .all(|chart| match (chart.place(left), chart.place(right)) {
                (Some(a), Some(b)) => a == b,
                _ => true,
            })
    }

    /// The charts at which two occurrences are separated, named. Empty exactly when they are
    /// indistinguishable to this atlas.
    pub fn separating_charts(&self, left: &X, right: &X) -> Vec<String> {
        self.charts
            .values()
            .filter(|chart| match (chart.place(left), chart.place(right)) {
                (Some(a), Some(b)) => a != b,
                _ => false,
            })
            .map(|chart| chart.name().to_string())
            .collect()
    }
}

// -------------------------------------------------------------------------------------------
// C6 (g) — the shift atlas: every chart inhabited, no global placement
// -------------------------------------------------------------------------------------------

/// The coordinate of the shift atlas: an exact natural number, the distance past the chart's base.
pub type ShiftCoordinate = u64;

/// The transition of the shift atlas from chart `a` to chart `b`: re-base the offset. It
/// transports `y ↦ (y + a) − b`, saturating at zero, and retains the truncated part as its
/// residual so that the reopening is exact.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::ShiftAtlas.tailTransition`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShiftChartMap {
    name: String,
    from: u64,
    to: u64,
}

impl ShiftChartMap {
    /// The transition between two declared chart bases.
    pub fn new(from: u64, to: u64) -> Self {
        Self {
            name: format!("shift:{from}->{to}"),
            from,
            to,
        }
    }
}

impl ChartMap for ShiftChartMap {
    type Coordinate = ShiftCoordinate;
    type Residual = u64;

    fn name(&self) -> &str {
        &self.name
    }

    fn apply(&self, source: &u64) -> Result<u64, AtlasRefusal> {
        Ok(source.saturating_add(self.from).saturating_sub(self.to))
    }

    fn residual(&self, source: &u64) -> Result<u64, AtlasRefusal> {
        Ok(source.saturating_add(self.from).min(self.to))
    }

    fn reopen(&self, target: &u64, residual: &u64) -> Result<u64, AtlasRefusal> {
        Ok(target.saturating_add(*residual).saturating_sub(self.from))
    }
}

/// The **shift atlas** over a declared chart aperture: chart `n` reads the tail `{x | n ≤ x}` of
/// the exact naturals in the coordinate "distance past `n`".
///
/// Every chart reads a nonempty region into an inhabited coordinate and every pair of charts is
/// linked by a lawful transition carrying its residual — and no coherent placement exists once the
/// aperture is wider than the base candidate.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::ShiftAtlas.shiftAtlas` and
/// `theEmbeddingIsNotOneVector`. Lean proves emptiness over the whole infinite index by citing
/// `shiftTower_obstructed`; a program is finite, so the executable witness is that **any** declared
/// aperture wider than the candidate obstructs, which is that proof's own argument made finite.
pub fn shift_atlas(depth: u64, occurrences: &[u64]) -> ReceiverAtlas<u64, ShiftCoordinate, u64> {
    let mut atlas = ReceiverAtlas::found("holonics.receiver_atlas.shift.v1");
    for base in 0..=depth {
        let placements: Vec<(u64, ShiftCoordinate)> = occurrences
            .iter()
            .filter(|x| **x >= base)
            .map(|x| (*x, x - base))
            .collect();
        atlas.admit(LocalChart::founded(
            format!("tail:{base}"),
            placements,
            None,
        ));
    }
    for from in 0..=depth {
        for to in 0..=depth {
            if from == to {
                continue;
            }
            atlas
                .declare_transition(
                    format!("tail:{from}"),
                    format!("tail:{to}"),
                    Box::new(ShiftChartMap::new(from, to)),
                )
                .expect("both charts were just admitted and each pair is declared once");
        }
    }
    atlas
}

// -------------------------------------------------------------------------------------------
// C6 (i) — the protein atlas
// -------------------------------------------------------------------------------------------

/// The identity of one presented structure inside the protein atlas.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PresentationId(pub u32);

/// The coordinate carrier of the protein atlas: one type with one arm per chart.
///
/// A chart map that reads one arm refuses the others by name rather than defaulting, which is the
/// executable form of "a chart with no declared relation to another chart is incomparable, and the
/// type says so".
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProteinCoordinate {
    /// The residue-type sequence, as exact integer codes. No geometry at all.
    Sequence(Vec<u32>),
    /// The atom-grain contact face: every pair the presentation did not decide `Outside`.
    AllAtomFrame(GrainFace),
    /// The residue-grain face read through the declared alpha-carbon selection.
    AlphaCarbonGrain(GrainFace),
    /// The contact complex: the `Inside` pairs alone, with the `Open` class forgotten.
    ContactComplex(BTreeSet<GrainPair>),
    /// The exact Maxwell count of the rigidity receiver at this presentation.
    RigidityReading(MaxwellCount),
}

/// What a transition of the protein atlas does not transport.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProteinResidual {
    /// Every fine reading the alpha-carbon selection never looked at.
    ///
    /// Lean counterpart: the `Residual` of `Foundation/GrainRestriction.lean::selectionTransition`.
    Selection(SelectionResidual),
    /// The pairs the contact complex dropped when it forgot the `Open` class, retained whole.
    /// `Open` is never rounded: the pair travels with its exact class.
    OpenClass(BTreeMap<GrainPair, ContactClass>),
}

/// The alpha-carbon selection of [`crate::grain_tower`] presented as a chart map of the protein
/// atlas. It is genuinely lossy and its residual reopens the atom-grain face exactly.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::selectionTransition` and
/// `grain_residual_reopens_the_source`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlphaCarbonChartMap {
    name: String,
    selection: GrainSelection,
}

impl AlphaCarbonChartMap {
    /// Present a declared selection as a chart map.
    pub fn new(selection: GrainSelection) -> Self {
        Self {
            name: format!("alphaCarbonSelection({})", selection.lineage),
            selection,
        }
    }

    /// The selection this map enacts.
    pub fn selection(&self) -> &GrainSelection {
        &self.selection
    }
}

impl ChartMap for AlphaCarbonChartMap {
    type Coordinate = ProteinCoordinate;
    type Residual = ProteinResidual;

    fn name(&self) -> &str {
        &self.name
    }

    fn apply(&self, source: &ProteinCoordinate) -> Result<ProteinCoordinate, AtlasRefusal> {
        match source {
            ProteinCoordinate::AllAtomFrame(face) => Ok(ProteinCoordinate::AlphaCarbonGrain(
                self.selection.apply(face),
            )),
            _ => Err(AtlasRefusal::CoordinateNotInChart {
                map: self.name.clone(),
                expected: "AllAtomFrame",
            }),
        }
    }

    fn residual(&self, source: &ProteinCoordinate) -> Result<ProteinResidual, AtlasRefusal> {
        match source {
            ProteinCoordinate::AllAtomFrame(face) => {
                Ok(ProteinResidual::Selection(self.selection.residual(face)))
            }
            _ => Err(AtlasRefusal::CoordinateNotInChart {
                map: self.name.clone(),
                expected: "AllAtomFrame",
            }),
        }
    }

    fn reopen(
        &self,
        target: &ProteinCoordinate,
        residual: &ProteinResidual,
    ) -> Result<ProteinCoordinate, AtlasRefusal> {
        match (target, residual) {
            (ProteinCoordinate::AlphaCarbonGrain(face), ProteinResidual::Selection(retained)) => {
                Ok(ProteinCoordinate::AllAtomFrame(
                    self.selection.reopen(face, retained),
                ))
            }
            _ => Err(AtlasRefusal::CoordinateNotInChart {
                map: self.name.clone(),
                expected: "AlphaCarbonGrain with a selection residual",
            }),
        }
    }
}

/// The contact complex read off a residue-grain face: the `Inside` pairs alone. It forgets the
/// `Open` class, and the retained residual is exactly the pairs it forgot, with their exact
/// classes — an `Open` reading is never rounded to `Inside` or `Outside`.
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct ContactComplexChartMap {
    name: String,
}

impl ContactComplexChartMap {
    /// The contact-complex reading.
    pub fn new() -> Self {
        Self {
            name: "contactComplex".to_string(),
        }
    }
}

impl ChartMap for ContactComplexChartMap {
    type Coordinate = ProteinCoordinate;
    type Residual = ProteinResidual;

    fn name(&self) -> &str {
        &self.name
    }

    fn apply(&self, source: &ProteinCoordinate) -> Result<ProteinCoordinate, AtlasRefusal> {
        match source {
            ProteinCoordinate::AlphaCarbonGrain(face) => Ok(ProteinCoordinate::ContactComplex(
                face.classified()
                    .iter()
                    .filter(|(_, class)| **class == ContactClass::Inside)
                    .map(|(pair, _)| *pair)
                    .collect(),
            )),
            _ => Err(AtlasRefusal::CoordinateNotInChart {
                map: self.name.clone(),
                expected: "AlphaCarbonGrain",
            }),
        }
    }

    fn residual(&self, source: &ProteinCoordinate) -> Result<ProteinResidual, AtlasRefusal> {
        match source {
            ProteinCoordinate::AlphaCarbonGrain(face) => Ok(ProteinResidual::OpenClass(
                face.classified()
                    .iter()
                    .filter(|(_, class)| **class != ContactClass::Inside)
                    .map(|(pair, class)| (*pair, *class))
                    .collect(),
            )),
            _ => Err(AtlasRefusal::CoordinateNotInChart {
                map: self.name.clone(),
                expected: "AlphaCarbonGrain",
            }),
        }
    }

    fn reopen(
        &self,
        target: &ProteinCoordinate,
        residual: &ProteinResidual,
    ) -> Result<ProteinCoordinate, AtlasRefusal> {
        match (target, residual) {
            (ProteinCoordinate::ContactComplex(inside), ProteinResidual::OpenClass(retained)) => {
                let readings = inside
                    .iter()
                    .map(|pair| (*pair, ContactClass::Inside))
                    .chain(retained.iter().map(|(pair, class)| (*pair, *class)));
                let grain = inside
                    .iter()
                    .next()
                    .map(GrainPair::grain)
                    .or_else(|| retained.keys().next().map(GrainPair::grain))
                    .unwrap_or(crate::grain_tower::Grain::Residue);
                let face =
                    GrainFace::founded(grain, readings).map_err(|_| AtlasRefusal::ReopenFailed {
                        map: self.name.clone(),
                    })?;
                Ok(ProteinCoordinate::AlphaCarbonGrain(face))
            }
            _ => Err(AtlasRefusal::CoordinateNotInChart {
                map: self.name.clone(),
                expected: "ContactComplex with an open-class residual",
            }),
        }
    }
}

/// Where one presented structure sits in every chart of the protein atlas.
///
/// `rigidity` is an `Option`: a presentation with no supplied exact configuration has **no**
/// rigidity reading, and that chart simply does not read it. That is the capability doctrine in
/// the atlas — a reading that was not supplied is absent, never zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProteinPlacement {
    /// The residue-type sequence as exact integer codes.
    pub sequence: Vec<u32>,
    /// The atom-grain contact face.
    pub all_atom: GrainFace,
    /// The residue-grain face read through the alpha-carbon selection.
    pub alpha_carbon: GrainFace,
    /// The exact rigidity count, when a configuration was supplied.
    pub rigidity: Option<MaxwellCount>,
}

/// The protein atlas: five charts and the transitions actually declared between them.
pub type ProteinAtlas = ReceiverAtlas<PresentationId, ProteinCoordinate, ProteinResidual>;

/// The five chart names of the protein atlas, in the order the plan names them.
pub const PROTEIN_CHARTS: [&str; 5] = [
    "sequence",
    "allAtomFrames",
    "alphaCarbonGrain",
    "contactComplex",
    "rigidityReading",
];

/// Found the protein atlas over a declared population of presentations.
///
/// Two transitions are declared, and both are genuinely lossy and carry their residual:
/// `allAtomFrames -> alphaCarbonGrain` is the alpha-carbon selection of [`crate::grain_tower`], and
/// `alphaCarbonGrain -> contactComplex` forgets the `Open` class and retains it whole. No
/// transition is declared out of `sequence` or into `rigidityReading`: those relations are
/// **undiscovered**, which the atlas says by carrying no entry rather than by inventing one.
pub fn protein_atlas(
    presentations: &[(PresentationId, ProteinPlacement)],
    selection: GrainSelection,
) -> Result<ProteinAtlas, AtlasRefusal> {
    let mut atlas = ReceiverAtlas::found("holonics.receiver_atlas.protein.v1");

    atlas.admit(LocalChart::founded(
        PROTEIN_CHARTS[0],
        presentations.iter().map(|(id, placement)| {
            (*id, ProteinCoordinate::Sequence(placement.sequence.clone()))
        }),
        None,
    ));
    atlas.admit(LocalChart::founded(
        PROTEIN_CHARTS[1],
        presentations.iter().map(|(id, placement)| {
            (
                *id,
                ProteinCoordinate::AllAtomFrame(placement.all_atom.clone()),
            )
        }),
        None,
    ));
    atlas.admit(LocalChart::founded(
        PROTEIN_CHARTS[2],
        presentations.iter().map(|(id, placement)| {
            (
                *id,
                ProteinCoordinate::AlphaCarbonGrain(placement.alpha_carbon.clone()),
            )
        }),
        None,
    ));
    let complex = ContactComplexChartMap::new();
    let mut complex_placements = Vec::new();
    for (id, placement) in presentations {
        let coordinate = complex.apply(&ProteinCoordinate::AlphaCarbonGrain(
            placement.alpha_carbon.clone(),
        ))?;
        complex_placements.push((*id, coordinate));
    }
    atlas.admit(LocalChart::founded(
        PROTEIN_CHARTS[3],
        complex_placements,
        None,
    ));
    atlas.admit(LocalChart::founded(
        PROTEIN_CHARTS[4],
        presentations.iter().filter_map(|(id, placement)| {
            placement
                .rigidity
                .map(|count| (*id, ProteinCoordinate::RigidityReading(count)))
        }),
        None,
    ));

    atlas.declare_transition(
        PROTEIN_CHARTS[1],
        PROTEIN_CHARTS[2],
        Box::new(AlphaCarbonChartMap::new(selection)),
    )?;
    atlas.declare_transition(
        PROTEIN_CHARTS[2],
        PROTEIN_CHARTS[3],
        Box::new(ContactComplexChartMap::new()),
    )?;
    Ok(atlas)
}


// -------------------------------------------------------------------------------------------
// R7 — the separating atlas theorem
// -------------------------------------------------------------------------------------------

/// The ceiling on the size of a **declared bounded class** [`ReceiverAtlas::is_separating`] will
/// scan.
///
/// [definition] The scan reads every unordered pair, so the work is `n(n−1)/2`. The ceiling bounds
/// `n` and the pair count is formed with checked arithmetic, both before any allocation.
pub const DECLARED_CLASS_CEILING: usize = 4096;

/// **What separated two occurrences**: the probe, the receiver and the time, with both faces.
///
/// This is R7's positive return. The plan asks for "some probe, receiver and time at which their
/// responses differ"; a chart of this atlas *is* a probe/receiver pair, and its declared time is
/// the third index.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separator<Z> {
    /// The chart — the probe/receiver pair — at which they differ.
    pub chart: String,
    /// The declared time that chart reads at.
    pub time: usize,
    /// What it reads for the first occurrence.
    pub left: Z,
    /// And for the second.
    pub right: Z,
}

/// The two lawful returns of a separating search over a declared horizon bound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeparationOutcome<Z> {
    /// A probe, receiver and time at which the responses differ.
    Separated(Separator<Z>),
    /// **No chart of this atlas, at or inside the declared horizon bound, tells them apart.**
    ///
    /// This is a fact about the atlas and the bound, never about the objects:
    /// `indistinguishable_of_refinement` says a richer atlas may reopen it, and the charts actually
    /// read are named so that what was tried is visible.
    IndistinguishableToThisAtlas {
        /// The atlas's schema.
        atlas: String,
        /// Every chart that read *both* occurrences inside the bound.
        charts_read: Vec<String>,
        /// Charts the bound excluded, named rather than silently skipped.
        charts_beyond_bound: Vec<String>,
        /// The declared bound.
        horizon_bound: usize,
    },
}

/// **An atlas insufficiency**: two inequivalent members of a declared class that the atlas cannot
/// separate. It is a *result* — it states which receiver is missing — and not a failure.
///
/// Lean counterpart: `Foundation/Receiver.lean::ReceiverInsufficiency`, and
/// `Foundation/ReceiverAtlas.lean::SeparatingAtlas.spectralTopologicalInsufficiency` is the worked
/// instance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtlasInsufficiency<X> {
    /// The atlas's schema.
    pub atlas: String,
    /// The first member.
    pub left: X,
    /// The second, inequivalent to it by the caller's declared equivalence.
    pub right: X,
    /// Every chart that read both.
    pub charts_read: Vec<String>,
    /// The declared bound.
    pub horizon_bound: usize,
}

/// The verdict of a separating search over a declared bounded class.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::Separates`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeparatingVerdict<X> {
    /// Every declared pair is separated by some chart inside the bound.
    Separating {
        /// How many members the class declared.
        members: usize,
        /// How many unordered pairs were checked.
        pairs_checked: usize,
        /// The declared bound.
        horizon_bound: usize,
    },
    /// Some declared pair is not, and here it is.
    NotSeparating(AtlasInsufficiency<X>),
}

impl<X, Z, R, M> ReceiverAtlas<X, Z, R, M>
where
    X: Ord + Clone + Debug,
    Z: Clone + Eq + Debug,
    R: Clone + Eq + Debug,
    M: Capability<Carrier = Z>,
{
    /// Admit one chart **at a declared time**. [`Self::admit`] is this at time zero.
    ///
    /// The time is the plan's third index: R7 asks for a probe, a receiver *and a time*, and a
    /// chart of this atlas carries the first two. A chart admitted twice under one name replaces
    /// the first, time included.
    pub fn admit_at(&mut self, chart: LocalChart<X, Z, M>, time: usize) {
        let name = chart.name().to_string();
        self.charts.insert(name.clone(), chart);
        self.times.insert(name, time);
    }

    /// The declared time of one chart. A chart admitted without one reads at time zero.
    pub fn chart_time(&self, name: &str) -> Option<usize> {
        self.charts
            .contains_key(name)
            .then(|| self.times.get(name).copied().unwrap_or(0))
    }

    /// **The separating search**: the first chart, inside a declared horizon bound, at which two
    /// occurrences differ — or the typed statement that this atlas, inside that bound, cannot tell
    /// them apart.
    ///
    /// Charts are scanned in name order, so the return is deterministic. A chart that does not read
    /// both occurrences separates nothing and is not counted as having been read; a chart whose
    /// declared time is past the bound is named in `charts_beyond_bound` rather than silently
    /// skipped, so a caller can see that raising the bound is an option.
    pub fn separate(&self, left: &X, right: &X, horizon_bound: usize) -> SeparationOutcome<Z> {
        let mut charts_read = Vec::new();
        let mut charts_beyond_bound = Vec::new();
        for (name, chart) in &self.charts {
            let time = self.times.get(name).copied().unwrap_or(0);
            let (Some(a), Some(b)) = (chart.place(left), chart.place(right)) else {
                continue;
            };
            if time > horizon_bound {
                charts_beyond_bound.push(name.clone());
                continue;
            }
            charts_read.push(name.clone());
            if a != b {
                return SeparationOutcome::Separated(Separator {
                    chart: name.clone(),
                    time,
                    left: a.clone(),
                    right: b.clone(),
                });
            }
        }
        SeparationOutcome::IndistinguishableToThisAtlas {
            atlas: self.schema.clone(),
            charts_read,
            charts_beyond_bound,
            horizon_bound,
        }
    }

    /// **R7 on a declared bounded class**: whether every pair of distinct declared members is
    /// separated by some probe, receiver and time inside the declared bound.
    ///
    /// The class is a *declaration* and its size is checked against [`DECLARED_CLASS_CEILING`]
    /// before any pair is formed; the pair count is formed with checked arithmetic. A
    /// `NotSeparating` return carries the insufficiency witness — the pair, and every chart that
    /// read both — because "this atlas is not separating" is a statement about what receiver is
    /// missing.
    ///
    /// Members that compare equal under `X`'s own order are not a pair: the caller declares the
    /// class, and repeating a member in it is not an inequivalence.
    pub fn is_separating(
        &self,
        declared_class: &[X],
        horizon_bound: usize,
    ) -> Result<SeparatingVerdict<X>, AtlasRefusal> {
        if declared_class.len() > DECLARED_CLASS_CEILING {
            return Err(AtlasRefusal::DeclaredClassTooWide {
                declared: declared_class.len(),
                ceiling: DECLARED_CLASS_CEILING,
            });
        }
        let count = declared_class.len();
        count
            .checked_mul(count.saturating_sub(1))
            .ok_or(AtlasRefusal::DeclaredClassPairsOverflow { declared: count })?;
        let mut pairs_checked = 0usize;
        for left in 0..count {
            for right in (left + 1)..count {
                if declared_class[left] == declared_class[right] {
                    continue;
                }
                pairs_checked += 1;
                match self.separate(&declared_class[left], &declared_class[right], horizon_bound) {
                    SeparationOutcome::Separated(_) => {}
                    SeparationOutcome::IndistinguishableToThisAtlas {
                        atlas, charts_read, ..
                    } => {
                        return Ok(SeparatingVerdict::NotSeparating(AtlasInsufficiency {
                            atlas,
                            left: declared_class[left].clone(),
                            right: declared_class[right].clone(),
                            charts_read,
                            horizon_bound,
                        }));
                    }
                }
            }
        }
        Ok(SeparatingVerdict::Separating {
            members: count,
            pairs_checked,
            horizon_bound,
        })
    }
}

// -------------------------------------------------------------------------------------------
// R7 — the contracts that make an atlas credible, as typed laws on a receiver
// -------------------------------------------------------------------------------------------

/// The five contracts the plan names. Each is a typed law on a receiver, not a slogan.
///
/// Lean counterparts: `RebaseEquivariant`, `SourceAccountable` and `DeclarationIndependent` in
/// `Foundation/ReceiverAtlas.lean`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AtlasContract {
    /// The reading is unchanged by the declared **change of chart or frame** the receiver declares
    /// it must be. R1's is the chart change `(A,B,C) ↦ (TAT⁻¹, TB, CT⁻¹)`; R4's is the
    /// rigid-motion group. Independence from a *supplied structure* is a different contract and is
    /// [`AtlasContract::DeclarationIndependence`].
    ///
    /// Lean counterpart: `Foundation/ReceiverAtlas.lean::RebaseEquivariant`.
    RebaseEquivariance,
    /// The reading does not depend on a **supplied structure** the doctrine says it must not. R3's
    /// harmonic dimension is the worked case: it must not depend on which positive metric was
    /// supplied.
    ///
    /// Lean counterpart: `Foundation/ReceiverAtlas.lean::DeclarationIndependent`.
    DeclarationIndependence,
    /// Every returned component is indexed by the source and the transport path that produced it,
    /// and the components recombine to the reading exactly.
    SourceAccountability,
    /// The reading's parts balance against one another exactly: a conservation the receiver owes.
    EnergyBalance,
    /// A reading of a glued object is determined by the readings of its parts **together with the
    /// interface coupling**, not by the parts alone.
    GluingWithInterfaceCoupling,
    /// The reading moves continuously with the object away from a genuine bifurcation.
    StabilityAwayFromBifurcation,
}

mod recomputation {
    /// **The token a `Satisfied` row is made of.**
    ///
    /// [definition] Its field is private to this module and its only constructor is
    /// [`Recomputed::by`], which is `pub(super)`. No struct literal of this type can be written
    /// anywhere — not in another crate, not in another module, and not in `receiver_atlas`
    /// itself — so [`super::ContractStatus::Satisfied`] cannot be written as a literal either. The
    /// only way to obtain one is to call a verifier that computed something.
    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct Recomputed {
        witness: String,
    }

    impl Recomputed {
        /// Record what a verifier just computed. Reachable only from `receiver_atlas`'s own
        /// verifier functions.
        pub(super) fn by(witness: String) -> Self {
            Self { witness }
        }

        /// What was computed.
        pub fn witness(&self) -> &str {
            &self.witness
        }
    }
}

pub use recomputation::Recomputed;

/// What a contract's verification actually returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ContractStatus {
    /// Verified here, by running the witness named. A `Satisfied` row is recomputed on every call
    /// of [`contract_ledger`]; a regression flips it. The payload is a [`Recomputed`] token, which
    /// has no literal, so this arm cannot be asserted — only computed.
    Satisfied(Recomputed),
    /// Refuted, by the counterexample named. When the counterexample lives in another owner the
    /// row cites it and says so.
    Failed {
        /// The counterexample.
        counterexample: String,
    },
    /// Neither verified nor refuted here: the concrete absent type, law or consequence, named.
    Unproved {
        /// What is missing.
        missing: String,
    },
    /// The contract does not apply to this receiver, and why.
    NotApplicable {
        /// Why.
        reason: String,
    },
}

impl ContractStatus {
    /// Build a `Satisfied` status from what a verifier computed. Module-private: the only callers
    /// are this module's own `verify_*` functions.
    fn satisfied(witness: String) -> Self {
        Self::Satisfied(Recomputed::by(witness))
    }

    /// What was computed, when the status is `Satisfied`.
    pub fn witness(&self) -> Option<&str> {
        match self {
            Self::Satisfied(recomputed) => Some(recomputed.witness()),
            _ => None,
        }
    }
}

/// **A status a *standing* row may carry: everything but `Satisfied`.**
///
/// [definition] A standing row states something about a law this library does not enforce. It is
/// written as a literal in [`ledger_entries`], and it is typed so that writing `Satisfied` there
/// is not expressible: `StandingStatus` has no `Satisfied` arm, and `ContractStatus::Satisfied`
/// carries a token no literal can produce. A row can therefore be `Satisfied` only by running a
/// verifier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StandingStatus {
    /// Refuted, by the counterexample named.
    Failed {
        /// The counterexample.
        counterexample: String,
    },
    /// Neither verified nor refuted here: the concrete absent type, law or consequence, named.
    Unproved {
        /// What is missing.
        missing: String,
    },
    /// The contract does not apply to this receiver, and why.
    NotApplicable {
        /// Why.
        reason: String,
    },
}

impl From<StandingStatus> for ContractStatus {
    fn from(standing: StandingStatus) -> Self {
        match standing {
            StandingStatus::Failed { counterexample } => Self::Failed { counterexample },
            StandingStatus::Unproved { missing } => Self::Unproved { missing },
            StandingStatus::NotApplicable { reason } => Self::NotApplicable { reason },
        }
    }
}

/// How one ledger row gets its status.
#[derive(Clone)]
pub enum ContractEntry {
    /// The status is **recomputed** by calling this verifier, on every call of
    /// [`contract_ledger`].
    Recomputed(fn() -> ContractStatus),
    /// The status is a standing statement, written as a literal. It cannot be `Satisfied`.
    Standing(StandingStatus),
}

impl Debug for ContractEntry {
    fn fmt(&self, out: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Recomputed(_) => out.write_str("Recomputed(<verifier>)"),
            Self::Standing(status) => out.debug_tuple("Standing").field(status).finish(),
        }
    }
}

impl ContractEntry {
    /// Produce the status: by running the verifier, or by carrying the standing statement.
    pub fn status(&self) -> ContractStatus {
        match self {
            Self::Recomputed(verify) => verify(),
            Self::Standing(standing) => ContractStatus::from(standing.clone()),
        }
    }

    /// Whether this row's status is recomputed on every call.
    pub fn is_recomputed(&self) -> bool {
        matches!(self, Self::Recomputed(_))
    }
}

/// One row of the contract ledger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContractRow {
    /// Which receiver: `R1`, `R3`, `R4`, `R5`, `B7phys` or `T7`.
    pub receiver: &'static str,
    /// Which contract.
    pub contract: AtlasContract,
    /// What its verification returned.
    pub status: ContractStatus,
}

/// **R1 rebase equivariance, computed.** The exact transfer object of a linearization is unchanged
/// by the chart change `(A,B,C) ↦ (TAT⁻¹, TB, CT⁻¹)`.
///
/// Lean counterpart: `Foundation/CausalChord.lean::rebase_transfer`, and
/// `Foundation/ReceiverAtlas.lean::causalChord_is_rebase_equivariant` states it as this contract.
fn verify_r1_rebase_equivariance() -> ContractStatus {
    let build = || -> Result<(bool, usize), ChordRefusal> {
        let state = ExactRatMatrix::new(vec![
            vec![Rat::zero(), Rat::one()],
            vec![-Rat::from_integer(BigInt::from(2)), -Rat::from_integer(BigInt::from(3))],
        ])?;
        let excitation = ExactRatMatrix::new(vec![vec![Rat::one()], vec![Rat::zero()]])?;
        let readout = ExactRatMatrix::new(vec![vec![Rat::one(), Rat::zero()]])?;
        let linearization = Linearization::declared(
            "ledger|r1|rebase",
            state,
            excitation,
            readout,
            vec!["u".to_owned()],
            vec!["y".to_owned()],
        )?;
        let chart = ExactRatMatrix::new(vec![
            vec![Rat::one(), Rat::one()],
            vec![Rat::zero(), Rat::one()],
        ])?;
        let rebased = linearization.rebased(&chart)?;
        let before = transfer_function(&linearization)?;
        let after = transfer_function(&rebased)?;
        let same = before.characteristic() == after.characteristic()
            && before.entries.len() == after.entries.len()
            && before
                .entries
                .iter()
                .zip(&after.entries)
                .all(|(a, b)| a.numerator == b.numerator && a.denominator == b.denominator);
        Ok((same, before.entries.len()))
    };
    match build() {
        Ok((true, entries)) => ContractStatus::satisfied(
            format!(
                "causal_chord::transfer_function is entrywise identical before and after the chart \
                 change (A,B,C) -> (TAT^-1, TB, CT^-1) on a 2x2 single-port linearization: \
                 {entries} entry and the characteristic polynomial agree exactly"
            ),
        ),
        Ok((false, _)) => ContractStatus::Failed {
            counterexample: "the transfer object changed under a chart change".to_owned(),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **R1 source accountability, computed.** Every returned chord component names its source port,
/// its transport path and its exact residual; no component is anonymous.
fn verify_r1_source_accountability() -> ContractStatus {
    let build = || -> Result<(usize, bool), ChordRefusal> {
        let state = ExactRatMatrix::from_diagonal(vec![
            -Rat::one(),
            -Rat::from_integer(BigInt::from(2)),
        ])?;
        let excitation = ExactRatMatrix::new(vec![vec![Rat::one()], vec![Rat::one()]])?;
        let readout = ExactRatMatrix::new(vec![vec![Rat::one(), Rat::one()]])?;
        let linearization = Linearization::declared(
            "ledger|r1|accountability",
            state,
            excitation,
            readout,
            vec!["port-u".to_owned()],
            vec!["port-y".to_owned()],
        )?;
        let chord = causal_chord(&linearization)?;
        let accountable = !chord.components.is_empty()
            && chord.components.iter().all(|component| {
                component.excitation < linearization.source_count()
                    && component.transport_path < linearization.receiver_count()
                    && !component.lineage.is_empty()
                    && component.residual.is_zero()
            });
        Ok((chord.components.len(), accountable))
    };
    match build() {
        Ok((count, true)) => ContractStatus::satisfied(
            format!(
                "every one of the {count} returned chord components carries its excitation port, \
                 its transport path, its lineage and an exactly zero residual"
            ),
        ),
        Ok((_, false)) => ContractStatus::Failed {
            counterexample: "a returned chord component carried no source or a nonzero residual"
                .to_owned(),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// The triangle complex the R3 witnesses read: three occurrences, three contacts, no filled face.
fn ledger_triangle() -> Result<GradedCausalComplex, HodgeError> {
    let events = BTreeSet::from([EventId(1)]);
    let mut complex = GradedCausalComplex::default();
    let mut vertices = Vec::new();
    for at in 0..3usize {
        vertices.push(
            complex
                .found_cell(format!("v{at}"), events.clone(), 0, CausalChain::default())
                .map_err(HodgeError::from)?,
        );
    }
    for (lower, upper) in [(0usize, 1usize), (1, 2), (0, 2)] {
        let mut boundary = CausalChain::default();
        boundary.add_term(vertices[upper], ComparativeMultiplicity::positive(1_u8));
        boundary.add_term(vertices[lower], ComparativeMultiplicity::negative(1_u8));
        complex
            .found_cell(format!("e{lower}_{upper}"), events.clone(), 1, boundary)
            .map_err(HodgeError::from)?;
    }
    Ok(complex)
}

/// **R3 rebase equivariance, computed: the harmonic dimension is metric-free.** `dim ker Δ_k` is
/// the same under the unit metric and under a declared per-cell positive metric, and it equals the
/// integral Betti number in both.
fn verify_r3_metric_free_harmonic_dimension() -> ContractStatus {
    let build = || -> Result<(usize, usize, usize, usize), HodgeError> {
        let complex = ledger_triangle()?;
        let unit = MetricDeclaration::unit("ledger|r3|unit");
        let weights = complex
            .cells()
            .keys()
            .enumerate()
            .map(|(at, id)| (*id, Rat::from_integer(BigInt::from(at as i64 + 2))))
            .collect::<Vec<_>>();
        let skewed = MetricDeclaration::per_cell("ledger|r3|skewed", weights);
        let flat = HodgeOperator::found("ledger|r3|flat", &complex, &unit, &BoundaryCondition::Free)?;
        let bent =
            HodgeOperator::found("ledger|r3|bent", &complex, &skewed, &BoundaryCondition::Free)?;
        let flat_zero = hodge_reading(&flat, 0)?;
        let bent_zero = hodge_reading(&bent, 0)?;
        let flat_one = hodge_reading(&flat, 1)?;
        let bent_one = hodge_reading(&bent, 1)?;
        Ok((
            flat_zero.harmonic_dimension,
            bent_zero.harmonic_dimension,
            flat_one.harmonic_dimension,
            bent_one.harmonic_dimension,
        ))
    };
    match build() {
        Ok((a, b, c, d)) if a == b && c == d => ContractStatus::satisfied(
            format!(
                "dim ker Delta_0 = {a} and dim ker Delta_1 = {c} under the unit metric and under a \
                 declared per-cell positive metric alike; the supplied metric moves the projections \
                 and not the harmonic dimension"
            ),
        ),
        Ok((a, b, c, d)) => ContractStatus::Failed {
            counterexample: format!(
                "the harmonic dimension depends on the supplied metric: grade 0 gave {a} and {b}, \
                 grade 1 gave {c} and {d}"
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **R3 energy balance and source accountability, computed.** The three components of the Hodge
/// decomposition recombine to the cochain exactly and pair to zero exactly — the exact Pythagoras
/// is the receiver's conservation, and the three labels are what makes it accountable.
fn verify_r3_energy_balance() -> ContractStatus {
    let build = || -> Result<(bool, bool), HodgeError> {
        let complex = ledger_triangle()?;
        let unit = MetricDeclaration::unit("ledger|r3|unit");
        let operator =
            HodgeOperator::found("ledger|r3|balance", &complex, &unit, &BoundaryCondition::Free)?;
        let cochain = vec![
            Rat::from_integer(BigInt::from(3)),
            -Rat::one(),
            Rat::from_integer(BigInt::from(5)),
        ];
        let decomposition = hodge_decomposition(&operator, 1, &cochain)?;
        let recombines = cochain.iter().enumerate().all(|(at, value)| {
            value
                == &(&decomposition.exact[at] + &decomposition.coexact[at]
                    + &decomposition.harmonic[at])
        });
        let orthogonal = decomposition.pairings.iter().all(Zero::is_zero);
        Ok((recombines, orthogonal))
    };
    match build() {
        Ok((true, true)) => ContractStatus::satisfied(
            "the exact, coexact and harmonic components of a grade-1 cochain recombine to \
                      it exactly and their three pairings are exactly zero"
                .to_owned(),
        ),
        Ok((recombines, orthogonal)) => ContractStatus::Failed {
            counterexample: format!(
                "the decomposition did not balance: recombines = {recombines}, \
                 pairings vanish = {orthogonal}"
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// The exact rational rotation `[[3/5, −4/5], [4/5, 3/5]]` composed with a translation: a rigid
/// motion over `Q` with no irrational entry and no float.
fn rigid_motion(place: &[Rat]) -> Vec<Rat> {
    let three_fifths = Rat::new(BigInt::from(3), BigInt::from(5));
    let four_fifths = Rat::new(BigInt::from(4), BigInt::from(5));
    let shift = Rat::from_integer(BigInt::from(7));
    vec![
        &three_fifths * &place[0] - &four_fifths * &place[1] + &shift,
        &four_fifths * &place[0] + &three_fifths * &place[1] - &shift,
    ]
}

/// **R4 rebase equivariance, computed: the rigid motions are invariant.** The rank, the motion
/// dimension and the self-stress dimension of a constraint Jacobian are unchanged by an exact
/// rational rigid motion of its configuration, and the trivial-motion dimension is *measured*
/// rather than assumed.
fn verify_r4_trivial_motion_invariance() -> ContractStatus {
    let build = || -> Result<(RigidityReading, RigidityReading, usize, usize), RigidityError> {
        let places = [
            vec![Rat::zero(), Rat::zero()],
            vec![Rat::from_integer(BigInt::from(4)), Rat::zero()],
            vec![Rat::zero(), Rat::from_integer(BigInt::from(3))],
        ];
        let declared = |transform: bool| -> Result<ExactConfiguration, RigidityError> {
            ExactConfiguration::declared(
                2,
                places.iter().enumerate().map(|(at, place)| {
                    (
                        ConstraintVertexId(at as u64 + 1),
                        if transform {
                            rigid_motion(place)
                        } else {
                            place.clone()
                        },
                    )
                }),
            )
        };
        let mut constraints = BTreeMap::new();
        for (lower, upper) in [(1u64, 2u64), (2, 3), (1, 3)] {
            let (edge, _) =
                ConstraintEdge::new(ConstraintVertexId(lower), ConstraintVertexId(upper))?;
            constraints.insert(edge, EdgeProvenance::AdmittedContact);
        }
        let before = RigidityJacobian::found("ledger|r4|before", &declared(false)?, &constraints)?;
        let after = RigidityJacobian::found("ledger|r4|after", &declared(true)?, &constraints)?;
        let before_motions = TrivialMotionReading::measure(&before)?;
        let after_motions = TrivialMotionReading::measure(&after)?;
        Ok((
            rigidity_reading(&before)?,
            rigidity_reading(&after)?,
            before_motions.dimension_of_span,
            after_motions.dimension_of_span,
        ))
    };
    match build() {
        Ok((before, after, before_trivial, after_trivial))
            if before.rank == after.rank
                && before.motion_dimension == after.motion_dimension
                && before.self_stress_dimension == after.self_stress_dimension
                && before_trivial == after_trivial =>
        {
            ContractStatus::satisfied(
                format!(
                    "under the exact rational rigid motion [[3/5,-4/5],[4/5,3/5]] plus a \
                     translation, rank J = {}, dim ker J = {}, dim ker J^T = {} and the measured \
                     trivial-motion dimension {before_trivial} are all unchanged",
                    before.rank, before.motion_dimension, before.self_stress_dimension
                ),
            )
        }
        Ok((before, after, before_trivial, after_trivial)) => ContractStatus::Failed {
            counterexample: format!(
                "a rigid motion moved the reading: rank {} vs {}, motions {} vs {}, self-stress {} \
                 vs {}, trivial {before_trivial} vs {after_trivial}",
                before.rank,
                after.rank,
                before.motion_dimension,
                after.motion_dimension,
                before.self_stress_dimension,
                after.self_stress_dimension
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **R4 source accountability, computed.** Every constraint's contribution is named: its removal
/// either moves `dim ker J` by exactly one or moves nothing, and which it is, is read off the
/// self-stress support rather than recomputed — a cross-check the receiver runs at every reading.
fn verify_r4_source_accountability() -> ContractStatus {
    let build = || -> Result<(usize, usize, usize), RigidityError> {
        let places = [
            vec![Rat::zero(), Rat::zero()],
            vec![Rat::from_integer(BigInt::from(4)), Rat::zero()],
            vec![Rat::zero(), Rat::from_integer(BigInt::from(3))],
        ];
        let configuration = ExactConfiguration::declared(
            2,
            places
                .iter()
                .enumerate()
                .map(|(at, place)| (ConstraintVertexId(at as u64 + 1), place.clone())),
        )?;
        let mut constraints = BTreeMap::new();
        for (lower, upper) in [(1u64, 2u64), (2, 3), (1, 3)] {
            let (edge, _) =
                ConstraintEdge::new(ConstraintVertexId(lower), ConstraintVertexId(upper))?;
            constraints.insert(edge, EdgeProvenance::AdmittedContact);
        }
        let jacobian =
            RigidityJacobian::found("ledger|r4|accountability", &configuration, &constraints)?;
        let reading = rigidity_reading(&jacobian)?;
        let sensitivity = removal_sensitivity(&jacobian, &reading)?;
        let rederived = verify_removal_sensitivity(
            &jacobian,
            &sensitivity,
            sensitivity.constraints.len(),
        )?;
        if rederived != sensitivity.constraints.len() {
            return Err(RigidityError::ReadingDisagreesWithJacobian {
                reading: rederived,
                jacobian: sensitivity.constraints.len(),
            });
        }
        Ok((
            sensitivity.constraints.len(),
            sensitivity.load_bearing.len(),
            sensitivity.redundant.len(),
        ))
    };
    match build() {
        Ok((total, load_bearing, redundant)) if total == load_bearing + redundant => {
            ContractStatus::satisfied(
                format!(
                    "all {total} constraints are accounted: {load_bearing} load-bearing and \
                     {redundant} redundant, read off the self-stress support and re-derived by \
                     rigidity_receiver::verify_removal_sensitivity"
                ),
            )
        }
        Ok((total, load_bearing, redundant)) => ContractStatus::Failed {
            counterexample: format!(
                "{total} constraints did not partition into {load_bearing} load-bearing and \
                 {redundant} redundant"
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **R5 source accountability, computed.**
///
/// [implemented-exact] The witness is run, not asserted: a small synthetic exact population — six
/// occurrences on two presented chains, exact rational centres, no fixture — is filtered by
/// squared aperture, the persistence reading is taken over `ℚ`, and
/// [`crate::topological_receiver::grade_zero_agreement`] recomputes the grade-zero reading by the
/// independent elder-rule union–find and compares the death multiset and the essential count. The
/// row is `Satisfied` only when every returned pair carries the birth cell that created it and,
/// when it is not essential, the death cell that killed it, **and** the two grade-zero routes
/// agree.
///
/// [definition] The agreement is enforced on the production path as well:
/// [`crate::topological_receiver::persistence`] runs it before returning, so the witness text is
/// true of every reading this library takes and not only of this one.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::SourceAccountable`.
fn verify_r5_source_accountability() -> ContractStatus {
    let build = || -> Result<(usize, usize, usize), TopologicalError> {
        let place = |x: i64, y: i64| {
            CoordinateBox3::point(
                Rat::from_integer(BigInt::from(x)),
                Rat::from_integer(BigInt::from(y)),
                Rat::zero(),
            )
        };
        // Two presented chains of three occurrences each, far enough apart that the two
        // communities merge strictly after each has closed.
        let places: [(i64, i64); 6] = [(0, 0), (2, 0), (1, 2), (9, 0), (11, 0), (10, 2)];
        let mut positions = BTreeMap::new();
        let mut component_of = BTreeMap::new();
        for (at, (x, y)) in places.iter().enumerate() {
            let id = ConstraintVertexId(at as u64 + 1);
            positions.insert(id, place(*x, *y));
            component_of.insert(id, ConstraintComponentId(if at < 3 { 1 } else { 2 }));
        }
        let filtration = ApertureFiltration::found(
            "ledger|r5|accountability",
            EventId(1),
            &positions,
            &component_of,
            Rat::from_integer(BigInt::from(200)),
            2,
            4096,
        )?;
        let order = FiltrationOrder::found(&filtration, &OrderLaw::ByLowerBound)?;
        let reading = persistence(&filtration, &order, &Coefficients::Rational, 1_000_000)?;
        let agreement = grade_zero_agreement(&filtration, &order, &reading)?;
        let accounted = reading.pairs.iter().all(|pair| {
            pair.death_cell.is_some() == pair.death_position.is_some()
                && pair.death_cell.is_some() == pair.death_value.is_some()
                && filtration.complex.cell(pair.birth_cell).is_ok()
                && pair
                    .death_cell
                    .is_none_or(|cell| filtration.complex.cell(cell).is_ok())
        });
        if !accounted {
            return Err(TopologicalError::EmptyPopulation);
        }
        Ok((
            reading.pairs.len(),
            agreement.merge_values.len(),
            agreement.standing,
        ))
    };
    match build() {
        Ok((pairs, merges, standing)) => ContractStatus::satisfied(format!(
            "all {pairs} returned persistence pairs carry the birth cell that created them and, \
             where they are not essential, the death cell that killed them; and \
             topological_receiver::grade_zero_agreement recomputed the grade-zero reading by an \
             independent elder-rule union-find over the same filtration, returning the same {merges} \
             merges and the same {standing} standing communities. The cross-check runs inside \
             topological_receiver::persistence itself, so it is enforced at every reading this \
             library takes and not only here."
        )),
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built or did not agree: {error}"),
        },
    }
}


/// **B7's physicochemical receiver, rebase equivariance, computed.** Every reading is a function of
/// the pairwise exact separations and the declared site chemistry alone, so an exact rational rigid
/// motion of the whole configuration must move none of them.
///
/// The motion is the composed Pythagorean rotation `R_z(3/5, 4/5) · R_x(5/13, 12/13)` with a
/// translation; `physicochemical_receiver::RigidMotion::declare` checks `RᵀR = I` entry by entry
/// over `Q` before the motion exists at all, so no approximate rotation can reach a reading.
fn verify_b7_physicochemical_rigid_motion_invariance() -> ContractStatus {
    type Reading = (BTreeMap<ClassPair, u64>, u64, usize, usize);
    let build = || -> Result<(Reading, Reading), PhysicochemicalRefusal> {
        let rational = |numerator: i64| Rat::from_integer(BigInt::from(numerator));
        let motion = RigidMotion::declared_pythagorean([
            rational(7),
            rational(-3),
            rational(11),
        ])?;
        let window = HydrogenBondWindow::conventional();
        let bound = PairWorkBound::declare(
            4_096,
            "the worked witness addresses eight sites, so its pair population is C(8,2) = 28",
        )?;
        let read = |motion: Option<&RigidMotion>| -> Result<Reading, PhysicochemicalRefusal> {
            let worked = worked_presentation(motion)?;
            let composition = composition_under_declared_protonation(
                &worked.complex,
                &worked.sites,
                &worked.tables,
                &worked.basis,
                0,
            )?;
            let population = PairPopulation::AmongSites {
                sites: worked.sites.sites().keys().copied().collect(),
                minimum_residue_separation: 1,
            };
            let hydrogen = hydrogen_bond_candidates(
                &worked.complex,
                &worked.sites,
                &worked.tables,
                &window,
                &population,
                &bound,
            )?;
            let steric = steric_overlaps(
                &worked.complex,
                &worked.sites,
                &worked.tables,
                &Rat::new(BigInt::from(4), BigInt::from(10)),
                &population,
                &bound,
            )?;
            Ok((
                composition.admitted.clone(),
                composition.admitted_total,
                hydrogen.candidates.len(),
                steric.clashes.len(),
            ))
        };
        Ok((read(None)?, read(Some(&motion))?))
    };
    match build() {
        Ok((before, after)) if before == after && before.1 > 0 => ContractStatus::satisfied(
            format!(
                "under the exact rational rigid motion R_z(3/5,4/5)·R_x(5/13,12/13) plus a \
                 translation, the residue-class composition ({} admitted contacts over {} class \
                 pairs), the hydrogen-bond candidate count {} and the steric overlap count {} are \
                 all unchanged; the rotation's orthogonality is checked entry by entry over Q \
                 before it can be applied",
                before.1,
                before.0.len(),
                before.2,
                before.3
            ),
        ),
        Ok((before, after)) => ContractStatus::Failed {
            counterexample: format!(
                "a rigid motion moved the reading: {before:?} against {after:?}"
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **B7's physicochemical receiver, source accountability, computed.** Every returned count is
/// accounted for: the per-class-pair counts sum to the admitted total, the admitted, undecided and
/// excluded counts exhaust the addressed population, and every hydrogen-bond candidate and every
/// steric overlap names the two addressed sites and carries the exact squared-distance interval its
/// verdict was taken from.
fn verify_b7_physicochemical_source_accountability() -> ContractStatus {
    let build = || -> Result<(u64, u64, usize, usize), PhysicochemicalRefusal> {
        let worked = worked_presentation(None)?;
        let composition = composition_under_declared_protonation(
            &worked.complex,
            &worked.sites,
            &worked.tables,
            &worked.basis,
            0,
        )?;
        let by_pair: u64 = composition.admitted.values().sum();
        let by_open: u64 = composition.open.values().sum();
        if by_pair != composition.admitted_total || by_open != composition.open_total {
            return Err(PhysicochemicalRefusal::PairCountOverflows);
        }
        if composition.admitted_total + composition.open_total + composition.excluded_total
            != composition.population
        {
            return Err(PhysicochemicalRefusal::PairCountOverflows);
        }
        let bound = PairWorkBound::declare(
            4_096,
            "the worked witness addresses eight sites, so its pair population is C(8,2) = 28",
        )?;
        let population = PairPopulation::AmongSites {
            sites: worked.sites.sites().keys().copied().collect(),
            minimum_residue_separation: 1,
        };
        let hydrogen = hydrogen_bond_candidates(
            &worked.complex,
            &worked.sites,
            &worked.tables,
            &HydrogenBondWindow::conventional(),
            &population,
            &bound,
        )?;
        let steric = steric_overlaps(
            &worked.complex,
            &worked.sites,
            &worked.tables,
            &Rat::new(BigInt::from(4), BigInt::from(10)),
            &population,
            &bound,
        )?;
        // Every returned candidate and every returned overlap names two standing sites and carries
        // the exact interval it was decided from, re-derived here from the presentation itself.
        for (left, right, interval) in hydrogen
            .candidates
            .iter()
            .map(|candidate| {
                (
                    candidate.donor,
                    candidate.acceptor,
                    candidate.squared_distance.clone(),
                )
            })
            .chain(steric.clashes.iter().map(|clash| {
                (clash.left, clash.right, clash.squared_distance.clone())
            }))
        {
            worked.sites.site(left)?;
            worked.sites.site(right)?;
            let a = &worked
                .complex
                .vertices
                .get(&left)
                .ok_or(PhysicochemicalRefusal::SiteAbsent { vertex: left })?
                .position;
            let b = &worked
                .complex
                .vertices
                .get(&right)
                .ok_or(PhysicochemicalRefusal::SiteAbsent { vertex: right })?
                .position;
            if a.squared_distance(b) != interval {
                return Err(PhysicochemicalRefusal::PairCountOverflows);
            }
        }
        Ok((
            composition.population,
            composition.admitted_total,
            hydrogen.candidates.len(),
            steric.clashes.len(),
        ))
    };
    match build() {
        Ok((population, admitted, candidates, clashes)) => ContractStatus::satisfied(format!(
            "over {population} addressed pairs the per-class-pair counts sum to the admitted total \
             {admitted}, the admitted, undecided and excluded counts exhaust the population, and \
             every one of the {candidates} hydrogen-bond candidates and {clashes} steric overlaps \
             names two standing sites and carries an exact squared-distance interval re-derived \
             here from the presentation's own coordinates"
        )),
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built or did not account: {error}"),
        },
    }
}

/// **B7's physicochemical receiver, energy balance, computed.** The declared finite electrostatic
/// model's enclosure over a pair population is **exactly** the sum of its enclosures over a
/// declared partition of that population: the parts recombine to the whole, endpoint for endpoint,
/// with no widening. That is the conservation this receiver owes, and it is recomputed rather than
/// asserted.
fn verify_b7_physicochemical_energy_balance() -> ContractStatus {
    let build = || -> Result<(String, u64), PhysicochemicalRefusal> {
        let worked = worked_presentation(None)?;
        let bound = PairWorkBound::declare(
            4_096,
            "the worked witness addresses eight sites, so its pair population is C(8,2) = 28",
        )?;
        let every: Vec<_> = worked.sites.sites().keys().copied().collect();
        let left_half: BTreeSet<_> = every[..4].iter().copied().collect();
        let right_half: BTreeSet<_> = every[4..].iter().copied().collect();
        let enclose = |population: PairPopulation| {
            electrostatic_enclosure(
                &worked.complex,
                &worked.sites,
                &worked.tables,
                &worked.basis,
                &population,
                &bound,
                32,
            )
        };
        let whole = enclose(PairPopulation::AmongSites {
            sites: every.iter().copied().collect(),
            minimum_residue_separation: 1,
        })?;
        let across = enclose(PairPopulation::SitesAgainstPresentation {
            sites: left_half,
            minimum_residue_separation: 1,
        })?;
        let within = enclose(PairPopulation::AmongSites {
            sites: right_half,
            minimum_residue_separation: 1,
        })?;
        let recombined = across.enclosure.sum(&within.enclosure)?;
        if recombined.enclosure() != whole.enclosure.enclosure() {
            return Err(PhysicochemicalRefusal::PairCountOverflows);
        }
        Ok((whole.enclosure.render(), whole.contributing_pairs))
    };
    match build() {
        Ok((rendered, contributing)) => ContractStatus::satisfied(format!(
            "the declared finite electrostatic model's enclosure over the whole pair population, \
             {rendered} from {contributing} contributing pairs, is exactly the sum of its \
             enclosures over a declared two-part partition of that population; the parts recombine \
             endpoint for endpoint with no widening, and the reading carries its unit rather than \
             being a bare number"
        )),
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built or did not balance: {error}"),
        },
    }
}

/// **The contract ledger: which receiver satisfies which contract, computed where it can be and
/// named as unproved where it cannot.**
///
/// [implemented-exact] The `Satisfied` rows are *recomputed on every call*, and that is enforced
/// by the types rather than by convention: [`ContractStatus::Satisfied`] carries a [`Recomputed`]
/// token whose only constructor is private to this module, so the arm has no literal anywhere;
/// and every row that is **not** recomputed is a [`ContractEntry::Standing`] carrying a
/// [`StandingStatus`], which has no `Satisfied` arm at all. A row is therefore `Satisfied` exactly
/// when a verifier function computed it, and
/// `the_contract_ledger_recomputes_every_satisfied_row` enumerates [`ledger_entries`] generically
/// to check that correspondence row by row.
///
/// [definition] The `Unproved` rows name the concrete absent law, the `Failed` rows cite the
/// counterexample their owner already returns, and the `NotApplicable` rows say why the contract
/// has no content for that receiver. Nothing here says "required", "guaranteed" or "discharged"
/// about a law this library does not enforce.
///
/// Lean counterpart: `Foundation/ReceiverAtlas.lean::RebaseEquivariant`, `SourceAccountable`,
/// `DeclarationIndependent` and `causalChord_is_rebase_equivariant`.
pub fn contract_ledger() -> Vec<ContractRow> {
    ledger_entries()
        .into_iter()
        .map(|(receiver, contract, entry)| ContractRow {
            receiver,
            contract,
            status: entry.status(),
        })
        .collect()
}

/// The two-loop resistive network the T7 witnesses read: four nodes, five branches, unit
/// conductance, and an injection that sums to zero.
fn ledger_two_loop_network() -> Result<(ResistiveNetwork, Vec<Rat>), JunctionRefusal> {
    let branches = [
        (0usize, 1usize, Rat::one()),
        (1, 2, Rat::one()),
        (2, 3, Rat::one()),
        (3, 0, Rat::one()),
        (0, 2, Rat::one()),
    ];
    let network = ResistiveNetwork::declare("ledger|t7|two-loop", 4, &branches)?;
    let injection = vec![Rat::one(), Rat::zero(), -Rat::one(), Rat::zero()];
    Ok((network, injection))
}

/// **T7 energy balance, computed: Tellegen's theorem at a junction.**
///
/// The pairing of the branch drops with the branch flux equals the pairing of the node potentials
/// with the declared injection, exactly. This is the summation-by-parts identity
/// `Foundation/HodgeReceiver.lean::codiff₀_adjoint` read at a balanced flux, and it is the
/// conservation a junction owes: power delivered at the nodes is power dissipated along the
/// branches, with no tolerance anywhere.
fn verify_t7_tellegen_energy_balance() -> ContractStatus {
    let build = || -> Result<(bool, bool, usize), JunctionRefusal> {
        let (network, injection) = ledger_two_loop_network()?;
        let solution = network.solve(&injection)?;
        if !solution.solved() {
            return Ok((false, false, 0));
        }
        let receipt = network.power_ledger(&solution.potentials)?;
        let dissipation_is_positive = receipt.dissipated.parts().0 > &Rat::zero();
        Ok((
            receipt.balances(),
            dissipation_is_positive,
            receipt.checked.len(),
        ))
    };
    match build() {
        Ok((true, true, checked)) => ContractStatus::satisfied(format!(
            "junction_law::tellegen returns an exactly zero residual on a four-node, five-branch \
             resistive network read at {checked} nodes: the pairing of the drops with the flux and \
             the pairing of the potential with the injection are the same exact rational, and the \
             dissipation is strictly positive so the balance is not the trivial one"
        )),
        Ok((balanced, positive, _)) => ContractStatus::Failed {
            counterexample: format!(
                "the power ledger did not balance: balances = {balanced}, dissipation positive = \
                 {positive}"
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **T7 gluing with interface coupling, computed.**
///
/// The reading of the glued object is determined by the two sides' readings **together with the
/// interface coupling**, and not by the sides alone: the normal jump at the interface is the sum
/// of the two sides' outward normal fluxes, and changing only the declared coupling on one side —
/// the permittivity, which is the Hodge metric weight there — moves the glued reading while both
/// sides' fields stay exactly what they were.
fn verify_t7_gluing_with_interface_coupling() -> ContractStatus {
    let build = || -> Result<(Rat, Rat, bool), JunctionRefusal> {
        let units = JointUnits::electrostatic()?;
        let field = vec![Rat::one(), Rat::new(BigInt::one(), BigInt::from(3))];
        let source = vec![
            -Rat::from_integer(BigInt::from(2)),
            Rat::one(),
            Rat::one(),
        ];
        let potential = vec![
            Rat::zero(),
            Rat::one(),
            Rat::new(BigInt::from(4), BigInt::from(3)),
        ];
        let mut jumps = Vec::new();
        for right_permittivity in [3i64, 6] {
            let branches = [
                (0usize, 1usize, Rat::from_integer(BigInt::from(2))),
                (1, 2, Rat::from_integer(BigInt::from(right_permittivity))),
            ];
            let chain = ResistiveNetwork::declare("ledger|t7|dielectric", 3, &branches)?;
            let operator = chain.operator();
            let interface = Interface::declare(
                "ledger|t7|interface",
                operator,
                0,
                [
                    (operator.cells(1)[0], Side::Left),
                    (operator.cells(1)[1], Side::Right),
                ]
                .into_iter()
                .collect(),
                [operator.cells(0)[1]].into_iter().collect(),
            )?;
            let verdict = check_junction(
                operator,
                &interface,
                &JunctionField {
                    potential: &potential,
                    field: &field,
                    source: &source,
                },
                &units,
            )?;
            let jump = match &verdict {
                JunctionVerdict::Balanced { law, .. } | JunctionVerdict::Unbalanced { law, .. } => {
                    law.normal_jump()
                        .values()
                        .next()
                        .cloned()
                        .unwrap_or_else(Rat::zero)
                }
                JunctionVerdict::Open { .. } => Rat::zero(),
            };
            jumps.push(jump);
        }
        let declared_matches = jumps[0] == Rat::one();
        Ok((jumps[0].clone(), jumps[1].clone(), declared_matches))
    };
    match build() {
        Ok((first, second, true)) if first != second => ContractStatus::satisfied(format!(
            "the normal jump of the displacement at a two-material interface is the sum of the two \
             sides' outward normal fluxes, and it is {first} at permittivity 3 against {second} at \
             permittivity 6 with both sides' fields unchanged: the glued reading is the parts' \
             readings together with the declared interface coupling, and the parts alone do not \
             determine it"
        )),
        Ok((first, second, matched)) => ContractStatus::Failed {
            counterexample: format!(
                "the coupling did not move the glued reading, or the declared balance was wrong: \
                 {first} against {second}, declared balance held = {matched}"
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **T7 source accountability, computed.** Every component of a junction reading is indexed by the
/// joint cell it was read at, the balanced arm names every cell it evaluated, and the unbalanced
/// arm returns the residual cochain whole rather than a norm of it.
fn verify_t7_source_accountability() -> ContractStatus {
    let build = || -> Result<(usize, usize, bool), JunctionRefusal> {
        let units = JointUnits::electrostatic()?;
        let branches = [
            (0usize, 1usize, Rat::from_integer(BigInt::from(2))),
            (1, 2, Rat::from_integer(BigInt::from(3))),
        ];
        let chain = ResistiveNetwork::declare("ledger|t7|accountability", 3, &branches)?;
        let operator = chain.operator();
        let potential = vec![
            Rat::zero(),
            Rat::one(),
            Rat::new(BigInt::from(4), BigInt::from(3)),
        ];
        let field = vec![Rat::one(), Rat::new(BigInt::one(), BigInt::from(3))];
        let wrong = vec![
            -Rat::from_integer(BigInt::from(2)),
            Rat::from_integer(BigInt::from(5)),
            Rat::one(),
        ];
        let interface = Interface::declare(
            "ledger|t7|accountability|interface",
            operator,
            0,
            [
                (operator.cells(1)[0], Side::Left),
                (operator.cells(1)[1], Side::Right),
            ]
            .into_iter()
            .collect(),
            [operator.cells(0)[1]].into_iter().collect(),
        )?;
        let verdict = check_junction(
            operator,
            &interface,
            &JunctionField {
                potential: &potential,
                field: &field,
                source: &wrong,
            },
            &units,
        )?;
        match verdict {
            JunctionVerdict::Unbalanced {
                law,
                residual,
                offending,
            } => Ok((
                residual.len(),
                offending.len(),
                residual.keys().all(|cell| law.normal_jump().contains_key(cell))
                    && law.source().len() == law.normal_jump().len(),
            )),
            _ => Ok((0, 0, false)),
        }
    };
    match build() {
        Ok((residual, offending, true)) if residual > 0 && offending > 0 => {
            ContractStatus::satisfied(format!(
                "a junction reading that does not balance returns its residual as a cochain of \
                 {residual} entry indexed by joint cell, names the {offending} offending cell, and \
                 carries the jump and the source at exactly the same joint population"
            ))
        }
        Ok((residual, offending, indexed)) => ContractStatus::Failed {
            counterexample: format!(
                "the reading was not accountable: residual entries = {residual}, offending = \
                 {offending}, indexed by the joint = {indexed}"
            ),
        },
        Err(error) => ContractStatus::Unproved {
            missing: format!("the witness could not be built: {error}"),
        },
    }
}

/// **Every ledger row, as `(receiver, contract, how its status is produced)`.**
///
/// [definition] There is no status literal in this table. A row is either
/// [`ContractEntry::Recomputed`] — a verifier run on every call — or [`ContractEntry::Standing`],
/// whose [`StandingStatus`] has no `Satisfied` arm. A `Satisfied` row therefore cannot exist
/// without a recomputation, and `the_contract_ledger_recomputes_every_satisfied_row` enumerates
/// this table generically to say so.
pub fn ledger_entries() -> Vec<(&'static str, AtlasContract, ContractEntry)> {
    vec![
        ("R1", AtlasContract::RebaseEquivariance, ContractEntry::Recomputed(verify_r1_rebase_equivariance)),
        ("R1", AtlasContract::DeclarationIndependence, ContractEntry::Standing(StandingStatus::NotApplicable {
                reason: "causal_chord reads a Linearization and nothing else: there is no supplied \
                         metric, field or order for the transfer object to depend on, so the \
                         contract has no content here. Inventing a declaration to be independent \
                         of would be a second receiver."
                    .to_owned(),
            })),
        ("R1", AtlasContract::SourceAccountability, ContractEntry::Recomputed(verify_r1_source_accountability)),
        ("R1", AtlasContract::EnergyBalance, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "the rate identity E_G' = Re(x* G s) + x* Sigma_G x / 2 is proved only at \
                          one dimension (Physics/PortEnergyHeat.lean:157). causal_chord::rate_form \
                          computes Sigma_G exactly and causal_chord::rate_form_congruence checks \
                          its congruence law, but no discrete port balance is enforced at a \
                          reading, so no balance is claimed here."
                    .to_owned(),
            })),
        ("R1", AtlasContract::GluingWithInterfaceCoupling, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "no interconnection receiver exists: causal_chord carries no series, \
                          parallel or feedback composition of two linearizations, so there is no \
                          law relating a glued system's transfer object to its parts' plus an \
                          interface coupling."
                    .to_owned(),
            })),
        ("R1", AtlasContract::StabilityAwayFromBifurcation, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "causal_chord::half_plane_count is exact at one polynomial and carries no \
                          modulus of continuity; no bound relates two nearby coefficient vectors' \
                          pole populations, so stability away from a bifurcation is unproved."
                    .to_owned(),
            })),
        ("R3", AtlasContract::RebaseEquivariance, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "hodge_receiver declares no chart-change or frame action on a graded \
                          complex, so there is no rebase for a reading to be equivariant under. \
                          What R3 does discharge is independence from the *supplied metric*, which \
                          is the DeclarationIndependence row below and a different contract."
                    .to_owned(),
            })),
        ("R3", AtlasContract::DeclarationIndependence, ContractEntry::Recomputed(verify_r3_metric_free_harmonic_dimension)),
        ("R3", AtlasContract::EnergyBalance, ContractEntry::Recomputed(verify_r3_energy_balance)),
        ("R3", AtlasContract::SourceAccountability, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "hodge_receiver labels the exact, coexact and harmonic parts and \
                          recombines them exactly — which is why the EnergyBalance row above is \
                          Satisfied — but a component is not indexed by the *source* that produced \
                          it: the exact potential is returned as one particular solution of a \
                          plural fibre and no per-cell source attribution exists."
                    .to_owned(),
            })),
        ("R3", AtlasContract::GluingWithInterfaceCoupling, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "no Mayer-Vietoris or interface-coupled Laplacian is implemented: a \
                          complex glued along a subcomplex has no declared reading relating its \
                          spectra to the parts' spectra and the interface."
                    .to_owned(),
            })),
        ("R3", AtlasContract::StabilityAwayFromBifurcation, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "hodge_receiver::refine_spectral_gap narrows an exact interval at one \
                          presentation; no perturbation bound relates two presentations' gaps, so \
                          the receiver's stability is measured pointwise and never proved."
                    .to_owned(),
            })),
        ("R4", AtlasContract::RebaseEquivariance, ContractEntry::Recomputed(verify_r4_trivial_motion_invariance)),
        ("R4", AtlasContract::DeclarationIndependence, ContractEntry::Standing(StandingStatus::NotApplicable {
                reason: "rigidity_receiver reads a constraint set and an ExactConfiguration. The \
                         configuration is the object read, not a structure supplied beside it, and \
                         no metric, field or order is declared to the Jacobian; there is nothing \
                         for the reading to be independent of."
                    .to_owned(),
            })),
        ("R4", AtlasContract::SourceAccountability, ContractEntry::Recomputed(verify_r4_source_accountability)),
        ("R4", AtlasContract::EnergyBalance, ContractEntry::Standing(StandingStatus::NotApplicable {
                reason: "the constraint Jacobian is a differential and carries no metric on the \
                         constraint space and no declared port; an energy balance is not among \
                         its laws, and inventing one would be a second receiver."
                    .to_owned(),
            })),
        ("R4", AtlasContract::GluingWithInterfaceCoupling, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "rigidity_receiver::rigid_clusters reads implied pairs inside one \
                          framework; no law composes two sub-frameworks' motion spaces across a \
                          shared boundary, so the gluing contract has no statement here."
                    .to_owned(),
            })),
        ("R4", AtlasContract::StabilityAwayFromBifurcation, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "the rank of J is exactly the reading that jumps at a degenerate \
                          configuration; rigidity_receiver names the degeneracies \
                          (ConfigurationDegeneracy) but proves no stability statement away from \
                          them."
                    .to_owned(),
            })),
        ("R5", AtlasContract::RebaseEquivariance, ContractEntry::Standing(StandingStatus::Failed {
                counterexample: "topological_receiver::the_projected_writhe_is_not_projection_\
                                 invariant exhibits one exact polygon whose projected writhes under \
                                 two admissible directions are 1 and 0. The linking number *is* \
                                 proved invariant under w -> -w and positive rescaling, and its \
                                 invariance under an arbitrary admissible projection change is an \
                                 open Prop tested over a declared candidate family. So R5 carries \
                                 a returned reading that is provably not equivariant, and says so."
                    .to_owned(),
            })),
        ("R5", AtlasContract::DeclarationIndependence, ContractEntry::Standing(StandingStatus::Failed {
                counterexample: "the reading depends on two supplied declarations and says so. \
                                 topological_receiver::\
                                 the_projective_plane_separates_the_rational_reading_from_the_field_two_reading \
                                 exhibits one exact complex whose persistence over Q and over F_2 \
                                 differ, so the declared coefficient field decides the reading; and \
                                 an Open aperture order makes ByLowerBound and ByUpperBound two \
                                 readings of one presentation. Neither dependence is hidden — \
                                 integral_profile returns the integral torsion beside the field \
                                 reading and TorsionProfile::field_dependence_primes names the \
                                 primes at which the fields must part, and sublevel_family returns \
                                 both order bounds — but the contract is refuted, not discharged."
                    .to_owned(),
            })),
        ("R5", AtlasContract::SourceAccountability, ContractEntry::Recomputed(verify_r5_source_accountability)),
        ("R5", AtlasContract::EnergyBalance, ContractEntry::Standing(StandingStatus::NotApplicable {
                reason: "persistence, linking and writhe are combinatorial and metric-free \
                         readings; no energy is declared and none is owed."
                    .to_owned(),
            })),
        ("R5", AtlasContract::GluingWithInterfaceCoupling, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "Filtration::toTower fits a filtration to ContinuingTower::Tower on the \
                          order dual, which composes restrictions; it is not a gluing law, and no \
                          Mayer-Vietoris for persistence with an interface term is implemented."
                    .to_owned(),
            })),
        ("R5", AtlasContract::StabilityAwayFromBifurcation, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "no stability bound is proved. The measured finding is the opposite \
                          direction: the deposited decimal precision, not the geometry, decides \
                          whether the aperture order is decided at all, and the two family bounds \
                          can return different pairings."
                    .to_owned(),
            })),
        ("B7phys", AtlasContract::RebaseEquivariance, ContractEntry::Recomputed(verify_b7_physicochemical_rigid_motion_invariance)),
        ("B7phys", AtlasContract::DeclarationIndependence, ContractEntry::Standing(StandingStatus::Failed {
                counterexample: "the declared parameter table decides the reading, and the owner \
                                 ships two named tables that exhibit it: \
                                 physicochemical_receiver::residue_classes_histidine_polar files \
                                 histidine polar and residue_classes_histidine_positive files it \
                                 positively charged, and on a presentation carrying a histidine \
                                 the two give different compositions — \
                                 a_second_table_changes_the_reading_and_the_comparison_refuses \
                                 exhibits one whose salt-bridge candidate count is 0 under the \
                                 first and 1 under the second. The dependence is not hidden: every \
                                 reading carries its TableIdentity and compare_across_tables \
                                 refuses two readings taken under different tables unless a \
                                 TablePassage accounting for every divergent residue is supplied. \
                                 The contract is refuted, not discharged."
                    .to_owned(),
            })),
        ("B7phys", AtlasContract::SourceAccountability, ContractEntry::Recomputed(verify_b7_physicochemical_source_accountability)),
        ("B7phys", AtlasContract::EnergyBalance, ContractEntry::Recomputed(verify_b7_physicochemical_energy_balance)),
        ("B7phys", AtlasContract::GluingWithInterfaceCoupling, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "CompositionReading::sum is additive over two populations that are \
                          already disjoint; it is not a gluing law. Gluing two presented parts \
                          owes the interface pairs neither part carries, and no law relates a \
                          whole's composition or electrostatic enclosure to its parts' readings \
                          plus a declared interface term without recomputing the cross population \
                          from the joined coordinates. The absent object is that interface term."
                    .to_owned(),
            })),
        ("B7phys", AtlasContract::StabilityAwayFromBifurcation, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "no continuity bound is proved and the measured finding runs the other \
                          way: a contact whose exact interval straddles the aperture makes the \
                          composition a family between two bounds that differ, and a last-place \
                          change in a deposited coordinate can carry a donor-acceptor pair across \
                          a hydrogen-bond window bound. Both are carried as undecided rather than \
                          rounded, which is honesty about the discontinuity and not a bound on it."
                    .to_owned(),
            })),
        ("T7", AtlasContract::RebaseEquivariance, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "junction_law reads a GradedCausalComplex, a declared metric and three \
                          cochains. This repository declares no relabelling action on that complex \
                          and no induced action on cochains, so there is no rebase for the junction \
                          reading to be equivariant under. The concrete absent object is a declared \
                          cell-relabelling functor with its action on the coboundary and the \
                          metric."
                    .to_owned(),
            })),
        ("T7", AtlasContract::DeclarationIndependence, ContractEntry::Standing(StandingStatus::NotApplicable {
                reason: "the declared metric IS the constitutive law here — the conductance of a \
                         branch, the permittivity of a side — so the reading depends on it by \
                         construction and must. That dependence is what the GluingWithInterfaceCoupling \
                         row computes. Independence from the supplied metric would be independence \
                         from the material, and asserting it would be a different receiver."
                    .to_owned(),
            })),
        ("T7", AtlasContract::SourceAccountability, ContractEntry::Recomputed(verify_t7_source_accountability)),
        ("T7", AtlasContract::EnergyBalance, ContractEntry::Recomputed(verify_t7_tellegen_energy_balance)),
        ("T7", AtlasContract::GluingWithInterfaceCoupling, ContractEntry::Recomputed(verify_t7_gluing_with_interface_coupling)),
        ("T7", AtlasContract::StabilityAwayFromBifurcation, ContractEntry::Standing(StandingStatus::Unproved {
                missing: "no perturbation bound relates two nearby declared metrics' junction \
                          readings. The nodal solve is exact at one presentation and carries no \
                          modulus of continuity, and the total-internal-reflection classification \
                          is a strict sign condition whose grazing case is returned as its own \
                          value rather than folded into either neighbour — which is honesty about \
                          the discontinuity, not a bound on it."
                    .to_owned(),
            })),
    ]
}

#[cfg(test)]
mod tests;
