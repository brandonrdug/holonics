//! The continuing tube read through the engine's receivers: the grain and presentation tubes, the
//! two-axis horizon, the defect profile and the route plan.
//!
//! [definition] The tube's own carrier law — [`StationedTower`], the two-axis commuting square
//! ([`check_commuting_square`], [`SquareVerdict`], [`SquareDefect`]), circuit holonomy and the
//! wormhole receipt — moved to `crates/holonic-core/src/restriction/tube.rs`
//! (`holonic_core::restriction::tube`) in phase 6 of
//! `docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md` and is re-exported here at its old
//! paths. What stays is every layer that needs an engine owner: the grain tube over
//! `grain_tower`, the presentation tube over `physical_constraint_complex`, and the horizon,
//! profile and route layers, which read a tube through `receiver_release`'s `Horizon`, width and
//! `ExactFace` and through `relation_ladder`'s `Rung` (receivers are phase 7; they do not move
//! before it).
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Transport/ContinuingTube.lean`, namespace
//! `Soma.Holonics.Transport.ContinuingTube`. The rows for the carrier law live in the core module's
//! table; the rows below are this file's.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `grainSquareDefect` | [`GrainReadingTube`], [`GrainStation`] |
//! | `grainSquare_defect_is_not_a_loss` | `grain_tower::GrainSelection` `Transition::check_reopen` (cited) |
//! | `ObserverAt`, `VisibleSquare` | [`Observer`], [`HorizonDeclaration`] |
//! | `visibleSquare_shift` | `two_observers_of_one_region_read_different_profiles` |
//! | `StrictlyRefines`, `CoveredBy`, `CoverAdjacent`, `coverAdjacent_symm`, `coverAdjacent_comparable` | [`index_distance`], [`IndexReading`] |
//! | `DeclaredTube`, `DeclaredTube.ProfileFlat`, `profileFlat_of_chartwise` | [`StationedTower`], [`DefectProfile`] |
//! | `tube_profile_is_flat_at_every_horizon` | `a_functorial_tube_has_an_identically_zero_profile` |
//! | `cycleTube`, `cycleShortCircuit_has_no_defect`, `cycleLongCircuit_hasDefect`, `flat_near_curved_far` | `a_tube_can_be_a_sharp_lattice_near_and_curved_far` |
//! | `ladderTower`, `ladderStep`, `ladderSquare_fails_at_the_top`, `ladderSquare_commutes_below` | the ladder tube of `continuing_tube/tests.rs` |
//! | `ladder_coveredBy_iff`, `ladder_chain_rank_bound`, `the_fine_observer_sees_at_one_step_what_the_coarse_one_sees_at_three` | `two_observers_of_one_region_read_different_profiles` |
//! | `receiver_defect_is_a_structural_defect`, `ladderReceiverInsufficiency`, `no_transformer_from_the_flat_reading` | [`SquareReading`], `a_poorer_receiver_reads_flat_what_a_richer_one_separates` |
//! | `descending_chain_is_the_tubes_own`, `rising_step_needs_the_retained_residual`, `the_three_kinds_of_cross_rank_passage` | [`CrossRankPassage`], [`classify_cross_rank`] |
//! | `grainContactReading` | [`GrainContactCount`] |
//!
//! Two names this module also cites belong to other Lean owners and are therefore not rows of that
//! table: `Foundation/ContinuingTower.lean::padicFibre_card` (the cross-section count) and
//! `Foundation/GrainRestriction.lean::equal_aperture_is_not_lawful` (the measured witness of the
//! failing grain square).
//!
//! # The physical realization
//!
//! `crates/holonic-engine/src/tube.rs::ReceiverTube` is the same two axes as physical apparatus —
//! a core receiver, a transverse section, a horizon that is the link of the receiver's simplicial
//! star, an exact projective attachment, and `ReceiverTube::presentation_holonomy` as the composite
//! of its longitudinal presentation word. The core tube is the carrier law that owner
//! instantiates; neither is a description of the other.

use std::collections::BTreeSet;
use std::fmt::{self, Debug};

use num_bigint::BigInt;
use num_traits::Zero;
use relational_geometry::Rat;

pub use holonic_core::restriction::tube::{
    CircuitDefect, CommutingSquares, ConstantTube, DECLARED_CHART_CEILING,
    DECLARED_CIRCUIT_CEILING, DECLARED_FACE_CEILING, DECLARED_WORK_CEILING, FlipTube,
    HolonomyVerdict, IdentityCircuit, LossySwapMigration, SquareDefect, SquareVerdict,
    StationedTower, TubeFace, TubeHolonomyVerdict, TubeIndex, TubeOutcome, TubeRefusal,
    TubeRefusalOf, TubeSquareVerdict, TubeStation, WormholeReceipt, WormholeRefusal,
    check_circuit_holonomy, check_commuting_square, wormhole_receipt,
};
use holonic_core::restriction::tube::{declared_work, total_face_population};

use crate::continuing_tower::{Tower, TowerRefusal};
use crate::grain_tower::{
    ApertureRelation, FineNativeDeclaration, Grain, GrainAddress, GrainCell, GrainFace,
    GrainRefusal, GrainSelection, GrainTower,
};
use crate::physical_constraint_complex::ContactClass;
use crate::receiver_release::{
    DiameterNorm, ExactFace, Horizon, ReceiverWidth, WidthRefusal, width_over_readings,
};
use crate::relation_ladder::Rung;

/// The two readings of one physical presentation: the complete atom-grain face, and the
/// alpha-carbon selection of it.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::grainSquareDefect`, whose witness is
/// `Foundation/GrainRestriction.lean::equal_aperture_is_not_lawful`. This is the measured instance
/// of a **failing** two-axis square: transporting to the selected reading and then restricting
/// atom→residue is not restricting and then transporting. On the M5 deposit the two routes return
/// 301 and 1,397 `Inside` readings at an equal 8 Å aperture, with 0 in the other direction — which
/// is `grain_tower::GrainCensus`'s `fine_only_inside` and `coarse_only_inside`.
///
/// The defect is not a loss: `grain_tower::GrainSelection` carries its residual and
/// `Transition::check_reopen` returns the fine face exactly, which is
/// `grainSquare_defect_is_not_a_loss`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrainReadingTube {
    complete: GrainTower,
    selected: GrainTower,
    selection: GrainSelection,
    representatives: BTreeSet<GrainCell>,
}

/// The two stations of a [`GrainReadingTube`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum GrainStation {
    /// The complete atom-grain reading, before any selection.
    Complete,
    /// The alpha-carbon reading the M5 deed enacts by discarding every non-`CA` row.
    Selected,
}

impl GrainReadingTube {
    /// Found the tube from a declared representative population and a complete atom-grain face.
    ///
    /// The representatives are declared, never derived: `"label_atom_id == CA"` is a statement
    /// about the presentation and not a property of the grain. `GrainSelection::declare` refuses a
    /// repeated representative by name, and that refusal is returned rather than repaired.
    pub fn found(
        lineage: impl Into<String>,
        fine_aperture_squared: Rat,
        representatives: impl IntoIterator<Item = GrainAddress>,
        atom_face: GrainFace,
    ) -> Result<Self, GrainRefusal> {
        let lineage = lineage.into();
        let addresses: Vec<GrainAddress> = representatives.into_iter().collect();
        let selection = GrainSelection::declare(
            lineage.clone(),
            Grain::Residue,
            Grain::Atom,
            addresses.iter().copied(),
        )?;
        let representative_cells: BTreeSet<GrainCell> = addresses
            .iter()
            .map(|address| address.cell(Grain::Atom))
            .collect();
        let dropped: Vec<_> = atom_face
            .classified()
            .keys()
            .copied()
            .filter(|pair| {
                !(representative_cells.contains(&pair.lower)
                    && representative_cells.contains(&pair.upper))
            })
            .collect();
        let selected_face = atom_face.without(dropped);
        let relation = ApertureRelation::NativeFineWithRefusal(FineNativeDeclaration::declare(
            lineage.clone(),
            fine_aperture_squared,
        ));
        let complete = GrainTower::found(lineage.clone(), relation.clone(), atom_face)?;
        let selected = GrainTower::found(lineage, relation, selected_face)?;
        Ok(Self {
            complete,
            selected,
            selection,
            representatives: representative_cells,
        })
    }

    /// The declared selection, retained whole.
    pub fn selection(&self) -> &GrainSelection {
        &self.selection
    }

    /// The representative atom cells the selection declared.
    pub fn representatives(&self) -> &BTreeSet<GrainCell> {
        &self.representatives
    }

    /// The complete atom-grain tower.
    pub fn complete(&self) -> &GrainTower {
        &self.complete
    }

    /// The alpha-carbon tower.
    pub fn selected(&self) -> &GrainTower {
        &self.selected
    }

    /// Delete every pair not between two declared representatives. At a grain coarser than `Atom`
    /// the selection changes no cell, so the transport there is the identity — which is exactly why
    /// the square fails: the join over a residue block sees every atom pair, and the selection sees
    /// only its own.
    fn select(&self, chart: Grain, face: &GrainFace) -> GrainFace {
        if chart != Grain::Atom {
            return face.clone();
        }
        let dropped: Vec<_> = face
            .classified()
            .keys()
            .copied()
            .filter(|pair| {
                !(self.representatives.contains(&pair.lower)
                    && self.representatives.contains(&pair.upper))
            })
            .collect();
        face.without(dropped)
    }
}

impl StationedTower for GrainReadingTube {
    type Station = GrainStation;
    type Section = GrainTower;

    fn follows(&self, earlier: &GrainStation, later: &GrainStation) -> bool {
        earlier <= later
    }

    /// The face's own classified population. [`GrainReadingTube::select`] clones the whole map, so
    /// one declared face is one container carrying this many exact readings, and this is the count
    /// the check's work is proportional to. `GrainFace::classified` hands back a borrow, so reading
    /// it costs nothing and no face is copied to bound the check.
    fn declared_face_population(&self, _chart: &Grain, face: &GrainFace) -> usize {
        face.classified().len()
    }

    fn section(&self, station: &GrainStation) -> Option<&GrainTower> {
        Some(match station {
            GrainStation::Complete => &self.complete,
            GrainStation::Selected => &self.selected,
        })
    }

    fn transport(
        &self,
        earlier: &GrainStation,
        later: &GrainStation,
        chart: &Grain,
        face: &GrainFace,
    ) -> Result<GrainFace, TubeRefusal<GrainStation, Grain, GrainFace>> {
        if !self.follows(earlier, later) {
            return Err(TubeRefusal::NotAStep {
                earlier: *earlier,
                later: *later,
            });
        }
        if face.grain() != *chart {
            return Err(TubeRefusal::Section(TowerRefusal::FaceNotCarried {
                chart: *chart,
                face: face.clone(),
            }));
        }
        if earlier == later {
            return Ok(face.clone());
        }
        Ok(self.select(*chart, face))
    }
}

// =============================================================================================
// T5 — the two-axis horizon: the observer is a station and a chart
// =============================================================================================

/// The largest number of fibre candidates a caller may declare to one reach.
///
/// A step of the horizon **toward the finer charts** replaces the face the observer holds by its
/// preimage fibre, and that fibre is read off a declared candidate population. The population is
/// therefore work a caller declares, and it is bounded — by its container count here and by its
/// exact entry population inside [`DECLARED_FACE_CEILING`] — before the first fibre is opened.
pub const DECLARED_CANDIDATE_CEILING: usize = 4096;

/// The largest number of entries one [`HorizonReach`] may carry.
///
/// The reach of a two-axis horizon grows multiplicatively: each longitudinal step carries the
/// whole transverse closure, and each step toward the finer charts multiplies by the fibre. The
/// per-axis ceilings bound the declaration; this bounds what the walk may actually accumulate, and
/// exceeding it is a typed refusal rather than a silent truncation of the reach.
///
/// It is `receiver_release::FAMILY_CEILING`, deliberately: [`two_axis_width`] reads the reach as a
/// compatible family, so a reach this walk admits is always one that owner will read. A larger
/// ceiling here would build reaches whose width is then refused.
pub const DECLARED_REACH_CEILING: usize = 4096;

/// The longest word of moves one planned route may carry.
pub const DECLARED_ROUTE_LENGTH_CEILING: usize = 16;

/// The largest number of routes one plan may return.
pub const DECLARED_ROUTE_CEILING: usize = 1024;

/// The largest number of search nodes one route enumeration may visit.
///
/// Route enumeration is a depth-first walk whose branching is the number of admitted moves at an
/// address, so its size is exponential in the declared length bound. This ceiling is the bound on
/// the walk itself; exceeding it returns [`HorizonRefusal::SearchAboveWorkCeiling`] naming the
/// bound, and never a partial enumeration presented as complete.
pub const DECLARED_SEARCH_CEILING: usize = 1 << 18;

/// Why a two-axis horizon reading, a defect profile or a route plan was refused.
///
/// Every arm names what was declared and what bound it exceeded. Nothing here is a panic and
/// nothing is a silent truncation: a declaration above a ceiling is refused **before** the work it
/// would have sized.
///
/// This type is `Debug + PartialEq` and deliberately not `Clone`: its `Width` arm carries a
/// `receiver_release::WidthRefusal`, which is neither, because that owner compares refusals by
/// their rendered message rather than structurally.
#[derive(Debug, PartialEq)]
pub enum HorizonRefusal<S, I, F> {
    /// The tube itself refused: a missing section, a step that is not one, or a ceiling of the
    /// square or circuit check.
    Tube(Box<TubeRefusal<S, I, F>>),
    /// A caller-declared population exceeded its bound. `what` names which one.
    DeclarationAboveCeiling {
        /// Which declaration: `"chart aperture"`, `"station word"`, `"circuit"`, `"candidate"`,
        /// `"reach"`, `"route length"`, `"route count"`.
        what: &'static str,
        /// What was declared.
        declared: usize,
        /// The bound it exceeded.
        ceiling: usize,
    },
    /// The declared work — the product of the horizon's two coordinates with the chart, face and
    /// candidate populations — exceeded [`DECLARED_WORK_CEILING`]. Nothing was walked.
    WorkAboveCeiling {
        /// The product that was formed, or `usize::MAX` when it overflowed.
        declared: usize,
        /// The bound it exceeded.
        ceiling: usize,
    },
    /// A route enumeration visited more search nodes than [`DECLARED_SEARCH_CEILING`] admits. The
    /// enumeration is abandoned rather than returned partial.
    SearchAboveWorkCeiling {
        /// The bound.
        ceiling: usize,
    },
    /// The observer's chart is not one of the declared charts, so its distance to anything is not
    /// a reading this aperture supports.
    ObserverChartNotDeclared {
        /// The observer's chart.
        chart: I,
    },
    /// The declared longitudinal word does not begin at the observer's station.
    WordDoesNotBeginAtTheObserver {
        /// Where the word begins.
        declared: S,
        /// Where the observer stands.
        observer: S,
    },
    /// The declared width refused: two faces of different arms, a family above its own ceiling, or
    /// a norm that is not exact where it was asked.
    Width(WidthRefusal),
}

impl<S: Debug, I: Debug, F: Debug> fmt::Display for HorizonRefusal<S, I, F> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Tube(refusal) => write!(formatter, "the tube refused: {refusal}"),
            Self::DeclarationAboveCeiling {
                what,
                declared,
                ceiling,
            } => write!(
                formatter,
                "a declared {what} of {declared} exceeds the ceiling of {ceiling}; nothing was walked"
            ),
            Self::WorkAboveCeiling { declared, ceiling } => write!(
                formatter,
                "the declared horizon asks for {declared} face comparisons, above the ceiling of \
                 {ceiling}; nothing was walked"
            ),
            Self::SearchAboveWorkCeiling { ceiling } => write!(
                formatter,
                "the route enumeration exceeded {ceiling} search nodes and is refused rather than \
                 returned partial"
            ),
            Self::ObserverChartNotDeclared { chart } => write!(
                formatter,
                "the observer's chart {chart:?} is not among the declared charts"
            ),
            Self::WordDoesNotBeginAtTheObserver { declared, observer } => write!(
                formatter,
                "the declared word begins at {declared:?} and the observer stands at {observer:?}"
            ),
            Self::Width(refusal) => write!(formatter, "the receiver refused: {refusal}"),
        }
    }
}

impl<S: Debug, I: Debug, F: Debug> std::error::Error for HorizonRefusal<S, I, F> {}

impl<S, I, F> From<TubeRefusal<S, I, F>> for HorizonRefusal<S, I, F> {
    fn from(refusal: TubeRefusal<S, I, F>) -> Self {
        Self::Tube(Box::new(refusal))
    }
}

impl<S, I, F> From<WidthRefusal> for HorizonRefusal<S, I, F> {
    fn from(refusal: WidthRefusal) -> Self {
        Self::Width(refusal)
    }
}

/// A tube's own [`HorizonRefusal`], in its own station, index and face types.
pub type HorizonRefusalOf<T> = HorizonRefusal<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;
/// A horizon return `V`, or that tube's own typed [`HorizonRefusal`].
pub type HorizonOutcome<T, V> = Result<V, HorizonRefusalOf<T>>;
/// A tube's own [`Observer`], in its own station and index types.
pub type TubeObserver<T> = Observer<TubeStation<T>, TubeIndex<T>>;
/// A tube's own [`HorizonDeclaration`].
pub type TubeHorizonDeclaration<T> =
    HorizonDeclaration<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;
/// A tube's own [`HorizonReach`].
pub type TubeHorizonReach<T> = HorizonReach<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;
/// A tube's own [`DefectProfile`].
pub type TubeDefectProfile<T> = DefectProfile<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;
/// A tube's own [`RoutePlan`].
pub type TubeRoutePlan<T> = RoutePlan<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;

/// **The observer: a station and a chart of a tube.**
///
/// [definition] `receiver_release`'s width reads at a horizon of `h` steps of `Φ`, which fixes
/// *where along the tube* the reading happens and says nothing about *at which grain*. An observer
/// is both, and every two-axis reading below is relative to one.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::ObserverAt`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Observer<S, I> {
    station: S,
    chart: I,
}

impl<S, I> Observer<S, I> {
    /// The observer standing at one station, reading at one chart.
    pub const fn at(station: S, chart: I) -> Self {
        Self { station, chart }
    }

    /// Where along the tube it stands.
    pub const fn station(&self) -> &S {
        &self.station
    }

    /// Which chart of the transverse section it reads at.
    pub const fn chart(&self) -> &I {
        &self.chart
    }
}

/// Which way a chart lies from the observer's own.
///
/// [definition] **The two directions are not symmetric, and the asymmetry is the content.** A
/// tower's only transport is `restrict`, and it runs one way: toward the coarser chart the reading
/// is *determined* — one face, obtained by restricting — and toward the finer chart it is a
/// **fibre**, the plural population of everything that restricts to what the observer holds. Both
/// are distance into the horizon; they are far in dual ways.
///
/// Lean counterpart: `Foundation/ReceiverRelease.lean::looking_toward_the_coarse_is_determined_and_toward_the_fine_is_plural`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IndexDirection {
    /// The same chart, or one the order relates in both directions.
    Same,
    /// Coarser than the observer's: the observer's face restricts to it, single-valued.
    Coarser,
    /// Finer than the observer's: the observer's face is the restriction of a whole fibre.
    Finer,
    /// Comparable to the observer's chart only through a chain that both descends and rises.
    Across,
}

impl IndexDirection {
    /// A short name for a receipt.
    pub const fn name(self) -> &'static str {
        match self {
            Self::Same => "same",
            Self::Coarser => "coarser",
            Self::Finer => "finer",
            Self::Across => "across",
        }
    }
}

/// **The index distance between two charts, or the typed statement that there is no chain.**
///
/// [definition] The distance is the length of a **shortest chain of comparable charts** through
/// the declared aperture, where one step of a chain is one *cover* — a comparability with no
/// declared chart strictly between. It is relative to the declared aperture and says so: adding an
/// intermediate chart lengthens the chain through it, which is exactly what a finer ladder of
/// grains is.
///
/// [definition] Where no chain exists the return is [`Self::NoChain`] and **not** an infinite
/// distance. That is the wormhole case — `Migration.ConnectsIncomparableCharts`, which
/// [`wormhole_receipt`] already reads — and it is carried as a value.
///
/// Lean counterpart: `Foundation/ReceiverRelease.lean::ChainDistanceAtMost`, with
/// `chainDistance_symm` the symmetry of the notion and `chainDistance_orderDual` the statement
/// that it is the same distance in the order dual: distance toward the fine and distance toward
/// the coarse are one notion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndexReading<I> {
    /// A chain of this many cover steps joins the two charts, and the target lies in this
    /// direction from the source.
    Within {
        /// How many cover steps the shortest chain takes.
        steps: usize,
        /// Where the target lies relative to the source.
        direction: IndexDirection,
    },
    /// No chain of comparable charts joins them inside the declared aperture.
    NoChain {
        /// The chart the reading started from.
        from: I,
        /// The chart it could not reach.
        to: I,
        /// How many charts were declared.
        charts_declared: usize,
    },
}

impl<I> IndexReading<I> {
    /// The distance, when there is a chain.
    pub const fn steps(&self) -> Option<usize> {
        match self {
            Self::Within { steps, .. } => Some(*steps),
            Self::NoChain { .. } => None,
        }
    }

    /// The direction, when there is a chain.
    pub const fn direction(&self) -> Option<IndexDirection> {
        match self {
            Self::Within { direction, .. } => Some(*direction),
            Self::NoChain { .. } => None,
        }
    }

    /// Whether the two charts are joined by no chain at all — the wormhole case.
    pub const fn is_wormhole(&self) -> bool {
        matches!(self, Self::NoChain { .. })
    }
}

/// Whether `fine` strictly refines `coarse` in a section's own order.
fn strictly_refines<T: Tower>(section: &T, coarse: &T::Index, fine: &T::Index) -> bool {
    section.refines(coarse, fine) && !section.refines(fine, coarse)
}

/// Whether `fine` **covers** `coarse` among the declared charts: it strictly refines it and no
/// declared chart lies strictly between. One cover is one step of an index chain.
fn covers<T: Tower>(section: &T, charts: &[T::Index], coarse: &T::Index, fine: &T::Index) -> bool {
    if !strictly_refines(section, coarse, fine) {
        return false;
    }
    !charts.iter().any(|middle| {
        strictly_refines(section, coarse, middle) && strictly_refines(section, middle, fine)
    })
}

/// Whether two declared charts are one index step apart: either covers the other, or the order
/// relates them both ways while they are different charts.
fn index_adjacent<T: Tower>(
    section: &T,
    charts: &[T::Index],
    left: &T::Index,
    right: &T::Index,
) -> bool {
    if left == right {
        return false;
    }
    if covers(section, charts, left, right) || covers(section, charts, right, left) {
        return true;
    }
    section.refines(left, right) && section.refines(right, left)
}

/// The direction of `target` from `source` in a section's order.
fn index_direction<T: Tower>(section: &T, source: &T::Index, target: &T::Index) -> IndexDirection {
    let coarser = section.refines(target, source);
    let finer = section.refines(source, target);
    match (coarser, finer) {
        (true, true) => IndexDirection::Same,
        (true, false) => IndexDirection::Coarser,
        (false, true) => IndexDirection::Finer,
        (false, false) => IndexDirection::Across,
    }
}

/// **Bound the cover-graph walk before it runs.**
///
/// A breadth-first search over covers expands each declared chart at most once, scans every
/// declared chart at each expansion, and asks [`covers`] — which itself scans every declared chart
/// for one strictly between. The walk is therefore **cubic** in the declared aperture, and the
/// per-axis ceiling alone does not bound it: 1,024 charts would ask for 2^30 comparisons. The cube
/// is formed with checked arithmetic and compared against [`DECLARED_WORK_CEILING`] before the
/// first chart is visited.
fn bound_chart_walk<S, I, F>(charts: usize) -> Result<(), HorizonRefusal<S, I, F>> {
    if charts > DECLARED_CHART_CEILING {
        return Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "chart aperture",
            declared: charts,
            ceiling: DECLARED_CHART_CEILING,
        });
    }
    match declared_work(&[charts, charts, charts]) {
        Some(work) if work <= DECLARED_WORK_CEILING => Ok(()),
        Some(work) => Err(HorizonRefusal::WorkAboveCeiling {
            declared: work,
            ceiling: DECLARED_WORK_CEILING,
        }),
        None => Err(HorizonRefusal::WorkAboveCeiling {
            declared: usize::MAX,
            ceiling: DECLARED_WORK_CEILING,
        }),
    }
}

/// Every declared chart's index distance from one chart, by breadth-first search over covers.
fn chart_distances<T: Tower>(
    section: &T,
    charts: &[T::Index],
    from: &T::Index,
) -> std::collections::BTreeMap<T::Index, usize> {
    let mut distances = std::collections::BTreeMap::new();
    distances.insert(from.clone(), 0_usize);
    let mut frontier = vec![from.clone()];
    let mut steps = 0_usize;
    while !frontier.is_empty() && steps < charts.len() + 1 {
        steps += 1;
        let mut next = Vec::new();
        for chart in &frontier {
            for candidate in charts {
                if distances.contains_key(candidate) {
                    continue;
                }
                if index_adjacent(section, charts, chart, candidate) {
                    distances.insert(candidate.clone(), steps);
                    next.push(candidate.clone());
                }
            }
        }
        frontier = next;
    }
    distances
}

/// **The index distance from one chart to another, read at one station's transverse section.**
///
/// The declared chart aperture is the aperture of the reading: the chain runs through those charts
/// and no others, and a chart the aperture does not carry is not a shorter route that was missed.
pub fn index_distance<T: StationedTower>(
    tube: &T,
    station: &TubeStation<T>,
    charts: &[TubeIndex<T>],
    from: &TubeIndex<T>,
    to: &TubeIndex<T>,
) -> HorizonOutcome<T, IndexReading<TubeIndex<T>>> {
    bound_chart_walk(charts.len())?;
    let Some(section) = tube.section(station) else {
        return Err(TubeRefusal::StationMissing {
            station: station.clone(),
        }
        .into());
    };
    let distances = chart_distances(section, charts, from);
    match distances.get(to) {
        Some(steps) => Ok(IndexReading::Within {
            steps: *steps,
            direction: index_direction(section, from, to),
        }),
        None => Ok(IndexReading::NoChain {
            from: from.clone(),
            to: to.clone(),
            charts_declared: charts.len(),
        }),
    }
}

/// **A declared two-axis horizon around one observer, with every bound checked before any work.**
///
/// [implemented-exact] Every field is private and the only constructor is [`Self::declare`], which
/// checks the station word, the chart aperture, the declared faces and the product of all of them
/// against their ceilings. There is no `Default` and no `Deserialize`, so a declaration that this
/// module would have refused cannot be reconstructed and handed to a reading.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HorizonDeclaration<S, I, F> {
    observer: Observer<S, I>,
    horizon: Horizon,
    word: Vec<S>,
    charts: Vec<I>,
    faces: Vec<(I, F)>,
    circuits: Vec<Vec<S>>,
}

impl<S: Clone + Ord + Debug, I: Clone + Ord + Debug, F: Clone + Eq + Debug>
    HorizonDeclaration<S, I, F>
{
    /// Declare the horizon. `word` is the longitudinal word the observer's station begins, with
    /// one admitted step between consecutive stations; `charts` is the transverse aperture the
    /// index distance is read in; `faces` are the `(chart, face)` pairs the squares are checked on.
    ///
    /// The horizon's own two coordinates were already checked by [`Horizon::declare`]; this checks
    /// the three populations and the product `(h + 1) · charts² · faces`, which is the work a
    /// profile actually performs.
    pub fn declare(
        observer: Observer<S, I>,
        horizon: Horizon,
        word: Vec<S>,
        charts: Vec<I>,
        faces: Vec<(I, F)>,
    ) -> Result<Self, HorizonRefusal<S, I, F>> {
        if word.len() > DECLARED_CIRCUIT_CEILING {
            return Err(HorizonRefusal::DeclarationAboveCeiling {
                what: "station word",
                declared: word.len(),
                ceiling: DECLARED_CIRCUIT_CEILING,
            });
        }
        bound_chart_walk(charts.len())?;
        if faces.len() > DECLARED_FACE_CEILING {
            return Err(HorizonRefusal::DeclarationAboveCeiling {
                what: "face population",
                declared: faces.len(),
                ceiling: DECLARED_FACE_CEILING,
            });
        }
        if !charts.contains(observer.chart()) {
            return Err(HorizonRefusal::ObserverChartNotDeclared {
                chart: observer.chart().clone(),
            });
        }
        match word.first() {
            Some(first) if first == observer.station() => {}
            Some(first) => {
                return Err(HorizonRefusal::WordDoesNotBeginAtTheObserver {
                    declared: first.clone(),
                    observer: observer.station().clone(),
                });
            }
            None => {
                return Err(HorizonRefusal::WordDoesNotBeginAtTheObserver {
                    declared: observer.station().clone(),
                    observer: observer.station().clone(),
                });
            }
        }
        let steps = horizon.longitudinal().min(word.len().saturating_sub(1)) + 1;
        let work = declared_work(&[
            steps,
            charts.len(),
            charts.len(),
            faces.len().max(1),
            horizon.index() + 1,
        ]);
        match work {
            Some(work) if work <= DECLARED_WORK_CEILING => {}
            Some(work) => {
                return Err(HorizonRefusal::WorkAboveCeiling {
                    declared: work,
                    ceiling: DECLARED_WORK_CEILING,
                });
            }
            None => {
                return Err(HorizonRefusal::WorkAboveCeiling {
                    declared: usize::MAX,
                    ceiling: DECLARED_WORK_CEILING,
                });
            }
        }
        Ok(Self {
            observer,
            horizon,
            word,
            charts,
            faces,
            circuits: Vec::new(),
        })
    }

    /// Add the declared circuits whose holonomy the profile reads. A circuit whose stations are
    /// not all inside the longitudinal horizon is not read, and the profile says how many were.
    pub fn with_circuits(
        mut self,
        circuits: Vec<Vec<S>>,
    ) -> Result<Self, HorizonRefusal<S, I, F>> {
        for circuit in &circuits {
            if circuit.len() > DECLARED_CIRCUIT_CEILING {
                return Err(HorizonRefusal::DeclarationAboveCeiling {
                    what: "circuit",
                    declared: circuit.len(),
                    ceiling: DECLARED_CIRCUIT_CEILING,
                });
            }
        }
        if circuits.len() > DECLARED_CIRCUIT_CEILING {
            return Err(HorizonRefusal::DeclarationAboveCeiling {
                what: "circuit count",
                declared: circuits.len(),
                ceiling: DECLARED_CIRCUIT_CEILING,
            });
        }
        // Each circuit is walked at every visible chart on every declared face, and each of those
        // walks is itself inside `check_circuit_holonomy`'s own ceiling. What the per-call ceiling
        // does not bound is the **number** of calls, so the product is formed here — with checked
        // arithmetic — before the first circuit is walked.
        let longest = circuits.iter().map(Vec::len).max().unwrap_or(0);
        match declared_work(&[
            circuits.len(),
            longest,
            self.charts.len(),
            self.faces.len().max(1),
        ]) {
            Some(work) if work <= DECLARED_WORK_CEILING => {}
            Some(work) => {
                return Err(HorizonRefusal::WorkAboveCeiling {
                    declared: work,
                    ceiling: DECLARED_WORK_CEILING,
                });
            }
            None => {
                return Err(HorizonRefusal::WorkAboveCeiling {
                    declared: usize::MAX,
                    ceiling: DECLARED_WORK_CEILING,
                });
            }
        }
        self.circuits = circuits;
        Ok(self)
    }

    /// The observer this horizon is declared around.
    pub const fn observer(&self) -> &Observer<S, I> {
        &self.observer
    }

    /// The two coordinates.
    pub const fn horizon(&self) -> Horizon {
        self.horizon
    }

    /// The declared longitudinal word.
    pub fn word(&self) -> &[S] {
        &self.word
    }

    /// The declared chart aperture.
    pub fn charts(&self) -> &[I] {
        &self.charts
    }

    /// The declared `(chart, face)` pairs.
    pub fn faces(&self) -> &[(I, F)] {
        &self.faces
    }

    /// The declared circuits.
    pub fn circuits(&self) -> &[Vec<S>] {
        &self.circuits
    }

    /// The stations inside the longitudinal horizon: the first `h + 1` of the declared word.
    pub fn stations_in_horizon(&self) -> &[S] {
        let last = (self.horizon.longitudinal() + 1).min(self.word.len());
        &self.word[..last]
    }
}

/// Whether one entry of a reach is a single determined face or one member of a fibre.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Plurality {
    /// The route to it restricts and transports only: the face is determined.
    Determined,
    /// The route to it opened a fibre: this is one member of the plural population that restricts
    /// to what the observer holds, and the others are carried beside it.
    FibreMember,
}

/// One face the observer's two-axis horizon reaches, with the route's two coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReachEntry<S, I, F> {
    station: S,
    chart: I,
    longitudinal: usize,
    index_steps: usize,
    direction: IndexDirection,
    plurality: Plurality,
    face: F,
}

impl<S, I, F> ReachEntry<S, I, F> {
    /// Where along the tube this face sits.
    pub const fn station(&self) -> &S {
        &self.station
    }

    /// Which chart it is presented at.
    pub const fn chart(&self) -> &I {
        &self.chart
    }

    /// How many longitudinal steps from the observer's station.
    pub const fn longitudinal(&self) -> usize {
        self.longitudinal
    }

    /// How many index steps the route to it took.
    pub const fn index_steps(&self) -> usize {
        self.index_steps
    }

    /// Which way its chart lies from the observer's.
    pub const fn direction(&self) -> IndexDirection {
        self.direction
    }

    /// Whether the route to it was determined or opened a fibre.
    pub const fn plurality(&self) -> Plurality {
        self.plurality
    }

    /// The face itself.
    pub const fn face(&self) -> &F {
        &self.face
    }
}

/// **Everything an observer's two-axis horizon reaches**, with the charts it reaches nothing in.
///
/// [implemented-exact] Every field is private and the only constructor is [`horizon_reach`], so a
/// value of this type is a receipt that the walk it names actually ran.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HorizonReach<S, I, F> {
    observer: Observer<S, I>,
    horizon: Horizon,
    entries: Vec<ReachEntry<S, I, F>>,
    unreachable: Vec<I>,
    stations_walked: usize,
    candidates_declared: usize,
}

impl<S, I, F> HorizonReach<S, I, F> {
    /// The observer it was walked from.
    pub const fn observer(&self) -> &Observer<S, I> {
        &self.observer
    }

    /// The two coordinates it was walked to.
    pub const fn horizon(&self) -> Horizon {
        self.horizon
    }

    /// Every face reached, with its route's coordinates.
    pub fn entries(&self) -> &[ReachEntry<S, I, F>] {
        &self.entries
    }

    /// The declared charts no chain of comparable charts joins to the observer's: passage to them
    /// is a [`Wormhole`](WormholeReceipt), not a longer walk.
    pub fn unreachable_charts(&self) -> &[I] {
        &self.unreachable
    }

    /// How many stations of the declared word the walk carried the face along.
    pub const fn stations_walked(&self) -> usize {
        self.stations_walked
    }

    /// How many fibre candidates were declared to it.
    pub const fn candidates_declared(&self) -> usize {
        self.candidates_declared
    }

    /// How many entries lie toward the coarser charts.
    pub fn toward_the_coarse(&self) -> usize {
        self.entries
            .iter()
            .filter(|entry| entry.direction == IndexDirection::Coarser)
            .count()
    }

    /// How many entries lie toward the finer charts.
    pub fn toward_the_fine(&self) -> usize {
        self.entries
            .iter()
            .filter(|entry| entry.direction == IndexDirection::Finer)
            .count()
    }

    /// How many entries are one member of an opened fibre rather than a determined face.
    pub fn fibre_members(&self) -> usize {
        self.entries
            .iter()
            .filter(|entry| entry.plurality == Plurality::FibreMember)
            .count()
    }
}

/// **The two-axis reach of an observer: everything inside `(h, k)` of `(s, i)`.**
///
/// [definition] The walk is the composition of the two axes and nothing else:
///
/// * **longitudinally**, the observer's face is carried one declared step at a time along the
///   declared word, `h` steps at most;
/// * **transversely**, from every face so reached, `k` cover steps of the section's index — one
///   step toward a coarser chart **restricts** (the face is determined), and one step toward a
///   finer chart **opens the fibre**: every declared candidate at that chart whose restriction is
///   the face the observer holds. That asymmetry is not an implementation choice; a tower's only
///   transport is `restrict`, and it runs one way.
///
/// Charts the declared aperture joins by no chain are not at an infinite distance: they are
/// returned in [`HorizonReach::unreachable_charts`], and passage to them is what
/// [`wormhole_receipt`] reads.
pub fn horizon_reach<T: StationedTower>(
    tube: &T,
    declaration: &TubeHorizonDeclaration<T>,
    source_face: &TubeFace<T>,
    candidates: &[(TubeIndex<T>, TubeFace<T>)],
) -> HorizonOutcome<T, TubeHorizonReach<T>> {
    if candidates.len() > DECLARED_CANDIDATE_CEILING {
        return Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "candidate population",
            declared: candidates.len(),
            ceiling: DECLARED_CANDIDATE_CEILING,
        });
    }
    // The population inside the declared candidate containers is what a fibre opening actually
    // moves, and it is bounded before the first restriction runs.
    total_face_population(tube, candidates)?;
    let observer = declaration.observer();
    let stations = declaration.stations_in_horizon();
    let charts = declaration.charts();
    let horizon = declaration.horizon();
    let Some(section) = tube.section(observer.station()) else {
        return Err(TubeRefusal::StationMissing {
            station: observer.station().clone(),
        }
        .into());
    };
    let distances = chart_distances(section, charts, observer.chart());
    let unreachable: Vec<TubeIndex<T>> = charts
        .iter()
        .filter(|chart| !distances.contains_key(*chart))
        .cloned()
        .collect();

    let mut entries: Vec<ReachEntry<TubeStation<T>, TubeIndex<T>, TubeFace<T>>> = Vec::new();
    // The declaration's product bounds what may be **asked**; it cannot see how far a fibre
    // multiplies, because that depends on the candidates' own restrictions. The comparisons the
    // walk actually performs are therefore counted as it runs, and the walk is abandoned by name
    // rather than truncated when they exceed the same ceiling.
    let mut compared = 0_usize;
    let mut carried = source_face.clone();
    for (longitudinal, station) in stations.iter().enumerate() {
        if longitudinal > 0 {
            let earlier = &stations[longitudinal - 1];
            if !tube.follows(earlier, station) {
                return Err(TubeRefusal::NotAStep {
                    earlier: earlier.clone(),
                    later: station.clone(),
                }
                .into());
            }
            carried = tube.transport(earlier, station, observer.chart(), &carried)?;
        }
        let Some(section) = tube.section(station) else {
            return Err(TubeRefusal::StationMissing {
                station: station.clone(),
            }
            .into());
        };
        // The transverse closure at this station: `k` cover steps out from the observer's chart,
        // restricting toward the coarse and opening the fibre toward the fine.
        let mut frontier: Vec<(TubeIndex<T>, TubeFace<T>, Plurality)> = vec![(
            observer.chart().clone(),
            carried.clone(),
            Plurality::Determined,
        )];
        push_reach_entry(
            &mut entries,
            ReachEntry {
                station: station.clone(),
                chart: observer.chart().clone(),
                longitudinal,
                index_steps: 0,
                direction: IndexDirection::Same,
                plurality: Plurality::Determined,
                face: carried.clone(),
            },
        )?;
        for index_steps in 1..=horizon.index() {
            let mut next: Vec<(TubeIndex<T>, TubeFace<T>, Plurality)> = Vec::new();
            for (chart, face, plurality) in &frontier {
                for target in charts {
                    compared = compared.saturating_add(charts.len());
                    if compared > DECLARED_WORK_CEILING {
                        return Err(HorizonRefusal::WorkAboveCeiling {
                            declared: compared,
                            ceiling: DECLARED_WORK_CEILING,
                        });
                    }
                    if !index_adjacent(section, charts, chart, target) {
                        continue;
                    }
                    if section.refines(target, chart) {
                        // One step toward the coarser chart: the face is determined.
                        let restricted = section
                            .restrict(target, chart, face)
                            .map_err(TubeRefusal::Section)?;
                        remember(&mut next, target, &restricted, *plurality);
                    } else if section.refines(chart, target) {
                        // One step toward the finer chart: the fibre, plural by construction.
                        for (candidate_chart, candidate) in candidates {
                            if candidate_chart != target {
                                continue;
                            }
                            let restricted = section
                                .restrict(chart, target, candidate)
                                .map_err(TubeRefusal::Section)?;
                            if &restricted == face {
                                remember(&mut next, target, candidate, Plurality::FibreMember);
                            }
                        }
                    }
                }
            }
            for (chart, face, plurality) in &next {
                push_reach_entry(
                    &mut entries,
                    ReachEntry {
                        station: station.clone(),
                        chart: chart.clone(),
                        longitudinal,
                        index_steps,
                        direction: index_direction(section, observer.chart(), chart),
                        plurality: *plurality,
                        face: face.clone(),
                    },
                )?;
            }
            frontier = next;
            if frontier.is_empty() {
                break;
            }
        }
    }

    Ok(HorizonReach {
        observer: observer.clone(),
        horizon,
        entries,
        unreachable,
        stations_walked: stations.len(),
        candidates_declared: candidates.len(),
    })
}

/// Remember one `(chart, face)` of a transverse frontier, keeping a fibre member's plurality once
/// it has been opened.
fn remember<I: Clone + Eq, F: Clone + Eq>(
    frontier: &mut Vec<(I, F, Plurality)>,
    chart: &I,
    face: &F,
    plurality: Plurality,
) {
    if let Some(existing) = frontier
        .iter_mut()
        .find(|(existing_chart, existing_face, _)| existing_chart == chart && existing_face == face)
    {
        if plurality == Plurality::FibreMember {
            existing.2 = Plurality::FibreMember;
        }
        return;
    }
    frontier.push((chart.clone(), face.clone(), plurality));
}

/// Push one entry of a reach, refusing before the reach exceeds its declared ceiling.
fn push_reach_entry<S: Clone + Ord + Debug, I: Clone + Ord + Debug, F: Clone + Eq + Debug>(
    entries: &mut Vec<ReachEntry<S, I, F>>,
    entry: ReachEntry<S, I, F>,
) -> Result<(), HorizonRefusal<S, I, F>> {
    if entries.iter().any(|existing| {
        existing.station == entry.station
            && existing.chart == entry.chart
            && existing.face == entry.face
    }) {
        return Ok(());
    }
    if entries.len() >= DECLARED_REACH_CEILING {
        return Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "reach",
            declared: entries.len() + 1,
            ceiling: DECLARED_REACH_CEILING,
        });
    }
    entries.push(entry);
    Ok(())
}

/// A declared exact reading of a tube's faces: the receiver of the two-axis horizon.
///
/// [definition] `receiver_release::Reading` reads a `Vec<Rat>` compatible state; a tube's faces are
/// whatever its transverse section presents, so the receiver of a tube is this trait. Its return is
/// the same [`ExactFace`], so the diameter law is `receiver_release`'s own and is not written a
/// second time.
pub trait FaceReading<T: StationedTower> {
    /// The receiver's declared name. It appears in every width and every profile.
    fn name(&self) -> &str;

    /// The exact face this receiver reads off one of the tube's faces.
    fn read(
        &self,
        station: &TubeStation<T>,
        chart: &TubeIndex<T>,
        face: &TubeFace<T>,
    ) -> Result<ExactFace, WidthRefusal>;
}

/// **The width of a receiver's reading over a two-axis horizon: `w_R(s, i; h, k)`.**
///
/// [definition] The diameter of the receiver's reading over everything the horizon reaches. At
/// `k = 0` the reach is the observer's own chart carried `h` steps, so this **is**
/// `receiver_release`'s `w_R(h)` — the existing theorems are its `k = 0` case and are not restated
/// here (`Foundation/ReceiverRelease.lean::twoAxisWidth_at_index_zero_is_the_longitudinal_width`).
///
/// Monotone in each coordinate, because a wider horizon reaches a superset and
/// `Foundation/ReceiverRelease.lean::width_mono` is monotone under fibre inclusion; the executable
/// statement is `the_two_axis_width_is_monotone_in_each_coordinate`.
pub fn two_axis_width<T: StationedTower>(
    reading: &dyn FaceReading<T>,
    reach: &TubeHorizonReach<T>,
    norm: DiameterNorm,
) -> Result<ReceiverWidth, WidthRefusal> {
    let faces = reach
        .entries()
        .iter()
        .map(|entry| reading.read(entry.station(), entry.chart(), entry.face()))
        .collect::<Result<Vec<_>, _>>()?;
    let lineage = format!(
        "two-axis horizon (h = {}, k = {}) at station {:?} chart {:?}",
        reach.horizon().longitudinal(),
        reach.horizon().index(),
        reach.observer().station(),
        reach.observer().chart(),
    );
    width_over_readings(reading.name(), &lineage, &faces, norm)
}

/// One non-commuting square inside an observer's horizon, read by a declared receiver.
///
/// [definition] The structural content is the [`SquareDefect`] the tube owner already returns: the
/// two routes' faces, both retained. The receiver's content is the exact separation of those two
/// faces under its reading, and the [`Rung`] on which the two routes stand — which is
/// `relation_ladder`'s scale and not a second one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SquareReading<S, I, F> {
    defect: SquareDefect<S, I, F>,
    discrepancy: Rat,
    rung: Rung,
}

impl<S, I, F> SquareReading<S, I, F> {
    /// The structural defect: both routes' faces, retained whole.
    pub const fn defect(&self) -> &SquareDefect<S, I, F> {
        &self.defect
    }

    /// The exact separation of the two routes under the declared receiver. Zero exactly when the
    /// receiver does not see the defect at all.
    pub const fn discrepancy(&self) -> &Rat {
        &self.discrepancy
    }

    /// **Where the two routes stand on `relation_ladder`'s scale.**
    ///
    /// `Identity` is impossible here — a defect is a pair of faces that differ — so the rungs this
    /// can carry are `ReceiverEqual` when the declared receiver reads them the same,
    /// `WithinTolerance` when it separates them inside the declared tolerance, and `NoRelation`
    /// when it separates them beyond it. No rung below identity is promoted to identity.
    pub const fn rung(&self) -> Rung {
        self.rung
    }
}

/// **The defect profile of an observer: curvature as a function of distance.**
///
/// [definition] Over every square and every declared circuit inside `(h, k)` of the observer, the
/// profile carries the count of non-commuting squares, the defect witnesses whole, the circuit
/// holonomies, and — for the declared receiver — how many of those defects that receiver actually
/// separates and the exact maximal discrepancy between the two routes. Nothing here is a float.
///
/// [definition] It is a **reading**, not the identity of the region:
/// [`Self::seen_by_the_receiver`] is at most [`Self::non_commuting`], with equality exactly when
/// the receiver separates every defect, and a poorer receiver reads flat what a richer one reads
/// as curved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DefectProfile<S, I, F> {
    observer: Observer<S, I>,
    horizon: Horizon,
    receiver: String,
    tolerance: Rat,
    squares_checked: usize,
    squares_with_no_declared_face: usize,
    non_commuting: usize,
    witnesses: Vec<SquareReading<S, I, F>>,
    circuits_checked: usize,
    holonomies: Vec<CircuitDefect<S, I, F>>,
    seen_by_the_receiver: usize,
    maximal_discrepancy: Rat,
    charts_visible: Vec<I>,
    unreachable_charts: Vec<I>,
}

impl<S, I, F> DefectProfile<S, I, F> {
    /// The observer whose profile this is.
    pub const fn observer(&self) -> &Observer<S, I> {
        &self.observer
    }

    /// The horizon it was read at.
    pub const fn horizon(&self) -> Horizon {
        self.horizon
    }

    /// The declared receiver.
    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    /// The declared tolerance the rung of each defect was classified against.
    pub const fn tolerance(&self) -> &Rat {
        &self.tolerance
    }

    /// How many squares were **compared on at least one declared face** inside the horizon. A
    /// square asked with no face at its finer chart is not counted here; it is counted by
    /// [`Self::squares_with_no_declared_face`], so a profile can never report flatness it did not
    /// read.
    pub const fn squares_checked(&self) -> usize {
        self.squares_checked
    }

    /// How many comparable chart pairs inside the horizon carried **no declared face** at their
    /// finer chart, so nothing was compared there. This is the exact scope of the flatness claim:
    /// these squares were not read, and a nonzero count is not evidence of anything.
    pub const fn squares_with_no_declared_face(&self) -> usize {
        self.squares_with_no_declared_face
    }

    /// How many of them did not commute.
    pub const fn non_commuting(&self) -> usize {
        self.non_commuting
    }

    /// The defect witnesses, each carrying both routes' faces.
    pub fn witnesses(&self) -> &[SquareReading<S, I, F>] {
        &self.witnesses
    }

    /// How many declared circuits lay inside the horizon and were walked.
    pub const fn circuits_checked(&self) -> usize {
        self.circuits_checked
    }

    /// The circuit holonomies found.
    pub fn holonomies(&self) -> &[CircuitDefect<S, I, F>] {
        &self.holonomies
    }

    /// How many of the non-commuting squares the declared receiver actually separates.
    pub const fn seen_by_the_receiver(&self) -> usize {
        self.seen_by_the_receiver
    }

    /// The exact maximal separation between two routes of one square, under the declared receiver.
    pub const fn maximal_discrepancy(&self) -> &Rat {
        &self.maximal_discrepancy
    }

    /// The charts inside the index horizon.
    pub fn charts_visible(&self) -> &[I] {
        &self.charts_visible
    }

    /// The declared charts no chain joins to the observer's — the wormhole charts.
    pub fn unreachable_charts(&self) -> &[I] {
        &self.unreachable_charts
    }

    /// **Flat**: every square inside the horizon commutes and every declared circuit inside it
    /// returns the identity. This is the structural reading, at the identity receiver.
    pub fn is_flat(&self) -> bool {
        self.non_commuting == 0 && self.holonomies.is_empty()
    }

    /// **Flat at the declared receiver**: that receiver separates no square's two routes. A
    /// profile can be curved and read flat; it is never flat and read curved.
    pub fn reads_flat_at_the_receiver(&self) -> bool {
        self.seen_by_the_receiver == 0
    }
}

/// **Read an observer's defect profile over its declared horizon.**
///
/// Every square is asked through [`check_commuting_square`] and every circuit through
/// [`check_circuit_holonomy`] — the tube owner's own checks, with their own ceilings — one square
/// at a time, so the count and the witnesses are of squares and not of the first failure.
pub fn defect_profile<T: StationedTower>(
    tube: &T,
    declaration: &TubeHorizonDeclaration<T>,
    reading: &dyn FaceReading<T>,
    tolerance: &Rat,
    norm: DiameterNorm,
) -> HorizonOutcome<T, TubeDefectProfile<T>> {
    let observer = declaration.observer();
    let charts = declaration.charts();
    let stations = declaration.stations_in_horizon();
    let horizon = declaration.horizon();
    let Some(section) = tube.section(observer.station()) else {
        return Err(TubeRefusal::StationMissing {
            station: observer.station().clone(),
        }
        .into());
    };
    let distances = chart_distances(section, charts, observer.chart());
    let visible: Vec<TubeIndex<T>> = charts
        .iter()
        .filter(|chart| {
            distances
                .get(*chart)
                .is_some_and(|steps| *steps <= horizon.index())
        })
        .cloned()
        .collect();
    let unreachable: Vec<TubeIndex<T>> = charts
        .iter()
        .filter(|chart| !distances.contains_key(*chart))
        .cloned()
        .collect();

    let mut squares_checked = 0_usize;
    let mut squares_with_no_declared_face = 0_usize;
    let mut non_commuting = 0_usize;
    let mut witnesses = Vec::new();
    let mut seen_by_the_receiver = 0_usize;
    let mut maximal_discrepancy = Rat::zero();
    for step in stations.windows(2) {
        let [earlier, later] = step else { continue };
        for coarse in &visible {
            for fine in &visible {
                if !strictly_refines(section, coarse, fine) {
                    continue;
                }
                let verdict = check_commuting_square(
                    tube,
                    earlier,
                    later,
                    &[coarse.clone(), fine.clone()],
                    &declaration
                        .faces()
                        .iter()
                        .filter(|(chart, _)| chart == fine)
                        .cloned()
                        .collect::<Vec<_>>(),
                )?;
                let defect = match verdict {
                    // A square asked with no face at its finer chart compared nothing. It is
                    // recorded as unread rather than counted as commuting.
                    SquareVerdict::Commutes(receipt) => {
                        if receipt.squares().is_empty() {
                            squares_with_no_declared_face += 1;
                        } else {
                            squares_checked += 1;
                        }
                        continue;
                    }
                    SquareVerdict::Defect(defect) => {
                        squares_checked += 1;
                        defect
                    }
                };
                non_commuting += 1;
                let left = reading.read(later, coarse, defect.transported_then_restricted())?;
                let right = reading.read(later, coarse, defect.restricted_then_transported())?;
                let discrepancy = left.separation(&right, norm)?;
                let rung = if discrepancy.is_zero() {
                    Rung::ReceiverEqual
                } else if &discrepancy <= tolerance {
                    Rung::WithinTolerance
                } else {
                    Rung::NoRelation
                };
                if !discrepancy.is_zero() {
                    seen_by_the_receiver += 1;
                }
                if discrepancy > maximal_discrepancy {
                    maximal_discrepancy = discrepancy.clone();
                }
                witnesses.push(SquareReading {
                    defect,
                    discrepancy,
                    rung,
                });
            }
        }
    }

    let mut circuits_checked = 0_usize;
    let mut holonomies = Vec::new();
    for circuit in declaration.circuits() {
        if !circuit.iter().all(|station| stations.contains(station)) {
            continue;
        }
        circuits_checked += 1;
        let visible_faces: Vec<_> = declaration
            .faces()
            .iter()
            .filter(|(chart, _)| visible.contains(chart))
            .cloned()
            .collect();
        let verdict = check_circuit_holonomy(tube, circuit, &visible, &visible_faces)?;
        if let HolonomyVerdict::Defect(defect) = verdict {
            holonomies.push(defect);
        }
    }

    Ok(DefectProfile {
        observer: observer.clone(),
        horizon,
        receiver: reading.name().to_owned(),
        tolerance: tolerance.clone(),
        squares_checked,
        squares_with_no_declared_face,
        non_commuting,
        witnesses,
        circuits_checked,
        holonomies,
        seen_by_the_receiver,
        maximal_discrepancy,
        charts_visible: visible,
        unreachable_charts: unreachable,
    })
}

// ---------------------------------------------------------------------------------------------
// T5 (c) — passages across ranks, and planning a route through them
// ---------------------------------------------------------------------------------------------

/// **What kind of passage joins two charts across ranks.**
///
/// [definition] Three kinds, and the classification is exact.
///
/// * [`Self::TubesOwn`] — a chain of restrictions alone. It is a composite of the tube's own
///   passages, so it is never a wormhole (`Tube.refinementRoute_is_not_a_wormhole`), and an
///   observer whose index horizon contains the chain sees it.
/// * [`Self::NeedsRetainedResidual`] — the chain exists but must rise at least once. A rise is a
///   reopening, and it returns the fine face exactly when the residual was retained:
///   `Foundation/ContinuingTower.lean::ResidualMigration.traversability_is_the_residual`, cited and
///   not reproved.
/// * [`Self::Wormhole`] — no chain of comparable charts at all, which is
///   `Migration.ConnectsIncomparableCharts` and is what [`wormhole_receipt`] reads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CrossRankPassage<I> {
    /// A descending chain: restrictions only.
    TubesOwn {
        /// The charts the chain passes through, from the source to the target.
        chain: Vec<I>,
    },
    /// A chain that rises: each rise needs the residual of the restriction it undoes.
    NeedsRetainedResidual {
        /// The charts the chain passes through, from the source to the target.
        chain: Vec<I>,
        /// How many steps of it rise toward a finer chart.
        reopenings: usize,
    },
    /// No chain at all.
    Wormhole {
        /// Where the passage starts.
        from: I,
        /// Where it would arrive.
        to: I,
        /// How many charts were declared.
        charts_declared: usize,
    },
}

impl<I> CrossRankPassage<I> {
    /// The chain, when there is one.
    pub fn chain(&self) -> Option<&[I]> {
        match self {
            Self::TubesOwn { chain } | Self::NeedsRetainedResidual { chain, .. } => Some(chain),
            Self::Wormhole { .. } => None,
        }
    }

    /// How many reopenings the passage needs. A wormhole needs none because it has no chain.
    pub const fn reopenings(&self) -> usize {
        match self {
            Self::TubesOwn { .. } | Self::Wormhole { .. } => 0,
            Self::NeedsRetainedResidual { reopenings, .. } => *reopenings,
        }
    }
}

/// One breadth-first search over the cover graph, returning a shortest chain when there is one.
fn shortest_chain<T: Tower>(
    section: &T,
    charts: &[T::Index],
    from: &T::Index,
    to: &T::Index,
    descending_only: bool,
) -> Option<Vec<T::Index>> {
    let mut parents: std::collections::BTreeMap<T::Index, T::Index> =
        std::collections::BTreeMap::new();
    let mut seen: std::collections::BTreeSet<T::Index> = std::collections::BTreeSet::new();
    seen.insert(from.clone());
    let mut frontier = vec![from.clone()];
    let mut rounds = 0_usize;
    while !frontier.is_empty() && rounds <= charts.len() {
        rounds += 1;
        let mut next = Vec::new();
        for chart in &frontier {
            for candidate in charts {
                if seen.contains(candidate) {
                    continue;
                }
                if !index_adjacent(section, charts, chart, candidate) {
                    continue;
                }
                if descending_only && !section.refines(candidate, chart) {
                    continue;
                }
                seen.insert(candidate.clone());
                parents.insert(candidate.clone(), chart.clone());
                if candidate == to {
                    let mut chain = vec![to.clone()];
                    let mut cursor = to.clone();
                    while let Some(parent) = parents.get(&cursor) {
                        chain.push(parent.clone());
                        cursor = parent.clone();
                    }
                    chain.reverse();
                    return Some(chain);
                }
                next.push(candidate.clone());
            }
        }
        frontier = next;
    }
    if from == to { Some(vec![from.clone()]) } else { None }
}

/// **Classify the passage from one chart to another across the ranks of one station's section.**
///
/// The descending-only search decides [`CrossRankPassage::TubesOwn`] exactly: when the target is
/// reachable by restrictions alone the passage is a composite of the tube's own, and when it is
/// not, every chain to it rises at least once and the residual is what makes it traversable.
pub fn classify_cross_rank<T: StationedTower>(
    tube: &T,
    station: &TubeStation<T>,
    charts: &[TubeIndex<T>],
    from: &TubeIndex<T>,
    to: &TubeIndex<T>,
) -> HorizonOutcome<T, CrossRankPassage<TubeIndex<T>>> {
    bound_chart_walk(charts.len())?;
    let Some(section) = tube.section(station) else {
        return Err(TubeRefusal::StationMissing {
            station: station.clone(),
        }
        .into());
    };
    if let Some(chain) = shortest_chain(section, charts, from, to, true) {
        return Ok(CrossRankPassage::TubesOwn { chain });
    }
    match shortest_chain(section, charts, from, to, false) {
        Some(chain) => {
            let reopenings = chain
                .windows(2)
                .filter(|step| {
                    let [earlier, later] = step else { return false };
                    strictly_refines(section, earlier, later)
                })
                .count();
            Ok(CrossRankPassage::NeedsRetainedResidual { chain, reopenings })
        }
        None => Ok(CrossRankPassage::Wormhole {
            from: from.clone(),
            to: to.clone(),
            charts_declared: charts.len(),
        }),
    }
}

/// One move of a route: a word in the tube's own passages and the reopenings a retained residual
/// buys.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RouteMove<S, I> {
    /// One admitted longitudinal step, at one chart.
    Transport {
        /// The station left.
        earlier: S,
        /// The station arrived at.
        later: S,
        /// The chart the face is carried at.
        chart: I,
    },
    /// One cover step toward a coarser chart: the tower's own `restrict`.
    Restrict {
        /// Where it happens.
        station: S,
        /// The chart restricted from.
        fine: I,
        /// The chart restricted to.
        coarse: I,
    },
    /// One cover step toward a finer chart: a reopening, which needs the residual of the
    /// restriction it undoes and is plural without it.
    Reopen {
        /// Where it happens.
        station: S,
        /// The chart reopened from.
        coarse: I,
        /// The chart reopened into.
        fine: I,
    },
}

/// One square a route crossed, and whether it commuted on the face the route carried.
/// **Forging one is a compile error.** `commutes` is a claim about a check that ran, so every field
/// is private and the only constructor is the route walk of [`plan_routes`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrossedSquare<S, I> {
    earlier: S,
    later: S,
    coarse: I,
    fine: I,
    commutes: bool,
}

impl<S, I> CrossedSquare<S, I> {
    /// The station the step left.
    pub const fn earlier(&self) -> &S {
        &self.earlier
    }

    /// The station it arrived at.
    pub const fn later(&self) -> &S {
        &self.later
    }

    /// The coarser chart of the square.
    pub const fn coarse(&self) -> &I {
        &self.coarse
    }

    /// The finer chart.
    pub const fn fine(&self) -> &I {
        &self.fine
    }

    /// Whether the square commuted on the face this route carried.
    pub const fn commutes(&self) -> bool {
        self.commutes
    }
}

/// **One planned route, with the exact receipt of what it costs.**
///
/// [definition] The receipt is what the route loses and what it crosses: every reopening needs the
/// residual of a restriction, and a route that crosses a non-commuting square delivers a face a
/// route that does not cross it does not. The delivered faces are carried whole; the plan never
/// picks between two routes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Route<S, I, F> {
    moves: Vec<RouteMove<S, I>>,
    delivered: F,
    residuals_retained: Vec<(S, I, I)>,
    crossed: Vec<CrossedSquare<S, I>>,
}

impl<S, I, F> Route<S, I, F> {
    /// The word of moves, in order.
    pub fn moves(&self) -> &[RouteMove<S, I>] {
        &self.moves
    }

    /// The face this route delivers at the target address.
    pub const fn delivered(&self) -> &F {
        &self.delivered
    }

    /// Every restriction whose residual this route must have retained to be traversable, as
    /// `(station, coarse, fine)`. An empty list is a route of the tube's own passages alone.
    pub fn residuals_retained(&self) -> &[(S, I, I)] {
        &self.residuals_retained
    }

    /// Every square this route crossed, with whether it commuted on the carried face.
    pub fn crossed_squares(&self) -> &[CrossedSquare<S, I>] {
        &self.crossed
    }

    /// Whether this route crossed a square that did not commute.
    pub fn crosses_a_non_commuting_square(&self) -> bool {
        self.crossed.iter().any(|square| !square.commutes())
    }
}

/// The declared bound a route enumeration runs under. Both coordinates are checked before the
/// first move is taken.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RouteBound {
    moves: usize,
    routes: usize,
}

impl RouteBound {
    /// Declare the bound, checking both coordinates against their ceilings.
    pub fn declare(moves: usize, routes: usize) -> Result<Self, (usize, usize)> {
        if moves > DECLARED_ROUTE_LENGTH_CEILING {
            return Err((moves, DECLARED_ROUTE_LENGTH_CEILING));
        }
        if routes > DECLARED_ROUTE_CEILING {
            return Err((routes, DECLARED_ROUTE_CEILING));
        }
        Ok(Self { moves, routes })
    }

    /// The longest word of moves a route may carry.
    pub const fn moves(&self) -> usize {
        self.moves
    }

    /// The most routes the plan may return.
    pub const fn routes(&self) -> usize {
        self.routes
    }
}

/// **Every route to an address inside a declared bound, with each route's receipt.**
///
/// [project-postulate] AGENTS.md: *"a scalar priority queue or scan over candidates is not the
/// general Holonics navigation law."* This is the structure, enumerated: every route inside the
/// bound, each with what it retains and what it crosses, and the distinct faces they deliver. A
/// ranking is a declared receiver applied to this afterwards — [`Self::ranked_by`] takes the
/// caller's key and the library supplies none.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RouteSet<S, I, F> {
    source: Observer<S, I>,
    target: Observer<S, I>,
    bound: RouteBound,
    routes: Vec<Route<S, I, F>>,
    searched: usize,
}

impl<S: Clone + Ord + Debug, I: Clone + Ord + Debug, F: Clone + Eq + Debug> RouteSet<S, I, F> {
    /// The address the routes leave.
    pub const fn source(&self) -> &Observer<S, I> {
        &self.source
    }

    /// The address they arrive at.
    pub const fn target(&self) -> &Observer<S, I> {
        &self.target
    }

    /// The bound they were enumerated under.
    pub const fn bound(&self) -> RouteBound {
        self.bound
    }

    /// Every route found.
    pub fn routes(&self) -> &[Route<S, I, F>] {
        &self.routes
    }

    /// How many search nodes the enumeration visited.
    pub const fn searched(&self) -> usize {
        self.searched
    }

    /// **The distinct faces the routes deliver at the target address.** More than one is the
    /// statement that the address is plural: two routes crossed a square that does not commute, or
    /// one of them opened a fibre. Both are returned; neither is picked.
    pub fn delivered_faces(&self) -> Vec<F> {
        let mut faces: Vec<F> = Vec::new();
        for route in &self.routes {
            if !faces.contains(route.delivered()) {
                faces.push(route.delivered().clone());
            }
        }
        faces
    }

    /// Whether two routes deliver different faces at the same address.
    ///
    /// [definition] Two different faces are two occurrences that are **not** identical, so the two
    /// routes' deliveries stand strictly below `relation_ladder`'s identity rung. Which rung they
    /// do stand on is a receiver's reading, and [`SquareReading::rung`] is where this module states
    /// it; a route plan carries no receiver and states no rung of its own.
    pub fn address_is_plural(&self) -> bool {
        self.delivered_faces().len() > 1
    }

    /// The routes ordered by a **declared** key. This is a receiver applied after the enumeration,
    /// never the navigation law: the set above is the return, and this is one reading of it.
    pub fn ranked_by<K: Ord>(&self, key: impl Fn(&Route<S, I, F>) -> K) -> Vec<&Route<S, I, F>> {
        let mut ranked: Vec<&Route<S, I, F>> = self.routes.iter().collect();
        ranked.sort_by_key(|route| key(route));
        ranked
    }
}

/// What a bounded route enumeration returns.
///
/// [definition] Three arms, and **none of them is "unreachable"**: a bounded search refutes and
/// never affirms, so the empty return names the bound it ran under and says exactly that no route
/// was found inside it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoutePlan<S, I, F> {
    /// The routes found inside the declared bound.
    Routes(RouteSet<S, I, F>),
    /// No route inside the declared bound. Not a claim that none exists.
    NoRouteWithinBound {
        /// Where the search started.
        source: Observer<S, I>,
        /// Where it was looking for.
        target: Observer<S, I>,
        /// The bound it ran under.
        bound: RouteBound,
        /// How many search nodes it visited.
        searched: usize,
    },
    /// More routes exist inside the declared move bound than the declared route count admits. The
    /// enumeration is not truncated and presented as complete; the bound is returned as too small.
    MoreRoutesThanDeclared {
        /// The bound it ran under.
        bound: RouteBound,
        /// How many routes were found before the count was exceeded.
        found: usize,
    },
}

/// The state of one depth-first route walk.
struct RouteWalk<'a, T: StationedTower> {
    tube: &'a T,
    target: &'a Observer<TubeStation<T>, TubeIndex<T>>,
    word: &'a [TubeStation<T>],
    charts: &'a [TubeIndex<T>],
    candidates: &'a [(TubeIndex<T>, TubeFace<T>)],
    bound: RouteBound,
    routes: Vec<Route<TubeStation<T>, TubeIndex<T>, TubeFace<T>>>,
    searched: usize,
    overflowed: bool,
}

impl<T: StationedTower> RouteWalk<'_, T> {
    #[allow(clippy::too_many_arguments)]
    fn walk(
        &mut self,
        station: &TubeStation<T>,
        chart: &TubeIndex<T>,
        face: &TubeFace<T>,
        moves: &mut Vec<RouteMove<TubeStation<T>, TubeIndex<T>>>,
        residuals: &mut Vec<(TubeStation<T>, TubeIndex<T>, TubeIndex<T>)>,
        crossed: &mut Vec<CrossedSquare<TubeStation<T>, TubeIndex<T>>>,
        visited: &mut Vec<(TubeStation<T>, TubeIndex<T>)>,
    ) -> HorizonOutcome<T, ()> {
        // One node, plus the square check this node runs at every comparable declared chart: the
        // ceiling bounds the work and not merely the node count.
        self.searched = self
            .searched
            .saturating_add(1 + self.charts.len().saturating_mul(self.charts.len()));
        if self.searched > DECLARED_SEARCH_CEILING {
            return Err(HorizonRefusal::SearchAboveWorkCeiling {
                ceiling: DECLARED_SEARCH_CEILING,
            });
        }
        if station == self.target.station() && chart == self.target.chart() {
            if self.routes.len() >= self.bound.routes() {
                self.overflowed = true;
                return Ok(());
            }
            self.routes.push(Route {
                moves: moves.clone(),
                delivered: face.clone(),
                residuals_retained: residuals.clone(),
                crossed: crossed.clone(),
            });
            return Ok(());
        }
        if moves.len() >= self.bound.moves() {
            return Ok(());
        }
        let Some(section) = self.tube.section(station) else {
            return Err(TubeRefusal::StationMissing {
                station: station.clone(),
            }
            .into());
        };

        // One longitudinal step along the declared word.
        let next_station = self
            .word
            .iter()
            .position(|candidate| candidate == station)
            .and_then(|at| self.word.get(at + 1));
        if let Some(later) = next_station
            && self.tube.follows(station, later)
            && !visited.contains(&(later.clone(), chart.clone()))
        {
                    let carried = self.tube.transport(station, later, chart, face)?;
                    // The squares this step crosses, at every declared chart comparable to the one
                    // the face is carried at: this is where two routes to one address part.
                    let mut crossed_here = Vec::new();
                    for other in self.charts {
                        let (coarse, fine) = if strictly_refines(section, other, chart) {
                            (other.clone(), chart.clone())
                        } else if strictly_refines(section, chart, other) {
                            (chart.clone(), other.clone())
                        } else {
                            continue;
                        };
                        let verdict = check_commuting_square(
                            self.tube,
                            station,
                            later,
                            &[coarse.clone(), fine.clone()],
                            &[(fine.clone(), face.clone())],
                        );
                        let commutes = match verdict {
                            Ok(verdict) => verdict.commutes(),
                            // A square the tube refuses to check on this face is not a square this
                            // route crossed; the route's own moves are checked by their own calls.
                            Err(_) => continue,
                        };
                        crossed_here.push(CrossedSquare {
                            earlier: station.clone(),
                            later: later.clone(),
                            coarse,
                            fine,
                            commutes,
                        });
                    }
                    moves.push(RouteMove::Transport {
                        earlier: station.clone(),
                        later: later.clone(),
                        chart: chart.clone(),
                    });
                    let crossed_at = crossed.len();
                    crossed.extend(crossed_here);
                    visited.push((later.clone(), chart.clone()));
            self.walk(later, chart, &carried, moves, residuals, crossed, visited)?;
            visited.pop();
            crossed.truncate(crossed_at);
            moves.pop();
        }

        // One cover step toward a coarser chart, and one toward a finer one.
        for other in self.charts {
            if !index_adjacent(section, self.charts, chart, other) {
                continue;
            }
            if visited.contains(&(station.clone(), other.clone())) {
                continue;
            }
            if section.refines(other, chart) {
                let restricted = section
                    .restrict(other, chart, face)
                    .map_err(TubeRefusal::Section)?;
                moves.push(RouteMove::Restrict {
                    station: station.clone(),
                    fine: chart.clone(),
                    coarse: other.clone(),
                });
                visited.push((station.clone(), other.clone()));
                self.walk(
                    station, other, &restricted, moves, residuals, crossed, visited,
                )?;
                visited.pop();
                moves.pop();
            } else if section.refines(chart, other) {
                for (candidate_chart, candidate) in self.candidates {
                    if candidate_chart != other {
                        continue;
                    }
                    let restricted = section
                        .restrict(chart, other, candidate)
                        .map_err(TubeRefusal::Section)?;
                    if &restricted != face {
                        continue;
                    }
                    moves.push(RouteMove::Reopen {
                        station: station.clone(),
                        coarse: chart.clone(),
                        fine: other.clone(),
                    });
                    residuals.push((station.clone(), chart.clone(), other.clone()));
                    visited.push((station.clone(), other.clone()));
                    self.walk(
                        station, other, candidate, moves, residuals, crossed, visited,
                    )?;
                    visited.pop();
                    residuals.pop();
                    moves.pop();
                }
            }
        }
        Ok(())
    }
}

/// **Plan every route between two addresses inside a declared bound.**
///
/// An address is a station and a chart. A route is a word of the tube's own passages — longitudinal
/// transports along the declared word and restrictions through the cover graph — together with the
/// reopenings a retained residual buys. Every route inside the bound is returned with its receipt;
/// a bound that finds none returns [`RoutePlan::NoRouteWithinBound`] naming the bound, never
/// "unreachable".
// Each argument is a **separately declared population** with its own ceiling and its own named
// refusal: the word, the chart aperture, the fibre candidates and the two coordinates of the
// bound. Bundling them into one struct would make a refusal name the bundle instead of the
// declaration that exceeded its bound.
#[allow(clippy::too_many_arguments)]
pub fn plan_routes<T: StationedTower>(
    tube: &T,
    source: &TubeObserver<T>,
    source_face: &TubeFace<T>,
    target: &TubeObserver<T>,
    bound: RouteBound,
    word: &[TubeStation<T>],
    charts: &[TubeIndex<T>],
    candidates: &[(TubeIndex<T>, TubeFace<T>)],
) -> HorizonOutcome<T, TubeRoutePlan<T>> {
    if charts.len() > DECLARED_CHART_CEILING {
        return Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "chart aperture",
            declared: charts.len(),
            ceiling: DECLARED_CHART_CEILING,
        });
    }
    if word.len() > DECLARED_CIRCUIT_CEILING {
        return Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "station word",
            declared: word.len(),
            ceiling: DECLARED_CIRCUIT_CEILING,
        });
    }
    if candidates.len() > DECLARED_CANDIDATE_CEILING {
        return Err(HorizonRefusal::DeclarationAboveCeiling {
            what: "candidate population",
            declared: candidates.len(),
            ceiling: DECLARED_CANDIDATE_CEILING,
        });
    }
    total_face_population(tube, candidates)?;
    let mut walk = RouteWalk {
        tube,
        target,
        word,
        charts,
        candidates,
        bound,
        routes: Vec::new(),
        searched: 0,
        overflowed: false,
    };
    let mut moves = Vec::new();
    let mut residuals = Vec::new();
    let mut crossed = Vec::new();
    let mut visited = vec![(source.station().clone(), source.chart().clone())];
    walk.walk(
        source.station(),
        source.chart(),
        source_face,
        &mut moves,
        &mut residuals,
        &mut crossed,
        &mut visited,
    )?;
    if walk.overflowed {
        return Ok(RoutePlan::MoreRoutesThanDeclared {
            bound,
            found: walk.routes.len(),
        });
    }
    if walk.routes.is_empty() {
        return Ok(RoutePlan::NoRouteWithinBound {
            source: source.clone(),
            target: target.clone(),
            bound,
            searched: walk.searched,
        });
    }
    Ok(RoutePlan::Routes(RouteSet {
        source: source.clone(),
        target: target.clone(),
        bound,
        routes: walk.routes,
        searched: walk.searched,
    }))
}

// ---------------------------------------------------------------------------------------------
// T5 (d) — the real instance: three presentations of one object, read at two grains
// ---------------------------------------------------------------------------------------------

/// A station of a [`PresentationTube`]: which presentation, and which reading of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct PresentationStation {
    /// Which presentation, in the declared order.
    pub presentation: usize,
    /// The complete atom-grain reading, or the selected one.
    pub reading: GrainStation,
}

impl PresentationStation {
    /// The station of one presentation's complete atom-grain reading.
    pub const fn complete(presentation: usize) -> Self {
        Self {
            presentation,
            reading: GrainStation::Complete,
        }
    }

    /// The station of one presentation's selected reading.
    pub const fn selected(presentation: usize) -> Self {
        Self {
            presentation,
            reading: GrainStation::Selected,
        }
    }
}

/// **Several presentations of one object as the stations of one tube.**
///
/// [definition] This composes [`GrainReadingTube`] and founds no second carrier: each presentation
/// carries one of those tubes, with its complete atom-grain tower, its alpha-carbon selection and
/// the measured square between them. What this adds is the **environment** axis — the same object
/// presented in several environments — as further stations of the same longitudinal order.
///
/// [definition] The two longitudinal transports are different in kind and the difference is the
/// finding:
///
/// * within one presentation, `Complete → Selected` is the declared alpha-carbon selection, and its
///   square with the atom→residue restriction **fails** — that is `grainSquareDefect`;
/// * between two presentations, the transport is the target presentation's own measured face at
///   that chart. It is **constant in its source**, exactly as
///   `physical_occurrence::Passage`'s `Transition::apply` is constant in the source's classes: a
///   later environment's contacts are measured there and are not computed from the earlier one.
///   Its square with the restriction commutes, because a `GrainTower`'s coarser face **is** the
///   restriction of its atom face.
///
/// [established-bounded] What does not fit, stated exactly: `physical_occurrence::Passage` is a
/// `Transition` between `OccurrenceFace`s — occurrence identity, environment and the per-contact
/// class of a `physical_constraint_complex` — while a tube's transverse section here is a
/// `GrainTower` whose face is a `GrainFace` over `GrainPair`s. No adapter between those two face
/// types exists in this repository, and founding one to make the passage type-check would be a
/// second carrier for a law that is already available: the constancy of `apply` in its source. The
/// transport below therefore **is** that passage's law at the grain tower's face type, and the
/// passage owner's environment coordinates travel beside it rather than inside it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PresentationTube {
    presentations: Vec<GrainReadingTube>,
    lineages: Vec<String>,
}

impl PresentationTube {
    /// Found the tube from the declared presentations, in order.
    ///
    /// The order is the caller's declaration — it is the order the environments are presented in,
    /// not a claim that one caused the next.
    /// Nothing about the declaration itself can fail — each presentation was already founded by
    /// `GrainReadingTube::found`, which is where the selection is checked — so this returns the
    /// tube rather than a `Result` that could not carry a refusal. A station outside the declared
    /// presentations is refused by name at the moment it is used
    /// (`TubeRefusal::StationMissing`).
    pub fn found(presentations: Vec<(String, GrainReadingTube)>) -> Self {
        let mut lineages = Vec::with_capacity(presentations.len());
        let mut tubes = Vec::with_capacity(presentations.len());
        for (lineage, tube) in presentations {
            lineages.push(lineage);
            tubes.push(tube);
        }
        Self {
            presentations: tubes,
            lineages,
        }
    }

    /// How many presentations this tube carries.
    pub fn presentations(&self) -> usize {
        self.presentations.len()
    }

    /// The declared lineage of one presentation.
    pub fn lineage(&self, presentation: usize) -> Option<&str> {
        self.lineages.get(presentation).map(String::as_str)
    }

    /// One presentation's own two-station grain tube.
    pub fn presentation(&self, presentation: usize) -> Option<&GrainReadingTube> {
        self.presentations.get(presentation)
    }

    /// Every station of the tube, in the declared order.
    pub fn stations(&self) -> Vec<PresentationStation> {
        (0..self.presentations.len())
            .flat_map(|presentation| {
                [
                    PresentationStation::complete(presentation),
                    PresentationStation::selected(presentation),
                ]
            })
            .collect()
    }
}

impl StationedTower for PresentationTube {
    type Station = PresentationStation;
    type Section = GrainTower;

    fn follows(&self, earlier: &PresentationStation, later: &PresentationStation) -> bool {
        earlier.presentation <= later.presentation && earlier.reading <= later.reading
    }

    fn declared_face_population(&self, _chart: &Grain, face: &GrainFace) -> usize {
        face.classified().len()
    }

    fn section(&self, station: &PresentationStation) -> Option<&GrainTower> {
        let presentation = self.presentations.get(station.presentation)?;
        presentation.section(&station.reading)
    }

    fn transport(
        &self,
        earlier: &PresentationStation,
        later: &PresentationStation,
        chart: &Grain,
        face: &GrainFace,
    ) -> Result<GrainFace, TubeRefusal<PresentationStation, Grain, GrainFace>> {
        if !self.follows(earlier, later) {
            return Err(TubeRefusal::NotAStep {
                earlier: *earlier,
                later: *later,
            });
        }
        if face.grain() != *chart {
            return Err(TubeRefusal::Section(TowerRefusal::FaceNotCarried {
                chart: *chart,
                face: face.clone(),
            }));
        }
        let Some(source) = self.presentations.get(earlier.presentation) else {
            return Err(TubeRefusal::StationMissing { station: *earlier });
        };
        if earlier.presentation == later.presentation {
            return source
                .transport(&earlier.reading, &later.reading, chart, face)
                .map_err(reseat_grain_refusal(*earlier, *later));
        }
        // Across presentations the transport is the target's own measured face at that chart:
        // constant in its source, exactly as a passage's `apply` is.
        let Some(target) = self.section(later) else {
            return Err(TubeRefusal::StationMissing { station: *later });
        };
        target
            .face(*chart)
            .map_err(|_| TubeRefusal::Section(TowerRefusal::NotARefinement {
                coarse: *chart,
                fine: Grain::Atom,
            }))
    }
}

/// Carry a [`GrainReadingTube`]'s own refusal into a [`PresentationTube`]'s station type.
fn reseat_grain_refusal(
    earlier: PresentationStation,
    later: PresentationStation,
) -> impl Fn(TubeRefusal<GrainStation, Grain, GrainFace>) -> TubeRefusal<PresentationStation, Grain, GrainFace>
{
    move |refusal| match refusal {
        TubeRefusal::NotAStep { .. } => TubeRefusal::NotAStep { earlier, later },
        TubeRefusal::StationMissing { .. } => TubeRefusal::StationMissing { station: earlier },
        TubeRefusal::Section(inner) => TubeRefusal::Section(inner),
        TubeRefusal::OrdersDisagree { coarse, fine } => {
            TubeRefusal::OrdersDisagree { coarse, fine }
        }
        TubeRefusal::FaceOutsideAperture { chart } => {
            TubeRefusal::FaceOutsideAperture { chart }
        }
        TubeRefusal::DeclarationAboveCeiling { declared, ceiling } => {
            TubeRefusal::DeclarationAboveCeiling { declared, ceiling }
        }
        TubeRefusal::CircuitNotClosed { .. } => TubeRefusal::CircuitNotClosed {
            first: earlier,
            last: later,
        },
        TubeRefusal::EmptyCircuit => TubeRefusal::EmptyCircuit,
    }
}

/// **The contact receiver of a grain face: how many pairs it reads in one declared class.**
///
/// Lean counterpart: `Transport/ContinuingTube.lean::grainContactReading`, which asks the same
/// question as a predicate. The count is an exact integer — a `ContactClass` population, never a
/// float — and it is the receiver the M5 profile is read at: the discrepancy between the two routes
/// of the failing square **is** the fine contacts the coarse receiver never saw.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GrainContactCount {
    receiver: String,
    class: ContactClass,
}

impl GrainContactCount {
    /// The receiver that counts one declared contact class.
    pub fn of(class: ContactClass) -> Self {
        Self {
            receiver: format!("grain contact count: {class:?}"),
            class,
        }
    }

    /// The class it counts.
    pub const fn class(&self) -> ContactClass {
        self.class
    }
}

impl<T> FaceReading<T> for GrainContactCount
where
    T: StationedTower<Section = GrainTower>,
{
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(
        &self,
        _station: &TubeStation<T>,
        _chart: &Grain,
        face: &GrainFace,
    ) -> Result<ExactFace, WidthRefusal> {
        let count = face
            .classified()
            .values()
            .filter(|class| **class == self.class)
            .count();
        Ok(ExactFace::Count(BigInt::from(count)))
    }
}

#[cfg(test)]
#[path = "continuing_tube/tests.rs"]
mod tests;
