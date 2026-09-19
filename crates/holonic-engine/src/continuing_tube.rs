//! The continuing tube: a tower is the transverse section of a tube, and a wormhole is exact.
//!
//! # The paired Lean owner
//!
//! This module is one half of a coupled pair. The other half is
//! `formal/elementary-holonics/ElementaryHolonics/Transport/ContinuingTube.lean`, namespace
//! `Soma.Holonics.Transport.ContinuingTube`, which names this file in its header. Every public item
//! below cites the declaration it realizes.
//!
//! Every name in the first column below is a declaration of that one file.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `ChartwiseMigration`, `ChartwiseMigration.naturality` | [`StationedTower::transport`], [`check_commuting_square`] |
//! | `Tube`, `Tube.square` | [`StationedTower`], [`SquareVerdict`] |
//! | `SquareVerdict.commutes`, `SquareVerdict.defect` | [`SquareVerdict::Commutes`], [`SquareVerdict::Defect`] |
//! | `squareVerdict_total` | [`SquareVerdict`] is the only return of [`check_commuting_square`] |
//! | `Tube.transport_roundTrip`, `tube_circuit_has_no_defect` | [`check_circuit_holonomy`], [`HolonomyVerdict::Identity`] |
//! | `ChartwiseMigration.HasDefect`, `flipCircuit_hasDefect` | [`HolonomyVerdict::Defect`], [`FlipTube`] |
//! | `ChartwiseMigration.cocycleDefect`, `circuit_defect_is_holonomy_not_loss` | [`HolonomyVerdict::Defect`] is holonomy, not loss |
//! | `Wormhole`, `Wormhole.crosses` | [`WormholeReceipt`], [`wormhole_receipt`] |
//! | `Tube.transport_is_not_a_wormhole`, `Tube.refinementRoute_is_not_a_wormhole` | [`WormholeReceipt::is_wormhole`] on a tube's own passages |
//! | `lossySwapMigration`, `lossiness_is_independent_of_being_a_wormhole` | [`LossySwapMigration`] |
//! | `constantTube`, `padicTube` | [`ConstantTube`] over `continuing_tower::ResidueTower` |
//! | `padicTube_crossSection_branching` | `continuing_tower::ResidueTower::split_fibre` (cited, not rebuilt) |
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
//! Three names this module also cites belong to other Lean owners and are therefore not rows of
//! that table: `Foundation/ContinuingTower.lean::Migration.ConnectsIncomparableCharts` (the
//! condition `Wormhole.crosses` carries) and `::padicFibre_card` (the cross-section count), and
//! `Foundation/GrainRestriction.lean::equal_aperture_is_not_lawful` (the measured witness of the
//! failing grain square).
//!
//! # What a tube is here
//!
//! A tube has two axes. The **transverse** axis is the `continuing_tower::Tower` presented at each
//! station: the aperture/grain/precision ladder, with `restrict` the only transport. The
//! **longitudinal** axis is the station order, with [`StationedTower::transport`] the passage along
//! it. The one law that joins them is that the two commute, and
//! [`check_commuting_square`] asks it over a declared aperture and returns a
//! [`SquareVerdict`] — never a repair.
//!
//! The Lean side proves that law *is* `Migration.naturality` with the identity index map. Here it
//! is checked, because a running tube's transport is declared and not typed.
//!
//! # What this module does not assume
//!
//! [`StationedTower`] does **not** impose the functor laws
//! `transport(s, s) = id` and `transport(t, r) ∘ transport(s, t) = transport(s, r)`. Lean's `Tube`
//! carries them as fields and therefore proves `Tube.transport_roundTrip`: a *functorial* tube has
//! no longitudinal holonomy, exactly as `Tower.restrict_roundTrip` shows its transverse ladder has
//! none. A declared family need not be functorial, and [`check_circuit_holonomy`] is precisely the
//! operation that finds out. [`FlipTube`] is a declared family whose every square commutes and
//! whose closed circuit does not return the identity — the two axes separate.
//!
//! # What is exact and what is declared
//!
//! No float decides anything. Faces and residuals are the underlying towers' exact carriers
//! (`num_bigint::BigUint`, `grain_tower::GrainFace`). Three things are caller-declared and every
//! one of them is bounded before any loop or allocation uses it: the chart aperture
//! ([`DECLARED_CHART_CEILING`]), the face population ([`DECLARED_FACE_CEILING`]) and the circuit
//! word ([`DECLARED_CIRCUIT_CEILING`]). Exceeding one is a typed refusal, never a panic and never a
//! silent truncation. Every receipt names exactly what was checked; the receipt is the scope of the
//! claim and is not a proof of the law.
//!
//! # The physical realization
//!
//! `crates/holonic-engine/src/tube.rs::ReceiverTube` is the same two axes as physical apparatus —
//! a core receiver, a transverse section, a horizon that is the link of the receiver's simplicial
//! star, an exact projective attachment, and `ReceiverTube::presentation_holonomy` as the composite
//! of its longitudinal presentation word. This module is the carrier law that owner instantiates;
//! neither is a description of the other.

use std::collections::BTreeSet;
use std::fmt::{self, Debug};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;

use crate::continuing_tower::{
    ChartRoute, Migration, MigrationOutcome, MigrationSourceIndex, MigrationTargetIndex,
    ResidualMigration, Tower, TowerRefusal, TwoChartTower, TwoCharts, check_index_routes,
};
use crate::grain_tower::{
    ApertureRelation, FineNativeDeclaration, Grain, GrainAddress, GrainCell, GrainFace,
    GrainRefusal, GrainSelection, GrainTower,
};
use crate::physical_constraint_complex::ContactClass;
use crate::receiver_release::{
    DiameterNorm, ExactFace, Horizon, ReceiverWidth, WidthRefusal, width_over_readings,
};
use crate::relation_ladder::Rung;

/// The largest chart aperture a caller may declare to one check.
///
/// Lean quantifies over every `i ≤ j`. A running program checks a declared finite list, and a
/// declaration above this bound is refused *before* any loop runs over it — the square check is
/// quadratic in the aperture.
pub const DECLARED_CHART_CEILING: usize = 1024;

/// The largest face population a caller may declare to one check.
///
/// It bounds **two** counts, because a declaration of faces declares two different sizes: how many
/// `(chart, face)` pairs the caller hands in, and how many exact entries those faces carry between
/// them ([`StationedTower::declared_face_population`] summed over the list). A tube's transport may
/// copy a face whole — [`GrainReadingTube`] clones its face map on every selection — so the second
/// is the one the work is actually proportional to, and counting containers alone would admit a
/// two-face declaration carrying a million contacts.
pub const DECLARED_FACE_CEILING: usize = 65_536;

/// The longest circuit word a caller may declare to one holonomy check.
pub const DECLARED_CIRCUIT_CEILING: usize = 4096;

/// The largest number of `(square, face)` or `(step, face)` comparisons one check may perform.
///
/// The per-axis ceilings above bound each declared list; this bounds their **product**, which is
/// what the work actually is: the square check is quadratic in the aperture and linear in the face
/// population, and the holonomy check is linear in all three. The product is formed with checked
/// arithmetic, so a declaration whose product overflows `usize` is refused rather than wrapping.
///
/// The face factor of that product is the **population** of the declared faces and not how many
/// containers they came in, because a transport may copy a face whole; see
/// [`StationedTower::declared_face_population`].
pub const DECLARED_WORK_CEILING: usize = 1 << 22;

/// The declared work of a check, or `None` when the product overflows.
fn declared_work(factors: &[usize]) -> Option<usize> {
    factors
        .iter()
        .try_fold(1usize, |carried, factor| carried.checked_mul((*factor).max(1)))
}

/// The total exact population of a declared face list, bounded before any transport runs.
///
/// The caller's own count is the number of `(chart, face)` pairs; this is the number of exact
/// entries inside them, which is what a transport that copies a face whole actually moves. The sum
/// is formed with `checked_add`, so an overflowing declaration is refused rather than wrapped.
fn total_face_population<T: StationedTower>(
    tube: &T,
    faces: &[(TubeIndex<T>, TubeFace<T>)],
) -> TubeOutcome<T, usize> {
    let mut total = 0_usize;
    for (chart, face) in faces {
        let Some(carried) = total.checked_add(tube.declared_face_population(chart, face)) else {
            return Err(TubeRefusal::DeclarationAboveCeiling {
                declared: usize::MAX,
                ceiling: DECLARED_FACE_CEILING,
            });
        };
        total = carried;
    }
    if total > DECLARED_FACE_CEILING {
        return Err(TubeRefusal::DeclarationAboveCeiling {
            declared: total,
            ceiling: DECLARED_FACE_CEILING,
        });
    }
    Ok(total)
}

/// Why a tube, a step or a square check was refused.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::Tube` carries `transport` as a field typed by
/// the step `s ≤ t`, so an inadmissible step cannot be formed. A running tube must be asked, so
/// every failure is returned as one of these variants instead of aborting.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TubeRefusal<S, I, F> {
    /// The later station does not follow the earlier one, so there is no longitudinal passage.
    NotAStep {
        /// The claimed earlier station.
        earlier: S,
        /// The claimed later station.
        later: S,
    },
    /// The tube presents no transverse section at that station.
    StationMissing {
        /// The station with no section.
        station: S,
    },
    /// One of the two transverse sections refused.
    Section(TowerRefusal<I, F>),
    /// The two stations' sections disagree about the refinement order, so there is no single
    /// square to check. Lean shares one `Preorder Index` between the towers of a `Tube` by
    /// construction; here two sections may present different orders, and that is returned.
    OrdersDisagree {
        /// The claimed coarser chart.
        coarse: I,
        /// The claimed finer chart.
        fine: I,
    },
    /// A supplied face names a chart outside the aperture whose square or circuit was declared.
    /// It is refused rather than silently ignored and counted as checked.
    FaceOutsideAperture { chart: I },
    /// A caller-declared aperture, face population or circuit word exceeded its bound. Nothing was
    /// allocated or iterated.
    DeclarationAboveCeiling {
        /// What was declared.
        declared: usize,
        /// The bound it exceeded.
        ceiling: usize,
    },
    /// A circuit word does not return to the station it left, so it is not a closed circuit and
    /// has no holonomy to read.
    CircuitNotClosed {
        /// Where the word starts.
        first: S,
        /// Where it ends.
        last: S,
    },
    /// An empty circuit word. A holonomy is read around an actual circuit, and the empty word is
    /// not one; returning `Identity` for it would be a receipt for a check that did not happen.
    EmptyCircuit,
}

impl<S: Debug, I: Debug, F: Debug> fmt::Display for TubeRefusal<S, I, F> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotAStep { earlier, later } => write!(
                formatter,
                "{later:?} does not follow {earlier:?}: no longitudinal passage"
            ),
            Self::StationMissing { station } => {
                write!(formatter, "no transverse section at station {station:?}")
            }
            Self::Section(refusal) => write!(formatter, "transverse section refused: {refusal}"),
            Self::OrdersDisagree { coarse, fine } => write!(
                formatter,
                "the two sections disagree on whether {fine:?} refines {coarse:?}"
            ),
            Self::FaceOutsideAperture { chart } => write!(
                formatter,
                "the supplied face names chart {chart:?}, outside the declared aperture"
            ),
            Self::DeclarationAboveCeiling { declared, ceiling } => write!(
                formatter,
                "declared {declared} entries, above the ceiling of {ceiling}"
            ),
            Self::CircuitNotClosed { first, last } => write!(
                formatter,
                "circuit word runs {first:?} to {last:?} and is not closed"
            ),
            Self::EmptyCircuit => write!(formatter, "the empty word is not a circuit"),
        }
    }
}

impl<S: Debug, I: Debug, F: Debug> std::error::Error for TubeRefusal<S, I, F> {}

/// A family of transverse sections over a longitudinal station order, together with the passage
/// along it.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::Tube`. [`Self::section`] is Lean's `station`
/// — the `Tower` presented at one station — and [`Self::transport`] is the component of Lean's
/// `ChartwiseMigration` at one chart. Lean's `naturality` field is checked here by
/// [`check_commuting_square`]; Lean's `transport_refl` and `transport_trans` are checked by
/// [`check_circuit_holonomy`] and are deliberately **not** assumed.
pub trait StationedTower {
    /// The longitudinal axis: where along the tube a cross-section sits.
    type Station: Clone + Ord + Debug;

    /// The transverse section: the tower of faces at one station.
    type Section: Tower;

    /// Whether `later` follows `earlier` along the tube.
    ///
    /// Lean counterpart: the `s ≤ t` that types `Tube.transport`.
    fn follows(&self, earlier: &Self::Station, later: &Self::Station) -> bool;

    /// The transverse section at one station, or `None` when the tube presents none there.
    ///
    /// Lean counterpart: `Tube.station`.
    fn section(&self, station: &Self::Station) -> Option<&Self::Section>;

    /// **How many exact entries one declared face carries.**
    ///
    /// The work of a transport is proportional to the *contents* of a face, not to the container
    /// the caller counted them in: [`GrainReadingTube`]'s selection clones a whole face map, so the
    /// work of one selection is that map's population and a declaration of "one face" says nothing
    /// about it. [`check_commuting_square`] and [`check_circuit_holonomy`] sum this over the
    /// declared list and bound the sum — against [`DECLARED_FACE_CEILING`] and inside
    /// [`DECLARED_WORK_CEILING`] — before any transport runs.
    ///
    /// The default is `1`, which is exact for a tube whose face is a single exact value such as a
    /// residue or a bit. A tube whose face is a collection overrides it with that collection's
    /// length, which must be readable without copying the face.
    fn declared_face_population(&self, _chart: &TubeIndex<Self>, _face: &TubeFace<Self>) -> usize {
        1
    }

    /// Carry a face along one longitudinal step, at one chart.
    ///
    /// Lean counterpart: `ChartwiseMigration.face` of `Tube.transport`.
    fn transport(
        &self,
        earlier: &Self::Station,
        later: &Self::Station,
        chart: &TubeIndex<Self>,
        face: &TubeFace<Self>,
    ) -> TubeOutcome<Self, TubeFace<Self>>;
}

/// The station type of a tube.
pub type TubeStation<T> = <T as StationedTower>::Station;
/// The chart index of a tube's transverse sections.
pub type TubeIndex<T> = <<T as StationedTower>::Section as Tower>::Index;
/// The face type of a tube's transverse sections.
pub type TubeFace<T> = <<T as StationedTower>::Section as Tower>::Face;
/// A tube's own typed refusal, in its own station, index and face types.
pub type TubeRefusalOf<T> = TubeRefusal<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;
/// A tube return `V`, or that tube's own typed [`TubeRefusal`].
pub type TubeOutcome<T, V> = Result<V, TubeRefusalOf<T>>;
/// A tube's own [`SquareVerdict`], in its own station, index and face types.
pub type TubeSquareVerdict<T> = SquareVerdict<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;
/// A tube's own [`HolonomyVerdict`], in its own station, index and face types.
pub type TubeHolonomyVerdict<T> = HolonomyVerdict<TubeStation<T>, TubeIndex<T>, TubeFace<T>>;

/// The two-axis square at one longitudinal step, read as an object: either the commuting law over
/// the declared aperture, or a witnessed defect carrying both routes' faces.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::SquareVerdict`, with `squareVerdict_total`
/// making the two arms exhaustive. A defect is returned whole and is never resolved by choosing a
/// route: `grainSquareDefect` is a real instance and
/// `grainSquare_defect_is_not_a_loss` proves the disagreement is holonomy rather than loss.
/// **Forging a verdict is a compile error.** The payload of each arm is a struct whose every field
/// is private to this module, with no public constructor, no `Default` and no `Deserialize`. Only
/// [`check_commuting_square`] builds one, so a value of this type is a receipt that the check
/// named in it actually ran; read access is the accessors on [`CommutingSquares`] and
/// [`SquareDefect`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SquareVerdict<S, I, F> {
    /// Every declared square commuted on every declared face.
    Commutes(CommutingSquares<S, I>),
    /// One face at which the two routes disagree, carrying both.
    Defect(SquareDefect<S, I, F>),
}

impl<S, I, F> SquareVerdict<S, I, F> {
    /// Whether the square commuted over the declared aperture.
    pub fn commutes(&self) -> bool {
        matches!(self, Self::Commutes(_))
    }

    /// The commuting receipt, when that is the verdict.
    pub const fn commuting(&self) -> Option<&CommutingSquares<S, I>> {
        match self {
            Self::Commutes(receipt) => Some(receipt),
            Self::Defect(_) => None,
        }
    }

    /// The witnessed defect, when that is the verdict.
    pub const fn defect(&self) -> Option<&SquareDefect<S, I, F>> {
        match self {
            Self::Defect(witness) => Some(witness),
            Self::Commutes(_) => None,
        }
    }
}

/// **The receipt that every declared square commuted**, and the exact scope of that claim.
///
/// Lean counterpart: the `commutes` arm of `SquareVerdict`, whose payload is the law itself. Here
/// the payload is what was checked: which squares carried a declared face, and how many faces and
/// how much face population the check ran over. Constructible only by [`check_commuting_square`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommutingSquares<S, I> {
    earlier: S,
    later: S,
    squares: Vec<(I, I)>,
    faces_checked: usize,
    population_checked: usize,
}

impl<S, I> CommutingSquares<S, I> {
    /// The step that was checked.
    pub const fn earlier(&self) -> &S {
        &self.earlier
    }

    /// The station it ran to.
    pub const fn later(&self) -> &S {
        &self.later
    }

    /// The `(coarse, fine)` chart pairs whose square commuted on at least one declared face.
    pub fn squares(&self) -> &[(I, I)] {
        &self.squares
    }

    /// How many `(chart, face)` pairs were presented.
    pub const fn faces_checked(&self) -> usize {
        self.faces_checked
    }

    /// How many exact entries those faces carried between them, which is the size the work of the
    /// check was actually proportional to.
    pub const fn population_checked(&self) -> usize {
        self.population_checked
    }
}

/// **One face at which the two routes of a square disagree**, carrying both.
///
/// Lean counterpart: the `defect` arm of `SquareVerdict`, with `grainSquareDefect` a real instance.
/// The defect is returned whole and never resolved by choosing a route. Constructible only by
/// [`check_commuting_square`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SquareDefect<S, I, F> {
    earlier: S,
    later: S,
    coarse: I,
    fine: I,
    source_face: F,
    transported_then_restricted: F,
    restricted_then_transported: F,
}

impl<S, I, F> SquareDefect<S, I, F> {
    /// The step that was checked.
    pub const fn earlier(&self) -> &S {
        &self.earlier
    }

    /// The station it ran to.
    pub const fn later(&self) -> &S {
        &self.later
    }

    /// The coarser chart of the failing square.
    pub const fn coarse(&self) -> &I {
        &self.coarse
    }

    /// The finer chart.
    pub const fn fine(&self) -> &I {
        &self.fine
    }

    /// The face at the finer chart on which the two routes disagreed.
    pub const fn source_face(&self) -> &F {
        &self.source_face
    }

    /// What transporting at `fine` and then restricting returned.
    pub const fn transported_then_restricted(&self) -> &F {
        &self.transported_then_restricted
    }

    /// What restricting and then transporting at `coarse` returned.
    pub const fn restricted_then_transported(&self) -> &F {
        &self.restricted_then_transported
    }
}

/// Ask the two-axis commuting square over a declared chart aperture and face population.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::Tube.square`, which is
/// `ChartwiseMigration.naturality` and therefore `Migration.naturality` with the identity index
/// map. Lean carries it as a field; here it is asked, and the answer is a [`SquareVerdict`] naming
/// exactly what was checked.
///
/// `faces` supplies `(fine chart, face at that chart)` pairs; every refining chart pair whose fine
/// member carries a supplied face is checked.
pub fn check_commuting_square<T: StationedTower>(
    tube: &T,
    earlier: &TubeStation<T>,
    later: &TubeStation<T>,
    charts: &[TubeIndex<T>],
    faces: &[(TubeIndex<T>, TubeFace<T>)],
) -> TubeOutcome<T, TubeSquareVerdict<T>> {
    if charts.len() > DECLARED_CHART_CEILING {
        return Err(TubeRefusal::DeclarationAboveCeiling {
            declared: charts.len(),
            ceiling: DECLARED_CHART_CEILING,
        });
    }
    if faces.len() > DECLARED_FACE_CEILING {
        return Err(TubeRefusal::DeclarationAboveCeiling {
            declared: faces.len(),
            ceiling: DECLARED_FACE_CEILING,
        });
    }
    // The containers are bounded above; this is the population inside them, which is the size the
    // transports below actually move. Both are asked before any square runs.
    let population = total_face_population(tube, faces)?;
    match declared_work(&[charts.len(), charts.len(), population]) {
        Some(work) if work <= DECLARED_WORK_CEILING => {}
        Some(work) => {
            return Err(TubeRefusal::DeclarationAboveCeiling {
                declared: work,
                ceiling: DECLARED_WORK_CEILING,
            });
        }
        None => {
            return Err(TubeRefusal::DeclarationAboveCeiling {
                declared: usize::MAX,
                ceiling: DECLARED_WORK_CEILING,
            });
        }
    }
    if let Some((chart, _)) = faces.iter().find(|(chart, _)| !charts.contains(chart)) {
        return Err(TubeRefusal::FaceOutsideAperture {
            chart: chart.clone(),
        });
    }
    if !tube.follows(earlier, later) {
        return Err(TubeRefusal::NotAStep {
            earlier: earlier.clone(),
            later: later.clone(),
        });
    }
    let Some(source) = tube.section(earlier) else {
        return Err(TubeRefusal::StationMissing {
            station: earlier.clone(),
        });
    };
    let Some(target) = tube.section(later) else {
        return Err(TubeRefusal::StationMissing {
            station: later.clone(),
        });
    };

    let mut squares = Vec::new();
    for coarse in charts {
        for fine in charts {
            if source.refines(coarse, fine) != target.refines(coarse, fine) {
                return Err(TubeRefusal::OrdersDisagree {
                    coarse: coarse.clone(),
                    fine: fine.clone(),
                });
            }
            if !source.refines(coarse, fine) {
                continue;
            }
            let mut checked_here = false;
            for (chart, face) in faces {
                if chart != fine {
                    continue;
                }
                let transported = tube.transport(earlier, later, fine, face)?;
                let transported_then_restricted = target
                    .restrict(coarse, fine, &transported)
                    .map_err(TubeRefusal::Section)?;
                let restricted = source
                    .restrict(coarse, fine, face)
                    .map_err(TubeRefusal::Section)?;
                let restricted_then_transported =
                    tube.transport(earlier, later, coarse, &restricted)?;
                if transported_then_restricted != restricted_then_transported {
                    return Ok(SquareVerdict::Defect(SquareDefect {
                        earlier: earlier.clone(),
                        later: later.clone(),
                        coarse: coarse.clone(),
                        fine: fine.clone(),
                        source_face: face.clone(),
                        transported_then_restricted,
                        restricted_then_transported,
                    }));
                }
                checked_here = true;
            }
            if checked_here {
                squares.push((coarse.clone(), fine.clone()));
            }
        }
    }

    Ok(SquareVerdict::Commutes(CommutingSquares {
        earlier: earlier.clone(),
        later: later.clone(),
        squares,
        faces_checked: faces.len(),
        population_checked: population,
    }))
}

/// What a closed longitudinal circuit returns.
///
/// Lean counterpart: `ChartwiseMigration.HasDefect` and `tube_circuit_has_no_defect`. A tube whose
/// transports satisfy the functor laws returns [`Self::Identity`] — that theorem is the reason a
/// *functorial* tube carries no more holonomy than a tower does. A declared family need not be
/// functorial, and the defect it returns is `ChartwiseMigration.cocycleDefect`'s witness: by
/// `circuit_defect_is_holonomy_not_loss` both routes still reopen their own source exactly,
/// so what differs is the presented face and not information.
/// **Forging a verdict is a compile error.** As with [`SquareVerdict`], each arm's payload is a
/// struct whose fields are private to this module with no public constructor, so an
/// [`Self::Identity`] cannot be minted by a caller who never walked a circuit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HolonomyVerdict<S, I, F> {
    /// Every declared face returned to itself around the circuit.
    Identity(IdentityCircuit<S>),
    /// One face the circuit did not return.
    Defect(CircuitDefect<S, I, F>),
}

impl<S, I, F> HolonomyVerdict<S, I, F> {
    /// Whether the circuit returned the identity over the declared aperture.
    pub fn is_identity(&self) -> bool {
        matches!(self, Self::Identity(_))
    }

    /// The identity receipt, when that is the verdict.
    pub const fn identity(&self) -> Option<&IdentityCircuit<S>> {
        match self {
            Self::Identity(receipt) => Some(receipt),
            Self::Defect(_) => None,
        }
    }

    /// The witnessed holonomy, when that is the verdict.
    pub const fn defect(&self) -> Option<&CircuitDefect<S, I, F>> {
        match self {
            Self::Defect(witness) => Some(witness),
            Self::Identity(_) => None,
        }
    }
}

/// **The receipt that a closed circuit returned every declared face**, and the exact aperture that
/// claim was read at. Constructible only by [`check_circuit_holonomy`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentityCircuit<S> {
    circuit: Vec<S>,
    charts_checked: usize,
    faces_checked: usize,
    population_checked: usize,
}

impl<S> IdentityCircuit<S> {
    /// The circuit word that was walked.
    pub fn circuit(&self) -> &[S] {
        &self.circuit
    }

    /// How many charts were declared.
    pub const fn charts_checked(&self) -> usize {
        self.charts_checked
    }

    /// How many `(chart, face)` pairs were presented.
    pub const fn faces_checked(&self) -> usize {
        self.faces_checked
    }

    /// How many exact entries those faces carried between them.
    pub const fn population_checked(&self) -> usize {
        self.population_checked
    }
}

/// **One face a closed circuit did not return**, carrying what entered and what came back.
///
/// Lean counterpart: `ChartwiseMigration.HasDefect`, exhibited by `flipCircuit_hasDefect`.
/// Constructible only by [`check_circuit_holonomy`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CircuitDefect<S, I, F> {
    circuit: Vec<S>,
    chart: I,
    entered: F,
    returned: F,
}

impl<S, I, F> CircuitDefect<S, I, F> {
    /// The circuit word that was walked.
    pub fn circuit(&self) -> &[S] {
        &self.circuit
    }

    /// The chart at which the holonomy was read.
    pub const fn chart(&self) -> &I {
        &self.chart
    }

    /// The face that entered the circuit.
    pub const fn entered(&self) -> &F {
        &self.entered
    }

    /// The face that came back.
    pub const fn returned(&self) -> &F {
        &self.returned
    }
}

/// Walk a closed circuit of stations and read its holonomy at each declared chart.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::tube_circuit_has_no_defect` for the
/// functorial case and `flipCircuit_hasDefect` for the declared one. The circuit word must return
/// to the station it left; an open word is refused rather than closed silently.
pub fn check_circuit_holonomy<T: StationedTower>(
    tube: &T,
    circuit: &[TubeStation<T>],
    charts: &[TubeIndex<T>],
    faces: &[(TubeIndex<T>, TubeFace<T>)],
) -> TubeOutcome<T, TubeHolonomyVerdict<T>> {
    if circuit.len() > DECLARED_CIRCUIT_CEILING {
        return Err(TubeRefusal::DeclarationAboveCeiling {
            declared: circuit.len(),
            ceiling: DECLARED_CIRCUIT_CEILING,
        });
    }
    if charts.len() > DECLARED_CHART_CEILING {
        return Err(TubeRefusal::DeclarationAboveCeiling {
            declared: charts.len(),
            ceiling: DECLARED_CHART_CEILING,
        });
    }
    if faces.len() > DECLARED_FACE_CEILING {
        return Err(TubeRefusal::DeclarationAboveCeiling {
            declared: faces.len(),
            ceiling: DECLARED_FACE_CEILING,
        });
    }
    // As in the square check: the population inside the declared containers is what the step-by-
    // step transports move, and it is bounded before the first of them runs.
    let population = total_face_population(tube, faces)?;
    match declared_work(&[circuit.len(), charts.len(), population]) {
        Some(work) if work <= DECLARED_WORK_CEILING => {}
        Some(work) => {
            return Err(TubeRefusal::DeclarationAboveCeiling {
                declared: work,
                ceiling: DECLARED_WORK_CEILING,
            });
        }
        None => {
            return Err(TubeRefusal::DeclarationAboveCeiling {
                declared: usize::MAX,
                ceiling: DECLARED_WORK_CEILING,
            });
        }
    }
    if let Some((chart, _)) = faces.iter().find(|(chart, _)| !charts.contains(chart)) {
        return Err(TubeRefusal::FaceOutsideAperture {
            chart: chart.clone(),
        });
    }
    let (Some(first), Some(last)) = (circuit.first(), circuit.last()) else {
        return Err(TubeRefusal::EmptyCircuit);
    };
    if first != last {
        return Err(TubeRefusal::CircuitNotClosed {
            first: first.clone(),
            last: last.clone(),
        });
    }

    for (chart, entered) in faces {
        if !charts.contains(chart) {
            continue;
        }
        let mut carried = entered.clone();
        for step in circuit.windows(2) {
            // `windows(2)` yields exactly two entries; the slice pattern makes that total rather
            // than relying on indexing.
            let [earlier, later] = step else {
                continue;
            };
            if !tube.follows(earlier, later) {
                return Err(TubeRefusal::NotAStep {
                    earlier: earlier.clone(),
                    later: later.clone(),
                });
            }
            carried = tube.transport(earlier, later, chart, &carried)?;
        }
        if &carried != entered {
            return Ok(HolonomyVerdict::Defect(CircuitDefect {
                circuit: circuit.to_vec(),
                chart: chart.clone(),
                entered: entered.clone(),
                returned: carried,
            }));
        }
    }

    Ok(HolonomyVerdict::Identity(IdentityCircuit {
        circuit: circuit.to_vec(),
        charts_checked: charts.len(),
        faces_checked: faces.len(),
        population_checked: population,
    }))
}

/// Which declared charts a passage crosses to a chart the tube's own order does not relate.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::Wormhole`, whose `crosses` field is
/// `Migration.ConnectsIncomparableCharts`. A tube's own passages — its longitudinal transports and
/// its refinement routes — never cross
/// (`Tube.transport_is_not_a_wormhole`, `Tube.refinementRoute_is_not_a_wormhole`), so a nonempty
/// [`Self::crossings`] is exactly passage the tube does not own.
/// **Forging a receipt is a compile error.** Every field is private to this module and there is no
/// public constructor, no `Default` and no `Deserialize`, so an empty-crossings receipt cannot be
/// minted by a caller who never ran [`wormhole_receipt`]. Read access is the accessors below.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WormholeReceipt<TI, SI> {
    crossings: Vec<(TI, SI)>,
    charts_checked: usize,
    orders_agreed: bool,
}

impl<TI, SI> WormholeReceipt<TI, SI> {
    /// Whether the passage is a wormhole over the declared aperture.
    pub fn is_wormhole(&self) -> bool {
        !self.crossings.is_empty()
    }

    /// Each declared chart that is incomparable with the chart it reads, and that chart.
    pub fn crossings(&self) -> &[(TI, SI)] {
        &self.crossings
    }

    /// How many charts were declared.
    pub const fn charts_checked(&self) -> usize {
        self.charts_checked
    }

    /// Whether the two towers agreed on the refinement order over the declared charts.
    pub const fn orders_agreed(&self) -> bool {
        self.orders_agreed
    }
}

/// Why a wormhole reading was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WormholeRefusal {
    /// The declared chart aperture exceeded [`DECLARED_CHART_CEILING`]. Nothing was iterated.
    DeclarationAboveCeiling {
        /// What was declared.
        declared: usize,
        /// The bound it exceeded.
        ceiling: usize,
    },
}

impl fmt::Display for WormholeRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self::DeclarationAboveCeiling { declared, ceiling } = self;
        write!(
            formatter,
            "declared {declared} charts, above the ceiling of {ceiling}"
        )
    }
}

impl std::error::Error for WormholeRefusal {}

/// Read whether a passage between two of a tube's stations is a wormhole.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Migration.ConnectsIncomparableCharts` and
/// `Migration.not_factorsThroughRefinement_of_connectsIncomparableCharts`, which
/// `Transport/ContinuingTube.lean::Wormhole.not_factorsThroughRefinement` applies. The
/// classification is decided by
/// the index map alone and says nothing about the face maps, which is why lossiness is independent
/// of it (`lossiness_is_independent_of_being_a_wormhole`). This composes
/// `continuing_tower::check_index_routes` rather than reclassifying the routes.
pub fn wormhole_receipt<M>(
    migration: &M,
    target_charts: &[MigrationTargetIndex<M>],
) -> Result<WormholeReceipt<MigrationTargetIndex<M>, MigrationSourceIndex<M>>, WormholeRefusal>
where
    M: Migration,
    M::Source: Tower<Index = MigrationTargetIndex<M>>,
{
    if target_charts.len() > DECLARED_CHART_CEILING {
        return Err(WormholeRefusal::DeclarationAboveCeiling {
            declared: target_charts.len(),
            ceiling: DECLARED_CHART_CEILING,
        });
    }
    let routes = check_index_routes(migration, target_charts);
    let mut crossings = Vec::new();
    for (chart, route) in routes.routes() {
        if matches!(route, ChartRoute::Incomparable) {
            crossings.push((chart.clone(), migration.index(chart)));
        }
    }
    Ok(WormholeReceipt {
        crossings,
        charts_checked: target_charts.len(),
        orders_agreed: routes.orders_agreed(),
    })
}

/// A tube with one transverse section at every station, carried by the identity.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::constantTube`, and `padicTube` when the
/// section is `continuing_tower::ResidueTower`. It is the tube a tower already is when nothing
/// moves along the longitudinal axis, and its square commutes by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstantTube<S> {
    section: S,
    ceiling: u32,
}

impl<S: Tower> ConstantTube<S> {
    /// Found a constant tube with a declared last station. There is no unbounded station axis: a
    /// station above the ceiling carries no section and is refused by name.
    pub fn new(section: S, ceiling: u32) -> Self {
        Self { section, ceiling }
    }

    /// The one transverse section.
    pub fn section_tower(&self) -> &S {
        &self.section
    }

    /// The last station this tube presents.
    pub fn ceiling(&self) -> u32 {
        self.ceiling
    }
}

impl<S: Tower> StationedTower for ConstantTube<S> {
    type Station = u32;
    type Section = S;

    fn follows(&self, earlier: &u32, later: &u32) -> bool {
        earlier <= later && *later <= self.ceiling
    }

    fn section(&self, station: &u32) -> Option<&S> {
        if *station <= self.ceiling {
            Some(&self.section)
        } else {
            None
        }
    }

    fn transport(
        &self,
        earlier: &u32,
        later: &u32,
        chart: &S::Index,
        face: &S::Face,
    ) -> Result<S::Face, TubeRefusal<u32, S::Index, S::Face>> {
        if !self.follows(earlier, later) {
            return Err(TubeRefusal::NotAStep {
                earlier: *earlier,
                later: *later,
            });
        }
        if !self.section.carries(chart, face) {
            return Err(TubeRefusal::Section(TowerRefusal::FaceNotCarried {
                chart: chart.clone(),
                face: face.clone(),
            }));
        }
        Ok(face.clone())
    }
}

/// A declared family whose self-transport is the Boolean flip on a two-chart section.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::flipCircuit`, with `flipCircuit_hasDefect` and
/// `flipCircuit_carries_no_invariant_end`. It is the smallest object that separates the two axes:
/// **every transverse square commutes** — the section's restriction is the identity at each chart —
/// **and the closed circuit does not return the identity.** Non-orientability lives on a
/// longitudinal axis closed on itself, never in the transverse ladder, which
/// `Tower.restrict_roundTrip` already excludes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FlipTube {
    section: TwoChartTower,
}

impl FlipTube {
    /// The flip tube.
    pub fn new() -> Self {
        Self {
            section: TwoChartTower,
        }
    }

    /// The Boolean flip, as the exact residue `face + 1 mod 2`.
    fn flip(face: &BigUint) -> BigUint {
        (face + BigUint::one()) % BigUint::from(2u32)
    }
}

impl StationedTower for FlipTube {
    type Station = u32;
    type Section = TwoChartTower;

    fn follows(&self, _earlier: &u32, _later: &u32) -> bool {
        true
    }

    fn section(&self, _station: &u32) -> Option<&TwoChartTower> {
        Some(&self.section)
    }

    fn transport(
        &self,
        _earlier: &u32,
        _later: &u32,
        _chart: &TwoCharts,
        face: &BigUint,
    ) -> Result<BigUint, TubeRefusal<u32, TwoCharts, BigUint>> {
        Ok(Self::flip(face))
    }
}

/// The swap of two incomparable charts, carrying the halved face and retaining the dropped bit.
///
/// Lean counterpart: `Transport/ContinuingTube.lean::lossySwapMigration`, with
/// `lossySwapMigration_connectsIncomparableCharts`, `lossySwapMigration_face_not_injective`,
/// `lossySwapMigration_no_reverse_passage` and
/// `lossySwapMigration_residual_restores_the_reverse_passage`. It is the fourth cell of
/// `lossiness_is_independent_of_being_a_wormhole`: a passage that is **both** lossy and a wormhole,
/// beside `padicHalfMigration` (lossy, not a wormhole) and `swapMigration` (a wormhole, not lossy).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct LossySwapMigration {
    tower: TwoChartTower,
}

impl LossySwapMigration {
    /// The lossy swap of the two-chart tower.
    pub fn new() -> Self {
        Self {
            tower: TwoChartTower,
        }
    }
}

impl Migration for LossySwapMigration {
    type Source = TwoChartTower;
    type Target = TwoChartTower;

    fn source_tower(&self) -> &TwoChartTower {
        &self.tower
    }

    fn target_tower(&self) -> &TwoChartTower {
        &self.tower
    }

    fn index(&self, target_chart: &TwoCharts) -> TwoCharts {
        match target_chart {
            TwoCharts::Left => TwoCharts::Right,
            TwoCharts::Right => TwoCharts::Left,
        }
    }

    fn face(
        &self,
        _target_chart: &TwoCharts,
        source_face: &BigUint,
    ) -> MigrationOutcome<Self, BigUint> {
        Ok(source_face / BigUint::from(2u32))
    }
}

impl ResidualMigration for LossySwapMigration {
    type Residual = BigUint;

    fn residual(
        &self,
        _target_chart: &TwoCharts,
        source_face: &BigUint,
    ) -> MigrationOutcome<Self, BigUint> {
        Ok(source_face % BigUint::from(2u32))
    }

    fn reopen(
        &self,
        _target_chart: &TwoCharts,
        target_face: &BigUint,
        residual: &BigUint,
    ) -> MigrationOutcome<Self, BigUint> {
        Ok(target_face * BigUint::from(2u32) + residual)
    }
}

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
