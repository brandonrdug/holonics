//! The continuing tube: a tower is the transverse section of a tube, and a wormhole is exact.
//!
//! [definition] This is the longitudinal axis of the Holon core's restriction facet `π`
//! ([`crate::restriction`]): the two-axis commuting square of a stationed tower, its circuit
//! holonomy and the wormhole receipt. It moved here from
//! `crates/holonic-engine/src/continuing_tube.rs`, which re-exports every item at its old path and
//! keeps the layers that read a tube through an engine receiver (the grain and presentation tubes,
//! the two-axis horizon, the defect profile and the route plan).
//!
//! [definition] **One square defect.** The per-face [`SquareDefect`] returned here is the
//! pointwise chart of the operator [`crate::restriction::SquareDefect`] `π A_fine − A_coarse π`:
//! at a linear tube ([`crate::restriction::LinearTube`]) the difference of its two routes at a
//! fine face `x` is exactly that operator applied to `x`
//! ([`SquareDefect::route_difference`]), and [`SquareVerdict::descent`] reads the verdict as the
//! core [`crate::restriction::Descent`].
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
//! | `constantTube`, `padicTube` | [`ConstantTube`] over `tower::ResidueTower` |
//! | `padicTube_crossSection_branching` | `tower::ResidueTower::split_fibre` (cited, not rebuilt) |
//!
//! One name this module also cites belongs to another Lean owner and is therefore not a row of that
//! table: `Foundation/ContinuingTower.lean::Migration.ConnectsIncomparableCharts` (the condition
//! `Wormhole.crosses` carries).
//!
//! # What a tube is here
//!
//! A tube has two axes. The **transverse** axis is the [`crate::restriction::tower::Tower`]
//! presented at each station: the aperture/grain/precision ladder, with `restrict` the only
//! transport. The **longitudinal** axis is the station order, with [`StationedTower::transport`]
//! the passage along it. The one law that joins them is that the two commute, and
//! [`check_commuting_square`] asks it over a declared aperture and returns a [`SquareVerdict`] —
//! never a repair.
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
//! No float decides anything. Faces and residuals are the underlying towers' exact carriers.
//! Three things are caller-declared and every one of them is bounded before any loop or allocation
//! uses it: the chart aperture ([`DECLARED_CHART_CEILING`]), the face population
//! ([`DECLARED_FACE_CEILING`]) and the circuit word ([`DECLARED_CIRCUIT_CEILING`]). Exceeding one
//! is a typed refusal, never a panic and never a silent truncation. Every receipt names exactly
//! what was checked; the receipt is the scope of the claim and is not a proof of the law.

use std::fmt::{self, Debug};

use num_bigint::BigUint;
use num_traits::One;
use relational_geometry::Rat;

use crate::restriction::Descent;

use crate::restriction::tower::{
    ChartRoute, Migration, MigrationOutcome, MigrationSourceIndex, MigrationTargetIndex,
    ResidualMigration, Tower, TowerRefusal, TwoChartTower, TwoCharts, check_index_routes,
};

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
/// copy a face whole — `continuing_tube::GrainReadingTube` (engine) clones its face map on every selection — so the second
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
pub fn declared_work(factors: &[usize]) -> Option<usize> {
    factors.iter().try_fold(1usize, |carried, factor| {
        carried.checked_mul((*factor).max(1))
    })
}

/// The total exact population of a declared face list, bounded before any transport runs.
///
/// The caller's own count is the number of `(chart, face)` pairs; this is the number of exact
/// entries inside them, which is what a transport that copies a face whole actually moves. The sum
/// is formed with `checked_add`, so an overflowing declaration is refused rather than wrapped.
pub fn total_face_population<T: StationedTower>(
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
    /// the caller counted them in: `continuing_tube::GrainReadingTube` (engine)'s selection clones a whole face map, so the
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

    /// **The verdict read as the core descent**: `Commutes` is the witness, `Defect` the typed
    /// defect retaining both routes (`Transport/ContinuingTube.lean::squareVerdict_total`).
    pub fn descent(self) -> Descent<CommutingSquares<S, I>, SquareDefect<S, I, F>> {
        match self {
            Self::Commutes(receipt) => Descent::Witness(receipt),
            Self::Defect(witness) => Descent::Defect(witness),
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

impl<S, I> SquareDefect<S, I, Vec<Rat>> {
    /// **The pointwise chart of the operator defect**: at an exact linear face, the difference of
    /// the two routes `π A_fine x − A_coarse π x`, which is
    /// [`crate::restriction::SquareDefect::at`] at the source face
    /// (`Holon/Restriction.lean::squareDefect_mulVec_eq_zero_iff`; tested on
    /// [`crate::restriction::LinearTube`]).
    pub fn route_difference(&self) -> Vec<Rat> {
        crate::scalar::sub(
            &self.transported_then_restricted,
            &self.restricted_then_transported,
        )
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
