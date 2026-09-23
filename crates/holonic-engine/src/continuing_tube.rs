//! The continuing tube over engine material: the grain and presentation tubes.
//!
//! [definition] The tube's own carrier law — [`StationedTower`], the two-axis commuting square
//! ([`check_commuting_square`], [`SquareVerdict`], [`SquareDefect`]), circuit holonomy and the
//! wormhole receipt — moved to `crates/holonic-core/src/restriction/tube.rs`
//! (`holonic_core::restriction::tube`) in phase 6 of
//! `docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md`, and the two-axis horizon, the defect
//! profile and the route plan followed in phase 7 to `holonic_core::restriction::tube::horizon`,
//! once `receiver_release`'s `Horizon`, width and `ExactFace` and `relation_ladder`'s `Rung` became
//! core receiver faces (`holonic_core::law::receiver`). Every moved item is re-exported here at
//! its old path. What stays is the tubes whose sections are engine presentations: the grain tube
//! over `grain_tower`, the presentation tube over `physical_constraint_complex`, and the grain
//! contact receiver.
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
use std::fmt::Debug;

use num_bigint::BigInt;
use relational_geometry::Rat;

pub use holonic_core::restriction::tube::{
    CircuitDefect, CommutingSquares, ConstantTube, DECLARED_CHART_CEILING,
    DECLARED_CIRCUIT_CEILING, DECLARED_FACE_CEILING, DECLARED_WORK_CEILING, FlipTube,
    HolonomyVerdict, IdentityCircuit, LossySwapMigration, SquareDefect, SquareVerdict,
    StationedTower, TubeFace, TubeHolonomyVerdict, TubeIndex, TubeOutcome, TubeRefusal,
    TubeRefusalOf, TubeSquareVerdict, TubeStation, WormholeReceipt, WormholeRefusal,
    check_circuit_holonomy, check_commuting_square, wormhole_receipt,
};

use crate::continuing_tower::TowerRefusal;
use crate::grain_tower::{
    ApertureRelation, FineNativeDeclaration, Grain, GrainAddress, GrainCell, GrainFace,
    GrainRefusal, GrainSelection, GrainTower,
};
use crate::physical_constraint_complex::ContactClass;
use crate::receiver_release::{ExactFace, WidthRefusal};

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
// T5 — the two-axis horizon, the defect profile and the route plan (moved to the core)
// =============================================================================================

/// [definition] **The horizon, profile and route layers moved to the core** (plan phase 7): once
/// `receiver_release`'s `Horizon`, width and `ExactFace` and `relation_ladder`'s `Rung` became core
/// receiver faces (`holonic_core::law::receiver`), these layers had no engine dependency left and
/// joined the core tube at `holonic_core::restriction::tube::horizon`. Every item is re-exported
/// here at its existing path.
pub use holonic_core::restriction::tube::horizon::{
    CrossRankPassage, CrossedSquare, DECLARED_CANDIDATE_CEILING, DECLARED_REACH_CEILING,
    DECLARED_ROUTE_CEILING, DECLARED_ROUTE_LENGTH_CEILING, DECLARED_SEARCH_CEILING, DefectProfile,
    FaceReading, HorizonDeclaration, HorizonOutcome, HorizonReach, HorizonRefusal,
    HorizonRefusalOf, IndexDirection, IndexReading, Observer, Plurality, ReachEntry, Route,
    RouteBound, RouteMove, RoutePlan, RouteSet, SquareReading, TubeDefectProfile,
    TubeHorizonDeclaration, TubeHorizonReach, TubeObserver, TubeRoutePlan, classify_cross_rank,
    defect_profile, horizon_reach, index_distance, plan_routes, two_axis_width,
};

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
