//! The grain tower `Component ⊑ Residue ⊑ Atom`, its restriction as a non-invertible
//! [`Transition`], and the typed [`ApertureRelation`] that says what a coarse receiver at a
//! declared aperture actually preserves.
//!
//! # What this repairs
//!
//! [established-bounded; measured] `crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE` selects
//! the `CA` atom of every residue. Every non-alpha-carbon occurrence is discarded before anything is founded, so no
//! atom-grain face is ever constructed and the atom→residue restriction is *asserted by the act of
//! selection* rather than built. This module builds it, and makes the coarse receiver's standing a
//! declared, typed, witnessed object instead of a side effect of a filter.
//!
//! Two different maps are involved and they are not the same map:
//!
//! * **The restriction** [`GrainFace::restricted`] — a coarse pair carries the *join* of every fine
//!   pair under it over the class order `Outside < Open < Inside`. This is the tower's own
//!   `restrict`, it satisfies `restrict_refl` and `restrict_trans`, and it is lawful by
//!   construction.
//! * **The selection** [`GrainSelection`] — the coarse pair carries the class of *one declared
//!   representative* fine pair. This is what the `CA` filter enacts. It is a genuine
//!   [`Transition`] of the atom-grain face, but it is **not** the restriction, and at equal
//!   aperture it is not a restriction of any aperture.
//!
//! The relation between them is never implicit: [`GrainTower::found`] demands an
//! [`ApertureRelation`] and the relation travels with the tower.
//!
//! # The paired Lean owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/GrainRestriction.lean`, namespace
//! `Soma.Holonics.Foundation.GrainRestriction`, which names this file and every item below. The
//! citation is bidirectional on purpose.
//!
//! | Lean declaration | Rust owner |
//! |---|---|
//! | `Grain`, `Grain.rank`, its `Preorder` instance | [`Grain`], [`Grain::refines`] |
//! | `classRank`, `classJoin`, `classJoin_assoc`, `classJoin_comm`, `classJoin_idem`, `classJoin_outside`, `classJoin_eq_inside_iff`, `foldr_classJoin_eq_inside_iff` | [`join_contact_class`], [`contact_class_rank`] |
//! | `FineInside`, `FineAdmissible` | [`GrainFace::restricted`] (the `Inside`/non-`Outside` arms) |
//! | `selectionReading` | [`GrainSelection`] as a [`Transition`] (`apply`) |
//! | `selection_inside_implies_fine_inside` | [`GrainCensus::coarse_only_inside`] is checked to be `0`, never assumed |
//! | `equal_aperture_is_not_lawful`, `selection_is_insufficient_for_the_fine_reading` | [`GrainCensus::fine_only_inside`] |
//! | `selectionTower`, `selectionTower_restrict` | `impl Tower for GrainTower`, `continuing_tower::check_restriction_laws` |
//! | `selectionTransition`, `grain_residual_reopens_the_source` | `impl Transition for GrainSelection`, [`Transition::check_reopen`] |
//! | `fineReading_factors` | [`GrainSelection::reopen_fine_reading`] |
//! | `residual_separates_fineOnly` | [`GrainSelection::separating_residuals`] on the deletion witness |
//! | `PseudoDistance`, `GrainRadius`, `coarse_distance_le_fine_aperture_add_radii` | [`CoarseReading::lower_grain_radius`], [`certified_coarse_aperture_squared`] |
//! | `ApertureRelation` (three constructors, no default) | [`ApertureRelation`] |
//! | `inflated_carries_every_fine_contact` | [`InflationWitness::measure`], [`InflationWitness::check_declared`] |
//! | `independent_is_mutual_insufficiency` | [`IndependenceDeclaration::declare`] |
//! | `nativeFine_refusal_is_a_residual_difference` | [`FineNativeDeclaration::admit_coarse`] |
//! | `equal_aperture_is_not_lawful` | the measured `fine_only_inside > 0` receipt |
//! | `open_admission_is_not_a_residual`, `grain_residual_and_open_class_are_two_objects`, `residual_does_not_close_an_open_reading`, `narrower_interval_decides` | the residual/open verdict; see **The residual and the open class** |
//!
//! # The residual and the open class are two objects
//!
//! [proved-derived; formal-checked] Both are content a coarse receiver fails to carry, and they are
//! **not** instances of one object.
//!
//! * A **grain residual** ([`GrainResidual`], [`SelectionResidual`]) is a *function of the source*:
//!   `residual : Source → Residual`, and `reopen(apply(x), residual(x)) = x` exactly. It is content
//!   the receiver *had and dropped*. Retaining it removes the loss.
//! * The **`Open` class** of [`crate::physical_constraint_grading`] is a *value of the target*: it
//!   is what the coarse face returns at that pair. `Foundation/AperturedGradedComplex.lean::
//!   openContact_is_plural` says two resolutions of the same source disagree, so **no** function of
//!   the source returns its admission — there is no `residual` to evaluate. That is
//!   `Foundation/GrainRestriction.lean::open_admission_is_not_a_residual`.
//!
//! The consequence is executable, not rhetorical. Reopening a face with its residual returns the
//! source *including its open readings*: a residual cannot close an open class
//! (`residual_does_not_close_an_open_reading`). What closes one is a strictly narrower exact
//! interval — a different source on the **precision** axis of the carrier's index — or an exterior
//! declaration, which enlarges the source. The grain residual lives on the **grain** axis. The
//! tower's `restrict` has no component along the precision axis, which is exactly why the `Open`
//! class does not transport between grains: it is measured below as
//! [`GrainCensus::open_shared`] = 0 over all 70,632 pairs of the M5 fixture, while both grains
//! carry an open pair of their own.
//!
//! # What is exact
//!
//! No float decides a contact, a restriction, a residual, an inflation or a receipt. Coordinates
//! enter as integer numerators over one declared denominator ([`ScaledOccurrence`]) — the same
//! exact wire the M5 driver hands the card — and every published aperture, radius and ratio is a
//! `holonics::geometry::Rat`. [`ScaledOccurrence::position`] recovers the exact
//! [`CoordinateBox3`] so that [`DistanceAperture::classify`] can re-derive any classification this
//! module produced.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use holonics::geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonics::restriction::tower::{
    ReopenReceipt, Tower, TowerRefusal, TowerRestrictTransition, Transition,
};
use holonics::exact_value::ExactInterval;
use crate::physical_constraint_complex::{ContactClass, CoordinateBox3, DistanceAperture};

/// The grain axis of the carrier's index. `Component` is coarsest and `Atom` finest, so the derived
/// order is the refinement order: `Component ≤ Residue ≤ Atom`.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::Grain`, whose `Preorder` instance is the
/// same order through `Grain.rank`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Grain {
    /// One presented chain, entity or component.
    Component,
    /// One monomer of a component.
    Residue,
    /// One atom of a monomer. The finest grain this tower presents.
    Atom,
}

impl Grain {
    /// The three grains in refinement order, coarsest first.
    pub const ASCENDING: [Grain; 3] = [Grain::Component, Grain::Residue, Grain::Atom];

    /// Whether `fine` refines `coarse`.
    ///
    /// Lean counterpart: `Grain.rank` and the `Preorder` it induces; `Tower.Refines` of
    /// `Foundation/ContinuingTower.lean` at this index.
    pub fn refines(coarse: Grain, fine: Grain) -> bool {
        coarse <= fine
    }

    /// `0`, `1`, `2` for `Component`, `Residue`, `Atom`.
    ///
    /// Lean counterpart: `Grain.rank`.
    pub fn rank(self) -> u8 {
        match self {
            Grain::Component => 0,
            Grain::Residue => 1,
            Grain::Atom => 2,
        }
    }
}

/// One occurrence addressed at every grain at once.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct GrainAddress {
    /// Which presented component.
    pub component: u32,
    /// Which monomer of that component, in presentation order.
    pub residue: u32,
    /// Which atom of that monomer, in presentation order.
    pub atom: u32,
}

impl GrainAddress {
    /// Build an address.
    pub fn new(component: u32, residue: u32, atom: u32) -> Self {
        Self {
            component,
            residue,
            atom,
        }
    }

    /// The cell this address presents at one grain. Coordinates below the grain are dropped, which
    /// is what makes the projection a genuine coarse graining and not a relabelling.
    ///
    /// Lean counterpart: the projection `π : Fine → Coarse` of
    /// `Foundation/GrainRestriction.lean`.
    pub fn cell(&self, grain: Grain) -> GrainCell {
        match grain {
            Grain::Component => GrainCell {
                grain,
                component: self.component,
                residue: 0,
                atom: 0,
            },
            Grain::Residue => GrainCell {
                grain,
                component: self.component,
                residue: self.residue,
                atom: 0,
            },
            Grain::Atom => GrainCell {
                grain,
                component: self.component,
                residue: self.residue,
                atom: self.atom,
            },
        }
    }
}

/// The cell an address presents at one grain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct GrainCell {
    /// Which grain this cell belongs to.
    pub grain: Grain,
    /// The component coordinate.
    pub component: u32,
    /// The residue coordinate, zero below `Residue` grain.
    pub residue: u32,
    /// The atom coordinate, zero below `Atom` grain.
    pub atom: u32,
}

impl GrainCell {
    /// The coarser cell this one presents.
    pub fn project(&self, coarse: Grain) -> Result<GrainCell, GrainRefusal> {
        if !Grain::refines(coarse, self.grain) {
            return Err(GrainRefusal::NotASubGrain {
                coarse,
                fine: self.grain,
            });
        }
        Ok(GrainAddress::new(self.component, self.residue, self.atom).cell(coarse))
    }
}

/// A canonical unordered pair of cells at one grain. A pair is an incidence question, and the
/// question is the same whichever endpoint is presented first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct GrainPair {
    /// The smaller endpoint under the cell order.
    pub lower: GrainCell,
    /// The larger endpoint.
    pub upper: GrainCell,
}

impl GrainPair {
    /// Canonicalize a presented pair. A collapsed pair and a pair whose endpoints sit at different
    /// grains are refused by name.
    pub fn new(left: GrainCell, right: GrainCell) -> Result<Self, GrainRefusal> {
        if left.grain != right.grain {
            return Err(GrainRefusal::MixedGrainPair {
                left: left.grain,
                right: right.grain,
            });
        }
        if left == right {
            return Err(GrainRefusal::CollapsedPair { cell: left });
        }
        Ok(if left < right {
            Self {
                lower: left,
                upper: right,
            }
        } else {
            Self {
                lower: right,
                upper: left,
            }
        })
    }

    /// The grain both endpoints belong to.
    pub fn grain(&self) -> Grain {
        self.lower.grain
    }

    /// The coarser pair this one presents, or `None` when both endpoints fall inside one coarse
    /// cell. A collapsed projection is not an error and it is not silently dropped: the coarse face
    /// cannot carry it at all, so [`GrainResidual::internal`] retains it whole.
    pub fn project(&self, coarse: Grain) -> Result<Option<GrainPair>, GrainRefusal> {
        let lower = self.lower.project(coarse)?;
        let upper = self.upper.project(coarse)?;
        if lower == upper {
            return Ok(None);
        }
        Ok(Some(GrainPair::new(lower, upper)?))
    }
}

/// `Outside = 0 < Open = 1 < Inside = 2`.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::classRank`.
pub fn contact_class_rank(class: ContactClass) -> u8 {
    match class {
        ContactClass::Outside => 0,
        ContactClass::Open => 1,
        ContactClass::Inside => 2,
    }
}

/// The join of the class order. Restriction to a coarser grain takes this join over the block: the
/// coarse pair is `Inside` when some fine pair is, `Open` when none is `Inside` and some is `Open`,
/// and `Outside` only when every fine pair is.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::classJoin`, with `classJoin_assoc`,
/// `classJoin_comm`, `classJoin_idem`, `classJoin_outside` and `foldr_classJoin_eq_inside_iff`.
pub fn join_contact_class(left: ContactClass, right: ContactClass) -> ContactClass {
    if contact_class_rank(left) >= contact_class_rank(right) {
        left
    } else {
        right
    }
}

/// The face at one grain: the exact class of every pair the presentation did **not** decide
/// `Outside`.
///
/// `Outside` is the default of a declared cross population and is never stored, so two faces are
/// equal exactly when they admit the same pairs with the same classes. The declared population
/// itself is a separate count and travels in [`GrainCensus::pairs`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "GrainFaceWire")]
pub struct GrainFace {
    grain: Grain,
    classified: BTreeMap<GrainPair, ContactClass>,
}

#[derive(Deserialize)]
struct GrainFaceWire {
    grain: Grain,
    classified: BTreeMap<GrainPair, ContactClass>,
}

impl TryFrom<GrainFaceWire> for GrainFace {
    type Error = GrainRefusal;

    fn try_from(wire: GrainFaceWire) -> Result<Self, Self::Error> {
        GrainFace::founded(wire.grain, wire.classified)
    }
}

impl GrainFace {
    /// An empty face: every pair `Outside`.
    pub fn empty(grain: Grain) -> Self {
        Self {
            grain,
            classified: BTreeMap::new(),
        }
    }

    /// Build a face from its non-`Outside` readings. An `Outside` reading is refused rather than
    /// stored, because storing it would make two equal faces unequal.
    pub fn founded(
        grain: Grain,
        readings: impl IntoIterator<Item = (GrainPair, ContactClass)>,
    ) -> Result<Self, GrainRefusal> {
        let mut classified = BTreeMap::new();
        for (pair, class) in readings {
            if pair.grain() != grain {
                return Err(GrainRefusal::PairNotAtGrain {
                    expected: grain,
                    found: pair.grain(),
                });
            }
            if class == ContactClass::Outside {
                return Err(GrainRefusal::OutsideReadingStored { pair });
            }
            let entry = classified.entry(pair).or_insert(class);
            *entry = join_contact_class(*entry, class);
        }
        Ok(Self { grain, classified })
    }

    /// The grain this face is read at.
    pub fn grain(&self) -> Grain {
        self.grain
    }

    /// Every non-`Outside` reading.
    pub fn classified(&self) -> &BTreeMap<GrainPair, ContactClass> {
        &self.classified
    }

    /// The class at one pair. A pair the face does not carry is `Outside`.
    pub fn class(&self, pair: &GrainPair) -> ContactClass {
        self.classified
            .get(pair)
            .copied()
            .unwrap_or(ContactClass::Outside)
    }

    /// How many pairs this face reads `Inside`.
    pub fn inside(&self) -> usize {
        self.classified
            .values()
            .filter(|class| **class == ContactClass::Inside)
            .count()
    }

    /// How many pairs this face reads `Open`.
    pub fn open(&self) -> usize {
        self.classified
            .values()
            .filter(|class| **class == ContactClass::Open)
            .count()
    }

    /// The coarser face this one presents: the join over each coarse pair's block.
    ///
    /// Lean counterpart: `Foundation/GrainRestriction.lean::FineInside` and `FineAdmissible` state
    /// the two arms of this join as existentials over the block.
    pub fn restricted(&self, coarse: Grain) -> Result<GrainFace, GrainRefusal> {
        if !Grain::refines(coarse, self.grain) {
            return Err(GrainRefusal::NotASubGrain {
                coarse,
                fine: self.grain,
            });
        }
        let mut classified: BTreeMap<GrainPair, ContactClass> = BTreeMap::new();
        for (pair, class) in &self.classified {
            let Some(coarse_pair) = pair.project(coarse)? else {
                continue;
            };
            let entry = classified.entry(coarse_pair).or_insert(*class);
            *entry = join_contact_class(*entry, *class);
        }
        Ok(GrainFace {
            grain: coarse,
            classified,
        })
    }

    /// The same face with a named population of pairs deleted. This is how the necessity half of
    /// `Foundation/ContinuingTower.lean::Transition.residual_separates` is instantiated on measured
    /// data: delete exactly the contacts the coarse receiver never saw and the coarse face is
    /// unchanged while the fine face is not.
    pub fn without(&self, deleted: impl IntoIterator<Item = GrainPair>) -> GrainFace {
        let mut classified = self.classified.clone();
        for pair in deleted {
            classified.remove(&pair);
        }
        GrainFace {
            grain: self.grain,
            classified,
        }
    }
}

/// What the atom→residue restriction drops.
///
/// Lean counterpart: the `Residual` of `Foundation/ContinuingTower.lean::Tower.restrictTransition`,
/// supplied rather than synthesized — the tower's laws say what restriction preserves and never
/// what it drops.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainResidual {
    /// For each coarse pair the coarse face admits, the fine pairs under it and their exact
    /// classes. A coarse pair the restriction left `Outside` has no block, because every fine pair
    /// under it is `Outside` — that is the only compression the restriction law licenses.
    pub blocks: BTreeMap<GrainPair, BTreeMap<GrainPair, ContactClass>>,
    /// Fine pairs whose endpoints fall inside one coarse cell. The coarse face cannot carry them at
    /// all, so they are retained whole rather than dropped.
    pub internal: BTreeMap<GrainPair, ContactClass>,
}

impl GrainResidual {
    /// How many fine readings this residual retains.
    pub fn retained(&self) -> usize {
        self.blocks.values().map(BTreeMap::len).sum::<usize>() + self.internal.len()
    }
}

/// The grain tower of one presentation: the atom-grain face is presented and every coarser face is
/// founded by restriction.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::selectionTower`, which is one
/// `Foundation/ContinuingTower.lean::Tower` over `Grain`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "GrainTowerWire")]
pub struct GrainTower {
    /// The schema this tower serializes under.
    pub schema: String,
    /// Exterior source lineage, retained as testimony.
    pub presentation_lineage: String,
    relation: ApertureRelation,
    atom_face: GrainFace,
}

#[derive(Deserialize)]
struct GrainTowerWire {
    schema: String,
    presentation_lineage: String,
    relation: ApertureRelation,
    atom_face: GrainFace,
}

impl TryFrom<GrainTowerWire> for GrainTower {
    type Error = GrainRefusal;

    fn try_from(wire: GrainTowerWire) -> Result<Self, Self::Error> {
        if wire.schema != "holonic-engine.grain-tower.v1" {
            return Err(GrainRefusal::TowerSchemaUnsupported { schema: wire.schema });
        }
        GrainTower::found(wire.presentation_lineage, wire.relation, wire.atom_face)
    }
}

impl GrainTower {
    /// Found a tower. The [`ApertureRelation`] is required: there is no default, and a coarse
    /// reading with no declared relation is not a reading.
    pub fn found(
        presentation_lineage: impl Into<String>,
        relation: ApertureRelation,
        atom_face: GrainFace,
    ) -> Result<Self, GrainRefusal> {
        if atom_face.grain() != Grain::Atom {
            return Err(GrainRefusal::PairNotAtGrain {
                expected: Grain::Atom,
                found: atom_face.grain(),
            });
        }
        Ok(Self {
            schema: "holonic-engine.grain-tower.v1".to_owned(),
            presentation_lineage: presentation_lineage.into(),
            relation,
            atom_face,
        })
    }

    /// The relation the coarse receiver stands in to the fine one. It travels with the tower.
    pub fn relation(&self) -> &ApertureRelation {
        &self.relation
    }

    /// The presented finest face.
    pub fn atom_face(&self) -> &GrainFace {
        &self.atom_face
    }

    /// The face at one grain, founded by restriction from the atom grain.
    pub fn face(&self, grain: Grain) -> Result<GrainFace, GrainRefusal> {
        self.atom_face.restricted(grain)
    }
}

impl Tower for GrainTower {
    type Index = Grain;
    type Face = GrainFace;

    fn refines(&self, coarse: &Grain, fine: &Grain) -> bool {
        Grain::refines(*coarse, *fine)
    }

    fn carries(&self, chart: &Grain, face: &GrainFace) -> bool {
        face.grain() == *chart
    }

    fn restrict(
        &self,
        coarse: &Grain,
        fine: &Grain,
        face: &GrainFace,
    ) -> Result<GrainFace, TowerRefusal<Grain, GrainFace>> {
        if !Grain::refines(*coarse, *fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if face.grain() != *fine {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *fine,
                face: face.clone(),
            });
        }
        face.restricted(*coarse)
            .map_err(|_| TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            })
    }
}

impl TowerRestrictTransition for GrainTower {
    type RestrictionResidual = GrainResidual;

    fn restriction_residual(
        &self,
        coarse: &Grain,
        fine: &Grain,
        fine_face: &GrainFace,
    ) -> Result<GrainResidual, TowerRefusal<Grain, GrainFace>> {
        if !Grain::refines(*coarse, *fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if fine_face.grain() != *fine {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *fine,
                face: fine_face.clone(),
            });
        }
        let mut residual = GrainResidual::default();
        for (pair, class) in fine_face.classified() {
            match pair.project(*coarse) {
                Ok(Some(coarse_pair)) => {
                    residual
                        .blocks
                        .entry(coarse_pair)
                        .or_default()
                        .insert(*pair, *class);
                }
                Ok(None) => {
                    residual.internal.insert(*pair, *class);
                }
                Err(_) => {
                    return Err(TowerRefusal::NotARefinement {
                        coarse: *coarse,
                        fine: *fine,
                    });
                }
            }
        }
        Ok(residual)
    }

    fn restriction_reopen(
        &self,
        coarse: &Grain,
        fine: &Grain,
        coarse_face: &GrainFace,
        residual: &GrainResidual,
    ) -> Result<GrainFace, TowerRefusal<Grain, GrainFace>> {
        if !Grain::refines(*coarse, *fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if coarse_face.grain() != *coarse {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *coarse,
                face: coarse_face.clone(),
            });
        }
        let mut classified = BTreeMap::new();
        for (coarse_pair, block) in &residual.blocks {
            if coarse_face.class(coarse_pair) == ContactClass::Outside {
                // The residual names a block under a coarse pair the coarse face refused. The
                // restriction can never produce that, so it is a refusal and not a silent repair.
                return Err(TowerRefusal::IncompatibleWitness {
                    coarse: *coarse,
                    fine: *fine,
                    restricted: coarse_face.clone(),
                    witness: GrainFace::empty(*coarse),
                });
            }
            for (pair, class) in block {
                classified.insert(*pair, *class);
            }
        }
        for (pair, class) in &residual.internal {
            classified.insert(*pair, *class);
        }
        Ok(GrainFace {
            grain: *fine,
            classified,
        })
    }
}

/// A coarse receiver that reads the fine face only at one declared representative per coarse cell.
///
/// This is the receiver `crates/holonic-life/examples/m5/cif.rs::REPRESENTATIVE` enacts by keeping
/// only the `CA` atom of each residue: the restriction is asserted by the act of selection. Presented here it is a
/// genuine [`Transition`] of the atom-grain face — `apply` is the coarse reading, `residual` is
/// every reading the selection never looked at, and `reopen` puts them back together exactly.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::selectionTransition`, with
/// `grain_residual_reopens_the_source`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "GrainSelectionWire")]
pub struct GrainSelection {
    /// Exterior lineage of the selection rule, retained as testimony — `"label_atom_id == CA"` is
    /// a declaration about the presentation, never a mathematical property of the grain.
    pub lineage: String,
    coarse: Grain,
    fine: Grain,
    representative: BTreeMap<GrainCell, GrainCell>,
    inverse: BTreeMap<GrainCell, GrainCell>,
}

#[derive(Deserialize)]
struct GrainSelectionWire {
    lineage: String,
    coarse: Grain,
    fine: Grain,
    representative: BTreeMap<GrainCell, GrainCell>,
    inverse: BTreeMap<GrainCell, GrainCell>,
}

impl TryFrom<GrainSelectionWire> for GrainSelection {
    type Error = GrainRefusal;

    fn try_from(wire: GrainSelectionWire) -> Result<Self, Self::Error> {
        if !Grain::refines(wire.coarse, wire.fine) {
            return Err(GrainRefusal::NotASubGrain {
                coarse: wire.coarse,
                fine: wire.fine,
            });
        }
        for (coarse_cell, fine_cell) in &wire.representative {
            if coarse_cell.grain != wire.coarse || fine_cell.grain != wire.fine {
                return Err(GrainRefusal::PairNotAtGrain {
                    expected: wire.fine,
                    found: fine_cell.grain,
                });
            }
            if fine_cell.project(wire.coarse)? != *coarse_cell {
                return Err(GrainRefusal::RepeatedRepresentative {
                    cell: *coarse_cell,
                });
            }
            if wire.inverse.get(fine_cell) != Some(coarse_cell) {
                return Err(GrainRefusal::SelectionWireInconsistent);
            }
        }
        if wire.inverse.len() != wire.representative.len()
            || wire.inverse.iter().any(|(fine, coarse)| {
                wire.representative.get(coarse) != Some(fine)
            })
        {
            return Err(GrainRefusal::SelectionWireInconsistent);
        }
        Ok(Self {
            lineage: wire.lineage,
            coarse: wire.coarse,
            fine: wire.fine,
            representative: wire.representative,
            inverse: wire.inverse,
        })
    }
}

impl GrainSelection {
    /// Declare one representative fine occurrence per coarse cell.
    ///
    /// Two representatives for one coarse cell, or a representative whose address does not lie in
    /// the cell it represents, are refused by name.
    pub fn declare(
        lineage: impl Into<String>,
        coarse: Grain,
        fine: Grain,
        representatives: impl IntoIterator<Item = GrainAddress>,
    ) -> Result<Self, GrainRefusal> {
        if !Grain::refines(coarse, fine) {
            return Err(GrainRefusal::NotASubGrain { coarse, fine });
        }
        let mut representative = BTreeMap::new();
        let mut inverse = BTreeMap::new();
        for address in representatives {
            let coarse_cell = address.cell(coarse);
            let fine_cell = address.cell(fine);
            if representative.insert(coarse_cell, fine_cell).is_some() {
                return Err(GrainRefusal::RepeatedRepresentative { cell: coarse_cell });
            }
            if inverse.insert(fine_cell, coarse_cell).is_some() {
                return Err(GrainRefusal::RepeatedRepresentative { cell: fine_cell });
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            coarse,
            fine,
            representative,
            inverse,
        })
    }

    /// The coarse grain this selection reads at.
    pub fn coarse(&self) -> Grain {
        self.coarse
    }

    /// The fine grain it selects from.
    pub fn fine(&self) -> Grain {
        self.fine
    }

    /// How many coarse cells carry a representative.
    pub fn represented(&self) -> usize {
        self.representative.len()
    }

    /// The representative of one coarse cell.
    pub fn representative_of(&self, coarse_cell: &GrainCell) -> Option<&GrainCell> {
        self.representative.get(coarse_cell)
    }

    /// Read the fine restriction off the coarse face together with the residual.
    ///
    /// Lean counterpart: `Foundation/ContinuingTower.lean::Transition.laterReceiverFactors` at this
    /// transition, restated as `Foundation/GrainRestriction.lean::fineReading_factors`. **This is
    /// the deliverable equation**: the coarse face plus the residual reconstructs the fine face,
    /// and nothing else is needed.
    pub fn reopen_fine_reading(
        &self,
        transported: &GrainFace,
        residual: &SelectionResidual,
    ) -> Result<GrainFace, GrainRefusal> {
        self.reopen(transported, residual).restricted(self.coarse)
    }
}

/// What a [`GrainSelection`] never looked at: every non-`Outside` fine reading that is not a pair
/// of representatives, together with every representative pair whose coarse projection collapses.
///
/// Lean counterpart: the `Residual` of `Foundation/GrainRestriction.lean::selectionTransition`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SelectionResidual {
    /// The retained readings, by fine pair.
    pub unselected: BTreeMap<GrainPair, ContactClass>,
}

impl SelectionResidual {
    /// How many fine readings this residual retains.
    pub fn retained(&self) -> usize {
        self.unselected.len()
    }
}

impl Transition for GrainSelection {
    type Source = GrainFace;
    type Target = GrainFace;
    type Residual = SelectionResidual;

    fn apply(&self, source: &GrainFace) -> GrainFace {
        let mut classified = BTreeMap::new();
        for (pair, class) in source.classified() {
            let (Some(lower), Some(upper)) =
                (self.inverse.get(&pair.lower), self.inverse.get(&pair.upper))
            else {
                continue;
            };
            let Ok(coarse_pair) = GrainPair::new(*lower, *upper) else {
                continue;
            };
            classified.insert(coarse_pair, *class);
        }
        GrainFace {
            grain: self.coarse,
            classified,
        }
    }

    fn residual(&self, source: &GrainFace) -> SelectionResidual {
        let mut unselected = BTreeMap::new();
        for (pair, class) in source.classified() {
            let selected = match (self.inverse.get(&pair.lower), self.inverse.get(&pair.upper)) {
                (Some(lower), Some(upper)) => GrainPair::new(*lower, *upper).is_ok(),
                _ => false,
            };
            if !selected {
                unselected.insert(*pair, *class);
            }
        }
        SelectionResidual { unselected }
    }

    fn reopen(&self, target: &GrainFace, residual: &SelectionResidual) -> GrainFace {
        let mut classified = BTreeMap::new();
        for (coarse_pair, class) in target.classified() {
            let (Some(lower), Some(upper)) = (
                self.representative.get(&coarse_pair.lower),
                self.representative.get(&coarse_pair.upper),
            ) else {
                continue;
            };
            let Ok(fine_pair) = GrainPair::new(*lower, *upper) else {
                continue;
            };
            classified.insert(fine_pair, *class);
        }
        for (pair, class) in &residual.unselected {
            classified.insert(*pair, *class);
        }
        GrainFace {
            grain: self.fine,
            classified,
        }
    }
}

/// Where the fine restriction and the coarse reading disagree, at one grain and one aperture.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::selection_inside_implies_fine_inside` is
/// the theorem that [`Self::coarse_only_inside`] is empty; it is **checked** here rather than
/// assumed, so a violation would be returned instead of being impossible to see.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainDisagreement {
    /// The grain both faces were read at.
    pub grain: Grain,
    /// Pairs the fine restriction admits and the coarse reading does not, with the fine class.
    pub fine_only: BTreeMap<GrainPair, ContactClass>,
    /// Pairs the coarse reading ranks strictly above the fine restriction. Theorem: empty for a
    /// selection. Measured, not assumed.
    pub coarse_only: BTreeMap<GrainPair, ContactClass>,
    /// Pairs both faces read the same way, `Outside` excluded.
    pub agreed: usize,
}

impl GrainDisagreement {
    /// Compare a fine restriction with a coarse reading at the same grain.
    pub fn between(fine: &GrainFace, coarse: &GrainFace) -> Result<Self, GrainRefusal> {
        if fine.grain() != coarse.grain() {
            return Err(GrainRefusal::PairNotAtGrain {
                expected: fine.grain(),
                found: coarse.grain(),
            });
        }
        let mut fine_only = BTreeMap::new();
        let mut coarse_only = BTreeMap::new();
        let mut agreed = 0usize;
        let mut pairs: Vec<GrainPair> = fine.classified().keys().copied().collect();
        pairs.extend(coarse.classified().keys().copied());
        pairs.sort_unstable();
        pairs.dedup();
        for pair in pairs {
            let fine_class = fine.class(&pair);
            let coarse_class = coarse.class(&pair);
            match contact_class_rank(fine_class).cmp(&contact_class_rank(coarse_class)) {
                std::cmp::Ordering::Greater => {
                    fine_only.insert(pair, fine_class);
                }
                std::cmp::Ordering::Less => {
                    coarse_only.insert(pair, coarse_class);
                }
                std::cmp::Ordering::Equal => agreed += 1,
            }
        }
        Ok(Self {
            grain: fine.grain(),
            fine_only,
            coarse_only,
            agreed,
        })
    }

    /// The fine-only pairs, as a deletable population. Deleting exactly these from the atom-grain
    /// face leaves the coarse reading unchanged, which is how
    /// `Foundation/ContinuingTower.lean::Transition.residual_separates` is instantiated on measured
    /// data.
    pub fn fine_only_pairs(&self) -> Vec<GrainPair> {
        self.fine_only.keys().copied().collect()
    }
}

/// One cell of the `(coarse class, fine class)` cross tabulation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrosstabCell {
    /// The coarse reading's class word.
    pub coarse: u8,
    /// The fine restriction's class word.
    pub fine: u8,
    /// How many pairs fall here.
    pub pairs: usize,
}

/// The exact pair table of one presentation read at two grains under one aperture.
///
/// This is the fixture of `docs/plans/THE_BIOLOGICAL_ECOLOGY_INSTANTIATES_THE_CARRIER.md` item
/// **B0**, as a first-class return rather than a printed number.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainCensus {
    /// The schema this census serializes under.
    pub schema: String,
    /// Exterior lineage of the presentation and family.
    pub lineage: String,
    /// The grain both readings were taken at.
    pub grain: Grain,
    /// The complete declared pair population, including `Outside`.
    pub pairs: usize,
    /// Pairs the fine restriction reads `Inside`.
    pub fine_inside: usize,
    /// Pairs the fine restriction reads `Open`.
    pub fine_open: usize,
    /// Pairs the coarse reading reads `Inside`.
    pub coarse_inside: usize,
    /// Pairs the coarse reading reads `Open`.
    pub coarse_open: usize,
    /// Fine `Inside`, coarse not `Inside`. The content the coarse receiver drops.
    pub fine_only_inside: usize,
    /// Coarse `Inside`, fine not `Inside`. Zero is a theorem for a selection; it is measured here.
    pub coarse_only_inside: usize,
    /// Pairs both readings leave `Open`. The `Open` class transports exactly when this is not
    /// smaller than each of `fine_open` and `coarse_open`.
    pub open_shared: usize,
    /// The complete `(coarse, fine)` cross tabulation, `Outside` included.
    pub crosstab: Vec<CrosstabCell>,
}

impl GrainCensus {
    /// Measure the table. `pairs` is the declared complete population at `grain`, which the faces
    /// themselves cannot supply because `Outside` is never stored.
    pub fn measure(
        lineage: impl Into<String>,
        pairs: usize,
        fine: &GrainFace,
        coarse: &GrainFace,
    ) -> Result<Self, GrainRefusal> {
        if fine.grain() != coarse.grain() {
            return Err(GrainRefusal::PairNotAtGrain {
                expected: fine.grain(),
                found: coarse.grain(),
            });
        }
        let mut keys: Vec<GrainPair> = fine.classified().keys().copied().collect();
        keys.extend(coarse.classified().keys().copied());
        keys.sort_unstable();
        keys.dedup();
        if keys.len() > pairs {
            return Err(GrainRefusal::PopulationTooSmall {
                declared: pairs,
                classified: keys.len(),
            });
        }
        let mut table: BTreeMap<(u8, u8), usize> = BTreeMap::new();
        let mut open_shared = 0usize;
        let mut fine_only_inside = 0usize;
        let mut coarse_only_inside = 0usize;
        for pair in &keys {
            let fine_class = fine.class(pair);
            let coarse_class = coarse.class(pair);
            *table
                .entry((coarse_class.wire(), fine_class.wire()))
                .or_default() += 1;
            if fine_class == ContactClass::Open && coarse_class == ContactClass::Open {
                open_shared += 1;
            }
            if fine_class == ContactClass::Inside && coarse_class != ContactClass::Inside {
                fine_only_inside += 1;
            }
            if coarse_class == ContactClass::Inside && fine_class != ContactClass::Inside {
                coarse_only_inside += 1;
            }
        }
        *table
            .entry((ContactClass::Outside.wire(), ContactClass::Outside.wire()))
            .or_default() += pairs - keys.len();
        Ok(Self {
            schema: "holonic-engine.grain-census.v1".to_owned(),
            lineage: lineage.into(),
            grain: fine.grain(),
            pairs,
            fine_inside: fine.inside(),
            fine_open: fine.open(),
            coarse_inside: coarse.inside(),
            coarse_open: coarse.open(),
            fine_only_inside,
            coarse_only_inside,
            open_shared,
            crosstab: table
                .into_iter()
                .map(|((coarse, fine), pairs)| CrosstabCell {
                    coarse,
                    fine,
                    pairs,
                })
                .collect(),
        })
    }
}

/// One coarse pair together with the fine class its block carries and the exact coarse
/// squared-distance interval the coarse receiver would read at that pair.
///
/// The two radii are the triangle-inequality certificate of
/// `Foundation/GrainRestriction.lean::coarse_distance_le_fine_aperture_add_radii`: they are the
/// measured grain radii, never assumed constants.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoarseReading {
    /// The coarse pair.
    pub pair: GrainPair,
    /// What the fine restriction reads there.
    pub fine_class: ContactClass,
    /// The exact squared distance between the two representatives.
    pub coarse_squared_distance: ExactInterval,
    /// The fine pair that carries `fine_class`, retained as the witness of why the coarse aperture
    /// must stretch.
    pub forcing_fine_pair: Option<GrainPair>,
    /// An exact rational upper bound on the lower endpoint's grain radius.
    pub lower_grain_radius: Rat,
    /// An exact rational upper bound on the upper endpoint's grain radius.
    pub upper_grain_radius: Rat,
}

/// The inflation a coarse receiver actually needs on one measured presentation, with the pair that
/// forces it.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::inflated_carries_every_fine_contact`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InflationWitness {
    /// Exterior lineage of the measurement.
    pub lineage: String,
    /// The fine receiver's aperture, squared.
    pub fine_aperture_squared: Rat,
    /// The least coarse aperture, squared, that reads every non-`Outside` fine pair `Inside`.
    /// Exact and attained: it is the maximum of an actually measured population and is never
    /// rounded outward for safety.
    pub coarse_aperture_squared: Rat,
    /// Exactly `coarse_aperture_squared / fine_aperture_squared`.
    pub inflation_ratio_squared: Rat,
    /// The pair that attains the maximum.
    pub extremal: CoarseReading,
    /// `(√fine_aperture + r_lower + r_upper)²` at the extremal pair, from its measured radii. The
    /// triangle inequality makes this an upper bound on `coarse_aperture_squared`, which
    /// [`InflationWitness::measure`] checks.
    pub certified_bound_squared: Rat,
    /// How many non-`Outside` fine pairs the inflated aperture carries.
    pub carried: usize,
    /// How many readings were examined.
    pub examined: usize,
}

/// `(root_bound + lower_radius + upper_radius)²`, exactly.
///
/// `root_bound` is a rational upper bound on the fine aperture's square root; [`rational_root_upper_bound`]
/// computes one from the aperture without a float. Lean counterpart:
/// `Foundation/GrainRestriction.lean::coarse_distance_le_fine_aperture_add_radii`, whose conclusion
/// is `d ≤ r_i + α + r_j` in distances.
pub fn certified_coarse_aperture_squared(
    root_bound: &Rat,
    lower_radius: &Rat,
    upper_radius: &Rat,
) -> Rat {
    let total = root_bound + lower_radius + upper_radius;
    &total * &total
}

/// The least rational with the declared denominator whose square is at least `squared`.
///
/// Exact integer arithmetic throughout: this is an upper bound on `√squared` and never a rounded
/// float. A negative argument is refused.
pub fn rational_root_upper_bound(
    squared: &Rat,
    denominator: &BigUint,
) -> Result<Rat, GrainRefusal> {
    if squared.is_negative() {
        return Err(GrainRefusal::NegativeSquare {
            value: squared.clone(),
        });
    }
    if denominator.is_zero() {
        return Err(GrainRefusal::ZeroDenominator);
    }
    let numerator = squared.numer().magnitude() * (denominator * denominator);
    let divisor = squared.denom().magnitude().clone();
    let ceiling = (&numerator + &divisor - BigUint::one()) / &divisor;
    let root = integer_sqrt_ceil(&ceiling);
    Ok(Rat::new(
        BigInt::from(root),
        BigInt::from(denominator.clone()),
    ))
}

fn integer_sqrt_floor(value: &BigUint) -> BigUint {
    if value.is_zero() {
        return BigUint::zero();
    }
    let mut guess = BigUint::one() << value.bits().div_ceil(2);
    loop {
        let next = (&guess + value / &guess) >> 1_u32;
        if next >= guess {
            return guess;
        }
        guess = next;
    }
}

fn integer_sqrt_ceil(value: &BigUint) -> BigUint {
    let floor = integer_sqrt_floor(value);
    if &floor * &floor == *value {
        floor
    } else {
        floor + BigUint::one()
    }
}

impl InflationWitness {
    /// Measure the required inflation. Refuses when no reading carries a non-`Outside` fine class,
    /// because then there is nothing to carry and an inflation would be a guess.
    pub fn measure(
        lineage: impl Into<String>,
        fine_aperture_squared: Rat,
        readings: &[CoarseReading],
    ) -> Result<Self, GrainRefusal> {
        if !fine_aperture_squared.is_positive() {
            return Err(GrainRefusal::NonPositiveAperture {
                value: fine_aperture_squared,
            });
        }
        let mut extremal: Option<&CoarseReading> = None;
        let mut carried = 0usize;
        for reading in readings {
            if reading.fine_class == ContactClass::Outside {
                continue;
            }
            carried += 1;
            let better = match extremal {
                None => true,
                Some(current) => {
                    reading.coarse_squared_distance.upper > current.coarse_squared_distance.upper
                }
            };
            if better {
                extremal = Some(reading);
            }
        }
        let extremal = extremal
            .ok_or(GrainRefusal::NoFineContactToCarry {
                examined: readings.len(),
            })?
            .clone();
        let coarse_aperture_squared = extremal.coarse_squared_distance.upper.clone();
        let inflation_ratio_squared = &coarse_aperture_squared / &fine_aperture_squared;
        let root_denominator = BigUint::from(1_000_000_u32);
        let root_bound = rational_root_upper_bound(&fine_aperture_squared, &root_denominator)?;
        let certified_bound_squared = certified_coarse_aperture_squared(
            &root_bound,
            &extremal.lower_grain_radius,
            &extremal.upper_grain_radius,
        );
        if certified_bound_squared < coarse_aperture_squared {
            return Err(GrainRefusal::CertificateBelowMeasurement(Box::new(
                CertificateRefutation {
                    pair: extremal.pair,
                    certified: certified_bound_squared,
                    measured: coarse_aperture_squared,
                },
            )));
        }
        Ok(Self {
            lineage: lineage.into(),
            fine_aperture_squared,
            coarse_aperture_squared,
            inflation_ratio_squared,
            extremal,
            certified_bound_squared,
            carried,
            examined: readings.len(),
        })
    }

    /// Check a coarse aperture a caller declared. An aperture below the measured requirement is
    /// refused with the pair that refutes it; nothing is quietly raised.
    pub fn check_declared(
        &self,
        declared_coarse_aperture_squared: &Rat,
    ) -> Result<(), GrainRefusal> {
        if declared_coarse_aperture_squared < &self.coarse_aperture_squared {
            return Err(GrainRefusal::CoarseApertureTooSmall(Box::new(
                ApertureRefutation {
                    pair: self.extremal.pair,
                    required_squared: self.coarse_aperture_squared.clone(),
                    declared_squared: declared_coarse_aperture_squared.clone(),
                },
            )));
        }
        Ok(())
    }
}

/// A declaration that the two grains are separate receivers and neither restricts the other.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::independent_is_mutual_insufficiency`, which
/// states independence as a pair of `Foundation/Receiver.lean::ReceiverInsufficiency` witnesses,
/// one in each direction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IndependenceDeclaration {
    /// Exterior lineage of the declaration.
    pub lineage: String,
    /// The fine receiver's aperture, squared.
    pub fine_aperture_squared: Rat,
    /// The coarse receiver's aperture, squared.
    pub coarse_aperture_squared: Rat,
    /// Pairs the fine reading admits and the coarse one does not.
    pub fine_only: usize,
    /// Pairs the coarse reading admits and the fine one does not.
    pub coarse_only: usize,
    /// One pair from each separating population, retained as the witness.
    pub separators: Vec<GrainPair>,
}

impl IndependenceDeclaration {
    /// Declare independence from a measured disagreement. Independence with no measured separation
    /// is refused: if the two readings agree, "independent" is a false description and the caller
    /// owes a restriction instead.
    pub fn declare(
        lineage: impl Into<String>,
        fine_aperture_squared: Rat,
        coarse_aperture_squared: Rat,
        disagreement: &GrainDisagreement,
    ) -> Result<Self, GrainRefusal> {
        if disagreement.fine_only.is_empty() && disagreement.coarse_only.is_empty() {
            return Err(GrainRefusal::IndependenceWithoutSeparation);
        }
        let mut separators = Vec::new();
        if let Some(pair) = disagreement.fine_only.keys().next() {
            separators.push(*pair);
        }
        if let Some(pair) = disagreement.coarse_only.keys().next() {
            separators.push(*pair);
        }
        Ok(Self {
            lineage: lineage.into(),
            fine_aperture_squared,
            coarse_aperture_squared,
            fine_only: disagreement.fine_only.len(),
            coarse_only: disagreement.coarse_only.len(),
            separators,
        })
    }
}

/// A declaration that the fine grain is the receiver and a coarse reading is admitted only where it
/// agrees.
///
/// Lean counterpart:
/// `Foundation/GrainRestriction.lean::nativeFine_refusal_is_a_residual_difference`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FineNativeDeclaration {
    /// Exterior lineage of the declaration.
    pub lineage: String,
    /// The fine receiver's aperture, squared.
    pub fine_aperture_squared: Rat,
}

impl FineNativeDeclaration {
    /// Declare the fine grain native.
    pub fn declare(lineage: impl Into<String>, fine_aperture_squared: Rat) -> Self {
        Self {
            lineage: lineage.into(),
            fine_aperture_squared,
        }
    }

    /// Admit a coarse reading, or refuse at the first pair where it disagrees with the fine
    /// restriction. There is no tolerance and no majority rule.
    pub fn admit_coarse(
        &self,
        fine: &GrainFace,
        coarse: &GrainFace,
    ) -> Result<GrainDisagreement, GrainRefusal> {
        let disagreement = GrainDisagreement::between(fine, coarse)?;
        if let Some((pair, class)) = disagreement.fine_only.iter().next() {
            return Err(GrainRefusal::CoarseReadingDisagrees {
                pair: *pair,
                fine: *class,
                coarse: coarse.class(pair),
            });
        }
        if let Some((pair, class)) = disagreement.coarse_only.iter().next() {
            return Err(GrainRefusal::CoarseReadingDisagrees {
                pair: *pair,
                fine: fine.class(pair),
                coarse: *class,
            });
        }
        Ok(disagreement)
    }
}

/// What relation a coarse receiver stands in to the fine one.
///
/// [definition] These are the only three lawful values. There is deliberately no `Default`, no
/// fallthrough and no inference from the data: [`GrainTower::found`] demands one and the chosen
/// relation travels with the tower. A coarse reading with no declared relation is not a reading.
///
/// Lean counterpart: `Foundation/GrainRestriction.lean::ApertureRelation`, with one theorem per
/// arm stating what that arm preserves.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ApertureRelation {
    /// The coarse receiver runs at an inflated aperture that carries every non-`Outside` fine
    /// contact, with the inflation exhibited as a measured witness.
    ///
    /// The witness is boxed: it is by far the largest arm, and every value of this enum — one of
    /// which every [`GrainTower`] carries — would otherwise be sized by it.
    InflatedCoarse(Box<InflationWitness>),
    /// The two grains are separate receivers; neither restricts the other, and no commuting receipt
    /// is owed or claimed.
    DeclaredIndependent(IndependenceDeclaration),
    /// The fine grain is the receiver. A coarse reading is admitted only where it agrees, and a
    /// disagreement is a refusal rather than a reading.
    NativeFineWithRefusal(FineNativeDeclaration),
}

impl ApertureRelation {
    /// A short name for receipts.
    pub fn name(&self) -> &'static str {
        match self {
            Self::InflatedCoarse(_) => "inflated-coarse",
            Self::DeclaredIndependent(_) => "declared-independent",
            Self::NativeFineWithRefusal(_) => "native-fine-with-refusal",
        }
    }

    /// The fine aperture, squared, whichever arm is declared.
    pub fn fine_aperture_squared(&self) -> &Rat {
        match self {
            Self::InflatedCoarse(witness) => &witness.fine_aperture_squared,
            Self::DeclaredIndependent(declaration) => &declaration.fine_aperture_squared,
            Self::NativeFineWithRefusal(declaration) => &declaration.fine_aperture_squared,
        }
    }
}

/// A grain-addressed occurrence whose exact coordinate box is carried on one declared denominator.
///
/// This is the same exact wire the M5 driver hands the card: integer numerators over a common
/// decimal denominator, with the outward interval already applied. No float participates, and
/// [`Self::position`] recovers the exact [`CoordinateBox3`] so any classification produced here can
/// be re-derived through [`DistanceAperture::classify`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScaledOccurrence {
    /// Where this occurrence sits in the grain hierarchy.
    pub address: GrainAddress,
    /// Exterior label, retained as testimony and never used to select geometry.
    pub label: String,
    /// The lower corner numerators, in units of `1/denominator`.
    pub lower: [i64; 3],
    /// The upper corner numerators.
    pub upper: [i64; 3],
}

impl ScaledOccurrence {
    /// The exact rational coordinate box over the declared denominator.
    pub fn position(&self, denominator: &BigUint) -> Result<CoordinateBox3, GrainRefusal> {
        if denominator.is_zero() {
            return Err(GrainRefusal::ZeroDenominator);
        }
        let den = BigInt::from(denominator.clone());
        let axis = |at: usize| ExactInterval {
            lower: Rat::new(BigInt::from(self.lower[at]), den.clone()),
            upper: Rat::new(BigInt::from(self.upper[at]), den.clone()),
        };
        Ok(CoordinateBox3 {
            x: axis(0),
            y: axis(1),
            z: axis(2),
        })
    }
}

/// The aperture on the scaled wire: one declared denominator and the aperture's square in units of
/// `1/denominator²`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ScaledAperture {
    /// Exterior lineage of the aperture declaration.
    pub lineage: String,
    /// The common decimal denominator every coordinate is carried on.
    pub denominator: u64,
    /// The aperture squared, in units of `1/denominator²`. Exact.
    pub aperture_squared_wire: i128,
}

impl ScaledAperture {
    /// The exact rational aperture this wire stands for.
    pub fn exact(&self) -> Result<DistanceAperture, GrainRefusal> {
        if self.denominator == 0 {
            return Err(GrainRefusal::ZeroDenominator);
        }
        let den = BigInt::from(self.denominator);
        Ok(DistanceAperture {
            lineage: self.lineage.clone(),
            squared: Rat::new(BigInt::from(self.aperture_squared_wire), &den * &den),
        })
    }

    /// Classify one exact scaled squared-distance interval. Identical trichotomy to
    /// [`DistanceAperture::classify`], carried out in `i128` on the common denominator.
    pub fn classify(&self, lower: i128, upper: i128) -> ContactClass {
        if upper <= self.aperture_squared_wire {
            ContactClass::Inside
        } else if lower > self.aperture_squared_wire {
            ContactClass::Outside
        } else {
            ContactClass::Open
        }
    }

    /// The exact scaled squared-distance interval between two boxes, or a typed refusal.
    ///
    /// # Why this returns a `Result`
    ///
    /// [established-bounded; source-inspected] The coordinates are `i64` numerators on a public,
    /// `Deserialize`-able type, so an axis difference reaches `2^64 - 1` in the worst admitted
    /// input and its square reaches `2^128 - 2^65 + 1`, which is outside `i128`. Three such axes
    /// are then summed. The aperture this interval is compared against is itself an `i128`
    /// ([`ScaledAperture::aperture_squared_wire`]), so a squared distance that leaves the wire is
    /// not a value this receiver can classify at all — there is no larger correct answer to give
    /// on this wire, and silently wrapping would hand [`Self::classify`] a small positive number
    /// and make a distant pair read `Inside`.
    ///
    /// Every product and every accumulation is therefore checked, and the refusal names both
    /// addresses and the axis. Real CIF-scaled intake is nowhere near this: the M5 family's
    /// resident decimal grain (`crates/holonic-life/examples/m5/fold.rs::derive_resident_places`)
    /// is seven places, so one angstrom is `10^7` and a coordinate of `10^11` — ten thousand
    /// angstroms, wider than any presented assembly — squares to `10^22`, sixteen orders of
    /// magnitude inside `i128::MAX`. The refusal exists because the type is public, not because
    /// the measured path reaches it.
    pub fn squared_distance(
        left: &ScaledOccurrence,
        right: &ScaledOccurrence,
    ) -> Result<(i128, i128), GrainRefusal> {
        let mut lower = 0_i128;
        let mut upper = 0_i128;
        for axis in 0..3 {
            let leaves = || GrainRefusal::ScaledDistanceLeavesTheWire {
                left: left.address,
                right: right.address,
                axis,
            };
            // Both differences fit: an `i64` difference is at most `2^64 - 1` in magnitude.
            let low = i128::from(left.lower[axis]) - i128::from(right.upper[axis]);
            let high = i128::from(left.upper[axis]) - i128::from(right.lower[axis]);
            let low_square = low.checked_mul(low).ok_or_else(leaves)?;
            let high_square = high.checked_mul(high).ok_or_else(leaves)?;
            let axis_lower = if low <= 0 && 0 <= high {
                0
            } else {
                low_square.min(high_square)
            };
            lower = lower.checked_add(axis_lower).ok_or_else(leaves)?;
            upper = upper
                .checked_add(low_square.max(high_square))
                .ok_or_else(leaves)?;
        }
        Ok((lower, upper))
    }
}

/// Found the atom-grain face of one declared cross population, exactly.
///
/// Every `(left, right)` pair is classified; only the non-`Outside` readings are stored, which is
/// what makes the face a carrier of the complete population without materializing it.
pub fn found_atom_face(
    left: &[ScaledOccurrence],
    right: &[ScaledOccurrence],
    aperture: &ScaledAperture,
) -> Result<GrainFace, GrainRefusal> {
    let mut classified = BTreeMap::new();
    for a in left {
        for b in right {
            let (lower, upper) = ScaledAperture::squared_distance(a, b)?;
            let class = aperture.classify(lower, upper);
            if class == ContactClass::Outside {
                continue;
            }
            let pair = GrainPair::new(a.address.cell(Grain::Atom), b.address.cell(Grain::Atom))?;
            let entry = classified.entry(pair).or_insert(class);
            *entry = join_contact_class(*entry, class);
        }
    }
    Ok(GrainFace {
        grain: Grain::Atom,
        classified,
    })
}

/// The coarse readings of one declared cross population at a coarser grain, for
/// [`InflationWitness::measure`].
///
/// `selection` supplies the representative of every coarse cell; `fine` supplies the restriction
/// already taken; `radii` supplies the measured grain radius of each coarse cell as an exact
/// rational bound. A coarse cell with no representative or no radius is refused by name.
pub fn coarse_readings(
    selection: &GrainSelection,
    fine: &GrainFace,
    positions: &BTreeMap<GrainCell, ScaledOccurrence>,
    radii: &BTreeMap<GrainCell, Rat>,
    denominator: &BigUint,
    forcing: &BTreeMap<GrainPair, GrainPair>,
) -> Result<Vec<CoarseReading>, GrainRefusal> {
    if fine.grain() != selection.coarse() {
        return Err(GrainRefusal::PairNotAtGrain {
            expected: selection.coarse(),
            found: fine.grain(),
        });
    }
    let den = BigInt::from(denominator.clone());
    let squared_denominator = Rat::new(BigInt::one(), &den * &den);
    let mut readings = Vec::with_capacity(fine.classified().len());
    for (pair, class) in fine.classified() {
        let lower_cell = *selection
            .representative_of(&pair.lower)
            .ok_or(GrainRefusal::NoRepresentative { cell: pair.lower })?;
        let upper_cell = *selection
            .representative_of(&pair.upper)
            .ok_or(GrainRefusal::NoRepresentative { cell: pair.upper })?;
        let lower_position = positions
            .get(&lower_cell)
            .ok_or(GrainRefusal::NoRepresentative { cell: lower_cell })?;
        let upper_position = positions
            .get(&upper_cell)
            .ok_or(GrainRefusal::NoRepresentative { cell: upper_cell })?;
        let (low, high) = ScaledAperture::squared_distance(lower_position, upper_position)?;
        readings.push(CoarseReading {
            pair: *pair,
            fine_class: *class,
            coarse_squared_distance: ExactInterval {
                lower: &Rat::from_integer(BigInt::from(low)) * &squared_denominator,
                upper: &Rat::from_integer(BigInt::from(high)) * &squared_denominator,
            },
            forcing_fine_pair: forcing.get(pair).copied(),
            lower_grain_radius: radii
                .get(&pair.lower)
                .cloned()
                .ok_or(GrainRefusal::NoGrainRadius { cell: pair.lower })?,
            upper_grain_radius: radii
                .get(&pair.upper)
                .cloned()
                .ok_or(GrainRefusal::NoGrainRadius { cell: pair.upper })?,
        });
    }
    Ok(readings)
}

/// A checked instance of the deliverable equation: the coarse face together with the residual
/// reconstructs the fine face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GrainReopenReceipt {
    /// The transition's own `reopen(apply(x), residual(x)) = x` receipt.
    pub source_reopened: usize,
    /// How many fine readings the residual had to retain.
    pub residual_retained: usize,
    /// How many readings the coarse face carried.
    pub coarse_carried: usize,
    /// How many non-`Outside` readings the reconstructed fine restriction carries.
    pub fine_reading_carried: usize,
}

/// Check, on one presentation, that the selection's residual reopens both the atom-grain source and
/// the fine restriction.
///
/// Lean counterpart: `Foundation/ContinuingTower.lean::Transition.reopen_apply` and
/// `Transition.laterReceiverFactors`, restated at this transition as
/// `Foundation/GrainRestriction.lean::grain_residual_reopens_the_source` and
/// `fineReading_factors`.
pub fn check_grain_reopen(
    selection: &GrainSelection,
    atom_face: &GrainFace,
) -> Result<GrainReopenReceipt, GrainRefusal> {
    let transported = selection.apply(atom_face);
    let residual = selection.residual(atom_face);
    let reopened = selection.reopen(&transported, &residual);
    if &reopened != atom_face {
        return Err(GrainRefusal::ReopenFailed {
            retained: residual.retained(),
        });
    }
    let fine_reading = atom_face.restricted(selection.coarse())?;
    let reopened_reading = selection.reopen_fine_reading(&transported, &residual)?;
    if reopened_reading != fine_reading {
        return Err(GrainRefusal::FineReadingNotReopened);
    }
    let ReopenReceipt { sources_reopened } =
        selection
            .check_reopen(atom_face)
            .map_err(|_| GrainRefusal::ReopenFailed {
                retained: residual.retained(),
            })?;
    Ok(GrainReopenReceipt {
        source_reopened: sources_reopened,
        residual_retained: residual.retained(),
        coarse_carried: transported.classified().len(),
        fine_reading_carried: fine_reading.classified().len(),
    })
}

/// The measured refutation of a declared coarse aperture: the pair that refutes it, what the
/// measurement requires there and what the caller declared.
///
/// This is carried boxed inside [`GrainRefusal::CoarseApertureTooSmall`]. The evidence is kept
/// whole and inline in the refusal; what the box removes is only its contribution to the *size* of
/// every `Result` this module returns, so the happy path is not sized by the worst refusal.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ApertureRefutation {
    /// The pair that refutes the declaration.
    pub pair: GrainPair,
    /// What the measurement requires at that pair.
    pub required_squared: Rat,
    /// What the caller declared.
    pub declared_squared: Rat,
}

/// The refutation of a grain-radius certificate: the extremal pair, the certificate the supplied
/// radii produce there, and the measurement that exceeds it.
///
/// Carried boxed inside [`GrainRefusal::CertificateBelowMeasurement`], for the same reason as
/// [`ApertureRefutation`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertificateRefutation {
    /// The extremal pair.
    pub pair: GrainPair,
    /// The certificate the supplied radii produce.
    pub certified: Rat,
    /// The measurement it failed to bound.
    pub measured: Rat,
}

/// Why a grain construction refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum GrainRefusal {
    /// A remount cannot silently reinterpret an unknown wire schema.
    #[error("unsupported grain tower schema {schema}")]
    TowerSchemaUnsupported { schema: String },
    /// The named fine grain does not refine the named coarse grain.
    #[error("grain {fine:?} does not refine grain {coarse:?}")]
    NotASubGrain {
        /// The claimed coarser grain.
        coarse: Grain,
        /// The claimed finer grain.
        fine: Grain,
    },
    /// A pair was offered with endpoints at two different grains.
    #[error("a pair cannot join grain {left:?} to grain {right:?}")]
    MixedGrainPair {
        /// The left endpoint's grain.
        left: Grain,
        /// The right endpoint's grain.
        right: Grain,
    },
    /// A pair collapsed to one cell.
    #[error("the pair collapses at cell {cell:?}")]
    CollapsedPair {
        /// Where it collapsed.
        cell: GrainCell,
    },
    /// A pair was offered at the wrong grain.
    #[error("expected a pair at grain {expected:?} but found one at grain {found:?}")]
    PairNotAtGrain {
        /// The grain the face is read at.
        expected: Grain,
        /// The grain the pair belongs to.
        found: Grain,
    },
    /// An `Outside` reading was offered for storage. `Outside` is the default and storing it would
    /// make two equal faces unequal.
    #[error("an Outside reading at {pair:?} is the default and is never stored")]
    OutsideReadingStored {
        /// The pair.
        pair: GrainPair,
    },
    /// Two representatives were declared for one coarse cell.
    #[error("cell {cell:?} already carries a representative")]
    RepeatedRepresentative {
        /// The cell.
        cell: GrainCell,
    },
    /// The forward and inverse representative maps on a remounted selection disagree.
    #[error("the selection wire's representative and inverse maps disagree")]
    SelectionWireInconsistent,
    /// A coarse cell carries no representative.
    #[error("cell {cell:?} carries no representative, so the coarse receiver cannot read it")]
    NoRepresentative {
        /// The cell.
        cell: GrainCell,
    },
    /// A coarse cell carries no measured grain radius.
    #[error("cell {cell:?} carries no measured grain radius, so no inflation can be certified")]
    NoGrainRadius {
        /// The cell.
        cell: GrainCell,
    },
    /// The declared population is smaller than the classified population.
    #[error("the declared population {declared} is smaller than the {classified} classified pairs")]
    PopulationTooSmall {
        /// What the caller declared.
        declared: usize,
        /// What was actually classified.
        classified: usize,
    },
    /// An aperture that is zero or negative.
    #[error("the aperture square {value} is not positive")]
    NonPositiveAperture {
        /// The offered value.
        value: Rat,
    },
    /// A negative squared value was offered to a square root.
    #[error("{value} is negative and has no rational root bound")]
    NegativeSquare {
        /// The offered value.
        value: Rat,
    },
    /// A zero denominator.
    #[error("a zero denominator carries no exact coordinate")]
    ZeroDenominator,
    /// No fine contact exists, so an inflation would be a guess rather than a measurement.
    #[error("none of the {examined} readings carries a fine contact, so no inflation is measured")]
    NoFineContactToCarry {
        /// How many readings were examined.
        examined: usize,
    },
    /// The declared coarse aperture does not carry every fine contact. The evidence is
    /// [`ApertureRefutation`], boxed.
    #[error(
        "the declared coarse aperture square {} does not carry the fine contact at {:?}, which requires {}",
        .0.declared_squared, .0.pair, .0.required_squared
    )]
    CoarseApertureTooSmall(Box<ApertureRefutation>),
    /// The triangle-inequality certificate is below the measured requirement, which means a
    /// supplied grain radius is wrong. The evidence is [`CertificateRefutation`], boxed.
    #[error(
        "the grain-radius certificate {} at {:?} is below the measured requirement {}; a supplied radius is not an upper bound",
        .0.certified, .0.pair, .0.measured
    )]
    CertificateBelowMeasurement(Box<CertificateRefutation>),
    /// A scaled squared distance left the exact `i128` wire the aperture is carried on.
    #[error(
        "the scaled squared distance between {left:?} and {right:?} leaves the exact i128 wire on axis {axis}"
    )]
    ScaledDistanceLeavesTheWire {
        /// The left occurrence's address.
        left: GrainAddress,
        /// The right occurrence's address.
        right: GrainAddress,
        /// Which axis the wire was left on: `0` is `x`, `1` is `y`, `2` is `z`.
        axis: usize,
    },
    /// Independence was declared where the two readings agree.
    #[error("independence was declared with no measured separation in either direction")]
    IndependenceWithoutSeparation,
    /// The coarse reading disagrees with the fine restriction under a native-fine declaration.
    #[error(
        "the coarse reading at {pair:?} returns {coarse:?} where the fine restriction returns {fine:?}"
    )]
    CoarseReadingDisagrees {
        /// The pair.
        pair: GrainPair,
        /// The fine restriction's class.
        fine: ContactClass,
        /// The coarse reading's class.
        coarse: ContactClass,
    },
    /// `reopen(apply(x), residual(x)) != x`.
    #[error("reopening the source from its coarse face and {retained} retained readings failed")]
    ReopenFailed {
        /// How many readings the residual retained.
        retained: usize,
    },
    /// The fine restriction was not recovered from the coarse face and the residual.
    #[error("the coarse face together with the residual did not return the fine restriction")]
    FineReadingNotReopened,
}

#[cfg(test)]
#[path = "grain_tower/tests.rs"]
mod tests;
