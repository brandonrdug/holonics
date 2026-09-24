//! **The fold: a reflection applied to one side of a crease, and what separates it from a cut.**
//!
//! [definition] This module owns the fold/cut half of item **T7** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. It is the
//! executable equivalent of
//! `formal/elementary-holonics/ElementaryHolonics/Transport/Fold.lean`, namespace
//! `Soma.Holonics.Transport.Fold`: same structures, same laws, the Lean theorems appearing here as
//! invariants and tests.
//!
//! # What a fold is
//!
//! [proved-derived; implemented-exact] A crease is an exact rational hyperplane of `Q^d`, a normal
//! `n` and an offset `b`, and its signed side is `σ(x) = ⟨n,x⟩ − b`. The reflection is
//!
//! ```text
//!   R_H x = x − 2 σ(x) n / ⟨n,n⟩
//! ```
//!
//! and the **fold** applies it to one side only: `fold_H x = x` where `σ(x) ≥ 0` and `R_H x` where
//! `σ(x) < 0`. **Everything is exact over `Q` and no square root is taken anywhere**: the
//! reflection needs `⟨n,n⟩` and never `‖n‖`, every distance below is a *squared* distance, and
//! every angle below is avoided by an exact rational surrogate.
//!
//! [proved-derived; implemented-exact] The fold is a **piecewise isometry and not an isometry**.
//! Inside one closed side it preserves every squared distance exactly
//! (`Crease::fold_defect` returns zero, Lean `fold_distSq_same_side`). Across the crease it changes
//! them by exactly
//!
//! ```text
//!   ‖fold x − fold y‖² − ‖x − y‖² = 4 σ(x) σ(y) / ⟨n,n⟩ ,
//! ```
//!
//! which is strictly negative when the two points are strictly on opposite sides (Lean
//! `fold_distSq_opposite_side`, `fold_brings_the_two_sides_together`). That defect **is** the
//! content of folding: each half stays rigid and the two halves move relative to each other.
//!
//! # Bounce and collision
//!
//! [proved-derived; implemented-exact] A **bounce** is that fold read in the trajectory:
//! [`billiard_unfolding`] returns the exact rational crossing parameter of a straight segment
//! through the crease, the crossing point, and the incoming and outgoing directions, and checks
//! that the tangential component is fixed and the normal component negated — equal angles with no
//! angle taken. A **collision** is the contact law between the layers the fold stacks:
//! [`layer_contact`] composes [`crate::physical_constraint_complex::DistanceAperture::classify`] on
//! the folded configuration and returns the three-valued `Inside`/`Outside`/`Open` reading whole.
//! An `Open` layer pair is a plural reading and is never resolved by a default:
//! [`layer_contact_within`] takes the caller's declared squared-separation tolerance, and the pairs
//! the aperture cannot decide under it come back in their own list.
//!
//! # Reversibility is the residual
//!
//! [proved-derived; implemented-exact] [`FoldTransition`] implements
//! [`holonics::restriction::tower::Transition`] with `Residual = Side`: the side bit, one bit, and
//! `reopen(fold(x), side(x)) = x` exactly (Lean `reopen_apply_fold`). The fold is two-to-one off
//! the crease (Lean `fold_fibre`): its fibre through `x` is `{x, R_H x}`, so **folding in half is
//! the quotient of the sheet by the reflection** onto the closed positive half-space as a
//! fundamental domain, and the side bit is the remainder. `k` folds are [`FoldWord`]: `k` bits of
//! residual and up to `2^k` layers, which is the dyadic tube's branching cross-section at `p = 2`
//! — [`FoldWord::dyadic_layer`] returns the layer's address as an element of `Z/2^k`, the level-`k`
//! face of `Foundation/ContinuingTower.lean::padicTower` at `p = 2`, cited through
//! `Transport/ContinuingTube.lean::padicTube_crossSection_branching`.
//!
//! [definition] An **elastic** crease retains that residual and is a `Transition`. A **plastic**
//! crease dissipates it: [`PlasticCrease`] has an `apply` and no `Transition` implementation at
//! all, and [`PlasticCrease::reverse_passage`] returns
//! [`holonics::restriction::tower::ReversePassageReceipt::OnlyWithTheResidual`] with the two merged
//! faces — the passage instance of
//! `Foundation/ContinuingTower.lean::ResidualMigration.traversability_is_the_residual`. The two are
//! **different types with no coercion**, which is the typing Brandon's "plastic warps via heat,
//! loose fabric transitions seamlessly" asks for.
//!
//! # Division, shear, inversion
//!
//! [proved-derived; implemented-exact] **Rotation is two reflections**, exactly over `Q`:
//! [`rotation_from_two_reflections`] writes a plane direction as a Gaussian rational and returns
//! the composite as `rot(v ū)` with its exact `2 × 2` matrix, its determinant `+1` and each
//! reflection's determinant `−1` (Lean `lineReflect_comp_eq_rotBy`). **Inversion** in a sphere is
//! the third member of Brandon's triple: [`Inversion`] satisfies the exact rational distance law
//! `‖inv x − inv y‖² = r⁴ ‖x − y‖² / (⟨x,x⟩⟨y,y⟩)`, from which cross-ratio invariance follows with
//! every factor cancelling (Lean `inversion_preserves_cross_ratio`). That inversion in a sphere
//! *is* a reflection in a hyperplane of the conformal model is `[proved-standard; cited]` and is
//! not formalized. **A shear is neither**: [`shear_defect`] exhibits, at every point and every
//! scale, a pair whose squared distance a nonzero shear changes, so a shear is not an isometry and
//! therefore not a composition of reflections (Lean `no_isometry_is_a_shear`). Shear is the one
//! that deforms the lattice rather than folding it.
//!
//! # Fold against cut
//!
//! [proved-derived; implemented-exact] A **fold of a complex** is a cellular map: an isometry on
//! each cell and a bijection on cells when the crease lies along the skeleton.
//! [`read_cellular_fold`] checks exactly that and reads the Betti vector before and after through
//! the existing Smith-normal-form owner [`crate::rebase_invariants::rebase_invariants`] — they
//! agree, and every edge keeps its exact squared length. The Lean statement is the **automorphism**
//! one (`ChainTwo.fold_preserves_betti`, through `Matrix.rank_submatrix`); the *quotient*
//! statement is `fold_fibre`, whose residual is one bit. A **cut** removes or duplicates cells:
//! [`read_cut`] exhibits an annulus cut to a disc (`b₁ : 1 ↦ 0`) and a disc cut in two
//! (`b₀ : 1 ↦ 2`), and returns the **gluing residual** — which cells were identified — that
//! reversing it needs. [`CutReading::residual_is_strictly_larger_than_a_folds`] is the comparison:
//! a fold's residual is one bit and a cut's is the whole gluing pattern, measured with
//! [`crate::presentation_cost::code_bits`]. A cut is also a passage that breaks bonds:
//! [`severed_contact_family`] projects a cut onto a contact family so that
//! [`crate::physical_occurrence::ConstraintDelta::between`] returns the broken contacts as its own
//! typed delta.
//!
//! # Crease patterns are hinge frameworks
//!
//! [definition] Rigid origami is rigid panels joined by hinges along creases. **This module uses
//! the bar-joint model with panels triangulated**, not a separate body-hinge rigidity matrix,
//! because the bar-joint Jacobian, its kernel, its self-stress space and its trivial-motion
//! measurement are already owned exactly by [`crate::rigidity_receiver`] and a panel-hinge matrix
//! would be a second Jacobian for the same question. [`hinge_framework`] therefore returns a
//! [`crate::rigidity_receiver::RigidityJacobian`] whose bars are the crease edges plus, for each
//! panel, **every pair of that panel's vertices** — the bar-joint presentation of a rigid body.
//! Folding motions are `ker J` modulo the trivial motions, measured as R4 measures them, and a
//! locked pattern is one carrying a self-stress.
//!
//! [proved-derived; implemented-exact] **Finding: in three dimensions a completely braced panel of
//! four or more *coplanar* vertices is infinitesimally flexible.** Its out-of-plane velocity
//! components are unconstrained by every in-plane bar, so a planar quadrilateral panel contributes
//! exactly one spurious infinitesimal motion and one self-stress. The bar-joint reading of rigid
//! origami is therefore exact for **triangulated** patterns and reports one extra motion per
//! planar panel of higher extent; [`CreasePatternFraming::planar_panels`] names them rather than
//! letting the count be read as a folding motion. That is a property of the *infinitesimal* model,
//! not of the panel, which stays finitely rigid.
//!
//! [proved-derived; implemented-exact] **Kawasaki's law needs no angle.** [`KawasakiVertex`] takes
//! the crease directions as exact rational vectors and returns the accumulated turn as a Gaussian
//! rational; flat-foldability of the vertex is exactly "the turn's imaginary part is zero", which
//! is one rational equation (Lean `kawasaki_iff`). **Maekawa's law** is an integer count:
//! [`MaekawaAssignment::is_balanced`] is `M − V = ±2`, which at a degree-`2n` vertex is exactly
//! `M = n ± 1` (Lean `maekawa_iff_mountain_count`). Global flat-foldability is NP-hard
//! (Bern and Hayes, *The complexity of flat origami*, SODA 1996) — `[proved-standard; cited]` — so
//! [`flat_foldability`] **never affirms**: it returns a named local refutation, or
//! [`FlatFoldabilityVerdict::NotDecidedWithinBound`] carrying the bound it ran under.
//!
//! # Unfolding at a tolerance
//!
//! [proved-derived; implemented-exact] [`FoldCatastrophe`] is `V_a(x) = x³/3 − a x`, whose
//! equilibria are counted exactly by [`holonics::exact_value::SturmChain`] and whose stability is the
//! exact sign of `V'' = 2x`. [`CreaseModel`] is the declared constitutive model — a polynomial
//! hinge torque `κ(u² − u₀²)` against a constant gravity load, with typed units through
//! [`crate::quantity`] — whose held equilibrium disappears at the exact threshold `κ u₀²`. Its
//! approximations are stated affirmatively on the type. Brandon's lever arm is
//! [`opening_displacement_squared`]: under the rational parametrization `t = tan(θ/2)` the squared
//! displacement of a point at distance `ℓ` from the crease is `4 ℓ² t² / (1 + t²)`, exactly
//! quadratic in `ℓ`, so the offset grows linearly with distance from the crease.
//!
//! # The protein backbone
//!
//! [definition] [`BackboneChain`] is the backbone as rigid origami of a one-dimensional linkage:
//! `N`, `CA`, `C` per residue with fixed bond lengths, fixed bond angles and a **declared planar
//! `ω`**, which is the `CA–CA` bar across each peptide unit. Its predicted internal freedom is
//! `2(r − 1)` — the `φ`/`ψ` dihedrals — and [`BackboneChain::framework`] measures it rather than
//! assuming it. Dihedral *values* are reported without an angle: [`ExactDihedral`] carries the
//! exact rational `cos²θ` with the signs of `cos θ` and `sin θ`, and never a float. A
//! [`RamachandranChart`] is a **declared** partition of that chart with a ground and no default;
//! a residue outside every declared region returns [`RamachandranReading::OutsideTheChart`] and is
//! not imputed. A lattice-protein **pivot** is a rotation about a chain axis, which is two
//! reflections: [`PivotMove`] applies them to a declared tail and checks every bond length exactly.
//!
//! # Formal owner
//!
//! `formal/elementary-holonics/ElementaryHolonics/Transport/Fold.lean`, namespace
//! `Soma.Holonics.Transport.Fold`. The correspondence, both directions:
//!
//! | Lean | Rust |
//! |---|---|
//! | `dot`, `distSq` | [`dot`], [`squared_distance`] |
//! | `Crease`, `Crease.side`, `Crease.reflect`, `Crease.fold` | [`Crease`], [`Crease::side_value`], [`Crease::reflect`], [`Crease::fold`] |
//! | `Crease.linReflect`, `linReflect_fixes_tangential`, `linReflect_normal` | [`Crease::linear_reflect`], the bounce reading |
//! | `reflect_involutive`, `reflect_distSq` | [`Crease::reflect`] is checked to be an involution and an isometry |
//! | `fold_distSq_same_side`, `fold_distSq_opposite_side` | [`Crease::fold_defect`] |
//! | `fold_brings_the_two_sides_together` | [`Crease::fold_defect`] is negative across the crease |
//! | `fold_mem_positive_side`, `fold_eq_self_iff`, `fold_fibre` | [`Crease::fold`], [`Crease::fold_fibre`] |
//! | `foldTransition`, `reopen_apply_fold` | [`FoldTransition`] |
//! | `segment`, `side_segment`, `crossing`, `crossing_side_eq_zero` | [`billiard_unfolding`] |
//! | `fold_segment_before`, `fold_segment_after`, `bounce_direction` | [`BilliardUnfolding`] |
//! | `sideWord_card`, `k_folds_branch_dyadically` | [`FoldWord::layer_count`], [`FoldWord::dyadic_layer`] |
//! | `residual_injective_on_fibre` | [`CutReading::residual_is_strictly_larger_than_a_folds`] |
//! | `cmul`, `cconj`, `cnormSq`, `lineReflect`, `rotBy` | [`GaussianRational`], [`line_reflection_matrix`] |
//! | `lineReflect_comp_eq_rotBy`, `rotBy_comp`, `rotBy_eq_id_iff` | [`rotation_from_two_reflections`] |
//! | `kawasakiTurn`, `reflectPairs`, `kawasaki_iff` | [`KawasakiVertex::turn`], [`KawasakiVertex::is_flat_foldable`] |
//! | `plusVertex`, `skewVertex` | the two exact degree-four instances in the tests |
//! | `mountains`, `valleys`, `MaekawaBalanced`, `maekawa_iff_mountain_count` | [`MaekawaAssignment`] |
//! | `shear`, `shear_changes_a_squared_distance_at_every_point_and_scale`, `no_isometry_is_a_shear` | [`shear_defect`] |
//! | `inversion`, `inversion_distSq`, `inversion_preserves_cross_ratio` | [`Inversion`] |
//! | `ChainTwo`, `ChainTwo.Relabelling`, `fold_preserves_betti` | [`CellComplex`], [`CellularFold`], [`read_cellular_fold`] |
//! | `fold_preserves_intrinsic_length` | [`CellularFoldReading::edge_lengths_preserved`] |
//! | `foldPotential`, `foldForce`, `foldStiffness`, `foldEquilibria_iff` | [`FoldCatastrophe`] |
//! | `foldEquilibria_two_of_pos`, `no_equilibrium_of_neg`, `positiveRoot_is_stable` | [`EquilibriumReading`] |
//! | `creaseTorque`, `held_equilibrium_iff_load_le_threshold` | [`CreaseModel`] |
//! | `rotCos`, `rotSin`, `rationalRotation_orthogonal` | [`rational_rotation`] |
//! | `displacementSq`, `displacementSq_scales_with_lever` | [`opening_displacement_squared`] |
//! | `backboneBarCount`, `backboneCoordinateCount`, `backbone_internal_dof` | [`BackboneChain::bar_count`], [`BackboneFraming::predicted_internal`] |
//! | `cross`, `lagrange_identity`, `dihedralCosSq`, `dihedralCosSq_le_one` | [`cross_product`], [`ExactDihedral`] |
//! | `pivot_preserves_squared_lengths`, `pivot_fixes_the_axis` | [`PivotMove`] |
//!
//! Every one of those elaborates with `#print axioms` returning
//! `[propext, Classical.choice, Quot.sound]` or fewer, and no `sorryAx`.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use holonics::geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::EventId;
use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use holonics::restriction::tower::{ReversePassageReceipt, Transition};
use holonics::exact_linear::ExactRatMatrix;
use holonics::exact_value::{ExactInterval, ExactValueError, IntegerPolynomial, SturmChain};
use crate::physical_constraint_complex::{
    ConstraintEdge, ConstraintVertexId, ContactClass, DistanceAperture,
};
use crate::physical_constraint_grading::EdgeProvenance;
use crate::physical_occurrence::{SituatedFamily, SituatedPairReading};
use crate::presentation_cost::{CostReceipt, Counted, code_bits};
use crate::quantity::{BaseUnits, Dimension, Quantity, QuantityError};
use holonics::rebase_invariants::PivotRule;
use crate::rebase_invariants::{rebase_invariants};
use crate::rigidity_receiver::{
    ExactConfiguration, RigidityError, RigidityJacobian, RigidityReading, rigidity_reading,
};

// ---------------------------------------------------------------------------------------------
// declared ceilings
// ---------------------------------------------------------------------------------------------

/// **The declared ceiling on an ambient dimension.**
///
/// [definition] The dimension sizes every coordinate loop, every reflection and the width of every
/// configuration this module builds. It comes from a caller, so it is bounded before any work is
/// done with it and refused by name above the ceiling.
pub const DIMENSION_CEILING: usize = 1024;

/// **The declared ceiling on the number of folds in a word.**
///
/// [definition] `k` folds carry `2^k` layers and a `k`-bit residual, so an unbounded `k` is an
/// unbounded exponential. The residual itself is linear in `k`; the *layer count* is not, and
/// [`FoldWord::layer_count`] returns a `BigUint` rather than a machine integer for that reason.
pub const FOLD_WORD_CEILING: usize = 64;

/// **The declared ceiling on a cell population.**
///
/// [definition] Every complex this module builds allocates per cell and runs an exact integer
/// Smith normal form over the boundary matrices, whose work is superlinear in the cell count.
pub const CELL_CEILING: usize = 4096;

/// **The declared ceiling on a crease-pattern vertex population.**
pub const PATTERN_VERTEX_CEILING: usize = 2048;

/// **The declared ceiling on one panel's vertex count.**
///
/// [definition] A panel is braced by every pair of its vertices, so its bar count is quadratic in
/// its extent. The extent comes from a caller, so it is bounded before the bracing loop runs.
pub const PANEL_EXTENT_CEILING: usize = 64;

/// **The declared ceiling on a probe or a gluing pattern.**
///
/// [definition] `PlasticCrease::reverse_passage` compares every pair of a supplied probe and
/// `reglue` walks every supplied identification against every vertex; both are quadratic in a
/// caller's collection, so the collection is bounded before the loop rather than inside it.
pub const PROBE_CEILING: usize = 4096;

/// **The declared ceiling on a vertex degree whose layer orderings are counted.**
///
/// [definition] `flat_foldability` reports the exact number of layer orderings, which is a
/// factorial of the degree. A degree above this is refused by name rather than multiplying a
/// caller's way into an arbitrarily large integer.
pub const LAYER_ORDERING_DEGREE_CEILING: usize = 64;

/// **The declared ceiling on a backbone residue window.**
///
/// [definition] The rigidity Jacobian of `r` residues is `(7r − 4) × 9r` and its exact rational
/// elimination is cubic in that shape, so the window is a declared extent and is bounded here.
pub const BACKBONE_RESIDUE_CEILING: usize = 512;

// ---------------------------------------------------------------------------------------------
// the exact bilinear form
// ---------------------------------------------------------------------------------------------

/// **The standard bilinear form on `Q^d`, exact.**
///
/// Lean counterpart: `Transport/Fold.lean::dot`. No norm is taken anywhere in this module: every
/// statement is about the squared quantity, which is why nothing needs a square root.
pub fn dot(left: &[Rat], right: &[Rat]) -> Result<Rat, FoldRefusal> {
    if left.len() != right.len() {
        return Err(FoldRefusal::DimensionDisagrees {
            expected: left.len(),
            supplied: right.len(),
        });
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (a, b)| sum + a * b))
}

/// **The exact squared distance.**
///
/// Lean counterpart: `Transport/Fold.lean::distSq`.
pub fn squared_distance(left: &[Rat], right: &[Rat]) -> Result<Rat, FoldRefusal> {
    if left.len() != right.len() {
        return Err(FoldRefusal::DimensionDisagrees {
            expected: left.len(),
            supplied: right.len(),
        });
    }
    Ok(left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
        let difference = a - b;
        sum + &difference * &difference
    }))
}

/// **The cross product on `Q³`, exact.**
///
/// Lean counterpart: `Transport/Fold.lean::cross`, with `lagrange_identity`.
pub fn cross_product(left: &[Rat], right: &[Rat]) -> Result<[Rat; 3], FoldRefusal> {
    if left.len() != 3 || right.len() != 3 {
        return Err(FoldRefusal::NotThreeDimensional {
            supplied: left.len().max(right.len()),
        });
    }
    Ok([
        &left[1] * &right[2] - &left[2] * &right[1],
        &left[2] * &right[0] - &left[0] * &right[2],
        &left[0] * &right[1] - &left[1] * &right[0],
    ])
}

// ---------------------------------------------------------------------------------------------
// the crease and the fold
// ---------------------------------------------------------------------------------------------

/// Which side of a crease a point sits on. **This is the fold's residual**, and it has three
/// values because the crease itself is neither side.
///
/// Lean counterpart: the `Bool` residual of `Transport/Fold.lean::foldTransition`, whose `true`
/// is [`Side::Negative`]. Three values here rather than two because `OnCrease` is a distinct
/// reading of the configuration and collapsing it into `Positive` would lose the fact that the
/// point is fixed by the reflection as well as by the fold.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Side {
    /// `σ(x) > 0`: the fundamental domain's interior. The fold fixes it.
    Positive,
    /// `σ(x) = 0`: the crease. Both the fold and the reflection fix it.
    OnCrease,
    /// `σ(x) < 0`: the reflected side.
    Negative,
}

impl Side {
    /// The one bit the fold actually retains: whether the point was reflected.
    pub const fn was_reflected(self) -> bool {
        matches!(self, Side::Negative)
    }

    /// The side of an exact signed value.
    pub fn of(value: &Rat) -> Self {
        if value.is_zero() {
            Side::OnCrease
        } else if value.is_positive() {
            Side::Positive
        } else {
            Side::Negative
        }
    }
}

/// **A point of `Q^d`, with its dimension checked at the constructor.**
///
/// [definition] The coordinates are private because the invariant — a nonempty coordinate list
/// inside [`DIMENSION_CEILING`] — is not expressible in the wire format, and a remounted value is
/// re-checked by [`FoldPoint::try_from`] through `#[serde(try_from = ...)]` so no `Deserialize`
/// path reconstructs one unchecked.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(try_from = "FoldPointWire")]
pub struct FoldPoint {
    coordinates: Vec<Rat>,
}

/// The wire of a [`FoldPoint`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct FoldPointWire {
    coordinates: Vec<Rat>,
}

impl TryFrom<FoldPointWire> for FoldPoint {
    type Error = FoldRefusal;

    fn try_from(wire: FoldPointWire) -> Result<Self, Self::Error> {
        FoldPoint::declared(wire.coordinates)
    }
}

impl FoldPoint {
    /// A declared point. Refuses the empty point and a dimension above the declared ceiling.
    pub fn declared(coordinates: Vec<Rat>) -> Result<Self, FoldRefusal> {
        if coordinates.is_empty() {
            return Err(FoldRefusal::ZeroDimension);
        }
        if coordinates.len() > DIMENSION_CEILING {
            return Err(FoldRefusal::DimensionTooWide {
                supplied: coordinates.len(),
                ceiling: DIMENSION_CEILING,
            });
        }
        Ok(Self { coordinates })
    }

    /// A point from small integers, for declared instances.
    pub fn integers(values: &[i64]) -> Result<Self, FoldRefusal> {
        Self::declared(
            values
                .iter()
                .map(|value| Rat::from_integer(BigInt::from(*value)))
                .collect(),
        )
    }

    pub fn dimension(&self) -> usize {
        self.coordinates.len()
    }

    pub fn coordinates(&self) -> &[Rat] {
        &self.coordinates
    }
}

/// **An exact rational crease: the hyperplane `⟨n, x⟩ = b` of `Q^d`.**
///
/// [definition] The fields are private because the invariant — a nonempty normal inside the
/// dimension ceiling with `⟨n,n⟩ ≠ 0` — is what every reflection divides by. Over `Q` a sum of
/// squares vanishes only at zero, so `⟨n,n⟩ ≠ 0` is exactly `n ≠ 0` and no norm is needed.
///
/// Lean counterpart: `Transport/Fold.lean::Crease`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "CreaseWire")]
pub struct Crease {
    normal: Vec<Rat>,
    offset: Rat,
    normal_squared: Rat,
}

/// The wire of a [`Crease`]. `normal_squared` is **recomputed**, never carried: a wire declaring a
/// different one would be declaring a different reflection under the same normal.
#[derive(Deserialize)]
struct CreaseWire {
    normal: Vec<Rat>,
    offset: Rat,
}

impl TryFrom<CreaseWire> for Crease {
    type Error = FoldRefusal;

    fn try_from(wire: CreaseWire) -> Result<Self, Self::Error> {
        Crease::declared(wire.normal, wire.offset)
    }
}

impl Crease {
    /// A declared crease.
    pub fn declared(normal: Vec<Rat>, offset: Rat) -> Result<Self, FoldRefusal> {
        if normal.is_empty() {
            return Err(FoldRefusal::ZeroDimension);
        }
        if normal.len() > DIMENSION_CEILING {
            return Err(FoldRefusal::DimensionTooWide {
                supplied: normal.len(),
                ceiling: DIMENSION_CEILING,
            });
        }
        let normal_squared = normal
            .iter()
            .fold(Rat::zero(), |sum, entry| sum + entry * entry);
        if normal_squared.is_zero() {
            return Err(FoldRefusal::DegenerateCrease);
        }
        Ok(Self {
            normal,
            offset,
            normal_squared,
        })
    }

    /// The crease through a declared point with a declared normal: `b = ⟨n, p⟩`.
    pub fn through(normal: Vec<Rat>, point: &FoldPoint) -> Result<Self, FoldRefusal> {
        let offset = dot(&normal, point.coordinates())?;
        Self::declared(normal, offset)
    }

    pub fn dimension(&self) -> usize {
        self.normal.len()
    }

    pub fn normal(&self) -> &[Rat] {
        &self.normal
    }

    pub fn offset(&self) -> &Rat {
        &self.offset
    }

    /// `⟨n,n⟩`, exact and nonzero.
    pub fn normal_squared(&self) -> &Rat {
        &self.normal_squared
    }

    /// **The signed side `σ(x) = ⟨n,x⟩ − b`**, exact.
    ///
    /// Lean counterpart: `Crease.side`.
    pub fn side_value(&self, point: &FoldPoint) -> Result<Rat, FoldRefusal> {
        Ok(dot(&self.normal, point.coordinates())? - &self.offset)
    }

    /// Which side, as the three-valued reading.
    pub fn side(&self, point: &FoldPoint) -> Result<Side, FoldRefusal> {
        Ok(Side::of(&self.side_value(point)?))
    }

    /// **The reflection `R_H x = x − 2 σ(x) n / ⟨n,n⟩`**, exact over `Q`.
    ///
    /// Lean counterpart: `Crease.reflect`, with `reflect_involutive` and `reflect_distSq`.
    pub fn reflect(&self, point: &FoldPoint) -> Result<FoldPoint, FoldRefusal> {
        let side = self.side_value(point)?;
        let coefficient = (Rat::from_integer(BigInt::from(2)) * &side) / &self.normal_squared;
        FoldPoint::declared(
            point
                .coordinates()
                .iter()
                .zip(&self.normal)
                .map(|(entry, normal)| entry - &coefficient * normal)
                .collect(),
        )
    }

    /// **The linear part**, `v ↦ v − 2⟨n,v⟩ n / ⟨n,n⟩`: the reflection of a *direction*.
    ///
    /// Lean counterpart: `Crease.linReflect`, with `linReflect_fixes_tangential` (the tangential
    /// component is fixed) and `linReflect_normal` (the normal component is negated).
    pub fn linear_reflect(&self, direction: &[Rat]) -> Result<Vec<Rat>, FoldRefusal> {
        let pairing = dot(&self.normal, direction)?;
        let coefficient = (Rat::from_integer(BigInt::from(2)) * &pairing) / &self.normal_squared;
        Ok(direction
            .iter()
            .zip(&self.normal)
            .map(|(entry, normal)| entry - &coefficient * normal)
            .collect())
    }

    /// **The fold**: the reflection applied to the negative side only.
    ///
    /// Lean counterpart: `Crease.fold`, with `fold_mem_positive_side` and `fold_eq_self_iff`.
    pub fn fold(&self, point: &FoldPoint) -> Result<FoldPoint, FoldRefusal> {
        if self.side_value(point)?.is_negative() {
            self.reflect(point)
        } else {
            Ok(point.clone())
        }
    }

    /// **The exact metric defect of the fold on one pair.**
    ///
    /// Zero when both points lie on one closed side — each half is rigid — and
    /// `4 σ(x) σ(y) / ⟨n,n⟩` across the crease, which is strictly negative when both sides are
    /// strict. That defect is the whole content of folding.
    ///
    /// Lean counterparts: `fold_distSq_same_side`, `fold_distSq_opposite_side`,
    /// `fold_brings_the_two_sides_together`.
    pub fn fold_defect(&self, left: &FoldPoint, right: &FoldPoint) -> Result<Rat, FoldRefusal> {
        let sigma_left = self.side_value(left)?;
        let sigma_right = self.side_value(right)?;
        let same_side = (!sigma_left.is_negative() && !sigma_right.is_negative())
            || (sigma_left.is_negative() && sigma_right.is_negative());
        if same_side {
            return Ok(Rat::zero());
        }
        Ok((Rat::from_integer(BigInt::from(4)) * &sigma_left * &sigma_right)
            / &self.normal_squared)
    }

    /// **The fibre of the fold through a point**: `{x}` on the crease and `{x, R_H x}` off it.
    ///
    /// Lean counterpart: `fold_fibre`. This is the exact sense in which folding in half is
    /// division by two: the fold is the quotient of the sheet by the reflection onto the closed
    /// positive half-space, and the side bit is the remainder.
    pub fn fold_fibre(&self, point: &FoldPoint) -> Result<Vec<FoldPoint>, FoldRefusal> {
        let mirrored = self.reflect(point)?;
        if &mirrored == point {
            Ok(vec![point.clone()])
        } else {
            let mut fibre = vec![point.clone(), mirrored];
            fibre.sort();
            Ok(fibre)
        }
    }
}

/// **The fold as a transition whose residual is the side bit.**
///
/// [definition] `reopen` is **total**: outside the image — a target whose dimension is not the
/// crease's — it returns the target unchanged, exactly as the Lean docstring says of
/// `Transition.reopen` ("outside the image of `apply`, `reopen` returns whatever the constructor
/// supplies; only presented pairs carry the law"). It never panics and never allocates from a
/// declared size.
///
/// Lean counterpart: `Transport/Fold.lean::foldTransition`, with `reopen_apply_fold`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoldTransition {
    crease: Crease,
}

impl FoldTransition {
    pub fn of(crease: Crease) -> Self {
        Self { crease }
    }

    pub fn crease(&self) -> &Crease {
        &self.crease
    }
}

impl Transition for FoldTransition {
    type Source = FoldPoint;
    type Target = FoldPoint;
    type Residual = Side;

    fn apply(&self, source: &FoldPoint) -> FoldPoint {
        self.crease.fold(source).unwrap_or_else(|_| source.clone())
    }

    fn residual(&self, source: &FoldPoint) -> Side {
        self.crease.side(source).unwrap_or(Side::OnCrease)
    }

    fn reopen(&self, target: &FoldPoint, residual: &Side) -> FoldPoint {
        if residual.was_reflected() {
            self.crease
                .reflect(target)
                .unwrap_or_else(|_| target.clone())
        } else {
            target.clone()
        }
    }
}

// ---------------------------------------------------------------------------------------------
// k folds: the dyadic tube
// ---------------------------------------------------------------------------------------------

/// **`k` folds across `k` declared creases, in order.**
///
/// Lean counterpart: the iterated `Transition.comp` of `foldTransition`, whose residual is the
/// list of `k` side bits (`sideWord_card`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "FoldWordWire")]
pub struct FoldWord {
    creases: Vec<Crease>,
}

/// The wire of a [`FoldWord`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct FoldWordWire {
    creases: Vec<Crease>,
}

impl TryFrom<FoldWordWire> for FoldWord {
    type Error = FoldRefusal;

    fn try_from(wire: FoldWordWire) -> Result<Self, Self::Error> {
        FoldWord::declared(wire.creases)
    }
}

impl FoldWord {
    /// A declared word of folds. Refuses an empty word by name — a word with no fold is not a
    /// fold, and a residual over no creases would be a certificate minted from nothing — and a
    /// word longer than [`FOLD_WORD_CEILING`], and creases of disagreeing dimension.
    pub fn declared(creases: Vec<Crease>) -> Result<Self, FoldRefusal> {
        let Some(first) = creases.first() else {
            return Err(FoldRefusal::EmptyFoldWord);
        };
        if creases.len() > FOLD_WORD_CEILING {
            return Err(FoldRefusal::FoldWordTooLong {
                supplied: creases.len(),
                ceiling: FOLD_WORD_CEILING,
            });
        }
        let dimension = first.dimension();
        for crease in &creases {
            if crease.dimension() != dimension {
                return Err(FoldRefusal::DimensionDisagrees {
                    expected: dimension,
                    supplied: crease.dimension(),
                });
            }
        }
        Ok(Self { creases })
    }

    pub fn creases(&self) -> &[Crease] {
        &self.creases
    }

    pub fn len(&self) -> usize {
        self.creases.len()
    }

    /// A [`FoldWord`] is never empty; this exists because [`FoldWord::len`] does.
    pub fn is_empty(&self) -> bool {
        false
    }

    pub fn dimension(&self) -> usize {
        self.creases[0].dimension()
    }

    /// Fold the point through every crease in order.
    pub fn apply(&self, point: &FoldPoint) -> Result<FoldPoint, FoldRefusal> {
        let mut carried = point.clone();
        for crease in &self.creases {
            carried = crease.fold(&carried)?;
        }
        Ok(carried)
    }

    /// The `k` side bits, in application order.
    pub fn residual(&self, point: &FoldPoint) -> Result<Vec<Side>, FoldRefusal> {
        let mut carried = point.clone();
        let mut sides = Vec::with_capacity(self.creases.len());
        for crease in &self.creases {
            sides.push(crease.side(&carried)?);
            carried = crease.fold(&carried)?;
        }
        Ok(sides)
    }

    /// Reopen the source exactly from the folded point and the retained `k` bits.
    pub fn reopen(&self, folded: &FoldPoint, residual: &[Side]) -> Result<FoldPoint, FoldRefusal> {
        if residual.len() != self.creases.len() {
            return Err(FoldRefusal::ResidualWidthDisagrees {
                expected: self.creases.len(),
                supplied: residual.len(),
            });
        }
        let mut carried = folded.clone();
        for (crease, side) in self.creases.iter().zip(residual).rev() {
            if side.was_reflected() {
                carried = crease.reflect(&carried)?;
            }
        }
        Ok(carried)
    }

    /// **`2^k` layers.** Exact, as a `BigUint`: the layer count is exponential in a declared
    /// extent and is never a machine integer.
    ///
    /// Lean counterpart: `sideWord_card`, and `k_folds_branch_dyadically`, which is
    /// `Transport/ContinuingTube.lean::padicTube_crossSection_branching` at `p = 2`.
    pub fn layer_count(&self) -> BigUint {
        BigUint::one() << self.creases.len()
    }

    /// The residual's exact code size in bits: `k`, one per fold.
    pub fn residual_code_bits(&self) -> BigUint {
        code_bits(&self.layer_count())
    }

    /// **The layer's address as an element of `Z/2^k`.**
    ///
    /// [definition] This is the level-`k` face of the dyadic tower at `p = 2`: the side word is a
    /// path down the `2`-ary tree whose cross-section branches exactly `2` ways per step
    /// (`padicTube_adjacent_branching`) and `2^k` ways over `k` steps
    /// (`padicTube_crossSection_branching`). The first fold is the least significant bit, so
    /// truncating the word to its first `j` folds is exactly the tower's restriction to level `j`.
    pub fn dyadic_layer(&self, residual: &[Side]) -> Result<BigUint, FoldRefusal> {
        if residual.len() != self.creases.len() {
            return Err(FoldRefusal::ResidualWidthDisagrees {
                expected: self.creases.len(),
                supplied: residual.len(),
            });
        }
        let mut address = BigUint::zero();
        for (at, side) in residual.iter().enumerate() {
            if side.was_reflected() {
                address += BigUint::one() << at;
            }
        }
        Ok(address)
    }
}

// ---------------------------------------------------------------------------------------------
// the bounce
// ---------------------------------------------------------------------------------------------

/// **The billiard unfolding of one crossing.**
///
/// Lean counterparts: `side_segment`, `crossing_side_eq_zero`, `fold_segment_before`,
/// `fold_segment_after`, `bounce_direction`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BilliardUnfolding {
    pub schema: String,
    /// The exact rational parameter at which the straight segment meets the crease.
    pub crossing_parameter: Rat,
    /// The crossing point, whose signed side is exactly zero.
    pub crossing_point: FoldPoint,
    /// `⟨n, d⟩` for the incoming direction `d = b − a`.
    pub incoming_normal_pairing: Rat,
    /// `⟨n, R₀ d⟩` for the reflected direction. Exactly the negative of the incoming pairing.
    pub outgoing_normal_pairing: Rat,
    /// The reflected direction, exactly.
    pub outgoing_direction: Vec<Rat>,
    /// The tangential part of the direction, `d − ⟨n,d⟩ n / ⟨n,n⟩`, which the bounce fixes.
    pub tangential: Vec<Rat>,
    /// Checked: the tangential part is fixed by the linear reflection.
    pub tangential_is_fixed: bool,
    /// Checked: the normal pairing is exactly negated. Equal angles, with no angle taken.
    pub normal_is_negated: bool,
}

/// **The straight segment's fold is the reflected path.**
///
/// Refuses a segment that does not change side by name rather than returning a parameter outside
/// `[0, 1]`: a bounce needs a crossing.
pub fn billiard_unfolding(
    crease: &Crease,
    from: &FoldPoint,
    to: &FoldPoint,
) -> Result<BilliardUnfolding, FoldRefusal> {
    if from.dimension() != crease.dimension() || to.dimension() != crease.dimension() {
        return Err(FoldRefusal::DimensionDisagrees {
            expected: crease.dimension(),
            supplied: from.dimension().max(to.dimension()),
        });
    }
    let sigma_from = crease.side_value(from)?;
    let sigma_to = crease.side_value(to)?;
    let denominator = &sigma_from - &sigma_to;
    if denominator.is_zero() {
        return Err(FoldRefusal::SegmentDoesNotCrossTheCrease);
    }
    let crossing_parameter = &sigma_from / &denominator;
    if crossing_parameter.is_negative() || crossing_parameter > Rat::one() {
        return Err(FoldRefusal::SegmentDoesNotCrossTheCrease);
    }
    let crossing_point = FoldPoint::declared(
        from.coordinates()
            .iter()
            .zip(to.coordinates())
            .map(|(a, b)| a + &crossing_parameter * (b - a))
            .collect(),
    )?;

    let direction: Vec<Rat> = from
        .coordinates()
        .iter()
        .zip(to.coordinates())
        .map(|(a, b)| b - a)
        .collect();
    let incoming_normal_pairing = dot(crease.normal(), &direction)?;
    let outgoing_direction = crease.linear_reflect(&direction)?;
    let outgoing_normal_pairing = dot(crease.normal(), &outgoing_direction)?;

    let coefficient = &incoming_normal_pairing / crease.normal_squared();
    let tangential: Vec<Rat> = direction
        .iter()
        .zip(crease.normal())
        .map(|(entry, normal)| entry - &coefficient * normal)
        .collect();
    let tangential_image = crease.linear_reflect(&tangential)?;

    Ok(BilliardUnfolding {
        schema: BILLIARD_UNFOLDING_SCHEMA.to_owned(),
        crossing_parameter,
        crossing_point,
        incoming_normal_pairing: incoming_normal_pairing.clone(),
        outgoing_normal_pairing: outgoing_normal_pairing.clone(),
        outgoing_direction,
        tangential_is_fixed: tangential_image == tangential,
        normal_is_negated: outgoing_normal_pairing == -incoming_normal_pairing,
        tangential,
    })
}

// ---------------------------------------------------------------------------------------------
// the collision: the contact law between the stacked layers
// ---------------------------------------------------------------------------------------------

/// **The contact reading between the two layers a fold stacks.**
///
/// [definition] The class is the existing three-valued
/// [`crate::physical_constraint_complex::ContactClass`] and it stays plural: an `Open` layer pair
/// is a precision question about the aperture and is returned as its own count, never resolved
/// into `Inside` or `Outside` by a default.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LayerContactReading {
    pub schema: String,
    pub aperture: DistanceAperture,
    /// Every `(upper index, lower index)` pair with its exact squared distance and its class.
    pub readings: Vec<((usize, usize), Rat, ContactClass)>,
    pub inside: usize,
    pub outside: usize,
    pub open: usize,
    /// The pairs the aperture reads as touching: the layers are in contact there.
    pub touching: Vec<(usize, usize)>,
    /// The pairs the aperture cannot decide. Carried, never rounded.
    pub undecided: Vec<(usize, usize)>,
}

/// **Compose the contact law on the folded configuration, with exact places.**
///
/// This is [`layer_contact_within`] at zero tolerance: every separation is a point and the reading
/// is two-valued in practice, because an exact point interval is never straddled by the aperture.
pub fn layer_contact(
    upper: &[FoldPoint],
    lower: &[FoldPoint],
    aperture: &DistanceAperture,
) -> Result<LayerContactReading, FoldRefusal> {
    layer_contact_within(upper, lower, aperture, &Rat::zero())
}

/// **Compose the contact law on the folded configuration, under a declared squared-separation
/// tolerance.**
///
/// [definition] The tolerance is the caller's declared uncertainty on the *squared* separation, in
/// the same units the aperture is declared in; the separation becomes the exact interval
/// `[max(0, d − t), d + t]` and the aperture's own trichotomy then returns `Open` wherever it
/// cannot decide. **That `Open` is carried in [`LayerContactReading::undecided`] and never rounded
/// into `Inside` or `Outside`.** Refuses a negative tolerance and an empty layer by name: a contact
/// reading over no pair is not a reading, and returning "no penetration" from it would be a verdict
/// minted from nothing.
pub fn layer_contact_within(
    upper: &[FoldPoint],
    lower: &[FoldPoint],
    aperture: &DistanceAperture,
    squared_tolerance: &Rat,
) -> Result<LayerContactReading, FoldRefusal> {
    if squared_tolerance.is_negative() {
        return Err(FoldRefusal::NegativeTolerance);
    }
    if upper.is_empty() || lower.is_empty() {
        return Err(FoldRefusal::EmptyLayerProbe {
            upper: upper.len(),
            lower: lower.len(),
        });
    }
    let pairs = upper
        .len()
        .checked_mul(lower.len())
        .ok_or(FoldRefusal::LayerPopulationOverflows {
            upper: upper.len(),
            lower: lower.len(),
        })?;
    if pairs > CELL_CEILING {
        return Err(FoldRefusal::LayerPopulationTooWide {
            pairs,
            ceiling: CELL_CEILING,
        });
    }
    let mut readings = Vec::with_capacity(pairs);
    let mut inside = 0usize;
    let mut outside = 0usize;
    let mut open = 0usize;
    let mut touching = Vec::new();
    let mut undecided = Vec::new();
    for (above, point) in upper.iter().enumerate() {
        for (below, other) in lower.iter().enumerate() {
            let separation = squared_distance(point.coordinates(), other.coordinates())?;
            let lower_bound = &separation - squared_tolerance;
            let enclosure = ExactInterval::new(
                if lower_bound.is_negative() {
                    Rat::zero()
                } else {
                    lower_bound
                },
                &separation + squared_tolerance,
            )?;
            let class = aperture.classify(&enclosure);
            match class {
                ContactClass::Inside => {
                    inside += 1;
                    touching.push((above, below));
                }
                ContactClass::Outside => outside += 1,
                ContactClass::Open => {
                    open += 1;
                    undecided.push((above, below));
                }
            }
            readings.push(((above, below), separation, class));
        }
    }
    Ok(LayerContactReading {
        schema: LAYER_CONTACT_SCHEMA.to_owned(),
        aperture: aperture.clone(),
        readings,
        inside,
        outside,
        open,
        touching,
        undecided,
    })
}

// ---------------------------------------------------------------------------------------------
// elastic and plastic creases are different types
// ---------------------------------------------------------------------------------------------

/// **A plastic crease: a fold whose residual is dissipated.**
///
/// [definition] This type has an `apply` and **no** [`Transition`] implementation, no `residual`
/// and no `reopen`. That is the typing: a plastic crease is not a transition, because the side bit
/// that would reverse it has left the system as heat. There is no `From`, `Into` or `Deref`
/// between it and [`FoldTransition`], and no constructor of one returns the other.
///
/// [proved-derived] By
/// `Foundation/ContinuingTower.lean::ResidualMigration.traversability_is_the_residual` the reverse
/// passage from the transported face alone exists exactly when the component is injective. The
/// fold is two-to-one off the crease, so it is not, and
/// [`PlasticCrease::reverse_passage`] returns the two merged faces as the receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PlasticCrease {
    crease: Crease,
    /// What the crease's residual became. Testimony about the material, never a value the library
    /// can use to reverse the fold.
    pub dissipation: String,
}

impl PlasticCrease {
    pub fn declared(crease: Crease, dissipation: impl Into<String>) -> Self {
        Self {
            crease,
            dissipation: dissipation.into(),
        }
    }

    pub fn crease(&self) -> &Crease {
        &self.crease
    }

    /// The fold, with nothing retained.
    pub fn apply(&self, point: &FoldPoint) -> Result<FoldPoint, FoldRefusal> {
        self.crease.fold(point)
    }

    /// **Is the reverse passage available from the folded face alone?**
    ///
    /// Refuses an empty probe by name: a receipt over no face is not a receipt, and
    /// `FromTheFaceAlone` returned from nothing would be exactly the certificate minted from an
    /// empty loop that wave 6 found.
    pub fn reverse_passage(
        &self,
        probe: &[FoldPoint],
    ) -> Result<ReversePassageReceipt<FoldPoint>, FoldRefusal> {
        if probe.is_empty() {
            return Err(FoldRefusal::EmptyProbe {
                what: "a plastic crease's reverse passage",
            });
        }
        if probe.len() > PROBE_CEILING {
            return Err(FoldRefusal::ProbeTooWide {
                supplied: probe.len(),
                ceiling: PROBE_CEILING,
            });
        }
        let mut folded = Vec::with_capacity(probe.len());
        for point in probe {
            folded.push(self.crease.fold(point)?);
        }
        for (left, left_face) in folded.iter().enumerate() {
            for (right, right_face) in folded.iter().enumerate().skip(left + 1) {
                if left_face == right_face && probe[left] != probe[right] {
                    return Ok(ReversePassageReceipt::OnlyWithTheResidual {
                        merged_left: probe[left].clone(),
                        merged_right: probe[right].clone(),
                    });
                }
            }
        }
        Ok(ReversePassageReceipt::FromTheFaceAlone {
            faces_checked: probe.len(),
        })
    }
}

// ---------------------------------------------------------------------------------------------
// rotation, shear, inversion
// ---------------------------------------------------------------------------------------------

/// **A Gaussian rational**, the exact chart in which a plane reflection and a plane rotation are
/// rational maps with no angle and no square root.
///
/// Lean counterparts: `cmul`, `cconj`, `cnormSq`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GaussianRational {
    pub real: Rat,
    pub imaginary: Rat,
}

impl GaussianRational {
    pub fn new(real: Rat, imaginary: Rat) -> Self {
        Self { real, imaginary }
    }

    pub fn integers(real: i64, imaginary: i64) -> Self {
        Self {
            real: Rat::from_integer(BigInt::from(real)),
            imaginary: Rat::from_integer(BigInt::from(imaginary)),
        }
    }

    pub fn one() -> Self {
        Self::integers(1, 0)
    }

    pub fn is_zero(&self) -> bool {
        self.real.is_zero() && self.imaginary.is_zero()
    }

    /// `u v`.
    pub fn times(&self, other: &Self) -> Self {
        Self {
            real: &self.real * &other.real - &self.imaginary * &other.imaginary,
            imaginary: &self.real * &other.imaginary + &self.imaginary * &other.real,
        }
    }

    /// `ū`.
    pub fn conjugate(&self) -> Self {
        Self {
            real: self.real.clone(),
            imaginary: -self.imaginary.clone(),
        }
    }

    /// `|u|²`, exact.
    pub fn norm_squared(&self) -> Rat {
        &self.real * &self.real + &self.imaginary * &self.imaginary
    }

    /// The direction as a pair of coordinates.
    pub fn coordinates(&self) -> [Rat; 2] {
        [self.real.clone(), self.imaginary.clone()]
    }
}

/// The exact `2 × 2` matrix of the reflection across the line through the origin with a declared
/// rational direction.
///
/// Its determinant is exactly `−1` for every nonzero direction, which is checked at every call.
pub fn line_reflection_matrix(direction: &GaussianRational) -> Result<[[Rat; 2]; 2], FoldRefusal> {
    let norm = direction.norm_squared();
    if norm.is_zero() {
        return Err(FoldRefusal::DegenerateCrease);
    }
    let (p, q) = (&direction.real, &direction.imaginary);
    let two = Rat::from_integer(BigInt::from(2));
    Ok([
        [(p * p - q * q) / &norm, (&two * p * q) / &norm],
        [(&two * p * q) / &norm, (q * q - p * p) / &norm],
    ])
}

/// **The composite of two line reflections, read as a rotation.**
///
/// Lean counterpart: `lineReflect_comp_eq_rotBy`. Rotation *is* two reflections, exactly over `Q`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RotationReading {
    pub schema: String,
    /// The turn `v ū`: the composite is `z ↦ turn² z / |turn|²`.
    pub turn: GaussianRational,
    /// The exact `2 × 2` matrix of the composite.
    pub matrix: [[Rat; 2]; 2],
    /// `+1`, checked.
    pub determinant: Rat,
    /// `−1` for each of the two reflections, checked.
    pub reflection_determinants: (Rat, Rat),
    /// `c² + s² = 1` for the composite's first column, checked.
    pub is_orthogonal: bool,
    /// The composite is the identity exactly when the turn's imaginary part is zero.
    pub is_identity: bool,
}

fn determinant_two(matrix: &[[Rat; 2]; 2]) -> Rat {
    &matrix[0][0] * &matrix[1][1] - &matrix[0][1] * &matrix[1][0]
}

fn multiply_two(left: &[[Rat; 2]; 2], right: &[[Rat; 2]; 2]) -> [[Rat; 2]; 2] {
    [
        [
            &left[0][0] * &right[0][0] + &left[0][1] * &right[1][0],
            &left[0][0] * &right[0][1] + &left[0][1] * &right[1][1],
        ],
        [
            &left[1][0] * &right[0][0] + &left[1][1] * &right[1][0],
            &left[1][0] * &right[0][1] + &left[1][1] * &right[1][1],
        ],
    ]
}

/// The composite `R_v ∘ R_u` of the reflections across two lines through the origin.
pub fn rotation_from_two_reflections(
    first: &GaussianRational,
    second: &GaussianRational,
) -> Result<RotationReading, FoldRefusal> {
    if first.is_zero() || second.is_zero() {
        return Err(FoldRefusal::DegenerateCrease);
    }
    let matrix_first = line_reflection_matrix(first)?;
    let matrix_second = line_reflection_matrix(second)?;
    let matrix = multiply_two(&matrix_second, &matrix_first);
    let determinant = determinant_two(&matrix);
    let turn = second.times(&first.conjugate());
    let column = &matrix[0][0] * &matrix[0][0] + &matrix[1][0] * &matrix[1][0];
    Ok(RotationReading {
        schema: ROTATION_READING_SCHEMA.to_owned(),
        is_identity: turn.imaginary.is_zero(),
        turn,
        determinant,
        reflection_determinants: (
            determinant_two(&matrix_first),
            determinant_two(&matrix_second),
        ),
        is_orthogonal: column == Rat::one(),
        matrix,
    })
}

/// **A shear changes a squared distance in every neighbourhood of every point.**
///
/// Returns the exact defect `k² t²` on the pair `(p, p + t e_y)`, which is nonzero for every
/// nonzero `k` and `t`. A fold is an exact isometry on each side of its crease; a shear is an
/// isometry on no nonempty open set at all, so it is not a composition of reflections and
/// therefore not a composition of folds.
///
/// Lean counterparts: `shear_changes_a_squared_distance_at_every_point_and_scale`,
/// `no_isometry_is_a_shear`.
pub fn shear_defect(coefficient: &Rat, scale: &Rat) -> Rat {
    coefficient * coefficient * scale * scale
}

/// **Inversion in a sphere**, the third member of Brandon's "division, shear, inversion" triple.
///
/// [proved-standard; cited] That inversion in a sphere is a reflection in a hyperplane of the
/// conformal (Lorentz) model of the ball is the classical statement; it is cited and not
/// formalized. What **is** exact here is [`Inversion::distance_law`], from which cross-ratio
/// invariance follows with every factor cancelling.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "InversionWire")]
pub struct Inversion {
    /// The radius, exact and nonzero. Only `r²` and `r⁴` ever appear, so no root is taken.
    radius: Rat,
}

/// The wire of an [`Inversion`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct InversionWire {
    radius: Rat,
}

impl TryFrom<InversionWire> for Inversion {
    type Error = FoldRefusal;

    fn try_from(wire: InversionWire) -> Result<Self, Self::Error> {
        Inversion::declared(wire.radius)
    }
}

impl Inversion {
    pub fn declared(radius: Rat) -> Result<Self, FoldRefusal> {
        if radius.is_zero() {
            return Err(FoldRefusal::DegenerateInversion);
        }
        Ok(Self { radius })
    }

    /// The declared radius.
    pub fn radius(&self) -> &Rat {
        &self.radius
    }

    /// `x ↦ r² x / ⟨x,x⟩`. Refuses the centre by name.
    pub fn apply(&self, point: &FoldPoint) -> Result<FoldPoint, FoldRefusal> {
        let norm = dot(point.coordinates(), point.coordinates())?;
        if norm.is_zero() {
            return Err(FoldRefusal::InversionAtTheCentre);
        }
        let factor = (&self.radius * &self.radius) / &norm;
        FoldPoint::declared(
            point
                .coordinates()
                .iter()
                .map(|entry| &factor * entry)
                .collect(),
        )
    }

    /// `‖inv x − inv y‖² = r⁴ ‖x − y‖² / (⟨x,x⟩⟨y,y⟩)`, exact over `Q`.
    ///
    /// Lean counterpart: `inversion_distSq`.
    pub fn distance_law(&self, left: &FoldPoint, right: &FoldPoint) -> Result<Rat, FoldRefusal> {
        let norm_left = dot(left.coordinates(), left.coordinates())?;
        let norm_right = dot(right.coordinates(), right.coordinates())?;
        if norm_left.is_zero() || norm_right.is_zero() {
            return Err(FoldRefusal::InversionAtTheCentre);
        }
        let radius_squared = &self.radius * &self.radius;
        let separation = squared_distance(left.coordinates(), right.coordinates())?;
        Ok((&radius_squared * &radius_squared * separation) / (norm_left * norm_right))
    }
}

// ---------------------------------------------------------------------------------------------
// fold against cut on a complex
// ---------------------------------------------------------------------------------------------

/// **A finite two-dimensional cell complex given by its vertices, edges and triangles.**
///
/// [definition] The homology is not computed here: [`CellComplex::graded`] realizes it as a
/// [`GradedCausalComplex`] and [`CellComplex::betti`] reads its invariants through the existing
/// Smith-normal-form owner [`crate::rebase_invariants::rebase_invariants`]. Nothing in this module
/// reimplements a boundary operator or an elimination.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "CellComplexWire")]
pub struct CellComplex {
    lineage: String,
    vertices: usize,
    edges: Vec<[usize; 2]>,
    triangles: Vec<[usize; 3]>,
}

/// The wire of a [`CellComplex`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct CellComplexWire {
    lineage: String,
    vertices: usize,
    edges: Vec<[usize; 2]>,
    triangles: Vec<[usize; 3]>,
}

impl TryFrom<CellComplexWire> for CellComplex {
    type Error = FoldRefusal;

    fn try_from(wire: CellComplexWire) -> Result<Self, Self::Error> {
        CellComplex::declared(wire.lineage, wire.vertices, wire.edges, wire.triangles)
    }
}

impl CellComplex {
    /// A declared complex. Every edge and triangle addresses existing vertices; every triangle's
    /// three edges stand; no cell is repeated; the cell population is inside [`CELL_CEILING`].
    pub fn declared(
        lineage: impl Into<String>,
        vertices: usize,
        mut edges: Vec<[usize; 2]>,
        mut triangles: Vec<[usize; 3]>,
    ) -> Result<Self, FoldRefusal> {
        if vertices == 0 {
            return Err(FoldRefusal::EmptyComplex);
        }
        let cells = vertices
            .checked_add(edges.len())
            .and_then(|sum| sum.checked_add(triangles.len()))
            .ok_or(FoldRefusal::CellPopulationOverflows)?;
        if cells > CELL_CEILING {
            return Err(FoldRefusal::CellPopulationTooWide {
                cells,
                ceiling: CELL_CEILING,
            });
        }
        for edge in &mut edges {
            if edge[0] == edge[1] {
                return Err(FoldRefusal::CollapsedCell);
            }
            edge.sort_unstable();
            if edge[1] >= vertices {
                return Err(FoldRefusal::CellAddressesAnAbsentVertex { vertex: edge[1] });
            }
        }
        let edge_set: BTreeSet<[usize; 2]> = edges.iter().copied().collect();
        if edge_set.len() != edges.len() {
            return Err(FoldRefusal::RepeatedCell);
        }
        for triangle in &mut triangles {
            triangle.sort_unstable();
            if triangle[0] == triangle[1] || triangle[1] == triangle[2] {
                return Err(FoldRefusal::CollapsedCell);
            }
            if triangle[2] >= vertices {
                return Err(FoldRefusal::CellAddressesAnAbsentVertex {
                    vertex: triangle[2],
                });
            }
            for face in [
                [triangle[0], triangle[1]],
                [triangle[0], triangle[2]],
                [triangle[1], triangle[2]],
            ] {
                if !edge_set.contains(&face) {
                    return Err(FoldRefusal::TriangleFaceAbsent { face });
                }
            }
        }
        let triangle_set: BTreeSet<[usize; 3]> = triangles.iter().copied().collect();
        if triangle_set.len() != triangles.len() {
            return Err(FoldRefusal::RepeatedCell);
        }
        edges.sort_unstable();
        triangles.sort_unstable();
        Ok(Self {
            lineage: lineage.into(),
            vertices,
            edges,
            triangles,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn vertex_count(&self) -> usize {
        self.vertices
    }

    pub fn edges(&self) -> &[[usize; 2]] {
        &self.edges
    }

    pub fn triangles(&self) -> &[[usize; 3]] {
        &self.triangles
    }

    /// The Euler characteristic of the cell counts, `V − E + F`.
    pub fn cell_euler_characteristic(&self) -> i64 {
        self.vertices as i64 - self.edges.len() as i64 + self.triangles.len() as i64
    }

    /// Realize the complex as a [`GradedCausalComplex`], the carrier the exact homology owner
    /// consumes.
    pub fn graded(&self) -> Result<GradedCausalComplex, FoldRefusal> {
        let mut complex = GradedCausalComplex::default();
        let event = BTreeSet::from([EventId(1)]);
        let mut vertex_cells = Vec::with_capacity(self.vertices);
        for at in 0..self.vertices {
            vertex_cells.push(complex.found_cell(
                format!("v{at}"),
                event.clone(),
                0,
                CausalChain::default(),
            )?);
        }
        let mut edge_cells: BTreeMap<[usize; 2], CausalCellId> = BTreeMap::new();
        for edge in &self.edges {
            let mut boundary = CausalChain::default();
            boundary.add_term(
                vertex_cells[edge[1]],
                ComparativeMultiplicity::positive(1_u32),
            );
            boundary.add_term(
                vertex_cells[edge[0]],
                ComparativeMultiplicity::negative(1_u32),
            );
            let cell = complex.found_cell(
                format!("e{}-{}", edge[0], edge[1]),
                event.clone(),
                1,
                boundary,
            )?;
            edge_cells.insert(*edge, cell);
        }
        for triangle in &self.triangles {
            let [a, b, c] = *triangle;
            let mut boundary = CausalChain::default();
            // ∂[a,b,c] = [b,c] − [a,c] + [a,b], with the ascending edge as the positive cell.
            boundary.add_term(edge_cells[&[b, c]], ComparativeMultiplicity::positive(1_u32));
            boundary.add_term(edge_cells[&[a, c]], ComparativeMultiplicity::negative(1_u32));
            boundary.add_term(edge_cells[&[a, b]], ComparativeMultiplicity::positive(1_u32));
            complex.found_cell(format!("f{a}-{b}-{c}"), event.clone(), 2, boundary)?;
        }
        Ok(complex)
    }

    /// [definition] **The complex as the core complex `K`** (plan phase 4): its realization
    /// [`Self::graded`] read through [`GradedCausalComplex::core_chart`], one core cell per vertex,
    /// edge and triangle with the same orientation. This type keeps its wire (`lineage`, `vertices`,
    /// `edges`, `triangles`); the rational Betti numbers of the core complex are the free ranks of
    /// [`Self::betti`] (tested).
    pub fn core_chart(&self) -> Result<crate::algebraic::CoreCellChart, FoldRefusal> {
        self.graded()?
            .core_chart()
            .map_err(|refusal| FoldRefusal::Core(Box::new(refusal)))
    }

    /// **The Betti vector, through the existing Smith-normal-form owner.**
    pub fn betti(&self) -> Result<Vec<usize>, FoldRefusal> {
        let graded = self.graded()?;
        let invariants = rebase_invariants(&graded, PivotRule::SmallestMagnitude)?;
        Ok(invariants.betti_vector())
    }

    /// Every edge's exact squared length at a declared placement.
    pub fn edge_lengths(&self, places: &[FoldPoint]) -> Result<Vec<Rat>, FoldRefusal> {
        if places.len() != self.vertices {
            return Err(FoldRefusal::PlacementWidthDisagrees {
                expected: self.vertices,
                supplied: places.len(),
            });
        }
        self.edges
            .iter()
            .map(|edge| {
                squared_distance(
                    places[edge[0]].coordinates(),
                    places[edge[1]].coordinates(),
                )
            })
            .collect()
    }
}

/// **A fold of a complex: a map on vertices that must be a bijection on every cell.**
///
/// Lean counterpart: `ChainTwo.Relabelling`, whose `fold_preserves_betti` is the automorphism
/// statement this reading enacts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellularFold {
    /// The image of each vertex.
    pub image: Vec<usize>,
}

/// What a cellular fold did to the homology. **Three values, because "not a fold" is its own
/// return and is never reported as "preserved".**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FoldHomologyVerdict {
    /// The map is a bijection on cells and every Betti number is unchanged.
    Preserved,
    /// The map is a bijection on cells and a Betti number moved. `ChainTwo.fold_preserves_betti`
    /// says this cannot happen; the arm exists so that a failure is a value and not a silence.
    Moved {
        /// The grades whose Betti number changed.
        grades: Vec<u32>,
    },
    /// The map is not a bijection on cells, so it is not a fold at all and **no homology claim is
    /// made about it.**
    NotAFold,
}

/// What a cellular fold does to the complex: nothing, exactly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellularFoldReading {
    pub schema: String,
    /// True when the vertex map permutes the vertices and carries edges to edges and triangles to
    /// triangles bijectively.
    pub is_cellular_automorphism: bool,
    pub betti_before: Vec<usize>,
    /// The image complex's Betti vector, present only when the map is a cellular automorphism.
    pub betti_after: Option<Vec<usize>>,
    /// The three-valued homology verdict.
    pub homology: FoldHomologyVerdict,
    /// Every edge's exact squared length, before and after, compared edge by edge.
    pub edge_lengths_preserved: bool,
    /// The edges whose length the fold moved, if any.
    pub moved_edges: Vec<[usize; 2]>,
}

/// **Read a fold of a complex.**
///
/// The placement is the geometric realization the crease acts on: when it is supplied, the edge
/// lengths are compared exactly, which is `fold_preserves_intrinsic_length`.
pub fn read_cellular_fold(
    complex: &CellComplex,
    fold: &CellularFold,
    places: Option<&[FoldPoint]>,
) -> Result<CellularFoldReading, FoldRefusal> {
    if fold.image.len() != complex.vertex_count() {
        return Err(FoldRefusal::PlacementWidthDisagrees {
            expected: complex.vertex_count(),
            supplied: fold.image.len(),
        });
    }
    if fold.image.iter().any(|at| *at >= complex.vertex_count()) {
        return Err(FoldRefusal::CellAddressesAnAbsentVertex {
            vertex: fold.image.iter().copied().max().unwrap_or_default(),
        });
    }
    let image_set: BTreeSet<usize> = fold.image.iter().copied().collect();
    let is_permutation = image_set.len() == complex.vertex_count();

    let mut carried_edges = BTreeSet::new();
    for edge in complex.edges() {
        let mut mapped = [fold.image[edge[0]], fold.image[edge[1]]];
        if mapped[0] == mapped[1] {
            carried_edges.clear();
            break;
        }
        mapped.sort_unstable();
        carried_edges.insert(mapped);
    }
    let edges_carried = carried_edges.len() == complex.edges().len()
        && complex.edges().iter().all(|edge| carried_edges.contains(edge));

    let mut carried_triangles = BTreeSet::new();
    for triangle in complex.triangles() {
        let mut mapped = [
            fold.image[triangle[0]],
            fold.image[triangle[1]],
            fold.image[triangle[2]],
        ];
        mapped.sort_unstable();
        if mapped[0] == mapped[1] || mapped[1] == mapped[2] {
            carried_triangles.clear();
            break;
        }
        carried_triangles.insert(mapped);
    }
    let triangles_carried = carried_triangles.len() == complex.triangles().len()
        && complex
            .triangles()
            .iter()
            .all(|triangle| carried_triangles.contains(triangle));

    let is_cellular_automorphism = is_permutation && edges_carried && triangles_carried;

    let betti_before = complex.betti()?;
    let betti_after = if is_cellular_automorphism {
        let after = CellComplex::declared(
            format!("{} / folded", complex.lineage()),
            complex.vertex_count(),
            carried_edges.iter().copied().collect(),
            carried_triangles.iter().copied().collect(),
        )?;
        Some(after.betti()?)
    } else {
        None
    };
    let homology = match &betti_after {
        None => FoldHomologyVerdict::NotAFold,
        Some(after) if *after == betti_before => FoldHomologyVerdict::Preserved,
        Some(after) => FoldHomologyVerdict::Moved {
            grades: (0..betti_before.len().max(after.len()))
                .filter(|grade| {
                    betti_before.get(*grade).copied().unwrap_or_default()
                        != after.get(*grade).copied().unwrap_or_default()
                })
                .map(|grade| grade as u32)
                .collect(),
        },
    };

    let mut moved_edges = Vec::new();
    let mut edge_lengths_preserved = true;
    if let Some(places) = places {
        if places.len() != complex.vertex_count() {
            return Err(FoldRefusal::PlacementWidthDisagrees {
                expected: complex.vertex_count(),
                supplied: places.len(),
            });
        }
        for edge in complex.edges() {
            let before = squared_distance(
                places[edge[0]].coordinates(),
                places[edge[1]].coordinates(),
            )?;
            let mapped = squared_distance(
                places[fold.image[edge[0]]].coordinates(),
                places[fold.image[edge[1]]].coordinates(),
            )?;
            if before != mapped {
                edge_lengths_preserved = false;
                moved_edges.push(*edge);
            }
        }
    }

    Ok(CellularFoldReading {
        schema: CELLULAR_FOLD_SCHEMA.to_owned(),
        is_cellular_automorphism,
        homology,
        betti_before,
        betti_after,
        edge_lengths_preserved,
        moved_edges,
    })
}

/// **One vertex identification a cut destroyed**: the two copies the cut made of one vertex.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CutIdentification {
    /// One copy in the cut complex.
    pub left: usize,
    /// The other.
    pub right: usize,
}

/// **What a cut did, and what reversing it would need.**
///
/// Lean counterpart: `residual_injective_on_fibre`, which is the general law behind
/// [`CutReading::residual_is_strictly_larger_than_a_folds`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CutReading {
    pub schema: String,
    pub betti_before: Vec<usize>,
    pub betti_after: Vec<usize>,
    /// A cut changes the chain complex. When this is false the caller cut nothing.
    pub homology_changed: bool,
    /// Which Betti numbers moved, by grade.
    pub grades_that_moved: Vec<u32>,
    /// The gluing data: which cells the cut separated. **This is the cut's residual.**
    pub gluing: Vec<CutIdentification>,
    /// Regluing the cut complex along that data returns the original, exactly.
    pub regluing_is_exact: bool,
    /// A fold's residual: one bit.
    pub fold_residual_bits: BigUint,
    /// A cut's residual: the code size of the gluing pattern over the cut complex's vertices.
    pub cut_residual_bits: BigUint,
    /// The receipt the whole comparison travels in.
    pub receipt: CostReceipt,
}

impl CutReading {
    /// **The irreversibility comparison.** A fold's residual is one bit; a cut's is the gluing
    /// pattern, which is strictly larger as soon as the cut identified anything at all.
    pub fn residual_is_strictly_larger_than_a_folds(&self) -> bool {
        self.cut_residual_bits > self.fold_residual_bits
    }
}

/// Reglue a cut complex along declared identifications, returning the complex the cut started from.
pub fn reglue(
    cut: &CellComplex,
    gluing: &[CutIdentification],
) -> Result<CellComplex, FoldRefusal> {
    if gluing.len() > PROBE_CEILING {
        return Err(FoldRefusal::ProbeTooWide {
            supplied: gluing.len(),
            ceiling: PROBE_CEILING,
        });
    }
    let mut representative: Vec<usize> = (0..cut.vertex_count()).collect();
    for identification in gluing {
        if identification.left >= cut.vertex_count() || identification.right >= cut.vertex_count() {
            return Err(FoldRefusal::CellAddressesAnAbsentVertex {
                vertex: identification.left.max(identification.right),
            });
        }
        let low = representative[identification.left].min(representative[identification.right]);
        let high = representative[identification.left].max(representative[identification.right]);
        for entry in representative.iter_mut() {
            if *entry == high {
                *entry = low;
            }
        }
    }
    let mut relabel: BTreeMap<usize, usize> = BTreeMap::new();
    for entry in &representative {
        let next = relabel.len();
        relabel.entry(*entry).or_insert(next);
    }
    let vertices = relabel.len();
    let mut edges = BTreeSet::new();
    for edge in cut.edges() {
        let mapped = [
            relabel[&representative[edge[0]]],
            relabel[&representative[edge[1]]],
        ];
        if mapped[0] == mapped[1] {
            return Err(FoldRefusal::CollapsedCell);
        }
        let mut sorted = mapped;
        sorted.sort_unstable();
        edges.insert(sorted);
    }
    let mut triangles = BTreeSet::new();
    for triangle in cut.triangles() {
        let mut mapped = [
            relabel[&representative[triangle[0]]],
            relabel[&representative[triangle[1]]],
            relabel[&representative[triangle[2]]],
        ];
        mapped.sort_unstable();
        if mapped[0] == mapped[1] || mapped[1] == mapped[2] {
            return Err(FoldRefusal::CollapsedCell);
        }
        triangles.insert(mapped);
    }
    CellComplex::declared(
        format!("{} / reglued", cut.lineage()),
        vertices,
        edges.into_iter().collect(),
        triangles.into_iter().collect(),
    )
}

/// **Read a cut: what it did to the homology, and what reversing it needs.**
///
/// Refuses an empty gluing by name: a cut that identified nothing is not a cut, and reporting
/// "homology unchanged" from it would be a verdict about a move nobody made.
pub fn read_cut(
    before: &CellComplex,
    after: &CellComplex,
    gluing: &[CutIdentification],
) -> Result<CutReading, FoldRefusal> {
    if gluing.is_empty() {
        return Err(FoldRefusal::EmptyProbe {
            what: "a cut's gluing data",
        });
    }
    let betti_before = before.betti()?;
    let betti_after = after.betti()?;
    let width = betti_before.len().max(betti_after.len());
    let mut grades_that_moved = Vec::new();
    for grade in 0..width {
        let left = betti_before.get(grade).copied().unwrap_or_default();
        let right = betti_after.get(grade).copied().unwrap_or_default();
        if left != right {
            grades_that_moved.push(grade as u32);
        }
    }
    let reglued = reglue(after, gluing)?;
    let regluing_is_exact = reglued.vertex_count() == before.vertex_count()
        && reglued.edges() == before.edges()
        && reglued.triangles() == before.triangles();

    // The fold's residual is one bit: the fibre of a fold has two elements.
    let fold_residual_bits = code_bits(&BigUint::from(2_u32));
    // The cut's residual is the address of the gluing pattern: each identification names an
    // ordered pair of the cut complex's vertices, and the reversal needs all of them.
    let addresses = BigUint::from(after.vertex_count() as u64);
    let per_identification = code_bits(&addresses) * BigUint::from(2_u32);
    let cut_residual_bits = per_identification * BigUint::from(gluing.len() as u64);

    let receipt = CostReceipt {
        presentation: format!(
            "the cut of {} into {}, with its gluing data",
            before.lineage(),
            after.lineage()
        ),
        bytes: Counted::measured(
            BigUint::from(gluing.len() as u64) * BigUint::from(16_u32),
            "fold::read_cut, two machine addresses per identification",
        ),
        decode_work: Counted::measured(
            BigUint::from(after.vertex_count() as u64),
            "fold::reglue, one union-find pass per vertex",
        ),
        update_work: Counted::measured(
            BigUint::from((after.edges().len() + after.triangles().len()) as u64),
            "fold::reglue, one relabelling per cell above dimension zero",
        ),
        certificate_work: Counted::measured(
            BigUint::from((before.vertex_count() + before.edges().len()) as u64),
            "fold::read_cut, the exact comparison of the reglued complex with the original",
        ),
        residual: Counted::derived(
            cut_residual_bits.clone(),
            "code_bits over the cut complex's vertex addresses, twice per identification",
        ),
    };

    Ok(CutReading {
        schema: CUT_READING_SCHEMA.to_owned(),
        homology_changed: betti_before != betti_after,
        grades_that_moved,
        betti_before,
        betti_after,
        gluing: gluing.to_vec(),
        regluing_is_exact,
        fold_residual_bits,
        cut_residual_bits,
        receipt,
    })
}

/// **Project a cut onto a contact family: the severed pairs become `Outside`.**
///
/// [definition] A cut is a passage that breaks bonds. This returns the family the cut leaves, so
/// that [`crate::physical_occurrence::ConstraintDelta::between`] returns the broken contacts as
/// its own typed delta — the existing B6 owner's, not a second one. Refuses an empty severed set
/// by name.
pub fn severed_contact_family(
    before: &SituatedFamily,
    severed: &BTreeSet<(u32, u32)>,
) -> Result<SituatedFamily, FoldRefusal> {
    if severed.is_empty() {
        return Err(FoldRefusal::EmptyProbe {
            what: "a cut's severed contact set",
        });
    }
    let addressed: BTreeSet<(u32, u32)> =
        before.readings.iter().map(|reading| reading.pair).collect();
    for pair in severed {
        if !addressed.contains(pair) {
            return Err(FoldRefusal::SeveredPairIsNotAddressed { pair: *pair });
        }
    }
    let readings = before
        .readings
        .iter()
        .map(|reading| SituatedPairReading {
            pair: reading.pair,
            class: if severed.contains(&reading.pair) {
                ContactClass::Outside
            } else {
                reading.class
            },
            squared_distance: reading.squared_distance.clone(),
            uncertainty: reading.uncertainty.clone(),
        })
        .collect();
    Ok(SituatedFamily {
        schema: before.schema.clone(),
        occurrence: before.occurrence,
        lineage: format!("{} / cut", before.lineage),
        environment: before.environment.clone(),
        left: before.left,
        right: before.right,
        left_sequence: before.left_sequence.clone(),
        right_sequence: before.right_sequence.clone(),
        aperture: before.aperture.clone(),
        readings,
    })
}

// ---------------------------------------------------------------------------------------------
// crease patterns as hinge frameworks
// ---------------------------------------------------------------------------------------------

/// **A crease pattern in a declared folded state.**
///
/// [definition] The panels are listed by their vertex cycles and are **triangulated by a fan** from
/// each panel's first vertex, so that the framework is a bar-joint framework and the existing
/// [`crate::rigidity_receiver`] Jacobian is the only Jacobian. A body-hinge rigidity matrix would
/// be a second one for the same question, and this module founds none.
///
/// [definition] The fields are public and carry no constructor invariant, because a pattern is a
/// *declaration* and every check it owes — the dimension, the vertex and panel ceilings, that every
/// address exists and that every panel is a polygon — belongs to the reader that does work with it,
/// [`hinge_framework`], which refuses each by name before any bar is founded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CreasePattern {
    pub lineage: String,
    /// The vertices' exact places in the declared folded state.
    pub places: Vec<Vec<Rat>>,
    /// The crease edges: the hinges.
    pub creases: Vec<[usize; 2]>,
    /// Each panel's vertex cycle, in order.
    pub panels: Vec<Vec<usize>>,
}

/// The rigidity reading of a crease pattern read as a hinge framework.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CreasePatternFraming {
    pub schema: String,
    pub jacobian: RigidityJacobian,
    pub reading: RigidityReading,
    /// `dim ker J` minus the trivial motions: the folding motions this pattern admits.
    pub folding_motions: usize,
    /// A pattern carrying a self-stress is **locked**: some bar is redundantly held.
    pub locked: bool,
    /// How many bars came from creases and how many from the panels' complete bracing.
    pub crease_bars: usize,
    pub panel_bars: usize,
    /// Panels whose vertices do not affinely span the ambient space and whose extent exceeds the
    /// dimension: each of these contributes a spurious infinitesimal motion and a self-stress to
    /// the bar-joint model even though the panel is finitely rigid. **Named, never silently
    /// counted as a folding motion.**
    pub planar_panels: Vec<usize>,
}

/// **Read a crease pattern as a bar-joint hinge framework.**
pub fn hinge_framework(pattern: &CreasePattern) -> Result<CreasePatternFraming, FoldRefusal> {
    if pattern.places.is_empty() {
        return Err(FoldRefusal::EmptyComplex);
    }
    if pattern.places.len() > PATTERN_VERTEX_CEILING {
        return Err(FoldRefusal::PatternTooWide {
            vertices: pattern.places.len(),
            ceiling: PATTERN_VERTEX_CEILING,
        });
    }
    let dimension = pattern.places[0].len();
    if dimension == 0 || dimension > DIMENSION_CEILING {
        return Err(FoldRefusal::DimensionTooWide {
            supplied: dimension,
            ceiling: DIMENSION_CEILING,
        });
    }
    for place in &pattern.places {
        if place.len() != dimension {
            return Err(FoldRefusal::DimensionDisagrees {
                expected: dimension,
                supplied: place.len(),
            });
        }
    }
    let configuration = ExactConfiguration::declared(
        dimension,
        pattern
            .places
            .iter()
            .enumerate()
            .map(|(at, place)| (ConstraintVertexId(at as u64 + 1), place.clone())),
    )?;

    let mut bars: BTreeMap<ConstraintEdge, EdgeProvenance> = BTreeMap::new();
    let mut crease_bars = 0usize;
    for crease in &pattern.creases {
        if crease[0] >= pattern.places.len() || crease[1] >= pattern.places.len() {
            return Err(FoldRefusal::CellAddressesAnAbsentVertex {
                vertex: crease[0].max(crease[1]),
            });
        }
        let (edge, _) = ConstraintEdge::new(
            ConstraintVertexId(crease[0] as u64 + 1),
            ConstraintVertexId(crease[1] as u64 + 1),
        )?;
        if bars.insert(edge, EdgeProvenance::Polygonal).is_none() {
            crease_bars += 1;
        }
    }
    let mut panel_bars = 0usize;
    let mut planar_panels = Vec::new();
    for (ordinal, panel) in pattern.panels.iter().enumerate() {
        if panel.len() < 3 {
            return Err(FoldRefusal::PanelIsNotAPolygon { extent: panel.len() });
        }
        if panel.len() > PANEL_EXTENT_CEILING {
            return Err(FoldRefusal::PanelTooWide {
                extent: panel.len(),
                ceiling: PANEL_EXTENT_CEILING,
            });
        }
        for at in panel {
            if *at >= pattern.places.len() {
                return Err(FoldRefusal::CellAddressesAnAbsentVertex { vertex: *at });
            }
        }
        // A rigid panel is a rigid body, and the bar-joint presentation of a rigid body is every
        // pair of its vertices. The extent is bounded above, so this quadratic loop is bounded.
        for (at, left) in panel.iter().enumerate() {
            for right in panel.iter().skip(at + 1) {
                if left == right {
                    continue;
                }
                let (edge, _) = ConstraintEdge::new(
                    ConstraintVertexId(*left as u64 + 1),
                    ConstraintVertexId(*right as u64 + 1),
                )?;
                if bars.insert(edge, EdgeProvenance::AdmittedContact).is_none() {
                    panel_bars += 1;
                }
            }
        }
        if panel.len() > dimension && panel_affine_span(&pattern.places, panel)? < dimension {
            planar_panels.push(ordinal);
        }
    }
    if bars.is_empty() {
        return Err(FoldRefusal::EmptyProbe {
            what: "a crease pattern's bar set",
        });
    }

    let jacobian = RigidityJacobian::found(pattern.lineage.clone(), &configuration, &bars)?;
    let reading = rigidity_reading(&jacobian)?;
    Ok(CreasePatternFraming {
        schema: CREASE_PATTERN_SCHEMA.to_owned(),
        folding_motions: reading.internal_motion_dimension,
        locked: reading.self_stress_dimension > 0,
        crease_bars,
        panel_bars,
        planar_panels,
        jacobian,
        reading,
    })
}

/// The exact affine span dimension of one panel's vertices.
fn panel_affine_span(places: &[Vec<Rat>], panel: &[usize]) -> Result<usize, FoldRefusal> {
    let Some((first, rest)) = panel.split_first() else {
        return Ok(0);
    };
    let origin = &places[*first];
    let rows: Vec<Vec<Rat>> = rest
        .iter()
        .map(|at| {
            places[*at]
                .iter()
                .zip(origin)
                .map(|(entry, base)| entry - base)
                .collect()
        })
        .collect();
    if rows.is_empty() {
        return Ok(0);
    }
    let width = origin.len();
    let matrix = ExactRatMatrix::shaped(rows.len(), width, rows)
        .map_err(|error| FoldRefusal::Rigidity(RigidityError::Linear(error)))?;
    matrix
        .rank()
        .map_err(|error| FoldRefusal::Rigidity(RigidityError::Linear(error)))
}

/// **A single vertex's crease directions, exactly over `Q`.**
///
/// Lean counterparts: `kawasakiTurn`, `reflectPairs`, `kawasaki_iff`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "KawasakiVertexWire")]
pub struct KawasakiVertex {
    directions: Vec<GaussianRational>,
}

/// The wire of a [`KawasakiVertex`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct KawasakiVertexWire {
    directions: Vec<GaussianRational>,
}

impl TryFrom<KawasakiVertexWire> for KawasakiVertex {
    type Error = FoldRefusal;

    fn try_from(wire: KawasakiVertexWire) -> Result<Self, Self::Error> {
        KawasakiVertex::declared(wire.directions)
    }
}

impl KawasakiVertex {
    /// A declared vertex: an even, nonzero number of nonzero crease directions in cyclic order,
    /// inside the pattern ceiling.
    pub fn declared(directions: Vec<GaussianRational>) -> Result<Self, FoldRefusal> {
        if directions.is_empty() {
            return Err(FoldRefusal::EmptyProbe {
                what: "a single-vertex crease pattern",
            });
        }
        if !directions.len().is_multiple_of(2) {
            return Err(FoldRefusal::VertexDegreeIsOdd {
                degree: directions.len(),
            });
        }
        if directions.len() > PATTERN_VERTEX_CEILING {
            return Err(FoldRefusal::PatternTooWide {
                vertices: directions.len(),
                ceiling: PATTERN_VERTEX_CEILING,
            });
        }
        if directions.iter().any(GaussianRational::is_zero) {
            return Err(FoldRefusal::DegenerateCrease);
        }
        Ok(Self { directions })
    }

    pub fn degree(&self) -> usize {
        self.directions.len()
    }

    pub fn directions(&self) -> &[GaussianRational] {
        &self.directions
    }

    /// **The accumulated turn**: `∏ (d_{2k} d̄_{2k−1})`, exact.
    pub fn turn(&self) -> GaussianRational {
        let mut turn = GaussianRational::one();
        for pair in self.directions.chunks_exact(2) {
            turn = pair[1].times(&pair[0].conjugate()).times(&turn);
        }
        turn
    }

    /// **Kawasaki's condition, with no angle**: the composite of the crease reflections is the
    /// identity exactly when the turn's imaginary part is zero.
    ///
    /// Lean counterpart: `kawasaki_iff`.
    pub fn is_flat_foldable(&self) -> bool {
        self.turn().imaginary.is_zero()
    }
}

/// **A mountain/valley assignment of a single vertex.**
///
/// Lean counterparts: `mountains`, `valleys`, `MaekawaBalanced`, `maekawa_iff_mountain_count`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "MaekawaAssignmentWire")]
pub struct MaekawaAssignment {
    /// `true` is a mountain.
    creases: Vec<bool>,
}

/// The wire of a [`MaekawaAssignment`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct MaekawaAssignmentWire {
    creases: Vec<bool>,
}

impl TryFrom<MaekawaAssignmentWire> for MaekawaAssignment {
    type Error = FoldRefusal;

    fn try_from(wire: MaekawaAssignmentWire) -> Result<Self, Self::Error> {
        MaekawaAssignment::declared(wire.creases)
    }
}

impl MaekawaAssignment {
    pub fn declared(creases: Vec<bool>) -> Result<Self, FoldRefusal> {
        if creases.is_empty() {
            return Err(FoldRefusal::EmptyProbe {
                what: "a mountain/valley assignment",
            });
        }
        if !creases.len().is_multiple_of(2) {
            return Err(FoldRefusal::VertexDegreeIsOdd {
                degree: creases.len(),
            });
        }
        if creases.len() > PATTERN_VERTEX_CEILING {
            return Err(FoldRefusal::PatternTooWide {
                vertices: creases.len(),
                ceiling: PATTERN_VERTEX_CEILING,
            });
        }
        Ok(Self { creases })
    }

    pub fn degree(&self) -> usize {
        self.creases.len()
    }

    /// `n`, where the degree is `2n`.
    pub fn half_degree(&self) -> usize {
        self.creases.len() / 2
    }

    pub fn mountains(&self) -> usize {
        self.creases.iter().filter(|mountain| **mountain).count()
    }

    pub fn valleys(&self) -> usize {
        self.creases.len() - self.mountains()
    }

    /// `M − V`, exact and signed.
    pub fn balance(&self) -> BigInt {
        BigInt::from(self.mountains() as i64) - BigInt::from(self.valleys() as i64)
    }

    /// **Maekawa's law**: `M − V = ±2`, which at a degree-`2n` vertex is exactly `M = n ± 1`.
    ///
    /// Lean counterpart: `maekawa_iff_mountain_count`.
    pub fn is_balanced(&self) -> bool {
        let balance = self.balance();
        balance == BigInt::from(2) || balance == BigInt::from(-2)
    }

    /// The count form of the same law, checked against [`Self::is_balanced`] at every call site
    /// that uses both.
    pub fn mountain_count_form(&self) -> bool {
        let half = self.half_degree();
        self.mountains() == half + 1 || (half >= 1 && self.mountains() == half - 1)
    }
}

/// **The verdict on a vertex's flat-foldability.** It never affirms.
///
/// [proved-standard; cited] Deciding whether a crease pattern folds flat is NP-hard (Bern and
/// Hayes, *The complexity of flat origami*, SODA 1996), and the obstruction is the global layer
/// ordering, not the local angle and assignment laws. So the local laws can **refute** and a
/// bounded search over layer orderings returns its bound; neither affirms.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum FlatFoldabilityVerdict {
    /// Kawasaki's condition fails at this vertex: it does not fold flat, and that is a theorem.
    RefutedByKawasaki {
        /// The turn's imaginary part, which a flat-foldable vertex would have to make zero.
        turn_imaginary: Rat,
    },
    /// Maekawa's law fails on the assignment: this assignment does not fold flat.
    RefutedByMaekawa {
        mountains: usize,
        valleys: usize,
        balance: BigInt,
    },
    /// Both local laws hold. **This is not an affirmation.** The layer ordering was searched to
    /// the declared bound and no valid one was exhibited, so nothing is claimed.
    NotDecidedWithinBound {
        /// How many orderings the caller admitted examining.
        bound: usize,
        /// How many the search actually examined before the bound.
        orderings_examined: usize,
        /// The total number of layer orderings at this degree, exact. It is a factorial.
        orderings_total: BigUint,
        /// Why nothing is claimed.
        why: String,
    },
}

/// **Decide what can be decided about a single vertex's flat-foldability.**
pub fn flat_foldability(
    vertex: &KawasakiVertex,
    assignment: &MaekawaAssignment,
    bound: usize,
) -> Result<FlatFoldabilityVerdict, FoldRefusal> {
    if vertex.degree() != assignment.degree() {
        return Err(FoldRefusal::AssignmentDegreeDisagrees {
            vertex: vertex.degree(),
            assignment: assignment.degree(),
        });
    }
    let turn = vertex.turn();
    if !turn.imaginary.is_zero() {
        return Ok(FlatFoldabilityVerdict::RefutedByKawasaki {
            turn_imaginary: turn.imaginary,
        });
    }
    if !assignment.is_balanced() {
        return Ok(FlatFoldabilityVerdict::RefutedByMaekawa {
            mountains: assignment.mountains(),
            valleys: assignment.valleys(),
            balance: assignment.balance(),
        });
    }
    if vertex.degree() > LAYER_ORDERING_DEGREE_CEILING {
        return Err(FoldRefusal::VertexDegreeTooWideForOrdering {
            degree: vertex.degree(),
            ceiling: LAYER_ORDERING_DEGREE_CEILING,
        });
    }
    let mut orderings_total = BigUint::one();
    for at in 1..=vertex.degree() {
        orderings_total *= BigUint::from(at as u64);
    }
    Ok(FlatFoldabilityVerdict::NotDecidedWithinBound {
        bound,
        orderings_examined: bound.min(vertex.degree()),
        orderings_total,
        why: "the local laws are necessary and not sufficient; deciding a global layer ordering \
              is NP-hard (Bern and Hayes 1996) and this owner exhibits no certificate"
            .to_owned(),
    })
}

// ---------------------------------------------------------------------------------------------
// the fold catastrophe
// ---------------------------------------------------------------------------------------------

/// **The fold catastrophe's normal form, `V_a(x) = x³/3 − a x`.**
///
/// Lean counterparts: `foldPotential`, `foldForce`, `foldStiffness`, `foldEquilibria_iff`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FoldCatastrophe {
    /// The exact rational parameter.
    pub parameter: Rat,
}

/// The exact equilibrium reading of one member of the family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EquilibriumReading {
    pub schema: String,
    pub parameter: Rat,
    /// How many equilibria: `2` above the threshold, `1` at it, `0` below.
    pub equilibria: u32,
    /// How many are stable, by the exact sign of `V'' = 2x`.
    pub stable: u32,
    /// How many are unstable.
    pub unstable: u32,
    /// True at `a = 0`: the two equilibria have merged and `V''` vanishes there.
    pub degenerate: bool,
    /// The window the Sturm count ran over, whose endpoints are proved not to be roots.
    pub window: ExactInterval,
}

impl FoldCatastrophe {
    pub fn declared(parameter: Rat) -> Self {
        Self { parameter }
    }

    /// `V'_a(x) = x² − a`, cleared to an exact integer polynomial.
    pub fn force_polynomial(&self) -> Result<IntegerPolynomial, FoldRefusal> {
        let denominator = self.parameter.denom().clone();
        let numerator = self.parameter.numer().clone();
        Ok(IntegerPolynomial::new(vec![
            -numerator,
            BigInt::zero(),
            denominator,
        ])?)
    }

    /// **Count the equilibria exactly, with the Sturm owner, and decide stability by the sign of
    /// `V''`.**
    ///
    /// The roots are `±√a` and are irrational in general; none is ever formed. The count comes
    /// from [`holonics::exact_value::SturmChain`] on two windows whose endpoints are proved not to be
    /// roots, and the stability of each root is the sign of the window it sits in, because
    /// `V''(x) = 2x`.
    pub fn equilibria(&self) -> Result<EquilibriumReading, FoldRefusal> {
        let zero = Rat::zero();
        let bound = Rat::one() + self.parameter.abs();
        let window = ExactInterval::new(-bound.clone(), bound.clone())?;
        let polynomial = self.force_polynomial()?;
        let chain = SturmChain::of(&polynomial)?;

        if self.parameter.is_zero() {
            // `V'(x) = x²` has the double root `0`, where `V''` also vanishes. The Sturm count
            // is of *distinct* roots, so it returns one; the window's endpoints are `±1` and
            // neither is a root.
            let count = chain.distinct_root_count(&window)?;
            return Ok(EquilibriumReading {
                schema: EQUILIBRIUM_READING_SCHEMA.to_owned(),
                parameter: self.parameter.clone(),
                equilibria: count,
                stable: 0,
                unstable: 0,
                degenerate: true,
                window,
            });
        }
        if self.parameter.is_negative() {
            let count = chain.distinct_root_count(&window)?;
            return Ok(EquilibriumReading {
                schema: EQUILIBRIUM_READING_SCHEMA.to_owned(),
                parameter: self.parameter.clone(),
                equilibria: count,
                stable: 0,
                unstable: 0,
                degenerate: false,
                window,
            });
        }
        // `a > 0`: `V'(0) = −a ≠ 0` and `V'(±bound) = bound² − a > 0`, so neither endpoint of
        // either window is a root and the two counts are exact.
        let upper = ExactInterval::new(zero.clone(), bound.clone())?;
        let lower = ExactInterval::new(-bound, zero)?;
        let stable = chain.distinct_root_count(&upper)?;
        let unstable = chain.distinct_root_count(&lower)?;
        Ok(EquilibriumReading {
            schema: EQUILIBRIUM_READING_SCHEMA.to_owned(),
            parameter: self.parameter.clone(),
            equilibria: stable + unstable,
            stable,
            unstable,
            degenerate: false,
            window,
        })
    }
}

/// **A declared constitutive model of one crease, with typed units.**
///
/// [definition] Its approximations, stated affirmatively:
///
/// 1. the hinge's restoring torque is modelled by the declared polynomial `κ (u² − u₀²)` in the
///    opening coordinate `u` — two terms of an expansion about the flat state, not a trigonometric
///    constitutive law;
/// 2. the panels are rigid, and the crease's finite thickness and its parabolic curvature are not
///    modelled at all;
/// 3. gravity acts as one constant torque `m g ℓ` with `ℓ` a declared lever arm, and the load is
///    carried as a torque with the same dimension as `κ`, which the constructor checks;
/// 4. the reading is quasi-static: no inertia, no rate dependence, no damping, and stability is
///    read from the sign of `V''` alone;
/// 5. the opening coordinate `u` is the rational parametrization `t = tan(θ/2)` of the dihedral,
///    which keeps every quantity in `Q` and is exact, not a small-angle expansion.
///
/// [interpretation] Brandon's measurement idea — reading gravity from the fine motion of a crease
/// lattice, since the angular offset grows with distance from the crease — is the calibrated
/// receiver this model would serve. What such a receiver would owe, and does not yet have here, is:
/// a measured `κ` for the actual material with its uncertainty; a measured `u₀`; an independent
/// measurement of the lever arm `ℓ`; a declared temperature and its effect on `κ`; and a noise
/// floor for the displacement reading, against which the exact `4 ℓ² t² / (1 + t²)` lever law is
/// the signal. None of those is supplied, and no measurement is claimed.
///
/// [definition] The fields are private because the invariant — a strictly positive stiffness and a
/// load carrying the stiffness's own dimension — is what makes the threshold a comparison at all,
/// and a direct struct literal would bypass it. The type carries no `Deserialize`, so
/// [`CreaseModel::declared`] is the only route in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CreaseModel {
    stiffness: Quantity,
    flat_opening: Rat,
    load: Quantity,
}

impl CreaseModel {
    /// A declared model. Refuses a load whose dimension is not the stiffness's, and a
    /// nonpositive stiffness.
    pub fn declared(
        stiffness: Quantity,
        flat_opening: Rat,
        load: Quantity,
    ) -> Result<Self, FoldRefusal> {
        if stiffness.dimension() != load.dimension() {
            return Err(FoldRefusal::CreaseModelUnitsDisagree {
                stiffness: stiffness.dimension().render(),
                load: load.dimension().render(),
            });
        }
        if !stiffness.parts().0.is_positive() {
            return Err(FoldRefusal::NonpositiveStiffness);
        }
        Ok(Self {
            stiffness,
            flat_opening,
            load,
        })
    }

    /// The torque dimension the model is stated in.
    pub fn dimension(&self) -> &Dimension {
        self.stiffness.dimension()
    }

    /// The hinge stiffness `κ`, a torque.
    pub fn stiffness(&self) -> &Quantity {
        &self.stiffness
    }

    /// The flat-state opening `u₀`, dimensionless.
    pub fn flat_opening(&self) -> &Rat {
        &self.flat_opening
    }

    /// The gravity load `m g ℓ`, a torque in the stiffness's units.
    pub fn load(&self) -> &Quantity {
        &self.load
    }

    /// **The exact threshold `κ u₀²`**: the load at which the held equilibrium disappears.
    ///
    /// Lean counterpart: `held_equilibrium_iff_load_le_threshold`.
    pub fn threshold(&self) -> Result<Quantity, FoldRefusal> {
        let square = &self.flat_opening * &self.flat_opening;
        // `parts` is the only unconditional reader and never hands out a magnitude without its
        // dimension; `rational` is for dimensionless quantities and a torque is not one.
        let (value, dimension) = self.stiffness.parts();
        Ok(Quantity::new(value * square, dimension.clone()))
    }

    /// The fold catastrophe's own parameter, `a = u₀² − load/κ`, dimensionless and exact.
    pub fn reduced_parameter(&self) -> Result<Rat, FoldRefusal> {
        // The ratio of two quantities of the same dimension is dimensionless, and the constructor
        // has already refused a load whose dimension is not the stiffness's, so this division is
        // the exact dimensionless reduced parameter and nothing is discarded.
        let stiffness = self.stiffness.parts().0.clone();
        let load = self.load.parts().0.clone();
        Ok(&self.flat_opening * &self.flat_opening - load / stiffness)
    }

    /// **Does a held equilibrium exist?** Exactly when `load ≤ κ u₀²`.
    pub fn held_equilibrium_exists(&self) -> Result<bool, FoldRefusal> {
        Ok(!self.reduced_parameter()?.is_negative())
    }

    /// The equilibrium reading of the model, through the fold catastrophe's own owner.
    pub fn equilibria(&self) -> Result<EquilibriumReading, FoldRefusal> {
        FoldCatastrophe::declared(self.reduced_parameter()?).equilibria()
    }
}

/// A mass–length–time base for the crease model's torques.
pub fn mechanical_base() -> Result<BaseUnits, QuantityError> {
    BaseUnits::declare(["kg", "m", "s"])
}

/// The torque dimension `M L² T⁻²` over [`mechanical_base`].
pub fn torque_dimension(base: &BaseUnits) -> Result<Dimension, QuantityError> {
    base.integer_dimension(&[1, 2, -2])
}

/// **The rational parametrization of a plane rotation**, `t = tan(θ/2)`: `(cos θ, sin θ)` exactly.
///
/// Lean counterparts: `rotCos`, `rotSin`, `rationalRotation_orthogonal`.
pub fn rational_rotation(half_angle_tangent: &Rat) -> (Rat, Rat) {
    let square = half_angle_tangent * half_angle_tangent;
    let denominator = Rat::one() + &square;
    (
        (Rat::one() - &square) / &denominator,
        (Rat::from_integer(BigInt::from(2)) * half_angle_tangent) / &denominator,
    )
}

/// **Brandon's lever arm, exactly**: the squared displacement of a point at perpendicular distance
/// `ℓ` from the crease when the crease opens by the rotation parametrized by `t`.
///
/// It is `4 ℓ² t² / (1 + t²)`, exactly quadratic in `ℓ`, so the displacement itself is exactly
/// proportional to the distance from the crease. Nothing here is a small-angle expansion.
///
/// Lean counterparts: `displacementSq`, `displacementSq_eq`, `displacementSq_scales_with_lever`.
pub fn opening_displacement_squared(distance: &Rat, half_angle_tangent: &Rat) -> Rat {
    let (cosine, sine) = rational_rotation(half_angle_tangent);
    let along = &cosine * distance - distance;
    let across = &sine * distance;
    &along * &along + &across * &across
}

// ---------------------------------------------------------------------------------------------
// the protein backbone
// ---------------------------------------------------------------------------------------------

/// One residue's three backbone atoms, as exact rational places.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BackboneResidue {
    /// `_atom_site.label_seq_id` of the source deposit.
    pub source_ordinal: i32,
    pub monomer: String,
    /// The amide nitrogen.
    pub nitrogen: Vec<Rat>,
    /// The alpha carbon.
    pub alpha_carbon: Vec<Rat>,
    /// The carbonyl carbon.
    pub carbon: Vec<Rat>,
}

/// **The protein backbone as rigid origami of a one-dimensional linkage.**
///
/// [definition] Fixed bond lengths, fixed bond angles and a **declared planar `ω`**. The bars:
///
/// * bonds `N–CA`, `CA–C` inside each residue and `C–N` between them: `3r − 1`;
/// * angle bars `N–C` at each `CA`, `CA–N` at each `C` and `C–CA` at each `N`: `3r − 2`;
/// * planarity bars `CA–CA` across each peptide unit, which *is* the declaration that `ω` is
///   planar: `r − 1`.
///
/// Total `7r − 4`, against `9r` coordinates and six trivial motions: the predicted internal
/// freedom is `2(r − 1)`, the `φ`/`ψ` dihedrals. That prediction is **measured** against the
/// presented configuration, never assumed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "BackboneChainWire")]
pub struct BackboneChain {
    lineage: String,
    residues: Vec<BackboneResidue>,
}

/// The wire of a [`BackboneChain`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct BackboneChainWire {
    lineage: String,
    residues: Vec<BackboneResidue>,
}

impl TryFrom<BackboneChainWire> for BackboneChain {
    type Error = FoldRefusal;

    fn try_from(wire: BackboneChainWire) -> Result<Self, Self::Error> {
        BackboneChain::declared(wire.lineage, wire.residues)
    }
}

/// How one backbone atom is addressed inside the chain.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BackboneAtom {
    /// The amide nitrogen.
    Nitrogen,
    /// The alpha carbon.
    AlphaCarbon,
    /// The carbonyl carbon.
    Carbon,
}

impl BackboneAtom {
    const fn offset(self) -> usize {
        match self {
            BackboneAtom::Nitrogen => 0,
            BackboneAtom::AlphaCarbon => 1,
            BackboneAtom::Carbon => 2,
        }
    }
}

impl BackboneChain {
    /// A declared chain. Refuses an empty chain, a window above the ceiling and a residue whose
    /// three atoms are not all three-dimensional.
    pub fn declared(
        lineage: impl Into<String>,
        residues: Vec<BackboneResidue>,
    ) -> Result<Self, FoldRefusal> {
        if residues.is_empty() {
            return Err(FoldRefusal::EmptyProbe {
                what: "a backbone chain",
            });
        }
        if residues.len() > BACKBONE_RESIDUE_CEILING {
            return Err(FoldRefusal::BackboneWindowTooWide {
                residues: residues.len(),
                ceiling: BACKBONE_RESIDUE_CEILING,
            });
        }
        for residue in &residues {
            for place in [&residue.nitrogen, &residue.alpha_carbon, &residue.carbon] {
                if place.len() != 3 {
                    return Err(FoldRefusal::NotThreeDimensional {
                        supplied: place.len(),
                    });
                }
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            residues,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn residues(&self) -> &[BackboneResidue] {
        &self.residues
    }

    pub fn residue_count(&self) -> usize {
        self.residues.len()
    }

    /// `3r` atoms.
    pub fn atom_count(&self) -> usize {
        self.residues.len() * 3
    }

    /// `7r − 4`, the itemized bar count. Exact and signed: it is negative only for `r = 0`, which
    /// the constructor refuses.
    pub fn bar_count(&self) -> i64 {
        7 * self.residues.len() as i64 - 4
    }

    /// The block ordinal of one atom.
    pub fn atom_index(&self, residue: usize, atom: BackboneAtom) -> Result<usize, FoldRefusal> {
        if residue >= self.residues.len() {
            return Err(FoldRefusal::ResidueAbsent { residue });
        }
        Ok(residue * 3 + atom.offset())
    }

    /// The place of one atom.
    pub fn place(&self, residue: usize, atom: BackboneAtom) -> Result<&[Rat], FoldRefusal> {
        let residue = self
            .residues
            .get(residue)
            .ok_or(FoldRefusal::ResidueAbsent { residue })?;
        Ok(match atom {
            BackboneAtom::Nitrogen => &residue.nitrogen,
            BackboneAtom::AlphaCarbon => &residue.alpha_carbon,
            BackboneAtom::Carbon => &residue.carbon,
        })
    }

    /// The atom places in block order.
    pub fn places(&self) -> Vec<Vec<Rat>> {
        self.residues
            .iter()
            .flat_map(|residue| {
                [
                    residue.nitrogen.clone(),
                    residue.alpha_carbon.clone(),
                    residue.carbon.clone(),
                ]
            })
            .collect()
    }

    /// The exact configuration of the whole window.
    pub fn configuration(&self) -> Result<ExactConfiguration, FoldRefusal> {
        Ok(ExactConfiguration::declared(
            3,
            self.places()
                .into_iter()
                .enumerate()
                .map(|(at, place)| (ConstraintVertexId(at as u64 + 1), place)),
        )?)
    }

    fn edge(&self, left: usize, right: usize) -> Result<ConstraintEdge, FoldRefusal> {
        Ok(ConstraintEdge::new(
            ConstraintVertexId(left as u64 + 1),
            ConstraintVertexId(right as u64 + 1),
        )?
        .0)
    }

    /// **The bars of the fixed-length, fixed-angle, planar-`ω` model.**
    pub fn bars(&self) -> Result<BTreeMap<ConstraintEdge, EdgeProvenance>, FoldRefusal> {
        let mut bars = BTreeMap::new();
        for at in 0..self.residues.len() {
            let n = self.atom_index(at, BackboneAtom::Nitrogen)?;
            let ca = self.atom_index(at, BackboneAtom::AlphaCarbon)?;
            let c = self.atom_index(at, BackboneAtom::Carbon)?;
            bars.insert(self.edge(n, ca)?, EdgeProvenance::Polygonal);
            bars.insert(self.edge(ca, c)?, EdgeProvenance::Polygonal);
            // the bond angle at CA
            bars.insert(self.edge(n, c)?, EdgeProvenance::AdmittedContact);
            if at + 1 < self.residues.len() {
                let next_n = self.atom_index(at + 1, BackboneAtom::Nitrogen)?;
                let next_ca = self.atom_index(at + 1, BackboneAtom::AlphaCarbon)?;
                bars.insert(self.edge(c, next_n)?, EdgeProvenance::Polygonal);
                // the bond angle at C, and the bond angle at the next N
                bars.insert(self.edge(ca, next_n)?, EdgeProvenance::AdmittedContact);
                bars.insert(self.edge(c, next_ca)?, EdgeProvenance::AdmittedContact);
                // the declared planar omega
                bars.insert(self.edge(ca, next_ca)?, EdgeProvenance::AdmittedContact);
            }
        }
        Ok(bars)
    }

    /// The within-chain contact bars at a declared sequence separation and squared aperture.
    ///
    /// Refuses a separation below two by name: that would name the covalent step, which is already
    /// a bar and is not a contact. An **empty** return is a real reading and is not refused — a
    /// window may genuinely carry no contact at the declared aperture, and reporting that is not
    /// the same as reporting nothing. The consumer that must not run on an empty probe is
    /// [`PlasticCrease::reverse_passage`], not this.
    pub fn contact_bars(
        &self,
        minimum_separation: u32,
        squared_aperture: &Rat,
    ) -> Result<BTreeMap<ConstraintEdge, EdgeProvenance>, FoldRefusal> {
        if minimum_separation < 2 {
            return Err(FoldRefusal::SeparationIsCovalent {
                separation: minimum_separation,
            });
        }
        let mut bars = BTreeMap::new();
        let places = self.places();
        for left in 0..self.residues.len() {
            for right in (left + minimum_separation as usize)..self.residues.len() {
                for left_atom in [
                    BackboneAtom::Nitrogen,
                    BackboneAtom::AlphaCarbon,
                    BackboneAtom::Carbon,
                ] {
                    for right_atom in [
                        BackboneAtom::Nitrogen,
                        BackboneAtom::AlphaCarbon,
                        BackboneAtom::Carbon,
                    ] {
                        let a = self.atom_index(left, left_atom)?;
                        let b = self.atom_index(right, right_atom)?;
                        if squared_distance(&places[a], &places[b])? <= *squared_aperture {
                            bars.insert(self.edge(a, b)?, EdgeProvenance::AdmittedContact);
                        }
                    }
                }
            }
        }
        Ok(bars)
    }

    /// **The hinge framework of the backbone, measured.**
    pub fn framework(
        &self,
        extra: &BTreeMap<ConstraintEdge, EdgeProvenance>,
    ) -> Result<BackboneFraming, FoldRefusal> {
        let configuration = self.configuration()?;
        let mut bars = self.bars()?;
        let backbone_bars = bars.len();
        for (edge, provenance) in extra {
            bars.insert(*edge, *provenance);
        }
        let contact_bars = bars.len() - backbone_bars;
        let jacobian = RigidityJacobian::found(self.lineage.clone(), &configuration, &bars)?;
        let reading = rigidity_reading(&jacobian)?;
        let predicted_internal = 2 * self.residues.len() as i64 - 2;
        Ok(BackboneFraming {
            schema: BACKBONE_FRAMING_SCHEMA.to_owned(),
            residues: self.residues.len(),
            backbone_bars,
            contact_bars,
            predicted_internal,
            measured_internal: reading.internal_motion_dimension,
            prediction_holds: extra.is_empty()
                && reading.internal_motion_dimension as i64 == predicted_internal,
            locked: reading.self_stress_dimension > 0,
            reading,
        })
    }

    /// The exact dihedral about the bond from the second to the third of four declared atoms.
    fn dihedral_of(&self, atoms: [(usize, BackboneAtom); 4]) -> Result<ExactDihedral, FoldRefusal> {
        let mut places = Vec::with_capacity(4);
        for (residue, atom) in atoms {
            places.push(self.place(residue, atom)?.to_vec());
        }
        exact_dihedral(&places[0], &places[1], &places[2], &places[3])
    }

    /// `φ` of a residue: the dihedral `C(i−1) − N(i) − CA(i) − C(i)`. Absent at the first residue.
    pub fn phi(&self, residue: usize) -> Result<ExactDihedral, FoldRefusal> {
        if residue == 0 {
            return Err(FoldRefusal::DihedralAbsentAtTheTerminus { residue });
        }
        self.dihedral_of([
            (residue - 1, BackboneAtom::Carbon),
            (residue, BackboneAtom::Nitrogen),
            (residue, BackboneAtom::AlphaCarbon),
            (residue, BackboneAtom::Carbon),
        ])
    }

    /// `ψ` of a residue: the dihedral `N(i) − CA(i) − C(i) − N(i+1)`. Absent at the last residue.
    pub fn psi(&self, residue: usize) -> Result<ExactDihedral, FoldRefusal> {
        if residue + 1 >= self.residues.len() {
            return Err(FoldRefusal::DihedralAbsentAtTheTerminus { residue });
        }
        self.dihedral_of([
            (residue, BackboneAtom::Nitrogen),
            (residue, BackboneAtom::AlphaCarbon),
            (residue, BackboneAtom::Carbon),
            (residue + 1, BackboneAtom::Nitrogen),
        ])
    }

    /// `ω` of a residue: the dihedral `CA(i) − C(i) − N(i+1) − CA(i+1)`, which the model declares
    /// planar. Reading it is how the declaration is checked against the deposit.
    pub fn omega(&self, residue: usize) -> Result<ExactDihedral, FoldRefusal> {
        if residue + 1 >= self.residues.len() {
            return Err(FoldRefusal::DihedralAbsentAtTheTerminus { residue });
        }
        self.dihedral_of([
            (residue, BackboneAtom::AlphaCarbon),
            (residue, BackboneAtom::Carbon),
            (residue + 1, BackboneAtom::Nitrogen),
            (residue + 1, BackboneAtom::AlphaCarbon),
        ])
    }

    /// **A pivot move: the tail rotated about a chain axis, as two reflections.**
    pub fn pivot(&self, move_: &PivotMove) -> Result<PivotReading, FoldRefusal> {
        move_.apply(&self.places(), &self.bars()?)
    }
}

/// The measured hinge framework of a backbone window.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BackboneFraming {
    pub schema: String,
    pub residues: usize,
    /// `7r − 4`, the bars of the fixed-length, fixed-angle, planar-`ω` model.
    pub backbone_bars: usize,
    /// The contact bars added on top of them.
    pub contact_bars: usize,
    /// `2(r − 1)`, the free chain's prediction.
    pub predicted_internal: i64,
    /// What the exact Jacobian actually returns.
    pub measured_internal: usize,
    /// True when there are no contact bars and the measurement equals the prediction.
    pub prediction_holds: bool,
    /// A framework carrying a self-stress is redundantly held.
    pub locked: bool,
    pub reading: RigidityReading,
}

/// **A dihedral without an angle.**
///
/// [definition] The dihedral itself is not rational and is never formed. What is reported is the
/// exact rational `cos²θ` together with the signs of `cos θ` and `sin θ`, which together determine
/// the quadrant exactly. **No float appears anywhere in this type.**
///
/// Lean counterparts: `dihedralCosSq`, `dihedralCosSq_nonneg`, `dihedralCosSq_le_one`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactDihedral {
    /// `⟨n₁,n₂⟩² / (⟨n₁,n₁⟩⟨n₂,n₂⟩)`, exact and in `[0, 1]`.
    pub cosine_squared: Rat,
    /// The sign of `cos θ`: `−1`, `0` or `+1`.
    pub cosine_sign: i8,
    /// The sign of `sin θ`: `−1`, `0` or `+1`.
    pub sine_sign: i8,
}

/// The exact dihedral of four places.
///
/// Refuses a degenerate configuration — three collinear atoms make a normal vanish — by name
/// rather than dividing by zero.
pub fn exact_dihedral(
    first: &[Rat],
    second: &[Rat],
    third: &[Rat],
    fourth: &[Rat],
) -> Result<ExactDihedral, FoldRefusal> {
    let b1: Vec<Rat> = second.iter().zip(first).map(|(a, b)| a - b).collect();
    let b2: Vec<Rat> = third.iter().zip(second).map(|(a, b)| a - b).collect();
    let b3: Vec<Rat> = fourth.iter().zip(third).map(|(a, b)| a - b).collect();
    let n1 = cross_product(&b1, &b2)?;
    let n2 = cross_product(&b2, &b3)?;
    let norm_one = dot(&n1, &n1)?;
    let norm_two = dot(&n2, &n2)?;
    if norm_one.is_zero() || norm_two.is_zero() {
        return Err(FoldRefusal::DegenerateDihedral);
    }
    let pairing = dot(&n1, &n2)?;
    let cosine_squared = (&pairing * &pairing) / (&norm_one * &norm_two);
    let cosine_sign = sign_of(&pairing);
    // sin θ has the sign of ⟨n₁ × b₂, n₂⟩, which is the IUPAC convention's own orientation.
    let m = cross_product(&n1, &b2)?;
    let sine_sign = -sign_of(&dot(&m, &n2)?);
    Ok(ExactDihedral {
        cosine_squared,
        cosine_sign,
        sine_sign,
    })
}

fn sign_of(value: &Rat) -> i8 {
    if value.is_zero() {
        0
    } else if value.is_positive() {
        1
    } else {
        -1
    }
}

/// One declared region of a Ramachandran chart, stated on the exact `(sign, cos²)` coordinates.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RamachandranRegion {
    pub name: String,
    /// The declared sign of `cos φ`.
    pub phi_cosine_sign: i8,
    /// The declared sign of `sin φ`.
    pub phi_sine_sign: i8,
    /// The declared sign of `cos ψ`.
    pub psi_cosine_sign: i8,
    /// The declared sign of `sin ψ`.
    pub psi_sine_sign: i8,
}

/// **A declared partition of the `(sign, cos²)` chart, with a ground and no default.**
///
/// [definition] This is a *declaration*, not a measurement and not a classifier: the regions and
/// their boundaries come from the `ground`, which names where they came from, and a residue the
/// declared regions do not cover returns [`RamachandranReading::OutsideTheChart`] rather than
/// being imputed to the nearest one. An empty chart is refused by name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "RamachandranChartWire")]
pub struct RamachandranChart {
    ground: String,
    regions: Vec<RamachandranRegion>,
}

/// The wire of a [`RamachandranChart`], re-checked by the `TryFrom` below.
#[derive(Deserialize)]
struct RamachandranChartWire {
    ground: String,
    regions: Vec<RamachandranRegion>,
}

impl TryFrom<RamachandranChartWire> for RamachandranChart {
    type Error = FoldRefusal;

    fn try_from(wire: RamachandranChartWire) -> Result<Self, Self::Error> {
        RamachandranChart::declared(wire.ground, wire.regions)
    }
}

impl RamachandranChart {
    /// A declared chart. Refuses an empty region list and a repeated quadrant.
    pub fn declared(
        ground: impl Into<String>,
        regions: Vec<RamachandranRegion>,
    ) -> Result<Self, FoldRefusal> {
        if regions.is_empty() {
            return Err(FoldRefusal::EmptyProbe {
                what: "a Ramachandran chart's declared regions",
            });
        }
        let mut seen = BTreeSet::new();
        for region in &regions {
            let quadrant = (
                region.phi_cosine_sign,
                region.phi_sine_sign,
                region.psi_cosine_sign,
                region.psi_sine_sign,
            );
            if !seen.insert(quadrant) {
                return Err(FoldRefusal::RamachandranRegionsOverlap {
                    name: region.name.clone(),
                });
            }
        }
        Ok(Self {
            ground: ground.into(),
            regions,
        })
    }

    /// Where the partition came from. It is testimony, never an identity.
    pub fn ground(&self) -> &str {
        &self.ground
    }

    pub fn regions(&self) -> &[RamachandranRegion] {
        &self.regions
    }

    /// Read one residue's `(φ, ψ)` against the declared partition.
    pub fn read(&self, phi: &ExactDihedral, psi: &ExactDihedral) -> RamachandranReading {
        for region in &self.regions {
            if region.phi_cosine_sign == phi.cosine_sign
                && region.phi_sine_sign == phi.sine_sign
                && region.psi_cosine_sign == psi.cosine_sign
                && region.psi_sine_sign == psi.sine_sign
            {
                return RamachandranReading::InRegion {
                    name: region.name.clone(),
                };
            }
        }
        RamachandranReading::OutsideTheChart {
            phi_cosine_sign: phi.cosine_sign,
            phi_sine_sign: phi.sine_sign,
            psi_cosine_sign: psi.cosine_sign,
            psi_sine_sign: psi.sine_sign,
        }
    }
}

/// The reading of one residue against a declared chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RamachandranReading {
    /// The residue sits in a declared region.
    InRegion {
        /// The region's declared name.
        name: String,
    },
    /// The declared partition does not cover this residue. **This is not a region and it is not a
    /// default**: it is the honest return, with the coordinates that fell outside.
    OutsideTheChart {
        phi_cosine_sign: i8,
        phi_sine_sign: i8,
        psi_cosine_sign: i8,
        psi_sine_sign: i8,
    },
}

/// **A lattice-protein pivot move: a rotation about a chain axis, as two reflections.**
///
/// [definition] Both creases contain the axis, so every atom on the axis is fixed by both
/// reflections and every bond crossing the pivot keeps its length. The moved set is a declared
/// tail of the chain; when that tail happens to lie strictly on one side of the first crease the
/// pivot **is** literally a fold, and [`PivotReading::is_a_half_space_fold`] says whether it does
/// on the actual data rather than assuming it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PivotMove {
    /// The first crease, containing the axis.
    pub first: Crease,
    /// The second crease, containing the axis.
    pub second: Crease,
    /// The atom block ordinals the pivot moves.
    pub moved: BTreeSet<usize>,
}

/// What a pivot did.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PivotReading {
    pub schema: String,
    /// The places after the pivot.
    pub places: Vec<Vec<Rat>>,
    /// Every bar's exact squared length is unchanged.
    pub bond_lengths_preserved: bool,
    /// The bars whose length the pivot moved, if any.
    pub moved_bars: Vec<ConstraintEdge>,
    /// The atoms the two creases both fix: the axis.
    pub fixed_atoms: Vec<usize>,
    /// True when the moved set is exactly the atoms strictly on the negative side of the first
    /// crease, so that the pivot's first half **is** a fold of a half-space.
    pub is_a_half_space_fold: bool,
    /// The atoms at which the pivot and the half-space fold disagree, if any.
    pub half_space_disagreements: Vec<usize>,
}

impl PivotMove {
    /// Apply the pivot to a declared placement and check every bar.
    pub fn apply(
        &self,
        places: &[Vec<Rat>],
        bars: &BTreeMap<ConstraintEdge, EdgeProvenance>,
    ) -> Result<PivotReading, FoldRefusal> {
        if places.is_empty() {
            return Err(FoldRefusal::EmptyProbe {
                what: "a pivot move's placement",
            });
        }
        if self.moved.is_empty() {
            return Err(FoldRefusal::EmptyProbe {
                what: "a pivot move's moved set",
            });
        }
        if let Some(at) = self.moved.iter().find(|at| **at >= places.len()) {
            return Err(FoldRefusal::CellAddressesAnAbsentVertex { vertex: *at });
        }
        let mut moved_places = Vec::with_capacity(places.len());
        let mut fixed_atoms = Vec::new();
        let mut half_space_disagreements = Vec::new();
        for (at, place) in places.iter().enumerate() {
            let point = FoldPoint::declared(place.clone())?;
            let first_side = self.first.side(&point)?;
            let second_side = self.second.side(&point)?;
            if first_side == Side::OnCrease && second_side == Side::OnCrease {
                fixed_atoms.push(at);
            }
            let in_tail = self.moved.contains(&at);
            let on_negative_side = first_side == Side::Negative;
            if in_tail != on_negative_side {
                half_space_disagreements.push(at);
            }
            if in_tail {
                let once = self.first.reflect(&point)?;
                let twice = self.second.reflect(&once)?;
                moved_places.push(twice.coordinates().to_vec());
            } else {
                moved_places.push(place.clone());
            }
        }
        let mut moved_bars = Vec::new();
        for edge in bars.keys() {
            let left = (edge.lower.0 as usize)
                .checked_sub(1)
                .ok_or(FoldRefusal::CellAddressesAnAbsentVertex { vertex: 0 })?;
            let right = (edge.upper.0 as usize)
                .checked_sub(1)
                .ok_or(FoldRefusal::CellAddressesAnAbsentVertex { vertex: 0 })?;
            if left >= places.len() || right >= places.len() {
                return Err(FoldRefusal::CellAddressesAnAbsentVertex {
                    vertex: left.max(right),
                });
            }
            let before = squared_distance(&places[left], &places[right])?;
            let after = squared_distance(&moved_places[left], &moved_places[right])?;
            if before != after {
                moved_bars.push(*edge);
            }
        }
        Ok(PivotReading {
            schema: PIVOT_READING_SCHEMA.to_owned(),
            places: moved_places,
            bond_lengths_preserved: moved_bars.is_empty(),
            moved_bars,
            fixed_atoms,
            is_a_half_space_fold: half_space_disagreements.is_empty(),
            half_space_disagreements,
        })
    }
}

// ---------------------------------------------------------------------------------------------
// schemas and refusals
// ---------------------------------------------------------------------------------------------

pub const BILLIARD_UNFOLDING_SCHEMA: &str = "holonic-engine.fold-billiard-unfolding.v1";
pub const LAYER_CONTACT_SCHEMA: &str = "holonic-engine.fold-layer-contact.v1";
pub const ROTATION_READING_SCHEMA: &str = "holonic-engine.fold-rotation-reading.v1";
pub const CELLULAR_FOLD_SCHEMA: &str = "holonic-engine.fold-cellular-reading.v1";
pub const CUT_READING_SCHEMA: &str = "holonic-engine.fold-cut-reading.v1";
pub const CREASE_PATTERN_SCHEMA: &str = "holonic-engine.fold-crease-pattern-framing.v1";
pub const EQUILIBRIUM_READING_SCHEMA: &str = "holonic-engine.fold-equilibrium-reading.v1";
pub const BACKBONE_FRAMING_SCHEMA: &str = "holonic-engine.fold-backbone-framing.v1";
pub const PIVOT_READING_SCHEMA: &str = "holonic-engine.fold-pivot-reading.v1";

/// Why a fold reading refused.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum FoldRefusal {
    #[error("the exact linear carrier refused: {0}")]
    Rigidity(#[from] RigidityError),
    #[error("the exact value carrier refused: {0}")]
    ExactValue(#[from] ExactValueError),
    #[error("the causal incidence refused: {0}")]
    Algebraic(#[from] CausalAlgebraicError),
    /// The core complex refused the chart (plan phase 4).
    #[error("the core complex refused the chart: {0}")]
    Core(Box<crate::algebraic::CoreChartRefusal>),
    #[error("the physical constraint complex refused: {0}")]
    Constraint(#[from] crate::physical_constraint_complex::ConstraintError),
    #[error("the typed-unit carrier refused: {0}")]
    Quantity(#[from] QuantityError),
    #[error("a point of zero dimension carries no crease and no fold")]
    ZeroDimension,
    #[error("a dimension of {supplied} exceeds the declared ceiling of {ceiling}")]
    DimensionTooWide { supplied: usize, ceiling: usize },
    #[error("a {expected}-dimensional reading was asked for a {supplied}-dimensional operand")]
    DimensionDisagrees { expected: usize, supplied: usize },
    #[error(
        "the crease's normal has zero square; over the rationals that is exactly the zero normal, \
         and it names no hyperplane"
    )]
    DegenerateCrease,
    #[error("a cross product and a dihedral are three-dimensional; {supplied} was supplied")]
    NotThreeDimensional { supplied: usize },
    #[error("a word of no folds is not a fold, and its residual would be a certificate from nothing")]
    EmptyFoldWord,
    #[error("a word of {supplied} folds exceeds the declared ceiling of {ceiling}")]
    FoldWordTooLong { supplied: usize, ceiling: usize },
    #[error("a residual of {supplied} bits does not reopen a word of {expected} folds")]
    ResidualWidthDisagrees { expected: usize, supplied: usize },
    #[error("the segment does not cross the crease, so there is no bounce to unfold")]
    SegmentDoesNotCrossTheCrease,
    #[error(
        "a contact reading between an empty layer ({upper} above, {lower} below) checks nothing; \
         no non-penetration verdict may be minted from it"
    )]
    EmptyLayerProbe { upper: usize, lower: usize },
    #[error("the layer pair population {upper} x {lower} overflows the machine integer")]
    LayerPopulationOverflows { upper: usize, lower: usize },
    #[error("a layer pair population of {pairs} exceeds the declared ceiling of {ceiling}")]
    LayerPopulationTooWide { pairs: usize, ceiling: usize },
    #[error("{what} was empty; a check over an empty probe is not a check")]
    EmptyProbe { what: &'static str },
    #[error("a complex with no vertex carries no cell")]
    EmptyComplex,
    #[error("the cell population overflows the machine integer")]
    CellPopulationOverflows,
    #[error("a cell population of {cells} exceeds the declared ceiling of {ceiling}")]
    CellPopulationTooWide { cells: usize, ceiling: usize },
    #[error("a cell repeating a vertex is collapsed and is not a cell")]
    CollapsedCell,
    #[error("the same cell was declared twice")]
    RepeatedCell,
    #[error("a cell addresses vertex {vertex}, which the complex does not carry")]
    CellAddressesAnAbsentVertex { vertex: usize },
    #[error("the triangle face {face:?} is not a declared edge, so the complex is not closed")]
    TriangleFaceAbsent { face: [usize; 2] },
    #[error("a placement of {supplied} points does not place a complex of {expected} vertices")]
    PlacementWidthDisagrees { expected: usize, supplied: usize },
    #[error("a crease pattern of {vertices} vertices exceeds the declared ceiling of {ceiling}")]
    PatternTooWide { vertices: usize, ceiling: usize },
    #[error("a panel of {extent} vertices is not a polygon")]
    PanelIsNotAPolygon { extent: usize },
    #[error("a panel of {extent} vertices exceeds the declared ceiling of {ceiling}")]
    PanelTooWide { extent: usize, ceiling: usize },
    #[error("a probe or gluing pattern of {supplied} exceeds the declared ceiling of {ceiling}")]
    ProbeTooWide { supplied: usize, ceiling: usize },
    #[error("a negative squared-separation tolerance encloses nothing")]
    NegativeTolerance,
    #[error(
        "a vertex of degree {degree} exceeds the declared ceiling of {ceiling} for counting layer \
         orderings, whose number is a factorial of the degree"
    )]
    VertexDegreeTooWideForOrdering { degree: usize, ceiling: usize },
    #[error("a single vertex of degree {degree} is odd; a flat-foldable vertex has even degree")]
    VertexDegreeIsOdd { degree: usize },
    #[error(
        "the assignment has {assignment} creases where the vertex has {vertex}; they address \
         different patterns"
    )]
    AssignmentDegreeDisagrees { vertex: usize, assignment: usize },
    #[error("the severed pair {pair:?} is not addressed by the family the cut was read on")]
    SeveredPairIsNotAddressed { pair: (u32, u32) },
    #[error(
        "the crease model's stiffness is in {stiffness} and its load in {load}; a load is a torque \
         in the same units or the threshold is not a comparison"
    )]
    CreaseModelUnitsDisagree { stiffness: String, load: String },
    #[error("a nonpositive hinge stiffness carries no restoring torque and no threshold")]
    NonpositiveStiffness,
    #[error("the sphere of radius zero carries no inversion")]
    DegenerateInversion,
    #[error("the centre of the sphere has no image under inversion")]
    InversionAtTheCentre,
    #[error("a backbone window of {residues} residues exceeds the declared ceiling of {ceiling}")]
    BackboneWindowTooWide { residues: usize, ceiling: usize },
    #[error("residue {residue} is not carried by this backbone window")]
    ResidueAbsent { residue: usize },
    #[error(
        "a sequence separation of {separation} names the covalent step, which is already a bar and \
         is not a contact"
    )]
    SeparationIsCovalent { separation: u32 },
    #[error("the dihedral at residue {residue} needs a neighbour this window does not carry")]
    DihedralAbsentAtTheTerminus { residue: usize },
    #[error("three collinear atoms make a dihedral's normal vanish; the dihedral is undefined")]
    DegenerateDihedral,
    #[error("the declared Ramachandran region {name} repeats a quadrant another region declares")]
    RamachandranRegionsOverlap { name: String },
}

#[cfg(test)]
#[path = "fold/tests.rs"]
mod tests;
