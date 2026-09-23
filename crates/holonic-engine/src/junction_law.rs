//! **The junction law: the tangential part is continuous, the normal part jumps, and the jump is
//! the source that lives on the joint.**
//!
//! [definition] This module is the executable owner of the **junction** half of item **T7** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its Lean
//! counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Transport/JunctionLaw.lean`
//! (namespace `Soma.Holonics.Transport.JunctionLaw`), and the correspondence is the deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `CompatiblePairs`, `join_is_exactly_the_compatible_pairs` | [`Joint`]'s `Pullback` arm and `the_joint_of_two_charts_is_the_pullback_of_compatible_pairs` |
//! | `noSharedBoundary_isEmpty_join` | [`Joint`]'s `OpenGap` and `Wormhole` arms, and `an_open_gap_carries_no_joint` |
//! | `IsJunction` | [`JunctionLaw::is_junction`] and [`Joint::is_junction`] |
//! | `SideSplit`, `restrictTo` | [`Interface`] and [`Side`] |
//! | `normalJump_eq_divergence` | [`check_junction`], which re-derives the split against the whole field's divergence at every joint cell and refuses on disagreement |
//! | `Balanced`, `balanced_iff_divergence` | [`JunctionVerdict`]'s `Balanced` arm |
//! | `balanceResidual`, `balanced_iff_residual_zero` | [`JunctionVerdict`]'s `Unbalanced` arm, and [`JunctionLaw::residual`] |
//! | `jump`, `Glues`, `glues_iff_agree` | [`check_tangential`] and [`TangentialVerdict`] |
//! | `descend_restricts_right`, `no_descent_of_nonzero_jump` | `a_nonzero_tangential_jump_admits_no_field_on_the_union` |
//! | `discrete_gauss` | [`gauss_region`] |
//! | `interior_cell_carries_no_boundary_flux` | `only_the_crossing_cells_carry_region_flux` |
//! | `tellegen` | [`tellegen`] and [`TellegenReceipt`] |
//! | `codiff_comp_zero`, `vertex_closure` | [`check_vertex_closure`] returning [`VertexVerdict`]'s `Closes` arm |
//! | `no_interface_flux_for_a_nonclosing_source` | [`VertexVerdict`]'s `Obstructed` arm, which carries the annihilating covector |
//! | `chi_glue_along_zero`, `each_junction_costs_one_euler` | [`assemble_euler`] and `each_junction_costs_one_unit_of_euler_characteristic` |
//! | `walkHolonomy_telescopes`, `closed_walk_holonomy_one` | [`OrientationBit`] and [`SurfaceReading`]'s orientation field |
//! | `no_consistent_orientation_on_a_reversing_loop` | [`OrientationBit`]'s `Reversing` arm, whose witness is `contact_gluing::OrientationReading`'s own |
//! | `orientation_reversing_iff_odd` | [`reflection_circuit_determinant`] |
//! | `three_conormals_balance_iff` | [`plateau_line_balance`] |
//! | `four_conormals_balance_of_pairwise`, `four_conormals_pairwise_sum` | [`plateau_vertex_balance`] |
//! | `burgersFlux`, `shockSpeed`, `rankine_hugoniot_speed` | [`burgers_flux`] and [`shock_speed`] |
//! | `rankine_hugoniot_balance` | [`ShockReading::balance_holds`] |
//! | `lax_admissible_iff`, `expansion_shock_violates_lax` | [`ShockVerdict`] |
//! | `tangentialPart`, `tangentialPart_orthogonal` | [`tangential_part`] |
//! | `innerQ_split` | [`refract`]'s exact normal component, and [`classify_interface`] |
//! | `snell_squared` | [`refract`] and [`RefractionReading::snell_identity_holds`] |
//! | `no_transmitted_covector_beyond_the_critical_angle` | [`InterfaceOutcome`]'s `TotallyReflected` arm |
//! | `classifyInterface`, `totally_reflected_iff` | [`classify_interface`] |
//!
//! # What a joint is, in each picture
//!
//! [definition] **Tower.** The joint of two charts is the **pullback over a common coarsening**:
//! the fibre product of their faces, which is exactly the population of compatible pairs. That
//! population is `Foundation/Lineage.lean::AddressedPassage.Join`, which carries both occurrences
//! *and the equality by which they glue*; `join_is_exactly_the_compatible_pairs` is the statement
//! that it is neither larger nor smaller than the pullback. The **join** of two charts is their
//! least common refinement where one exists; where none exists — which is
//! `Foundation/ContinuingTower.lean::twoCharts_no_common_refinement` — the comparison is undefined
//! and a connection between them is a `Transport/ContinuingTube.lean::Wormhole`. [`Joint`] types
//! the three cases and returns the wormhole rather than a default.
//!
//! [definition] **Tube.** A valence-2 station is a **serial join**: its occurrence type *is* the
//! pullback, through `Transport/WorldTube.lean::ClockedSpan.comp`, and a failed join is an open
//! gap with no joined occurrence at all
//! (`Transport/WorldTube.lean::openGap_has_no_joined_occurrence`). A **junction** is a station of
//! valence at least three ([`JunctionLaw::is_junction`]).
//!
//! [definition] **Staircase.** A joint is a spline knot, and its **order** is the lowest
//! derivative that jumps at the observer's grain. That object belongs to the jet tower of **T8**
//! and is deliberately not built here: this module carries no derivative, no jet and no
//! mollification. The forward reference is to T8's owner, and [`JointOrder`] records only the
//! declared order as an integer so that a T8 consumer has the field to fill.
//!
//! # The one law
//!
//! [proved-derived; implemented-exact] Over a cell complex with a declared codimension-1
//! interface, a field cochain `u` and the interface's own incidence:
//!
//! ```text
//!   [[ι* u]] = 0            the tangential/intrinsic part is continuous
//!   [[n · flux]] = σ        the normal/extrinsic part jumps, by the source on the joint
//! ```
//!
//! and these are the two halves of `d` and its metric adjoint `δ` restricted to the interface.
//! The first is exactness of the Mayer–Vietoris map `(a, b) ↦ ι*a − ι*b`: two side fields descend
//! to one field on the union **exactly when** their pullbacks to the shared cells agree
//! ([`check_tangential`], with `no_descent_of_nonzero_jump` the other half). The second is
//! `normalJump_eq_divergence`: splitting the flux cells into the two sides splits the divergence
//! into the two sides' outward normal fluxes, whose sum is `δ f` and nothing else, so
//! `[[n · flux]] = σ` **is** `δ f = σ`.
//!
//! [definition] **The metric is the constitutive law.** `δ_k = W_k^{-1} d_k^T W_{k+1}` is reached
//! through [`crate::hodge_receiver::HodgeOperator::codifferential`], and the declared weight on a
//! flux cell is the constitutive coefficient there: a conductance for a circuit, a permittivity
//! for a dielectric interface, unity for the Newtonian sheet. Changing the material is changing
//! the declared metric, and nothing else in this module moves.
//!
//! # Nothing here is approximate
//!
//! [implemented-exact] Every value is an exact `Rat` or an exact integer. No `f32`, `f64` or
//! float literal appears anywhere on any path. Total internal reflection is an exact sign
//! condition on a rational square and returns a typed deficit, never a `NaN`; a shock speed is an
//! exact rational; Plateau's `120°` law is proved and computed in the squared form, which is the
//! form that is rational.
//!
//! # The law is grade-parametric
//!
//! [definition] [`check_junction`] takes the grade of the joint, so the same function reads the
//! node balance of a circuit (`grade = 0`: flux on edges, joint at nodes) and the seam balance of
//! a two-sheet complex (`grade = 1`: flux on faces, joint at the crease edge). The two
//! electromagnetic interface conditions are that one function at two grades — the normal
//! displacement jumping by a surface charge at a node, and the tangential field jumping by a
//! surface current along a crease — and both are built here.
//!
//! # Physical scope, stated affirmatively
//!
//! [established-bounded] The instances are: **a finite circuit** (a resistive network on a graph
//! with declared positive rational conductances, its nodal analysis, its circulating currents and
//! its exact power ledger); **a finite Maxwell-type interface model** (rational wave covectors, a
//! declared rational `n²`, tangential continuity and the dispersion relation, plus a two-material
//! dielectric interface on a one-dimensional cell complex and a magnetostatic seam on a
//! two-triangle complex); **a scalar conservation law with the
//! exact polynomial Burgers flux** (its shock speed, mass balance and Lax condition); **a
//! Newtonian thin sheet** (the discrete Poisson jump condition, with the coupling carried as a
//! declared unit and never as a float); and **a tension balance at a film junction**. Each states
//! its constitutive and boundary law and its approximations. The Israel junction conditions of
//! general relativity are **stated and cited**, not built: [`israel_junction_conditions`] carries
//! the statement, its grade and what a faithful instance would owe.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use thiserror::Error;

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::causal::EventId;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::hodge_receiver::{
    BoundaryCondition, HodgeError, HodgeOperator, MetricDeclaration, hodge_reading,
};
use crate::quantity::{BaseUnits, Dimension, Quantity, QuantityError};
use crate::relation_ladder::Rung;

pub const JUNCTION_LAW_SCHEMA: &str = "holonic-engine.junction-law.v1";

// ===============================================================================================
// 0. refusals
// ===============================================================================================

/// Every way a junction reading refuses. A refusal is a return, never a panic.
#[derive(Debug, Error)]
pub enum JunctionRefusal {
    #[error("the declared joint is empty, so there is nothing to check and no certificate is minted")]
    EmptyJoint,
    #[error(
        "the triangulation {name:?} is not a surface ({branching} branching edges, {bad_links} bad \
         links, {bad_boundary} bad boundary vertices), so no Euler characteristic, homology or \
         orientation is read from it as a surface's"
    )]
    NotASurface {
        /// The declared name.
        name: String,
        /// Edges carried by three or more triangles.
        branching: usize,
        /// Vertices whose link is neither one path nor one cycle.
        bad_links: usize,
        /// Boundary vertices not carrying exactly two boundary edges.
        bad_boundary: usize,
    },
    #[error("the declared interface names no flux cell, so no normal jump exists to read")]
    EmptyInterface,
    #[error(
        "the interface names cell {cell:?}, which the operator does not carry at grade {grade}"
    )]
    InterfaceNamesAbsentCell { cell: CausalCellId, grade: u32 },
    #[error(
        "the two sides' normal fluxes at cell {cell:?} do not add up to the divergence of the \
         whole field, so this reading is defective and the interface is not reported on"
    )]
    NormalSplitDisagrees { cell: CausalCellId },
    #[error("the cochain has width {supplied} where grade {grade} carries {expected} cells")]
    CochainWidth {
        grade: u32,
        expected: usize,
        supplied: usize,
    },
    #[error("the source dimension {source_dimension:?} does not match the flux dimension {flux:?}")]
    SourceDimensionDisagrees {
        flux: Dimension,
        source_dimension: Dimension,
    },
    #[error("the junction cochains do not have the same joint key set")]
    JunctionCochainKeysDisagree,
    #[error(
        "the declared extent {declared} exceeds this module's ceiling {ceiling}; a presentation \
         that outgrows its carrier is rebased or refused, never let through by a raised ceiling"
    )]
    ExtentBeyondCeiling { declared: u64, ceiling: u64 },
    #[error("the declared triangulation is degenerate at {reason}")]
    DegenerateTriangulation { reason: String },
    #[error("a conormal population of {supplied} was supplied where {expected} was declared")]
    ConormalCount { expected: usize, supplied: usize },
    #[error("the covector population is empty, so no interface reading can be taken")]
    EmptyCovector,
    #[error("the declared interface normal has zero squared length, so it names no interface")]
    DegenerateNormal,
    #[error("the declared squared index {index_squared} is not positive")]
    NonPositiveIndexSquared { index_squared: String },
    #[error("a covector of arity {supplied} met a normal of arity {expected}")]
    CovectorArity { expected: usize, supplied: usize },
    #[error("the two states of the declared jump are equal, so there is no shock to read")]
    NoJump,
    #[error("hodge receiver: {0}")]
    Hodge(#[from] HodgeError),
    #[error("exact linear algebra: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("causal algebra: {0}")]
    Algebraic(#[from] CausalAlgebraicError),
    #[error("quantity: {0}")]
    Quantity(#[from] QuantityError),
}

/// **The ceiling on a declared triangulation extent.**
///
/// [definition] A caller declares a grid's extent, and every cell, edge and triangle population
/// below is sized by it. The product is checked against this ceiling *before* any allocation, and
/// a declaration beyond it is refused by name rather than rebased silently or let through.
pub const DECLARED_EXTENT_CEILING: u64 = 4_096;

// ===============================================================================================
// 1. the declared units
// ===============================================================================================

/// **The units a junction reading carries.**
///
/// [definition] A physical claim owes typed units. This is `quantity.rs`'s `BaseUnits` with the
/// four dimensions a junction law names: the potential whose tangential part is continuous, the
/// flux whose normal part jumps, the source living on the joint, and the power the Tellegen ledger
/// balances. There is no default: [`Self::electrical`], [`Self::electrostatic`] and
/// [`Self::newtonian_sheet`] are declarations, each named.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointUnits {
    lineage: String,
    base: BaseUnits,
    potential: Dimension,
    flux: Dimension,
    source: Dimension,
    power: Dimension,
}

impl JointUnits {
    /// The declaration, with the product law `potential × flux = power` re-derived rather than
    /// asserted and the source taken to be the divergence of the flux, hence its own dimension.
    pub fn declare(
        lineage: impl Into<String>,
        base: BaseUnits,
        potential: Dimension,
        flux: Dimension,
        source: Dimension,
    ) -> Result<Self, JunctionRefusal> {
        let power = potential.product(&flux)?;
        // In this discrete owner the source is the codifferential of the flux cochain, so it
        // carries the same declared unit. This is a cochain-level equality, not a claim about
        // pointwise density or a continuum divergence convention.
        if source != flux {
            return Err(JunctionRefusal::SourceDimensionDisagrees {
                flux,
                source_dimension: source,
            });
        }
        Ok(Self {
            lineage: lineage.into(),
            base,
            potential,
            flux,
            source,
            power,
        })
    }

    /// **A finite circuit**: potential in volts, flux in amperes, the node source in amperes, the
    /// ledger in watts.
    pub fn electrical() -> Result<Self, JunctionRefusal> {
        let base = BaseUnits::declare(["V", "A"])?;
        let potential = base.unit("V")?;
        let flux = base.unit("A")?;
        let source = base.unit("A")?;
        Self::declare("junction|electrical|V,A", base, potential, flux, source)
    }

    /// **A finite dielectric interface**: the potential in volts, the displacement flux in
    /// coulombs, the interface source a surface charge in coulombs.
    pub fn electrostatic() -> Result<Self, JunctionRefusal> {
        let base = BaseUnits::declare(["V", "C"])?;
        let potential = base.unit("V")?;
        let flux = base.unit("C")?;
        let source = base.unit("C")?;
        Self::declare("junction|electrostatic|V,C", base, potential, flux, source)
    }

    /// **A Newtonian thin sheet.** The potential is `Φ`, the flux `∂_n Φ`, and the source on the
    /// sheet is `4πG σ` — carried as one declared symbol `S` of the flux's own dimension, so the
    /// factor `4πG` is a unit and never a float. Its numerical value in another unit system is a
    /// separate declared cast and this module performs none.
    pub fn newtonian_sheet() -> Result<Self, JunctionRefusal> {
        let base = BaseUnits::declare(["P", "S"])?;
        let potential = base.unit("P")?;
        let flux = base.unit("S")?;
        let source = base.unit("S")?;
        Self::declare("junction|newtonian-sheet|P,S", base, potential, flux, source)
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn base(&self) -> &BaseUnits {
        &self.base
    }

    pub fn potential(&self) -> &Dimension {
        &self.potential
    }

    pub fn flux(&self) -> &Dimension {
        &self.flux
    }

    pub fn source(&self) -> &Dimension {
        &self.source
    }

    pub fn power(&self) -> &Dimension {
        &self.power
    }

    /// **The declared joint as one core port** (`Holon/Port.lean::power`): flow the flux, effort
    /// the potential, power their product, each through [`Dimension::to_core`]. The core refuses a
    /// power that is not flow times effort, which this declaration already re-derived.
    pub fn port_units(&self) -> Result<holonic_core::port::PortUnits, JunctionRefusal> {
        holonic_core::port::PortUnits::declared(
            self.flux.to_core()?,
            self.potential.to_core()?,
            self.power.to_core()?,
        )
        .map_err(|_| {
            JunctionRefusal::Quantity(QuantityError::DimensionMismatch {
                operation: "a joint's power read as flux times potential",
                left: self.power.render(),
                right: self.flux.render(),
            })
        })
    }

    /// **A joint from a core port**: potential the port's effort, flux and source its flow,
    /// each through [`Dimension::from_core`] over the declared base.
    pub fn from_port_units(
        lineage: impl Into<String>,
        base: BaseUnits,
        units: &holonic_core::port::PortUnits,
    ) -> Result<Self, JunctionRefusal> {
        let potential = Dimension::from_core(&base, units.effort())?;
        let flux = Dimension::from_core(&base, units.flow())?;
        Self::declare(lineage, base, potential, flux.clone(), flux)
    }

    /// A source reading with its declared dimension attached.
    pub fn source_quantity(&self, value: Rat) -> Quantity {
        Quantity::new(value, self.source.clone())
    }

    /// A power reading with its declared dimension attached.
    pub fn power_quantity(&self, value: Rat) -> Quantity {
        Quantity::new(value, self.power.clone())
    }
}

// ===============================================================================================
// 2. the joint in the tower: a pullback, or a wormhole
// ===============================================================================================

/// **The order of a joint on the staircase.**
///
/// [definition] The lowest derivative that jumps at the observer's grain. This module computes no
/// derivative and declares none: the field exists so that **T8**'s jet-tower owner has somewhere
/// to put the order it computes. A `JointOrder` here is a declaration carried, not a reading
/// taken.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JointOrder(pub u32);

/// **What two charts have at their joint.**
///
/// [definition] Three cases, and the third is not a failure of the first two — it is the honest
/// return when no comparison is defined.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Joint {
    /// The pullback over a common coarsening: the compatible pairs, with the joining face each
    /// pair agrees at. This is `Foundation/Lineage.lean::AddressedPassage.Join` computed on a
    /// finite population.
    Pullback {
        /// Each compatible pair, and the boundary face at which it joins.
        pairs: Vec<(usize, usize, String)>,
        /// How many passages meet at this station.
        valence: usize,
    },
    /// No predecessor target is any successor source: the join is empty. This is
    /// `Transport/WorldTube.lean::openGap_has_no_joined_occurrence` on a finite population.
    OpenGap {
        /// The boundary faces the predecessor reaches.
        left_faces: Vec<String>,
        /// The boundary faces the successor departs from.
        right_faces: Vec<String>,
    },
    /// The two charts admit no common refinement, so the comparison is undefined and a connection
    /// between them is a wormhole, not a join. Cited:
    /// `Foundation/ContinuingTower.lean::twoCharts_no_common_refinement` and
    /// `Transport/ContinuingTube.lean::Wormhole`.
    Wormhole {
        /// Why no common refinement exists.
        reason: String,
    },
}

impl Joint {
    /// **The joint of two finite chart populations, computed as the pullback.**
    ///
    /// The two populations are the occurrences of the two passages; `left_target` and
    /// `right_source` are their boundary maps. A pair joins exactly when the faces agree, and
    /// every such pair is returned — the population, not its cardinality.
    ///
    /// **The product of the two declared populations is bounded before the pullback is walked**,
    /// with checked arithmetic, and an empty population on either side is refused by name: a
    /// pullback over nothing would return "no pair joins" from no comparison at all.
    pub fn pullback(
        left_target: &[String],
        right_source: &[String],
        valence: usize,
    ) -> Result<Self, JunctionRefusal> {
        if left_target.is_empty() || right_source.is_empty() {
            return Err(JunctionRefusal::EmptyInterface);
        }
        let product = u64::try_from(left_target.len())
            .ok()
            .and_then(|left| {
                u64::try_from(right_source.len())
                    .ok()
                    .and_then(|right| left.checked_mul(right))
            })
            .ok_or(JunctionRefusal::ExtentBeyondCeiling {
                declared: u64::MAX,
                ceiling: DECLARED_EXTENT_CEILING,
            })?;
        if product > DECLARED_EXTENT_CEILING {
            return Err(JunctionRefusal::ExtentBeyondCeiling {
                declared: product,
                ceiling: DECLARED_EXTENT_CEILING,
            });
        }
        let mut pairs = Vec::new();
        for (at, target) in left_target.iter().enumerate() {
            for (to, source) in right_source.iter().enumerate() {
                if target == source {
                    pairs.push((at, to, target.clone()));
                }
            }
        }
        if pairs.is_empty() {
            return Ok(Self::OpenGap {
                left_faces: left_target.to_vec(),
                right_faces: right_source.to_vec(),
            });
        }
        Ok(Self::Pullback { pairs, valence })
    }

    /// How many passages meet, when the joint exists.
    pub fn valence(&self) -> Option<usize> {
        match self {
            Self::Pullback { valence, .. } => Some(*valence),
            _ => None,
        }
    }

    /// Whether this joint is a junction rather than a serial join.
    /// Lean counterpart: `Transport/JunctionLaw.lean::IsJunction`.
    pub fn is_junction(&self) -> bool {
        self.valence().is_some_and(|valence| valence >= 3)
    }
}

// ===============================================================================================
// 3. the interface and the typed law
// ===============================================================================================

/// Which side of the interface a flux cell lies on.
///
/// Lean counterpart: `Transport/JunctionLaw.lean::SideSplit`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Side {
    /// One side.
    Left,
    /// The other.
    Right,
    /// **Whether this cell exists at all is undecided.** The reading is then a family over both
    /// bounds and is never resolved by a default.
    OpenExistence,
}

/// **A declared codimension-1 interface.**
///
/// [definition] The flux-carrying cells of grade `grade + 1` split into the two sides the
/// interface separates, together with the grade-`grade` cells of the joint at which the balance is
/// read. The interface itself is not a third side.
///
/// **Its invariants need the operator, so its constructor takes one.** Every named cell must be
/// carried at the grade it is named at, and the joint must be nonempty — a check over an empty
/// probe is not a check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interface {
    lineage: String,
    grade: u32,
    sides: BTreeMap<CausalCellId, Side>,
    joint: BTreeSet<CausalCellId>,
}

impl Interface {
    /// Declare an interface against the operator it will be read on.
    pub fn declare(
        lineage: impl Into<String>,
        operator: &HodgeOperator,
        grade: u32,
        sides: BTreeMap<CausalCellId, Side>,
        joint: BTreeSet<CausalCellId>,
    ) -> Result<Self, JunctionRefusal> {
        if joint.is_empty() {
            return Err(JunctionRefusal::EmptyJoint);
        }
        if sides.is_empty() {
            return Err(JunctionRefusal::EmptyInterface);
        }
        let flux_grade = grade.saturating_add(1);
        let flux_cells: BTreeSet<CausalCellId> = operator.cells(flux_grade).iter().copied().collect();
        for cell in sides.keys() {
            if !flux_cells.contains(cell) {
                return Err(JunctionRefusal::InterfaceNamesAbsentCell {
                    cell: *cell,
                    grade: flux_grade,
                });
            }
        }
        let joint_cells: BTreeSet<CausalCellId> = operator.cells(grade).iter().copied().collect();
        for cell in &joint {
            if !joint_cells.contains(cell) {
                return Err(JunctionRefusal::InterfaceNamesAbsentCell {
                    cell: *cell,
                    grade,
                });
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            grade,
            sides,
            joint,
        })
    }

    /// Declare the interface that puts every flux cell on the side its declared sign says, with
    /// the whole grade-`grade` population as the joint. The common case, still a declaration.
    pub fn whole(
        lineage: impl Into<String>,
        operator: &HodgeOperator,
        grade: u32,
        left: &BTreeSet<CausalCellId>,
    ) -> Result<Self, JunctionRefusal> {
        let flux_grade = grade.saturating_add(1);
        let sides = operator
            .cells(flux_grade)
            .iter()
            .map(|cell| {
                (
                    *cell,
                    if left.contains(cell) {
                        Side::Left
                    } else {
                        Side::Right
                    },
                )
            })
            .collect();
        let joint = operator.cells(grade).iter().copied().collect();
        Self::declare(lineage, operator, grade, sides, joint)
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn grade(&self) -> u32 {
        self.grade
    }

    pub fn sides(&self) -> &BTreeMap<CausalCellId, Side> {
        &self.sides
    }

    pub fn joint(&self) -> &BTreeSet<CausalCellId> {
        &self.joint
    }

    /// The cells whose existence is undecided. A nonempty return means every later reading is a
    /// family over both bounds.
    pub fn open_cells(&self) -> Vec<CausalCellId> {
        self.sides
            .iter()
            .filter(|(_, side)| **side == Side::OpenExistence)
            .map(|(cell, _)| *cell)
            .collect()
    }

    fn side_cells(&self, side: Side) -> BTreeSet<CausalCellId> {
        self.sides
            .iter()
            .filter(|(_, declared)| **declared == side)
            .map(|(cell, _)| *cell)
            .collect()
    }
}

/// **The orientation bit of a joint**: whether carrying a frame across it returns it or reverses
/// it.
///
/// [definition] `O(1) = {±1}`, and non-orientability is **exhibited** by a closed path along which
/// the frame reverses — never counted. `Reversing` therefore carries the witnessing faces, exactly
/// as `contact_gluing::OrientationReading::reversing` does.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OrientationBit {
    /// Every closed dual walk returns the frame: determinant `+1`.
    Preserving,
    /// Some closed dual walk reverses it: determinant `−1`, exhibited at these faces.
    Reversing {
        /// The two-sided faces at which no sign assignment cancels.
        witness: Vec<(String, String)>,
    },
    /// The joint carries no declared frame, so the bit is not a reading this joint offers.
    NotDeclared,
}

impl OrientationBit {
    /// Whether the bit is the reversing one.
    pub fn reverses(&self) -> bool {
        matches!(self, Self::Reversing { .. })
    }
}

/// **The determinant of a circuit of `k` reflections.**
///
/// Lean counterpart: `Transport/JunctionLaw.lean::reflection_circuit_determinant` and
/// `orientation_reversing_iff_odd`. Odd is orientation-reversing; that parity is `w₁`.
pub fn reflection_circuit_determinant(reflections: u32) -> i8 {
    if reflections.is_multiple_of(2) { 1 } else { -1 }
}

/// **One typed junction law.**
///
/// [definition] The six things a junction carries: its valence, the continuous tangential part,
/// the jumping normal part, the source living on the joint, its Euler-characteristic contribution
/// and its orientation bit — with the declared units every reading is in.
///
/// **Its invariants are checked at its constructor and nowhere else can produce one.** The fields
/// are private, there is no `Default`, and **no type in this module derives `Serialize` or
/// `Deserialize`**: a wire form would rebuild the three cochains without the joint they are
/// indexed by and the operator they were read on, which is exactly the relation the constructor
/// exists to enforce. A caller that needs a wire owes the complex and the metric beside it, and
/// that is `hodge_receiver`'s wire, not a second one here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JunctionLaw {
    schema: String,
    lineage: String,
    valence: usize,
    tangential: BTreeMap<CausalCellId, Rat>,
    normal_jump: BTreeMap<CausalCellId, Rat>,
    source: BTreeMap<CausalCellId, Rat>,
    euler_contribution: i64,
    orientation: OrientationBit,
    units: JointUnits,
}

impl JunctionLaw {
    /// Found the law. The three cochains must be indexed by exactly the same joint, and that joint
    /// must be nonempty.
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        lineage: impl Into<String>,
        valence: usize,
        tangential: BTreeMap<CausalCellId, Rat>,
        normal_jump: BTreeMap<CausalCellId, Rat>,
        source: BTreeMap<CausalCellId, Rat>,
        euler_contribution: i64,
        orientation: OrientationBit,
        units: JointUnits,
    ) -> Result<Self, JunctionRefusal> {
        if normal_jump.is_empty() {
            return Err(JunctionRefusal::EmptyJoint);
        }
        let joint: BTreeSet<CausalCellId> = normal_jump.keys().copied().collect();
        let source_keys: BTreeSet<CausalCellId> = source.keys().copied().collect();
        let tangential_keys: BTreeSet<CausalCellId> = tangential.keys().copied().collect();
        if joint != source_keys || joint != tangential_keys {
            return Err(JunctionRefusal::JunctionCochainKeysDisagree);
        }
        Ok(Self {
            schema: JUNCTION_LAW_SCHEMA.to_owned(),
            lineage: lineage.into(),
            valence,
            tangential,
            normal_jump,
            source,
            euler_contribution,
            orientation,
            units,
        })
    }

    pub fn schema(&self) -> &str {
        &self.schema
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn valence(&self) -> usize {
        self.valence
    }

    /// Lean counterpart: `Transport/JunctionLaw.lean::IsJunction`.
    pub fn is_junction(&self) -> bool {
        self.valence >= 3
    }

    /// The continuous part: the single-valued pullback to the joint.
    pub fn tangential(&self) -> &BTreeMap<CausalCellId, Rat> {
        &self.tangential
    }

    /// The jumping part: `[[n · flux]]` at each joint cell.
    pub fn normal_jump(&self) -> &BTreeMap<CausalCellId, Rat> {
        &self.normal_jump
    }

    /// The source living on the joint.
    pub fn source(&self) -> &BTreeMap<CausalCellId, Rat> {
        &self.source
    }

    /// What this joint costs the Euler characteristic.
    pub fn euler_contribution(&self) -> i64 {
        self.euler_contribution
    }

    pub fn orientation(&self) -> &OrientationBit {
        &self.orientation
    }

    pub fn units(&self) -> &JointUnits {
        &self.units
    }

    /// The residual cochain `[[n · flux]] − σ`, whole. Not a norm of one.
    pub fn residual(&self) -> BTreeMap<CausalCellId, Rat> {
        self.normal_jump
            .iter()
            .map(|(cell, jump)| {
                let declared = self.source.get(cell).cloned().unwrap_or_else(Rat::zero);
                (*cell, jump - declared)
            })
            .collect()
    }

    /// Whether the normal half of the law holds at every joint cell.
    pub fn balanced(&self) -> bool {
        self.residual().values().all(Zero::is_zero)
    }
}

// ===============================================================================================
// 4. the checker
// ===============================================================================================

/// What a junction check returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JunctionVerdict {
    /// The jump equals the source at every joint cell that was checked, and the cells are named.
    Balanced {
        /// The law, whole.
        law: JunctionLaw,
        /// Every joint cell at which the equality was actually evaluated.
        checked: Vec<CausalCellId>,
    },
    /// The jump and the source differ; the complete residual cochain is returned.
    Unbalanced {
        /// The law, whole.
        law: JunctionLaw,
        /// `[[n · flux]] − σ` at every joint cell.
        residual: BTreeMap<CausalCellId, Rat>,
        /// The joint cells at which it is nonzero.
        offending: Vec<CausalCellId>,
    },
    /// One or more flux cells' existence is undecided, so the reading is a family over both
    /// bounds. Neither bound is a default, a best case or a tie-break.
    Open {
        /// The undecided cells.
        undecided: Vec<CausalCellId>,
        /// The reading with every undecided cell present.
        present: Box<JunctionVerdict>,
        /// The reading with every undecided cell absent.
        absent: Box<JunctionVerdict>,
    },
}

impl JunctionVerdict {
    /// Whether this verdict is the balanced one. An `Open` family is never balanced *as a family*
    /// unless both of its bounds are — and the accessor says so rather than choosing.
    pub fn is_balanced(&self) -> bool {
        match self {
            Self::Balanced { .. } => true,
            Self::Unbalanced { .. } => false,
            Self::Open {
                present, absent, ..
            } => present.is_balanced() && absent.is_balanced(),
        }
    }
}

fn cochain_of(
    operator: &HodgeOperator,
    grade: u32,
    values: &[Rat],
) -> Result<Vec<Rat>, JunctionRefusal> {
    let cells = operator.cells(grade);
    if values.len() != cells.len() {
        return Err(JunctionRefusal::CochainWidth {
            grade,
            expected: cells.len(),
            supplied: values.len(),
        });
    }
    Ok(values.to_vec())
}

fn degrees_at(degrees: &mut BTreeMap<CausalCellId, usize>, cell: CausalCellId) {
    *degrees.entry(cell).or_insert(0) += 1;
}

/// The divergence `δ_g f` of a field cochain, as a map from joint cell to value.
fn divergence(
    operator: &HodgeOperator,
    grade: u32,
    flux: &[Rat],
) -> Result<BTreeMap<CausalCellId, Rat>, JunctionRefusal> {
    let codifferential = operator.codifferential(grade)?;
    let applied = codifferential.apply(flux)?;
    Ok(operator
        .cells(grade)
        .iter()
        .copied()
        .zip(applied)
        .collect())
}

/// **The three cochains a junction reading takes.**
///
/// [definition] Named rather than positional, because "which of these three is the flux" is
/// exactly the question a junction law answers and a bare argument list would lose it.
#[derive(Clone, Copy, Debug)]
pub struct JunctionField<'a> {
    /// The continuous part, of the joint's own grade: the potential, whose pullback to the joint
    /// is single-valued because it is one cochain on the union. `[[ι* u]] = 0` is that, and
    /// [`check_tangential`] is the reading that decides it for a pair of side fields that have not
    /// yet been shown to be one.
    pub potential: &'a [Rat],
    /// The field cochain, one grade above. Its metric dual `W f` is the flux, and the declared
    /// weight on a cell is the constitutive coefficient there.
    pub field: &'a [Rat],
    /// The source living on the joint, of the joint's own grade.
    pub source: &'a [Rat],
}

/// **`check_junction`: the normal half of the law, read at a declared interface.**
///
/// [implemented-exact] Computes the two sides' outward normal fluxes separately, adds them — which
/// is `normalJump_eq_divergence`, re-derived at every reading rather than assumed — and compares
/// the result with the declared source at every joint cell. An undecided cell makes the return a
/// family over both bounds.
///
/// **It refuses an empty joint by name.** A loop over no cells would pass vacuously and mint a
/// balanced verdict from nothing; [`Interface::declare`] refuses that at the declaration and this
/// function names every cell it actually evaluated in the balanced arm's `checked` field.
pub fn check_junction(
    operator: &HodgeOperator,
    interface: &Interface,
    reading: &JunctionField<'_>,
    units: &JointUnits,
) -> Result<JunctionVerdict, JunctionRefusal> {
    let grade = interface.grade();
    let flux_grade = grade.saturating_add(1);
    let field = cochain_of(operator, flux_grade, reading.field)?;
    let declared_source = cochain_of(operator, grade, reading.source)?;
    let potential = cochain_of(operator, grade, reading.potential)?;

    let undecided = interface.open_cells();
    if !undecided.is_empty() {
        let present_field = field.clone();
        let mut absent_field = field.clone();
        for (at, cell) in operator.cells(flux_grade).iter().enumerate() {
            if undecided.contains(cell) {
                absent_field[at] = Rat::zero();
            }
        }
        let mut resolved_present = interface.clone();
        let mut resolved_absent = interface.clone();
        for cell in &undecided {
            resolved_present.sides.insert(*cell, Side::Left);
            resolved_absent.sides.insert(*cell, Side::Left);
        }
        let present = check_junction(
            operator,
            &resolved_present,
            &JunctionField {
                potential: reading.potential,
                field: &present_field,
                source: reading.source,
            },
            units,
        )?;
        let absent = check_junction(
            operator,
            &resolved_absent,
            &JunctionField {
                potential: reading.potential,
                field: &absent_field,
                source: reading.source,
            },
            units,
        )?;
        return Ok(JunctionVerdict::Open {
            undecided,
            present: Box::new(present),
            absent: Box::new(absent),
        });
    }

    let cells = operator.cells(flux_grade).to_vec();
    let restrict = |side: Side| -> Vec<Rat> {
        let chosen = interface.side_cells(side);
        cells
            .iter()
            .enumerate()
            .map(|(at, cell)| {
                if chosen.contains(cell) {
                    field[at].clone()
                } else {
                    Rat::zero()
                }
            })
            .collect()
    };

    let left = divergence(operator, grade, &restrict(Side::Left))?;
    let right = divergence(operator, grade, &restrict(Side::Right))?;
    let whole = divergence(operator, grade, &field)?;

    // `normalJump_eq_divergence`, re-derived here rather than assumed: the two sides' outward
    // normal fluxes add up to the divergence of the whole flux. A disagreement is a defect in this
    // reading, not a property of the interface, and it refuses rather than reporting.
    let mut normal_jump = BTreeMap::new();
    for cell in interface.joint() {
        let from_left = left.get(cell).cloned().unwrap_or_else(Rat::zero);
        let from_right = right.get(cell).cloned().unwrap_or_else(Rat::zero);
        let sum = &from_left + &from_right;
        let direct = whole.get(cell).cloned().unwrap_or_else(Rat::zero);
        if sum != direct {
            return Err(JunctionRefusal::NormalSplitDisagrees { cell: *cell });
        }
        normal_jump.insert(*cell, sum);
    }

    let mut degree_of: BTreeMap<CausalCellId, usize> = BTreeMap::new();
    let joint_index: BTreeMap<CausalCellId, usize> = operator
        .cells(grade)
        .iter()
        .enumerate()
        .map(|(at, cell)| (*cell, at))
        .collect();
    let mut source_map = BTreeMap::new();
    let mut tangential = BTreeMap::new();
    for cell in interface.joint() {
        // An interface declared against one operator may be handed to another, so the lookup is
        // total: a joint cell this operator does not carry is a typed refusal and never an index
        // into a shorter vector.
        let at = *joint_index
            .get(cell)
            .ok_or(JunctionRefusal::InterfaceNamesAbsentCell {
                cell: *cell,
                grade,
            })?;
        source_map.insert(*cell, declared_source[at].clone());
        // The continuous part at a joint cell is the pullback of the potential to it. It is
        // single-valued because the potential is one cochain on the union — which is exactly what
        // `[[i* u]] = 0` says, and `check_tangential` is what decides it when the two sides have
        // not yet been shown to be one cochain.
        tangential.insert(*cell, potential[at].clone());
    }

    // The valence of the joint is the largest incidence degree among its cells: how many flux
    // cells meet there. A station of valence `v` thickens to a `v`-holed sphere, whose Euler
    // characteristic is `2 − v` — `0` for a serial join and `−1` for the trivalent junction. The
    // contribution is therefore computed from the incidence and never written down.
    let coboundary = operator.coboundary(grade)?;
    let mut valence = 0usize;
    for row in 0..operator.extent(flux_grade) {
        for (column, joint_cell) in operator.cells(grade).iter().enumerate() {
            if interface.joint().contains(joint_cell) && !coboundary.get(row, column)?.is_zero() {
                degrees_at(&mut degree_of, *joint_cell);
            }
        }
    }
    for cell in interface.joint() {
        valence = valence.max(degree_of.get(cell).copied().unwrap_or(0));
    }
    let euler_contribution = 2i64.saturating_sub(i64::try_from(valence).unwrap_or(i64::MAX));

    let law = JunctionLaw::found(
        interface.lineage(),
        valence,
        tangential,
        normal_jump,
        source_map,
        euler_contribution,
        OrientationBit::NotDeclared,
        units.clone(),
    )?;

    let residual = law.residual();
    let offending: Vec<CausalCellId> = residual
        .iter()
        .filter(|(_, value)| !value.is_zero())
        .map(|(cell, _)| *cell)
        .collect();
    if offending.is_empty() {
        Ok(JunctionVerdict::Balanced {
            checked: law.normal_jump().keys().copied().collect(),
            law,
        })
    } else {
        Ok(JunctionVerdict::Unbalanced {
            law,
            residual,
            offending,
        })
    }
}

/// What a tangential-continuity check returned.
///
/// Lean counterpart: `Transport/JunctionLaw.lean::Glues` and `glues_iff_agree`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TangentialVerdict {
    /// The two pullbacks agree at every shared cell, and the cells are named.
    Continuous {
        /// Every shared cell at which the equality was evaluated.
        checked: Vec<CausalCellId>,
    },
    /// They disagree; the jump is returned whole.
    Jump {
        /// `ι*a − ι*b` at every shared cell where it is nonzero.
        at: BTreeMap<CausalCellId, Rat>,
    },
}

/// **`check_tangential`: the intrinsic half of the law.**
///
/// [implemented-exact] Two side fields descend to one field on the union exactly when their
/// pullbacks to the shared cells agree. A nonzero jump is not a violated constraint to be repaired
/// — it is the proof that the pair is two cochains and not one, which is
/// `Transport/JunctionLaw.lean::no_descent_of_nonzero_jump`.
///
/// **It refuses an empty shared population by name.**
pub fn check_tangential(
    left: &BTreeMap<CausalCellId, Rat>,
    right: &BTreeMap<CausalCellId, Rat>,
    shared: &BTreeSet<CausalCellId>,
) -> Result<TangentialVerdict, JunctionRefusal> {
    if shared.is_empty() {
        return Err(JunctionRefusal::EmptyJoint);
    }
    let mut at = BTreeMap::new();
    let mut checked = Vec::new();
    for cell in shared {
        let a = left.get(cell).cloned().unwrap_or_else(Rat::zero);
        let b = right.get(cell).cloned().unwrap_or_else(Rat::zero);
        checked.push(*cell);
        let difference = &a - &b;
        if !difference.is_zero() {
            at.insert(*cell, difference);
        }
    }
    if at.is_empty() {
        Ok(TangentialVerdict::Continuous { checked })
    } else {
        Ok(TangentialVerdict::Jump { at })
    }
}

/// **The field on the union built from two side fields**, when the jump vanishes.
///
/// Lean counterpart: `Transport/JunctionLaw.lean::descend`, `descend_restricts_left` and
/// `descend_restricts_right`. Returns `None` exactly when no such field exists.
pub fn descend(
    left: &BTreeMap<CausalCellId, Rat>,
    right: &BTreeMap<CausalCellId, Rat>,
    shared: &BTreeSet<CausalCellId>,
) -> Result<Option<BTreeMap<CausalCellId, Rat>>, JunctionRefusal> {
    match check_tangential(left, right, shared)? {
        TangentialVerdict::Jump { .. } => Ok(None),
        TangentialVerdict::Continuous { .. } => {
            let mut merged = right.clone();
            for (cell, value) in left {
                merged.insert(*cell, value.clone());
            }
            Ok(Some(merged))
        }
    }
}

/// What a codimension-2 closure check returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VertexVerdict {
    /// The junction sources close around every vertex that was checked.
    Closes {
        /// Every vertex at which the sum of jumps was evaluated.
        checked: Vec<CausalCellId>,
    },
    /// They do not, and the obstruction is returned rather than repaired.
    Obstructed {
        /// `δ σ` at every vertex where it is nonzero.
        residual: BTreeMap<CausalCellId, Rat>,
        /// A covector annihilating the image of `δ` and pairing nonzero with `σ`, which proves no
        /// interface flux produces this source. `None` when the complex carries no cell above the
        /// interface, where the statement is already the residual.
        annihilator: Option<Vec<Rat>>,
    },
}

/// **`check_vertex_closure`: the compatibility on each codimension-2 stratum.**
///
/// [implemented-exact] The junction laws carried on the codimension-1 strata around a vertex must
/// close: the sum of the jumps around a vertex link vanishes, which is `δ ∘ δ = 0`. A source that
/// does not close admits no interface flux at all, and the annihilating covector is returned as
/// the proof — the obstruction is a return, never a repair.
///
/// **It refuses an empty vertex population by name.**
pub fn check_vertex_closure(
    operator: &HodgeOperator,
    grade: u32,
    interface_source: &[Rat],
) -> Result<VertexVerdict, JunctionRefusal> {
    let below = match grade.checked_sub(1) {
        Some(below) => below,
        None => return Err(JunctionRefusal::EmptyJoint),
    };
    let vertices = operator.cells(below);
    if vertices.is_empty() {
        return Err(JunctionRefusal::EmptyJoint);
    }
    let source = cochain_of(operator, grade, interface_source)?;
    let closure = divergence(operator, below, &source)?;
    let residual: BTreeMap<CausalCellId, Rat> = closure
        .into_iter()
        .filter(|(_, value)| !value.is_zero())
        .collect();
    if residual.is_empty() {
        return Ok(VertexVerdict::Closes {
            checked: vertices.to_vec(),
        });
    }
    let annihilator = if operator.extent(grade.saturating_add(1)) == 0 {
        None
    } else {
        operator
            .codifferential(grade)?
            .preimage_obstruction(&source)?
    };
    Ok(VertexVerdict::Obstructed {
        residual,
        annihilator,
    })
}

/// The exact power ledger a junction owes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TellegenReceipt {
    /// `⟪d v, f⟫` — the pairing of the drops with the flux, in the declared power unit.
    pub dissipated: Quantity,
    /// `⟪v, σ⟫` — the pairing of the potential with the source, in the same unit.
    pub delivered: Quantity,
    /// Their exact difference. Zero, or the receipt is not a balance.
    pub residual: Quantity,
    /// Every joint cell the source was read at.
    pub checked: Vec<CausalCellId>,
}

impl TellegenReceipt {
    /// Whether the two sides agree exactly.
    pub fn balances(&self) -> bool {
        self.residual.is_zero()
    }

    /// **The Tellegen ledger as a view of the core energy balance.** A static junction stores
    /// nothing: `stored_change = 0`, `dissipated = ⟪d v, f⟫` (the branch power), `port = ⟪v, σ⟫`
    /// (the power the source delivers), and the core residual `0 − (−dissipated + port)` is this
    /// receipt's own `dissipated − delivered`, number for number. The magnitudes are read in the
    /// declared power unit; a receipt whose three quantities do not share one dimension is refused.
    /// Tellegen on the Kirchhoff structure is `Holon/Dirac.lean::tellegen`; the tests assert the
    /// core's `holonic_core::dirac::tellegen` returns the same pair at the metric-weighted flux.
    pub fn energy_balance(&self) -> Result<holonic_core::law::EnergyBalance, JunctionRefusal> {
        let (dissipated, unit) = self.dissipated.parts();
        let (delivered, delivered_unit) = self.delivered.parts();
        let (_, residual_unit) = self.residual.parts();
        for other in [delivered_unit, residual_unit] {
            if other != unit {
                return Err(JunctionRefusal::Quantity(
                    QuantityError::DimensionMismatch {
                        operation: "a Tellegen ledger read as one energy balance",
                        left: unit.render(),
                        right: other.render(),
                    },
                ));
            }
        }
        let zero = Rat::zero();
        Ok(holonic_core::law::EnergyBalance::closed(
            zero.clone(),
            dissipated.clone(),
            delivered.clone(),
            zero.clone(),
            zero.clone(),
            zero,
        ))
    }
}

/// **Tellegen's theorem: the junction's exact energy balance.**
///
/// [proved-derived; implemented-exact] For any potential `v` and any flux `f` whose divergence is
/// the declared source `σ`, `⟪d v, f⟫ = ⟪v, σ⟫`. It is the summation-by-parts identity
/// `Foundation/HodgeReceiver.lean::codiff₀_adjoint` read at a balanced flux, and it holds with no
/// tolerance: both sides are exact rationals. Cited, not rebuilt:
/// `Transport/JunctionLaw.lean::tellegen`.
///
/// **It refuses an empty joint by name.**
pub fn tellegen(
    operator: &HodgeOperator,
    grade: u32,
    potential: &[Rat],
    flux: &[Rat],
    units: &JointUnits,
) -> Result<TellegenReceipt, JunctionRefusal> {
    let flux_grade = grade.saturating_add(1);
    let potential = cochain_of(operator, grade, potential)?;
    let flux = cochain_of(operator, flux_grade, flux)?;
    let cells = operator.cells(grade);
    if cells.is_empty() {
        return Err(JunctionRefusal::EmptyJoint);
    }
    let drops = operator.coboundary(grade)?.apply(&potential)?;
    let dissipated = operator.inner(flux_grade, &drops, &flux)?;
    let source = operator.codifferential(grade)?.apply(&flux)?;
    let delivered = operator.inner(grade, &potential, &source)?;
    let residual = &dissipated - &delivered;
    Ok(TellegenReceipt {
        dissipated: units.power_quantity(dissipated),
        delivered: units.power_quantity(delivered),
        residual: units.power_quantity(residual),
        checked: cells.to_vec(),
    })
}

/// **The discrete Gauss statement over a declared region.**
///
/// [proved-derived; implemented-exact] The total source inside a region equals the pairing of the
/// flux with the coboundary of the region's indicator, which is supported on the cells crossing
/// its boundary. Lean counterpart: `Transport/JunctionLaw.lean::discrete_gauss`.
///
/// Returns `(interior total, boundary total)`, which are equal.
pub fn gauss_region(
    operator: &HodgeOperator,
    grade: u32,
    region: &BTreeSet<CausalCellId>,
    flux: &[Rat],
) -> Result<(Rat, Rat), JunctionRefusal> {
    if region.is_empty() {
        return Err(JunctionRefusal::EmptyJoint);
    }
    let flux_grade = grade.saturating_add(1);
    let flux = cochain_of(operator, flux_grade, flux)?;
    let indicator: Vec<Rat> = operator
        .cells(grade)
        .iter()
        .map(|cell| {
            if region.contains(cell) {
                Rat::one()
            } else {
                Rat::zero()
            }
        })
        .collect();
    let source = operator.codifferential(grade)?.apply(&flux)?;
    let interior = operator.inner(grade, &indicator, &source)?;
    let crossing = operator.coboundary(grade)?.apply(&indicator)?;
    let boundary = operator.inner(flux_grade, &crossing, &flux)?;
    Ok((interior, boundary))
}

/// **Euler characteristic of an assembly glued along loci of vanishing Euler characteristic.**
///
/// [proved-derived; implemented-exact] `χ(A ∪_{S¹} B) = χ(A) + χ(B)`, hence a surface assembled
/// from `n` pieces of `χ = −1` has `χ = −n`: **each junction costs one unit of Euler
/// characteristic.** Lean counterpart: `Transport/JunctionLaw.lean::chi_glue_along_zero` and
/// `each_junction_costs_one_euler`.
///
/// **It refuses an empty assembly by name**, because the sum over no pieces is zero and reporting
/// that as an assembly's Euler characteristic would be a reading taken over nothing.
pub fn assemble_euler(pieces: &[i64]) -> Result<i64, JunctionRefusal> {
    if pieces.is_empty() {
        return Err(JunctionRefusal::EmptyJoint);
    }
    Ok(pieces.iter().sum())
}

// ===============================================================================================
// 5. Kirchhoff: a finite circuit
// ===============================================================================================

/// **A finite resistive circuit on a graph, with declared positive rational conductances.**
///
/// [established-bounded; implemented-exact] The model, stated affirmatively: a finite connected or
/// disconnected graph; one 0-cell per node and one 1-cell per branch; a declared positive rational
/// conductance per branch, which **is** the Hodge metric weight there; unit node weights. The
/// constitutive law is Ohm's `i = G Δv`, the boundary law is the declared nodal injection, and the
/// approximations are named: the model is static (no inductance, no capacitance, no time), linear,
/// and lumped (each branch is one cell and carries no interior).
///
/// With that declaration:
///
/// ```text
///   KVL    the branch drop cochain is exact:      u = d₀ v
///   KCL    the nodal balance is the divergence:   δ₀ u = s
///   Ohm    the flux is the metric dual:           i_e = G_e u_e
///   hence  Δ₀ v = s                               the weighted graph Laplacian
/// ```
///
/// and the harmonic 1-cochains — `ker Δ₁ = ker δ₀` on a graph, because there is no 2-cell — are
/// exactly the **circulating currents**, of dimension `b₁`.
#[derive(Clone, Debug)]
pub struct ResistiveNetwork {
    lineage: String,
    nodes: Vec<CausalCellId>,
    branches: Vec<(usize, usize)>,
    conductances: Vec<Rat>,
    operator: HodgeOperator,
    units: JointUnits,
}

impl ResistiveNetwork {
    /// Declare the network. **The declared node count is bounded before anything is sized by it**,
    /// every branch endpoint is checked against it, every conductance must be strictly positive,
    /// and a self-loop is refused: it is not a branch between two nodes.
    pub fn declare(
        lineage: impl Into<String>,
        node_count: usize,
        branches: &[(usize, usize, Rat)],
    ) -> Result<Self, JunctionRefusal> {
        let declared = u64::try_from(node_count).unwrap_or(u64::MAX);
        if declared > DECLARED_EXTENT_CEILING {
            return Err(JunctionRefusal::ExtentBeyondCeiling {
                declared,
                ceiling: DECLARED_EXTENT_CEILING,
            });
        }
        let declared_branches = u64::try_from(branches.len()).unwrap_or(u64::MAX);
        if declared_branches > DECLARED_EXTENT_CEILING {
            return Err(JunctionRefusal::ExtentBeyondCeiling {
                declared: declared_branches,
                ceiling: DECLARED_EXTENT_CEILING,
            });
        }
        if node_count == 0 || branches.is_empty() {
            return Err(JunctionRefusal::EmptyInterface);
        }
        for (tail, head, conductance) in branches {
            if *tail >= node_count || *head >= node_count {
                return Err(JunctionRefusal::InterfaceNamesAbsentCell {
                    cell: CausalCellId(u64::try_from(*tail.max(head)).unwrap_or(u64::MAX)),
                    grade: 0,
                });
            }
            if tail == head {
                return Err(JunctionRefusal::DegenerateTriangulation {
                    reason: format!("branch {tail}->{head} is a self-loop"),
                });
            }
            if !conductance.is_positive() {
                return Err(JunctionRefusal::NonPositiveIndexSquared {
                    index_squared: conductance.to_string(),
                });
            }
        }

        let lineage = lineage.into();
        let events = BTreeSet::from([EventId(1)]);
        let mut complex = GradedCausalComplex::default();
        let mut nodes = Vec::with_capacity(node_count);
        for at in 0..node_count {
            nodes.push(complex.found_cell(
                format!("node-{at}"),
                events.clone(),
                0,
                CausalChain::default(),
            )?);
        }
        let mut weights: Vec<(CausalCellId, Rat)> =
            nodes.iter().map(|node| (*node, Rat::one())).collect();
        let mut edges = Vec::with_capacity(branches.len());
        let mut conductances = Vec::with_capacity(branches.len());
        for (at, (tail, head, conductance)) in branches.iter().enumerate() {
            let mut boundary = CausalChain::default();
            boundary.add_term(nodes[*head], ComparativeMultiplicity::positive(1_u8));
            boundary.add_term(nodes[*tail], ComparativeMultiplicity::negative(1_u8));
            let edge =
                complex.found_cell(format!("branch-{at}"), events.clone(), 1, boundary)?;
            weights.push((edge, conductance.clone()));
            edges.push((*tail, *head));
            conductances.push(conductance.clone());
        }
        let metric = MetricDeclaration::per_cell(format!("{lineage}|conductance"), weights);
        let operator =
            HodgeOperator::found(lineage.clone(), &complex, &metric, &BoundaryCondition::Free)?;
        Ok(Self {
            lineage,
            nodes,
            branches: edges,
            conductances,
            operator,
            units: JointUnits::electrical()?,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn operator(&self) -> &HodgeOperator {
        &self.operator
    }

    pub fn units(&self) -> &JointUnits {
        &self.units
    }

    pub fn nodes(&self) -> &[CausalCellId] {
        &self.nodes
    }

    pub fn branches(&self) -> &[(usize, usize)] {
        &self.branches
    }

    pub fn conductances(&self) -> &[Rat] {
        &self.conductances
    }

    /// `Δ₀ = δ₀ d₀`, the weighted graph Laplacian.
    pub fn nodal_laplacian(&self) -> Result<ExactRatMatrix, JunctionRefusal> {
        Ok(self.operator.laplacian(0)?)
    }

    /// **The complete affine solution of `Δ₀ v = s`, with the gauge carried and no representative
    /// selected.**
    ///
    /// Returns the particular potential, the kernel basis — the constants, which is the gauge
    /// freedom of a potential — and the branch currents, which are the same for every member of
    /// the fibre. When the injection is not in the image the annihilating covector is returned
    /// instead: an injection that does not sum to zero on a component has no potential, and that
    /// is an obstruction and not a rounding.
    pub fn solve(&self, injection: &[Rat]) -> Result<NodalSolution, JunctionRefusal> {
        let injection = cochain_of(&self.operator, 0, injection)?;
        let laplacian = self.nodal_laplacian()?;
        let Some((particular, gauge)) = laplacian.preimage_fibre(&injection)? else {
            let annihilator = laplacian.preimage_obstruction(&injection)?;
            return Ok(NodalSolution {
                potentials: Vec::new(),
                gauge: Vec::new(),
                drops: Vec::new(),
                currents: Vec::new(),
                unreachable: annihilator,
            });
        };
        let coboundary = self.operator.coboundary(0)?;
        let drops = coboundary.apply(&particular)?;
        let currents = drops
            .iter()
            .zip(&self.conductances)
            .map(|(drop, conductance)| drop * conductance)
            .collect();
        Ok(NodalSolution {
            potentials: particular,
            gauge,
            drops,
            currents,
            unreachable: None,
        })
    }

    /// **The circulating currents: `ker Δ₁`, of dimension `b₁`.**
    ///
    /// Reached through [`crate::hodge_receiver::hodge_reading`], which cross-checks the harmonic
    /// dimension against the integral Betti number from the Smith normal form at every reading —
    /// so "the loop space has this dimension" is two independent computations agreeing, not one
    /// asserted.
    pub fn circulating(&self) -> Result<CirculatingReading, JunctionRefusal> {
        let reading = hodge_reading(&self.operator, 1)?;
        Ok(CirculatingReading {
            dimension: reading.harmonic_dimension,
            betti: reading.betti,
            basis: reading.harmonic_basis.clone(),
        })
    }

    /// The exact power ledger at a declared potential and its own drops.
    pub fn power_ledger(&self, potential: &[Rat]) -> Result<TellegenReceipt, JunctionRefusal> {
        let potential = cochain_of(&self.operator, 0, potential)?;
        let drops = self.operator.coboundary(0)?.apply(&potential)?;
        tellegen(&self.operator, 0, &potential, &drops, &self.units)
    }

    /// [definition] **The network as the core complex** (plan phase 4): its operator's chart, one
    /// 0-cell per node and one 1-cell per branch in declaration order, `d₀` the branch drop map.
    /// The circuit is this complex with two element relations: the conductance
    /// ([`Self::conductance_relation`]) and the free nodal injection port.
    pub fn core_chart(&self) -> Result<crate::algebraic::CoreCellChart, JunctionRefusal> {
        Ok(self.operator.core_chart()?)
    }

    /// [definition] **Ohm's law as the core resistive element** `e_R = −G f_R` on the branch drops
    /// `f_R = d₀ v`, certified passive by its inertia (`G` is diagonal and strictly positive). Its
    /// dissipation `⟨u, G u⟩` is the Tellegen ledger's dissipated power at those drops.
    pub fn conductance_relation(
        &self,
    ) -> Result<holonic_core::element::ResistiveRelation, JunctionRefusal> {
        let conductance = ExactRatMatrix::from_diagonal(self.conductances.clone())?;
        holonic_core::element::ResistiveRelation::new(conductance)
            .map_err(|error| JunctionRefusal::Hodge(HodgeError::Core(Box::new(error.into()))))
    }
}

/// The complete affine solution of the nodal equation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodalSolution {
    /// One particular potential. The fibre is this plus the span of [`Self::gauge`].
    pub potentials: Vec<Rat>,
    /// The kernel of `Δ₀`: the constants, per connected component. The gauge, carried.
    pub gauge: Vec<Vec<Rat>>,
    /// The branch drops `d₀ v`.
    pub drops: Vec<Rat>,
    /// The branch currents `G_e (d₀ v)_e`.
    pub currents: Vec<Rat>,
    /// When the injection lies outside the image, the covector that proves it.
    pub unreachable: Option<Vec<Rat>>,
}

impl NodalSolution {
    /// Whether a potential exists at all.
    pub fn solved(&self) -> bool {
        self.unreachable.is_none() && !self.potentials.is_empty()
    }
}

/// The circulating currents of a network.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CirculatingReading {
    /// `dim ker Δ₁`.
    pub dimension: usize,
    /// `b₁` from the Smith normal form over `ℤ`. Equal to [`Self::dimension`] or the reading
    /// refused.
    pub betti: usize,
    /// The canonical reduced-echelon basis of the loop space, exactly.
    pub basis: Vec<Vec<Rat>>,
}

// ===============================================================================================
// 6. Electromagnetism: a finite interface on rational wave covectors
// ===============================================================================================

/// The exact pairing of two rational covectors.
pub fn dot_exact(left: &[Rat], right: &[Rat]) -> Result<Rat, JunctionRefusal> {
    if left.len() != right.len() {
        return Err(JunctionRefusal::CovectorArity {
            expected: left.len(),
            supplied: right.len(),
        });
    }
    if left.is_empty() {
        return Err(JunctionRefusal::EmptyCovector);
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (a, b)| sum + a * b))
}

/// **The tangential part of a covector at a declared interface normal.**
///
/// Lean counterpart: `Transport/JunctionLaw.lean::tangentialPart` and
/// `tangentialPart_orthogonal`. Exact over `ℚ`: no normalization of the normal is taken, so no
/// square root appears.
pub fn tangential_part(normal: &[Rat], covector: &[Rat]) -> Result<Vec<Rat>, JunctionRefusal> {
    let normal_squared = dot_exact(normal, normal)?;
    if normal_squared.is_zero() {
        return Err(JunctionRefusal::DegenerateNormal);
    }
    let projection = dot_exact(covector, normal)? / normal_squared;
    Ok(covector
        .iter()
        .zip(normal)
        .map(|(component, direction)| component - &projection * direction)
        .collect())
}

/// What a declared tangential covector meets on the far side of an interface.
///
/// Lean counterpart: `Transport/JunctionLaw.lean::InterfaceOutcome` and `classifyInterface`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InterfaceOutcome {
    /// A transmitted covector exists; the payload is its exact squared normal component.
    Transmitted {
        /// `n₂² κ² − |kᵗ|²`, exactly.
        normal_squared: Rat,
    },
    /// The normal component vanishes exactly: the grazing case, returned as its own value and not
    /// folded into either neighbour.
    Grazing,
    /// No transmitted covector exists. The payload is the exact deficit `|kᵗ|² − n₂² κ²`, which is
    /// what a floating-point route would have returned as the argument of a square root of a
    /// negative number.
    TotallyReflected {
        /// `|kᵗ|² − n₂² κ²`, exactly.
        deficit: Rat,
    },
}

/// Classify an interface by the exact sign of the squared normal component.
///
/// Lean counterpart: `Transport/JunctionLaw.lean::totally_reflected_iff`.
pub fn classify_interface(
    tangential_squared: &Rat,
    index_squared: &Rat,
    wavenumber_squared: &Rat,
) -> InterfaceOutcome {
    let available = index_squared * wavenumber_squared;
    let normal_squared = &available - tangential_squared;
    if normal_squared.is_positive() {
        InterfaceOutcome::Transmitted { normal_squared }
    } else if normal_squared.is_zero() {
        InterfaceOutcome::Grazing
    } else {
        InterfaceOutcome::TotallyReflected {
            deficit: tangential_squared - &available,
        }
    }
}

/// A complete refraction reading at a declared planar interface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RefractionReading {
    /// The tangential part of the incident covector, which the transmitted one must equal.
    pub tangential: Vec<Rat>,
    /// `|kᵗ|²`.
    pub tangential_squared: Rat,
    /// `κ² = ω²/c²`, derived from the incident covector and the declared `n₁²`.
    pub wavenumber_squared: Rat,
    /// `sin²θ₁`, exactly rational.
    pub incident_sine_squared: Rat,
    /// `sin²θ₂`, exactly rational. Greater than one exactly beyond the critical angle, which is
    /// why there is no real transmitted angle there.
    pub transmitted_sine_squared: Rat,
    /// `n₁² sin²θ₁`.
    pub snell_incident: Rat,
    /// `n₂² sin²θ₂`.
    pub snell_transmitted: Rat,
    /// Whether a transmitted covector exists, and with what exact normal component.
    pub outcome: InterfaceOutcome,
}

impl RefractionReading {
    /// **Snell's law as an exact rational identity in squares.**
    ///
    /// Lean counterpart: `Transport/JunctionLaw.lean::snell_squared`.
    pub fn snell_identity_holds(&self) -> bool {
        self.snell_incident == self.snell_transmitted
    }
}

/// **Refraction at a planar interface, from tangential continuity alone.**
///
/// [established-bounded; implemented-exact] The model, stated affirmatively: **a finite
/// Maxwell-type interface**. A planar interface with a declared rational normal; an incident wave
/// covector with rational components; declared rational squared refractive indices `n₁²` and `n₂²`
/// on the two sides; the dispersion relation `|k_j|² = n_j² ω²/c²`. The constitutive law is the
/// scalar index on each side; the boundary law is tangential continuity of the wave covector,
/// which is the junction law's intrinsic half. The approximations are named: the medium is
/// isotropic, non-magnetic, non-absorbing and homogeneous on each side; the interface is planar
/// and the wave is monochromatic; polarization, amplitude and the Fresnel coefficients are not
/// modelled here.
///
/// Under that declaration `n₁² sin²θ₁ = n₂² sin²θ₂` holds **exactly over `ℚ`**, in squares — the
/// sines themselves are ratios `|kᵗ|/|k|` whose squares are rational, and no square root is taken
/// anywhere on this path.
pub fn refract(
    normal: &[Rat],
    incident: &[Rat],
    incident_index_squared: &Rat,
    transmitted_index_squared: &Rat,
) -> Result<RefractionReading, JunctionRefusal> {
    if !incident_index_squared.is_positive() {
        return Err(JunctionRefusal::NonPositiveIndexSquared {
            index_squared: incident_index_squared.to_string(),
        });
    }
    if !transmitted_index_squared.is_positive() {
        return Err(JunctionRefusal::NonPositiveIndexSquared {
            index_squared: transmitted_index_squared.to_string(),
        });
    }
    let tangential = tangential_part(normal, incident)?;
    let tangential_squared = dot_exact(&tangential, &tangential)?;
    let incident_squared = dot_exact(incident, incident)?;
    if incident_squared.is_zero() {
        return Err(JunctionRefusal::EmptyCovector);
    }
    let wavenumber_squared = &incident_squared / incident_index_squared;
    let incident_sine_squared = &tangential_squared / &incident_squared;
    let transmitted_total = transmitted_index_squared * &wavenumber_squared;
    let transmitted_sine_squared = &tangential_squared / &transmitted_total;
    Ok(RefractionReading {
        snell_incident: incident_index_squared * &incident_sine_squared,
        snell_transmitted: transmitted_index_squared * &transmitted_sine_squared,
        outcome: classify_interface(
            &tangential_squared,
            transmitted_index_squared,
            &wavenumber_squared,
        ),
        tangential,
        tangential_squared,
        wavenumber_squared,
        incident_sine_squared,
        transmitted_sine_squared,
    })
}

// ===============================================================================================
// 7. Fluids: Rankine–Hugoniot for an exact polynomial flux
// ===============================================================================================

/// The Burgers flux `f(u) = u²/2`, exact over `ℚ`.
pub fn burgers_flux(state: &Rat) -> Rat {
    state * state / Rat::from_integer(BigInt::from(2))
}

/// The exact rational shock speed `s = [[f]] / [[u]]` of a Burgers jump. Refuses a vanishing jump
/// by name rather than dividing by zero.
pub fn shock_speed(left: &Rat, right: &Rat) -> Result<Rat, JunctionRefusal> {
    if left == right {
        return Err(JunctionRefusal::NoJump);
    }
    Ok((burgers_flux(right) - burgers_flux(left)) / (right - left))
}

/// Whether a declared jump is an admissible shock.
///
/// Lean counterpart: `Transport/JunctionLaw.lean::lax_admissible_iff` and
/// `expansion_shock_violates_lax`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShockVerdict {
    /// `f'(u_L) > s > f'(u_R)`: the characteristics run into the shock, and it is admissible.
    Admissible,
    /// They run out of it: an expansion shock, which the entropy condition excludes. **This is the
    /// junction's irreversibility**, and it belongs to the `(junction, direction)` pair: reversing
    /// the traversal reverses the verdict.
    EntropyViolating,
}

/// A complete Rankine–Hugoniot reading, with typed units.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShockReading {
    /// The state on the left, with its unit.
    pub left: Quantity,
    /// The state on the right.
    pub right: Quantity,
    /// `[[u]]`.
    pub state_jump: Quantity,
    /// `[[f]]`.
    pub flux_jump: Quantity,
    /// `s = [[f]] / [[u]]`, exactly rational.
    pub speed: Quantity,
    /// Whether the entropy condition admits it.
    pub verdict: ShockVerdict,
}

impl ShockReading {
    /// **Mass balance across the joint: `s [[u]] = [[f]]`, exactly, dimension included.**
    ///
    /// The value equality and the dimensional equality are checked separately, so a reading that
    /// balanced numerically in mismatched units would still refuse.
    pub fn balance_holds(&self) -> Result<bool, JunctionRefusal> {
        let carried = self.speed.product(&self.state_jump)?;
        Ok(carried == self.flux_jump)
    }
}

/// **The Rankine–Hugoniot condition for a scalar conservation law with the exact polynomial
/// Burgers flux.**
///
/// [established-bounded; implemented-exact] The model, stated affirmatively: the scalar
/// conservation law `u_t + f(u)_x = 0` in one space dimension with `f(u) = u²/2`, a single planar
/// discontinuity separating two constant states, and no viscosity. The constitutive law is that
/// polynomial flux; the boundary law is the jump condition `s [[u]] = [[f]]`, which is the
/// junction law with the space-time flux `(u, f)` and **no source on the joint**; the
/// approximations are named: the states are constant on each side, the discontinuity is planar,
/// and no interaction with another wave is modelled.
///
/// Units: the state is a velocity `L/T`, the flux `L²/T²`, and the speed `L/T`, so
/// `s [[u]] = [[f]]` is a dimensional identity as well as a numerical one.
///
/// **A vortex sheet is the same joint with the two halves exchanged**: the *tangential* velocity
/// jumps and the normal flux is continuous, so it carries no source and is a crease rather than a
/// shock. This owner does not model it; the crease and its side-bit residual belong to
/// [`crate::fold`]'s `Crease` and `FoldTransition`, which is T7's other half.
pub fn rankine_hugoniot(left: &Rat, right: &Rat) -> Result<ShockReading, JunctionRefusal> {
    let speed_value = shock_speed(left, right)?;
    let base = BaseUnits::declare(["L", "T"])?;
    let velocity = base.integer_dimension(&[1, -1])?;
    let flux = base.integer_dimension(&[2, -2])?;
    // The Lax condition for `f'(u) = u`: `u_L > s > u_R`, which holds exactly when the jump is a
    // decrease. Both halves are evaluated; neither is inferred from the other.
    let runs_in = &speed_value < left && right < &speed_value;
    Ok(ShockReading {
        left: Quantity::new(left.clone(), velocity.clone()),
        right: Quantity::new(right.clone(), velocity.clone()),
        state_jump: Quantity::new(right - left, velocity.clone()),
        flux_jump: Quantity::new(burgers_flux(right) - burgers_flux(left), flux),
        speed: Quantity::new(speed_value, velocity),
        verdict: if runs_in {
            ShockVerdict::Admissible
        } else {
            ShockVerdict::EntropyViolating
        },
    })
}

// ===============================================================================================
// 8. Gravity: a Newtonian sheet built, the Israel conditions stated
// ===============================================================================================

/// A law this library states and cites rather than implements.
///
/// [definition] Its fields are prose and a grade. It claims nothing about this repository's code
/// and is not a certificate: `owed` names exactly what a faithful instance would have to carry.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StatedLaw {
    /// The law's name.
    pub name: &'static str,
    /// Its statement.
    pub statement: &'static str,
    /// Its truth-status grade, in the form `docs/canon/EPISTEMIC_GRADES.md` declares.
    pub grade: &'static str,
    /// Where it is established.
    pub citation: &'static str,
    /// What a faithful instance in this repository would owe.
    pub owed: &'static str,
}

/// **The Israel junction conditions, stated and cited, not built.**
///
/// [proved-standard] They are the junction law in general relativity, and they have exactly the
/// shape this module's law has: the intrinsic part continuous, the extrinsic part jumping, the
/// jump being the source on the joint.
pub fn israel_junction_conditions() -> StatedLaw {
    StatedLaw {
        name: "Israel junction conditions",
        statement:
            "Across a timelike or spacelike hypersurface Sigma separating two spacetime regions, \
             the induced (first fundamental) metric is continuous, [[h_ij]] = 0, and the jump of \
             the extrinsic (second fundamental) curvature is the surface stress-energy: \
             [[K_ij]] - h_ij [[K]] = -8 pi G S_ij. The first half is the intrinsic part continuous; \
             the second is the extrinsic part jumping by the source that lives on the joint.",
        grade: "proved-standard",
        citation: "W. Israel, Nuovo Cimento B 44 (1966) 1; corrigendum 48 (1967) 463.",
        owed:
            "A faithful instance in this repository would owe: a Lorentzian metric on a declared \
             4-dimensional chart; an embedded hypersurface with its unit normal; the induced \
             metric and the extrinsic curvature K_ij = nabla_i n_j computed from that embedding; \
             the Gauss-Codazzi relations relating them to the ambient curvature; and an exact \
             carrier for all of it. The existing formal owner \
             Millennium/HolonicCurvedArcEinstein.lean supplies minkowskiMetric with signature \
             (-,+) and flatLorentzVacuumDynamics; \
             Millennium/NavierStokesCurvedTransport.lean supplies EinsteinFluidDynamics and \
             derives stress-energy conservation from its field equation and compatibility laws. \
             This junction owner has not composed those foundations with a four-dimensional \
             hypersurface, computed extrinsic curvature and Gauss-Codazzi realization. Its \
             executable gravitational instance is the Newtonian sheet below, at its declared \
             weak-field scalar scope.",
    }
}

/// A Newtonian thin-sheet reading.
#[derive(Clone, Debug)]
pub struct ThinSheetReading {
    /// The verdict of the junction check at the sheet.
    pub verdict: JunctionVerdict,
    /// The potential at every node of the declared lattice.
    pub potential: Vec<Rat>,
    /// `[[∂_n Φ]]` at the sheet, with its declared unit.
    pub normal_jump: Quantity,
    /// The declared sheet source, with its declared unit. In the declared units the coupling
    /// `4 pi G` is the unit `S` itself, so the factor is carried symbolically and never as a
    /// float.
    pub source: Quantity,
}

/// **A Newtonian thin sheet: the potential is continuous and its normal derivative jumps by the
/// declared surface source.**
///
/// [established-bounded; implemented-exact] The model, stated affirmatively: the discrete Poisson
/// equation `δ d Φ = ρ` on a one-dimensional lattice of `2 m + 1` nodes with unit metric, a source
/// concentrated on the central node, and free boundary conditions. The constitutive law is unit
/// permittivity — a declared metric, not an absent one; the boundary law is the concentrated
/// source. The approximations are named: Newtonian gravity, one dimension, a sheet of zero
/// thickness, and units in which the coupling `4 pi G` is the declared unit `S`, so that no
/// transcendental constant is approximated anywhere. This is **not** an instance of the Israel
/// conditions and does not claim to be; see [`israel_junction_conditions`].
pub fn newtonian_sheet(half_width: usize, surface_source: &Rat) -> Result<ThinSheetReading, JunctionRefusal> {
    let declared = u64::try_from(half_width).unwrap_or(u64::MAX);
    if declared == 0 || declared > DECLARED_EXTENT_CEILING / 4 {
        return Err(JunctionRefusal::ExtentBeyondCeiling {
            declared,
            ceiling: DECLARED_EXTENT_CEILING / 4,
        });
    }
    let node_count = 2 * half_width + 1;
    let branches: Vec<(usize, usize, Rat)> = (0..node_count - 1)
        .map(|at| (at, at + 1, Rat::one()))
        .collect();
    let lattice = ResistiveNetwork::declare("junction|newtonian-sheet", node_count, &branches)?;
    let units = JointUnits::newtonian_sheet()?;
    let middle = half_width;

    let mut injection = vec![Rat::zero(); node_count];
    injection[middle] = surface_source.clone();
    // A free-boundary lattice's Laplacian annihilates the constants, so a source concentrated at
    // one node is outside its image. The sheet is closed by returning the compensating outflow at
    // the two ends, which is the declared boundary law: the field escapes to the two exteriors.
    let half = surface_source / Rat::from_integer(BigInt::from(2));
    injection[0] = -&half;
    injection[node_count - 1] = -half;

    let solution = lattice.solve(&injection)?;
    let left: BTreeSet<CausalCellId> = lattice
        .operator()
        .cells(1)
        .iter()
        .take(middle)
        .copied()
        .collect();
    let interface = Interface::declare(
        "junction|newtonian-sheet|interface",
        lattice.operator(),
        0,
        lattice
            .operator()
            .cells(1)
            .iter()
            .map(|cell| {
                (
                    *cell,
                    if left.contains(cell) {
                        Side::Left
                    } else {
                        Side::Right
                    },
                )
            })
            .collect(),
        BTreeSet::from([lattice.operator().cells(0)[middle]]),
    )?;
    let verdict = check_junction(
        lattice.operator(),
        &interface,
        &JunctionField {
            potential: &solution.potentials,
            field: &solution.drops,
            source: &injection,
        },
        &units,
    )?;
    let normal_jump = match &verdict {
        JunctionVerdict::Balanced { law, .. } | JunctionVerdict::Unbalanced { law, .. } => law
            .normal_jump()
            .values()
            .next()
            .cloned()
            .unwrap_or_else(Rat::zero),
        JunctionVerdict::Open { .. } => Rat::zero(),
    };
    Ok(ThinSheetReading {
        verdict,
        potential: solution.potentials,
        normal_jump: Quantity::new(normal_jump, units.flux().clone()),
        source: units.source_quantity(surface_source.clone()),
    })
}

// ===============================================================================================
// 9. Films: Plateau's laws as a tension balance at a junction
// ===============================================================================================

/// What a tension balance returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PlateauVerdict {
    /// The conormals balance. At a three-conormal line every pairwise product has the value the
    /// valence forces; at a four-conormal vertex the balance forces only their sum, and `pairwise`
    /// reports each product as read.
    Balanced {
        /// The common squared tension.
        tension_squared: Rat,
        /// Every pairwise inner product, in lexicographic order of the pairs.
        pairwise: Vec<Rat>,
        /// The value each pairwise product must take: `−T/2` at three conormals, `−T/3` at four.
        required: Rat,
    },
    /// They do not balance; the residual vector is returned whole.
    Unbalanced {
        /// `Σ conormal`, exactly.
        residual: Vec<Rat>,
    },
    /// The conormals do not share one squared tension, so Plateau's law has no content for them
    /// and no verdict is manufactured.
    UnequalTension {
        /// Each conormal's squared length.
        squared: Vec<Rat>,
    },
}

fn plateau_balance(conormals: &[Vec<Rat>], expected: usize) -> Result<PlateauVerdict, JunctionRefusal> {
    if conormals.len() != expected {
        return Err(JunctionRefusal::ConormalCount {
            expected,
            supplied: conormals.len(),
        });
    }
    let arity = conormals[0].len();
    if arity == 0 {
        return Err(JunctionRefusal::EmptyCovector);
    }
    for conormal in conormals {
        if conormal.len() != arity {
            return Err(JunctionRefusal::CovectorArity {
                expected: arity,
                supplied: conormal.len(),
            });
        }
    }
    let squared: Vec<Rat> = conormals
        .iter()
        .map(|conormal| dot_exact(conormal, conormal))
        .collect::<Result<_, _>>()?;
    let tension_squared = squared[0].clone();
    if squared.iter().any(|value| *value != tension_squared) {
        return Ok(PlateauVerdict::UnequalTension { squared });
    }
    let mut residual = vec![Rat::zero(); arity];
    for conormal in conormals {
        for (at, component) in conormal.iter().enumerate() {
            residual[at] = &residual[at] + component;
        }
    }
    if residual.iter().any(|value| !value.is_zero()) {
        return Ok(PlateauVerdict::Unbalanced { residual });
    }
    let mut pairwise = Vec::new();
    for at in 0..conormals.len() {
        for to in (at + 1)..conormals.len() {
            pairwise.push(dot_exact(&conormals[at], &conormals[to])?);
        }
    }
    let divisor = Rat::from_integer(BigInt::from(i64::try_from(expected - 1).unwrap_or(1)));
    Ok(PlateauVerdict::Balanced {
        required: -&tension_squared / divisor,
        tension_squared,
        pairwise,
    })
}

/// **Plateau's first law: three films meet along a line at equal angles.**
///
/// [proved-derived; implemented-exact] Three conormals of equal squared tension `T` sum to zero
/// **exactly when** every pairwise inner product is `−T/2`. Both directions are proved in
/// `Transport/JunctionLaw.lean::three_conormals_balance_iff`; this is the same statement computed.
/// The `120°` is the squared form's content: the directions themselves need not be rational and
/// their inner products are, so the law is exact over `ℚ` and the angle is not.
///
/// This is the node law of [`check_junction`] for a vector-valued flux: the sum of the outgoing
/// conormals is the normal jump, and a film junction carries no source, so it vanishes.
pub fn plateau_line_balance(conormals: &[Vec<Rat>]) -> Result<PlateauVerdict, JunctionRefusal> {
    plateau_balance(conormals, 3)
}

/// **Plateau's second law: four such lines meet at a vertex at the tetrahedral angle.**
///
/// [proved-derived; implemented-exact] Four conormals of equal squared tension whose pairwise
/// products are all `−T/3` sum to zero (`four_conormals_balance_of_pairwise`). The converse is
/// **weaker and this owner says so**: the balance alone forces only that the six pairwise products
/// sum to `−2T` (`four_conormals_pairwise_sum`), and `(a, −a, b, −b)` is a balanced configuration
/// of equal tension whose pairwise products are not all `−T/3`. So the `120°` law at a junction
/// line is forced by the balance and the tetrahedral law at a vertex is an extra declaration.
pub fn plateau_vertex_balance(conormals: &[Vec<Rat>]) -> Result<PlateauVerdict, JunctionRefusal> {
    plateau_balance(conormals, 4)
}

// ===============================================================================================
// 10. Valence, Euler characteristic and the orientation bit, on explicit triangulations
// ===============================================================================================

/// **A declared triangulation, read as a surface.**
///
/// [definition] Each triangle is an *ordered* vertex triple: the order is the declared local
/// orientation, and it is what the orientability reading uses. The unordered vertex sets are what
/// the chain complex uses. Two different readings of one declaration, and neither is derived from
/// the other.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Triangulation {
    lineage: String,
    triangles: Vec<[String; 3]>,
}

impl Triangulation {
    /// Declare a triangulation. **The declared population is bounded before anything is sized by
    /// it**, a triangle with a repeated vertex is refused, and a repeated triangle is refused —
    /// both would silently corrupt every reading below.
    pub fn declare(
        lineage: impl Into<String>,
        triangles: Vec<[String; 3]>,
    ) -> Result<Self, JunctionRefusal> {
        let declared = u64::try_from(triangles.len()).unwrap_or(u64::MAX);
        if declared > DECLARED_EXTENT_CEILING {
            return Err(JunctionRefusal::ExtentBeyondCeiling {
                declared,
                ceiling: DECLARED_EXTENT_CEILING,
            });
        }
        if triangles.is_empty() {
            return Err(JunctionRefusal::DegenerateTriangulation {
                reason: "the declared triangulation carries no triangle".to_owned(),
            });
        }
        let mut seen: BTreeSet<Vec<String>> = BTreeSet::new();
        for triangle in &triangles {
            let [a, b, c] = triangle;
            if a == b || b == c || a == c {
                return Err(JunctionRefusal::DegenerateTriangulation {
                    reason: format!("triangle [{a}, {b}, {c}] repeats a vertex"),
                });
            }
            let mut key = vec![a.clone(), b.clone(), c.clone()];
            key.sort();
            if !seen.insert(key) {
                return Err(JunctionRefusal::DegenerateTriangulation {
                    reason: format!("triangle [{a}, {b}, {c}] occurs twice"),
                });
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            triangles,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn triangles(&self) -> &[[String; 3]] {
        &self.triangles
    }

    /// The vertex population.
    pub fn vertices(&self) -> BTreeSet<String> {
        self.triangles
            .iter()
            .flat_map(|triangle| triangle.iter().cloned())
            .collect()
    }

    /// Every edge, with the triangles carrying it.
    pub fn edges(&self) -> BTreeMap<(String, String), Vec<usize>> {
        let mut edges: BTreeMap<(String, String), Vec<usize>> = BTreeMap::new();
        for (at, [a, b, c]) in self.triangles.iter().enumerate() {
            for (left, right) in [(a, b), (b, c), (a, c)] {
                let key = if left <= right {
                    (left.clone(), right.clone())
                } else {
                    (right.clone(), left.clone())
                };
                edges.entry(key).or_default().push(at);
            }
        }
        for carriers in edges.values_mut() {
            carriers.sort_unstable();
            carriers.dedup();
        }
        edges
    }

    /// The simplicial chain complex, with the standard sorted-vertex signs.
    pub fn complex(&self) -> Result<GradedCausalComplex, JunctionRefusal> {
        let events = BTreeSet::from([EventId(1)]);
        let mut complex = GradedCausalComplex::default();
        let mut vertex_cells: BTreeMap<String, CausalCellId> = BTreeMap::new();
        for vertex in self.vertices() {
            let cell =
                complex.found_cell(vertex.clone(), events.clone(), 0, CausalChain::default())?;
            vertex_cells.insert(vertex, cell);
        }
        let mut edge_cells: BTreeMap<(String, String), CausalCellId> = BTreeMap::new();
        for (low, high) in self.edges().keys() {
            let mut boundary = CausalChain::default();
            boundary.add_term(vertex_cells[high], ComparativeMultiplicity::positive(1_u8));
            boundary.add_term(vertex_cells[low], ComparativeMultiplicity::negative(1_u8));
            let cell = complex.found_cell(
                format!("{low}|{high}"),
                events.clone(),
                1,
                boundary,
            )?;
            edge_cells.insert((low.clone(), high.clone()), cell);
        }
        for [a, b, c] in &self.triangles {
            let mut sorted = [a.clone(), b.clone(), c.clone()];
            sorted.sort();
            let [v0, v1, v2] = sorted;
            let mut boundary = CausalChain::default();
            boundary.add_term(
                edge_cells[&(v1.clone(), v2.clone())],
                ComparativeMultiplicity::positive(1_u8),
            );
            boundary.add_term(
                edge_cells[&(v0.clone(), v2.clone())],
                ComparativeMultiplicity::negative(1_u8),
            );
            boundary.add_term(
                edge_cells[&(v0.clone(), v1.clone())],
                ComparativeMultiplicity::positive(1_u8),
            );
            complex.found_cell(format!("{v0}|{v1}|{v2}"), events.clone(), 2, boundary)?;
        }
        Ok(complex)
    }

    /// **The certificate that this declaration really is a surface**, computed and never assumed.
    pub fn certificate(&self) -> SurfaceCertificate {
        let edges = self.edges();
        let mut boundary_edges = Vec::new();
        let mut branching_edges = Vec::new();
        for (edge, carriers) in &edges {
            match carriers.len() {
                0 | 1 => boundary_edges.push(edge.clone()),
                2 => {}
                _ => branching_edges.push(edge.clone()),
            }
        }

        // The boundary circles: connected components of the graph the boundary edges form. Each
        // boundary vertex must carry exactly two boundary edges, or the boundary is not a
        // disjoint union of circles and the certificate says so.
        let mut boundary_degree: BTreeMap<String, usize> = BTreeMap::new();
        for (low, high) in &boundary_edges {
            *boundary_degree.entry(low.clone()).or_insert(0) += 1;
            *boundary_degree.entry(high.clone()).or_insert(0) += 1;
        }
        let bad_boundary: Vec<String> = boundary_degree
            .iter()
            .filter(|(_, degree)| **degree != 2)
            .map(|(vertex, _)| vertex.clone())
            .collect();
        let boundary_circles = count_components(&boundary_edges);

        // Every vertex link must be one path (an interior-free boundary vertex) or one cycle (an
        // interior vertex). The link's edges are the opposite edges of the triangles at that
        // vertex.
        let mut bad_links = Vec::new();
        for vertex in self.vertices() {
            let mut link: Vec<(String, String)> = Vec::new();
            for [a, b, c] in &self.triangles {
                let opposite = if a == &vertex {
                    Some((b.clone(), c.clone()))
                } else if b == &vertex {
                    Some((a.clone(), c.clone()))
                } else if c == &vertex {
                    Some((a.clone(), b.clone()))
                } else {
                    None
                };
                if let Some((left, right)) = opposite {
                    link.push(if left <= right {
                        (left, right)
                    } else {
                        (right, left)
                    });
                }
            }
            if link.is_empty() {
                bad_links.push(vertex);
                continue;
            }
            let mut degree: BTreeMap<String, usize> = BTreeMap::new();
            for (left, right) in &link {
                *degree.entry(left.clone()).or_insert(0) += 1;
                *degree.entry(right.clone()).or_insert(0) += 1;
            }
            let ends = degree.values().filter(|value| **value == 1).count();
            let high = degree.values().any(|value| *value > 2);
            if high || count_components(&link) != 1 || (ends != 0 && ends != 2) {
                bad_links.push(vertex);
            }
        }

        SurfaceCertificate {
            is_surface: branching_edges.is_empty()
                && bad_links.is_empty()
                && bad_boundary.is_empty(),
            boundary_edges,
            branching_edges,
            boundary_circles,
            bad_links,
            bad_boundary,
        }
    }

    /// **The complete reading**: the exact `f`-vector, Euler characteristic, integral Betti
    /// numbers with torsion, the `𝔽₂` Betti numbers, the boundary circles, the surface
    /// certificate and the orientation bit.
    pub fn reading(&self) -> Result<SurfaceReading, JunctionRefusal> {
        use crate::rebase_invariants::{
            PivotRule, boundary_matrix, rebase_invariants, smith_normal_form,
        };

        let certificate = self.certificate();
        // The reading is a surface's. A declaration that fails its certificate returns the
        // certificate's own content as the refusal rather than a confident χ beside a `false`
        // the caller may not read.
        if !certificate.is_surface {
            return Err(JunctionRefusal::NotASurface {
                name: self.lineage.clone(),
                branching: certificate.branching_edges.len(),
                bad_links: certificate.bad_links.len(),
                bad_boundary: certificate.bad_boundary.len(),
            });
        }
        let complex = self.complex()?;
        let invariants = rebase_invariants(&complex, PivotRule::FirstNonzero)?;
        let f_vector = complex.f_vector();
        let vertices = f_vector.get(&0).copied().unwrap_or(0);
        let edges = f_vector.get(&1).copied().unwrap_or(0);
        let triangles = f_vector.get(&2).copied().unwrap_or(0);

        // `𝔽₂` Betti numbers from the *integral* Smith normal form: reducing the diagonal form mod
        // two, the rank over `𝔽₂` is the number of invariant factors that two does not divide. No
        // second reduction is run, and the two readings differ exactly where torsion at two lives
        // — which is what exhibits non-orientability on a closed surface.
        let two = BigInt::from(2);
        let mut rank_mod_two = Vec::new();
        for grade in 0..=3u32 {
            let matrix = boundary_matrix(&complex, grade)?;
            let form = smith_normal_form(&matrix, PivotRule::FirstNonzero);
            rank_mod_two.push(
                form.factors
                    .iter()
                    .filter(|factor| !(*factor % &two).is_zero())
                    .count(),
            );
        }
        let counts = [vertices, edges, triangles];
        let mod_two_betti: Vec<usize> = (0..3usize)
            .map(|grade| {
                counts[grade]
                    .saturating_sub(rank_mod_two[grade])
                    .saturating_sub(rank_mod_two[grade + 1])
            })
            .collect();

        let orientation = self.orientation();
        Ok(SurfaceReading {
            lineage: self.lineage.clone(),
            f_vector: (vertices, edges, triangles),
            euler_characteristic: invariants.cell_euler_characteristic(),
            homology_euler_characteristic: invariants.euler_characteristic(),
            integral_betti: invariants.betti_vector(),
            torsion: invariants.total_torsion(),
            mod_two_betti,
            boundary_circles: certificate.boundary_circles,
            orientation,
            certificate,
        })
    }

    /// **The orientation bit, through `contact_gluing::orient`.**
    ///
    /// The triangles are handed to that owner as unit-weight contact triangles — every triple
    /// `(1, 1, 1)` realizes a Euclidean triangle, so every one of them is admitted — and the
    /// reading that comes back is its own: the propagated sign per triangle and, where no
    /// assignment cancels, the **witnessing seams**. Non-orientability is exhibited, not counted.
    pub fn orientation(&self) -> OrientationBit {
        use crate::contact_gluing::{ContactTriangle, corners_from_weights, realization_of};
        let one = BigInt::one();
        let triangles: Vec<ContactTriangle> = self
            .triangles
            .iter()
            .map(|[a, b, c]| {
                let stems = [format!("{a}{b}"), format!("{b}{c}"), format!("{c}{a}")];
                let weights = [one.clone(), one.clone(), one.clone()];
                let corners = corners_from_weights(
                    [a.as_str(), b.as_str(), c.as_str()],
                    [&stems[0], &stems[1], &stems[2]],
                    [&weights[0], &weights[1], &weights[2]],
                );
                let euclidean = realization_of([&weights[0], &weights[1], &weights[2]]);
                ContactTriangle {
                    identifiers: [a.clone(), b.clone(), c.clone()],
                    stems,
                    weights,
                    corners,
                    euclidean,
                    composes_exactly: true,
                }
            })
            .collect();
        let reading = crate::contact_gluing::orient(&triangles);
        if reading.coherent {
            OrientationBit::Preserving
        } else {
            OrientationBit::Reversing {
                witness: reading.reversing,
            }
        }
    }
}

/// Connected components of a graph given as an edge list.
fn count_components(edges: &[(String, String)]) -> usize {
    let mut adjacency: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    for (left, right) in edges {
        adjacency
            .entry(left.as_str())
            .or_default()
            .push(right.as_str());
        adjacency
            .entry(right.as_str())
            .or_default()
            .push(left.as_str());
    }
    let seeds: Vec<&str> = adjacency.keys().copied().collect();
    let mut seen: BTreeSet<&str> = BTreeSet::new();
    let mut components = 0usize;
    for seed in seeds {
        if seen.contains(seed) {
            continue;
        }
        components += 1;
        let mut frontier = vec![seed];
        seen.insert(seed);
        while let Some(current) = frontier.pop() {
            let Some(neighbours) = adjacency.get(current) else {
                continue;
            };
            for next in neighbours.clone() {
                if seen.insert(next) {
                    frontier.push(next);
                }
            }
        }
    }
    components
}

/// The certificate that a declared triangulation is a surface.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceCertificate {
    /// Whether every check passed. A `false` here is never overridden by a later reading.
    pub is_surface: bool,
    /// The edges carried by exactly one triangle: the boundary.
    pub boundary_edges: Vec<(String, String)>,
    /// The edges carried by three or more: not a surface there.
    pub branching_edges: Vec<(String, String)>,
    /// How many circles the boundary edges form.
    pub boundary_circles: usize,
    /// Vertices whose link is not one path and not one cycle.
    pub bad_links: Vec<String>,
    /// Boundary vertices not carrying exactly two boundary edges.
    pub bad_boundary: Vec<String>,
}

/// The complete reading of a declared triangulation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceReading {
    /// Whose reading this is.
    pub lineage: String,
    /// `(vertices, edges, triangles)`.
    pub f_vector: (usize, usize, usize),
    /// `V − E + F`, from the cell counts.
    pub euler_characteristic: i64,
    /// The alternating sum of the Betti numbers. Equal to [`Self::euler_characteristic`] — two
    /// independent computations, and the equality is a check and not a definition.
    pub homology_euler_characteristic: i64,
    /// `b_k` over `ℤ` (free rank), from the Smith normal form.
    pub integral_betti: Vec<usize>,
    /// The torsion coefficients, every grade together.
    pub torsion: Vec<BigInt>,
    /// `b_k` over `𝔽₂`.
    pub mod_two_betti: Vec<usize>,
    /// How many circles the boundary forms.
    pub boundary_circles: usize,
    /// Orientable, or non-orientable with the seams exhibited.
    pub orientation: OrientationBit,
    /// The surface certificate.
    pub certificate: SurfaceCertificate,
}

impl SurfaceReading {
    /// Whether the rational and `𝔽₂` readings part anywhere — the face at which torsion at two,
    /// hence non-orientability of a closed surface, becomes visible.
    pub fn fields_part(&self) -> bool {
        self.integral_betti != self.mod_two_betti
    }
}

/// Which identification a grid's boundary carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GridIdentification {
    /// None: the grid is a rectangle.
    Open,
    /// `(x, q) ~ (x, 0)` and `(p, y) ~ (0, y)`: the torus.
    Torus,
    /// `(x, q) ~ (x, 0)` and `(p, y) ~ (0, q − y)`: the Klein bottle. The half-twist in the second
    /// identification is the whole difference, and it is the `ℤ/2` the record of 2026-08-16 calls
    /// the junction.
    Klein,
}

/// **A triangulated grid with a declared identification and declared removed squares.**
///
/// **The declared extent is bounded before anything is sized by it**: the vertex, edge and
/// triangle populations are all products of `cols` and `rows`, and the product is checked against
/// [`DECLARED_EXTENT_CEILING`] with checked arithmetic before the first allocation.
pub fn grid_triangulation(
    lineage: impl Into<String>,
    cols: usize,
    rows: usize,
    identification: GridIdentification,
    removed: &[(usize, usize)],
) -> Result<Triangulation, JunctionRefusal> {
    let extent = u64::try_from(cols)
        .ok()
        .and_then(|c| u64::try_from(rows).ok().and_then(|r| c.checked_mul(r)))
        .ok_or(JunctionRefusal::ExtentBeyondCeiling {
            declared: u64::MAX,
            ceiling: DECLARED_EXTENT_CEILING,
        })?;
    if cols == 0 || rows == 0 || extent > DECLARED_EXTENT_CEILING {
        return Err(JunctionRefusal::ExtentBeyondCeiling {
            declared: extent,
            ceiling: DECLARED_EXTENT_CEILING,
        });
    }
    for (i, j) in removed {
        if *i >= cols || *j >= rows {
            return Err(JunctionRefusal::DegenerateTriangulation {
                reason: format!("the removed square ({i}, {j}) lies outside the declared grid"),
            });
        }
    }
    let canon = |i: usize, j: usize| -> (usize, usize) {
        match identification {
            GridIdentification::Open => (i, j),
            GridIdentification::Torus => {
                let (mut i, mut j) = (i, j);
                if i == cols {
                    i = 0;
                }
                if j == rows {
                    j = 0;
                }
                (i, j)
            }
            GridIdentification::Klein => {
                let (mut i, mut j) = (i, j);
                if i == cols {
                    i = 0;
                    j = rows - j;
                }
                if j == rows {
                    j = 0;
                }
                (i, j)
            }
        }
    };
    let name = |i: usize, j: usize| -> String {
        let (i, j) = canon(i, j);
        format!("v{i}-{j}")
    };
    let mut triangles = Vec::with_capacity(2 * cols * rows);
    for i in 0..cols {
        for j in 0..rows {
            if removed.contains(&(i, j)) {
                continue;
            }
            let a = name(i, j);
            let b = name(i + 1, j);
            let c = name(i + 1, j + 1);
            let d = name(i, j + 1);
            triangles.push([a.clone(), b, c.clone()]);
            triangles.push([a, c, d]);
        }
    }
    Triangulation::declare(lineage, triangles)
}

/// **The pair of pants**: genus 0, three boundary circles, `χ = −1`, orientable.
///
/// Built as a rectangle with two square holes, which is `S²` minus three discs. Nothing about it
/// is asserted: [`Triangulation::reading`] computes `χ`, the Betti numbers over `ℤ` and `𝔽₂`, the
/// boundary circles and the orientation bit from this declaration.
pub fn pair_of_pants() -> Result<Triangulation, JunctionRefusal> {
    grid_triangulation(
        "surface|pair-of-pants",
        6,
        4,
        GridIdentification::Open,
        &[(1, 1), (3, 1)],
    )
}

/// **The Klein bottle**: two crosscaps, closed, `χ = 0`, non-orientable.
pub fn klein_bottle() -> Result<Triangulation, JunctionRefusal> {
    grid_triangulation("surface|klein-bottle", 4, 4, GridIdentification::Klein, &[])
}

/// **The Möbius shorts**: the Klein bottle with a disc removed — two crosscaps, one boundary
/// circle, `χ = −1`, non-orientable. The pair of pants' non-orientable sibling, and Brandon's
/// 2026-08-16 name for the junction.
///
/// Built by removing one triangle from [`klein_bottle`], which lowers `χ` by exactly one and opens
/// exactly one boundary circle.
pub fn mobius_shorts() -> Result<Triangulation, JunctionRefusal> {
    let closed = klein_bottle()?;
    let mut triangles = closed.triangles().to_vec();
    triangles.pop();
    Triangulation::declare("surface|mobius-shorts", triangles)
}

/// **The torus**: genus 1, closed, `χ = 0`, orientable. The Klein bottle's orientable sibling, and
/// the only difference between the two declarations is the half-twist in the second
/// identification.
pub fn torus() -> Result<Triangulation, JunctionRefusal> {
    grid_triangulation("surface|torus", 4, 4, GridIdentification::Torus, &[])
}

/// **The one-holed torus**: genus 1 with one boundary circle, `χ = −1`, orientable.
///
/// This is the **orientable surface that agrees with the Möbius shorts at every receiver but
/// one**: same Euler characteristic, same Betti numbers over `ℤ` and `𝔽₂`, same torsion, same
/// boundary count. The orientation bit is the only thing that separates them, and that is the
/// exact sense in which orientability is the extra `ℤ/2` beside the Euler characteristic.
pub fn one_holed_torus() -> Result<Triangulation, JunctionRefusal> {
    let closed = torus()?;
    let mut triangles = closed.triangles().to_vec();
    triangles.pop();
    Triangulation::declare("surface|one-holed-torus", triangles)
}

/// **The Möbius band**: one crosscap, one boundary circle, `χ = 0`, non-orientable. The five
/// vertex triangulation, which is the minimal one.
pub fn mobius_band() -> Result<Triangulation, JunctionRefusal> {
    let vertex = |at: usize| format!("m{at}");
    let triangles = (0..5usize)
        .map(|at| {
            [
                vertex(at),
                vertex((at + 1) % 5),
                vertex((at + 2) % 5),
            ]
        })
        .collect();
    Triangulation::declare("surface|mobius-band", triangles)
}

/// **An annulus**: the serial join thickened — two boundary circles, `χ = 0`, orientable.
pub fn annulus() -> Result<Triangulation, JunctionRefusal> {
    grid_triangulation("surface|annulus", 4, 4, GridIdentification::Open, &[(1, 1)])
}

/// Two surfaces compared on `RelationLadder`'s rungs.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SurfaceComparison {
    /// The rung the **surface-homology** receivers alone establish: the Euler characteristic, the
    /// integral Betti numbers, the torsion and the `𝔽₂` Betti numbers.
    pub homological_rung: Rung,
    /// The rung the full declared family establishes: those receivers together with the boundary
    /// count and the orientation bit. It is `rung_meet` of the two, so no rung is promoted.
    pub rung: Rung,
    /// The receivers that agree.
    pub agreeing: Vec<String>,
    /// Every receiver that separates them, each named. A separator is returned, never summarized.
    pub separators: Vec<String>,
}

/// **Compare two surface readings on the relation ladder.**
///
/// [established-bounded; implemented-exact] A compact surface with boundary is homotopy equivalent
/// to a wedge of circles whatever its orientability, so **no receiver reading the surface's own
/// homology can separate two of them with the same Euler characteristic**. The pair of pants and
/// the Möbius shorts are the first worked case: they agree on `χ`, on the integral Betti numbers,
/// on the torsion and on the `𝔽₂` Betti numbers, and are separated by the boundary count and by
/// the orientation bit. The **one-holed torus** against the Möbius shorts is the sharp case: those
/// two agree on the boundary count as well, and the orientation bit is the only separator left.
///
/// The returned rung is `relation_ladder::rung_meet` of the two families' rungs, so the coarser
/// family's `ReceiverEqual` is never promoted past the finer family's separation.
pub fn compare_surfaces(left: &SurfaceReading, right: &SurfaceReading) -> SurfaceComparison {
    let mut agreeing = Vec::new();
    let mut separators = Vec::new();
    let mut homological = true;
    for (name, agrees) in [
        (
            "euler-characteristic",
            left.euler_characteristic == right.euler_characteristic,
        ),
        ("integral-betti", left.integral_betti == right.integral_betti),
        ("torsion", left.torsion == right.torsion),
        ("mod-two-betti", left.mod_two_betti == right.mod_two_betti),
    ] {
        if agrees {
            agreeing.push(name.to_owned());
        } else {
            homological = false;
            separators.push(format!("{name}: the two readings differ"));
        }
    }
    let mut finer = true;
    if left.boundary_circles == right.boundary_circles {
        agreeing.push("boundary-circles".to_owned());
    } else {
        finer = false;
        separators.push(format!(
            "boundary-circles: {} against {}",
            left.boundary_circles, right.boundary_circles
        ));
    }
    if left.orientation.reverses() == right.orientation.reverses() {
        agreeing.push("orientation".to_owned());
    } else {
        finer = false;
        separators.push(
            "orientation: one carries a reversing dual circuit and the other does not".to_owned(),
        );
    }
    let homological_rung = if homological {
        Rung::ReceiverEqual
    } else {
        Rung::NoRelation
    };
    let finer_rung = if finer {
        Rung::ReceiverEqual
    } else {
        Rung::NoRelation
    };
    SurfaceComparison {
        homological_rung,
        rung: crate::relation_ladder::rung_meet(homological_rung, finer_rung),
        agreeing,
        separators,
    }
}

#[cfg(test)]
#[path = "junction_law/tests.rs"]
mod tests;
