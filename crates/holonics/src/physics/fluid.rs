//! **The fluid instance of the Holon law** (rebuild step 6, K3, #74; restructure plan §3.5 and §3.7
//! at `13f8c734`; [fluid construction](../../../../docs/HOLONIC_FLUID_CONSTRUCTION.md)).
//!
//! [definition] A fluid keeps its constitutive equations, its clocks, its heat and entropy returns
//! and its participating receiver. The instance is built on the elementary objects: cells of a
//! complex joined into a Holarchy, per-face returns paired with oriented boundaries, the Swing, the
//! Möbius navigator and the ratio carried with its winding. Every law computes over exact
//! rationals (Gaussian rationals where a complex number enters); no float and no evaluated
//! logarithm enters a law. Lean owner: `Physics/Fluid` (relative to the library root).
//!
//! - [`cells`] — battle test 1: cubical cells, `∂² = 0`, the Swing as a chain map with its hand
//!   `(−1)^k`, and the reflect-and-join of a square and a cube through [`crate::holarchy`], whose
//!   shared face cancels exactly once (Lean `Physics/Fluid/Cells`).
//! - [`control_volume`] — battle test 3: per-face returns of mass flux, momentum flux and
//!   traction, storage plus outflow equal to the source (against the continuity storage rate), the
//!   joined balance, Newtonian stress and the viscous heat handed to the thermal port with the
//!   cell's mechanical deficit, and the coholon reading of velocity, vorticity, pressure,
//!   circulation (the instantaneous face of Kelvin's) and the Lamb cross-current (Lean
//!   `Physics/Fluid/ControlVolume`). Battle test 3 stays open (#74) on the time advance and the
//!   pressure solve (#62).
//! - [`complex`] — battle test 4: the complex-bilinear fluid law and its Hermitian energy
//!   exchange, kept distinct from the Fourier chart of one real field (Lean
//!   `Physics/Fluid/ComplexFluid`).
//! - [`singularity`] — planar point-singularity flows as one-parameter Möbius navigators,
//!   classified by site kind, with the potential carried as the log of an undivided ratio with its
//!   winding (egg record §4; Lean `Physics/Fluid/Singularity`).
//! - [`body`] — a closed dividing streamline, an actual loop continued by path lifting, forces
//!   zero net strength (Gauss/Rankine necessity),
//!   the half-body counterexample, and the Gauss law on a Holarchy block (Lean
//!   `Physics/Fluid/Body`).
//!
//! The exact complex scalar of the last three is the ratio owner's Gaussian rational
//! ([`crate::ratio::GaussianRat`]), and the log of an undivided ratio with its winding is
//! [`crate::ratio::LogRatio`]; the Möbius generators are `compression::landmark`'s
//! [`crate::compression::landmark::MobiusNavigator`] over `ℚ(i)`.
//!
//! [open] A native source-conforming fluid solver (time advance, pressure solve, the
//! discretization defect of a non-affine field) and the continuum limit are owed (#62). The heat
//! port value is defined here; its consumer is the thermal instance's own module.

pub mod body;
pub mod cells;
pub mod complex;
pub mod control_volume;
pub mod singularity;

use thiserror::Error;

use crate::compression::landmark::LandmarkError;
use crate::holon::HolonError;
use crate::ratio::GaussianError;
use crate::ratio::linear::ExactLinearError;

/// Every refusal of the fluid instance. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum FluidError {
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("direction {direction} is not a direction of a grid chart of dimension at most 3")]
    Direction { direction: usize },
    #[error("the directions of a cell must be distinct and increasing")]
    Directions,
    #[error("the cell {what} is not a top cell of its chart")]
    NotATopCell { what: &'static str },
    #[error("{what} has no inverse: its value is zero")]
    ZeroDivisor { what: &'static str },
    #[error("{what} must be positive")]
    NotPositive { what: &'static str },
    #[error("the two singularities of a pair coincide")]
    CoincidentSingularities,
    #[error("the {order}-th roots of unity are not Gaussian rationals; the chart is refused")]
    NotAGaussianRoot { order: usize },
    #[error("the difference matrix is not antisymmetric, so its advection is not skew")]
    NotAntisymmetric,
    #[error("the turn fraction {numerator}/{denominator} has no rational cotangent")]
    IrrationalDirection { numerator: i64, denominator: i64 },
    #[error("the Cayley chart has its pole at this generator: rescale its clock")]
    CayleyPole,
    #[error("a one-parameter generator is traceless; this block is not")]
    NotTraceless,
    #[error(transparent)]
    Holon(#[from] HolonError),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Landmark(#[from] LandmarkError),
    #[error(transparent)]
    Gaussian(#[from] GaussianError),
}
