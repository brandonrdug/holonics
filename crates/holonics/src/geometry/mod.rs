//! **Geometry: the complex, frames, carriers and charts on which the Holon is placed.**
//!
//! - [`complex`]: oriented cells, `∂² = 0`, connection-valued incidence and its curvature;
//! - the exact frame carriers ([`RatVec3`], [`RatMat3`], [`AffineMap3`]) and the Cayley chart of
//!   rotations;
//! - [`screw`]: the Lie generator `ξ = (ω, v)` of a helix, situated screws, the screw pair and its
//!   quadrance jet;
//! - [`winding`]: phase, winding and carry, the odometer, and the holonomy around a cell;
//! - [`swing`]: the Swing, its composition to a translation, the pantograph and the projective
//!   Swing as a cross ratio.
//!
//! Lean: `Holon/Complex`, `Geometry/{ScrewGeometry,PhaseCarry,AffineSwing,CrossRatio}`,
//! `Transport/CellHolonomy`.

pub mod complex;
mod exact;
pub mod screw;
pub mod swing;
pub mod winding;

pub use exact::{
    AffineMap3, Axis, RatMat3, RatVec3, cayley_rotation_x, cayley_rotation_y, cayley_rotation_z,
    rational_circle,
};
