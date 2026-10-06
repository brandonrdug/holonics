//! **Geometry: the complex, frames, carriers and charts on which the Holon is placed.**
//!
//! - [`complex`]: oriented cells, `∂² = 0`, connection-valued incidence and its curvature;
//! - the exact frame carriers ([`RatVec3`], [`RatMat3`], [`AffineMap3`]) and the Cayley chart of
//!   rotations;
//! - [`screw`]: the Lie generator `ξ = (ω, v)` of a helix, situated screws, the screw pair and its
//!   quadrance jet;
//! - [`winding`]: phase, winding and carry, the odometer, and the holonomy around a cell;
//! - [`motion`]: the move pair `(v, v′)` over the Gaussian integers, carried undivided, with its
//!   change, kind (rest, start, stop, free fall, turn, boost, turn and boost), traction disk, power
//!   and signed turn; the chase's lattice arithmetic;
//! - [`swing`]: the half-turn (one move of the Swing), its composition to a translation, the
//!   pantograph and the projective half-turn as a cross ratio.
//!
//! Lean: `Holon/Complex`, `Geometry/{ScrewGeometry,PhaseCarry,Motion,AffineSwing,CrossRatio}`,
//! `Transport/CellHolonomy`.

pub mod complex;
mod exact;
pub mod motion;
pub mod screw;
pub mod swing;
pub mod winding;

pub use exact::{
    AffineMap3, Axis, RatMat3, RatVec3, cayley_rotation_x, cayley_rotation_y, cayley_rotation_z,
    rational_circle,
};
