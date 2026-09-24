//! Exact, receiver-relative geometry of the Holonics library.
//!
//! This module is intentionally independent of Bevy, glam, and rendering
//! scalars.  It owns exact local frames, relations, algebraic faces,
//! receiver maps, projection fibers, crossings, and discrete event history.

pub mod decorated_path;
pub mod eta_atlas;
mod exact;
mod exact_analysis;
pub mod model;
pub mod projection;
pub mod receiver_atlas;
pub mod receiver_topology;
pub mod scene;
pub mod screw;
pub mod winding;

pub use decorated_path::*;
pub use eta_atlas::*;
pub use exact::*;
pub use exact_analysis::*;
pub use model::*;
pub use projection::*;
pub use receiver_atlas::*;
pub use receiver_topology::*;
pub use scene::*;
pub use screw::*;
pub use winding::*;
