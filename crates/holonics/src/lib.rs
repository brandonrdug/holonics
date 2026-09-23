//! Public Holonics framework entry point. Implementations retain their existing owners.
//!
//! [`structure`], [`geometry`] and [`core`] currently re-export their existing package owners.
//! These three paths are remaining M1 forwarding boundaries; their implementations have not yet
//! moved into this crate. Geometry and structural carriers do not require a CUDA SDK or device
//! runtime. They do not encompass every mathematical construction in the repository.
//!
//! The current HNN implementation remains in the direct `holonics-hna` and `holonic-engine`
//! packages while M1 moves their backend-neutral laws into this crate and their resident execution
//! into `holonics-cuda`. Those packages are application-selected dependencies, not re-exported
//! compatibility paths from `holonics`. Package containers are distinct from standard executable
//! model graphs; see docs/INTEROPERABILITY.md.

pub use holonic_core as core;
pub use holonic_structure as structure;
pub use relational_geometry as geometry;
