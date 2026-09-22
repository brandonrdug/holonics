//! **The hardware cover: declared charts, fronts and their decomposition** — owned by `holonic_core::hardware_cover`.
//!
//! [definition] Moved into the Holon core (`crates/holonic-core`) with the exact linear base it
//! belongs to; every public item is re-exported here at its existing path, explicitly, so each
//! `holonic_engine::hardware_cover::X` name, and any crate-root name it had, is unchanged. The module
//! documentation, the laws and their tests live with the owner.

pub use holonic_core::hardware_cover::{
    Chart, ChartId, CoverBarrier, CoverDecomposition, CoverSection, CpuDeclaration,
    DeviceDeclaration, FrontCell, HardwareCover, ModeIdentity, SectionWork, SurfaceRefusal,
    expand_front,
};
