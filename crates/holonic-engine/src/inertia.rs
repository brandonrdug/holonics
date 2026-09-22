//! **Exact symmetric forms and their inertia** — owned by `holonic_core::inertia`.
//!
//! [definition] Moved into the Holon core (`crates/holonic-core`) with the exact linear base it
//! belongs to; every public item is re-exported here at its existing path, explicitly, so each
//! `holonic_engine::inertia::X` name, and any crate-root name it had, is unchanged. The module
//! documentation, the laws and their tests live with the owner.

pub use holonic_core::inertia::{
    Inertia, InertiaError, InertiaSchedule, PivotOrder, PivotStep, PositiveSourceEnergy,
    PullbackInertia, SourceEnergyError, SymmetricForm, block_defect, congruence, inertia,
    inertia_with_order, inertia_with_schedule, inertia_with_work, positive_source_energy,
    pullback_inertia_bound, pullback_inertia_bound_with_work, rank_trace_defect,
};
