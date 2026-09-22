//! **The exact work of a reading, and its budget** — owned by `holonic_core::exact_work`.
//!
//! [definition] Moved into the Holon core (`crates/holonic-core`) with the exact linear base it
//! belongs to; every public item is re-exported here at its existing path, explicitly, so each
//! `holonic_engine::exact_work::X` name, and any crate-root name it had, is unchanged. The module
//! documentation, the laws and their tests live with the owner.

pub use holonic_core::exact_work::{Admission, ExactWork, WorkBudget, WorkMetric};
