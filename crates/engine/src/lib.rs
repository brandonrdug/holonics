//! The engine: the built attempt that trains, its law and its host reference (docs/plans/THE_CONSOLIDATION.md, D1 and D2).
//!
//! C3 of the consolidation (#603) lifted it here from `crates/holonics` by moves only: `field` is `hnn::tower::field` and its
//! submodules as they stood, and `inherited` holds the items it borrowed from the October machine, each from the file it stood in.
//! `crates/holonics` imports both back under their old paths for as long as it stands. C5 cuts the engine by object (§5).

pub mod field;
pub mod inherited;
