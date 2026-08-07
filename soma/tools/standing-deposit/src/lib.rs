//! The standing deposit and its verifier.
//!
//! The laboratory lost its tiger phase-atlas figures and a kernel-accepted theorem file named
//! `semantics_invariant_under_exact_chart.lean` to an untracked `runs/`. Only the name, the proof
//! term and a SHA-256 survive; neither is recoverable at any commit in either repository. The
//! archived C++ body is the one place that led — `cmake/HolonicDeposit.cmake` and
//! `cmake/HolonicRegistry.cmake` bound every deposited return to two hashes and separated the two
//! ways a binding can fail. `grep -rln closure_sha256` hit only the archive. This is that mechanism
//! in Rust.
//!
//! ```text
//!   plan  ──▶  deposit  ──▶  standing/MANIFEST.txt  ──▶  verify  ──▶  REFUSE | HELD
//!                                two hashes per row
//! ```
//!
//! Two hashes per deposited return:
//!
//! - the **content hash** of the deposited octets; and
//! - the **closure hash** of the founding that produced it — the executable together with every
//!   input it mounted, folded content-only and in declared order.
//!
//! And two failure species, which is the entire point:
//!
//! - **CONTENT drift** — the deposit no longer holds what was deposited. The evidence is corrupt.
//!   **REFUSE.**
//! - **CLOSURE drift** — the founding's material has moved. The machine has advanced past what it
//!   rested. **REPORT.** A standing that could not fall behind the current would not be standing.
//!
//! What this port adds over the archived original: the manifest records the founding's material, so
//! the closure is **recomputed** rather than proxied. `HolonicRegistry.cmake:64-72` could not
//! recompute — its manifest recorded only the resulting hash — so it compared the current build
//! tree's output to the recorded content hash instead. That proxy misreads in both directions.
//!
//! What this port also adds: the frame discipline in [`frame`]. No absolute path, no `..`, no
//! whitespace, and no path in the closure fold. `CLAUDE.md` §0: *"No absolute frame in a lineage."*

pub mod frame;
pub mod manifest;
pub mod plan;
pub mod registry;
pub mod sha256;

#[cfg(test)]
mod tests;

pub use frame::{FoundingName, RelPath};
pub use manifest::{DepositRow, FoundingRow, Manifest, MANIFEST_NAME};
pub use plan::{Founding, Plan};
pub use registry::{deposit, fold_closure, verify, verify_manifest, ClosureStatus, Verdict};
