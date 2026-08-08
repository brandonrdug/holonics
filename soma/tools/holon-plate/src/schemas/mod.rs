//! The schemas this reader holds.
//!
//! Three. Each is a form codec that exists in this body under its own owner; the plate holds them
//! and defines none of them:
//!
//! | tag | version | owner | what it is |
//! |---|---|---|---|
//! | `HTEC` | 1 | `soma/life/src/holonic_training.rs:443` | the training ecology's recurrent route population |
//! | `ERST` | 2 | `soma/membrane/src/live_current.rs:1241` | one direct-production body at a receiving-edge rest |
//! | `RBIN` | 1 | `crates/holonic-engine/src/graded_complex_form.rs` | one graded causal incidence, read for its rebase invariants |
//!
//! Adding a fourth means writing a `PlateSchema` and listing it in [`crate::registry`]. It does not
//! mean touching the container, which is why the container carries a version separate from theirs.
//!
//! Every one of them takes its `version()` **from the codec it holds** rather than from a literal
//! written here. A copied version is a claim about another crate's wire that stops being true
//! silently; a read one stops holding old plates by name.

pub mod current;
pub mod rebase;
pub mod training;

pub use current::{CurrentSchema, CURRENT_SCHEMA, CURRENT_SCHEMA_VERSION, CURRENT_TAG};
pub use rebase::{RebaseSchema, REBASE_SCHEMA, REBASE_SCHEMA_VERSION, REBASE_TAG};
pub use training::{TrainingSchema, TRAINING_SCHEMA, TRAINING_SCHEMA_VERSION, TRAINING_TAG};
