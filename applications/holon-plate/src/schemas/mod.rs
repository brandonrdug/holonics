//! The schemas this reader holds.
//!
//! Three. Each is a form codec that exists in this body under its own owner; the plate holds them
//! and defines none of them:
//!
//! | tag | version | owner | what it is |
//! |---|---|---|---|
//! | `HTEC` | 2 | `crates/holonic-life/src/holonic_training.rs:443` | the training ecology's recurrent route population |
//! | `RBIN` | 1 | `crates/holonic-engine/src/graded_complex_form.rs` | one graded causal incidence, read for its rebase invariants |
//! | `CDER` | 1 | `crates/holonic-life/src/conditioned_rest.rs` | one conditioned derivation body: a founded morphology and the standing it conducts over |
//!
//! Adding a fifth means writing a `PlateSchema` and listing it in [`crate::registry`]. It does not
//! mean touching the container, which is why the container carries a version separate from theirs.
//!
//! Every one of them takes its `version()` **from the codec it holds** rather than from a literal
//! written here. A copied version is a claim about another crate's wire that stops being true
//! silently; a read one stops holding old plates by name.

pub mod conditioned;
pub mod rebase;
pub mod training;

pub use conditioned::{
    ConditionedSchema, CONDITIONED_SCHEMA, CONDITIONED_SCHEMA_VERSION, CONDITIONED_TAG,
};
pub use rebase::{RebaseSchema, REBASE_SCHEMA, REBASE_SCHEMA_VERSION, REBASE_TAG};
pub use training::{TrainingSchema, TRAINING_SCHEMA, TRAINING_SCHEMA_VERSION, TRAINING_TAG};
