//! The schemas this reader holds.
//!
//! Two, both of which already existed as form codecs in this body before the plate did:
//!
//! | tag | version | owner | what it is |
//! |---|---|---|---|
//! | `HTEC` | 1 | `soma/life/src/holonic_training.rs:443` | the training ecology's recurrent route population |
//! | `ERST` | 2 | `soma/membrane/src/live_current.rs:1241` | one direct-production body at a receiving-edge rest |
//!
//! Adding a third means writing a `PlateSchema` and listing it in [`crate::registry`]. It does not
//! mean touching the container, which is why the container carries a version separate from theirs.

pub mod current;
pub mod training;

pub use current::{CurrentSchema, CURRENT_SCHEMA, CURRENT_SCHEMA_VERSION, CURRENT_TAG};
pub use training::{TrainingSchema, TRAINING_SCHEMA, TRAINING_SCHEMA_VERSION, TRAINING_TAG};
