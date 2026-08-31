//! Receiver/history compression and its exact native quotient owners.
//!
//! The implementation is partitioned by mathematical owner seams. Re-exports preserve the
//! historical module path and public API while keeping each owner reviewable.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::receiver_exact_compression::{
    CollapsedPair, InputId, ItemId, ObservedSystem, ReceiverExactCompression, ReceiverId,
};

mod compression;
mod factored_forms;
mod membrane;
mod observable;
mod projective_history;

pub use compression::*;
pub use factored_forms::*;
pub use membrane::*;
pub use observable::*;
pub use projective_history::*;

#[cfg(test)]
#[path = "receiver_history_compression/tests.rs"]
mod tests;
