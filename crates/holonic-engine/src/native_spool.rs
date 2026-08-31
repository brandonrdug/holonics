//! Source-neutral addressed threads and reusable native spool complexes.
//!
//! The implementation is partitioned by owner: thread/core, deposits, situated withdrawal,
//! bundle addressing, resident conduct, validation helpers, and refusal types. Re-exports keep
//! the established `crate::native_spool::*` API intact.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::{
    EventId, ExactComplexWaveCurrent, ExactRatMatrix,
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
};

mod bundle;
mod deposits;
mod helpers;
mod refusal;
mod resident;
mod situated;
mod thread;

pub use bundle::*;
pub use deposits::*;
pub(crate) use helpers::*;
pub use refusal::*;
pub use resident::*;
pub use situated::*;
pub use thread::*;

#[cfg(test)]
#[path = "native_spool/tests.rs"]
mod tests;
