//! Source-neutral addressed threads and inherited native transport scaffolds.
//!
//! The implementation is partitioned by owner: thread/core, deposits, situated withdrawal,
//! scaffold addressing, resident conduct, validation helpers, and refusal types. A `NativeSpool`
//! remains one reusable winding/generator family; `NativeTransportScaffold` owns the complete
//! compatible assembly.

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

mod deposits;
pub mod fixture;
mod helpers;
mod refusal;
mod resident;
mod scaffold;
mod situated;
mod thread;

pub use deposits::*;
pub(crate) use helpers::*;
pub use refusal::*;
pub use resident::*;
pub use scaffold::*;
pub use situated::*;
pub use thread::*;

#[cfg(test)]
#[path = "native_spool/tests.rs"]
mod tests;
