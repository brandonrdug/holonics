//! Canonical receiver and native-action carriers.
//!
//! The finite quotient is discovered by the engine's source-qualified compression machinery.
//! This module owns only receiver identifiers and the state, transport, and receiver-factor
//! carriers shared by that discovery and its native realization. Lean peer:
//! `ElementaryHolonics.Foundation.ReceiverHistoryCompression`, whose naturality theorem proves
//! that the quotient commutes with every ordered generator word. Quotient assignments, source
//! fibres, shortest separators, and source-qualified witnesses remain in the engine.

use serde::{Deserialize, Serialize};

/// One declared receiver in a compression or native receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverId(pub u64);

/// One admitted generator/input that advances conduct.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct InputId(pub u64);

/// What a receiver returns from an item, exactly. An opaque exact token — never a magnitude.
///
/// It derives `Ord` because partition construction groups by observation signatures and the device
/// path uses the key. No law here reads that order as a magnitude: it is a canonical arrangement,
/// never a comparison of what two receivers returned. Subtracting, averaging, or thresholding these
/// values leaves the receiver calculus.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Observation(pub u64);

/// One state of the native quotient. Its ordinal is only the canonical address of a conduct block;
/// no arithmetic or semantic ordering is read from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct NativeStateId(pub u64);

/// One edge in an induced native generator transport.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeTransport {
    pub from: NativeStateId,
    pub to: NativeStateId,
}

/// The receiver factor `rhoBar_j : Q -> Face` at one native state.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFactor {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
}
