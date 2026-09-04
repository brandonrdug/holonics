use holonic_engine::receiver_exact_compression::{CollapsedPair, ItemId, Observation, ReceiverId};
use holonic_engine::receiver_history_compression::{NativeStateId, ReceiverFactor};
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub const LONG_HORIZON_STANDING_SCHEMA: &str = "holonics.r4.retained-boundary-standing.v1";
pub const LONG_HORIZON_DECODER_SCHEMA: &str = "holonics.r4.retained-boundary-decoder.v1";
pub const LONG_HORIZON_FIBRES_SCHEMA: &str = "holonics.r4.retained-boundary-fibres.v1";

/// One exact interior occurrence.  The payload remains in the reconstruction component and never
/// enters hot native standing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HistoricalInterior {
    pub occurrence: String,
    pub predecessor: Option<String>,
    pub payload_sha256: String,
    pub payload: Vec<u8>,
}

/// One source realization of an interior at a continuing physical boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HistoricalSourceMember {
    pub item: ItemId,
    pub interior: u32,
    pub physical_state: u32,
    pub base_observations: Vec<Observation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CultivatedActionLineage {
    pub dynamic_rest_sha256: String,
    pub predecessor_action_sha256: String,
    pub successor_action_sha256: String,
    pub returned_occurrences: Vec<String>,
    pub commutator_rank: usize,
}

/// First recurrence is derived from the finite action, never from a response limit.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryRecurrence {
    pub generator: u32,
    pub entering: NativeStateId,
    pub trace: Vec<NativeStateId>,
    pub first_repeated_state: NativeStateId,
    pub first_at: usize,
    pub returned_at: usize,
}

/// The noncommuting two-word return carried from R3's cultivated action family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OrderedBoundaryHolonomy {
    pub entering: NativeStateId,
    pub left_word: Vec<u32>,
    pub right_word: Vec<u32>,
    pub left_trace: Vec<NativeStateId>,
    pub right_trace: Vec<NativeStateId>,
    pub left_endpoint: NativeStateId,
    pub right_endpoint: NativeStateId,
    pub commutator_rank: usize,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedBoundaryStanding {
    pub schema: String,
    pub predecessor_identity: String,
    pub boundary_identity: String,
    pub source_compression_sha256: String,
    pub native_states: Vec<NativeStateId>,
    pub source_physical_states: u32,
    /// The material-founded action before the receiver/history quotient.
    pub source_physical_action: Vec<u32>,
    pub physical_to_native: Vec<NativeStateId>,
    /// Row-major `[generator][native state]`.
    pub generator_table: Vec<u32>,
    pub receiver_ids: Vec<ReceiverId>,
    pub receiver_factors: Vec<ReceiverFactor>,
    pub cultivation: CultivatedActionLineage,
    pub recurrences: Vec<BoundaryRecurrence>,
    pub ordered_holonomy: OrderedBoundaryHolonomy,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedBoundaryDecoder {
    pub schema: String,
    pub interiors: Vec<HistoricalInterior>,
    pub source_members: Vec<HistoricalSourceMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RicherReceiverReopening {
    pub native: NativeStateId,
    pub left_item: ItemId,
    pub right_item: ItemId,
    pub left_occurrence: String,
    pub right_occurrence: String,
    pub receiver_occurrence: String,
    pub left_reading_sha256: String,
    pub right_reading_sha256: String,
    pub shortest_history: Vec<u32>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedBoundaryFibres {
    pub schema: String,
    pub fibres: Vec<(NativeStateId, Vec<ItemId>)>,
    pub shortest_separators: Vec<CollapsedPair>,
    pub richer_reopenings: Vec<RicherReceiverReopening>,
}

/// One continuing context owner, serialized as standing/decoder/fibres rather than a transcript.
#[derive(Debug, PartialEq, Eq)]
pub struct LongHorizonRetainedBoundary {
    pub standing: RetainedBoundaryStanding,
    pub decoder: RetainedBoundaryDecoder,
    pub fibres: RetainedBoundaryFibres,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum LongHorizonBoundaryError {
    #[error("the addressed history system is malformed")]
    System,
    #[error("the source receiver/history compression refused: {0}")]
    Compression(String),
    #[error("the predecessor, boundary, cultivation, or source identity is incomplete")]
    Identity,
    #[error("the retained boundary standing is malformed")]
    Standing,
    #[error("the historical decoder is incomplete or cannot reconstruct its lineage")]
    Decoder,
    #[error("the reconstruction fibres do not partition the source occurrence family")]
    Fibre,
    #[error("no richer later receiver reopens a retained historical interior")]
    Reopening,
    #[error("the cultivated action family returns no noncommuting ordered word")]
    Holonomy,
    #[error("retained boundary wire refused: {0}")]
    Wire(String),
}
