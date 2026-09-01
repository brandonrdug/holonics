use holonic_engine::{
    receiver_exact_compression::{InputId, ReceiverExactCompression, ReceiverId},
    receiver_history_compression::ReceiverHistoryCompression,
};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ReceiverGrain {
    ReturnedSurface,
    BoundaryIncidence,
    WorldConsequence,
    ContinuationPort,
}

impl ReceiverGrain {
    pub const fn id(self) -> ReceiverId {
        ReceiverId(self as u64)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum TransportSpecies {
    ExteriorReturn,
    ExactRebase,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProposalRelationKind {
    Development,
    Sibling,
    HeldOut,
    Revisit,
    Rebase,
    Control,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RelationTargetFace {
    Family,
    Message,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalSectionAddress {
    pub source_item: u64,
    pub family_occurrence: String,
    pub predecessor_family_address: String,
    pub prompt_occurrence: String,
    pub history_occurrences: Vec<String>,
    pub response_occurrences: Vec<String>,
    pub later_return_occurrence: Option<String>,
    pub returned_surface_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportGeneratorAddress {
    pub generator: InputId,
    pub occurrence: String,
    pub species: TransportSpecies,
    pub nonidentity_passages: Vec<(String, String)>,
    pub exact_inverse_generator: Option<InputId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProposalRoleIncidence {
    pub proposal: String,
    pub relation: ProposalRelationKind,
    pub target: String,
    pub target_face: RelationTargetFace,
    pub addressed_lineage: String,
    pub witness: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SurfaceOnlyCounterexample {
    pub left_family: String,
    pub right_family: String,
    pub equal_returned_surface_sha256: String,
    pub separating_receiver: Option<ReceiverGrain>,
    pub shortest_ordered_word: Vec<String>,
    pub separated_by_terminus: bool,
    pub left_face: Option<u64>,
    pub right_face: Option<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResidentQuotientReceipt {
    pub schema: String,
    pub device: String,
    pub block_threads: u32,
    pub warp_size: u32,
    pub launches: u64,
    pub source_states: usize,
    pub receiver_grains: usize,
    pub transport_generators: usize,
    pub one_shot_classes: usize,
    pub receiver_history_classes: usize,
    pub memory_order: Option<usize>,
    pub cpu_device_partition_equal: bool,
    pub cpu_semantic_replay_after_device: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHistoryCongruence {
    pub schema: String,
    pub source_occurrence_sha256: String,
    pub receivers: Vec<ReceiverGrain>,
    pub sections: Vec<CausalSectionAddress>,
    pub transport_generators: Vec<TransportGeneratorAddress>,
    pub proposal_roles: Vec<ProposalRoleIncidence>,
    pub exact: ReceiverExactCompression,
    pub native: ReceiverHistoryCompression,
    pub surface_only_counterexamples: Vec<SurfaceOnlyCounterexample>,
    pub resident: ResidentQuotientReceipt,
    pub open_fibres: Vec<String>,
}
