use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::native_family_types::{
    NativeCarrierChart, NativeGeneratorRelation, NativeHexisRest, NativeNaturalityReceipt,
    NativeShortestSeparator, NativeSuccessorHistory, ReceiverHistoryFactorization,
};
use super::types::{ProductionInquiryPresentation, ProductionReceiver};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTerrainWorldReturn {
    pub occurrence: String,
    pub emitted_product_sha256: String,
    pub returned_lean_sha256: String,
    pub lean_exit_status: i32,
    pub accepted: bool,
    pub exact_difference_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTerrainCultivation {
    pub decision_occurrence: String,
    pub predecessor_identity: String,
    pub world_return: NativeTerrainWorldReturn,
    pub carrier_chart: NativeCarrierChart,
    pub generator_relation: NativeGeneratorRelation,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTerrainStanding {
    pub schema: String,
    pub cultivation: NativeTerrainCultivation,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTerrainDecoder {
    pub schema: String,
    pub added_histories: Vec<NativeSuccessorHistory>,
    pub added_factorizations: Vec<ReceiverHistoryFactorization>,
    pub carrier_contacts: Vec<NativeNaturalityReceipt>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTerrainReconstruction {
    pub schema: String,
    pub generator_fibre_addition: Vec<String>,
    pub complete_fibres: Vec<String>,
    pub shortest_separators: Vec<NativeShortestSeparator>,
    pub unresolved_families: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTerrainInquiry {
    pub schema: String,
    pub occurrence: String,
    pub predecessor_rest_sha256: String,
    pub presentation: ProductionInquiryPresentation,
    pub receiver_family: Vec<ProductionReceiver>,
    pub sections: Vec<Vec<i64>>,
    pub revisited_histories: Vec<NativeSuccessorHistory>,
    pub prior_history_occurrences: Vec<String>,
    pub ablated_family: Option<u32>,
}

/// L3's continuing ecology. It consumes the L2 rest, owns one returned local delta, and is neither
/// `Clone` nor shared. Exact withdrawal transfers the owned L2 predecessor back to the caller.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeTerrainRest {
    pub(super) predecessor: NativeHexisRest,
    pub(super) standing: NativeTerrainStanding,
    pub(super) decoder: NativeTerrainDecoder,
    pub(super) reconstruction: NativeTerrainReconstruction,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeTerrainWithdrawalReceipt {
    pub cultivated_identity: String,
    pub predecessor_identity: String,
    pub restored_identity: String,
    pub withdrawn_chart_occurrence: String,
    pub exact_immediate_predecessor_restored: bool,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeTerrainError {
    #[error("the L2 predecessor refused the L3 terrain: {0}")]
    Predecessor(String),
    #[error("the returned passage does not found one local carrier chart")]
    WorldReturn,
    #[error("the added chart or generator relation is malformed")]
    CarrierChart,
    #[error("the added receiver/history factors or carrier contacts are incomplete")]
    ReceiverHistory,
    #[error("the L3 reconstruction boundary is incomplete")]
    Reconstruction,
    #[error("the L3 inquiry is malformed or addresses another terrain")]
    Inquiry,
    #[error("L3 withdrawal did not restore the exact L2 predecessor")]
    Withdrawal,
    #[error("L3 wire refused: {0}")]
    Wire(String),
}
