use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::laboratory_types::{LaboratoryAthenaRest, LaboratoryChronology};
use super::types::{ProductionInquiryPresentation, ProductionReceiver};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FixedSectionPlate {
    pub occurrence: String,
    pub returned_occurrence: String,
    pub dimension: u32,
    /// Zero is the integer carrier; every positive modulus is at least two.
    pub modulus: i64,
    pub action: Vec<i64>,
    /// Row-major inside a complete `dimension × dimension` exterior wire. Only the first
    /// `constraint_rows` rows are active.
    pub constraints: Vec<i64>,
    pub constraint_rows: u32,
    /// Row-major `dimension × constraint_rows`, certifying `A-I = L*C`.
    pub action_difference_factor: Vec<i64>,
    pub receiver_metric: Vec<i64>,
    pub support_coordinates: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyWorldReturn {
    pub occurrence: String,
    pub emitted_product_sha256: String,
    pub returned_lean_sha256: String,
    pub lean_exit_status: i32,
    pub accepted: bool,
    pub exact_difference_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyCultivationOccurrence {
    pub decision_occurrence: String,
    pub predecessor_identity: String,
    pub world_return: FamilyWorldReturn,
    pub plate: FixedSectionPlate,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyCultivationStanding {
    pub schema: String,
    pub l0_predecessor_sha256: String,
    pub genesis_decision_occurrence: String,
    pub cultivations: Vec<FamilyCultivationOccurrence>,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyCultivationDecoder {
    pub schema: String,
    pub expanded_transport_word: Vec<u32>,
    pub condensed_transport_word: Vec<u32>,
    pub obstruction_transport_word: Vec<u32>,
    pub composed_transport_word: Vec<u32>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyCultivationReconstruction {
    pub schema: String,
    pub developmental_occurrence_sha256: Vec<String>,
    pub complete_component_fibres: Vec<String>,
    pub shortest_separating_receivers: Vec<String>,
    pub unresolved_families: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyInquiry {
    pub schema: String,
    pub occurrence: String,
    pub predecessor_rest_sha256: String,
    pub presentation: ProductionInquiryPresentation,
    pub receiver_family: Vec<ProductionReceiver>,
    pub sections: Vec<Vec<i64>>,
    pub prior_history_occurrences: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FamilyWithdrawalReceipt {
    pub withdrawn_plate_occurrence: String,
    pub committed_identity: String,
    pub predecessor_identity: String,
    pub restored_identity: String,
    pub exact_immediate_predecessor_restored: bool,
}

/// L1's continuing ecology. It owns L0 and is intentionally neither `Clone` nor shared.
#[derive(Debug, PartialEq, Eq)]
pub struct FamilyCultivatedAthenaRest {
    pub(super) predecessor: LaboratoryAthenaRest,
    pub(super) chronology: LaboratoryChronology,
    pub(super) standing: FamilyCultivationStanding,
    pub(super) decoder: FamilyCultivationDecoder,
    pub(super) reconstruction: FamilyCultivationReconstruction,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum FamilyCultivationError {
    #[error("the L0 predecessor refused: {0}")]
    Predecessor(String),
    #[error("the L1 chronology or component lineage moved")]
    Chronology,
    #[error("the fixed-section plate lacks an exact support or factorization")]
    Plate,
    #[error("the L1 inquiry is malformed, belongs to development, or leaves the cultivated family")]
    Inquiry,
    #[error("the exterior family return is absent or malformed")]
    WorldReturn,
    #[error("the cultivation decision is not founded by its immediate predecessor")]
    Decision,
    #[error("family withdrawal did not restore the exact immediate predecessor")]
    Withdrawal,
    #[error("L1 wire refused: {0}")]
    Wire(String),
}
