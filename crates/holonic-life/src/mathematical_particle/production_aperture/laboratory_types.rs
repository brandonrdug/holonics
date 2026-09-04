use holonic_engine::{
    generator_native_rest::GeneratorNativeRest,
    receiver_history_cultivation::CultivatedReceiverHistoryRest,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::types::{ProductionEcologyRest, ProductionInquiryPresentation, ProductionReceiver};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratorySourceChange {
    pub occurrence: String,
    pub status: String,
    pub lineage_path: String,
    pub blob_sha256: String,
    pub octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryCommitOccurrence {
    pub occurrence: String,
    pub commit: String,
    pub parent: String,
    pub tree: String,
    pub committed_unix_seconds: u64,
    pub summary: String,
    pub changes: Vec<LaboratorySourceChange>,
}

#[derive(Clone, Copy, Debug, Ord, PartialOrd, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LaboratoryPartitionKind {
    Development,
    HeldOutSuccessor,
    CodecNotationLayoutRebase,
    PhysicalApparatusPerturbation,
    EqualAnswerDifferentRoute,
    SubjectPortDisjointControl,
    LaterChronology,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryPartition {
    pub kind: LaboratoryPartitionKind,
    pub occurrences: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryChronology {
    pub schema: String,
    pub predecessor_commit: String,
    pub prefix_commit: String,
    pub prefix_tree: String,
    pub occurrences: Vec<LaboratoryCommitOccurrence>,
    pub partitions: Vec<LaboratoryPartition>,
    pub incrementally_mounted_octets: u64,
    pub whole_repository_semantic_materializations: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryInquiry {
    pub schema: String,
    pub occurrence: String,
    pub predecessor_rest_sha256: String,
    pub presentation: ProductionInquiryPresentation,
    pub receiver_family: Vec<ProductionReceiver>,
    /// Coefficients of `a*x^2 + b*x*y + c*y^2`.
    pub quadratic_section: [i64; 3],
    /// Complete chart map `(p,q,r,s)` for `x'=p*x+q*y`, `y'=r*x+s*y`.
    pub chart_map: [i64; 4],
    pub prior_history_occurrences: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryWorldReturn {
    pub occurrence: String,
    pub emitted_product_sha256: String,
    pub returned_lean_sha256: String,
    pub lean_exit_status: i32,
    pub accepted: bool,
    pub exact_difference_octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryMorphologyDelta {
    pub occurrence: String,
    pub returned_occurrence: String,
    pub support_coordinates: Vec<u32>,
    pub expanded_transport_word: Vec<u32>,
    pub condensed_transport_word: Vec<u32>,
    pub metric_adjoint_held: bool,
    pub exact_rank: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum LaboratoryDecision {
    Declined,
    Committed,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryStandingJunction {
    pub schema: String,
    pub component_identities: Vec<LaboratoryComponentIdentity>,
    pub genesis_decision_occurrence: String,
    pub decision_occurrence: String,
    pub decision: LaboratoryDecision,
    pub predecessor_identity: Option<String>,
    pub world_return: Option<LaboratoryWorldReturn>,
    pub morphology_delta: Option<LaboratoryMorphologyDelta>,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryComponentIdentity {
    pub role: String,
    pub sha256: String,
    pub octets: u64,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryReconstructionBoundary {
    pub schema: String,
    pub developmental_occurrence_sha256: Vec<String>,
    pub complete_component_fibres: Vec<String>,
    pub shortest_separating_receivers: Vec<String>,
    pub open_alternatives: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryRouteDecoder {
    pub schema: String,
    pub expanded_transport_word: Vec<u32>,
    pub condensed_transport_word: Vec<u32>,
    pub obstruction_transport_word: Vec<u32>,
    pub coefficient_basis: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryWithdrawalReceipt {
    pub committed_identity: String,
    pub predecessor_identity: String,
    pub restored_identity: String,
    pub exact_predecessor_restored: bool,
}

/// L0's continuing ecology.  It is intentionally neither `Clone` nor internally shared.
#[derive(Debug, PartialEq, Eq)]
pub struct LaboratoryProductionRest {
    pub production: ProductionEcologyRest,
    pub native: GeneratorNativeRest,
    pub cultivated_history: CultivatedReceiverHistoryRest,
    pub chronology: LaboratoryChronology,
    pub junction: LaboratoryStandingJunction,
    pub decoder: LaboratoryRouteDecoder,
    pub reconstruction: LaboratoryReconstructionBoundary,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum LaboratoryProductionError {
    #[error("the R6 production ecology refused: {0}")]
    Production(String),
    #[error("the M3 generator-native rest refused: {0}")]
    Native(String),
    #[error("the M4 cultivated history refused: {0}")]
    Cultivated(String),
    #[error("the addressed laboratory chronology or causal partitions moved")]
    Chronology,
    #[error("the entering laboratory inquiry is malformed or belongs to development")]
    Inquiry,
    #[error("the exterior Lean/world return is absent or malformed")]
    WorldReturn,
    #[error("the laboratory morphology decision is not founded by its immediate predecessor")]
    Decision,
    #[error("targeted laboratory withdrawal did not restore the exact predecessor")]
    Withdrawal,
    #[error("laboratory wire refused: {0}")]
    Wire(String),
}
