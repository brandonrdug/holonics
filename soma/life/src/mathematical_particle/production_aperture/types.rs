use holonic_engine::native_ecology::inference_ecology::InferenceEcologyRest;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::super::{DynamicMorphologyRest, LongHorizonRetainedBoundary, MultimodalTransportRest};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionComponentIdentity {
    pub role: String,
    pub sha256: String,
    pub octets: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProductionDecision {
    Declined,
    Committed,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionWorldReturn {
    pub occurrence: String,
    pub emitted_product_sha256: String,
    pub returned_product_sha256: String,
    pub receiver: String,
    pub accepted: bool,
    pub exact_difference_octets: u64,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionStandingJunction {
    pub schema: String,
    pub component_identities: Vec<ProductionComponentIdentity>,
    pub receiver_basis: Vec<String>,
    pub history_basis: Vec<String>,
    pub genesis_decision_occurrence: String,
    pub decision_occurrence: String,
    pub decision: ProductionDecision,
    pub predecessor_identity: Option<String>,
    pub world_return: Option<ProductionWorldReturn>,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionFibreBinding {
    pub role: String,
    pub component_sha256: String,
    pub complete_reconstruction_component: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionReconstructionBoundary {
    pub schema: String,
    pub development_occurrence_sha256: Vec<String>,
    pub component_fibres: Vec<ProductionFibreBinding>,
    pub shortest_separating_receivers: Vec<String>,
    pub open_alternatives: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionInquiryPresentation {
    pub natural_language: String,
    pub notation: String,
    pub vector_face_sha256: String,
    pub raster_face_sha256: String,
    pub prior_history_occurrences: Vec<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProductionReceiver {
    Language,
    LeanProof,
    ExactValue,
    UnitDimension,
    ExactVisual,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionInquiryFace {
    pub left_species: u32,
    pub right_species: u32,
    pub oriented_relation: String,
    pub carrier: String,
    pub unit: String,
    pub dimension: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionInquiry {
    pub schema: String,
    pub occurrence: String,
    pub predecessor_rest_sha256: String,
    pub presentation: ProductionInquiryPresentation,
    pub context_word: Vec<u32>,
    pub receiver_family: Vec<ProductionReceiver>,
    pub requested_face: ProductionInquiryFace,
    pub heldout_family: u32,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProductionWithdrawalReceipt {
    pub committed_identity: String,
    pub predecessor_identity: String,
    pub restored_identity: String,
    pub exact_predecessor_restored: bool,
}

/// One continuing product ecology. It is intentionally neither `Clone` nor internally shared.
#[derive(Debug, PartialEq, Eq)]
pub struct ProductionAthenaRest {
    pub inference: InferenceEcologyRest,
    pub morphology: DynamicMorphologyRest,
    pub retained_boundary: LongHorizonRetainedBoundary,
    pub media: MultimodalTransportRest,
    pub junction: ProductionStandingJunction,
    pub reconstruction: ProductionReconstructionBoundary,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ProductionAthenaError {
    #[error("the I5 inference ecology refused: {0}")]
    Inference(String),
    #[error("the R3 morphology refused: {0}")]
    Morphology(String),
    #[error("the R4 retained boundary refused: {0}")]
    Boundary(String),
    #[error("the R5 media rest refused: {0}")]
    Media(String),
    #[error("the production component lineage, receiver basis, or reconstruction boundary moved")]
    Lineage,
    #[error(
        "the entering inquiry is malformed, belongs to development, or leaves the bounded aperture"
    )]
    Inquiry,
    #[error("the exterior world return is absent or malformed")]
    WorldReturn,
    #[error("the production cultivation decision is not founded by its immediate predecessor")]
    Decision,
    #[error("targeted production withdrawal did not restore the exact predecessor")]
    Withdrawal,
    #[error("the production extent cannot cross its exact wire")]
    Extent,
    #[error("production wire refused: {0}")]
    Wire(String),
}
