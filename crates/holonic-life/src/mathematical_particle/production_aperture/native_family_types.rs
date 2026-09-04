use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::types::{ProductionInquiryPresentation, ProductionReceiver};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOrientedGenerator {
    pub occurrence: String,
    pub dimension: u32,
    pub constraint_orientation: Vec<i8>,
    pub action_difference_orientation: Vec<i8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCarrierChart {
    pub source_plate_occurrence: String,
    pub returned_occurrence: String,
    pub cultivation_decision_occurrence: String,
    pub source_plate_sha256: String,
    pub modulus: i64,
    pub support_coordinates: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGeneratorRelation {
    pub occurrence: String,
    pub source_action_sha256: String,
    pub source_constraint_sha256: String,
    pub source_factor_sha256: String,
    pub identity_plus_oriented_outer_product: bool,
    pub fixed_kernel_factors: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeHexisStanding {
    pub schema: String,
    pub cultivated_predecessor_sha256: String,
    pub generator: NativeOrientedGenerator,
    pub carrier_charts: Vec<NativeCarrierChart>,
    pub relations: Vec<NativeGeneratorRelation>,
    pub exact_interchange: bool,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeSuccessorHistory {
    FixedSection,
    ExpandedGenerator,
    ComposedJoint,
    LocalAblation { family: u32 },
    CarrierRebase { source: u32, target: u32 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum FactorizationStatus {
    Exact,
    ExactDefect,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverHistoryFactorization {
    pub receiver: ProductionReceiver,
    pub history: NativeSuccessorHistory,
    pub status: FactorizationStatus,
    pub consequence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeNaturalityReceipt {
    pub source_chart: u32,
    pub target_chart: u32,
    pub intervention_section: Vec<i64>,
    pub source_transport: Vec<i64>,
    pub target_transport: Vec<i64>,
    pub rebased_source_transport: Vec<i64>,
    pub generator_square_commutes: bool,
    pub source_route: u32,
    pub target_route: u32,
    pub cultivation_square_commutes: bool,
    pub exact_defect: String,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeHexisDecoder {
    pub schema: String,
    pub receivers: Vec<ProductionReceiver>,
    pub declared_histories: Vec<NativeSuccessorHistory>,
    pub factorizations: Vec<ReceiverHistoryFactorization>,
    pub naturality: Vec<NativeNaturalityReceipt>,
    pub expanded_transport_word: Vec<u32>,
    pub fixed_transport_word: Vec<u32>,
    pub obstruction_transport_word: Vec<u32>,
    pub composed_transport_word: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCollapsedPopulation {
    pub native_occurrence: String,
    pub source_occurrences: Vec<String>,
    pub complete: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeShortestSeparator {
    pub proposed_quotient: String,
    pub equal_present_sections: Vec<Vec<i64>>,
    pub successor_sections: Vec<Vec<i64>>,
    pub returned_residuals: Vec<i64>,
    pub returned_routes: Vec<u32>,
    pub shortest_word: Vec<u32>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeHexisReconstruction {
    pub schema: String,
    pub predecessor_component_addresses: Vec<String>,
    pub collapsed_populations: Vec<NativeCollapsedPopulation>,
    pub complete_fibres: Vec<String>,
    pub shortest_separators: Vec<NativeShortestSeparator>,
    pub unresolved_families: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeHexisInquiry {
    pub schema: String,
    pub occurrence: String,
    pub predecessor_rest_sha256: String,
    pub presentation: ProductionInquiryPresentation,
    pub receiver_family: Vec<ProductionReceiver>,
    pub sections: Vec<Vec<i64>>,
    pub prior_history_occurrences: Vec<String>,
}

/// L2 replaces the cultivated source shape with a local generator-native rest.  It deliberately
/// owns no L1 source body and is neither `Clone` nor an inverse of its quotient.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeHexisRest {
    pub(super) standing: NativeHexisStanding,
    pub(super) decoder: NativeHexisDecoder,
    pub(super) reconstruction: NativeHexisReconstruction,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeHexisError {
    #[error("the cultivated L1 predecessor refused native condensation: {0}")]
    CultivatedPredecessor(String),
    #[error("the cultivated passages do not share one exact oriented generator relation")]
    GeneratorRelation,
    #[error("the native carrier charts or their exact interchange are malformed")]
    CarrierCharts,
    #[error("a declared receiver/history lacks an exact factorization or defect")]
    ReceiverHistory,
    #[error("the complete reconstruction fibres or shortest separator are malformed")]
    Reconstruction,
    #[error("the L2 inquiry is malformed or addresses another rest")]
    Inquiry,
    #[error("L2 wire refused: {0}")]
    Wire(String),
}
