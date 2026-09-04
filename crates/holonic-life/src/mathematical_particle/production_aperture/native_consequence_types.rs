use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::native_family_types::{
    NativeCollapsedPopulation, NativeShortestSeparator, NativeSuccessorHistory,
};

/// N0 begins after a material codec has already returned native incidence. Raw optical recovery is
/// deliberately outside this port and remains N1's open deed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeMathematicalPort {
    RecoveredOperationConstraintGeometry,
}

/// The productive receiver family contains only native consequences. Surface languages and
/// checkers cannot be represented here; they enter later through [`NativeCodec`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeMathematicalReceiver {
    OperationIncidence,
    ConstraintReturn,
    GeometryIncidence,
    ExactConsequence,
    DerivationalTransport,
    ReconstructionFibre,
    AddressedLineage,
    ObstructionExterior,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMathematicalInquiry {
    pub schema: String,
    pub occurrence: String,
    pub predecessor_rest_sha256: String,
    pub port: NativeMathematicalPort,
    pub source_occurrences: Vec<String>,
    pub receiver_family: Vec<NativeMathematicalReceiver>,
    pub sections: Vec<Vec<i64>>,
    pub requested_histories: Vec<NativeSuccessorHistory>,
    pub prior_history_occurrences: Vec<String>,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOperationCell {
    pub occurrence: String,
    pub carrier_chart_occurrence: String,
    pub generator_relation_occurrence: String,
    pub source_boundary: String,
    pub target_boundary: String,
    pub entered_section: Vec<i64>,
    pub returned_section: Vec<i64>,
    pub exact_difference: Vec<i64>,
    pub ordered_transport_word: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeConstraintCell {
    pub occurrence: String,
    pub carrier_chart_occurrence: String,
    pub orientation: Vec<i8>,
    pub exact_residual: i64,
    pub held: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGeometryVertex {
    pub coordinate: u32,
    pub entered: i64,
    pub returned: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeGeometryCell {
    pub occurrence: String,
    pub carrier_chart_occurrence: String,
    pub vertices: Vec<NativeGeometryVertex>,
    pub constraint_incidence: Vec<i8>,
    pub transport_incidence: Vec<i8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeExactConsequenceFace {
    pub carrier_chart_occurrence: String,
    pub returned_section: Vec<i64>,
    pub exact_residual: i64,
    pub selected_route: u32,
    pub fixed_section: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMathematicalComplex {
    pub operation_cells: Vec<NativeOperationCell>,
    pub constraint_cells: Vec<NativeConstraintCell>,
    pub geometry_cells: Vec<NativeGeometryCell>,
    pub exact_consequence_faces: Vec<NativeExactConsequenceFace>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeDerivationTransport {
    pub occurrence: String,
    pub predecessor_occurrence: String,
    pub successor_occurrence: String,
    pub ordered_word: Vec<u32>,
    pub prior_history_occurrences: Vec<String>,
    pub returned_difference: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeDeviceRouteFibre {
    pub carrier_chart_occurrence: String,
    pub selected_route: u32,
    pub exact_ablation_route: u32,
    pub local_ablation_preserves_joint_contact: bool,
    pub complete_route_population: Vec<u32>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeConsequenceReconstruction {
    pub inherited_collapsed_populations: Vec<NativeCollapsedPopulation>,
    pub complete_inherited_fibres: Vec<String>,
    pub device_route_fibres: Vec<NativeDeviceRouteFibre>,
    pub shortest_available_separators: Vec<NativeShortestSeparator>,
    pub unresolved_families: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAddressedConsequenceSpan {
    pub occurrence: String,
    pub left_boundary_map: String,
    pub right_boundary_map: String,
    pub joining_equality: String,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeConsequenceLineage {
    pub predecessor_rest_sha256: String,
    pub inquiry_occurrence: String,
    pub source_occurrences: Vec<String>,
    pub addressed_spans: Vec<NativeAddressedConsequenceSpan>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeReturnedObstruction {
    pub carrier_chart_occurrence: String,
    pub exact_residual: i64,
    pub selected_route: u32,
    pub reason: String,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeConsequenceExterior {
    pub returned_obstructions: Vec<NativeReturnedObstruction>,
    pub inquiry_open_exterior: Vec<String>,
    pub rested_open_exterior: Vec<String>,
    pub unresolved_families: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeApparatusReceipt {
    pub device: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub typed_reductions: u64,
    pub active_lanes: u32,
    pub semantic_work: String,
    pub semantic_span: u64,
    pub resident_octets: u64,
    pub transfer_octets: u64,
    pub host_semantic_callbacks: u32,
}

/// The frozen N0 return. It is intentionally not `Clone`; projections borrow it after its native
/// identity has been fixed.
#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMathematicalConsequence {
    pub schema: String,
    pub truth_status: String,
    pub occurrence: String,
    pub inquiry_occurrence: String,
    pub predecessor_rest_sha256: String,
    pub receiver_family: Vec<NativeMathematicalReceiver>,
    pub complex: NativeMathematicalComplex,
    pub derivational_transport: Vec<NativeDerivationTransport>,
    pub reconstruction: NativeConsequenceReconstruction,
    pub lineage: NativeConsequenceLineage,
    pub exterior: NativeConsequenceExterior,
    pub apparatus: NativeApparatusReceipt,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeCodec {
    ExactNotation,
    Json,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCodecProjection {
    pub schema: String,
    pub truth_status: String,
    pub codec: NativeCodec,
    pub native_consequence_occurrence: String,
    pub media_type: String,
    pub payload: String,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeMathematicalConsequenceError {
    #[error("the generator-native predecessor refused: {0}")]
    Predecessor(String),
    #[error("the native inquiry is malformed or addresses another rest")]
    Inquiry,
    #[error("the resident fixed-section passage refused: {0}")]
    Apparatus(String),
    #[error("the resident return does not carry the complete native consequence")]
    IncompleteReturn,
    #[error("the optional codec projection refused: {0}")]
    Codec(String),
}
