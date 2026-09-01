use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralRelationalRecultivationReceipt {
    pub predecessor_rest_identity_sha256: String,
    pub successor_rest_identity_sha256: String,
    pub exchange_family_population: usize,
    pub ingress_occurrence_population: usize,
    pub emanation_occurrence_population: usize,
    pub return_occurrence_population: usize,
    pub native_factor_population: usize,
    pub native_face_population: usize,
    pub native_cell_population: usize,
    pub realization_presentation_population: usize,
    pub source_occurrence_ledger_retained: bool,
    pub exterior_surface_paths_are_native_identity: bool,
}
