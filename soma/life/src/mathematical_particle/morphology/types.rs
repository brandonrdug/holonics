use holonic_engine::exact_linear::ExactRatMatrix;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::super::DerivationRecurrenceRest;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ConstraintReceiver {
    ProofChecker,
    ExactOwner,
    Rendering,
    PhysicalBoundary,
    LaterOperator,
}

impl ConstraintReceiver {
    pub(super) const FAMILY: [Self; 5] = [
        Self::ProofChecker,
        Self::ExactOwner,
        Self::Rendering,
        Self::PhysicalBoundary,
        Self::LaterOperator,
    ];
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedConstraintOccurrence {
    pub receiver: ConstraintReceiver,
    pub emission_occurrence: String,
    pub world_occurrence: String,
    pub return_occurrence: String,
    pub consequence_sha256: String,
    pub primitive_orientation: i32,
    pub support_native_states: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactSupportSubcomplex {
    pub native_states: Vec<u32>,
    pub source_terminal_events: Vec<u64>,
    pub returned_occurrences: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CausingForwardLineage {
    pub entering_native_state: u32,
    pub terminal_native_state: u32,
    pub source_terminal_events: Vec<u64>,
    pub return_occurrences: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedReceiverAdjoint {
    pub support_incidence: ExactRatMatrix,
    pub receiver_covector: ExactRatMatrix,
    pub state_metric: ExactRatMatrix,
    pub receiver_metric: ExactRatMatrix,
    pub metric_adjoint: ExactRatMatrix,
    pub returned_native_covector: ExactRatMatrix,
    pub primitive_native_covector: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConstitutiveActionChange {
    pub added_native_state: u32,
    pub supported_from: u32,
    pub predecessor_to: u32,
    pub successor_to: u32,
    pub predecessor_action: Vec<u32>,
    pub successor_action: Vec<u32>,
    pub action_delta: ExactRatMatrix,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MorphologyCompatibilityReceipt {
    pub one_common_support_face: bool,
    pub one_shared_delta_not_parallel_updates: bool,
    pub disjoint_control_occurrence: String,
    pub disjoint_control_absent_from_support: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CultivationHolonomy {
    pub predecessor_action: ExactRatMatrix,
    pub local_delta: ExactRatMatrix,
    pub commutator: ExactRatMatrix,
    pub commutator_rank: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReconstructionFibreChange {
    pub predecessor_native_state: u32,
    pub retained_source_terminal_events: Vec<u64>,
    pub opened_successor_native_state: u32,
    pub withdrawal_reopens_predecessor_fibre: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactWithdrawal {
    pub predecessor_sha256: String,
    pub subtracts_addressed_delta: bool,
    pub removes_opened_state_and_relation: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalMorphologyDelta {
    pub predecessor_occurrence: String,
    pub exact_support_subcomplex: ExactSupportSubcomplex,
    pub causing_forward_lineage: CausingForwardLineage,
    pub returned_receiver_adjoint: ReturnedReceiverAdjoint,
    pub constitutive_action_change: ConstitutiveActionChange,
    pub compatibility: MorphologyCompatibilityReceipt,
    pub changed_and_reopened_fibres: Vec<ReconstructionFibreChange>,
    pub cultivation_holonomy: CultivationHolonomy,
    pub exact_withdrawal: ExactWithdrawal,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DynamicMorphologyRest {
    pub schema: String,
    pub predecessor: DerivationRecurrenceRest,
    pub returned_constraints: Vec<ReturnedConstraintOccurrence>,
    pub development_occurrence: String,
    pub held_out_occurrence: String,
    pub development_start: u32,
    pub held_out_start: u32,
    pub delta: LocalMorphologyDelta,
}

#[derive(Debug)]
pub struct DynamicMorphologyCandidate {
    pub(super) predecessor: DerivationRecurrenceRest,
    pub(super) returned_constraints: Vec<ReturnedConstraintOccurrence>,
    pub(super) development_occurrence: String,
    pub(super) held_out_occurrence: String,
    pub(super) development_start: u32,
    pub(super) held_out_start: u32,
    pub(super) delta: LocalMorphologyDelta,
}

#[derive(Debug, PartialEq, Eq)]
pub enum MorphologyDecision {
    Committed(DynamicMorphologyRest),
    Declined {
        predecessor: DerivationRecurrenceRest,
        reason: String,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WithdrawalReceipt {
    pub predecessor_sha256: String,
    pub restored_sha256: String,
    pub exact_predecessor_restored: bool,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DynamicMorphologyError {
    #[error("the returned-constraint occurrence family is incomplete or inconsistent")]
    ReturnedConstraint,
    #[error("the returned constraints do not share one exact local support subcomplex")]
    Support,
    #[error("the development, held-out, control, or return lineage is incomplete")]
    Lineage,
    #[error("no structurally related held-out start reaches the cultivated support")]
    HeldOut,
    #[error("the finite morphology extent cannot cross its exact wire")]
    Extent,
    #[error("the declared metric adjoint does not return the candidate support")]
    Adjoint,
    #[error("the constitutive action change is not one exact local relation")]
    Action,
    #[error("the revisit commutator carries no cultivation holonomy")]
    Holonomy,
    #[error("the resident morphology passage disagrees with the exact candidate")]
    Device,
    #[error("targeted withdrawal did not restore the immediate predecessor")]
    Withdrawal,
    #[error("the source-detached dynamic morphology rest is inconsistent")]
    Identity,
    #[error("dynamic morphology wire refused: {0}")]
    Wire(String),
    #[error("R2 predecessor refused: {0}")]
    Predecessor(String),
    #[error("exact linear transport refused: {0}")]
    ExactLinear(String),
}

impl From<super::super::DerivationRecurrenceError> for DynamicMorphologyError {
    fn from(value: super::super::DerivationRecurrenceError) -> Self {
        Self::Predecessor(value.to_string())
    }
}

impl From<holonic_engine::exact_linear::ExactLinearError> for DynamicMorphologyError {
    fn from(value: holonic_engine::exact_linear::ExactLinearError) -> Self {
        Self::ExactLinear(value.to_string())
    }
}
