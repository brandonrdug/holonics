use super::*;

/// Exact obstruction returned when the same later current and native-radiation receiver meet a
/// body whose addressed inherited carrier has been moved out.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralNativeRadiationObstruction {
    pub schema: String,
    pub original_rest_identity_sha256: String,
    pub ablated_body_identity_sha256: String,
    pub ingress_current_identity_sha256: String,
    pub standing_potential_identity_sha256: String,
    pub spool_address: String,
    pub thread_address: String,
    pub receiver_insufficiency: ReceiverInsufficiency,
    pub same_later_current_held: bool,
    pub same_native_radiation_receiver_held: bool,
    pub source_codec_consulted: bool,
    pub exterior_reconstruction_fibre_reachable: bool,
    pub identity_sha256: String,
}

/// Move-owned staged ablation of one structurally inherited thread.
pub struct SourceNeutralInheritedThreadAblation {
    pub(super) original_rest_identity_sha256: String,
    pub(super) ablated_body_identity_sha256: String,
    pub(super) spool_address: String,
    pub(super) thread_address: String,
    pub(super) ecology: NativeSituatedSpoolBundle,
    pub(super) branches: Vec<SourceNeutralCultivationBranch>,
    pub(super) predecessor_deposit_receipt: NativeThreadDepositBatchReceipt,
    pub(super) returned_deposits: Vec<SourceNeutralReturnedDeposit>,
    pub(super) granular: NativeGranularPotential,
    pub(super) relational: SourceNeutralRelationalMorphology,
    pub(super) realization: SourceNeutralExteriorRealizationMorphology,
    pub(super) acoustic: SourceNeutralAcousticMorphology,
    pub(super) optical: SourceNeutralOpticalMorphology,
    pub(super) withdrawal: NativeSituatedThreadWithdrawal,
    pub(super) receiver_insufficiency: ReceiverInsufficiency,
}

/// Exact dynamic receipt for a moved receiver-radical direction.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralRadicalConductPreservationReceipt {
    pub schema: String,
    pub original_rest_identity_sha256: String,
    pub ablated_body_identity_sha256: String,
    pub fibre_address: String,
    pub direction_position: usize,
    pub direction: Vec<Rat>,
    pub returned_covector_before: Vec<Rat>,
    pub returned_covector_after: Vec<Rat>,
    pub withdrawn_direction_return: Vec<Rat>,
    pub conduct_constitution_before_sha256: String,
    pub conduct_constitution_after_sha256: String,
    pub held_later_current_identity_sha256: String,
    pub child_receiver_consequence_identity_sha256: String,
    pub preserved_receiver_consequence_identity_sha256: String,
    pub same_later_current_held: bool,
    pub same_native_radiation_constitution: bool,
    pub withdrawn_direction_in_receiver_radical: bool,
    pub returned_covector_preserved: bool,
    pub source_codec_consulted: bool,
    pub exterior_reconstruction_fibre_reachable: bool,
    pub identity_sha256: String,
}

/// Move-owned staging of one support-disjoint radical withdrawal.
pub struct SourceNeutralRadicalDirectionAblation {
    pub(super) original_rest_identity_sha256: String,
    pub(super) ablated_body_identity_sha256: String,
    pub(super) fibre_address: String,
    pub(super) direction_position: usize,
    pub(super) direction: Vec<Rat>,
    pub(super) returned_covector_before: Vec<Rat>,
    pub(super) returned_covector_after: Vec<Rat>,
    pub(super) withdrawn_direction_return: Vec<Rat>,
    pub(super) conduct_constitution_before_sha256: String,
    pub(super) conduct_constitution_after_sha256: String,
    pub(super) ecology: NativeSituatedSpoolBundle,
    pub(super) branches: Vec<SourceNeutralCultivationBranch>,
    pub(super) predecessor_deposit_receipt: NativeThreadDepositBatchReceipt,
    pub(super) returned_deposits: Vec<SourceNeutralReturnedDeposit>,
    pub(super) granular: NativeGranularPotential,
    pub(super) relational: SourceNeutralRelationalMorphology,
    pub(super) realization: SourceNeutralExteriorRealizationMorphology,
    pub(super) acoustic: SourceNeutralAcousticMorphology,
    pub(super) optical: SourceNeutralOpticalMorphology,
    pub(super) withdrawal: NativeSituatedRadicalWithdrawal,
}
