//! Causal-adjoint cultivation of the complete L1 situated-difference population.
//!
//! This owner consumes the exchange/K3 product and returns one source-neutral continuation of the
//! admitted K3 ecology.  The constitutive form has already acted through every retained reverse
//! causal word: the coefficient entering morphology is the rederived source covector, accompanied
//! by its exact operator, affine fibre, radical, obstruction, and carrying pullback.  Exchange
//! source identities, response interiors, seals, and source ordinals are unrepresentable in the
//! rested product.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::is_sha256_digest;
use holonic_engine::{
    cuda_refine::{
        CausalAdjointPulledIncidence, CoupledComplexInteraction, CudaRefineExecutor,
        ResidentCoupledComplexParametron, ResidentCoupledComplexParametronReturn,
    },
    native_spool::{
        NativeConstitutiveResponse, NativeDepositFibreDelta, NativeExactReconstructionFibre,
        NativeIncidenceTerm, NativeMixedConstitutiveFamily, NativeParametronCell,
        NativePullbackOccurrence, NativeReceiverConsequence, NativeSituatedRadicalWithdrawal,
        NativeSituatedSpoolBundle, NativeSituatedSpoolPredecessor, NativeSituatedThreadWithdrawal,
        NativeThread, NativeThreadDeposit, NativeThreadDepositBatchReceipt,
        NativeThreadDepositReceipt, NATIVE_THREAD_DEPOSIT_SCHEMA, NATIVE_THREAD_SCHEMA,
    },
    receiver_history_compression::NativeStateId,
    ExactComplexWaveCurrent, OccurrencePort,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::athena_native::exchange_situated_product::{
    ExchangeSituatedProduct, K3PullbackBranch, MixedConstitutiveInteractionFamily,
    NativeStateExchangeCover,
};
use crate::athena_native::returned_difference_deposit::{
    derive_returned_difference_deposit_from_history, ReturnedDifferenceStaging,
};
use crate::athena_native::situated_difference::SituatedDifferenceSection;
use crate::athena_native::types::{NativeEcologyRest, ReceiverHistoryRealizationPassage};

pub const SITUATED_CULTIVATED_ATHENA_REST_SCHEMA: &str =
    "soma-life.situated-cultivated-athena-rest.v1";
pub const LABORATORY_CULTIVATED_ATHENA_REST_SCHEMA: &str =
    "soma-life.laboratory-cultivated-athena-rest.v1";

/// One compact branch-family deposition.  Population is measured from the complete local family;
/// it is not an authored width.  The returned covector remains exact beside its integer apparatus
/// face, so the hot coefficient cannot silently become an unexplained constant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedCultivationBranch {
    pub branch: usize,
    pub k3_pullback_address: String,
    pub thread_address: String,
    pub returned_source_covector: Vec<Rat>,
    pub local_population: usize,
    pub exact_fibre_population: usize,
    pub return_operator_identity_sha256: String,
    pub occurrence_population_identity_sha256: String,
}

/// One continuing situated Athena ecology.  It does not wrap an unchanged predecessor: the K3
/// bundle has moved into `ecology`, where the deposited threads and every incident exact relation
/// are part of the same singular owner.  `realization` is only its recomputed addressed view.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedCultivatedAthenaRest {
    schema: String,
    predecessor_wire_sha256: String,
    ecology: NativeSituatedSpoolBundle,
    realization: ReceiverHistoryRealizationPassage,
    branches: Vec<SituatedCultivationBranch>,
    deposit_receipt: NativeThreadDepositBatchReceipt,
    identity_sha256: String,
}

/// One complete returned passage deposited into the standing four-cycle chart.
///
/// `winding_coefficients` are the four dual-probe readings of one simultaneous section.  Their
/// vector order is the standing receiver chart and never a chronology.  The native receipt owns
/// one deposited passage whose four constitutive contacts join it to the existing cycle body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedReturnedDifferenceDeposit {
    pub difference_identity_sha256: String,
    pub thread_address: String,
    pub winding_coefficients: Vec<Rat>,
    pub return_operator_identity_sha256: String,
    pub occurrence_population_identity_sha256: String,
    pub native_receipt: NativeThreadDepositReceipt,
}

/// The L5 type-state successor.  It owns the moved L2 ecology after the complete returned passage
/// has entered that ecology; it is not a wrapper around an independently conductible predecessor.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LaboratoryCultivatedAthenaRest {
    schema: String,
    predecessor_rest_identity_sha256: String,
    predecessor_wire_sha256: String,
    ecology: NativeSituatedSpoolBundle,
    realization: ReceiverHistoryRealizationPassage,
    branches: Vec<SituatedCultivationBranch>,
    predecessor_deposit_receipt: NativeThreadDepositBatchReceipt,
    returned_deposit: SituatedReturnedDifferenceDeposit,
    identity_sha256: String,
}

pub const RECURRENT_LABORATORY_CULTIVATED_ATHENA_REST_SCHEMA: &str =
    "soma-life.recurrent-laboratory-cultivated-athena-rest.v1";

/// The same native ecology after more than one genuinely returned difference has entered.
///
/// Every return is an addressed native thread in `ecology`; the vector is exact inverse and
/// reconstruction testimony, not an independently consulted history store.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecurrentLaboratoryCultivatedAthenaRest {
    schema: String,
    rest_identity_history: Vec<String>,
    origin_predecessor_rest_identity_sha256: String,
    predecessor_wire_sha256: String,
    ecology: NativeSituatedSpoolBundle,
    realization: ReceiverHistoryRealizationPassage,
    branches: Vec<SituatedCultivationBranch>,
    predecessor_deposit_receipt: NativeThreadDepositBatchReceipt,
    returned_deposits: Vec<SituatedReturnedDifferenceDeposit>,
    identity_sha256: String,
}

/// Move-owned inverse of the newest return in a recurrent laboratory body.
#[derive(Debug, PartialEq, Eq)]
pub struct RecurrentSituatedDifferenceWithdrawal {
    original_rest_identity_sha256: String,
    predecessor_rest_identity_sha256: String,
    returned_deposit: SituatedReturnedDifferenceDeposit,
    native_deposit: NativeThreadDeposit,
}

#[derive(Debug, PartialEq, Eq)]
pub enum RecurrentLaboratoryPredecessor {
    First(LaboratoryCultivatedAthenaRest),
    Recurrent(RecurrentLaboratoryCultivatedAthenaRest),
}

impl RecurrentLaboratoryPredecessor {
    pub fn identity(&self) -> &str {
        match self {
            Self::First(rest) => rest.identity(),
            Self::Recurrent(rest) => rest.identity(),
        }
    }
}

/// Move-owned inverse of the L5 returned passage.  Restoration consumes the exact native deposit;
/// no copy of cultivated morphology survives beside the predecessor.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedReturnedDifferenceWithdrawal {
    original_rest_identity_sha256: String,
    predecessor_rest_identity_sha256: String,
    returned_deposit: SituatedReturnedDifferenceDeposit,
    native_deposit: NativeThreadDeposit,
}

/// One mounted hot body for the L5 rest.  Base winding current and returned morphology share the
/// same resident contraction and are never sequenced as host-side semantic phases.
pub struct ResidentLaboratoryCultivatedAthena {
    rest: LaboratoryCultivatedAthenaRest,
    factors: Vec<(String, Vec<String>)>,
    expected: Vec<ExactComplexWaveCurrent>,
    resident: ResidentCoupledComplexParametron,
}

/// Recoverable removal of one branch factor and every exact relation incident to it.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedCultivationWithdrawal {
    original_rest_identity_sha256: String,
    branch: SituatedCultivationBranch,
    native: NativeSituatedThreadWithdrawal,
}

/// Move-owned removal of one thread inherited from the admitted K3/Soulkiller spool.
///
/// A cultivated branch cannot enter this passage: branch withdrawals have their own typed inverse.
/// This owner exposes the previously buried inherited-spool ablation without making Soulkiller or
/// its exterior witness reachable from Athena.  The complete native thread, every incident
/// constitutive relation, and every reconstruction-fibre member travel in `native`.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedInheritedThreadWithdrawal {
    original_rest_identity_sha256: String,
    ablated_rest_identity_sha256: String,
    spool_address: String,
    thread_address: String,
    native: NativeSituatedThreadWithdrawal,
}

/// A moved receiver-radical direction.  It changes the complete reconstruction body while the
/// declared causal-adjoint consequence remains invariant because the return operator annihilates
/// the direction.  This is an exact support-disjoint ablation, not a fabricated uncoupled branch.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedRadicalWithdrawal {
    original_rest_identity_sha256: String,
    native: NativeSituatedRadicalWithdrawal,
}

/// Complete reverse return from the situated rest to its exact admitted K3 predecessor.
#[derive(Debug, PartialEq, Eq)]
pub struct CompleteSituatedCultivationWithdrawal {
    pub restored_predecessor: NativeEcologyRest,
    pub withdrawn_deposits: Vec<NativeThreadDeposit>,
    pub predecessor_wire_sha256: String,
    pub cultivated_identity_sha256: String,
    pub complete_reverse_word_applied: bool,
}

/// One addressed factor of the returned coupled current.  Primary factors retain one deposited
/// thread; mixed factors retain both incident thread addresses.  The distinction is structural
/// testimony derived from the ecology, not a semantic route.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SituatedCultivatedConductedFactor {
    pub address: String,
    pub incident_threads: Vec<String>,
    pub current: ExactComplexWaveCurrent,
}

/// Exact native return from one mounted coupled Complex-Parametron body.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SituatedCultivatedConductReturn {
    pub rest_identity_sha256: String,
    pub factors: Vec<SituatedCultivatedConductedFactor>,
    pub apparatus: ResidentCoupledComplexParametronReturn,
}

/// The singular rest and its one resident hot contraction.  Source exchange material is not an
/// input to this type and cannot be reopened through it.
pub struct ResidentSituatedCultivatedAthena {
    rest: SituatedCultivatedAthenaRest,
    factors: Vec<(String, Vec<String>)>,
    expected: Vec<ExactComplexWaveCurrent>,
    resident: ResidentCoupledComplexParametron,
}

#[derive(Debug, Error)]
pub enum SituatedCultivationError {
    #[error("the admitted K3 predecessor refused cultivation: {0}")]
    Predecessor(String),
    #[error("the L1 situated product refused cultivation: {0}")]
    Product(String),
    #[error("the source-neutral morphology descent is malformed: {0}")]
    Descent(String),
    #[error("the singular situated ecology refused the returned morphology: {0}")]
    Ecology(String),
    #[error("the resident coupled Complex-Parametron apparatus refused the passage: {0}")]
    Apparatus(String),
    #[error("the situated Athena rest wire is malformed: {0}")]
    Wire(String),
}

mod cultivation;
mod deposit;
mod resident;

pub(crate) use resident::{derive_recurrent_resident_coupling, derive_resident_coupling};
