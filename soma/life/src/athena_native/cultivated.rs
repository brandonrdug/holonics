//! Same-owner deposition of complete-exchange factors into Athena's native current.
//!
//! Cultivation is not a census beside an unchanged passage. The H2N boundary factors descend
//! once into a source-neutral [`NativeCultivationMorphology`]. Its signed candidate incidence is
//! mounted as an exact Complex-Parametron section, and the addressed current of every later native
//! occurrence crosses that resident section. Returned receiver limbs remain attached to each
//! coordinate of the resulting potential complex; no maximum, scalar score, or contact count
//! replaces the plural response.
//!
//! Ablation moves one complete deposit out of the ecology. Restoration consumes that move-only
//! object. The inverse laws are the two separately checked exact matrix sums, not two names for
//! one digest comparison.

use std::collections::BTreeSet;

use holonic_engine::{
    ExactComplexWaveCurrent,
    cuda_refine::{CudaRefineExecutor, ResidentComplexIncidence, ResidentComplexIncidenceReturn},
    exact_linear::ExactRatMatrix,
    native_spool::ReceiverInsufficiency,
    receiver_exact_compression::ReceiverId,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    AthenaNativeConsequence, AthenaNativeError, AthenaNativePassage, AthenaNativeRest,
    CompleteExchangeCultivationCover, NativeCultivationMorphology, NativeFactorDeposit,
    NativeFactorReturnedLimb, NativeSectionAddress,
};

const CULTIVATED_ATHENA_REST_SCHEMA: &str = "soma-life.cultivated-athena-native-rest.v2";
const WITHDRAWN_NATIVE_FACTOR_SCHEMA: &str = "soma-life.withdrawn-native-factor.v1";

/// One exact coordinate of the cultivated potential complex returned after resident conduct.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCultivatedPotentialCoordinate {
    pub deposit_address: String,
    pub causal_ordinal: usize,
    pub candidate_coefficient: Rat,
    pub response: ExactComplexWaveCurrent,
    pub returned_limbs: Vec<NativeFactorReturnedLimb>,
    pub radical_dimension: usize,
    pub open_exterior_dimension: usize,
}

/// The direct-sum current which cultivation adds to one predecessor section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCultivatedPotentialComplex {
    pub support_section: NativeSectionAddress,
    pub drive: ExactComplexWaveCurrent,
    pub coordinates: Vec<NativeCultivatedPotentialCoordinate>,
    pub changed_on_this_section: bool,
}

/// One continuing Athena ecology. It owns its predecessor and hot native morphology and is
/// deliberately not `Clone`.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CultivatedAthenaRest {
    schema: String,
    predecessor: AthenaNativeRest,
    morphology: NativeCultivationMorphology,
    identity_sha256: String,
}

/// The complete factor which has physically left the cultivated owner. It is deliberately not
/// `Clone`; restoration must consume this object rather than recover a hidden copy by address.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WithdrawnNativeFactor {
    schema: String,
    predecessor_wire_sha256: String,
    deposit: NativeFactorDeposit,
    identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AthenaCultivationMutation {
    pub operation: String,
    pub factor_address: String,
    pub predecessor_identity_sha256: String,
    pub successor_identity_sha256: String,
    pub forward_then_inverse_zero: bool,
    pub inverse_then_forward_zero: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AthenaCultivationWithdrawal {
    pub cultivated_identity_sha256: String,
    pub declared_predecessor_wire_sha256: String,
    pub restored_predecessor_wire_sha256: String,
    pub reverse_factor_addresses: Vec<String>,
    pub complete_reverse_word_applied: bool,
    pub forward_then_inverse_identity: bool,
    pub inverse_then_forward_identity: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CultivatedAthenaPassage {
    pub predecessor: AthenaNativePassage,
    pub potential_complex: NativeCultivatedPotentialComplex,
    pub resident_return: ResidentComplexIncidenceReturn,
    pub cultivated_rest_identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum CultivatedAthenaConsequence {
    Returned(CultivatedAthenaPassage),
    Insufficient(ReceiverInsufficiency),
}

pub struct ResidentCultivatedAthena {
    rest: CultivatedAthenaRest,
    ingress_sections: Vec<NativeSectionAddress>,
    morphology_current: ResidentComplexIncidence,
}

#[derive(Debug, Error)]
pub enum CultivatedAthenaError {
    #[error("cultivated Athena native standing is malformed")]
    Standing,
    #[error("unknown or inadmissible cultivation factor {0}")]
    Factor(String),
    #[error("cultivated Athena wire refused: {0}")]
    Wire(String),
    #[error("cultivated Athena predecessor refused: {0}")]
    Predecessor(String),
    #[error("cultivated Athena apparatus refused: {0}")]
    Apparatus(String),
}

impl CultivatedAthenaRest {
    pub fn cultivate(
        predecessor: AthenaNativeRest,
        reconstruction: CompleteExchangeCultivationCover,
    ) -> Result<Self, CultivatedAthenaError> {
        predecessor
            .validate()
            .map_err(|error| CultivatedAthenaError::Predecessor(error.to_string()))?;
        reconstruction
            .validate()
            .map_err(CultivatedAthenaError::Wire)?;
        let morphology = NativeCultivationMorphology::derive(&predecessor, &reconstruction)
            .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
        // `reconstruction` is consumed and drops here. The rest below contains only its exact
        // source-neutral native descent; source columns and exchange receipts stay exterior.
        let mut rest = Self {
            schema: CULTIVATED_ATHENA_REST_SCHEMA.to_owned(),
            predecessor,
            morphology,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, CultivatedAthenaError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, CultivatedAthenaError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| CultivatedAthenaError::Wire(error.to_string()))
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn predecessor(&self) -> &AthenaNativeRest {
        &self.predecessor
    }

    pub fn morphology(&self) -> &NativeCultivationMorphology {
        &self.morphology
    }

    pub fn mount(self) -> Result<ResidentCultivatedAthena, CultivatedAthenaError> {
        self.validate()?;
        let ingress_sections = self.predecessor.realization.ingress_sections.clone();
        if ingress_sections.is_empty() || self.morphology.deposits.is_empty() {
            return Err(CultivatedAthenaError::Standing);
        }
        let incidence = native_incidence(&self.morphology, &ingress_sections)?;
        let card = CudaRefineExecutor::new()
            .map_err(|error| CultivatedAthenaError::Apparatus(error.to_string()))?;
        let morphology_current = ResidentComplexIncidence::mount(
            card,
            "athena/native-cultivation-complex-parametron",
            0,
            self.morphology.deposits.len(),
            ingress_sections.len(),
            &incidence,
        )
        .map_err(|error| CultivatedAthenaError::Apparatus(error.to_string()))?;
        Ok(ResidentCultivatedAthena {
            rest: self,
            ingress_sections,
            morphology_current,
        })
    }

    pub fn ablate(
        mut self,
        factor_address: &str,
    ) -> Result<(Self, WithdrawnNativeFactor, AthenaCultivationMutation), CultivatedAthenaError>
    {
        self.validate()?;
        if self.morphology.deposits.len() < 2 {
            return Err(CultivatedAthenaError::Factor(factor_address.to_owned()));
        }
        let at = self
            .morphology
            .deposits
            .iter()
            .position(|deposit| deposit.address == factor_address)
            .ok_or_else(|| CultivatedAthenaError::Factor(factor_address.to_owned()))?;
        let before = self.identity_sha256.clone();
        let deposit = self.morphology.deposits.remove(at);
        let (forward_then_inverse_zero, inverse_then_forward_zero) =
            exact_inverse_checks(&deposit)?;
        if !forward_then_inverse_zero || !inverse_then_forward_zero {
            return Err(CultivatedAthenaError::Standing);
        }
        let withdrawn =
            WithdrawnNativeFactor::found(self.morphology.predecessor_wire_sha256.clone(), deposit)?;
        self.identity_sha256 = self.rederived_identity()?;
        self.validate()?;
        let mutation = AthenaCultivationMutation {
            operation: "withdraw-native-factor".to_owned(),
            factor_address: withdrawn.deposit.address.clone(),
            predecessor_identity_sha256: before,
            successor_identity_sha256: self.identity_sha256.clone(),
            forward_then_inverse_zero,
            inverse_then_forward_zero,
        };
        Ok((self, withdrawn, mutation))
    }

    pub fn restore(
        mut self,
        withdrawn: WithdrawnNativeFactor,
    ) -> Result<(Self, AthenaCultivationMutation), CultivatedAthenaError> {
        self.validate()?;
        withdrawn.validate()?;
        if withdrawn.predecessor_wire_sha256 != self.morphology.predecessor_wire_sha256
            || self.morphology.deposits.iter().any(|deposit| {
                deposit.address == withdrawn.deposit.address
                    || deposit.causal_ordinal == withdrawn.deposit.causal_ordinal
            })
        {
            return Err(CultivatedAthenaError::Factor(
                withdrawn.deposit.address.clone(),
            ));
        }
        let before = self.identity_sha256.clone();
        let factor_address = withdrawn.deposit.address.clone();
        let (forward_then_inverse_zero, inverse_then_forward_zero) =
            exact_inverse_checks(&withdrawn.deposit)?;
        if !forward_then_inverse_zero || !inverse_then_forward_zero {
            return Err(CultivatedAthenaError::Standing);
        }
        self.morphology.deposits.push(withdrawn.deposit);
        self.morphology
            .deposits
            .sort_by_key(|deposit| deposit.causal_ordinal);
        self.morphology
            .validate(&self.predecessor)
            .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
        self.identity_sha256 = self.rederived_identity()?;
        self.validate()?;
        let mutation = AthenaCultivationMutation {
            operation: "restore-native-factor".to_owned(),
            factor_address,
            predecessor_identity_sha256: before,
            successor_identity_sha256: self.identity_sha256.clone(),
            forward_then_inverse_zero,
            inverse_then_forward_zero,
        };
        Ok((self, mutation))
    }

    pub fn withdraw(
        mut self,
    ) -> Result<(AthenaNativeRest, AthenaCultivationWithdrawal), CultivatedAthenaError> {
        self.validate()?;
        let cultivated_identity_sha256 = self.identity_sha256.clone();
        let declared = self.morphology.predecessor_wire_sha256.clone();
        let mut reverse_factor_addresses = Vec::with_capacity(self.morphology.deposits.len());
        let mut forward_then_inverse_identity = true;
        let mut inverse_then_forward_identity = true;
        // `pop` enacts the reverse causal word. Each removed direct-sum coordinate is accompanied
        // by its actual negative factor, and the two compositions are checked independently.
        while let Some(deposit) = self.morphology.deposits.pop() {
            let (left, right) = exact_inverse_checks(&deposit)?;
            forward_then_inverse_identity &= left;
            inverse_then_forward_identity &= right;
            reverse_factor_addresses.push(deposit.address);
        }
        let restored = self
            .predecessor
            .wire_sha256()
            .map_err(|error| CultivatedAthenaError::Predecessor(error.to_string()))?;
        let complete_reverse_word_applied = !reverse_factor_addresses.is_empty()
            && reverse_factor_addresses
                .windows(2)
                .all(|pair| pair[0] != pair[1]);
        if declared != restored
            || !complete_reverse_word_applied
            || !forward_then_inverse_identity
            || !inverse_then_forward_identity
        {
            return Err(CultivatedAthenaError::Standing);
        }
        Ok((
            self.predecessor,
            AthenaCultivationWithdrawal {
                cultivated_identity_sha256,
                declared_predecessor_wire_sha256: declared,
                restored_predecessor_wire_sha256: restored,
                reverse_factor_addresses,
                complete_reverse_word_applied,
                forward_then_inverse_identity,
                inverse_then_forward_identity,
            },
        ))
    }

    pub fn validate(&self) -> Result<(), CultivatedAthenaError> {
        self.predecessor
            .validate()
            .map_err(|error| CultivatedAthenaError::Predecessor(error.to_string()))?;
        self.morphology
            .validate(&self.predecessor)
            .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
        if self.schema != CULTIVATED_ATHENA_REST_SCHEMA
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(CultivatedAthenaError::Standing);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, CultivatedAthenaError> {
        digest_json(&(
            CULTIVATED_ATHENA_REST_SCHEMA,
            self.predecessor
                .wire_sha256()
                .map_err(|error| CultivatedAthenaError::Predecessor(error.to_string()))?,
            &self.morphology,
        ))
    }
}

impl WithdrawnNativeFactor {
    fn found(
        predecessor_wire_sha256: String,
        deposit: NativeFactorDeposit,
    ) -> Result<Self, CultivatedAthenaError> {
        let mut withdrawn = Self {
            schema: WITHDRAWN_NATIVE_FACTOR_SCHEMA.to_owned(),
            predecessor_wire_sha256,
            deposit,
            identity_sha256: String::new(),
        };
        withdrawn.identity_sha256 = withdrawn.rederived_identity()?;
        withdrawn.validate()?;
        Ok(withdrawn)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, CultivatedAthenaError> {
        let withdrawn: Self = serde_json::from_slice(bytes)
            .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
        withdrawn.validate()?;
        Ok(withdrawn)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, CultivatedAthenaError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| CultivatedAthenaError::Wire(error.to_string()))
    }

    pub fn deposit_address(&self) -> &str {
        &self.deposit.address
    }

    fn validate(&self) -> Result<(), CultivatedAthenaError> {
        let (left, right) = exact_inverse_checks(&self.deposit)?;
        if self.schema != WITHDRAWN_NATIVE_FACTOR_SCHEMA
            || self.predecessor_wire_sha256.len() != 64
            || !left
            || !right
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(CultivatedAthenaError::Standing);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, CultivatedAthenaError> {
        digest_json(&(
            WITHDRAWN_NATIVE_FACTOR_SCHEMA,
            &self.predecessor_wire_sha256,
            &self.deposit,
        ))
    }
}

impl ResidentCultivatedAthena {
    pub fn identity(&self) -> &str {
        self.rest.identity()
    }

    pub fn conduct(
        &mut self,
        requested: &NativeSectionAddress,
        receiver: ReceiverId,
    ) -> Result<CultivatedAthenaConsequence, CultivatedAthenaError> {
        let predecessor = match self
            .rest
            .predecessor
            .conduct(requested, receiver)
            .map_err(|error| CultivatedAthenaError::Predecessor(error.to_string()))?
        {
            AthenaNativeConsequence::Returned(passage) => passage,
            AthenaNativeConsequence::Insufficient(insufficiency) => {
                return Ok(CultivatedAthenaConsequence::Insufficient(insufficiency));
            }
        };
        let drive = predecessor.section.emitting_current.clone();
        let mut front = vec![ExactComplexWaveCurrent::zero(); self.ingress_sections.len()];
        if let Some(at) = self
            .ingress_sections
            .iter()
            .position(|section| section == requested)
        {
            front[at] = drive.clone();
        }
        let resident_return = self
            .morphology_current
            .conduct(&[front])
            .map_err(|error| CultivatedAthenaError::Apparatus(error.to_string()))?;
        let responses = resident_return
            .sections
            .first()
            .ok_or(CultivatedAthenaError::Standing)?;
        if responses.len() != self.rest.morphology.deposits.len()
            || resident_return.invariant_transport_reuploaded
            || resident_return.cpu_semantic_replay_after_device
            || resident_return.binary_receiver_taken
        {
            return Err(CultivatedAthenaError::Standing);
        }
        let coordinates = self
            .rest
            .morphology
            .deposits
            .iter()
            .zip(responses)
            .map(|(deposit, response)| {
                let candidate_coefficient = deposit
                    .candidate_limbs
                    .iter()
                    .filter(|limb| limb.section == *requested)
                    .fold(Rat::from_integer(BigInt::from(0)), |sum, limb| {
                        sum + &limb.coefficient
                    });
                NativeCultivatedPotentialCoordinate {
                    deposit_address: deposit.address.clone(),
                    causal_ordinal: deposit.causal_ordinal,
                    candidate_coefficient,
                    response: response.clone(),
                    returned_limbs: deposit.returned_limbs.clone(),
                    radical_dimension: deposit.reconstruction_fibre.radical_fibre.len(),
                    open_exterior_dimension: deposit.reconstruction_fibre.open_exterior.len(),
                }
            })
            .collect::<Vec<_>>();
        let changed_on_this_section = coordinates
            .iter()
            .any(|coordinate| !coordinate.response.is_zero());
        Ok(CultivatedAthenaConsequence::Returned(
            CultivatedAthenaPassage {
                predecessor,
                potential_complex: NativeCultivatedPotentialComplex {
                    support_section: requested.clone(),
                    drive,
                    coordinates,
                    changed_on_this_section,
                },
                resident_return,
                cultivated_rest_identity_sha256: self.rest.identity_sha256.clone(),
            },
        ))
    }

    pub fn into_rest(self) -> CultivatedAthenaRest {
        self.rest
    }
}

fn native_incidence(
    morphology: &NativeCultivationMorphology,
    ingress_sections: &[NativeSectionAddress],
) -> Result<Vec<i64>, CultivatedAthenaError> {
    let ingress = ingress_sections.iter().collect::<BTreeSet<_>>();
    if ingress.len() != ingress_sections.len() {
        return Err(CultivatedAthenaError::Standing);
    }
    let mut incidence = Vec::with_capacity(
        morphology
            .deposits
            .len()
            .checked_mul(ingress_sections.len())
            .ok_or(CultivatedAthenaError::Standing)?,
    );
    for deposit in &morphology.deposits {
        for section in ingress_sections {
            let coefficient = deposit
                .candidate_limbs
                .iter()
                .filter(|limb| limb.section == *section)
                .fold(Rat::from_integer(BigInt::from(0)), |sum, limb| {
                    sum + &limb.coefficient
                });
            if coefficient.denom() != &BigInt::from(1) {
                return Err(CultivatedAthenaError::Apparatus(
                    "the native factor incidence is exact but not integral on this card chart"
                        .to_owned(),
                ));
            }
            incidence.push(
                coefficient
                    .numer()
                    .to_string()
                    .parse::<i64>()
                    .map_err(|_| {
                        CultivatedAthenaError::Apparatus(
                            "the native factor incidence exceeds the resident integer carrier"
                                .to_owned(),
                        )
                    })?,
            );
        }
    }
    if incidence.iter().all(|coefficient| *coefficient == 0) {
        return Err(CultivatedAthenaError::Standing);
    }
    Ok(incidence)
}

fn exact_inverse_checks(
    deposit: &NativeFactorDeposit,
) -> Result<(bool, bool), CultivatedAthenaError> {
    let forward_then_inverse = deposit
        .forward
        .add(&deposit.inverse)
        .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
    let inverse_then_forward = deposit
        .inverse
        .add(&deposit.forward)
        .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
    Ok((
        matrix_is_zero(&forward_then_inverse),
        matrix_is_zero(&inverse_then_forward),
    ))
}

fn matrix_is_zero(matrix: &ExactRatMatrix) -> bool {
    matrix
        .entries()
        .iter()
        .all(|entry| entry.numer() == &BigInt::from(0))
}

fn digest_json(value: &impl Serialize) -> Result<String, CultivatedAthenaError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| CultivatedAthenaError::Wire(error.to_string()))?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

impl From<AthenaNativeError> for CultivatedAthenaError {
    fn from(error: AthenaNativeError) -> Self {
        Self::Predecessor(error.to_string())
    }
}
