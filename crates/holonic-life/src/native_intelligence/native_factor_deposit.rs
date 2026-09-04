//! Source-neutral descent of returned cultivation factors into native Athena morphology.
//!
//! The H2N exchange chart is accepted only while deriving this product.  The returned morphology
//! retains addressed native candidate limbs, receiver-return limbs, exact forward and inverse
//! maps, and the complete reconstruction fibre.  Source coordinates and factor identifiers do not
//! survive as fields; the original factor address contributes only to the opaque native address.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    exact_linear::ExactRatMatrix,
    receiver_exact_compression::{Observation, ReceiverId},
    receiver_history_compression::NativeStateId,
};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    CompleteExchangeCultivationCover, ExchangeDefectBasisFace, NativeEcologyRest,
    NativeSectionAddress,
};

pub const NATIVE_CULTIVATION_MORPHOLOGY_SCHEMA: &str = "soma-life.native-cultivation-morphology.v1";
const NATIVE_FACTOR_DEPOSIT_ADDRESS_DOMAIN: &str = "soma-life.native-factor-deposit-address.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFactorCandidateLimb {
    pub section: NativeSectionAddress,
    pub entering_native: NativeStateId,
    pub emitting_native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
    pub coefficient: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFactorReturnedLimb {
    pub receiver: ReceiverId,
    pub observation: Observation,
    pub coefficient: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFactorReconstructionFibre {
    pub radical_fibre: Vec<Vec<Rat>>,
    pub open_exterior: Vec<Vec<Rat>>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeFactorDeposit {
    pub address: String,
    pub causal_ordinal: usize,
    pub candidate_limbs: Vec<NativeFactorCandidateLimb>,
    pub returned_limbs: Vec<NativeFactorReturnedLimb>,
    pub forward: ExactRatMatrix,
    pub inverse: ExactRatMatrix,
    pub reconstruction_fibre: NativeFactorReconstructionFibre,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeCultivationMorphology {
    pub schema: String,
    pub predecessor_wire_sha256: String,
    pub deposits: Vec<NativeFactorDeposit>,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeFactorDepositError {
    #[error("Athena predecessor refused: {0}")]
    Predecessor(String),
    #[error("complete exchange cover refused: {0}")]
    Cover(String),
    #[error("the factor cover is not bound to this Athena predecessor")]
    PredecessorBinding,
    #[error("native factor {0} has an inadmissible shape")]
    FactorShape(usize),
    #[error("native factor {0} does not cancel exactly")]
    FactorCancellation(usize),
    #[error("native factor {0} does not reconstruct from its typed limbs")]
    LimbReconstruction(usize),
    #[error("native factor {0} names a candidate outside the predecessor ecology")]
    CandidateOutsidePredecessor(usize),
    #[error("native cultivation morphology has a malformed identity or causal order")]
    MorphologyIdentity,
    #[error("native factor address derivation refused: {0}")]
    Address(String),
}

#[derive(Clone, Debug)]
struct NativeCandidateAtlasEntry {
    entering_native: NativeStateId,
    emitting_native: NativeStateId,
    consequences: BTreeSet<(NativeStateId, ReceiverId, Observation)>,
}

impl NativeCultivationMorphology {
    pub fn derive(
        predecessor: &NativeEcologyRest,
        cover: &CompleteExchangeCultivationCover,
    ) -> Result<Self, NativeFactorDepositError> {
        predecessor
            .validate()
            .map_err(|error| NativeFactorDepositError::Predecessor(error.to_string()))?;
        cover.validate().map_err(NativeFactorDepositError::Cover)?;
        let predecessor_wire_sha256 = predecessor
            .wire_sha256()
            .map_err(|error| NativeFactorDepositError::Predecessor(error.to_string()))?;
        if cover.predecessor_rest_wire_sha256 != predecessor_wire_sha256 {
            return Err(NativeFactorDepositError::PredecessorBinding);
        }

        let mut deposits = Vec::with_capacity(cover.cover.locals.len());
        for (causal_ordinal, local) in cover.cover.locals.iter().enumerate() {
            if local.factors.len() != 1 || local.section.support_columns.len() != 1 {
                return Err(NativeFactorDepositError::FactorShape(causal_ordinal));
            }
            let factor = &local.factors[0];
            if cover.cover.factor_order.get(causal_ordinal) != Some(&factor.address)
                || factor.support_rows != local.section.support_rows
                || factor.support_columns != local.section.support_columns
                || factor.reconstruction.rows() != local.section.support_rows.len()
                || factor.reconstruction.columns() != 1
                || factor.withdrawal.factor_address != factor.address
            {
                return Err(NativeFactorDepositError::FactorShape(causal_ordinal));
            }

            let forward = factor.reconstruction.clone();
            let inverse = factor.withdrawal.delta.clone();
            let mut candidate_limbs = Vec::new();
            let mut returned_limbs = Vec::new();
            for (local_row, ambient_row) in local.section.support_rows.iter().enumerate() {
                let coefficient = forward
                    .get(local_row, 0)
                    .map_err(|_| NativeFactorDepositError::FactorShape(causal_ordinal))?
                    .clone();
                match cover
                    .codomain_basis
                    .get(*ambient_row)
                    .ok_or(NativeFactorDepositError::FactorShape(causal_ordinal))?
                {
                    ExchangeDefectBasisFace::SealedCandidate {
                        seed_section,
                        entering_native,
                        emitting_native,
                        receiver,
                        observation,
                    } => candidate_limbs.push(NativeFactorCandidateLimb {
                        section: seed_section.clone(),
                        entering_native: *entering_native,
                        emitting_native: *emitting_native,
                        receiver: *receiver,
                        observation: *observation,
                        coefficient,
                    }),
                    ExchangeDefectBasisFace::ReturnedReceiver {
                        receiver,
                        observation,
                    } => returned_limbs.push(NativeFactorReturnedLimb {
                        receiver: *receiver,
                        observation: *observation,
                        coefficient,
                    }),
                }
            }
            let reconstruction_fibre = NativeFactorReconstructionFibre {
                radical_fibre: local.radical_fibre.clone(),
                open_exterior: local.open_exterior.clone(),
            };
            let address = derive_native_factor_address(
                &factor.address,
                causal_ordinal,
                &candidate_limbs,
                &returned_limbs,
                &forward,
                &inverse,
                &reconstruction_fibre,
            )?;
            deposits.push(NativeFactorDeposit {
                address,
                causal_ordinal,
                candidate_limbs,
                returned_limbs,
                forward,
                inverse,
                reconstruction_fibre,
            });
        }

        let morphology = Self {
            schema: NATIVE_CULTIVATION_MORPHOLOGY_SCHEMA.to_owned(),
            predecessor_wire_sha256,
            deposits,
        };
        morphology.validate(predecessor)?;
        Ok(morphology)
    }

    pub fn validate(
        &self,
        predecessor: &NativeEcologyRest,
    ) -> Result<(), NativeFactorDepositError> {
        predecessor
            .validate()
            .map_err(|error| NativeFactorDepositError::Predecessor(error.to_string()))?;
        let predecessor_wire_sha256 = predecessor
            .wire_sha256()
            .map_err(|error| NativeFactorDepositError::Predecessor(error.to_string()))?;
        if self.schema != NATIVE_CULTIVATION_MORPHOLOGY_SCHEMA
            || self.predecessor_wire_sha256 != predecessor_wire_sha256
            || self.deposits.is_empty()
            || self
                .deposits
                .windows(2)
                .any(|pair| pair[0].causal_ordinal >= pair[1].causal_ordinal)
        {
            return Err(NativeFactorDepositError::MorphologyIdentity);
        }
        let unique_addresses = self
            .deposits
            .iter()
            .map(|deposit| deposit.address.as_str())
            .collect::<BTreeSet<_>>();
        if unique_addresses.len() != self.deposits.len() {
            return Err(NativeFactorDepositError::MorphologyIdentity);
        }

        let atlas = candidate_atlas(predecessor)?;
        for deposit in &self.deposits {
            deposit.validate_against_atlas(&atlas)?;
        }
        Ok(())
    }
}

impl NativeFactorDeposit {
    pub fn validate(
        &self,
        predecessor: &NativeEcologyRest,
    ) -> Result<(), NativeFactorDepositError> {
        predecessor
            .validate()
            .map_err(|error| NativeFactorDepositError::Predecessor(error.to_string()))?;
        self.validate_against_atlas(&candidate_atlas(predecessor)?)
    }

    fn validate_against_atlas(
        &self,
        atlas: &BTreeMap<NativeSectionAddress, NativeCandidateAtlasEntry>,
    ) -> Result<(), NativeFactorDepositError> {
        self.validate_algebra()?;
        for limb in &self.candidate_limbs {
            let Some(section) = atlas.get(&limb.section) else {
                return Err(NativeFactorDepositError::CandidateOutsidePredecessor(
                    self.causal_ordinal,
                ));
            };
            if section.entering_native != limb.entering_native
                || section.emitting_native != limb.emitting_native
                || !section.consequences.contains(&(
                    limb.emitting_native,
                    limb.receiver,
                    limb.observation,
                ))
            {
                return Err(NativeFactorDepositError::CandidateOutsidePredecessor(
                    self.causal_ordinal,
                ));
            }
        }
        Ok(())
    }

    fn validate_algebra(&self) -> Result<(), NativeFactorDepositError> {
        let limb_population = self
            .candidate_limbs
            .len()
            .checked_add(self.returned_limbs.len())
            .ok_or(NativeFactorDepositError::FactorShape(self.causal_ordinal))?;
        if !is_sha256(&self.address)
            || self.candidate_limbs.is_empty()
            || self.returned_limbs.is_empty()
            || self.forward.rows() != limb_population
            || self.forward.columns() != 1
            || self.inverse.rows() != limb_population
            || self.inverse.columns() != 1
            || self
                .reconstruction_fibre
                .radical_fibre
                .iter()
                .any(|direction| direction.len() != self.forward.columns())
            || self
                .reconstruction_fibre
                .open_exterior
                .iter()
                .any(|direction| direction.len() != self.forward.rows())
        {
            return Err(NativeFactorDepositError::FactorShape(self.causal_ordinal));
        }

        let limb_coefficients = self
            .candidate_limbs
            .iter()
            .map(|limb| limb.coefficient.clone())
            .chain(
                self.returned_limbs
                    .iter()
                    .map(|limb| limb.coefficient.clone()),
            )
            .collect::<Vec<_>>();
        if self.forward.entries() != limb_coefficients.as_slice() {
            return Err(NativeFactorDepositError::LimbReconstruction(
                self.causal_ordinal,
            ));
        }

        let zero = ExactRatMatrix::zero(self.forward.rows(), self.forward.columns())
            .map_err(|_| NativeFactorDepositError::FactorShape(self.causal_ordinal))?;
        let forward_then_inverse = self
            .forward
            .add(&self.inverse)
            .map_err(|_| NativeFactorDepositError::FactorShape(self.causal_ordinal))?;
        let inverse_then_forward = self
            .inverse
            .add(&self.forward)
            .map_err(|_| NativeFactorDepositError::FactorShape(self.causal_ordinal))?;
        if forward_then_inverse != zero || inverse_then_forward != zero {
            return Err(NativeFactorDepositError::FactorCancellation(
                self.causal_ordinal,
            ));
        }
        Ok(())
    }
}

fn candidate_atlas(
    predecessor: &NativeEcologyRest,
) -> Result<BTreeMap<NativeSectionAddress, NativeCandidateAtlasEntry>, NativeFactorDepositError> {
    let mut atlas = BTreeMap::new();
    for address in &predecessor.realization.sections {
        let section = predecessor
            .ecology
            .addressed_section(&address.spool, &address.thread, address.occurrence)
            .map_err(|error| NativeFactorDepositError::Predecessor(error.to_string()))?;
        let occurrence = section.occurrence();
        let consequences = section
            .thread()
            .receiver_consequences
            .iter()
            .map(|consequence| {
                (
                    consequence.native,
                    consequence.receiver,
                    consequence.observation,
                )
            })
            .collect();
        let entry = NativeCandidateAtlasEntry {
            entering_native: occurrence.entering_native,
            emitting_native: occurrence.emitting_native,
            consequences,
        };
        if atlas.insert(address.clone(), entry).is_some() {
            return Err(NativeFactorDepositError::MorphologyIdentity);
        }
    }
    Ok(atlas)
}

fn derive_native_factor_address(
    lineage_factor_address: &str,
    causal_ordinal: usize,
    candidate_limbs: &[NativeFactorCandidateLimb],
    returned_limbs: &[NativeFactorReturnedLimb],
    forward: &ExactRatMatrix,
    inverse: &ExactRatMatrix,
    reconstruction_fibre: &NativeFactorReconstructionFibre,
) -> Result<String, NativeFactorDepositError> {
    let bytes = serde_json::to_vec(&(
        NATIVE_FACTOR_DEPOSIT_ADDRESS_DOMAIN,
        lineage_factor_address,
        causal_ordinal,
        candidate_limbs,
        returned_limbs,
        forward,
        inverse,
        reconstruction_fibre,
    ))
    .map_err(|error| NativeFactorDepositError::Address(error.to_string()))?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

fn is_sha256(address: &str) -> bool {
    address.len() == 64
        && address
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

#[cfg(test)]
mod tests {
    use holonic_engine::{
        receiver_exact_compression::{Observation, ReceiverId},
        receiver_history_compression::NativeStateId,
        EventId,
    };
    use num_bigint::BigInt;

    use super::*;

    #[test]
    fn typed_limbs_reconstruct_and_cancel_the_exact_factor() {
        let deposit = fixture(ExactRatMatrix::new(vec![vec![rat(1)], vec![rat(-1)]]).unwrap());
        assert_eq!(deposit.validate_algebra(), Ok(()));
    }

    #[test]
    fn noninverse_withdrawal_is_refused() {
        let deposit = fixture(ExactRatMatrix::new(vec![vec![rat(1)], vec![rat(1)]]).unwrap());
        assert_eq!(
            deposit.validate_algebra(),
            Err(NativeFactorDepositError::FactorCancellation(0))
        );
    }

    fn fixture(inverse: ExactRatMatrix) -> NativeFactorDeposit {
        NativeFactorDeposit {
            address: "a".repeat(64),
            causal_ordinal: 0,
            candidate_limbs: vec![NativeFactorCandidateLimb {
                section: NativeSectionAddress {
                    spool: "spool/native".to_owned(),
                    thread: "thread/native".to_owned(),
                    occurrence: EventId(1),
                },
                entering_native: NativeStateId(1),
                emitting_native: NativeStateId(2),
                receiver: ReceiverId(3),
                observation: Observation(4),
                coefficient: rat(-1),
            }],
            returned_limbs: vec![NativeFactorReturnedLimb {
                receiver: ReceiverId(3),
                observation: Observation(5),
                coefficient: rat(1),
            }],
            forward: ExactRatMatrix::new(vec![vec![rat(-1)], vec![rat(1)]]).unwrap(),
            inverse,
            reconstruction_fibre: NativeFactorReconstructionFibre {
                radical_fibre: Vec::new(),
                open_exterior: vec![vec![rat(1), rat(0)]],
            },
        }
    }

    fn rat(value: i64) -> Rat {
        Rat::from_integer(BigInt::from(value))
    }
}
