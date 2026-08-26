use std::collections::BTreeSet;

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::family_types::{
    FamilyCultivatedAthenaRest, FamilyCultivationDecoder, FamilyCultivationError,
    FamilyCultivationOccurrence, FamilyCultivationReconstruction, FamilyCultivationStanding,
    FamilyInquiry, FamilyWithdrawalReceipt, FamilyWorldReturn, FixedSectionPlate,
};
use super::laboratory_types::{LaboratoryAthenaRest, LaboratoryChronology};
use super::types::{ProductionInquiryPresentation, ProductionReceiver};
use super::wire::{decode_components, digest, encode_components, hex};

pub const FAMILY_CULTIVATION_STANDING_SCHEMA: &str = "holonics.l1.family-cultivation-standing.v1";
pub const FAMILY_CULTIVATION_DECODER_SCHEMA: &str = "holonics.l1.family-cultivation-decoder.v1";
pub const FAMILY_CULTIVATION_FIBRES_SCHEMA: &str = "holonics.l1.family-cultivation-fibres.v1";
pub const FAMILY_INQUIRY_SCHEMA: &str = "holonics.l1.family-inquiry.v1";

const STANDING_MAGIC: &[u8; 8] = b"HLF1S001";
const DECODER_MAGIC: &[u8; 8] = b"HLF1D001";
const FIBRES_MAGIC: &[u8; 8] = b"HLF1F001";

fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

impl FixedSectionPlate {
    pub fn validate(&self) -> Result<(), FamilyCultivationError> {
        let dimension = self.dimension as usize;
        let rows = self.constraint_rows as usize;
        let square = dimension
            .checked_mul(dimension)
            .ok_or(FamilyCultivationError::Plate)?;
        if self.occurrence.is_empty()
            || self.returned_occurrence.is_empty()
            || dimension == 0
            || rows == 0
            || rows > dimension
            || self.modulus < 0
            || self.modulus == 1
            || self.action.len() != square
            || self.constraints.len() != square
            || self.action_difference_factor.len() != dimension * rows
            || self.receiver_metric.len() != square
            || self.support_coordinates.is_empty()
            || self
                .support_coordinates
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
        {
            return Err(FamilyCultivationError::Plate);
        }
        for row in 0..dimension {
            for column in 0..dimension {
                let expected_metric = i64::from(row == column);
                if self.receiver_metric[row * dimension + column] != expected_metric {
                    return Err(FamilyCultivationError::Plate);
                }
                let mut factored = 0_i64;
                for inner in 0..rows {
                    factored = factored
                        .checked_add(
                            self.action_difference_factor[row * rows + inner]
                                .checked_mul(self.constraints[inner * dimension + column])
                                .ok_or(FamilyCultivationError::Plate)?,
                        )
                        .ok_or(FamilyCultivationError::Plate)?;
                }
                let action_difference = self.action[row * dimension + column]
                    .checked_sub(i64::from(row == column))
                    .ok_or(FamilyCultivationError::Plate)?;
                let equal = if self.modulus == 0 {
                    action_difference == factored
                } else {
                    action_difference.rem_euclid(self.modulus) == factored.rem_euclid(self.modulus)
                };
                if !equal {
                    return Err(FamilyCultivationError::Plate);
                }
            }
        }
        Ok(())
    }
}

impl FamilyInquiry {
    pub fn found(
        predecessor_rest_sha256: String,
        presentation: ProductionInquiryPresentation,
        receiver_family: Vec<ProductionReceiver>,
        sections: Vec<Vec<i64>>,
        prior_history_occurrences: Vec<String>,
    ) -> Result<Self, FamilyCultivationError> {
        let mut inquiry = Self {
            schema: FAMILY_INQUIRY_SCHEMA.to_owned(),
            occurrence: String::new(),
            predecessor_rest_sha256,
            presentation,
            receiver_family,
            sections,
            prior_history_occurrences,
        };
        inquiry.occurrence = format!("l1/inquiry/{}", inquiry.body_sha256()?);
        inquiry.validate_shape()?;
        Ok(inquiry)
    }

    fn body_sha256(&self) -> Result<String, FamilyCultivationError> {
        #[derive(Serialize)]
        struct Body<'a> {
            schema: &'a str,
            predecessor_rest_sha256: &'a str,
            presentation: &'a ProductionInquiryPresentation,
            receiver_family: &'a [ProductionReceiver],
            sections: &'a [Vec<i64>],
            prior_history_occurrences: &'a [String],
        }
        serde_json::to_vec(&Body {
            schema: &self.schema,
            predecessor_rest_sha256: &self.predecessor_rest_sha256,
            presentation: &self.presentation,
            receiver_family: &self.receiver_family,
            sections: &self.sections,
            prior_history_occurrences: &self.prior_history_occurrences,
        })
        .map(|bytes| digest(&bytes))
        .map_err(|error| FamilyCultivationError::Wire(error.to_string()))
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, FamilyCultivationError> {
        self.validate_shape()?;
        serde_json::to_vec(self).map_err(|error| FamilyCultivationError::Wire(error.to_string()))
    }

    fn validate_shape(&self) -> Result<(), FamilyCultivationError> {
        let mut receivers = self.receiver_family.clone();
        receivers.sort_by_key(|receiver| *receiver as u8);
        receivers.dedup();
        if self.schema != FAMILY_INQUIRY_SCHEMA
            || self.occurrence != format!("l1/inquiry/{}", self.body_sha256()?)
            || !is_digest(&self.predecessor_rest_sha256)
            || self.presentation.natural_language.is_empty()
            || self.presentation.notation.is_empty()
            || !is_digest(&self.presentation.vector_face_sha256)
            || !is_digest(&self.presentation.raster_face_sha256)
            || receivers.len() != 5
            || self.sections.len() < 2
            || self.sections.iter().any(Vec::is_empty)
            || self.prior_history_occurrences.is_empty()
        {
            return Err(FamilyCultivationError::Inquiry);
        }
        Ok(())
    }
}

impl FamilyCultivatedAthenaRest {
    pub fn found(
        predecessor: LaboratoryAthenaRest,
        chronology: LaboratoryChronology,
        genesis_decision_occurrence: String,
    ) -> Result<Self, FamilyCultivationError> {
        predecessor
            .validate()
            .map_err(|error| FamilyCultivationError::Predecessor(error.to_string()))?;
        chronology
            .validate()
            .map_err(|_| FamilyCultivationError::Chronology)?;
        if !predecessor.committed() || genesis_decision_occurrence.is_empty() {
            return Err(FamilyCultivationError::Decision);
        }
        let l0_predecessor_sha256 = predecessor
            .canonical_identity()
            .map_err(|error| FamilyCultivationError::Predecessor(error.to_string()))?;
        let mut developmental_occurrence_sha256 = chronology
            .occurrences
            .iter()
            .flat_map(|commit| {
                std::iter::once(&commit.occurrence)
                    .chain(commit.changes.iter().map(|change| &change.occurrence))
            })
            .map(|occurrence| digest(occurrence.as_bytes()))
            .collect::<Vec<_>>();
        developmental_occurrence_sha256.sort();
        developmental_occurrence_sha256.dedup();
        let rest = Self {
            predecessor,
            chronology,
            standing: FamilyCultivationStanding {
                schema: FAMILY_CULTIVATION_STANDING_SCHEMA.to_owned(),
                l0_predecessor_sha256,
                genesis_decision_occurrence,
                cultivations: Vec::new(),
                open_exterior: vec![
                    "fixed-section families not yet returned by an exterior receiver remain open"
                        .to_owned(),
                    "overlapping supports remain obstructed until a higher-cell receipt returns"
                        .to_owned(),
                    "new successor histories may reopen every present family condensation"
                        .to_owned(),
                ],
            },
            decoder: FamilyCultivationDecoder {
                schema: FAMILY_CULTIVATION_DECODER_SCHEMA.to_owned(),
                expanded_transport_word: vec![0, 1, 2],
                condensed_transport_word: vec![3],
                obstruction_transport_word: vec![4],
                composed_transport_word: vec![5],
            },
            reconstruction: FamilyCultivationReconstruction {
                schema: FAMILY_CULTIVATION_FIBRES_SCHEMA.to_owned(),
                developmental_occurrence_sha256,
                complete_component_fibres: vec![
                    "l0-complete-reconstruction-boundary".to_owned(),
                    "fixed-section-action-interior".to_owned(),
                    "constraint-kernel-fibre".to_owned(),
                    "action-difference-factorization".to_owned(),
                    "expanded-condensed-obstructed-route-fibre".to_owned(),
                    "local-family-ablation-fibre".to_owned(),
                ],
                shortest_separating_receivers: vec![
                    "constraint-residual-reopens-the-expanded-action".to_owned(),
                    "equal-total-different-oriented-face".to_owned(),
                    "equal-present-section-different-successor-action".to_owned(),
                ],
                unresolved_families: vec![
                    "overlapping returned supports".to_owned(),
                    "nonlinear fixed varieties".to_owned(),
                    "receivers outside the frozen L1 chronology".to_owned(),
                ],
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(
        standing: &[u8],
        decoder: &[u8],
        fibres: &[u8],
    ) -> Result<Self, FamilyCultivationError> {
        let standing = decode_components(STANDING_MAGIC, standing, 3)
            .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?;
        let decoder = decode_components(DECODER_MAGIC, decoder, 2)
            .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?;
        let fibres = decode_components(FIBRES_MAGIC, fibres, 2)
            .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?;
        let rest = Self {
            predecessor: LaboratoryAthenaRest::read(&standing[0], &decoder[0], &fibres[0])
                .map_err(|error| FamilyCultivationError::Predecessor(error.to_string()))?,
            chronology: serde_json::from_slice(&standing[1])
                .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
            standing: serde_json::from_slice(&standing[2])
                .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
            decoder: serde_json::from_slice(&decoder[1])
                .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
            reconstruction: serde_json::from_slice(&fibres[1])
                .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, FamilyCultivationError> {
        self.validate()?;
        encode_components(
            STANDING_MAGIC,
            &[
                self.predecessor
                    .standing_bytes()
                    .map_err(|error| FamilyCultivationError::Predecessor(error.to_string()))?,
                serde_json::to_vec(&self.chronology)
                    .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
                serde_json::to_vec(&self.standing)
                    .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
            ],
        )
        .map_err(|error| FamilyCultivationError::Wire(error.to_string()))
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, FamilyCultivationError> {
        self.validate()?;
        encode_components(
            DECODER_MAGIC,
            &[
                self.predecessor
                    .decoder_bytes()
                    .map_err(|error| FamilyCultivationError::Predecessor(error.to_string()))?,
                serde_json::to_vec(&self.decoder)
                    .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
            ],
        )
        .map_err(|error| FamilyCultivationError::Wire(error.to_string()))
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, FamilyCultivationError> {
        self.validate()?;
        encode_components(
            FIBRES_MAGIC,
            &[
                self.predecessor
                    .fibre_bytes()
                    .map_err(|error| FamilyCultivationError::Predecessor(error.to_string()))?,
                serde_json::to_vec(&self.reconstruction)
                    .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?,
            ],
        )
        .map_err(|error| FamilyCultivationError::Wire(error.to_string()))
    }

    pub fn canonical_identity(&self) -> Result<String, FamilyCultivationError> {
        self.validate()?;
        self.identity_at(self.standing.cultivations.len())
    }

    fn identity_at(&self, cultivation_prefix: usize) -> Result<String, FamilyCultivationError> {
        if cultivation_prefix > self.standing.cultivations.len() {
            return Err(FamilyCultivationError::Decision);
        }
        #[derive(Serialize)]
        struct StandingPrefix<'a> {
            schema: &'a str,
            l0_predecessor_sha256: &'a str,
            genesis_decision_occurrence: &'a str,
            cultivations: &'a [FamilyCultivationOccurrence],
            open_exterior: &'a [String],
        }
        let standing = serde_json::to_vec(&StandingPrefix {
            schema: &self.standing.schema,
            l0_predecessor_sha256: &self.standing.l0_predecessor_sha256,
            genesis_decision_occurrence: &self.standing.genesis_decision_occurrence,
            cultivations: &self.standing.cultivations[..cultivation_prefix],
            open_exterior: &self.standing.open_exterior,
        })
        .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?;
        let chronology = serde_json::to_vec(&self.chronology)
            .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?;
        let decoder = serde_json::to_vec(&self.decoder)
            .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?;
        let reconstruction = serde_json::to_vec(&self.reconstruction)
            .map_err(|error| FamilyCultivationError::Wire(error.to_string()))?;
        let mut hasher = Sha256::new();
        for bytes in [
            self.standing.l0_predecessor_sha256.as_bytes(),
            chronology.as_slice(),
            standing.as_slice(),
            decoder.as_slice(),
            reconstruction.as_slice(),
        ] {
            hasher.update((bytes.len() as u64).to_le_bytes());
            hasher.update(bytes);
        }
        Ok(hex(hasher.finalize()))
    }

    pub fn chronology(&self) -> &LaboratoryChronology {
        &self.chronology
    }

    pub fn predecessor_is_committed(&self) -> bool {
        self.predecessor.committed()
    }

    pub fn cultivations(&self) -> &[FamilyCultivationOccurrence] {
        &self.standing.cultivations
    }

    pub fn composed_transport_word(&self) -> &[u32] {
        &self.decoder.composed_transport_word
    }

    pub fn complete_component_fibres(&self) -> &[String] {
        &self.reconstruction.complete_component_fibres
    }

    pub fn unresolved_families(&self) -> &[String] {
        &self.reconstruction.unresolved_families
    }

    pub fn shortest_separating_receivers(&self) -> &[String] {
        &self.reconstruction.shortest_separating_receivers
    }

    pub fn open_exterior(&self) -> &[String] {
        &self.standing.open_exterior
    }

    pub fn commit_return(
        mut self,
        world_return: FamilyWorldReturn,
        plate: FixedSectionPlate,
        decision_occurrence: String,
    ) -> Result<Self, FamilyCultivationError> {
        self.validate()?;
        plate.validate()?;
        if decision_occurrence.is_empty()
            || world_return.occurrence.is_empty()
            || world_return.occurrence != plate.returned_occurrence
            || !world_return.accepted
            || world_return.lean_exit_status != 0
            || world_return.exact_difference_octets == 0
            || !is_digest(&world_return.emitted_product_sha256)
            || !is_digest(&world_return.returned_lean_sha256)
            || self
                .standing
                .cultivations
                .iter()
                .any(|cultivation| cultivation.plate.occurrence == plate.occurrence)
        {
            return Err(FamilyCultivationError::WorldReturn);
        }
        let predecessor_identity = self.canonical_identity()?;
        self.standing
            .cultivations
            .push(FamilyCultivationOccurrence {
                decision_occurrence,
                predecessor_identity,
                world_return,
                plate,
            });
        self.validate()?;
        Ok(self)
    }

    pub fn admit_inquiry(&self, inquiry: &FamilyInquiry) -> Result<(), FamilyCultivationError> {
        inquiry.validate_shape()?;
        if inquiry.predecessor_rest_sha256 != self.canonical_identity()?
            || inquiry.sections.len() != self.standing.cultivations.len()
            || inquiry
                .sections
                .iter()
                .zip(&self.standing.cultivations)
                .any(|(section, cultivation)| section.len() != cultivation.plate.dimension as usize)
            || self
                .reconstruction
                .developmental_occurrence_sha256
                .binary_search(&digest(inquiry.occurrence.as_bytes()))
                .is_ok()
        {
            return Err(FamilyCultivationError::Inquiry);
        }
        Ok(())
    }

    pub fn sections_wire(&self, inquiry: &FamilyInquiry) -> Vec<i64> {
        inquiry.sections.iter().flatten().copied().collect()
    }

    pub fn actions_wire(&self) -> Vec<i64> {
        self.standing
            .cultivations
            .iter()
            .flat_map(|cultivation| cultivation.plate.action.iter().copied())
            .collect()
    }

    pub fn constraints_wire(&self) -> Vec<i64> {
        self.standing
            .cultivations
            .iter()
            .flat_map(|cultivation| cultivation.plate.constraints.iter().copied())
            .collect()
    }

    pub fn constraint_rows_wire(&self) -> Vec<u32> {
        self.standing
            .cultivations
            .iter()
            .map(|cultivation| cultivation.plate.constraint_rows)
            .collect()
    }

    pub fn moduli_wire(&self) -> Vec<i64> {
        self.standing
            .cultivations
            .iter()
            .map(|cultivation| cultivation.plate.modulus)
            .collect()
    }

    pub fn cultivation_flags(&self) -> Vec<u32> {
        vec![1; self.standing.cultivations.len()]
    }

    pub fn supports_are_independent(&self) -> bool {
        let mut support = BTreeSet::new();
        self.standing.cultivations.iter().all(|cultivation| {
            cultivation
                .plate
                .support_coordinates
                .iter()
                .all(|coordinate| support.insert(*coordinate))
        })
    }

    pub fn composed_route_reachable(&self) -> bool {
        self.standing.cultivations.len() >= 2 && self.supports_are_independent()
    }

    pub fn withdraw_last(
        mut self,
    ) -> Result<(Self, FamilyWithdrawalReceipt), FamilyCultivationError> {
        self.validate()?;
        let committed_identity = self.canonical_identity()?;
        let cultivation = self
            .standing
            .cultivations
            .pop()
            .ok_or(FamilyCultivationError::Decision)?;
        self.validate()?;
        let restored_identity = self.canonical_identity()?;
        let receipt = FamilyWithdrawalReceipt {
            withdrawn_plate_occurrence: cultivation.plate.occurrence,
            committed_identity,
            predecessor_identity: cultivation.predecessor_identity.clone(),
            restored_identity: restored_identity.clone(),
            exact_immediate_predecessor_restored: restored_identity
                == cultivation.predecessor_identity,
        };
        if !receipt.exact_immediate_predecessor_restored {
            return Err(FamilyCultivationError::Withdrawal);
        }
        Ok((self, receipt))
    }

    pub fn validate(&self) -> Result<(), FamilyCultivationError> {
        self.chronology
            .validate()
            .map_err(|_| FamilyCultivationError::Chronology)?;
        if !self.predecessor.committed()
            || self.standing.schema != FAMILY_CULTIVATION_STANDING_SCHEMA
            || !is_digest(&self.standing.l0_predecessor_sha256)
            || self.standing.genesis_decision_occurrence.is_empty()
            || self.standing.open_exterior.is_empty()
            || self.decoder.schema != FAMILY_CULTIVATION_DECODER_SCHEMA
            || self.decoder.expanded_transport_word.len()
                <= self.decoder.condensed_transport_word.len()
            || self.decoder.condensed_transport_word.is_empty()
            || self.decoder.obstruction_transport_word.is_empty()
            || self.decoder.composed_transport_word.is_empty()
            || self.reconstruction.schema != FAMILY_CULTIVATION_FIBRES_SCHEMA
            || self
                .reconstruction
                .developmental_occurrence_sha256
                .is_empty()
            || self
                .reconstruction
                .developmental_occurrence_sha256
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || self.reconstruction.complete_component_fibres.len() < 6
            || self.reconstruction.shortest_separating_receivers.is_empty()
            || self.reconstruction.unresolved_families.is_empty()
        {
            return Err(FamilyCultivationError::Chronology);
        }
        let mut plate_occurrences = BTreeSet::new();
        for (at, cultivation) in self.standing.cultivations.iter().enumerate() {
            cultivation.plate.validate()?;
            if cultivation.decision_occurrence.is_empty()
                || !is_digest(&cultivation.predecessor_identity)
                || cultivation.predecessor_identity != self.identity_at(at)?
                || cultivation.world_return.occurrence != cultivation.plate.returned_occurrence
                || !cultivation.world_return.accepted
                || cultivation.world_return.lean_exit_status != 0
                || cultivation.world_return.exact_difference_octets == 0
                || !is_digest(&cultivation.world_return.emitted_product_sha256)
                || !is_digest(&cultivation.world_return.returned_lean_sha256)
                || !plate_occurrences.insert(&cultivation.plate.occurrence)
            {
                return Err(FamilyCultivationError::Decision);
            }
        }
        Ok(())
    }
}
