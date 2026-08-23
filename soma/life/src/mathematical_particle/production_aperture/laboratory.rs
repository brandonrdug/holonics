use std::collections::BTreeSet;

use holonic_engine::{
    generator_native_rest::GeneratorNativeRest,
    receiver_history_cultivation::CultivatedReceiverHistoryRest,
};
use serde::Serialize;
use sha2::{Digest, Sha256};

use super::laboratory_types::{
    LaboratoryAthenaError, LaboratoryAthenaRest, LaboratoryChronology,
    LaboratoryComponentIdentity, LaboratoryDecision, LaboratoryInquiry,
    LaboratoryMorphologyDelta, LaboratoryPartitionKind,
    LaboratoryReconstructionBoundary, LaboratoryRouteDecoder, LaboratoryStandingJunction,
    LaboratoryWithdrawalReceipt, LaboratoryWorldReturn,
};
use super::types::{ProductionAthenaRest, ProductionInquiryPresentation, ProductionReceiver};
use super::wire::{decode_components, digest, encode_components, hex};

pub const LABORATORY_CHRONOLOGY_SCHEMA: &str = "holonics.l0.laboratory-chronology.v1";
pub const LABORATORY_INQUIRY_SCHEMA: &str = "holonics.l0.laboratory-inquiry.v1";
pub const LABORATORY_JUNCTION_SCHEMA: &str = "holonics.l0.laboratory-junction.v1";
pub const LABORATORY_DECODER_SCHEMA: &str = "holonics.l0.laboratory-route-decoder.v1";
pub const LABORATORY_FIBRES_SCHEMA: &str = "holonics.l0.laboratory-reconstruction-boundary.v1";

const STANDING_MAGIC: &[u8; 8] = b"HLA0S001";
const DECODER_MAGIC: &[u8; 8] = b"HLA0D001";
const FIBRES_MAGIC: &[u8; 8] = b"HLA0F001";

fn is_hex(value: &str, extent: usize) -> bool {
    value.len() == extent && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn component(role: &str, bytes: &[u8]) -> LaboratoryComponentIdentity {
    LaboratoryComponentIdentity {
        role: role.to_owned(),
        sha256: digest(bytes),
        octets: bytes.len() as u64,
    }
}

fn identities(
    production: &ProductionAthenaRest,
    native: &GeneratorNativeRest,
    cultivated: &CultivatedReceiverHistoryRest,
    chronology: &LaboratoryChronology,
) -> Result<Vec<LaboratoryComponentIdentity>, LaboratoryAthenaError> {
    let chronology_bytes = serde_json::to_vec(chronology)
        .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?;
    Ok(vec![
        component(
            "r6-production-standing",
            &production
                .standing_bytes()
                .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?,
        ),
        component(
            "r6-production-decoder",
            &production
                .decoder_bytes()
                .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?,
        ),
        component(
            "r6-production-fibres",
            &production
                .fibre_bytes()
                .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?,
        ),
        component(
            "m3-generator-native-rest",
            &native
                .canonical_bytes()
                .map_err(|error| LaboratoryAthenaError::Native(error.to_string()))?,
        ),
        component(
            "m4-cultivated-history-rest",
            &cultivated
                .canonical_bytes()
                .map_err(|error| LaboratoryAthenaError::Cultivated(error.to_string()))?,
        ),
        component("laboratory-chronology", &chronology_bytes),
    ])
}

impl LaboratoryChronology {
    pub fn validate(&self) -> Result<(), LaboratoryAthenaError> {
        if self.schema != LABORATORY_CHRONOLOGY_SCHEMA
            || !is_hex(&self.predecessor_commit, 40)
            || !is_hex(&self.prefix_commit, 40)
            || !is_hex(&self.prefix_tree, 40)
            || self.occurrences.is_empty()
            || self.incrementally_mounted_octets == 0
            || self.whole_repository_semantic_materializations != 0
            || self.occurrences.first().map(|commit| commit.parent.as_str())
                != Some(self.predecessor_commit.as_str())
            || self.occurrences.last().map(|commit| commit.commit.as_str())
                != Some(self.prefix_commit.as_str())
            || self.occurrences.last().map(|commit| commit.tree.as_str())
                != Some(self.prefix_tree.as_str())
        {
            return Err(LaboratoryAthenaError::Chronology);
        }
        let mut previous = self.predecessor_commit.as_str();
        let mut addresses = BTreeSet::new();
        let mut mounted = 0_u64;
        for occurrence in &self.occurrences {
            if !is_hex(&occurrence.commit, 40)
                || !is_hex(&occurrence.parent, 40)
                || !is_hex(&occurrence.tree, 40)
                || occurrence.parent != previous
                || occurrence.occurrence != format!("git/commit/{}", occurrence.commit)
                || occurrence.summary.is_empty()
                || occurrence.changes.is_empty()
                || !addresses.insert(occurrence.occurrence.clone())
            {
                return Err(LaboratoryAthenaError::Chronology);
            }
            for change in &occurrence.changes {
                if change.occurrence.is_empty()
                    || change.status.is_empty()
                    || change.lineage_path.is_empty()
                    || !is_hex(&change.blob_sha256, 64)
                    || !addresses.insert(change.occurrence.clone())
                {
                    return Err(LaboratoryAthenaError::Chronology);
                }
                mounted = mounted
                    .checked_add(change.octets)
                    .ok_or(LaboratoryAthenaError::Chronology)?;
            }
            previous = &occurrence.commit;
        }
        if mounted != self.incrementally_mounted_octets || self.partitions.len() != 7 {
            return Err(LaboratoryAthenaError::Chronology);
        }
        let expected = [
            LaboratoryPartitionKind::Development,
            LaboratoryPartitionKind::HeldOutSuccessor,
            LaboratoryPartitionKind::CodecNotationLayoutRebase,
            LaboratoryPartitionKind::PhysicalApparatusPerturbation,
            LaboratoryPartitionKind::EqualAnswerDifferentRoute,
            LaboratoryPartitionKind::SubjectPortDisjointControl,
            LaboratoryPartitionKind::LaterChronology,
        ]
        .into_iter()
        .collect::<BTreeSet<_>>();
        let actual = self
            .partitions
            .iter()
            .map(|partition| partition.kind)
            .collect::<BTreeSet<_>>();
        if actual != expected
            || self.partitions.iter().any(|partition| {
                partition.occurrences.is_empty()
                    || partition
                        .occurrences
                        .iter()
                        .any(|occurrence| !addresses.contains(occurrence))
            })
        {
            return Err(LaboratoryAthenaError::Chronology);
        }
        Ok(())
    }
}

impl LaboratoryInquiry {
    pub fn found(
        predecessor_rest_sha256: String,
        presentation: ProductionInquiryPresentation,
        receiver_family: Vec<ProductionReceiver>,
        quadratic_section: [i64; 3],
        chart_map: [i64; 4],
        prior_history_occurrences: Vec<String>,
    ) -> Result<Self, LaboratoryAthenaError> {
        let mut inquiry = Self {
            schema: LABORATORY_INQUIRY_SCHEMA.to_owned(),
            occurrence: String::new(),
            predecessor_rest_sha256,
            presentation,
            receiver_family,
            quadratic_section,
            chart_map,
            prior_history_occurrences,
        };
        inquiry.occurrence = format!("l0/inquiry/{}", inquiry.body_sha256()?);
        inquiry.validate_shape()?;
        Ok(inquiry)
    }

    fn body_sha256(&self) -> Result<String, LaboratoryAthenaError> {
        #[derive(Serialize)]
        struct Body<'a> {
            schema: &'a str,
            predecessor_rest_sha256: &'a str,
            presentation: &'a ProductionInquiryPresentation,
            receiver_family: &'a [ProductionReceiver],
            quadratic_section: [i64; 3],
            chart_map: [i64; 4],
            prior_history_occurrences: &'a [String],
        }
        serde_json::to_vec(&Body {
            schema: &self.schema,
            predecessor_rest_sha256: &self.predecessor_rest_sha256,
            presentation: &self.presentation,
            receiver_family: &self.receiver_family,
            quadratic_section: self.quadratic_section,
            chart_map: self.chart_map,
            prior_history_occurrences: &self.prior_history_occurrences,
        })
        .map(|bytes| digest(&bytes))
        .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, LaboratoryAthenaError> {
        self.validate_shape()?;
        serde_json::to_vec(self).map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))
    }

    fn validate_shape(&self) -> Result<(), LaboratoryAthenaError> {
        let mut receivers = self.receiver_family.clone();
        receivers.sort_by_key(|receiver| *receiver as u8);
        receivers.dedup();
        let determinant = self.chart_map[0]
            .checked_mul(self.chart_map[3])
            .and_then(|left| {
                self.chart_map[1]
                    .checked_mul(self.chart_map[2])
                    .and_then(|right| left.checked_sub(right))
            });
        if self.schema != LABORATORY_INQUIRY_SCHEMA
            || self.occurrence != format!("l0/inquiry/{}", self.body_sha256()?)
            || !is_hex(&self.predecessor_rest_sha256, 64)
            || self.presentation.natural_language.is_empty()
            || self.presentation.notation.is_empty()
            || !is_hex(&self.presentation.vector_face_sha256, 64)
            || !is_hex(&self.presentation.raster_face_sha256, 64)
            || receivers.len() != 5
            || self.prior_history_occurrences.is_empty()
            || determinant.is_none_or(|value| value == 0)
        {
            return Err(LaboratoryAthenaError::Inquiry);
        }
        Ok(())
    }
}

impl LaboratoryAthenaRest {
    pub fn found(
        production: ProductionAthenaRest,
        native: GeneratorNativeRest,
        cultivated_history: CultivatedReceiverHistoryRest,
        chronology: LaboratoryChronology,
        decision_occurrence: String,
    ) -> Result<Self, LaboratoryAthenaError> {
        production
            .validate()
            .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?;
        chronology.validate()?;
        let native_bytes = native
            .canonical_bytes()
            .map_err(|error| LaboratoryAthenaError::Native(error.to_string()))?;
        let cultivated_bytes = cultivated_history
            .canonical_bytes()
            .map_err(|error| LaboratoryAthenaError::Cultivated(error.to_string()))?;
        CultivatedReceiverHistoryRest::mount(&cultivated_bytes, &native_bytes)
            .map_err(|error| LaboratoryAthenaError::Cultivated(error.to_string()))?;
        if decision_occurrence.is_empty() {
            return Err(LaboratoryAthenaError::Decision);
        }
        let component_identities = identities(
            &production,
            &native,
            &cultivated_history,
            &chronology,
        )?;
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
            production,
            native,
            cultivated_history,
            chronology,
            junction: LaboratoryStandingJunction {
                schema: LABORATORY_JUNCTION_SCHEMA.to_owned(),
                component_identities,
                genesis_decision_occurrence: decision_occurrence.clone(),
                decision_occurrence,
                decision: LaboratoryDecision::Declined,
                predecessor_identity: None,
                world_return: None,
                morphology_delta: None,
                open_exterior: vec![
                    "non-quadratic operation families remain open to later L-passages".to_owned(),
                    "unexcited inherited transport remains an open reconstruction fibre".to_owned(),
                    "new receiver histories may reopen the present route condensation".to_owned(),
                ],
            },
            decoder: LaboratoryRouteDecoder {
                schema: LABORATORY_DECODER_SCHEMA.to_owned(),
                expanded_transport_word: vec![0, 1, 2],
                condensed_transport_word: vec![3],
                obstruction_transport_word: vec![4],
                coefficient_basis: vec!["x^2".to_owned(), "x*y".to_owned(), "y^2".to_owned()],
            },
            reconstruction: LaboratoryReconstructionBoundary {
                schema: LABORATORY_FIBRES_SCHEMA.to_owned(),
                developmental_occurrence_sha256,
                complete_component_fibres: vec![
                    "r6-production-fibres".to_owned(),
                    "m3-native-source-fibres".to_owned(),
                    "m4-causal-adjoint-orbit".to_owned(),
                    "expanded-quadratic-coefficient-route".to_owned(),
                    "condensed-central-inversion-route".to_owned(),
                    "non-invariant-shortest-separator".to_owned(),
                ],
                shortest_separating_receivers: vec![
                    "single-axis-reflection-changes-the-mixed-coefficient".to_owned(),
                    "inhomogeneous-constant-or-linear-sections-reopen-central-inversion".to_owned(),
                    "same-value-different-operation-retains-route-lineage".to_owned(),
                ],
                open_alternatives: vec![
                    "higher-degree homogeneous sections".to_owned(),
                    "singular chart maps with kernel-image-cokernel fibres".to_owned(),
                    "receiver families beyond the frozen L0 chronology".to_owned(),
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
    ) -> Result<Self, LaboratoryAthenaError> {
        let standing = decode_components(STANDING_MAGIC, standing, 5)?;
        let decoder = decode_components(DECODER_MAGIC, decoder, 2)?;
        let fibres = decode_components(FIBRES_MAGIC, fibres, 2)?;
        let production = ProductionAthenaRest::read(&standing[0], &decoder[0], &fibres[0])
            .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?;
        let native = GeneratorNativeRest::read(&standing[1])
            .map_err(|error| LaboratoryAthenaError::Native(error.to_string()))?;
        let cultivated_history: CultivatedReceiverHistoryRest = serde_json::from_slice(&standing[2])
            .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?;
        CultivatedReceiverHistoryRest::mount(&standing[2], &standing[1])
            .map_err(|error| LaboratoryAthenaError::Cultivated(error.to_string()))?;
        let rest = Self {
            production,
            native,
            cultivated_history,
            chronology: serde_json::from_slice(&standing[3])
                .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
            junction: serde_json::from_slice(&standing[4])
                .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
            decoder: serde_json::from_slice(&decoder[1])
                .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
            reconstruction: serde_json::from_slice(&fibres[1])
                .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, LaboratoryAthenaError> {
        self.validate()?;
        encode_components(
            STANDING_MAGIC,
            &[
                self.production
                    .standing_bytes()
                    .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?,
                self.native
                    .canonical_bytes()
                    .map_err(|error| LaboratoryAthenaError::Native(error.to_string()))?,
                self.cultivated_history
                    .canonical_bytes()
                    .map_err(|error| LaboratoryAthenaError::Cultivated(error.to_string()))?,
                serde_json::to_vec(&self.chronology)
                    .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
                serde_json::to_vec(&self.junction)
                    .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
            ],
        )
        .map_err(Into::into)
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, LaboratoryAthenaError> {
        self.validate()?;
        encode_components(
            DECODER_MAGIC,
            &[
                self.production
                    .decoder_bytes()
                    .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?,
                serde_json::to_vec(&self.decoder)
                    .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
            ],
        )
        .map_err(Into::into)
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, LaboratoryAthenaError> {
        self.validate()?;
        encode_components(
            FIBRES_MAGIC,
            &[
                self.production
                    .fibre_bytes()
                    .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?,
                serde_json::to_vec(&self.reconstruction)
                    .map_err(|error| LaboratoryAthenaError::Wire(error.to_string()))?,
            ],
        )
        .map_err(Into::into)
    }

    pub fn canonical_identity(&self) -> Result<String, LaboratoryAthenaError> {
        let mut hasher = Sha256::new();
        for bytes in [
            self.standing_bytes()?,
            self.decoder_bytes()?,
            self.fibre_bytes()?,
        ] {
            hasher.update((bytes.len() as u64).to_le_bytes());
            hasher.update(bytes);
        }
        Ok(hex(hasher.finalize()))
    }

    pub fn committed(&self) -> bool {
        self.junction.decision == LaboratoryDecision::Committed
    }

    pub fn admit_inquiry(&self, inquiry: &LaboratoryInquiry) -> Result<(), LaboratoryAthenaError> {
        inquiry.validate_shape()?;
        if inquiry.predecessor_rest_sha256 != self.canonical_identity()?
            || self
                .reconstruction
                .developmental_occurrence_sha256
                .binary_search(&digest(inquiry.occurrence.as_bytes()))
                .is_ok()
        {
            return Err(LaboratoryAthenaError::Inquiry);
        }
        Ok(())
    }

    pub fn route_for(&self, invariant: bool, chart_map: [i64; 4]) -> &[u32] {
        if !invariant {
            &self.decoder.obstruction_transport_word
        } else if self.committed() && chart_map == [-1, 0, 0, -1] {
            &self.decoder.condensed_transport_word
        } else {
            &self.decoder.expanded_transport_word
        }
    }

    pub fn route_after_targeted_ablation(&self, invariant: bool) -> &[u32] {
        if invariant {
            &self.decoder.expanded_transport_word
        } else {
            &self.decoder.obstruction_transport_word
        }
    }

    pub fn commit_return(
        mut self,
        world_return: LaboratoryWorldReturn,
        morphology_delta: LaboratoryMorphologyDelta,
        decision_occurrence: String,
    ) -> Result<Self, LaboratoryAthenaError> {
        self.validate()?;
        if self.committed()
            || decision_occurrence.is_empty()
            || decision_occurrence == self.junction.decision_occurrence
            || !world_return.accepted
            || world_return.lean_exit_status != 0
            || world_return.exact_difference_octets == 0
            || !is_hex(&world_return.emitted_product_sha256, 64)
            || !is_hex(&world_return.returned_lean_sha256, 64)
            || morphology_delta.occurrence.is_empty()
            || morphology_delta.returned_occurrence != world_return.occurrence
            || morphology_delta.support_coordinates.is_empty()
            || morphology_delta.expanded_transport_word != self.decoder.expanded_transport_word
            || morphology_delta.condensed_transport_word != self.decoder.condensed_transport_word
            || !morphology_delta.metric_adjoint_held
            || morphology_delta.exact_rank == 0
        {
            return Err(LaboratoryAthenaError::WorldReturn);
        }
        let predecessor_identity = self.canonical_identity()?;
        self.junction.decision = LaboratoryDecision::Committed;
        self.junction.decision_occurrence = decision_occurrence;
        self.junction.predecessor_identity = Some(predecessor_identity);
        self.junction.world_return = Some(world_return);
        self.junction.morphology_delta = Some(morphology_delta);
        self.validate()?;
        Ok(self)
    }

    pub fn withdraw(
        mut self,
    ) -> Result<(Self, LaboratoryWithdrawalReceipt), LaboratoryAthenaError> {
        self.validate()?;
        if !self.committed() {
            return Err(LaboratoryAthenaError::Decision);
        }
        let committed_identity = self.canonical_identity()?;
        let predecessor_identity = self
            .junction
            .predecessor_identity
            .take()
            .ok_or(LaboratoryAthenaError::Decision)?;
        self.junction.decision = LaboratoryDecision::Declined;
        self.junction.decision_occurrence = self.junction.genesis_decision_occurrence.clone();
        self.junction.world_return = None;
        self.junction.morphology_delta = None;
        self.validate()?;
        let restored_identity = self.canonical_identity()?;
        let receipt = LaboratoryWithdrawalReceipt {
            committed_identity,
            predecessor_identity: predecessor_identity.clone(),
            restored_identity: restored_identity.clone(),
            exact_predecessor_restored: predecessor_identity == restored_identity,
        };
        if !receipt.exact_predecessor_restored {
            return Err(LaboratoryAthenaError::Withdrawal);
        }
        Ok((self, receipt))
    }

    pub fn validate(&self) -> Result<(), LaboratoryAthenaError> {
        self.production
            .validate()
            .map_err(|error| LaboratoryAthenaError::Production(error.to_string()))?;
        self.chronology.validate()?;
        self.native
            .validate()
            .map_err(|error| LaboratoryAthenaError::Native(error.to_string()))?;
        let native_bytes = self
            .native
            .canonical_bytes()
            .map_err(|error| LaboratoryAthenaError::Native(error.to_string()))?;
        let cultivated_bytes = self
            .cultivated_history
            .canonical_bytes()
            .map_err(|error| LaboratoryAthenaError::Cultivated(error.to_string()))?;
        CultivatedReceiverHistoryRest::mount(&cultivated_bytes, &native_bytes)
            .map_err(|error| LaboratoryAthenaError::Cultivated(error.to_string()))?;
        if self.junction.schema != LABORATORY_JUNCTION_SCHEMA
            || self.junction.component_identities
                != identities(
                    &self.production,
                    &self.native,
                    &self.cultivated_history,
                    &self.chronology,
                )?
            || self.junction.genesis_decision_occurrence.is_empty()
            || self.junction.decision_occurrence.is_empty()
            || self.junction.open_exterior.is_empty()
            || self.decoder.schema != LABORATORY_DECODER_SCHEMA
            || self.decoder.expanded_transport_word.len() <= self.decoder.condensed_transport_word.len()
            || self.decoder.condensed_transport_word.is_empty()
            || self.decoder.obstruction_transport_word.is_empty()
            || self.decoder.coefficient_basis.len() != 3
            || self.reconstruction.schema != LABORATORY_FIBRES_SCHEMA
            || self.reconstruction.developmental_occurrence_sha256.is_empty()
            || self
                .reconstruction
                .developmental_occurrence_sha256
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || self.reconstruction.complete_component_fibres.len() < 6
            || self.reconstruction.shortest_separating_receivers.is_empty()
            || self.reconstruction.open_alternatives.is_empty()
        {
            return Err(LaboratoryAthenaError::Chronology);
        }
        match (
            self.junction.decision,
            &self.junction.predecessor_identity,
            &self.junction.world_return,
            &self.junction.morphology_delta,
        ) {
            (LaboratoryDecision::Declined, None, None, None) => {
                if self.junction.decision_occurrence != self.junction.genesis_decision_occurrence {
                    return Err(LaboratoryAthenaError::Decision);
                }
            }
            (LaboratoryDecision::Committed, Some(predecessor), Some(returned), Some(delta)) => {
                if !is_hex(predecessor, 64)
                    || !returned.accepted
                    || returned.lean_exit_status != 0
                    || returned.exact_difference_octets == 0
                    || !is_hex(&returned.emitted_product_sha256, 64)
                    || !is_hex(&returned.returned_lean_sha256, 64)
                    || delta.returned_occurrence != returned.occurrence
                    || !delta.metric_adjoint_held
                    || delta.exact_rank == 0
                    || self.junction.decision_occurrence
                        == self.junction.genesis_decision_occurrence
                {
                    return Err(LaboratoryAthenaError::Decision);
                }
            }
            _ => return Err(LaboratoryAthenaError::Decision),
        }
        Ok(())
    }
}

impl From<super::types::ProductionAthenaError> for LaboratoryAthenaError {
    fn from(error: super::types::ProductionAthenaError) -> Self {
        LaboratoryAthenaError::Wire(error.to_string())
    }
}
