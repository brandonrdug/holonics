use holonic_engine::native_ecology::inference_ecology::InferenceEcologyRest;
use sha2::{Digest, Sha256};

use super::super::{DynamicMorphologyRest, LongHorizonRetainedBoundary, MultimodalTransportRest};
use super::components::component_identities;
use super::types::{
    ProductionDecision, ProductionEcologyError, ProductionEcologyRest, ProductionFibreBinding,
    ProductionInquiry, ProductionReconstructionBoundary, ProductionStandingJunction,
    ProductionWithdrawalReceipt, ProductionWorldReturn,
};
use super::wire::{decode_components, digest, digest_text, encode_components, hex};
use super::{
    DECODER_MAGIC, FIBRES_MAGIC, PRODUCTION_FIBRES_SCHEMA, PRODUCTION_JUNCTION_SCHEMA,
    STANDING_MAGIC,
};

impl ProductionEcologyRest {
    pub fn found(
        inference: InferenceEcologyRest,
        morphology: DynamicMorphologyRest,
        retained_boundary: LongHorizonRetainedBoundary,
        media: MultimodalTransportRest,
        development_occurrences: Vec<String>,
        decision_occurrence: String,
    ) -> Result<Self, ProductionEcologyError> {
        if development_occurrences.is_empty() || decision_occurrence.is_empty() {
            return Err(ProductionEcologyError::Lineage);
        }
        let component_identities =
            component_identities(&inference, &morphology, &retained_boundary, &media)?;
        let component_fibres = [
            "i5-recurrent-fibres",
            "i5-heterogeneous-fibres",
            "r4-retained-boundary-fibres",
            "r5-joint-media-fibres",
        ]
        .into_iter()
        .map(|role| {
            let identity = component_identities
                .iter()
                .find(|identity| identity.role == role)
                .ok_or(ProductionEcologyError::Lineage)?;
            Ok(ProductionFibreBinding {
                role: role.to_owned(),
                component_sha256: identity.sha256.clone(),
                complete_reconstruction_component: true,
            })
        })
        .collect::<Result<Vec<_>, ProductionEcologyError>>()?;
        let mut development_occurrence_sha256 = development_occurrences
            .iter()
            .map(|occurrence| digest(occurrence.as_bytes()))
            .collect::<Vec<_>>();
        development_occurrence_sha256.sort();
        development_occurrence_sha256.dedup();
        let rest = Self {
            inference,
            morphology,
            retained_boundary,
            media,
            junction: ProductionStandingJunction {
                schema: PRODUCTION_JUNCTION_SCHEMA.to_owned(),
                component_identities,
                receiver_basis: vec![
                    "codec-rebase-and-presentation-separation".to_owned(),
                    "ordered-operation-and-retained-history".to_owned(),
                    "proof-checker-and-exact-value".to_owned(),
                    "unit-dimension-and-physical-boundary".to_owned(),
                    "notation-vector-raster-common-world".to_owned(),
                    "world-return-cultivation-and-withdrawal".to_owned(),
                ],
                history_basis: vec![
                    "r2-first-recurrence-of-the-material-founded-endomap".to_owned(),
                    "r3-returned-constraint-successor-and-immediate-predecessor".to_owned(),
                    "r4-all-declared-ordered-generator-words-and-richer-reopening".to_owned(),
                    "r5-heldout-joint-media-successor-and-all-withdrawals".to_owned(),
                ],
                genesis_decision_occurrence: decision_occurrence.clone(),
                decision_occurrence,
                decision: ProductionDecision::Declined,
                predecessor_identity: None,
                world_return: None,
                open_exterior: vec![
                    "transport outside the declared native receiver/history family remains an open reconstruction fibre"
                        .to_owned(),
                    "mathematical operations outside the R0--R5 receiver/history basis remain open"
                        .to_owned(),
                    "audio, temporal production, sensorimotor consequence, and external model fusion remain open"
                        .to_owned(),
                    "a new receiver or successor history may reopen every present condensation"
                        .to_owned(),
                ],
            },
            reconstruction: ProductionReconstructionBoundary {
                schema: PRODUCTION_FIBRES_SCHEMA.to_owned(),
                development_occurrence_sha256,
                component_fibres,
                shortest_separating_receivers: vec![
                    "same-value-different-operation".to_owned(),
                    "equal-prefix-different-future".to_owned(),
                    "r4-richer-exact-interior".to_owned(),
                    "r5-four-versus-eight-connected-raster-incidence".to_owned(),
                ],
                open_alternatives: vec![
                    "the vector/raster direct pair remains undeclared".to_owned(),
                    "a new media chart reopens its retained interior".to_owned(),
                    "proof acceptance does not identify proof-route lineage".to_owned(),
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
    ) -> Result<Self, ProductionEcologyError> {
        let standing = decode_components(STANDING_MAGIC, standing, 7)?;
        let decoder = decode_components(DECODER_MAGIC, decoder, 4)?;
        let fibres = decode_components(FIBRES_MAGIC, fibres, 5)?;
        let rest = Self {
            inference: InferenceEcologyRest::read(
                &standing[0],
                &decoder[0],
                &fibres[0],
                &standing[1],
                &decoder[1],
                &fibres[1],
                &standing[2],
            )
            .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
            morphology: DynamicMorphologyRest::read(&standing[3])
                .map_err(|error| ProductionEcologyError::Morphology(error.to_string()))?,
            retained_boundary: LongHorizonRetainedBoundary::read(
                &standing[4],
                &decoder[2],
                &fibres[2],
            )
            .map_err(|error| ProductionEcologyError::Boundary(error.to_string()))?,
            media: MultimodalTransportRest::read(&standing[5], &decoder[3], &fibres[3])
                .map_err(|error| ProductionEcologyError::Media(error.to_string()))?,
            junction: serde_json::from_slice(&standing[6])
                .map_err(|error| ProductionEcologyError::Wire(error.to_string()))?,
            reconstruction: serde_json::from_slice(&fibres[4])
                .map_err(|error| ProductionEcologyError::Wire(error.to_string()))?,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, ProductionEcologyError> {
        self.validate()?;
        encode_components(
            STANDING_MAGIC,
            &[
                self.inference
                    .recurrent
                    .standing_bytes()
                    .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
                self.inference
                    .heterogeneous
                    .standing_bytes()
                    .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
                self.inference
                    .junction_bytes()
                    .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
                self.morphology
                    .canonical_bytes()
                    .map_err(|error| ProductionEcologyError::Morphology(error.to_string()))?,
                self.retained_boundary
                    .standing_bytes()
                    .map_err(|error| ProductionEcologyError::Boundary(error.to_string()))?,
                self.media
                    .standing_bytes()
                    .map_err(|error| ProductionEcologyError::Media(error.to_string()))?,
                serde_json::to_vec(&self.junction)
                    .map_err(|error| ProductionEcologyError::Wire(error.to_string()))?,
            ],
        )
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, ProductionEcologyError> {
        self.validate()?;
        encode_components(
            DECODER_MAGIC,
            &[
                self.inference
                    .recurrent
                    .decoder_bytes()
                    .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
                self.inference
                    .heterogeneous
                    .decoder_bytes()
                    .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
                self.retained_boundary
                    .decoder_bytes()
                    .map_err(|error| ProductionEcologyError::Boundary(error.to_string()))?,
                self.media
                    .decoder_bytes()
                    .map_err(|error| ProductionEcologyError::Media(error.to_string()))?,
            ],
        )
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, ProductionEcologyError> {
        self.validate()?;
        encode_components(
            FIBRES_MAGIC,
            &[
                self.inference
                    .recurrent
                    .fibre_bytes()
                    .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
                self.inference
                    .heterogeneous
                    .fibre_bytes()
                    .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?,
                self.retained_boundary
                    .fibre_bytes()
                    .map_err(|error| ProductionEcologyError::Boundary(error.to_string()))?,
                self.media
                    .fibre_bytes()
                    .map_err(|error| ProductionEcologyError::Media(error.to_string()))?,
                serde_json::to_vec(&self.reconstruction)
                    .map_err(|error| ProductionEcologyError::Wire(error.to_string()))?,
            ],
        )
    }

    pub fn canonical_identity(&self) -> Result<String, ProductionEcologyError> {
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
        self.junction.decision == ProductionDecision::Committed
    }

    pub fn admit_inquiry(&self, inquiry: &ProductionInquiry) -> Result<(), ProductionEcologyError> {
        inquiry.validate_shape()?;
        let admitted_predecessor = self
            .junction
            .predecessor_identity
            .as_deref()
            .unwrap_or(&inquiry.predecessor_rest_sha256);
        if inquiry.predecessor_rest_sha256 != admitted_predecessor
            || (!self.committed()
                && inquiry.predecessor_rest_sha256 != self.canonical_identity()?)
            || inquiry.heldout_family != self.media.standing.heldout_family
            || inquiry.requested_face.left_species != 2
            || inquiry.requested_face.right_species != 3
            || inquiry
                .context_word
                .iter()
                .any(|generator| *generator as usize >= self.context_generators())
            || self
                .reconstruction
                .development_occurrence_sha256
                .binary_search(&digest(inquiry.occurrence.as_bytes()))
                .is_ok()
        {
            return Err(ProductionEcologyError::Inquiry);
        }
        Ok(())
    }

    pub fn commit_return(
        mut self,
        world_return: ProductionWorldReturn,
        decision_occurrence: String,
    ) -> Result<Self, ProductionEcologyError> {
        self.validate()?;
        world_return.validate()?;
        if self.committed()
            || decision_occurrence.is_empty()
            || decision_occurrence == self.junction.decision_occurrence
        {
            return Err(ProductionEcologyError::Decision);
        }
        let predecessor_identity = self.canonical_identity()?;
        self.junction.decision = ProductionDecision::Committed;
        self.junction.decision_occurrence = decision_occurrence;
        self.junction.predecessor_identity = Some(predecessor_identity);
        self.junction.world_return = Some(world_return);
        self.validate()?;
        Ok(self)
    }

    pub fn withdraw(
        mut self,
    ) -> Result<(Self, ProductionWithdrawalReceipt), ProductionEcologyError> {
        self.validate()?;
        if !self.committed() {
            return Err(ProductionEcologyError::Decision);
        }
        let committed_identity = self.canonical_identity()?;
        let predecessor_identity = self
            .junction
            .predecessor_identity
            .take()
            .ok_or(ProductionEcologyError::Decision)?;
        self.junction.decision = ProductionDecision::Declined;
        self.junction.decision_occurrence = self.junction.genesis_decision_occurrence.clone();
        self.junction.world_return = None;
        self.validate()?;
        let restored_identity = self.canonical_identity()?;
        let receipt = ProductionWithdrawalReceipt {
            committed_identity,
            predecessor_identity: predecessor_identity.clone(),
            restored_identity: restored_identity.clone(),
            exact_predecessor_restored: restored_identity == predecessor_identity,
        };
        if !receipt.exact_predecessor_restored {
            return Err(ProductionEcologyError::Withdrawal);
        }
        Ok((self, receipt))
    }

    pub fn context_generators(&self) -> usize {
        self.retained_boundary.standing.generator_table.len()
            / self.retained_boundary.standing.native_states.len()
    }

    pub fn context_starts(&self) -> Result<Vec<u32>, ProductionEcologyError> {
        self.retained_boundary
            .standing
            .native_states
            .iter()
            .map(|state| u32::try_from(state.0).map_err(|_| ProductionEcologyError::Extent))
            .collect()
    }

    pub fn media_candidate_species(&self) -> Vec<u32> {
        self.media
            .standing
            .heldout_anchor_sections
            .iter()
            .flat_map(|section| {
                [
                    1,
                    section.vector_candidates,
                    section.raster_four_candidates,
                    section.raster_eight_candidates,
                ]
            })
            .collect()
    }

    pub fn validate(&self) -> Result<(), ProductionEcologyError> {
        self.inference
            .validate()
            .map_err(|error| ProductionEcologyError::Inference(error.to_string()))?;
        self.morphology
            .canonical_bytes()
            .map_err(|error| ProductionEcologyError::Morphology(error.to_string()))?;
        self.retained_boundary
            .validate()
            .map_err(|error| ProductionEcologyError::Boundary(error.to_string()))?;
        self.media
            .standing_bytes()
            .map_err(|error| ProductionEcologyError::Media(error.to_string()))?;
        let expected = component_identities(
            &self.inference,
            &self.morphology,
            &self.retained_boundary,
            &self.media,
        )?;
        if self.junction.schema != PRODUCTION_JUNCTION_SCHEMA
            || self.junction.component_identities != expected
            || self.junction.receiver_basis.len() < 5
            || self.junction.history_basis.len() < 4
            || self.junction.genesis_decision_occurrence.is_empty()
            || self.junction.decision_occurrence.is_empty()
            || self.junction.open_exterior.is_empty()
            || self.reconstruction.schema != PRODUCTION_FIBRES_SCHEMA
            || self.reconstruction.development_occurrence_sha256.is_empty()
            || self
                .reconstruction
                .development_occurrence_sha256
                .windows(2)
                .any(|pair| pair[0] >= pair[1])
            || self.reconstruction.component_fibres.len() != 4
            || self
                .reconstruction
                .component_fibres
                .iter()
                .any(|binding| !binding.complete_reconstruction_component)
            || self.reconstruction.shortest_separating_receivers.is_empty()
            || self.reconstruction.open_alternatives.is_empty()
            || self.context_generators() < 2
            || self.morphology.predecessor_action().len()
                != self.morphology.successor_action().len()
            || self.media.standing.heldout_anchor_sections.is_empty()
        {
            return Err(ProductionEcologyError::Lineage);
        }
        match (
            self.junction.decision,
            &self.junction.predecessor_identity,
            &self.junction.world_return,
        ) {
            (ProductionDecision::Declined, None, None) => {
                if self.junction.decision_occurrence != self.junction.genesis_decision_occurrence {
                    return Err(ProductionEcologyError::Decision);
                }
            }
            (ProductionDecision::Committed, Some(predecessor), Some(world_return)) => {
                if !digest_text(predecessor)
                    || self.junction.decision_occurrence
                        == self.junction.genesis_decision_occurrence
                {
                    return Err(ProductionEcologyError::Decision);
                }
                world_return.validate()?;
            }
            _ => return Err(ProductionEcologyError::Decision),
        }
        for binding in &self.reconstruction.component_fibres {
            let identity = expected
                .iter()
                .find(|identity| identity.role == binding.role)
                .ok_or(ProductionEcologyError::Lineage)?;
            if identity.sha256 != binding.component_sha256 {
                return Err(ProductionEcologyError::Lineage);
            }
        }
        Ok(())
    }
}
