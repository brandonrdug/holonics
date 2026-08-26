//! The N4 product owns one native mathematical continuation, one optical rest, and one
//! heterogeneous three-port rest. It is intentionally not `Clone`.

use holonic_engine::{
    cuda_refine::{CudaRefineExecutor, DeviceHeterogeneousFusion},
    native_ecology::heterogeneous_fusion::HeterogeneousFusionRest,
};
use life::{
    mathematical_particle::{
        NativeMathematicalConsequence, NativeMathematicalInquiry, NativeSuccessorHistory,
    },
    mathematical_source::OpticalPassage,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::cultivation::{NativeCultivatedMathematicalRest, NativeMathematicalWorldReturn};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AthenaContinuationStanding {
    pub schema: String,
    pub predecessor_cultivated_rest_sha256: String,
    pub predecessor_world_return_occurrence: String,
    pub returned_world: NativeMathematicalWorldReturn,
    pub retained_history_suffix: Vec<String>,
    pub receiver_visible_change: String,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AthenaProductWithdrawal {
    pub product_sha256: String,
    pub mathematical_rest_sha256: String,
    pub optical_rest_sha256: String,
    pub heterogeneous_rest_sha256: String,
    pub continuation_withdrawn: bool,
    pub exact_component_owners_returned: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct LaboratoryAthenaProduct {
    mathematics: NativeCultivatedMathematicalRest,
    optical: OpticalPassage,
    heterogeneous: HeterogeneousFusionRest,
    continuation: AthenaContinuationStanding,
}

impl AthenaContinuationStanding {
    pub fn found(
        predecessor: &NativeCultivatedMathematicalRest,
        returned_world: NativeMathematicalWorldReturn,
    ) -> Result<Self, String> {
        let predecessor_cultivated_rest_sha256 = predecessor.canonical_identity()?;
        if !returned_world.separately_addressed_after_emission
            || returned_world.occurrence == predecessor.standing().world_return.occurrence
            || returned_world.causing_laboratory_occurrences.len() < 3
            || returned_world.support_families != vec![0, 1]
        {
            return Err("the N4 world return is not a later addressed continuation".to_owned());
        }
        let retained_history_suffix = vec![
            predecessor.standing().world_return.occurrence.clone(),
            returned_world.occurrence.clone(),
        ];
        Ok(Self {
            schema: "holonics.n4.athena-continuation-standing.v1".to_owned(),
            predecessor_cultivated_rest_sha256,
            predecessor_world_return_occurrence: predecessor
                .standing()
                .world_return
                .occurrence
                .clone(),
            returned_world,
            retained_history_suffix,
            receiver_visible_change: "the later native consequence retains the newly returned world occurrence in every derivational transport word; exact answer equality does not collapse the richer causal signature".to_owned(),
            open_exterior: vec![
                "continued morphology beyond this returned history suffix remains an open typed port".to_owned(),
                "receiver families outside the fixed-section native decoder remain open".to_owned(),
            ],
        })
    }
}

impl LaboratoryAthenaProduct {
    pub fn found(
        mathematics: NativeCultivatedMathematicalRest,
        optical: OpticalPassage,
        heterogeneous: HeterogeneousFusionRest,
        continuation: AthenaContinuationStanding,
    ) -> Result<Self, String> {
        let product = Self {
            mathematics,
            optical,
            heterogeneous,
            continuation,
        };
        product.validate()?;
        Ok(product)
    }

    #[allow(clippy::too_many_arguments)]
    pub fn read(
        mathematical_predecessor_standing: &[u8],
        mathematical_predecessor_decoder: &[u8],
        mathematical_predecessor_fibres: &[u8],
        mathematical_cultivation_standing: &[u8],
        optical_standing: &[u8],
        heterogeneous_standing: &[u8],
        heterogeneous_decoder: &[u8],
        heterogeneous_fibres: &[u8],
        continuation_standing: &[u8],
    ) -> Result<Self, String> {
        let mathematics = NativeCultivatedMathematicalRest::read(
            mathematical_predecessor_standing,
            mathematical_predecessor_decoder,
            mathematical_predecessor_fibres,
            mathematical_cultivation_standing,
        )?;
        let optical =
            serde_json::from_slice(optical_standing).map_err(|error| error.to_string())?;
        let heterogeneous = HeterogeneousFusionRest::read(
            heterogeneous_standing,
            heterogeneous_decoder,
            heterogeneous_fibres,
        )
        .map_err(|error| error.to_string())?;
        let continuation =
            serde_json::from_slice(continuation_standing).map_err(|error| error.to_string())?;
        Self::found(mathematics, optical, heterogeneous, continuation)
    }

    pub fn found_inquiry(
        &self,
        source_occurrences: Vec<String>,
        sections: Vec<Vec<i64>>,
        requested_histories: Vec<NativeSuccessorHistory>,
        open_exterior: Vec<String>,
    ) -> Result<NativeMathematicalInquiry, String> {
        let mut history = self
            .mathematics
            .predecessor()
            .reconstruction()
            .predecessor_component_addresses
            .iter()
            .rev()
            .take(4)
            .cloned()
            .collect::<Vec<_>>();
        history.extend(self.continuation.retained_history_suffix.clone());
        self.mathematics
            .predecessor()
            .found_native_mathematical_inquiry(
                source_occurrences,
                sections,
                requested_histories,
                history,
                open_exterior,
            )
            .map_err(|error| error.to_string())
    }

    pub fn found_precontinuation_inquiry(
        &self,
        source_occurrences: Vec<String>,
        sections: Vec<Vec<i64>>,
        requested_histories: Vec<NativeSuccessorHistory>,
        open_exterior: Vec<String>,
    ) -> Result<NativeMathematicalInquiry, String> {
        let history = self
            .mathematics
            .predecessor()
            .reconstruction()
            .predecessor_component_addresses
            .iter()
            .rev()
            .take(4)
            .cloned()
            .chain(std::iter::once(
                self.continuation
                    .predecessor_world_return_occurrence
                    .clone(),
            ))
            .collect::<Vec<_>>();
        self.mathematics
            .predecessor()
            .found_native_mathematical_inquiry(
                source_occurrences,
                sections,
                requested_histories,
                history,
                open_exterior,
            )
            .map_err(|error| error.to_string())
    }

    pub fn conduct(
        &self,
        inquiry: &NativeMathematicalInquiry,
        card: &mut CudaRefineExecutor,
    ) -> Result<NativeMathematicalConsequence, String> {
        self.mathematics
            .conduct_rich_cultivated_consequence(inquiry, card)
    }

    pub fn conduct_heterogeneous(
        &self,
        card: &mut CudaRefineExecutor,
    ) -> Result<DeviceHeterogeneousFusion, String> {
        card.conduct_heterogeneous_fusion_on_device(
            &self.heterogeneous.standing.successor_action,
            &self.heterogeneous.decoder_addresses(),
            &self.heterogeneous.starts(),
            self.heterogeneous.standing.family_count as usize,
            self.heterogeneous.standing.ports.len(),
        )
        .map_err(|error| error.to_string())
    }

    pub fn mathematics(&self) -> &NativeCultivatedMathematicalRest {
        &self.mathematics
    }

    pub fn optical(&self) -> &OpticalPassage {
        &self.optical
    }

    pub fn heterogeneous(&self) -> &HeterogeneousFusionRest {
        &self.heterogeneous
    }

    pub fn continuation(&self) -> &AthenaContinuationStanding {
        &self.continuation
    }

    pub fn continuation_bytes(&self) -> Result<Vec<u8>, String> {
        serde_json::to_vec(&self.continuation).map_err(|error| error.to_string())
    }

    pub fn optical_bytes(&self) -> Result<Vec<u8>, String> {
        serde_json::to_vec(&self.optical).map_err(|error| error.to_string())
    }

    pub fn canonical_identity(&self) -> Result<String, String> {
        let mut digest = Sha256::new();
        for bytes in self.component_bytes()? {
            digest.update((bytes.len() as u64).to_le_bytes());
            digest.update(bytes);
        }
        Ok(hex(digest.finalize()))
    }

    pub fn component_bytes(&self) -> Result<Vec<Vec<u8>>, String> {
        Ok(vec![
            self.mathematics
                .predecessor()
                .standing_bytes()
                .map_err(|error| error.to_string())?,
            self.mathematics
                .predecessor()
                .decoder_bytes()
                .map_err(|error| error.to_string())?,
            self.mathematics
                .predecessor()
                .fibre_bytes()
                .map_err(|error| error.to_string())?,
            self.mathematics.standing_bytes()?,
            self.optical_bytes()?,
            self.heterogeneous
                .standing_bytes()
                .map_err(|error| error.to_string())?,
            self.heterogeneous
                .decoder_bytes()
                .map_err(|error| error.to_string())?,
            self.heterogeneous
                .fibre_bytes()
                .map_err(|error| error.to_string())?,
            self.continuation_bytes()?,
        ])
    }

    pub fn withdraw(self) -> Result<AthenaProductWithdrawal, String> {
        self.validate()?;
        let product_sha256 = self.canonical_identity()?;
        let mathematical_rest_sha256 = self.mathematics.canonical_identity()?;
        let optical_rest_sha256 = hex(Sha256::digest(self.optical_bytes()?));
        let heterogeneous_rest_sha256 = heterogeneous_identity(&self.heterogeneous)?;
        Ok(AthenaProductWithdrawal {
            product_sha256,
            mathematical_rest_sha256,
            optical_rest_sha256,
            heterogeneous_rest_sha256,
            continuation_withdrawn: true,
            exact_component_owners_returned: true,
        })
    }

    fn validate(&self) -> Result<(), String> {
        if self.mathematics.canonical_identity()?
            != self.continuation.predecessor_cultivated_rest_sha256
            || self.continuation.schema != "holonics.n4.athena-continuation-standing.v1"
            || self.continuation.retained_history_suffix.len() != 2
            || self.continuation.returned_world.occurrence
                != self.continuation.retained_history_suffix[1]
            || self.optical.components.is_empty()
            || self.optical.relations.is_empty()
            || self
                .optical
                .glyph_testimony
                .as_ref()
                .is_none_or(|testimony| {
                    testimony.glyphs.is_empty()
                        || !testimony.complete_overlap_fibre
                        || testimony.labels_route_spatial_law
                })
            || self.optical.productive_transcript_present
            || self.optical.productive_text_layer_present
            || self.heterogeneous.standing.ports.len() != 3
            || self.heterogeneous.fibres.naturality_squares.len() != 6
            || self
                .heterogeneous
                .fibres
                .naturality_squares
                .iter()
                .any(|square| !square.commutes)
        {
            return Err("the N4 product components do not close one bounded ecology".to_owned());
        }
        Ok(())
    }
}

fn heterogeneous_identity(rest: &HeterogeneousFusionRest) -> Result<String, String> {
    let mut digest = Sha256::new();
    for bytes in [
        rest.standing_bytes().map_err(|error| error.to_string())?,
        rest.decoder_bytes().map_err(|error| error.to_string())?,
        rest.fibre_bytes().map_err(|error| error.to_string())?,
    ] {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    Ok(hex(digest.finalize()))
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
