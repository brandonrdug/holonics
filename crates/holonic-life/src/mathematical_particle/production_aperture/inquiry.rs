use serde::Serialize;

use super::types::{
    ProductionEcologyError, ProductionInquiry, ProductionInquiryFace,
    ProductionInquiryPresentation, ProductionReceiver, ProductionWorldReturn,
};
use super::wire::{digest, digest_text};
use super::PRODUCTION_INQUIRY_SCHEMA;

impl ProductionWorldReturn {
    pub(super) fn validate(&self) -> Result<(), ProductionEcologyError> {
        if self.occurrence.is_empty()
            || self.receiver.is_empty()
            || !self.accepted
            || self.exact_difference_octets == 0
            || !digest_text(&self.emitted_product_sha256)
            || !digest_text(&self.returned_product_sha256)
        {
            return Err(ProductionEcologyError::WorldReturn);
        }
        Ok(())
    }
}

impl ProductionInquiry {
    pub fn found(
        predecessor_rest_sha256: String,
        presentation: ProductionInquiryPresentation,
        context_word: Vec<u32>,
        receiver_family: Vec<ProductionReceiver>,
        requested_face: ProductionInquiryFace,
        heldout_family: u32,
    ) -> Result<Self, ProductionEcologyError> {
        let mut inquiry = Self {
            schema: PRODUCTION_INQUIRY_SCHEMA.to_owned(),
            occurrence: String::new(),
            predecessor_rest_sha256,
            presentation,
            context_word,
            receiver_family,
            requested_face,
            heldout_family,
        };
        inquiry.occurrence = format!("r6/inquiry/{}", inquiry.body_sha256()?);
        Ok(inquiry)
    }

    fn body_sha256(&self) -> Result<String, ProductionEcologyError> {
        #[derive(Serialize)]
        struct Body<'a> {
            schema: &'a str,
            predecessor_rest_sha256: &'a str,
            presentation: &'a ProductionInquiryPresentation,
            context_word: &'a [u32],
            receiver_family: &'a [ProductionReceiver],
            requested_face: &'a ProductionInquiryFace,
            heldout_family: u32,
        }
        serde_json::to_vec(&Body {
            schema: &self.schema,
            predecessor_rest_sha256: &self.predecessor_rest_sha256,
            presentation: &self.presentation,
            context_word: &self.context_word,
            receiver_family: &self.receiver_family,
            requested_face: &self.requested_face,
            heldout_family: self.heldout_family,
        })
        .map(|bytes| digest(&bytes))
        .map_err(|error| ProductionEcologyError::Wire(error.to_string()))
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, ProductionEcologyError> {
        self.validate_shape()?;
        serde_json::to_vec(self).map_err(|error| ProductionEcologyError::Wire(error.to_string()))
    }

    pub(super) fn validate_shape(&self) -> Result<(), ProductionEcologyError> {
        let mut receivers = self.receiver_family.clone();
        receivers.sort_by_key(|receiver| *receiver as u8);
        receivers.dedup();
        if self.schema != PRODUCTION_INQUIRY_SCHEMA
            || self.occurrence != format!("r6/inquiry/{}", self.body_sha256()?)
            || !digest_text(&self.predecessor_rest_sha256)
            || self.presentation.natural_language.is_empty()
            || self.presentation.notation.is_empty()
            || !digest_text(&self.presentation.vector_face_sha256)
            || !digest_text(&self.presentation.raster_face_sha256)
            || self.presentation.prior_history_occurrences.is_empty()
            || self.context_word.is_empty()
            || receivers.len() != 5
            || self.requested_face.left_species == self.requested_face.right_species
            || self.requested_face.oriented_relation.is_empty()
            || self.requested_face.carrier.is_empty()
            || self.requested_face.unit.is_empty()
        {
            return Err(ProductionEcologyError::Inquiry);
        }
        Ok(())
    }
}
