use holonic_engine::phoenix::inference_ecology::InferenceEcologyRest;

use super::super::{DynamicMorphologyRest, LongHorizonRetainedBoundary, MultimodalTransportRest};
use super::types::{ProductionAthenaError, ProductionComponentIdentity};
use super::wire::digest;

pub(super) fn component_identities(
    inference: &InferenceEcologyRest,
    morphology: &DynamicMorphologyRest,
    retained: &LongHorizonRetainedBoundary,
    media: &MultimodalTransportRest,
) -> Result<Vec<ProductionComponentIdentity>, ProductionAthenaError> {
    let components = vec![
        (
            "i5-recurrent-standing",
            inference
                .recurrent
                .standing_bytes()
                .map_err(|error| ProductionAthenaError::Inference(error.to_string()))?,
        ),
        (
            "i5-recurrent-decoder",
            inference
                .recurrent
                .decoder_bytes()
                .map_err(|error| ProductionAthenaError::Inference(error.to_string()))?,
        ),
        (
            "i5-recurrent-fibres",
            inference
                .recurrent
                .fibre_bytes()
                .map_err(|error| ProductionAthenaError::Inference(error.to_string()))?,
        ),
        (
            "i5-heterogeneous-standing",
            inference
                .heterogeneous
                .standing_bytes()
                .map_err(|error| ProductionAthenaError::Inference(error.to_string()))?,
        ),
        (
            "i5-heterogeneous-decoder",
            inference
                .heterogeneous
                .decoder_bytes()
                .map_err(|error| ProductionAthenaError::Inference(error.to_string()))?,
        ),
        (
            "i5-heterogeneous-fibres",
            inference
                .heterogeneous
                .fibre_bytes()
                .map_err(|error| ProductionAthenaError::Inference(error.to_string()))?,
        ),
        (
            "i5-inference-junction",
            inference
                .junction_bytes()
                .map_err(|error| ProductionAthenaError::Inference(error.to_string()))?,
        ),
        (
            "r3-dynamic-morphology",
            morphology
                .canonical_bytes()
                .map_err(|error| ProductionAthenaError::Morphology(error.to_string()))?,
        ),
        (
            "r4-retained-boundary-standing",
            retained
                .standing_bytes()
                .map_err(|error| ProductionAthenaError::Boundary(error.to_string()))?,
        ),
        (
            "r4-retained-boundary-decoder",
            retained
                .decoder_bytes()
                .map_err(|error| ProductionAthenaError::Boundary(error.to_string()))?,
        ),
        (
            "r4-retained-boundary-fibres",
            retained
                .fibre_bytes()
                .map_err(|error| ProductionAthenaError::Boundary(error.to_string()))?,
        ),
        (
            "r5-joint-media-standing",
            media
                .standing_bytes()
                .map_err(|error| ProductionAthenaError::Media(error.to_string()))?,
        ),
        (
            "r5-joint-media-decoder",
            media
                .decoder_bytes()
                .map_err(|error| ProductionAthenaError::Media(error.to_string()))?,
        ),
        (
            "r5-joint-media-fibres",
            media
                .fibre_bytes()
                .map_err(|error| ProductionAthenaError::Media(error.to_string()))?,
        ),
    ];
    Ok(components
        .into_iter()
        .map(|(role, bytes)| ProductionComponentIdentity {
            role: role.to_owned(),
            sha256: digest(&bytes),
            octets: bytes.len() as u64,
        })
        .collect())
}
