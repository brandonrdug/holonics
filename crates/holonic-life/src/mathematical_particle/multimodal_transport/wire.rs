use serde::{Deserialize, Serialize};

use super::{
    types::{
        ExactSpatialDeclaration, JointMediaDecoder, MathematicalMediaPort, MediaSourceInterior,
        NativeMediaConsequence,
    },
    validation::MultimodalTransportRefusal,
};

const DECODER_WIRE: &[u8] = b"HOLONICS-R5-JOINT-MEDIA-DECODER\0";

#[derive(Serialize, Deserialize)]
struct DecoderInteriorHeader {
    family: u32,
    port: MathematicalMediaPort,
    artifact_occurrence: String,
    artifact_sha256: String,
    chart: String,
    occurrence_population: u32,
    contact_population: u32,
    incidence_sha256: String,
    spatial: ExactSpatialDeclaration,
    canonical_octets: u64,
}

#[derive(Serialize, Deserialize)]
struct DecoderHeader {
    schema: String,
    consequences: Vec<NativeMediaConsequence>,
    interiors: Vec<DecoderInteriorHeader>,
}

pub(super) fn encode_decoder(
    decoder: &JointMediaDecoder,
) -> Result<Vec<u8>, MultimodalTransportRefusal> {
    let header = DecoderHeader {
        schema: decoder.schema.clone(),
        consequences: decoder.consequences.clone(),
        interiors: decoder
            .interiors
            .iter()
            .map(|interior| DecoderInteriorHeader {
                family: interior.family,
                port: interior.port,
                artifact_occurrence: interior.artifact_occurrence.clone(),
                artifact_sha256: interior.artifact_sha256.clone(),
                chart: interior.chart.clone(),
                occurrence_population: interior.occurrence_population,
                contact_population: interior.contact_population,
                incidence_sha256: interior.incidence_sha256.clone(),
                spatial: interior.spatial.clone(),
                canonical_octets: interior.canonical_interior.len() as u64,
            })
            .collect(),
    };
    let header = serde_json::to_vec(&header)
        .map_err(|error| MultimodalTransportRefusal::Wire(error.to_string()))?;
    let mut wire = Vec::with_capacity(
        DECODER_WIRE.len()
            + 8
            + header.len()
            + decoder
                .interiors
                .iter()
                .map(|interior| 8 + interior.canonical_interior.len())
                .sum::<usize>(),
    );
    wire.extend_from_slice(DECODER_WIRE);
    wire.extend_from_slice(&(header.len() as u64).to_le_bytes());
    wire.extend_from_slice(&header);
    for interior in &decoder.interiors {
        wire.extend_from_slice(&(interior.canonical_interior.len() as u64).to_le_bytes());
        wire.extend_from_slice(&interior.canonical_interior);
    }
    Ok(wire)
}

pub(super) fn decode_decoder(wire: &[u8]) -> Result<JointMediaDecoder, MultimodalTransportRefusal> {
    if !wire.starts_with(DECODER_WIRE) {
        return Err(MultimodalTransportRefusal::Decoder);
    }
    let mut at = DECODER_WIRE.len();
    let header_octets = take_u64(wire, &mut at)? as usize;
    let header_end = at
        .checked_add(header_octets)
        .ok_or(MultimodalTransportRefusal::Extent)?;
    let header: DecoderHeader = serde_json::from_slice(
        wire.get(at..header_end)
            .ok_or(MultimodalTransportRefusal::Decoder)?,
    )
    .map_err(|error| MultimodalTransportRefusal::Wire(error.to_string()))?;
    at = header_end;
    let mut interiors = Vec::with_capacity(header.interiors.len());
    for source in header.interiors {
        let octets = take_u64(wire, &mut at)? as usize;
        if octets != source.canonical_octets as usize {
            return Err(MultimodalTransportRefusal::Decoder);
        }
        let end = at
            .checked_add(octets)
            .ok_or(MultimodalTransportRefusal::Extent)?;
        let canonical_interior = wire
            .get(at..end)
            .ok_or(MultimodalTransportRefusal::Decoder)?
            .to_vec();
        at = end;
        interiors.push(MediaSourceInterior {
            family: source.family,
            port: source.port,
            artifact_occurrence: source.artifact_occurrence,
            artifact_sha256: source.artifact_sha256,
            chart: source.chart,
            occurrence_population: source.occurrence_population,
            contact_population: source.contact_population,
            incidence_sha256: source.incidence_sha256,
            spatial: source.spatial,
            canonical_interior,
        });
    }
    if at != wire.len() {
        return Err(MultimodalTransportRefusal::Decoder);
    }
    Ok(JointMediaDecoder {
        schema: header.schema,
        consequences: header.consequences,
        interiors,
    })
}

fn take_u64(wire: &[u8], at: &mut usize) -> Result<u64, MultimodalTransportRefusal> {
    let end = at
        .checked_add(8)
        .ok_or(MultimodalTransportRefusal::Extent)?;
    let bytes: [u8; 8] = wire
        .get(*at..end)
        .ok_or(MultimodalTransportRefusal::Decoder)?
        .try_into()
        .map_err(|_| MultimodalTransportRefusal::Decoder)?;
    *at = end;
    Ok(u64::from_le_bytes(bytes))
}
