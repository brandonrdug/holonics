//! N2's raw-waveform crossing and inherited Gemma audio projection.
//!
//! The WAV source is recovered by `life::mathematical_source`; no transcript enters this module.
//! The exact signed acoustic section then crosses the authenticated
//! `model.embed_audio.embedding_projection.weight` population on the resident card. The foreign
//! twelve-layer audio-tower interior is retained as an explicit open fibre rather than inferred
//! from the projection's success.

use std::path::{Path, PathBuf};

use holonic_engine::embedding_fiber::{AlignedMaterial, ResidentReadout};
use holonic_engine::foreign_map::manifest_safetensors;
use holonic_engine::phoenix::heterogeneous_fusion::{ModalityPort, SourcePortResponse};
use life::mathematical_source::ExactAcousticOccurrence;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const AUDIO_PROJECTION: &str = "model.embed_audio.embedding_projection.weight";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AudioProjectionReturn {
    pub family: u32,
    pub state: u32,
    pub source: ExactAcousticOccurrence,
    pub inherited_population: String,
    pub inherited_shape: [usize; 2],
    pub projection_scores: Vec<i128>,
    pub projection_exponent: i32,
    pub consequence_sha256: String,
    pub exact_multiply_accumulates: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AudioProjectionApparatus {
    pub resident_chart: String,
    pub inherited_population: String,
    pub inherited_weight_octets: u64,
    pub query_ingress_octets: u64,
    pub result_egress_octets: u64,
    pub resident_octets: u64,
    pub exact_multiply_accumulates: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AudioSourceConduct {
    pub schema: String,
    pub truth_status: String,
    pub returns: Vec<AudioProjectionReturn>,
    pub responses: Vec<SourcePortResponse>,
    pub apparatus: AudioProjectionApparatus,
    pub open_exterior: Vec<String>,
}

pub fn conduct(
    model_root: &Path,
    occurrences: &[(u32, u32, PathBuf)],
    frame_length: u32,
    frame_hop: u32,
) -> Result<AudioSourceConduct, String> {
    if occurrences.is_empty() {
        return Err("N2 audio conduct received no waveform occurrences".to_owned());
    }
    let locator = model_root.join("model.safetensors");
    let (mut file, container) = manifest_safetensors(
        locator
            .to_str()
            .ok_or_else(|| format!("non-UTF8 model locator {}", locator.display()))?,
    )
    .map_err(|error| error.to_string())?;
    let projection_tensor = container
        .tensor(AUDIO_PROJECTION)
        .map_err(|error| error.to_string())?;
    if projection_tensor.shape.len() != 2 {
        return Err("the inherited audio projection is not a matrix".to_owned());
    }
    let output_width = projection_tensor.shape[0];
    let input_width = projection_tensor.shape[1];
    let projection = container
        .read_bf16_whole(&mut file, AUDIO_PROJECTION)
        .map_err(|error| error.to_string())?;
    if projection.len() != output_width * input_width {
        return Err("the inherited audio projection population is ragged".to_owned());
    }

    let mut sources = Vec::with_capacity(occurrences.len());
    let mut queries = Vec::with_capacity(occurrences.len());
    for (family, state, path) in occurrences {
        let source = ExactAcousticOccurrence::read(
            path,
            format!("n2/audio/family-{family}/state-{state}"),
            frame_length,
            frame_hop,
            input_width,
        )
        .map_err(|error| error.to_string())?;
        let entry_octaves = source
            .section
            .iter()
            .map(|value| value.unsigned_abs().checked_ilog2().unwrap_or(0) + 1)
            .max()
            .unwrap_or(1);
        let negatives = source.section.iter().filter(|value| **value < 0).count() as u64;
        queries.push(AlignedMaterial {
            entries: source.section.clone(),
            exponent: 0,
            entry_octaves,
            negatives,
        });
        sources.push((*family, *state, source));
    }

    let chart = ResidentReadout::new().map_err(|error| error.to_string())?;
    let mounted = chart
        .mount_bfloat16(&projection, input_width)
        .map_err(|error| error.to_string())?;
    let borrowed = queries.iter().collect::<Vec<_>>();
    let projected = mounted
        .score_many(&borrowed)
        .map_err(|error| error.to_string())?;
    if projected.len() != occurrences.len()
        || projected
            .iter()
            .any(|returning| returning.scores.len() != output_width)
    {
        return Err("the inherited audio projection returned an incomplete family".to_owned());
    }

    let exact_work_per_occurrence = output_width
        .checked_mul(input_width)
        .and_then(|work| u64::try_from(work).ok())
        .ok_or_else(|| "the audio projection work extent overflowed".to_owned())?;
    let mut returns = Vec::with_capacity(projected.len());
    for ((family, state, source), returning) in sources.into_iter().zip(projected) {
        let mut identity = Sha256::new();
        identity.update(AUDIO_PROJECTION.as_bytes());
        identity.update(source.section_sha256.as_bytes());
        identity.update(returning.readout_exponent.to_le_bytes());
        for score in &returning.scores {
            identity.update(score.to_le_bytes());
        }
        returns.push(AudioProjectionReturn {
            family,
            state,
            source,
            inherited_population: AUDIO_PROJECTION.to_owned(),
            inherited_shape: [output_width, input_width],
            projection_scores: returning.scores,
            projection_exponent: returning.readout_exponent,
            consequence_sha256: hex(identity.finalize()),
            exact_multiply_accumulates: exact_work_per_occurrence,
        });
    }
    let responses = returns
        .iter()
        .map(|returning| SourcePortResponse {
            family: returning.family,
            state: returning.state,
            port: ModalityPort::AudioFrame,
            occurrence: returning.source.occurrence.clone(),
            occurrence_sha256: returning.source.source_sha256.clone(),
            consequence_sha256: returning.consequence_sha256.clone(),
            incidence_sha256: returning.source.incidence_sha256.clone(),
            semantic_units: returning.source.frames.len() as u64,
        })
        .collect::<Vec<_>>();
    let query_ingress_octets = queries
        .iter()
        .map(|query| query.entries.len() * std::mem::size_of::<i64>())
        .sum::<usize>() as u64;
    let result_egress_octets = returns
        .iter()
        .map(|returning| returning.projection_scores.len() * std::mem::size_of::<i128>())
        .sum::<usize>() as u64;
    Ok(AudioSourceConduct {
        schema: "holonics.n2.audio-source-conduct.v1".to_owned(),
        truth_status: "implemented-exact".to_owned(),
        returns,
        responses,
        apparatus: AudioProjectionApparatus {
            resident_chart: chart.device_name().to_owned(),
            inherited_population: AUDIO_PROJECTION.to_owned(),
            inherited_weight_octets: (projection.len() * std::mem::size_of::<u16>()) as u64,
            query_ingress_octets,
            result_egress_octets,
            resident_octets: mounted.resident_octets() as u64,
            exact_multiply_accumulates: exact_work_per_occurrence * occurrences.len() as u64,
        },
        open_exterior: vec![
            "the exact PCM/frame owner and inherited 1536→2560 Gemma audio projection are enacted; the stored twelve-layer foreign audio tower interior remains an explicit unexcited reconstruction fibre".to_owned(),
            "no transcript, filename word, or acoustic class selects the shared mathematical generator".to_owned(),
        ],
    })
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
