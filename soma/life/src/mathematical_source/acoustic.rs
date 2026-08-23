//! Exact PCM chronology at the mathematical-source mouth.
//!
//! A waveform is not text and this owner performs no transcription. It retains the mono PCM
//! occurrence, derives frame/sample incidence using the authenticated apparatus extents, and
//! returns one exact signed section for an inherited acoustic projection. The section is a
//! receiver quotient: the complete PCM population remains beside it as the reconstruction fibre.

use std::path::Path;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcousticFrame {
    pub ordinal: u32,
    pub sample_from: u32,
    pub sample_to: u32,
    pub signed_sum: i64,
    pub alternating_sum: i64,
    pub square_sum: u64,
}

/// One caused waveform occurrence and its complete source/quotient fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExactAcousticOccurrence {
    pub occurrence: String,
    pub locator: String,
    pub source_sha256: String,
    pub source_octets: u64,
    pub sample_rate: u32,
    pub frame_length: u32,
    pub frame_hop: u32,
    pub samples: Vec<i16>,
    pub frames: Vec<AcousticFrame>,
    pub incidence_sha256: String,
    pub section: Vec<i64>,
    pub section_sha256: String,
    pub open_exterior: Vec<String>,
}

impl ExactAcousticOccurrence {
    /// Read a mono signed-PCM occurrence and recover exact frame/sample incidence.
    ///
    /// `frame_length`, `frame_hop`, and `section_width` are authenticated apparatus/configuration
    /// extents supplied at the port. They are not semantic routing constants.
    pub fn read(
        path: &Path,
        occurrence: impl Into<String>,
        frame_length: u32,
        frame_hop: u32,
        section_width: usize,
    ) -> Result<Self, ExactAcousticRefusal> {
        let occurrence = occurrence.into();
        if occurrence.is_empty() {
            return Err(ExactAcousticRefusal::Occurrence);
        }
        if frame_length == 0 || frame_hop == 0 || section_width == 0 {
            return Err(ExactAcousticRefusal::Aperture);
        }
        let source = std::fs::read(path).map_err(|error| ExactAcousticRefusal::Io {
            path: path.display().to_string(),
            message: error.to_string(),
        })?;
        let mut reader =
            hound::WavReader::open(path).map_err(|error| ExactAcousticRefusal::Codec {
                path: path.display().to_string(),
                message: error.to_string(),
            })?;
        let spec = reader.spec();
        if spec.channels != 1
            || spec.bits_per_sample != 16
            || spec.sample_format != hound::SampleFormat::Int
            || spec.sample_rate == 0
        {
            return Err(ExactAcousticRefusal::PcmBoundary {
                channels: spec.channels,
                bits_per_sample: spec.bits_per_sample,
                sample_rate: spec.sample_rate,
            });
        }
        let samples = reader
            .samples::<i16>()
            .collect::<Result<Vec<_>, _>>()
            .map_err(|error| ExactAcousticRefusal::Codec {
                path: path.display().to_string(),
                message: error.to_string(),
            })?;
        if samples.is_empty() || samples.len() > u32::MAX as usize {
            return Err(ExactAcousticRefusal::Extent);
        }
        let frames = recover_frames(&samples, frame_length, frame_hop)?;
        let section = fold_section(&samples, section_width)?;
        let incidence_sha256 = incidence_identity(spec.sample_rate, &samples, &frames);
        let section_sha256 = signed_identity(&section);
        Ok(Self {
            occurrence,
            locator: path.display().to_string(),
            source_sha256: hex(Sha256::digest(&source)),
            source_octets: source.len() as u64,
            sample_rate: spec.sample_rate,
            frame_length,
            frame_hop,
            samples,
            frames,
            incidence_sha256,
            section,
            section_sha256,
            open_exterior: vec![
                "the exterior WAV header/padding byte presentation is retained by source identity, not reconstructed from the PCM fibre".to_owned(),
                "the exact signed section is not a transcript and does not claim the foreign audio tower's learned feature law".to_owned(),
            ],
        })
    }
}

fn recover_frames(
    samples: &[i16],
    frame_length: u32,
    frame_hop: u32,
) -> Result<Vec<AcousticFrame>, ExactAcousticRefusal> {
    let frame_length = frame_length as usize;
    let frame_hop = frame_hop as usize;
    let mut frames = Vec::new();
    let mut from = 0usize;
    while from < samples.len() {
        let to = from.saturating_add(frame_length).min(samples.len());
        let mut signed_sum = 0i64;
        let mut alternating_sum = 0i64;
        let mut square_sum = 0u64;
        for (local, sample) in samples[from..to].iter().copied().enumerate() {
            let sample = i64::from(sample);
            signed_sum = signed_sum
                .checked_add(sample)
                .ok_or(ExactAcousticRefusal::Extent)?;
            alternating_sum = alternating_sum
                .checked_add(if local & 1 == 0 { sample } else { -sample })
                .ok_or(ExactAcousticRefusal::Extent)?;
            square_sum = square_sum
                .checked_add(sample.unsigned_abs().pow(2))
                .ok_or(ExactAcousticRefusal::Extent)?;
        }
        frames.push(AcousticFrame {
            ordinal: frames.len() as u32,
            sample_from: from as u32,
            sample_to: to as u32,
            signed_sum,
            alternating_sum,
            square_sum,
        });
        if to == samples.len() {
            break;
        }
        from = from
            .checked_add(frame_hop)
            .ok_or(ExactAcousticRefusal::Extent)?;
    }
    Ok(frames)
}

/// Fold the full chronology through two coprime traversals. This is an exact receiver projection,
/// not a claim that the quotient is injective; `samples` retains the complete inverse image.
fn fold_section(samples: &[i16], width: usize) -> Result<Vec<i64>, ExactAcousticRefusal> {
    let mut section = vec![0i64; width];
    let reverse_step = width.saturating_sub(1).max(1);
    for (at, sample) in samples.iter().copied().enumerate() {
        let sample = i64::from(sample);
        let forward = at % width;
        let reverse = at
            .checked_mul(reverse_step)
            .ok_or(ExactAcousticRefusal::Extent)?
            % width;
        section[forward] = section[forward]
            .checked_add(sample)
            .ok_or(ExactAcousticRefusal::Extent)?;
        section[reverse] = section[reverse]
            .checked_add(if at & 1 == 0 { sample } else { -sample })
            .ok_or(ExactAcousticRefusal::Extent)?;
    }
    Ok(section)
}

fn incidence_identity(sample_rate: u32, samples: &[i16], frames: &[AcousticFrame]) -> String {
    let mut digest = Sha256::new();
    digest.update(sample_rate.to_le_bytes());
    digest.update((samples.len() as u64).to_le_bytes());
    for (at, sample) in samples.iter().copied().enumerate() {
        digest.update((at as u64).to_le_bytes());
        digest.update(sample.to_le_bytes());
        if at > 0 {
            digest.update((at as u64 - 1).to_le_bytes());
            digest.update((at as u64).to_le_bytes());
        }
    }
    for frame in frames {
        digest.update(frame.ordinal.to_le_bytes());
        digest.update(frame.sample_from.to_le_bytes());
        digest.update(frame.sample_to.to_le_bytes());
    }
    hex(digest.finalize())
}

fn signed_identity(values: &[i64]) -> String {
    let mut digest = Sha256::new();
    for value in values {
        digest.update(value.to_le_bytes());
    }
    hex(digest.finalize())
}

fn hex(bytes: impl AsRef<[u8]>) -> String {
    bytes
        .as_ref()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum ExactAcousticRefusal {
    #[error("the acoustic occurrence address is empty")]
    Occurrence,
    #[error("the acoustic frame or section aperture is empty")]
    Aperture,
    #[error("the acoustic occurrence extent overflowed")]
    Extent,
    #[error("{path} could not be read: {message}")]
    Io { path: String, message: String },
    #[error("{path} is not an admitted WAV occurrence: {message}")]
    Codec { path: String, message: String },
    #[error(
        "the acoustic boundary requires mono signed 16-bit PCM at a positive sample rate; received channels={channels}, bits={bits_per_sample}, rate={sample_rate}"
    )]
    PcmBoundary {
        channels: u16,
        bits_per_sample: u16,
        sample_rate: u32,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn framing_and_section_folding_are_exact_and_chronological() {
        let samples = [1i16, -2, 3, -4, 5];
        let frames = recover_frames(&samples, 3, 2).expect("bounded exact frames");
        assert_eq!(frames.len(), 2);
        assert_eq!((frames[0].sample_from, frames[0].sample_to), (0, 3));
        assert_eq!((frames[1].sample_from, frames[1].sample_to), (2, 5));
        assert_eq!(frames[0].signed_sum, 2);
        assert_eq!(frames[0].alternating_sum, 6);
        assert_eq!(frames[0].square_sum, 14);
        let section = fold_section(&samples, 3).expect("bounded exact fold");
        assert_eq!(section.len(), 3);
        assert_ne!(section, vec![0; 3]);
    }
}
