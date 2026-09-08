//! Exact two-channel PCM reception for an ordered temporal complex current.
//!
//! This is a cold exterior receiver.  One complex current is one PCM frame: its real and
//! imaginary coordinates occupy the two channels at the caller's declared sample clock.  The
//! native current remains the carrier, while quantization and clipping are retained as an exact
//! rational residual in the receiver record.

use std::io::Cursor;

use holonic_engine::{
    phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId},
    ExactComplexWaveCurrent,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::Signed;
use serde::{Deserialize, Serialize};

use super::NativeAcousticError;

pub const NATIVE_ACOUSTIC_TEMPORAL_PCM16_SCHEMA: &str =
    "soma-life.native-acoustic-temporal-pcm16.v1";

/// One exact temporal complex carrier and its two-channel PCM quotient.
///
/// `remainder` is in caller PCM units: for each coordinate,
/// `carrier * gain = pcm + remainder`.  It therefore retains the exact value even when the
/// exterior i16 quotient clips at a signed-16 endpoint.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticTemporalPcm16Frame {
    pub carrier: ExactComplexWaveCurrent,
    pub pcm: [i16; 2],
    pub remainder: ExactComplexWaveCurrent,
    pub clipped: [bool; 2],
}

/// A cold two-channel PCM receiver with caller-declared digital gain for temporal coordinates.
///
/// The receiver does not create native events or inspect a learner.  `frames` retain the complete
/// exact carrier and quotient fibre, while the WAV face presents real and imaginary coordinates as
/// channels 0 and 1 at exactly one frame per input coefficient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticTemporalPcm16Projection {
    pub schema: String,
    pub receiver: PhaseCurrentReceiverId,
    pub lineage: PhaseCurrentLineageId,
    pub origin: Rat,
    pub sample_step: Rat,
    pub sample_rate: u32,
    /// Positive caller-declared PCM units per native-current unit; no physical SPL calibration.
    pub gain: Rat,
    pub frames: Vec<NativeAcousticTemporalPcm16Frame>,
    pub clipped_sample_population: usize,
}

impl NativeAcousticTemporalPcm16Projection {
    /// Quantize one ordered complex coefficient per PCM frame.
    pub fn found(
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        sample_rate: u32,
        gain: Rat,
        coordinates: &[ExactComplexWaveCurrent],
    ) -> Result<Self, NativeAcousticError> {
        if sample_rate == 0 {
            return Err(NativeAcousticError::Pcm(
                "the temporal PCM receiver requires a positive sample rate".to_owned(),
            ));
        }
        if !sample_step.is_positive()
            || sample_step != Rat::new(BigInt::from(1), BigInt::from(sample_rate))
        {
            return Err(NativeAcousticError::Pcm(
                "the temporal PCM clock must equal one over the sample rate".to_owned(),
            ));
        }
        if !gain.is_positive() {
            return Err(NativeAcousticError::Pcm(
                "the temporal PCM gain must be positive".to_owned(),
            ));
        }
        if coordinates.is_empty() {
            return Err(NativeAcousticError::Pcm(
                "the temporal PCM receiver requires one or more coordinates".to_owned(),
            ));
        }

        let mut frames = Vec::with_capacity(coordinates.len());
        let mut clipped_sample_population = 0_usize;
        for carrier in coordinates {
            let (real, real_clipped) = quantize(&carrier.real, &gain)?;
            let (imaginary, imaginary_clipped) = quantize(&carrier.imaginary, &gain)?;
            clipped_sample_population += usize::from(real_clipped) + usize::from(imaginary_clipped);
            frames.push(NativeAcousticTemporalPcm16Frame {
                carrier: carrier.clone(),
                pcm: [real.sample, imaginary.sample],
                remainder: ExactComplexWaveCurrent::new(real.remainder, imaginary.remainder),
                clipped: [real_clipped, imaginary_clipped],
            });
        }
        let projection = Self {
            schema: NATIVE_ACOUSTIC_TEMPORAL_PCM16_SCHEMA.to_owned(),
            receiver,
            lineage,
            origin,
            sample_step,
            sample_rate,
            gain,
            frames,
            clipped_sample_population,
        };
        projection.validate()?;
        Ok(projection)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        if self.schema != NATIVE_ACOUSTIC_TEMPORAL_PCM16_SCHEMA
            || self.sample_rate == 0
            || !self.sample_step.is_positive()
            || self.sample_step != Rat::new(BigInt::from(1), BigInt::from(self.sample_rate))
            || !self.gain.is_positive()
            || self.frames.is_empty()
        {
            return Err(NativeAcousticError::Pcm(
                "the temporal PCM receiver has invalid chart or carrier metadata".to_owned(),
            ));
        }

        let mut clipped_sample_population = 0_usize;
        for frame in &self.frames {
            let (real, real_clipped) = quantize(&frame.carrier.real, &self.gain)?;
            let (imaginary, imaginary_clipped) = quantize(&frame.carrier.imaginary, &self.gain)?;
            if frame.pcm != [real.sample, imaginary.sample]
                || frame.remainder
                    != ExactComplexWaveCurrent::new(real.remainder, imaginary.remainder)
                || frame.clipped != [real_clipped, imaginary_clipped]
            {
                return Err(NativeAcousticError::Pcm(
                    "the temporal PCM receiver lost its exact quotient fibre".to_owned(),
                ));
            }
            clipped_sample_population += usize::from(real_clipped) + usize::from(imaginary_clipped);
        }
        if clipped_sample_population != self.clipped_sample_population {
            return Err(NativeAcousticError::Pcm(
                "the temporal PCM clipping receipt does not match its carriers".to_owned(),
            ));
        }
        Ok(())
    }

    /// Reconstruct every exact carrier from the two PCM channels and retained residuals.
    pub fn reconstructed_carriers(
        &self,
    ) -> Result<Vec<ExactComplexWaveCurrent>, NativeAcousticError> {
        self.validate()?;
        Ok(self
            .frames
            .iter()
            .map(|frame| {
                ExactComplexWaveCurrent::new(
                    (Rat::from_integer(BigInt::from(frame.pcm[0])) + &frame.remainder.real)
                        / &self.gain,
                    (Rat::from_integer(BigInt::from(frame.pcm[1])) + &frame.remainder.imaginary)
                        / &self.gain,
                )
            })
            .collect())
    }

    /// Write the exterior two-channel signed-16 presentation, one frame per carrier.
    pub fn wav_bytes(&self) -> Result<Vec<u8>, NativeAcousticError> {
        self.validate()?;
        let specification = hound::WavSpec {
            channels: 2,
            sample_rate: self.sample_rate,
            bits_per_sample: 16,
            sample_format: hound::SampleFormat::Int,
        };
        let mut bytes = Vec::new();
        {
            let cursor = Cursor::new(&mut bytes);
            let mut writer = hound::WavWriter::new(cursor, specification)
                .map_err(|error| NativeAcousticError::Pcm(error.to_string()))?;
            for frame in &self.frames {
                writer
                    .write_sample(frame.pcm[0])
                    .map_err(|error| NativeAcousticError::Pcm(error.to_string()))?;
                writer
                    .write_sample(frame.pcm[1])
                    .map_err(|error| NativeAcousticError::Pcm(error.to_string()))?;
            }
            writer
                .finalize()
                .map_err(|error| NativeAcousticError::Pcm(error.to_string()))?;
        }
        Ok(bytes)
    }
}

struct QuantizedCoordinate {
    sample: i16,
    remainder: Rat,
}

fn quantize(value: &Rat, gain: &Rat) -> Result<(QuantizedCoordinate, bool), NativeAcousticError> {
    let scaled = value * gain;
    let toward_zero = scaled.to_integer();
    let minimum = BigInt::from(i16::MIN);
    let maximum = BigInt::from(i16::MAX);
    let (sample_integer, clipped) = if toward_zero < minimum {
        (minimum, true)
    } else if toward_zero > maximum {
        (maximum, true)
    } else {
        (toward_zero, false)
    };
    let sample = i16::try_from(sample_integer.clone()).map_err(|_| NativeAcousticError::Extent)?;
    let remainder = scaled - Rat::from_integer(sample_integer);
    Ok((QuantizedCoordinate { sample, remainder }, clipped))
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::{One, Zero};

    fn q(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn current(real: Rat, imaginary: Rat) -> ExactComplexWaveCurrent {
        ExactComplexWaveCurrent::new(real, imaginary)
    }

    #[test]
    fn signed_fractional_coordinates_retain_both_quadratures() {
        let projection = NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(7),
            PhaseCurrentLineageId(9),
            Rat::zero(),
            q(1, 16_000),
            16_000,
            q(2, 3),
            &[current(q(3, 2), q(-5, 3))],
        )
        .unwrap();
        assert_eq!(projection.frames[0].pcm, [1, -1]);
        assert_eq!(projection.frames[0].remainder.real, Rat::zero());
        assert_eq!(projection.frames[0].remainder.imaginary, q(-1, 9));
        assert_eq!(
            projection.reconstructed_carriers().unwrap()[0],
            current(q(3, 2), q(-5, 3))
        );
    }

    #[test]
    fn zero_current_is_silence_and_wav_has_two_channels() {
        let projection = NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 8_000),
            8_000,
            Rat::one(),
            &[ExactComplexWaveCurrent::zero(), current(q(2, 1), q(-3, 1))],
        )
        .unwrap();
        assert_eq!(projection.frames[0].pcm, [0, 0]);
        let reader = hound::WavReader::new(Cursor::new(projection.wav_bytes().unwrap())).unwrap();
        assert_eq!(reader.spec().channels, 2);
        assert_eq!(reader.spec().sample_rate, 8_000);
        assert_eq!(reader.duration(), 2);
    }

    #[test]
    fn clipping_is_reported_and_residual_reconstructs_exact_coordinates() {
        let projection = NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 44_100),
            44_100,
            Rat::one(),
            &[current(q(40_000, 1), q(-40_000, 1))],
        )
        .unwrap();
        assert_eq!(projection.frames[0].pcm, [i16::MAX, i16::MIN]);
        assert_eq!(projection.clipped_sample_population, 2);
        assert_eq!(
            projection.reconstructed_carriers().unwrap()[0],
            current(q(40_000, 1), q(-40_000, 1))
        );
    }

    #[test]
    fn altered_receipt_metadata_is_refused() {
        let mut projection = NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 16_000),
            16_000,
            Rat::one(),
            &[current(q(3, 2), q(-5, 3))],
        )
        .unwrap();
        projection.frames[0].remainder.real += Rat::one();
        assert!(projection.validate().is_err());
        assert!(projection.reconstructed_carriers().is_err());

        let mut projection = NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 16_000),
            16_000,
            Rat::one(),
            &[current(q(3, 2), q(-5, 3))],
        )
        .unwrap();
        projection.frames[0].pcm[1] = 0;
        assert!(projection.validate().is_err());

        let mut projection = NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            q(1, 16_000),
            16_000,
            Rat::one(),
            &[current(q(3, 2), q(-5, 3))],
        )
        .unwrap();
        projection.frames[0].clipped[0] = true;
        assert!(projection.validate().is_err());
    }

    #[test]
    fn invalid_gain_clock_and_empty_carrier_are_refused() {
        let coordinate = [current(Rat::one(), Rat::zero())];
        assert!(NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(1),
            Rat::zero(),
            q(1, 16_000),
            16_000,
            Rat::zero(),
            &coordinate,
        )
        .is_err());
        assert!(NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(1),
            Rat::zero(),
            q(1, 8_000),
            16_000,
            Rat::one(),
            &coordinate,
        )
        .is_err());
        assert!(NativeAcousticTemporalPcm16Projection::found(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(1),
            Rat::zero(),
            q(1, 16_000),
            16_000,
            Rat::one(),
            &[],
        )
        .is_err());
    }
}
