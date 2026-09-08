//! PCM16 projection of a global Euclidean enclosure around an ordered temporal current.
//!
//! The PCM face stores a numerical representative of the ball centre together with its exact
//! quotient remainder.  The representative is never admitted as a native point current.  The
//! retained radius remains global across all realified quadratures and reconstructs the complete
//! enclosure after the cold receiver round trip.

use holonic_engine::{
    ExactComplexWaveCurrent,
    native_ecology::constitutive_fibre::NativeFieldCurrentBall,
    phase_current::{PhaseCurrentLineageId, PhaseCurrentReceiverId},
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use num_traits::Signed;
use serde::{Deserialize, Serialize};

use super::{
    NativeAcousticError,
    temporal_receiver::{pcm_wav_bytes, quantize},
};

pub const NATIVE_ACOUSTIC_ENCLOSED_TEMPORAL_PCM16_SCHEMA: &str =
    "soma-life.native-acoustic-enclosed-temporal-pcm16.v1";

/// One numerical representative frame of an enclosed current.
///
/// `representative` is a receiver coordinate, not an exact native current.  The exact quotient
/// relation is retained by `pcm + remainder = representative * gain`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticEnclosedTemporalPcm16Frame {
    pub representative: ExactComplexWaveCurrent,
    pub pcm: [i16; 2],
    pub remainder: ExactComplexWaveCurrent,
    pub clipped: [bool; 2],
}

/// Cold PCM projection of a complete global Euclidean current enclosure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticEnclosedTemporalPcm16Projection {
    pub schema: String,
    pub receiver: PhaseCurrentReceiverId,
    pub lineage: PhaseCurrentLineageId,
    pub origin: Rat,
    pub sample_step: Rat,
    pub sample_rate: u32,
    pub gain: Rat,
    /// Global Euclidean radius in native current units.  Its PCM-coordinate uncertainty is the
    /// same global radius multiplied by `gain`; the WAV face alone does not retain that fibre.
    pub radius: Rat,
    pub frames: Vec<NativeAcousticEnclosedTemporalPcm16Frame>,
    pub clipped_sample_population: usize,
}

impl NativeAcousticEnclosedTemporalPcm16Projection {
    /// Project the ball centre to PCM while retaining the complete global radius.
    pub fn found(
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        sample_rate: u32,
        gain: Rat,
        ball: &NativeFieldCurrentBall,
    ) -> Result<Self, NativeAcousticError> {
        if ball.center.is_empty() || ball.radius < Rat::from_integer(0.into()) {
            return Err(NativeAcousticError::Pcm(
                "the enclosed temporal receiver requires a nonnegative nonempty ball".to_owned(),
            ));
        }
        let mut frames = Vec::with_capacity(ball.center.len());
        let mut clipped_sample_population = 0_usize;
        for representative in &ball.center {
            let (real, real_clipped) = quantize(&representative.real, &gain)?;
            let (imaginary, imaginary_clipped) = quantize(&representative.imaginary, &gain)?;
            clipped_sample_population += usize::from(real_clipped) + usize::from(imaginary_clipped);
            frames.push(NativeAcousticEnclosedTemporalPcm16Frame {
                representative: representative.clone(),
                pcm: [real.sample, imaginary.sample],
                remainder: ExactComplexWaveCurrent::new(real.remainder, imaginary.remainder),
                clipped: [real_clipped, imaginary_clipped],
            });
        }
        let projection = Self {
            schema: NATIVE_ACOUSTIC_ENCLOSED_TEMPORAL_PCM16_SCHEMA.to_owned(),
            receiver,
            lineage,
            origin,
            sample_step,
            sample_rate,
            gain,
            radius: ball.radius.clone(),
            frames,
            clipped_sample_population,
        };
        projection.validate()?;
        Ok(projection)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        if self.schema != NATIVE_ACOUSTIC_ENCLOSED_TEMPORAL_PCM16_SCHEMA
            || self.sample_rate == 0
            || !self.sample_step.is_positive()
            || self.sample_step != Rat::new(BigInt::from(1), BigInt::from(self.sample_rate))
            || !self.gain.is_positive()
            || self.radius < Rat::from_integer(0.into())
            || self.frames.is_empty()
        {
            return Err(NativeAcousticError::Pcm(
                "the enclosed temporal PCM receiver has invalid chart or ball metadata".to_owned(),
            ));
        }
        let mut clipped_sample_population = 0_usize;
        for frame in &self.frames {
            let (real, real_clipped) = quantize(&frame.representative.real, &self.gain)?;
            let (imaginary, imaginary_clipped) =
                quantize(&frame.representative.imaginary, &self.gain)?;
            if frame.pcm != [real.sample, imaginary.sample]
                || frame.remainder
                    != ExactComplexWaveCurrent::new(real.remainder, imaginary.remainder)
                || frame.clipped != [real_clipped, imaginary_clipped]
            {
                return Err(NativeAcousticError::Pcm(
                    "the enclosed temporal PCM quotient fibre is inconsistent".to_owned(),
                ));
            }
            clipped_sample_population += usize::from(real_clipped) + usize::from(imaginary_clipped);
        }
        if clipped_sample_population != self.clipped_sample_population {
            return Err(NativeAcousticError::Pcm(
                "the enclosed temporal clipping receipt does not match its representatives"
                    .to_owned(),
            ));
        }
        Ok(())
    }

    /// Reconstruct the complete ball from the PCM representative and exact quotient remainder.
    pub fn reconstructed_enclosure(&self) -> Result<NativeFieldCurrentBall, NativeAcousticError> {
        self.validate()?;
        let center = self
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
            .collect();
        Ok(NativeFieldCurrentBall {
            center,
            radius: self.radius.clone(),
        })
    }

    /// Write only the PCM representative. The radius and quotient fibre stay in this record, so a
    /// WAV consumer without this record cannot reconstruct the enclosure or exact remainder.
    pub fn wav_bytes(&self) -> Result<Vec<u8>, NativeAcousticError> {
        self.validate()?;
        pcm_wav_bytes(self.sample_rate, self.frames.iter().map(|frame| frame.pcm))
    }
}

#[cfg(test)]
mod tests;
