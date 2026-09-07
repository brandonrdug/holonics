//! Reversible UTF-8 octet excitation at the native field boundary.
//!
//! The octet chart supplies addresses only. Every bit position has two native input channels;
//! exactly one channel receives the same unit impulse for every octet. The field's resident
//! constitutive law produces the outgoing and held currents. This module does not make a native
//! text emission, assign semantic values to bytes, or select a response.

use holonic_engine::{
    embedding_fiber::ResidentReadout,
    native_ecology::constitutive_fibre::{
        ConstitutiveFibreError, NativeConstitutiveField, NativeJunctionSeed,
    },
    resident_section::ResidentSurface,
};
use thiserror::Error;

pub const OCTET_BIT_POSITIONS: usize = 8;
pub const OCTET_INPUT_CHANNELS: usize = OCTET_BIT_POSITIONS * 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OctetExcitation {
    octet: u8,
    channels: [u8; OCTET_BIT_POSITIONS],
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum OctetExcitationError {
    #[error("octet excitation has {0} input channels; expected {OCTET_INPUT_CHANNELS}")]
    InputLength(usize),
    #[error("octet excitation channel {channel} is outside bit pair {bit}")]
    ChannelAddress { bit: usize, channel: u8 },
    #[error("octet excitation channel {channel} is neither the unit nor zero impulse")]
    ChannelCurrent { channel: usize },
    #[error(
        "octet excitation channel chart disagrees at bit {bit}: octet {octet}, channel {channel}"
    )]
    ChartMismatch { bit: usize, octet: u8, channel: u8 },
}

impl OctetExcitation {
    pub fn from_octet(octet: u8) -> Self {
        let channels = std::array::from_fn(|bit| 2 * bit as u8 + ((octet >> bit) & 1));
        Self { octet, channels }
    }

    /// Reconstruct the octet from the addressed one-of-two channel for each bit.
    pub fn from_channels(
        channels: [u8; OCTET_BIT_POSITIONS],
    ) -> Result<Self, OctetExcitationError> {
        for (bit, channel) in channels.iter().copied().enumerate() {
            let pair_start = 2 * bit as u8;
            if channel != pair_start && channel != pair_start + 1 {
                return Err(OctetExcitationError::ChannelAddress { bit, channel });
            }
        }
        let octet = channels
            .iter()
            .enumerate()
            .fold(0u8, |value, (bit, channel)| {
                value | (((channel & 1) as u8) << bit)
            });
        let excitation = Self { octet, channels };
        excitation.validate()?;
        Ok(excitation)
    }

    /// Recover this excitation chart from the complete 16-channel native input field.
    pub fn from_inputs(
        inputs: &[holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent],
    ) -> Result<Self, OctetExcitationError> {
        if inputs.len() != OCTET_INPUT_CHANNELS {
            return Err(OctetExcitationError::InputLength(inputs.len()));
        }
        let unit = holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::unit();
        let zero = holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::zero();
        let mut channels = [0u8; OCTET_BIT_POSITIONS];
        for bit in 0..OCTET_BIT_POSITIONS {
            let left = 2 * bit;
            let right = left + 1;
            let left_unit = inputs[left] == unit;
            let right_unit = inputs[right] == unit;
            let left_zero = inputs[left] == zero;
            let right_zero = inputs[right] == zero;
            if left_unit && right_zero {
                channels[bit] = left as u8;
            } else if left_zero && right_unit {
                channels[bit] = right as u8;
            } else {
                return Err(OctetExcitationError::ChannelCurrent { channel: left });
            }
        }
        Self::from_channels(channels)
    }

    pub fn octet(&self) -> u8 {
        self.octet
    }

    pub fn channels(&self) -> [u8; OCTET_BIT_POSITIONS] {
        self.channels
    }

    /// Convert the chart to the complete 16-port field: one unit and one zero per bit pair.
    pub fn inputs(
        &self,
    ) -> Vec<holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent> {
        let unit = holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::unit();
        let zero = holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::zero();
        let mut inputs = vec![zero; OCTET_INPUT_CHANNELS];
        for channel in self.channels {
            inputs[channel as usize] = unit;
        }
        inputs
    }

    pub fn validate(&self) -> Result<(), OctetExcitationError> {
        for (bit, channel) in self.channels.iter().copied().enumerate() {
            let expected = 2 * bit as u8 + ((self.octet >> bit) & 1);
            if channel != expected {
                return Err(OctetExcitationError::ChartMismatch {
                    bit,
                    octet: self.octet,
                    channel,
                });
            }
        }
        Ok(())
    }
}

/// A matched 16-port field seed. The native field derives outgoing and held currents from this
/// standing material and the complete incoming field; no byte value enters the seed.
pub fn matched_unit_field_seed() -> Vec<NativeJunctionSeed> {
    (0..OCTET_INPUT_CHANNELS)
        .map(|_| NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport:
                holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::unit(),
            initial_held:
                holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::zero(),
        })
        .collect()
}

#[derive(Debug, Error)]
pub enum AlphaMaterialError {
    #[error("native constitutive field: {0}")]
    Native(#[from] ConstitutiveFibreError),
    #[error("native apparatus: {0}")]
    Apparatus(String),
    #[error("octet excitation: {0}")]
    Excitation(#[from] OctetExcitationError),
    #[error("conversation exposure: {0}")]
    Exposure(String),
}

/// Mount one matched 16-port `NativeConstitutiveField` and run a callback on that same owner.
pub fn with_octet_field<R>(
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, AlphaMaterialError>,
) -> Result<R, AlphaMaterialError> {
    with_octet_field_profile(false, operation)
}

/// Mount the same exterior chart on the developing paired passive junction.
pub fn with_paired_octet_field<R>(
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, AlphaMaterialError>,
) -> Result<R, AlphaMaterialError> {
    with_octet_field_profile(true, operation)
}

fn with_octet_field_profile<R>(
    paired: bool,
    operation: impl FnOnce(&mut NativeConstitutiveField<'_>) -> Result<R, AlphaMaterialError>,
) -> Result<R, AlphaMaterialError> {
    let readout =
        ResidentReadout::new().map_err(|error| AlphaMaterialError::Apparatus(error.to_string()))?;
    let surface = ResidentSurface::on(&readout)
        .map_err(|error| AlphaMaterialError::Apparatus(error.to_string()))?;
    let mut field = if paired {
        NativeConstitutiveField::found_with_paired_junction(&surface, matched_unit_field_seed())?
    } else {
        NativeConstitutiveField::found(&surface, matched_unit_field_seed())?
    };
    operation(&mut field)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_octet_round_trips_through_the_excitation_chart() {
        for octet in 0..=u8::MAX {
            let excitation = OctetExcitation::from_octet(octet);
            excitation.validate().unwrap();
            let inverse = OctetExcitation::from_channels(excitation.channels()).unwrap();
            assert_eq!(inverse.octet(), octet);
            let from_inputs = OctetExcitation::from_inputs(&excitation.inputs()).unwrap();
            assert_eq!(from_inputs, excitation);
        }
    }

    #[test]
    fn every_octet_has_the_same_eight_unit_impulses() {
        let unit = holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::unit();
        let zero = holonic_engine::native_ecology::constitutive_fibre::NativePhaseCurrent::zero();
        for octet in [0, 1, 0x55, 0xaa, u8::MAX] {
            let inputs = OctetExcitation::from_octet(octet).inputs();
            assert_eq!(inputs.iter().filter(|current| **current == unit).count(), 8);
            assert_eq!(inputs.iter().filter(|current| **current == zero).count(), 8);
            for pair in inputs.chunks_exact(2) {
                assert_eq!(pair.iter().filter(|current| **current == unit).count(), 1);
            }
        }
    }
}
