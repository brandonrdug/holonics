//! Exact finite image testimony at a world membrane.
//!
//! A raster is an observation carrier, not the engine's world geometry.
//! Production laws may derive continuous or combinatorial structure from
//! these samples, but a sample address is never silently promoted into a
//! physical cell.

use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct ExactRgb {
    pub red: u8,
    pub green: u8,
    pub blue: u8,
}

impl ExactRgb {
    pub fn channels(self) -> [u8; 3] {
        [self.red, self.green, self.blue]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ImageExtent {
    pub width: u32,
    pub height: u32,
}

impl ImageExtent {
    pub fn sample_count(self) -> Result<usize, ImageCarrierError> {
        let count = u64::from(self.width)
            .checked_mul(u64::from(self.height))
            .ok_or(ImageCarrierError::CarrierOverflow)?;
        usize::try_from(count).map_err(|_| ImageCarrierError::CarrierOverflow)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactRaster {
    pub schema: String,
    pub extent: ImageExtent,
    pub samples: Vec<ExactRgb>,
}

impl ExactRaster {
    pub fn new(extent: ImageExtent, samples: Vec<ExactRgb>) -> Result<Self, ImageCarrierError> {
        if extent.width == 0 || extent.height == 0 {
            return Err(ImageCarrierError::EmptyRaster);
        }
        let expected = extent.sample_count()?;
        if samples.len() != expected {
            return Err(ImageCarrierError::RasterSampleCount {
                expected,
                received: samples.len(),
            });
        }
        Ok(Self {
            schema: "holonic-engine.exact-raster.v1".to_owned(),
            extent,
            samples,
        })
    }

    pub fn sample(&self, column: u32, row: u32) -> Option<ExactRgb> {
        sample_ordinal(self.extent, column, row)
            .ok()
            .and_then(|ordinal| self.samples.get(ordinal).copied())
    }

    pub fn channel_sums(&self) -> [u64; 3] {
        self.samples.iter().fold([0_u64; 3], |mut sums, sample| {
            for (sum, value) in sums.iter_mut().zip(sample.channels()) {
                *sum += u64::from(value);
            }
            sums
        })
    }
}

pub(crate) fn sample_ordinal(
    extent: ImageExtent,
    column: u32,
    row: u32,
) -> Result<usize, ImageCarrierError> {
    if column >= extent.width || row >= extent.height {
        return Err(ImageCarrierError::SampleOutsideExtent { column, row });
    }
    let ordinal = u64::from(row)
        .checked_mul(u64::from(extent.width))
        .and_then(|value| value.checked_add(u64::from(column)))
        .ok_or(ImageCarrierError::CarrierOverflow)?;
    usize::try_from(ordinal).map_err(|_| ImageCarrierError::CarrierOverflow)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ImageCarrierError {
    #[error("an exact raster must have a positive extent")]
    EmptyRaster,
    #[error("the raster expected {expected} samples but received {received}")]
    RasterSampleCount { expected: usize, received: usize },
    #[error("sample ({column},{row}) lies outside the raster extent")]
    SampleOutsideExtent { column: u32, row: u32 },
    #[error("an image carrier count overflowed its exact finite representation")]
    CarrierOverflow,
}
