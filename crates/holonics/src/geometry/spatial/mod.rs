//! Exact finite spatial boundary charts (Refs #73, #148, #62).
//!
//! [agent-inferred, October 15] A raster is an exterior receiver's samples on a declared
//! rectangular chart, not a learned representation or a digit-recognition law. Coordinates,
//! oriented neighbours and sample values remain separate. Translation retains its lost support;
//! quarter turns permute samples exactly. Neither operation asserts label invariance. General
//! resampling and its unresolved fibre are deliberately not silently supplied.
//!
//! The existing `AffineMap3` owns coordinate recharting and `CellComplex` owns incidence.
//! These finite permutation/translation witnesses have executable tests; their general Lean
//! consumer bridge remains an obligation under #62. No new HNN dynamics are introduced here.

pub mod idx;
mod placed;
pub use placed::{PlacedRaster, PlacedRasterSlice};

use super::{AffineMap3, RatVec3};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SpatialError {
    #[error("a spatial extent must be nonempty and its area fit usize")]
    Extent,
    #[error("raster length {found} does not match chart area {expected}")]
    Length { expected: usize, found: usize },
    #[error("coordinate is outside the declared spatial chart")]
    Outside,
    #[error("spatial passage has an invalid digit, extent or coordinate order")]
    Passage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Grid {
    width: usize,
    height: usize,
    area: usize,
}

impl Grid {
    pub fn new(width: usize, height: usize) -> Result<Self, SpatialError> {
        let area = width
            .checked_mul(height)
            .filter(|&n| n > 0)
            .ok_or(SpatialError::Extent)?;
        // Coordinate transforms use a signed carrier. Refuse instead of wrapping.
        if width > isize::MAX as usize || height > isize::MAX as usize {
            return Err(SpatialError::Extent);
        }
        Ok(Self {
            width,
            height,
            area,
        })
    }
    pub fn width(self) -> usize {
        self.width
    }
    pub fn height(self) -> usize {
        self.height
    }
    pub fn area(self) -> usize {
        self.area
    }
    pub fn index(self, x: usize, y: usize) -> Result<usize, SpatialError> {
        if x >= self.width || y >= self.height {
            return Err(SpatialError::Outside);
        }
        Ok(y * self.width + x)
    }
    pub fn coordinate(self, index: usize) -> Result<(usize, usize), SpatialError> {
        if index >= self.area {
            return Err(SpatialError::Outside);
        }
        Ok((index % self.width, index / self.width))
    }
    /// Oriented positive-x and positive-y incidence, without a dense matrix.
    pub fn edges(self) -> impl Iterator<Item = (usize, usize)> {
        (0..self.area).flat_map(move |i| {
            let x = i % self.width;
            let y = i / self.width;
            [
                if x + 1 < self.width {
                    Some((i, i + 1))
                } else {
                    None
                },
                if y + 1 < self.height {
                    Some((i, i + self.width))
                } else {
                    None
                },
            ]
            .into_iter()
            .flatten()
        })
    }
    pub fn situated(self, index: usize, frame: &AffineMap3) -> Result<RatVec3, SpatialError> {
        let (x, y) = self.coordinate(index)?;
        Ok(frame.apply(&RatVec3::new(
            crate::ratio::Rat::from_integer(x.into()),
            crate::ratio::Rat::from_integer(y.into()),
            crate::ratio::integer(0),
        )))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Raster {
    grid: Grid,
    samples: Vec<u8>,
}

/// Samples outside the translated receiver's support, with their original locations.
/// This is a boundary receipt; it must not be mistaken for lossless retained learner state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Translation {
    pub raster: Raster,
    pub displacement: (isize, isize),
    pub outside: Vec<(usize, u8)>,
}

impl Raster {
    pub fn new(grid: Grid, samples: Vec<u8>) -> Result<Self, SpatialError> {
        if samples.len() != grid.area() {
            return Err(SpatialError::Length {
                expected: grid.area(),
                found: samples.len(),
            });
        }
        Ok(Self { grid, samples })
    }
    pub fn grid(&self) -> Grid {
        self.grid
    }
    pub fn samples(&self) -> &[u8] {
        &self.samples
    }
    /// Zero-filled finite receiver. No toroidal wrap and no hidden clipping.
    pub fn translate(&self, dx: isize, dy: isize) -> Translation {
        let mut samples = vec![0; self.grid.area()];
        let mut outside = Vec::new();
        for (i, &sample) in self.samples.iter().enumerate() {
            let x = (i % self.grid.width) as isize;
            let y = (i / self.grid.width) as isize;
            let destination = x.checked_add(dx).zip(y.checked_add(dy)).filter(|&(x, y)| {
                x >= 0
                    && y >= 0
                    && (x as usize) < self.grid.width
                    && (y as usize) < self.grid.height
            });
            if let Some((x, y)) = destination {
                samples[y as usize * self.grid.width + x as usize] = sample;
            } else {
                outside.push((i, sample));
            }
        }
        Translation {
            raster: Self {
                grid: self.grid,
                samples,
            },
            displacement: (dx, dy),
            outside,
        }
    }
    /// Clockwise in the raster convention (x right, y down). Shape is exchanged.
    pub fn quarter_turn(&self) -> Self {
        let grid = Grid {
            width: self.grid.height,
            height: self.grid.width,
            area: self.grid.area,
        };
        let mut samples = vec![0; grid.area];
        for (i, &sample) in self.samples.iter().enumerate() {
            let x = i % self.grid.width;
            let y = i / self.grid.width;
            samples[x * grid.width + self.grid.height - 1 - y] = sample;
        }
        Self { grid, samples }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn coordinates_and_oriented_neighbours_do_not_wrap_rows() {
        let g = Grid::new(3, 2).unwrap();
        assert_eq!(
            g.edges().collect::<Vec<_>>(),
            vec![(0, 1), (0, 3), (1, 2), (1, 4), (2, 5), (3, 4), (4, 5)]
        );
        for i in 0..g.area() {
            let (x, y) = g.coordinate(i).unwrap();
            assert_eq!(g.index(x, y), Ok(i));
        }
        assert!(g.index(3, 0).is_err());
        assert_eq!(
            g.situated(5, &AffineMap3::identity()).unwrap(),
            RatVec3::from_i64(2, 1, 0)
        );
    }
    #[test]
    fn four_turns_restore_every_byte_including_non_square_extent() {
        let r = Raster::new(Grid::new(3, 2).unwrap(), vec![0, 1, 2, 3, 254, 255]).unwrap();
        assert_eq!(r.quarter_turn().samples(), &[3, 0, 254, 1, 255, 2]);
        assert_eq!(
            r.quarter_turn()
                .quarter_turn()
                .quarter_turn()
                .quarter_turn(),
            r
        );
    }
    #[test]
    fn translation_reports_lost_support_and_never_wraps() {
        let r = Raster::new(Grid::new(3, 2).unwrap(), vec![0, 1, 2, 3, 4, 5]).unwrap();
        let t = r.translate(1, 0);
        assert_eq!(t.raster.samples(), &[0, 0, 1, 0, 3, 4]);
        assert_eq!(t.outside, vec![(2, 2), (5, 5)]);
        assert_eq!(r.translate(isize::MAX, isize::MIN).outside.len(), 6);
    }
    #[test]
    fn translation_returns_nonclipped_ink_exactly() {
        let r = Raster::new(Grid::new(3, 3).unwrap(), vec![0, 0, 0, 0, 255, 0, 0, 0, 0]).unwrap();
        let t = r.translate(1, 0);
        assert!(t.outside.iter().all(|&(_, v)| v == 0));
        assert_eq!(t.raster.translate(-1, 0).raster, r);
    }
    #[test]
    fn malformed_shapes_refuse() {
        assert!(Grid::new(0, 28).is_err());
        assert!(Grid::new(usize::MAX, 2).is_err());
        assert!(Raster::new(Grid::new(2, 2).unwrap(), vec![1]).is_err());
    }
}

/// An exact coordinate-bearing exterior serial chart. Its coordinates are data, not a
/// certificate that a downstream navigator implements planar translation or rotation.
/// The source consumer must separately establish its spatial transport relation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpatialPassage {
    grid: Grid,
    digits: Vec<usize>,
}

fn coordinate_width(extent: usize) -> usize {
    let mut top = extent - 1;
    let mut width = 1;
    while top >= 16 {
        top /= 16;
        width += 1;
    }
    width
}
fn write_digits(mut value: usize, width: usize, into: &mut Vec<usize>) {
    let start = into.len();
    into.resize(start + width, 0);
    for at in (start..start + width).rev() {
        into[at] = value % 16;
        value /= 16;
    }
}
fn read_digits(digits: &[usize]) -> Result<usize, SpatialError> {
    digits.iter().try_fold(0usize, |value, &digit| {
        if digit >= 16 {
            return Err(SpatialError::Passage);
        }
        value
            .checked_mul(16)
            .and_then(|v| v.checked_add(digit))
            .ok_or(SpatialError::Passage)
    })
}
impl SpatialPassage {
    /// Row, column, intensity in big-endian base sixteen for each sample. Row and column
    /// widths follow the declared extent; intensity always retains both nibbles.
    pub fn encode(raster: &Raster) -> Self {
        let grid = raster.grid();
        let (row_width, column_width) =
            (coordinate_width(grid.height), coordinate_width(grid.width));
        let mut digits = Vec::new();
        for (at, &sample) in raster.samples().iter().enumerate() {
            write_digits(at / grid.width, row_width, &mut digits);
            write_digits(at % grid.width, column_width, &mut digits);
            write_digits(usize::from(sample), 2, &mut digits);
        }
        Self { grid, digits }
    }
    pub fn from_digits(grid: Grid, digits: Vec<usize>) -> Result<Self, SpatialError> {
        let passage = Self { grid, digits };
        passage.decode()?;
        Ok(passage)
    }
    pub fn grid(&self) -> Grid {
        self.grid
    }
    pub fn digits(&self) -> &[usize] {
        &self.digits
    }
    /// (row width, column width), each measured in base-sixteen digits.
    pub fn coordinate_digits(&self) -> (usize, usize) {
        (
            coordinate_width(self.grid.height),
            coordinate_width(self.grid.width),
        )
    }
    pub fn decode(&self) -> Result<Raster, SpatialError> {
        let (rows, columns) = self.coordinate_digits();
        let stride = rows + columns + 2;
        let expected = self
            .grid
            .area
            .checked_mul(stride)
            .ok_or(SpatialError::Passage)?;
        if self.digits.len() != expected {
            return Err(SpatialError::Passage);
        }
        let mut samples = Vec::with_capacity(self.grid.area);
        for (at, cell) in self.digits.chunks_exact(stride).enumerate() {
            if read_digits(&cell[..rows])? != at / self.grid.width
                || read_digits(&cell[rows..rows + columns])? != at % self.grid.width
            {
                return Err(SpatialError::Passage);
            }
            samples.push(
                u8::try_from(read_digits(&cell[rows + columns..])?)
                    .map_err(|_| SpatialError::Passage)?,
            );
        }
        Raster::new(self.grid, samples)
    }
}

#[cfg(test)]
mod passage_tests {
    use super::*;
    #[test]
    fn coordinate_passage_roundtrips_full_mnist_extent_and_every_intensity() {
        let raster = Raster::new(
            Grid::new(28, 28).unwrap(),
            (0..784).map(|i| (i % 256) as u8).collect(),
        )
        .unwrap();
        let passage = SpatialPassage::encode(&raster);
        assert_eq!(passage.coordinate_digits(), (2, 2));
        assert_eq!(passage.digits().len(), 784 * 6);
        assert_eq!(passage.decode().unwrap(), raster);
        assert_eq!(
            SpatialPassage::from_digits(raster.grid(), passage.digits().to_vec()).unwrap(),
            passage
        );
    }
    #[test]
    fn coordinate_passage_refuses_missing_duplicate_reordered_and_invalid_cells() {
        let raster = Raster::new(Grid::new(2, 2).unwrap(), vec![1, 2, 3, 4]).unwrap();
        let passage = SpatialPassage::encode(&raster);
        let mut digits = passage.digits().to_vec();
        digits.pop();
        assert!(SpatialPassage::from_digits(raster.grid(), digits).is_err());
        let mut digits = passage.digits().to_vec();
        digits[4..8].copy_from_slice(&passage.digits()[..4]);
        assert!(SpatialPassage::from_digits(raster.grid(), digits).is_err());
        let mut digits = passage.digits().to_vec();
        digits.rotate_left(4);
        assert!(SpatialPassage::from_digits(raster.grid(), digits).is_err());
        let mut digits = passage.digits().to_vec();
        digits[2] = 16;
        assert!(SpatialPassage::from_digits(raster.grid(), digits).is_err());
    }
}
