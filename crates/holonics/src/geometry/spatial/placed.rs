//! Coordinate placement for a finite raster receiver (Refs #73, #148, #62).
//!
//! Axis 0 is x = column (rightwards); axis 1 is y = row (downwards), exactly as `Grid::index`.
//! Each pixel supplies its high then low nibble at the SAME (x,y) phase prefix. Unlike the
//! serial `SpatialPassage`, coordinates are native placement operands rather than symbols.
//! The source consumer checks the first two ring periods against `periods`, and supplies these
//! prefixes to `hnn::encoding::OccurrencePlacement::at` at its actual continuing `Current`.
//! That owner retains the exact opening and arrival lifts, including winding and later-ring
//! carry. This chart never reconstructs a lifecycle from residues or discards that winding.
//!
//! The finite raster embeds in the two ring periods without coordinate aliasing; it is not a
//! periodic image and no wrap, rotation or translation invariance of labels is asserted.

use super::{Grid, Raster, SpatialError};
use std::ops::Range;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PlacedRaster {
    grid: Grid,
    periods: [u64; 2],
    symbols: Vec<usize>,
    phases: Vec<Vec<u64>>,
}

impl PlacedRaster {
    pub fn encode(raster: &Raster, periods: [u64; 2]) -> Result<Self, SpatialError> {
        let grid = raster.grid();
        if u64::try_from(grid.width()).map_err(|_| SpatialError::Extent)? > periods[0]
            || u64::try_from(grid.height()).map_err(|_| SpatialError::Extent)? > periods[1]
        {
            return Err(SpatialError::Passage);
        }
        let capacity = grid.area().checked_mul(2).ok_or(SpatialError::Extent)?;
        let mut symbols = Vec::with_capacity(capacity);
        let mut phases = Vec::with_capacity(capacity);
        for (index, &value) in raster.samples().iter().enumerate() {
            let (x, y) = grid.coordinate(index)?;
            let phase = vec![x as u64, y as u64];
            symbols.extend([usize::from(value >> 4), usize::from(value & 15)]);
            phases.push(phase.clone());
            phases.push(phase);
        }
        Self::from_parts(grid, periods, symbols, phases)
    }
    /// Read an exterior chart only after checking its complete coordinate/decoder relation.
    pub fn from_parts(
        grid: Grid,
        periods: [u64; 2],
        symbols: Vec<usize>,
        phases: Vec<Vec<u64>>,
    ) -> Result<Self, SpatialError> {
        let chart = Self {
            grid,
            periods,
            symbols,
            phases,
        };
        chart.decode()?;
        Ok(chart)
    }
    pub fn grid(&self) -> Grid {
        self.grid
    }
    pub fn periods(&self) -> [u64; 2] {
        self.periods
    }
    pub fn symbols(&self) -> &[usize] {
        &self.symbols
    }
    pub fn phase_prefixes(&self) -> &[Vec<u64>] {
        &self.phases
    }
    pub fn decode(&self) -> Result<Raster, SpatialError> {
        let count = self
            .grid
            .area()
            .checked_mul(2)
            .ok_or(SpatialError::Extent)?;
        if self.symbols.len() != count
            || self.phases.len() != count
            || u64::try_from(self.grid.width()).map_err(|_| SpatialError::Extent)? > self.periods[0]
            || u64::try_from(self.grid.height()).map_err(|_| SpatialError::Extent)?
                > self.periods[1]
        {
            return Err(SpatialError::Passage);
        }
        let mut samples = Vec::with_capacity(self.grid.area());
        for (i, pair) in self.symbols.chunks_exact(2).enumerate() {
            let (x, y) = self.grid.coordinate(i)?;
            let expected = [x as u64, y as u64];
            if pair.iter().any(|&v| v >= 16)
                || self.phases[2 * i].as_slice() != expected
                || self.phases[2 * i + 1].as_slice() != expected
            {
                return Err(SpatialError::Passage);
            }
            samples.push((pair[0] * 16 + pair[1]) as u8);
        }
        Raster::new(self.grid, samples)
    }
    /// A pixel-aligned borrowed cut retains absolute positions in the original chart.
    /// Match this with native placement.part(2*start..2*end) to preserve the actual opening lift.
    pub fn part(&self, pixels: Range<usize>) -> Result<PlacedRasterSlice<'_>, SpatialError> {
        if pixels.start > pixels.end || pixels.end > self.grid.area() {
            return Err(SpatialError::Outside);
        }
        Ok(PlacedRasterSlice {
            chart: self,
            pixels,
        })
    }
}

#[derive(Debug, Clone)]
pub struct PlacedRasterSlice<'a> {
    chart: &'a PlacedRaster,
    pixels: Range<usize>,
}
impl PlacedRasterSlice<'_> {
    pub fn grid(&self) -> Grid {
        self.chart.grid
    }
    pub fn periods(&self) -> [u64; 2] {
        self.chart.periods
    }
    pub fn range(&self) -> Range<usize> {
        self.pixels.clone()
    }
    pub fn occurrence_range(&self) -> Range<usize> {
        2 * self.pixels.start..2 * self.pixels.end
    }
    pub fn symbols(&self) -> &[usize] {
        &self.chart.symbols[self.occurrence_range()]
    }
    pub fn phase_prefixes(&self) -> &[Vec<u64>] {
        &self.chart.phases[self.occurrence_range()]
    }
    pub fn samples(&self) -> Vec<u8> {
        self.symbols()
            .chunks_exact(2)
            .map(|p| (16 * p[0] + p[1]) as u8)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn asymmetric_corners_use_x_then_y_and_both_nibbles_share_the_site() {
        let raster = Raster::new(
            Grid::new(3, 2).unwrap(),
            vec![0x01, 0x23, 0x45, 0x67, 0x89, 0xab],
        )
        .unwrap();
        let chart = PlacedRaster::encode(&raster, [3, 2]).unwrap();
        assert_eq!(chart.symbols(), &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]);
        assert_eq!(
            chart.phase_prefixes(),
            &[
                vec![0, 0],
                vec![0, 0],
                vec![1, 0],
                vec![1, 0],
                vec![2, 0],
                vec![2, 0],
                vec![0, 1],
                vec![0, 1],
                vec![1, 1],
                vec![1, 1],
                vec![2, 1],
                vec![2, 1]
            ]
        );
        assert_eq!(chart.decode().unwrap(), raster);
    }
    #[test]
    fn full_raw_mnist_extent_preserves_all_intensities_without_aliasing() {
        let raster = Raster::new(
            Grid::new(28, 28).unwrap(),
            (0..784).map(|i| (i % 256) as u8).collect(),
        )
        .unwrap();
        for periods in [[28, 28], [29, 31]] {
            let chart = PlacedRaster::encode(&raster, periods).unwrap();
            assert_eq!(chart.symbols().len(), 1568);
            assert_eq!(chart.decode().unwrap(), raster);
            assert_eq!(chart.phase_prefixes()[1567], vec![27, 27]);
        }
        assert!(PlacedRaster::encode(&raster, [27, 28]).is_err());
        assert!(PlacedRaster::encode(&raster, [28, 27]).is_err());
    }
    #[test]
    fn slices_keep_absolute_coordinates_and_pixel_decoder() {
        let raster = Raster::new(Grid::new(3, 2).unwrap(), vec![0, 1, 2, 3, 4, 255]).unwrap();
        let chart = PlacedRaster::encode(&raster, [5, 7]).unwrap();
        let part = chart.part(2..5).unwrap();
        assert_eq!(part.occurrence_range(), 4..10);
        assert_eq!(part.phase_prefixes()[0], vec![2, 0]);
        assert_eq!(part.phase_prefixes()[2], vec![0, 1]);
        assert_eq!(part.samples(), vec![2, 3, 4]);
        assert!(chart.part(6..6).unwrap().symbols().is_empty());
        assert!(chart.part(5..7).is_err());
    }
    #[test]
    fn decoder_refuses_transposed_reordered_missing_and_outside_nibbles() {
        let r = Raster::new(Grid::new(3, 2).unwrap(), vec![0; 6]).unwrap();
        let chart = PlacedRaster::encode(&r, [3, 2]).unwrap();
        let mut c = chart.clone();
        c.phases[2] = vec![0, 1];
        assert!(c.decode().is_err());
        let mut c = chart.clone();
        c.phases.swap(2, 6);
        assert!(c.decode().is_err());
        let mut c = chart.clone();
        c.symbols.pop();
        assert!(c.decode().is_err());
        let mut c = chart;
        c.symbols[1] = 16;
        assert!(c.decode().is_err());
    }
}
