//! Strict, borrowed unsigned-byte IDX boundary readers. The parser knows dimensions and bytes,
//! never digit meanings, a class prediction, a training partition or a native source law.
//! Gzip decompression and file provenance belong to the exterior caller. Images and annotations
//! are intentionally separate readers so a caller can predict before an annotation arrives.

use super::{Grid, SpatialError};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum IdxError {
    #[error("IDX header is truncated")]
    Header,
    #[error("IDX magic {found} differs from expected {expected}")]
    Magic { expected: u32, found: u32 },
    #[error("IDX dimensions or payload length overflow their carrier")]
    Overflow,
    #[error("IDX payload length {found} differs from expected {expected}")]
    Length { expected: usize, found: usize },
    #[error("IDX index {index} is outside count {count}")]
    Index { index: usize, count: usize },
    #[error(transparent)]
    Spatial(#[from] SpatialError),
}

fn word(bytes: &[u8], at: usize) -> Result<u32, IdxError> {
    let value = bytes.get(at..at + 4).ok_or(IdxError::Header)?;
    Ok(u32::from_be_bytes([value[0], value[1], value[2], value[3]]))
}
fn size(bytes: &[u8], at: usize) -> Result<usize, IdxError> {
    usize::try_from(word(bytes, at)?).map_err(|_| IdxError::Overflow)
}
fn payload(bytes: &[u8], header: usize, expected: usize) -> Result<&[u8], IdxError> {
    let data = bytes.get(header..).ok_or(IdxError::Header)?;
    if data.len() != expected {
        return Err(IdxError::Length {
            expected,
            found: data.len(),
        });
    }
    Ok(data)
}
fn magic(bytes: &[u8], expected: u32) -> Result<(), IdxError> {
    let found = word(bytes, 0)?;
    if found != expected {
        return Err(IdxError::Magic { expected, found });
    }
    Ok(())
}

#[derive(Debug, Clone, Copy)]
pub struct Images<'a> {
    grid: Grid,
    count: usize,
    data: &'a [u8],
}
impl<'a> Images<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, IdxError> {
        magic(bytes, 0x0000_0803)?;
        let count = size(bytes, 4)?;
        let grid = Grid::new(size(bytes, 12)?, size(bytes, 8)?)?;
        let expected = count.checked_mul(grid.area()).ok_or(IdxError::Overflow)?;
        Ok(Self {
            grid,
            count,
            data: payload(bytes, 16, expected)?,
        })
    }
    pub fn grid(self) -> Grid {
        self.grid
    }
    pub fn len(self) -> usize {
        self.count
    }
    pub fn is_empty(self) -> bool {
        self.count == 0
    }
    pub fn image(self, index: usize) -> Result<&'a [u8], IdxError> {
        if index >= self.count {
            return Err(IdxError::Index {
                index,
                count: self.count,
            });
        }
        let start = index * self.grid.area();
        Ok(&self.data[start..start + self.grid.area()])
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Labels<'a> {
    data: &'a [u8],
}
impl<'a> Labels<'a> {
    pub fn parse(bytes: &'a [u8]) -> Result<Self, IdxError> {
        magic(bytes, 0x0000_0801)?;
        Ok(Self {
            data: payload(bytes, 8, size(bytes, 4)?)?,
        })
    }
    pub fn len(self) -> usize {
        self.data.len()
    }
    pub fn is_empty(self) -> bool {
        self.data.is_empty()
    }
    pub fn label(self, index: usize) -> Result<u8, IdxError> {
        self.data.get(index).copied().ok_or(IdxError::Index {
            index,
            count: self.data.len(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn bytes(words: &[u32], data: &[u8]) -> Vec<u8> {
        words
            .iter()
            .flat_map(|n| n.to_be_bytes())
            .chain(data.iter().copied())
            .collect()
    }
    #[test]
    fn preserves_raw_bytes_and_distinct_annotations() {
        let b = bytes(
            &[0x803, 2, 2, 3],
            &[0, 1, 2, 3, 254, 255, 6, 7, 8, 9, 10, 11],
        );
        let i = Images::parse(&b).unwrap();
        assert_eq!(i.grid(), Grid::new(3, 2).unwrap());
        assert_eq!(i.len(), 2);
        assert_eq!(i.image(0).unwrap(), &[0, 1, 2, 3, 254, 255]);
        assert_eq!(i.image(1).unwrap(), &[6, 7, 8, 9, 10, 11]);
        assert!(i.image(2).is_err());
        let b = bytes(&[0x801, 2], &[9, 6]);
        let l = Labels::parse(&b).unwrap();
        assert_eq!(l.label(0), Ok(9));
        assert_eq!(l.label(1), Ok(6));
        assert!(l.label(2).is_err());
    }
    #[test]
    fn refuses_truncation_trailing_data_wrong_type_and_zero_extent() {
        for n in 0..16 {
            assert!(Images::parse(&vec![0; n]).is_err());
        }
        assert!(Images::parse(&bytes(&[0x803, 1, 2, 2], &[0; 3])).is_err());
        assert!(Images::parse(&bytes(&[0x803, 1, 2, 2], &[0; 5])).is_err());
        assert!(Images::parse(&bytes(&[0x903, 1, 2, 2], &[0; 4])).is_err());
        assert!(Images::parse(&bytes(&[0x803, 1, 0, 2], &[])).is_err());
        assert!(Labels::parse(&bytes(&[0x801, 2], &[0])).is_err());
        assert!(Labels::parse(&bytes(&[0x801, 1], &[0, 1])).is_err());
    }
    #[test]
    fn no_dataset_semantics_are_inferred_by_the_codec() {
        let b = bytes(&[0x801, 1], &[255]);
        assert_eq!(Labels::parse(&b).unwrap().label(0), Ok(255));
        // The MNIST harness, not this general codec, owns its ten-label contract.
        let b = bytes(&[0x803, 0, 28, 28], &[]);
        assert!(Images::parse(&b).unwrap().is_empty());
    }
}
