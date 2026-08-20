//! Native-material adapter for the streamed Phoenix circulation.
//!
//! This owner is deliberately narrow. `MountedNativeRest` authenticates the source-detached
//! rest; the retained `File` is only the exterior staging handle. No native scheduler, semantic
//! fallback, or second circulation is introduced here.

use std::fs::File;
use std::os::unix::fs::FileExt;

use holonic_engine::native_rest::MountedNativeRest;
use holonic_engine::source_occurrence::{OccurrenceWitness, RegionIdentity};
use holonic_engine::streamed_standing::StagedRegion;

use super::streamed::MaterialSource;

/// A mounted native rest and the stable file handle opened from that authenticated occurrence.
pub struct NativeMaterialSource {
    pub rest: MountedNativeRest,
    pub file: File,
}

impl NativeMaterialSource {
    pub fn open(path: impl AsRef<std::path::Path>) -> Result<Self, String> {
        let rest = MountedNativeRest::open(path).map_err(|error| error.to_string())?;
        let file = rest.open_file().map_err(|error| error.to_string())?;
        Ok(Self { rest, file })
    }

    fn extent(
        &self,
        population: &str,
    ) -> Result<holonic_engine::native_rest::MountedPopulationExtent, String> {
        self.rest
            .population_extent(population)
            .map_err(|error| error.to_string())
    }

    fn bf16_extent(
        &self,
        population: &str,
    ) -> Result<holonic_engine::native_rest::MountedPopulationExtent, String> {
        let extent = self.extent(population)?;
        if !matches!(extent.dtype.as_str(), "BF16" | "Bf16") {
            return Err(format!(
                "{population} is {}; the native H4 mouth admits BF16 only",
                extent.dtype
            ));
        }
        if (extent.end - extent.start) % 2 != 0 {
            return Err(format!("{population} has an odd byte extent"));
        }
        Ok(extent)
    }
}

impl MaterialSource for NativeMaterialSource {
    fn file(&self) -> Result<&File, String> {
        Ok(&self.file)
    }

    fn file_octets(&self) -> Result<u64, String> {
        Ok(self.rest.total_file_octets())
    }

    fn region(&self, population: &str) -> Result<RegionIdentity, String> {
        self.bf16_extent(population)?;
        self.rest
            .populations()
            .iter()
            .find(|descriptor| descriptor.source().population == population)
            .map(|descriptor| descriptor.source().clone())
            .ok_or_else(|| format!("native population {population} is not admitted"))
    }

    fn staged(&self, population: &str) -> Result<StagedRegion, String> {
        let extent = self.bf16_extent(population)?;
        let dim = *extent.shape.last().unwrap_or(&0);
        let words = (extent.end - extent.start) / 2;
        Ok(StagedRegion {
            population: extent.population,
            start: extent.start,
            words: u32::try_from(words)
                .map_err(|_| format!("{population} is wider than one staged region"))?,
            dim,
        })
    }

    fn rows(
        &mut self,
        population: &str,
        from: usize,
        count: usize,
    ) -> Result<(Vec<u16>, usize), String> {
        let extent = self.bf16_extent(population)?;
        if extent.shape.len() != 2 {
            return Err(format!(
                "{population} is not a row-addressable rank-2 population"
            ));
        }
        let rows = extent.shape[0];
        let width = extent.shape[1];
        let end_row = from
            .checked_add(count)
            .ok_or_else(|| format!("{population} row extent overflow"))?;
        if end_row > rows {
            return Err(format!("{population} rows {from}..{end_row} exceed {rows}"));
        }
        let octets = count
            .checked_mul(width)
            .and_then(|words| words.checked_mul(2))
            .ok_or_else(|| format!("{population} row byte extent overflow"))?;
        let row_words =
            u64::try_from(from).map_err(|_| format!("{population} row index exceeds u64"))?;
        let width_u64 =
            u64::try_from(width).map_err(|_| format!("{population} width exceeds u64"))?;
        let byte_offset = row_words
            .checked_mul(width_u64)
            .and_then(|words| words.checked_mul(2))
            .ok_or_else(|| format!("{population} row offset overflow"))?;
        let start = extent
            .start
            .checked_add(byte_offset)
            .ok_or_else(|| format!("{population} row offset overflow"))?;
        let mut bytes = vec![0u8; octets];
        self.file
            .read_exact_at(&mut bytes, start)
            .map_err(|error| error.to_string())?;
        let words = bytes
            .chunks_exact(2)
            .map(|pair| u16::from_le_bytes([pair[0], pair[1]]))
            .collect();
        Ok((words, width))
    }

    fn occurrence(&self) -> &dyn OccurrenceWitness {
        &self.rest
    }

    fn source_identity(&self) -> String {
        let source = self.rest.source();
        let graph_keys: Vec<&str> = self
            .rest
            .graphs()
            .iter()
            .map(|graph| graph.key.as_str())
            .collect();
        format!(
            "native rest {} octets, payload offset {}, source container {} octets, header {} octets, header sha256 {}, content sha256 {:?}, implementation sha256 {}, configuration sha256 {}, graph keys {:?}",
            self.rest.total_file_octets(),
            self.rest.payload_offset(),
            source.container_octets,
            source.container_header_octets,
            source.container_header_sha256,
            source.container_content_sha256,
            source.implementation_sha256,
            source.configuration_sha256,
            graph_keys,
        )
    }

    fn verify_stable(&self) -> Result<(), String> {
        self.rest.verify_still().map_err(|error| error.to_string())
    }
}
