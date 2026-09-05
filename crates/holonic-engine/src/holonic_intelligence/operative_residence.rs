//! Packed coefficient residency for the source-neutral operator ecology.
//!
//! Retained coefficients cross once as exact BF16 codewords. Restricted rows stay compact and
//! a device decoder inserts the declared zero rows only in a requested temporary tile. One
//! mutually-exclusive aligned tile uses the complete restricted population's frame. The chart
//! does not identify omitted foreign coefficients with zero and does not restrict later overlays.

use std::{
    collections::BTreeMap, fs::File, os::unix::fs::FileExt, path::Path,
};

use mount::DeviceBuffer;
use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::{
    embedding_fiber::{
        FiberError, FixedFramePooledMount, PooledReadout, ResidentBfloat16Frame,
        ResidentBfloat16Population,
    },
    exact_value::{AlgebraicRoot, CertifiedSeries, ExactInterval},
    resident_section::{BandElements, DyadicEnclosure, ResidentRefusal, ResidentSurface},
};

use super::{
    NativeCarrierAxis, NativeFullOperatorColdWitness, NativeFullOperatorEcology,
    NativeFullOperatorError, NativeOperationPrimitive, NativeTensorOrdinal,
};

pub const NATIVE_OPERATOR_RESIDENCE_SCHEMA: &str = "holonic-engine.native-operator-residence.v1";
pub const NATIVE_OPERATOR_TILE_ROWS: usize = 16_384;
pub const NATIVE_OPERATOR_COPY_CHUNK_OCTETS: usize = 64 * 1024 * 1024;

struct CountedOctets<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    buffer: DeviceBuffer<u8>,
    octets: usize,
}

impl CountedOctets<'_> {
    fn device_ptr(&self) -> u64 {
        self.buffer.device_ptr()
    }
}

impl Drop for CountedOctets<'_> {
    fn drop(&mut self) {
        self.surface.released_octets(self.octets as u64);
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ResidentNativeOperatorPopulation {
    pub ordinal: NativeTensorOrdinal,
    pub raw_offset: u64,
    pub words: u32,
    pub rows: usize,
    pub dim: usize,
    pub frame: ResidentBfloat16Frame,
    /// Physical packed rows in ascending logical order. None is the dense chart; Some([])
    /// is an explicitly zero restricted native map, not a claim about omitted foreign data.
    pub retained_rows: Option<Vec<u32>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeOperatorResidenceReceipt {
    pub schema: String,
    pub device: String,
    pub population_count: usize,
    pub raw_coefficient_octets: u64,
    pub logical_coefficient_octets: u64,
    pub decoder_staging_octets: u64,
    pub decoder_zero_row_octets: u64,
    pub retained_row_chart_octets: u64,
    pub aligned_tile_octets: u64,
    pub row_mass_octets: u64,
    pub score_octets: u64,
    pub vector_workspace_octets: u64,
    pub addressed_occurrence_rows: usize,
    pub addressed_occurrence_octets: u64,
    pub reduction_scratch_octets: u64,
    pub pooled_apparatus_octets: u64,
    pub total_resident_octets: u64,
    pub available_before_mount: u64,
    pub available_after_raw_mount: u64,
    pub available_after_decoder_base_mount: u64,
    pub target_tile_rows: usize,
    pub tile_rows: usize,
    pub mass_score_rows: usize,
    pub alignment_allocation_refusals: usize,
    pub widest_dim: usize,
    pub ingress_octets: u64,
    pub complete_population_frames: usize,
    pub chronology_population: usize,
    pub chronology_octets: u64,
}

/// Apparatus work of zero-insertion decoding, separate from arithmetic launches and ingress.
/// These counters never select current or change morphology. They include successful copies
/// made before any later obstruction; the receiver does not pretend a failed request was free.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
pub struct NativeOperatorDecoderCensus {
    pub completed_tiles: u64,
    pub completed_lookup_rows: u64,
    pub retained_runs: u64,
    pub zero_runs: u64,
    pub device_copy_calls: u64,
    pub device_copy_octets: u64,
}

/// One full packed coefficient residence.  It owns one ecology's complete coefficient standing
/// and one aligned tile aperture; there is no second aligned slot and no host fallback.
pub struct NativeOperatorResidence<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    raw: CountedOctets<'chart>,
    /// One shared zero codeword row; no absent population is expanded into resident coefficients.
    zero_row: Option<CountedOctets<'chart>>,
    pool: CountedOctets<'chart>,
    aligned_offset: usize,
    mass_offset: usize,
    _score_offset: usize,
    _vector_offset: usize,
    gather_offset: usize,
    decode_offset: usize,
    scratch_offset: usize,
    chronologies: BTreeMap<(u64, usize, usize), BandElements<'chart>>,
    populations: Vec<ResidentNativeOperatorPopulation>,
    receipt: NativeOperatorResidenceReceipt,
    /// The single alignment slot's occupancy: one aligned tile at a time, refused at runtime
    /// rather than by a mutable borrow, so a segment may hold its tile while it reads bands and
    /// positions.
    slot_in_use: std::cell::Cell<bool>,
    decoder_census: std::cell::Cell<NativeOperatorDecoderCensus>,
}

pub struct NativeAlignedOperatorTile<'residence, 'chart> {
    pub population: NativeTensorOrdinal,
    pub first_row: usize,
    pub rows: usize,
    pub mounted: PooledReadout<'chart>,
    residence: &'residence NativeOperatorResidence<'chart>,
}

impl Drop for NativeAlignedOperatorTile<'_, '_> {
    fn drop(&mut self) {
        self.residence.slot_in_use.set(false);
    }
}

pub(crate) struct ResidentBfloat16Selection {
    pub address: u64,
    pub rows: usize,
    pub width: usize,
    pub frame: ResidentBfloat16Frame,
    pub entry_octaves: u32,
}

/// Where the packed coefficients come from at mount: the source container through the cold
/// witness, or a productive lane that carries the codewords itself.  Every population's octets
/// are delivered in ascending offset order, and their count must equal the ecology's.
pub trait NativeCoefficientIntake {
    fn populations(&self) -> usize;
    fn population_octets(&self, ordinal: usize) -> Result<u64, NativeOperatorResidenceError>;
    fn deliver(
        &mut self,
        ordinal: usize,
        sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
    ) -> Result<(), NativeOperatorResidenceError>;
    /// Optional exact zero-insertion chart for a restricted native population. The normal
    /// `deliver` method remains the expanded reference; `deliver_retained` supplies packed rows.
    fn retained_rows(&self, _ordinal: usize) -> Result<Option<Vec<u32>>, NativeOperatorResidenceError> {
        Ok(None)
    }
    fn deliver_retained(&mut self, ordinal: usize,
        sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
    ) -> Result<(), NativeOperatorResidenceError> {
        self.deliver(ordinal, sink)
    }
}

/// The source container read through the cold witness's byte ranges, in chunks.
struct SourceIntake<'a> {
    witness: &'a NativeFullOperatorColdWitness,
    source: File,
    chunk: Vec<u8>,
}

impl NativeCoefficientIntake for SourceIntake<'_> {
    fn populations(&self) -> usize {
        self.witness.populations.len()
    }

    fn population_octets(&self, ordinal: usize) -> Result<u64, NativeOperatorResidenceError> {
        let population = self
            .witness
            .populations
            .get(ordinal)
            .ok_or(NativeOperatorResidenceError::Witness)?;
        if population.ordinal != NativeTensorOrdinal(ordinal as u32)
            || population.source_end < population.source_start
        {
            return Err(NativeOperatorResidenceError::Witness);
        }
        Ok(population.source_end - population.source_start)
    }

    fn deliver(
        &mut self,
        ordinal: usize,
        sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
    ) -> Result<(), NativeOperatorResidenceError> {
        let population = &self.witness.populations[ordinal];
        let span = usize::try_from(population.source_end - population.source_start)
            .map_err(|_| NativeOperatorResidenceError::Extent)?;
        let mut copied = 0usize;
        while copied < span {
            let take = (span - copied).min(self.chunk.len());
            let source_at = self
                .witness
                .payload_base
                .checked_add(population.source_start)
                .and_then(|value| value.checked_add(copied as u64))
                .ok_or(NativeOperatorResidenceError::Extent)?;
            self.source
                .read_exact_at(&mut self.chunk[..take], source_at)
                .map_err(|error| NativeOperatorResidenceError::Io(error.to_string()))?;
            sink(copied, &self.chunk[..take])?;
            copied += take;
        }
        Ok(())
    }
}

impl<'chart> NativeOperatorResidence<'chart> {
    pub fn mount(
        surface: &'chart ResidentSurface<'chart>,
        ecology: &NativeFullOperatorEcology,
        witness: &NativeFullOperatorColdWitness,
    ) -> Result<Self, NativeOperatorResidenceError> {
        Self::mount_with_chunk(surface, ecology, witness, NATIVE_OPERATOR_COPY_CHUNK_OCTETS)
    }

    pub fn mount_with_chunk(
        surface: &'chart ResidentSurface<'chart>,
        ecology: &NativeFullOperatorEcology,
        witness: &NativeFullOperatorColdWitness,
        chunk_octets: usize,
    ) -> Result<Self, NativeOperatorResidenceError> {
        if chunk_octets == 0 {
            return Err(NativeOperatorResidenceError::Witness);
        }
        let source = File::open(Path::new(&witness.source_container))
            .map_err(|error| NativeOperatorResidenceError::Io(error.to_string()))?;
        let raw_octets = ecology.coefficient_octets()?;
        let mut intake = SourceIntake {
            witness,
            source,
            chunk: vec![0u8; chunk_octets.min(usize::try_from(raw_octets).unwrap_or(chunk_octets))],
        };
        Self::mount_from_intake(surface, ecology, &mut intake)
    }

    /// Mount from any coefficient intake: the packed residency is the same whatever delivered
    /// the codewords.
    pub fn mount_from_intake(
        surface: &'chart ResidentSurface<'chart>,
        ecology: &NativeFullOperatorEcology,
        intake: &mut dyn NativeCoefficientIntake,
    ) -> Result<Self, NativeOperatorResidenceError> {
        Self::mount_intake_chart(surface, ecology, intake, false)
    }

    /// Explicit expanded-layout comparison receiver. Normal mounts use the intake's declared
    /// packed chart; this path exists to compare its decoder with the former zero-filled body.
    pub fn mount_expanded_reference(
        surface: &'chart ResidentSurface<'chart>, ecology: &NativeFullOperatorEcology,
        intake: &mut dyn NativeCoefficientIntake,
    ) -> Result<Self, NativeOperatorResidenceError> {
        Self::mount_intake_chart(surface, ecology, intake, true)
    }

    fn mount_intake_chart(
        surface: &'chart ResidentSurface<'chart>, ecology: &NativeFullOperatorEcology,
        intake: &mut dyn NativeCoefficientIntake, expanded: bool,
    ) -> Result<Self, NativeOperatorResidenceError> {
        ecology.validate()?;
        if intake.populations() != ecology.coefficient_populations.len() {
            return Err(NativeOperatorResidenceError::Witness);
        }
        let mut layouts = Vec::with_capacity(ecology.coefficient_populations.len());
        let mut stored_spans = Vec::with_capacity(ecology.coefficient_populations.len());
        for (at, population) in ecology.coefficient_populations.iter().enumerate() {
            if intake.population_octets(at)? != population.coefficient_population.checked_mul(2)
                .ok_or(NativeOperatorResidenceError::Extent)? {
                return Err(NativeOperatorResidenceError::Witness);
            }
            u32::try_from(population.coefficient_population).map_err(|_| NativeOperatorResidenceError::Extent)?;
            let (rows, dim) = match population.shape.as_slice() {
                [dim] => (1, *dim), [rows, dim] => (*rows, *dim),
                _ => return Err(NativeOperatorResidenceError::Rank),
            };
            let layout = if expanded { None } else { intake.retained_rows(at)? };
            if let Some(retained) = &layout {
                if retained.windows(2).any(|pair| pair[0] >= pair[1])
                    || retained.last().is_some_and(|row| *row as usize >= rows) {
                    return Err(NativeOperatorResidenceError::Witness);
                }
            }
            stored_spans.push(checked_product(&[layout.as_ref().map_or(rows, Vec::len), dim, 2])?);
            layouts.push(layout);
        }
        let logical_octets = ecology.coefficient_octets()?;
        let raw_octets = stored_spans.iter().try_fold(0u64, |sum, span|
            sum.checked_add(*span as u64).ok_or(NativeOperatorResidenceError::Extent))?;
        let compact = layouts.iter().any(Option::is_some);
        let widest_dim = ecology
            .coefficient_populations
            .iter()
            .filter_map(|population| population.shape.last().copied())
            .max()
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let vector_widths = vector_workspace_widths(ecology)?;
        let vector_octets = checked_product(&[vector_widths.iter().sum(), 16])?;
        let addressed_occurrence_rows = ecology
            .operations
            .iter()
            .filter_map(|operation| match operation.primitive {
                NativeOperationPrimitive::CausalContact {
                    reach: super::NativeCausalReach::Window(rows),
                    ..
                } => Some(rows),
                _ => None,
            })
            .max()
            .unwrap_or(1);
        let gather_octets = checked_product(&[addressed_occurrence_rows, widest_dim, 2])?;
        let scratch_octets = 16usize;
        let available = surface.memory()?.free_bytes as u64;
        if raw_octets >= available {
            return Err(NativeOperatorResidenceError::Resident(
                ResidentRefusal::MemoryAperture {
                    required: raw_octets,
                    free: available,
                },
            ));
        }

        let raw = counted(
            surface,
            usize::try_from(raw_octets.max(1)).map_err(|_| NativeOperatorResidenceError::Extent)?,
            "packed coefficients",
        )?;
        let available_after_raw = surface.memory()?.free_bytes;
        let zero_row = if compact {
            let row = counted(surface, checked_product(&[widest_dim, 2])?, "restricted decoder zero row")?;
            surface.copy_octets(&row.buffer, 0, &vec![0; row.octets])?;
            Some(row)
        } else { None };
        let available_after_decoder_base = surface.memory()?.free_bytes;
        let fixed_pool_octets = vector_octets
            .checked_add(gather_octets)
            .and_then(|value| value.checked_add(scratch_octets))
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let per_row_octets = widest_dim
            .checked_mul(if compact { 10 } else { 8 })
            .and_then(|aligned| aligned.checked_add(32))
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let admitted_rows = available_after_decoder_base.saturating_sub(fixed_pool_octets) / per_row_octets;
        let mut tile_rows = greatest_power_of_two(admitted_rows.min(NATIVE_OPERATOR_TILE_ROWS))
            .ok_or_else(|| {
                NativeOperatorResidenceError::Resident(ResidentRefusal::MemoryAperture {
                    required: raw_octets
                        + u64::try_from(fixed_pool_octets + per_row_octets).unwrap_or(u64::MAX),
                    free: available,
                })
            })?;
        let mut allocation_refusals = 0usize;
        let (pool, pool_shape) = loop {
            let shape = OperatorPoolShape::for_rows(
                tile_rows,
                NATIVE_OPERATOR_TILE_ROWS,
                widest_dim,
                vector_octets,
                gather_octets,
                scratch_octets,
                compact,
            )?;
            match counted(
                surface,
                shape.pool_octets,
                "single alignment and scratch pool",
            ) {
                Ok(pool) => break (pool, shape),
                Err(NativeOperatorResidenceError::Allocation {
                    source: ResidentRefusal::Driver { code: 2, .. },
                    ..
                }) if tile_rows > 1 => {
                    allocation_refusals += 1;
                    tile_rows /= 2;
                }
                Err(error) => return Err(error),
            }
        };
        let aligned_octets = pool_shape.aligned_octets;
        let mass_octets = pool_shape.mass_octets;
        let score_octets = pool_shape.score_octets;
        let aligned_offset = pool_shape.aligned_offset;
        let mass_offset = pool_shape.mass_offset;
        let score_offset = pool_shape.score_offset;
        let vector_offset = pool_shape.vector_offset;
        let gather_offset = pool_shape.gather_offset;
        let decode_offset = pool_shape.decode_offset;
        let scratch_offset = pool_shape.scratch_offset;
        let pool_octets = pool_shape.pool_octets;
        let zero_row_octets = zero_row.as_ref().map_or(0, |row| row.octets as u64);
        let mut total = raw_octets.max(1).checked_add(zero_row_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        total = total
            .checked_add(
                u64::try_from(pool_octets).map_err(|_| NativeOperatorResidenceError::Extent)?,
            )
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let mut resident_offset = 0usize;
        for at in 0..ecology.coefficient_populations.len() {
            let span = stored_spans[at];
            let base = resident_offset;
            let mut delivered = 0usize;
            let mut copy = |offset: usize, octets: &[u8]| {
                if offset != delivered || offset.checked_add(octets.len()).is_none_or(|end| end > span) {
                    return Err(NativeOperatorResidenceError::Witness);
                }
                surface
                    .copy_octets(&raw.buffer, base + offset, octets)
                    .map_err(NativeOperatorResidenceError::from)?;
                delivered += octets.len();
                Ok(())
            };
            if layouts[at].is_some() { intake.deliver_retained(at, &mut copy)?; }
            else { intake.deliver(at, &mut copy)?; }
            if delivered != span { return Err(NativeOperatorResidenceError::Witness); }
            resident_offset = resident_offset
                .checked_add(span)
                .ok_or(NativeOperatorResidenceError::Extent)?;
        }
        if resident_offset as u64 != raw_octets {
            return Err(NativeOperatorResidenceError::Witness);
        }

        let mut populations = Vec::with_capacity(ecology.coefficient_populations.len());
        let mut raw_offset = 0u64;
        for (at, population) in ecology.coefficient_populations.iter().enumerate() {
            let words = u32::try_from(population.coefficient_population)
                .map_err(|_| NativeOperatorResidenceError::Extent)?;
            let (rows, dim) = match population.shape.as_slice() {
                [extent] => (1usize, *extent),
                [rows, dim] => (*rows, *dim),
                _ => return Err(NativeOperatorResidenceError::Rank),
            };
            let stored_words = u32::try_from(stored_spans[at] / 2).map_err(|_| NativeOperatorResidenceError::Extent)?;
            let frame = if stored_words == 0 {
                // This is the existing BF16 zero-population convention: zero has no lowest ulp.
                ResidentBfloat16Frame { exponent: 0 }
            } else { unsafe {
                surface.readout().resident_bfloat16_frames(
                    std::ptr::null_mut(),
                    pool.device_ptr() + scratch_offset as u64,
                    &[ResidentBfloat16Population {
                        stored: raw.device_ptr() + raw_offset,
                        count: stored_words,
                    }],
                )?
            }
            .into_iter()
            .next()
            .ok_or(NativeOperatorResidenceError::Extent)? };
            populations.push(ResidentNativeOperatorPopulation {
                ordinal: population.ordinal,
                raw_offset,
                words,
                rows,
                dim,
                frame,
                retained_rows: layouts[at].take(),
            });
            raw_offset = raw_offset
                .checked_add(stored_spans[at] as u64)
                .ok_or(NativeOperatorResidenceError::Extent)?;
        }
        let mut chronologies = BTreeMap::new();
        for operation in &ecology.operations {
            if let NativeOperationPrimitive::RotaryChronology {
                theta,
                head_width,
                rotated_width,
            } = operation.primitive
            {
                let key = (theta, head_width, rotated_width);
                if !chronologies.contains_key(&key) {
                    let elements = found_chronology(theta, head_width, rotated_width)?;
                    chronologies.insert(key, surface.mount_bands(&elements, 60)?);
                }
            }
        }
        let chronology_octets = chronologies
            .values()
            .map(BandElements::resident_octets)
            .sum::<u64>();
        total = total
            .checked_add(chronology_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let receipt = NativeOperatorResidenceReceipt {
            schema: NATIVE_OPERATOR_RESIDENCE_SCHEMA.to_owned(),
            device: surface.device_name().to_owned(),
            population_count: populations.len(),
            raw_coefficient_octets: raw_octets,
            logical_coefficient_octets: logical_octets,
            decoder_staging_octets: pool_shape.decode_octets as u64,
            decoder_zero_row_octets: zero_row_octets,
            retained_row_chart_octets: populations.iter().filter_map(|p| p.retained_rows.as_ref())
                .try_fold(0u64, |sum, rows| (rows.len() as u64).checked_mul(4)
                    .and_then(|octets| sum.checked_add(octets)).ok_or(NativeOperatorResidenceError::Extent))?,
            aligned_tile_octets: aligned_octets as u64,
            row_mass_octets: mass_octets as u64,
            score_octets: score_octets as u64,
            vector_workspace_octets: vector_octets as u64,
            addressed_occurrence_rows,
            addressed_occurrence_octets: gather_octets as u64,
            reduction_scratch_octets: scratch_octets as u64,
            pooled_apparatus_octets: pool_octets as u64,
            total_resident_octets: total,
            available_before_mount: available,
            available_after_raw_mount: available_after_raw as u64,
            available_after_decoder_base_mount: available_after_decoder_base as u64,
            target_tile_rows: NATIVE_OPERATOR_TILE_ROWS,
            tile_rows,
            mass_score_rows: NATIVE_OPERATOR_TILE_ROWS,
            alignment_allocation_refusals: allocation_refusals,
            widest_dim,
            ingress_octets: raw_octets.checked_add(zero_row_octets).ok_or(NativeOperatorResidenceError::Extent)?,
            complete_population_frames: populations.len(),
            chronology_population: chronologies.len(),
            chronology_octets,
        };
        Ok(Self {
            surface,
            raw,
            zero_row,
            pool,
            aligned_offset,
            mass_offset,
            _score_offset: score_offset,
            _vector_offset: vector_offset,
            gather_offset,
            decode_offset,
            scratch_offset,
            chronologies,
            populations,
            receipt,
            slot_in_use: std::cell::Cell::new(false),
            decoder_census: std::cell::Cell::new(NativeOperatorDecoderCensus::default()),
        })
    }

    pub fn receipt(&self) -> &NativeOperatorResidenceReceipt {
        &self.receipt
    }

    pub fn decoder_census(&self) -> NativeOperatorDecoderCensus {
        self.decoder_census.get()
    }

    pub fn populations(&self) -> &[ResidentNativeOperatorPopulation] {
        &self.populations
    }

    pub(crate) fn surface(&self) -> &'chart ResidentSurface<'chart> {
        self.surface
    }

    pub(crate) fn population_frame(
        &self,
        population: NativeTensorOrdinal,
    ) -> Result<ResidentBfloat16Frame, NativeOperatorResidenceError> {
        self.populations
            .get(population.0 as usize)
            .map(|population| population.frame)
            .ok_or(NativeOperatorResidenceError::Population)
    }

    pub(crate) fn chronology(
        &self,
        theta: u64,
        head_width: usize,
        rotated_width: usize,
    ) -> Result<&BandElements<'chart>, NativeOperatorResidenceError> {
        self.chronologies
            .get(&(theta, head_width, rotated_width))
            .ok_or(NativeOperatorResidenceError::Chronology)
    }

    pub(crate) fn aligned_row_capacity(
        &self,
        population: NativeTensorOrdinal,
    ) -> Result<usize, NativeOperatorResidenceError> {
        let descriptor = self
            .populations
            .get(population.0 as usize)
            .ok_or(NativeOperatorResidenceError::Population)?;
        Ok(((self.receipt.aligned_tile_octets as usize)
            / descriptor.dim
            / std::mem::size_of::<i64>())
        .min(self.receipt.mass_score_rows))
    }

    /// Gather arbitrary row addresses into the reserved resident vector workspace, then ask the
    /// fixed-frame mouth for the selected population's exact aligned octave bound.  The gathered
    /// BF16 codewords remain on the card and are the source consumed by the lookup operation.
    pub(crate) fn gather_rows(
        &self,
        population: NativeTensorOrdinal,
        addresses: &[u32],
    ) -> Result<ResidentBfloat16Selection, NativeOperatorResidenceError> {
        if self.slot_in_use.get() {
            return Err(NativeOperatorResidenceError::Tile);
        }
        let descriptor = self
            .populations
            .get(population.0 as usize)
            .ok_or(NativeOperatorResidenceError::Population)?;
        let row_octets = descriptor
            .dim
            .checked_mul(2)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let gathered_octets = addresses
            .len()
            .checked_mul(row_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let aligned_row_capacity = self.aligned_row_capacity(population)?;
        if addresses.is_empty()
            || addresses.len() > aligned_row_capacity
            || addresses.len() > self.receipt.addressed_occurrence_rows
            || gathered_octets > self.receipt.addressed_occurrence_octets as usize
            || addresses
                .iter()
                .any(|address| *address as usize >= descriptor.rows)
        {
            return Err(NativeOperatorResidenceError::Tile);
        }
        for (at, address) in addresses.iter().enumerate() {
            let physical = match &descriptor.retained_rows {
                None => Some(*address as usize),
                Some(rows) => rows.binary_search(address).ok(),
            };
            self.decode_run(descriptor, self.gather_offset + at * row_octets, physical, 1)?;
        }
        if descriptor.retained_rows.is_some() {
            let mut census = self.decoder_census.get();
            census.completed_lookup_rows += addresses.len() as u64;
            self.decoder_census.set(census);
        }
        let count = addresses
            .len()
            .checked_mul(descriptor.dim)
            .and_then(|value| u32::try_from(value).ok())
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let mounted = unsafe {
            self.surface.readout().mount_bfloat16_pooled_fixed_frame(
                std::ptr::null_mut(),
                self.pool.device_ptr() + self.scratch_offset as u64,
                &[FixedFramePooledMount {
                    stored: self.pool.device_ptr() + self.gather_offset as u64,
                    aligned: self.pool.device_ptr() + self.aligned_offset as u64,
                    mass: self.pool.device_ptr() + self.mass_offset as u64,
                    count,
                    rows: addresses.len(),
                    dim: descriptor.dim,
                    frame: descriptor.frame,
                }],
            )?
        }
        .into_iter()
        .next()
        .ok_or(NativeOperatorResidenceError::Tile)?;
        let entry_octaves = mounted.readout.entry_octaves();
        drop(mounted);
        Ok(ResidentBfloat16Selection {
            address: self.pool.device_ptr() + self.gather_offset as u64,
            rows: addresses.len(),
            width: descriptor.dim,
            frame: descriptor.frame,
            entry_octaves,
        })
    }

    /// Align one complete-row tile under the population's device-derived complete frame.  The
    /// mutable borrow makes the single alignment pool exclusive until the returned tile is dropped.
    pub fn align_tile<'residence>(
        &'residence self,
        population: NativeTensorOrdinal,
        first_row: usize,
        rows: usize,
    ) -> Result<NativeAlignedOperatorTile<'residence, 'chart>, NativeOperatorResidenceError> {
        if self.slot_in_use.get() {
            return Err(NativeOperatorResidenceError::Tile);
        }
        let descriptor = self
            .populations
            .get(population.0 as usize)
            .ok_or(NativeOperatorResidenceError::Population)?;
        let aligned_row_capacity = self.aligned_row_capacity(population)?;
        if rows == 0
            || rows > aligned_row_capacity
            || first_row >= descriptor.rows
            || first_row
                .checked_add(rows)
                .is_none_or(|end| end > descriptor.rows)
        {
            return Err(NativeOperatorResidenceError::Tile);
        }
        let word_offset = first_row
            .checked_mul(descriptor.dim)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let count = rows
            .checked_mul(descriptor.dim)
            .and_then(|value| u32::try_from(value).ok())
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let stored = if let Some(retained) = &descriptor.retained_rows {
            let decoded_octets = checked_product(&[rows, descriptor.dim, 2])?;
            if decoded_octets as u64 > self.receipt.decoder_staging_octets {
                return Err(NativeOperatorResidenceError::Tile);
            }
            for run in decoded_row_runs(retained, first_row, rows) {
                let destination = self.decode_offset.checked_add(checked_product(&[run.destination, descriptor.dim, 2])?)
                    .ok_or(NativeOperatorResidenceError::Extent)?;
                self.decode_run(descriptor,
                    destination,
                    run.physical, run.rows)?;
            }
            let mut census = self.decoder_census.get();
            census.completed_tiles += 1;
            self.decoder_census.set(census);
            self.pool.device_ptr() + self.decode_offset as u64
        } else {
            self.raw.device_ptr().checked_add(descriptor.raw_offset)
                .and_then(|value| value.checked_add((word_offset * 2) as u64))
                .ok_or(NativeOperatorResidenceError::Extent)?
        };
        let mounted = unsafe {
            self.surface.readout().mount_bfloat16_pooled_fixed_frame(
                std::ptr::null_mut(),
                self.pool.device_ptr() + self.scratch_offset as u64,
                &[FixedFramePooledMount {
                    stored,
                    aligned: self.pool.device_ptr() + self.aligned_offset as u64,
                    mass: self.pool.device_ptr() + self.mass_offset as u64,
                    count,
                    rows,
                    dim: descriptor.dim,
                    frame: descriptor.frame,
                }],
            )?
        }
        .into_iter()
        .next()
        .ok_or(NativeOperatorResidenceError::Tile)?;
        self.slot_in_use.set(true);
        Ok(NativeAlignedOperatorTile {
            population,
            first_row,
            rows,
            mounted,
            residence: self,
        })
    }

    /// Decode a contiguous run on the device. Missing rows use one zero row followed by
    /// non-overlapping doubling copies, not a host zero population or one transfer per row.
    fn decode_run(&self, descriptor: &ResidentNativeOperatorPopulation,
        destination: usize, physical: Option<usize>, rows: usize,
    ) -> Result<(), NativeOperatorResidenceError> {
        let row_octets = checked_product(&[descriptor.dim, 2])?;
        let octets = checked_product(&[rows, row_octets])?;
        if rows == 0 || destination.checked_add(octets).is_none_or(|end| end > self.pool.octets) {
            return Err(NativeOperatorResidenceError::Tile);
        }
        if let Some(physical) = physical {
            let offset = usize::try_from(descriptor.raw_offset).ok()
                .and_then(|base| physical.checked_mul(row_octets).and_then(|row| base.checked_add(row)))
                .ok_or(NativeOperatorResidenceError::Extent)?;
            self.surface.copy_resident_octets(&self.pool.buffer, destination,
                &self.raw.buffer, offset, octets)?;
            if descriptor.retained_rows.is_some() {
                self.count_decoder_copy(octets);
                let mut census = self.decoder_census.get();
                census.retained_runs += 1;
                self.decoder_census.set(census);
            }
        } else {
            let zero = self.zero_row.as_ref().ok_or(NativeOperatorResidenceError::Witness)?;
            self.surface.copy_resident_octets(&self.pool.buffer, destination,
                &zero.buffer, 0, row_octets)?;
            self.count_decoder_copy(row_octets);
            let mut filled = row_octets;
            while filled < octets {
                let copy = filled.min(octets - filled);
                self.surface.copy_resident_octets(&self.pool.buffer, destination + filled,
                    &self.pool.buffer, destination, copy)?;
                self.count_decoder_copy(copy);
                filled += copy;
            }
            let mut census = self.decoder_census.get();
            census.zero_runs += 1;
            self.decoder_census.set(census);
        }
        Ok(())
    }

    fn count_decoder_copy(&self, octets: usize) {
        let mut census = self.decoder_census.get();
        census.device_copy_calls += 1;
        census.device_copy_octets += octets as u64;
        self.decoder_census.set(census);
    }
}

#[derive(Debug, PartialEq, Eq)]
struct DecodedRowRun {
    destination: usize,
    rows: usize,
    physical: Option<usize>,
}

/// A finite storage decoder over a validated sorted row chart. Contiguous present rows share
/// one copy; gaps share one zero-fill run. The chart carries no claim about foreign omitted rows.
fn decoded_row_runs(retained: &[u32], first: usize, count: usize) -> Vec<DecodedRowRun> {
    let end = first + count;
    let mut cursor = first;
    let mut physical = retained.partition_point(|row| (*row as usize) < first);
    let mut runs = Vec::new();
    while cursor < end {
        let next = retained.get(physical).map_or(end, |row| (*row as usize).min(end));
        if next > cursor {
            runs.push(DecodedRowRun { destination: cursor - first, rows: next - cursor, physical: None });
            cursor = next;
        } else {
            let start = physical;
            while cursor < end && retained.get(physical).is_some_and(|row| *row as usize == cursor) {
                physical += 1;
                cursor += 1;
            }
            runs.push(DecodedRowRun { destination: cursor - first - (physical - start),
                rows: physical - start, physical: Some(start) });
        }
    }
    runs
}

#[cfg(test)]
mod restriction_tests {
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    use super::super::{mount_operator_surface, NativeAttentionTopology, NativeCarrierChart,
        NativeCarrierOrdinal, NativeCoefficientPopulation, NativeKvStanding, NativeLayerTopology,
        NativeOperatorNode, NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA};

    struct TestIntake { rows: Vec<u32>, words: Vec<u16>, gap: bool }

    impl NativeCoefficientIntake for TestIntake {
        fn populations(&self) -> usize { 1 }
        fn population_octets(&self, _: usize) -> Result<u64, NativeOperatorResidenceError> { Ok(54) }
        fn retained_rows(&self, _: usize) -> Result<Option<Vec<u32>>, NativeOperatorResidenceError> {
            Ok(Some(self.rows.clone()))
        }
        fn deliver_retained(&mut self, _: usize,
            sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
        ) -> Result<(), NativeOperatorResidenceError> {
            let bytes: Vec<u8> = self.words.iter().flat_map(|word| word.to_le_bytes()).collect();
            for (at, chunk) in bytes.chunks(7).enumerate() { sink(at * 7 + usize::from(self.gap), chunk)?; }
            Ok(())
        }
        fn deliver(&mut self, _: usize,
            sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
        ) -> Result<(), NativeOperatorResidenceError> {
            let mut bytes = vec![0; 54];
            for (physical, row) in self.rows.iter().enumerate() {
                for col in 0..3 {
                    bytes[*row as usize * 6 + col * 2..*row as usize * 6 + col * 2 + 2]
                        .copy_from_slice(&self.words[physical * 3 + col].to_le_bytes());
                }
            }
            sink(0, &bytes)
        }
    }

    fn test_ecology() -> NativeFullOperatorEcology {
        NativeFullOperatorEcology {
            schema: NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA.into(), shared_carrier_extent: 3,
            coefficient_populations: vec![NativeCoefficientPopulation {
                ordinal: NativeTensorOrdinal(0), shape: vec![9, 3], coefficient_population: 27 }],
            carriers: [3, 5, 7, 11].into_iter().enumerate().map(|(at, dim)| NativeCarrierChart {
                ordinal: NativeCarrierOrdinal(at as u32), axes: vec![NativeCarrierAxis::Fixed(dim)] }).collect(),
            operations: vec![NativeOperatorNode { ordinal: 0, layer: Some(0),
                primitive: NativeOperationPrimitive::Lookup { scale: super::super::NativeScaleConstraint::Rational { numerator: 1, denominator: 1 } }, inputs: vec![], output: NativeCarrierOrdinal(3),
                coefficients: vec![NativeTensorOrdinal(0)] }],
            layers: vec![NativeLayerTopology { ordinal: 0, attention: NativeAttentionTopology::Local,
                kv_standing: NativeKvStanding::Own, first_operation: 0, operation_population: 1 }],
            coefficient_obstructions: vec![],
        }
    }

    #[test]
    #[ignore = "requires CUDA; compare compact decoder with expanded reference on the device"]
    fn native_compact_tiles_gathers_and_frames_match_the_expanded_chart() {
        let readout = ResidentReadout::new().expect("CUDA");
        let surface = mount_operator_surface(&readout).unwrap();
        let ecology = test_ecology();
        // Empty, isolated, interior gaps, contiguous runs, and the full population. Negative
        // zero remains an exact stored codeword; decoding only inserts positive zero in gaps.
        for rows in [vec![], vec![4], vec![1, 3, 8], vec![0, 1, 2, 6, 7, 8], (0..9).collect()] {
            let words = rows.iter().enumerate().flat_map(|(at, _)|
                [0x3f80 + (at as u16) * 0x80, 0xc000, 0x8000]).collect();
            let mut intake = TestIntake { rows, words, gap: false };
            let compact = NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut intake).unwrap();
            let dense = NativeOperatorResidence::mount_expanded_reference(&surface, &ecology, &mut intake).unwrap();
            assert_eq!(compact.populations[0].frame, dense.populations[0].frame);
            assert_eq!(compact.receipt.raw_coefficient_octets, intake.rows.len() as u64 * 6);
            assert_eq!(dense.receipt.raw_coefficient_octets, 54);
            for first in 0..9 {
                for count in 1..=9 - first {
                    let left = compact.align_tile(NativeTensorOrdinal(0), first, count).unwrap();
                    let right = dense.align_tile(NativeTensorOrdinal(0), first, count).unwrap();
                    let mut a = vec![0u8; count * 3 * 8];
                    let mut b = a.clone();
                    compact.pool.buffer.copy_range_to_slice(compact.aligned_offset, &mut a).unwrap();
                    dense.pool.buffer.copy_range_to_slice(dense.aligned_offset, &mut b).unwrap();
                    assert_eq!(a, b, "tile {first}+{count}, rows {:?}", intake.rows);
                    assert_eq!(left.mounted.readout.entry_octaves(), right.mounted.readout.entry_octaves());
                    assert!(compact.gather_rows(NativeTensorOrdinal(0), &[0]).is_err(), "live tile owns its aperture");
                }
                compact.gather_rows(NativeTensorOrdinal(0), &[first as u32]).unwrap();
                dense.gather_rows(NativeTensorOrdinal(0), &[first as u32]).unwrap();
                let mut a = [0u8; 6];
                let mut b = [0u8; 6];
                compact.pool.buffer.copy_range_to_slice(compact.gather_offset, &mut a).unwrap();
                dense.pool.buffer.copy_range_to_slice(dense.gather_offset, &mut b).unwrap();
                assert_eq!(a, b);
            }
        }
        let mut invalid = TestIntake { rows: vec![1, 1], words: vec![0; 6], gap: false };
        assert!(matches!(NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut invalid),
            Err(NativeOperatorResidenceError::Witness)));
        invalid.rows = vec![9];
        assert!(matches!(NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut invalid),
            Err(NativeOperatorResidenceError::Witness)));
        invalid.rows = vec![1]; invalid.words = vec![0; 3]; invalid.gap = true;
        assert!(matches!(NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut invalid),
            Err(NativeOperatorResidenceError::Witness)));
        invalid.gap = false; invalid.words.pop();
        assert!(matches!(NativeOperatorResidence::mount_from_intake(&surface, &ecology, &mut invalid),
            Err(NativeOperatorResidenceError::Witness)));
    }

    #[test]
    fn every_small_restriction_and_partial_tile_decodes_exactly_once() {
        for mask in 0u32..(1 << 9) {
            let retained: Vec<u32> = (0..9).filter(|row| mask & (1 << row) != 0).collect();
            for first in 0..9 {
                for count in 1..=9 - first {
                    let mut returned = Vec::new();
                    for run in decoded_row_runs(&retained, first, count) {
                        assert_eq!(run.destination, returned.len());
                        assert!(run.rows > 0);
                        for row in 0..run.rows {
                            returned.push(run.physical.map(|at| retained[at + row]));
                        }
                    }
                    assert_eq!(returned, (first..first + count).map(|row|
                        retained.binary_search(&(row as u32)).ok().map(|_| row as u32))
                        .collect::<Vec<_>>());
                }
            }
        }
        assert!(decoded_row_runs(&[], 0, 0).is_empty());
    }

    #[test]
    fn compact_pool_counts_decoder_space_and_dense_pool_does_not_allocate_it() {
        let dense = OperatorPoolShape::for_rows(8, 16, 3, 128, 60, 16, false).unwrap();
        let compact = OperatorPoolShape::for_rows(8, 16, 3, 128, 60, 16, true).unwrap();
        assert_eq!(compact.decode_octets, 48);
        assert_eq!(compact.pool_octets, dense.pool_octets + 48);
        assert!(compact.scratch_offset >= compact.decode_offset + 48);
        assert!(compact.scratch_offset < compact.decode_offset + 48 + 16);
        assert_eq!(compact.scratch_offset % 16, 0);
        assert_eq!(compact.mass_offset % 16, 0);
        assert_eq!(dense.decode_octets, 0);
    }
}

#[derive(Debug, Error)]
pub enum NativeOperatorResidenceError {
    #[error("operator ecology: {0}")]
    Ecology(#[from] NativeFullOperatorError),
    #[error("resident apparatus: {0}")]
    Resident(#[from] ResidentRefusal),
    #[error("resident allocation for {part}: {source}")]
    Allocation {
        part: &'static str,
        source: ResidentRefusal,
    },
    #[error("exact BF16 mouth: {0}")]
    Fiber(#[from] FiberError),
    #[error("source I/O: {0}")]
    Io(String),
    #[error("the cold source witness does not match the native coefficient population")]
    Witness,
    #[error("the coefficient population has unsupported rank")]
    Rank,
    #[error("the coefficient or apparatus extent overflowed")]
    Extent,
    #[error("there is no such native coefficient population")]
    Population,
    #[error("the requested aligned tile is outside the population or the single-slot aperture")]
    Tile,
    #[error("the declared rotary chronology is absent or malformed")]
    Chronology,
}

fn counted<'chart>(
    surface: &'chart ResidentSurface<'chart>,
    octets: usize,
    part: &'static str,
) -> Result<CountedOctets<'chart>, NativeOperatorResidenceError> {
    Ok(CountedOctets {
        surface,
        buffer: surface
            .alloc_octets(octets)
            .map_err(|source| NativeOperatorResidenceError::Allocation { part, source })?,
        octets,
    })
}

fn checked_product(factors: &[usize]) -> Result<usize, NativeOperatorResidenceError> {
    factors.iter().try_fold(1usize, |total, factor| {
        total
            .checked_mul(*factor)
            .ok_or(NativeOperatorResidenceError::Extent)
    })
}

fn greatest_power_of_two(value: usize) -> Option<usize> {
    (value > 0).then(|| 1usize << value.ilog2())
}

struct OperatorPoolShape {
    aligned_octets: usize,
    mass_octets: usize,
    score_octets: usize,
    aligned_offset: usize,
    mass_offset: usize,
    score_offset: usize,
    vector_offset: usize,
    gather_offset: usize,
    decode_offset: usize,
    decode_octets: usize,
    scratch_offset: usize,
    pool_octets: usize,
}

impl OperatorPoolShape {
    fn for_rows(
        aligned_rows: usize,
        mass_score_rows: usize,
        widest_dim: usize,
        vector_octets: usize,
        gather_octets: usize,
        scratch_octets: usize,
        compact: bool,
    ) -> Result<Self, NativeOperatorResidenceError> {
        let aligned_octets = checked_product(&[aligned_rows, widest_dim, 8])?;
        let mass_octets = checked_product(&[mass_score_rows, 16])?;
        let score_octets = checked_product(&[mass_score_rows, 16])?;
        let aligned_offset = 0usize;
        // Masses and reduction scratch contain wide integer words. Odd BF16 row widths must
        // not let their preceding byte regions misalign those device addresses.
        let align_wide = |octets: usize| octets.checked_add(15).map(|value| value & !15)
            .ok_or(NativeOperatorResidenceError::Extent);
        let mass_offset = align_wide(aligned_octets)?;
        let score_offset = mass_offset
            .checked_add(mass_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let vector_offset = score_offset
            .checked_add(score_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let gather_offset = vector_offset
            .checked_add(vector_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let decode_offset = gather_offset
            .checked_add(gather_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let decode_octets = if compact { checked_product(&[aligned_rows, widest_dim, 2])? } else { 0 };
        let scratch_offset = align_wide(decode_offset.checked_add(decode_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?)?;
        let pool_octets = scratch_offset
            .checked_add(scratch_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        Ok(Self {
            aligned_octets,
            mass_octets,
            score_octets,
            aligned_offset,
            mass_offset,
            score_offset,
            vector_offset,
            gather_offset,
            decode_offset,
            decode_octets,
            scratch_offset,
            pool_octets,
        })
    }
}

fn vector_workspace_widths(
    ecology: &NativeFullOperatorEcology,
) -> Result<[usize; 3], NativeOperatorResidenceError> {
    let emitted = ecology
        .operations
        .last()
        .and_then(|operation| ecology.carriers.get(operation.output.0 as usize))
        .and_then(|carrier| carrier.axes.last())
        .and_then(|axis| match axis {
            NativeCarrierAxis::Fixed(width) => Some(*width),
            _ => None,
        })
        .ok_or(NativeOperatorResidenceError::Extent)?;
    let mut widths = ecology
        .carriers
        .iter()
        .filter_map(|carrier| match carrier.axes.last() {
            Some(NativeCarrierAxis::Fixed(width)) if *width != emitted => Some(*width),
            _ => None,
        })
        .collect::<Vec<_>>();
    widths.sort_unstable();
    widths.dedup();
    let three = widths.into_iter().rev().take(3).collect::<Vec<_>>();
    if three.len() != 3 {
        return Err(NativeOperatorResidenceError::Extent);
    }
    Ok([three[0], three[1], three[2]])
}

fn found_chronology(
    theta: u64,
    head_width: usize,
    rotated_width: usize,
) -> Result<Vec<((i64, i64), (i64, i64))>, NativeOperatorResidenceError> {
    if theta == 0
        || head_width == 0
        || head_width % 2 != 0
        || rotated_width > head_width
        || rotated_width % 2 != 0
    {
        return Err(NativeOperatorResidenceError::Chronology);
    }
    let pairs = head_width / 2;
    let rotated_pairs = rotated_width / 2;
    if rotated_pairs == 0 {
        let one = 1i64 << 60;
        return Ok((0..pairs).map(|_| ((one, one), (0, 0))).collect());
    }
    let ratio = AlgebraicRoot::nth_root(&Rat::from_integer(BigInt::from(theta)), pairs as u32, 64)
        .map_err(|_| NativeOperatorResidenceError::Chronology)?
        .enclosure()
        .reciprocal()
        .map_err(|_| NativeOperatorResidenceError::Chronology)?;
    let mut angle = ExactInterval::point(Rat::from_integer(BigInt::from(1)));
    let mut angles = Vec::with_capacity(rotated_pairs);
    for _ in 0..rotated_pairs {
        angles.push(angle.clone());
        angle = angle
            .times(&ratio)
            .map_err(|_| NativeOperatorResidenceError::Chronology)?
            .round_out(64)
            .map_err(|_| NativeOperatorResidenceError::Chronology)?;
    }
    let workers = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1)
        .min(rotated_pairs.max(1));
    let chunk = rotated_pairs.div_ceil(workers);
    let rotated = std::thread::scope(|scope| {
        let mut handles = Vec::new();
        for slice in angles.chunks(chunk) {
            handles.push(scope.spawn(move || {
                slice
                    .iter()
                    .map(|angle| -> Result<_, ()> {
                        let (cos_low, sin_low) =
                            CertifiedSeries::circular_series(&angle.lower, 40).map_err(|_| ())?;
                        let (cos_high, sin_high) =
                            CertifiedSeries::circular_series(&angle.upper, 40).map_err(|_| ())?;
                        let cos = ExactInterval::new(
                            cos_high
                                .enclosure()
                                .lower
                                .clone()
                                .min(cos_low.enclosure().lower.clone()),
                            cos_low
                                .enclosure()
                                .upper
                                .clone()
                                .max(cos_high.enclosure().upper.clone()),
                        )
                        .map_err(|_| ())?;
                        let sin = ExactInterval::new(
                            sin_low
                                .enclosure()
                                .lower
                                .clone()
                                .min(sin_high.enclosure().lower.clone()),
                            sin_high
                                .enclosure()
                                .upper
                                .clone()
                                .max(sin_low.enclosure().upper.clone()),
                        )
                        .map_err(|_| ())?;
                        let cos = DyadicEnclosure::of_interval(&cos, 60).map_err(|_| ())?;
                        let sin = DyadicEnclosure::of_interval(&sin, 60).map_err(|_| ())?;
                        Ok(((cos.lo, cos.hi), (sin.lo, sin.hi)))
                    })
                    .collect::<Result<Vec<_>, _>>()
            }));
        }
        let mut values = Vec::with_capacity(rotated_pairs);
        for handle in handles {
            values.extend(handle.join().map_err(|_| ())??);
        }
        Ok::<_, ()>(values)
    })
    .map_err(|_| NativeOperatorResidenceError::Chronology)?;
    let mut elements = rotated;
    let one = 1i64 << 60;
    elements.extend((rotated_pairs..pairs).map(|_| ((one, one), (0, 0))));
    Ok(elements)
}
