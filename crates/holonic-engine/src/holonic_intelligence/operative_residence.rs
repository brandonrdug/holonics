//! Full packed coefficient residency for the source-neutral operator ecology.
//!
//! Every coefficient crosses the device boundary once as its exact BF16 codeword.  The complete
//! population stays packed; one mutually-exclusive aligned tile is reused under the complete
//! tensor's frame.  The aligned tile is an arithmetic representation, never morphology identity.

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
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeOperatorResidenceReceipt {
    pub schema: String,
    pub device: String,
    pub population_count: usize,
    pub raw_coefficient_octets: u64,
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

/// One full packed coefficient residence.  It owns one ecology's complete coefficient standing
/// and one aligned tile aperture; there is no second aligned slot and no host fallback.
pub struct NativeOperatorResidence<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    raw: CountedOctets<'chart>,
    pool: CountedOctets<'chart>,
    aligned_offset: usize,
    mass_offset: usize,
    _score_offset: usize,
    _vector_offset: usize,
    gather_offset: usize,
    scratch_offset: usize,
    chronologies: BTreeMap<(u64, usize, usize), BandElements<'chart>>,
    populations: Vec<ResidentNativeOperatorPopulation>,
    receipt: NativeOperatorResidenceReceipt,
    /// The single alignment slot's occupancy: one aligned tile at a time, refused at runtime
    /// rather than by a mutable borrow, so a segment may hold its tile while it reads bands and
    /// positions.
    slot_in_use: std::cell::Cell<bool>,
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
        ecology.validate()?;
        if intake.populations() != ecology.coefficient_populations.len() {
            return Err(NativeOperatorResidenceError::Witness);
        }
        for (at, population) in ecology.coefficient_populations.iter().enumerate() {
            if intake.population_octets(at)? != population.coefficient_population * 2 {
                return Err(NativeOperatorResidenceError::Witness);
            }
        }
        let raw_octets = ecology.coefficient_octets()?;
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
            usize::try_from(raw_octets).map_err(|_| NativeOperatorResidenceError::Extent)?,
            "packed coefficients",
        )?;
        let available_after_raw = surface.memory()?.free_bytes;
        let fixed_pool_octets = vector_octets
            .checked_add(gather_octets)
            .and_then(|value| value.checked_add(scratch_octets))
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let per_row_octets = widest_dim
            .checked_mul(8)
            .and_then(|aligned| aligned.checked_add(32))
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let admitted_rows = available_after_raw.saturating_sub(fixed_pool_octets) / per_row_octets;
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
        let scratch_offset = pool_shape.scratch_offset;
        let pool_octets = pool_shape.pool_octets;
        let mut total = raw_octets
            .checked_add(
                u64::try_from(pool_octets).map_err(|_| NativeOperatorResidenceError::Extent)?,
            )
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let mut resident_offset = 0usize;
        for at in 0..ecology.coefficient_populations.len() {
            let span = usize::try_from(intake.population_octets(at)?)
                .map_err(|_| NativeOperatorResidenceError::Extent)?;
            let base = resident_offset;
            intake.deliver(at, &mut |offset, octets| {
                if offset + octets.len() > span {
                    return Err(NativeOperatorResidenceError::Witness);
                }
                surface
                    .copy_octets(&raw.buffer, base + offset, octets)
                    .map_err(NativeOperatorResidenceError::from)
            })?;
            resident_offset = resident_offset
                .checked_add(span)
                .ok_or(NativeOperatorResidenceError::Extent)?;
        }
        if resident_offset as u64 != raw_octets {
            return Err(NativeOperatorResidenceError::Witness);
        }

        let mut populations = Vec::with_capacity(ecology.coefficient_populations.len());
        let mut raw_offset = 0u64;
        for population in &ecology.coefficient_populations {
            let words = u32::try_from(population.coefficient_population)
                .map_err(|_| NativeOperatorResidenceError::Extent)?;
            let (rows, dim) = match population.shape.as_slice() {
                [extent] => (1usize, *extent),
                [rows, dim] => (*rows, *dim),
                _ => return Err(NativeOperatorResidenceError::Rank),
            };
            let frame = unsafe {
                surface.readout().resident_bfloat16_frames(
                    std::ptr::null_mut(),
                    pool.device_ptr() + scratch_offset as u64,
                    &[ResidentBfloat16Population {
                        stored: raw.device_ptr() + raw_offset,
                        count: words,
                    }],
                )?
            }
            .into_iter()
            .next()
            .ok_or(NativeOperatorResidenceError::Extent)?;
            populations.push(ResidentNativeOperatorPopulation {
                ordinal: population.ordinal,
                raw_offset,
                words,
                rows,
                dim,
                frame,
            });
            raw_offset = raw_offset
                .checked_add(population.coefficient_population * 2)
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
            target_tile_rows: NATIVE_OPERATOR_TILE_ROWS,
            tile_rows,
            mass_score_rows: NATIVE_OPERATOR_TILE_ROWS,
            alignment_allocation_refusals: allocation_refusals,
            widest_dim,
            ingress_octets: raw_octets,
            complete_population_frames: populations.len(),
            chronology_population: chronologies.len(),
            chronology_octets,
        };
        Ok(Self {
            surface,
            raw,
            pool,
            aligned_offset,
            mass_offset,
            _score_offset: score_offset,
            _vector_offset: vector_offset,
            gather_offset,
            scratch_offset,
            chronologies,
            populations,
            receipt,
            slot_in_use: std::cell::Cell::new(false),
        })
    }

    pub fn receipt(&self) -> &NativeOperatorResidenceReceipt {
        &self.receipt
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
            let source_offset = usize::try_from(descriptor.raw_offset)
                .ok()
                .and_then(|base| {
                    (*address as usize)
                        .checked_mul(row_octets)
                        .and_then(|offset| base.checked_add(offset))
                })
                .ok_or(NativeOperatorResidenceError::Extent)?;
            self.surface.copy_resident_octets(
                &self.pool.buffer,
                self.gather_offset + at * row_octets,
                &self.raw.buffer,
                source_offset,
                row_octets,
            )?;
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
        let stored = self
            .raw
            .device_ptr()
            .checked_add(descriptor.raw_offset)
            .and_then(|value| value.checked_add((word_offset * 2) as u64))
            .ok_or(NativeOperatorResidenceError::Extent)?;
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
    ) -> Result<Self, NativeOperatorResidenceError> {
        let aligned_octets = checked_product(&[aligned_rows, widest_dim, 8])?;
        let mass_octets = checked_product(&[mass_score_rows, 16])?;
        let score_octets = checked_product(&[mass_score_rows, 16])?;
        let aligned_offset = 0usize;
        let mass_offset = aligned_octets;
        let score_offset = mass_offset
            .checked_add(mass_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let vector_offset = score_offset
            .checked_add(score_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let gather_offset = vector_offset
            .checked_add(vector_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
        let scratch_offset = gather_offset
            .checked_add(gather_octets)
            .ok_or(NativeOperatorResidenceError::Extent)?;
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
