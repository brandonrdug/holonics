//! Exact phase-resolved current and its carried causal convolution.
//!
//! A coarse current cell is not one scalar.  It is a local polynomial
//! `x_0 + x_1 z + ... + x_(g-1) z^(g-1)`.  Multiplication by a response cell
//! transports a product with phase exponent `a + b`; quotient and remainder
//! by `g` select the later coarse cell and its local phase.  The carry is
//! therefore causal structure, not rounding error.

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{CpuExecutionError, CpuExecutionReceipt, CpuExecutor};

pub mod resident;

const SECTION_SCHEMA: &str = "holonic-engine.exact-phase-current-section.v1";
const RECEIPT_SCHEMA: &str = "holonic-engine.phase-current-convolution-receipt.v1";
const SPECTRUM_SCHEMA: &str = "holonic-engine.exact-phase-transport-spectrum.v1";
const EMISSION_SCHEMA: &str = "holonic-engine.phase-current-emission-receipt.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PhaseCurrentReceiverId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PhaseCurrentLineageId(pub u64);

/// One exact receiver-local current with a finite phase fiber in every cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactPhaseCurrentSection {
    pub schema: String,
    pub receiver: PhaseCurrentReceiverId,
    pub lineage: PhaseCurrentLineageId,
    pub origin: Rat,
    pub sample_step: Rat,
    pub phase_extent: u32,
    raw_extent: usize,
    /// Cell-major phase coefficients.  Only the final cell may contain
    /// structural zero padding beyond `raw_extent`.
    pub cells: Vec<Vec<BigInt>>,
}

impl ExactPhaseCurrentSection {
    pub fn from_i32(
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        phase_extent: usize,
        samples: &[i32],
    ) -> Result<Self, PhaseCurrentError> {
        Self::from_integers(
            receiver,
            lineage,
            origin,
            sample_step,
            phase_extent,
            samples.iter().copied().map(BigInt::from).collect(),
        )
    }

    pub fn from_integers(
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        phase_extent: usize,
        samples: Vec<BigInt>,
    ) -> Result<Self, PhaseCurrentError> {
        if samples.is_empty() || phase_extent == 0 || !sample_step.is_positive() {
            return Err(PhaseCurrentError::MalformedSection);
        }
        let raw_extent = samples.len();
        let cells_needed = raw_extent.div_ceil(phase_extent);
        let padded_extent = cells_needed
            .checked_mul(phase_extent)
            .ok_or(PhaseCurrentError::CarrierOverflow)?;
        let mut padded = samples;
        padded.resize(padded_extent, BigInt::zero());
        let section = Self {
            schema: SECTION_SCHEMA.to_owned(),
            receiver,
            lineage,
            origin,
            sample_step,
            phase_extent: u32::try_from(phase_extent)
                .map_err(|_| PhaseCurrentError::CarrierOverflow)?,
            raw_extent,
            cells: padded
                .chunks_exact(phase_extent)
                .map(<[BigInt]>::to_vec)
                .collect(),
        };
        section.validate()?;
        Ok(section)
    }

    pub fn raw_extent(&self) -> usize {
        self.raw_extent
    }

    pub fn phase_extent_usize(&self) -> Result<usize, PhaseCurrentError> {
        usize::try_from(self.phase_extent).map_err(|_| PhaseCurrentError::CarrierOverflow)
    }

    pub fn flat_values(&self) -> Vec<BigInt> {
        self.cells
            .iter()
            .flatten()
            .take(self.raw_extent)
            .cloned()
            .collect()
    }

    /// The scalar quotient deliberately forgets local phase.
    pub fn integrated_cells(&self) -> Vec<BigInt> {
        self.cells
            .iter()
            .map(|cell| cell.iter().fold(BigInt::zero(), |sum, value| sum + value))
            .collect()
    }

    fn validate(&self) -> Result<(), PhaseCurrentError> {
        let phase_extent = self.phase_extent_usize()?;
        if self.schema != SECTION_SCHEMA
            || !self.sample_step.is_positive()
            || phase_extent == 0
            || self.raw_extent == 0
            || self.cells.is_empty()
            || self.cells.iter().any(|cell| cell.len() != phase_extent)
            || self
                .cells
                .len()
                .checked_mul(phase_extent)
                .ok_or(PhaseCurrentError::CarrierOverflow)?
                < self.raw_extent
            || self
                .cells
                .iter()
                .flatten()
                .skip(self.raw_extent)
                .any(|value| !value.is_zero())
        {
            return Err(PhaseCurrentError::MalformedSection);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhaseCurrentConvolutionReceipt {
    pub schema: String,
    pub source_lineage: PhaseCurrentLineageId,
    pub response_lineage: PhaseCurrentLineageId,
    pub output: ExactPhaseCurrentSection,
    /// Nonzero coefficient products which remain in the same coarse cell.
    pub local_phase_products: BigUint,
    /// Nonzero coefficient products whose phase sum crosses a cell boundary.
    pub carried_phase_products: BigUint,
    pub exact_integer_carrier: String,
    pub execution: CpuExecutionReceipt,
}

/// One signed population in a receiver-relative phase section.
///
/// Positive and negative current remain separate even when their net is
/// zero.  A cancellation is therefore a received relation, not an absent
/// emission.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactSignedPhasePopulation {
    pub positive_occurrences: BigUint,
    pub negative_occurrences: BigUint,
    pub positive_current: BigUint,
    pub negative_current: BigUint,
    pub net_current: BigInt,
}

impl ExactSignedPhasePopulation {
    fn validate(&self) -> Result<(), PhaseCurrentError> {
        if self.net_current
            != BigInt::from(self.positive_current.clone())
                - BigInt::from(self.negative_current.clone())
        {
            return Err(PhaseCurrentError::MalformedSpectrum);
        }
        Ok(())
    }

    fn finish(&mut self) {
        self.net_current = BigInt::from(self.positive_current.clone())
            - BigInt::from(self.negative_current.clone());
    }
}

/// The receiver face of all exact products which arrive at one local phase
/// with one cell carry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactPhaseTransportBand {
    pub target_phase: u32,
    /// `0` remains in the source/response coarse-cell sum; `1` crosses its
    /// local boundary.  Two finite phase polynomials cannot carry farther.
    pub cell_carry: u8,
    pub population: ExactSignedPhasePopulation,
}

/// A receiver-relative emission spectrum over an exact carried current.
///
/// This is not a Fourier magnitude and it is not source-intrinsic.  It is the
/// exact quotient obtained by asking how every nonzero source/response
/// product reaches the target receiver's local phase chart.  The complete
/// target chronology remains the separate convolution receipt.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactPhaseTransportSpectrum {
    pub schema: String,
    pub source_receiver: PhaseCurrentReceiverId,
    pub source_lineage: PhaseCurrentLineageId,
    pub response_receiver: PhaseCurrentReceiverId,
    pub response_lineage: PhaseCurrentLineageId,
    pub target_receiver: PhaseCurrentReceiverId,
    pub target_lineage: PhaseCurrentLineageId,
    pub origin: Rat,
    pub sample_step: Rat,
    pub phase_extent: u32,
    /// Exact populations at every phase of the emitted current.
    pub source_phases: Vec<ExactSignedPhasePopulation>,
    /// Exact populations at every phase of the transported response.
    pub response_phases: Vec<ExactSignedPhasePopulation>,
    /// Ordered first by carry, then by target phase.  Structural zero bands
    /// remain present so the receiver aperture is inspectable.
    pub target_bands: Vec<ExactPhaseTransportBand>,
    pub local_phase_products: BigUint,
    pub carried_phase_products: BigUint,
    pub net_transported_current: BigInt,
}

impl ExactPhaseTransportSpectrum {
    fn validate(&self) -> Result<(), PhaseCurrentError> {
        let phase_extent =
            usize::try_from(self.phase_extent).map_err(|_| PhaseCurrentError::CarrierOverflow)?;
        let band_extent = phase_extent
            .checked_mul(2)
            .ok_or(PhaseCurrentError::CarrierOverflow)?;
        if self.schema != SPECTRUM_SCHEMA
            || phase_extent == 0
            || !self.sample_step.is_positive()
            || self.source_phases.len() != phase_extent
            || self.response_phases.len() != phase_extent
            || self.target_bands.len() != band_extent
        {
            return Err(PhaseCurrentError::MalformedSpectrum);
        }
        for population in &self.source_phases {
            population.validate()?;
        }
        for population in &self.response_phases {
            population.validate()?;
        }

        let mut local_occurrences = BigUint::zero();
        let mut carried_occurrences = BigUint::zero();
        let mut net_transported_current = BigInt::zero();
        for (index, band) in self.target_bands.iter().enumerate() {
            let expected_carry = u8::try_from(index / phase_extent)
                .map_err(|_| PhaseCurrentError::CarrierOverflow)?;
            let expected_phase = u32::try_from(index % phase_extent)
                .map_err(|_| PhaseCurrentError::CarrierOverflow)?;
            if band.cell_carry != expected_carry || band.target_phase != expected_phase {
                return Err(PhaseCurrentError::MalformedSpectrum);
            }
            band.population.validate()?;
            let occurrences =
                &band.population.positive_occurrences + &band.population.negative_occurrences;
            if band.cell_carry == 0 {
                local_occurrences += occurrences;
            } else {
                carried_occurrences += occurrences;
            }
            net_transported_current += &band.population.net_current;
        }
        if local_occurrences != self.local_phase_products
            || carried_occurrences != self.carried_phase_products
            || net_transported_current != self.net_transported_current
        {
            return Err(PhaseCurrentError::MalformedSpectrum);
        }

        let mut source_current = BigInt::zero();
        for population in &self.source_phases {
            source_current += &population.net_current;
        }
        let mut response_current = BigInt::zero();
        for population in &self.response_phases {
            response_current += &population.net_current;
        }
        if source_current * response_current != self.net_transported_current {
            return Err(PhaseCurrentError::MalformedSpectrum);
        }
        Ok(())
    }
}

/// The complete exact propagation together with its receiver-relative
/// phase-and-carry spectral face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PhaseCurrentEmissionReceipt {
    pub schema: String,
    pub propagation: PhaseCurrentConvolutionReceipt,
    pub spectrum: ExactPhaseTransportSpectrum,
}

/// Receive the exact phase-and-carry spectrum without enumerating the full
/// output chronology.
///
/// Distributivity permits every signed product population to be assembled
/// from phase-local positive and negative currents.  This is exact and scales
/// with receiver phase extent rather than with the pairwise sample product.
pub fn receive_phase_transport_spectrum(
    source: &ExactPhaseCurrentSection,
    response: &ExactPhaseCurrentSection,
    target_receiver: PhaseCurrentReceiverId,
    target_lineage: PhaseCurrentLineageId,
) -> Result<ExactPhaseTransportSpectrum, PhaseCurrentError> {
    source.validate()?;
    response.validate()?;
    if source.phase_extent != response.phase_extent || source.sample_step != response.sample_step {
        return Err(PhaseCurrentError::ChartMismatch);
    }
    let phase_extent = source.phase_extent_usize()?;
    let source_phases = signed_phase_populations(&source.flat_values(), phase_extent);
    let response_phases = signed_phase_populations(&response.flat_values(), phase_extent);
    let band_extent = phase_extent
        .checked_mul(2)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let mut target_bands = Vec::with_capacity(band_extent);
    for carry in 0_u8..=1_u8 {
        for target_phase in 0..phase_extent {
            target_bands.push(ExactPhaseTransportBand {
                target_phase: u32::try_from(target_phase)
                    .map_err(|_| PhaseCurrentError::CarrierOverflow)?,
                cell_carry: carry,
                population: ExactSignedPhasePopulation::default(),
            });
        }
    }

    for (source_phase, source_population) in source_phases.iter().enumerate() {
        for (response_phase, response_population) in response_phases.iter().enumerate() {
            let phase_sum = source_phase
                .checked_add(response_phase)
                .ok_or(PhaseCurrentError::CarrierOverflow)?;
            let carry = usize::from(phase_sum >= phase_extent);
            let target_phase = phase_sum % phase_extent;
            let band_index = carry
                .checked_mul(phase_extent)
                .and_then(|offset| offset.checked_add(target_phase))
                .ok_or(PhaseCurrentError::CarrierOverflow)?;
            accumulate_product_population(
                &mut target_bands[band_index].population,
                source_population,
                response_population,
            );
        }
    }

    let mut local_phase_products = BigUint::zero();
    let mut carried_phase_products = BigUint::zero();
    let mut net_transported_current = BigInt::zero();
    for band in &mut target_bands {
        band.population.finish();
        let occurrences =
            &band.population.positive_occurrences + &band.population.negative_occurrences;
        if band.cell_carry == 0 {
            local_phase_products += occurrences;
        } else {
            carried_phase_products += occurrences;
        }
        net_transported_current += &band.population.net_current;
    }

    let spectrum = ExactPhaseTransportSpectrum {
        schema: SPECTRUM_SCHEMA.to_owned(),
        source_receiver: source.receiver,
        source_lineage: source.lineage,
        response_receiver: response.receiver,
        response_lineage: response.lineage,
        target_receiver,
        target_lineage,
        origin: &source.origin + &response.origin,
        sample_step: source.sample_step.clone(),
        phase_extent: source.phase_extent,
        source_phases,
        response_phases,
        target_bands,
        local_phase_products,
        carried_phase_products,
        net_transported_current,
    };
    spectrum.validate()?;
    Ok(spectrum)
}

/// Propagate one exact current and return both the complete chronology and its
/// phase-and-carry emission spectrum.
pub fn propagate_phase_current_emission(
    source: &ExactPhaseCurrentSection,
    response: &ExactPhaseCurrentSection,
    target_receiver: PhaseCurrentReceiverId,
    target_lineage: PhaseCurrentLineageId,
    executor: CpuExecutor,
) -> Result<PhaseCurrentEmissionReceipt, PhaseCurrentError> {
    let spectrum =
        receive_phase_transport_spectrum(source, response, target_receiver, target_lineage)?;
    let propagation =
        convolve_phase_current(source, response, target_receiver, target_lineage, executor)?;
    if propagation.local_phase_products != spectrum.local_phase_products
        || propagation.carried_phase_products != spectrum.carried_phase_products
    {
        return Err(PhaseCurrentError::MalformedSpectrum);
    }
    let mut output_current = BigInt::zero();
    for value in propagation.output.flat_values() {
        output_current += value;
    }
    if output_current != spectrum.net_transported_current {
        return Err(PhaseCurrentError::MalformedSpectrum);
    }
    Ok(PhaseCurrentEmissionReceipt {
        schema: EMISSION_SCHEMA.to_owned(),
        propagation,
        spectrum,
    })
}

/// Multiply two complete phase-current sections without flattening phase into
/// a scalar receiver quotient.
pub fn convolve_phase_current(
    source: &ExactPhaseCurrentSection,
    response: &ExactPhaseCurrentSection,
    target_receiver: PhaseCurrentReceiverId,
    target_lineage: PhaseCurrentLineageId,
    executor: CpuExecutor,
) -> Result<PhaseCurrentConvolutionReceipt, PhaseCurrentError> {
    source.validate()?;
    response.validate()?;
    if source.phase_extent != response.phase_extent || source.sample_step != response.sample_step {
        return Err(PhaseCurrentError::ChartMismatch);
    }
    let phase_extent = source.phase_extent_usize()?;
    let source_values = source.flat_values();
    let response_values = response.flat_values();
    let output_extent = source_values
        .len()
        .checked_add(response_values.len())
        .and_then(|extent| extent.checked_sub(1))
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let output_ordinals = (0..output_extent).collect::<Vec<_>>();

    let max_source = source_values
        .iter()
        .map(BigInt::abs)
        .max()
        .unwrap_or_else(BigInt::zero);
    let max_response = response_values
        .iter()
        .map(BigInt::abs)
        .max()
        .unwrap_or_else(BigInt::zero);
    let overlap = source_values.len().min(response_values.len());
    let bound = max_source * max_response * BigInt::from(overlap);
    let use_i128 = bound.bits() <= 126;

    let (values, execution, carrier) = if use_i128 {
        let source_i128 = source_values
            .iter()
            .map(|value| value.to_i128().ok_or(PhaseCurrentError::CarrierOverflow))
            .collect::<Result<Vec<_>, _>>()?;
        let response_i128 = response_values
            .iter()
            .map(|value| value.to_i128().ok_or(PhaseCurrentError::CarrierOverflow))
            .collect::<Result<Vec<_>, _>>()?;
        let (values, execution) = executor
            .execute_indexed(&output_ordinals, |_index, output| {
                let source_first = output.saturating_sub(response_i128.len() - 1);
                let source_last = (*output).min(source_i128.len() - 1);
                let mut value = 0_i128;
                for (source_ordinal, source_value) in source_i128
                    .iter()
                    .enumerate()
                    .take(source_last + 1)
                    .skip(source_first)
                {
                    let delay = *output - source_ordinal;
                    value = value
                        .checked_add(
                            source_value
                                .checked_mul(response_i128[delay])
                                .ok_or(PhaseCurrentError::CarrierOverflow)?,
                        )
                        .ok_or(PhaseCurrentError::CarrierOverflow)?;
                }
                Ok::<_, PhaseCurrentError>(BigInt::from(value))
            })
            .map_err(map_cpu_error)?;
        (values, execution, "i128")
    } else {
        let (values, execution) = executor
            .execute_indexed(&output_ordinals, |_index, output| {
                let source_first = output.saturating_sub(response_values.len() - 1);
                let source_last = (*output).min(source_values.len() - 1);
                let mut value = BigInt::zero();
                for (source_ordinal, source_value) in source_values
                    .iter()
                    .enumerate()
                    .take(source_last + 1)
                    .skip(source_first)
                {
                    let delay = *output - source_ordinal;
                    value += source_value * &response_values[delay];
                }
                Ok::<_, PhaseCurrentError>(value)
            })
            .map_err(map_cpu_error)?;
        (values, execution, "arbitrary-precision")
    };

    let (local_phase_products, carried_phase_products) =
        phase_product_partition(&source_values, &response_values, phase_extent)?;
    Ok(PhaseCurrentConvolutionReceipt {
        schema: RECEIPT_SCHEMA.to_owned(),
        source_lineage: source.lineage,
        response_lineage: response.lineage,
        output: ExactPhaseCurrentSection::from_integers(
            target_receiver,
            target_lineage,
            &source.origin + &response.origin,
            source.sample_step.clone(),
            phase_extent,
            values,
        )?,
        local_phase_products,
        carried_phase_products,
        exact_integer_carrier: carrier.to_owned(),
        execution,
    })
}

fn phase_product_partition(
    source: &[BigInt],
    response: &[BigInt],
    phase_extent: usize,
) -> Result<(BigUint, BigUint), PhaseCurrentError> {
    let mut source_counts = vec![BigUint::zero(); phase_extent];
    let mut response_counts = vec![BigUint::zero(); phase_extent];
    for (ordinal, value) in source.iter().enumerate() {
        if !value.is_zero() {
            source_counts[ordinal % phase_extent] += BigUint::from(1_u8);
        }
    }
    for (ordinal, value) in response.iter().enumerate() {
        if !value.is_zero() {
            response_counts[ordinal % phase_extent] += BigUint::from(1_u8);
        }
    }
    let mut local = BigUint::zero();
    let mut carried = BigUint::zero();
    for (source_phase, source_count) in source_counts.iter().enumerate() {
        for (response_phase, response_count) in response_counts.iter().enumerate() {
            let products = source_count * response_count;
            if source_phase
                .checked_add(response_phase)
                .ok_or(PhaseCurrentError::CarrierOverflow)?
                >= phase_extent
            {
                carried += products;
            } else {
                local += products;
            }
        }
    }
    Ok((local, carried))
}

fn signed_phase_populations(
    values: &[BigInt],
    phase_extent: usize,
) -> Vec<ExactSignedPhasePopulation> {
    let mut populations = vec![ExactSignedPhasePopulation::default(); phase_extent];
    for (ordinal, value) in values.iter().enumerate() {
        if value.is_zero() {
            continue;
        }
        let population = &mut populations[ordinal % phase_extent];
        if value.is_positive() {
            population.positive_occurrences += BigUint::from(1_u8);
            population.positive_current += value.magnitude();
        } else {
            population.negative_occurrences += BigUint::from(1_u8);
            population.negative_current += value.magnitude();
        }
    }
    for population in &mut populations {
        population.finish();
    }
    populations
}

fn accumulate_product_population(
    target: &mut ExactSignedPhasePopulation,
    source: &ExactSignedPhasePopulation,
    response: &ExactSignedPhasePopulation,
) {
    target.positive_occurrences += &source.positive_occurrences * &response.positive_occurrences;
    target.positive_occurrences += &source.negative_occurrences * &response.negative_occurrences;
    target.negative_occurrences += &source.positive_occurrences * &response.negative_occurrences;
    target.negative_occurrences += &source.negative_occurrences * &response.positive_occurrences;

    target.positive_current += &source.positive_current * &response.positive_current;
    target.positive_current += &source.negative_current * &response.negative_current;
    target.negative_current += &source.positive_current * &response.negative_current;
    target.negative_current += &source.negative_current * &response.positive_current;
}

fn map_cpu_error(error: CpuExecutionError<PhaseCurrentError>) -> PhaseCurrentError {
    match error {
        CpuExecutionError::Operation(error) => error,
        CpuExecutionError::WorkerPanicked => PhaseCurrentError::WorkerPanicked,
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum PhaseCurrentError {
    #[error("the exact phase-current section is malformed")]
    MalformedSection,
    #[error("source and response do not share one phase-current chart")]
    ChartMismatch,
    #[error("the exact phase-transport spectrum is malformed")]
    MalformedSpectrum,
    #[error("one exact CPU phase-current worker panicked")]
    WorkerPanicked,
    #[error("an exact phase-current carrier overflowed")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use std::num::NonZeroUsize;

    use num_bigint::BigInt;
    use num_traits::Zero;

    use super::*;

    fn section(lineage: u64, values: &[i32]) -> ExactPhaseCurrentSection {
        ExactPhaseCurrentSection::from_i32(
            PhaseCurrentReceiverId(lineage),
            PhaseCurrentLineageId(lineage),
            Rat::zero(),
            Rat::from_integer(BigInt::from(1)),
            2,
            values,
        )
        .unwrap()
    }

    #[test]
    fn phase_carry_recovers_complete_exact_convolution() {
        let receipt = convolve_phase_current(
            &section(1, &[1, 2, 3]),
            &section(2, &[4, 5]),
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(3),
            CpuExecutor::serial(),
        )
        .unwrap();
        assert_eq!(
            receipt.output.flat_values(),
            [4, 13, 22, 15]
                .into_iter()
                .map(BigInt::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(receipt.local_phase_products, BigUint::from(5_u8));
        assert_eq!(receipt.carried_phase_products, BigUint::from(1_u8));
    }

    #[test]
    fn scalar_cell_integration_is_not_closed_under_convolution() {
        let source = section(1, &[1, 2]);
        let response = section(2, &[3, 4]);
        let propagated = convolve_phase_current(
            &source,
            &response,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(3),
            CpuExecutor::serial(),
        )
        .unwrap();
        assert_eq!(
            propagated.output.integrated_cells(),
            vec![BigInt::from(13), BigInt::from(8)]
        );
        assert_eq!(
            source.integrated_cells()[0].clone() * response.integrated_cells()[0].clone(),
            BigInt::from(21)
        );
    }

    #[test]
    fn serial_and_multicore_realize_the_same_phase_current() {
        let source = section(1, &[1, -2, 3, 4, -5, 6, 7]);
        let response = section(2, &[2, 1, -3, 5]);
        let serial = convolve_phase_current(
            &source,
            &response,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(3),
            CpuExecutor::serial(),
        )
        .unwrap();
        let parallel = convolve_phase_current(
            &source,
            &response,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(3),
            CpuExecutor::multicore(NonZeroUsize::new(4).unwrap()),
        )
        .unwrap();
        assert_eq!(serial.output, parallel.output);
        assert_eq!(serial.local_phase_products, parallel.local_phase_products);
        assert_eq!(
            serial.carried_phase_products,
            parallel.carried_phase_products
        );
    }

    #[test]
    fn emission_spectrum_retains_signed_cancellation_and_carry() {
        let emission = propagate_phase_current_emission(
            &section(1, &[1, -2]),
            &section(2, &[3, -4]),
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(3),
            CpuExecutor::serial(),
        )
        .unwrap();
        assert_eq!(
            emission.propagation.output.flat_values(),
            [3, -10, 8]
                .into_iter()
                .map(BigInt::from)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            emission.spectrum.target_bands,
            vec![
                ExactPhaseTransportBand {
                    target_phase: 0,
                    cell_carry: 0,
                    population: ExactSignedPhasePopulation {
                        positive_occurrences: BigUint::from(1_u8),
                        negative_occurrences: BigUint::zero(),
                        positive_current: BigUint::from(3_u8),
                        negative_current: BigUint::zero(),
                        net_current: BigInt::from(3),
                    },
                },
                ExactPhaseTransportBand {
                    target_phase: 1,
                    cell_carry: 0,
                    population: ExactSignedPhasePopulation {
                        positive_occurrences: BigUint::zero(),
                        negative_occurrences: BigUint::from(2_u8),
                        positive_current: BigUint::zero(),
                        negative_current: BigUint::from(10_u8),
                        net_current: BigInt::from(-10),
                    },
                },
                ExactPhaseTransportBand {
                    target_phase: 0,
                    cell_carry: 1,
                    population: ExactSignedPhasePopulation {
                        positive_occurrences: BigUint::from(1_u8),
                        negative_occurrences: BigUint::zero(),
                        positive_current: BigUint::from(8_u8),
                        negative_current: BigUint::zero(),
                        net_current: BigInt::from(8),
                    },
                },
                ExactPhaseTransportBand {
                    target_phase: 1,
                    cell_carry: 1,
                    population: ExactSignedPhasePopulation::default(),
                },
            ]
        );
        assert_eq!(emission.spectrum.net_transported_current, BigInt::from(1));
    }

    #[test]
    fn same_propagation_has_distinct_receiver_phase_spectra() {
        let source_two = section(1, &[1, 2, 3, 4]);
        let response_two = section(2, &[5, 6, 7]);
        let source_four = ExactPhaseCurrentSection::from_i32(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(1),
            Rat::zero(),
            Rat::from_integer(BigInt::from(1)),
            4,
            &[1, 2, 3, 4],
        )
        .unwrap();
        let response_four = ExactPhaseCurrentSection::from_i32(
            PhaseCurrentReceiverId(2),
            PhaseCurrentLineageId(2),
            Rat::zero(),
            Rat::from_integer(BigInt::from(1)),
            4,
            &[5, 6, 7],
        )
        .unwrap();
        let emission_two = propagate_phase_current_emission(
            &source_two,
            &response_two,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(3),
            CpuExecutor::serial(),
        )
        .unwrap();
        let emission_four = propagate_phase_current_emission(
            &source_four,
            &response_four,
            PhaseCurrentReceiverId(3),
            PhaseCurrentLineageId(3),
            CpuExecutor::serial(),
        )
        .unwrap();
        assert_eq!(
            emission_two.propagation.output.flat_values(),
            emission_four.propagation.output.flat_values()
        );
        assert_ne!(
            emission_two.spectrum.target_bands,
            emission_four.spectrum.target_bands
        );
        assert_eq!(
            emission_two.spectrum.net_transported_current,
            emission_four.spectrum.net_transported_current
        );
    }
}
