//! Exact acoustic receiver chart over native Athena membrane radiation.
//!
//! The productive input is already-returned complex port current. One causal order is one coarse
//! current cell; the complete ordered port population and its two complex quadratures are the
//! derived local phase fibre. The owner stores no PCM source, transcript, waveform template, or
//! foreign runtime. A later PCM rendering is an explicitly lossy exterior receiver which retains
//! its divisor and every remainder.

mod potential_formation;

pub use potential_formation::{
    NativeAcousticAudibleProjection, NativeAcousticPotentialComplex, NativeAcousticReceiverChart,
    NativeAcousticSpectralIncidence,
};

use std::io::Cursor;

use holonic_engine::{
    phase_current::{ExactPhaseCurrentSection, PhaseCurrentLineageId, PhaseCurrentReceiverId},
    ExactComplexWaveCurrent, ExactPhaseTransportSpectrum,
};
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::membrane_cultivation::MembraneDifferenceStanding;
use super::{
    AthenaMembraneStanding, GranularAthenaMembraneStanding, LaboratoryCellAffineSection,
    LaboratoryFactorCycleCorrespondence, NativeGranularPotential, NativeOpenWorldTubeReceipt,
    NativeOpenWorldTubeTerminal, NativeOutwardPortReturn, ReceiverHistoryRealizationPassage,
    RecurrentGranularRelationalCellWithdrawal, RecurrentGranularReturnedAffineAthenaRest,
    SituatedCultivationBranch, SituatedDifferenceSection,
};

pub const NATIVE_ACOUSTIC_PRODUCTION_MORPHOLOGY_SCHEMA: &str =
    "soma-life.native-acoustic-production-morphology.v1";
const NATIVE_ACOUSTIC_RADIATION_INPUT_SCHEMA: &str = "soma-life.native-acoustic-radiation-input.v1";
const NATIVE_ACOUSTIC_PRODUCTION_SECTION_SCHEMA: &str =
    "soma-life.native-acoustic-production-section.v1";
const ACOUSTIC_ATHENA_REST_SCHEMA: &str = "soma-life.acoustic-athena-rest.v1";
const WITHDRAWN_ACOUSTIC_PRODUCTION_SCHEMA: &str =
    "soma-life.withdrawn-native-acoustic-production.v1";

/// One causal order of complete source-neutral outward current.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticRadiationOrder {
    pub causal_order: u64,
    pub outward_port_returns: Vec<NativeOutwardPortReturn>,
}

/// The source-neutral acoustic face of an exact open-world-tube return.
///
/// The original exterior occurrence and its source fibre are absent by type. The full receipt
/// identity remains cold lineage so an artifact import cannot masquerade as another native deed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticRadiationInput {
    pub schema: String,
    pub rested_identity_sha256: String,
    pub open_world_tube_receipt_identity_sha256: String,
    pub source_section: u64,
    pub outward_port_population: usize,
    pub orders: Vec<NativeAcousticRadiationOrder>,
    pub terminal: NativeOpenWorldTubeTerminal,
    pub identity_sha256: String,
}

impl NativeAcousticRadiationInput {
    /// Found the exact source-neutral face after an exterior storage cut. Every productive
    /// coordinate is supplied by the already-returned native receipt; this constructor derives
    /// identity and refuses reordered, incomplete, or falsely silent port populations.
    pub fn found_returned(
        rested_identity_sha256: impl Into<String>,
        open_world_tube_receipt_identity_sha256: impl Into<String>,
        source_section: u64,
        outward_port_population: usize,
        orders: Vec<NativeAcousticRadiationOrder>,
        terminal: NativeOpenWorldTubeTerminal,
    ) -> Result<Self, NativeAcousticError> {
        let mut input = Self {
            schema: NATIVE_ACOUSTIC_RADIATION_INPUT_SCHEMA.to_owned(),
            rested_identity_sha256: rested_identity_sha256.into(),
            open_world_tube_receipt_identity_sha256: open_world_tube_receipt_identity_sha256.into(),
            source_section,
            outward_port_population,
            orders,
            terminal,
            identity_sha256: String::new(),
        };
        input.identity_sha256 = input.rederived_identity()?;
        input.validate()?;
        Ok(input)
    }

    pub fn from_open_world_tube(
        receipt: &NativeOpenWorldTubeReceipt,
        current: usize,
    ) -> Result<Self, NativeAcousticError> {
        if receipt.schema != super::OPEN_WORLD_TUBE_RADIATION_SCHEMA {
            return Err(NativeAcousticError::MalformedRadiation);
        }
        let returned = receipt
            .current_returns
            .get(current)
            .ok_or(NativeAcousticError::MalformedRadiation)?;
        Self::found_returned(
            receipt.rested_identity_sha256.clone(),
            receipt.identity_sha256.clone(),
            returned.source_section,
            receipt.outward_port_population,
            returned
                .orders
                .iter()
                .map(|order| NativeAcousticRadiationOrder {
                    causal_order: order.causal_order,
                    outward_port_returns: order.outward_port_returns.clone(),
                })
                .collect(),
            returned.terminal.clone(),
        )
    }

    /// Re-admit the already-returned source-neutral face across a storage cut.
    pub fn read(bytes: &[u8]) -> Result<Self, NativeAcousticError> {
        let input: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeAcousticError::Wire(error.to_string()))?;
        input.validate()?;
        Ok(input)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeAcousticError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeAcousticError::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        if self.schema != NATIVE_ACOUSTIC_RADIATION_INPUT_SCHEMA
            || !is_digest(&self.rested_identity_sha256)
            || !is_digest(&self.open_world_tube_receipt_identity_sha256)
            || self.outward_port_population == 0
            || self.orders.is_empty()
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedRadiation);
        }
        match self.terminal {
            NativeOpenWorldTubeTerminal::DynamicallyCondensedRest {
                scale_reconstruction_fibre_retained: true,
                ..
            }
            | NativeOpenWorldTubeTerminal::RecurrentOpenFront {
                scale_reconstruction_fibre_retained: true,
                ..
            } => {}
            _ => return Err(NativeAcousticError::MalformedRadiation),
        }
        let expected_ports = self.canonical_ports()?;
        let mut prior = None;
        let mut nonzero = false;
        for order in &self.orders {
            if prior.is_some_and(|prior| order.causal_order != prior + 1)
                || order.outward_port_returns.len() != self.outward_port_population
            {
                return Err(NativeAcousticError::MalformedRadiation);
            }
            prior = Some(order.causal_order);
            for (position, returned) in order.outward_port_returns.iter().enumerate() {
                let expected = expected_ports
                    .get(position)
                    .ok_or(NativeAcousticError::MalformedRadiation)?;
                if (returned.port, returned.universal_port) != *expected
                    || returned.returned_response.is_zero() != returned.lies_in_outward_radical
                {
                    return Err(NativeAcousticError::MalformedRadiation);
                }
                nonzero |= !returned.returned_response.is_zero();
            }
        }
        if !nonzero {
            return Err(NativeAcousticError::MalformedRadiation);
        }
        Ok(())
    }

    fn canonical_ports(&self) -> Result<Vec<(u32, u32)>, NativeAcousticError> {
        let first = self
            .orders
            .first()
            .ok_or(NativeAcousticError::MalformedRadiation)?;
        let mut ports = Vec::with_capacity(first.outward_port_returns.len());
        for (position, returned) in first.outward_port_returns.iter().enumerate() {
            if usize::try_from(returned.port).ok() != Some(position) {
                return Err(NativeAcousticError::MalformedRadiation);
            }
            ports.push((returned.port, returned.universal_port));
        }
        if ports.len() != self.outward_port_population {
            return Err(NativeAcousticError::MalformedRadiation);
        }
        let mut universal = ports.iter().map(|(_, port)| *port).collect::<Vec<_>>();
        universal.sort_unstable();
        universal.dedup();
        if universal.len() != ports.len() {
            return Err(NativeAcousticError::MalformedRadiation);
        }
        Ok(ports)
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            &self.rested_identity_sha256,
            &self.open_world_tube_receipt_identity_sha256,
            self.source_section,
            self.outward_port_population,
            &self.orders,
            &self.terminal,
        ))
    }
}

/// Reusable source-neutral incidence from native outward ports into an acoustic phase fibre.
/// It stores no current values and therefore cannot replay the founding waveform.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticProductionMorphology {
    pub schema: String,
    /// The exact body upon which this organ was founded. Later lawful return changes the body,
    /// never this historical lineage coordinate or the reusable incidence itself.
    pub founding_rest_identity_sha256: String,
    pub founding_radiation_identity_sha256: String,
    pub ordered_ports: Vec<(u32, u32)>,
    pub quadrature_population: u32,
    pub phase_extent: u32,
    pub identity_sha256: String,
}

impl NativeAcousticProductionMorphology {
    fn found(input: &NativeAcousticRadiationInput) -> Result<Self, NativeAcousticError> {
        input.validate()?;
        let ordered_ports = input.canonical_ports()?;
        let quadrature_population = 2_u32;
        let phase_extent = u32::try_from(ordered_ports.len())
            .ok()
            .and_then(|ports| ports.checked_mul(quadrature_population))
            .ok_or(NativeAcousticError::Extent)?;
        let mut morphology = Self {
            schema: NATIVE_ACOUSTIC_PRODUCTION_MORPHOLOGY_SCHEMA.to_owned(),
            founding_rest_identity_sha256: input.rested_identity_sha256.clone(),
            founding_radiation_identity_sha256: input.identity_sha256.clone(),
            ordered_ports,
            quadrature_population,
            phase_extent,
            identity_sha256: String::new(),
        };
        morphology.identity_sha256 = morphology.rederived_identity()?;
        morphology.validate()?;
        Ok(morphology)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        let expected_extent = u32::try_from(self.ordered_ports.len())
            .ok()
            .and_then(|ports| ports.checked_mul(self.quadrature_population))
            .ok_or(NativeAcousticError::Extent)?;
        if self.schema != NATIVE_ACOUSTIC_PRODUCTION_MORPHOLOGY_SCHEMA
            || !is_digest(&self.founding_rest_identity_sha256)
            || !is_digest(&self.founding_radiation_identity_sha256)
            || self.ordered_ports.is_empty()
            || self.quadrature_population != 2
            || self.phase_extent != expected_extent
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedMorphology);
        }
        let mut unique = self.ordered_ports.clone();
        unique.sort_unstable();
        unique.dedup();
        if unique.len() != self.ordered_ports.len() {
            return Err(NativeAcousticError::MalformedMorphology);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            &self.founding_rest_identity_sha256,
            &self.founding_radiation_identity_sha256,
            &self.ordered_ports,
            self.quadrature_population,
            self.phase_extent,
        ))
    }
}

/// Complete exact acoustic current before any PCM receiver acts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticProductionSection {
    pub schema: String,
    pub morphology_identity_sha256: String,
    pub radiation_identity_sha256: String,
    pub causal_orders: Vec<u64>,
    pub exact_phase_current: ExactPhaseCurrentSection,
    pub common_denominator: BigUint,
    pub outward_radical_population: usize,
    pub nonradical_population: usize,
    pub complete_port_quadrature_fibre: Vec<(u64, u32, u32, ExactComplexWaveCurrent)>,
    pub source_samples_accessible: bool,
    pub waveform_template_applied: bool,
    pub identity_sha256: String,
}

impl NativeAcousticProductionSection {
    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        if self.schema != NATIVE_ACOUSTIC_PRODUCTION_SECTION_SCHEMA
            || !is_digest(&self.morphology_identity_sha256)
            || !is_digest(&self.radiation_identity_sha256)
            || self.causal_orders.is_empty()
            || self.common_denominator == BigUint::from(0_u8)
            || self.complete_port_quadrature_fibre.is_empty()
            || self.source_samples_accessible
            || self.waveform_template_applied
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedProduction);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            &self.morphology_identity_sha256,
            &self.radiation_identity_sha256,
            &self.causal_orders,
            &self.exact_phase_current,
            &self.common_denominator,
            self.outward_radical_population,
            self.nonradical_population,
            &self.complete_port_quadrature_fibre,
            self.source_samples_accessible,
            self.waveform_template_applied,
        ))
    }
}

/// Exterior PCM receiver quotient. The exact native section remains its source; `remainders`
/// reconstruct every integral numerator from `sample * scale_divisor + remainder`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticPcm16Projection {
    pub production_identity_sha256: String,
    pub sample_rate: u32,
    pub scale_divisor: BigInt,
    pub samples: Vec<i16>,
    pub remainders: Vec<BigInt>,
    pub exact_denominator: BigUint,
    pub identity_sha256: String,
}

/// Exact projective rebase from an unbounded physical acoustic current into the resident
/// signed-word apparatus. The productive ray enters the device; the removed signed scale and the
/// presented current remain the complete reconstruction fibre. This is neither clamping nor a
/// floating normalization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticProjectiveCurrent {
    pub presented_current: ExactComplexWaveCurrent,
    pub primitive_resident_current: ExactComplexWaveCurrent,
    pub removed_scale: Rat,
    pub cleared_common_denominator: BigUint,
    pub removed_integral_divisor: BigUint,
    pub orientation_reversed: bool,
    pub complete_scale_reconstruction_fibre_retained: bool,
    pub identity_sha256: String,
}

impl NativeAcousticProjectiveCurrent {
    pub fn found(presented: ExactComplexWaveCurrent) -> Result<Self, NativeAcousticError> {
        if presented.is_zero() {
            return Err(NativeAcousticError::MalformedProjectiveCurrent);
        }
        let denominator = lcm_positive(presented.real.denom(), presented.imaginary.denom());
        let cleared_real = clear_denominator(&presented.real, &denominator);
        let cleared_imaginary = clear_denominator(&presented.imaginary, &denominator);
        let divisor = gcd_positive(cleared_real.clone(), cleared_imaginary.clone());
        if divisor == BigInt::from(0) {
            return Err(NativeAcousticError::MalformedProjectiveCurrent);
        }
        let first = if cleared_real != BigInt::from(0) {
            &cleared_real
        } else {
            &cleared_imaginary
        };
        let orientation_reversed = first < &BigInt::from(0);
        let orientation = if orientation_reversed {
            BigInt::from(-1)
        } else {
            BigInt::from(1)
        };
        let primitive_resident_current = ExactComplexWaveCurrent::new(
            Rat::from_integer((&cleared_real / &divisor) * &orientation),
            Rat::from_integer((&cleared_imaginary / &divisor) * &orientation),
        );
        let removed_scale = Rat::new(&divisor * orientation, denominator.clone());
        let mut quotient = Self {
            presented_current: presented,
            primitive_resident_current,
            removed_scale,
            cleared_common_denominator: denominator
                .to_biguint()
                .ok_or(NativeAcousticError::MalformedProjectiveCurrent)?,
            removed_integral_divisor: divisor
                .to_biguint()
                .ok_or(NativeAcousticError::MalformedProjectiveCurrent)?,
            orientation_reversed,
            complete_scale_reconstruction_fibre_retained: true,
            identity_sha256: String::new(),
        };
        quotient.identity_sha256 = quotient.rederived_identity()?;
        quotient.validate()?;
        Ok(quotient)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        let primitive_real = self.primitive_resident_current.real.to_integer();
        let primitive_imaginary = self.primitive_resident_current.imaginary.to_integer();
        let leading = if primitive_real != BigInt::from(0) {
            &primitive_real
        } else {
            &primitive_imaginary
        };
        let primitive_divisor = gcd_positive(primitive_real.clone(), primitive_imaginary.clone());
        if self.presented_current.is_zero()
            || self.primitive_resident_current.is_zero()
            || self.primitive_resident_current.real.denom() != &BigInt::from(1)
            || self.primitive_resident_current.imaginary.denom() != &BigInt::from(1)
            || primitive_divisor != BigInt::from(1)
            || leading <= &BigInt::from(0)
            || self.removed_scale == Rat::from_integer(BigInt::from(0))
            || self.cleared_common_denominator == BigUint::from(0_u8)
            || self.removed_integral_divisor == BigUint::from(0_u8)
            || !self.complete_scale_reconstruction_fibre_retained
            || self.primitive_resident_current.scaled(&self.removed_scale) != self.presented_current
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedProjectiveCurrent);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.presented_current,
            &self.primitive_resident_current,
            &self.removed_scale,
            &self.cleared_common_denominator,
            &self.removed_integral_divisor,
            self.orientation_reversed,
            self.complete_scale_reconstruction_fibre_retained,
        ))
    }
}

/// Exact finite receiver of a binaural room return. The full pressure/current face remains in
/// `presented_current`; resident coordinates are the signed local-versus-carried product
/// populations of both measured paths plus the signed exterior-speaker population. Device ingress
/// is therefore derived from physical transport receipts, never from clipping or a caller-chosen
/// threshold.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticReceiverCurrent {
    pub presented_current: ExactComplexWaveCurrent,
    pub room_spectrum_identities_sha256: Vec<String>,
    pub local_phase_product_populations: Vec<BigUint>,
    pub carried_phase_product_populations: Vec<BigUint>,
    pub other_speaker_lineage: PhaseCurrentLineageId,
    pub other_speaker_positive_occurrences: BigUint,
    pub other_speaker_negative_occurrences: BigUint,
    pub resident_current: ExactComplexWaveCurrent,
    pub exact_presented_current_retained: bool,
    pub identity_sha256: String,
}

impl NativeAcousticReceiverCurrent {
    pub fn found(
        presented_current: ExactComplexWaveCurrent,
        room_spectra: &[ExactPhaseTransportSpectrum],
        other_speaker: &ExactPhaseCurrentSection,
    ) -> Result<Self, NativeAcousticError> {
        if presented_current.is_zero()
            || room_spectra.len() != 2
            || room_spectra[0].phase_extent != room_spectra[1].phase_extent
            || room_spectra[0].sample_step != room_spectra[1].sample_step
            || room_spectra[0].sample_step != other_speaker.sample_step
            || room_spectra[0].phase_extent != other_speaker.phase_extent
        {
            return Err(NativeAcousticError::MalformedReceiverCurrent);
        }
        let mut positive = BigUint::from(0_u8);
        let mut negative = BigUint::from(0_u8);
        for sample in other_speaker.flat_values() {
            if sample > BigInt::from(0) {
                positive += BigUint::from(1_u8);
            } else if sample < BigInt::from(0) {
                negative += BigUint::from(1_u8);
            }
        }
        let speaker_signed = BigInt::from(positive.clone()) - BigInt::from(negative.clone());
        let local = room_spectra
            .iter()
            .map(|spectrum| spectrum.local_phase_products.clone())
            .collect::<Vec<_>>();
        let carried = room_spectra
            .iter()
            .map(|spectrum| spectrum.carried_phase_products.clone())
            .collect::<Vec<_>>();
        let coordinate = |axis: usize| {
            BigInt::from(local[axis].clone()) - BigInt::from(carried[axis].clone())
                + &speaker_signed
        };
        let resident_current = ExactComplexWaveCurrent::new(
            Rat::from_integer(coordinate(0)),
            Rat::from_integer(coordinate(1)),
        );
        if resident_current.is_zero() {
            return Err(NativeAcousticError::MalformedReceiverCurrent);
        }
        let mut receiver = Self {
            presented_current,
            room_spectrum_identities_sha256: room_spectra
                .iter()
                .map(digest)
                .collect::<Result<Vec<_>, _>>()?,
            local_phase_product_populations: local,
            carried_phase_product_populations: carried,
            other_speaker_lineage: other_speaker.lineage,
            other_speaker_positive_occurrences: positive,
            other_speaker_negative_occurrences: negative,
            resident_current,
            exact_presented_current_retained: true,
            identity_sha256: String::new(),
        };
        receiver.identity_sha256 = receiver.rederived_identity()?;
        receiver.validate()?;
        Ok(receiver)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        if self.presented_current.is_zero()
            || self.room_spectrum_identities_sha256.len() != 2
            || self
                .room_spectrum_identities_sha256
                .iter()
                .any(|identity| !is_digest(identity))
            || self.local_phase_product_populations.len() != 2
            || self.carried_phase_product_populations.len() != 2
            || self.resident_current.is_zero()
            || !self.exact_presented_current_retained
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedReceiverCurrent);
        }
        let speaker_signed = BigInt::from(self.other_speaker_positive_occurrences.clone())
            - BigInt::from(self.other_speaker_negative_occurrences.clone());
        let coordinate = |axis: usize| {
            BigInt::from(self.local_phase_product_populations[axis].clone())
                - BigInt::from(self.carried_phase_product_populations[axis].clone())
                + &speaker_signed
        };
        if self.resident_current.real != Rat::from_integer(coordinate(0))
            || self.resident_current.imaginary != Rat::from_integer(coordinate(1))
        {
            return Err(NativeAcousticError::MalformedReceiverCurrent);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.presented_current,
            &self.room_spectrum_identities_sha256,
            &self.local_phase_product_populations,
            &self.carried_phase_product_populations,
            self.other_speaker_lineage,
            &self.other_speaker_positive_occurrences,
            &self.other_speaker_negative_occurrences,
            &self.resident_current,
            self.exact_presented_current_retained,
        ))
    }
}

impl NativeAcousticPcm16Projection {
    pub fn wav_bytes(&self) -> Result<Vec<u8>, NativeAcousticError> {
        self.validate()?;
        let specification = hound::WavSpec {
            channels: 1,
            sample_rate: self.sample_rate,
            bits_per_sample: 16,
            sample_format: hound::SampleFormat::Int,
        };
        let mut bytes = Vec::new();
        {
            let cursor = Cursor::new(&mut bytes);
            let mut writer = hound::WavWriter::new(cursor, specification)
                .map_err(|error| NativeAcousticError::Pcm(error.to_string()))?;
            for sample in &self.samples {
                writer
                    .write_sample(*sample)
                    .map_err(|error| NativeAcousticError::Pcm(error.to_string()))?;
            }
            writer
                .finalize()
                .map_err(|error| NativeAcousticError::Pcm(error.to_string()))?;
        }
        Ok(bytes)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        if !is_digest(&self.production_identity_sha256)
            || self.sample_rate == 0
            || self.scale_divisor <= BigInt::from(0)
            || self.samples.is_empty()
            || self.samples.len() != self.remainders.len()
            || self.exact_denominator == BigUint::from(0_u8)
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::Pcm(
                "the PCM receiver lost its exact quotient fibre".to_owned(),
            ));
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.production_identity_sha256,
            self.sample_rate,
            &self.scale_divisor,
            &self.samples,
            &self.remainders,
            &self.exact_denominator,
        ))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticCultivationReceipt {
    pub predecessor_rest_identity_sha256: String,
    pub successor_rest_identity_sha256: String,
    pub morphology_identity_sha256: String,
    pub founding_radiation_identity_sha256: String,
    pub port_population: usize,
    pub derived_phase_extent: u32,
    pub source_current_retained_in_morphology: bool,
    pub waveform_template_retained: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticStandingMutation {
    pub operation: String,
    pub predecessor_rest_identity_sha256: String,
    pub successor_rest_identity_sha256: String,
    pub morphology_identity_sha256: String,
}

/// Receipt for composing an already source-neutral acoustic morphology with another compatible
/// Athena continuation body. No founding waveform or exterior source is consulted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticOrganCompositionReceipt {
    pub inherited_rest_identity_sha256: String,
    pub inherited_predecessor_identity_sha256: String,
    pub morphology_identity_sha256: String,
    pub receiving_body_identity_sha256: String,
    pub composed_rest_identity_sha256: String,
    pub source_occurrence_consulted: bool,
    pub source_current_retained_in_morphology: bool,
    pub waveform_template_retained: bool,
}

/// The exact productive organ after it has left the one Athena owner.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WithdrawnNativeAcousticProduction {
    schema: String,
    original_rest_identity_sha256: String,
    predecessor_body_identity_sha256: String,
    morphology: NativeAcousticProductionMorphology,
    identity_sha256: String,
}

/// One move-owned Athena body carrying reusable acoustic boundary morphology.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AcousticAthenaRest {
    schema: String,
    body: RecurrentGranularReturnedAffineAthenaRest,
    production: NativeAcousticProductionMorphology,
    identity_sha256: String,
}

/// Exact inverse for one affine-cell ablation conducted through the still-present acoustic organ.
#[derive(Debug, PartialEq, Eq)]
pub struct AcousticRelationalCellWithdrawal {
    original_rest_identity_sha256: String,
    body: RecurrentGranularRelationalCellWithdrawal,
}

impl AcousticAthenaRest {
    pub fn cultivate(
        body: RecurrentGranularReturnedAffineAthenaRest,
        founding: &NativeAcousticRadiationInput,
    ) -> Result<(Self, NativeAcousticCultivationReceipt), NativeAcousticError> {
        body.validate_membrane_standing()
            .map_err(NativeAcousticError::Standing)?;
        if body.membrane_identity() != founding.rested_identity_sha256 {
            return Err(NativeAcousticError::Lineage);
        }
        let production = NativeAcousticProductionMorphology::found(founding)?;
        let predecessor_rest_identity_sha256 = body.identity().to_owned();
        let mut rest = Self {
            schema: ACOUSTIC_ATHENA_REST_SCHEMA.to_owned(),
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        let receipt = NativeAcousticCultivationReceipt {
            predecessor_rest_identity_sha256,
            successor_rest_identity_sha256: rest.identity_sha256.clone(),
            morphology_identity_sha256: rest.production.identity_sha256.clone(),
            founding_radiation_identity_sha256: founding.identity_sha256.clone(),
            port_population: rest.production.ordered_ports.len(),
            derived_phase_extent: rest.production.phase_extent,
            source_current_retained_in_morphology: false,
            waveform_template_retained: false,
        };
        Ok((rest, receipt))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeAcousticError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeAcousticError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeAcousticError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeAcousticError::Wire(error.to_string()))
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }

    pub fn body(&self) -> &RecurrentGranularReturnedAffineAthenaRest {
        &self.body
    }

    pub fn production(&self) -> &NativeAcousticProductionMorphology {
        &self.production
    }

    pub fn withdraw_relational_cell(
        self,
        cell_address: &str,
    ) -> Result<(Self, AcousticRelationalCellWithdrawal), NativeAcousticError> {
        self.validate()?;
        let Self {
            schema,
            body,
            production,
            identity_sha256,
        } = self;
        let (body, withdrawal) = body
            .withdraw_relational_cell(cell_address)
            .map_err(|error| NativeAcousticError::Standing(error.to_string()))?;
        let mut rest = Self {
            schema,
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok((
            rest,
            AcousticRelationalCellWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                body: withdrawal,
            },
        ))
    }

    pub fn restore_relational_cell(
        self,
        withdrawal: AcousticRelationalCellWithdrawal,
    ) -> Result<Self, NativeAcousticError> {
        self.validate()?;
        let Self {
            schema,
            body,
            production,
            identity_sha256: _,
        } = self;
        let body = body
            .restore_relational_cell(withdrawal.body)
            .map_err(|error| NativeAcousticError::Standing(error.to_string()))?;
        let mut rest = Self {
            schema,
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        if rest.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(NativeAcousticError::Lineage);
        }
        rest.validate()?;
        Ok(rest)
    }

    pub fn radiate(
        &self,
        input: &NativeAcousticRadiationInput,
        sample_step: Rat,
    ) -> Result<NativeAcousticProductionSection, NativeAcousticError> {
        self.validate()?;
        input.validate()?;
        // The founding rest is historical lineage, not a permanent gate on later conduct. A
        // cultivated successor may reuse this organ precisely when its emitted boundary section
        // retains the complete ordered port incidence on which the organ was founded.
        if input.canonical_ports()? != self.production.ordered_ports
            || sample_step <= Rat::from_integer(BigInt::from(0))
        {
            return Err(NativeAcousticError::Lineage);
        }

        let mut denominator = BigInt::from(1);
        for order in &input.orders {
            for returned in &order.outward_port_returns {
                denominator = lcm_positive(&denominator, returned.returned_response.real.denom());
                denominator =
                    lcm_positive(&denominator, returned.returned_response.imaginary.denom());
            }
        }
        let denominator_uint = denominator
            .to_biguint()
            .ok_or(NativeAcousticError::Extent)?;
        let mut samples = Vec::with_capacity(
            input
                .orders
                .len()
                .checked_mul(self.production.phase_extent as usize)
                .ok_or(NativeAcousticError::Extent)?,
        );
        let mut fibre = Vec::with_capacity(samples.capacity());
        let mut outward_radical_population = 0_usize;
        let mut nonradical_population = 0_usize;
        for order in &input.orders {
            for returned in &order.outward_port_returns {
                samples.push(clear_denominator(
                    &returned.returned_response.real,
                    &denominator,
                ));
                samples.push(clear_denominator(
                    &returned.returned_response.imaginary,
                    &denominator,
                ));
                fibre.push((
                    order.causal_order,
                    returned.port,
                    returned.universal_port,
                    returned.returned_response.clone(),
                ));
                if returned.lies_in_outward_radical {
                    outward_radical_population += 1;
                } else {
                    nonradical_population += 1;
                }
            }
        }
        let receiver = PhaseCurrentReceiverId(project_digest(&self.production.identity_sha256)?);
        let lineage = PhaseCurrentLineageId(project_digest(&input.identity_sha256)?);
        let exact_phase_current = ExactPhaseCurrentSection::from_integers(
            receiver,
            lineage,
            Rat::from_integer(BigInt::from(0)),
            sample_step,
            self.production.phase_extent as usize,
            samples,
        )
        .map_err(|error| NativeAcousticError::Phase(error.to_string()))?;
        let mut section = NativeAcousticProductionSection {
            schema: NATIVE_ACOUSTIC_PRODUCTION_SECTION_SCHEMA.to_owned(),
            morphology_identity_sha256: self.production.identity_sha256.clone(),
            radiation_identity_sha256: input.identity_sha256.clone(),
            causal_orders: input
                .orders
                .iter()
                .map(|order| order.causal_order)
                .collect(),
            exact_phase_current,
            common_denominator: denominator_uint,
            outward_radical_population,
            nonradical_population,
            complete_port_quadrature_fibre: fibre,
            source_samples_accessible: false,
            waveform_template_applied: false,
            identity_sha256: String::new(),
        };
        section.identity_sha256 = section.rederived_identity()?;
        section.validate()?;
        Ok(section)
    }

    pub fn project_pcm16(
        &self,
        section: &NativeAcousticProductionSection,
        sample_rate: u32,
    ) -> Result<NativeAcousticPcm16Projection, NativeAcousticError> {
        self.validate()?;
        section.validate()?;
        if section.morphology_identity_sha256 != self.production.identity_sha256
            || sample_rate == 0
            || section.exact_phase_current.sample_step
                != Rat::new(BigInt::from(1), BigInt::from(sample_rate))
        {
            return Err(NativeAcousticError::Lineage);
        }
        let values = section.exact_phase_current.flat_values();
        let maximum = values
            .iter()
            .map(abs_bigint)
            .max()
            .unwrap_or_else(|| BigInt::from(0));
        let pcm_peak = BigInt::from(i16::MAX);
        let scale_divisor = if maximum <= pcm_peak {
            BigInt::from(1)
        } else {
            (&maximum + &pcm_peak - BigInt::from(1)) / &pcm_peak
        };
        let mut samples = Vec::with_capacity(values.len());
        let mut remainders = Vec::with_capacity(values.len());
        for value in values {
            let quotient = &value / &scale_divisor;
            let remainder = &value - &quotient * &scale_divisor;
            let sample = i16::try_from(quotient).map_err(|_| NativeAcousticError::Extent)?;
            samples.push(sample);
            remainders.push(remainder);
        }
        let mut projection = NativeAcousticPcm16Projection {
            production_identity_sha256: section.identity_sha256.clone(),
            sample_rate,
            scale_divisor,
            samples,
            remainders,
            exact_denominator: section.common_denominator.clone(),
            identity_sha256: String::new(),
        };
        projection.identity_sha256 = projection.rederived_identity()?;
        projection.validate()?;
        Ok(projection)
    }

    pub fn withdraw_production(
        self,
    ) -> Result<
        (
            RecurrentGranularReturnedAffineAthenaRest,
            WithdrawnNativeAcousticProduction,
            NativeAcousticStandingMutation,
        ),
        NativeAcousticError,
    > {
        self.validate()?;
        let original_rest_identity_sha256 = self.identity_sha256;
        let predecessor_body_identity_sha256 = self.body.identity().to_owned();
        let morphology_identity_sha256 = self.production.identity_sha256.clone();
        let mut withdrawn = WithdrawnNativeAcousticProduction {
            schema: WITHDRAWN_ACOUSTIC_PRODUCTION_SCHEMA.to_owned(),
            original_rest_identity_sha256: original_rest_identity_sha256.clone(),
            predecessor_body_identity_sha256: predecessor_body_identity_sha256.clone(),
            morphology: self.production,
            identity_sha256: String::new(),
        };
        withdrawn.identity_sha256 = withdrawn.rederived_identity()?;
        let mutation = NativeAcousticStandingMutation {
            operation: "withdraw-native-acoustic-production".to_owned(),
            predecessor_rest_identity_sha256: original_rest_identity_sha256,
            successor_rest_identity_sha256: predecessor_body_identity_sha256,
            morphology_identity_sha256,
        };
        Ok((self.body, withdrawn, mutation))
    }

    pub fn restore_production(
        body: RecurrentGranularReturnedAffineAthenaRest,
        withdrawn: WithdrawnNativeAcousticProduction,
    ) -> Result<(Self, NativeAcousticStandingMutation), NativeAcousticError> {
        withdrawn.validate()?;
        if body.identity() != withdrawn.predecessor_body_identity_sha256 {
            return Err(NativeAcousticError::Lineage);
        }
        let predecessor_rest_identity_sha256 = body.identity().to_owned();
        let morphology_identity_sha256 = withdrawn.morphology.identity_sha256.clone();
        let expected = withdrawn.original_rest_identity_sha256;
        let mut rest = Self {
            schema: ACOUSTIC_ATHENA_REST_SCHEMA.to_owned(),
            body,
            production: withdrawn.morphology,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        if rest.identity_sha256 != expected {
            return Err(NativeAcousticError::Lineage);
        }
        rest.validate()?;
        let mutation = NativeAcousticStandingMutation {
            operation: "restore-native-acoustic-production".to_owned(),
            predecessor_rest_identity_sha256,
            successor_rest_identity_sha256: rest.identity_sha256.clone(),
            morphology_identity_sha256,
        };
        Ok((rest, mutation))
    }

    /// Move an inherited source-neutral production morphology onto a compatible body. The
    /// historical founding coordinates remain lineage while the wrapper identity is derived from
    /// the receiving body and that exact morphology.
    pub fn compose_source_neutral_production(
        body: RecurrentGranularReturnedAffineAthenaRest,
        withdrawn: WithdrawnNativeAcousticProduction,
    ) -> Result<(Self, NativeAcousticOrganCompositionReceipt), NativeAcousticError> {
        body.validate_membrane_standing()
            .map_err(NativeAcousticError::Standing)?;
        withdrawn.validate()?;
        let inherited_rest_identity_sha256 = withdrawn.original_rest_identity_sha256.clone();
        let inherited_predecessor_identity_sha256 =
            withdrawn.predecessor_body_identity_sha256.clone();
        let morphology_identity_sha256 = withdrawn.morphology.identity_sha256.clone();
        let receiving_body_identity_sha256 = body.identity().to_owned();
        let mut rest = Self {
            schema: ACOUSTIC_ATHENA_REST_SCHEMA.to_owned(),
            body,
            production: withdrawn.morphology,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        let receipt = NativeAcousticOrganCompositionReceipt {
            inherited_rest_identity_sha256,
            inherited_predecessor_identity_sha256,
            morphology_identity_sha256,
            receiving_body_identity_sha256,
            composed_rest_identity_sha256: rest.identity_sha256.clone(),
            source_occurrence_consulted: false,
            source_current_retained_in_morphology: false,
            waveform_template_retained: false,
        };
        Ok((rest, receipt))
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        self.body
            .validate_membrane_standing()
            .map_err(NativeAcousticError::Standing)?;
        self.production.validate()?;
        if self.schema != ACOUSTIC_ATHENA_REST_SCHEMA
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::Lineage);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            self.body.identity(),
            &self.production.identity_sha256,
        ))
    }
}

impl WithdrawnNativeAcousticProduction {
    fn validate(&self) -> Result<(), NativeAcousticError> {
        self.morphology.validate()?;
        if self.schema != WITHDRAWN_ACOUSTIC_PRODUCTION_SCHEMA
            || !is_digest(&self.original_rest_identity_sha256)
            || !is_digest(&self.predecessor_body_identity_sha256)
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::Lineage);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            &self.original_rest_identity_sha256,
            &self.predecessor_body_identity_sha256,
            &self.morphology,
        ))
    }
}

impl AthenaMembraneStanding for AcousticAthenaRest {
    fn validate_membrane_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn membrane_identity(&self) -> &str {
        &self.identity_sha256
    }

    fn membrane_ecology(&self) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.membrane_ecology()
    }

    fn membrane_realization(&self) -> &ReceiverHistoryRealizationPassage {
        self.body.membrane_realization()
    }

    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.membrane_branches()
    }

    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        self.body.membrane_correspondences()
    }

    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        self.body.membrane_affine_cells()
    }
}

impl GranularAthenaMembraneStanding for AcousticAthenaRest {
    fn membrane_granular_potential(&self) -> &NativeGranularPotential {
        self.body.granular_potential()
    }
}

impl MembraneDifferenceStanding for AcousticAthenaRest {
    type Successor = Self;

    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String> {
        let production = self.production;
        let body = self
            .body
            .deposit_additional_returned_difference(difference)
            .map_err(|error| error.to_string())?;
        let mut rest = Self {
            schema: ACOUSTIC_ATHENA_REST_SCHEMA.to_owned(),
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest
            .rederived_identity()
            .map_err(|error| error.to_string())?;
        rest.validate().map_err(|error| error.to_string())?;
        Ok(rest)
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeAcousticError {
    #[error("the native outward radiation face is malformed")]
    MalformedRadiation,
    #[error("the native acoustic production morphology is malformed")]
    MalformedMorphology,
    #[error("the exact acoustic production section is malformed")]
    MalformedProduction,
    #[error(
        "the exact acoustic projective current lost its primitive ray or reconstruction scale"
    )]
    MalformedProjectiveCurrent,
    #[error("the acoustic room return lost its exact finite receiver current")]
    MalformedReceiverCurrent,
    #[error("the native acoustic potential complex or audible receiver face is malformed")]
    MalformedAudibleFormation,
    #[error("the acoustic boundary lineage does not join")]
    Lineage,
    #[error("the exact acoustic carrier exceeded its finite apparatus chart")]
    Extent,
    #[error("the acoustic phase-current owner refused: {0}")]
    Phase(String),
    #[error("the PCM receiver refused: {0}")]
    Pcm(String),
    #[error("the rested Athena body refused: {0}")]
    Standing(String),
    #[error("the acoustic rest wire refused: {0}")]
    Wire(String),
}

fn clear_denominator(value: &Rat, denominator: &BigInt) -> BigInt {
    value.numer() * (denominator / value.denom())
}

fn lcm_positive(left: &BigInt, right: &BigInt) -> BigInt {
    (left / gcd_positive(left.clone(), right.clone())) * right
}

fn gcd_positive(mut left: BigInt, mut right: BigInt) -> BigInt {
    if left < BigInt::from(0) {
        left = -left;
    }
    if right < BigInt::from(0) {
        right = -right;
    }
    while right != BigInt::from(0) {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn abs_bigint(value: &BigInt) -> BigInt {
    if value < &BigInt::from(0) {
        -value
    } else {
        value.clone()
    }
}

fn project_digest(identity: &str) -> Result<u64, NativeAcousticError> {
    if !is_digest(identity) {
        return Err(NativeAcousticError::Lineage);
    }
    let bytes = identity.as_bytes();
    let mut projected = [0_u8; 8];
    for (at, target) in projected.iter_mut().enumerate() {
        let high = decode_hex(bytes[at * 2])?;
        let low = decode_hex(bytes[at * 2 + 1])?;
        *target = high << 4 | low;
    }
    Ok(u64::from_be_bytes(projected))
}

fn decode_hex(byte: u8) -> Result<u8, NativeAcousticError> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        b'A'..=b'F' => Ok(byte - b'A' + 10),
        _ => Err(NativeAcousticError::Lineage),
    }
}

use holonic_engine::is_sha256_digest as is_digest;

fn digest(value: &impl Serialize) -> Result<String, NativeAcousticError> {
    let bytes =
        serde_json::to_vec(value).map_err(|error| NativeAcousticError::Wire(error.to_string()))?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
        ExactComplexWaveCurrent::new(
            Rat::from_integer(BigInt::from(real)),
            Rat::from_integer(BigInt::from(imaginary)),
        )
    }

    fn input() -> NativeAcousticRadiationInput {
        let terminal = NativeOpenWorldTubeTerminal::DynamicallyCondensedRest {
            resident_current_identity_sha256: "4".repeat(64),
            projective_ray_population: 2,
            scale_reconstruction_fibre_retained: true,
        };
        let orders = vec![
            NativeAcousticRadiationOrder {
                causal_order: 0,
                outward_port_returns: vec![
                    NativeOutwardPortReturn {
                        port: 0,
                        universal_port: 7,
                        returned_response: ExactComplexWaveCurrent::zero(),
                        lies_in_outward_radical: true,
                        lies_in_receiver_phase_front: false,
                    },
                    NativeOutwardPortReturn {
                        port: 1,
                        universal_port: 9,
                        returned_response: current(3, -2),
                        lies_in_outward_radical: false,
                        lies_in_receiver_phase_front: true,
                    },
                ],
            },
            NativeAcousticRadiationOrder {
                causal_order: 1,
                outward_port_returns: vec![
                    NativeOutwardPortReturn {
                        port: 0,
                        universal_port: 7,
                        returned_response: ExactComplexWaveCurrent::zero(),
                        lies_in_outward_radical: true,
                        lies_in_receiver_phase_front: false,
                    },
                    NativeOutwardPortReturn {
                        port: 1,
                        universal_port: 9,
                        returned_response: current(5, 1),
                        lies_in_outward_radical: false,
                        lies_in_receiver_phase_front: true,
                    },
                ],
            },
        ];
        let mut input = NativeAcousticRadiationInput {
            schema: NATIVE_ACOUSTIC_RADIATION_INPUT_SCHEMA.to_owned(),
            rested_identity_sha256: "1".repeat(64),
            open_world_tube_receipt_identity_sha256: "2".repeat(64),
            source_section: 0,
            outward_port_population: 2,
            orders,
            terminal,
            identity_sha256: String::new(),
        };
        input.identity_sha256 = input.rederived_identity().unwrap();
        input
    }

    #[test]
    fn the_phase_extent_is_derived_from_complete_ports_and_quadratures() {
        let input = input();
        input.validate().unwrap();
        let morphology = NativeAcousticProductionMorphology::found(&input).unwrap();
        assert_eq!(morphology.phase_extent, 4);
        assert_eq!(morphology.ordered_ports, vec![(0, 7), (1, 9)]);
    }

    #[test]
    fn a_reordered_or_silently_nonzero_radical_face_is_refused() {
        let mut reordered = input();
        reordered.orders[1].outward_port_returns.swap(0, 1);
        reordered.identity_sha256 = reordered.rederived_identity().unwrap();
        assert_eq!(
            reordered.validate(),
            Err(NativeAcousticError::MalformedRadiation)
        );

        let mut false_silence = input();
        false_silence.orders[0].outward_port_returns[0].returned_response = current(1, 0);
        false_silence.identity_sha256 = false_silence.rederived_identity().unwrap();
        assert_eq!(
            false_silence.validate(),
            Err(NativeAcousticError::MalformedRadiation)
        );
    }

    #[test]
    fn an_unbounded_current_returns_a_primitive_ray_with_its_exact_scale() {
        let quotient = NativeAcousticProjectiveCurrent::found(ExactComplexWaveCurrent::new(
            Rat::new(BigInt::from(-6), BigInt::from(35)),
            Rat::new(BigInt::from(-9), BigInt::from(35)),
        ))
        .unwrap();
        assert!(quotient.orientation_reversed);
        assert_eq!(
            quotient.primitive_resident_current,
            ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(2)),
                Rat::from_integer(BigInt::from(3)),
            )
        );
        assert_eq!(
            quotient.removed_scale,
            Rat::new(BigInt::from(-3), BigInt::from(35))
        );
        quotient.validate().unwrap();
    }

    #[test]
    fn physical_phase_populations_found_one_finite_resident_current() {
        let step = Rat::new(BigInt::from(1), BigInt::from(16_000));
        let source = ExactPhaseCurrentSection::from_integers(
            PhaseCurrentReceiverId(1),
            PhaseCurrentLineageId(1),
            Rat::from_integer(BigInt::from(0)),
            step.clone(),
            2,
            [1, -2, 3].into_iter().map(BigInt::from).collect(),
        )
        .unwrap();
        let response = |receiver, lineage, values: [i64; 2]| {
            ExactPhaseCurrentSection::from_integers(
                PhaseCurrentReceiverId(receiver),
                PhaseCurrentLineageId(lineage),
                Rat::from_integer(BigInt::from(0)),
                step.clone(),
                2,
                values.into_iter().map(BigInt::from).collect(),
            )
            .unwrap()
        };
        let spectra = [response(2, 2, [2, 1]), response(3, 3, [1, -1])]
            .iter()
            .enumerate()
            .map(|(axis, response)| {
                holonic_engine::receive_phase_transport_spectrum(
                    &source,
                    response,
                    PhaseCurrentReceiverId(10 + axis as u64),
                    PhaseCurrentLineageId(10 + axis as u64),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        let speaker = response(4, 4, [4, -1]);
        let current = NativeAcousticReceiverCurrent::found(
            ExactComplexWaveCurrent::new(
                Rat::new(BigInt::from(7), BigInt::from(5)),
                Rat::new(BigInt::from(-2), BigInt::from(7)),
            ),
            &spectra,
            &speaker,
        )
        .unwrap();
        assert_eq!(current.room_spectrum_identities_sha256.len(), 2);
        assert!(current.exact_presented_current_retained);
        assert_eq!(current.resident_current.real.denom(), &BigInt::from(1));
        assert_eq!(current.resident_current.imaginary.denom(), &BigInt::from(1));
        current.validate().unwrap();
    }
}
