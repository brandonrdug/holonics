//! Receiver-situated audible formation from exact native acoustic current.
//!
//! `NativeAcousticProductionSection` is an exact causal section, not a sampled waveform. This
//! owner composes its order/port incidence with a declared acoustic receiver: causal orders found
//! overlapping time supports, ordered ports found spectral incidences, and the two exact current
//! coordinates act as quadrature coefficients. The resulting potential complex remains native;
//! PCM is a later cold quotient. No source waveform, transcript, model, token, or per-section peak
//! normalization participates.

use std::{
    collections::BTreeMap,
    f64::consts::{PI, TAU},
    io::Cursor,
};

use holonic_engine::ExactComplexWaveCurrent;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{NativeAcousticError, NativeAcousticProductionSection};

pub const NATIVE_ACOUSTIC_POTENTIAL_COMPLEX_SCHEMA: &str =
    "soma-life.native-acoustic-potential-complex.v1";
const NATIVE_ACOUSTIC_RECEIVER_CHART_SCHEMA: &str = "soma-life.native-acoustic-receiver-chart.v1";
const NATIVE_ACOUSTIC_AUDIBLE_PROJECTION_SCHEMA: &str =
    "soma-life.native-acoustic-audible-projection.v1";

/// A cold physical receiver chart. Its coordinates govern an exterior acoustic apparatus, not
/// Athena's state population. One chart is reused unchanged across every compared section.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticReceiverChart {
    pub schema: String,
    pub sample_rate: u32,
    /// Distance between consecutive native causal-order supports in receiver samples.
    pub order_stride_samples: u32,
    /// Extent of each order support. Extent above stride gives lawful overlap.
    pub order_support_samples: u32,
    pub lowest_frequency_hz: u32,
    pub highest_frequency_hz: u32,
    /// One founding section calibrates the cold receiver once. Its current population does not
    /// survive; only the population-derived logarithmic center and width remain.
    pub calibration_production_identity_sha256: String,
    pub logarithmic_current_center_millibits: i64,
    pub logarithmic_current_width_millibits: u64,
    pub calibration_source_current_retained: bool,
    pub identity_sha256: String,
}

impl NativeAcousticReceiverChart {
    pub fn calibrated_from(
        production: &NativeAcousticProductionSection,
        sample_rate: u32,
        order_stride_samples: u32,
        order_support_samples: u32,
        lowest_frequency_hz: u32,
        highest_frequency_hz: u32,
    ) -> Result<Self, NativeAcousticError> {
        production.validate()?;
        let mut magnitudes = production
            .complete_port_quadrature_fibre
            .iter()
            .filter_map(|(_, _, _, current)| complex_log2_millibits(current))
            .collect::<Vec<_>>();
        if magnitudes.is_empty() {
            return Err(NativeAcousticError::MalformedAudibleFormation);
        }
        magnitudes.sort_unstable();
        let center = magnitudes[(magnitudes.len() - 1) / 2];
        let mut deviations = magnitudes
            .iter()
            .map(|magnitude| magnitude.abs_diff(center))
            .collect::<Vec<_>>();
        deviations.sort_unstable();
        let width = deviations[(deviations.len() - 1) / 2].max(1);
        let mut chart = Self {
            schema: NATIVE_ACOUSTIC_RECEIVER_CHART_SCHEMA.to_owned(),
            sample_rate,
            order_stride_samples,
            order_support_samples,
            lowest_frequency_hz,
            highest_frequency_hz,
            calibration_production_identity_sha256: production.identity_sha256.clone(),
            logarithmic_current_center_millibits: center,
            logarithmic_current_width_millibits: width,
            calibration_source_current_retained: false,
            identity_sha256: String::new(),
        };
        chart.identity_sha256 = chart.rederived_identity()?;
        chart.validate()?;
        Ok(chart)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        let nyquist = self.sample_rate / 2;
        if self.schema != NATIVE_ACOUSTIC_RECEIVER_CHART_SCHEMA
            || self.sample_rate == 0
            || self.order_stride_samples == 0
            || self.order_support_samples < self.order_stride_samples
            || self.lowest_frequency_hz == 0
            || self.highest_frequency_hz <= self.lowest_frequency_hz
            || self.highest_frequency_hz >= nyquist
            || !is_digest(&self.calibration_production_identity_sha256)
            || self.logarithmic_current_width_millibits == 0
            || self.calibration_source_current_retained
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedAudibleFormation);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            self.sample_rate,
            self.order_stride_samples,
            self.order_support_samples,
            self.lowest_frequency_hz,
            self.highest_frequency_hz,
            &self.calibration_production_identity_sha256,
            self.logarithmic_current_center_millibits,
            self.logarithmic_current_width_millibits,
            self.calibration_source_current_retained,
        ))
    }
}

/// One exact order/port current placed in a receiver-local time and frequency incidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticSpectralIncidence {
    pub address_sha256: String,
    pub causal_order: u64,
    pub port: u32,
    pub universal_port: u32,
    pub support_begin_sample: u64,
    pub support_end_sample: u64,
    pub frequency_numerator_hz: u64,
    pub frequency_denominator: u64,
    pub exact_quadrature_current: ExactComplexWaveCurrent,
    pub complete_port_current_fibre_retained: bool,
}

/// Native potential complex before a playback codec acts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticPotentialComplex {
    pub schema: String,
    pub production_identity_sha256: String,
    pub morphology_identity_sha256: String,
    pub receiver: NativeAcousticReceiverChart,
    pub first_causal_order: u64,
    pub last_causal_order: u64,
    pub port_population: usize,
    pub maximum_simultaneous_order_supports: u32,
    pub fixed_mixing_divisor: u64,
    pub duration_samples: u64,
    pub incidences: Vec<NativeAcousticSpectralIncidence>,
    pub per_section_peak_normalization_applied: bool,
    pub source_waveform_accessible: bool,
    pub complete_production_fibre_retained: bool,
    pub identity_sha256: String,
}

/// A lossy cold PCM face. The native complex and every exact current remain its explicit
/// reconstruction fibre. `clipped_sample_population == 0` establishes that no hidden saturation
/// changed the accepted receiver face.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeAcousticAudibleProjection {
    pub schema: String,
    pub potential_complex_identity_sha256: String,
    pub receiver_identity_sha256: String,
    pub sample_rate: u32,
    pub samples: Vec<i16>,
    pub nonzero_sample_population: usize,
    pub clipped_sample_population: usize,
    pub per_section_peak_normalization_applied: bool,
    pub complete_potential_complex_fibre_retained: bool,
    pub cold_renderer_only: bool,
    pub identity_sha256: String,
}

impl NativeAcousticPotentialComplex {
    pub fn found(
        production: &NativeAcousticProductionSection,
        receiver: NativeAcousticReceiverChart,
    ) -> Result<Self, NativeAcousticError> {
        production.validate()?;
        receiver.validate()?;
        let first_causal_order = *production
            .causal_orders
            .first()
            .ok_or(NativeAcousticError::MalformedAudibleFormation)?;
        let last_causal_order = *production
            .causal_orders
            .last()
            .ok_or(NativeAcousticError::MalformedAudibleFormation)?;
        if production
            .causal_orders
            .windows(2)
            .any(|pair| pair[1] != pair[0].saturating_add(1))
        {
            return Err(NativeAcousticError::MalformedAudibleFormation);
        }

        let mut ports = BTreeMap::<(u32, u32), usize>::new();
        for (_, port, universal_port, _) in &production.complete_port_quadrature_fibre {
            let next = ports.len();
            ports.entry((*port, *universal_port)).or_insert(next);
        }
        if ports.is_empty()
            || production.complete_port_quadrature_fibre.len()
                != ports.len().saturating_mul(production.causal_orders.len())
        {
            return Err(NativeAcousticError::MalformedAudibleFormation);
        }
        let port_population = ports.len();
        let support = u64::from(receiver.order_support_samples);
        let stride = u64::from(receiver.order_stride_samples);
        let maximum_simultaneous_order_supports = receiver
            .order_support_samples
            .div_ceil(receiver.order_stride_samples);
        let fixed_mixing_divisor = u64::try_from(port_population)
            .ok()
            .and_then(|ports| ports.checked_mul(u64::from(maximum_simultaneous_order_supports)))
            .ok_or(NativeAcousticError::Extent)?;
        let duration_samples = last_causal_order
            .checked_sub(first_causal_order)
            .and_then(|orders| orders.checked_mul(stride))
            .and_then(|elapsed| elapsed.checked_add(support))
            .ok_or(NativeAcousticError::Extent)?;
        let low = u64::from(receiver.lowest_frequency_hz);
        let frequency_span = u64::from(receiver.highest_frequency_hz)
            .checked_sub(low)
            .ok_or(NativeAcousticError::Extent)?;
        let frequency_denominator = u64::try_from(port_population)
            .ok()
            .and_then(|ports| ports.checked_add(1))
            .ok_or(NativeAcousticError::Extent)?;

        let mut incidences = Vec::with_capacity(production.complete_port_quadrature_fibre.len());
        for (causal_order, port, universal_port, current) in
            &production.complete_port_quadrature_fibre
        {
            let port_position = *ports
                .get(&(*port, *universal_port))
                .ok_or(NativeAcousticError::MalformedAudibleFormation)?;
            let position = u64::try_from(port_position)
                .ok()
                .and_then(|position| position.checked_add(1))
                .ok_or(NativeAcousticError::Extent)?;
            let support_begin_sample = causal_order
                .checked_sub(first_causal_order)
                .and_then(|order| order.checked_mul(stride))
                .ok_or(NativeAcousticError::Extent)?;
            let support_end_sample = support_begin_sample
                .checked_add(support)
                .ok_or(NativeAcousticError::Extent)?;
            let frequency_numerator_hz = low
                .checked_mul(frequency_denominator)
                .and_then(|base| base.checked_add(frequency_span.checked_mul(position)?))
                .ok_or(NativeAcousticError::Extent)?;
            let address_sha256 = digest(&(
                &production.identity_sha256,
                &receiver.identity_sha256,
                causal_order,
                port,
                universal_port,
                support_begin_sample,
                support_end_sample,
                frequency_numerator_hz,
                frequency_denominator,
                current,
            ))?;
            incidences.push(NativeAcousticSpectralIncidence {
                address_sha256,
                causal_order: *causal_order,
                port: *port,
                universal_port: *universal_port,
                support_begin_sample,
                support_end_sample,
                frequency_numerator_hz,
                frequency_denominator,
                exact_quadrature_current: current.clone(),
                complete_port_current_fibre_retained: true,
            });
        }
        let mut complex = Self {
            schema: NATIVE_ACOUSTIC_POTENTIAL_COMPLEX_SCHEMA.to_owned(),
            production_identity_sha256: production.identity_sha256.clone(),
            morphology_identity_sha256: production.morphology_identity_sha256.clone(),
            receiver,
            first_causal_order,
            last_causal_order,
            port_population,
            maximum_simultaneous_order_supports,
            fixed_mixing_divisor,
            duration_samples,
            incidences,
            per_section_peak_normalization_applied: false,
            source_waveform_accessible: false,
            complete_production_fibre_retained: true,
            identity_sha256: String::new(),
        };
        complex.identity_sha256 = complex.rederived_identity()?;
        complex.validate()?;
        Ok(complex)
    }

    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        self.receiver.validate()?;
        if self.schema != NATIVE_ACOUSTIC_POTENTIAL_COMPLEX_SCHEMA
            || !is_digest(&self.production_identity_sha256)
            || !is_digest(&self.morphology_identity_sha256)
            || self.first_causal_order > self.last_causal_order
            || self.port_population == 0
            || self.maximum_simultaneous_order_supports == 0
            || self.fixed_mixing_divisor == 0
            || self.duration_samples == 0
            || self.incidences.is_empty()
            || self.per_section_peak_normalization_applied
            || self.source_waveform_accessible
            || !self.complete_production_fibre_retained
            || self.incidences.iter().any(|incidence| {
                !is_digest(&incidence.address_sha256)
                    || incidence.support_begin_sample >= incidence.support_end_sample
                    || incidence.support_end_sample > self.duration_samples
                    || incidence.frequency_denominator == 0
                    || !incidence.complete_port_current_fibre_retained
            })
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedAudibleFormation);
        }
        Ok(())
    }

    /// Project the native potential into one fixed signed-16 receiver. Complex current acts by
    /// `Re((a+ib)e^{iθ}) = a cos θ - b sin θ`; a Hann support makes neighboring causal orders
    /// overlap without discontinuous boundaries. The fixed mixing divisor follows only from the
    /// admitted port incidence and maximum support overlap, never from this section's peak.
    pub fn render_pcm16(&self) -> Result<NativeAcousticAudibleProjection, NativeAcousticError> {
        self.validate()?;
        let sample_population =
            usize::try_from(self.duration_samples).map_err(|_| NativeAcousticError::Extent)?;
        let mut accumulated = vec![0.0_f64; sample_population];
        let sample_rate = f64::from(self.receiver.sample_rate);
        let divisor = self.fixed_mixing_divisor as f64;
        for incidence in &self.incidences {
            if incidence.exact_quadrature_current.is_zero() {
                continue;
            }
            let begin = usize::try_from(incidence.support_begin_sample)
                .map_err(|_| NativeAcousticError::Extent)?;
            let end = usize::try_from(incidence.support_end_sample)
                .map_err(|_| NativeAcousticError::Extent)?;
            let support = (end - begin) as f64;
            let frequency =
                incidence.frequency_numerator_hz as f64 / incidence.frequency_denominator as f64;
            let (mut real, mut imaginary) =
                projective_receiver_coordinates(&incidence.exact_quadrature_current)?;
            let magnitude = complex_log2_millibits(&incidence.exact_quadrature_current)
                .ok_or(NativeAcousticError::MalformedAudibleFormation)?;
            let situated = (magnitude - self.receiver.logarithmic_current_center_millibits) as f64
                / self.receiver.logarithmic_current_width_millibits as f64;
            let amplitude = 1.0 / (1.0 + (-situated).exp());
            real *= amplitude;
            imaginary *= amplitude;
            for (local, target) in accumulated[begin..end].iter_mut().enumerate() {
                let time = local as f64 / sample_rate;
                let phase = TAU * frequency * time;
                let envelope = (PI * (local as f64 + 0.5) / support).sin().powi(2);
                *target += envelope * (real * phase.cos() - imaginary * phase.sin()) / divisor;
            }
        }
        let mut clipped_sample_population = 0_usize;
        let samples = accumulated
            .into_iter()
            .map(|value| {
                let scaled = value * f64::from(i16::MAX);
                if scaled > f64::from(i16::MAX) || scaled < f64::from(i16::MIN) {
                    clipped_sample_population += 1;
                }
                scaled
                    .round()
                    .clamp(f64::from(i16::MIN), f64::from(i16::MAX)) as i16
            })
            .collect::<Vec<_>>();
        let nonzero_sample_population = samples.iter().filter(|sample| **sample != 0).count();
        let mut projection = NativeAcousticAudibleProjection {
            schema: NATIVE_ACOUSTIC_AUDIBLE_PROJECTION_SCHEMA.to_owned(),
            potential_complex_identity_sha256: self.identity_sha256.clone(),
            receiver_identity_sha256: self.receiver.identity_sha256.clone(),
            sample_rate: self.receiver.sample_rate,
            samples,
            nonzero_sample_population,
            clipped_sample_population,
            per_section_peak_normalization_applied: false,
            complete_potential_complex_fibre_retained: true,
            cold_renderer_only: true,
            identity_sha256: String::new(),
        };
        projection.identity_sha256 = projection.rederived_identity()?;
        projection.validate()?;
        Ok(projection)
    }

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            &self.production_identity_sha256,
            &self.morphology_identity_sha256,
            &self.receiver,
            self.first_causal_order,
            self.last_causal_order,
            self.port_population,
            self.maximum_simultaneous_order_supports,
            self.fixed_mixing_divisor,
            self.duration_samples,
            &self.incidences,
            self.per_section_peak_normalization_applied,
            self.source_waveform_accessible,
            self.complete_production_fibre_retained,
        ))
    }
}

impl NativeAcousticAudibleProjection {
    pub fn validate(&self) -> Result<(), NativeAcousticError> {
        if self.schema != NATIVE_ACOUSTIC_AUDIBLE_PROJECTION_SCHEMA
            || !is_digest(&self.potential_complex_identity_sha256)
            || !is_digest(&self.receiver_identity_sha256)
            || self.sample_rate == 0
            || self.samples.is_empty()
            || self.nonzero_sample_population == 0
            || self.nonzero_sample_population
                != self.samples.iter().filter(|sample| **sample != 0).count()
            || self.clipped_sample_population != 0
            || self.per_section_peak_normalization_applied
            || !self.complete_potential_complex_fibre_retained
            || !self.cold_renderer_only
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeAcousticError::MalformedAudibleFormation);
        }
        Ok(())
    }

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

    fn rederived_identity(&self) -> Result<String, NativeAcousticError> {
        digest(&(
            &self.schema,
            &self.potential_complex_identity_sha256,
            &self.receiver_identity_sha256,
            self.sample_rate,
            &self.samples,
            self.nonzero_sample_population,
            self.clipped_sample_population,
            self.per_section_peak_normalization_applied,
            self.complete_potential_complex_fibre_retained,
            self.cold_renderer_only,
        ))
    }
}

/// Receiver chart of one exact complex ray. A common positive scale is removed from the two
/// quadratures together, so relative phase survives even when the exact rationals exceed `f64`.
/// The complete unscaled current remains in `NativeAcousticSpectralIncidence`; this is therefore a
/// projective apparatus rebase with an explicit reconstruction fibre, not per-section peak
/// normalization.
fn projective_receiver_coordinates(
    current: &ExactComplexWaveCurrent,
) -> Result<(f64, f64), NativeAcousticError> {
    if current.is_zero() {
        return Ok((0.0, 0.0));
    }
    let real_log = log2_abs_rational(&current.real);
    let imaginary_log = log2_abs_rational(&current.imaginary);
    let maximum = match (real_log, imaginary_log) {
        (Some(real), Some(imaginary)) => real.max(imaginary),
        (Some(real), None) => real,
        (None, Some(imaginary)) => imaginary,
        (None, None) => return Err(NativeAcousticError::MalformedAudibleFormation),
    };
    let real = project_from_log(&current.real, real_log, maximum);
    let imaginary = project_from_log(&current.imaginary, imaginary_log, maximum);
    let norm = real.hypot(imaginary);
    if !norm.is_finite() || norm == 0.0 {
        return Err(NativeAcousticError::MalformedAudibleFormation);
    }
    Ok((real / norm, imaginary / norm))
}

fn project_from_log(
    value: &num_rational::BigRational,
    logarithm: Option<f64>,
    maximum: f64,
) -> f64 {
    let Some(logarithm) = logarithm else {
        return 0.0;
    };
    let sign = if value.is_negative() { -1.0 } else { 1.0 };
    sign * 2.0_f64.powf(logarithm - maximum)
}

fn log2_abs_rational(value: &num_rational::BigRational) -> Option<f64> {
    if value.is_zero() {
        return None;
    }
    Some(log2_abs_bigint(value.numer()) - log2_abs_bigint(value.denom()))
}

fn complex_log2_millibits(current: &ExactComplexWaveCurrent) -> Option<i64> {
    let logarithm = match (
        log2_abs_rational(&current.real),
        log2_abs_rational(&current.imaginary),
    ) {
        (Some(real), Some(imaginary)) => real.max(imaginary),
        (Some(real), None) => real,
        (None, Some(imaginary)) => imaginary,
        (None, None) => return None,
    };
    (logarithm * 1_000.0).round().to_i64()
}

fn log2_abs_bigint(value: &BigInt) -> f64 {
    let magnitude = value.magnitude();
    let bits = magnitude.bits();
    let retained = bits.min(53);
    let shift = bits.saturating_sub(retained);
    let leading = (magnitude >> usize::try_from(shift).unwrap_or(usize::MAX))
        .to_u64()
        .unwrap_or(u64::MAX)
        .max(1);
    (shift as f64) + (leading as f64).log2()
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
