//! Accumulated normal statistics and their cold receiver. The exact moments retain the
//! common source chart; a numerical material matrix is bounded by its full normal residual.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::point_section;
use num_traits::{Signed, ToPrimitive, Zero};
use std::collections::BTreeMap;

mod layout;
use layout::{MomentWire, NormalLayout, ReportBall, STATISTIC_SCALARS};

pub(crate) fn state_words(n: usize, t: usize) -> Option<usize> {
    Some(NormalLayout::new(n, t)?.state_words)
}
pub(crate) fn report_words(n: usize, t: usize) -> Option<usize> {
    Some(NormalLayout::new(n, t)?.report_words)
}
pub(crate) fn workspace_words(n: usize, t: usize) -> Option<usize> {
    Some(NormalLayout::new(n, t)?.workspace_words)
}
pub(crate) fn feature_state_words(sources: usize, targets: usize) -> Option<usize> {
    Some(NormalLayout::for_sources(sources, targets)?.state_words)
}
pub(crate) fn feature_report_words(sources: usize, targets: usize) -> Option<usize> {
    Some(NormalLayout::for_sources(sources, targets)?.report_words)
}
pub(crate) fn feature_workspace_words(sources: usize, targets: usize) -> Option<usize> {
    Some(NormalLayout::for_sources(sources, targets)?.workspace_words)
}
pub(super) fn initial_words(
    n: usize,
    t: usize,
    grain: u32,
) -> Result<Vec<(i64, i64)>, ConstitutiveFibreError> {
    initial_words_for_sources(
        n.checked_mul(3).ok_or(ConstitutiveFibreError::Shape)?,
        t,
        grain,
    )
}
fn initial_words_for_sources(
    sources: usize,
    t: usize,
    grain: u32,
) -> Result<Vec<(i64, i64)>, ConstitutiveFibreError> {
    let layout = NormalLayout::for_sources(sources, t).ok_or(ConstitutiveFibreError::Shape)?;
    let mut out = vec![(0, 0); layout.state_words];
    let square_scale_bit = 2 * grain as usize;
    for i in 0..layout.sources {
        let at = layout.matrix_words
            + MomentWire::COMPLEX_WORDS * (i * layout.sources + i)
            + square_scale_bit / MomentWire::LIMB_BITS;
        let v = 1i64 << (square_scale_bit % MomentWire::LIMB_BITS);
        out[at] = (v, v);
    }
    Ok(out)
}

/// Seed a normal chart with H₀=I and an explicit B₀=W₀H₀.  The resident wire
/// stores moments at S², where S=2^grain; requiring a dyadic prior at the chart
/// grain keeps this initialization exact and avoids a host floating-point path.
pub(super) fn initial_words_for_sources_with_prior(
    sources: usize,
    targets: usize,
    grain: u32,
    prior: &NativeNormalPrior,
) -> Result<Vec<(i64, i64)>, ConstitutiveFibreError> {
    if prior.targets() != targets || prior.source_complex() != sources {
        return Err(ConstitutiveFibreError::Shape);
    }
    let layout =
        NormalLayout::for_sources(sources, targets).ok_or(ConstitutiveFibreError::Shape)?;
    let mut out = initial_words_for_sources(sources, targets, grain)?;
    let scale = BigInt::one() << grain;
    let moment = |value: &Rat| -> Result<BigInt, ConstitutiveFibreError> {
        let numerator = value.numer().clone() * &scale * &scale;
        let denominator = value.denom();
        if &numerator % denominator != BigInt::zero() {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(numerator / denominator)
    };
    let write = |value: BigInt, dst: &mut [(i64, i64)]| -> Result<(), ConstitutiveFibreError> {
        if dst.len() != MomentWire::WORDS {
            return Err(ConstitutiveFibreError::Shape);
        }
        let negative = value.is_negative();
        let absolute = value.abs();
        let mut rest = absolute;
        for limb in &mut dst[..MomentWire::LIMBS] {
            let value_limb = (rest.clone() & BigInt::from(u32::MAX))
                .to_u32()
                .ok_or(ConstitutiveFibreError::Shape)? as i64;
            *limb = (value_limb, value_limb);
            rest >>= MomentWire::LIMB_BITS;
        }
        if !rest.is_zero() {
            return Err(ConstitutiveFibreError::Shape);
        }
        dst[MomentWire::LIMBS] = (i64::from(negative), i64::from(negative));
        Ok(())
    };
    let b = layout.cross_words_at();
    for (row, values) in prior.cross_source.iter().enumerate() {
        for (column, value) in values.iter().enumerate() {
            let at = b + MomentWire::COMPLEX_WORDS * (row * sources + column);
            write(moment(&value.real)?, &mut out[at..at + MomentWire::WORDS])?;
            write(
                moment(&value.imaginary)?,
                &mut out[at + MomentWire::WORDS..at + MomentWire::COMPLEX_WORDS],
            )?;
        }
    }
    // H0=I and B0=W0 imply the initial applied operator is W0 itself. Populate its
    // checked wide coefficients as well as the statistics; an all-zero applied map
    // would silently discard the prior and kill the codec's initial correspondence.
    let mut coefficient_norm = 0i128;
    for (row, values) in prior.cross_source.iter().enumerate() {
        for (column, value) in values.iter().enumerate() {
            for (quadrature, coordinate) in [&value.real, &value.imaginary].into_iter().enumerate()
            {
                let scaled = coordinate.numer() * &scale;
                if &scaled % coordinate.denom() != BigInt::zero() {
                    return Err(ConstitutiveFibreError::Shape);
                }
                let coefficient = (scaled / coordinate.denom())
                    .to_i128()
                    .ok_or(ConstitutiveFibreError::Shape)?;
                coefficient_norm = coefficient_norm
                    .checked_add(
                        coefficient
                            .checked_abs()
                            .ok_or(ConstitutiveFibreError::Shape)?,
                    )
                    .ok_or(ConstitutiveFibreError::Shape)?;
                let at = 2 * (2 * (row * sources + column) + quadrature);
                out[at] = (coefficient as i64, coefficient as i64);
                out[at + 1] = ((coefficient >> 64) as i64, (coefficient >> 64) as i64);
            }
        }
    }
    let norm_at = 2 * (layout.cross_values + 2);
    out[norm_at] = (coefficient_norm as i64, coefficient_norm as i64);
    out[norm_at + 1] = (
        (coefficient_norm >> 64) as i64,
        (coefficient_norm >> 64) as i64,
    );
    let c = moment(&prior.target_energy)?;
    let at = layout.scalar_words_at() + 2 * MomentWire::WORDS;
    write(c, &mut out[at..at + MomentWire::WORDS])?;
    Ok(out)
}
fn invalid(s: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(format!("normal material: {s}"))
}
pub(super) fn integer(words: &[(i64, i64)]) -> Result<BigInt, ConstitutiveFibreError> {
    if words.len() != MomentWire::WORDS
        || words.iter().any(|(a, b)| a != b)
        || ![0, 1].contains(&words[MomentWire::LIMBS].0)
        || words[..MomentWire::LIMBS]
            .iter()
            .any(|v| v.0 < 0 || v.0 > u32::MAX as i64)
    {
        return Err(invalid("moment encoding"));
    }
    let mut n = BigInt::zero();
    for (i, v) in words[..MomentWire::LIMBS].iter().enumerate() {
        n += BigInt::from(v.0) << (MomentWire::LIMB_BITS * i);
    }
    if words[MomentWire::LIMBS].0 == 1 {
        if n.is_zero() {
            return Err(invalid("negative zero moment"));
        }
        n = -n;
    }
    Ok(n)
}
fn ceil_norm(values: &[i128]) -> BigInt {
    let q: BigInt = values.iter().map(|v| BigInt::from(*v).pow(2)).sum();
    let s = q.sqrt();
    if &s * &s < q { s + 1 } else { s }
}
// The two observer-only accumulated-error fields keep legacy nonnegative grained
// numerators, or -e for the outward numerator 2^e. This is not a native current codec.
fn diagnostic_numerator(code: i128) -> Result<BigInt, ConstitutiveFibreError> {
    if code >= 0 {
        return Ok(code.into());
    }
    let exponent = code
        .checked_neg()
        .ok_or_else(|| invalid("diagnostic exponent"))?;
    if !(127..=(MomentWire::LIMBS * MomentWire::LIMB_BITS) as i128).contains(&exponent) {
        return Err(invalid("diagnostic exponent"));
    }
    Ok(BigInt::one() << exponent as usize)
}
fn increments(raw: &[i128], layout: &NormalLayout) -> [BigInt; STATISTIC_SCALARS] {
    let x = &raw[layout.source_at..layout.source_at + layout.source_components];
    let observed = layout.ball_at(ReportBall::Observed);
    let y = &raw[observed..observed + layout.target_components];
    let ex = BigInt::from(raw[layout.source_at + layout.source_components]);
    let ey = BigInt::from(raw[layout.ball_radius_at(ReportBall::Observed)]);
    let nx = ceil_norm(x);
    let ny = ceil_norm(y);
    [
        (2 * &nx + &ex) * &ex,
        &ny * &ex + &nx * &ey + &ex * &ey,
        y.iter().map(|v| BigInt::from(*v).pow(2)).sum(),
        (2 * &ny + &ey) * &ey,
    ]
}
pub(in super::super) fn validate_report(
    s: &ResidentSectionRest,
    n: usize,
    t: usize,
    linked: bool,
) -> Result<i128, ConstitutiveFibreError> {
    validate_report_layout(
        s,
        &NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?,
        linked,
    )
}
fn validate_report_layout(
    s: &ResidentSectionRest,
    layout: &NormalLayout,
    linked: bool,
) -> Result<i128, ConstitutiveFibreError> {
    point_section(s, 1, layout.report_words)?;
    let base = layout.report_moments_at;
    let v = wides(&s.intervals[..base])?;
    let extra = layout.metadata_at;
    if ReportBall::ALL
        .iter()
        .any(|&ball| v[layout.ball_radius_at(ball)] < 0)
        || v[layout.source_at + layout.source_components] < 0
        || v[extra..extra + 3].iter().any(|v| *v < 0)
    {
        return Err(invalid("report bound"));
    }
    diagnostic_numerator(v[extra + 3])?;
    diagnostic_numerator(v[extra + 4])?;
    let expected = if linked {
        increments(&v, &layout)
    } else {
        std::array::from_fn(|_| BigInt::zero())
    };
    for (i, want) in expected.iter().enumerate() {
        if integer(&s.intervals[base + MomentWire::WORDS * i..base + MomentWire::WORDS * (i + 1)])?
            != *want
        {
            return Err(invalid("observation increment"));
        }
    }
    if !linked
        && v[layout.source_at..layout.source_at + layout.source_components + 1]
            .iter()
            .any(|v| *v != 0)
    {
        return Err(invalid("unobserved source increment"));
    }
    Ok(v[extra])
}

// Cold persistence validation pays the actual sufficient-statistic identity. This is not a
// second learner: no coefficient is fitted or field operation replayed by this check.
pub(in super::super) fn validate_state<'a>(
    s: &ResidentSectionRest,
    n: usize,
    t: usize,
    grain: u32,
    error: i128,
    reports: impl Iterator<Item = (bool, &'a ResidentSectionRest)>,
) -> Result<(), ConstitutiveFibreError> {
    point_section(
        s,
        1,
        state_words(n, t).ok_or(ConstitutiveFibreError::Shape)?,
    )?;
    let layout = NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?;
    let m = layout.sources;
    let h = layout.matrix_words;
    let hh = layout.gram_values;
    let bb = layout.cross_values;
    let scale = BigInt::one() << grain;
    let square = &scale * &scale;
    let mut expected = vec![BigInt::zero(); hh + bb + STATISTIC_SCALARS];
    for i in 0..m {
        expected[2 * (i * m + i)] = square.clone();
    }
    for (linked, r) in reports {
        if !linked {
            continue;
        }
        let base = layout.report_moments_at;
        let v = wides(&r.intervals[..base])?;
        let x = &v[layout.source_at..layout.source_at + layout.source_components];
        let observed = layout.ball_at(ReportBall::Observed);
        let y = &v[observed..observed + layout.target_components];
        let xs = (0..m)
            .filter(|&i| x[2 * i] != 0 || x[2 * i + 1] != 0)
            .collect::<Vec<_>>();
        for &i in &xs {
            let ar = BigInt::from(x[2 * i]);
            let ai = BigInt::from(x[2 * i + 1]);
            for &j in &xs {
                let br = BigInt::from(x[2 * j]);
                let bi = BigInt::from(x[2 * j + 1]);
                expected[2 * (i * m + j)] += &ar * &br + &ai * &bi;
                expected[2 * (i * m + j) + 1] += &ai * &br - &ar * &bi;
            }
        }
        for i in (0..t).filter(|&i| y[2 * i] != 0 || y[2 * i + 1] != 0) {
            let ar = BigInt::from(y[2 * i]);
            let ai = BigInt::from(y[2 * i + 1]);
            for &j in &xs {
                let br = BigInt::from(x[2 * j]);
                let bi = BigInt::from(x[2 * j + 1]);
                expected[hh + 2 * (i * m + j)] += &ar * &br + &ai * &bi;
                expected[hh + 2 * (i * m + j) + 1] += &ai * &br - &ar * &bi;
            }
        }
        for i in 0..STATISTIC_SCALARS {
            expected[hh + bb + i] += integer(
                &r.intervals[base + MomentWire::WORDS * i..base + MomentWire::WORDS * (i + 1)],
            )?;
        }
    }
    for (i, want) in expected.iter().enumerate() {
        if integer(&s.intervals[h + MomentWire::WORDS * i..h + MomentWire::WORDS * (i + 1)])?
            != *want
        {
            return Err(invalid(
                "standing does not equal its observed normal increments",
            ));
        }
    }
    validate_numerical_witness(s, n, t, grain, error, &expected)
}

// Shared exact wire-scale comparison. This avoids reducing millions of intermediate
// rational products when a cold material already supplies one common dyadic chart.
fn validate_numerical_witness(
    s: &ResidentSectionRest,
    n: usize,
    t: usize,
    grain: u32,
    error: i128,
    expected: &[BigInt],
) -> Result<(), ConstitutiveFibreError> {
    validate_numerical_witness_layout(
        s,
        NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?,
        t,
        grain,
        error,
        expected,
    )
}
fn validate_numerical_witness_layout(
    s: &ResidentSectionRest,
    layout: NormalLayout,
    t: usize,
    grain: u32,
    error: i128,
    expected: &[BigInt],
) -> Result<(), ConstitutiveFibreError> {
    let m = layout.sources;
    let h = layout.matrix_words;
    let hh = layout.gram_values;
    let bb = layout.cross_values;
    let scale = BigInt::one() << grain;
    let square = &scale * &scale;
    let matrix = wides(&s.intervals[..h])?;
    if matrix[bb] != error || matrix[bb..].iter().any(|v| *v < 0) {
        return Err(invalid("coefficient/error standing"));
    }
    let norm: BigInt = matrix[..bb].iter().map(|v| BigInt::from(*v).abs()).sum();
    if norm != BigInt::from(matrix[bb + 2]) {
        return Err(invalid("coefficient norm"));
    }
    // The same exact WH-B witness through its actual nonzero moment entries.
    // Unit-prior directions and sparse observed source support need no dense matrix product.
    let support = (0..m)
        .map(|k| {
            (0..m)
                .filter(|&j| {
                    !expected[2 * (k * m + j)].is_zero() || !expected[2 * (k * m + j) + 1].is_zero()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut residual = BigInt::zero();
    // The coefficient and complete B rows are the whole WH-B operand for one target row.
    // Borrow both slices so repeated rows reuse only the exact residual value; keying on B
    // alone would let a corrupted duplicate coefficient row inherit its neighbour's witness.
    let mut residual_cache: BTreeMap<(&[i128], &[BigInt]), BigInt> = BTreeMap::new();
    for row in 0..t {
        let coefficient_row = &matrix[2 * row * m..2 * (row + 1) * m];
        let b_row = &expected[hh + 2 * row * m..hh + 2 * (row + 1) * m];
        if let Some(cached) = residual_cache.get(&(coefficient_row, b_row)) {
            residual += cached;
            continue;
        }
        if coefficient_row.iter().all(|v| *v == 0) && b_row.iter().all(Zero::is_zero) {
            residual_cache.insert((coefficient_row, b_row), BigInt::zero());
            continue;
        }
        let mut real = vec![BigInt::zero(); m];
        let mut imaginary = vec![BigInt::zero(); m];
        for k in 0..m {
            let at = 2 * (row * m + k);
            if matrix[at] == 0 && matrix[at + 1] == 0 {
                continue;
            }
            let ar = BigInt::from(matrix[at]);
            let ai = BigInt::from(matrix[at + 1]);
            for &j in &support[k] {
                let br = &expected[2 * (k * m + j)];
                let bi = &expected[2 * (k * m + j) + 1];
                real[j] += &ar * br - &ai * bi;
                imaginary[j] += &ar * bi + &ai * br;
            }
        }
        let mut row_residual = BigInt::zero();
        for j in 0..m {
            real[j] -= &scale * &b_row[2 * j];
            imaginary[j] -= &scale * &b_row[2 * j + 1];
            row_residual += real[j].abs() + imaginary[j].abs();
        }
        residual += &row_residual;
        // Every duplicate contributes its multiplicity without retaining copied row data.
        residual_cache.insert((coefficient_row, b_row), row_residual);
    }
    let ceil = |v: &BigInt| {
        let q = v / &square;
        if v % &square == BigInt::zero() {
            q
        } else {
            q + 1
        }
    };
    let residual_bound =
        ceil(&(&residual + &norm * &expected[hh + bb] + &scale * &expected[hh + bb + 1]));
    let energy = &expected[hh + bb + 2] + &expected[hh + bb + 3];
    if energy.is_negative() {
        return Err(invalid("negative target energy family"));
    }
    let root = energy.sqrt();
    let root_upper = if &root * &root == energy {
        root
    } else {
        root + 1
    };
    let energy_bound = &norm + root_upper;
    let tightened_bound = residual_bound.clone().min(energy_bound);
    // Retain legacy residual-only rests as well as the new independently certified minimum.
    // Both bounds describe the same source-qualified reference, not different coefficients.
    if BigInt::from(matrix[bb + 1]) != ceil(&residual)
        || (BigInt::from(error) != residual_bound && BigInt::from(error) != tightened_bound)
    {
        return Err(invalid("normal residual or family bound"));
    }
    Ok(())
}

#[derive(Debug, Serialize)]
pub struct NativeNormalMaterialReading {
    pub forward: NativeFieldCurrentBall,
    pub observed: NativeFieldCurrentBall,
    pub contemporary_source_forward: Option<NativeFieldCurrentBall>,
    pub returned_difference: Option<NativeFieldCurrentBall>,
    pub chronological_current: Option<NativeFieldCurrentBall>,
    pub contemporary_difference: Option<NativeFieldCurrentBall>,
    pub source_current: Option<NativeFieldCurrentBall>,
    pub coefficient_error: Rat,
    pub normal_residual_upper: Rat,
    pub coefficient_norm_upper: Rat,
    pub source_normal_error_upper: Rat,
    pub cross_source_error_upper: Rat,
    pub increments: [Rat; 4],
}
#[derive(Clone, Debug, Serialize)]
pub struct NativeNormalMaterialState {
    pub material: NativeFieldMaterialTransportState,
    pub source_normal: Vec<Vec<ExactComplexWaveCurrent>>,
    pub cross_source: Vec<Vec<ExactComplexWaveCurrent>>,
    pub source_normal_error: Rat,
    pub cross_source_error: Rat,
    pub target_energy: Rat,
    pub target_energy_error: Rat,
    pub normal_residual_upper: Rat,
}

/// Immutable nonzero coefficient prior for a normal chart.  `cross_source` is
/// `B_0 = W_0 H_0` and `target_energy` is `C_0 = ||W_0||²`; the observed
/// `target_energy` retained in a state remains Q_data.  Keeping this operand
/// separate prevents a prior from being reported as an observation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct NativeNormalPrior {
    pub cross_source: Vec<Vec<ExactComplexWaveCurrent>>,
    pub target_energy: Rat,
}

impl NativeNormalPrior {
    pub fn from_coefficients(
        coefficients: Vec<Vec<ExactComplexWaveCurrent>>,
    ) -> Result<Self, ConstitutiveFibreError> {
        if coefficients.is_empty()
            || coefficients
                .iter()
                .any(|row| row.len() != coefficients[0].len())
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let target_energy = coefficients
            .iter()
            .flatten()
            .map(ExactComplexWaveCurrent::norm_square)
            .sum();
        Ok(Self {
            cross_source: coefficients,
            target_energy,
        })
    }

    pub fn source_complex(&self) -> usize {
        self.cross_source.first().map_or(0, Vec::len)
    }
    pub fn targets(&self) -> usize {
        self.cross_source.len()
    }
}

/// Cold objective comparison in the unit-prior source chart. This describes the observed
/// geometry, not language quality or a unique source selected from the retained family.
#[derive(Debug, Serialize)]
pub struct NativeNormalMaterialObjective {
    pub nominal_data_term: Rat,
    pub prior_term: Rat,
    pub nominal_regularized_objective: Rat,
    pub normal_residual_squared: Rat,
    /// H >= I implies 0 <= Phi(M) - min Phi <= ||M H - B||_F^2 / 2.
    pub solve_gap_upper: Rat,
    pub nominal_minimum: crate::ExactInterval,
    /// Bounds at the stored numerical M over every admitted observed-source/target family.
    pub family_data_term: crate::ExactInterval,
    pub family_regularized_objective: crate::ExactInterval,
    /// Minimum for each admitted source geometry, including its unit prior.
    pub family_minimum: crate::ExactInterval,
}

impl NativeNormalMaterialState {
    /// Evaluate the normal objective with a supplied immutable prior.  The resident
    /// state carries total H/B, while its Q_data remains the observed/proxy-target
    /// energy; this method forms B-B0 and adds C0 only for the objective.
    pub fn objective_with_prior(
        &self,
        prior: &NativeNormalPrior,
    ) -> Result<NativeNormalMaterialObjective, ConstitutiveFibreError> {
        if prior.targets() != self.cross_source.len()
            || prior.source_complex() != self.source_normal.len()
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut data = self.clone();
        for (row, p) in data.cross_source.iter_mut().zip(&prior.cross_source) {
            for (value, prior_value) in row.iter_mut().zip(p) {
                *value = value.subtract(prior_value);
            }
        }
        data.target_energy += &prior.target_energy;
        data.objective()
    }

    /// Validate the prior's dimensions and the retained H-I/B-B0 split without
    /// conflating its C0 with Q_data.  Source-family uncertainty remains separate.
    pub fn validate_prior(&self, prior: &NativeNormalPrior) -> Result<(), ConstitutiveFibreError> {
        if prior.targets() != self.cross_source.len()
            || prior.source_complex() != self.source_normal.len()
            || self
                .source_normal
                .iter()
                .any(|row| row.len() != self.source_normal.len())
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        // Validate the observed source geometry as H-I. A nonzero prior does
        // not require a fresh chart after observations have accumulated.
        for i in 0..self.source_normal.len() {
            for j in 0..self.source_normal.len() {
                if self.source_normal[i][j] != self.source_normal[j][i].conjugate() {
                    return Err(ConstitutiveFibreError::Uncertain);
                }
            }
            let observed_diagonal = &self.source_normal[i][i].real - Rat::one();
            if observed_diagonal.is_negative() {
                return Err(ConstitutiveFibreError::Uncertain);
            }
        }
        Ok(())
    }

    /// Decode the signed numerical normal residual from its retained exact factors.
    /// Source/target family uncertainty remains in the separate normal and cross-source bounds.
    pub fn normal_residual(
        &self,
    ) -> Result<Vec<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
        let m = self.source_normal.len();
        if m == 0
            || self.source_normal.iter().any(|r| r.len() != m)
            || self.material.coefficients.len() != self.cross_source.len()
            || self
                .material
                .coefficients
                .iter()
                .chain(&self.cross_source)
                .any(|r| r.len() != m)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(self
            .material
            .coefficients
            .iter()
            .zip(&self.cross_source)
            .map(|(row, b)| {
                (0..m)
                    .map(|j| {
                        row.iter()
                            .zip(&self.source_normal)
                            .fold(ExactComplexWaveCurrent::zero(), |sum, (a, h)| {
                                sum.add(&a.multiply(&h[j]))
                            })
                            .subtract(&b[j])
                    })
                    .collect()
            })
            .collect())
    }

    /// Observe a state returned by `inspect_normal_material_state`. Its exact accumulated
    /// Gram and every admitted source Gram are at least I. No inverse, raw-source replay,
    /// source-centre selection for learning, or native coefficient change occurs here.
    pub fn objective(&self) -> Result<NativeNormalMaterialObjective, ConstitutiveFibreError> {
        if [
            &self.source_normal_error,
            &self.cross_source_error,
            &self.target_energy_error,
        ]
        .iter()
        .any(|q| q.is_negative())
        {
            return Err(invalid("negative objective family bound"));
        }
        let residual = self.normal_residual()?;
        let two = Rat::from_integer(2.into());
        let mut norm_square = Rat::zero();
        let mut norm_upper = Rat::zero();
        let mut cross_norm_upper = Rat::zero();
        let mut paired = Rat::zero();
        let mut residual_square = Rat::zero();
        for ((m, b), r) in self
            .material
            .coefficients
            .iter()
            .flatten()
            .zip(self.cross_source.iter().flatten())
            .zip(residual.iter().flatten())
        {
            norm_square += m.norm_square();
            norm_upper += m.real.abs() + m.imaginary.abs();
            cross_norm_upper += b.real.abs() + b.imaginary.abs();
            // M H = B + R: avoids a second matrix multiplication for the objective.
            paired += m.multiply(&r.subtract(b).conjugate()).real;
            residual_square += r.norm_square();
        }
        let prior = &norm_square / &two;
        let attained = (&self.target_energy + paired) / &two;
        let data = &attained - &prior;
        if data.is_negative() || attained.is_negative() {
            return Err(invalid(
                "objective incompatible with accumulated unit-prior geometry",
            ));
        }
        let gap = &residual_square / &two;
        let lower = (&attained - &gap).max(Rat::zero());
        let family_error = (&norm_square * &self.source_normal_error
            + &two * &norm_upper * &self.cross_source_error
            + &self.target_energy_error)
            / &two;
        // Both minimizers have norm <= ||B_nominal||_F + EB. L1 is an exact upper bound.
        let k = cross_norm_upper + &self.cross_source_error;
        let minimum_error = (&k * &k * &self.source_normal_error
            + &two * &k * &self.cross_source_error
            + &self.target_energy_error)
            / &two;
        let around = |value: &Rat, error: &Rat| crate::ExactInterval {
            lower: (value - error).max(Rat::zero()),
            upper: value + error,
        };
        Ok(NativeNormalMaterialObjective {
            family_data_term: around(&data, &family_error),
            family_regularized_objective: around(&attained, &family_error),
            family_minimum: crate::ExactInterval {
                lower: (&lower - &minimum_error).max(Rat::zero()),
                upper: &attained + &minimum_error,
            },
            nominal_minimum: crate::ExactInterval {
                lower,
                upper: attained.clone(),
            },
            nominal_data_term: data,
            prior_term: prior,
            nominal_regularized_objective: attained,
            normal_residual_squared: residual_square,
            solve_gap_upper: gap,
        })
    }
}
impl NativeConstitutiveField<'_> {
    pub fn inspect_normal_material_transport(
        &self,
        at: usize,
    ) -> Result<Option<NativeNormalMaterialReading>, ConstitutiveFibreError> {
        if self.material_transport_source() != Some(NativeMaterialTransportSource::OperativeNormal)
        {
            return Err(invalid("wrong material law"));
        }
        let Some(s) = self.inspect_material_transport_wire(at)? else {
            return Ok(None);
        };
        let n = self.nodes();
        let t = self
            .material_target_dimension()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let g = self.transport_grain()?;
        let linked = self
            .history
            .get(at)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?
            .lineage
            .observed_source()
            .is_some();
        decode_report(&s, n, t, g, linked).map(Some)
    }
    pub fn inspect_normal_material_state(
        &self,
    ) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if self.material_transport_source() != Some(NativeMaterialTransportSource::OperativeNormal)
        {
            return Err(invalid("wrong material law"));
        }
        let n = self.nodes();
        let t = self
            .material_target_dimension()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let g = self.transport_grain()?;
        let state = self
            .relation
            .surface
            .detach_section(&self.transport.as_ref().unwrap().state, 64)?;
        decode_state(&state, n, t, g)
    }
}

#[cfg(test)]
mod tests;

fn decode_report(
    s: &ResidentSectionRest,
    n: usize,
    t: usize,
    g: u32,
    linked: bool,
) -> Result<NativeNormalMaterialReading, ConstitutiveFibreError> {
    decode_report_layout(
        s,
        NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?,
        g,
        linked,
    )
}
fn decode_report_layout(
    s: &ResidentSectionRest,
    layout: NormalLayout,
    g: u32,
    linked: bool,
) -> Result<NativeNormalMaterialReading, ConstitutiveFibreError> {
    validate_report_layout(s, &layout, linked)?;
    let base = layout.report_moments_at;
    let v = wides(&s.intervals[..base])?;
    let extra = layout.metadata_at;
    let scale = BigInt::one() << g;
    let q = |x: i128| Rat::new(x.into(), scale.clone());
    let ball = |start: usize, width: usize| NativeFieldCurrentBall {
        center: v[start..start + width]
            .chunks_exact(2)
            .map(|x| ExactComplexWaveCurrent::new(q(x[0]), q(x[1])))
            .collect(),
        radius: q(v[start + width]),
    };
    let raw = (0..STATISTIC_SCALARS)
        .map(|i| {
            integer(&s.intervals[base + MomentWire::WORDS * i..base + MomentWire::WORDS * (i + 1)])
                .map(|v| Rat::new(v, &scale * &scale))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(NativeNormalMaterialReading {
        forward: ball(
            layout.ball_at(ReportBall::Forward),
            layout.target_components,
        ),
        observed: ball(
            layout.ball_at(ReportBall::Observed),
            layout.target_components,
        ),
        contemporary_source_forward: linked.then(|| {
            ball(
                layout.ball_at(ReportBall::ContemporarySource),
                layout.target_components,
            )
        }),
        returned_difference: linked.then(|| {
            ball(
                layout.ball_at(ReportBall::ReturnedDifference),
                layout.target_components,
            )
        }),
        chronological_current: linked.then(|| {
            ball(
                layout.ball_at(ReportBall::Chronological),
                layout.target_components,
            )
        }),
        contemporary_difference: linked.then(|| {
            ball(
                layout.ball_at(ReportBall::ContemporaryDifference),
                layout.target_components,
            )
        }),
        source_current: linked.then(|| ball(layout.source_at, layout.source_components)),
        coefficient_error: q(v[extra]),
        normal_residual_upper: q(v[extra + 1]),
        coefficient_norm_upper: q(v[extra + 2]),
        source_normal_error_upper: Rat::new(diagnostic_numerator(v[extra + 3])?, scale.clone()),
        cross_source_error_upper: Rat::new(diagnostic_numerator(v[extra + 4])?, scale),
        increments: raw.try_into().map_err(|_| ConstitutiveFibreError::Shape)?,
    })
}

fn decode_state(
    state: &ResidentSectionRest,
    n: usize,
    t: usize,
    g: u32,
) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
    decode_state_layout(
        state,
        NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?,
        t,
        g,
    )
}
fn decode_state_layout(
    state: &ResidentSectionRest,
    layout: NormalLayout,
    t: usize,
    g: u32,
) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
    point_section(state, 1, layout.state_words)?;
    let numeric = wides(&state.intervals[..layout.matrix_words])?;
    let unit = BigInt::one() << g;
    if numeric[layout.cross_values] < 0 {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    let m = layout.sources;
    let h = layout.matrix_words;
    let b = layout.cross_words_at();
    let e = layout.scalar_words_at();
    let scale = BigInt::one() << (2 * g);
    let q = |at: usize| {
        integer(&state.intervals[at..at + MomentWire::WORDS]).map(|v| Rat::new(v, scale.clone()))
    };
    let matrix = |at: usize,
                  rows: usize|
     -> Result<Vec<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
        (0..rows)
            .map(|i| {
                (0..m)
                    .map(|j| {
                        Ok(ExactComplexWaveCurrent::new(
                            q(at + MomentWire::COMPLEX_WORDS * (i * m + j))?,
                            q(at + MomentWire::COMPLEX_WORDS * (i * m + j) + MomentWire::WORDS)?,
                        ))
                    })
                    .collect()
            })
            .collect()
    };
    Ok(NativeNormalMaterialState {
        material: NativeFieldMaterialTransportState {
            coefficients: numeric[..layout.cross_values]
                .chunks_exact(2 * m)
                .map(|row| {
                    row.chunks_exact(2)
                        .map(|z| {
                            ExactComplexWaveCurrent::new(
                                Rat::new(z[0].into(), unit.clone()),
                                Rat::new(z[1].into(), unit.clone()),
                            )
                        })
                        .collect()
                })
                .collect(),
            radius: Rat::new(numeric[layout.cross_values].into(), unit.clone()),
        },
        source_normal: matrix(h, m)?,
        cross_source: matrix(b, t)?,
        source_normal_error: q(e)?,
        cross_source_error: q(e + MomentWire::WORDS)?,
        target_energy: q(e + 2 * MomentWire::WORDS)?,
        target_energy_error: q(e + 3 * MomentWire::WORDS)?,
        normal_residual_upper: Rat::new(
            wides(&state.intervals[h - 4..h - 2])?[0].into(),
            BigInt::one() << g,
        ),
    })
}

/// The resident scalar keeps Q_data+C₀ so the existing CUDA normal-fit ABI can
/// use the augmented reference bound.  Exterior inspection exposes Q_data alone;
/// the prior remains an explicit sibling operand.
pub(super) fn expose_data_energy(
    mut state: NativeNormalMaterialState,
    prior: Option<&NativeNormalPrior>,
) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
    if let Some(prior) = prior {
        if state.target_energy < prior.target_energy {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        state.target_energy -= &prior.target_energy;
    }
    Ok(state)
}

mod direct;
pub use direct::{
    BoundaryMaterialMaps, BoundaryMaterialSeed, CompiledCoupledJoint,
    ConstitutiveComparisonSection, ConstitutiveSourceFrame, ConstitutiveSourceRefusal,
    CoupledConstitutiveAlternative, CoupledConstitutiveFamily, CoupledConstitutiveRefusal,
    CoupledConstitutiveRest, CoupledJointEvaluation, CoupledJointReading, FamilyBasisReading,
    FamilyBasisSelection, NormalBasisScore, NormalBasisSelection, NormalContinuationJoin,
    NormalContinuationPullback, NormalCoupledAttachRefusal, NormalCoupledComparison,
    NormalCoupledContact, NormalCoupledContinuation, NormalCoupledObservation,
    NormalCoupledPrediction, NormalCoupledProducingHandle, NormalCoupledReception,
    NormalCoupledSourceActuation, NormalCoupledStep, NormalFamilyBasisFace,
    NormalFamilyComparisonRow, NormalFamilyPullback, NormalFamilyReceiverReading,
    NormalFamilySupport, NormalMaterialRest, NormalProducingHandle, NormalRealizationRefinement,
    NormalReceiverCoordinates, NormalSectionBasisFace, NormalSourceActuation, NormalSourceChart,
    NormalWaveBasisChart, NormalWaveBasisFace, NormalWaveBasisReading, NormalWaveComparison,
    NormalWaveComparisonReading, NormalWaveCoupled, NormalWaveCurrent, NormalWaveDevelopment,
    NormalWaveFacePacket, NormalWaveFamily, NormalWaveFamilyReceiver, NormalWaveFamilyRest,
    NormalWaveFibre, NormalWaveJointSource, NormalWavePrediction, NormalWaveReading,
    NormalWaveReception, NormalWaveReceptionReading, NormalWaveReference,
    NormalWaveReferenceReading, NormalWaveRest, NormalWaveSeedKind, NormalWaveSeedRefusal,
    NormalWaveSource, NormalWaveStep, NormalWaveTransport, NormalWaveTransportChange,
    NormalWaveWord, ResidentCoupledConstitutive, ResidentHeldSection, ResidentHeldSectionRest,
    ResidentNormalEnclosure, ResidentNormalEnclosureSection, ResidentNormalEnclosureView,
    ResidentNormalInput, ResidentNormalMaterial, ResidentNormalMaterialView, ResidentNormalReturn,
    ResidentNormalSectionReturn, ResidentNormalWave,
};
pub use direct::{
    NativeAffineGeometry, NativeAffineGeometryAdjoint, NativeEnclosurePropagation,
    NativeRealification, NativeRealificationAdjoint,
};
