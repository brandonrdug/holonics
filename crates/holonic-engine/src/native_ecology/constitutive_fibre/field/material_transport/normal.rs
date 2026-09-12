//! Accumulated normal statistics and their cold receiver. The exact moments retain the
//! common source chart; a numerical material matrix is bounded by its full normal residual.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::point_section;
use num_traits::{Signed, Zero};

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
pub(super) fn initial_words(
    n: usize,
    t: usize,
    grain: u32,
) -> Result<Vec<(i64, i64)>, ConstitutiveFibreError> {
    let layout = NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?;
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
    if &s * &s < q {
        s + 1
    } else {
        s
    }
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
    point_section(
        s,
        1,
        report_words(n, t).ok_or(ConstitutiveFibreError::Shape)?,
    )?;
    let layout = NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?;
    let base = layout.report_moments_at;
    let v = wides(&s.intervals[..base])?;
    let extra = layout.metadata_at;
    if ReportBall::ALL
        .iter()
        .any(|&ball| v[layout.ball_radius_at(ball)] < 0)
        || v[layout.source_at + layout.source_components] < 0
        || v[extra..].iter().any(|v| *v < 0)
    {
        return Err(invalid("report bound"));
    }
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
    s: &ResidentSectionRest, n: usize, t: usize, grain: u32,
    error: i128, expected: &[BigInt],
) -> Result<(), ConstitutiveFibreError> {
    let layout=NormalLayout::new(n,t).ok_or(ConstitutiveFibreError::Shape)?;
    let m=layout.sources;
    let h=layout.matrix_words;
    let hh=layout.gram_values;
    let bb=layout.cross_values;
    let scale=BigInt::one()<<grain;
    let square=&scale*&scale;
    let matrix = wides(&s.intervals[..h])?;
    if matrix[bb] != error || matrix[bb..].iter().any(|v| *v < 0) {
        return Err(invalid("coefficient/error standing"));
    }
    let norm: BigInt = matrix[..bb].iter().map(|v| BigInt::from(*v).abs()).sum();
    if norm != BigInt::from(matrix[bb + 2]) {
        return Err(invalid("coefficient norm"));
    }
    let mut residual = BigInt::zero();
    for row in 0..t {
        if matrix[2 * row * m..2 * (row + 1) * m]
            .iter()
            .all(|v| *v == 0)
            && expected[hh + 2 * row * m..hh + 2 * (row + 1) * m]
                .iter()
                .all(Zero::is_zero)
        {
            continue;
        }
        for j in 0..m {
            let mut re = BigInt::zero();
            let mut im = BigInt::zero();
            for k in 0..m {
                let ar = BigInt::from(matrix[2 * (row * m + k)]);
                let ai = BigInt::from(matrix[2 * (row * m + k) + 1]);
                let br = &expected[2 * (k * m + j)];
                let bi = &expected[2 * (k * m + j) + 1];
                re += &ar * br - &ai * bi;
                im += &ar * bi + &ai * br;
            }
            re -= &scale * &expected[hh + 2 * (row * m + j)];
            im -= &scale * &expected[hh + 2 * (row * m + j) + 1];
            residual += re.abs() + im.abs();
        }
    }
    let ceil = |v: &BigInt| {
        let q = v / &square;
        if v % &square == BigInt::zero() {
            q
        } else {
            q + 1
        }
    };
    let residual_bound = ceil(&(&residual + &norm * &expected[hh + bb]
        + &scale * &expected[hh + bb + 1]));
    let energy = &expected[hh + bb + 2] + &expected[hh + bb + 3];
    if energy.is_negative() { return Err(invalid("negative target energy family")); }
    let root = energy.sqrt();
    let root_upper = if &root * &root == energy { root } else { root + 1 };
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
#[derive(Debug, Serialize)]
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
    validate_report(s, n, t, linked)?;
    let layout = NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?;
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
        source_normal_error_upper: q(v[extra + 3]),
        cross_source_error_upper: q(v[extra + 4]),
        increments: raw.try_into().map_err(|_| ConstitutiveFibreError::Shape)?,
    })
}

fn decode_state(
    state: &ResidentSectionRest,
    n: usize,
    t: usize,
    g: u32,
) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
    let layout = NormalLayout::new(n, t).ok_or(ConstitutiveFibreError::Shape)?;
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

mod direct;
pub use direct::{ResidentNormalMaterial, NormalMaterialRest, NormalRealizationRefinement, ResidentNormalReturn, ResidentNormalWave, NormalWaveWord, NormalWaveCoupled, NormalCoupledAttachRefusal, NormalCoupledContact, NormalCoupledStep, NormalCoupledReception, NormalCoupledSourceActuation, NormalCoupledProducingHandle, NormalCoupledPrediction, NormalCoupledComparison, ConstitutiveComparisonSection, ResidentCoupledConstitutive, CoupledConstitutiveRefusal, ConstitutiveSourceRefusal, CoupledConstitutiveRest, NormalCoupledContinuation, NormalContinuationPullback, NormalContinuationJoin, CoupledConstitutiveFamily, CoupledConstitutiveAlternative, CompiledCoupledJoint, CoupledJointEvaluation, CoupledJointReading, NormalFamilyComparisonRow, NormalWaveCurrent, NormalWaveFibre, NormalWaveStep, NormalWaveReading, NormalWaveRest, NormalWaveSeedRefusal, NormalWaveSeedKind, NormalWaveReception, NormalWaveReceptionReading, NormalWaveDevelopment, NormalSourceActuation, NormalProducingHandle, NormalWavePrediction, NormalWaveComparison, NormalWaveComparisonReading, NormalWaveTransport, NormalWaveTransportChange, NormalWaveReference, NormalWaveReferenceReading, NormalWaveBasisChart, NormalWaveBasisFace, NormalWaveBasisReading, NormalBasisSelection, NormalBasisScore, NormalWaveSource, NormalWaveJointSource, NormalReceiverCoordinates,NormalWaveFacePacket, NormalFamilyPullback, NormalWaveFamily, NormalWaveFamilyRest, NormalFamilyBasisFace, FamilyBasisSelection, FamilyBasisReading, NormalFamilySupport, NormalFamilyReceiverReading, NormalWaveFamilyReceiver, ResidentNormalSectionReturn, ResidentNormalInput, ResidentNormalEnclosure, ResidentNormalEnclosureView};
