//! Accumulated normal statistics and their cold receiver. The exact moments retain the
//! common source chart; a numerical material matrix is bounded by its full normal residual.
use super::*;
use crate::native_ecology::constitutive_fibre::circulation::rest::point_section;
use num_traits::{Signed, Zero};

pub(crate) fn matrix_words(n: usize, t: usize) -> Option<usize> {
    n.checked_mul(t)?.checked_mul(12)?.checked_add(6)
}
pub(crate) fn state_words(n: usize, t: usize) -> Option<usize> {
    let m = n.checked_mul(3)?;
    matrix_words(n, t)?
        .checked_add(m.checked_mul(m.checked_add(t)?)?.checked_mul(36)?)?
        .checked_add(72)
}
pub(crate) fn report_words(n: usize, t: usize) -> Option<usize> {
    t.checked_mul(24)?
        .checked_add(n.checked_mul(12)?)?
        .checked_add(96)
}
pub(crate) fn workspace_words(n: usize, t: usize) -> Option<usize> {
    let d = n.checked_mul(6)?;
    d.checked_mul(d.checked_add(t)?.checked_add(1)?)?
        .checked_mul(2)?
        .checked_add(t.checked_mul(20)?)
}
pub(super) fn initial_words(
    n: usize,
    t: usize,
    grain: u32,
) -> Result<Vec<(i64, i64)>, ConstitutiveFibreError> {
    let mut out = vec![(0, 0); state_words(n, t).ok_or(ConstitutiveFibreError::Shape)?];
    let h = matrix_words(n, t).ok_or(ConstitutiveFibreError::Shape)?;
    for i in 0..3 * n {
        let at = h + 36 * (i * 3 * n + i) + (2 * grain / 32) as usize;
        let v = 1i64 << (2 * grain % 32);
        out[at] = (v, v);
    }
    Ok(out)
}
fn invalid(s: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(format!("normal material: {s}"))
}
pub(super) fn integer(words: &[(i64, i64)]) -> Result<BigInt, ConstitutiveFibreError> {
    if words.len() != 18
        || words.iter().any(|(a, b)| a != b)
        || ![0, 1].contains(&words[17].0)
        || words[..17].iter().any(|v| v.0 < 0 || v.0 > u32::MAX as i64)
    {
        return Err(invalid("moment encoding"));
    }
    let mut n = BigInt::zero();
    for (i, v) in words[..17].iter().enumerate() {
        n += BigInt::from(v.0) << (32 * i);
    }
    if words[17].0 == 1 {
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
pub(super) fn increments(raw: &[i128], n: usize, t: usize) -> [BigInt; 4] {
    let stride = 2 * t + 1;
    let x = &raw[6 * stride..6 * stride + 6 * n];
    let y = &raw[2 * stride..2 * stride + 2 * t];
    let ex = BigInt::from(raw[6 * stride + 6 * n]);
    let ey = BigInt::from(raw[3 * stride - 1]);
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
    let base = 24 * t + 12 * n + 24;
    let v = wides(&s.intervals[..base])?;
    let stride = 2 * t + 1;
    let extra = 6 * stride + 6 * n + 1;
    if (0..6).any(|i| v[i * stride + 2 * t] < 0)
        || v[6 * stride + 6 * n] < 0
        || v[extra..].iter().any(|v| *v < 0)
    {
        return Err(invalid("report bound"));
    }
    let expected = if linked {
        increments(&v, n, t)
    } else {
        std::array::from_fn(|_| BigInt::zero())
    };
    for (i, want) in expected.iter().enumerate() {
        if integer(&s.intervals[base + 18 * i..base + 18 * (i + 1)])? != *want {
            return Err(invalid("observation increment"));
        }
    }
    if !linked
        && v[6 * stride..6 * stride + 6 * n + 1]
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
    let m = 3 * n;
    let h = matrix_words(n, t).ok_or(ConstitutiveFibreError::Shape)?;
    let hh = 2 * m * m;
    let bb = 2 * m * t;
    let scale = BigInt::one() << grain;
    let square = &scale * &scale;
    let mut expected = vec![BigInt::zero(); hh + bb + 4];
    for i in 0..m {
        expected[2 * (i * m + i)] = square.clone();
    }
    for (linked, r) in reports {
        if !linked {
            continue;
        }
        let base = 24 * t + 12 * n + 24;
        let v = wides(&r.intervals[..base])?;
        let stride = 2 * t + 1;
        let x = &v[6 * stride..6 * stride + 2 * m];
        let y = &v[2 * stride..2 * stride + 2 * t];
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
        for i in 0..4 {
            expected[hh + bb + i] += integer(&r.intervals[base + 18 * i..base + 18 * (i + 1)])?;
        }
    }
    for (i, want) in expected.iter().enumerate() {
        if integer(&s.intervals[h + 18 * i..h + 18 * (i + 1)])? != *want {
            return Err(invalid(
                "standing does not equal its observed normal increments",
            ));
        }
    }
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
    if BigInt::from(matrix[bb + 1]) != ceil(&residual)
        || BigInt::from(error)
            != ceil(&(residual + norm * &expected[hh + bb] + &scale * &expected[hh + bb + 1]))
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
impl NativeNormalMaterialState {
    /// Decode the signed numerical normal residual from its retained exact factors.
    /// Source/target family uncertainty remains in the separate normal and cross-source bounds.
    pub fn normal_residual(&self) -> Result<Vec<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
        let m = self.source_normal.len();
        if m == 0 || self.source_normal.iter().any(|r| r.len() != m)
            || self.material.coefficients.len() != self.cross_source.len()
            || self.material.coefficients.iter().chain(&self.cross_source).any(|r| r.len() != m) {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(self.material.coefficients.iter().zip(&self.cross_source).map(|(row, b)| {
            (0..m).map(|j| row.iter().zip(&self.source_normal)
                .fold(ExactComplexWaveCurrent::zero(), |sum, (a, h)| sum.add(&a.multiply(&h[j])))
                .subtract(&b[j])).collect()
        }).collect())
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
        validate_report(&s, n, t, linked)?;
        let base = 24 * t + 12 * n + 24;
        let v = wides(&s.intervals[..base])?;
        let stride = 2 * t + 1;
        let extra = 6 * stride + 6 * n + 1;
        let scale = BigInt::one() << g;
        let q = |x: i128| Rat::new(x.into(), scale.clone());
        let ball = |start: usize, width: usize| NativeFieldCurrentBall {
            center: v[start..start + width]
                .chunks_exact(2)
                .map(|x| ExactComplexWaveCurrent::new(q(x[0]), q(x[1])))
                .collect(),
            radius: q(v[start + width]),
        };
        let raw = (0..4)
            .map(|i| {
                integer(&s.intervals[base + 18 * i..base + 18 * (i + 1)])
                    .map(|v| Rat::new(v, &scale * &scale))
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Some(NativeNormalMaterialReading {
            forward: ball(0, 2 * t),
            observed: ball(2 * stride, 2 * t),
            contemporary_source_forward: linked.then(|| ball(stride, 2 * t)),
            returned_difference: linked.then(|| ball(3 * stride, 2 * t)),
            chronological_current: linked.then(|| ball(4 * stride, 2 * t)),
            contemporary_difference: linked.then(|| ball(5 * stride, 2 * t)),
            source_current: linked.then(|| ball(6 * stride, 6 * n)),
            coefficient_error: q(v[extra]),
            normal_residual_upper: q(v[extra + 1]),
            coefficient_norm_upper: q(v[extra + 2]),
            source_normal_error_upper: q(v[extra + 3]),
            cross_source_error_upper: q(v[extra + 4]),
            increments: raw.try_into().map_err(|_| ConstitutiveFibreError::Shape)?,
        }))
    }
    pub fn inspect_normal_material_state(
        &self,
    ) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        if self.material_transport_source() != Some(NativeMaterialTransportSource::OperativeNormal)
        {
            return Err(invalid("wrong material law"));
        }
        let n = self.nodes();
        let m = 3 * n;
        let t = self
            .material_target_dimension()
            .ok_or(ConstitutiveFibreError::Shape)?;
        let g = self.transport_grain()?;
        let state = self
            .relation
            .surface
            .detach_section(&self.transport.as_ref().unwrap().state, 64)?;
        let h = matrix_words(n, t).ok_or(ConstitutiveFibreError::Shape)?;
        let b = h + 36 * m * m;
        let e = b + 36 * m * t;
        let scale = BigInt::one() << (2 * g);
        let q =
            |at: usize| integer(&state.intervals[at..at + 18]).map(|v| Rat::new(v, scale.clone()));
        let matrix = |at: usize,
                      rows: usize|
         -> Result<Vec<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
            (0..rows)
                .map(|i| {
                    (0..m)
                        .map(|j| {
                            Ok(ExactComplexWaveCurrent::new(
                                q(at + 36 * (i * m + j))?,
                                q(at + 36 * (i * m + j) + 18)?,
                            ))
                        })
                        .collect()
                })
                .collect()
        };
        Ok(NativeNormalMaterialState {
            material: self
                .inspect_material_transport_state()?
                .ok_or(ConstitutiveFibreError::Shape)?,
            source_normal: matrix(h, m)?,
            cross_source: matrix(b, t)?,
            source_normal_error: q(e)?,
            cross_source_error: q(e + 18)?,
            target_energy: q(e + 36)?,
            target_energy_error: q(e + 54)?,
            normal_residual_upper: Rat::new(
                wides(&state.intervals[h - 4..h - 2])?[0].into(),
                BigInt::one() << g,
            ),
        })
    }
}

#[cfg(test)]
mod tests;
