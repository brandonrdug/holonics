//! Normalized homogeneous Hermitian sources in the existing material-return owner.
use super::super::current_history_source::{decode_source, integer};
use super::*;
mod exact;

pub(in super::super) struct MomentFactors<'c> {
    pub(in super::super) table: ResidentSection<'c>,
    pub(in super::super) weights: ResidentSection<'c>,
    pub(in super::super) count: usize,
}
#[derive(Debug, Serialize)]
pub struct NativeMomentMaterialReading {
    pub forward: NativeFieldCurrentBall,
    pub contemporary_source_forward: Option<NativeFieldCurrentBall>,
    pub observed: NativeFieldCurrentBall,
    pub returned_difference: Option<NativeFieldCurrentBall>,
    pub chronological_current: Option<NativeFieldCurrentBall>,
    pub contemporary_difference: Option<NativeFieldCurrentBall>,
    pub numerical_return_factor: Vec<ExactComplexWaveCurrent>,
    pub beta_rounding_residual: Vec<ExactComplexWaveCurrent>,
    pub grid_kernel_forward: Vec<ExactComplexWaveCurrent>,
    pub kernel_evaluation_lower: Vec<ExactComplexWaveCurrent>,
    pub kernel_evaluation_upper: Vec<ExactComplexWaveCurrent>,
    pub source: NativeCurrentHistorySourceReading,
    pub coefficient_error: Rat,
    pub coefficient_norm_upper: Rat,
    pub source_evaluation_error: Rat,
    pub forward_evaluation_error: Rat,
}
fn invalid(e: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(format!("homogeneous moment: {e}"))
}
pub(in super::super) fn validate_report(
    rest: &ResidentSectionRest,
    n: usize,
    grain: u32,
    at: usize,
) -> Result<i128, ConstitutiveFibreError> {
    let r = 2 * n;
    let d = 6 * n;
    let source = 14 * r + 12;
    let raw = source + 6 * d + 22;
    let remainder = raw + 15 * r;
    let extra = remainder + r;
    if rest.rows != 1
        || rest.width != extra + 10
        || rest.grain.0 != 0
        || rest.intervals.iter().any(|(a, b)| a != b)
    {
        return Err(invalid("report shape"));
    }
    let v = wides(&rest.intervals[..source])?;
    if (0..6).any(|i| v[i * (r + 1) + r] < 0) {
        return Err(invalid("negative current radius"));
    }
    decode_source(&rest.intervals[source..raw], n, grain, at)?;
    for (i, v) in rest.intervals[raw..remainder].chunks_exact(5).enumerate() {
        if i >= r && integer(v)? < BigInt::from(0) {
            return Err(invalid("negative oriented evaluation bound"));
        }
        integer(v)?;
    }
    if rest.intervals[remainder..extra]
        .iter()
        .any(|p| !(-1..=1).contains(&p.0))
    {
        return Err(invalid("beta remainder"));
    }
    let e = wides(&rest.intervals[extra..])?;
    if e.iter().any(|v| *v < 0) {
        return Err(invalid("negative material bound"));
    }
    Ok(e[0])
}
pub(in super::super) fn validate_state(
    rest: &ResidentSectionRest,
    n: usize,
    grain: u32,
    count: usize,
    error: i128,
) -> Result<(), ConstitutiveFibreError> {
    let ga = 12 * n + 8;
    if rest.rows != 1
        || rest.width != ga + 4
        || rest.grain.0 != 0
        || rest.intervals.iter().any(|(a, b)| a != b)
    {
        return Err(invalid("state shape"));
    }
    let w = &rest.intervals;
    if w[ga - 3].0 != count as i64
        || w[ga - 2].0 != grain as i64
        || w[ga - 1].0 != 0
        || integer(&w[ga - 8..ga - 3])? < BigInt::from(0)
    {
        return Err(invalid("birth state"));
    }
    let e = wides(&w[ga..])?;
    if e[0] != error
        || e[1] < 0
        || (count == 0 && w.iter().enumerate().any(|(i, p)| i != ga - 2 && p.0 != 0))
    {
        return Err(invalid("state bounds"));
    }
    Ok(())
}
impl<'c> NativeConstitutiveField<'c> {
    /// Physical factor addresses only. No parameter or kernel value is recomputed on the host.
    pub(in super::super) fn moment_factors(
        &mut self,
        from: usize,
    ) -> Result<MomentFactors<'c>, ConstitutiveFibreError> {
        let refs = (from..self.history.len())
            .filter_map(|i| self.history[i].lineage.received_from.map(|s| (i, s)))
            .collect::<Vec<_>>();
        for &(i, s) in &refs {
            self.mount_history_source(i)?;
            self.mount_history_source(s)?;
        }
        let mut words = Vec::with_capacity(refs.len().max(1) * 2);
        for &(i, s) in &refs {
            for at in [i, s] {
                let p = self.history[at]
                    .resident()?
                    .transport
                    .as_ref()
                    .ok_or_else(|| invalid("missing factor"))?
                    .lo_device_ptr() as i64;
                words.push((p, p));
            }
        }
        if words.is_empty() {
            words.resize(2, (0, 0));
        }
        let surface = self.relation.surface;
        Ok(MomentFactors {
            count: refs.len(),
            table: surface.mount_section_rest(
                &ResidentSectionRest::found(refs.len().max(1), 2, ResidentGrain(0), 64, words)
                    .map_err(invalid)?,
            )?,
            weights: surface.fresh_section(refs.len() + 1, 4, ResidentGrain(0))?,
        })
    }
    pub(in super::super) fn prepare_moment_refresh(
        &mut self,
        at: usize,
    ) -> Result<Option<complete::CurrentSourceRefresh<'c>>, ConstitutiveFibreError> {
        if at >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let f = self.moment_factors(at + 1)?;
        if f.count == 0 {
            return Ok(None);
        }
        Ok(Some(complete::CurrentSourceRefresh {
            tail: f.table,
            count: f.count,
            moment_weights: Some(f.weights),
            output: self
                .relation
                .surface
                .fresh_section(1, 30 * self.nodes(), ResidentGrain(0))?,
        }))
    }
    pub fn inspect_moment_material_transport(
        &self,
        at: usize,
    ) -> Result<Option<NativeMomentMaterialReading>, ConstitutiveFibreError> {
        if self.material_transport_source()
            != Some(NativeMaterialTransportSource::HomogeneousMoment)
        {
            return Ok(None);
        }
        let rest = self
            .inspect_material_transport_wire(at)?
            .ok_or_else(|| invalid("missing report"))?;
        let n = self.nodes();
        let r = 2 * n;
        let d = 6 * n;
        let stride = r + 1;
        let source = 14 * r + 12;
        let raw = source + 6 * d + 22;
        let remainder = raw + 15 * r;
        let extra = remainder + r;
        let grain = self.transport_grain()?;
        validate_report(&rest, n, grain, at)?;
        let w = &rest.intervals;
        let v = wides(&w[..source])?;
        let scale = BigInt::one() << grain;
        let square = &scale * &scale;
        let complex = |a: i128, b: i128, den: &BigInt| {
            ExactComplexWaveCurrent::new(
                Rat::new(a.into(), den.clone()),
                Rat::new(b.into(), den.clone()),
            )
        };
        let vec = |at: usize| {
            (0..n)
                .map(|i| complex(v[at + 2 * i], v[at + 2 * i + 1], &scale))
                .collect::<Vec<_>>()
        };
        let ball = |at: usize| NativeFieldCurrentBall {
            center: vec(at),
            radius: Rat::new(v[at + r].into(), scale.clone()),
        };
        let bigvec = |start: usize,
                      negative: bool|
         -> Result<Vec<ExactComplexWaveCurrent>, ConstitutiveFibreError> {
            (0..n)
                .map(|i| {
                    let a = integer(&w[start + 10 * i..start + 10 * i + 5])?;
                    let b = integer(&w[start + 10 * i + 5..start + 10 * i + 10])?;
                    Ok(ExactComplexWaveCurrent::new(
                        Rat::new(if negative { -a } else { a }, square.clone()),
                        Rat::new(if negative { -b } else { b }, square.clone()),
                    ))
                })
                .collect()
        };
        let half_scale = &scale * 2;
        let linked = self.history[at].lineage.received_from.is_some();
        let e = wides(&w[extra..])?;
        Ok(Some(NativeMomentMaterialReading {
            forward: ball(0),
            contemporary_source_forward: linked.then(|| ball(stride)),
            observed: ball(2 * stride),
            returned_difference: linked.then(|| ball(3 * stride)),
            chronological_current: linked.then(|| ball(4 * stride)),
            contemporary_difference: linked.then(|| ball(5 * stride)),
            numerical_return_factor: vec(6 * stride),
            beta_rounding_residual: (0..n)
                .map(|i| {
                    complex(
                        w[remainder + 2 * i].0.into(),
                        w[remainder + 2 * i + 1].0.into(),
                        &half_scale,
                    )
                })
                .collect(),
            grid_kernel_forward: bigvec(raw, false)?,
            kernel_evaluation_lower: bigvec(raw + 10 * r, true)?,
            kernel_evaluation_upper: bigvec(raw + 5 * r, false)?,
            source: decode_source(&w[source..raw], n, grain, at)?,
            coefficient_error: Rat::new(e[0].into(), scale.clone()),
            coefficient_norm_upper: Rat::new(e[1].into(), scale.clone()),
            source_evaluation_error: Rat::new(e[2].into(), scale.clone()),
            forward_evaluation_error: Rat::new(e[4].into(), scale),
        }))
    }
}

#[cfg(test)]
mod tests;
