//! Ordinary source/condition material conduct and native source-null reference frames.
use super::super::current_history_source::{decode_source, integer};
use super::*;

pub(in super::super) struct ContextualWork<'c> {
    pub(in super::super) table: ResidentSection<'c>,
    pub(in super::super) weights: ResidentSection<'c>,
    pub(in super::super) evaluations: ResidentSection<'c>,
}
#[cfg(test)]
pub(in super::super) fn offsets(n: usize) -> [usize; 7] {
    offsets_for(n,n)
}
pub(in super::super) fn offsets_for(n:usize,targets:usize)->[usize;7]{
    let beta = 22 * (2 * targets + 1);
    let output = beta + 8 * targets;
    let input = output + 16 * n + 12;
    let context = input + 16 * n + 12;
    let raw = context + 36 * n + 22;
    let meta = raw + 30 * targets;
    [beta, output, input, context, raw, meta, meta + 4]
}
#[derive(Debug, Serialize)]
pub struct NativeVisibleSourceReading {
    pub exact: Vec<ExactComplexWaveCurrent>,
    pub center: Vec<ExactComplexWaveCurrent>,
    pub radius: Rat,
    pub numerical_norm_square_with_reference: Rat,
    pub numerical_norm_upper_with_reference: Rat,
}
#[derive(Debug, Serialize)]
pub struct NativeContextualMaterialReading {
    pub target_chart: NativeMaterialTarget,
    pub source_chart_version: u32,
    pub forward: NativeFieldCurrentBall,
    pub effective_source_forward: Option<NativeFieldCurrentBall>,
    pub observed: NativeFieldCurrentBall,
    pub returned_difference: Option<NativeFieldCurrentBall>,
    pub parameter_change: Option<NativeFieldCurrentBall>,
    pub condition_change: Option<NativeFieldCurrentBall>,
    pub contemporary_difference: Option<NativeFieldCurrentBall>,
    pub original_source_at_current_map: Option<NativeFieldCurrentBall>,
    pub contextual_return: Option<NativeFieldCurrentBall>,
    pub contextual_forward_after_ordinary_return: Option<NativeFieldCurrentBall>,
    pub contextual_residual: Option<NativeFieldCurrentBall>,
    pub ordinary_factor: Vec<ExactComplexWaveCurrent>,
    pub contextual_factor: Vec<ExactComplexWaveCurrent>,
    pub visible_source: NativeVisibleSourceReading,
    pub input_source: Option<NativeVisibleSourceReading>,
    pub context: Option<NativeCurrentHistorySourceReading>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub operative_context: Option<NativeOperativeContextReading>,
    pub source_occurrence: Option<usize>,
    pub input_context_occurrence: Option<usize>,
    pub reference_receiving_occurrence: Option<usize>,
    pub coefficient_error: Rat,
    pub coefficient_norm_upper: Rat,
    pub ordinary_gain: Rat,
    pub contextual_gain: Option<Rat>,
    pub forward_evaluation_error: Rat,
}
#[derive(Debug, Serialize)]
pub struct NativeOperativeContextReading {
    pub occurrence: usize,
    pub outgoing_center: Vec<ExactComplexWaveCurrent>,
    pub internal_center: Vec<ExactComplexWaveCurrent>,
    pub source_radius: Rat,
    pub numerical_norm_square: Rat,
    pub numerical_norm_upper: Rat,
}
pub(in super::super) fn validate_operative_profile(
    words: &[(i64, i64)],
    n: usize,
    grain: u32,
    at: usize,
    b: Option<&ResidentSectionRest>,
) -> Result<(), ConstitutiveFibreError> {
    let d = 6 * n;
    if words.len() != 6 * d + 22
        || words.iter().any(|(a, b)| a != b)
        || words[2 * d..6 * d + 10].iter().any(|p| p.0 != 0)
        || words[6 * d + 15].0 != grain as i64
        || words[6 * d + 18].0 < 0
        || words[6 * d + 19].0 != at as i64
    {
        return Err(invalid("operative source profile"));
    }
    let norm = integer(&words[6 * d + 10..6 * d + 15])?;
    let bounds = wides(&words[6 * d + 16..6 * d + 18])?;
    let upper = wides(&words[6 * d + 20..])?[0];
    let u = BigInt::from(upper);
    let prev = &u - 1;
    if norm < BigInt::from(0)
        || bounds[0] < 0
        || upper < 0
        || &u * &u < norm
        || (upper > 0 && &prev * &prev >= norm)
    {
        return Err(invalid("operative source bound"));
    }
    if let Some(b) = b {
        let count = words[6 * d + 18].0 as usize;
        if b.rows != count.max(1) || b.width != 4 || b.grain.0 != 0 {
            return Err(invalid("operative source population"));
        }
        let body = wides(&b.intervals)?;
        let out = wides(&words[..2 * d])?;
        let actual = out
            .iter()
            .chain(body[..2 * count].iter())
            .map(|v| {
                let v = BigInt::from(*v);
                &v * &v
            })
            .sum::<BigInt>();
        if actual != norm {
            return Err(invalid("operative source norm does not match its current"));
        }
    }
    Ok(())
}
fn invalid(s: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(format!("contextual material: {s}"))
}
fn visible(
    words: &[(i64, i64)],
    n: usize,
    grain: u32,
) -> Result<NativeVisibleSourceReading, ConstitutiveFibreError> {
    if words.len() != 16 * n + 12 || words[16 * n + 7] != (0, 0) {
        return Err(invalid("source profile shape"));
    }
    let raw = wides(&words[..8 * n + 2])?;
    let hat = wides(&words[8 * n + 2..16 * n + 2])?;
    let bounds = wides(&words[16 * n + 8..])?;
    if raw[4 * n] <= 0 || bounds.iter().any(|x| *x < 0) {
        return Err(invalid("source profile denominator or bound"));
    }
    let scale = BigInt::one() << grain;
    let norm = integer(&words[16 * n + 2..16 * n + 7])?;
    let expected = &scale * &scale
        + hat
            .iter()
            .map(|v| {
                let v = BigInt::from(*v);
                &v * &v
            })
            .sum::<BigInt>();
    let upper = BigInt::from(bounds[1]);
    let error: BigInt = raw[..4 * n]
        .iter()
        .zip(&hat)
        .map(|(a, b)| {
            let d = BigInt::from(*a) * &scale - BigInt::from(*b) * BigInt::from(raw[4 * n]);
            &d * &d
        })
        .sum();
    let radius = BigInt::from(bounds[0]) * BigInt::from(raw[4 * n]);
    if norm != expected
        || &upper * &upper < norm
        || (bounds[1] > 0 && {
            let lower = &upper - 1;
            &lower * &lower >= norm
        })
        || error > &radius * &radius
    {
        return Err(invalid("source reference norm"));
    }
    let complex = |r: i128, i: i128, d: BigInt| {
        ExactComplexWaveCurrent::new(Rat::new(r.into(), d.clone()), Rat::new(i.into(), d))
    };
    Ok(NativeVisibleSourceReading {
        exact: (0..2 * n)
            .map(|j| complex(raw[2 * j], raw[2 * j + 1], raw[4 * n].into()))
            .collect(),
        center: (0..2 * n)
            .map(|j| complex(hat[2 * j], hat[2 * j + 1], scale.clone()))
            .collect(),
        radius: Rat::new(bounds[0].into(), scale.clone()),
        numerical_norm_square_with_reference: Rat::new(norm, &scale * &scale),
        numerical_norm_upper_with_reference: Rat::new(bounds[1].into(), scale),
    })
}
pub(in super::super) fn validate_report_for(rest:&ResidentSectionRest,n:usize,targets:usize,grain:u32,at:usize)->Result<i128,ConstitutiveFibreError>{
    let [beta, output, input, context, raw, meta, extra] = offsets_for(n,targets);
    let r = 2 * targets;
    if rest.rows != 1
        || rest.width != 68 * n + 82 * targets + 96
        || rest.grain.0 != 0
        || rest.intervals.iter().any(|(a, b)| a != b)
    {
        return Err(invalid("report shape"));
    }
    let w = &rest.intervals;
    let balls = wides(&w[..beta])?;
    if (0..11).any(|i| balls[i * (r + 1) + r] < 0) {
        return Err(invalid("negative current radius"));
    }
    if w[meta].0 != at as i64
        || !matches!(w[meta + 3].0, 1 | 2 | 3)
        || w[meta + 1].0 < -1
        || w[meta + 1].0 >= at as i64
    {
        return Err(invalid("source chronology"));
    }
    let linked = w[meta + 1].0 >= 0;
    if (linked && (w[meta + 2].0 < 1 || w[meta + 2].0 > at as i64))
        || (!linked
            && (w[meta + 2].0 != -1
                || w[beta..output].iter().any(|p| p.0 != 0)
                || w[input..context].iter().any(|p| p.0 != 0)))
    {
        return Err(invalid("reference chronology"));
    }
    visible(&w[output..input], n, grain)?;
    if linked {
        visible(&w[input..context], n, grain)?;
    }
    if w[meta + 3].0 == 3 {
        validate_operative_profile(&w[context..raw], n, grain, at, None)?;
    } else {
        decode_source(&w[context..raw], n, grain, at)?;
    }
    for (i, v) in w[raw..meta].chunks_exact(5).enumerate() {
        if i >= r && integer(v)? < BigInt::from(0) {
            return Err(invalid("negative evaluation bound"));
        }
        integer(v)?;
    }
    let bounds = wides(&w[extra..])?;
    let scale = 1i128 << grain;
    if bounds.iter().any(|x| *x < 0)
        || bounds[2] > scale
        || bounds[6] > scale
        || ![0, 1].contains(&bounds[3])
        || ![0, 1].contains(&bounds[7])
    {
        return Err(invalid("material bounds or gain"));
    }
    Ok(bounds[0])
}

impl<'c> NativeConstitutiveField<'c> {
    pub(in super::super) fn prepare_contextual_work(
        &mut self,
    ) -> Result<ContextualWork<'c>, ConstitutiveFibreError> {
        let count = self.history.len();
        if count >= u32::MAX as usize {
            return Err(ConstitutiveFibreError::Shape);
        }
        for i in 0..count {
            self.mount_history_source(i)?;
        }
        let mut pointers = Vec::with_capacity(3 * count.max(1));
        for h in &self.history {
            let p = h
                .resident()?
                .transport
                .as_ref()
                .ok_or_else(|| invalid("missing historical material"))?
                .lo_device_ptr() as i64;
            pointers.push((p, p));
            let (b, k) = h
                .resident()?
                .operative
                .as_ref()
                .map_or((0, 0), |o| (o.b.lo_device_ptr() as i64, o.count as i64));
            if self.material_transport_source()
                == Some(NativeMaterialTransportSource::OperativeContextual)
                && b == 0
            {
                return Err(invalid(
                    "operative material source is missing its actual current",
                ));
            }
            pointers.extend([(b, b), (k, k)]);
        }
        if pointers.is_empty() {
            pointers.resize(3, (0, 0));
        }
        let s = self.relation.surface;
        Ok(ContextualWork {
            table: s.mount_section_rest(
                &ResidentSectionRest::found(count.max(1), 3, ResidentGrain(0), 64, pointers)
                    .map_err(invalid)?,
            )?,
            weights: s.fresh_section(count + 1, 16, ResidentGrain(0))?,
            evaluations: s.fresh_section(4, 30 * self.material_target_dimension().ok_or(ConstitutiveFibreError::Shape)?, ResidentGrain(0))?,
        })
    }
    pub fn inspect_contextual_material_transport(
        &self,
        at: usize,
    ) -> Result<Option<NativeContextualMaterialReading>, ConstitutiveFibreError> {
        if !matches!(
            self.material_transport_source(),
            Some(
                NativeMaterialTransportSource::Contextual
                    | NativeMaterialTransportSource::BilinearContextual
                    | NativeMaterialTransportSource::OperativeContextual
            )
        ) {
            return Ok(None);
        }
        let wire = self
            .inspect_material_transport_wire(at)?
            .ok_or_else(|| invalid("missing report"))?;
        let n = self.nodes();
        let target_chart=self.material_target().ok_or(ConstitutiveFibreError::Shape)?;
        let targets=target_chart.dimension(n).ok_or(ConstitutiveFibreError::Shape)?;
        let r = 2 * targets;
        let stride = r + 1;
        let grain = self.transport_grain()?;
        validate_report_for(&wire, n, targets, grain, at)?;
        let w = &wire.intervals;
        let [beta, output, input, context, raw, meta, extra] = offsets_for(n,targets);
        let values = wides(&w[..output])?;
        let scale = BigInt::one() << grain;
        let complex = |r: i128, i: i128| {
            ExactComplexWaveCurrent::new(
                Rat::new(r.into(), scale.clone()),
                Rat::new(i.into(), scale.clone()),
            )
        };
        let vector = |start: usize| {
            (0..targets)
                .map(|j| complex(values[start + 2 * j], values[start + 2 * j + 1]))
                .collect::<Vec<_>>()
        };
        let ball = |index: usize| NativeFieldCurrentBall {
            center: vector(index * stride),
            radius: Rat::new(values[index * stride + r].into(), scale.clone()),
        };
        let linked = w[meta + 1].0 >= 0;
        let contrasted = linked && w[meta + 2].0 < at as i64;
        let b = wides(&w[extra..])?;
        Ok(Some(NativeContextualMaterialReading {
            target_chart,
            source_chart_version: w[meta + 3].0 as u32,
            forward: ball(0),
            effective_source_forward: linked.then(|| ball(1)),
            observed: ball(2),
            returned_difference: linked.then(|| ball(3)),
            parameter_change: linked.then(|| ball(4)),
            condition_change: linked.then(|| ball(5)),
            contemporary_difference: linked.then(|| ball(6)),
            original_source_at_current_map: linked.then(|| ball(7)),
            contextual_return: contrasted.then(|| ball(8)),
            contextual_forward_after_ordinary_return: contrasted.then(|| ball(9)),
            contextual_residual: contrasted.then(|| ball(10)),
            ordinary_factor: vector(beta / 2),
            contextual_factor: vector(beta / 2 + r),
            visible_source: visible(&w[output..input], n, grain)?,
            input_source: if linked {
                Some(visible(&w[input..context], n, grain)?)
            } else {
                None
            },
            context: if w[meta + 3].0 == 3 {
                None
            } else {
                Some(decode_source(&w[context..raw], n, grain, at)?)
            },
            operative_context: if w[meta + 3].0 == 3 {
                Some(
                    self.history
                        .get(at)
                        .ok_or(ConstitutiveFibreError::ForeignOccurrence)?
                        .with_resident(self.relation.surface, |h| {
                            let op = h
                                .operative
                                .as_ref()
                                .ok_or_else(|| invalid("missing operative current"))?;
                            let b = self.relation.surface.detach_section(&op.b, 64)?;
                            validate_operative_profile(&w[context..raw], n, grain, at, Some(&b))?;
                            let d = 6 * n;
                            let out = wides(&w[context..context + 2 * d])?;
                            let values = wides(&b.intervals)?;
                            let radius = wides(&w[context + 6 * d + 16..context + 6 * d + 18])?[0];
                            let op_bounds = wides(
                                &self
                                    .relation
                                    .surface
                                    .detach_section(&op.bounds, 64)?
                                    .intervals,
                            )?;
                            if radius != op_bounds[1]
                                || op.count != w[context + 6 * d + 18].0 as usize
                            {
                                return Err(invalid("operative source/current cut"));
                            }
                            let vec = |v: &[i128]| {
                                v.chunks_exact(2).map(|v| complex(v[0], v[1])).collect()
                            };
                            Ok(NativeOperativeContextReading {
                                occurrence: at,
                                outgoing_center: vec(&out),
                                internal_center: vec(&values[..2 * op.count]),
                                source_radius: Rat::new(radius.into(), scale.clone()),
                                numerical_norm_square: Rat::new(
                                    integer(&w[context + 6 * d + 10..context + 6 * d + 15])?,
                                    &scale * &scale,
                                ),
                                numerical_norm_upper: Rat::new(
                                    wides(&w[context + 6 * d + 20..context + 6 * d + 22])?[0]
                                        .into(),
                                    scale.clone(),
                                ),
                            })
                        })?,
                )
            } else {
                None
            },
            source_occurrence: linked.then_some(w[meta + 1].0 as usize),
            input_context_occurrence: linked.then_some(at.saturating_sub(1)),
            reference_receiving_occurrence: linked.then_some(w[meta + 2].0 as usize),
            coefficient_error: Rat::new(b[0].into(), scale.clone()),
            coefficient_norm_upper: Rat::new(b[1].into(), scale.clone()),
            ordinary_gain: Rat::new(b[2].into(), scale.clone()),
            contextual_gain: contrasted.then(|| Rat::new(b[6].into(), scale.clone())),
            forward_evaluation_error: Rat::new(b[10].into(), scale),
        }))
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod packet_tests;
