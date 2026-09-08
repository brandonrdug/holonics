//! Complete-current material transport receivers and physical preparation of an older-source
//! contraction. Native coefficient updates are performed only by the fused field return.
use super::super::current_history_source::{decode_source, integer};
use super::*;

mod exact;
mod mode;
pub use mode::{
    NativeMaterialModeComponent, NativeMaterialModeDifferential, NativeMaterialModeReading,
    NativeMaterialModeReturn, NativeMaterialModeUnfolding,
};
#[cfg(test)]
mod tests;

pub(in super::super) struct CurrentSourceRefresh<'chart> {
    pub(in super::super) tail: ResidentSection<'chart>,
    pub(in super::super) count: usize,
    pub(in super::super) output: ResidentSection<'chart>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NativeCompleteMaterialTransportState {
    /// Folded material action on the outgoing part of a new source.
    pub outgoing_coefficients: Vec<Vec<ExactComplexWaveCurrent>>,
    /// Folded action on the prefix of a source newer than every retained coefficient source.
    pub prefix_coefficients: Vec<Vec<ExactComplexWaveCurrent>>,
    pub birth_offset: Vec<ExactComplexWaveCurrent>,
    pub coefficient_error: Rat,
    pub numerical_coefficient_norm_upper: Rat,
    /// Exact mixed-scale native birth moment; source-qualified history remains part of the model.
    pub numerical_birth_cross: Vec<ExactComplexWaveCurrent>,
    pub numerical_birth_square: Rat,
    pub birth_occurrences: usize,
}
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NativeCompleteMaterialTransportReading {
    pub forward: NativeFieldCurrentBall,
    pub observed: NativeFieldCurrentBall,
    pub contemporary_source_forward: Option<NativeFieldCurrentBall>,
    pub returned_difference: Option<NativeFieldCurrentBall>,
    pub chronological_current: Option<NativeFieldCurrentBall>,
    pub contemporary_difference: Option<NativeFieldCurrentBall>,
    pub numerical_return_factor: Vec<ExactComplexWaveCurrent>,
    pub exact_numerical_forward: Vec<ExactComplexWaveCurrent>,
    pub numerical_source: NativeCurrentHistorySourceReading,
    pub coefficient_error: Rat,
    pub numerical_coefficient_norm_upper: Rat,
    pub parameter_rounding_bound: Rat,
    pub source_dot_rounding_bound: Rat,
    pub forward_dot_rounding_bound: Rat,
}
fn invalid(e: impl std::fmt::Display) -> ConstitutiveFibreError {
    ConstitutiveFibreError::Rest(format!("complete material transport: {e}"))
}
fn complex256(
    words: &[(i64, i64)],
    scale: &BigInt,
) -> Result<ExactComplexWaveCurrent, ConstitutiveFibreError> {
    Ok(ExactComplexWaveCurrent::new(
        Rat::new(integer(&words[..5])?, scale.clone()),
        Rat::new(integer(&words[5..10])?, scale.clone()),
    ))
}

pub(in super::super) fn validate_report(
    rest: &ResidentSectionRest,
    n: usize,
    grain: u32,
    at: usize,
) -> Result<i128, ConstitutiveFibreError> {
    let r = 2 * n;
    let d = 6 * n;
    let balls = 12 * (r + 1);
    let feature = balls + 7 * r;
    let extra = feature + 6 * d + 22;
    if rest.rows != 1
        || rest.width != extra + 10
        || rest.grain.0 != 0
        || rest.intervals.iter().any(|(a, b)| a != b)
    {
        return Err(invalid("full report shape"));
    }
    let values = wides(&rest.intervals[..balls])?;
    if (0..6).any(|i| values[i * (r + 1) + r] < 0) {
        return Err(invalid("full report radius"));
    }
    for words in rest.intervals[balls + 2 * r..feature].chunks_exact(5) {
        integer(words)?;
    }
    decode_source(&rest.intervals[feature..extra], n, grain, at)?;
    let values = wides(&rest.intervals[extra..])?;
    if values.iter().any(|v| *v < 0) {
        return Err(invalid("full report error"));
    }
    Ok(values[0])
}
pub(in super::super) fn validate_state(
    rest: &ResidentSectionRest,
    n: usize,
    grain: u32,
    occurrences: usize,
    error: i128,
) -> Result<(), ConstitutiveFibreError> {
    let ga = 12 * n + 8;
    let words = &rest.intervals;
    if rest.rows != 1
        || rest.width != 60 * n * n + 22 * n + 12
        || rest.grain.0 != 0
        || words.iter().any(|(a, b)| a != b)
    {
        return Err(invalid("full state shape"));
    }
    if words[ga - 3].0 != occurrences as i64
        || words[ga - 2].0 != grain as i64
        || words[ga - 1].0 != 0
        || integer(&words[ga - 8..ga - 3])? < BigInt::from(0)
    {
        return Err(invalid("full birth state"));
    }
    for chunk in words[ga..words.len() - 4].chunks_exact(5) {
        integer(chunk)?;
    }
    let extra = wides(&words[words.len() - 4..])?;
    if extra[0] != error || extra[1] < 0 {
        return Err(invalid("full state bound"));
    }
    if occurrences == 0
        && words
            .iter()
            .enumerate()
            .any(|(i, p)| i != ga - 2 && p.0 != 0)
    {
        return Err(invalid("nonempty initial full transport"));
    }
    Ok(())
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Read the current complete material operator at an actual retained source without
    /// receiving another occurrence. Only placement and this explicit receiver are enacted.
    pub fn read_complete_material_source(
        &mut self,
        source: &NativeFieldSourceAnchor,
    ) -> Result<NativeFieldCurrentBall, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&self.owner, &source.owner) || source.occurrence >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        if self.material_transport_source() != Some(NativeMaterialTransportSource::CompleteCurrent)
        {
            return Err(invalid("complete transport required"));
        }
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let at = source.occurrence;
        self.mount_history_source(at)?;
        let refresh = self.prepare_current_source_refresh(at)?;
        let report = self.history[at]
            .resident()?
            .transport
            .as_ref()
            .ok_or_else(|| invalid("source report absent"))?;
        let surface = self.relation.surface;
        let output = surface.fresh_section(1, 4 * self.nodes() + 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            if let Some(r) = &refresh {
                surface.record_complete_material_source_current(
                    &lane,
                    report,
                    &r.tail,
                    r.count,
                    self.nodes(),
                    &r.output,
                )?;
            }
            surface.record_complete_material_source_reading(
                &lane,
                &self.transport.as_ref().unwrap().state,
                report,
                refresh.as_ref().map(|r| &r.output),
                self.nodes(),
                self.transport_grain()?,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "complete material source: {:?}",
                reading.obstruction
            )));
        }
        let values = wides(&surface.read_out(&output)?)?;
        let scale = BigInt::one() << self.transport_grain()?;
        if values[2 * self.nodes()] < 0 {
            return Err(invalid("negative source-current radius"));
        }
        Ok(NativeFieldCurrentBall {
            center: (0..self.nodes())
                .map(|i| {
                    ExactComplexWaveCurrent::new(
                        Rat::new(values[2 * i].into(), scale.clone()),
                        Rat::new(values[2 * i + 1].into(), scale.clone()),
                    )
                })
                .collect(),
            radius: Rat::new(values[2 * self.nodes()].into(), scale),
        })
    }
    pub(in super::super) fn prepare_current_source_refresh(
        &mut self,
        at: usize,
    ) -> Result<Option<CurrentSourceRefresh<'chart>>, ConstitutiveFibreError> {
        if at >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let increments = (at + 1..self.history.len())
            .filter_map(|i| {
                self.history[i]
                    .lineage
                    .received_from
                    .map(|source| (i, source))
            })
            .collect::<Vec<_>>();
        if increments.is_empty() {
            return Ok(None);
        }
        // Only physical addresses are assembled on the host. Historical numerical carriers
        // mount through their existing exact archive; no current or parameter is computed here.
        self.mount_history_source(at)?;
        let needed = increments
            .iter()
            .flat_map(|(i, s)| [*i, *s])
            .collect::<std::collections::BTreeSet<_>>();
        for index in needed {
            self.mount_history_source(index)?;
        }
        let mut words = Vec::new();
        for (i, source) in &increments {
            for index in [*i, *source] {
                let report = self.history[index]
                    .resident()?
                    .transport
                    .as_ref()
                    .ok_or_else(|| invalid("missing complete coefficient/source carrier"))?;
                let pointer = report.lo_device_ptr() as i64;
                words.push((pointer, pointer));
            }
        }
        let surface = self.relation.surface;
        Ok(Some(CurrentSourceRefresh {
            count: increments.len(),
            tail: surface.mount_section_rest(
                &ResidentSectionRest::found(increments.len(), 2, ResidentGrain(0), 64, words)
                    .map_err(invalid)?,
            )?,
            output: surface.fresh_section(1, 10 * self.nodes(), ResidentGrain(0))?,
        }))
    }
    pub fn inspect_complete_material_transport(
        &self,
        at: usize,
    ) -> Result<Option<NativeCompleteMaterialTransportReading>, ConstitutiveFibreError> {
        if self.material_transport_source() != Some(NativeMaterialTransportSource::CompleteCurrent)
        {
            return Ok(None);
        }
        let rest = self
            .inspect_material_transport_wire(at)?
            .ok_or_else(|| invalid("missing complete report"))?;
        let n = self.nodes();
        let r = 2 * n;
        let d = 6 * n;
        let stride = r + 1;
        let beta_at = 12 * stride;
        let forward_at = beta_at + 2 * r;
        let feature_at = forward_at + 5 * r;
        let extra_at = feature_at + 6 * d + 22;
        if rest.width != extra_at + 10 || rest.intervals.iter().any(|(a, b)| a != b) {
            return Err(invalid("report extent"));
        }
        let words = &rest.intervals;
        let values = wides(&words[..beta_at + 2 * r])?;
        let scale = BigInt::one() << self.transport_grain()?;
        let cube = &scale * &scale * &scale;
        let vector = |offset: usize| -> Vec<ExactComplexWaveCurrent> {
            (0..n)
                .map(|i| {
                    ExactComplexWaveCurrent::new(
                        Rat::new(values[offset + 2 * i].into(), scale.clone()),
                        Rat::new(values[offset + 2 * i + 1].into(), scale.clone()),
                    )
                })
                .collect()
        };
        let ball = |at: usize| -> Result<NativeFieldCurrentBall, ConstitutiveFibreError> {
            if values[at + r] < 0 {
                return Err(invalid("negative material radius"));
            }
            Ok(NativeFieldCurrentBall {
                center: vector(at),
                radius: Rat::new(values[at + r].into(), scale.clone()),
            })
        };
        let linked = self.history[at].lineage.received_from.is_some();
        let extra = wides(&words[extra_at..])?;
        if extra.iter().any(|v| *v < 0) {
            return Err(invalid("negative material error"));
        }
        Ok(Some(NativeCompleteMaterialTransportReading {
            forward: ball(0)?,
            observed: ball(2 * stride)?,
            contemporary_source_forward: linked.then(|| ball(stride)).transpose()?,
            returned_difference: linked.then(|| ball(3 * stride)).transpose()?,
            chronological_current: linked.then(|| ball(4 * stride)).transpose()?,
            contemporary_difference: linked.then(|| ball(5 * stride)).transpose()?,
            numerical_return_factor: vector(6 * stride),
            exact_numerical_forward: (0..n)
                .map(|i| complex256(&words[forward_at + 10 * i..forward_at + 10 * i + 10], &cube))
                .collect::<Result<_, _>>()?,
            numerical_source: decode_source(
                &words[feature_at..extra_at],
                n,
                self.transport_grain()?,
                at,
            )?,
            coefficient_error: Rat::new(extra[0].into(), scale.clone()),
            numerical_coefficient_norm_upper: Rat::new(extra[1].into(), scale.clone()),
            parameter_rounding_bound: Rat::new(extra[2].into(), scale.clone()),
            source_dot_rounding_bound: Rat::new(extra[3].into(), scale.clone()),
            forward_dot_rounding_bound: Rat::new(extra[4].into(), scale),
        }))
    }
    pub fn inspect_complete_material_transport_state(
        &self,
    ) -> Result<Option<NativeCompleteMaterialTransportState>, ConstitutiveFibreError> {
        let Some(transport) = self
            .transport
            .as_ref()
            .filter(|t| t.source == NativeMaterialTransportSource::CompleteCurrent)
        else {
            return Ok(None);
        };
        let rest = self.relation.surface.detach_section(&transport.state, 64)?;
        let n = self.nodes();
        let d = 6 * n;
        let ga = 2 * d + 8;
        let matrix_words = 30 * n * n;
        let offset = ga + 2 * matrix_words;
        let extra_at = offset + 10 * n;
        let scale = BigInt::one() << self.transport_grain()?;
        let square = &scale * &scale;
        let cube = &square * &scale;
        let words = &rest.intervals;
        if words.len() != extra_at + 4 || words.iter().any(|(a, b)| a != b) {
            return Err(invalid("state extent"));
        }
        let matrix =
            |start: usize| -> Result<Vec<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
                (0..n)
                    .map(|row| {
                        (0..3 * n)
                            .map(|col| {
                                let at = start + 10 * (row * 3 * n + col);
                                complex256(&words[at..at + 10], &square)
                            })
                            .collect()
                    })
                    .collect()
            };
        let extra = wides(&words[extra_at..])?;
        if extra.iter().any(|v| *v < 0) {
            return Err(invalid("negative state bound"));
        }
        let birth_values = wides(&words[..12 * n])?;
        let birth_cross = (0..3 * n)
            .map(|i| {
                ExactComplexWaveCurrent::new(
                    Rat::new(birth_values[2 * i].into(), scale.clone()),
                    Rat::new(birth_values[2 * i + 1].into(), scale.clone()),
                )
            })
            .collect();
        Ok(Some(NativeCompleteMaterialTransportState {
            outgoing_coefficients: matrix(ga)?,
            prefix_coefficients: matrix(ga + matrix_words)?,
            birth_offset: (0..n)
                .map(|i| complex256(&words[offset + 10 * i..offset + 10 * i + 10], &cube))
                .collect::<Result<_, _>>()?,
            coefficient_error: Rat::new(extra[0].into(), scale.clone()),
            numerical_coefficient_norm_upper: Rat::new(extra[1].into(), scale),
            numerical_birth_cross: birth_cross,
            numerical_birth_square: Rat::new(integer(&words[ga - 8..ga - 3])?, square),
            birth_occurrences: words[ga - 3].0 as usize,
        }))
    }
}
