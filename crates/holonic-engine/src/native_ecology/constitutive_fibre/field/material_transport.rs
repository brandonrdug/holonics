//! Native returned-current material transport and cold reconstruction of its retained factors.
use super::*;
use num_bigint::BigInt;
use num_traits::One;

pub(super) mod complete;
pub(super) mod contextual;
pub(super) mod moment;
pub use complete::{
    NativeCompleteMaterialTransportReading, NativeCompleteMaterialTransportState,
    NativeMaterialModeComponent, NativeMaterialModeDifferential, NativeMaterialModeReading,
    NativeMaterialModeReturn, NativeMaterialModeUnfolding,
};
pub use contextual::{
    NativeContextualMaterialReading, NativeOperativeContextReading, NativeVisibleSourceReading,
};
pub use moment::NativeMomentMaterialReading;

/// Exterior target chart of the same native material operator. Its extent is independent
/// of the root junction. Tensor factors follow incoming order; the first factor is the
/// least-significant radix digit of the resulting coordinate.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(tag="kind", rename_all="kebab-case")]
pub enum NativeMaterialTarget {
    #[default]
    DirectCurrent,
    TensorProduct { factor_width: usize },
}
impl NativeMaterialTarget {
    pub fn dimension(self, roots:usize)->Option<usize>{
        match self {
            Self::DirectCurrent=>Some(roots),
            Self::TensorProduct{factor_width} if factor_width>=2 && roots%factor_width==0=>
                factor_width.checked_pow(u32::try_from(roots/factor_width).ok()?),
            _=>None,
        }.filter(|n|*n>0 && *n<=u32::MAX as usize/82)
    }
    pub(super) fn kernel(self)->u32 {match self {Self::DirectCurrent=>0,Self::TensorProduct{factor_width}=>factor_width as u32}}
    pub(super) fn is_direct(&self)->bool{*self==Self::DirectCurrent}
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeMaterialTransportSource {
    #[default]
    CoupledOutgoing,
    CompleteCurrent,
    HomogeneousMoment,
    /// Retained direct-sum experiment; the complete bilinear contact is `BilinearContextual`.
    Contextual,
    /// Ordinary source-null return using the full bound source/context mixed product.
    BilinearContextual,
    /// The same bilinear phase moment over explicit operative current carriers.
    OperativeContextual,
}
impl NativeMaterialTransportSource {
    pub(super) fn is_outgoing(&self) -> bool {
        *self == Self::CoupledOutgoing
    }
    pub(super) fn kernel(self) -> u32 {
        match self {
            Self::CoupledOutgoing => 1,
            Self::CompleteCurrent => 2,
            Self::HomogeneousMoment => 3,
            Self::Contextual => 4,
            Self::BilinearContextual => 5,
            Self::OperativeContextual => 6,
        }
    }
    pub(super) fn state_words(self, n: usize) -> Option<usize> {
        match self {
            Self::CoupledOutgoing => n.checked_mul(n)?.checked_mul(12)?.checked_add(2),
            Self::CompleteCurrent => n
                .checked_mul(n)?
                .checked_mul(60)?
                .checked_add(n.checked_mul(22)?)?
                .checked_add(12),
            Self::HomogeneousMoment
            | Self::Contextual
            | Self::BilinearContextual
            | Self::OperativeContextual => n.checked_mul(12)?.checked_add(12),
        }
    }
    pub(super) fn report_words_for(self,n:usize,target:NativeMaterialTarget)->Option<usize>{
        let targets=target.dimension(n)?;
        if !target.is_direct() && self!=Self::OperativeContextual {return None;}
        if matches!(
            self,
            Self::Contextual | Self::BilinearContextual | Self::OperativeContextual
        ) {
            return n.checked_mul(68)?.checked_add(targets.checked_mul(82)?)?.checked_add(96);
        }
        n.checked_mul(if self == Self::HomogeneousMoment {
            96
        } else if self == Self::CoupledOutgoing {
            36
        } else {
            74
        })?
        .checked_add(if self == Self::CoupledOutgoing {
            24
        } else {
            44
        })
    }
}

pub(super) struct MaterialTransport<'chart> {
    pub(super) state: ResidentSection<'chart>,
    pub(super) source: NativeMaterialTransportSource,
    pub(super) target: NativeMaterialTarget,
}
pub(super) struct PendingMaterialTransport<'chart> {
    pub(super) delta: ResidentSection<'chart>,
    pub(super) report: Rc<ResidentSection<'chart>>,
    pub(super) refresh: Option<complete::CurrentSourceRefresh<'chart>>,
    pub(super) moment: Option<moment::MomentFactors<'chart>>,
    pub(super) contextual: Option<contextual::ContextualWork<'chart>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldMaterialTransportReading {
    pub forward: NativeFieldCurrentBall,
    pub observed: NativeFieldCurrentBall,
    pub contemporary_source_forward: Option<NativeFieldCurrentBall>,
    pub returned_difference: Option<NativeFieldCurrentBall>,
    pub chronological_current: Option<NativeFieldCurrentBall>,
    pub contemporary_difference: Option<NativeFieldCurrentBall>,
    /// Numerical gain for the retained source centre, not an exact gain for the source current.
    pub numerical_gain: NativeFieldCurrentBall,
    pub coefficient_error: Rat,
    pub gain_denominator: Rat,
    pub update_rounding_bound: Rat,
    pub source_dot_rounding_bound: Rat,
    pub forward_dot_rounding_bound: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldMaterialTransportState {
    pub coefficients: Vec<Vec<ExactComplexWaveCurrent>>,
    /// Frobenius error of the complete complex matrix.
    pub radius: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldExactMaterialTransport {
    pub coefficients: Vec<Vec<ExactComplexWaveCurrent>>,
    pub forward: Vec<ExactComplexWaveCurrent>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldMaterialTransportResidual {
    /// Numerical delta minus the exact coercive update of the numerical operands.
    pub parameter_update: Vec<Vec<ExactComplexWaveCurrent>>,
    pub source_dot: Vec<ExactComplexWaveCurrent>,
    pub gain: Vec<ExactComplexWaveCurrent>,
}

pub(super) fn wides(words: &[(i64, i64)]) -> Result<Vec<i128>, ConstitutiveFibreError> {
    if words.len() % 2 != 0 || words.iter().any(|(a, b)| a != b) {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    Ok(words
        .chunks_exact(2)
        .map(|p| (((p[1].0 as u64 as u128) << 64) | p[0].0 as u64 as u128) as i128)
        .collect())
}
fn zeros(rows: usize, columns: usize) -> Vec<Vec<ExactComplexWaveCurrent>> {
    vec![vec![ExactComplexWaveCurrent::zero(); columns]; rows]
}
fn apply(
    matrix: &[Vec<ExactComplexWaveCurrent>],
    source: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    matrix
        .iter()
        .map(|row| {
            row.iter()
                .zip(source)
                .fold(ExactComplexWaveCurrent::zero(), |sum, (a, x)| {
                    sum.add(&a.multiply(x))
                })
        })
        .collect()
}
fn subtract(
    a: &[ExactComplexWaveCurrent],
    b: &[ExactComplexWaveCurrent],
) -> Vec<ExactComplexWaveCurrent> {
    a.iter().zip(b).map(|(a, b)| a.subtract(b)).collect()
}
fn denominator(source: &[ExactComplexWaveCurrent]) -> Rat {
    Rat::one()
        + source
            .iter()
            .map(ExactComplexWaveCurrent::norm_square)
            .sum::<Rat>()
}
fn exact_delta(
    matrix: &[Vec<ExactComplexWaveCurrent>],
    source: &[ExactComplexWaveCurrent],
    observed: &[ExactComplexWaveCurrent],
) -> Vec<Vec<ExactComplexWaveCurrent>> {
    let residual = subtract(observed, &apply(matrix, source));
    let inverse = Rat::one() / denominator(source);
    residual
        .iter()
        .map(|r| {
            source
                .iter()
                .map(|x| r.multiply(&x.conjugate()).scaled(&inverse))
                .collect()
        })
        .collect()
}
fn add_matrix(matrix: &mut [Vec<ExactComplexWaveCurrent>], delta: &[Vec<ExactComplexWaveCurrent>]) {
    for (row, change) in matrix.iter_mut().zip(delta) {
        for (a, b) in row.iter_mut().zip(change) {
            *a = a.add(b);
        }
    }
}
fn numerical_delta(
    reading: &NativeFieldMaterialTransportReading,
    grain: u32,
) -> Vec<Vec<ExactComplexWaveCurrent>> {
    let scale = BigInt::one() << grain;
    let truncate = |a: &Rat, b: &Rat| {
        let value = a * b * Rat::from_integer(scale.clone());
        Rat::new(value.numer() / value.denom(), scale.clone())
    };
    let Some(difference) = &reading.contemporary_difference else {
        return zeros(
            reading.forward.center.len(),
            reading.numerical_gain.center.len(),
        );
    };
    difference
        .center
        .iter()
        .map(|r| {
            reading
                .numerical_gain
                .center
                .iter()
                .map(|g| {
                    ExactComplexWaveCurrent::new(
                        truncate(&r.real, &g.real) - truncate(&r.imaginary, &g.imaginary),
                        truncate(&r.real, &g.imaginary) + truncate(&r.imaginary, &g.real),
                    )
                })
                .collect()
        })
        .collect()
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Found an initially zero transport in this same owner, before any material enters. Its
    /// contextual sources and actual future returns are subsequently formed on the device.
    pub fn enable_material_transport(&mut self) -> Result<(), ConstitutiveFibreError> {
        self.enable_material_transport_source(NativeMaterialTransportSource::CoupledOutgoing)
    }
    pub fn enable_material_transport_source(
        &mut self,
        source: NativeMaterialTransportSource,
    ) -> Result<(), ConstitutiveFibreError> {
        self.enable_material_transport_chart(source,NativeMaterialTarget::DirectCurrent)
    }
    pub fn enable_material_transport_chart(&mut self,source:NativeMaterialTransportSource,target:NativeMaterialTarget)
        ->Result<(),ConstitutiveFibreError>{
        source.report_words_for(self.nodes(),target).ok_or(ConstitutiveFibreError::Shape)?;
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if !self.history.is_empty()
            || self.transport.is_some()
            || !matches!(
                self.junction_representation(),
                Some(NativeFieldJunctionRepresentation::EnclosedDyadic { .. })
            )
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        if source == NativeMaterialTransportSource::OperativeContextual {
            self.enable_operative_contacts()?;
        }
        let width = source
            .state_words(self.nodes())
            .ok_or(ConstitutiveFibreError::Shape)?;
        let mut words = vec![(0, 0); width];
        if source != NativeMaterialTransportSource::CoupledOutgoing {
            let grain = self.transport_grain()? as i64;
            words[12 * self.nodes() + 6] = (grain, grain);
        }
        let state = self.relation.surface.mount_section_rest(
            &ResidentSectionRest::found(1, width, ResidentGrain(0), 64, words)
                .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        self.transport = Some(MaterialTransport { state, source, target });
        Ok(())
    }
    pub fn has_material_transport(&self) -> bool {
        self.transport.is_some()
    }
    pub fn material_transport_source(&self) -> Option<NativeMaterialTransportSource> {
        self.transport.as_ref().map(|t| t.source)
    }
    pub fn material_target(&self)->Option<NativeMaterialTarget>{self.transport.as_ref().map(|t|t.target)}
    pub fn material_target_dimension(&self)->Option<usize>{self.material_target()?.dimension(self.nodes())}
    pub(super) fn transport_grain(&self) -> Result<u32, ConstitutiveFibreError> {
        match self.junction_representation() {
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => {
                Ok(fractional_bits)
            }
            _ => Err(ConstitutiveFibreError::Shape),
        }
    }
    pub(super) fn prepare_material_transport(
        &mut self,
        source_at: Option<usize>,
    ) -> Result<Option<PendingMaterialTransport<'chart>>, ConstitutiveFibreError> {
        let Some(kind) = self.material_transport_source() else {
            return Ok(None);
        };
        let refresh = if kind == NativeMaterialTransportSource::CompleteCurrent {
            source_at
                .map(|at| self.prepare_current_source_refresh(at))
                .transpose()?
                .flatten()
        } else if kind == NativeMaterialTransportSource::HomogeneousMoment {
            source_at
                .map(|at| self.prepare_moment_refresh(at))
                .transpose()?
                .flatten()
        } else {
            None
        };
        let surface = self.relation.surface;
        Ok(Some(PendingMaterialTransport {
            contextual: if matches!(
                kind,
                NativeMaterialTransportSource::Contextual
                    | NativeMaterialTransportSource::BilinearContextual
                    | NativeMaterialTransportSource::OperativeContextual
            ) {
                Some(self.prepare_contextual_work()?)
            } else {
                None
            },
            moment: if kind == NativeMaterialTransportSource::HomogeneousMoment {
                Some(self.moment_factors(0)?)
            } else {
                None
            },
            delta: surface.fresh_section(
                1,
                kind.state_words(self.nodes())
                    .ok_or(ConstitutiveFibreError::Shape)?,
                ResidentGrain(0),
            )?,
            report: Rc::new(
                surface.fresh_section(
                    1,
                    kind.report_words_for(self.nodes(),self.material_target().unwrap())
                        .ok_or(ConstitutiveFibreError::Shape)?,
                    ResidentGrain(0),
                )?,
            ),
            refresh,
        }))
    }

    pub fn inspect_material_transport_wire(
        &self,
        occurrence: usize,
    ) -> Result<Option<ResidentSectionRest>, ConstitutiveFibreError> {
        let event = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        event.transport_rest(self.relation.surface)
    }
    pub fn inspect_material_transport(
        &self,
        occurrence: usize,
    ) -> Result<Option<NativeFieldMaterialTransportReading>, ConstitutiveFibreError> {
        if matches!(
            self.material_transport_source(),
            Some(
                NativeMaterialTransportSource::CompleteCurrent
                    | NativeMaterialTransportSource::HomogeneousMoment
                    | NativeMaterialTransportSource::Contextual
                    | NativeMaterialTransportSource::BilinearContextual
                    | NativeMaterialTransportSource::OperativeContextual
            )
        ) {
            return Err(ConstitutiveFibreError::Rest(
                "use the receiver for the selected material source".into(),
            ));
        }

        let Some(rest) = self.inspect_material_transport_wire(occurrence)? else {
            return Ok(None);
        };
        let values = wides(&rest.intervals)?;
        let target = 2 * self.nodes();
        let source = 6 * self.nodes();
        let stride = target + 1;
        let gain_at = 6 * stride;
        let extra = gain_at + source + 1;
        if values.len() != extra + 5
            || (0..6).any(|k| values[k * stride + target] < 0)
            || values[gain_at + source] < 0
            || values[extra..].iter().any(|v| *v < 0)
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let scale = BigInt::one() << self.transport_grain()?;
        let rat = |v: i128| Rat::new(v.into(), scale.clone());
        let ball = |at: usize, real: usize| NativeFieldCurrentBall {
            center: (0..real / 2)
                .map(|i| {
                    ExactComplexWaveCurrent::new(
                        rat(values[at + 2 * i]),
                        rat(values[at + 2 * i + 1]),
                    )
                })
                .collect(),
            radius: rat(values[at + real]),
        };
        let linked = self.history[occurrence].lineage.received_from.is_some();
        Ok(Some(NativeFieldMaterialTransportReading {
            forward: ball(0, target),
            observed: ball(2 * stride, target),
            contemporary_source_forward: linked.then(|| ball(stride, target)),
            returned_difference: linked.then(|| ball(3 * stride, target)),
            chronological_current: linked.then(|| ball(4 * stride, target)),
            contemporary_difference: linked.then(|| ball(5 * stride, target)),
            numerical_gain: ball(gain_at, source),
            coefficient_error: rat(values[extra]),
            gain_denominator: rat(values[extra + 1]),
            update_rounding_bound: rat(values[extra + 2]),
            source_dot_rounding_bound: rat(values[extra + 3]),
            forward_dot_rounding_bound: rat(values[extra + 4]),
        }))
    }
    pub fn inspect_material_transport_state(
        &self,
    ) -> Result<Option<NativeFieldMaterialTransportState>, ConstitutiveFibreError> {
        if matches!(
            self.material_transport_source(),
            Some(
                NativeMaterialTransportSource::CompleteCurrent
                    | NativeMaterialTransportSource::HomogeneousMoment
                    | NativeMaterialTransportSource::Contextual
                    | NativeMaterialTransportSource::BilinearContextual
                    | NativeMaterialTransportSource::OperativeContextual
            )
        ) {
            return Err(ConstitutiveFibreError::Rest(
                "use the receiver for the selected material source".into(),
            ));
        }

        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let Some(transport) = &self.transport else {
            return Ok(None);
        };
        let values = wides(&self.relation.surface.read_out(&transport.state)?)?;
        let rows = self.nodes();
        let columns = 3 * rows;
        if values.len() != 2 * rows * columns + 1 || values[2 * rows * columns] < 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let scale = BigInt::one() << self.transport_grain()?;
        let rat = |v: i128| Rat::new(v.into(), scale.clone());
        Ok(Some(NativeFieldMaterialTransportState {
            coefficients: (0..rows)
                .map(|i| {
                    (0..columns)
                        .map(|j| {
                            let at = 2 * (i * columns + j);
                            ExactComplexWaveCurrent::new(rat(values[at]), rat(values[at + 1]))
                        })
                        .collect()
                })
                .collect(),
            radius: rat(values[2 * rows * columns]),
        }))
    }
    /// Reconstruct the complete oriented arithmetic defect from retained update factors. This
    /// cold decoder performs no native event, parameter update or source-handle creation.
    pub fn inspect_material_transport_residual(
        &self,
        occurrence: usize,
    ) -> Result<Option<NativeFieldMaterialTransportResidual>, ConstitutiveFibreError> {
        if !self.has_material_transport() {
            return Ok(None);
        }
        let mut matrix = zeros(self.nodes(), 3 * self.nodes());
        let grain = self.transport_grain()?;
        for at in 0..=occurrence {
            let reading = self
                .inspect_material_transport(at)?
                .ok_or(ConstitutiveFibreError::Uncertain)?;
            let delta = numerical_delta(&reading, grain);
            if at == occurrence {
                let Some(source) = self.history[at].lineage.received_from else {
                    return Ok(None);
                };
                let source = self
                    .inspect_junction_enclosure(source)?
                    .ok_or(ConstitutiveFibreError::Uncertain)?
                    .outgoing
                    .center;
                let ideal = exact_delta(&matrix, &source, &reading.observed.center);
                let inverse = Rat::one() / denominator(&source);
                return Ok(Some(NativeFieldMaterialTransportResidual {
                    parameter_update: delta
                        .iter()
                        .zip(&ideal)
                        .map(|(a, b)| subtract(a, b))
                        .collect(),
                    source_dot: subtract(
                        &reading.contemporary_source_forward.as_ref().unwrap().center,
                        &apply(&matrix, &source),
                    ),
                    gain: subtract(
                        &reading.numerical_gain.center,
                        &source
                            .iter()
                            .map(|x| x.conjugate().scaled(&inverse))
                            .collect::<Vec<_>>(),
                    ),
                }));
            }
            add_matrix(&mut matrix, &delta);
        }
        Err(ConstitutiveFibreError::ForeignOccurrence)
    }
    /// Exact algebraic coefficient/current reconstruction over the retained encoder trace and
    /// actual returns. It is deliberately cold and its rational work grows with the requested cut.
    pub fn inspect_exact_material_transport(
        &self,
        until: usize,
    ) -> Result<Option<NativeFieldExactMaterialTransport>, ConstitutiveFibreError> {
        if !self.has_material_transport() {
            return Ok(None);
        }
        let encoder = self.decode_junction_residual_trace(until)?;
        let mut exact = zeros(self.nodes(), 3 * self.nodes());
        let mut centre = zeros(self.nodes(), 3 * self.nodes());
        let mut forwards: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
        for at in 0..=until {
            let reading = self
                .inspect_material_transport(at)?
                .ok_or(ConstitutiveFibreError::Uncertain)?;
            if let Some(source) = self.history[at].lineage.received_from {
                let x = &encoder[source].outgoing;
                let y = self
                    .inspect_incoming(at)?
                    .iter()
                    .map(|value| value.current())
                    .collect::<Vec<_>>();
                let current = apply(&exact, x);
                let old = &forwards[source];
                if !reading.observed.contains(&y)
                    || !reading
                        .contemporary_source_forward
                        .as_ref()
                        .unwrap()
                        .contains(&current)
                    || !reading
                        .returned_difference
                        .as_ref()
                        .unwrap()
                        .contains(&subtract(&y, old))
                    || !reading
                        .chronological_current
                        .as_ref()
                        .unwrap()
                        .contains(&subtract(&current, old))
                    || !reading
                        .contemporary_difference
                        .as_ref()
                        .unwrap()
                        .contains(&subtract(&y, &current))
                {
                    return Err(ConstitutiveFibreError::Rest(format!(
                        "unfounded material return at {at}"
                    )));
                }
                let delta = exact_delta(&exact, x, &y);
                add_matrix(&mut exact, &delta);
            }
            add_matrix(
                &mut centre,
                &numerical_delta(&reading, self.transport_grain()?),
            );
            let difference = exact
                .iter()
                .zip(&centre)
                .flat_map(|(a, b)| a.iter().zip(b))
                .map(|(a, b)| a.subtract(b).norm_square())
                .sum::<Rat>();
            if difference > &reading.coefficient_error * &reading.coefficient_error {
                return Err(ConstitutiveFibreError::Rest(format!(
                    "unfounded coefficient enclosure at {at}"
                )));
            }
            let forward = apply(&exact, &encoder[at].outgoing);
            if !reading.forward.contains(&forward) {
                return Err(ConstitutiveFibreError::Rest(format!(
                    "unfounded material emission at {at}"
                )));
            }
            forwards.push(forward);
        }
        Ok(Some(NativeFieldExactMaterialTransport {
            coefficients: exact,
            forward: forwards.pop().unwrap(),
        }))
    }
}

#[cfg(test)]
mod tests;
