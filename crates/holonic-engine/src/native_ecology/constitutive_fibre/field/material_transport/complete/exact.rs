//! Cold evaluation of the retained complete-source coefficient expression. Never used by a
//! productive operation, current receiver, or restart.
use super::*;

fn dot(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> ExactComplexWaveCurrent {
    a.iter()
        .zip(b)
        .fold(ExactComplexWaveCurrent::zero(), |s, (a, b)| {
            s.add(&a.conjugate().multiply(b))
        })
}
fn error_square(a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]) -> Rat {
    a.iter()
        .zip(b)
        .map(|(a, b)| a.subtract(b).norm_square())
        .sum()
}
fn check_ball(
    value: &[ExactComplexWaveCurrent],
    ball: &NativeFieldCurrentBall,
) -> Result<(), ConstitutiveFibreError> {
    if value.len() != ball.center.len()
        || error_square(value, &ball.center) > &ball.radius * &ball.radius
    {
        return Err(invalid("complete current escapes its native enclosure"));
    }
    Ok(())
}
fn outer(
    beta: &[ExactComplexWaveCurrent],
    source: &[ExactComplexWaveCurrent],
) -> Vec<Vec<ExactComplexWaveCurrent>> {
    beta.iter()
        .map(|b| source.iter().map(|x| b.multiply(&x.conjugate())).collect())
        .collect()
}
fn matrix_error(a: &[Vec<ExactComplexWaveCurrent>], b: &[Vec<ExactComplexWaveCurrent>]) -> Rat {
    a.iter().zip(b).map(|(a, b)| error_square(a, b)).sum()
}

impl NativeConstitutiveField<'_> {
    /// Evaluate the exact source-qualified return expression and check every encountered
    /// native source/current/parameter bound. Cost grows with history and rational precision.
    pub fn inspect_exact_complete_material_transport(
        &self,
        until: usize,
    ) -> Result<Option<NativeFieldExactMaterialTransport>, ConstitutiveFibreError> {
        if self.material_transport_source() != Some(NativeMaterialTransportSource::CompleteCurrent)
        {
            return Ok(None);
        }
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if until >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let exact_junction = self.decode_junction_residual_trace(until)?;
        let numeric_junction = (0..=until)
            .map(|i| {
                self.inspect_junction_enclosure(i)
                    .map(|v| v.expect("enclosed source"))
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut contacts = Vec::new();
        let mut exact_sources: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
        let mut numeric_sources: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
        let mut exact_forwards: Vec<Vec<ExactComplexWaveCurrent>> = Vec::new();
        let mut exact = zeros(self.nodes(), 3 * self.nodes());
        let mut numeric = zeros(self.nodes(), 3 * self.nodes());
        let scale = BigInt::one() << self.transport_grain()?;
        let quantize = |x: &Rat| {
            let scaled = x * Rat::from_integer(scale.clone());
            Rat::new(scaled.numer() / scaled.denom(), scale.clone())
        };
        for at in 0..=until {
            if let Some(d) = self.junction_contact(at)? {
                contacts.push((at, d));
            }
            let mut true_source = exact_junction[at].outgoing.clone();
            let mut numerical_source = numeric_junction[at].outgoing.center.clone();
            let sign = Rat::from_integer((if at % 2 == 0 { 1 } else { -1 }).into());
            for (birth, d) in &contacts {
                let zero = vec![ExactComplexWaveCurrent::zero(); 3 * self.nodes()];
                let actual_birth = if *birth == 0 {
                    &zero
                } else {
                    &exact_junction[*birth - 1].potential_prefix
                };
                let numerical_birth = if *birth == 0 {
                    &zero
                } else {
                    &numeric_junction[*birth - 1].potential_prefix.center
                };
                true_source.push(
                    dot(
                        d,
                        &subtract(&exact_junction[at].potential_prefix, actual_birth),
                    )
                    .scaled(&sign),
                );
                numerical_source.push(
                    dot(
                        d,
                        &subtract(
                            &numeric_junction[at].potential_prefix.center,
                            numerical_birth,
                        ),
                    )
                    .scaled(&sign),
                );
            }
            let reading = self
                .inspect_complete_material_transport(at)?
                .ok_or_else(|| invalid("complete source report missing"))?;
            if error_square(&true_source, &numerical_source)
                > &reading.numerical_source.source_radius * &reading.numerical_source.source_radius
                || dot(&numerical_source, &numerical_source).real
                    != reading.numerical_source.numerical_norm_square
            {
                return Err(invalid("complete source reconstruction/bound"));
            }
            for row in &mut exact {
                row.resize(true_source.len(), ExactComplexWaveCurrent::zero());
            }
            for row in &mut numeric {
                row.resize(numerical_source.len(), ExactComplexWaveCurrent::zero());
            }
            let observed = self
                .inspect_incoming(at)?
                .iter()
                .map(|v| v.current())
                .collect::<Vec<_>>();
            check_ball(&observed, &reading.observed)?;
            if let Some(source) = self.history[at].lineage.received_from {
                let old = apply(&exact, &exact_sources[source]);
                check_ball(&old, reading.contemporary_source_forward.as_ref().unwrap())?;
                check_ball(
                    &subtract(&observed, &exact_forwards[source]),
                    reading.returned_difference.as_ref().unwrap(),
                )?;
                check_ball(
                    &subtract(&old, &exact_forwards[source]),
                    reading.chronological_current.as_ref().unwrap(),
                )?;
                check_ball(
                    &subtract(&observed, &old),
                    reading.contemporary_difference.as_ref().unwrap(),
                )?;
                let numeric_old = apply(&numeric, &numeric_sources[source]);
                let quantized = numeric_old
                    .iter()
                    .map(|v| {
                        ExactComplexWaveCurrent::new(quantize(&v.real), quantize(&v.imaginary))
                    })
                    .collect::<Vec<_>>();
                if quantized != reading.contemporary_source_forward.as_ref().unwrap().center {
                    return Err(invalid("current source coefficient contraction"));
                }
                let d = denominator(&numeric_sources[source]);
                let beta = subtract(&reading.observed.center, &quantized)
                    .into_iter()
                    .map(|v| {
                        ExactComplexWaveCurrent::new(
                            quantize(&(&v.real / &d)),
                            quantize(&(&v.imaginary / &d)),
                        )
                    })
                    .collect::<Vec<_>>();
                if beta != reading.numerical_return_factor {
                    return Err(invalid("native coercive return factor"));
                }
                let exact_numeric_delta =
                    exact_delta(&numeric, &numeric_sources[source], &reading.observed.center);
                let actual_numeric_delta = outer(&beta, &numeric_sources[source]);
                if matrix_error(&exact_numeric_delta, &actual_numeric_delta)
                    > &reading.parameter_rounding_bound * &reading.parameter_rounding_bound
                {
                    return Err(invalid("numerical parameter return defect"));
                }
                let delta = exact_delta(&exact, &exact_sources[source], &observed);
                add_matrix(&mut exact, &delta);
                add_matrix(&mut numeric, &actual_numeric_delta);
            } else if reading
                .numerical_return_factor
                .iter()
                .any(|v| v != &ExactComplexWaveCurrent::zero())
            {
                return Err(invalid("unlinked parameter return"));
            }
            let forward = apply(&exact, &true_source);
            let numeric_forward = apply(&numeric, &numerical_source);
            if numeric_forward != reading.exact_numerical_forward {
                return Err(invalid("folded complete-source forward"));
            }
            check_ball(&forward, &reading.forward)?;
            if matrix_error(&exact, &numeric)
                > &reading.coefficient_error * &reading.coefficient_error
            {
                return Err(invalid("complete coefficient enclosure"));
            }
            let norm: Rat = numeric
                .iter()
                .flatten()
                .map(ExactComplexWaveCurrent::norm_square)
                .sum();
            if norm
                > &reading.numerical_coefficient_norm_upper
                    * &reading.numerical_coefficient_norm_upper
            {
                return Err(invalid("numerical coefficient norm upper bound"));
            }
            exact_sources.push(true_source);
            numeric_sources.push(numerical_source);
            exact_forwards.push(forward);
        }
        Ok(Some(NativeFieldExactMaterialTransport {
            coefficients: exact,
            forward: exact_forwards.pop().expect("requested occurrence"),
        }))
    }
}
