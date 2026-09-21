//! Cold decoder of the exact deposit and the retained unrounded-response comparison.
use super::*;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

fn factor_reference_bound(rp: &Rat, rc: &Rat, ports_l1: &Rat, currents_l1: &Rat) -> Rat {
    rp * currents_l1 + rc * ports_l1 + rp * rc
}

#[derive(Debug, Serialize)]
pub struct NativeContactDepositReading {
    pub at_cut: usize,
    pub contact_count: usize,
    pub realization: NativeContactRealization,
    pub bound_kind: NativeOperativeBoundKind,
    /// Under `FactorBalls` this is the first factor-ball radius, not a matrix radius.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub factor_port_radius: Option<Rat>,
    /// Under `FactorBalls` this is the second factor-ball radius, not an internal-current radius.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub factor_current_radius: Option<Rat>,
    /// A cold, arbitrary-precision scalar upper bound derived from the retained factor balls.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub factor_reference_bound: Option<Rat>,
    pub fractional_bits: u32,
    /// Legacy matrix-and-internal packets report their covector radius here. For a sparse
    /// factor-ball packet this is the arbitrary-precision scalar reference bound below; the
    /// factor fields above remain the authoritative tagged radii.
    pub unrounded_covector_radius: Rat,
    /// Oriented Q_F(Ghat)-Ghat, decoded from the immutable factors, in contact birth order.
    pub numerical_projection_residual: Vec<Vec<ExactComplexWaveCurrent>>,
    pub numerical_projection_residual_norm_square: Rat,
    /// Bounds distance from the installed numerical increment to the unrounded covector.
    /// In DyadicDeposit this is a comparison defect, not uncertainty in the new coefficient.
    pub unrounded_response_distance_upper: Rat,
}

#[derive(Debug, Serialize)]
pub struct NativeContactDepositBoundReading {
    pub at_cut: usize,
    pub realization: NativeContactRealization,
    pub bound_kind: NativeOperativeBoundKind,
    /// Populated only for the legacy matrix-and-internal interpretation.
    pub matrix_radius: Option<Rat>,
    pub internal_radius: Option<Rat>,
    /// Populated only for the sparse factor-ball interpretation.
    pub factor_port_radius: Option<Rat>,
    pub factor_current_radius: Option<Rat>,
}

impl NativeConstitutiveField<'_> {
    /// Cold source-qualified bound inspection. This reads only the retained bound packet and
    /// never expands the d×k factor products or matrix increment.
    pub fn inspect_contact_deposit_bound(
        &self,
        at: usize,
    ) -> Result<NativeContactDepositBoundReading, Error> {
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        let returned = op.returns.get(at).ok_or(Error::ForeignOccurrence)?;
        let words = wides(
            &self
                .relation
                .surface
                .detach_section(&returned.bounds, 64)?
                .intervals,
        )?;
        if words.len() != 2 || words.iter().any(|value| *value < 0) {
            return Err(Error::Uncertain);
        }
        let scale = BigInt::one() << op.grain;
        let first = Rat::new(words[0].into(), scale.clone());
        let second = Rat::new(words[1].into(), scale);
        let factor = returned.bound_kind() == NativeOperativeBoundKind::FactorBalls;
        Ok(NativeContactDepositBoundReading {
            at_cut: returned.at_cut,
            realization: returned.realization,
            bound_kind: returned.bound_kind(),
            matrix_radius: (!factor).then(|| first.clone()),
            internal_radius: (!factor).then(|| second.clone()),
            factor_port_radius: factor.then(|| first),
            factor_current_radius: factor.then(|| second),
        })
    }

    pub fn inspect_contact_deposit(&self, at: usize) -> Result<NativeContactDepositReading, Error> {
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        let r = op.returns.get(at).ok_or(Error::ForeignOccurrence)?;
        let read = |s: &ResidentSection<'_>| {
            wides(&self.relation.surface.detach_section(s, 64)?.intervals)
        };
        let ports = read(&r.ports)?;
        let factors = self.resolve_operative_current_factors(r)?;
        let currents = read(&factors)?;
        let bounds = read(&r.bounds)?;
        let bound_kind = r.bound_kind();
        let source = r
            .source_overlap
            .as_ref()
            .map(|h| {
                let map = self.operative_producing_map(h.source)?;
                Ok::<_, Error>((read(&map)?, read(&h.coefficients)?, h.count))
            })
            .transpose()?;
        let scale = BigInt::one() << op.grain;
        let scale_ratio = Rat::from_integer(scale.clone());
        let wave = |v: &[i128]| {
            ExactComplexWaveCurrent::new(
                Rat::new(v[0].into(), scale.clone()),
                Rat::new(v[1].into(), scale.clone()),
            )
        };
        let l1 = |values: &[i128]| {
            values
                .chunks_exact(2)
                .map(|pair| {
                    Rat::new(pair[0].into(), scale.clone()).abs()
                        + Rat::new(pair[1].into(), scale.clone()).abs()
                })
                .sum::<Rat>()
        };
        let d = 6 * self.nodes();
        let k = r.contact_count;
        let mut residual = Vec::with_capacity(k);
        let mut norm = Rat::zero();
        let mut loss = Rat::zero();
        for i in 0..k {
            let mut row = Vec::with_capacity(d / 2);
            for j in (0..d).step_by(2) {
                let mut value = ExactComplexWaveCurrent::zero();
                for f in 0..if i < r.factor_count { 2 } else { 0 } {
                    value = value.add(
                        &wave(&ports[f * d + j..f * d + j + 2]).multiply(
                            &wave(
                                &currents[2 * (f * r.factor_count + i)
                                    ..2 * (f * r.factor_count + i) + 2],
                            )
                            .conjugate(),
                        ),
                    );
                }
                if let Some((source, h, count)) = &source {
                    for after in 0..*count {
                        let joined = op.births[after].source;
                        let Ok(before) =
                            op.births[..after].binary_search_by_key(&joined, |b| b.receiving)
                        else {
                            continue;
                        };
                        let z = wave(&h[2 * after..2 * after + 2]);
                        if i == before {
                            value = value.add(
                                &wave(&source[after * d + j..after * d + j + 2])
                                    .multiply(&z.conjugate()),
                            );
                        }
                        if i == after {
                            value = value.add(
                                &wave(&source[before * d + j..before * d + j + 2]).multiply(&z),
                            );
                        }
                    }
                }
                // Sparse deposits retain the exact products of their dyadic factors (2g
                // scale); there is no additional coefficient-grid projection in that map.
                let quantize = |x: &Rat| {
                    if op.sections.factor_program.is_some() {
                        x.clone()
                    } else {
                        Rat::new((x * &scale_ratio).to_integer(), scale.clone())
                    }
                };
                let difference = ExactComplexWaveCurrent::new(
                    quantize(&value.real) - value.real,
                    quantize(&value.imaginary) - value.imaginary,
                );
                norm += difference.norm_square();
                loss += difference.real.abs() + difference.imaginary.abs();
                row.push(difference);
            }
            residual.push(row);
        }
        let factor_reference_bound = if bound_kind == NativeOperativeBoundKind::FactorBalls {
            let rp = Rat::new(bounds[0].into(), BigInt::one() << op.grain);
            let rc = Rat::new(bounds[1].into(), BigInt::one() << op.grain);
            let pn = l1(&ports);
            let cn = l1(&currents);
            Some(factor_reference_bound(&rp, &rc, &pn, &cn))
        } else {
            None
        };
        let radius = factor_reference_bound
            .clone()
            .unwrap_or_else(|| Rat::new(bounds[0].into(), scale.clone()));
        Ok(NativeContactDepositReading {
            at_cut: r.at_cut,
            contact_count: k,
            realization: r.realization,
            bound_kind,
            factor_port_radius: (bound_kind == NativeOperativeBoundKind::FactorBalls)
                .then(|| Rat::new(bounds[0].into(), scale.clone())),
            factor_current_radius: (bound_kind == NativeOperativeBoundKind::FactorBalls)
                .then(|| Rat::new(bounds[1].into(), scale.clone())),
            factor_reference_bound: factor_reference_bound.clone(),
            fractional_bits: op.grain,
            unrounded_covector_radius: radius.clone(),
            numerical_projection_residual: residual,
            numerical_projection_residual_norm_square: norm,
            unrounded_response_distance_upper: factor_reference_bound.unwrap_or(radius + loss),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factor_reference_bound_keeps_overwide_factor_balls_out_of_carrier_arithmetic() {
        let huge = Rat::from_integer(BigInt::one() << 200);
        let bound = factor_reference_bound(&huge, &huge, &huge, &huge);
        assert!(bound > Rat::from_integer(BigInt::one() << 400));
    }
}
