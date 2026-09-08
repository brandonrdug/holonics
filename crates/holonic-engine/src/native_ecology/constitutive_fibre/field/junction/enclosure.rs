//! Certified current balls and the executable decoder of their retained numerical residuals.
//! This module never seals a numerical center as the unique physical current.

use super::*;
use crate::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldCurrentBall {
    pub center: Vec<ExactComplexWaveCurrent>,
    /// Euclidean radius in the complete root realification, not one radius per coordinate.
    pub radius: Rat,
}

#[cfg(test)]
mod tests;

impl NativeFieldCurrentBall {
    pub fn contains(&self, value: &[ExactComplexWaveCurrent]) -> bool {
        value.len() == self.center.len()
            && self.radius >= Rat::zero()
            && value
                .iter()
                .zip(&self.center)
                .map(|(a, b)| a.subtract(b).norm_square())
                .sum::<Rat>()
                <= &self.radius * &self.radius
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldEnclosedJunctionReading {
    pub fractional_bits: u32,
    pub potential: NativeFieldCurrentBall,
    pub outgoing: NativeFieldCurrentBall,
    pub held_current: NativeFieldCurrentBall,
    pub potential_prefix: NativeFieldCurrentBall,
    pub source_center: Vec<ExactComplexWaveCurrent>,
    /// Complete oriented A V - 2(Uhat+H), with the exact native moment and source chart.
    pub solve_residual: Vec<ExactComplexWaveCurrent>,
    pub source_error_l1_bound: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldInternalCurrentBall {
    pub source_occurrence: usize,
    pub receiving_occurrence: usize,
    pub contact: Vec<ExactComplexWaveCurrent>,
    /// The current operative map is distinct from the immutable birth contact above.
    #[serde(skip_serializing_if="Option::is_none")]
    pub operative_contact: Option<NativeFieldCurrentBall>,
    /// A single complex internal current, enclosed without evaluating the exact error trace.
    pub current: NativeFieldCurrentBall,
}

pub(super) fn decode_report(
    words: &[(i64, i64)],
    width: usize,
    grain: u32,
) -> Result<NativeFieldEnclosedJunctionReading, ConstitutiveFibreError> {
    if words.len() != 12 * (width + 1)
        || width % 2 != 0
        || !(1..=120).contains(&grain)
        || words.iter().any(|(a, b)| a != b)
    {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    let value = |index: usize| -> i128 {
        let low = words[2 * index].0 as u64 as u128;
        let high = words[2 * index + 1].0 as u64 as u128;
        ((high << 64) | low) as i128
    };
    let stride = width + 1;
    if (0..5).any(|part| value(part * stride + width) < 0) || value(5 * stride + width) <= 0 {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    let scale = BigInt::one() << grain;
    let vector = |part: usize, den: &BigInt| -> Vec<ExactComplexWaveCurrent> {
        (0..width / 2)
            .map(|j| {
                ExactComplexWaveCurrent::new(
                    Rat::new(value(part * stride + 2 * j).into(), den.clone()),
                    Rat::new(value(part * stride + 2 * j + 1).into(), den.clone()),
                )
            })
            .collect()
    };
    let ball = |part| NativeFieldCurrentBall {
        center: vector(part, &scale),
        radius: Rat::new(value(part * stride + width).into(), scale.clone()),
    };
    let residual_den = &scale * BigInt::from(value(5 * stride + width));
    Ok(NativeFieldEnclosedJunctionReading {
        fractional_bits: grain,
        potential: ball(0),
        outgoing: ball(1),
        held_current: ball(2),
        potential_prefix: ball(3),
        source_center: vector(4, &scale),
        solve_residual: vector(5, &residual_den),
        source_error_l1_bound: Rat::new(value(4 * stride + width).into(), scale),
    })
}

fn real(values: &[ExactComplexWaveCurrent]) -> Vec<Rat> {
    values
        .iter()
        .flat_map(|v| [v.real.clone(), v.imaginary.clone()])
        .collect()
}
fn complex(values: &[Rat]) -> Vec<ExactComplexWaveCurrent> {
    values
        .chunks_exact(2)
        .map(|p| ExactComplexWaveCurrent::new(p[0].clone(), p[1].clone()))
        .collect()
}
fn add(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    a.iter().zip(b).map(|(a, b)| a + b).collect()
}
fn subtract(a: &[Rat], b: &[Rat]) -> Vec<Rat> {
    a.iter().zip(b).map(|(a, b)| a - b).collect()
}
fn twice(a: &[Rat]) -> Vec<Rat> {
    a.iter().map(|v| v * Rat::from_integer(2.into())).collect()
}

impl<'chart> NativeConstitutiveField<'chart> {
    pub(in super::super) fn root_junction_source(
        &self,
        occurrence: usize,
    ) -> Result<Vec<ExactComplexWaveCurrent>, ConstitutiveFibreError> {
        let source = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let words = source.source_rest(self.relation.surface)?.intervals;
        let denominator = words[self.relation.source_width].0;
        if denominator <= 0 || words.iter().any(|(a, b)| a != b) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let mut values = Vec::with_capacity(2 * self.nodes());
        for (node, frame) in source.frame.view.root_to_local().iter().enumerate() {
            for branch in 0..2 {
                let at = 4 * node + 2 * branch;
                let local = ExactComplexWaveCurrent::new(
                    Rat::new(words[at].0.into(), denominator.into()),
                    Rat::new(words[at + 1].0.into(), denominator.into()),
                );
                values.push(frame.current().conjugate().multiply(&local));
            }
        }
        Ok(values)
    }

    pub(in super::super) fn junction_contact(
        &self,
        receiving: usize,
    ) -> Result<Option<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
        let event = self
            .history
            .get(receiving)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let Some(source) = event.lineage.received_from else {
            return Ok(None);
        };
        let mut d = self.root_junction_source(source)?;
        d.extend(
            self.inspect_incoming(receiving)?
                .iter()
                .map(|a| a.current().negated()),
        );
        Ok(Some(d))
    }

    /// Explicit cold inspection of one retained enclosed report. No exact value is selected.
    pub fn inspect_junction_enclosure(
        &self,
        occurrence: usize,
    ) -> Result<Option<NativeFieldEnclosedJunctionReading>, ConstitutiveFibreError> {
        if self.junction.as_ref().and_then(|j|j.operative.as_ref()).is_some_and(|o|occurrence>=o.activated_at) {
            return Err(ConstitutiveFibreError::Rest("operative reflection has its own complete residual receiver".into()));
        }
        let Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) =
            self.junction_representation()
        else {
            return Ok(None);
        };
        let event = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let section = event
            .junction_rest(self.relation.surface)?
            .ok_or(ConstitutiveFibreError::Uncertain)?;
        decode_report(&section.intervals, 6 * self.nodes(), fractional_bits).map(Some)
    }

    /// Cheap cold enclosure of the complete internal population through the birth-prefix map.
    /// The exact decoder remains separately available; centers here are never reported as exact.
    pub fn inspect_internal_current_enclosures(
        &self,
    ) -> Result<Option<Vec<NativeFieldInternalCurrentBall>>, ConstitutiveFibreError> {
        if let Some(op)=self.junction.as_ref().and_then(|j|j.operative.as_ref()) {
            let reading=super::operative::inspect_sections(self,op.grain,&op.births,&op.sections,0)?;
            return Ok(Some(reading.births.iter().enumerate().map(|(i,b)|Ok(NativeFieldInternalCurrentBall {
                source_occurrence:b.source,receiving_occurrence:b.receiving,
                contact:self.junction_contact(b.receiving)?.ok_or(ConstitutiveFibreError::Uncertain)?,
                operative_contact:Some(NativeFieldCurrentBall{center:reading.contacts[i].clone(),radius:reading.contacts_radius.clone()}),
                current:NativeFieldCurrentBall{center:vec![reading.internal.center[i].clone()],radius:reading.internal.radius.clone()}
            })).collect::<Result<Vec<_>,ConstitutiveFibreError>>()?));
        }
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if !matches!(
            self.junction_representation(),
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { .. })
        ) {
            return Ok(None);
        }
        if self.history.is_empty() {
            return Ok(Some(vec![]));
        }
        let now = self
            .inspect_junction_enclosure(self.history.len() - 1)?
            .expect("enclosed representation")
            .potential_prefix;
        let sign = Rat::from_integer(if self.history.len() % 2 == 1 { 1 } else { -1 }.into());
        let zero = NativeFieldCurrentBall {
            center: vec![ExactComplexWaveCurrent::zero(); 3 * self.nodes()],
            radius: Rat::zero(),
        };
        let mut values = Vec::new();
        for (at, event) in self.history.iter().enumerate() {
            let Some(source) = event.lineage.received_from else {
                continue;
            };
            let contact = self.junction_contact(at)?.expect("linked contact");
            let birth = if at == 0 {
                zero.clone()
            } else {
                self.inspect_junction_enclosure(at - 1)?
                    .expect("enclosed birth")
                    .potential_prefix
            };
            let center = contact
                .iter()
                .zip(now.center.iter().zip(&birth.center))
                .fold(ExactComplexWaveCurrent::zero(), |sum, (d, (p, p0))| {
                    sum.add(&d.conjugate().multiply(&p.subtract(p0)))
                })
                .scaled(&sign);
            let bound = contact
                .iter()
                .map(|d| d.real.abs() + d.imaginary.abs())
                .sum::<Rat>();
            let radius = bound * (&now.radius + &birth.radius);
            values.push(NativeFieldInternalCurrentBall {
                source_occurrence: source,
                receiving_occurrence: at,
                contact,
                operative_contact: None,
                current: NativeFieldCurrentBall {
                    center: vec![center],
                    radius,
                },
            });
        }
        Ok(Some(values))
    }

    /// Evaluate the held residual expression, with its zero initial error, to reconstruct one
    /// exact current. This cold reference is deliberately separate from resident conduct and
    /// restart: it issues no events, deposits or handles and changes no model state. Its cost
    /// grows with the requested historical cut and rational precision; it is not the hot solver.
    pub fn inspect_exact_junction(
        &self,
        occurrence: usize,
    ) -> Result<Option<NativeFieldExactJunctionReading>, ConstitutiveFibreError> {
        if !matches!(
            self.junction_representation(),
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { .. })
        ) {
            return Ok(None);
        }
        Ok(self.decode_junction_residual_trace(occurrence)?.pop())
    }

    pub(in super::super) fn decode_junction_residual_trace(
        &self,
        until: usize,
    ) -> Result<Vec<NativeFieldExactJunctionReading>, ConstitutiveFibreError> {
        if self.junction.as_ref().and_then(|j|j.operative.as_ref()).is_some_and(|o|until>=o.activated_at) {
            return Err(ConstitutiveFibreError::Rest("the fixed-contact residual decoder does not decode operative reflections".into()));
        }
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if until >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let width = 6 * self.nodes();
        let mut a = vec![vec![Rat::zero(); width]; width];
        for (i, row) in a.iter_mut().enumerate() {
            row[i] = Rat::one();
        }
        let mut h_error = vec![Rat::zero(); width];
        let mut prefix_error = vec![Rat::zero(); width];
        let mut prior_center = vec![Rat::zero(); width];
        let mut decoded = Vec::new();
        for at in 0..=until {
            // Decode the old constitutive operator from its actual retained factor population.
            // This is an immutable matrix expression, not an enactment of native formation.
            if let Some(d) = self.junction_contact(at)? {
                for (i, left) in d.iter().enumerate() {
                    for (j, right) in d.iter().enumerate() {
                        let c = left.multiply(&right.conjugate());
                        a[2 * i][2 * j] += &c.real;
                        a[2 * i + 1][2 * j + 1] += &c.real;
                        a[2 * i][2 * j + 1] -= &c.imaginary;
                        a[2 * i + 1][2 * j] += &c.imaginary;
                    }
                }
            }
            let observed = self
                .inspect_junction_enclosure(at)?
                .ok_or(ConstitutiveFibreError::Uncertain)?;
            let mut u = self.root_junction_source(at)?;
            u.extend(vec![ExactComplexWaveCurrent::zero(); self.nodes()]);
            let u = real(&u);
            let u_hat = real(&observed.source_center);
            let delta_u = subtract(&u, &u_hat);
            let operator = ExactRatMatrix::new(a.clone())
                .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
            let residual = real(&observed.solve_residual);
            let verify = subtract(
                &operator
                    .apply(&real(&observed.potential.center))
                    .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?,
                &twice(&add(&u_hat, &prior_center)),
            );
            if verify != residual {
                return Err(ConstitutiveFibreError::Rest(format!(
                    "unfounded native solve residual at {at}"
                )));
            }
            let rhs = subtract(&twice(&add(&h_error, &delta_u)), &residual);
            let v_error = operator
                .inverse()
                .and_then(|inverse| inverse.apply(&rhs))
                .map_err(|e| ConstitutiveFibreError::Rest(e.to_string()))?;
            let potential = complex(&add(&real(&observed.potential.center), &v_error));
            let outgoing = complex(&add(
                &real(&observed.outgoing.center),
                &subtract(&v_error, &delta_u),
            ));
            h_error = subtract(&add(&h_error, &twice(&delta_u)), &v_error);
            prefix_error = if at % 2 == 0 {
                add(&prefix_error, &v_error)
            } else {
                subtract(&prefix_error, &v_error)
            };
            let held_current = complex(&add(&real(&observed.held_current.center), &h_error));
            let potential_prefix = complex(&add(
                &real(&observed.potential_prefix.center),
                &prefix_error,
            ));
            if !observed.potential.contains(&potential)
                || !observed.outgoing.contains(&outgoing)
                || !observed.held_current.contains(&held_current)
                || !observed.potential_prefix.contains(&potential_prefix)
            {
                return Err(ConstitutiveFibreError::Rest(format!(
                    "unfounded current enclosure at {at}"
                )));
            }
            prior_center = real(&observed.held_current.center);
            decoded.push(NativeFieldExactJunctionReading {
                potential,
                outgoing,
                held_current,
                potential_prefix,
            });
        }
        Ok(decoded)
    }

    pub(super) fn decode_enclosed_internal_currents(
        &self,
    ) -> Result<Vec<NativeFieldInternalCurrent>, ConstitutiveFibreError> {
        if self.history.is_empty() {
            return Ok(vec![]);
        }
        let trace = self.decode_junction_residual_trace(self.history.len() - 1)?;
        let now = &trace.last().expect("nonempty trace").potential_prefix;
        let sign = Rat::from_integer(if self.history.len() % 2 == 1 { 1 } else { -1 }.into());
        let zero = vec![ExactComplexWaveCurrent::zero(); 3 * self.nodes()];
        let mut values = Vec::new();
        for (at, event) in self.history.iter().enumerate() {
            let Some(source) = event.lineage.received_from else {
                continue;
            };
            let contact = self.junction_contact(at)?.expect("linked contact");
            let birth = if at == 0 {
                &zero
            } else {
                &trace[at - 1].potential_prefix
            };
            let current = contact
                .iter()
                .zip(now.iter().zip(birth))
                .fold(ExactComplexWaveCurrent::zero(), |sum, (d, (p, p0))| {
                    sum.add(&d.conjugate().multiply(&p.subtract(p0)))
                })
                .scaled(&sign);
            values.push(NativeFieldInternalCurrent {
                source_occurrence: source,
                receiving_occurrence: at,
                contact,
                current,
            });
        }
        Ok(values)
    }
}
