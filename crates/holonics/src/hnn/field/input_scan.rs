//! Input-selected translation prefixes for the field's actual selective clock.
//!
//! [agent-inferred, A2] Before carries, a cell's map is `tau -> tau + c_g(cell)`.
//! These affine maps have identity linear part and compose by exact integer addition.
//! After their prefix scan, ring g's cumulative carry is
//! `floor((tau_g + prefix_g + carry_in)/d_g) - floor(tau_g/d_g)`.
//! Rings stay in carry order. Own rings advance once and pass the preceding carry
//! unchanged, exactly as `Field::step_class`; no lock, chart or word is scanned here.
//! Full occurrence squares are checked by the consuming `SourceMoment::scan_epoch`.
//! Lean owns the step/carry law in HNN/Moment; its equivalence to this cumulative
//! realization remains owed in #62. Native tests compare every consumed prefix.

use super::*;
use rayon::prelude::*;
use std::ops::Range;

impl Field {
    pub(crate) fn scan_input_selected(
        &self,
        opening: &[BigInt],
        encoded: &Encoded,
        range: Range<usize>,
        partitions: usize,
    ) -> Result<Vec<(Vec<BigInt>, SelectiveStep)>, HnnError> {
        if partitions == 0 || range.start > range.end || range.end > encoded.len() {
            return Err(HnnError::Unadmitted {
                reason: "an input prefix needs a nonzero partition and a range within its encoding",
            });
        }
        if opening.len() != self.rings.len() {
            return Err(HnnError::Shape {
                what: "input prefix opening lift",
                expected: self.rings.len(),
                found: opening.len(),
            });
        }
        for (ring, tau) in self.rings.iter().zip(opening) {
            ring.clock_at(tau)?;
        }
        let mut result = vec![
            (
                opening.to_vec(),
                SelectiveStep {
                    ticks: vec![0; self.rings.len()],
                    carry_out: false,
                }
            );
            range.len()
        ];
        let mut carry = vec![BigInt::zero(); range.len()];
        for (g, ring) in self.rings.iter().enumerate() {
            let selected = range
                .clone()
                .map(|at| {
                    BigInt::from(self.advance_of(
                        g,
                        encoded.cells()[at].class(),
                        encoded.advance(at),
                    ))
                })
                .collect::<Vec<_>>();
            let prefix = translation_prefix(&selected, partitions);
            let winding = &opening[g] / BigInt::from(ring.period());
            let mut previous = opening[g].clone();
            for (at, ((lift, step), selected_prefix)) in result.iter_mut().zip(prefix).enumerate() {
                lift[g] = &opening[g] + selected_prefix;
                if ring.advance != RingAdvance::Own {
                    lift[g] += &carry[at];
                    carry[at] = &lift[g] / BigInt::from(ring.period()) - &winding;
                }
                step.ticks[g] = (&lift[g] - &previous)
                    .to_u64()
                    .ok_or(HnnError::CountOverflow)?;
                previous = lift[g].clone();
            }
        }
        let mut previous = BigInt::zero();
        for ((_, step), cumulative) in result.iter_mut().zip(carry) {
            let crossing = &cumulative - &previous;
            if crossing != BigInt::zero() && crossing != BigInt::one() {
                return Err(HnnError::Unadmitted {
                    reason: "one selective occurrence crosses at most one joint section",
                });
            }
            step.carry_out = crossing == BigInt::one();
            previous = cumulative;
        }
        Ok(result)
    }
}

/// Inclusive composition of the identity-linear affine maps `x -> x + input[i]`.
/// Local prefixes run on disjoint lanes. Lane totals use a Hillis--Steele prefix,
/// then each lane is translated by its predecessor total. BigInt never wraps.
fn translation_prefix(input: &[BigInt], partitions: usize) -> Vec<BigInt> {
    if input.is_empty() {
        return Vec::new();
    }
    let chunk = input.len().div_ceil(partitions.min(input.len()));
    let mut lanes = input
        .par_chunks(chunk)
        .map(|lane| {
            let mut sum = BigInt::zero();
            lane.iter()
                .map(|value| {
                    sum += value;
                    sum.clone()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut totals = lanes
        .iter()
        .map(|lane| lane.last().expect("nonempty lane").clone())
        .collect::<Vec<_>>();
    let mut reach = 1;
    while reach < totals.len() {
        let previous = &totals;
        totals = previous
            .par_iter()
            .enumerate()
            .map(|(at, value)| {
                if at >= reach {
                    &previous[at - reach] + value
                } else {
                    value.clone()
                }
            })
            .collect();
        reach = reach.saturating_mul(2);
    }
    lanes.par_iter_mut().enumerate().for_each(|(at, lane)| {
        if at != 0 {
            for value in lane {
                *value += &totals[at - 1];
            }
        }
    });
    lanes.into_iter().flatten().collect()
}
