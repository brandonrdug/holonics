//! Occurrence-specific placement through the existing ring carry law.
//!
//! Desired residues of a prefix of rings (for example x,y) determine nonnegative modular
//! advances; the other rings receive only the carry. Every exact opening/arrival lift is retained.
//! This is a declared placement, not inferred key location or a spatial invariance quotient.
//! Its formal integration with the source moment and CUDA scan remains an obligation of #62.

use super::{EncodingError, chart_refusal};
use crate::hnn::field::{Current, Field};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OccurrencePlacement {
    periods: Vec<u64>,
    opening: Vec<BigInt>,
    advances: Vec<Vec<u64>>,
    arrivals: Vec<Vec<BigInt>>,
}

impl OccurrencePlacement {
    /// Concatenate the actual one-cell placements of an observed crib, inserting
    /// each unplaced cell's declared selective step at its original opening.
    /// Each supplied placement must already start at the predecessor's arrival;
    /// no position or rotor digit is inferred from a later observation.
    pub fn observed_crib(
        field: &Field,
        opening: &Current,
        cells: &[(usize, Option<OccurrencePlacement>)],
    ) -> Result<Self, EncodingError> {
        let periods: Vec<u64> = field.rings().iter().map(|ring| ring.period()).collect();
        let mut lift = opening.lift().to_vec();
        let mut advances = Vec::with_capacity(cells.len());
        let mut arrivals = Vec::with_capacity(cells.len());
        for (class, placement) in cells {
            let digits = match placement {
                Some(placement) => {
                    if placement.len() != 1
                        || placement.periods != periods
                        || placement.opening != lift
                    {
                        return Err(chart_refusal(
                            "the crib placement does not open at its original occurrence",
                        ));
                    }
                    placement.advances[0].clone()
                }
                None => (0..periods.len())
                    .map(|g| field.advance_of(g, *class, None))
                    .collect(),
            };
            field.step_class(&mut lift, *class, Some(&digits))?;
            if let Some(placement) = placement {
                if placement.arrivals[0] != lift {
                    return Err(chart_refusal(
                        "the crib placement does not arrive at its original occurrence",
                    ));
                }
            }
            advances.push(digits);
            arrivals.push(lift.clone());
        }
        Ok(Self {
            periods,
            opening: opening.lift().to_vec(),
            advances,
            arrivals,
        })
    }
    /// Place each occurrence at the declared first-k ring residues, retaining all windings.
    /// A repeated identical class can reach a different site: placement belongs to occurrence.
    pub fn at(
        field: &Field,
        current: &Current,
        positions: &[Vec<u64>],
    ) -> Result<Self, EncodingError> {
        field.admit_lock_route()?;
        let periods: Vec<_> = field.rings().iter().map(|ring| ring.period()).collect();
        let opening = current.lift().to_vec();
        if opening.len() != periods.len() || opening.iter().any(|n| n < &BigInt::zero()) {
            return Err(chart_refusal(
                "a placement opens on the field's nonnegative exact lift",
            ));
        }
        let dimensions = positions.first().map_or(0, Vec::len);
        if !positions.is_empty() && (dimensions == 0 || dimensions > periods.len()) {
            return Err(chart_refusal(
                "a placement names a nonempty prefix of the ring frame",
            ));
        }
        let mut lift = opening.clone();
        let mut advances = Vec::with_capacity(positions.len());
        let mut arrivals = Vec::with_capacity(positions.len());
        for position in positions {
            if position.len() != dimensions || position.iter().zip(&periods).any(|(&p, &d)| p >= d)
            {
                return Err(chart_refusal(
                    "a placed coordinate lies outside its declared ring frame",
                ));
            }
            let mut carry = 0u64;
            let mut digits = Vec::with_capacity(periods.len());
            for (g, &period) in periods.iter().enumerate() {
                let phase = (&lift[g] % BigInt::from(period))
                    .to_u64()
                    .ok_or_else(|| chart_refusal("a placement phase is outside its ring"))?;
                let digit = if g < dimensions {
                    // Use widened arithmetic, including period=u64::MAX.
                    ((u128::from(position[g]) + u128::from(period)
                        - ((u128::from(phase) + u128::from(carry)) % u128::from(period)))
                        % u128::from(period)) as u64
                } else {
                    0
                };
                let ticks = u128::from(digit) + u128::from(carry);
                carry = ((u128::from(phase) + ticks) / u128::from(period)) as u64;
                lift[g] += BigInt::from(ticks);
                digits.push(digit);
            }
            advances.push(digits);
            arrivals.push(lift.clone());
        }
        Ok(Self {
            periods,
            opening,
            advances,
            arrivals,
        })
    }
    pub fn periods(&self) -> &[u64] {
        &self.periods
    }
    pub fn opening(&self) -> &[BigInt] {
        &self.opening
    }
    pub fn arrivals(&self) -> &[Vec<BigInt>] {
        &self.arrivals
    }
    pub fn len(&self) -> usize {
        self.advances.len()
    }
    pub fn is_empty(&self) -> bool {
        self.advances.is_empty()
    }
    pub fn advance(&self, at: usize) -> Option<&[u64]> {
        self.advances.get(at).map(Vec::as_slice)
    }
    pub fn part(&self, range: std::ops::Range<usize>) -> Result<Self, EncodingError> {
        let advances = self
            .advances
            .get(range.clone())
            .ok_or_else(|| chart_refusal("placement slice is outside its passage"))?;
        let opening = if range.start == 0 {
            self.opening.clone()
        } else {
            self.arrivals[range.start - 1].clone()
        };
        Ok(Self {
            periods: self.periods.clone(),
            opening,
            advances: advances.to_vec(),
            arrivals: self.arrivals[range].to_vec(),
        })
    }
    pub(crate) fn check_step(
        &self,
        at: usize,
        before: &[BigInt],
        after: &[BigInt],
    ) -> Result<(), EncodingError> {
        let expected_before = if at == 0 {
            &self.opening
        } else {
            self.arrivals
                .get(at - 1)
                .ok_or_else(|| chart_refusal("placement occurrence is outside its passage"))?
        };
        let expected_after = self
            .arrivals
            .get(at)
            .ok_or_else(|| chart_refusal("placement occurrence is outside its passage"))?;
        if before != expected_before || after != expected_after {
            return Err(chart_refusal(
                "the placed occurrence was consumed at another lift or lost its carry",
            ));
        }
        Ok(())
    }
}
