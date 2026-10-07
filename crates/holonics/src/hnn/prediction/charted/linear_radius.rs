//! Exact contact coefficient faces shared within one producing Word (Refs #73 #62).
//!
//! For the existing linear contact map L and nonnegative component radius e, the consumer
//! remains |L|e. A coefficient column is located by the same native map on its unit input
//! once, then reused only under these borrowed immutable producing operands. No point,
//! target, covector, source response or occurrence state is retained here. Material, step,
//! selection and the executed solve belong to that borrow; a new Word builds a fresh face.

use crate::hnn::HnnError;
use crate::hnn::propagation::Operands;
use crate::ratio::Rat;
use num_traits::{One, Signed, Zero};

struct RadiusColumns {
    shape: Vec<usize>,
    output: usize,
    columns: Vec<Option<Vec<Rat>>>,
}

impl RadiusColumns {
    fn new(shape: Vec<usize>, output: usize) -> Self {
        let columns = vec![None; shape.iter().sum()];
        Self {
            shape,
            output,
            columns,
        }
    }

    fn apply(
        &mut self,
        inputs: &[&[Rat]],
        map: impl Fn(&[Vec<Rat>]) -> Result<Vec<Rat>, HnnError>,
    ) -> Result<Vec<Rat>, HnnError> {
        if inputs.len() != self.shape.len()
            || inputs.iter().zip(&self.shape).any(|(x, n)| x.len() != *n)
        {
            return Err(HnnError::Unadmitted {
                reason: "the contact radius face has another producing input shape",
            });
        }
        let mut basis: Vec<_> = self.shape.iter().map(|&n| vec![Rat::zero(); n]).collect();
        let mut image = vec![Rat::zero(); self.output];
        let mut offset = 0;
        for (part, radius) in inputs.iter().enumerate() {
            for (coordinate, value) in radius.iter().enumerate().filter(|(_, x)| !x.is_zero()) {
                let slot = offset + coordinate;
                if self.columns[slot].is_none() {
                    basis[part][coordinate] = Rat::one();
                    let column = map(&basis)?;
                    basis[part][coordinate] = Rat::zero();
                    if column.len() != self.output {
                        return Err(HnnError::Unadmitted {
                            reason: "the contact radius face has another producing output shape",
                        });
                    }
                    self.columns[slot] =
                        Some(column.into_iter().map(|value| value.abs()).collect());
                }
                for (image, coefficient) in
                    image.iter_mut().zip(self.columns[slot].as_ref().unwrap())
                {
                    *image += value * coefficient;
                }
            }
            offset += radius.len();
        }
        Ok(image)
    }
}

/// Word-local contact maps, bound to the same producing operands as every error tick.
/// Lazy columns preserve the old map's zero-radius behaviour and typed coefficient failures.
pub(super) struct ContactRadiusMaps<'o> {
    pub(super) operands: &'o Operands,
    right: Vec<RadiusColumns>,
    update: Vec<RadiusColumns>,
}

impl<'o> ContactRadiusMaps<'o> {
    pub(super) fn new(operands: &'o Operands) -> Self {
        let mut right = Vec::new();
        let mut update = Vec::new();
        for contact in operands.contacts() {
            let (from, to) = contact.ends();
            let n0 = operands.rings()[from].width();
            let n1 = operands.rings()[to].width();
            let n = contact.width();
            right.push(RadiusColumns::new(vec![n0, n1, n, n], n));
            update.push(RadiusColumns::new(vec![n, n0, n1, n, n], n0 + n1 + 2 * n));
        }
        Self {
            operands,
            right,
            update,
        }
    }

    pub(super) fn right(
        &mut self,
        contact: usize,
        inputs: &[&[Rat]],
    ) -> Result<Vec<Rat>, HnnError> {
        let c = &self.operands.contacts()[contact];
        let h = self.operands.step();
        self.right[contact].apply(inputs, |b| {
            Ok(crate::hnn::propagation::transit_solve(c, h, &b[0], &b[1], &b[2], &b[3])?.0)
        })
    }

    pub(super) fn update(
        &mut self,
        contact: usize,
        inputs: &[&[Rat]],
    ) -> Result<Vec<Rat>, HnnError> {
        let c = &self.operands.contacts()[contact];
        let h = self.operands.step();
        self.update[contact].apply(inputs, |b| {
            let p =
                crate::hnn::propagation::transit_update(c, h, &b[0], &b[1], &b[2], &b[3], &b[4]);
            Ok([p.arrive_from, p.arrive_to, p.displacement, p.rate].concat())
        })
    }

    #[cfg(test)]
    pub(super) fn located_columns(&self) -> usize {
        self.right
            .iter()
            .chain(&self.update)
            .map(|face| {
                face.columns
                    .iter()
                    .filter(|column| column.is_some())
                    .count()
            })
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::integer;
    use std::cell::Cell;

    #[test]
    fn lazy_radius_columns_preserve_exact_images_zero_work_and_typed_shape_refusal() {
        let builds = Cell::new(0usize);
        let raw = |b: &[Vec<Rat>]| Ok(vec![&b[0][0] - &b[1][0], integer(2) * &b[0][1] + &b[1][0]]);
        let map = |b: &[Vec<Rat>]| {
            builds.set(builds.get() + 1);
            raw(b)
        };
        let mut face = RadiusColumns::new(vec![2, 1], 2);
        let zero = vec![integer(0); 2];
        let tail_zero = vec![integer(0)];
        assert_eq!(face.apply(&[&zero, &tail_zero], &map).unwrap(), zero);
        assert_eq!(builds.get(), 0);
        for (left, right) in [([1, 2], 3), ([3, 1], 2), ([0, 4], 0)] {
            let left = left.map(integer);
            let right = [integer(right)];
            let expected =
                crate::hnn::prediction::physical_linear_radius(&[&left, &right], 2, &raw).unwrap();
            assert_eq!(face.apply(&[&left, &right], &map).unwrap(), expected);
            assert_eq!(
                builds.get(),
                3,
                "the same three located columns serve every new radius"
            );
        }
        assert!(face.apply(&[&zero], &map).is_err());
        assert!(face.apply(&[&tail_zero, &tail_zero], &map).is_err());
    }
}
