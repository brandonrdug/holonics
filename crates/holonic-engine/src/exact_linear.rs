//! Shared exact rational linear operators.
//!
//! Several physical laws need a finite linear solve, but the solve is not
//! their ontology.  This module owns the bounded exact carrier so diffusion,
//! inverse transport, conservative advection, and later laws need not each
//! invent another unchecked `Vec<Vec<Rat>>` implementation.  Construction may
//! use dense elimination; a continuing law should retain the resulting
//! operator or factorization rather than solve it again on every event.
//!
//! # The four laws that bypassed this carrier, and what the bypass cost
//!
//! The paragraph above named its consumers on the day it was written and none of them arrived.
//! Measured 2026-08-15: `diffusion`, `sheaf_diffusion`, `inverse_transport` and
//! `generative_transport` — the exact modules named — each carried a private `invert_exact`,
//! and `inverse_transport`'s and `generative_transport`'s twenty-eight-line bodies differed
//! by **one line**, the error variant. Two things were lost by re-invention rather than by
//! decision:
//!
//! - **`inverse` verifies itself; none of the four functions did, and their callers each wrote
//!   the check again.** This is the sharper half and it is worth stating exactly, because the
//!   loose form — *"none of the four checked its inverse"* — is false of the modules. Every one
//!   of the six call sites re-derived an identity residual by hand *downstream* of the
//!   operation, in five different vocabularies (`TransferCertificateFailure` twice,
//!   `InverseCertificateFailure`, `InverseResidualNonzero`). **The exception is the one that
//!   matters**: `generative_transport::propagate` checks only `A x - b` for the single
//!   right-hand side it happened to solve, which verifies the inverse against one vector rather
//!   than against the identity. Moving the check inside the operation makes it unconditional —
//!   a caller cannot forget it, and cannot substitute a weaker one.
//!
//!   What the certificate guards is the *elimination*, not the material: over `Rat` a completed
//!   Gauss–Jordan is exact, so it cannot fire while the elimination is correct. That is what it
//!   is for, and stating otherwise would claim a material property this carrier does not have.
//!   The modules' own retained residuals are **not** made redundant by it and are untouched:
//!   they travel in a serialized certificate for a later reader, where this refuses at the point
//!   of construction.
//! - **`diffusion` and `sheaf_diffusion` inverted in `O(n^4)`.** Both built the inverse one
//!   column at a time, re-running a full `O(n^3)` forward solve per column, where the augmented
//!   elimination below runs once.
//!
//! `to_rows` exists so a law whose own signatures and serialized certificates speak
//! `Vec<Vec<Rat>>` can route its algebra through this carrier without changing either.

use std::ops::Range;

use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactRatMatrix {
    rows: usize,
    columns: usize,
    entries: Vec<Rat>,
}

impl ExactRatMatrix {
    pub fn new(entries: Vec<Vec<Rat>>) -> Result<Self, ExactLinearError> {
        let rows = entries.len();
        let columns = entries.first().map_or(0, Vec::len);
        if entries.iter().any(|row| row.len() != columns) {
            return Err(ExactLinearError::RaggedMatrix);
        }
        Ok(Self {
            rows,
            columns,
            entries: entries.into_iter().flatten().collect(),
        })
    }

    /// Construct from dense rows against a **declared** shape.
    ///
    /// `new` infers the column count from the first row, and a matrix with no rows therefore
    /// loses it: an `0 x m` operator and an `0 x 0` operator are the same `Vec<Vec<Rat>>`. That
    /// is not a nuisance — it is a real degeneracy the diffusion laws reach whenever a boundary
    /// or an interior population is empty, and inferring there would silently turn a lawful
    /// empty product into a shape refusal. A caller that knows its shape declares it here.
    pub fn shaped(
        rows: usize,
        columns: usize,
        entries: Vec<Vec<Rat>>,
    ) -> Result<Self, ExactLinearError> {
        if entries.len() != rows || entries.iter().any(|row| row.len() != columns) {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let extent = rows
            .checked_mul(columns)
            .ok_or(ExactLinearError::ExtentOverflow)?;
        let flattened: Vec<Rat> = entries.into_iter().flatten().collect();
        debug_assert_eq!(flattened.len(), extent);
        Ok(Self {
            rows,
            columns,
            entries: flattened,
        })
    }

    pub fn zero(rows: usize, columns: usize) -> Result<Self, ExactLinearError> {
        let extent = rows
            .checked_mul(columns)
            .ok_or(ExactLinearError::ExtentOverflow)?;
        Ok(Self {
            rows,
            columns,
            entries: vec![Rat::zero(); extent],
        })
    }

    pub fn identity(extent: usize) -> Result<Self, ExactLinearError> {
        let mut result = Self::zero(extent, extent)?;
        for ordinal in 0..extent {
            result.set(ordinal, ordinal, Rat::one())?;
        }
        Ok(result)
    }

    pub fn from_diagonal(diagonal: Vec<Rat>) -> Result<Self, ExactLinearError> {
        let mut result = Self::zero(diagonal.len(), diagonal.len())?;
        for (ordinal, value) in diagonal.into_iter().enumerate() {
            result.set(ordinal, ordinal, value)?;
        }
        Ok(result)
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn columns(&self) -> usize {
        self.columns
    }

    pub fn is_square(&self) -> bool {
        self.rows == self.columns
    }

    pub fn get(&self, row: usize, column: usize) -> Result<&Rat, ExactLinearError> {
        let address = self.address(row, column)?;
        Ok(&self.entries[address])
    }

    pub fn row(&self, row: usize) -> Result<&[Rat], ExactLinearError> {
        if row >= self.rows {
            return Err(ExactLinearError::AddressOutside);
        }
        let start = row
            .checked_mul(self.columns)
            .ok_or(ExactLinearError::ExtentOverflow)?;
        Ok(&self.entries[start..start + self.columns])
    }

    pub fn entries(&self) -> &[Rat] {
        &self.entries
    }

    /// The entries as dense rows — the shape the physical laws' own signatures and serialized
    /// certificates speak in.
    ///
    /// This is a presentation of the same operator and not a second carrier: it round-trips
    /// through `new` exactly, including the degenerate `0 x 0` case, which is what lets a law
    /// route one operation through this module without moving its public types.
    pub fn to_rows(&self) -> Vec<Vec<Rat>> {
        (0..self.rows)
            .map(|row| {
                let Range { start, end } = self.span(row);
                self.entries[start..end].to_vec()
            })
            .collect()
    }

    fn span(&self, row: usize) -> Range<usize> {
        let start = row * self.columns;
        start..start + self.columns
    }

    pub fn transpose(&self) -> Result<Self, ExactLinearError> {
        let mut result = Self::zero(self.columns, self.rows)?;
        for row in 0..self.rows {
            for column in 0..self.columns {
                result.set(column, row, self.get(row, column)?.clone())?;
            }
        }
        Ok(result)
    }

    pub fn scaled(&self, coefficient: &Rat) -> Self {
        Self {
            rows: self.rows,
            columns: self.columns,
            entries: self
                .entries
                .iter()
                .map(|entry| coefficient * entry)
                .collect(),
        }
    }

    pub fn add(&self, other: &Self) -> Result<Self, ExactLinearError> {
        self.zip(other, |left, right| left + right)
    }

    pub fn subtract(&self, other: &Self) -> Result<Self, ExactLinearError> {
        self.zip(other, |left, right| left - right)
    }

    pub fn multiply(&self, other: &Self) -> Result<Self, ExactLinearError> {
        Ok(self.multiply_with_work(other)?.0)
    }

    /// **The same product, returning what it cost.**
    ///
    /// Added 2026-08-17 because an adjudication observed that a timing of `A† W A` followed by an
    /// elimination *"is not isolated Gaussian elimination"* — the product and the reduction share the
    /// interval, and a clock cannot separate them. Counted, they separate exactly.
    ///
    /// A product's **dependency span is one**: every output entry is independent of every other, so
    /// the whole deed is one step however many operations it performs. An elimination's span is its
    /// pivot count. That single coordinate is the difference between a deed a card could carry and a
    /// deed it could not, and no scalar cost carries it.
    pub fn multiply_with_work(
        &self,
        other: &Self,
    ) -> Result<(Self, crate::exact_work::ExactWork), ExactLinearError> {
        if self.columns != other.rows {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut work = crate::exact_work::ExactWork::nothing();
        work.resident(u64::try_from(self.rows.saturating_mul(other.columns)).unwrap_or(u64::MAX));
        work.stepped();
        let mut result = Self::zero(self.rows, other.columns)?;
        for row in 0..self.rows {
            for column in 0..other.columns {
                let mut value = Rat::zero();
                for inner in 0..self.columns {
                    value += self.get(row, inner)? * other.get(inner, column)?;
                    work.multiplied(1);
                    work.added(1);
                }
                work.wrote(&value);
                result.set(row, column, value)?;
            }
        }
        Ok((result, work))
    }

    pub fn apply(&self, vector: &[Rat]) -> Result<Vec<Rat>, ExactLinearError> {
        if self.columns != vector.len() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut result = Vec::with_capacity(self.rows);
        for row in 0..self.rows {
            let value = self
                .row(row)?
                .iter()
                .zip(vector)
                .fold(Rat::zero(), |sum, (coefficient, value)| {
                    sum + coefficient * value
                });
            result.push(value);
        }
        Ok(result)
    }

    pub fn inverse(&self) -> Result<Self, ExactLinearError> {
        if !self.is_square() {
            return Err(ExactLinearError::NonsquareMatrix);
        }
        let extent = self.rows;
        let mut left = (0..extent)
            .map(|row| self.row(row).map(ToOwned::to_owned))
            .collect::<Result<Vec<_>, _>>()?;
        let mut right = (0..extent)
            .map(|row| {
                (0..extent)
                    .map(|column| {
                        if row == column {
                            Rat::one()
                        } else {
                            Rat::zero()
                        }
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        for column in 0..extent {
            let pivot = (column..extent)
                .find(|row| !left[*row][column].is_zero())
                .ok_or(ExactLinearError::SingularMatrix)?;
            if pivot != column {
                left.swap(pivot, column);
                right.swap(pivot, column);
            }
            let divisor = left[column][column].clone();
            for entry in &mut left[column] {
                *entry /= &divisor;
            }
            for entry in &mut right[column] {
                *entry /= &divisor;
            }
            let pivot_left = left[column].clone();
            let pivot_right = right[column].clone();
            for row in 0..extent {
                if row == column || left[row][column].is_zero() {
                    continue;
                }
                let factor = left[row][column].clone();
                for (entry, pivot_entry) in left[row].iter_mut().zip(&pivot_left) {
                    *entry -= &factor * pivot_entry;
                }
                for (entry, pivot_entry) in right[row].iter_mut().zip(&pivot_right) {
                    *entry -= &factor * pivot_entry;
                }
            }
        }
        let inverse = Self::new(right)?;
        let identity = Self::identity(extent)?;
        if self.multiply(&inverse)? != identity || inverse.multiply(self)? != identity {
            return Err(ExactLinearError::InverseCertificateFailure);
        }
        Ok(inverse)
    }

    fn zip(
        &self,
        other: &Self,
        operation: impl Fn(&Rat, &Rat) -> Rat,
    ) -> Result<Self, ExactLinearError> {
        if self.rows != other.rows || self.columns != other.columns {
            return Err(ExactLinearError::ShapeMismatch);
        }
        Ok(Self {
            rows: self.rows,
            columns: self.columns,
            entries: self
                .entries
                .iter()
                .zip(&other.entries)
                .map(|(left, right)| operation(left, right))
                .collect(),
        })
    }

    fn set(&mut self, row: usize, column: usize, value: Rat) -> Result<(), ExactLinearError> {
        let address = self.address(row, column)?;
        self.entries[address] = value;
        Ok(())
    }

    fn address(&self, row: usize, column: usize) -> Result<usize, ExactLinearError> {
        if row >= self.rows || column >= self.columns {
            return Err(ExactLinearError::AddressOutside);
        }
        row.checked_mul(self.columns)
            .and_then(|base| base.checked_add(column))
            .ok_or(ExactLinearError::ExtentOverflow)
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactLinearError {
    #[error("an exact matrix cannot have ragged rows")]
    RaggedMatrix,
    #[error("an exact matrix address lies outside its shape")]
    AddressOutside,
    #[error("the exact matrix extent overflowed its physical carrier")]
    ExtentOverflow,
    #[error("the exact linear operator shapes do not compose")]
    ShapeMismatch,
    #[error("only a square exact matrix can be inverted")]
    NonsquareMatrix,
    #[error("the exact linear operator is singular")]
    SingularMatrix,
    #[error("the exact inverse failed its multiplication certificate")]
    InverseCertificateFailure,
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;

    use super::*;

    #[test]
    fn exact_inverse_returns_identity_without_tolerance() {
        let matrix = ExactRatMatrix::new(vec![
            vec![Rat::from_integer(2.into()), Rat::one()],
            vec![Rat::one(), Rat::from_integer(2.into())],
        ])
        .unwrap();
        let inverse = matrix.inverse().unwrap();
        assert_eq!(
            inverse,
            ExactRatMatrix::new(vec![
                vec![
                    Rat::new(BigInt::from(2), BigInt::from(3)),
                    Rat::new(BigInt::from(-1), BigInt::from(3)),
                ],
                vec![
                    Rat::new(BigInt::from(-1), BigInt::from(3)),
                    Rat::new(BigInt::from(2), BigInt::from(3)),
                ],
            ])
            .unwrap()
        );
        assert_eq!(
            matrix.multiply(&inverse).unwrap(),
            ExactRatMatrix::identity(2).unwrap()
        );
        assert_eq!(
            inverse.multiply(&matrix).unwrap(),
            ExactRatMatrix::identity(2).unwrap()
        );
    }

    /// The dense-row presentation must round-trip, or a law routed through this carrier would
    /// return a different operator than the one it handed over. The degenerate and the
    /// rectangular shapes are both included because the four laws that now route through here
    /// reach both: an empty interior gives `0 x 0`, and a boundary/interior section gives
    /// `n x m`.
    #[test]
    fn the_dense_row_presentation_round_trips_at_every_shape_the_laws_reach() {
        let shapes = [
            Vec::new(),
            vec![vec![Rat::zero(); 0]; 3],
            vec![vec![Rat::one(), Rat::from_integer(2.into())]],
            vec![
                vec![Rat::one(), Rat::from_integer(2.into())],
                vec![Rat::from_integer(3.into()), Rat::from_integer(4.into())],
                vec![Rat::from_integer(5.into()), Rat::from_integer(6.into())],
            ],
        ];
        for rows in shapes {
            let carrier = ExactRatMatrix::new(rows.clone()).unwrap();
            assert_eq!(carrier.to_rows(), rows);
            assert_eq!(ExactRatMatrix::new(carrier.to_rows()).unwrap(), carrier);
        }
    }

    /// A singular operator refuses by name rather than returning an unchecked inverse. This is
    /// the one refusal of `inverse` the material can actually cause; the certificate below it
    /// guards the elimination and cannot fire while the elimination is correct, which the doc
    /// says rather than claiming otherwise.
    #[test]
    fn a_singular_operator_refuses_and_the_refusal_is_named() {
        let singular = ExactRatMatrix::new(vec![
            vec![Rat::one(), Rat::from_integer(2.into())],
            vec![Rat::from_integer(2.into()), Rat::from_integer(4.into())],
        ])
        .unwrap();
        assert_eq!(singular.inverse(), Err(ExactLinearError::SingularMatrix));
        assert_eq!(
            ExactRatMatrix::new(vec![vec![Rat::one(), Rat::zero()]])
                .unwrap()
                .inverse(),
            Err(ExactLinearError::NonsquareMatrix)
        );
    }
}
