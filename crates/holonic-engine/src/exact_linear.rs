//! Shared exact rational linear operators.
//!
//! Several physical laws need a finite linear solve, but the solve is not
//! their ontology.  This module owns the bounded exact carrier so diffusion,
//! inverse transport, conservative advection, and later laws need not each
//! invent another unchecked `Vec<Vec<Rat>>` implementation.  Construction may
//! use dense elimination; a continuing law should retain the resulting
//! operator or factorization rather than solve it again on every event.

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
        if self.columns != other.rows {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut result = Self::zero(self.rows, other.columns)?;
        for row in 0..self.rows {
            for column in 0..other.columns {
                let mut value = Rat::zero();
                for inner in 0..self.columns {
                    value += self.get(row, inner)? * other.get(inner, column)?;
                }
                result.set(row, column, value)?;
            }
        }
        Ok(result)
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
        if self.multiply(&inverse)? != Self::identity(extent)? {
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
    }
}
