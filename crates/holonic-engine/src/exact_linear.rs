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

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

mod bilinear;
mod joint_bilinear;
mod kernel_modes;
pub use joint_bilinear::{JointBilinearFibre, JointBilinearSystem, JointPreimageReduction};
pub use kernel_modes::{KernelModeAction, KernelModeError, KernelModeReduction, KernelModeSummary};
mod contextual;
pub use bilinear::{
    BilinearOperator, BilinearProductCore, BilinearRealization, BilinearSupportReturn,
    BilinearSupportSearch,
};
pub use contextual::{
    ContextualFactorization, ContextualObstruction, ExactContextualLift, LinearMapFamily,
    ReceiverFactorization,
};

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
        if self.entries.iter().all(|entry| entry.denom().is_one()) {
            return self.inverse_integral_fraction_free();
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

    /// Fraction-free Gauss--Jordan (Montante/Bareiss) for an integral presentation.  The
    /// augmented word remains in `BigInt` until its terminal diagonal is reached, so a large
    /// common physical scale cannot trigger rational normalization at every intermediate pivot.
    /// The returned inverse is still checked in both directions against the original operator.
    fn inverse_integral_fraction_free(&self) -> Result<Self, ExactLinearError> {
        let extent = self.rows;
        if extent == 0 {
            return Self::identity(0);
        }
        let width = extent
            .checked_mul(2)
            .ok_or(ExactLinearError::ExtentOverflow)?;
        let mut augmented = Vec::with_capacity(extent);
        for row in 0..extent {
            let mut values = Vec::with_capacity(width);
            for column in 0..extent {
                values.push(self.get(row, column)?.numer().clone());
            }
            values.extend((0..extent).map(|column| {
                if row == column {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }
            }));
            augmented.push(values);
        }

        let mut previous_pivot = BigInt::one();
        for pivot_at in 0..extent {
            let pivot_row = (pivot_at..extent)
                .find(|row| !augmented[*row][pivot_at].is_zero())
                .ok_or(ExactLinearError::SingularMatrix)?;
            if pivot_row != pivot_at {
                augmented.swap(pivot_row, pivot_at);
            }
            let pivot = augmented[pivot_at][pivot_at].clone();
            if pivot.is_zero() {
                return Err(ExactLinearError::SingularMatrix);
            }
            let pivot_row_values = augmented[pivot_at].clone();
            for row in 0..extent {
                if row == pivot_at {
                    continue;
                }
                let eliminated = augmented[row][pivot_at].clone();
                for column in 0..width {
                    if column == pivot_at {
                        continue;
                    }
                    let numerator =
                        &pivot * &augmented[row][column] - &eliminated * &pivot_row_values[column];
                    if &numerator % &previous_pivot != BigInt::zero() {
                        return Err(ExactLinearError::InverseCertificateFailure);
                    }
                    augmented[row][column] = numerator / &previous_pivot;
                }
                augmented[row][pivot_at] = BigInt::zero();
            }
            previous_pivot = pivot;
        }

        let inverse = Self::new(
            (0..extent)
                .map(|row| {
                    let diagonal = augmented[row][row].clone();
                    if diagonal.is_zero() {
                        return Err(ExactLinearError::SingularMatrix);
                    }
                    Ok((0..extent)
                        .map(|column| {
                            Rat::new(augmented[row][extent + column].clone(), diagonal.clone())
                        })
                        .collect::<Vec<_>>())
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let identity = Self::identity(extent)?;
        if self.multiply(&inverse)? != identity || inverse.multiply(self)? != identity {
            return Err(ExactLinearError::InverseCertificateFailure);
        }
        Ok(inverse)
    }

    // ---------------------------------------------------------------------------------------
    // THE THREE RETURNS A MAP OWES, AND THEY ARE NOT THE SAME RETURN
    // ---------------------------------------------------------------------------------------
    //
    // `research/records/2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_...md` §6 states the law and
    // records these as `open`:
    //
    //     X -> X / ker(T) -> image(T) -> Y
    //          quotient       rebase       inclusion / open cokernel
    //
    // - an **inverse** exists only for a rebase, and only with BOTH identity compositions;
    // - a singular or rectangular map returns **kernel, image, cokernel and an affine preimage
    //   fibre**, and selects no representative;
    // - a **metric adjoint** `G_X^-1 T^T G_Y` is a third object again, and a bare transpose is it
    //   only under undeclared orthonormal Euclidean charts — the smuggling this line refuses.
    //
    // They are added here rather than beside this owner because that is where the factorization of
    // an exact rational operator belongs. Nothing below decides a receiver's purpose; each returns
    // the complete population and lets a declaration do the choosing.

    /// The reduced row echelon form, its pivot columns, and what the reduction cost.
    ///
    /// One primitive under everything below. `inverse` predates it and keeps its own augmented
    /// elimination, so the certificate it already carries is untouched.
    pub fn reduced_row_echelon(
        &self,
    ) -> Result<(Self, Vec<usize>, crate::exact_work::ExactWork), ExactLinearError> {
        let mut work = crate::exact_work::ExactWork::nothing();
        work.resident(u64::try_from(self.rows.saturating_mul(self.columns)).unwrap_or(u64::MAX));
        let mut rows = self.to_rows();
        let mut pivots = Vec::new();
        let mut pivot_row = 0usize;
        for column in 0..self.columns {
            if pivot_row >= self.rows {
                break;
            }
            let Some(found) = (pivot_row..self.rows).find(|row| !rows[*row][column].is_zero())
            else {
                continue;
            };
            rows.swap(found, pivot_row);
            work.stepped();
            let divisor = rows[pivot_row][column].clone();
            for entry in &mut rows[pivot_row] {
                *entry /= &divisor;
                work.divided(1);
            }
            let pivot = rows[pivot_row].clone();
            for row in 0..self.rows {
                if row == pivot_row || rows[row][column].is_zero() {
                    continue;
                }
                let factor = rows[row][column].clone();
                for (entry, above) in rows[row].iter_mut().zip(&pivot) {
                    *entry -= &factor * above;
                    work.multiplied(1);
                    work.added(1);
                }
            }
            pivots.push(column);
            pivot_row += 1;
        }
        for row in &rows {
            for entry in row {
                work.wrote(entry);
            }
        }
        Ok((Self::new(rows)?, pivots, work))
    }

    /// The rank, read off the reduction rather than declared.
    pub fn rank(&self) -> Result<usize, ExactLinearError> {
        Ok(self.reduced_row_echelon()?.1.len())
    }

    /// **A basis of `ker(T)`: the directions this map collapses.**
    ///
    /// One vector per free column, each carrying a single `1` in its own free coordinate, so the
    /// population is exhibited rather than summarized by a count. An empty return is a genuine
    /// zero: the map collapses nothing.
    pub fn kernel_basis(&self) -> Result<Vec<Vec<Rat>>, ExactLinearError> {
        let (reduced, pivots, _) = self.reduced_row_echelon()?;
        let free: Vec<usize> = (0..self.columns)
            .filter(|column| !pivots.contains(column))
            .collect();
        let mut basis = Vec::with_capacity(free.len());
        for column in &free {
            let mut vector = vec![Rat::zero(); self.columns];
            vector[*column] = Rat::one();
            for (row, pivot) in pivots.iter().enumerate() {
                vector[*pivot] = -reduced.get(row, *column)?.clone();
            }
            basis.push(vector);
        }
        Ok(basis)
    }

    /// **A basis of `image(T)`: the pivot columns of the map itself**, not of its reduction.
    pub fn image_basis(&self) -> Result<Vec<Vec<Rat>>, ExactLinearError> {
        let (_, pivots, _) = self.reduced_row_echelon()?;
        let mut basis = Vec::with_capacity(pivots.len());
        for column in pivots {
            basis.push(
                (0..self.rows)
                    .map(|row| self.get(row, column).cloned())
                    .collect::<Result<Vec<_>, _>>()?,
            );
        }
        Ok(basis)
    }

    /// **A basis of the cokernel's annihilator: the covectors that see nothing this map emits.**
    ///
    /// `coker(T) = Y / image(T)`, and what exhibits it exactly is `ker(T^T)` — every covector
    /// vanishing on the image. A nonempty return is the **open exterior** of this transport: a
    /// receiver direction the map cannot reach, named rather than counted.
    pub fn cokernel_annihilator(&self) -> Result<Vec<Vec<Rat>>, ExactLinearError> {
        self.transpose()?.kernel_basis()
    }

    /// **The complete affine preimage of a declared target, and no representative is selected.**
    ///
    /// Returns `Some((particular, kernel_basis))` — the fibre `x_0 + ker(T)` — or `None` with the
    /// inconsistency exhibited by [`Self::preimage_obstruction`]. A caller that wants one point
    /// declares that reading itself.
    pub fn preimage_fibre(
        &self,
        target: &[Rat],
    ) -> Result<Option<(Vec<Rat>, Vec<Vec<Rat>>)>, ExactLinearError> {
        if target.len() != self.rows {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut augmented = self.to_rows();
        for (row, value) in augmented.iter_mut().zip(target) {
            row.push(value.clone());
        }
        let augmented = Self::new(augmented)?;
        let (reduced, pivots, _) = augmented.reduced_row_echelon()?;
        if pivots.last() == Some(&self.columns) {
            // A pivot in the augmented column: the target is outside the image.
            return Ok(None);
        }
        let mut particular = vec![Rat::zero(); self.columns];
        for (row, pivot) in pivots.iter().enumerate() {
            particular[*pivot] = reduced.get(row, self.columns)?.clone();
        }
        Ok(Some((particular, self.kernel_basis()?)))
    }

    /// The covector witnessing that a target lies outside the image, or `None` when it does not.
    ///
    /// **An obstruction is a return.** `w` with `w^T T = 0` and `<w, y> != 0` proves the refusal
    /// rather than asserting it.
    pub fn preimage_obstruction(
        &self,
        target: &[Rat],
    ) -> Result<Option<Vec<Rat>>, ExactLinearError> {
        if target.len() != self.rows {
            return Err(ExactLinearError::ShapeMismatch);
        }
        for covector in self.cokernel_annihilator()? {
            let pairing = covector
                .iter()
                .zip(target)
                .fold(Rat::zero(), |sum, (left, right)| sum + left * right);
            if !pairing.is_zero() {
                return Some(Ok(covector)).transpose();
            }
        }
        Ok(None)
    }

    /// **The complete factorization**, so a caller cannot read one face and forget the others.
    pub fn factorization(&self) -> Result<LinearFactorization, ExactLinearError> {
        let (_, pivots, work) = self.reduced_row_echelon()?;
        Ok(LinearFactorization {
            rows: self.rows,
            columns: self.columns,
            rank: pivots.len(),
            kernel: self.kernel_basis()?,
            image: self.image_basis()?,
            cokernel_annihilator: self.cokernel_annihilator()?,
            work,
        })
    }

    /// The canonical pivot-column rank factorization `T = U V`.
    ///
    /// `U` is formed from the pivot columns of the unreduced operator and `V` is formed from the
    /// nonzero rows of its reduced row-echelon form.  Consequently the factor population is the
    /// exact image rank; no caller supplies a width.  The pivot columns are retained as the gauge
    /// which made this representative canonical.  Rank zero is a lawful `m x 0` followed by
    /// `0 x n` passage, not a fabricated rank-one zero factor.
    pub fn rank_factorization(&self) -> Result<ExactRankFactorization, ExactLinearError> {
        let (reduced, pivot_columns, reduction_work) = self.reduced_row_echelon()?;
        let derived_rank = pivot_columns.len();
        let left = ExactRatMatrix::shaped(
            self.rows,
            derived_rank,
            (0..self.rows)
                .map(|row| {
                    pivot_columns
                        .iter()
                        .map(|column| self.get(row, *column).cloned())
                        .collect::<Result<Vec<_>, _>>()
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let right = ExactRatMatrix::shaped(
            derived_rank,
            self.columns,
            (0..derived_rank)
                .map(|row| reduced.row(row).map(<[Rat]>::to_vec))
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let (reconstruction, reconstruction_work) = left.multiply_with_work(&right)?;
        if reconstruction != *self {
            return Err(ExactLinearError::RankFactorizationCertificateFailure);
        }
        Ok(ExactRankFactorization {
            rows: self.rows,
            columns: self.columns,
            derived_rank,
            pivot_columns,
            left,
            right,
            reconstruction,
            linear: self.factorization()?,
            work: reduction_work.then(&reconstruction_work),
        })
    }

    /// **A rebase receipt, which requires BOTH identity compositions.**
    ///
    /// `TABLET_THE_OPERATIONS`: an inverse exists only for a rebase. A map that is not one refuses
    /// here and returns its factorization instead of a pseudo-inverse nobody declared.
    pub fn rebase_receipt(&self) -> Result<RebaseReceipt, ExactLinearError> {
        if !self.is_square() {
            return Ok(RebaseReceipt::Refused {
                factorization: Box::new(self.factorization()?),
                reason: "a rectangular map has no inverse; it has a factorization",
            });
        }
        match self.inverse() {
            Ok(inverse) => {
                let identity = Self::identity(self.rows)?;
                let forward = self.multiply(&inverse)?;
                let backward = inverse.multiply(self)?;
                if forward != identity || backward != identity {
                    return Err(ExactLinearError::InverseCertificateFailure);
                }
                Ok(RebaseReceipt::Rebase {
                    inverse: Box::new(inverse),
                    forward_identity: true,
                    backward_identity: true,
                })
            }
            Err(ExactLinearError::SingularMatrix) => Ok(RebaseReceipt::Refused {
                factorization: Box::new(self.factorization()?),
                reason: "the map collapses a direction; it is a quotient, not a rebase",
            }),
            Err(other) => Err(other),
        }
    }

    /// **The metric adjoint `G_X^-1 T^T G_Y`**, characterized by `<Tx, y>_Y = <x, T^dagger y>_X`.
    ///
    /// A bare transpose is this object only when both metrics are the identity, which is an
    /// orthonormal Euclidean declaration nobody made. `CLAUDE.md` §13: *the metric is a receiver
    /// face of standing*, so it is a parameter here and never a default.
    pub fn metric_adjoint(
        &self,
        domain_metric: &Self,
        codomain_metric: &Self,
    ) -> Result<Self, ExactLinearError> {
        if domain_metric.rows != self.columns || !domain_metric.is_square() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        if codomain_metric.rows != self.rows || !codomain_metric.is_square() {
            return Err(ExactLinearError::ShapeMismatch);
        }
        domain_metric
            .inverse()?
            .multiply(&self.transpose()?)?
            .multiply(codomain_metric)
    }

    /// The exact defect of a claimed adjoint against its own characterization, over a declared
    /// pair. Zero is the claim; anything else is the obstruction, exhibited.
    pub fn adjoint_defect(
        &self,
        claimed: &Self,
        domain_metric: &Self,
        codomain_metric: &Self,
        x: &[Rat],
        y: &[Rat],
    ) -> Result<Rat, ExactLinearError> {
        let left = {
            let tx = self.apply(x)?;
            let gy = codomain_metric.apply(y)?;
            tx.iter()
                .zip(&gy)
                .fold(Rat::zero(), |sum, (a, b)| sum + a * b)
        };
        let right = {
            let ty = claimed.apply(y)?;
            let gx = domain_metric.apply(x)?;
            gx.iter()
                .zip(&ty)
                .fold(Rat::zero(), |sum, (a, b)| sum + a * b)
        };
        Ok(left - right)
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

/// The complete factorization of an exact rational transport.
///
/// **All four faces at once**, so a caller cannot read the rank and forget that the map collapses
/// something or that its exterior is open.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LinearFactorization {
    pub rows: usize,
    pub columns: usize,
    pub rank: usize,
    /// The collapsed directions, exhibited.
    pub kernel: Vec<Vec<Rat>>,
    /// The reached directions, as columns of the map itself.
    pub image: Vec<Vec<Rat>>,
    /// Covectors that see nothing this map emits: the **open exterior**.
    pub cokernel_annihilator: Vec<Vec<Rat>>,
    pub work: crate::exact_work::ExactWork,
}

/// One exact rank factorization and the gauge and fibres which keep it interpretable.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactRankFactorization {
    pub rows: usize,
    pub columns: usize,
    /// The cardinality of the image basis; never a caller aperture.
    pub derived_rank: usize,
    /// The unreduced source columns chosen by deterministic RREF pivot order.
    pub pivot_columns: Vec<usize>,
    /// `rows x derived_rank` image-basis map.
    pub left: ExactRatMatrix,
    /// `derived_rank x columns` coordinate-functional map.
    pub right: ExactRatMatrix,
    /// The returned exact product, retained rather than summarized by a boolean.
    pub reconstruction: ExactRatMatrix,
    /// Kernel, image, cokernel and their exact dimensions remain attached.
    pub linear: LinearFactorization,
    pub work: crate::exact_work::ExactWork,
}

impl LinearFactorization {
    /// A rebase collapses nothing and leaves nothing unreached.
    pub fn is_rebase(&self) -> bool {
        self.kernel.is_empty() && self.cokernel_annihilator.is_empty() && self.rows == self.columns
    }

    pub fn collapsed_dimension(&self) -> usize {
        self.kernel.len()
    }

    pub fn open_exterior_dimension(&self) -> usize {
        self.cokernel_annihilator.len()
    }
}

/// What a map returns when asked whether it is a rebase.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RebaseReceipt {
    /// **Both identity compositions returned.** That is what makes it a rebase.
    Rebase {
        inverse: Box<ExactRatMatrix>,
        forward_identity: bool,
        backward_identity: bool,
    },
    /// Not a rebase, and the factorization is what it has instead.
    Refused {
        factorization: Box<LinearFactorization>,
        reason: &'static str,
    },
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
    #[error("the exact pivot-column rank factorization failed its multiplication certificate")]
    RankFactorizationCertificateFailure,
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn matrix(rows: &[&[i64]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|row| row.iter().map(|value| rat(*value, 1)).collect())
                .collect(),
        )
        .expect("well-formed")
    }

    /// **A singular map returns its factorization, never an inverse.** The collapsed direction is
    /// exhibited as a vector rather than reported as a rank deficit.
    #[test]
    fn a_singular_map_returns_a_factorization_rather_than_an_inverse() {
        // Columns two and three are dependent, so exactly one direction collapses.
        let singular = matrix(&[&[1, 2, 3], &[2, 4, 6], &[1, 1, 1]]);
        let receipt = singular.rebase_receipt().expect("receipt");
        let RebaseReceipt::Refused { factorization, .. } = receipt else {
            panic!("a singular map must refuse to be a rebase");
        };
        assert_eq!(factorization.rank, 2);
        assert_eq!(factorization.collapsed_dimension(), 1);
        assert_eq!(factorization.open_exterior_dimension(), 1);
        assert!(!factorization.is_rebase());
        // And the collapsed direction really is collapsed: T k = 0, exactly.
        let kernel = &factorization.kernel[0];
        let image = singular.apply(kernel).expect("applies");
        assert!(image.iter().all(Zero::is_zero), "kernel vector {kernel:?}");
        // The open exterior is a covector that sees nothing the map emits.
        let covector = &factorization.cokernel_annihilator[0];
        for column in factorization.image.iter() {
            let pairing = covector
                .iter()
                .zip(column)
                .fold(Rat::zero(), |sum, (a, b)| sum + a * b);
            assert!(
                pairing.is_zero(),
                "the annihilator must annihilate the image"
            );
        }
    }

    /// **A rectangular map has no inverse and says so**, returning the affine preimage fibre for a
    /// reachable target and a witnessing covector for an unreachable one. No representative is
    /// selected in either case.
    #[test]
    fn a_rectangular_map_returns_an_affine_fibre_or_an_exhibited_obstruction() {
        // Two equations, three unknowns: one free direction.
        let wide = matrix(&[&[1, 1, 0], &[0, 1, 1]]);
        assert!(matches!(
            wide.rebase_receipt().expect("receipt"),
            RebaseReceipt::Refused { .. }
        ));
        let target = vec![rat(2, 1), rat(3, 1)];
        let (particular, kernel) = wide
            .preimage_fibre(&target)
            .expect("solved")
            .expect("reachable");
        assert_eq!(wide.apply(&particular).expect("applies"), target);
        assert_eq!(kernel.len(), 1, "one free direction");
        // Every point of the fibre maps to the same target, which is what makes it a fibre.
        let moved: Vec<Rat> = particular
            .iter()
            .zip(&kernel[0])
            .map(|(base, direction)| base + direction * rat(7, 2))
            .collect();
        assert_eq!(wide.apply(&moved).expect("applies"), target);
        assert!(
            wide.preimage_obstruction(&target)
                .expect("checked")
                .is_none(),
            "a reachable target has no obstruction"
        );

        // A tall map whose exterior is genuinely open.
        let tall = matrix(&[&[1, 0], &[0, 1], &[0, 0]]);
        let unreachable = vec![rat(0, 1), rat(0, 1), rat(1, 1)];
        assert!(tall.preimage_fibre(&unreachable).expect("solved").is_none());
        let covector = tall
            .preimage_obstruction(&unreachable)
            .expect("checked")
            .expect("the refusal is witnessed");
        let pairing = covector
            .iter()
            .zip(&unreachable)
            .fold(Rat::zero(), |sum, (a, b)| sum + a * b);
        assert!(!pairing.is_zero(), "the witness must separate the target");
    }

    /// **A rebase returns both identity compositions**, and that is the whole content of the claim.
    #[test]
    fn a_rebase_returns_both_identity_compositions() {
        let rebase = matrix(&[&[2, 1], &[1, 1]]);
        let RebaseReceipt::Rebase {
            inverse,
            forward_identity,
            backward_identity,
        } = rebase.rebase_receipt().expect("receipt")
        else {
            panic!("an invertible map is a rebase");
        };
        assert!(forward_identity && backward_identity);
        let identity = ExactRatMatrix::identity(2).expect("identity");
        assert_eq!(rebase.multiply(&inverse).expect("product"), identity);
        assert_eq!(inverse.multiply(&rebase).expect("product"), identity);
        assert!(rebase.factorization().expect("factored").is_rebase());
    }

    #[test]
    fn pivot_columns_derive_zero_one_and_higher_rank_factor_populations() {
        let zero = ExactRatMatrix::zero(2, 3).expect("zero");
        let zero_factor = zero.rank_factorization().expect("rank-zero return");
        assert_eq!(zero_factor.derived_rank, 0);
        assert_eq!(
            (zero_factor.left.rows(), zero_factor.left.columns()),
            (2, 0)
        );
        assert_eq!(
            (zero_factor.right.rows(), zero_factor.right.columns()),
            (0, 3)
        );
        assert_eq!(zero_factor.reconstruction, zero);

        let rank_one = matrix(&[&[2, 4, 6], &[3, 6, 9]]);
        let one_factor = rank_one.rank_factorization().expect("rank-one return");
        assert_eq!(one_factor.derived_rank, 1);
        assert_eq!(one_factor.pivot_columns, vec![0]);
        assert_eq!(
            one_factor
                .left
                .multiply(&one_factor.right)
                .expect("product"),
            rank_one
        );

        let singular_rank_two = matrix(&[&[1, 0, 1], &[0, 1, 1], &[1, 1, 2]]);
        let two_factor = singular_rank_two
            .rank_factorization()
            .expect("rank-two singular return");
        assert_eq!(two_factor.derived_rank, 2);
        assert_eq!(two_factor.pivot_columns, vec![0, 1]);
        assert_eq!(two_factor.reconstruction, singular_rank_two);
        assert_eq!(two_factor.linear.kernel.len(), 1);
        assert_eq!(two_factor.linear.cokernel_annihilator.len(), 1);
    }

    /// **A bare transpose is the adjoint only under undeclared orthonormal charts.**
    ///
    /// Under a nonidentity receiver metric the transpose fails `<Tx,y>_Y = <x,T*y>_X` and the
    /// metric adjoint passes it. This is the smuggling `CLAUDE.md` §13 refuses, made executable.
    #[test]
    fn a_bare_transpose_fails_the_adjoint_test_under_a_declared_metric() {
        let transport = matrix(&[&[1, 2], &[0, 3]]);
        let domain_metric = matrix(&[&[2, 0], &[0, 5]]);
        let codomain_metric = matrix(&[&[3, 1], &[1, 4]]);
        let x = vec![rat(1, 1), rat(-2, 1)];
        let y = vec![rat(3, 1), rat(1, 2)];

        let bare = transport.transpose().expect("transposed");
        let bare_defect = transport
            .adjoint_defect(&bare, &domain_metric, &codomain_metric, &x, &y)
            .expect("paired");
        assert!(
            !bare_defect.is_zero(),
            "a bare transpose must not satisfy a declared metric's adjoint law"
        );

        let adjoint = transport
            .metric_adjoint(&domain_metric, &codomain_metric)
            .expect("adjoint");
        let defect = transport
            .adjoint_defect(&adjoint, &domain_metric, &codomain_metric, &x, &y)
            .expect("paired");
        assert!(
            defect.is_zero(),
            "the metric adjoint must satisfy its own law, got {defect}"
        );

        // And under identity metrics the two coincide, which is exactly when the shortcut is lawful.
        let identity = ExactRatMatrix::identity(2).expect("identity");
        assert_eq!(
            transport
                .metric_adjoint(&identity, &identity)
                .expect("adjoint"),
            bare
        );
    }

    /// The reduction's rank agrees with the factorization it founds, and the work is counted rather
    /// than timed.
    #[test]
    fn the_reduction_returns_its_rank_and_what_it_cost() {
        let map = matrix(&[&[1, 2, 3], &[2, 4, 6], &[1, 1, 1]]);
        let (_, pivots, work) = map.reduced_row_echelon().expect("reduced");
        assert_eq!(pivots.len(), 2);
        assert_eq!(map.rank().expect("rank"), 2);
        let coordinates = work.coordinates();
        assert!(
            coordinates
                .iter()
                .any(|(name, count)| *name == "dependency-span"
                    && *count == num_bigint::BigUint::from(2u32)),
            "the dependency span is the pivot count: {coordinates:?}"
        );
    }

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
