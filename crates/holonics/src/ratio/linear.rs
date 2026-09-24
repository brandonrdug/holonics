//! **The exact linear carrier over ℚ: a matrix of ratios whose inversion keeps its fibre.**
//!
//! [definition] Inversion keeps its nonunit fibre instead of inventing a reciprocal
//! ([objects §9](../../../../docs/ELEMENTARY_OBJECTS.md#9-ratio)). For a map `T` the carrier
//! returns all four faces at once ([`LinearFactorization`]): the kernel it collapses, the image it
//! reaches, the cokernel covectors that see nothing it emits (its open exterior), and the rank.
//! The preimage of a target is the complete affine fibre `x₀ + ker T`, or the covector that
//! witnesses the target is unreachable; no representative is selected. [`ExactRatMatrix::inverse`]
//! verifies itself against the identity on both sides.
//!
//! Above a declared extent the rank, kernel and fibre are read through certified prime images
//! (the reduction in `ℤ/p` charts, lifted by Chinese remainder, reconstructed and verified against
//! the caller's own matrix over ℚ); below it by rational Gauss–Jordan. Both return the same values.
//!
//! Lean: `Foundation/TransportLift` (the nonunit fibre), `Holon/Restriction.affineFibre_mem`.

use std::ops::Range;

use crate::ratio::Rat;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use thiserror::Error;

use crate::ratio::polynomial::RationalPolynomial;

pub mod inertia;
pub(crate) mod prime_image;
pub(crate) mod vector;

/// **The declared side above which a reduction is the certified prime-image one.**
///
/// [definition; agent-inferred] See [`ExactRatMatrix::certified_reading`] for what this is
/// inferred from and why it is `min(rows, columns)` rather than an entry population. Below it the
/// textbook rational Gauss–Jordan below owns the reduction unchanged; above it the returned values
/// are identical and the certificate is the authority.
///
/// `48` is sixteen three-dimensional occurrences — the smallest extent at which any of the
/// measured rigidity, chain and contact consumers reads.
pub(crate) const DECLARED_PRIME_IMAGE_CROSSOVER: usize = 48;

/// The work a certified reading performed, in the coordinates [`crate::ratio::work::ExactWork`]
/// names, with nothing invented.
///
/// [definition] The prime-image path's arithmetic is in **machine words**, not in rationals, so
/// its ring multiplications are reported as multiplications and its cumulative/peak widths come
/// only from the rationals actually written into the return. The **dependency span is the pivot
/// count**, as it was for the rational reduction and for the same reason: one image is a sequence
/// of dependent pivots, and placing the images on more lanes does not shorten it.
fn certified_work(
    certificate: &crate::ratio::linear::prime_image::KernelCertificate,
) -> crate::ratio::work::ExactWork {
    let cost = certificate.cost();
    let mut work = crate::ratio::work::ExactWork::nothing();
    work.resident(
        u64::try_from(certificate.rows().saturating_mul(certificate.columns())).unwrap_or(u64::MAX),
    );
    work.multiplied(
        cost.image_multiplications
            .saturating_add(cost.verification_multiplications),
    );
    work.added(cost.lifted_entries);
    work.divided(cost.reconstructed_entries);
    for _ in 0..cost.dependency_span {
        work.stepped();
    }
    for vector in certificate.kernel() {
        for entry in vector {
            work.wrote(entry);
        }
    }
    work
}

#[derive(Clone, Debug, PartialEq, Eq)]
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

    /// The entries as dense rows — the shape the physical laws' own signatures speak in.
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
        self.scaled_impl(coefficient, None)
    }

    pub(crate) fn scaled_with_work(
        &self,
        coefficient: &Rat,
    ) -> (Self, crate::ratio::work::ExactWork) {
        let mut work = crate::ratio::work::ExactWork::nothing();
        let result = self.scaled_impl(coefficient, Some(&mut work));
        (result, work)
    }

    fn scaled_impl(
        &self,
        coefficient: &Rat,
        mut work: Option<&mut crate::ratio::work::ExactWork>,
    ) -> Self {
        let entries = self
            .entries
            .iter()
            .map(|entry| {
                let value = coefficient * entry;
                if let Some(work) = work.as_deref_mut() {
                    work.multiplied(1);
                    work.wrote(&value);
                }
                value
            })
            .collect();
        Self {
            rows: self.rows,
            columns: self.columns,
            entries,
        }
    }

    pub fn add(&self, other: &Self) -> Result<Self, ExactLinearError> {
        self.add_impl(other, None)
    }

    pub(crate) fn add_with_work(
        &self,
        other: &Self,
    ) -> Result<(Self, crate::ratio::work::ExactWork), ExactLinearError> {
        if self.rows != other.rows || self.columns != other.columns {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut work = crate::ratio::work::ExactWork::nothing();
        let result = self.add_impl(other, Some(&mut work))?;
        Ok((result, work))
    }

    fn add_impl(
        &self,
        other: &Self,
        mut work: Option<&mut crate::ratio::work::ExactWork>,
    ) -> Result<Self, ExactLinearError> {
        if self.rows != other.rows || self.columns != other.columns {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let entries = self
            .entries
            .iter()
            .zip(&other.entries)
            .map(|(left, right)| {
                let value = left + right;
                if let Some(work) = work.as_deref_mut() {
                    work.added(1);
                    work.wrote(&value);
                }
                value
            })
            .collect();
        Ok(Self {
            rows: self.rows,
            columns: self.columns,
            entries,
        })
    }

    pub fn subtract(&self, other: &Self) -> Result<Self, ExactLinearError> {
        self.zip(other, |left, right| left - right)
    }

    pub fn multiply(&self, other: &Self) -> Result<Self, ExactLinearError> {
        Ok(self.multiply_with_work(other)?.0)
    }

    /// **The same product, returning what it cost.**
    ///
    /// A product followed by an elimination shares one interval of any clock; counted, the two
    /// separate exactly.
    ///
    /// A product's **dependency span is one**: every output entry is independent of every other, so
    /// the whole deed is one step however many operations it performs. An elimination's span is its
    /// pivot count. That single coordinate is the difference between a deed a card could carry and a
    /// deed it could not, and no scalar cost carries it.
    pub(crate) fn multiply_with_work(
        &self,
        other: &Self,
    ) -> Result<(Self, crate::ratio::work::ExactWork), ExactLinearError> {
        if self.columns != other.rows {
            return Err(ExactLinearError::ShapeMismatch);
        }
        let mut work = crate::ratio::work::ExactWork::nothing();
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

    /// The monic characteristic polynomial, computed by exact Faddeev--LeVerrier recurrence.
    ///
    /// This is the generic matrix operation. Domain-specific spectrum owners may wrap it in their
    /// own refusal type, but the exact matrix and polynomial arithmetic remain shared here.
    pub fn characteristic_polynomial(&self) -> Result<RationalPolynomial, ExactLinearError> {
        if !self.is_square() {
            return Err(ExactLinearError::NonsquareMatrix);
        }
        let extent = self.rows;
        let identity = Self::identity(extent)?;
        let mut coefficients = vec![Rat::one()];
        let mut standing = Self::zero(extent, extent)?;
        for step in 1..=extent {
            let last = coefficients
                .last()
                .cloned()
                .expect("the characteristic recurrence has a leading coefficient");
            standing = self.multiply(&standing)?.add(&identity.scaled(&last))?;
            let product = self.multiply(&standing)?;
            let trace: Rat = (0..extent)
                .map(|index| product.get(index, index).cloned())
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .sum();
            coefficients.push(-trace / Rat::from_integer(BigInt::from(step as i64)));
        }
        coefficients.reverse();
        Ok(RationalPolynomial::new(coefficients))
    }

    /// The first monic polynomial relation among the powers of this square exact matrix.
    ///
    /// The search is over the matrix's own dimension, which is the Cayley--Hamilton bound. Each
    /// candidate solves the flattened operator relation through [`Self::preimage_fibre`]; the first
    /// reachable degree is the unique monic minimal polynomial over `Q`.
    pub fn minimal_polynomial(&self) -> Result<RationalPolynomial, ExactLinearError> {
        Ok(self.minimal_polynomial_with_work()?.0)
    }

    /// The minimal polynomial together with the exact work of power construction and relation
    /// searches. The coefficient preimage kernel is checked to be empty at the first degree because
    /// a monic minimum-degree relation is unique; callers needing a family at a fixed larger degree
    /// should use [`Self::preimage_fibre`] directly.
    pub(crate) fn minimal_polynomial_with_work(
        &self,
    ) -> Result<(RationalPolynomial, crate::ratio::work::ExactWork), ExactLinearError> {
        let (polynomial, work, _) = self.minimal_polynomial_with_work_and_powers()?;
        Ok((polynomial, work))
    }

    fn minimal_polynomial_with_work_and_powers(
        &self,
    ) -> Result<(RationalPolynomial, crate::ratio::work::ExactWork, Vec<Self>), ExactLinearError>
    {
        if !self.is_square() {
            return Err(ExactLinearError::NonsquareMatrix);
        }
        if self.rows == 0 {
            return Ok((
                RationalPolynomial::one(),
                crate::ratio::work::ExactWork::nothing(),
                vec![Self::identity(0)?],
            ));
        }

        let mut powers = vec![Self::identity(self.rows)?];
        let mut work = crate::ratio::work::ExactWork::nothing();
        for degree in 1..=self.rows {
            let (next, power_work) = powers
                .last()
                .expect("the identity power exists")
                .multiply_with_work(self)?;
            work = work.then(&power_work);
            powers.push(next);

            let mut relation_rows = Vec::with_capacity(self.rows * self.columns);
            for row in 0..self.rows {
                for column in 0..self.columns {
                    let mut coefficients = Vec::with_capacity(degree);
                    for power in 0..degree {
                        coefficients.push(powers[power].get(row, column)?.clone());
                    }
                    relation_rows.push(coefficients);
                }
            }
            let target: Vec<Rat> = powers[degree]
                .entries
                .iter()
                .map(|entry| -entry.clone())
                .collect();
            let relation = Self::new(relation_rows)?;
            let (solution, relation_work) = relation.preimage_fibre_with_work(&target)?;
            work = work.then(&relation_work);
            let Some((mut coefficients, kernel)) = solution else {
                continue;
            };
            if !kernel.is_empty() {
                return Err(ExactLinearError::RankFactorizationCertificateFailure);
            }
            coefficients.push(Rat::one());
            let polynomial = RationalPolynomial::new(coefficients.clone());
            let mut residual = Self::zero(self.rows, self.columns)?;
            for (power, coefficient) in coefficients.iter().enumerate() {
                let scaled = powers[power].scaled_with_work(coefficient);
                work = work.then(&scaled.1);
                let added = residual.add_with_work(&scaled.0)?;
                work = work.then(&added.1);
                residual = added.0;
            }
            if residual.entries.iter().any(|entry| !entry.is_zero()) {
                return Err(ExactLinearError::RankFactorizationCertificateFailure);
            }
            return Ok((polynomial, work, powers));
        }
        Err(ExactLinearError::RankFactorizationCertificateFailure)
    }

    /// Evaluate a large operator power after reducing its exponent modulo the exact minimal
    /// polynomial. The returned matrix is the same operator power, with the polynomial reduction
    /// and the exact matrix multiplication/evaluation work retained.
    pub fn power_reduced(&self, exponent: u64) -> Result<Self, ExactLinearError> {
        Ok(self.power_reduced_with_work(exponent)?.0)
    }

    /// The reduced operator power together with the work of discovering its minimal polynomial,
    /// constructing the needed powers, and evaluating the reduced polynomial in the matrix.
    /// Polynomial coefficient arithmetic itself is exact and uses the existing
    /// `RationalPolynomial` owner.
    pub(crate) fn power_reduced_with_work(
        &self,
        exponent: u64,
    ) -> Result<(Self, crate::ratio::work::ExactWork), ExactLinearError> {
        if !self.is_square() {
            return Err(ExactLinearError::NonsquareMatrix);
        }
        if exponent == 0 {
            return Ok((
                Self::identity(self.rows)?,
                crate::ratio::work::ExactWork::nothing(),
            ));
        }
        let (minimal, mut work, powers) = self.minimal_polynomial_with_work_and_powers()?;
        if minimal.degree().is_none() {
            return Err(ExactLinearError::RankFactorizationCertificateFailure);
        }
        let mut reduced_result = RationalPolynomial::one();
        let mut reduced_base = RationalPolynomial::variable();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining % 2 == 1 {
                let (product, product_work) = reduced_result.times_with_work(&reduced_base);
                work = work.then(&product_work);
                let (_, remainder, division_work) = product
                    .divided_by_with_work(&minimal)
                    .map_err(|_| ExactLinearError::RankFactorizationCertificateFailure)?;
                work = work.then(&division_work);
                reduced_result = remainder;
            }
            remaining /= 2;
            if remaining > 0 {
                let (product, product_work) = reduced_base.times_with_work(&reduced_base);
                work = work.then(&product_work);
                let (_, remainder, division_work) = product
                    .divided_by_with_work(&minimal)
                    .map_err(|_| ExactLinearError::RankFactorizationCertificateFailure)?;
                work = work.then(&division_work);
                reduced_base = remainder;
            }
        }

        let mut rows = vec![vec![Rat::zero(); self.columns]; self.rows];
        for (power, coefficient) in reduced_result.coefficients().iter().enumerate() {
            for row in 0..self.rows {
                for column in 0..self.columns {
                    let term = coefficient * powers[power].get(row, column)?;
                    work.multiplied(1);
                    if power == 0 {
                        rows[row][column] = term;
                    } else {
                        rows[row][column] += term;
                        work.added(1);
                    }
                }
            }
        }
        for row in &rows {
            for value in row {
                work.wrote(value);
            }
        }
        Ok((Self::new(rows)?, work))
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
    // A map factors as
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
    ///
    /// **Above [`DECLARED_PRIME_IMAGE_CROSSOVER`] the reduction is the certified prime-image one**
    /// and the returned rows are identical: a reduced row echelon form is canonical, so the two
    /// paths cannot disagree about it, and
    /// [`crate::ratio::linear::prime_image::KernelCertificate::reduced_rows`] reconstructs nothing extra
    /// to produce it. See [`Self::certified_reading`] for why the signature is unchanged.
    pub(crate) fn reduced_row_echelon(
        &self,
    ) -> Result<(Self, Vec<usize>, crate::ratio::work::ExactWork), ExactLinearError> {
        if let Some(certificate) = self.certified_reading() {
            let work = certified_work(&certificate);
            let rows = certificate.reduced_rows();
            let pivots = certificate.pivot_columns().to_vec();
            return Ok((Self::shaped(self.rows, self.columns, rows)?, pivots, work));
        }
        let mut work = crate::ratio::work::ExactWork::nothing();
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
    ///
    /// Above [`DECLARED_PRIME_IMAGE_CROSSOVER`] this is the **certified** rank: `≥ r` from a
    /// nonzero modular minor and `≤ r` from `n − r` exhibited independent rational kernel vectors
    /// checked against this matrix over ℚ. Below it, the rational reduction's pivot count.
    pub fn rank(&self) -> Result<usize, ExactLinearError> {
        if let Some(certificate) = self.certified_reading() {
            return Ok(certificate.rank());
        }
        Ok(self.reduced_row_echelon()?.1.len())
    }

    /// **The certified reading of this map, or `None` where the rational reduction owns it.**
    ///
    /// [definition; agent-inferred] The crossover is on `min(rows, columns)`, which bounds the
    /// rank, because the rational path's cost is driven by **coefficient growth** — the
    /// intermediate entries of a rational elimination are minors of the input, whose bit width
    /// grows with the rank — and not by the entry population. Below the crossover a certified
    /// reading's fixed cost (the charts decided and reduced) would dominate.
    ///
    /// **A refusal falls back rather than propagating.** The rational path is exact and total, so a
    /// reading that exhausts its prime budget or fails its own verification costs a slower return,
    /// never a wrong one.
    fn certified_reading(&self) -> Option<crate::ratio::linear::prime_image::KernelCertificate> {
        if self.rows.min(self.columns) < DECLARED_PRIME_IMAGE_CROSSOVER {
            return None;
        }
        crate::ratio::linear::prime_image::certified_kernel(self).ok()
    }

    /// **A basis of `ker(T)`: the directions this map collapses.**
    ///
    /// One vector per free column, each carrying a single `1` in its own free coordinate, so the
    /// population is exhibited rather than summarized by a count. An empty return is a genuine
    /// zero: the map collapses nothing.
    pub fn kernel_basis(&self) -> Result<Vec<Vec<Rat>>, ExactLinearError> {
        if let Some(certificate) = self.certified_reading() {
            return Ok(certificate.kernel().to_vec());
        }
        let (reduced, pivots, _) = self.reduced_row_echelon()?;
        self.kernel_basis_from_reduced(&reduced, &pivots)
    }

    fn kernel_basis_from_reduced(
        &self,
        reduced: &Self,
        pivots: &[usize],
    ) -> Result<Vec<Vec<Rat>>, ExactLinearError> {
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
        Ok(self.preimage_fibre_with_work(target)?.0)
    }

    /// The complete affine preimage together with the exact work of its one augmented RREF.
    ///
    /// The particular and kernel are both derived from the same reduced augmented matrix. This
    /// keeps the returned work truthful and avoids rerunning the source reduction just to recover
    /// its kernel basis.
    pub(crate) fn preimage_fibre_with_work(
        &self,
        target: &[Rat],
    ) -> Result<
        (
            Option<(Vec<Rat>, Vec<Vec<Rat>>)>,
            crate::ratio::work::ExactWork,
        ),
        ExactLinearError,
    > {
        if target.len() != self.rows {
            return Err(ExactLinearError::ShapeMismatch);
        }
        if self.rows.min(self.columns) >= DECLARED_PRIME_IMAGE_CROSSOVER
            && let Ok((fibre, certificate)) =
                crate::ratio::linear::prime_image::certified_fibre(self, target)
        {
            // `A x = b` is one clause of the augmented certificate's own `[A | b] N = 0`, already
            // checked over Q; `None` is the augmented column taken as a pivot, which is exactly
            // `rank [A | b] = rank A + 1`.
            return Ok((fibre, certified_work(&certificate)));
        }
        let mut augmented = self.to_rows();
        for (row, value) in augmented.iter_mut().zip(target) {
            row.push(value.clone());
        }
        let augmented = Self::new(augmented)?;
        let (reduced, pivots, work) = augmented.reduced_row_echelon()?;
        if pivots.last() == Some(&self.columns) {
            // A pivot in the augmented column: the target is outside the image.
            return Ok((None, work));
        }
        let mut particular = vec![Rat::zero(); self.columns];
        for (row, pivot) in pivots.iter().enumerate() {
            particular[*pivot] = reduced.get(row, self.columns)?.clone();
        }
        let kernel = self.kernel_basis_from_reduced(&reduced, &pivots)?;
        Ok((Some((particular, kernel)), work))
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

    /// **The metric adjoint `G_X^-1 T^T G_Y`**, characterized by `<Tx, y>_Y = <x, T^dagger y>_X`.
    ///
    /// A bare transpose is this object only when both metrics are the identity, which is an
    /// orthonormal Euclidean declaration. The metric is a declared receiver face, so it is a
    /// parameter here and never a default.
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
#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub work: crate::ratio::work::ExactWork,
}

/// One exact rank factorization and the gauge and fibres which keep it interpretable.
#[derive(Clone, Debug, PartialEq, Eq)]
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
    pub work: crate::ratio::work::ExactWork,
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

    fn pairing(left: &[Rat], right: &[Rat]) -> Rat {
        left.iter()
            .zip(right)
            .fold(Rat::zero(), |sum, (a, b)| sum + a * b)
    }

    /// **Inversion keeps its nonunit fibre.** A singular map returns its four faces, not an
    /// inverse: the kernel it collapses (`T k = 0`) and the cokernel covectors that annihilate its
    /// image.
    #[test]
    fn a_singular_map_returns_its_kernel_and_cokernel_instead_of_an_inverse() {
        let singular = matrix(&[&[1, 2, 3], &[2, 4, 6], &[1, 1, 1]]);
        assert_eq!(singular.inverse(), Err(ExactLinearError::SingularMatrix));
        let factorization = singular.factorization().expect("factored");
        assert_eq!(factorization.rank, 2);
        assert_eq!(factorization.collapsed_dimension(), 1);
        assert_eq!(factorization.open_exterior_dimension(), 1);
        assert!(!factorization.is_rebase());
        let kernel = &factorization.kernel[0];
        assert!(
            singular
                .apply(kernel)
                .expect("applies")
                .iter()
                .all(Zero::is_zero)
        );
        let covector = &factorization.cokernel_annihilator[0];
        for column in &factorization.image {
            assert!(pairing(covector, column).is_zero());
        }
    }

    /// An invertible map composes with its inverse to the identity on both sides, exactly.
    #[test]
    fn the_inverse_composes_to_the_identity_on_both_sides() {
        let map = matrix(&[&[2, 1], &[1, 2]]);
        let inverse = map.inverse().unwrap();
        let identity = ExactRatMatrix::identity(2).unwrap();
        assert_eq!(map.multiply(&inverse).unwrap(), identity);
        assert_eq!(inverse.multiply(&map).unwrap(), identity);
        assert!(map.factorization().expect("factored").is_rebase());
    }

    /// **A rectangular map has no inverse and says so**, returning the affine preimage fibre for a
    /// reachable target and a witnessing covector for an unreachable one. No representative is
    /// selected in either case.
    #[test]
    fn a_rectangular_map_returns_an_affine_fibre_or_an_exhibited_obstruction() {
        // Two equations, three unknowns: one free direction.
        let wide = matrix(&[&[1, 1, 0], &[0, 1, 1]]);
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

    /// The rank factorization reconstructs the map, `A = left · right`, at ranks zero, one and two.
    #[test]
    fn the_rank_factorization_reconstructs_the_map() {
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

    /// **The metric adjoint** `G_X⁻¹ Tᵀ G_Y` satisfies `⟨Tx, y⟩_Y = ⟨x, T†y⟩_X`; the bare transpose
    /// does not under a declared nonidentity metric, and coincides with it under identity metrics.
    #[test]
    fn the_metric_adjoint_satisfies_its_pairing_and_the_bare_transpose_does_not() {
        let transport = matrix(&[&[1, 2], &[0, 3]]);
        let domain_metric = matrix(&[&[2, 0], &[0, 5]]);
        let codomain_metric = matrix(&[&[3, 1], &[1, 4]]);
        let x = vec![rat(1, 1), rat(-2, 1)];
        let y = vec![rat(3, 1), rat(1, 2)];
        let defect = |claimed: &ExactRatMatrix| {
            pairing(
                &transport.apply(&x).unwrap(),
                &codomain_metric.apply(&y).unwrap(),
            ) - pairing(
                &domain_metric.apply(&x).unwrap(),
                &claimed.apply(&y).unwrap(),
            )
        };
        let bare = transport.transpose().expect("transposed");
        assert!(!defect(&bare).is_zero());
        let adjoint = transport
            .metric_adjoint(&domain_metric, &codomain_metric)
            .expect("adjoint");
        assert!(defect(&adjoint).is_zero());
        let identity = ExactRatMatrix::identity(2).expect("identity");
        assert_eq!(
            transport.metric_adjoint(&identity, &identity).unwrap(),
            bare
        );
    }

    /// The minimal polynomial divides the characteristic one and drops the repeated eigenvalue.
    #[test]
    fn the_minimal_polynomial_drops_a_repeated_semisimple_eigenvalue() {
        let repeated = ExactRatMatrix::from_diagonal(vec![
            Rat::one(),
            Rat::from_integer(2.into()),
            Rat::from_integer(2.into()),
        ])
        .unwrap();
        assert_eq!(
            repeated.characteristic_polynomial().unwrap(),
            RationalPolynomial::new(vec![
                Rat::from_integer(BigInt::from(-4)),
                Rat::from_integer(8.into()),
                Rat::from_integer(BigInt::from(-5)),
                Rat::one(),
            ])
        );
        assert_eq!(
            repeated.minimal_polynomial().unwrap(),
            RationalPolynomial::new(vec![
                Rat::from_integer(2.into()),
                Rat::from_integer(BigInt::from(-3)),
                Rat::one(),
            ])
        );
    }

    /// A nilpotent Jordan block has minimal polynomial `x²`, so every reduced power past one is zero.
    #[test]
    fn the_minimal_polynomial_of_a_nilpotent_jordan_block_is_x_squared() {
        let nilpotent = matrix(&[&[0, 1], &[0, 0]]);
        assert_eq!(
            nilpotent.minimal_polynomial().unwrap(),
            RationalPolynomial::new(vec![Rat::zero(), Rat::zero(), Rat::one()])
        );
        assert_eq!(
            nilpotent.power_reduced(7).unwrap(),
            ExactRatMatrix::zero(2, 2).unwrap()
        );
    }

    /// Above the crossover the certified prime-image reading returns the same reduction, pivots
    /// and kernel as the rational Gauss–Jordan on the same matrix, and verifies against it over ℚ.
    #[test]
    fn the_certified_path_and_the_rational_path_return_the_same_reduction() {
        // Deterministic, generic, and exactly at the crossover so both paths are reachable.
        let side = DECLARED_PRIME_IMAGE_CROSSOVER;
        let rows: Vec<Vec<Rat>> = (0..side)
            .map(|row| {
                (0..side)
                    .map(|column| {
                        let value = ((row * 31 + column * 17) % 23) as i64 - 11;
                        // The last two rows are dependent, so the map has a real kernel to exhibit.
                        rat(value, if column % 3 == 0 { 2 } else { 1 })
                    })
                    .collect()
            })
            .collect();
        let mut rows = rows;
        rows[side - 1] = rows[0].clone();
        rows[side - 2] = rows[1]
            .iter()
            .zip(&rows[2])
            .map(|(left, right)| left + right)
            .collect();
        let map = ExactRatMatrix::shaped(side, side, rows).expect("a square fixture");

        let certificate = map
            .certified_reading()
            .expect("the certified path is taken");
        certificate
            .verify(&map)
            .expect("the certificate verifies against this very matrix");

        // The rational primitive, reached directly so the comparison is between the two paths and
        // not between one path and itself.
        let mut work = crate::ratio::work::ExactWork::nothing();
        work.resident(u64::try_from(side * side).unwrap_or(u64::MAX));
        let mut rational_rows = map.to_rows();
        let mut rational_pivots: Vec<usize> = Vec::new();
        let mut pivot_row = 0usize;
        for column in 0..side {
            if pivot_row >= side {
                break;
            }
            let Some(found) = (pivot_row..side).find(|row| !rational_rows[*row][column].is_zero())
            else {
                continue;
            };
            rational_rows.swap(found, pivot_row);
            let divisor = rational_rows[pivot_row][column].clone();
            for entry in &mut rational_rows[pivot_row] {
                *entry /= &divisor;
            }
            let pivot = rational_rows[pivot_row].clone();
            for row in 0..side {
                if row == pivot_row || rational_rows[row][column].is_zero() {
                    continue;
                }
                let factor = rational_rows[row][column].clone();
                for (entry, above) in rational_rows[row].iter_mut().zip(&pivot) {
                    *entry -= &factor * above;
                }
            }
            rational_pivots.push(column);
            pivot_row += 1;
        }

        assert_eq!(certificate.rank(), rational_pivots.len());
        assert_eq!(certificate.pivot_columns(), rational_pivots.as_slice());
        assert_eq!(certificate.reduced_rows(), rational_rows);
        assert_eq!(map.rank().expect("rank"), rational_pivots.len());
        let (reduced, pivots, _) = map.reduced_row_echelon().expect("reduced");
        assert_eq!(reduced.to_rows(), rational_rows);
        assert_eq!(pivots, rational_pivots);

        // And the kernel the public entry returns is the canonical one the rational reduction
        // determines, vector for vector.
        let reduced_matrix = ExactRatMatrix::shaped(side, side, rational_rows).expect("shaped");
        let rational_kernel = map
            .kernel_basis_from_reduced(&reduced_matrix, &rational_pivots)
            .expect("the rational kernel");
        assert_eq!(map.kernel_basis().expect("kernel"), rational_kernel);
        assert!(
            !rational_kernel.is_empty(),
            "the fixture has a kernel to exhibit"
        );
    }

    /// The fibre is the same object on both sides of the crossover, target by target.
    #[test]
    fn the_certified_fibre_agrees_with_the_rational_one_at_the_crossover() {
        let side = DECLARED_PRIME_IMAGE_CROSSOVER;
        let rows: Vec<Vec<Rat>> = (0..side)
            .map(|row| {
                (0..side)
                    .map(|column| rat(((row * 13 + column * 29) % 19) as i64 - 9, 1))
                    .collect()
            })
            .collect();
        let map = ExactRatMatrix::shaped(side, side, rows).expect("a square fixture");
        let source: Vec<Rat> = (0..side).map(|at| rat(at as i64 - 5, 3)).collect();
        let target = map.apply(&source).expect("a reachable target");

        let fibre = map.preimage_fibre(&target).expect("the fibre returns");
        let (particular, kernel) = fibre.expect("a reachable target has a fibre");
        assert_eq!(map.apply(&particular).expect("applied"), target);
        for vector in &kernel {
            assert!(
                map.apply(vector)
                    .expect("applied")
                    .iter()
                    .all(num_traits::Zero::is_zero)
            );
        }
        // The particular point is the canonical one: zero on every free coordinate.
        let (_, pivots, _) = map.reduced_row_echelon().expect("reduced");
        for column in 0..side {
            if !pivots.contains(&column) {
                assert!(
                    particular[column].is_zero(),
                    "canonical on the free coordinates"
                );
            }
        }
    }
}
