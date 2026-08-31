#![allow(unused_imports)]

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::*;

/// Refactor a direct sum through an intrinsic row image. The selected rows remain integral;
/// `source_to_image` carries every transported row into that basis, and the constitutive form is
/// pulled through the same addressed map. This is the chart-independent law mirrored by the
/// resident finite-chart construction; no cross-moment Gram is part of the returned section.
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::receiver_history_compression::{
    AddressedFactoredIntegralReceiverComplex, FactoredIntegralReceiverForm,
    SparseIntegralFunctional,
};

struct CanonicalizedMoment {
    section: FactoredMomentSection,
    source_to_image: ExactRatMatrix,
}

struct IntegralFactorSpanFounder {
    factor_population: usize,
    basis: Vec<Vec<BigInt>>,
    pivots: Vec<usize>,
}

impl IntegralFactorSpanFounder {
    fn new(factor_population: usize) -> Result<Self, FactoredMomentError> {
        if factor_population == 0 {
            return Err(FactoredMomentError::Shape);
        }
        Ok(Self {
            factor_population,
            basis: Vec::new(),
            pivots: Vec::new(),
        })
    }

    fn reduce(&self, candidate: &[BigInt]) -> Result<(Vec<Rat>, Vec<Rat>), FactoredMomentError> {
        if candidate.len() != self.factor_population {
            return Err(FactoredMomentError::Shape);
        }
        let mut residual = candidate
            .iter()
            .cloned()
            .map(Rat::from_integer)
            .collect::<Vec<_>>();
        let mut coordinates = vec![Rat::zero(); self.basis.len()];
        for (basis_at, (basis, pivot)) in self.basis.iter().zip(&self.pivots).enumerate() {
            let coefficient = &residual[*pivot] / Rat::from_integer(basis[*pivot].clone());
            if coefficient.is_zero() {
                continue;
            }
            coordinates[basis_at] += &coefficient;
            for (held, basis_value) in residual.iter_mut().zip(basis) {
                *held -= &coefficient * Rat::from_integer(basis_value.clone());
            }
        }
        Ok((residual, coordinates))
    }

    fn admit(&mut self, candidate: Vec<BigInt>) -> Result<bool, FactoredMomentError> {
        let (residual, _) = self.reduce(&candidate)?;
        let Some(pivot) = residual.iter().position(|entry| !entry.is_zero()) else {
            return Ok(false);
        };
        let common_denominator = residual.iter().fold(BigInt::one(), |held, entry| {
            exact_bigint_lcm(held, entry.denom().clone())
        });
        let mut integral = residual
            .iter()
            .map(|entry| entry.numer() * (&common_denominator / entry.denom()))
            .collect::<Vec<_>>();
        let divisor = integral
            .iter()
            .filter(|entry| !entry.is_zero())
            .map(|entry| entry.abs())
            .reduce(exact_bigint_gcd)
            .ok_or(FactoredMomentError::ZeroImage)?;
        if divisor.is_zero() {
            return Err(FactoredMomentError::ZeroImage);
        }
        if integral[pivot].is_negative() {
            for entry in &mut integral {
                *entry = -entry.clone();
            }
        }
        for entry in &mut integral {
            *entry /= &divisor;
        }
        self.basis.push(integral);
        self.pivots.push(pivot);
        Ok(true)
    }
}

fn exact_bigint_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn exact_bigint_lcm(left: BigInt, right: BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        BigInt::ZERO
    } else {
        let divisor = exact_bigint_gcd(left.clone(), right.clone());
        (left / divisor * right).abs()
    }
}

impl FactoredMomentSection {
    /// Found the exact canonical image chart from one positive weighted integral current family.
    /// The family is returned separately as reconstruction testimony and is not retained by the
    /// hot section.
    pub fn found(
        factor_population: u32,
        family: Vec<WeightedIntegralCurrent>,
    ) -> Result<FactoredMomentFoundation, FactoredMomentError> {
        if factor_population == 0
            || family.is_empty()
            || family.len() > u32::MAX as usize
            || family.iter().any(|current| {
                current.weight.is_zero()
                    || current.entries.is_empty()
                    || current
                        .entries
                        .windows(2)
                        .any(|pair| pair[0].0 >= pair[1].0)
                    || current.entries.iter().any(|(factor, coefficient)| {
                        *factor >= factor_population || coefficient.is_zero()
                    })
            })
        {
            return Err(FactoredMomentError::Shape);
        }

        let canonical = canonicalize_integral_weighted_family(factor_population, &family)?;
        Ok(FactoredMomentFoundation {
            schema: "holonic-engine.factored-moment-foundation.v1".to_owned(),
            source_population: u32::try_from(family.len())
                .map_err(|_| FactoredMomentError::Shape)?,
            source_to_image: canonical.source_to_image,
            reconstruction_fibre: family,
            section: canonical.section,
        })
    }

    /// Apply every addressed generator independently, take the direct sum of their quadratic
    /// moments, and derive the next exact image chart.  The operation consumes no source family
    /// and introduces no caller-chosen width.
    pub fn transport_direct_sum(
        &self,
        generators: &[Vec<u32>],
    ) -> Result<FactoredMomentPassage, FactoredMomentError> {
        self.validate_admitted()?;
        let factors = self.factor_population as usize;
        let rank = self.image_rank as usize;
        if generators.is_empty()
            || generators.len() > u32::MAX as usize
            || generators.iter().any(|generator| {
                generator.len() != factors
                    || generator
                        .iter()
                        .any(|target| *target >= self.factor_population)
            })
        {
            return Err(FactoredMomentError::Shape);
        }
        let block_rows = generators
            .len()
            .checked_mul(rank)
            .ok_or(FactoredMomentError::Shape)?;
        // The admitted normal form keeps incidence integral and carries every quotient in the
        // constitutive leg. `integralized_incidence` remains defensive for remounted exterior
        // testimony created before that normal form was enforced:
        //
        //     B = A / d,   B^T H B = A^T (H / d^2) A.
        //
        // This keeps recurrence closed over every exact section.
        let (incidence_denominator, source_incidence) = self.integralized_incidence()?;
        let denominator_square = &incidence_denominator * &incidence_denominator;
        let effective_constitutive = ExactRatMatrix::new(
            self.constitutive
                .to_rows()
                .into_iter()
                .map(|row| {
                    row.into_iter()
                        .map(|entry| entry / Rat::from_integer(denominator_square.clone()))
                        .collect()
                })
                .collect(),
        )?;
        let mut transported = vec![vec![BigInt::ZERO; factors]; block_rows];
        for (generator_at, generator) in generators.iter().enumerate() {
            for source_rank in 0..rank {
                let row = &mut transported[generator_at * rank + source_rank];
                for (source_factor, target_factor) in generator.iter().enumerate() {
                    row[*target_factor as usize] += &source_incidence[source_rank][source_factor];
                }
            }
        }
        let canonical = canonicalize_integral_direct_sum_moment(
            &transported,
            generators.len(),
            &effective_constitutive,
        )?;
        FactoredMomentPassage::found(
            self.clone(),
            generators.to_vec(),
            canonical.source_to_image,
            canonical.section,
        )
    }

    fn integralized_incidence(&self) -> Result<(BigInt, Vec<Vec<BigInt>>), FactoredMomentError> {
        self.validate_admitted()?;
        let denominator = self
            .incidence
            .entries()
            .iter()
            .fold(BigInt::one(), |held, entry| {
                exact_bigint_lcm(held, entry.denom().clone())
            });
        if denominator.is_zero() {
            return Err(FactoredMomentError::Reconstruction);
        }
        let rows = self
            .incidence
            .to_rows()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|entry| entry.numer() * (&denominator / entry.denom()))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Ok((denominator, rows))
    }

    /// Return the integral cross-moment chart required by an integer apparatus boundary.  This
    /// stricter projection is distinct from the denominator-carrying recurrent passage above.
    pub fn integral_incidence(&self) -> Result<Vec<Vec<BigInt>>, FactoredMomentError> {
        self.incidence
            .to_rows()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|value| {
                        value
                            .denom()
                            .is_one()
                            .then(|| value.numer().clone())
                            .ok_or(FactoredMomentError::NonIntegralChart)
                    })
                    .collect()
            })
            .collect()
    }

    pub(crate) fn read_functional_admitted(
        &self,
        functional: &SparseIntegralFunctional,
    ) -> Result<Vec<Rat>, FactoredMomentError> {
        if functional.factor_population != self.factor_population {
            return Err(FactoredMomentError::Shape);
        }
        (0..self.image_rank as usize)
            .map(|row| {
                functional
                    .entries
                    .iter()
                    .try_fold(Rat::zero(), |sum, entry| {
                        if entry.factor >= self.factor_population {
                            return Err(FactoredMomentError::Shape);
                        }
                        Ok(sum
                            + Rat::from_integer(entry.coefficient.clone())
                                * self.incidence.get(row, entry.factor as usize)?)
                    })
            })
            .collect()
    }

    pub(crate) fn validate_admitted(&self) -> Result<(), FactoredMomentError> {
        let rank = self.image_rank as usize;
        if self.schema != "holonic-engine.factored-moment-section.v2"
            || self.factor_population == 0
            || rank == 0
            || self.basis_factors.len() != rank
            || self
                .basis_factors
                .iter()
                .any(|factor| *factor >= self.factor_population)
            || self.basis_factors.windows(2).any(|pair| pair[0] >= pair[1])
            || self.incidence.rows() != rank
            || self.incidence.columns() != self.factor_population as usize
            || self.constitutive.rows() != rank
            || self.constitutive.columns() != rank
        {
            return Err(FactoredMomentError::Shape);
        }
        if self.constitutive.transpose()? != self.constitutive {
            return Err(FactoredMomentError::Reconstruction);
        }
        let basis_minor = ExactRatMatrix::new(
            self.incidence
                .to_rows()
                .into_iter()
                .map(|row| {
                    self.basis_factors
                        .iter()
                        .map(|factor| row[*factor as usize].clone())
                        .collect::<Vec<_>>()
                })
                .collect(),
        )?;
        // Invertibility of one addressed minor certifies that the image frame has exactly the
        // declared row rank. The inverse is discarded: it belongs to admission testimony and is
        // not a constitutive law of the section.
        let _basis_inverse = basis_minor.inverse()?;
        Ok(())
    }
}

fn canonicalize_integral_direct_sum_moment(
    transported: &[Vec<BigInt>],
    generator_population: usize,
    source_constitutive: &ExactRatMatrix,
) -> Result<CanonicalizedMoment, FactoredMomentError> {
    let block_rows = transported.len();
    let factors = transported.first().map_or(0, Vec::len);
    let source_rank = source_constitutive.rows();
    if generator_population == 0
        || source_rank == 0
        || source_constitutive.columns() != source_rank
        || block_rows != generator_population.saturating_mul(source_rank)
        || factors == 0
        || transported.iter().any(|row| row.len() != factors)
    {
        return Err(FactoredMomentError::Shape);
    }

    let mut row_founder = IntegralFactorSpanFounder::new(factors)?;
    let mut image_rows = Vec::<Vec<BigInt>>::new();
    for row in transported {
        if row_founder.admit(row.clone())? {
            image_rows.push(row.clone());
        }
    }
    let target_rank = image_rows.len();
    if target_rank == 0 || target_rank > u32::MAX as usize {
        return Err(FactoredMomentError::ZeroImage);
    }

    // Select an addressed nonsingular factor minor of the intrinsic row frame. The selection is
    // testimony of full row rank and gives the exact coordinate chart used to factor every
    // transported row through `image_rows`.
    let mut column_founder = IntegralFactorSpanFounder::new(target_rank)?;
    let mut basis_factors = Vec::new();
    for factor in 0..factors {
        let column = image_rows
            .iter()
            .map(|row| row[factor].clone())
            .collect::<Vec<_>>();
        if column_founder.admit(column)? {
            basis_factors.push(factor);
        }
        if basis_factors.len() == target_rank {
            break;
        }
    }
    if basis_factors.len() != target_rank {
        return Err(FactoredMomentError::Reconstruction);
    }

    let incidence = ExactRatMatrix::new(
        image_rows
            .iter()
            .map(|row| row.iter().cloned().map(Rat::from_integer).collect())
            .collect(),
    )?;
    let basis_minor = ExactRatMatrix::new(
        image_rows
            .iter()
            .map(|row| {
                basis_factors
                    .iter()
                    .map(|factor| Rat::from_integer(row[*factor].clone()))
                    .collect()
            })
            .collect(),
    )?;
    let basis_inverse = basis_minor.inverse()?;
    let restricted_rows = ExactRatMatrix::new(
        transported
            .iter()
            .map(|row| {
                basis_factors
                    .iter()
                    .map(|factor| Rat::from_integer(row[*factor].clone()))
                    .collect()
            })
            .collect(),
    )?;
    let source_to_image = restricted_rows.multiply(&basis_inverse)?;
    let source_rows = source_constitutive.to_rows();
    let mut plural_constitutive = vec![vec![Rat::zero(); block_rows]; block_rows];
    for generator in 0..generator_population {
        for row in 0..source_rank {
            for column in 0..source_rank {
                plural_constitutive[generator * source_rank + row]
                    [generator * source_rank + column] = source_rows[row][column].clone();
            }
        }
    }
    let plural_constitutive = ExactRatMatrix::new(plural_constitutive)?;
    let constitutive = source_to_image
        .transpose()?
        .multiply(&plural_constitutive)?
        .multiply(&source_to_image)?;
    let section = FactoredMomentSection {
        schema: "holonic-engine.factored-moment-section.v2".to_owned(),
        factor_population: u32::try_from(factors).map_err(|_| FactoredMomentError::Shape)?,
        image_rank: u32::try_from(target_rank).map_err(|_| FactoredMomentError::Shape)?,
        basis_factors: basis_factors
            .into_iter()
            .map(|factor| u32::try_from(factor).map_err(|_| FactoredMomentError::Shape))
            .collect::<Result<Vec<_>, _>>()?,
        incidence,
        constitutive,
    };
    section.validate_admitted()?;
    Ok(CanonicalizedMoment {
        section,
        source_to_image,
    })
}

fn canonicalize_integral_weighted_family(
    factor_population: u32,
    family: &[WeightedIntegralCurrent],
) -> Result<CanonicalizedMoment, FactoredMomentError> {
    let source_rows = family.len();
    let factors = factor_population as usize;
    if source_rows == 0 || factors == 0 {
        return Err(FactoredMomentError::Shape);
    }
    let mut source_frame = vec![vec![BigInt::ZERO; factors]; source_rows];
    let source_weights = family
        .iter()
        .map(|current| BigInt::from(current.weight.clone()))
        .collect::<Vec<_>>();
    for (row, current) in family.iter().enumerate() {
        for (factor, coefficient) in &current.entries {
            source_frame[row][*factor as usize] = BigInt::from(coefficient.clone());
        }
    }

    // Let `P = source_frame[:, pivot_factors]` be the lexicographically first independent factor
    // columns.  The exact moment `C = Xᵀ H X` then has the canonical cross-moment chart
    //
    //     B = Pᵀ H X,       K = Pᵀ H P,       C = Bᵀ K⁻¹ B.
    //
    // The entering rows reconstruct as `X = (P K⁻¹) B`.  This derives the intrinsic image
    // directly from the covariance and never row-reduces the foreign factor population or asks
    // the generic linear owner to enumerate its enormous ambient cokernel.
    // The entering chart and its diagonal constitutive weights are integral.  Keep the broad
    // factor sweep in that exact carrier: converting all `source_rows × factors` entries to
    // rationals and then multiplying two broad matrices is an exterior apparatus cost, not part
    // of the canonical image law.
    let mut column_founder = IntegralFactorSpanFounder::new(source_rows)?;
    let mut pivot_factors = Vec::new();
    for factor in 0..factors {
        let column = source_frame
            .iter()
            .map(|row| row[factor].clone())
            .collect::<Vec<_>>();
        if column_founder.admit(column)? {
            pivot_factors.push(factor);
        }
        if pivot_factors.len() == source_rows {
            break;
        }
    }
    let rank = pivot_factors.len();
    if rank == 0 || rank > u32::MAX as usize {
        return Err(FactoredMomentError::ZeroImage);
    }
    let incidence_integral = pivot_factors
        .iter()
        .map(|pivot| {
            (0..factors)
                .map(|factor| {
                    (0..source_rows).fold(BigInt::ZERO, |sum, row| {
                        sum + &source_frame[row][*pivot]
                            * &source_weights[row]
                            * &source_frame[row][factor]
                    })
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let incidence = ExactRatMatrix::new(
        incidence_integral
            .iter()
            .map(|row| row.iter().cloned().map(Rat::from_integer).collect())
            .collect(),
    )?;
    let pivot_gram = ExactRatMatrix::new(
        incidence_integral
            .iter()
            .map(|row| {
                pivot_factors
                    .iter()
                    .map(|factor| Rat::from_integer(row[*factor].clone()))
                    .collect::<Vec<_>>()
            })
            .collect(),
    )?;
    let constitutive = pivot_gram.inverse()?;
    let pivot_frame = ExactRatMatrix::new(
        source_frame
            .iter()
            .map(|row| {
                pivot_factors
                    .iter()
                    .map(|factor| Rat::from_integer(row[*factor].clone()))
                    .collect::<Vec<_>>()
            })
            .collect(),
    )?;
    let source_to_image = pivot_frame.multiply(&constitutive)?;
    let source_constitutive = ExactRatMatrix::from_diagonal(
        source_weights
            .iter()
            .cloned()
            .map(Rat::from_integer)
            .collect(),
    )?;

    // The exact column-basis construction above already establishes that every source factor
    // column lies in `span(P)`.  Certify the reconstructed basis columns and constitutive pullback
    // here; the general reconstruction follows by linearity without replaying a dense
    // `source_rows × rank × factor_population` multiplication on every continuation.
    if source_to_image.multiply(&pivot_gram)? != pivot_frame
        || source_to_image
            .transpose()?
            .multiply(&source_constitutive)?
            .multiply(&source_to_image)?
            != constitutive
    {
        return Err(FactoredMomentError::Reconstruction);
    }

    let section = FactoredMomentSection {
        schema: "holonic-engine.factored-moment-section.v2".to_owned(),
        factor_population,
        image_rank: u32::try_from(rank).map_err(|_| FactoredMomentError::Shape)?,
        basis_factors: pivot_factors
            .into_iter()
            .map(|factor| u32::try_from(factor).map_err(|_| FactoredMomentError::Shape))
            .collect::<Result<_, _>>()?,
        incidence,
        constitutive,
    };
    section.validate_admitted()?;
    Ok(CanonicalizedMoment {
        section,
        source_to_image,
    })
}
