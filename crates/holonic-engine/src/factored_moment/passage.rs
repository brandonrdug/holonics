#![allow(unused_imports)]

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::*;

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
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::receiver_history_compression::{
    AddressedFactoredIntegralReceiverComplex, FactoredIntegralReceiverForm,
    SparseIntegralFunctional,
};

impl FactoredMomentPassage {
    /// Found one complete apparatus-neutral image passage.  The constructor returns only after
    /// the transported incidence and the pulled constitutive form commute through the exact
    /// source-image to target-image boundary map.
    pub(crate) fn found(
        source: FactoredMomentSection,
        generator_targets: Vec<Vec<u32>>,
        generator_source_to_target_image: ExactRatMatrix,
        target: FactoredMomentSection,
    ) -> Result<Self, FactoredMomentError> {
        source.validate_admitted()?;
        target.validate_admitted()?;
        let factors = source.factor_population as usize;
        let source_rank = source.image_rank as usize;
        let target_rank = target.image_rank as usize;
        if target.factor_population != source.factor_population
            || generator_targets.is_empty()
            || generator_targets.len() > u32::MAX as usize
            || generator_targets.iter().any(|generator| {
                generator.len() != factors
                    || generator
                        .iter()
                        .any(|factor| *factor >= source.factor_population)
            })
            || generator_source_to_target_image.rows()
                != generator_targets.len().saturating_mul(source_rank)
            || generator_source_to_target_image.columns() != target_rank
        {
            return Err(FactoredMomentError::Shape);
        }

        let transported_incidence = ExactRatMatrix::new(
            generator_targets
                .iter()
                .flat_map(|generator| {
                    source.incidence.to_rows().into_iter().map(|source_row| {
                        let mut target_row = vec![Rat::zero(); factors];
                        for (source_factor, target_factor) in generator.iter().copied().enumerate()
                        {
                            target_row[target_factor as usize] += source_row[source_factor].clone();
                        }
                        target_row
                    })
                })
                .collect(),
        )?;
        if generator_source_to_target_image.multiply(&target.incidence)? != transported_incidence {
            return Err(FactoredMomentError::Reconstruction);
        }

        let source_constitutive = source.constitutive.to_rows();
        let mut plural_constitutive = vec![
            vec![Rat::zero(); generator_targets.len() * source_rank];
            generator_targets.len() * source_rank
        ];
        for generator in 0..generator_targets.len() {
            for row in 0..source_rank {
                for column in 0..source_rank {
                    plural_constitutive[generator * source_rank + row]
                        [generator * source_rank + column] =
                        source_constitutive[row][column].clone();
                }
            }
        }
        let plural_constitutive = ExactRatMatrix::new(plural_constitutive)?;
        if generator_source_to_target_image
            .transpose()?
            .multiply(&plural_constitutive)?
            .multiply(&generator_source_to_target_image)?
            != target.constitutive
        {
            return Err(FactoredMomentError::Reconstruction);
        }

        Ok(Self {
            schema: "holonic-engine.factored-moment-passage.v1".to_owned(),
            factor_population: source.factor_population,
            generator_population: u32::try_from(generator_targets.len())
                .map_err(|_| FactoredMomentError::Shape)?,
            source_image_rank: source.image_rank,
            target_image_rank: target.image_rank,
            source,
            generator_targets,
            generator_source_to_target_image,
            target,
        })
    }

    /// Revalidate an exterior or remounted passage against the complete source, generator,
    /// target, incidence-factorization, and constitutive-pullback laws.
    pub fn validate(&self) -> Result<(), FactoredMomentError> {
        let rebuilt = Self::found(
            self.source.clone(),
            self.generator_targets.clone(),
            self.generator_source_to_target_image.clone(),
            self.target.clone(),
        )?;
        if &rebuilt != self {
            return Err(FactoredMomentError::Reconstruction);
        }
        Ok(())
    }
}

impl FactoredMomentSection {
    /// Contract one factored receiver directly against `Bᵀ K⁻¹ B`.
    pub fn contract_receiver(
        &self,
        receiver: &FactoredIntegralReceiverForm,
    ) -> Result<Rat, FactoredMomentError> {
        self.validate_admitted()?;
        self.contract_admitted_receiver(receiver)
    }

    /// Contract through a section returned directly by [`Self::found`] or
    /// [`Self::transport_direct_sum`].  Those constructors already returned the two-sided
    /// constitutive certificate; a continuing receiver must not replay its cubic validation for
    /// every observation.  Serialized exterior sections must pass [`Self::contract_receiver`]
    /// or be remounted through a validating owner first.
    pub fn contract_admitted_receiver(
        &self,
        receiver: &FactoredIntegralReceiverForm,
    ) -> Result<Rat, FactoredMomentError> {
        if receiver.factor_population != self.factor_population {
            return Err(FactoredMomentError::Shape);
        }
        receiver.terms.iter().try_fold(Rat::zero(), |sum, term| {
            let left = self.read_functional_admitted(&term.left)?;
            let right = self.read_functional_admitted(&term.right)?;
            let acted = self.constitutive.apply(&right)?;
            let paired = left
                .iter()
                .zip(acted)
                .fold(Rat::zero(), |held, (left, right)| held + left * right);
            Ok(sum + Rat::from_integer(term.coefficient.clone()) * paired)
        })
    }

    pub fn contract_receivers(
        &self,
        receivers: &[FactoredIntegralReceiverForm],
    ) -> Result<Vec<Rat>, FactoredMomentError> {
        self.validate_admitted()?;
        self.contract_admitted_receivers(receivers)
    }

    /// Batch counterpart of [`Self::contract_admitted_receiver`].
    pub fn contract_admitted_receivers(
        &self,
        receivers: &[FactoredIntegralReceiverForm],
    ) -> Result<Vec<Rat>, FactoredMomentError> {
        if receivers
            .iter()
            .any(|receiver| receiver.factor_population != self.factor_population)
        {
            return Err(FactoredMomentError::Shape);
        }
        let mut functional_addresses = HashMap::<&SparseIntegralFunctional, usize>::new();
        let mut functionals = Vec::<&SparseIntegralFunctional>::new();
        for functional in receivers.iter().flat_map(|receiver| {
            receiver
                .terms
                .iter()
                .flat_map(|term| [&term.left, &term.right])
        }) {
            if functional_addresses.contains_key(functional) {
                continue;
            }
            let address = functionals.len();
            functional_addresses.insert(functional, address);
            functionals.push(functional);
        }
        let incidence_denominator = self
            .incidence
            .entries()
            .iter()
            .fold(BigInt::one(), |held, entry| {
                exact_bigint_lcm(held, entry.denom().clone())
            });
        let integral_incidence = self
            .incidence
            .to_rows()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|entry| entry.numer() * (&incidence_denominator / entry.denom()))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let readings = functionals
            .iter()
            .map(|functional| {
                integral_incidence
                    .iter()
                    .map(|row| {
                        functional
                            .entries
                            .iter()
                            .try_fold(BigInt::ZERO, |sum, entry| {
                                row.get(entry.factor as usize)
                                    .map(|value| sum + &entry.coefficient * value)
                                    .ok_or(FactoredMomentError::Shape)
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?;
        let constitutive_denominator = self
            .constitutive
            .entries()
            .iter()
            .fold(BigInt::one(), |held, entry| {
                exact_bigint_lcm(held, entry.denom().clone())
            });
        let integral_constitutive = self
            .constitutive
            .to_rows()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|entry| entry.numer() * (&constitutive_denominator / entry.denom()))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let acted = readings
            .iter()
            .map(|reading| {
                integral_constitutive
                    .iter()
                    .map(|row| {
                        row.iter()
                            .zip(reading)
                            .fold(BigInt::ZERO, |sum, (operator, current)| {
                                sum + operator * current
                            })
                    })
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let common_denominator =
            &incidence_denominator * &incidence_denominator * &constitutive_denominator;
        receivers
            .iter()
            .map(|receiver| {
                let numerator = receiver.terms.iter().try_fold(BigInt::ZERO, |sum, term| {
                    let left = functional_addresses
                        .get(&term.left)
                        .copied()
                        .ok_or(FactoredMomentError::Shape)?;
                    let right = functional_addresses
                        .get(&term.right)
                        .copied()
                        .ok_or(FactoredMomentError::Shape)?;
                    let paired = readings[left]
                        .iter()
                        .zip(&acted[right])
                        .fold(BigInt::ZERO, |held, (left, right)| held + left * right);
                    Ok::<BigInt, FactoredMomentError>(sum + &term.coefficient * paired)
                })?;
                Ok(Rat::new(numerator, common_denominator.clone()))
            })
            .collect()
    }

    /// Read one ambient covariance entry without materializing the ambient field.
    pub fn reconstruct_entry(&self, left: u32, right: u32) -> Result<Rat, FactoredMomentError> {
        self.validate_admitted()?;
        if left >= self.factor_population || right >= self.factor_population {
            return Err(FactoredMomentError::Shape);
        }
        let left = (0..self.image_rank as usize)
            .map(|row| self.incidence.get(row, left as usize).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let right = (0..self.image_rank as usize)
            .map(|row| self.incidence.get(row, right as usize).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        let acted = self.constitutive.apply(&right)?;
        Ok(left
            .iter()
            .zip(acted)
            .fold(Rat::zero(), |sum, (left, right)| sum + left * right))
    }
}
