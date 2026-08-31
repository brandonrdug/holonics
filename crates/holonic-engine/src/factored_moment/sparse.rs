#![allow(unused_imports)]

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use super::*;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::receiver_history_compression::{
    AddressedFactoredIntegralReceiverComplex, FactoredIntegralReceiverForm,
    SparseIntegralFunctional,
};

impl SparseQuadraticMomentFoundation {
    pub fn found(
        factor_population: u32,
        family: Vec<WeightedIntegralCurrent>,
        generators: Vec<Vec<u32>>,
    ) -> Result<Self, FactoredMomentError> {
        if family.is_empty()
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
        let action = SparseQuadraticMomentAction::found(factor_population, &family, &generators)?;
        let pair_coordinates = action
            .pairs
            .iter()
            .copied()
            .enumerate()
            .map(|(coordinate, pair)| (pair, coordinate))
            .collect::<BTreeMap<_, _>>();
        let mut coefficients = vec![BigUint::zero(); action.pairs.len()];
        for current in &family {
            for (left_at, (left, left_coefficient)) in current.entries.iter().enumerate() {
                for (right, right_coefficient) in &current.entries[left_at..] {
                    let coordinate = *pair_coordinates
                        .get(&SymmetricFactorPair::new(*left, *right))
                        .ok_or(FactoredMomentError::Reconstruction)?;
                    coefficients[coordinate] +=
                        &current.weight * left_coefficient * right_coefficient;
                }
            }
        }
        let section = SparseQuadraticMomentSection {
            schema: "holonic-engine.sparse-quadratic-moment-section.v1".to_owned(),
            factor_population,
            generation: 0,
            pairs: action.pairs.clone(),
            coefficients,
        };
        section.validate()?;
        Ok(Self {
            schema: "holonic-engine.sparse-quadratic-moment-foundation.v1".to_owned(),
            action,
            section,
            reconstruction_fibre: family,
        })
    }
}

impl SparseQuadraticMomentSection {
    /// Integrate a diagonal chronology without enumerating its live suffix family.  For one pair
    /// coordinate `(i,j)`, if `d_t` is the current crossing at order `t`, the live suffix moment
    /// and the accumulated history obey
    ///
    /// `C_t(i,j) = d_t(i)d_t(j)(C_(t-1)(i,j) + 1)` and
    /// `Q_t(i,j) = Q_(t-1)(i,j) + C_t(i,j)`.
    ///
    /// This method is the apparatus-neutral exact reference.  Production enacts the same
    /// pair-independent recurrence on the resident card.
    pub fn from_diagonal_chronology(
        action: &SparseQuadraticMomentAction,
        chronology: &[AddressedDiagonalCurrentStep],
    ) -> Result<Self, FactoredMomentError> {
        action.validate()?;
        if chronology.is_empty()
            || chronology.iter().any(|step| {
                step.entries.is_empty()
                    || step.entries.windows(2).any(|pair| pair[0].0 >= pair[1].0)
                    || step.entries.iter().any(|(factor, coefficient)| {
                        *factor >= action.factor_population || coefficient.is_zero()
                    })
            })
            || chronology
                .windows(2)
                .any(|pair| pair[0].target_state != pair[1].source_state)
        {
            return Err(FactoredMomentError::Shape);
        }
        let factors = action.factor_population as usize;
        let mut standing = vec![BigUint::zero(); action.pairs.len()];
        let mut accumulated = vec![BigUint::zero(); action.pairs.len()];
        let mut diagonal = vec![BigUint::zero(); factors];
        for step in chronology {
            diagonal.fill(BigUint::zero());
            for (factor, coefficient) in &step.entries {
                diagonal[*factor as usize] = coefficient.clone();
            }
            for (coordinate, pair) in action.pairs.iter().enumerate() {
                let scale = &diagonal[pair.left as usize] * &diagonal[pair.right as usize];
                if scale.is_zero() {
                    standing[coordinate] = BigUint::zero();
                } else {
                    standing[coordinate] = scale * (&standing[coordinate] + BigUint::one());
                }
                accumulated[coordinate] += &standing[coordinate];
            }
        }
        let section = Self {
            schema: "holonic-engine.sparse-quadratic-moment-section.v1".to_owned(),
            factor_population: action.factor_population,
            generation: 0,
            pairs: action.pairs.clone(),
            coefficients: accumulated,
        };
        section.validate()?;
        Ok(section)
    }

    pub fn validate(&self) -> Result<(), FactoredMomentError> {
        if self.schema != "holonic-engine.sparse-quadratic-moment-section.v1"
            || self.factor_population == 0
            || self.pairs.is_empty()
            || self.pairs.len() != self.coefficients.len()
            || self.pairs.windows(2).any(|pair| pair[0] >= pair[1])
            || self
                .pairs
                .iter()
                .any(|pair| pair.left > pair.right || pair.right >= self.factor_population)
        {
            return Err(FactoredMomentError::Shape);
        }
        Ok(())
    }

    /// Apply the complete plural-generator front.  Generator branches are summed only at this
    /// declared direct-sum receiver; no cross-generator quadratic terms are introduced.
    pub fn transport_direct_sum(
        &self,
        action: &SparseQuadraticMomentAction,
    ) -> Result<Self, FactoredMomentError> {
        self.validate()?;
        action.validate()?;
        if self.factor_population != action.factor_population || self.pairs != action.pairs {
            return Err(FactoredMomentError::Shape);
        }
        let pair_population = self.pairs.len();
        let mut coefficients = vec![BigUint::zero(); pair_population];
        for generator_at in 0..action.generator_population as usize {
            for source_at in 0..pair_population {
                let action_at = generator_at * pair_population + source_at;
                let target = action.target_pair_coordinates[action_at] as usize;
                coefficients[target] +=
                    &self.coefficients[source_at] * BigUint::from(action.multiplicities[action_at]);
            }
        }
        let returned = Self {
            schema: self.schema.clone(),
            factor_population: self.factor_population,
            generation: self
                .generation
                .checked_add(1)
                .ok_or(FactoredMomentError::Shape)?,
            pairs: self.pairs.clone(),
            coefficients,
        };
        returned.validate()?;
        Ok(returned)
    }

    /// Apply one returned boundary restriction to both legs of the already-transported moment.
    /// If `r` is the exact factor-current section carried by the returned membrane face, this is
    /// the diagonal constitutive action
    ///
    /// ```text
    /// C_next = diag(r) C_transported diag(r).
    /// ```
    ///
    /// It is the quadratic image of the standing granular law which intersects two local factor
    /// currents coordinatewise.  The pair carrier and causal generation do not change: this is
    /// the returned interaction at that generation, not another generator step.  Missing factors
    /// are exact zero incidence, and a restriction which annihilates the whole current returns an
    /// obstruction rather than an arbitrary successor.
    pub fn condition_by_diagonal_restriction(
        &self,
        restriction: &[(u32, BigUint)],
    ) -> Result<Self, FactoredMomentError> {
        self.validate()?;
        if restriction.is_empty()
            || restriction.windows(2).any(|pair| pair[0].0 >= pair[1].0)
            || restriction.iter().any(|(factor, coefficient)| {
                *factor >= self.factor_population || coefficient.is_zero()
            })
        {
            return Err(FactoredMomentError::Shape);
        }
        let incidence = restriction.iter().cloned().collect::<BTreeMap<_, _>>();
        let coefficients = self
            .pairs
            .iter()
            .zip(&self.coefficients)
            .map(|(pair, coefficient)| {
                incidence
                    .get(&pair.left)
                    .zip(incidence.get(&pair.right))
                    .map(|(left, right)| coefficient * left * right)
                    .unwrap_or_else(BigUint::zero)
            })
            .collect::<Vec<_>>();
        if coefficients.iter().all(BigUint::is_zero) {
            return Err(FactoredMomentError::ZeroImage);
        }
        let returned = Self {
            schema: self.schema.clone(),
            factor_population: self.factor_population,
            generation: self.generation,
            pairs: self.pairs.clone(),
            coefficients,
        };
        returned.validate()?;
        Ok(returned)
    }

    pub fn coefficient(&self, left: u32, right: u32) -> Option<&BigUint> {
        self.pairs
            .binary_search(&SymmetricFactorPair::new(left, right))
            .ok()
            .and_then(|coordinate| self.coefficients.get(coordinate))
    }
}

impl SparseQuadraticPairReceiverFrame {
    /// Descend an addressed bilinear receiver complex directly onto a fixed native pair carrier.
    /// Iterating the two sparse functional supports supplies the off-diagonal symmetric sum; no
    /// ambient matrix, inverse, or chosen receiver rank is constructed.
    pub fn found(
        action: &SparseQuadraticMomentAction,
        complex: &AddressedFactoredIntegralReceiverComplex,
    ) -> Result<Self, FactoredMomentError> {
        action.validate()?;
        if complex.factor_population != action.factor_population {
            return Err(FactoredMomentError::Shape);
        }
        let forms = complex
            .reopen_receiver_forms()
            .map_err(|_| FactoredMomentError::Shape)?;
        let pair_coordinates = action
            .pairs
            .iter()
            .copied()
            .enumerate()
            .map(|(coordinate, pair)| (pair, coordinate as u32))
            .collect::<BTreeMap<_, _>>();
        let mut receiver_term_offsets = Vec::with_capacity(forms.len() + 1);
        let mut terms = Vec::new();
        receiver_term_offsets.push(0);
        for receiver in forms {
            let mut contracted = BTreeMap::<u32, BigInt>::new();
            for term in receiver.terms {
                for left in &term.left.entries {
                    for right in &term.right.entries {
                        let pair = SymmetricFactorPair::new(left.factor, right.factor);
                        let Some(coordinate) = pair_coordinates.get(&pair) else {
                            continue;
                        };
                        *contracted.entry(*coordinate).or_default() +=
                            &term.coefficient * &left.coefficient * &right.coefficient;
                    }
                }
            }
            terms.extend(
                contracted
                    .into_iter()
                    .filter_map(|(pair_coordinate, coefficient)| {
                        (!coefficient.is_zero()).then_some(SparseQuadraticPairReceiverTerm {
                            pair_coordinate,
                            coefficient,
                        })
                    }),
            );
            receiver_term_offsets
                .push(u64::try_from(terms.len()).map_err(|_| FactoredMomentError::Shape)?);
        }
        Ok(Self {
            schema: "holonic-engine.sparse-quadratic-pair-receiver-frame.v1".to_owned(),
            factor_population: action.factor_population,
            pair_population: u32::try_from(action.pairs.len())
                .map_err(|_| FactoredMomentError::Shape)?,
            receiver_population: u32::try_from(receiver_term_offsets.len() - 1)
                .map_err(|_| FactoredMomentError::Shape)?,
            receiver_term_offsets,
            terms,
        })
    }

    pub fn contract(
        &self,
        section: &SparseQuadraticMomentSection,
    ) -> Result<Vec<BigInt>, FactoredMomentError> {
        section.validate()?;
        if self.schema != "holonic-engine.sparse-quadratic-pair-receiver-frame.v1"
            || self.factor_population != section.factor_population
            || self.pair_population as usize != section.pairs.len()
            || self.receiver_term_offsets.len() != self.receiver_population as usize + 1
            || self.receiver_term_offsets.first() != Some(&0)
            || self.receiver_term_offsets.last().copied() != Some(self.terms.len() as u64)
            || self
                .receiver_term_offsets
                .windows(2)
                .any(|offsets| offsets[0] > offsets[1])
            || self
                .terms
                .iter()
                .any(|term| term.pair_coordinate >= self.pair_population)
        {
            return Err(FactoredMomentError::Shape);
        }
        (0..self.receiver_population as usize)
            .map(|receiver| {
                let start = self.receiver_term_offsets[receiver] as usize;
                let end = self.receiver_term_offsets[receiver + 1] as usize;
                Ok(self.terms[start..end]
                    .iter()
                    .fold(BigInt::zero(), |sum, term| {
                        sum + &term.coefficient
                            * BigInt::from(
                                section.coefficients[term.pair_coordinate as usize].clone(),
                            )
                    }))
            })
            .collect()
    }
}
