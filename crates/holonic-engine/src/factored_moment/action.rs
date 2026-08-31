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

impl SparseQuadraticMomentAction {
    /// Found the complete symmetric pair carrier without deriving its extent from an enumerated
    /// rank-one history.  This is the receiver-independent reference carrier for an ordered
    /// diagonal chronology.  A later proved receiver quotient may replace it with a smaller
    /// generator-biinvariant carrier while retaining the omitted pair fibre.
    pub fn complete_symmetric(
        factor_population: u32,
        generators: Vec<Vec<u32>>,
    ) -> Result<Self, FactoredMomentError> {
        if factor_population == 0
            || generators.is_empty()
            || generators.len() > u32::MAX as usize
            || generators.iter().any(|generator| {
                generator.len() != factor_population as usize
                    || generator.iter().any(|target| *target >= factor_population)
            })
        {
            return Err(FactoredMomentError::Shape);
        }
        let factors = factor_population as usize;
        let pair_population = factors
            .checked_mul(factors.checked_add(1).ok_or(FactoredMomentError::Shape)?)
            .and_then(|population| population.checked_div(2))
            .ok_or(FactoredMomentError::Shape)?;
        if pair_population > u32::MAX as usize {
            return Err(FactoredMomentError::Shape);
        }
        let mut pairs = Vec::with_capacity(pair_population);
        for left in 0..factor_population {
            for right in left..factor_population {
                pairs.push(SymmetricFactorPair { left, right });
            }
        }
        let pair_coordinate = |left: u32, right: u32| -> Result<u32, FactoredMomentError> {
            let (left, right) = if left <= right {
                (left as usize, right as usize)
            } else {
                (right as usize, left as usize)
            };
            let row = left
                .checked_mul(factors)
                .and_then(|value| {
                    left.checked_mul(left.saturating_sub(1))
                        .and_then(|triangle| value.checked_sub(triangle / 2))
                })
                .ok_or(FactoredMomentError::Shape)?;
            u32::try_from(
                row.checked_add(right.checked_sub(left).ok_or(FactoredMomentError::Shape)?)
                    .ok_or(FactoredMomentError::Shape)?,
            )
            .map_err(|_| FactoredMomentError::Shape)
        };
        let expected_action = generators
            .len()
            .checked_mul(pair_population)
            .ok_or(FactoredMomentError::Shape)?;
        let mut target_pair_coordinates = Vec::with_capacity(expected_action);
        let mut multiplicities = Vec::with_capacity(expected_action);
        for generator in &generators {
            for pair in &pairs {
                let target_left = generator[pair.left as usize];
                let target_right = generator[pair.right as usize];
                target_pair_coordinates.push(pair_coordinate(target_left, target_right)?);
                multiplicities
                    .push(u8::from(pair.left != pair.right && target_left == target_right) + 1);
            }
        }
        let action = Self {
            schema: "holonic-engine.sparse-quadratic-moment-action.v1".to_owned(),
            factor_population,
            generator_population: generators.len() as u32,
            pairs,
            generator_targets: generators,
            target_pair_coordinates,
            multiplicities,
        };
        action.validate()?;
        Ok(action)
    }

    /// Derive the least generator-closed symmetric pair carrier from the entering current support.
    /// Its extent is a consequence of incidence and admitted action, never a caller-supplied rank.
    pub(crate) fn found(
        factor_population: u32,
        family: &[WeightedIntegralCurrent],
        generators: &[Vec<u32>],
    ) -> Result<Self, FactoredMomentError> {
        if factor_population == 0
            || family.is_empty()
            || generators.is_empty()
            || generators.len() > u32::MAX as usize
            || generators.iter().any(|generator| {
                generator.len() != factor_population as usize
                    || generator.iter().any(|target| *target >= factor_population)
            })
        {
            return Err(FactoredMomentError::Shape);
        }

        let mut pair_set = BTreeSet::<SymmetricFactorPair>::new();
        for current in family {
            for (left_at, (left, _)) in current.entries.iter().enumerate() {
                for (right, _) in &current.entries[left_at..] {
                    pair_set.insert(SymmetricFactorPair::new(*left, *right));
                }
            }
        }
        if pair_set.is_empty() {
            return Err(FactoredMomentError::ZeroImage);
        }

        loop {
            let standing = pair_set.iter().copied().collect::<Vec<_>>();
            let mut changed = false;
            for pair in standing {
                for generator in generators {
                    changed |= pair_set.insert(SymmetricFactorPair::new(
                        generator[pair.left as usize],
                        generator[pair.right as usize],
                    ));
                }
            }
            if !changed {
                break;
            }
        }

        let pairs = pair_set.into_iter().collect::<Vec<_>>();
        let pair_coordinates = pairs
            .iter()
            .copied()
            .enumerate()
            .map(|(coordinate, pair)| (pair, coordinate as u32))
            .collect::<BTreeMap<_, _>>();
        let mut target_pair_coordinates = Vec::with_capacity(generators.len() * pairs.len());
        let mut multiplicities = Vec::with_capacity(generators.len() * pairs.len());
        for generator in generators {
            for pair in &pairs {
                let target_left = generator[pair.left as usize];
                let target_right = generator[pair.right as usize];
                let target = SymmetricFactorPair::new(target_left, target_right);
                target_pair_coordinates.push(
                    *pair_coordinates
                        .get(&target)
                        .ok_or(FactoredMomentError::Reconstruction)?,
                );
                multiplicities
                    .push(u8::from(pair.left != pair.right && target_left == target_right) + 1);
            }
        }

        let action = Self {
            schema: "holonic-engine.sparse-quadratic-moment-action.v1".to_owned(),
            factor_population,
            generator_population: u32::try_from(generators.len())
                .map_err(|_| FactoredMomentError::Shape)?,
            pairs,
            generator_targets: generators.to_vec(),
            target_pair_coordinates,
            multiplicities,
        };
        action.validate()?;
        Ok(action)
    }

    pub fn validate(&self) -> Result<(), FactoredMomentError> {
        let pair_population = self.pairs.len();
        let expected_action = (self.generator_population as usize)
            .checked_mul(pair_population)
            .ok_or(FactoredMomentError::Shape)?;
        if self.schema != "holonic-engine.sparse-quadratic-moment-action.v1"
            || self.factor_population == 0
            || self.generator_population == 0
            || pair_population == 0
            || self.pairs.windows(2).any(|pair| pair[0] >= pair[1])
            || self
                .pairs
                .iter()
                .any(|pair| pair.left > pair.right || pair.right >= self.factor_population)
            || self.generator_targets.len() != self.generator_population as usize
            || self.generator_targets.iter().any(|generator| {
                generator.len() != self.factor_population as usize
                    || generator
                        .iter()
                        .any(|target| *target >= self.factor_population)
            })
            || self.target_pair_coordinates.len() != expected_action
            || self.multiplicities.len() != expected_action
            || self
                .target_pair_coordinates
                .iter()
                .any(|target| *target as usize >= pair_population)
            || self
                .multiplicities
                .iter()
                .any(|multiplicity| !matches!(multiplicity, 1 | 2))
        {
            return Err(FactoredMomentError::Shape);
        }

        for (generator_at, generator) in self.generator_targets.iter().enumerate() {
            for (source_at, pair) in self.pairs.iter().enumerate() {
                let left = generator[pair.left as usize];
                let right = generator[pair.right as usize];
                let target = SymmetricFactorPair::new(left, right);
                let action_at = generator_at * pair_population + source_at;
                let stored = self
                    .pairs
                    .get(self.target_pair_coordinates[action_at] as usize)
                    .ok_or(FactoredMomentError::Shape)?;
                let multiplicity = u8::from(pair.left != pair.right && left == right) + 1;
                if stored != &target || self.multiplicities[action_at] != multiplicity {
                    return Err(FactoredMomentError::Reconstruction);
                }
            }
        }
        Ok(())
    }
}
