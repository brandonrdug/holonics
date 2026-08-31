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

impl FactoredConstitutiveSpine {
    /// Found the rooted chart at one admitted section.  No matrix is duplicated in a resident
    /// realization: this apparatus-neutral value specifies the equality which distinct execution
    /// axes must reconstruct.
    pub fn found(section: &FactoredMomentSection) -> Result<Self, FactoredMomentError> {
        section.validate_admitted()?;
        Ok(Self {
            schema: "holonic-engine.factored-constitutive-spine.v1".to_owned(),
            factor_population: section.factor_population,
            root_rank: section.image_rank,
            history_population: 1,
            root_constitutive: section.constitutive.clone(),
            effective_incidence: section.incidence.clone(),
            history_weights: vec![BigUint::one()],
            reconstruction_fibre: Vec::new(),
        })
    }

    fn validate(&self) -> Result<(), FactoredMomentError> {
        let root_rank = self.root_rank as usize;
        let histories = self.history_population as usize;
        let rows = root_rank
            .checked_mul(histories)
            .ok_or(FactoredMomentError::Shape)?;
        if self.schema != "holonic-engine.factored-constitutive-spine.v1"
            || root_rank == 0
            || histories == 0
            || self.factor_population == 0
            || self.root_constitutive.rows() != root_rank
            || self.root_constitutive.columns() != root_rank
            || self.root_constitutive.transpose()? != self.root_constitutive
            || self.effective_incidence.rows() != rows
            || self.effective_incidence.columns() != self.factor_population as usize
            || self.history_weights.len() != histories
            || self.history_weights.iter().any(BigUint::is_zero)
        {
            return Err(FactoredMomentError::Shape);
        }
        Ok(())
    }

    /// Append one plural generator front to every addressed history.  Row order is
    /// `(generator, prior_history, root_coordinate)` and is therefore the complete joining
    /// population rather than an enumerated semantic word table.
    pub fn transport_direct_sum(
        &self,
        generators: &[Vec<u32>],
    ) -> Result<Self, FactoredMomentError> {
        self.validate()?;
        let factors = self.factor_population as usize;
        if generators.is_empty()
            || generators.iter().any(|generator| {
                generator.len() != factors
                    || generator
                        .iter()
                        .any(|target| *target >= self.factor_population)
            })
        {
            return Err(FactoredMomentError::Shape);
        }
        let source_rows = self.effective_incidence.to_rows();
        let root_rank = self.root_rank as usize;
        let source_histories = self.history_population as usize;
        let presented_history_population = source_histories
            .checked_mul(generators.len())
            .ok_or(FactoredMomentError::Shape)?;
        let mut distinct_blocks = Vec::<Vec<Vec<Rat>>>::new();
        let mut history_weights = Vec::<BigUint>::new();
        let mut candidate_to_target = Vec::<u32>::with_capacity(presented_history_population);
        for generator in generators {
            for source_history in 0..source_histories {
                let mut block = Vec::with_capacity(root_rank);
                for source in
                    &source_rows[source_history * root_rank..(source_history + 1) * root_rank]
                {
                    let mut target = vec![Rat::zero(); factors];
                    for (source_factor, target_factor) in generator.iter().enumerate() {
                        target[*target_factor as usize] += &source[source_factor];
                    }
                    block.push(target);
                }
                let target_history = distinct_blocks
                    .iter()
                    .position(|standing| standing == &block)
                    .unwrap_or_else(|| {
                        distinct_blocks.push(block);
                        history_weights.push(BigUint::zero());
                        distinct_blocks.len() - 1
                    });
                history_weights[target_history] += &self.history_weights[source_history];
                candidate_to_target.push(
                    u32::try_from(target_history).expect("bounded by presented history population"),
                );
            }
        }
        let history_population =
            u32::try_from(distinct_blocks.len()).map_err(|_| FactoredMomentError::Shape)?;
        let mut reconstruction_fibre = self.reconstruction_fibre.clone();
        reconstruction_fibre.push(FactoredHistoryQuotientPassage {
            source_history_population: self.history_population,
            generator_population: u32::try_from(generators.len())
                .map_err(|_| FactoredMomentError::Shape)?,
            presented_history_population: u32::try_from(presented_history_population)
                .map_err(|_| FactoredMomentError::Shape)?,
            target_history_population: history_population,
            candidate_to_target,
        });
        let returned = Self {
            schema: self.schema.clone(),
            factor_population: self.factor_population,
            root_rank: self.root_rank,
            history_population,
            root_constitutive: self.root_constitutive.clone(),
            effective_incidence: ExactRatMatrix::new(
                distinct_blocks.into_iter().flatten().collect(),
            )?,
            history_weights,
            reconstruction_fibre,
        };
        returned.validate()?;
        Ok(returned)
    }

    /// Reconstruct the complete moment through the addressed direct sum of the root constitutive
    /// form.  This is a cold equality witness and is never the resident production allocation.
    pub fn reconstruct_moment(&self) -> Result<ExactRatMatrix, FactoredMomentError> {
        self.validate()?;
        let root_rank = self.root_rank as usize;
        let rows = self.effective_incidence.rows();
        let direct_sum = ExactRatMatrix::new(
            (0..rows)
                .map(|left| {
                    (0..rows)
                        .map(|right| {
                            let history = left / root_rank;
                            if history == right / root_rank {
                                Rat::from_integer(BigInt::from(
                                    self.history_weights[history].clone(),
                                )) * self
                                    .root_constitutive
                                    .get(left % root_rank, right % root_rank)
                                    .cloned()
                                    .expect("validated root coordinate")
                            } else {
                                Rat::zero()
                            }
                        })
                        .collect::<Vec<_>>()
                })
                .collect(),
        )?;
        Ok(self
            .effective_incidence
            .transpose()?
            .multiply(&direct_sum)?
            .multiply(&self.effective_incidence)?)
    }

    /// The rooted productive chart and compact reconstruction chart return the same complete
    /// moment without identifying their row addresses or stored fibres.
    pub fn agrees_with(
        &self,
        section: &FactoredMomentSection,
    ) -> Result<bool, FactoredMomentError> {
        section.validate_admitted()?;
        if section.factor_population != self.factor_population {
            return Err(FactoredMomentError::Shape);
        }
        let compact = section
            .incidence
            .transpose()?
            .multiply(&section.constitutive)?
            .multiply(&section.incidence)?;
        Ok(self.reconstruct_moment()? == compact)
    }
}
