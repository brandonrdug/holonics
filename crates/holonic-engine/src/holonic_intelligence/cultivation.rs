use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::generator_native_rest::GeneratorNativeRest;
use crate::native_ecology::recurrent::BoundaryDecoder;
use crate::native_ecology::recurrent_return::{
    ExteriorToolReturn, LocalGeneratorDelta, RecurrentReturnRefusal, RecurrentSemanticWork,
    ReturnCommitEvent, ReturnedCausalAdjoint, ReturnedRecurrentRest, RevisitHolonomy,
    action_matrix, local_delta, next, recurrence_trace, semantic_work,
};
use crate::receiver_exact_compression::InputId;
use crate::receiver_history_compression::NativeStateId;

/// Material crossing without a durable morphology claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exposure<Material>(pub Material);

/// Separately retained testimony consulted without changing the native rest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceConsultation<Testimony>(pub Testimony);

/// Contemporary standing mounted for one inference circulation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MountedStanding<Standing>(pub Standing);

/// A genuinely later return proposed as durable morphology.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedCultivation<Returned>(pub Returned);

/// A complete returned difference and one later scalar or coarse receiver face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompleteReturnedDifference<Complete, Loss> {
    pub complete: Complete,
    pub loss: Loss,
}

/// Equal scalar/coarse loss cannot identify two complete returned differences it separates.
pub fn equal_loss_different_return<Complete: PartialEq, Loss: PartialEq>(
    left: &CompleteReturnedDifference<Complete, Loss>,
    right: &CompleteReturnedDifference<Complete, Loss>,
) -> bool {
    left.loss == right.loss && left.complete != right.complete
}

const SOURCE_DETACHED_CULTIVATION_SCHEMA: &str =
    "holonic-engine.source-detached-cultivated-recurrence.v1";

/// Cold occurrence, codec, and world-return testimony removed from productive native conduct.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ColdCultivationWitness {
    pub predecessor_identity: String,
    pub entering_occurrence: String,
    pub exterior: ExteriorToolReturn,
    pub decision: ReturnCommitEvent,
    pub decoder: Vec<BoundaryDecoder>,
}

/// Productive cultivated recurrence after exterior testimony has physically departed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceDetachedCultivatedRecurrence {
    schema: String,
    base: GeneratorNativeRest,
    delta: LocalGeneratorDelta,
    causal_adjoint: ReturnedCausalAdjoint,
    holonomy: RevisitHolonomy,
    recurrence_starts: Vec<NativeStateId>,
    main_start: NativeStateId,
    held_out_start: NativeStateId,
    control_from: NativeStateId,
    semantic_work: RecurrentSemanticWork,
    open_fibres: Vec<String>,
}

/// Exterior chronology retained beside, never inside, the productive cultivated recurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceNeutralReturnWitness {
    pub emitted_occurrence: String,
    pub returned_occurrence: String,
    pub returned_content: u64,
}

/// The physically separated return of one direct source-neutral cultivation.
#[derive(Debug, PartialEq, Eq)]
pub struct SourceNeutralCultivationClosure {
    pub productive: SourceDetachedCultivatedRecurrence,
    pub exterior: SourceNeutralReturnWitness,
}

impl ReturnedRecurrentRest {
    /// Consume the boundary passage and physically split cold testimony from productive hexis.
    pub fn depart_source(
        self,
    ) -> Result<
        (SourceDetachedCultivatedRecurrence, ColdCultivationWitness),
        CultivationPackagingError,
    > {
        self.canonical_bytes()?;
        let productive = SourceDetachedCultivatedRecurrence {
            schema: SOURCE_DETACHED_CULTIVATION_SCHEMA.to_owned(),
            base: self.base,
            delta: self.delta,
            causal_adjoint: self.causal_adjoint,
            holonomy: self.holonomy,
            recurrence_starts: self.recurrence_starts,
            main_start: self.main_start,
            held_out_start: self.held_out_start,
            control_from: self.control_from,
            semantic_work: self.semantic_work_prediction,
            open_fibres: self.open_fibres,
        };
        productive.validate()?;
        Ok((
            productive,
            ColdCultivationWitness {
                predecessor_identity: self.predecessor_sha256,
                entering_occurrence: self.entering_occurrence,
                exterior: self.exterior,
                decision: self.decision,
                decoder: self.decoder,
            },
        ))
    }
}

impl SourceDetachedCultivatedRecurrence {
    /// Found productive hexis directly from one total native recurrence and an actual later
    /// exterior return. No decoder, source surface, predecessor output file, or foreign executor
    /// enters the productive value.
    pub fn found_from_native_return(
        base: GeneratorNativeRest,
        generator: InputId,
        forward_lineage: Vec<NativeStateId>,
        emitted_occurrence: String,
        returned_occurrence: String,
        returned_content: u64,
    ) -> Result<SourceNeutralCultivationClosure, CultivationPackagingError> {
        base.validate()
            .map_err(|error| CultivationPackagingError::Native(error.to_string()))?;
        if emitted_occurrence.is_empty()
            || returned_occurrence.is_empty()
            || emitted_occurrence == returned_occurrence
            || returned_content == 0
            || forward_lineage.len() < 3
        {
            return Err(CultivationPackagingError::Malformed);
        }
        for pair in forward_lineage.windows(2) {
            if next(&base, generator, pair[0], None)? != pair[1] {
                return Err(CultivationPackagingError::Malformed);
            }
        }
        let predecessor_to = *forward_lineage
            .last()
            .ok_or(CultivationPackagingError::Malformed)?;
        if !forward_lineage[..forward_lineage.len() - 1].contains(&predecessor_to) {
            return Err(CultivationPackagingError::Malformed);
        }
        let from = forward_lineage[forward_lineage.len() - 2];
        if from == predecessor_to {
            return Err(CultivationPackagingError::Malformed);
        }
        let successor_to = from;
        let dimension = base.native_population.len();
        let (delta, left_factor, right_factor) =
            local_delta(dimension, from, predecessor_to, successor_to)?;
        let predecessor_action = action_matrix(&base, generator)?;
        let successor_action = predecessor_action.add(&delta)?;
        let receiver_metric = ExactRatMatrix::identity(dimension)?;
        let metric_adjoint = delta.metric_adjoint(&receiver_metric, &receiver_metric)?;
        if metric_adjoint != delta.transpose()? || delta.rank()? != 1 {
            return Err(CultivationPackagingError::Malformed);
        }
        let commutator = predecessor_action
            .multiply(&delta)?
            .subtract(&delta.multiply(&predecessor_action)?)?;
        let commutator_rank = commutator.rank()?;
        if commutator_rank == 0 {
            return Err(CultivationPackagingError::Malformed);
        }
        let recurrence_starts = base.native_population.clone();
        let main_start = forward_lineage[0];
        let held_out_start = recurrence_starts
            .iter()
            .copied()
            .filter(|state| *state != main_start)
            .find(|state| {
                recurrence_trace(&base, generator, *state, None)
                    != recurrence_trace(&base, generator, *state, Some((from, successor_to)))
            })
            .ok_or(CultivationPackagingError::Malformed)?;
        let control_from = recurrence_starts
            .iter()
            .copied()
            .find(|state| {
                *state != from
                    && next(&base, generator, *state, None)
                        == next(&base, generator, *state, Some((from, successor_to)))
            })
            .ok_or(CultivationPackagingError::Malformed)?;
        let semantic_work =
            semantic_work(&base, generator, &recurrence_starts, (from, successor_to))?;
        let productive = Self {
            schema: SOURCE_DETACHED_CULTIVATION_SCHEMA.to_owned(),
            base,
            delta: LocalGeneratorDelta {
                generator,
                from,
                predecessor_to,
                successor_to,
                left_factor,
                right_factor,
                delta: delta.clone(),
            },
            causal_adjoint: ReturnedCausalAdjoint {
                forward_lineage: forward_lineage.clone(),
                return_lineage: forward_lineage.iter().copied().rev().collect(),
                receiver_metric,
                metric_adjoint,
                measured_delta_rank: 1,
                returned_content,
                primitive_orientation: 1,
            },
            holonomy: RevisitHolonomy {
                predecessor_action,
                successor_action,
                commutator,
                commutator_rank,
            },
            recurrence_starts,
            main_start,
            held_out_start,
            control_from,
            semantic_work,
            open_fibres: vec![
                "receiver families outside the admitted native recurrence remain open".to_owned(),
            ],
        };
        productive.validate()?;
        Ok(SourceNeutralCultivationClosure {
            productive,
            exterior: SourceNeutralReturnWitness {
                emitted_occurrence,
                returned_occurrence,
                returned_content,
            },
        })
    }

    pub fn read(bytes: &[u8]) -> Result<Self, CultivationPackagingError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| CultivationPackagingError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, CultivationPackagingError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| CultivationPackagingError::Wire(error.to_string()))
    }

    pub fn predecessor_trace(
        &self,
        start: NativeStateId,
    ) -> Result<Vec<NativeStateId>, CultivationPackagingError> {
        Ok(recurrence_trace(
            &self.base,
            self.delta.generator,
            start,
            None,
        )?)
    }

    pub fn predecessor_step(
        &self,
        start: NativeStateId,
    ) -> Result<NativeStateId, CultivationPackagingError> {
        Ok(crate::native_ecology::recurrent_return::next(
            &self.base,
            self.delta.generator,
            start,
            None,
        )?)
    }

    pub fn successor_trace(
        &self,
        start: NativeStateId,
    ) -> Result<Vec<NativeStateId>, CultivationPackagingError> {
        Ok(recurrence_trace(
            &self.base,
            self.delta.generator,
            start,
            Some((self.delta.from, self.delta.successor_to)),
        )?)
    }

    pub fn successor_step(
        &self,
        start: NativeStateId,
    ) -> Result<NativeStateId, CultivationPackagingError> {
        Ok(crate::native_ecology::recurrent_return::next(
            &self.base,
            self.delta.generator,
            start,
            Some((self.delta.from, self.delta.successor_to)),
        )?)
    }

    pub fn withdrawn_trace(
        &self,
        start: NativeStateId,
    ) -> Result<Vec<NativeStateId>, CultivationPackagingError> {
        self.predecessor_trace(start)
    }

    pub fn held_out_start(&self) -> NativeStateId {
        self.held_out_start
    }

    pub fn control_start(&self) -> NativeStateId {
        self.control_from
    }

    pub fn predecessor_action(&self) -> &ExactRatMatrix {
        &self.holonomy.predecessor_action
    }

    pub fn successor_action(&self) -> &ExactRatMatrix {
        &self.holonomy.successor_action
    }

    pub fn withdrawn_action(&self) -> &ExactRatMatrix {
        &self.holonomy.predecessor_action
    }

    pub fn restored_successor_action(&self) -> Result<ExactRatMatrix, CultivationPackagingError> {
        Ok(self.holonomy.predecessor_action.add(&self.delta.delta)?)
    }

    fn validate(&self) -> Result<(), CultivationPackagingError> {
        if self.schema != SOURCE_DETACHED_CULTIVATION_SCHEMA
            || self.recurrence_starts != self.base.native_population
            || self.open_fibres.iter().any(String::is_empty)
        {
            return Err(CultivationPackagingError::Malformed);
        }
        self.base
            .validate()
            .map_err(|error| CultivationPackagingError::Native(error.to_string()))?;
        let expected_delta = local_delta(
            self.base.native_population.len(),
            self.delta.from,
            self.delta.predecessor_to,
            self.delta.successor_to,
        )?;
        let predecessor_action = action_matrix(&self.base, self.delta.generator)?;
        let successor_action = predecessor_action.add(&self.delta.delta)?;
        if self.delta.delta != expected_delta.0
            || self.delta.left_factor != expected_delta.1
            || self.delta.right_factor != expected_delta.2
            || self.holonomy.predecessor_action != predecessor_action
            || self.holonomy.successor_action != successor_action
            || self.causal_adjoint.metric_adjoint != self.delta.delta.transpose()?
            || self.causal_adjoint.measured_delta_rank != 1
            || self.semantic_work.starting_occurrences != self.recurrence_starts.len() as u64
        {
            return Err(CultivationPackagingError::Malformed);
        }
        let predecessor = self.predecessor_trace(self.held_out_start)?;
        let successor = self.successor_trace(self.held_out_start)?;
        if predecessor == successor || self.withdrawn_trace(self.held_out_start)? != predecessor {
            return Err(CultivationPackagingError::Malformed);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CultivationPackagingError {
    #[error("returned recurrence refused: {0}")]
    Returned(#[from] RecurrentReturnRefusal),
    #[error("exact cultivation return refused: {0}")]
    Exact(#[from] ExactLinearError),
    #[error("source-detached native recurrence refused: {0}")]
    Native(String),
    #[error("source-detached cultivation wire refused: {0}")]
    Wire(String),
    #[error("source-detached cultivation structure is malformed")]
    Malformed,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_scalar_loss_retains_distinct_oriented_returns() {
        let left = CompleteReturnedDifference {
            complete: (1i64, 0i64),
            loss: 1i64,
        };
        let right = CompleteReturnedDifference {
            complete: (0i64, 1i64),
            loss: 1i64,
        };
        assert!(equal_loss_different_return(&left, &right));
    }

    #[test]
    fn exposure_reference_mount_and_cultivation_are_distinct_rust_types() {
        assert_ne!(
            std::any::type_name::<Exposure<u8>>(),
            std::any::type_name::<ReferenceConsultation<u8>>()
        );
        assert_ne!(
            std::any::type_name::<MountedStanding<u8>>(),
            std::any::type_name::<ReturnedCultivation<u8>>()
        );
    }
}
