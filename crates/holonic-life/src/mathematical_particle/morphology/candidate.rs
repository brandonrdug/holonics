use std::collections::BTreeSet;

use holonic_engine::{cuda_refine::DeviceDynamicMorphology, exact_linear::ExactRatMatrix};

use super::super::DerivationRecurrenceRest;
use super::{
    algebra::{
        action_matrix, common_support, digest, extended_action, raw_native_adjoint, reaches,
        returned_adjoint, validate_occurrences,
    },
    types::{
        CausingForwardLineage, ConstitutiveActionChange, CultivationHolonomy,
        DynamicMorphologyCandidate, DynamicMorphologyError, DynamicMorphologyRest,
        ExactSupportSubcomplex, ExactWithdrawal, LocalMorphologyDelta,
        MorphologyCompatibilityReceipt, MorphologyDecision, ReconstructionFibreChange,
        ReturnedConstraintOccurrence,
    },
    DYNAMIC_MORPHOLOGY_SCHEMA,
};

impl DynamicMorphologyCandidate {
    #[allow(clippy::too_many_arguments)]
    pub fn found(
        predecessor: DerivationRecurrenceRest,
        predecessor_occurrence: impl Into<String>,
        returned_constraints: Vec<ReturnedConstraintOccurrence>,
        source_terminal_events: Vec<u64>,
        development_occurrence: impl Into<String>,
        held_out_occurrence: impl Into<String>,
        disjoint_control_occurrence: impl Into<String>,
    ) -> Result<Self, DynamicMorphologyError> {
        let predecessor_occurrence = predecessor_occurrence.into();
        let development_occurrence = development_occurrence.into();
        let held_out_occurrence = held_out_occurrence.into();
        let disjoint_control_occurrence = disjoint_control_occurrence.into();
        let predecessor_sha256 = digest(&predecessor.canonical_bytes()?);
        let predecessor_states = predecessor.native_action.len();
        validate_occurrences(&returned_constraints, predecessor_states)?;
        let exact_support = common_support(&returned_constraints)?;
        if exact_support.len() != 1
            || source_terminal_events.is_empty()
            || source_terminal_events.iter().collect::<BTreeSet<_>>().len()
                != source_terminal_events.len()
            || predecessor_occurrence.is_empty()
            || development_occurrence.is_empty()
            || held_out_occurrence.is_empty()
            || disjoint_control_occurrence.is_empty()
            || development_occurrence == held_out_occurrence
            || returned_constraints.iter().any(|returned| {
                returned.return_occurrence == disjoint_control_occurrence
                    || returned.world_occurrence == disjoint_control_occurrence
            })
        {
            return Err(DynamicMorphologyError::Lineage);
        }
        let supported = exact_support[0];
        if predecessor.native_action[supported as usize] != supported {
            return Err(DynamicMorphologyError::Support);
        }
        let development_start = supported;
        let held_out_start = predecessor
            .native_starts
            .iter()
            .copied()
            .find(|start| {
                *start != supported && reaches(&predecessor.native_action, *start, supported)
            })
            .ok_or(DynamicMorphologyError::HeldOut)?;
        let returned_receiver_adjoint =
            returned_adjoint(predecessor_states, &returned_constraints, &exact_support)?;
        let added_native_state =
            u32::try_from(predecessor_states).map_err(|_| DynamicMorphologyError::Extent)?;
        let predecessor_action = extended_action(&predecessor.native_action);
        let mut successor_action = predecessor_action.clone();
        successor_action[supported as usize] = added_native_state;
        let predecessor_matrix = action_matrix(&predecessor_action)?;
        let successor_matrix = action_matrix(&successor_action)?;
        let action_delta = successor_matrix.subtract(&predecessor_matrix)?;
        require_rank_one(&action_delta)?;
        let commutator = predecessor_matrix
            .multiply(&action_delta)?
            .subtract(&action_delta.multiply(&predecessor_matrix)?)?;
        let commutator_rank = commutator.rank()?;
        if commutator_rank == 0 {
            return Err(DynamicMorphologyError::Holonomy);
        }
        let returned_occurrences = returned_constraints
            .iter()
            .map(|returned| returned.return_occurrence.clone())
            .collect::<Vec<_>>();
        let delta = LocalMorphologyDelta {
            predecessor_occurrence,
            exact_support_subcomplex: ExactSupportSubcomplex {
                native_states: exact_support,
                source_terminal_events: source_terminal_events.clone(),
                returned_occurrences: returned_occurrences.clone(),
            },
            causing_forward_lineage: CausingForwardLineage {
                entering_native_state: held_out_start,
                terminal_native_state: supported,
                source_terminal_events: source_terminal_events.clone(),
                return_occurrences: returned_occurrences,
            },
            returned_receiver_adjoint,
            constitutive_action_change: ConstitutiveActionChange {
                added_native_state,
                supported_from: supported,
                predecessor_to: supported,
                successor_to: added_native_state,
                predecessor_action,
                successor_action,
                action_delta: action_delta.clone(),
            },
            compatibility: MorphologyCompatibilityReceipt {
                one_common_support_face: true,
                one_shared_delta_not_parallel_updates: true,
                disjoint_control_occurrence,
                disjoint_control_absent_from_support: true,
            },
            changed_and_reopened_fibres: vec![ReconstructionFibreChange {
                predecessor_native_state: supported,
                retained_source_terminal_events: source_terminal_events,
                opened_successor_native_state: added_native_state,
                withdrawal_reopens_predecessor_fibre: true,
            }],
            cultivation_holonomy: CultivationHolonomy {
                predecessor_action: predecessor_matrix,
                local_delta: action_delta,
                commutator,
                commutator_rank,
            },
            exact_withdrawal: ExactWithdrawal {
                predecessor_sha256,
                subtracts_addressed_delta: true,
                removes_opened_state_and_relation: true,
            },
            open_exterior: vec![
                "the committed relation is exact only for the returned R2 constraint family"
                    .to_owned(),
                "a compatible FamilySupport operation passage remains outside this local morphology"
                    .to_owned(),
                "long-horizon retained context remains the R4 aperture".to_owned(),
            ],
        };
        Ok(Self {
            predecessor,
            returned_constraints,
            development_occurrence,
            held_out_occurrence,
            development_start,
            held_out_start,
            delta,
        })
    }

    pub fn predecessor_action(&self) -> &[u32] {
        &self.predecessor.native_action
    }

    pub fn support_incidence_wire(&self) -> Vec<i32> {
        self.returned_constraints
            .iter()
            .flat_map(|returned| {
                (0..self.predecessor.native_action.len()).map(move |state| {
                    i32::from(returned.support_native_states.contains(&(state as u32)))
                })
            })
            .collect()
    }

    pub fn returned_covector_wire(&self) -> Vec<i32> {
        self.returned_constraints
            .iter()
            .map(|returned| returned.primitive_orientation)
            .collect()
    }

    pub fn recurrence_starts(&self) -> [u32; 2] {
        [self.development_start, self.held_out_start]
    }

    pub fn finish(
        self,
        device: &DeviceDynamicMorphology,
    ) -> Result<MorphologyDecision, DynamicMorphologyError> {
        let expected_adjoint = raw_native_adjoint(
            self.predecessor.native_action.len(),
            &self.returned_constraints,
        );
        let expected_commit = self
            .returned_constraints
            .iter()
            .all(|returned| returned.primitive_orientation > 0);
        if device.returned_adjoint != expected_adjoint
            || device.committed != expected_commit
            || device.supported_state != Some(self.delta.constitutive_action_change.supported_from)
            || device.predecessor_action != self.delta.constitutive_action_change.predecessor_action
            || device.withdrawn_action != device.predecessor_action
            || device.committed
                && device.successor_action != self.delta.constitutive_action_change.successor_action
            || !device.committed && device.successor_action != device.predecessor_action
        {
            return Err(DynamicMorphologyError::Device);
        }
        if !device.committed {
            return Ok(MorphologyDecision::Declined {
                predecessor: self.predecessor,
                reason: "the complete returned receiver family did not carry positive current"
                    .to_owned(),
            });
        }
        let rest = DynamicMorphologyRest {
            schema: DYNAMIC_MORPHOLOGY_SCHEMA.to_owned(),
            predecessor: self.predecessor,
            returned_constraints: self.returned_constraints,
            development_occurrence: self.development_occurrence,
            held_out_occurrence: self.held_out_occurrence,
            development_start: self.development_start,
            held_out_start: self.held_out_start,
            delta: self.delta,
        };
        rest.validate()?;
        Ok(MorphologyDecision::Committed(rest))
    }
}

fn require_rank_one(delta: &ExactRatMatrix) -> Result<(), DynamicMorphologyError> {
    if delta.rank()? != 1 {
        return Err(DynamicMorphologyError::Action);
    }
    Ok(())
}
