use super::super::DerivationRecurrenceRest;
use super::{
    algebra::{
        action_matrix, common_support, digest, extended_action, reaches, returned_adjoint,
        validate_occurrences,
    },
    types::{DynamicMorphologyError, DynamicMorphologyRest, WithdrawalReceipt},
    DYNAMIC_MORPHOLOGY_SCHEMA,
};

impl DynamicMorphologyRest {
    pub fn read(bytes: &[u8]) -> Result<Self, DynamicMorphologyError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| DynamicMorphologyError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, DynamicMorphologyError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| DynamicMorphologyError::Wire(error.to_string()))
    }

    pub fn predecessor_action(&self) -> &[u32] {
        &self.delta.constitutive_action_change.predecessor_action
    }

    pub fn successor_action(&self) -> &[u32] {
        &self.delta.constitutive_action_change.successor_action
    }

    pub fn recurrence_starts(&self) -> [u32; 2] {
        [self.development_start, self.held_out_start]
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

    pub fn withdraw(
        self,
    ) -> Result<(DerivationRecurrenceRest, WithdrawalReceipt), DynamicMorphologyError> {
        self.validate()?;
        let predecessor_sha256 = self.delta.exact_withdrawal.predecessor_sha256.clone();
        let restored_sha256 = digest(&self.predecessor.canonical_bytes()?);
        let receipt = WithdrawalReceipt {
            exact_predecessor_restored: restored_sha256 == predecessor_sha256,
            predecessor_sha256,
            restored_sha256,
        };
        if !receipt.exact_predecessor_restored {
            return Err(DynamicMorphologyError::Withdrawal);
        }
        Ok((self.predecessor, receipt))
    }

    pub(super) fn validate(&self) -> Result<(), DynamicMorphologyError> {
        if self.schema != DYNAMIC_MORPHOLOGY_SCHEMA
            || self.development_occurrence.is_empty()
            || self.held_out_occurrence.is_empty()
            || self.development_occurrence == self.held_out_occurrence
        {
            return Err(DynamicMorphologyError::Identity);
        }
        let predecessor_sha256 = digest(&self.predecessor.canonical_bytes()?);
        validate_occurrences(
            &self.returned_constraints,
            self.predecessor.native_action.len(),
        )?;
        let support = common_support(&self.returned_constraints)?;
        let change = &self.delta.constitutive_action_change;
        let expected_predecessor = extended_action(&self.predecessor.native_action);
        let mut expected_successor = expected_predecessor.clone();
        expected_successor[change.supported_from as usize] = change.added_native_state;
        let predecessor_matrix = action_matrix(&expected_predecessor)?;
        let successor_matrix = action_matrix(&expected_successor)?;
        let action_delta = successor_matrix.subtract(&predecessor_matrix)?;
        let commutator = predecessor_matrix
            .multiply(&action_delta)?
            .subtract(&action_delta.multiply(&predecessor_matrix)?)?;
        if support != self.delta.exact_support_subcomplex.native_states
            || support != vec![change.supported_from]
            || change.added_native_state as usize != self.predecessor.native_action.len()
            || change.predecessor_to != change.supported_from
            || change.successor_to != change.added_native_state
            || change.predecessor_action != expected_predecessor
            || change.successor_action != expected_successor
            || change.action_delta != action_delta
            || action_delta.rank()? != 1
            || self.delta.cultivation_holonomy.predecessor_action != predecessor_matrix
            || self.delta.cultivation_holonomy.local_delta != action_delta
            || self.delta.cultivation_holonomy.commutator != commutator
            || self.delta.cultivation_holonomy.commutator_rank != commutator.rank()?
            || self.delta.cultivation_holonomy.commutator_rank == 0
            || self.delta.exact_withdrawal.predecessor_sha256 != predecessor_sha256
            || !self.delta.exact_withdrawal.subtracts_addressed_delta
            || !self
                .delta
                .exact_withdrawal
                .removes_opened_state_and_relation
            || !self.delta.compatibility.one_common_support_face
            || !self
                .delta
                .compatibility
                .one_shared_delta_not_parallel_updates
            || !self
                .delta
                .compatibility
                .disjoint_control_absent_from_support
            || self.delta.open_exterior.is_empty()
            || self.delta.changed_and_reopened_fibres.len() != 1
            || self.development_start != change.supported_from
            || !reaches(
                &self.predecessor.native_action,
                self.held_out_start,
                change.supported_from,
            )
        {
            return Err(DynamicMorphologyError::Identity);
        }
        let expected_adjoint = returned_adjoint(
            self.predecessor.native_action.len(),
            &self.returned_constraints,
            &support,
        )?;
        if self.delta.returned_receiver_adjoint != expected_adjoint {
            return Err(DynamicMorphologyError::Adjoint);
        }
        Ok(())
    }
}
