use std::collections::BTreeSet;

use holonic_engine::exact_linear::ExactRatMatrix;
use num_rational::BigRational as Rat;
use sha2::{Digest, Sha256};

use super::types::{
    ConstraintReceiver, DynamicMorphologyError, ReturnedConstraintOccurrence,
    ReturnedReceiverAdjoint,
};

pub(super) fn validate_occurrences(
    returned: &[ReturnedConstraintOccurrence],
    states: usize,
) -> Result<(), DynamicMorphologyError> {
    let family = returned
        .iter()
        .map(|occurrence| occurrence.receiver)
        .collect::<BTreeSet<_>>();
    if returned.len() != ConstraintReceiver::FAMILY.len()
        || family != ConstraintReceiver::FAMILY.into_iter().collect()
        || returned.iter().any(|occurrence| {
            occurrence.emission_occurrence.is_empty()
                || occurrence.world_occurrence.is_empty()
                || occurrence.return_occurrence.is_empty()
                || occurrence.emission_occurrence == occurrence.world_occurrence
                || occurrence.world_occurrence == occurrence.return_occurrence
                || !is_digest(&occurrence.consequence_sha256)
                || !matches!(occurrence.primitive_orientation, -1 | 0 | 1)
                || occurrence.support_native_states.is_empty()
                || occurrence
                    .support_native_states
                    .iter()
                    .any(|state| *state as usize >= states)
        })
    {
        return Err(DynamicMorphologyError::ReturnedConstraint);
    }
    let occurrences = returned
        .iter()
        .flat_map(|returned| {
            [
                &returned.emission_occurrence,
                &returned.world_occurrence,
                &returned.return_occurrence,
            ]
        })
        .collect::<BTreeSet<_>>();
    if occurrences.len() != returned.len() * 3 {
        return Err(DynamicMorphologyError::ReturnedConstraint);
    }
    Ok(())
}

pub(super) fn common_support(
    returned: &[ReturnedConstraintOccurrence],
) -> Result<Vec<u32>, DynamicMorphologyError> {
    let first = returned
        .first()
        .ok_or(DynamicMorphologyError::ReturnedConstraint)?;
    let mut support = first
        .support_native_states
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    for occurrence in returned.iter().skip(1) {
        support.retain(|state| occurrence.support_native_states.contains(state));
    }
    if support.is_empty() {
        return Err(DynamicMorphologyError::Support);
    }
    Ok(support.into_iter().collect())
}

pub(super) fn returned_adjoint(
    states: usize,
    returned: &[ReturnedConstraintOccurrence],
    support: &[u32],
) -> Result<ReturnedReceiverAdjoint, DynamicMorphologyError> {
    let zero = Rat::from_integer(0.into());
    let one = Rat::from_integer(1.into());
    let incidence = ExactRatMatrix::new(
        returned
            .iter()
            .map(|occurrence| {
                (0..states)
                    .map(|state| {
                        if occurrence.support_native_states.contains(&(state as u32)) {
                            one.clone()
                        } else {
                            zero.clone()
                        }
                    })
                    .collect()
            })
            .collect(),
    )?;
    let receiver_covector = ExactRatMatrix::new(
        returned
            .iter()
            .map(|occurrence| vec![Rat::from_integer(occurrence.primitive_orientation.into())])
            .collect(),
    )?;
    let state_metric = ExactRatMatrix::identity(states)?;
    let receiver_metric = ExactRatMatrix::identity(returned.len())?;
    let metric_adjoint = incidence.metric_adjoint(&state_metric, &receiver_metric)?;
    let returned_native_covector = metric_adjoint.multiply(&receiver_covector)?;
    let raw = raw_native_adjoint(states, returned);
    let divisor = raw.iter().map(|value| value.unsigned_abs()).fold(0, gcd);
    let primitive_native_covector = if divisor == 0 {
        vec![0; states]
    } else {
        raw.iter().map(|value| value / divisor as i64).collect()
    };
    if support.len() != 1
        || primitive_native_covector
            .iter()
            .enumerate()
            .filter(|(_, value)| **value != 0)
            .map(|(state, _)| state as u32)
            .collect::<Vec<_>>()
            != support
    {
        return Err(DynamicMorphologyError::Adjoint);
    }
    Ok(ReturnedReceiverAdjoint {
        support_incidence: incidence,
        receiver_covector,
        state_metric,
        receiver_metric,
        metric_adjoint,
        returned_native_covector,
        primitive_native_covector,
    })
}

pub(super) fn raw_native_adjoint(
    states: usize,
    returned: &[ReturnedConstraintOccurrence],
) -> Vec<i64> {
    (0..states)
        .map(|state| {
            returned
                .iter()
                .filter(|occurrence| occurrence.support_native_states.contains(&(state as u32)))
                .map(|occurrence| i64::from(occurrence.primitive_orientation))
                .sum()
        })
        .collect()
}

pub(super) fn action_matrix(action: &[u32]) -> Result<ExactRatMatrix, DynamicMorphologyError> {
    let zero = Rat::from_integer(0.into());
    let one = Rat::from_integer(1.into());
    let mut rows = vec![vec![zero; action.len()]; action.len()];
    for (from, to) in action.iter().copied().enumerate() {
        if to as usize >= action.len() {
            return Err(DynamicMorphologyError::Action);
        }
        rows[to as usize][from] = one.clone();
    }
    Ok(ExactRatMatrix::new(rows)?)
}

pub(super) fn extended_action(predecessor: &[u32]) -> Vec<u32> {
    let mut action = predecessor.to_vec();
    action.push(predecessor.len() as u32);
    action
}

pub(super) fn reaches(action: &[u32], start: u32, target: u32) -> bool {
    let mut state = start;
    for _ in 0..action.len() {
        if state == target {
            return true;
        }
        state = action[state as usize];
    }
    false
}

fn gcd(left: u64, right: u64) -> u64 {
    if right == 0 {
        left
    } else {
        gcd(right, left % right)
    }
}

pub(super) fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}
