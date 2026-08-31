//! Source-neutral returned-difference deposit construction shared by Athena history views.

use std::collections::BTreeSet;

use holonic_engine::{
    native_spool::{
        NativeConstitutiveResponse, NativeDepositFibreDelta, NativeExactReconstructionFibre,
        NativeIncidenceTerm, NativeMixedConstitutiveFamily, NativeParametronCell,
        NativeReceiverConsequence, NativeSituatedSpoolBundle, NativeThread, NativeThreadDeposit,
        NATIVE_THREAD_DEPOSIT_SCHEMA, NATIVE_THREAD_SCHEMA,
    },
    receiver_history_compression::NativeStateId,
    ExactComplexWaveCurrent, OccurrencePort,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::athena_native::situated_difference::SituatedDifferenceSection;

#[derive(Debug, Error)]
pub(super) enum ReturnedDifferenceError {
    #[error("the source-neutral morphology descent is malformed: {0}")]
    Descent(String),
    #[error("the singular situated ecology refused the returned morphology: {0}")]
    Ecology(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ReturnedDifferenceStaging {
    pub(super) difference_identity_sha256: String,
    pub(super) thread_address: String,
    pub(super) winding_coefficients: Vec<Rat>,
    pub(super) return_operator_identity_sha256: String,
    pub(super) occurrence_population_identity_sha256: String,
}

pub(super) fn derive_returned_difference_deposit_from_history(
    ecology: &NativeSituatedSpoolBundle,
    branch_threads: &[String],
    prior_returns: &[(String, Vec<Rat>)],
    difference: &SituatedDifferenceSection,
) -> Result<(NativeThreadDeposit, ReturnedDifferenceStaging), ReturnedDifferenceError> {
    let winding_coefficients = difference.causal_adjoint.returned_source_covector.clone();
    if winding_coefficients.len() != branch_threads.len()
        || winding_coefficients
            .iter()
            .all(|coefficient| coefficient == &Rat::from_integer(BigInt::from(0)))
    {
        return Err(ReturnedDifferenceError::Descent(
            "the returned section does not inhabit the complete standing winding chart".to_owned(),
        ));
    }
    let spool_address = common_spool_address_from_threads(ecology, branch_threads)?;
    if difference.candidate.address.spool != spool_address
        || difference.returned.address.spool != spool_address
    {
        return Err(ReturnedDifferenceError::Descent(
            "the returned section does not cross the standing native spool".to_owned(),
        ));
    }
    let existing_occurrences = ecology
        .native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .flat_map(|thread| &thread.occurrences)
        .map(|occurrence| occurrence.occurrence)
        .collect::<BTreeSet<_>>();
    if existing_occurrences.contains(&difference.returned.address.occurrence) {
        return Err(ReturnedDifferenceError::Descent(
            "the returned occurrence is already owned; cultivation requires a genuinely later return"
                .to_owned(),
        ));
    }
    let thread_address = format!(
        "native-spool/returned-situated-difference/{}",
        difference.identity_sha256
    );
    let entering_native = difference.returned.entering_native;
    let emitting_native = difference.returned.emitting_native;
    let native_support = BTreeSet::from([entering_native, emitting_native]);
    let occurrence = difference.returned.address.occurrence;
    let thread = NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address: thread_address.clone(),
        entering_boundary: difference.returned.entering_boundary,
        emitting_boundary: difference.returned.emitting_boundary,
        entering_carrier: "native-returned-situated-complex-parametron-current".to_owned(),
        emitting_carrier: "native-returned-situated-complex-parametron-current".to_owned(),
        occurrences: vec![holonic_engine::native_spool::NativeThreadOccurrence {
            occurrence,
            predecessor: Some(difference.candidate.address.occurrence),
            entering_port: OccurrencePort::input(occurrence, 0),
            emitting_port: OccurrencePort::output(occurrence, 0),
            entering_native,
            emitting_native,
        }],
        native_support: native_support.clone(),
        incidence: vec![NativeIncidenceTerm {
            occurrence,
            from: entering_native,
            to: emitting_native,
            coefficient: 1,
        }],
        parametrons: vec![
            NativeParametronCell {
                native: entering_native,
                section: difference.complex_difference.entering_section.clone(),
                current: difference.complex_difference.entering_current.clone(),
                relative_phase: difference.returned.relative_phase.clone(),
                hand: difference.returned.hand,
            },
            NativeParametronCell {
                native: emitting_native,
                section: difference.complex_difference.emitting_section.clone(),
                current: difference.complex_difference.emitting_current.clone(),
                relative_phase: difference.returned.relative_phase.clone(),
                hand: difference.returned.hand,
            },
        ],
        constitutive_responses: vec![
            NativeConstitutiveResponse {
                native: entering_native,
                receiver: difference.returned.receiver,
                presented: difference.complex_difference.entering_section.clone(),
                stored: difference.complex_difference.entering_current.clone(),
            },
            NativeConstitutiveResponse {
                native: emitting_native,
                receiver: difference.returned.receiver,
                presented: difference.complex_difference.emitting_section.clone(),
                stored: difference.complex_difference.emitting_current.clone(),
            },
        ],
        chronology: difference.returned.ordered_word.clone(),
        receiver_consequences: vec![
            NativeReceiverConsequence {
                native: entering_native,
                receiver: difference.returned.receiver,
                observation: difference.returned.observation,
            },
            NativeReceiverConsequence {
                native: emitting_native,
                receiver: difference.returned.receiver,
                observation: difference.returned.observation,
            },
        ],
        obstruction: difference.native_obstructions.first().cloned(),
        open_exterior: vec![
            "receiver and successor histories outside the cultivated world-tube remain open"
                .to_owned(),
        ],
        reconstruction_fibre: BTreeSet::from([occurrence]),
    };

    let spool = ecology
        .native()
        .spools
        .iter()
        .find(|spool| spool.address == spool_address)
        .ok_or_else(|| ReturnedDifferenceError::Ecology("standing spool disappeared".to_owned()))?;
    if !spool
        .receiver_family
        .contains(&difference.returned.receiver)
        || !spool.native_population.contains(&entering_native)
        || !spool.native_population.contains(&emitting_native)
    {
        return Err(ReturnedDifferenceError::Descent(
            "the returned section escaped the standing receiver/native family".to_owned(),
        ));
    }
    let dependent_receiver_support = spool.native_population.clone();
    let support_population = u64::try_from(dependent_receiver_support.len())
        .map_err(|_| ReturnedDifferenceError::Descent("native support overflow".to_owned()))?;
    let pair_population = support_population
        .checked_mul(support_population.saturating_sub(1))
        .and_then(|population| population.checked_div(2))
        .ok_or_else(|| ReturnedDifferenceError::Descent("pair support overflow".to_owned()))?;
    let returned_current = difference.complex_difference.emitting_current.clone();
    if returned_current.is_zero() {
        return Err(ReturnedDifferenceError::Descent(
            "the returned passage carries no Complex-Parametron current".to_owned(),
        ));
    }
    let one = Rat::from_integer(BigInt::from(1));
    let mut mixed_constitutive_families =
        Vec::with_capacity(branch_threads.len() + prior_returns.len() + 1);
    for (coordinate, branch_thread) in branch_threads.iter().enumerate() {
        let left_current = emitting_thread_current(ecology, branch_thread)?;
        let coefficient = &winding_coefficients[coordinate];
        let storage = &one + coefficient * coefficient;
        mixed_constitutive_families.push(returned_mixed_family(
            branch_thread,
            &thread_address,
            difference.returned.receiver,
            storage,
            &left_current,
            &returned_current,
            &dependent_receiver_support,
            pair_population,
            &difference.identity_sha256,
        )?);
    }
    for (prior_thread, prior_winding) in prior_returns {
        if prior_winding.len() != winding_coefficients.len() {
            return Err(ReturnedDifferenceError::Descent(
                "a prior returned section left the common winding chart".to_owned(),
            ));
        }
        let left_current = emitting_thread_current(ecology, prior_thread)?;
        let storage = prior_winding.iter().zip(&winding_coefficients).fold(
            one.clone(),
            |sum, (left, right)| {
                let overlap = left * right;
                sum + &overlap * &overlap
            },
        );
        mixed_constitutive_families.push(returned_mixed_family(
            prior_thread,
            &thread_address,
            difference.returned.receiver,
            storage,
            &left_current,
            &returned_current,
            &dependent_receiver_support,
            pair_population,
            &difference.identity_sha256,
        )?);
    }
    let self_storage = winding_coefficients
        .iter()
        .fold(one.clone(), |sum, coefficient| {
            sum + coefficient * coefficient
        });
    mixed_constitutive_families.push(returned_mixed_family(
        &thread_address,
        &thread_address,
        difference.returned.receiver,
        self_storage,
        &returned_current,
        &returned_current,
        &dependent_receiver_support,
        pair_population,
        &difference.identity_sha256,
    )?);

    let exact_occurrences = BTreeSet::from([
        difference.candidate.address.occurrence,
        difference.returned.address.occurrence,
    ]);
    let exact_fibre = NativeExactReconstructionFibre {
        address: format!(
            "native-returned-situated-fibre/{}",
            difference.identity_sha256
        ),
        thread: thread_address.clone(),
        return_operator: difference.causal_adjoint.composite_adjoint.clone(),
        terminal_covector: difference.causal_adjoint.terminal_covector.clone(),
        returned_covector: winding_coefficients.clone(),
        particular: difference
            .causal_adjoint
            .reconstruction_fibre
            .particular
            .clone(),
        radical: difference.causal_adjoint.radical.clone(),
        obstruction: difference.causal_adjoint.obstruction.clone(),
        carrying_pullback: difference.carrying_occurrence,
        k3_native_support: dependent_receiver_support.clone(),
        dependent_receiver_fibre: dependent_receiver_support.clone(),
        occurrences: exact_occurrences.clone(),
        open_exterior: vec![
            "the exact candidate/return fibre remains available to richer future receivers"
                .to_owned(),
        ],
    };
    let deposit = NativeThreadDeposit {
        schema: NATIVE_THREAD_DEPOSIT_SCHEMA.to_owned(),
        spool_address,
        thread,
        serial_pullbacks: Vec::new(),
        generator_descents: Vec::new(),
        receiver_factors: Vec::new(),
        mutual_constitutive_responses: Vec::new(),
        mixed_constitutive_families,
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        reconstruction_fibre_deltas: vec![NativeDepositFibreDelta {
            native: emitting_native,
            occurrences: BTreeSet::from([occurrence]),
        }],
        exact_reconstruction_fibres: vec![exact_fibre],
    };
    deposit
        .validate()
        .map_err(|error| ReturnedDifferenceError::Ecology(error.to_string()))?;
    let staging = ReturnedDifferenceStaging {
        difference_identity_sha256: difference.identity_sha256.clone(),
        thread_address,
        winding_coefficients,
        return_operator_identity_sha256: digest_json(&(
            &difference.causal_adjoint.composite_adjoint,
            &difference.causal_adjoint.terminal_covector,
            &difference.causal_adjoint.returned_source_covector,
        ))?,
        occurrence_population_identity_sha256: digest_json(&exact_occurrences)?,
    };
    Ok((deposit, staging))
}

#[allow(clippy::too_many_arguments)]
fn returned_mixed_family(
    left_thread: &str,
    right_thread: &str,
    receiver: holonic_engine::receiver_exact_compression::ReceiverId,
    storage: Rat,
    returned_left: &ExactComplexWaveCurrent,
    returned_right: &ExactComplexWaveCurrent,
    dependent_receiver_support: &BTreeSet<NativeStateId>,
    pair_population: u64,
    difference_identity: &str,
) -> Result<NativeMixedConstitutiveFamily, ReturnedDifferenceError> {
    let zero = ExactComplexWaveCurrent::zero();
    let left_difference = returned_left.clone();
    let right_difference = returned_right.clone();
    let candidate_product = zero.clone();
    let source_linear_terms = zero.clone();
    let mixed_remainder = left_difference.multiply(&right_difference).scaled(&storage);
    let returned_product = returned_left.multiply(returned_right).scaled(&storage);
    let family = NativeMixedConstitutiveFamily {
        address: format!(
            "native-returned-constitutive/{}/{}",
            difference_identity,
            digest_json(&(left_thread, right_thread, &storage))?
        ),
        left_thread: left_thread.to_owned(),
        right_thread: right_thread.to_owned(),
        receiver,
        storage,
        candidate_left: zero.clone(),
        candidate_right: zero,
        returned_left: returned_left.clone(),
        returned_right: returned_right.clone(),
        left_difference,
        right_difference,
        candidate_product,
        source_linear_terms,
        mixed_remainder: mixed_remainder.clone(),
        reconstructed_returned_product: mixed_remainder,
        returned_product,
        dependent_receiver_support: dependent_receiver_support.clone(),
        pair_population,
    };
    family
        .validate()
        .map_err(|error| ReturnedDifferenceError::Ecology(error.to_string()))?;
    Ok(family)
}

fn emitting_thread_current(
    ecology: &NativeSituatedSpoolBundle,
    thread_address: &str,
) -> Result<ExactComplexWaveCurrent, ReturnedDifferenceError> {
    let thread = ecology
        .native()
        .spools
        .iter()
        .flat_map(|spool| &spool.threads)
        .find(|thread| thread.address == thread_address)
        .ok_or_else(|| {
            ReturnedDifferenceError::Ecology(format!(
                "standing thread {thread_address} disappeared"
            ))
        })?;
    let emitting_native = thread
        .occurrences
        .first()
        .map(|occurrence| occurrence.emitting_native)
        .ok_or_else(|| ReturnedDifferenceError::Ecology("thread has no occurrence".to_owned()))?;
    thread
        .parametrons
        .iter()
        .find(|cell| cell.native == emitting_native)
        .map(|cell| cell.current.clone())
        .ok_or_else(|| {
            ReturnedDifferenceError::Ecology("thread has no emitting current".to_owned())
        })
}

pub(super) fn common_spool_address_from_threads(
    ecology: &NativeSituatedSpoolBundle,
    branch_threads: &[String],
) -> Result<String, ReturnedDifferenceError> {
    let first = branch_threads.first().ok_or_else(|| {
        ReturnedDifferenceError::Descent("the standing winding population is empty".to_owned())
    })?;
    ecology
        .native()
        .spools
        .iter()
        .find(|spool| spool.threads.iter().any(|thread| thread.address == *first))
        .map(|spool| spool.address.clone())
        .ok_or_else(|| {
            ReturnedDifferenceError::Ecology("the standing winding spool disappeared".to_owned())
        })
}

fn digest_json(value: &impl Serialize) -> Result<String, ReturnedDifferenceError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| ReturnedDifferenceError::Ecology(error.to_string()))?;
    Ok(Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect())
}
