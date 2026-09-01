//! Receiver-exact cultivation and release of an inherited native transport scaffold.
//!
//! One actual inference emission and one genuinely later returned Complex-Parametron current
//! found a native thread in the continuing ecology. The inherited threads can then depart while
//! that returned conduct remains remountable. No foreign realization, model name, modality,
//! executor, surface, or target label enters this owner.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    native_ecology::holonic_intelligence::{
        conduct_native_inference, InferenceCirculation, NativeEmissionAddress,
        NativeInferenceAddress, NativeInferenceRequest,
    },
    native_spool::{
        NativeConstitutiveResponse, NativeDepositFibreDelta, NativeExactReconstructionFibre,
        NativeGeneratorDescent, NativeGeneratorStep, NativeIncidenceTerm, NativeParametronCell,
        NativePullbackOccurrence, NativeReceiverConsequence, NativeSerialPullback,
        NativeSituatedThreadWithdrawal, NativeThread, NativeThreadDeposit,
        NativeThreadDepositReceipt, NativeThreadHand, NativeThreadOccurrence,
        SituatedNativeTransportScaffold, NATIVE_THREAD_DEPOSIT_SCHEMA, NATIVE_THREAD_SCHEMA,
    },
    receiver_exact_compression::{InputId, Observation},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactRatMatrix, ExactUnitConicPhase,
    OccurrencePort,
};
use serde::Serialize;
use thiserror::Error;

use super::NativeEcologyRest;

/// One exact later current crossing the world-return boundary of an emitted native section.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedScaffoldCurrent {
    pub occurrence: EventId,
    pub emitting_boundary: BoundaryId,
    pub current: ExactComplexWaveCurrent,
}

/// Stable receiver consequence used to compare the cultivated body across apparatus remounts.
/// Device names, launch counts, hashes, and serialized identity are deliberately excluded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScaffoldCultivatedConsequence {
    pub native_start: Vec<NativeStateId>,
    pub native_end: Vec<NativeStateId>,
    pub observations: Vec<Observation>,
    pub emitted: NativeEmissionAddress,
    pub returned_current_sections: Vec<Vec<ExactComplexWaveCurrent>>,
    pub reconstruction_fibre: BTreeSet<EventId>,
}

/// The one continuing ecology after a returned current has founded reusable native morphology.
#[derive(Debug)]
pub struct ScaffoldCultivatedRest {
    ecology: SituatedNativeTransportScaffold,
    cultivated_request: NativeInferenceRequest,
    inherited_threads: Vec<(String, String)>,
    deposit_receipt: NativeThreadDepositReceipt,
}

/// The exact release receipt. Every Boolean is returned by a typed operation performed by
/// `release`, never accepted from a caller.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScaffoldReleaseReceipt {
    pub before_withdrawal: ScaffoldCultivatedConsequence,
    pub after_source_detached_remount: ScaffoldCultivatedConsequence,
    pub declared_consequence_preserved: bool,
    pub cultivated_ablation_removed_conduct: bool,
    pub restoration_recovered_successor: bool,
    pub inherited_thread_population: usize,
    pub departed_reconstruction_fibre_population: usize,
    pub final_source_detached: bool,
}

/// Productive native continuation and its physically separate inherited reconstruction lane.
#[derive(Debug)]
pub struct ReleasedScaffoldCultivation {
    pub hot: SituatedNativeTransportScaffold,
    pub departed_inherited: Vec<NativeSituatedThreadWithdrawal>,
    pub receipt: ScaffoldReleaseReceipt,
}

#[derive(Debug, Error)]
pub enum ScaffoldCultivationError {
    #[error("the predecessor ecology refused scaffold cultivation: {0}")]
    Predecessor(String),
    #[error("the world return is not a genuine later consequence of the emitted section")]
    Return,
    #[error("the native returned-current deposit is malformed: {0}")]
    Deposit(String),
    #[error("the cultivated ecology refused release: {0}")]
    Ecology(String),
    #[error("the declared cultivated consequence changed after source-detached remount")]
    Consequence,
}

impl ScaffoldCultivatedRest {
    /// Consume one hot SCF3 rest and found morphology from an actual SCF4 emission/return pair.
    pub fn cultivate(
        predecessor: NativeEcologyRest,
        source: NativeInferenceAddress,
        emitted: NativeEmissionAddress,
        returned: ReturnedScaffoldCurrent,
    ) -> Result<Self, ScaffoldCultivationError> {
        predecessor
            .validate()
            .map_err(|error| ScaffoldCultivationError::Predecessor(error.to_string()))?;
        let inherited_threads = predecessor
            .ecology
            .spools
            .iter()
            .flat_map(|spool| {
                spool
                    .threads
                    .iter()
                    .map(move |thread| (spool.address.clone(), thread.address.clone()))
            })
            .collect::<Vec<_>>();
        let deposit = returned_current_deposit(&predecessor, &source, &emitted, &returned)?;
        let cultivated_request = NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: source.spool.clone(),
                thread: deposit.thread.address.clone(),
                occurrence: returned.occurrence,
            },
            receiver: emitted.receiver,
        };
        let (ecology, deposit_receipt) = predecessor
            .ecology
            .deposit_thread(deposit)
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
        if ecology
            .identity_sha256()
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?
            != deposit_receipt.successor_identity_sha256
        {
            return Err(ScaffoldCultivationError::Ecology(
                "the cultivation receipt does not name the complete successor".to_owned(),
            ));
        }
        Ok(Self {
            ecology,
            cultivated_request,
            inherited_threads,
            deposit_receipt,
        })
    }

    pub fn ecology(&self) -> &SituatedNativeTransportScaffold {
        &self.ecology
    }

    pub fn cultivated_request(&self) -> &NativeInferenceRequest {
        &self.cultivated_request
    }

    /// Prove cultivated survival, targeted ablation, exact restoration, and final scaffold
    /// departure by ownership transfer.
    pub fn release(self) -> Result<ReleasedScaffoldCultivation, ScaffoldCultivationError> {
        let Self {
            mut ecology,
            cultivated_request,
            inherited_threads,
            deposit_receipt,
        } = self;
        let full_identity = ecology
            .identity_sha256()
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
        if full_identity != deposit_receipt.successor_identity_sha256 {
            return Err(ScaffoldCultivationError::Ecology(
                "cultivated successor identity changed before release".to_owned(),
            ));
        }
        let before_withdrawal = cultivated_consequence(&ecology, &cultivated_request)?;

        let mut first_departure = Vec::with_capacity(inherited_threads.len());
        for (spool, thread) in &inherited_threads {
            let (rest, withdrawal) = ecology
                .withdraw_thread(spool, thread)
                .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
            ecology = rest;
            first_departure.push(withdrawal);
        }
        let detached_identity = ecology
            .identity_sha256()
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
        let after_source_detached_remount = cultivated_consequence(&ecology, &cultivated_request)?;
        if before_withdrawal != after_source_detached_remount {
            return Err(ScaffoldCultivationError::Consequence);
        }

        for withdrawal in first_departure.into_iter().rev() {
            ecology = ecology
                .restore_thread(withdrawal)
                .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
        }
        let restoration_recovered_successor = ecology
            .identity_sha256()
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?
            == full_identity;
        if !restoration_recovered_successor {
            return Err(ScaffoldCultivationError::Ecology(
                "inherited scaffold restoration did not recover the successor".to_owned(),
            ));
        }

        let (ablated, cultivated_withdrawal) = ecology
            .withdraw_thread(
                &cultivated_request.address.spool,
                &cultivated_request.address.thread,
            )
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
        let cultivated_ablation_removed_conduct =
            conduct_native_inference(ablated.native(), cultivated_request.clone()).is_err();
        if !cultivated_ablation_removed_conduct {
            return Err(ScaffoldCultivationError::Ecology(
                "cultivated-thread ablation left its conduct reachable".to_owned(),
            ));
        }
        ecology = ablated
            .restore_thread(cultivated_withdrawal)
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
        if ecology
            .identity_sha256()
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?
            != full_identity
        {
            return Err(ScaffoldCultivationError::Ecology(
                "cultivated-thread restoration did not recover the successor".to_owned(),
            ));
        }

        let mut departed_inherited = Vec::with_capacity(inherited_threads.len());
        for (spool, thread) in &inherited_threads {
            let (rest, withdrawal) = ecology
                .withdraw_thread(spool, thread)
                .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
            ecology = rest;
            departed_inherited.push(withdrawal);
        }
        let final_source_detached = ecology
            .identity_sha256()
            .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?
            == detached_identity
            && inherited_threads.iter().all(|(spool, thread)| {
                ecology.native().spools.iter().all(|candidate| {
                    candidate.address != *spool
                        || candidate
                            .threads
                            .iter()
                            .all(|candidate| candidate.address != *thread)
                })
            });
        if !final_source_detached {
            return Err(ScaffoldCultivationError::Ecology(
                "the final hot body retained inherited scaffold conduct".to_owned(),
            ));
        }
        let departed_reconstruction_fibre_population = departed_inherited
            .iter()
            .map(|withdrawal| {
                withdrawal.native.fibre_deltas.len() + withdrawal.exact_reconstruction_fibres.len()
            })
            .sum();
        Ok(ReleasedScaffoldCultivation {
            hot: ecology,
            departed_inherited,
            receipt: ScaffoldReleaseReceipt {
                before_withdrawal,
                after_source_detached_remount,
                declared_consequence_preserved: true,
                cultivated_ablation_removed_conduct,
                restoration_recovered_successor,
                inherited_thread_population: inherited_threads.len(),
                departed_reconstruction_fibre_population,
                final_source_detached,
            },
        })
    }
}

fn returned_current_deposit(
    predecessor: &NativeEcologyRest,
    source: &NativeInferenceAddress,
    emitted: &NativeEmissionAddress,
    returned: &ReturnedScaffoldCurrent,
) -> Result<NativeThreadDeposit, ScaffoldCultivationError> {
    if returned.occurrence == source.occurrence
        || emitted.entering_occurrence != source.occurrence
        || returned.current.is_zero()
    {
        return Err(ScaffoldCultivationError::Return);
    }
    let section = predecessor
        .ecology
        .addressed_section(&source.spool, &source.thread, source.occurrence)
        .map_err(|error| ScaffoldCultivationError::Predecessor(error.to_string()))?;
    if !section.spool().receiver_family.contains(&emitted.receiver)
        || emitted.emitted.from != section.occurrence().entering_native
        || emitted.emitted.to == emitted.emitted.from
    {
        return Err(ScaffoldCultivationError::Return);
    }
    let spool = section.spool();
    if spool
        .threads
        .iter()
        .flat_map(|thread| &thread.occurrences)
        .any(|occurrence| occurrence.occurrence == returned.occurrence)
    {
        return Err(ScaffoldCultivationError::Return);
    }
    let entering_native = emitted.emitted.to;
    let emitting_native = emitted.emitted.from;
    let existing_current = spool
        .threads
        .iter()
        .flat_map(|thread| &thread.parametrons)
        .find(|cell| cell.native == entering_native)
        .ok_or(ScaffoldCultivationError::Return)?
        .current
        .clone();
    let returned_difference = returned.current.subtract(&existing_current);
    if returned_difference.is_zero() {
        return Err(ScaffoldCultivationError::Return);
    }

    let mut cell_by_native = BTreeMap::<NativeStateId, NativeParametronCell>::new();
    for cell in spool.threads.iter().flat_map(|thread| &thread.parametrons) {
        match cell_by_native.get(&cell.native) {
            Some(existing)
                if existing.current != cell.current || existing.section != cell.section =>
            {
                return Err(ScaffoldCultivationError::Deposit(
                    "one native state carries inconsistent inherited current".to_owned(),
                ));
            }
            Some(_) => {}
            None => {
                cell_by_native.insert(cell.native, cell.clone());
            }
        }
    }
    let all_native = spool.native_population.clone();
    let parametrons = all_native
        .iter()
        .map(|native| {
            let mut cell = cell_by_native.get(native).cloned().ok_or_else(|| {
                ScaffoldCultivationError::Deposit("native current absent".to_owned())
            })?;
            cell.relative_phase = ExactUnitConicPhase::identity();
            cell.hand = NativeThreadHand::Along;
            if *native == emitting_native {
                cell.section = returned.current.clone();
                cell.current = returned.current.clone();
            }
            Ok(cell)
        })
        .collect::<Result<Vec<_>, ScaffoldCultivationError>>()?;
    let factors = spool
        .receiver_factors
        .iter()
        .filter(|factor| factor.receiver == emitted.receiver)
        .map(|factor| (factor.native, factor.clone()))
        .collect::<BTreeMap<_, _>>();
    if factors.len() != all_native.len() {
        return Err(ScaffoldCultivationError::Return);
    }
    let consequences = all_native
        .iter()
        .map(|native| NativeReceiverConsequence {
            native: *native,
            receiver: emitted.receiver,
            observation: factors[native].observation,
        })
        .collect::<Vec<_>>();
    let constitutive_responses = parametrons
        .iter()
        .map(|cell| NativeConstitutiveResponse {
            native: cell.native,
            receiver: emitted.receiver,
            presented: cell.section.clone(),
            stored: cell.current.clone(),
        })
        .collect::<Vec<_>>();
    let generator = InputId(
        spool
            .generator_family
            .iter()
            .map(|generator| generator.0)
            .max()
            .unwrap_or(0)
            .checked_add(1)
            .ok_or_else(|| {
                ScaffoldCultivationError::Deposit("generator address overflow".to_owned())
            })?,
    );
    let thread_address = format!("thread/returned-current-{}", returned.occurrence.0);
    let thread = NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address: thread_address.clone(),
        entering_boundary: section.thread().emitting_boundary,
        emitting_boundary: returned.emitting_boundary,
        entering_carrier: "exact-returned-complex-current".to_owned(),
        emitting_carrier: "exact-returned-complex-current".to_owned(),
        occurrences: vec![NativeThreadOccurrence {
            occurrence: returned.occurrence,
            predecessor: Some(source.occurrence),
            entering_port: OccurrencePort::input(returned.occurrence, 0),
            emitting_port: OccurrencePort::output(returned.occurrence, 0),
            entering_native,
            emitting_native,
        }],
        native_support: all_native.clone(),
        incidence: vec![NativeIncidenceTerm {
            occurrence: returned.occurrence,
            from: entering_native,
            to: emitting_native,
            coefficient: 1,
        }],
        parametrons,
        constitutive_responses,
        chronology: vec![generator],
        receiver_consequences: consequences,
        obstruction: None,
        open_exterior: vec![
            "successor and receiver histories outside the returned current remain open".to_owned(),
        ],
        reconstruction_fibre: BTreeSet::from([returned.occurrence]),
    };
    let covector = vec![
        returned_difference.real.clone(),
        returned_difference.imaginary.clone(),
    ];
    let exact_fibre = NativeExactReconstructionFibre {
        address: format!("fibre/returned-current-{}", returned.occurrence.0),
        thread: thread_address.clone(),
        return_operator: ExactRatMatrix::identity(2)
            .map_err(|error| ScaffoldCultivationError::Deposit(error.to_string()))?,
        terminal_covector: covector.clone(),
        returned_covector: covector.clone(),
        particular: covector,
        radical: Vec::new(),
        obstruction: None,
        carrying_pullback: NativePullbackOccurrence {
            left: source.occurrence,
            right: returned.occurrence,
            joining_native: entering_native,
        },
        k3_native_support: all_native.clone(),
        dependent_receiver_fibre: all_native.clone(),
        occurrences: BTreeSet::from([source.occurrence, returned.occurrence]),
        open_exterior: vec![
            "richer returned-current receivers retain the complete causal preimage".to_owned(),
        ],
    };
    let deposit = NativeThreadDeposit {
        schema: NATIVE_THREAD_DEPOSIT_SCHEMA.to_owned(),
        spool_address: source.spool.clone(),
        thread,
        serial_pullbacks: vec![NativeSerialPullback {
            left_thread: source.thread.clone(),
            right_thread: thread_address.clone(),
            joining_boundary: section.thread().emitting_boundary,
            occurrences: BTreeSet::from([NativePullbackOccurrence {
                left: source.occurrence,
                right: returned.occurrence,
                joining_native: entering_native,
            }]),
        }],
        generator_descents: vec![NativeGeneratorDescent {
            generator,
            steps: vec![NativeGeneratorStep {
                from: entering_native,
                to: emitting_native,
                thread: thread_address,
            }],
            open_domain: all_native
                .iter()
                .copied()
                .filter(|native| *native != entering_native)
                .collect(),
        }],
        receiver_factors: Vec::<ReceiverFactor>::new(),
        mutual_constitutive_responses: Vec::new(),
        mixed_constitutive_families: Vec::new(),
        // The returned occurrence does not collapse with its predecessor under this receiver.
        // A shortest separator is owed only when two distinct occurrences share one collapsed
        // native fibre; the exact cross-fibre causal preimage is retained below instead.
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        reconstruction_fibre_deltas: vec![NativeDepositFibreDelta {
            native: emitting_native,
            occurrences: BTreeSet::from([returned.occurrence]),
        }],
        exact_reconstruction_fibres: vec![exact_fibre],
    };
    deposit
        .validate()
        .map_err(|error| ScaffoldCultivationError::Deposit(error.to_string()))?;
    Ok(deposit)
}

fn cultivated_consequence(
    ecology: &SituatedNativeTransportScaffold,
    request: &NativeInferenceRequest,
) -> Result<ScaffoldCultivatedConsequence, ScaffoldCultivationError> {
    let cut = conduct_native_inference(ecology.native(), request.clone())
        .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
    let conducted = cut.conducted_section();
    let emitted = cut.emitted_occurrence().clone();
    let reconstruction_fibre = cut
        .active_section()
        .reconstruction_fibre()
        .occurrences
        .clone();
    let native_start = conducted.native_start.clone();
    let native_end = conducted.native_end.clone();
    let observations = conducted.observations.clone();
    drop(cut);
    let mut resident = ecology
        .native()
        .mount_thread_current(&request.address.spool, &request.address.thread)
        .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
    let current = resident
        .conduct()
        .map_err(|error| ScaffoldCultivationError::Ecology(error.to_string()))?;
    if current.invariant_transport_reuploaded || current.cpu_semantic_replay_after_device {
        return Err(ScaffoldCultivationError::Ecology(
            "resident returned-current conduct replayed its invariant on the host".to_owned(),
        ));
    }
    Ok(ScaffoldCultivatedConsequence {
        native_start,
        native_end,
        observations,
        emitted,
        returned_current_sections: current.sections,
        reconstruction_fibre,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            conduct_native_inference, lift_bf16_excitations, ExteriorModality,
            ForeignBf16Excitation,
        },
        receiver_exact_compression::ReceiverId,
    };
    use num_bigint::BigInt;
    use relational_geometry::Rat;

    fn excitation(event: u64, entering: u16, returned: u16) -> ForeignBf16Excitation {
        ForeignBf16Excitation {
            event: EventId(event),
            predecessor: None,
            entering_boundary: BoundaryId(event),
            emitting_boundary: BoundaryId(event + 10),
            source_occurrence: format!("cold/{event}"),
            exterior_modality: ExteriorModality::Text,
            entering_codewords: vec![entering],
            returned_codewords: vec![returned],
            interventions: BTreeSet::from([format!("intervention/{event}")]),
            receiver_consequences: BTreeSet::from([format!("consequence/{event}")]),
        }
    }

    #[test]
    fn returned_current_survives_scaffold_withdrawal_and_targeted_ablation() {
        let lifted = lift_bf16_excitations(
            ReceiverId(7),
            vec![excitation(1, 0x3f80, 0x4000), excitation(2, 0x4040, 0x4080)],
        )
        .expect("lift");
        let (predecessor, departed) =
            super::super::consume_dismantling_return(lifted).expect("move-owned handoff");
        assert_eq!(departed.cold_witness.excitations.len(), 2);
        let source = NativeInferenceAddress {
            spool: predecessor.ecology.spools[0].address.clone(),
            thread: predecessor.ecology.spools[0].threads[0].address.clone(),
            occurrence: EventId(1),
        };
        let cut = conduct_native_inference(
            &predecessor.ecology,
            NativeInferenceRequest {
                address: source.clone(),
                receiver: ReceiverId(7),
            },
        )
        .expect("emission");
        let emitted = cut.emitted_occurrence().clone();
        drop(cut);
        let cultivated = ScaffoldCultivatedRest::cultivate(
            predecessor,
            source,
            emitted,
            ReturnedScaffoldCurrent {
                occurrence: EventId(100),
                emitting_boundary: BoundaryId(101),
                current: ExactComplexWaveCurrent::new(
                    Rat::from_integer(BigInt::from(9)),
                    Rat::from_integer(BigInt::from(1)),
                ),
            },
        )
        .expect("cultivate");
        let released = cultivated.release().expect("release");
        assert!(released.receipt.declared_consequence_preserved);
        assert!(released.receipt.cultivated_ablation_removed_conduct);
        assert!(released.receipt.restoration_recovered_successor);
        assert!(released.receipt.final_source_detached);
        assert_eq!(released.hot.native().spools[0].threads.len(), 1);
        assert_eq!(released.departed_inherited.len(), 2);
        assert!(released.receipt.departed_reconstruction_fibre_population >= 2);
    }
}
