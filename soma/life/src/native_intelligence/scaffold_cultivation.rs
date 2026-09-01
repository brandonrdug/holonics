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
        NativeGeneratorDescent, NativeGeneratorStep, NativeIncidenceTerm, NativeInterchangeReceipt,
        NativeMutualConstitutiveResponse, NativeOccurrenceSection, NativeOrderedConsequence,
        NativeParametronCell, NativePullbackOccurrence, NativeReceiverConsequence,
        NativeSerialPullback, NativeSituatedThreadWithdrawal, NativeThread, NativeThreadDeposit,
        NativeThreadDepositReceipt, NativeThreadHand, NativeThreadObstruction,
        NativeThreadOccurrence, NativeTransportScaffold, SituatedNativeTransportScaffold,
        NATIVE_THREAD_DEPOSIT_SCHEMA, NATIVE_THREAD_SCHEMA,
    },
    receiver_exact_compression::{InputId, Observation},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactRatMatrix, ExactUnitConicPhase,
    OccurrencePort,
};
use num_rational::BigRational as Rat;
use serde::Serialize;
use thiserror::Error;

use super::NativeEcologyRest;

/// One exact exterior current returning through a particular emitted native section.
/// The native successor current is derived from this interaction and the standing local current.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnedScaffoldInteraction {
    pub emitted: NativeEmissionAddress,
    pub occurrence: EventId,
    pub emitting_boundary: BoundaryId,
    pub exterior_current: ExactComplexWaveCurrent,
    pub storage: Rat,
    pub contact_support: BTreeSet<NativeStateId>,
}

impl ReturnedScaffoldInteraction {
    pub fn found(
        emitted: NativeEmissionAddress,
        occurrence: EventId,
        emitting_boundary: BoundaryId,
        exterior_current: ExactComplexWaveCurrent,
        storage: Rat,
        additional_contact_support: BTreeSet<NativeStateId>,
    ) -> Result<Self, ScaffoldCultivationError> {
        if occurrence == emitted.entering_occurrence
            || exterior_current.is_zero()
            || storage == Rat::from_integer(0.into())
        {
            return Err(ScaffoldCultivationError::Return);
        }
        let mut contact_support = BTreeSet::from([emitted.emitted.from, emitted.emitted.to]);
        contact_support.extend(additional_contact_support);
        Ok(Self {
            emitted,
            occurrence,
            emitting_boundary,
            exterior_current,
            storage,
            contact_support,
        })
    }
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
    causal_cone: BTreeSet<NativeStateId>,
    outside_thread_population: usize,
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
    pub causal_cone_population: usize,
    pub outside_thread_population: usize,
    pub outside_cone_morphology_unchanged: bool,
    pub inactive_native_not_deposited: bool,
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
        returned: ReturnedScaffoldInteraction,
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
        let emitted = &returned.emitted;
        let causal_cone = returned.contact_support.clone();
        let outside_before = outside_cone_threads(&predecessor.ecology, &causal_cone)?;
        let deposit = returned_current_deposit(&predecessor, &source, &returned)?;
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
        let outside_after = outside_cone_threads(ecology.native(), &causal_cone)?;
        if outside_before != outside_after {
            return Err(ScaffoldCultivationError::Consequence);
        }
        Ok(Self {
            ecology,
            cultivated_request,
            inherited_threads,
            deposit_receipt,
            causal_cone,
            outside_thread_population: outside_before.len(),
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
            causal_cone,
            outside_thread_population,
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
        let inactive_native_not_deposited = ecology
            .native()
            .spools
            .iter()
            .all(|spool| spool.native_population.is_subset(&causal_cone));
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
                causal_cone_population: causal_cone.len(),
                outside_thread_population,
                outside_cone_morphology_unchanged: true,
                inactive_native_not_deposited,
                final_source_detached,
            },
        })
    }
}

fn outside_cone_threads(
    ecology: &NativeTransportScaffold,
    causal_cone: &BTreeSet<NativeStateId>,
) -> Result<Vec<OutsideThreadSnapshot>, ScaffoldCultivationError> {
    let mut faces = ecology
        .spools
        .iter()
        .flat_map(|spool| {
            spool
                .threads
                .iter()
                .filter(|thread| thread.native_support.is_disjoint(causal_cone))
                .map(move |thread| OutsideThreadSnapshot::from_thread(&spool.address, thread))
        })
        .collect::<Vec<_>>();
    faces.sort_by(|left, right| {
        (&left.spool_address, &left.thread_address)
            .cmp(&(&right.spool_address, &right.thread_address))
    });
    Ok(faces)
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OutsideThreadSnapshot {
    spool_address: String,
    thread_address: String,
    entering_boundary: BoundaryId,
    emitting_boundary: BoundaryId,
    entering_carrier: String,
    emitting_carrier: String,
    occurrences: Vec<NativeThreadOccurrence>,
    native_support: BTreeSet<NativeStateId>,
    incidence: Vec<NativeIncidenceTerm>,
    parametrons: Vec<NativeParametronCell>,
    sections: Vec<NativeOccurrenceSection>,
    constitutive_responses: Vec<NativeConstitutiveResponse>,
    chronology: Vec<InputId>,
    receiver_consequences: Vec<NativeReceiverConsequence>,
    obstruction: Option<NativeThreadObstruction>,
    open_exterior: Vec<String>,
    reconstruction_fibre: BTreeSet<EventId>,
}

impl OutsideThreadSnapshot {
    fn from_thread(spool_address: &str, thread: &NativeThread) -> Self {
        Self {
            spool_address: spool_address.to_owned(),
            thread_address: thread.address.clone(),
            entering_boundary: thread.entering_boundary,
            emitting_boundary: thread.emitting_boundary,
            entering_carrier: thread.entering_carrier.clone(),
            emitting_carrier: thread.emitting_carrier.clone(),
            occurrences: thread.occurrences.clone(),
            native_support: thread.native_support.clone(),
            incidence: thread.incidence.clone(),
            parametrons: thread.parametrons.clone(),
            sections: thread.sections.clone(),
            constitutive_responses: thread.constitutive_responses.clone(),
            chronology: thread.chronology.clone(),
            receiver_consequences: thread.receiver_consequences.clone(),
            obstruction: thread.obstruction.clone(),
            open_exterior: thread.open_exterior.clone(),
            reconstruction_fibre: thread.reconstruction_fibre.clone(),
        }
    }
}

fn returned_current_deposit(
    predecessor: &NativeEcologyRest,
    source: &NativeInferenceAddress,
    returned: &ReturnedScaffoldInteraction,
) -> Result<NativeThreadDeposit, ScaffoldCultivationError> {
    let emitted = &returned.emitted;
    if returned.occurrence <= source.occurrence || emitted.entering_occurrence != source.occurrence
    {
        return Err(ScaffoldCultivationError::Return);
    }
    let section = predecessor
        .ecology
        .addressed_section(&source.spool, &source.thread, source.occurrence)
        .map_err(|error| ScaffoldCultivationError::Predecessor(error.to_string()))?;
    if !section.spool().receiver_family.contains(&emitted.receiver)
        || emitted.emitted.from != section.occurrence().entering_native
        || emitted.emitted.to != section.occurrence().emitting_native
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
    let causal_cone = returned.contact_support.clone();
    if !causal_cone.is_subset(&spool.native_population)
        || !causal_cone.contains(&entering_native)
        || !causal_cone.contains(&emitting_native)
    {
        return Err(ScaffoldCultivationError::Return);
    }
    let existing_current = section.emitting_parametron().current.clone();
    let returned_difference = returned.exterior_current.scaled(&returned.storage);
    let returned_current = existing_current.add(&returned_difference);
    if returned_difference.is_zero() {
        return Err(ScaffoldCultivationError::Return);
    }

    let mut cell_by_native = BTreeMap::<NativeStateId, NativeParametronCell>::new();
    for cell in spool
        .threads
        .iter()
        .flat_map(|thread| &thread.parametrons)
        .filter(|cell| causal_cone.contains(&cell.native))
    {
        match cell_by_native.get(&cell.native) {
            Some(existing)
                if existing.current != cell.current || existing.section != cell.section =>
            {
                return Err(ScaffoldCultivationError::Deposit(
                    "one causal-cone state carries inconsistent inherited current".to_owned(),
                ));
            }
            Some(_) => {}
            None => {
                cell_by_native.insert(cell.native, cell.clone());
            }
        }
    }
    if cell_by_native.len() != causal_cone.len() {
        return Err(ScaffoldCultivationError::Return);
    }
    let parametrons = causal_cone
        .iter()
        .map(|native| {
            let mut cell = cell_by_native[native].clone();
            cell.relative_phase = ExactUnitConicPhase::identity();
            cell.hand = NativeThreadHand::Along;
            if *native == emitting_native {
                cell.section = returned_current.clone();
                cell.current = returned_current.clone();
            }
            cell
        })
        .collect::<Vec<_>>();
    let factors = spool
        .receiver_factors
        .iter()
        .filter(|factor| {
            factor.receiver == emitted.receiver && causal_cone.contains(&factor.native)
        })
        .map(|factor| (factor.native, factor.clone()))
        .collect::<BTreeMap<_, _>>();
    if factors.len() != causal_cone.len() {
        return Err(ScaffoldCultivationError::Return);
    }
    let consequences = causal_cone
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
    let thread_address = format!("thread/returned-interaction-{}", returned.occurrence.0);
    let thread = NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address: thread_address.clone(),
        entering_boundary: section.thread().emitting_boundary,
        emitting_boundary: returned.emitting_boundary,
        entering_carrier: "exact-returned-local-interaction-current".to_owned(),
        emitting_carrier: "exact-returned-local-interaction-current".to_owned(),
        occurrences: vec![NativeThreadOccurrence {
            occurrence: returned.occurrence,
            predecessor: Some(source.occurrence),
            entering_port: OccurrencePort::input(returned.occurrence, 0),
            emitting_port: OccurrencePort::output(returned.occurrence, 0),
            entering_native,
            emitting_native,
        }],
        native_support: causal_cone.clone(),
        incidence: vec![NativeIncidenceTerm {
            occurrence: returned.occurrence,
            from: entering_native,
            to: emitting_native,
            coefficient: 1,
        }],
        parametrons,
        sections: vec![NativeOccurrenceSection::from_currents(
            returned.occurrence,
            existing_current,
            returned_current,
        )],
        constitutive_responses,
        chronology: vec![generator],
        receiver_consequences: consequences,
        obstruction: None,
        open_exterior: vec![
            "successor and receiver histories outside the returned local interaction remain open"
                .to_owned(),
        ],
        reconstruction_fibre: BTreeSet::from([returned.occurrence]),
    };
    let covector = vec![
        returned_difference.real.clone(),
        returned_difference.imaginary.clone(),
    ];
    let exact_fibre = NativeExactReconstructionFibre {
        address: format!("fibre/returned-interaction-{}", returned.occurrence.0),
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
        k3_native_support: causal_cone.clone(),
        dependent_receiver_fibre: causal_cone.clone(),
        occurrences: BTreeSet::from([source.occurrence, returned.occurrence]),
        open_exterior: vec![
            "richer returned-interaction receivers retain the complete causal preimage".to_owned(),
        ],
    };
    let interchanges = spool
        .threads
        .iter()
        .filter(|candidate| candidate.native_support.is_disjoint(&causal_cone))
        .map(|candidate| {
            let lineage_occurrences = candidate
                .occurrences
                .iter()
                .map(|occurrence| occurrence.occurrence)
                .chain(std::iter::once(returned.occurrence))
                .collect::<BTreeSet<_>>();
            let obstructions = candidate.obstruction.iter().cloned().collect();
            let left_then_right = NativeOrderedConsequence {
                order: vec![candidate.address.clone(), thread_address.clone()],
                successor: emitting_native,
                obstructions,
                lineage_occurrences: lineage_occurrences.clone(),
                logical_resources: BTreeMap::new(),
            };
            let right_then_left = NativeOrderedConsequence {
                order: vec![thread_address.clone(), candidate.address.clone()],
                successor: emitting_native,
                obstructions: left_then_right.obstructions.clone(),
                lineage_occurrences,
                logical_resources: BTreeMap::new(),
            };
            NativeInterchangeReceipt {
                left_thread: candidate.address.clone(),
                right_thread: thread_address.clone(),
                left_then_right,
                right_then_left,
            }
        })
        .collect();
    let pullback_occurrences = section
        .thread()
        .occurrences
        .iter()
        .filter(|occurrence| occurrence.emitting_native == entering_native)
        .map(|occurrence| NativePullbackOccurrence {
            left: occurrence.occurrence,
            right: returned.occurrence,
            joining_native: entering_native,
        })
        .collect();
    let deposit = NativeThreadDeposit {
        schema: NATIVE_THREAD_DEPOSIT_SCHEMA.to_owned(),
        spool_address: source.spool.clone(),
        thread,
        serial_pullbacks: vec![NativeSerialPullback {
            left_thread: source.thread.clone(),
            right_thread: thread_address.clone(),
            joining_boundary: section.thread().emitting_boundary,
            occurrences: pullback_occurrences,
        }],
        generator_descents: vec![NativeGeneratorDescent {
            generator,
            steps: vec![NativeGeneratorStep {
                from: entering_native,
                to: emitting_native,
                thread: thread_address,
            }],
            open_domain: spool
                .native_population
                .iter()
                .copied()
                .filter(|native| *native != entering_native)
                .collect(),
        }],
        receiver_factors: Vec::<ReceiverFactor>::new(),
        mutual_constitutive_responses: vec![NativeMutualConstitutiveResponse {
            left_occurrence: source.occurrence,
            right_occurrence: returned.occurrence,
            left_native: emitting_native,
            right_native: entering_native,
            receiver: emitted.receiver,
            storage: returned.storage.clone(),
        }],
        mixed_constitutive_families: Vec::new(),
        shortest_separators: Vec::new(),
        interchanges,
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
            conduct_native_inference, Bf16ExcitationDismantling, ExteriorModality,
            ForeignBf16Excitation,
        },
        receiver_exact_compression::ReceiverId,
        soulkiller::dismantle,
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
    fn returned_local_interaction_preserves_disjoint_morphology_and_survives_release() {
        let lifted = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![excitation(1, 0x3f80, 0x4000), excitation(2, 0x4040, 0x4080)],
        })
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
        let returned = ReturnedScaffoldInteraction::found(
            emitted,
            EventId(100),
            BoundaryId(101),
            ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(9)),
                Rat::from_integer(BigInt::from(1)),
            ),
            Rat::from_integer(BigInt::from(1)),
            BTreeSet::new(),
        )
        .expect("world return");
        let cultivated =
            ScaffoldCultivatedRest::cultivate(predecessor, source, returned).expect("cultivate");
        let released = cultivated.release().expect("release");
        assert!(released.receipt.declared_consequence_preserved);
        assert!(released.receipt.cultivated_ablation_removed_conduct);
        assert!(released.receipt.restoration_recovered_successor);
        assert!(released.receipt.final_source_detached);
        assert!(released.receipt.outside_cone_morphology_unchanged);
        assert!(released.receipt.inactive_native_not_deposited);
        assert_eq!(released.receipt.causal_cone_population, 2);
        assert_eq!(released.receipt.outside_thread_population, 1);
        assert_eq!(released.hot.native().spools[0].threads.len(), 1);
        assert_eq!(released.departed_inherited.len(), 2);
        assert!(released.receipt.departed_reconstruction_fibre_population >= 2);
    }

    #[test]
    fn declared_global_contact_returns_the_complete_native_causal_cone() {
        let lifted = dismantle(Bf16ExcitationDismantling {
            receiver: ReceiverId(7),
            excitations: vec![
                excitation(1, 0x3f80, 0x4000),
                excitation(2, 0x4040, 0x4080),
                excitation(3, 0x40a0, 0x40c0),
            ],
        })
        .expect("lift");
        let (predecessor, _) =
            super::super::consume_dismantling_return(lifted).expect("move-owned handoff");
        let total_native = predecessor.ecology.spools[0].native_population.clone();
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
        let returned = ReturnedScaffoldInteraction::found(
            cut.emitted_occurrence().clone(),
            EventId(100),
            BoundaryId(101),
            ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(1)),
                Rat::from_integer(BigInt::from(1)),
            ),
            Rat::from_integer(BigInt::from(1)),
            total_native.clone(),
        )
        .expect("global return");
        drop(cut);
        let cultivated = ScaffoldCultivatedRest::cultivate(predecessor, source, returned)
            .expect("global cultivation");
        let cultivated_thread = cultivated
            .ecology()
            .native()
            .spools
            .iter()
            .flat_map(|spool| &spool.threads)
            .find(|thread| thread.address == cultivated.cultivated_request().address.thread)
            .expect("cultivated thread");
        assert_eq!(cultivated_thread.native_support, total_native);
    }
}
