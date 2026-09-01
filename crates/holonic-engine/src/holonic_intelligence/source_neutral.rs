use std::collections::BTreeSet;

use num_bigint::BigInt;
use relational_geometry::Rat;
use serde::Serialize;
use thiserror::Error;

use crate::generator_native_rest::{
    GeneratorNativeRest, GeneratorNativeRestError, NativeGenerator,
};
use crate::native_ecology::recurrent_return::{RecurrentReturnRefusal, recurrence_trace};
use crate::native_spool::{
    NATIVE_SPOOL_SCHEMA, NATIVE_THREAD_SCHEMA, NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
    NativeCollapsedFibre, NativeConstitutiveResponse, NativeGeneratorDescent, NativeGeneratorStep,
    NativeIncidenceTerm, NativeMutualConstitutiveResponse, NativeOccurrenceSection,
    NativeParametronCell, NativePullbackOccurrence, NativeReceiverConsequence,
    NativeSerialPullback, NativeSpool, NativeSpoolRefusal, NativeThread, NativeThreadHand,
    NativeThreadOccurrence, NativeTransportScaffold,
};
use crate::receiver_exact_compression::{InputId, Observation, ReceiverId};
use crate::receiver_history_compression::{NativeStateId, NativeTransport, ReceiverFactor};
use crate::{BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort};

use super::{
    CultivationPackagingError, ExteriorReturnOccurrence, InferenceCirculation,
    NativeInferenceAddress, NativeInferenceError, NativeInferenceRequest,
    SourceDetachedCultivatedRecurrence, SourceNeutralCultivationClosure, conduct_native_inference,
};

const DIRECT_SOURCE_NEUTRAL_SCHEMA: &str = "holonic-engine.direct-source-neutral-closure.v1";

fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(
        Rat::from_integer(BigInt::from(real)),
        Rat::from_integer(BigInt::from(imaginary)),
    )
}

fn thread(
    address: &str,
    event: EventId,
    predecessor: Option<EventId>,
    entering_boundary: BoundaryId,
    emitting_boundary: BoundaryId,
    from: NativeStateId,
    to: NativeStateId,
) -> NativeThread {
    let receiver = ReceiverId(9);
    NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address: address.to_owned(),
        entering_boundary,
        emitting_boundary,
        entering_carrier: "exact-complex-current".to_owned(),
        emitting_carrier: "exact-complex-current".to_owned(),
        occurrences: vec![NativeThreadOccurrence {
            occurrence: event,
            predecessor,
            entering_port: OccurrencePort::input(event, 0),
            emitting_port: OccurrencePort::output(event, 0),
            entering_native: from,
            emitting_native: to,
        }],
        native_support: BTreeSet::from([from, to]),
        incidence: vec![NativeIncidenceTerm {
            occurrence: event,
            from,
            to,
            coefficient: 1,
        }],
        parametrons: vec![
            NativeParametronCell {
                native: from,
                section: current(1, 0),
                current: current(0, 1),
                relative_phase: ExactUnitConicPhase::identity(),
                hand: NativeThreadHand::Along,
            },
            NativeParametronCell {
                native: to,
                section: current(0, 1),
                current: current(-1, 0),
                relative_phase: ExactUnitConicPhase::identity(),
                hand: NativeThreadHand::Along,
            },
        ],
        sections: vec![NativeOccurrenceSection::from_currents(
            event,
            current(0, 1),
            current(-1, 0),
        )],
        constitutive_responses: vec![
            NativeConstitutiveResponse {
                native: from,
                receiver,
                presented: current(1, 0),
                stored: current(0, 1),
            },
            NativeConstitutiveResponse {
                native: to,
                receiver,
                presented: current(0, 1),
                stored: current(-1, 0),
            },
        ],
        chronology: vec![InputId(7)],
        receiver_consequences: vec![
            NativeReceiverConsequence {
                native: from,
                receiver,
                observation: Observation(from.0 + 100),
            },
            NativeReceiverConsequence {
                native: to,
                receiver,
                observation: Observation(to.0 + 100),
            },
        ],
        obstruction: None,
        open_exterior: vec!["receivers outside the direct finite family remain open".to_owned()],
        reconstruction_fibre: BTreeSet::from([event]),
    }
}

/// Construct one productive native cycle from intrinsic current/incidence values alone.
/// No serialized predecessor, source corpus, foreign tensor chart, or historical output is read.
pub fn direct_source_neutral_rest() -> Result<NativeTransportScaffold, NativeSpoolRefusal> {
    let first = EventId(1);
    let second = EventId(2);
    let left = thread(
        "thread/outward",
        first,
        None,
        BoundaryId(10),
        BoundaryId(11),
        NativeStateId(0),
        NativeStateId(1),
    );
    let right = thread(
        "thread/return",
        second,
        Some(first),
        BoundaryId(11),
        BoundaryId(10),
        NativeStateId(1),
        NativeStateId(0),
    );
    let spool = NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: "spool/direct-cycle".to_owned(),
        native_population: BTreeSet::from([NativeStateId(0), NativeStateId(1)]),
        receiver_family: BTreeSet::from([ReceiverId(9)]),
        generator_family: BTreeSet::from([InputId(7)]),
        threads: vec![left, right],
        serial_pullbacks: vec![
            NativeSerialPullback {
                left_thread: "thread/outward".to_owned(),
                right_thread: "thread/return".to_owned(),
                joining_boundary: BoundaryId(11),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: first,
                    right: second,
                    joining_native: NativeStateId(1),
                }]),
            },
            NativeSerialPullback {
                left_thread: "thread/return".to_owned(),
                right_thread: "thread/outward".to_owned(),
                joining_boundary: BoundaryId(10),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: second,
                    right: first,
                    joining_native: NativeStateId(0),
                }]),
            },
        ],
        generator_descents: vec![NativeGeneratorDescent {
            generator: InputId(7),
            steps: vec![
                NativeGeneratorStep {
                    from: NativeStateId(0),
                    to: NativeStateId(1),
                    thread: "thread/outward".to_owned(),
                },
                NativeGeneratorStep {
                    from: NativeStateId(1),
                    to: NativeStateId(0),
                    thread: "thread/return".to_owned(),
                },
            ],
            open_domain: BTreeSet::new(),
        }],
        receiver_factors: vec![
            ReceiverFactor {
                native: NativeStateId(0),
                receiver: ReceiverId(9),
                observation: Observation(100),
            },
            ReceiverFactor {
                native: NativeStateId(1),
                receiver: ReceiverId(9),
                observation: Observation(101),
            },
        ],
        mutual_constitutive_responses: vec![NativeMutualConstitutiveResponse {
            left_occurrence: first,
            right_occurrence: second,
            left_native: NativeStateId(0),
            right_native: NativeStateId(1),
            receiver: ReceiverId(9),
            storage: Rat::from_integer(BigInt::from(1)),
        }],
        reconstruction_fibres: vec![
            NativeCollapsedFibre {
                native: NativeStateId(0),
                occurrences: BTreeSet::from([second]),
            },
            NativeCollapsedFibre {
                native: NativeStateId(1),
                occurrences: BTreeSet::from([first]),
            },
        ],
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec!["larger receiver histories remain open".to_owned()],
    };
    let scaffold = NativeTransportScaffold {
        schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        address: "scaffold/direct-source-neutral".to_owned(),
        spools: vec![spool],
        compositions: Vec::new(),
        open_exterior: vec!["additional compatible native organs remain open".to_owned()],
    };
    scaffold.validate()?;
    Ok(scaffold)
}

fn recurrent_projection(
    rest: &NativeTransportScaffold,
) -> Result<(GeneratorNativeRest, InputId), SourceNeutralClosureError> {
    let spool = rest
        .spools
        .first()
        .ok_or(SourceNeutralClosureError::Malformed)?;
    let generator = *spool
        .generator_family
        .first()
        .ok_or(SourceNeutralClosureError::Malformed)?;
    let action = spool
        .generator_descents
        .iter()
        .find(|descent| descent.generator == generator)
        .ok_or(SourceNeutralClosureError::Malformed)?;
    let base = GeneratorNativeRest::new(
        spool.native_population.iter().copied().collect(),
        spool.receiver_factors.clone(),
        vec![NativeGenerator {
            generator,
            transport: action
                .steps
                .iter()
                .map(|step| NativeTransport {
                    from: step.from,
                    to: step.to,
                })
                .collect(),
        }],
    )?;
    Ok((base, generator))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DirectWorldReturn {
    pub occurrence: String,
    pub returned_content: u64,
}

#[derive(Debug, Serialize)]
pub struct SourceNeutralResidentClosureReceipt {
    pub schema: String,
    pub direct_rest_roundtrip: bool,
    pub historical_output_consulted: bool,
    pub source_artifact_consulted: bool,
    pub foreign_executor_present: bool,
    pub plural_future_population: usize,
    pub reconstruction_fibre_population: usize,
    pub later_current_population: usize,
    pub off_diagonal_complex_contact_present: bool,
    pub complex_transport_has_quadrature: bool,
    pub resident_launches: u64,
    pub resident_synchronizations: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
    pub actual_return_matches_emission: bool,
    pub source_detached_productive_wire: bool,
    pub held_out_later_conduct_changed: bool,
    pub targeted_withdrawal_exact: bool,
    pub restoration_exact: bool,
}

pub struct SourceNeutralResidentClosure {
    pub rest: NativeTransportScaffold,
    pub cultivation: SourceNeutralCultivationClosure,
    pub receipt: SourceNeutralResidentClosureReceipt,
}

/// Close one direct resident inference/return/cultivation cycle without consulting the filesystem.
pub fn close_direct_source_neutral_cycle()
-> Result<SourceNeutralResidentClosure, SourceNeutralClosureError> {
    let rest = direct_source_neutral_rest()?;
    let rest_wire = rest.canonical_bytes()?;
    let remounted = NativeTransportScaffold::read(&rest_wire)?;
    let request = NativeInferenceRequest {
        address: NativeInferenceAddress {
            spool: "spool/direct-cycle".to_owned(),
            thread: "thread/outward".to_owned(),
            occurrence: EventId(1),
        },
        receiver: ReceiverId(9),
    };
    let circulation = conduct_native_inference(&remounted, request)?;
    let emitted = circulation.emitted_occurrence().clone();
    let emitted_occurrence = format!(
        "native-event/{}/receiver/{}/{}->{}",
        emitted.entering_occurrence.0,
        emitted.receiver.0,
        emitted.emitted.from.0,
        emitted.emitted.to.0
    );
    let world = DirectWorldReturn {
        occurrence: "world-return/direct-cycle/1".to_owned(),
        returned_content: 1,
    };
    let actual_return: ExteriorReturnOccurrence<DirectWorldReturn> =
        circulation.return_aperture().clone().admit(world);

    let mut resident_current =
        remounted.mount_thread_current("spool/direct-cycle", "thread/outward")?;
    let complex_return = resident_current.conduct()?;
    let complex_transport_has_quadrature = complex_return.sections.iter().flatten().any(|value| {
        value.real != Rat::from_integer(BigInt::from(0))
            && value.imaginary != Rat::from_integer(BigInt::from(0))
    });
    let off_diagonal_complex_contact_present = remounted.spools.iter().any(|spool| {
        spool.mutual_constitutive_responses.iter().any(|response| {
            response.left_occurrence != response.right_occurrence
                && response.left_native != response.right_native
        })
    });

    let (base, generator) = recurrent_projection(&remounted)?;
    let forward_lineage = recurrence_trace(&base, generator, NativeStateId(0), None)?;
    let cultivation = SourceDetachedCultivatedRecurrence::found_from_native_return(
        base,
        generator,
        forward_lineage,
        emitted_occurrence.clone(),
        actual_return.returned.occurrence.clone(),
        actual_return.returned.returned_content,
    )?;
    let productive_wire = cultivation.productive.canonical_bytes()?;
    let remounted_productive = SourceDetachedCultivatedRecurrence::read(&productive_wire)?;
    let held_out = remounted_productive.held_out_start();
    let predecessor = remounted_productive.predecessor_trace(held_out)?;
    let successor = remounted_productive.successor_trace(held_out)?;
    let withdrawn = remounted_productive.withdrawn_trace(held_out)?;
    let restored = remounted_productive.restored_successor_action()?;
    let later_current_population = circulation.successor_requests().len();
    let receipt = SourceNeutralResidentClosureReceipt {
        schema: DIRECT_SOURCE_NEUTRAL_SCHEMA.to_owned(),
        direct_rest_roundtrip: remounted == rest,
        historical_output_consulted: false,
        source_artifact_consulted: false,
        foreign_executor_present: false,
        plural_future_population: circulation.face().plural_futures.len(),
        reconstruction_fibre_population: circulation.reconstruction().fibres.len(),
        later_current_population,
        off_diagonal_complex_contact_present,
        complex_transport_has_quadrature,
        resident_launches: complex_return.launches,
        resident_synchronizations: complex_return.synchronizations,
        invariant_transport_reuploaded: complex_return.invariant_transport_reuploaded,
        cpu_semantic_replay_after_device: complex_return.cpu_semantic_replay_after_device,
        actual_return_matches_emission: cultivation.exterior.emitted_occurrence
            == emitted_occurrence
            && cultivation.exterior.returned_occurrence == actual_return.returned.occurrence,
        source_detached_productive_wire: !productive_wire.is_empty(),
        held_out_later_conduct_changed: predecessor != successor,
        targeted_withdrawal_exact: withdrawn == predecessor,
        restoration_exact: restored == *remounted_productive.successor_action(),
    };
    if !receipt.direct_rest_roundtrip
        || receipt.historical_output_consulted
        || receipt.source_artifact_consulted
        || receipt.foreign_executor_present
        || receipt.plural_future_population < 2
        || receipt.reconstruction_fibre_population != receipt.plural_future_population
        || receipt.later_current_population == 0
        || !receipt.off_diagonal_complex_contact_present
        || !receipt.complex_transport_has_quadrature
        || receipt.resident_launches == 0
        || receipt.resident_synchronizations == 0
        || receipt.invariant_transport_reuploaded
        || receipt.cpu_semantic_replay_after_device
        || !receipt.actual_return_matches_emission
        || !receipt.source_detached_productive_wire
        || !receipt.held_out_later_conduct_changed
        || !receipt.targeted_withdrawal_exact
        || !receipt.restoration_exact
    {
        return Err(SourceNeutralClosureError::Malformed);
    }
    drop(circulation);
    Ok(SourceNeutralResidentClosure {
        rest,
        cultivation,
        receipt,
    })
}

#[derive(Debug, Error)]
pub enum SourceNeutralClosureError {
    #[error("native direct rest refused: {0}")]
    Native(#[from] NativeSpoolRefusal),
    #[error("native inference refused: {0}")]
    Inference(#[from] NativeInferenceError),
    #[error("generator-native projection refused: {0}")]
    Generator(#[from] GeneratorNativeRestError),
    #[error("recurrent return refused: {0}")]
    Recurrent(#[from] RecurrentReturnRefusal),
    #[error("cultivation packaging refused: {0}")]
    Cultivation(#[from] CultivationPackagingError),
    #[error("the direct source-neutral closure is malformed")]
    Malformed,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_rest_has_no_source_or_foreign_fields() {
        let rest = direct_source_neutral_rest().expect("direct rest");
        let text = String::from_utf8(rest.canonical_bytes().expect("wire")).expect("json");
        for forbidden in ["source_surface", "foreign", "output/"] {
            assert!(
                !text.contains(forbidden),
                "productive rest retained {forbidden}"
            );
        }
    }

    #[test]
    fn direct_rest_projects_one_total_recurrent_action() {
        let rest = direct_source_neutral_rest().expect("direct rest");
        let (projection, generator) = recurrent_projection(&rest).expect("projection");
        assert_eq!(
            recurrence_trace(&projection, generator, NativeStateId(0), None).expect("trace"),
            vec![NativeStateId(0), NativeStateId(1), NativeStateId(0)]
        );
    }
}
