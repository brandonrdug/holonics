//! One declared native body for tests and demos.
//!
//! Every state, occurrence, thread, generator, receiver, and current below is written down
//! directly. This module lifts nothing, decodes nothing, and reconstructs nothing: it is not a
//! function from a recorded event list to a native body, and it makes no claim whatever about
//! excitation, about an exterior source, or about a Soulkiller founding. It exists only so that
//! owners which need *a* valid `NativeTransportScaffold` — mount, conduct, commit, snapshot,
//! remount, export, ABI — can obtain one without borrowing a founding claim.
//!
//! The declared body is two native states `0` and `1`, two threads whose occurrences `1` and `2`
//! close the cycle `0 -> 1 -> 0`, one shared generator `InputId(7)` whose descent is total, and
//! one receiver `ReceiverId(9)`.

use std::collections::BTreeSet;

use relational_geometry::Rat;

use crate::receiver_exact_compression::{InputId, Observation, ReceiverId};
use crate::receiver_history_compression::{NativeStateId, ReceiverFactor};
use crate::soulkiller::SoulkillerDismantlingReturn;
use crate::{BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort};

use super::{
    NATIVE_SPOOL_SCHEMA, NATIVE_THREAD_SCHEMA, NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
    NativeCollapsedFibre, NativeConstitutiveResponse, NativeGeneratorDescent, NativeGeneratorStep,
    NativeIncidenceTerm, NativeOccurrenceSection, NativeParametronCell, NativePullbackOccurrence,
    NativeReceiverConsequence, NativeSerialPullback, NativeSpool, NativeThread, NativeThreadHand,
    NativeThreadOccurrence, NativeTransportScaffold, RECEIVER_INSUFFICIENCY_SCHEMA,
    ReceiverInsufficiency, ReceiverInsufficiencyCause,
};

/// The receiver this declared body admits.
pub const FIXTURE_RECEIVER: ReceiverId = ReceiverId(9);

/// A receiver outside the declared family, used only to name an insufficiency.
pub const FIXTURE_UNADMITTED_RECEIVER: ReceiverId = ReceiverId(10);

/// The generator both declared threads share.
pub const FIXTURE_GENERATOR: InputId = InputId(7);

pub fn current(real: i64, imaginary: i64) -> ExactComplexWaveCurrent {
    ExactComplexWaveCurrent::new(
        Rat::from_integer(real.into()),
        Rat::from_integer(imaginary.into()),
    )
}

/// One declared thread carrying exactly one occurrence between two declared native states.
#[allow(clippy::too_many_arguments)]
pub fn thread(
    address: &str,
    event: u64,
    predecessor: Option<u64>,
    entering_boundary: u64,
    emitting_boundary: u64,
    from: u64,
    to: u64,
    generator: u64,
) -> NativeThread {
    let occurrence = EventId(event);
    let from = NativeStateId(from);
    let to = NativeStateId(to);
    let receiver = FIXTURE_RECEIVER;
    NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address: address.to_owned(),
        entering_boundary: BoundaryId(entering_boundary),
        emitting_boundary: BoundaryId(emitting_boundary),
        entering_carrier: "native-complex-section".to_owned(),
        emitting_carrier: "native-complex-section".to_owned(),
        occurrences: vec![NativeThreadOccurrence {
            occurrence,
            predecessor: predecessor.map(EventId),
            entering_port: OccurrencePort::input(occurrence, 0),
            emitting_port: OccurrencePort::output(occurrence, 0),
            entering_native: from,
            emitting_native: to,
        }],
        native_support: BTreeSet::from([from, to]),
        incidence: vec![NativeIncidenceTerm {
            occurrence,
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
            occurrence,
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
        chronology: vec![InputId(generator)],
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
        open_exterior: vec!["receiver/history outside the admitted family".to_owned()],
        reconstruction_fibre: BTreeSet::from([occurrence]),
    }
}

/// The declared two-state winding family: occurrence `2` is the actual successor of occurrence
/// `1`, and the one shared generator descends totally over both states.
pub fn spool() -> NativeSpool {
    let left = thread("thread/turn-out", 1, None, 10, 11, 0, 1, 7);
    let right = thread("thread/turn-back", 2, Some(1), 11, 10, 1, 0, 7);
    NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: "spool/native-turn".to_owned(),
        native_population: BTreeSet::from([NativeStateId(0), NativeStateId(1)]),
        receiver_family: BTreeSet::from([FIXTURE_RECEIVER]),
        generator_family: BTreeSet::from([FIXTURE_GENERATOR]),
        threads: vec![left, right],
        serial_pullbacks: vec![
            NativeSerialPullback {
                left_thread: "thread/turn-out".to_owned(),
                right_thread: "thread/turn-back".to_owned(),
                joining_boundary: BoundaryId(11),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: EventId(1),
                    right: EventId(2),
                    joining_native: NativeStateId(1),
                }]),
            },
            NativeSerialPullback {
                left_thread: "thread/turn-back".to_owned(),
                right_thread: "thread/turn-out".to_owned(),
                joining_boundary: BoundaryId(10),
                occurrences: BTreeSet::from([NativePullbackOccurrence {
                    left: EventId(2),
                    right: EventId(1),
                    joining_native: NativeStateId(0),
                }]),
            },
        ],
        generator_descents: vec![NativeGeneratorDescent {
            generator: FIXTURE_GENERATOR,
            steps: vec![
                NativeGeneratorStep {
                    from: NativeStateId(0),
                    to: NativeStateId(1),
                    thread: "thread/turn-out".to_owned(),
                },
                NativeGeneratorStep {
                    from: NativeStateId(1),
                    to: NativeStateId(0),
                    thread: "thread/turn-back".to_owned(),
                },
            ],
            open_domain: BTreeSet::new(),
        }],
        receiver_factors: vec![
            ReceiverFactor {
                native: NativeStateId(0),
                receiver: FIXTURE_RECEIVER,
                observation: Observation(100),
            },
            ReceiverFactor {
                native: NativeStateId(1),
                receiver: FIXTURE_RECEIVER,
                observation: Observation(101),
            },
        ],
        mutual_constitutive_responses: Vec::new(),
        reconstruction_fibres: vec![
            NativeCollapsedFibre {
                native: NativeStateId(0),
                occurrences: BTreeSet::from([EventId(2)]),
            },
            NativeCollapsedFibre {
                native: NativeStateId(1),
                occurrences: BTreeSet::from([EventId(1)]),
            },
        ],
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec!["larger receiver family".to_owned()],
    }
}

/// The declared native body as one complete transport scaffold.
pub fn scaffold() -> NativeTransportScaffold {
    NativeTransportScaffold {
        schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        address: "scaffold/native-turn".to_owned(),
        spools: vec![spool()],
        compositions: Vec::new(),
        open_exterior: vec!["another compatible spool".to_owned()],
    }
}

/// The generator the detached winding of [`detached_spool`] descends along.
pub const FIXTURE_DETACHED_GENERATOR: InputId = InputId(8);

/// A second declared body: one open winding `0 -> 1 -> 4` along the shared generator, together
/// with one causally detached winding `2 -> 3` along a second generator. Nothing is lifted here
/// either; the detached family exists so an owner can ask whether a local return leaves unrelated
/// morphology untouched.
pub fn detached_spool() -> NativeSpool {
    NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: "spool/native-turn".to_owned(),
        native_population: BTreeSet::from([
            NativeStateId(0),
            NativeStateId(1),
            NativeStateId(2),
            NativeStateId(3),
            NativeStateId(4),
        ]),
        receiver_family: BTreeSet::from([FIXTURE_RECEIVER]),
        generator_family: BTreeSet::from([FIXTURE_GENERATOR, FIXTURE_DETACHED_GENERATOR]),
        threads: vec![
            thread("thread/turn-out", 1, None, 10, 11, 0, 1, 7),
            thread("thread/turn-onward", 2, Some(1), 11, 12, 1, 4, 7),
            thread("thread/detached", 3, None, 20, 21, 2, 3, 8),
        ],
        serial_pullbacks: vec![NativeSerialPullback {
            left_thread: "thread/turn-out".to_owned(),
            right_thread: "thread/turn-onward".to_owned(),
            joining_boundary: BoundaryId(11),
            occurrences: BTreeSet::from([NativePullbackOccurrence {
                left: EventId(1),
                right: EventId(2),
                joining_native: NativeStateId(1),
            }]),
        }],
        generator_descents: vec![
            NativeGeneratorDescent {
                generator: FIXTURE_GENERATOR,
                steps: vec![
                    NativeGeneratorStep {
                        from: NativeStateId(0),
                        to: NativeStateId(1),
                        thread: "thread/turn-out".to_owned(),
                    },
                    NativeGeneratorStep {
                        from: NativeStateId(1),
                        to: NativeStateId(4),
                        thread: "thread/turn-onward".to_owned(),
                    },
                ],
                open_domain: BTreeSet::from([
                    NativeStateId(2),
                    NativeStateId(3),
                    NativeStateId(4),
                ]),
            },
            NativeGeneratorDescent {
                generator: FIXTURE_DETACHED_GENERATOR,
                steps: vec![NativeGeneratorStep {
                    from: NativeStateId(2),
                    to: NativeStateId(3),
                    thread: "thread/detached".to_owned(),
                }],
                open_domain: BTreeSet::from([
                    NativeStateId(0),
                    NativeStateId(1),
                    NativeStateId(3),
                    NativeStateId(4),
                ]),
            },
        ],
        receiver_factors: (0..5)
            .map(|native| ReceiverFactor {
                native: NativeStateId(native),
                receiver: FIXTURE_RECEIVER,
                observation: Observation(native + 100),
            })
            .collect(),
        mutual_constitutive_responses: Vec::new(),
        reconstruction_fibres: vec![
            NativeCollapsedFibre {
                native: NativeStateId(1),
                occurrences: BTreeSet::from([EventId(1)]),
            },
            NativeCollapsedFibre {
                native: NativeStateId(3),
                occurrences: BTreeSet::from([EventId(3)]),
            },
            NativeCollapsedFibre {
                native: NativeStateId(4),
                occurrences: BTreeSet::from([EventId(2)]),
            },
        ],
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec!["larger receiver family".to_owned()],
    }
}

/// The second declared body as one complete transport scaffold.
pub fn detached_scaffold() -> NativeTransportScaffold {
    let body = NativeTransportScaffold {
        schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        address: "scaffold/native-turn".to_owned(),
        spools: vec![detached_spool()],
        compositions: Vec::new(),
        open_exterior: vec!["another compatible spool".to_owned()],
    };
    body.validate()
        .expect("the declared detached body is valid");
    body
}

/// The second declared body in the three physical lanes.
pub fn detached_returned() -> SoulkillerDismantlingReturn<()> {
    SoulkillerDismantlingReturn {
        native: detached_scaffold(),
        exterior: (),
        insufficiency: insufficiency(),
    }
}

/// One declared native insufficiency over the body above: a receiver outside its admitted family
/// leaves the exact retained occurrence fibre of the first occurrence.
pub fn insufficiency() -> ReceiverInsufficiency {
    let insufficiency = ReceiverInsufficiency {
        schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
        at_occurrence: EventId(1),
        native: NativeStateId(1),
        retained_fibre: BTreeSet::from([EventId(1)]),
        cause: ReceiverInsufficiencyCause::ReceiverOutsideFamily {
            requested: FIXTURE_UNADMITTED_RECEIVER,
            admitted: BTreeSet::from([FIXTURE_RECEIVER]),
        },
        open_exterior: vec!["a richer receiver must return another occurrence".to_owned()],
    };
    insufficiency
        .validate()
        .expect("the declared insufficiency is valid");
    insufficiency
}

/// The declared body presented in the three physical lanes every dismantling boundary returns.
/// The cold lane is the unit: this body departed from no exterior chart, so it carries no cold
/// reconstruction testimony.
pub fn returned() -> SoulkillerDismantlingReturn<()> {
    let native = scaffold();
    native.validate().expect("the declared body is valid");
    SoulkillerDismantlingReturn {
        native,
        exterior: (),
        insufficiency: insufficiency(),
    }
}
