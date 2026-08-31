//! Source-neutral native recurrence founded from visible dialogue incidence.
//!
//! Text and exterior speaker/provider charts remain cold lineage. Native state is the two-face
//! receiver quotient of causal depth parity, and every message remains an addressed occurrence in
//! the complete reconstruction fibre.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::{
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort,
    native_spool::{
        NATIVE_SPOOL_BUNDLE_SCHEMA, NATIVE_SPOOL_SCHEMA, NATIVE_THREAD_SCHEMA,
        NativeCollapsedFibre, NativeConstitutiveResponse, NativeGeneratorDescent,
        NativeGeneratorStep, NativeIncidenceTerm, NativeParametronCell, NativeReceiverConsequence,
        NativePullbackOccurrence, NativeSerialPullback, NativeSpool, NativeSpoolBundle,
        NativeSpoolRefusal, NativeThread, NativeThreadHand, NativeThreadOccurrence,
    },
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;

use crate::dialogue_lineage::ExactDialogueLineage;

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct AddressedDialogueOccurrence {
    pub address: String,
    pub predecessor: Option<String>,
    pub caused_by: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct DialogueNativeOccurrenceWitness {
    pub event: EventId,
    pub source_address: String,
    pub predecessor: Option<String>,
    pub caused_by: BTreeSet<String>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct DialogueNativeSpoolReturn {
    pub native: NativeSpoolBundle,
    pub exterior: Vec<DialogueNativeOccurrenceWitness>,
}

const RECEIVER: ReceiverId = ReceiverId(0);
const GENERATOR: InputId = InputId(0);

pub fn found_dialogue_native_spool(
    lineage: &ExactDialogueLineage,
) -> Result<NativeSpoolBundle, NativeSpoolRefusal> {
    let occurrences = lineage
        .occurrences()
        .iter()
        .enumerate()
        .map(|(at, occurrence)| AddressedDialogueOccurrence {
            address: occurrence.identity.clone(),
            predecessor: at
                .checked_sub(1)
                .map(|prior| lineage.occurrences()[prior].identity.clone()),
            caused_by: occurrence.caused_by.clone(),
        })
        .collect::<Vec<_>>();
    Ok(found_addressed_dialogue_native_spool(&occurrences)?.native)
}

pub fn found_addressed_dialogue_native_spool(
    occurrences: &[AddressedDialogueOccurrence],
) -> Result<DialogueNativeSpoolReturn, NativeSpoolRefusal> {
    if occurrences.len() < 2 {
        return Err(NativeSpoolRefusal::MalformedBundle(
            "dialogue/native-recurrence".to_owned(),
        ));
    }
    let events = (0..occurrences.len())
        .map(|at| EventId(at as u64 + 1))
        .collect::<Vec<_>>();
    let by_identity = occurrences
        .iter()
        .enumerate()
        .map(|(at, occurrence)| (occurrence.address.as_str(), at))
        .collect::<BTreeMap<_, _>>();
    if by_identity.len() != occurrences.len() {
        return Err(NativeSpoolRefusal::DuplicateOccurrence(EventId(0)));
    }
    let mut depth = vec![0usize; occurrences.len()];
    for (at, occurrence) in occurrences.iter().enumerate() {
        depth[at] = match occurrence
            .predecessor
            .as_deref()
            .and_then(|predecessor| by_identity.get(predecessor).copied())
        {
            Some(predecessor) if predecessor < at => depth[predecessor] + 1,
            Some(_) => return Err(NativeSpoolRefusal::Occurrence("dialogue/native-recurrence".to_owned())),
            None => 0,
        };
    }
    let states = (0..occurrences.len())
        .map(|at| NativeStateId(at as u64))
        .collect::<Vec<_>>();
    let phases = depth.iter().map(|depth| depth % 2).collect::<Vec<_>>();
    let mut grouped = BTreeMap::<
        (usize, usize),
        Vec<(usize, EventId, NativeStateId, NativeStateId, Option<EventId>)>,
    >::new();
    let predecessor = occurrences
        .iter()
        .map(|occurrence| {
            occurrence
                .predecessor
                .as_deref()
                .and_then(|address| by_identity.get(address).copied())
        })
        .collect::<Vec<_>>();
    let mut successor = vec![None; occurrences.len()];
    for (at, predecessor) in predecessor.iter().copied().enumerate() {
        if let Some(predecessor) = predecessor {
            if successor[predecessor].replace(at).is_some() {
                return Err(NativeSpoolRefusal::Occurrence("dialogue/native-branch".to_owned()));
            }
        }
    }
    let root = (0..occurrences.len())
        .map(|mut at| {
            while let Some(prior) = predecessor[at] {
                at = prior;
            }
            at
        })
        .collect::<Vec<_>>();
    for at in 0..occurrences.len() {
        let target = successor[at].unwrap_or(root[at]);
        grouped.entry((phases[at], phases[target])).or_default().push((
            at,
            events[at],
            states[at],
            states[target],
            predecessor[at].map(|prior| events[prior]),
        ));
    }
    let mut threads = grouped
        .into_iter()
        .map(|((from_phase, to_phase), members)| {
            thread(from_phase, to_phase, members, &phases)
        })
        .collect::<Result<Vec<_>, _>>()?;
    threads.sort_by(|left, right| left.address.cmp(&right.address));
    let mut serial_pullbacks = Vec::new();
    for left in &threads {
        for right in &threads {
            if left.emitting_boundary != right.entering_boundary {
                continue;
            }
            let right_by_native = right
                .occurrences
                .iter()
                .map(|occurrence| (occurrence.entering_native, occurrence.occurrence))
                .collect::<BTreeMap<_, _>>();
            let pullback = left
                .occurrences
                .iter()
                .filter_map(|occurrence| {
                    right_by_native.get(&occurrence.emitting_native).map(|right| {
                        NativePullbackOccurrence {
                            left: occurrence.occurrence,
                            right: *right,
                            joining_native: occurrence.emitting_native,
                        }
                    })
                })
                .collect::<BTreeSet<_>>();
            if !pullback.is_empty() {
                serial_pullbacks.push(NativeSerialPullback {
                    left_thread: left.address.clone(),
                    right_thread: right.address.clone(),
                    joining_boundary: left.emitting_boundary,
                    occurrences: pullback,
                });
            }
        }
    }
    let mut generator_steps = threads
        .iter()
        .flat_map(|thread| {
            thread
                .occurrences
                .iter()
                .map(move |occurrence| NativeGeneratorStep {
                    from: occurrence.entering_native,
                    to: occurrence.emitting_native,
                    thread: thread.address.clone(),
                })
        })
        .collect::<Vec<_>>();
    generator_steps.sort_by_key(|step| step.from);
    let fibres = states
        .iter()
        .map(|native| NativeCollapsedFibre {
            native: *native,
            occurrences: threads
                .iter()
                .flat_map(|thread| &thread.occurrences)
                .filter(|occurrence| occurrence.emitting_native == *native)
                .map(|occurrence| occurrence.occurrence)
                .collect(),
        })
        .collect::<Vec<_>>();
    let spool = NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: "dialogue/native-recurrence".to_owned(),
        native_population: states.iter().copied().collect(),
        receiver_family: BTreeSet::from([RECEIVER]),
        generator_family: BTreeSet::from([GENERATOR]),
        threads,
        serial_pullbacks,
        generator_descents: vec![NativeGeneratorDescent {
            generator: GENERATOR,
            steps: generator_steps,
        }],
        receiver_factors: states
            .iter()
            .enumerate()
            .map(|(at, native)| ReceiverFactor {
                native: *native,
                receiver: RECEIVER,
                observation: Observation(phases[at] as u64),
            })
            .collect(),
        mutual_constitutive_responses: Vec::new(),
        reconstruction_fibres: fibres,
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec!["later returned dialogue incidence".to_owned()],
    };
    spool.validate()?;
    let bundle = NativeSpoolBundle {
        schema: NATIVE_SPOOL_BUNDLE_SCHEMA.to_owned(),
        address: "dialogue/native-bundle".to_owned(),
        spools: vec![spool],
        compositions: Vec::new(),
        open_exterior: vec!["additional compatible native organs".to_owned()],
    };
    bundle.validate()?;
    Ok(DialogueNativeSpoolReturn {
        native: bundle,
        exterior: occurrences
            .iter()
            .zip(events)
            .map(|(occurrence, event)| DialogueNativeOccurrenceWitness {
                event,
                source_address: occurrence.address.clone(),
                predecessor: occurrence.predecessor.clone(),
                caused_by: occurrence.caused_by.clone(),
            })
            .collect(),
    })
}

fn thread(
    from_phase: usize,
    to_phase: usize,
    members: Vec<(
        usize,
        EventId,
        NativeStateId,
        NativeStateId,
        Option<EventId>,
    )>,
    phases: &[usize],
) -> Result<NativeThread, NativeSpoolRefusal> {
    let address = format!("dialogue/native-{from_phase}-{to_phase}");
    let occurrences = members
        .iter()
        .map(|(_at, occurrence, from, to, predecessor)| NativeThreadOccurrence {
            occurrence: *occurrence,
            predecessor: *predecessor,
            entering_port: OccurrencePort::input(*occurrence, 0),
            emitting_port: OccurrencePort::output(*occurrence, 0),
            entering_native: *from,
            emitting_native: *to,
        })
        .collect::<Vec<_>>();
    let native_support = occurrences
        .iter()
        .flat_map(|occurrence| [occurrence.entering_native, occurrence.emitting_native])
        .collect::<BTreeSet<_>>();
    let reconstruction_fibre = occurrences.iter().map(|item| item.occurrence).collect();
    let one = ExactComplexWaveCurrent::one();
    let turn = ExactComplexWaveCurrent::new(
        Rat::from_integer(BigInt::from(0)),
        Rat::from_integer(BigInt::from(1)),
    );
    let parametrons = native_support
        .iter()
        .map(|native| {
            if phases[native.0 as usize] == 0 {
                NativeParametronCell {
                    native: *native,
                    section: one.clone(),
                    current: turn.clone(),
                    relative_phase: ExactUnitConicPhase::identity(),
                    hand: NativeThreadHand::Along,
                }
            } else {
                NativeParametronCell {
                    native: *native,
                    section: turn.clone(),
                    current: one.negated(),
                    relative_phase: ExactUnitConicPhase::identity(),
                    hand: NativeThreadHand::Along,
                }
            }
        })
        .collect::<Vec<_>>();
    let thread = NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(),
        address,
        entering_boundary: BoundaryId(from_phase as u64),
        emitting_boundary: BoundaryId(to_phase as u64),
        entering_carrier: "native-complex-current".to_owned(),
        emitting_carrier: "native-complex-current".to_owned(),
        incidence: occurrences
            .iter()
            .map(|item| NativeIncidenceTerm {
                occurrence: item.occurrence,
                from: item.entering_native,
                to: item.emitting_native,
                coefficient: 1,
            })
            .collect(),
        occurrences,
        native_support,
        parametrons: parametrons.clone(),
        constitutive_responses: parametrons
            .iter()
            .map(|cell| NativeConstitutiveResponse {
                native: cell.native,
                receiver: RECEIVER,
                presented: cell.section.clone(),
                stored: cell.current.clone(),
            })
            .collect(),
        chronology: vec![GENERATOR],
        receiver_consequences: parametrons
            .iter()
            .map(|cell| NativeReceiverConsequence {
                native: cell.native,
                receiver: RECEIVER,
                observation: Observation(phases[cell.native.0 as usize] as u64),
            })
            .collect(),
        obstruction: None,
        open_exterior: vec!["richer receiver family".to_owned()],
        reconstruction_fibre,
    };
    thread.validate()?;
    Ok(thread)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dialogue_lineage::{CodexDialogueImportSpec, ExactDialogueLineage};

    #[test]
    fn visible_text_founds_lineage_but_not_native_state_or_wire_content() {
        let path = std::env::temp_dir().join(format!("dialogue-native-{}.jsonl", std::process::id()));
        let material = concat!(
            "{\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"user\",\"id\":\"u\",\"content\":[{\"type\":\"input_text\",\"text\":\"Unique source sentence.\"}]}}\n",
            "{\"type\":\"response_item\",\"payload\":{\"type\":\"message\",\"role\":\"assistant\",\"phase\":\"final_answer\",\"id\":\"a\",\"content\":[{\"type\":\"output_text\",\"text\":\"Unique returned sentence.\"}]}}\n"
        );
        std::fs::write(&path, material).unwrap();
        let lineage = ExactDialogueLineage::import_codex_rollout(&path, &CodexDialogueImportSpec::default()).unwrap();
        let bundle = found_dialogue_native_spool(&lineage).unwrap();
        let wire = bundle.canonical_bytes().unwrap();
        assert!(!wire.windows("Unique source sentence.".len()).any(|window| window == b"Unique source sentence."));
        assert_eq!(bundle.spools[0].reconstruction_fibres.iter().map(|fibre| fibre.occurrences.len()).sum::<usize>(), 2);
        std::fs::remove_file(path).unwrap();
    }

    #[test]
    fn disjoint_container_chronologies_each_retain_ingress_and_total_transport() {
        let occurrences = vec![
            AddressedDialogueOccurrence { address: "a/0".to_owned(), predecessor: None, caused_by: BTreeSet::new() },
            AddressedDialogueOccurrence { address: "a/1".to_owned(), predecessor: Some("a/0".to_owned()), caused_by: BTreeSet::from(["a/0".to_owned()]) },
            AddressedDialogueOccurrence { address: "b/0".to_owned(), predecessor: None, caused_by: BTreeSet::new() },
            AddressedDialogueOccurrence { address: "b/1".to_owned(), predecessor: Some("b/0".to_owned()), caused_by: BTreeSet::from(["b/0".to_owned()]) },
        ];
        let returned = found_addressed_dialogue_native_spool(&occurrences).unwrap();
        let spool = &returned.native.spools[0];
        assert_eq!(spool.native_population.len(), 4);
        assert_eq!(spool.generator_descents[0].steps.len(), 4);
        assert_eq!(spool.serial_pullbacks.iter().map(|pullback| pullback.occurrences.len()).sum::<usize>(), 4);
        assert_eq!(spool.threads.iter().flat_map(|thread| &thread.occurrences).filter(|occurrence| occurrence.predecessor.is_none()).count(), 2);
    }
}
