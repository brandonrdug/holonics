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
        NativeSpool, NativeSpoolBundle, NativeSpoolRefusal, NativeThread, NativeThreadHand,
        NativeThreadOccurrence,
    },
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;

use crate::dialogue_lineage::ExactDialogueLineage;

const ENTERING: NativeStateId = NativeStateId(0);
const RETURNED: NativeStateId = NativeStateId(1);
const RECEIVER: ReceiverId = ReceiverId(0);
const GENERATOR: InputId = InputId(0);

pub fn found_dialogue_native_spool(
    lineage: &ExactDialogueLineage,
) -> Result<NativeSpoolBundle, NativeSpoolRefusal> {
    let occurrences = lineage.occurrences();
    if occurrences.len() < 2 {
        return Err(NativeSpoolRefusal::MalformedBundle(
            "dialogue/native-recurrence".to_owned(),
        ));
    }
    let events = occurrences
        .iter()
        .map(|occurrence| EventId(occurrence.ordinal + 1))
        .collect::<Vec<_>>();
    let by_identity = occurrences
        .iter()
        .enumerate()
        .map(|(at, occurrence)| (occurrence.identity.as_str(), at))
        .collect::<BTreeMap<_, _>>();
    let mut depth = vec![0usize; occurrences.len()];
    for (at, occurrence) in occurrences.iter().enumerate() {
        depth[at] = occurrence
            .caused_by
            .iter()
            .filter_map(|cause| by_identity.get(cause.as_str()).copied())
            .filter(|cause| *cause < at)
            .map(|cause| depth[cause] + 1)
            .max()
            .unwrap_or_else(|| usize::from(at != 0) + depth[at.saturating_sub(1)]);
    }
    let forward = thread(
        "dialogue/native-forward",
        ENTERING,
        RETURNED,
        occurrences
            .iter()
            .enumerate()
            .filter(|(at, _)| depth[*at] % 2 == 0)
            .map(|(at, _)| (at, events[at])),
        &events,
    )?;
    let returned = thread(
        "dialogue/native-return",
        RETURNED,
        ENTERING,
        occurrences
            .iter()
            .enumerate()
            .filter(|(at, _)| depth[*at] % 2 == 1)
            .map(|(at, _)| (at, events[at])),
        &events,
    )?;
    let fibres = [ENTERING, RETURNED]
        .into_iter()
        .map(|native| NativeCollapsedFibre {
            native,
            occurrences: [(&forward, RETURNED), (&returned, ENTERING)]
                .into_iter()
                .filter(|(_, target)| *target == native)
                .flat_map(|(thread, _)| thread.occurrences.iter().map(|item| item.occurrence))
                .collect(),
        })
        .collect::<Vec<_>>();
    let spool = NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: "dialogue/native-recurrence".to_owned(),
        native_population: BTreeSet::from([ENTERING, RETURNED]),
        receiver_family: BTreeSet::from([RECEIVER]),
        generator_family: BTreeSet::from([GENERATOR]),
        threads: vec![forward, returned],
        serial_pullbacks: Vec::new(),
        generator_descents: vec![NativeGeneratorDescent {
            generator: GENERATOR,
            steps: vec![
                NativeGeneratorStep {
                    from: ENTERING,
                    to: RETURNED,
                    thread: "dialogue/native-forward".to_owned(),
                },
                NativeGeneratorStep {
                    from: RETURNED,
                    to: ENTERING,
                    thread: "dialogue/native-return".to_owned(),
                },
            ],
        }],
        receiver_factors: vec![
            ReceiverFactor {
                native: ENTERING,
                receiver: RECEIVER,
                observation: Observation(0),
            },
            ReceiverFactor {
                native: RETURNED,
                receiver: RECEIVER,
                observation: Observation(1),
            },
        ],
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
    Ok(bundle)
}

fn thread(
    address: &str,
    from: NativeStateId,
    to: NativeStateId,
    members: impl Iterator<Item = (usize, EventId)>,
    events: &[EventId],
) -> Result<NativeThread, NativeSpoolRefusal> {
    let occurrences = members
        .map(|(at, occurrence)| NativeThreadOccurrence {
            occurrence,
            predecessor: at.checked_sub(1).map(|prior| events[prior]),
            entering_port: OccurrencePort::input(occurrence, 0),
            emitting_port: OccurrencePort::output(occurrence, 0),
            entering_native: from,
            emitting_native: to,
        })
        .collect::<Vec<_>>();
    let reconstruction_fibre = occurrences.iter().map(|item| item.occurrence).collect();
    let one = ExactComplexWaveCurrent::one();
    let turn = ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(0)), Rat::from_integer(BigInt::from(1)));
    let parametrons = vec![
        NativeParametronCell { native: ENTERING, section: one.clone(), current: turn.clone(), relative_phase: ExactUnitConicPhase::identity(), hand: NativeThreadHand::Along },
        NativeParametronCell { native: RETURNED, section: turn.clone(), current: one.negated(), relative_phase: ExactUnitConicPhase::identity(), hand: NativeThreadHand::Along },
    ];
    let thread = NativeThread {
        schema: NATIVE_THREAD_SCHEMA.to_owned(), address: address.to_owned(),
        entering_boundary: BoundaryId(u64::from(from.0)), emitting_boundary: BoundaryId(u64::from(to.0)),
        entering_carrier: "native-complex-current".to_owned(), emitting_carrier: "native-complex-current".to_owned(),
        incidence: occurrences.iter().map(|item| NativeIncidenceTerm { occurrence: item.occurrence, from, to, coefficient: 1 }).collect(),
        occurrences, native_support: BTreeSet::from([ENTERING, RETURNED]), parametrons: parametrons.clone(),
        constitutive_responses: parametrons.iter().map(|cell| NativeConstitutiveResponse { native: cell.native, receiver: RECEIVER, presented: cell.section.clone(), stored: cell.current.clone() }).collect(),
        chronology: vec![GENERATOR],
        receiver_consequences: vec![NativeReceiverConsequence { native: ENTERING, receiver: RECEIVER, observation: Observation(0) }, NativeReceiverConsequence { native: RETURNED, receiver: RECEIVER, observation: Observation(1) }],
        obstruction: None, open_exterior: vec!["richer receiver family".to_owned()], reconstruction_fibre,
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
}
