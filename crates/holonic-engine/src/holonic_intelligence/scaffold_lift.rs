use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::ieee754::decode_bfloat16_bits;
use crate::native_spool::{
    NATIVE_SPOOL_SCHEMA, NATIVE_THREAD_SCHEMA, NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
    NativeCollapsedFibre, NativeConstitutiveResponse, NativeFactorizedSection,
    NativeGeneratorDescent, NativeGeneratorStep, NativeIncidenceTerm, NativeOccurrenceSection,
    NativeParametronCell, NativeReceiverConsequence, NativeSpool, NativeSpoolRefusal, NativeThread,
    NativeThreadHand, NativeThreadOccurrence, NativeTransportScaffold,
    RECEIVER_INSUFFICIENCY_SCHEMA, ReceiverInsufficiency, ReceiverInsufficiencyCause,
};
use crate::receiver_exact_compression::{InputId, Observation, ReceiverId};
use crate::receiver_history_compression::{NativeStateId, ReceiverFactor};
use crate::soulkiller::{SoulkillerDismantlingInput, SoulkillerDismantlingReturn};
use crate::{BoundaryId, EventId, ExactUnitConicPhase, OccurrencePort};

use super::ExteriorModality;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ForeignBf16Excitation {
    pub event: EventId,
    pub predecessor: Option<EventId>,
    pub entering_boundary: BoundaryId,
    pub emitting_boundary: BoundaryId,
    pub source_occurrence: String,
    pub exterior_modality: ExteriorModality,
    pub entering_codewords: Vec<u16>,
    pub returned_codewords: Vec<u16>,
    pub interventions: BTreeSet<String>,
    pub receiver_consequences: BTreeSet<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Bf16ExcitationColdWitness {
    pub schema: String,
    pub excitations: Vec<ForeignBf16Excitation>,
    pub open_exterior: Vec<String>,
}

/// Reconstruct every productive factorized section from the exact cold BF16 codeword lane.
///
/// The cold codewords remain source-codec testimony; the hot lane retains their exact decoded
/// local values and block incidence. This receipt proves the two physical lanes still join at
/// every occurrence without making BF16 a native state type.
pub fn validate_bf16_section_reconstruction(
    returned: &SoulkillerDismantlingReturn<Bf16ExcitationColdWitness>,
) -> Result<(), ScaffoldLiftError> {
    returned.native.validate()?;
    for excitation in &returned.exterior.excitations {
        let section = returned
            .native
            .spools
            .iter()
            .flat_map(|spool| &spool.threads)
            .flat_map(|thread| &thread.sections)
            .find(|section| section.occurrence == excitation.event)
            .ok_or(ScaffoldLiftError::Excitation)?;
        if section.entering != factorize_bf16(&excitation.entering_codewords)?
            || section.returned != factorize_bf16(&excitation.returned_codewords)?
        {
            return Err(ScaffoldLiftError::Excitation);
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ScaffoldLiftError {
    #[error("the BF16 excitation family is empty, repeated, or malformed")]
    Excitation,
    #[error("the BF16 excitation contains a nonfinite codeword")]
    Codeword,
    #[error("an actual predecessor does not meet the later excitation at one native state")]
    Pullback,
    #[error("the source-neutral scaffold refused: {0}")]
    Scaffold(#[from] NativeSpoolRefusal),
}

pub struct Bf16ExcitationDismantling {
    pub receiver: ReceiverId,
    pub excitations: Vec<ForeignBf16Excitation>,
}

impl SoulkillerDismantlingInput for Bf16ExcitationDismantling {
    type ColdWitness = Bf16ExcitationColdWitness;
    type Error = ScaffoldLiftError;

    fn dismantle(self) -> Result<SoulkillerDismantlingReturn<Self::ColdWitness>, Self::Error> {
        dismantle_bf16_excitations(self.receiver, self.excitations)
    }
}

#[derive(Clone, Debug)]
struct NativeExcitation {
    event: EventId,
    predecessor: Option<EventId>,
    entering_boundary: BoundaryId,
    emitting_boundary: BoundaryId,
    entering: NativeFactorizedSection,
    returned: NativeFactorizedSection,
}

const NATIVE_SECTION_BLOCK_WORDS: usize = 4096;

fn dismantle_bf16_excitations(
    receiver: ReceiverId,
    excitations: Vec<ForeignBf16Excitation>,
) -> Result<SoulkillerDismantlingReturn<Bf16ExcitationColdWitness>, ScaffoldLiftError> {
    if excitations.is_empty() {
        return Err(ScaffoldLiftError::Excitation);
    }
    let mut events = BTreeSet::new();
    let mut native_excitations = Vec::with_capacity(excitations.len());
    for excitation in &excitations {
        if !events.insert(excitation.event)
            || excitation.predecessor == Some(excitation.event)
            || excitation.source_occurrence.is_empty()
            || excitation.entering_codewords.is_empty()
            || excitation.returned_codewords.is_empty()
            || excitation.interventions.is_empty()
            || excitation.receiver_consequences.is_empty()
        {
            return Err(ScaffoldLiftError::Excitation);
        }
        native_excitations.push(NativeExcitation {
            event: excitation.event,
            predecessor: excitation.predecessor,
            entering_boundary: excitation.entering_boundary,
            emitting_boundary: excitation.emitting_boundary,
            entering: factorize_bf16(&excitation.entering_codewords)?,
            returned: factorize_bf16(&excitation.returned_codewords)?,
        });
    }
    if native_excitations.iter().any(|excitation| {
        excitation
            .predecessor
            .is_some_and(|event| !events.contains(&event))
    }) {
        return Err(ScaffoldLiftError::Excitation);
    }
    let mut section_by_key = BTreeMap::new();
    for excitation in &native_excitations {
        section_by_key
            .entry(section_key(&excitation.entering))
            .or_insert_with(|| excitation.entering.clone());
        section_by_key
            .entry(section_key(&excitation.returned))
            .or_insert_with(|| excitation.returned.clone());
    }
    let state_by_key = section_by_key
        .keys()
        .enumerate()
        .map(|(at, key)| (key.clone(), NativeStateId(at as u64)))
        .collect::<BTreeMap<_, _>>();
    let generator_by_event = native_excitations
        .iter()
        .enumerate()
        .map(|(at, excitation)| (excitation.event, InputId(at as u64)))
        .collect::<BTreeMap<_, _>>();
    let observation = state_by_key
        .values()
        .map(|state| (*state, Observation(state.0)))
        .collect::<BTreeMap<_, _>>();

    let mut threads = Vec::with_capacity(native_excitations.len());
    let mut emitted_by_event = BTreeMap::new();
    let mut entering_by_event = BTreeMap::new();
    for excitation in &native_excitations {
        let from = state_by_key[&section_key(&excitation.entering)];
        let to = state_by_key[&section_key(&excitation.returned)];
        entering_by_event.insert(excitation.event, from);
        emitted_by_event.insert(excitation.event, to);
        let support = BTreeSet::from([from, to]);
        let parametrons = support
            .iter()
            .map(|state| {
                let section = section_by_key
                    .iter()
                    .find_map(|(key, section)| (state_by_key[key] == *state).then_some(section))
                    .expect("every native state has one exact current")
                    .clone();
                let current = section.receiver_current;
                NativeParametronCell {
                    native: *state,
                    section: current.clone(),
                    current,
                    relative_phase: ExactUnitConicPhase::identity(),
                    hand: NativeThreadHand::Along,
                }
            })
            .collect::<Vec<_>>();
        let constitutive_responses = parametrons
            .iter()
            .map(|cell| NativeConstitutiveResponse {
                native: cell.native,
                receiver,
                presented: cell.section.clone(),
                stored: cell.current.clone(),
            })
            .collect();
        let receiver_consequences = support
            .iter()
            .map(|state| NativeReceiverConsequence {
                native: *state,
                receiver,
                observation: observation[state],
            })
            .collect();
        let generator = generator_by_event[&excitation.event];
        threads.push(NativeThread {
            schema: NATIVE_THREAD_SCHEMA.to_owned(),
            address: format!("thread/excitation-{}", excitation.event.0),
            entering_boundary: excitation.entering_boundary,
            emitting_boundary: excitation.emitting_boundary,
            entering_carrier: "exact-complex-current".to_owned(),
            emitting_carrier: "exact-complex-current".to_owned(),
            occurrences: vec![NativeThreadOccurrence {
                occurrence: excitation.event,
                predecessor: excitation.predecessor,
                entering_port: OccurrencePort::input(excitation.event, 0),
                emitting_port: OccurrencePort::output(excitation.event, 0),
                entering_native: from,
                emitting_native: to,
            }],
            native_support: support,
            incidence: vec![NativeIncidenceTerm {
                occurrence: excitation.event,
                from,
                to,
                coefficient: 1,
            }],
            parametrons,
            sections: vec![NativeOccurrenceSection {
                occurrence: excitation.event,
                entering: excitation.entering.clone(),
                returned: excitation.returned.clone(),
            }],
            constitutive_responses,
            chronology: vec![generator],
            receiver_consequences,
            obstruction: None,
            open_exterior: vec![
                "receiver histories outside the admitted excitation remain open".to_owned(),
            ],
            reconstruction_fibre: BTreeSet::from([excitation.event]),
        });
    }

    for excitation in &native_excitations {
        if let Some(predecessor) = excitation.predecessor
            && emitted_by_event[&predecessor] != entering_by_event[&excitation.event]
        {
            return Err(ScaffoldLiftError::Pullback);
        }
    }
    let generator_descents = threads
        .iter()
        .map(|thread| {
            let occurrence = &thread.occurrences[0];
            NativeGeneratorDescent {
                generator: thread.chronology[0],
                steps: vec![NativeGeneratorStep {
                    from: occurrence.entering_native,
                    to: occurrence.emitting_native,
                    thread: thread.address.clone(),
                }],
                open_domain: state_by_key
                    .values()
                    .copied()
                    .filter(|state| *state != occurrence.entering_native)
                    .collect(),
            }
        })
        .collect();
    let receiver_factors = state_by_key
        .values()
        .map(|state| ReceiverFactor {
            native: *state,
            receiver,
            observation: observation[state],
        })
        .collect();
    let reconstruction_fibres = state_by_key
        .values()
        .filter_map(|state| {
            let occurrences = emitted_by_event
                .iter()
                .filter_map(|(event, emitted)| (*emitted == *state).then_some(*event))
                .collect::<BTreeSet<_>>();
            (!occurrences.is_empty()).then_some(NativeCollapsedFibre {
                native: *state,
                occurrences,
            })
        })
        .collect();
    let first = &native_excitations[0];
    let first_native = emitted_by_event[&first.event];
    let first_fibre = BTreeSet::from([first.event]);
    let spool = NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: "spool/inherited-excitation-windings".to_owned(),
        native_population: state_by_key.values().copied().collect(),
        receiver_family: BTreeSet::from([receiver]),
        generator_family: generator_by_event.values().copied().collect(),
        threads,
        serial_pullbacks: Vec::new(),
        generator_descents,
        receiver_factors,
        mutual_constitutive_responses: Vec::new(),
        reconstruction_fibres,
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec!["unexcited foreign capability remains cold".to_owned()],
    };
    let native = NativeTransportScaffold {
        schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        address: "scaffold/inherited-excitation".to_owned(),
        spools: vec![spool],
        compositions: Vec::new(),
        open_exterior: vec!["compatible later scaffold facets remain open".to_owned()],
    };
    native.validate()?;
    let insufficiency = ReceiverInsufficiency {
        schema: RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
        at_occurrence: first.event,
        native: first_native,
        retained_fibre: first_fibre,
        cause: ReceiverInsufficiencyCause::ReceiverOutsideFamily {
            requested: ReceiverId(receiver.0.wrapping_add(1)),
            admitted: BTreeSet::from([receiver]),
        },
        open_exterior: vec!["a richer receiver must return another excitation".to_owned()],
    };
    insufficiency.validate()?;
    let returned = SoulkillerDismantlingReturn {
        native,
        exterior: Bf16ExcitationColdWitness {
            schema: "holonic-engine.bf16-excitation-cold-witness.v1".to_owned(),
            excitations,
            open_exterior: vec!["source modalities and tensor coordinates remain cold".to_owned()],
        },
        insufficiency,
    };
    validate_bf16_section_reconstruction(&returned)?;
    Ok(returned)
}

fn factorize_bf16(words: &[u16]) -> Result<NativeFactorizedSection, ScaffoldLiftError> {
    let values = words
        .iter()
        .map(|word| {
            decode_bfloat16_bits(*word)
                .map_err(|_| ScaffoldLiftError::Codeword)
                .map(|decoded| decoded.value())
        })
        .collect::<Result<Vec<_>, _>>()?;
    NativeFactorizedSection::from_values(values, NATIVE_SECTION_BLOCK_WORDS)
        .map_err(ScaffoldLiftError::Scaffold)
}

fn section_key(section: &NativeFactorizedSection) -> Vec<String> {
    section
        .coordinate_values()
        .map(ToString::to_string)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lift(
        receiver: ReceiverId,
        excitations: Vec<ForeignBf16Excitation>,
    ) -> Result<SoulkillerDismantlingReturn<Bf16ExcitationColdWitness>, ScaffoldLiftError> {
        crate::soulkiller::dismantle(Bf16ExcitationDismantling {
            receiver,
            excitations,
        })
    }

    fn excitation(
        event: u64,
        modality: ExteriorModality,
        entering: Vec<u16>,
        returned: Vec<u16>,
    ) -> ForeignBf16Excitation {
        ForeignBf16Excitation {
            event: EventId(event),
            predecessor: None,
            entering_boundary: BoundaryId(10 + event),
            emitting_boundary: BoundaryId(20 + event),
            source_occurrence: format!("source/{event}"),
            exterior_modality: modality,
            entering_codewords: entering,
            returned_codewords: returned,
            interventions: BTreeSet::from([format!("intervention/{event}")]),
            receiver_consequences: BTreeSet::from([format!("consequence/{event}")]),
        }
    }

    #[test]
    fn source_names_and_modalities_remain_cold_while_exact_currents_found_the_scaffold() {
        let returned = lift(
            ReceiverId(7),
            vec![
                excitation(1, ExteriorModality::Text, vec![0x3f80], vec![0x4000]),
                excitation(2, ExteriorModality::Image, vec![0x3f80], vec![0x4040]),
                excitation(3, ExteriorModality::Audio, vec![0x3f80], vec![0x4080]),
            ],
        )
        .expect("lift");
        returned.native.validate().expect("native scaffold");
        assert_eq!(returned.native.spools[0].threads.len(), 3);
        let wire = returned.native.canonical_bytes().expect("wire");
        let text = String::from_utf8(wire).expect("JSON");
        for forbidden in [
            "source/",
            "text",
            "image",
            "audio",
            "intervention",
            "consequence/",
        ] {
            assert!(
                !text.to_ascii_lowercase().contains(forbidden),
                "forbidden cold coordinate {forbidden:?} entered {text}"
            );
        }
        assert_eq!(returned.exterior.excitations.len(), 3);
    }

    #[test]
    fn nonfinite_bf16_and_false_predecessor_join_are_refused() {
        let nonfinite = lift(
            ReceiverId(7),
            vec![excitation(
                1,
                ExteriorModality::Text,
                vec![0x7f80],
                vec![0x3f80],
            )],
        );
        assert!(matches!(nonfinite, Err(ScaffoldLiftError::Codeword)));
        let mut later = excitation(2, ExteriorModality::Text, vec![0x4040], vec![0x4080]);
        later.predecessor = Some(EventId(1));
        let false_join = lift(
            ReceiverId(7),
            vec![
                excitation(1, ExteriorModality::Text, vec![0x3f80], vec![0x4000]),
                later,
            ],
        );
        assert_eq!(false_join, Err(ScaffoldLiftError::Pullback));
    }

    #[test]
    fn complete_sections_separate_an_old_alternating_sum_collision() {
        let left = excitation(
            1,
            ExteriorModality::Text,
            vec![0x3f80, 0x0000, 0x0000, 0x3f80],
            vec![0x4000],
        );
        let right = excitation(
            2,
            ExteriorModality::Image,
            vec![0x0000, 0x3f80, 0x3f80, 0x0000],
            vec![0x4040],
        );
        let returned = lift(ReceiverId(7), vec![left, right]).expect("lift");
        let left = &returned.native.spools[0].threads[0];
        let right = &returned.native.spools[0].threads[1];
        assert_eq!(
            left.sections[0].entering.receiver_current, right.sections[0].entering.receiver_current,
            "the former scalar face really collides"
        );
        assert_ne!(
            left.occurrences[0].entering_native, right.occurrences[0].entering_native,
            "complete factorized sections must not inherit the scalar collision"
        );
        assert_ne!(
            section_key(&left.sections[0].entering),
            section_key(&right.sections[0].entering)
        );
    }

    #[test]
    fn exterior_occurrence_order_survives_without_event_resorting() {
        let returned = lift(
            ReceiverId(7),
            vec![
                excitation(20, ExteriorModality::Audio, vec![0x3f80], vec![0x4000]),
                excitation(10, ExteriorModality::Text, vec![0x4040], vec![0x4080]),
            ],
        )
        .expect("lift");
        let threads = &returned.native.spools[0].threads;
        assert_eq!(threads[0].occurrences[0].occurrence, EventId(20));
        assert_eq!(threads[1].occurrences[0].occurrence, EventId(10));
        assert_eq!(threads[0].chronology, vec![InputId(0)]);
        assert_eq!(threads[1].chronology, vec![InputId(1)]);
    }
}
