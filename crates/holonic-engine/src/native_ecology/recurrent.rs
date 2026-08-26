//! The retained causal boundary of one bounded recurrent native passage.
//!
//! This module owns only the missing product receipt between already-returned source fronts and a
//! generator-native recurrence. It does not own a language, decoder policy, scheduler, cache, or
//! second inference body. Source histories and their full receiver testimony remain in
//! [`RetainedContinuationPassage`]; [`RetainedContinuationRest`] contains only the native action,
//! its closure word, and the exterior decoder response needed by the detached return.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::exact_work::ExactWork;
use crate::generator_native_rest::{GeneratorNativeRest, NativeGenerator};
use crate::receiver_exact_compression::{InputId, Observation, ReceiverId};
use crate::receiver_history_compression::{NativeStateId, NativeTransport};

pub const RETAINED_PASSAGE_SCHEMA: &str = "holonics.i1.retained-continuation-passage.v1";
pub const RETAINED_REST_SCHEMA: &str = "holonics.i1.retained-continuation-rest.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryFace {
    pub native_id: u32,
    pub source_surface: String,
    pub lower: i64,
    pub upper: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceFrontApparatus {
    pub total_deed_launches: u64,
    pub terminal_synchronizations: u64,
    pub streamed_staged_octets: u64,
    pub asynchronous_copy_octets: u64,
    pub resident_octets_peak: u64,
    pub physical_wall_seconds: String,
}

/// One source-schedule control front. Every context in the control is fixed before the control
/// population conducts; no preceding card return selects which later context is launched.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceBoundaryFront {
    pub before_occurrence: String,
    pub after_occurrence: String,
    pub before_native_ids: Vec<u32>,
    pub after_native_ids: Vec<u32>,
    pub emitted: BoundaryFace,
    pub plural_population: usize,
    pub complete_terminal_potential_sha256: String,
    pub terminal_hidden_sha256: String,
    pub runtime_receipt_sha256: String,
    pub exact_work: ExactWork,
    pub apparatus: SourceFrontApparatus,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedContinuationSection {
    pub occurrence: String,
    pub native_boundary: NativeStateId,
    pub entering_native_ids_sha256: String,
    pub live_fronts: Vec<BoundaryFace>,
    pub carried_runtime_receipt_sha256: Option<String>,
    pub complete_terminal_potential_sha256: Option<String>,
    pub terminal_hidden_sha256: Option<String>,
    pub predecessor: Option<String>,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryFibre {
    pub native: NativeStateId,
    pub source_sections: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReceiverReopening {
    pub native: NativeStateId,
    pub first_section: String,
    pub later_section: String,
    pub shortest_separating_history: Vec<InputId>,
    pub receiver: String,
    pub first_reading_sha256: String,
    pub later_reading_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryDecoder {
    pub native: NativeStateId,
    pub face: Option<BoundaryFace>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ClosureDerivation {
    pub entering_state: NativeStateId,
    pub first_repeated_state: NativeStateId,
    pub first_at_section: usize,
    pub returned_at_section: usize,
    pub ordered_word: Vec<InputId>,
    pub expected_trace: Vec<NativeStateId>,
    pub crossed_nonterminal_boundaries: usize,
    pub derived_from_first_repeated_boundary: bool,
}

/// The source-free boundary response and its one admitted exterior decoding.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedContinuationRest {
    pub schema: String,
    pub predecessor_identity: String,
    pub continuation_identity: String,
    pub native: GeneratorNativeRest,
    pub decoder: Vec<BoundaryDecoder>,
    pub closure: ClosureDerivation,
    pub emitted_native_ids: Vec<u32>,
    pub emitted_text: String,
    pub codec_identity: String,
    pub open_exterior: Vec<String>,
}

impl RetainedContinuationRest {
    pub fn read(bytes: &[u8]) -> Result<Self, RecurrentRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| RecurrentRefusal::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, RecurrentRefusal> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| RecurrentRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), RecurrentRefusal> {
        if self.schema != RETAINED_REST_SCHEMA {
            return Err(RecurrentRefusal::Schema(self.schema.clone()));
        }
        if self.predecessor_identity.is_empty()
            || self.continuation_identity.is_empty()
            || self.codec_identity.is_empty()
            || self.emitted_text.is_empty()
        {
            return Err(RecurrentRefusal::Identity);
        }
        self.native
            .validate()
            .map_err(|error| RecurrentRefusal::Native(error.to_string()))?;
        if self.closure.ordered_word.is_empty()
            || self.closure.expected_trace.len() != self.closure.ordered_word.len() + 1
            || self.closure.expected_trace.first() != Some(&self.closure.entering_state)
            || self.closure.expected_trace.last() != Some(&self.closure.first_repeated_state)
            || self.closure.first_at_section >= self.closure.returned_at_section
            || self.closure.returned_at_section + 1 != self.closure.expected_trace.len()
            || self.closure.crossed_nonterminal_boundaries < 1
            || !self.closure.derived_from_first_repeated_boundary
        {
            return Err(RecurrentRefusal::Closure);
        }
        let first = self.closure.expected_trace[..self.closure.returned_at_section]
            .iter()
            .position(|state| *state == self.closure.first_repeated_state)
            .ok_or(RecurrentRefusal::Closure)?;
        if first != self.closure.first_at_section
            || self.closure.expected_trace[..self.closure.returned_at_section]
                .iter()
                .copied()
                .collect::<BTreeSet<_>>()
                .len()
                != self.closure.returned_at_section
        {
            return Err(RecurrentRefusal::Closure);
        }
        let mut enacted = self.closure.entering_state;
        let mut trace = vec![enacted];
        for generator in &self.closure.ordered_word {
            enacted = self
                .native
                .conduct_word(enacted, &[*generator])
                .map_err(|error| RecurrentRefusal::Native(error.to_string()))?;
            trace.push(enacted);
        }
        if trace != self.closure.expected_trace {
            return Err(RecurrentRefusal::Closure);
        }
        let decoder = self
            .decoder
            .iter()
            .map(|entry| (entry.native, entry.face.as_ref()))
            .collect::<BTreeMap<_, _>>();
        if decoder.len() != self.native.native_population.len()
            || self
                .native
                .native_population
                .iter()
                .any(|state| !decoder.contains_key(state))
        {
            return Err(RecurrentRefusal::Decoder);
        }
        let decoded = self.closure.expected_trace[1..]
            .iter()
            .map(|state| {
                decoder
                    .get(state)
                    .and_then(|face| *face)
                    .map(|face| face.native_id)
                    .ok_or(RecurrentRefusal::Decoder)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if decoded != self.emitted_native_ids {
            return Err(RecurrentRefusal::Decoder);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RetainedContinuationPassage {
    pub schema: String,
    pub predecessor_identity: String,
    pub continuation_identity: String,
    pub entering_occurrence: String,
    pub source_fronts: Vec<SourceBoundaryFront>,
    pub sections: Vec<RetainedContinuationSection>,
    pub fibres: Vec<BoundaryFibre>,
    pub reopenings: Vec<ReceiverReopening>,
    pub rest: RetainedContinuationRest,
    pub complete_source_work: ExactWork,
    pub source_schedule_is_a_control: bool,
    pub cpu_semantic_callbacks_in_native_deed: u64,
}

impl RetainedContinuationPassage {
    pub fn found(
        predecessor_identity: String,
        continuation_identity: String,
        entering_occurrence: String,
        source_fronts: Vec<SourceBoundaryFront>,
        emitted_text: String,
        codec_identity: String,
    ) -> Result<Self, RecurrentRefusal> {
        validate_fronts(&source_fronts)?;
        if predecessor_identity.is_empty()
            || continuation_identity.is_empty()
            || entering_occurrence.is_empty()
        {
            return Err(RecurrentRefusal::Identity);
        }

        let mut state_of_face = BTreeMap::<u32, NativeStateId>::new();
        let entering_state = NativeStateId(0);
        let mut next_state = 1u64;
        let mut boundary_states = vec![entering_state];
        let mut decoder = vec![BoundaryDecoder {
            native: entering_state,
            face: None,
        }];
        for front in &source_fronts {
            let state = *state_of_face
                .entry(front.emitted.native_id)
                .or_insert_with(|| {
                    let state = NativeStateId(next_state);
                    next_state += 1;
                    decoder.push(BoundaryDecoder {
                        native: state,
                        face: Some(front.emitted.clone()),
                    });
                    state
                });
            let declared = decoder
                .iter()
                .find(|entry| entry.native == state)
                .and_then(|entry| entry.face.as_ref())
                .ok_or(RecurrentRefusal::Decoder)?;
            if declared.native_id != front.emitted.native_id
                || declared.source_surface != front.emitted.source_surface
            {
                return Err(RecurrentRefusal::Decoder);
            }
            boundary_states.push(state);
        }

        let mut transitions = BTreeMap::<NativeStateId, NativeStateId>::new();
        for edge in boundary_states.windows(2) {
            match transitions.insert(edge[0], edge[1]) {
                Some(existing) if existing != edge[1] => {
                    return Err(RecurrentRefusal::NonfunctionalBoundary {
                        from: edge[0],
                        first: existing,
                        later: edge[1],
                    });
                }
                _ => {}
            }
        }
        let native_population = (0..next_state).map(NativeStateId).collect::<Vec<_>>();
        if transitions.len() != native_population.len() {
            return Err(RecurrentRefusal::PartialBoundary);
        }
        let receiver = ReceiverId(0);
        let receiver_factors = decoder
            .iter()
            .map(
                |entry| crate::receiver_history_compression::ReceiverFactor {
                    native: entry.native,
                    receiver,
                    observation: Observation(
                        entry
                            .face
                            .as_ref()
                            .map(|face| u64::from(face.native_id) + 1)
                            .unwrap_or(0),
                    ),
                },
            )
            .collect();
        let advance = InputId(0);
        let native = GeneratorNativeRest::new(
            native_population.clone(),
            receiver_factors,
            vec![NativeGenerator {
                generator: advance,
                transport: native_population
                    .iter()
                    .map(|state| NativeTransport {
                        from: *state,
                        to: transitions[state],
                    })
                    .collect(),
            }],
        )
        .map_err(|error| RecurrentRefusal::Native(error.to_string()))?;

        let mut first_at = BTreeMap::new();
        let mut closure = None;
        for (at, state) in boundary_states.iter().copied().enumerate() {
            if let Some(first) = first_at.get(&state).copied() {
                closure = Some((state, first, at));
                break;
            }
            first_at.insert(state, at);
        }
        let (first_repeated_state, first_at_section, returned_at_section) =
            closure.ok_or(RecurrentRefusal::Closure)?;
        if returned_at_section < 3 || returned_at_section >= source_fronts.len() {
            return Err(RecurrentRefusal::Closure);
        }
        let closure = ClosureDerivation {
            entering_state,
            first_repeated_state,
            first_at_section,
            returned_at_section,
            ordered_word: vec![advance; returned_at_section],
            expected_trace: boundary_states[..=returned_at_section].to_vec(),
            crossed_nonterminal_boundaries: returned_at_section - 1,
            derived_from_first_repeated_boundary: true,
        };

        let mut sections: Vec<RetainedContinuationSection> =
            Vec::with_capacity(source_fronts.len() + 1);
        for at in 0..=source_fronts.len() {
            let (occurrence, native_ids, carried) = if at == 0 {
                (
                    source_fronts[0].before_occurrence.clone(),
                    source_fronts[0].before_native_ids.as_slice(),
                    None,
                )
            } else {
                (
                    source_fronts[at - 1].after_occurrence.clone(),
                    source_fronts[at - 1].after_native_ids.as_slice(),
                    Some(&source_fronts[at - 1]),
                )
            };
            sections.push(RetainedContinuationSection {
                occurrence,
                native_boundary: boundary_states[at],
                entering_native_ids_sha256: digest_native_ids(native_ids),
                live_fronts: source_fronts
                    .get(at)
                    .map(|front| vec![front.emitted.clone()])
                    .unwrap_or_default(),
                carried_runtime_receipt_sha256: carried
                    .map(|front| front.runtime_receipt_sha256.clone()),
                complete_terminal_potential_sha256: carried
                    .map(|front| front.complete_terminal_potential_sha256.clone()),
                terminal_hidden_sha256: carried.map(|front| front.terminal_hidden_sha256.clone()),
                predecessor: at
                    .checked_sub(1)
                    .map(|before| sections[before].occurrence.clone()),
                open_exterior: vec![
                    "successor histories beyond the first returned boundary cycle remain open"
                        .to_owned(),
                ],
            });
        }

        let fibres = native_population
            .iter()
            .map(|native| BoundaryFibre {
                native: *native,
                source_sections: sections
                    .iter()
                    .filter(|section| section.native_boundary == *native)
                    .map(|section| section.occurrence.clone())
                    .collect(),
            })
            .collect::<Vec<_>>();
        let mut reopenings = Vec::new();
        for fibre in &fibres {
            if fibre.source_sections.len() < 2 {
                continue;
            }
            let readings = sections
                .iter()
                .filter(|section| section.native_boundary == fibre.native)
                .filter_map(|section| {
                    Some((
                        section.occurrence.clone(),
                        section.complete_terminal_potential_sha256.clone()?,
                    ))
                })
                .collect::<Vec<_>>();
            if let Some(pair) = readings.windows(2).find(|pair| pair[0].1 != pair[1].1) {
                reopenings.push(ReceiverReopening {
                    native: fibre.native,
                    first_section: pair[0].0.clone(),
                    later_section: pair[1].0.clone(),
                    shortest_separating_history: vec![advance],
                    receiver: "the complete terminal-potential section after one further boundary crossing"
                        .to_owned(),
                    first_reading_sha256: pair[0].1.clone(),
                    later_reading_sha256: pair[1].1.clone(),
                });
            }
        }
        if reopenings.is_empty() {
            return Err(RecurrentRefusal::NoReopening);
        }
        let emitted_native_ids = closure.expected_trace[1..]
            .iter()
            .map(|state| {
                decoder
                    .iter()
                    .find(|entry| entry.native == *state)
                    .and_then(|entry| entry.face.as_ref())
                    .map(|face| face.native_id)
                    .ok_or(RecurrentRefusal::Decoder)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let rest = RetainedContinuationRest {
            schema: RETAINED_REST_SCHEMA.to_owned(),
            predecessor_identity: predecessor_identity.clone(),
            continuation_identity: continuation_identity.clone(),
            native,
            decoder,
            closure,
            emitted_native_ids,
            emitted_text,
            codec_identity,
            open_exterior: vec![
                "the native recurrence is exact only for the admitted source boundary/history family"
                    .to_owned(),
                "the complete source terminal potentials remain in the exterior reconstruction fibres"
                    .to_owned(),
            ],
        };
        rest.validate()?;
        let complete_source_work = source_fronts
            .iter()
            .fold(ExactWork::nothing(), |work, front| {
                work.then(&front.exact_work)
            });
        let passage = Self {
            schema: RETAINED_PASSAGE_SCHEMA.to_owned(),
            predecessor_identity,
            continuation_identity,
            entering_occurrence,
            source_fronts,
            sections,
            fibres,
            reopenings,
            rest,
            complete_source_work,
            source_schedule_is_a_control: true,
            cpu_semantic_callbacks_in_native_deed: 0,
        };
        passage.validate()?;
        Ok(passage)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, RecurrentRefusal> {
        let passage: Self = serde_json::from_slice(bytes)
            .map_err(|error| RecurrentRefusal::Wire(error.to_string()))?;
        passage.validate()?;
        Ok(passage)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, RecurrentRefusal> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| RecurrentRefusal::Wire(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), RecurrentRefusal> {
        if self.schema != RETAINED_PASSAGE_SCHEMA {
            return Err(RecurrentRefusal::Schema(self.schema.clone()));
        }
        validate_fronts(&self.source_fronts)?;
        self.rest.validate()?;
        if self.predecessor_identity != self.rest.predecessor_identity
            || self.continuation_identity != self.rest.continuation_identity
            || self.sections.len() != self.source_fronts.len() + 1
            || !self.source_schedule_is_a_control
            || self.cpu_semantic_callbacks_in_native_deed != 0
        {
            return Err(RecurrentRefusal::Identity);
        }
        let section_population = self
            .sections
            .iter()
            .map(|section| section.occurrence.as_str())
            .collect::<BTreeSet<_>>();
        let fibre_population = self
            .fibres
            .iter()
            .flat_map(|fibre| fibre.source_sections.iter().map(String::as_str))
            .collect::<Vec<_>>();
        if section_population.len() != self.sections.len()
            || fibre_population.len() != self.sections.len()
            || fibre_population.iter().copied().collect::<BTreeSet<_>>() != section_population
            || self.reopenings.is_empty()
        {
            return Err(RecurrentRefusal::Fibre);
        }
        Ok(())
    }
}

fn validate_fronts(fronts: &[SourceBoundaryFront]) -> Result<(), RecurrentRefusal> {
    if fronts.len() < 4 {
        return Err(RecurrentRefusal::FrontPopulation);
    }
    for (at, front) in fronts.iter().enumerate() {
        if front.before_occurrence.is_empty()
            || front.after_occurrence.is_empty()
            || front.before_occurrence == front.after_occurrence
            || front.before_native_ids.is_empty()
            || front.after_native_ids.len() != front.before_native_ids.len() + 1
            || !front.after_native_ids.starts_with(&front.before_native_ids)
            || front.after_native_ids.last() != Some(&front.emitted.native_id)
            || front.plural_population != 1
            || front.emitted.source_surface.is_empty()
            || front.emitted.lower > front.emitted.upper
            || !is_digest(&front.complete_terminal_potential_sha256)
            || !is_digest(&front.terminal_hidden_sha256)
            || !is_digest(&front.runtime_receipt_sha256)
        {
            return Err(RecurrentRefusal::Front { at });
        }
        if let Some(next) = fronts.get(at + 1) {
            if front.after_occurrence != next.before_occurrence
                || front.after_native_ids != next.before_native_ids
            {
                return Err(RecurrentRefusal::BrokenLineage { at });
            }
        }
    }
    Ok(())
}

pub fn digest_native_ids(ids: &[u32]) -> String {
    let mut digest = Sha256::new();
    for id in ids {
        digest.update(id.to_le_bytes());
    }
    format!("{:x}", digest.finalize())
}

fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum RecurrentRefusal {
    #[error("recurrent boundary wire refused: {0}")]
    Wire(String),
    #[error("unknown recurrent boundary schema {0}")]
    Schema(String),
    #[error("recurrent boundary identity is incomplete or inconsistent")]
    Identity,
    #[error("the source schedule must carry at least four matched fronts")]
    FrontPopulation,
    #[error("source boundary front {at} is incomplete or inconsistent")]
    Front { at: usize },
    #[error("source boundary lineage breaks after front {at}")]
    BrokenLineage { at: usize },
    #[error("native boundary {from:?} responds as both {first:?} and {later:?}")]
    NonfunctionalBoundary {
        from: NativeStateId,
        first: NativeStateId,
        later: NativeStateId,
    },
    #[error("the admitted source boundary does not found a total native response")]
    PartialBoundary,
    #[error("native recurrence refused: {0}")]
    Native(String),
    #[error("the first-return closure derivation is incomplete")]
    Closure,
    #[error("the native boundary decoder is incomplete or inconsistent")]
    Decoder,
    #[error("the reconstruction fibres do not partition the source sections")]
    Fibre,
    #[error("no richer receiver reopens the static boundary quotient")]
    NoReopening,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn face(id: u32, surface: &str, lower: i64) -> BoundaryFace {
        BoundaryFace {
            native_id: id,
            source_surface: surface.to_owned(),
            lower,
            upper: lower + 1,
        }
    }

    fn front(at: usize, before: Vec<u32>, emitted: BoundaryFace) -> SourceBoundaryFront {
        let mut after = before.clone();
        after.push(emitted.native_id);
        SourceBoundaryFront {
            before_occurrence: format!("section-{at}"),
            after_occurrence: format!("section-{}", at + 1),
            before_native_ids: before,
            after_native_ids: after,
            emitted,
            plural_population: 1,
            complete_terminal_potential_sha256: format!("{:064x}", at + 1),
            terminal_hidden_sha256: format!("{:064x}", at + 11),
            runtime_receipt_sha256: format!("{:064x}", at + 21),
            exact_work: ExactWork::nothing(),
            apparatus: SourceFrontApparatus {
                total_deed_launches: 1,
                terminal_synchronizations: 1,
                streamed_staged_octets: 4,
                asynchronous_copy_octets: 4,
                resident_octets_peak: 8,
                physical_wall_seconds: "unknown".to_owned(),
            },
        }
    }

    #[test]
    fn the_first_repeated_boundary_closes_while_the_complete_potential_reopens() {
        let fronts = vec![
            front(0, vec![9], face(7, " France", 10)),
            front(1, vec![9, 7], face(8, " is", 20)),
            front(2, vec![9, 7, 8], face(7, " France", 30)),
            front(3, vec![9, 7, 8, 7], face(8, " is", 40)),
        ];
        let passage = RetainedContinuationPassage::found(
            "predecessor".to_owned(),
            "continuation".to_owned(),
            "section-0".to_owned(),
            fronts,
            "France is France".to_owned(),
            "codec".to_owned(),
        )
        .expect("passage");
        assert_eq!(passage.rest.closure.expected_trace.len(), 4);
        assert_eq!(passage.rest.emitted_native_ids, vec![7, 8, 7]);
        assert_eq!(passage.reopenings.len(), 2);
        let bytes = passage.canonical_bytes().expect("bytes");
        assert_eq!(
            RetainedContinuationPassage::read(&bytes).expect("read"),
            passage
        );
    }
}
