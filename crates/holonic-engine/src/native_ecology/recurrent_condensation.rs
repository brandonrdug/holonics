//! Recurrent native condensation of the physical realization passage.
//!
//! The source recurrence, its returned successor, and the richer terminal-potential receiver do
//! not form one quotient. The boundary transport squares commute through a three-state native
//! action; two potential pairs do not factor and therefore remain complete reconstruction fibres
//! with shortest separators. This owner seals exactly that product as three exterior components:
//! compact standing, executable decoder, and retained fibres. It owns no clustering, semantic
//! labels, schedule, source coordinate, or foreign tensor address.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::{
    recurrent::{BoundaryFace, RetainedContinuationPassage},
    recurrent_return::{ReturnDecision, ReturnedRecurrentRest},
};

pub const CONDENSED_STANDING_SCHEMA: &str = "holonics.i3.condensed-standing.v1";
pub const CONDENSED_DECODER_SCHEMA: &str = "holonics.i3.condensed-decoder.v1";
pub const CONDENSED_FIBRES_SCHEMA: &str = "holonics.i3.condensed-fibres.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CondensedStanding {
    pub schema: String,
    pub source_passage_sha256: String,
    pub returned_predecessor_sha256: String,
    pub native_states: u32,
    /// The committed successor action, indexed only by dense native state.
    pub successor_action: Vec<u32>,
    /// The one retained noncommuting predecessor route is a local override, not a second table.
    pub predecessor_from: u32,
    pub predecessor_to: u32,
    pub main_start: u32,
    pub held_out_start: u32,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CompactBoundaryFace {
    pub native_id: u32,
    pub source_surface: String,
    /// The upper boundary is exactly `lower + 1` in the admitted I1 face family.
    pub lower: i64,
}

impl CompactBoundaryFace {
    pub fn upper(&self) -> Result<i64, RecurrentCondensationRefusal> {
        self.lower
            .checked_add(1)
            .ok_or(RecurrentCondensationRefusal::Decoder)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CondensedDecoder {
    pub schema: String,
    /// Dense native-state order; `None` is a genuine un-emitted entering boundary.
    pub faces: Vec<Option<CompactBoundaryFace>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CondensedFibreMember {
    pub occurrence: String,
    pub terminal_potential_sha256: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CondensedFibre {
    pub native: u32,
    pub members: Vec<CondensedFibreMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CondensedSeparator {
    pub native: u32,
    pub left_occurrence: String,
    pub right_occurrence: String,
    pub left_potential_sha256: String,
    pub right_potential_sha256: String,
    pub shortest_history: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CondensedFibres {
    pub schema: String,
    pub fibres: Vec<CondensedFibre>,
    pub separators: Vec<CondensedSeparator>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CondensedRecurrentRest {
    pub standing: CondensedStanding,
    pub decoder: CondensedDecoder,
    pub fibres: CondensedFibres,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CondensedRoute {
    Predecessor,
    Successor,
    Withdrawn,
}

impl CondensedRecurrentRest {
    /// Condense the admitted I1 physical passage and I2 returned successor. The richer receiver
    /// faces are copied only into the reconstruction component and never used as quotient keys.
    pub fn found(
        passage_bytes: &[u8],
        returned_bytes: &[u8],
    ) -> Result<Self, RecurrentCondensationRefusal> {
        let passage = RetainedContinuationPassage::read(passage_bytes)
            .map_err(|error| RecurrentCondensationRefusal::Source(error.to_string()))?;
        let returned = ReturnedRecurrentRest::read(returned_bytes)
            .map_err(|error| RecurrentCondensationRefusal::Source(error.to_string()))?;
        if returned.decision.decision != ReturnDecision::Committed
            || sha256(
                &passage
                    .rest
                    .canonical_bytes()
                    .map_err(|error| RecurrentCondensationRefusal::Source(error.to_string()))?,
            ) != returned.predecessor_sha256
            || returned.base.generators.len() != 1
            || returned.base.native_population.len() != returned.decoder.len()
        {
            return Err(RecurrentCondensationRefusal::Lineage);
        }

        let state_count = returned.base.native_population.len();
        if !returned
            .base
            .native_population
            .iter()
            .enumerate()
            .all(|(at, state)| state.0 == at as u64)
        {
            return Err(RecurrentCondensationRefusal::Standing);
        }
        let generator = &returned.base.generators[0];
        if generator.generator != returned.delta.generator {
            return Err(RecurrentCondensationRefusal::Lineage);
        }
        let mut successor_action = vec![0u32; state_count];
        for edge in &generator.transport {
            let from =
                usize::try_from(edge.from.0).map_err(|_| RecurrentCondensationRefusal::Standing)?;
            let to =
                u32::try_from(edge.to.0).map_err(|_| RecurrentCondensationRefusal::Standing)?;
            if from >= state_count {
                return Err(RecurrentCondensationRefusal::Standing);
            }
            successor_action[from] = to;
        }
        let changed_state = usize::try_from(returned.delta.from.0)
            .map_err(|_| RecurrentCondensationRefusal::Standing)?;
        if changed_state >= successor_action.len() {
            return Err(RecurrentCondensationRefusal::Standing);
        }
        successor_action[changed_state] = u32::try_from(returned.delta.successor_to.0)
            .map_err(|_| RecurrentCondensationRefusal::Standing)?;

        let faces = returned
            .decoder
            .iter()
            .map(|entry| entry.face.as_ref().map(compact_face))
            .collect::<Vec<_>>();
        let mut fibres = Vec::with_capacity(passage.fibres.len());
        for fibre in &passage.fibres {
            let members = fibre
                .source_sections
                .iter()
                .map(|occurrence| {
                    let section = passage
                        .sections
                        .iter()
                        .find(|section| section.occurrence == *occurrence)
                        .ok_or(RecurrentCondensationRefusal::Fibre)?;
                    Ok(CondensedFibreMember {
                        occurrence: occurrence.clone(),
                        terminal_potential_sha256: section
                            .complete_terminal_potential_sha256
                            .clone(),
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            fibres.push(CondensedFibre {
                native: u32::try_from(fibre.native.0)
                    .map_err(|_| RecurrentCondensationRefusal::Fibre)?,
                members,
            });
        }
        let separators = passage
            .reopenings
            .iter()
            .map(|reopening| {
                let native = u32::try_from(reopening.native.0)
                    .map_err(|_| RecurrentCondensationRefusal::Separator)?;
                let shortest_history = reopening
                    .shortest_separating_history
                    .iter()
                    .map(|input| {
                        u32::try_from(input.0).map_err(|_| RecurrentCondensationRefusal::Separator)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(CondensedSeparator {
                    native,
                    left_occurrence: reopening.first_section.clone(),
                    right_occurrence: reopening.later_section.clone(),
                    left_potential_sha256: reopening.first_reading_sha256.clone(),
                    right_potential_sha256: reopening.later_reading_sha256.clone(),
                    shortest_history,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let native_states =
            u32::try_from(state_count).map_err(|_| RecurrentCondensationRefusal::Standing)?;
        let predecessor_from = u32::try_from(returned.delta.from.0)
            .map_err(|_| RecurrentCondensationRefusal::Standing)?;
        let predecessor_to = u32::try_from(returned.delta.predecessor_to.0)
            .map_err(|_| RecurrentCondensationRefusal::Standing)?;
        let main_start = u32::try_from(returned.main_start.0)
            .map_err(|_| RecurrentCondensationRefusal::Standing)?;
        let held_out_start = u32::try_from(returned.held_out_start.0)
            .map_err(|_| RecurrentCondensationRefusal::Standing)?;
        let rest = Self {
            standing: CondensedStanding {
                schema: CONDENSED_STANDING_SCHEMA.to_owned(),
                source_passage_sha256: sha256(passage_bytes),
                returned_predecessor_sha256: sha256(returned_bytes),
                native_states,
                successor_action,
                predecessor_from,
                predecessor_to,
                main_start,
                held_out_start,
                open_exterior: vec![
                    "terminal-potential faces remain reconstruction fibres, not native equality"
                        .to_owned(),
                    "unexcited foreign successor histories remain open".to_owned(),
                    "modality ports have not yet entered this recurrent condensation".to_owned(),
                ],
            },
            decoder: CondensedDecoder {
                schema: CONDENSED_DECODER_SCHEMA.to_owned(),
                faces,
            },
            fibres: CondensedFibres {
                schema: CONDENSED_FIBRES_SCHEMA.to_owned(),
                fibres,
                separators,
            },
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(
        standing_bytes: &[u8],
        decoder_bytes: &[u8],
        fibre_bytes: &[u8],
    ) -> Result<Self, RecurrentCondensationRefusal> {
        let standing = serde_json::from_slice(standing_bytes)
            .map_err(|error| RecurrentCondensationRefusal::Wire(error.to_string()))?;
        let decoder = serde_json::from_slice(decoder_bytes)
            .map_err(|error| RecurrentCondensationRefusal::Wire(error.to_string()))?;
        let fibres = serde_json::from_slice(fibre_bytes)
            .map_err(|error| RecurrentCondensationRefusal::Wire(error.to_string()))?;
        let rest = Self {
            standing,
            decoder,
            fibres,
        };
        rest.validate()?;
        Ok(rest)
    }

    pub fn standing_bytes(&self) -> Result<Vec<u8>, RecurrentCondensationRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.standing)
            .map_err(|error| RecurrentCondensationRefusal::Wire(error.to_string()))
    }

    pub fn decoder_bytes(&self) -> Result<Vec<u8>, RecurrentCondensationRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.decoder)
            .map_err(|error| RecurrentCondensationRefusal::Wire(error.to_string()))
    }

    pub fn fibre_bytes(&self) -> Result<Vec<u8>, RecurrentCondensationRefusal> {
        self.validate()?;
        serde_json::to_vec(&self.fibres)
            .map_err(|error| RecurrentCondensationRefusal::Wire(error.to_string()))
    }

    pub fn trace(
        &self,
        route: CondensedRoute,
        start: u32,
    ) -> Result<Vec<u32>, RecurrentCondensationRefusal> {
        if start >= self.standing.native_states {
            return Err(RecurrentCondensationRefusal::Standing);
        }
        let mut trace = vec![start];
        let mut state = start;
        for _ in 0..self.standing.native_states {
            let next = match route {
                CondensedRoute::Withdrawn => state,
                CondensedRoute::Successor => self.standing.successor_action[state as usize],
                CondensedRoute::Predecessor if state == self.standing.predecessor_from => {
                    self.standing.predecessor_to
                }
                CondensedRoute::Predecessor => self.standing.successor_action[state as usize],
            };
            let repeated = trace.contains(&next);
            trace.push(next);
            if repeated {
                return Ok(trace);
            }
            state = next;
        }
        Err(RecurrentCondensationRefusal::Recurrence)
    }

    pub fn decode_trace(&self, trace: &[u32]) -> Result<String, RecurrentCondensationRefusal> {
        if trace.len() < 2 {
            return Err(RecurrentCondensationRefusal::Recurrence);
        }
        let mut text = String::new();
        for state in trace.iter().skip(1) {
            let face = self
                .decoder
                .faces
                .get(*state as usize)
                .ok_or(RecurrentCondensationRefusal::Decoder)?;
            if let Some(face) = face {
                text.push_str(&face.source_surface.replace('▁', " "));
            }
        }
        Ok(text)
    }

    pub fn validate(&self) -> Result<(), RecurrentCondensationRefusal> {
        let standing = &self.standing;
        if standing.schema != CONDENSED_STANDING_SCHEMA
            || self.decoder.schema != CONDENSED_DECODER_SCHEMA
            || self.fibres.schema != CONDENSED_FIBRES_SCHEMA
            || !is_digest(&standing.source_passage_sha256)
            || !is_digest(&standing.returned_predecessor_sha256)
            || standing.native_states == 0
            || standing.successor_action.len() != standing.native_states as usize
            || standing.open_exterior.is_empty()
            || standing.open_exterior.iter().any(String::is_empty)
        {
            return Err(RecurrentCondensationRefusal::Standing);
        }
        for state in standing.successor_action.iter().copied().chain([
            standing.predecessor_from,
            standing.predecessor_to,
            standing.main_start,
            standing.held_out_start,
        ]) {
            if state >= standing.native_states {
                return Err(RecurrentCondensationRefusal::Standing);
            }
        }
        if standing.main_start == standing.held_out_start
            || standing.successor_action[standing.predecessor_from as usize]
                == standing.predecessor_to
            || self.decoder.faces.len() != standing.native_states as usize
            || self.decoder.faces[standing.main_start as usize].is_some()
        {
            return Err(RecurrentCondensationRefusal::Standing);
        }
        for face in self.decoder.faces.iter().flatten() {
            if face.source_surface.is_empty() || face.upper().is_err() {
                return Err(RecurrentCondensationRefusal::Decoder);
            }
        }

        if self.fibres.fibres.len() != standing.native_states as usize {
            return Err(RecurrentCondensationRefusal::Fibre);
        }
        let mut occurrences = BTreeSet::new();
        for (native, fibre) in self.fibres.fibres.iter().enumerate() {
            if fibre.native != native as u32 || fibre.members.is_empty() {
                return Err(RecurrentCondensationRefusal::Fibre);
            }
            for member in &fibre.members {
                if !is_digest(&member.occurrence)
                    || member
                        .terminal_potential_sha256
                        .as_ref()
                        .is_some_and(|value| !is_digest(value))
                    || !occurrences.insert(member.occurrence.clone())
                {
                    return Err(RecurrentCondensationRefusal::Fibre);
                }
            }
        }
        if occurrences.len() < standing.native_states as usize {
            return Err(RecurrentCondensationRefusal::Fibre);
        }
        for separator in &self.fibres.separators {
            let fibre = self
                .fibres
                .fibres
                .get(separator.native as usize)
                .ok_or(RecurrentCondensationRefusal::Separator)?;
            let member = |occurrence: &str| {
                fibre
                    .members
                    .iter()
                    .find(|member| member.occurrence == occurrence)
            };
            if separator.shortest_history.is_empty()
                || separator.left_occurrence == separator.right_occurrence
                || !is_digest(&separator.left_potential_sha256)
                || !is_digest(&separator.right_potential_sha256)
                || separator.left_potential_sha256 == separator.right_potential_sha256
                || member(&separator.left_occurrence)
                    .and_then(|entry| entry.terminal_potential_sha256.as_ref())
                    != Some(&separator.left_potential_sha256)
                || member(&separator.right_occurrence)
                    .and_then(|entry| entry.terminal_potential_sha256.as_ref())
                    != Some(&separator.right_potential_sha256)
            {
                return Err(RecurrentCondensationRefusal::Separator);
            }
        }
        if self.fibres.separators.is_empty() {
            return Err(RecurrentCondensationRefusal::Separator);
        }

        let main_predecessor = self.trace(CondensedRoute::Predecessor, standing.main_start)?;
        let main_successor = self.trace(CondensedRoute::Successor, standing.main_start)?;
        let held_predecessor = self.trace(CondensedRoute::Predecessor, standing.held_out_start)?;
        let held_successor = self.trace(CondensedRoute::Successor, standing.held_out_start)?;
        if main_predecessor == main_successor
            || held_predecessor == held_successor
            || self.decode_trace(&main_predecessor)? == self.decode_trace(&main_successor)?
            || self.decode_trace(&held_predecessor)? == self.decode_trace(&held_successor)?
        {
            return Err(RecurrentCondensationRefusal::Recurrence);
        }
        Ok(())
    }
}

fn compact_face(face: &BoundaryFace) -> CompactBoundaryFace {
    CompactBoundaryFace {
        native_id: face.native_id,
        source_surface: face.source_surface.clone(),
        lower: face.lower,
    }
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

fn is_digest(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum RecurrentCondensationRefusal {
    #[error("recurrent condensation wire refused: {0}")]
    Wire(String),
    #[error("recurrent condensation source refused: {0}")]
    Source(String),
    #[error("the I1/I2 addressed lineage does not compose")]
    Lineage,
    #[error("the compact recurrent standing is malformed")]
    Standing,
    #[error("the compact boundary decoder is malformed")]
    Decoder,
    #[error("the complete reconstruction fibre population is malformed")]
    Fibre,
    #[error("a receiver-visible route has no valid shortest separator")]
    Separator,
    #[error("the compact action did not close by recurrence")]
    Recurrence,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn digest(octet: char) -> String {
        std::iter::repeat_n(octet, 64).collect()
    }

    fn fixture() -> CondensedRecurrentRest {
        CondensedRecurrentRest {
            standing: CondensedStanding {
                schema: CONDENSED_STANDING_SCHEMA.to_owned(),
                source_passage_sha256: digest('a'),
                returned_predecessor_sha256: digest('b'),
                native_states: 3,
                successor_action: vec![1, 2, 2],
                predecessor_from: 2,
                predecessor_to: 1,
                main_start: 0,
                held_out_start: 1,
                open_exterior: vec!["unexcited histories remain open".to_owned()],
            },
            decoder: CondensedDecoder {
                schema: CONDENSED_DECODER_SCHEMA.to_owned(),
                faces: vec![
                    None,
                    Some(CompactBoundaryFace {
                        native_id: 7001,
                        source_surface: "▁France".to_owned(),
                        lower: 7,
                    }),
                    Some(CompactBoundaryFace {
                        native_id: 563,
                        source_surface: "▁is".to_owned(),
                        lower: 9,
                    }),
                ],
            },
            fibres: CondensedFibres {
                schema: CONDENSED_FIBRES_SCHEMA.to_owned(),
                fibres: vec![
                    CondensedFibre {
                        native: 0,
                        members: vec![CondensedFibreMember {
                            occurrence: digest('0'),
                            terminal_potential_sha256: None,
                        }],
                    },
                    CondensedFibre {
                        native: 1,
                        members: vec![
                            CondensedFibreMember {
                                occurrence: digest('1'),
                                terminal_potential_sha256: Some(digest('c')),
                            },
                            CondensedFibreMember {
                                occurrence: digest('3'),
                                terminal_potential_sha256: Some(digest('d')),
                            },
                        ],
                    },
                    CondensedFibre {
                        native: 2,
                        members: vec![
                            CondensedFibreMember {
                                occurrence: digest('2'),
                                terminal_potential_sha256: Some(digest('e')),
                            },
                            CondensedFibreMember {
                                occurrence: digest('4'),
                                terminal_potential_sha256: Some(digest('f')),
                            },
                        ],
                    },
                ],
                separators: vec![
                    CondensedSeparator {
                        native: 1,
                        left_occurrence: digest('1'),
                        right_occurrence: digest('3'),
                        left_potential_sha256: digest('c'),
                        right_potential_sha256: digest('d'),
                        shortest_history: vec![0],
                    },
                    CondensedSeparator {
                        native: 2,
                        left_occurrence: digest('2'),
                        right_occurrence: digest('4'),
                        left_potential_sha256: digest('e'),
                        right_potential_sha256: digest('f'),
                        shortest_history: vec![0],
                    },
                ],
            },
        }
    }

    #[test]
    fn the_compact_rest_returns_both_routes_and_complete_fibres() {
        let rest = fixture();
        rest.validate().expect("the fixture is a lawful rest");
        assert_eq!(
            rest.decode_trace(
                &rest
                    .trace(CondensedRoute::Predecessor, 0)
                    .expect("predecessor closes")
            )
            .expect("predecessor decodes"),
            " France is France"
        );
        assert_eq!(
            rest.decode_trace(
                &rest
                    .trace(CondensedRoute::Successor, 0)
                    .expect("successor closes")
            )
            .expect("successor decodes"),
            " France is is"
        );
        let remounted = CondensedRecurrentRest::read(
            &rest.standing_bytes().expect("standing serializes"),
            &rest.decoder_bytes().expect("decoder serializes"),
            &rest.fibre_bytes().expect("fibres serialize"),
        )
        .expect("three components remount");
        assert_eq!(remounted, rest);
    }

    #[test]
    fn collapsing_a_receiver_visible_pair_is_refused() {
        let mut rest = fixture();
        rest.fibres.fibres[1].members.pop();
        assert_eq!(
            rest.validate(),
            Err(RecurrentCondensationRefusal::Separator)
        );
    }
}
