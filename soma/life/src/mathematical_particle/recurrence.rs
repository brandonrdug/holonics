//! The material-founded derivation recurrence carried by one rich operation world-tube.
//!
//! This relation adds no solver, route vocabulary, or authored response extent. Each M1 passage
//! branch supplies an ordered event word. Remaining distance to that branch's actual terminal is a
//! receiver quotient; equal distances form native fibres while source events and branch lineage
//! remain in the decoder. Closure is the first repeated boundary of the resulting finite endomap.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::{MaterialOperationWorldTube, PassageBranchId};

pub const DERIVATION_RECURRENCE_SCHEMA: &str = "holonics.r2.derivation-recurrence-rest.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DerivationSourceState {
    pub state: u32,
    pub event: u64,
    pub law: u64,
    pub branch: u64,
    pub remaining_to_terminal: u32,
    pub terminal: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DerivationSourceEdge {
    pub from: u32,
    pub to: u32,
    pub generator_member_law: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DerivationHigherCell {
    pub left_event: u64,
    pub right_event: u64,
    pub interaction_witnesses: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DerivationFibreMember {
    pub source_state: u32,
    pub event: u64,
    pub branch: u64,
    pub source_occurrences: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DerivationDecoderFibre {
    pub native_state: u32,
    pub remaining_to_terminal: u32,
    pub members: Vec<DerivationFibreMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DerivationSeparator {
    pub native_state: u32,
    pub left_event: u64,
    pub right_event: u64,
    pub left_branch: u64,
    pub right_branch: u64,
    pub shortest_receiver_occurrence: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RequestedReceiverFactor {
    pub terminal_event: u64,
    pub receiver_occurrence: String,
    pub native_terminal_state: u32,
    pub factorization_returned: bool,
    pub compatible_product_returned: bool,
    pub obstruction: String,
}

/// Source-free executable standing. Source members occur only in the separately retained decoder.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DerivationRecurrenceRest {
    pub schema: String,
    pub predecessor_product_sha256: String,
    pub native_action: Vec<u32>,
    pub native_starts: Vec<u32>,
    pub generator_member_population: u32,
    pub open_exterior: Vec<String>,
}

impl DerivationRecurrenceRest {
    pub fn read(bytes: &[u8]) -> Result<Self, DerivationRecurrenceError> {
        let rest = serde_json::from_slice(bytes)
            .map_err(|error| DerivationRecurrenceError::Wire(error.to_string()))?;
        validate_rest(&rest)?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, DerivationRecurrenceError> {
        validate_rest(self)?;
        serde_json::to_vec(self).map_err(|error| DerivationRecurrenceError::Wire(error.to_string()))
    }
}

/// One exact source/native passage and its complete reconstruction boundary. It is intentionally
/// not `Clone`: source operation, quotient, decoder, receivers, and obstruction form one return.
#[derive(Debug)]
pub struct MaterialDerivationPassage {
    source_states: Vec<DerivationSourceState>,
    source_edges: Vec<DerivationSourceEdge>,
    source_action: Vec<u32>,
    source_starts: Vec<u32>,
    higher_cells: Vec<DerivationHigherCell>,
    generator_members: BTreeSet<u64>,
    rest: DerivationRecurrenceRest,
    decoder: Vec<DerivationDecoderFibre>,
    separators: Vec<DerivationSeparator>,
    receiver_factors: Vec<RequestedReceiverFactor>,
}

impl MaterialDerivationPassage {
    pub fn found(
        world: &MaterialOperationWorldTube,
        predecessor_product_sha256: impl Into<String>,
    ) -> Result<Self, DerivationRecurrenceError> {
        let predecessor_product_sha256 = predecessor_product_sha256.into();
        if predecessor_product_sha256.len() != 64
            || !predecessor_product_sha256
                .bytes()
                .all(|octet| octet.is_ascii_hexdigit())
        {
            return Err(DerivationRecurrenceError::PredecessorIdentity);
        }

        let mut source_states = Vec::new();
        let mut source_edges = Vec::new();
        let mut source_action = Vec::new();
        let mut source_starts = Vec::new();
        let mut generator_members = BTreeSet::new();
        let mut seen_events = BTreeSet::new();

        for (branch, staging) in world.passage().staging() {
            let word = world
                .passage()
                .branch(*branch)
                .ok_or(DerivationRecurrenceError::Branch(*branch))?;
            let mut events = Vec::with_capacity(word.steps.len() + 1);
            events.push((staging.event, staging.law));
            events.extend(word.steps.iter().map(|step| (step.event, step.law)));
            let start = u32::try_from(source_states.len())
                .map_err(|_| DerivationRecurrenceError::Extent)?;
            source_starts.push(start);
            let branch_length = events.len();
            for (at, (event, law)) in events.iter().enumerate() {
                let state = u32::try_from(source_states.len())
                    .map_err(|_| DerivationRecurrenceError::Extent)?;
                if !seen_events.insert(*event) {
                    return Err(DerivationRecurrenceError::RepeatedEvent(event.0));
                }
                let remaining = u32::try_from(branch_length - at - 1)
                    .map_err(|_| DerivationRecurrenceError::Extent)?;
                source_states.push(DerivationSourceState {
                    state,
                    event: event.0,
                    law: law.0,
                    branch: branch.0,
                    remaining_to_terminal: remaining,
                    terminal: remaining == 0,
                });
                source_action.push(state);
            }
            for (at, pair) in events.windows(2).enumerate() {
                let from = start
                    .checked_add(u32::try_from(at).map_err(|_| DerivationRecurrenceError::Extent)?)
                    .ok_or(DerivationRecurrenceError::Extent)?;
                let to = from
                    .checked_add(1)
                    .ok_or(DerivationRecurrenceError::Extent)?;
                generator_members.insert(pair[1].1 .0);
                source_action[from as usize] = to;
                source_edges.push(DerivationSourceEdge {
                    from,
                    to,
                    generator_member_law: pair[1].1 .0,
                });
            }
        }
        if source_starts.len() < 2 || generator_members.is_empty() {
            return Err(DerivationRecurrenceError::NotPlural);
        }
        if source_states.len() != world.passage().addressed().occurrences().len() {
            return Err(DerivationRecurrenceError::PassagePopulation);
        }

        let native_states = source_states
            .iter()
            .map(|state| state.remaining_to_terminal)
            .max()
            .ok_or(DerivationRecurrenceError::Extent)?
            .checked_add(1)
            .ok_or(DerivationRecurrenceError::Extent)?;
        let native_action = (0..native_states)
            .map(|state| state.saturating_sub(1))
            .collect::<Vec<_>>();
        if source_states.iter().any(|state| {
            let next = source_action[state.state as usize] as usize;
            source_states[next].remaining_to_terminal
                != native_action[state.remaining_to_terminal as usize]
        }) {
            return Err(DerivationRecurrenceError::NoncommutingQuotient);
        }
        let native_starts = source_starts
            .iter()
            .map(|state| source_states[*state as usize].remaining_to_terminal)
            .collect::<Vec<_>>();

        let mut decoder = Vec::new();
        let mut separators = Vec::new();
        for native_state in 0..native_states {
            let members = source_states
                .iter()
                .filter(|state| state.remaining_to_terminal == native_state)
                .map(|state| DerivationFibreMember {
                    source_state: state.state,
                    event: state.event,
                    branch: state.branch,
                    source_occurrences: world.passage().staging_sources()
                        [&PassageBranchId(state.branch)]
                        .iter()
                        .cloned()
                        .collect(),
                })
                .collect::<Vec<_>>();
            for pair in members.windows(2) {
                let left_sources = &pair[0].source_occurrences;
                let right_sources = &pair[1].source_occurrences;
                let shortest = left_sources
                    .iter()
                    .find(|source| !right_sources.contains(source))
                    .or_else(|| {
                        right_sources
                            .iter()
                            .find(|source| !left_sources.contains(source))
                    })
                    .ok_or(DerivationRecurrenceError::Separator)?;
                separators.push(DerivationSeparator {
                    native_state,
                    left_event: pair[0].event,
                    right_event: pair[1].event,
                    left_branch: pair[0].branch,
                    right_branch: pair[1].branch,
                    shortest_receiver_occurrence: shortest.clone(),
                });
            }
            decoder.push(DerivationDecoderFibre {
                native_state,
                remaining_to_terminal: native_state,
                members,
            });
        }

        let higher_cells = world
            .passage()
            .addressed()
            .pullback_joins()
            .iter()
            .map(|join| DerivationHigherCell {
                left_event: join.left().0,
                right_event: join.right().0,
                interaction_witnesses: join
                    .interactions()
                    .iter()
                    .map(|interaction| interaction.0)
                    .collect(),
            })
            .collect::<Vec<_>>();
        let terminals = source_states
            .iter()
            .filter(|state| state.terminal)
            .collect::<Vec<_>>();
        let receiver_factors = terminals
            .iter()
            .flat_map(|terminal| {
                world
                    .receiver_record_occurrences()
                    .iter()
                    .map(move |receiver| RequestedReceiverFactor {
                        terminal_event: terminal.event,
                        receiver_occurrence: receiver.clone(),
                        native_terminal_state: 0,
                        factorization_returned: true,
                        compatible_product_returned: false,
                        obstruction: "the material terminal has no founded interaction to this requested receiver occurrence".to_owned(),
                    })
            })
            .collect::<Vec<_>>();
        let rest = DerivationRecurrenceRest {
            schema: DERIVATION_RECURRENCE_SCHEMA.to_owned(),
            predecessor_product_sha256,
            native_action,
            native_starts,
            generator_member_population: u32::try_from(generator_members.len())
                .map_err(|_| DerivationRecurrenceError::Extent)?,
            open_exterior: vec![
                "variable-level mathematical operation transport is absent from the R1 boundary"
                    .to_owned(),
                "requested proof/value/boundary receivers retain explicit obstruction factors"
                    .to_owned(),
                "returned constraint has not yet changed reusable morphology".to_owned(),
            ],
        };
        validate_rest(&rest)?;
        Ok(Self {
            source_states,
            source_edges,
            source_action,
            source_starts,
            higher_cells,
            generator_members,
            rest,
            decoder,
            separators,
            receiver_factors,
        })
    }

    pub fn source_states(&self) -> &[DerivationSourceState] {
        &self.source_states
    }
    pub fn source_edges(&self) -> &[DerivationSourceEdge] {
        &self.source_edges
    }
    pub fn source_action(&self) -> &[u32] {
        &self.source_action
    }
    pub fn source_starts(&self) -> &[u32] {
        &self.source_starts
    }
    pub fn higher_cells(&self) -> &[DerivationHigherCell] {
        &self.higher_cells
    }
    pub fn generator_members(&self) -> &BTreeSet<u64> {
        &self.generator_members
    }
    pub fn rest(&self) -> &DerivationRecurrenceRest {
        &self.rest
    }
    pub fn decoder(&self) -> &[DerivationDecoderFibre] {
        &self.decoder
    }
    pub fn separators(&self) -> &[DerivationSeparator] {
        &self.separators
    }
    pub fn receiver_factors(&self) -> &[RequestedReceiverFactor] {
        &self.receiver_factors
    }
}

fn validate_rest(rest: &DerivationRecurrenceRest) -> Result<(), DerivationRecurrenceError> {
    if rest.schema != DERIVATION_RECURRENCE_SCHEMA
        || rest.predecessor_product_sha256.len() != 64
        || !rest
            .predecessor_product_sha256
            .bytes()
            .all(|octet| octet.is_ascii_hexdigit())
        || rest.native_action.is_empty()
        || rest.native_starts.len() < 2
        || rest.generator_member_population == 0
        || rest.open_exterior.is_empty()
        || rest.open_exterior.iter().any(String::is_empty)
        || rest
            .native_action
            .iter()
            .chain(&rest.native_starts)
            .any(|state| *state as usize >= rest.native_action.len())
    {
        return Err(DerivationRecurrenceError::Rest);
    }
    Ok(())
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DerivationRecurrenceError {
    #[error("the predecessor product has no exact SHA-256 identity")]
    PredecessorIdentity,
    #[error("passage branch {0:?} is incomplete")]
    Branch(PassageBranchId),
    #[error("derivation recurrence extent cannot cross the exact wire")]
    Extent,
    #[error("event {0} occurs in more than one derivation section")]
    RepeatedEvent(u64),
    #[error("the material recurrence is not plural")]
    NotPlural,
    #[error("the source recurrence does not cover the complete addressed passage")]
    PassagePopulation,
    #[error("the remaining-to-terminal quotient square does not commute")]
    NoncommutingQuotient,
    #[error("a compactified fibre has no separating receiver occurrence")]
    Separator,
    #[error("the source-detached derivation recurrence rest is incomplete")]
    Rest,
    #[error("derivation recurrence wire refused: {0}")]
    Wire(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_detached_rest_refuses_an_authored_state_outside_its_material_extent() {
        let bytes = br#"{"schema":"holonics.r2.derivation-recurrence-rest.v1","predecessor_product_sha256":"0000000000000000000000000000000000000000000000000000000000000000","native_action":[0,0],"native_starts":[1,2],"generator_member_population":1,"open_exterior":["open"]}"#;
        assert_eq!(
            DerivationRecurrenceRest::read(bytes),
            Err(DerivationRecurrenceError::Rest)
        );
    }
}
