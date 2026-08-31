//! Exterior return and local cultivation of one retained native recurrence.
//!
//! This owner closes the relation absent between [`super::recurrent`] and the existing exact
//! adjoint/cultivation laws. It does not own a tool, scheduler, trainer, language, or second native
//! body. One actual exterior consequence supplies an oriented nonzero return. The return follows
//! the already-retained closing edge, founds one rank-one local generator difference, and leaves a
//! source-detached rest carrying the predecessor action plus that difference. Targeted ablation is
//! subtraction of the same addressed difference, not reconstruction from source material.

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use relational_geometry::Rat;

use crate::{
    exact_linear::{ExactLinearError, ExactRatMatrix},
    generator_native_rest::GeneratorNativeRest,
    receiver_exact_compression::InputId,
    receiver_history_compression::NativeStateId,
};

use super::recurrent::{BoundaryDecoder, RetainedContinuationRest};

pub const RETURNED_RECURRENCE_SCHEMA: &str = "holonics.i2.returned-recurrence-rest.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorToolReturn {
    pub schema: String,
    pub receiver: String,
    pub emitted_occurrence: String,
    pub consequence_occurrence: String,
    pub return_occurrence: String,
    pub emitted_sha256: String,
    pub consequence_sha256: String,
    pub echoed_sha256: String,
    pub before_octets: u64,
    pub after_octets: u64,
    pub exact_difference_octets: u64,
    pub process_status: i32,
}

impl ExteriorToolReturn {
    pub fn validate(&self) -> Result<(), RecurrentReturnRefusal> {
        if self.schema != "holonics.i2.exterior-tool-return.v1"
            || self.receiver.is_empty()
            || self.emitted_occurrence.is_empty()
            || self.consequence_occurrence.is_empty()
            || self.return_occurrence.is_empty()
            || self.emitted_occurrence == self.consequence_occurrence
            || self.emitted_occurrence == self.return_occurrence
            || self.consequence_occurrence == self.return_occurrence
            || !is_digest(&self.emitted_sha256)
            || self.emitted_sha256 != self.consequence_sha256
            || self.emitted_sha256 != self.echoed_sha256
            || self.before_octets != 0
            || self.after_octets.checked_sub(self.before_octets)
                != Some(self.exact_difference_octets)
            || self.process_status != 0
        {
            return Err(RecurrentReturnRefusal::Exterior);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ReturnDecision {
    Committed,
    Declined,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnCommitEvent {
    pub decision: ReturnDecision,
    pub returned_difference_octets: u64,
    pub predecessor_sha256: String,
    pub successor_sha256: Option<String>,
    pub reason: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalGeneratorDelta {
    pub generator: InputId,
    pub from: NativeStateId,
    pub predecessor_to: NativeStateId,
    pub successor_to: NativeStateId,
    pub left_factor: Vec<Rat>,
    pub right_factor: Vec<Rat>,
    pub delta: ExactRatMatrix,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedCausalAdjoint {
    pub forward_lineage: Vec<NativeStateId>,
    pub return_lineage: Vec<NativeStateId>,
    pub receiver_metric: ExactRatMatrix,
    pub metric_adjoint: ExactRatMatrix,
    pub measured_delta_rank: usize,
    pub returned_content: u64,
    pub primitive_orientation: i8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RevisitHolonomy {
    pub predecessor_action: ExactRatMatrix,
    pub successor_action: ExactRatMatrix,
    pub commutator: ExactRatMatrix,
    pub commutator_rank: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecurrentSemanticWork {
    pub starting_occurrences: u64,
    pub predecessor_transition_reads: u64,
    pub successor_transition_reads: u64,
    pub ablation_transition_reads: u64,
    pub recurrence_equality_comparisons: u64,
    pub trace_entries_written: u64,
    pub dependency_span: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReturnedRecurrentRest {
    pub schema: String,
    pub predecessor_sha256: String,
    pub entering_occurrence: String,
    pub exterior: ExteriorToolReturn,
    pub decision: ReturnCommitEvent,
    pub base: GeneratorNativeRest,
    pub decoder: Vec<BoundaryDecoder>,
    pub delta: LocalGeneratorDelta,
    pub causal_adjoint: ReturnedCausalAdjoint,
    pub holonomy: RevisitHolonomy,
    pub recurrence_starts: Vec<NativeStateId>,
    pub main_start: NativeStateId,
    pub held_out_start: NativeStateId,
    pub control_from: NativeStateId,
    pub semantic_work_prediction: RecurrentSemanticWork,
    pub open_fibres: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DeclinedReturn {
    pub schema: String,
    pub exterior: ExteriorToolReturn,
    pub event: ReturnCommitEvent,
}

impl DeclinedReturn {
    pub fn from_exterior(
        exterior: ExteriorToolReturn,
        predecessor_sha256: String,
    ) -> Result<Self, RecurrentReturnRefusal> {
        exterior.validate()?;
        if exterior.exact_difference_octets != 0 || !is_digest(&predecessor_sha256) {
            return Err(RecurrentReturnRefusal::Decision);
        }
        Ok(Self {
            schema: "holonics.i2.declined-return.v1".to_owned(),
            event: ReturnCommitEvent {
                decision: ReturnDecision::Declined,
                returned_difference_octets: 0,
                predecessor_sha256,
                successor_sha256: None,
                reason: "the exterior crossing left no receiver-visible residue".to_owned(),
            },
            exterior,
        })
    }
}

impl ReturnedRecurrentRest {
    pub fn seal(
        predecessor_bytes: &[u8],
        entering_occurrence: String,
        exterior: ExteriorToolReturn,
    ) -> Result<Self, RecurrentReturnRefusal> {
        let predecessor = RetainedContinuationRest::read(predecessor_bytes)
            .map_err(|error| RecurrentReturnRefusal::Predecessor(error.to_string()))?;
        exterior.validate()?;
        if exterior.exact_difference_octets == 0 {
            return Err(RecurrentReturnRefusal::Decision);
        }
        if entering_occurrence.is_empty() {
            return Err(RecurrentReturnRefusal::Lineage);
        }
        let forward = &predecessor.closure.expected_trace;
        let from = *forward
            .get(
                forward
                    .len()
                    .checked_sub(2)
                    .ok_or(RecurrentReturnRefusal::Lineage)?,
            )
            .ok_or(RecurrentReturnRefusal::Lineage)?;
        let predecessor_to = *forward.last().ok_or(RecurrentReturnRefusal::Lineage)?;
        if from == predecessor_to
            || predecessor.closure.ordered_word.is_empty()
            || predecessor
                .closure
                .ordered_word
                .iter()
                .any(|generator| *generator != predecessor.closure.ordered_word[0])
        {
            return Err(RecurrentReturnRefusal::Lineage);
        }
        let generator = predecessor.closure.ordered_word[0];
        let successor_to = from;
        let dimension = predecessor.native.native_population.len();
        let (delta, left_factor, right_factor) =
            local_delta(dimension, from, predecessor_to, successor_to)?;
        let predecessor_action = action_matrix(&predecessor.native, generator)?;
        let successor_action = predecessor_action.add(&delta)?;
        let receiver_metric = ExactRatMatrix::identity(dimension)?;
        let metric_adjoint = delta.metric_adjoint(&receiver_metric, &receiver_metric)?;
        let expected_adjoint = delta.transpose()?;
        if metric_adjoint != expected_adjoint || delta.rank()? != 1 {
            return Err(RecurrentReturnRefusal::Adjoint);
        }
        let commutator = predecessor_action
            .multiply(&delta)?
            .subtract(&delta.multiply(&predecessor_action)?)?;
        let commutator_rank = commutator.rank()?;
        if commutator_rank == 0 {
            return Err(RecurrentReturnRefusal::Holonomy);
        }

        let recurrence_starts = predecessor.native.native_population.clone();
        let main_start = predecessor.closure.entering_state;
        let held_out_start = recurrence_starts
            .iter()
            .copied()
            .filter(|state| *state != main_start)
            .find(|state| {
                recurrence_trace(&predecessor.native, generator, *state, None)
                    != recurrence_trace(
                        &predecessor.native,
                        generator,
                        *state,
                        Some((from, successor_to)),
                    )
            })
            .ok_or(RecurrentReturnRefusal::HeldOut)?;
        let control_from = recurrence_starts
            .iter()
            .copied()
            .find(|state| {
                *state != from
                    && next(&predecessor.native, generator, *state, None)
                        == next(
                            &predecessor.native,
                            generator,
                            *state,
                            Some((from, successor_to)),
                        )
            })
            .ok_or(RecurrentReturnRefusal::Control)?;
        let semantic_work_prediction = semantic_work(
            &predecessor.native,
            generator,
            &recurrence_starts,
            (from, successor_to),
        )?;
        let predecessor_sha256 = sha256(predecessor_bytes);
        let mut rest = Self {
            schema: RETURNED_RECURRENCE_SCHEMA.to_owned(),
            predecessor_sha256: predecessor_sha256.clone(),
            entering_occurrence,
            exterior,
            decision: ReturnCommitEvent {
                decision: ReturnDecision::Committed,
                returned_difference_octets: 0,
                predecessor_sha256,
                successor_sha256: None,
                reason: "a positive exterior residue returned through the closing edge".to_owned(),
            },
            base: predecessor.native,
            decoder: predecessor.decoder,
            delta: LocalGeneratorDelta {
                generator,
                from,
                predecessor_to,
                successor_to,
                left_factor,
                right_factor,
                delta,
            },
            causal_adjoint: ReturnedCausalAdjoint {
                forward_lineage: forward.clone(),
                return_lineage: forward.iter().copied().rev().collect(),
                receiver_metric,
                metric_adjoint,
                measured_delta_rank: 1,
                returned_content: 0,
                primitive_orientation: 1,
            },
            holonomy: RevisitHolonomy {
                predecessor_action,
                successor_action,
                commutator,
                commutator_rank,
            },
            recurrence_starts,
            main_start,
            held_out_start,
            control_from,
            semantic_work_prediction,
            open_fibres: vec![
                "the byte-preserving exterior receiver does not grade linguistic truth".to_owned(),
                "world receivers beyond the admitted exact tool consequence remain open".to_owned(),
                "the local generator delta is exact only for the retained I1 native family"
                    .to_owned(),
            ],
        };
        rest.decision.returned_difference_octets = rest.exterior.exact_difference_octets;
        rest.causal_adjoint.returned_content = rest.exterior.exact_difference_octets;
        let provisional = rest.canonical_bytes_without_successor()?;
        rest.decision.successor_sha256 = Some(sha256(&provisional));
        rest.validate()?;
        Ok(rest)
    }

    pub fn read(bytes: &[u8]) -> Result<Self, RecurrentReturnRefusal> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| RecurrentReturnRefusal::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, RecurrentReturnRefusal> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| RecurrentReturnRefusal::Wire(error.to_string()))
    }

    pub fn generator_table(&self) -> Result<Vec<u32>, RecurrentReturnRefusal> {
        let states = self.base.native_population.len();
        let mut table = Vec::with_capacity(states * self.base.generators.len());
        for generator in &self.base.generators {
            for state in &self.base.native_population {
                table.push(
                    u32::try_from(next(&self.base, generator.generator, *state, None)?.0)
                        .map_err(|_| RecurrentReturnRefusal::Carrier)?,
                );
            }
        }
        Ok(table)
    }

    pub fn decode_trace(&self, trace: &[u32]) -> Result<String, RecurrentReturnRefusal> {
        let mut text = String::new();
        for state in trace.iter().skip(1) {
            let face = self
                .decoder
                .iter()
                .find(|entry| entry.native.0 == u64::from(*state))
                .and_then(|entry| entry.face.as_ref())
                .ok_or(RecurrentReturnRefusal::Decoder)?;
            text.push_str(&face.source_surface.replace('▁', " "));
        }
        Ok(text)
    }

    fn canonical_bytes_without_successor(&self) -> Result<Vec<u8>, RecurrentReturnRefusal> {
        let mut copy = self.clone();
        copy.decision.successor_sha256 = None;
        serde_json::to_vec(&copy).map_err(|error| RecurrentReturnRefusal::Wire(error.to_string()))
    }

    fn validate(&self) -> Result<(), RecurrentReturnRefusal> {
        if self.schema != RETURNED_RECURRENCE_SCHEMA
            || !is_digest(&self.predecessor_sha256)
            || self.entering_occurrence.is_empty()
            || self.recurrence_starts != self.base.native_population
            || self.decision.decision != ReturnDecision::Committed
            || self.decision.returned_difference_octets != self.exterior.exact_difference_octets
            || self.decision.predecessor_sha256 != self.predecessor_sha256
            || self.causal_adjoint.returned_content != self.exterior.exact_difference_octets
            || self.causal_adjoint.primitive_orientation != 1
        {
            return Err(RecurrentReturnRefusal::Identity);
        }
        self.exterior.validate()?;
        self.base
            .validate()
            .map_err(|error| RecurrentReturnRefusal::Predecessor(error.to_string()))?;
        let dense = self
            .base
            .native_population
            .iter()
            .enumerate()
            .all(|(at, state)| state.0 == at as u64);
        if !dense || self.decoder.len() != self.base.native_population.len() {
            return Err(RecurrentReturnRefusal::Decoder);
        }
        let expected_delta = local_delta(
            self.base.native_population.len(),
            self.delta.from,
            self.delta.predecessor_to,
            self.delta.successor_to,
        )?;
        if self.delta.delta != expected_delta.0
            || self.delta.left_factor != expected_delta.1
            || self.delta.right_factor != expected_delta.2
            || self.delta.successor_to != self.delta.from
            || next(&self.base, self.delta.generator, self.delta.from, None)?
                != self.delta.predecessor_to
        {
            return Err(RecurrentReturnRefusal::Delta);
        }
        let predecessor_action = action_matrix(&self.base, self.delta.generator)?;
        let successor_action = predecessor_action.add(&self.delta.delta)?;
        let metric = ExactRatMatrix::identity(self.base.native_population.len())?;
        if self.holonomy.predecessor_action != predecessor_action
            || self.holonomy.successor_action != successor_action
            || self.causal_adjoint.receiver_metric != metric
            || self.causal_adjoint.metric_adjoint != self.delta.delta.transpose()?
            || self.causal_adjoint.measured_delta_rank != self.delta.delta.rank()?
            || self.causal_adjoint.measured_delta_rank != 1
        {
            return Err(RecurrentReturnRefusal::Adjoint);
        }
        let commutator = predecessor_action
            .multiply(&self.delta.delta)?
            .subtract(&self.delta.delta.multiply(&predecessor_action)?)?;
        if self.holonomy.commutator != commutator
            || self.holonomy.commutator_rank != commutator.rank()?
            || self.holonomy.commutator_rank == 0
        {
            return Err(RecurrentReturnRefusal::Holonomy);
        }
        if self.causal_adjoint.return_lineage
            != self
                .causal_adjoint
                .forward_lineage
                .iter()
                .copied()
                .rev()
                .collect::<Vec<_>>()
            || self.causal_adjoint.forward_lineage.len() < 3
            || self.causal_adjoint.forward_lineage.first() != Some(&self.main_start)
            || self.causal_adjoint.forward_lineage.last() != Some(&self.delta.predecessor_to)
            || self.causal_adjoint.forward_lineage[self.causal_adjoint.forward_lineage.len() - 2]
                != self.delta.from
        {
            return Err(RecurrentReturnRefusal::Lineage);
        }
        let predicted = semantic_work(
            &self.base,
            self.delta.generator,
            &self.recurrence_starts,
            (self.delta.from, self.delta.successor_to),
        )?;
        if self.semantic_work_prediction != predicted {
            return Err(RecurrentReturnRefusal::Work);
        }
        let successor = self
            .decision
            .successor_sha256
            .as_ref()
            .ok_or(RecurrentReturnRefusal::Decision)?;
        if successor != &sha256(&self.canonical_bytes_without_successor()?) {
            return Err(RecurrentReturnRefusal::Decision);
        }
        Ok(())
    }
}

fn local_delta(
    dimension: usize,
    from: NativeStateId,
    predecessor_to: NativeStateId,
    successor_to: NativeStateId,
) -> Result<(ExactRatMatrix, Vec<Rat>, Vec<Rat>), RecurrentReturnRefusal> {
    if dimension == 0
        || from.0 as usize >= dimension
        || predecessor_to.0 as usize >= dimension
        || successor_to.0 as usize >= dimension
        || predecessor_to == successor_to
    {
        return Err(RecurrentReturnRefusal::Delta);
    }
    let zero = Rat::from_integer(0.into());
    let one = Rat::from_integer(1.into());
    let mut left = vec![zero.clone(); dimension];
    let mut right = vec![zero.clone(); dimension];
    left[successor_to.0 as usize] = one.clone();
    left[predecessor_to.0 as usize] = -one.clone();
    right[from.0 as usize] = one;
    let delta = ExactRatMatrix::new(
        left.iter()
            .map(|left| right.iter().map(|right| left * right).collect())
            .collect(),
    )?;
    Ok((delta, left, right))
}

fn action_matrix(
    base: &GeneratorNativeRest,
    generator: InputId,
) -> Result<ExactRatMatrix, RecurrentReturnRefusal> {
    let dimension = base.native_population.len();
    let zero = Rat::from_integer(0.into());
    let one = Rat::from_integer(1.into());
    let mut rows = vec![vec![zero; dimension]; dimension];
    for state in &base.native_population {
        let reaches = next(base, generator, *state, None)?;
        rows[reaches.0 as usize][state.0 as usize] = one.clone();
    }
    Ok(ExactRatMatrix::new(rows)?)
}

fn next(
    base: &GeneratorNativeRest,
    generator: InputId,
    state: NativeStateId,
    delta: Option<(NativeStateId, NativeStateId)>,
) -> Result<NativeStateId, RecurrentReturnRefusal> {
    if let Some((from, to)) = delta {
        if state == from {
            return Ok(to);
        }
    }
    base.generators
        .iter()
        .find(|action| action.generator == generator)
        .and_then(|action| action.transport.iter().find(|edge| edge.from == state))
        .map(|edge| edge.to)
        .ok_or(RecurrentReturnRefusal::Carrier)
}

fn recurrence_trace(
    base: &GeneratorNativeRest,
    generator: InputId,
    start: NativeStateId,
    delta: Option<(NativeStateId, NativeStateId)>,
) -> Result<Vec<NativeStateId>, RecurrentReturnRefusal> {
    let mut trace = vec![start];
    let mut state = start;
    for _ in 0..base.native_population.len() {
        state = next(base, generator, state, delta)?;
        let repeated = trace.contains(&state);
        trace.push(state);
        if repeated {
            return Ok(trace);
        }
    }
    Err(RecurrentReturnRefusal::Recurrence)
}

fn semantic_work(
    base: &GeneratorNativeRest,
    generator: InputId,
    starts: &[NativeStateId],
    delta: (NativeStateId, NativeStateId),
) -> Result<RecurrentSemanticWork, RecurrentReturnRefusal> {
    let predecessor = starts
        .iter()
        .map(|start| recurrence_trace(base, generator, *start, None))
        .collect::<Result<Vec<_>, _>>()?;
    let successor = starts
        .iter()
        .map(|start| recurrence_trace(base, generator, *start, Some(delta)))
        .collect::<Result<Vec<_>, _>>()?;
    let predecessor_steps = predecessor
        .iter()
        .map(|trace| trace.len() - 1)
        .sum::<usize>();
    let successor_steps = successor.iter().map(|trace| trace.len() - 1).sum::<usize>();
    let comparisons = predecessor
        .iter()
        .chain(&successor)
        .chain(&predecessor)
        .map(|trace| (1..trace.len()).sum::<usize>())
        .sum::<usize>();
    // The card retains one rectangular terminal trace face. Entries after each first recurrence
    // repeat that terminal boundary, so they are apparatus padding but still exact writes.
    let entries = starts.len() * (base.native_population.len() + 1) * 3;
    Ok(RecurrentSemanticWork {
        starting_occurrences: starts.len() as u64,
        predecessor_transition_reads: predecessor_steps as u64,
        successor_transition_reads: successor_steps as u64,
        ablation_transition_reads: predecessor_steps as u64,
        recurrence_equality_comparisons: comparisons as u64,
        trace_entries_written: entries as u64,
        dependency_span: predecessor
            .iter()
            .chain(&successor)
            .map(Vec::len)
            .max()
            .unwrap_or(0) as u64,
    })
}

fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

use crate::is_sha256_digest as is_digest;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum RecurrentReturnRefusal {
    #[error("returned recurrence wire refused: {0}")]
    Wire(String),
    #[error("I1 predecessor refused: {0}")]
    Predecessor(String),
    #[error("the exterior tool return is incomplete or inconsistent")]
    Exterior,
    #[error("the emitted/exterior/return lineage is incomplete")]
    Lineage,
    #[error("the exterior residue did not found the declared commit decision")]
    Decision,
    #[error("the returned local generator delta is inconsistent")]
    Delta,
    #[error("the metric-adjoint return is inconsistent")]
    Adjoint,
    #[error("the revisit loop returned zero holonomy")]
    Holonomy,
    #[error("no nonidentical held-out recurrence changes under the successor")]
    HeldOut,
    #[error("no target-disjoint control port survives the local delta")]
    Control,
    #[error("the decoder is incomplete")]
    Decoder,
    #[error("a finite total native recurrence did not close")]
    Recurrence,
    #[error("the exact recurrent work prediction moved")]
    Work,
    #[error("the native integer carrier cannot address this recurrence")]
    Carrier,
    #[error("returned recurrence identity is incomplete or inconsistent")]
    Identity,
    #[error("exact linear return refused: {0}")]
    ExactLinear(String),
}

impl From<ExactLinearError> for RecurrentReturnRefusal {
    fn from(value: ExactLinearError) -> Self {
        Self::ExactLinear(value.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generator_native_rest::NativeGenerator;
    use crate::native_ecology::recurrent::{
        BoundaryFace, ClosureDerivation, RetainedContinuationRest,
    };
    use crate::receiver_exact_compression::{Observation, ReceiverId};
    use crate::receiver_history_compression::{NativeTransport, ReceiverFactor};

    fn predecessor() -> Vec<u8> {
        let native = GeneratorNativeRest::new(
            vec![NativeStateId(0), NativeStateId(1), NativeStateId(2)],
            (0..3)
                .map(|state| ReceiverFactor {
                    native: NativeStateId(state),
                    receiver: ReceiverId(0),
                    observation: Observation(state),
                })
                .collect(),
            vec![NativeGenerator {
                generator: InputId(0),
                transport: vec![
                    NativeTransport {
                        from: NativeStateId(0),
                        to: NativeStateId(1),
                    },
                    NativeTransport {
                        from: NativeStateId(1),
                        to: NativeStateId(2),
                    },
                    NativeTransport {
                        from: NativeStateId(2),
                        to: NativeStateId(1),
                    },
                ],
            }],
        )
        .expect("native");
        let face = |native, id, surface: &str| BoundaryDecoder {
            native: NativeStateId(native),
            face: (native != 0).then(|| BoundaryFace {
                native_id: id,
                source_surface: surface.to_owned(),
                lower: 0,
                upper: 1,
            }),
        };
        RetainedContinuationRest {
            schema: super::super::recurrent::RETAINED_REST_SCHEMA.to_owned(),
            predecessor_identity: "predecessor".to_owned(),
            continuation_identity: "continuation".to_owned(),
            native,
            decoder: vec![face(0, 0, ""), face(1, 7, " France"), face(2, 8, " is")],
            closure: ClosureDerivation {
                entering_state: NativeStateId(0),
                first_repeated_state: NativeStateId(1),
                first_at_section: 1,
                returned_at_section: 3,
                ordered_word: vec![InputId(0); 3],
                expected_trace: vec![
                    NativeStateId(0),
                    NativeStateId(1),
                    NativeStateId(2),
                    NativeStateId(1),
                ],
                crossed_nonterminal_boundaries: 2,
                derived_from_first_repeated_boundary: true,
            },
            emitted_native_ids: vec![7, 8, 7],
            emitted_text: " France is France".to_owned(),
            codec_identity: "codec".to_owned(),
            open_exterior: vec!["open".to_owned()],
        }
        .canonical_bytes()
        .expect("predecessor")
    }

    fn exterior(octets: u64) -> ExteriorToolReturn {
        ExteriorToolReturn {
            schema: "holonics.i2.exterior-tool-return.v1".to_owned(),
            receiver: "/usr/bin/tee exact byte-preserving consequence".to_owned(),
            emitted_occurrence: "emitted".to_owned(),
            consequence_occurrence: "consequence".to_owned(),
            return_occurrence: "return".to_owned(),
            emitted_sha256: format!("{:064x}", 1),
            consequence_sha256: format!("{:064x}", 1),
            echoed_sha256: format!("{:064x}", 1),
            before_octets: 0,
            after_octets: octets,
            exact_difference_octets: octets,
            process_status: 0,
        }
    }

    #[test]
    fn a_positive_return_commits_one_rank_one_edge_and_ablation_is_the_predecessor() {
        let rest = ReturnedRecurrentRest::seal(&predecessor(), "entering".to_owned(), exterior(17))
            .expect("rest");
        assert_eq!(rest.delta.from, NativeStateId(2));
        assert_eq!(rest.delta.predecessor_to, NativeStateId(1));
        assert_eq!(rest.delta.successor_to, NativeStateId(2));
        assert_eq!(rest.causal_adjoint.measured_delta_rank, 1);
        assert!(rest.holonomy.commutator_rank > 0);
        assert_eq!(
            recurrence_trace(
                &rest.base,
                InputId(0),
                NativeStateId(0),
                Some((NativeStateId(2), NativeStateId(2)))
            )
            .expect("trace"),
            vec![
                NativeStateId(0),
                NativeStateId(1),
                NativeStateId(2),
                NativeStateId(2)
            ]
        );
        let bytes = rest.canonical_bytes().expect("bytes");
        assert_eq!(ReturnedRecurrentRest::read(&bytes).expect("read"), rest);
    }

    #[test]
    fn an_empty_return_declines_without_a_successor() {
        let predecessor = predecessor();
        let declined =
            DeclinedReturn::from_exterior(exterior(0), sha256(&predecessor)).expect("declined");
        assert_eq!(declined.event.decision, ReturnDecision::Declined);
        assert!(declined.event.successor_sha256.is_none());
    }
}
