//! Exact reconstruction of opaque finite bit transducers.
//!
//! A supplied observation is lineage-relative testimony. It restricts the
//! contemporary family of compatible programs but is never promoted to an
//! observer-free fact. The production law owns distinguishing-query
//! selection, retains every compatible program, and certifies completion only
//! after exhaustive comparison over every admitted finite receiver width.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{CausalDiagram, EventId, EventSuccessor, ExactEventLaw, LogicalResourceReceipt};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BitLineageId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BitQuery {
    pub width: u8,
    pub state: u8,
    pub input: u8,
}

impl BitQuery {
    pub fn new(width: u8, state: u8, input: u8) -> Result<Self, BitCausalError> {
        let query = Self {
            width,
            state,
            input,
        };
        query.validate()?;
        Ok(query)
    }

    pub fn encoded(self) -> u32 {
        u32::from(self.state) << self.width | u32::from(self.input)
    }

    fn validate(self) -> Result<(), BitCausalError> {
        let mask = bit_mask(self.width)?;
        if self.state > mask || self.input > mask {
            return Err(BitCausalError::MalformedQuery(self));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BitResponse {
    pub next_state: u8,
    pub output: u8,
}

impl BitResponse {
    pub fn new(width: u8, next_state: u8, output: u8) -> Result<Self, BitCausalError> {
        let response = Self { next_state, output };
        response.validate(width)?;
        Ok(response)
    }

    pub fn packed(self, width: u8) -> Result<u16, BitCausalError> {
        self.validate(width)?;
        Ok(u16::from(self.next_state) | u16::from(self.output) << width)
    }

    fn validate(self, width: u8) -> Result<(), BitCausalError> {
        let mask = bit_mask(width)?;
        if self.next_state > mask || self.output > mask {
            return Err(BitCausalError::MalformedResponse {
                width,
                response: self,
            });
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BitBinaryLaw {
    Xor,
    WrappingAdd,
    WrappingSubtract,
    And,
    Or,
}

impl BitBinaryLaw {
    const ALL: [Self; 5] = [
        Self::Xor,
        Self::WrappingAdd,
        Self::WrappingSubtract,
        Self::And,
        Self::Or,
    ];

    fn apply(self, left: u8, right: u8, mask: u8) -> u8 {
        match self {
            Self::Xor => left ^ right,
            Self::WrappingAdd => left.wrapping_add(right) & mask,
            Self::WrappingSubtract => left.wrapping_sub(right) & mask,
            Self::And => left & right,
            Self::Or => left | right,
        }
    }

    pub const fn law_name(self) -> &'static str {
        match self {
            Self::Xor => "xor",
            Self::WrappingAdd => "wrapping-add",
            Self::WrappingSubtract => "wrapping-subtract",
            Self::And => "and",
            Self::Or => "or",
        }
    }

    fn is_carrying(self) -> bool {
        matches!(self, Self::WrappingAdd | Self::WrappingSubtract)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BitImmediateLaw {
    Xor,
    WrappingAdd,
}

impl BitImmediateLaw {
    const ALL: [Self; 2] = [Self::Xor, Self::WrappingAdd];

    fn apply(self, value: u8, immediate: u8, mask: u8) -> u8 {
        match self {
            Self::Xor => value ^ immediate,
            Self::WrappingAdd => value.wrapping_add(immediate) & mask,
        }
    }

    pub const fn law_name(self) -> &'static str {
        match self {
            Self::Xor => "xor-immediate",
            Self::WrappingAdd => "add-immediate",
        }
    }

    fn is_carrying(self) -> bool {
        self == Self::WrappingAdd
    }
}

/// One program in the declared two-input recurrent bit ecology.
///
/// The program is the five-event causal diagram
///
/// ```text
/// state,input --mix--> rotate-state --> immediate --\
/// input -------------------------> rotate-input ------> output-mix
/// ```
///
/// `next_state` is the immediate result. `output` combines that result with
/// the independently rotated input.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BitTransducerProgram {
    pub state_input_law: BitBinaryLaw,
    pub state_rotation: u8,
    pub immediate_law: BitImmediateLaw,
    pub immediate: u8,
    pub output_law: BitBinaryLaw,
    pub input_rotation: u8,
}

/// One exact enactment of a program at a receiver-local bit problem.
///
/// This is a reasoning receipt rather than a second evaluator: every intermediate face is the
/// actual value carried by [`BitTransducerProgram::evaluate`]. Distinct compatible programs may
/// agree on the returned response while retaining different internal traces.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct BitProgramTrace {
    pub program: BitTransducerProgram,
    pub query: BitQuery,
    pub mixed_state_input: u8,
    pub rotated_state: u8,
    pub next_state: u8,
    pub rotated_input: u8,
    pub output: u8,
}

impl BitProgramTrace {
    pub const fn response(self) -> BitResponse {
        BitResponse {
            next_state: self.next_state,
            output: self.output,
        }
    }
}

impl BitTransducerProgram {
    pub fn evaluate(self, query: BitQuery) -> Result<BitResponse, BitCausalError> {
        Ok(self.trace(query)?.response())
    }

    pub fn trace(self, query: BitQuery) -> Result<BitProgramTrace, BitCausalError> {
        query.validate()?;
        let mask = bit_mask(query.width)?;
        self.validate(8)?;
        let mixed = self.state_input_law.apply(query.state, query.input, mask);
        let turned = rotate_word(mixed, self.state_rotation, query.width)?;
        let next_state = self
            .immediate_law
            .apply(turned, self.immediate & mask, mask);
        let turned_input = rotate_word(query.input, self.input_rotation, query.width)?;
        let output = self.output_law.apply(next_state, turned_input, mask);
        BitResponse::new(query.width, next_state, output)?;
        Ok(BitProgramTrace {
            program: self,
            query,
            mixed_state_input: mixed,
            rotated_state: turned,
            next_state,
            rotated_input: turned_input,
            output,
        })
    }

    pub fn causal_diagram(self) -> Result<CausalDiagram, BitCausalError> {
        let mut diagram = CausalDiagram::default();
        let mix = diagram.add_event(self.state_input_law.law_name());
        let turn_state = diagram.add_event("rotate-state");
        let immediate = diagram.add_event(self.immediate_law.law_name());
        let turn_input = diagram.add_event("rotate-input");
        let output = diagram.add_event(self.output_law.law_name());
        diagram.precedes(mix, turn_state)?;
        diagram.precedes(turn_state, immediate)?;
        diagram.precedes(immediate, output)?;
        diagram.precedes(turn_input, output)?;
        Ok(diagram)
    }

    pub fn logical_resources(self) -> Result<LogicalResourceReceipt, BitCausalError> {
        Ok(LogicalResourceReceipt::from_diagram(
            &self.causal_diagram()?,
        )?)
    }

    pub fn instruction_resources(self) -> BitInstructionResourceReceipt {
        let carrying_operations = u64::from(self.state_input_law.is_carrying())
            + u64::from(self.immediate_law.is_carrying())
            + u64::from(self.output_law.is_carrying());
        BitInstructionResourceReceipt {
            schema: "holonic-engine.bit-instruction-resource-receipt.v1".to_owned(),
            causal_events: 5,
            rotations: 2,
            boolean_operations: 3 - carrying_operations,
            carrying_operations,
            immediate_octets: 3,
        }
    }

    fn validate(self, maximum_width: u8) -> Result<(), BitCausalError> {
        let maximum_mask = bit_mask(maximum_width)?;
        if self.state_rotation >= maximum_width
            || self.input_rotation >= maximum_width
            || self.immediate > maximum_mask
            || (self.immediate == 0 && self.immediate_law != BitImmediateLaw::Xor)
        {
            return Err(BitCausalError::MalformedProgram(self));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitInstructionResourceReceipt {
    pub schema: String,
    pub causal_events: u64,
    pub rotations: u64,
    pub boolean_operations: u64,
    pub carrying_operations: u64,
    pub immediate_octets: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum BitTestimonySource {
    ImportedLandmark(BitLineageId),
    ReturnedReceiver(BitLineageId),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitTestimony {
    pub event: EventId,
    pub source: BitTestimonySource,
    pub query: BitQuery,
    pub response: BitResponse,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitExhaustiveTestimony {
    pub event: EventId,
    pub receiver: BitLineageId,
    pub width: u8,
    /// Binary-address order over `(state,input)`.
    pub responses: Vec<BitResponse>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BitCausalHistoryEntry {
    ReceiverFounded { event: EventId, width: u8 },
    Testimony(BitTestimony),
    ExhaustiveTestimony(BitExhaustiveTestimony),
}

impl BitCausalHistoryEntry {
    fn event(&self) -> EventId {
        match self {
            Self::ReceiverFounded { event, .. } => *event,
            Self::Testimony(testimony) => testimony.event,
            Self::ExhaustiveTestimony(testimony) => testimony.event,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitSearchWork {
    pub candidate_evaluations: u64,
    pub compared_program_pairs: u64,
    pub visited_query_vertices: u64,
}

impl BitSearchWork {
    fn add_assign(&mut self, other: &Self) -> Result<(), BitCausalError> {
        self.candidate_evaluations = self
            .candidate_evaluations
            .checked_add(other.candidate_evaluations)
            .ok_or(BitCausalError::CarrierOverflow)?;
        self.compared_program_pairs = self
            .compared_program_pairs
            .checked_add(other.compared_program_pairs)
            .ok_or(BitCausalError::CarrierOverflow)?;
        self.visited_query_vertices = self
            .visited_query_vertices
            .checked_add(other.visited_query_vertices)
            .ok_or(BitCausalError::CarrierOverflow)?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitSemanticCertificate {
    pub schema: String,
    pub receiver_widths: BTreeSet<u8>,
    pub compatible_programs: u64,
    pub representative: BitTransducerProgram,
    pub exhaustively_testified_query_vertices: u64,
    pub testimony_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitCausalStanding {
    pub schema: String,
    pub maximum_width: u8,
    pub initial_width: u8,
    receiver_widths: BTreeSet<u8>,
    candidates: Vec<BitTransducerProgram>,
    history: Vec<BitCausalHistoryEntry>,
    used_events: BTreeSet<EventId>,
    next_query: Option<BitQuery>,
    certified_widths: BTreeSet<u8>,
    verification_width: Option<u8>,
}

/// One receiver-relative answer section of a read-only code problem.
///
/// Every compatible program remains present. The response is a quotient common to this section;
/// the programs retain the plural internal explanations which produced it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitReferenceResponseFiber {
    pub response: BitResponse,
    pub programs: Vec<BitTransducerProgram>,
}

/// A non-mutating view of the contemporary version fiber at one supplied problem.
///
/// A reference does not become testimony merely because the machine can inspect it. This receipt
/// is therefore absent from [`BitCausalStanding::history`], does not remove candidates, and cannot
/// certify the opaque source. The caller may later return an observed response through
/// [`BitCausalEvent`]; that later caused occurrence is conditioning.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitReferenceInspection {
    pub query: BitQuery,
    pub standing_history_events: u64,
    pub standing_candidate_population: u64,
    pub receiver_width_already_founded: bool,
    pub response_fibers: Vec<BitReferenceResponseFiber>,
}

impl BitReferenceInspection {
    pub fn forced_response(&self) -> Option<BitResponse> {
        (self.response_fibers.len() == 1).then(|| self.response_fibers[0].response)
    }

    pub fn response_population(&self) -> usize {
        self.response_fibers.len()
    }
}

impl BitCausalStanding {
    pub fn new(maximum_width: u8, initial_width: u8) -> Result<Self, BitCausalError> {
        validate_width_range(maximum_width, initial_width)?;
        let candidates = enumerate_program_ecology(maximum_width)?;
        let receiver_widths = BTreeSet::from([initial_width]);
        let (next_query, _) = select_distinguishing_query(&candidates, &receiver_widths)?;
        let verification_width =
            next_verification_width(next_query, &receiver_widths, &BTreeSet::new());
        let standing = Self {
            schema: "holonic-engine.bit-causal-standing.v1".to_owned(),
            maximum_width,
            initial_width,
            receiver_widths,
            candidates,
            history: Vec::new(),
            used_events: BTreeSet::new(),
            next_query,
            certified_widths: BTreeSet::new(),
            verification_width,
        };
        standing.validate_incremental()?;
        Ok(standing)
    }

    pub fn receiver_widths(&self) -> &BTreeSet<u8> {
        &self.receiver_widths
    }

    pub fn candidates(&self) -> &[BitTransducerProgram] {
        &self.candidates
    }

    pub fn history(&self) -> &[BitCausalHistoryEntry] {
        &self.history
    }

    pub fn next_query(&self) -> Option<BitQuery> {
        self.next_query
    }

    pub fn verification_width(&self) -> Option<u8> {
        self.verification_width
    }

    pub fn certified_widths(&self) -> &BTreeSet<u8> {
        &self.certified_widths
    }

    /// Inspect a mathematical/code problem through the contemporary compatible family without
    /// changing that family. References may use any width admitted by the declared ecology; a
    /// width need not already have been founded as an observed receiver.
    pub fn inspect_reference(
        &self,
        query: BitQuery,
    ) -> Result<BitReferenceInspection, BitCausalError> {
        query.validate()?;
        if query.width > self.maximum_width {
            return Err(BitCausalError::ReferenceExceedsDeclaredWidth {
                maximum: self.maximum_width,
                received: query.width,
            });
        }
        let mut sections = BTreeMap::<BitResponse, Vec<BitTransducerProgram>>::new();
        for program in &self.candidates {
            sections
                .entry(program.evaluate(query)?)
                .or_default()
                .push(*program);
        }
        let response_fibers = sections
            .into_iter()
            .map(|(response, programs)| BitReferenceResponseFiber { response, programs })
            .collect::<Vec<_>>();
        let standing_history_events =
            u64::try_from(self.history.len()).map_err(|_| BitCausalError::CarrierOverflow)?;
        let standing_candidate_population =
            u64::try_from(self.candidates.len()).map_err(|_| BitCausalError::CarrierOverflow)?;
        Ok(BitReferenceInspection {
            query,
            standing_history_events,
            standing_candidate_population,
            receiver_width_already_founded: self.receiver_widths.contains(&query.width),
            response_fibers,
        })
    }

    pub fn is_complete(&self) -> bool {
        self.next_query.is_none()
            && self.verification_width.is_none()
            && self.certified_widths == self.receiver_widths
    }

    pub fn certificate(&self) -> Option<BitSemanticCertificate> {
        self.is_complete().then(|| BitSemanticCertificate {
            schema: "holonic-engine.bit-semantic-certificate.v1".to_owned(),
            receiver_widths: self.receiver_widths.clone(),
            compatible_programs: u64::try_from(self.candidates.len())
                .expect("usize always fits the exact u64 carrier"),
            representative: self.candidates[0],
            exhaustively_testified_query_vertices: self
                .receiver_widths
                .iter()
                .map(|width| 1_u64 << (2 * width))
                .sum(),
            testimony_events: self
                .history
                .iter()
                .filter_map(|entry| match entry {
                    BitCausalHistoryEntry::Testimony(testimony) => Some(testimony.event),
                    BitCausalHistoryEntry::ExhaustiveTestimony(testimony) => Some(testimony.event),
                    BitCausalHistoryEntry::ReceiverFounded { .. } => None,
                })
                .collect(),
        })
    }

    pub fn testimonies(&self) -> impl Iterator<Item = &BitTestimony> {
        self.history.iter().filter_map(|entry| match entry {
            BitCausalHistoryEntry::Testimony(testimony) => Some(testimony),
            BitCausalHistoryEntry::ReceiverFounded { .. }
            | BitCausalHistoryEntry::ExhaustiveTestimony(_) => None,
        })
    }

    pub fn exhaustive_testimonies(&self) -> impl Iterator<Item = &BitExhaustiveTestimony> {
        self.history.iter().filter_map(|entry| match entry {
            BitCausalHistoryEntry::ExhaustiveTestimony(testimony) => Some(testimony),
            BitCausalHistoryEntry::ReceiverFounded { .. } | BitCausalHistoryEntry::Testimony(_) => {
                None
            }
        })
    }

    pub fn validate(&self) -> Result<(), BitCausalError> {
        self.validate_incremental()?;
        self.validate_complete_replay()
    }

    /// Validate the carried recurrence without reconstructing its entire
    /// ancestry.
    ///
    /// The transition law only ever obtains a successor by filtering the
    /// predecessor's complete family. Rebuilding the original ecology after
    /// every occurrence would discard that lawful recurrence and dominate the
    /// search cost. `validate` remains the independent full replay authority.
    fn validate_incremental(&self) -> Result<(), BitCausalError> {
        if self.schema != "holonic-engine.bit-causal-standing.v1" {
            return Err(BitCausalError::MalformedStanding);
        }
        validate_width_range(self.maximum_width, self.initial_width)?;
        if !self.receiver_widths.contains(&self.initial_width)
            || self
                .receiver_widths
                .iter()
                .any(|width| *width == 0 || *width > self.maximum_width)
        {
            return Err(BitCausalError::MalformedStanding);
        }
        let history_events = self
            .history
            .iter()
            .map(BitCausalHistoryEntry::event)
            .collect::<BTreeSet<_>>();
        if history_events.len() != self.history.len() || history_events != self.used_events {
            return Err(BitCausalError::MalformedStanding);
        }
        if self.candidates.is_empty()
            || self.candidates.windows(2).any(|pair| pair[0] >= pair[1])
            || self
                .candidates
                .iter()
                .any(|program| program.validate(self.maximum_width).is_err())
            || !self.certified_widths.is_subset(&self.receiver_widths)
            || self
                .next_query
                .is_some_and(|query| !self.receiver_widths.contains(&query.width))
            || self.verification_width
                != next_verification_width(
                    self.next_query,
                    &self.receiver_widths,
                    &self.certified_widths,
                )
        {
            return Err(BitCausalError::MalformedStanding);
        }
        let mut contemporary_widths = BTreeSet::from([self.initial_width]);
        for entry in &self.history {
            match entry {
                BitCausalHistoryEntry::ReceiverFounded { width, .. } => {
                    if *width
                        <= *contemporary_widths
                            .last()
                            .ok_or(BitCausalError::MalformedStanding)?
                        || *width > self.maximum_width
                    {
                        return Err(BitCausalError::MalformedStanding);
                    }
                    contemporary_widths.insert(*width);
                }
                BitCausalHistoryEntry::Testimony(testimony) => {
                    validate_testimony(&contemporary_widths, testimony.query, testimony.response)?;
                }
                BitCausalHistoryEntry::ExhaustiveTestimony(testimony) => {
                    if !contemporary_widths.contains(&testimony.width) {
                        return Err(BitCausalError::MalformedStanding);
                    }
                    validate_exhaustive_testimony(testimony)?;
                }
            }
        }
        if contemporary_widths != self.receiver_widths {
            return Err(BitCausalError::MalformedStanding);
        }
        for candidate in &self.candidates {
            for entry in &self.history {
                match entry {
                    BitCausalHistoryEntry::Testimony(testimony) => {
                        if candidate.evaluate(testimony.query)? != testimony.response {
                            return Err(BitCausalError::MalformedStanding);
                        }
                    }
                    BitCausalHistoryEntry::ExhaustiveTestimony(testimony) => {
                        if !candidate_matches_exhaustive(
                            *candidate,
                            testimony.width,
                            &testimony.responses,
                        )?
                        .0
                        {
                            return Err(BitCausalError::MalformedStanding);
                        }
                    }
                    BitCausalHistoryEntry::ReceiverFounded { .. } => {}
                }
            }
        }
        Ok(())
    }

    fn validate_complete_replay(&self) -> Result<(), BitCausalError> {
        let mut receiver_widths = BTreeSet::from([self.initial_width]);
        let mut certified_widths = BTreeSet::new();
        let mut candidates = enumerate_program_ecology(self.maximum_width)?;
        let (mut next_query, _) = select_distinguishing_query(&candidates, &receiver_widths)?;
        let mut verification_width =
            next_verification_width(next_query, &receiver_widths, &certified_widths);
        for entry in &self.history {
            match entry {
                BitCausalHistoryEntry::ReceiverFounded { width, .. } => {
                    if *width
                        <= *receiver_widths
                            .last()
                            .ok_or(BitCausalError::MalformedStanding)?
                        || *width > self.maximum_width
                    {
                        return Err(BitCausalError::MalformedStanding);
                    }
                    receiver_widths.insert(*width);
                }
                BitCausalHistoryEntry::Testimony(testimony) => {
                    testimony.query.validate()?;
                    testimony.response.validate(testimony.query.width)?;
                    if !receiver_widths.contains(&testimony.query.width) {
                        return Err(BitCausalError::MalformedStanding);
                    }
                    if matches!(testimony.source, BitTestimonySource::ReturnedReceiver(_))
                        && next_query != Some(testimony.query)
                    {
                        return Err(BitCausalError::MalformedStanding);
                    }
                    candidates =
                        filter_candidates(&candidates, testimony.query, testimony.response)?.0;
                    if candidates.is_empty() {
                        return Err(BitCausalError::MalformedStanding);
                    }
                }
                BitCausalHistoryEntry::ExhaustiveTestimony(testimony) => {
                    if verification_width != Some(testimony.width) {
                        return Err(BitCausalError::MalformedStanding);
                    }
                    validate_exhaustive_testimony(testimony)?;
                    candidates = filter_candidates_exhaustively(
                        &candidates,
                        testimony.width,
                        &testimony.responses,
                    )?
                    .0;
                    if candidates.is_empty() {
                        return Err(BitCausalError::MalformedStanding);
                    }
                    certified_widths.insert(testimony.width);
                }
            }
            next_query = select_distinguishing_query(&candidates, &receiver_widths)?.0;
            verification_width =
                next_verification_width(next_query, &receiver_widths, &certified_widths);
        }
        if receiver_widths != self.receiver_widths
            || candidates != self.candidates
            || next_query != self.next_query
            || certified_widths != self.certified_widths
            || verification_width != self.verification_width
        {
            return Err(BitCausalError::MalformedStanding);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum BitCausalEvent {
    InheritLandmark {
        event: EventId,
        lineage: BitLineageId,
        query: BitQuery,
        response: BitResponse,
    },
    FoundReceiver {
        event: EventId,
        width: u8,
    },
    ReturnObservation {
        event: EventId,
        receiver: BitLineageId,
        query: BitQuery,
        response: BitResponse,
    },
    ReturnExhaustiveReceiver {
        event: EventId,
        receiver: BitLineageId,
        width: u8,
        responses: Vec<BitResponse>,
    },
}

impl BitCausalEvent {
    fn event(&self) -> EventId {
        match self {
            Self::InheritLandmark { event, .. }
            | Self::FoundReceiver { event, .. }
            | Self::ReturnObservation { event, .. }
            | Self::ReturnExhaustiveReceiver { event, .. } => *event,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitCausalRadiation {
    pub schema: String,
    pub event: EventId,
    pub received_testimony: Option<BitTestimony>,
    pub received_exhaustive_testimony: Option<BitExhaustiveTestimony>,
    pub founded_receiver: Option<u8>,
    pub candidates_before: u64,
    pub candidates_after: u64,
    pub eliminated_candidates: u64,
    pub next_query: Option<BitQuery>,
    pub certificate: Option<BitSemanticCertificate>,
    pub search_work: BitSearchWork,
}

#[derive(Clone, Debug)]
pub struct BitCausalLaw {
    maximum_width: u8,
    initial_width: u8,
}

impl BitCausalLaw {
    pub fn new(maximum_width: u8, initial_width: u8) -> Result<Self, BitCausalError> {
        validate_width_range(maximum_width, initial_width)?;
        Ok(Self {
            maximum_width,
            initial_width,
        })
    }
}

impl ExactEventLaw for BitCausalLaw {
    type Standing = BitCausalStanding;
    type Event = BitCausalEvent;
    type Radiation = BitCausalRadiation;
    type Error = BitCausalError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate_incremental()?;
        if standing_before.maximum_width != self.maximum_width
            || standing_before.initial_width != self.initial_width
        {
            return Err(BitCausalError::LawStandingMismatch);
        }
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(BitCausalError::RepeatedEvent(event_id));
        }

        let mut standing_after = standing_before.clone();
        let candidates_before = u64::try_from(standing_before.candidates.len())
            .map_err(|_| BitCausalError::CarrierOverflow)?;
        let mut received_testimony = None;
        let mut received_exhaustive_testimony = None;
        let mut founded_receiver = None;
        let mut search_work = BitSearchWork::default();
        match event {
            BitCausalEvent::InheritLandmark {
                event,
                lineage,
                query,
                response,
            } => {
                validate_testimony(&standing_after.receiver_widths, *query, *response)?;
                let testimony = BitTestimony {
                    event: *event,
                    source: BitTestimonySource::ImportedLandmark(*lineage),
                    query: *query,
                    response: *response,
                };
                let (candidates, work) =
                    filter_candidates(&standing_after.candidates, *query, *response)?;
                if candidates.is_empty() {
                    return Err(BitCausalError::TestimonyObstructsEcology(*event));
                }
                standing_after.candidates = candidates;
                standing_after
                    .history
                    .push(BitCausalHistoryEntry::Testimony(testimony.clone()));
                received_testimony = Some(testimony);
                search_work.add_assign(&work)?;
            }
            BitCausalEvent::FoundReceiver { event, width } => {
                let largest = *standing_after
                    .receiver_widths
                    .last()
                    .ok_or(BitCausalError::MalformedStanding)?;
                if *width <= largest || *width > self.maximum_width {
                    return Err(BitCausalError::ReceiverDoesNotExtend {
                        present: largest,
                        requested: *width,
                    });
                }
                standing_after.receiver_widths.insert(*width);
                standing_after
                    .history
                    .push(BitCausalHistoryEntry::ReceiverFounded {
                        event: *event,
                        width: *width,
                    });
                founded_receiver = Some(*width);
            }
            BitCausalEvent::ReturnObservation {
                event,
                receiver,
                query,
                response,
            } => {
                validate_testimony(&standing_after.receiver_widths, *query, *response)?;
                if standing_after.next_query != Some(*query) {
                    return Err(BitCausalError::UnexpectedReturnedQuery {
                        expected: standing_after.next_query,
                        received: *query,
                    });
                }
                let testimony = BitTestimony {
                    event: *event,
                    source: BitTestimonySource::ReturnedReceiver(*receiver),
                    query: *query,
                    response: *response,
                };
                let (candidates, work) =
                    filter_candidates(&standing_after.candidates, *query, *response)?;
                if candidates.is_empty() {
                    return Err(BitCausalError::TestimonyObstructsEcology(*event));
                }
                standing_after.candidates = candidates;
                standing_after
                    .history
                    .push(BitCausalHistoryEntry::Testimony(testimony.clone()));
                received_testimony = Some(testimony);
                search_work.add_assign(&work)?;
            }
            BitCausalEvent::ReturnExhaustiveReceiver {
                event,
                receiver,
                width,
                responses,
            } => {
                if standing_after.verification_width != Some(*width) {
                    return Err(BitCausalError::UnexpectedVerificationWidth {
                        expected: standing_after.verification_width,
                        received: *width,
                    });
                }
                let testimony = BitExhaustiveTestimony {
                    event: *event,
                    receiver: *receiver,
                    width: *width,
                    responses: responses.clone(),
                };
                validate_exhaustive_testimony(&testimony)?;
                let (candidates, work) =
                    filter_candidates_exhaustively(&standing_after.candidates, *width, responses)?;
                if candidates.is_empty() {
                    return Err(BitCausalError::TestimonyObstructsEcology(*event));
                }
                standing_after.candidates = candidates;
                standing_after.certified_widths.insert(*width);
                standing_after
                    .history
                    .push(BitCausalHistoryEntry::ExhaustiveTestimony(
                        testimony.clone(),
                    ));
                received_exhaustive_testimony = Some(testimony);
                search_work.add_assign(&work)?;
            }
        }
        standing_after.used_events.insert(event_id);
        let (next_query, query_work) = select_distinguishing_query(
            &standing_after.candidates,
            &standing_after.receiver_widths,
        )?;
        search_work.add_assign(&query_work)?;
        standing_after.next_query = next_query;
        standing_after.verification_width = next_verification_width(
            next_query,
            &standing_after.receiver_widths,
            &standing_after.certified_widths,
        );
        standing_after.validate_incremental()?;

        let candidates_after = u64::try_from(standing_after.candidates.len())
            .map_err(|_| BitCausalError::CarrierOverflow)?;
        let radiation = BitCausalRadiation {
            schema: "holonic-engine.bit-causal-radiation.v1".to_owned(),
            event: event_id,
            received_testimony,
            received_exhaustive_testimony,
            founded_receiver,
            candidates_before,
            candidates_after,
            eliminated_candidates: candidates_before
                .checked_sub(candidates_after)
                .ok_or(BitCausalError::CarrierOverflow)?,
            next_query: standing_after.next_query,
            certificate: standing_after.certificate(),
            search_work,
        };
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum BitCausalError {
    #[error("bit receiver widths must satisfy 1 <= initial <= maximum <= 8")]
    InvalidWidthRange,
    #[error("bit query {0:?} is malformed")]
    MalformedQuery(BitQuery),
    #[error("bit response {response:?} is malformed at width {width}")]
    MalformedResponse { width: u8, response: BitResponse },
    #[error("bit transducer program {0:?} is malformed")]
    MalformedProgram(BitTransducerProgram),
    #[error("bit-causal law and standing disagree")]
    LawStandingMismatch,
    #[error("reference receiver width {received} exceeds the declared maximum width {maximum}")]
    ReferenceExceedsDeclaredWidth { maximum: u8, received: u8 },
    #[error("bit-causal occurrence {0:?} was already used")]
    RepeatedEvent(EventId),
    #[error("receiver width {requested} does not extend present width {present}")]
    ReceiverDoesNotExtend { present: u8, requested: u8 },
    #[error("testimony references receiver width {0}, which is not active")]
    MissingReceiverWidth(u8),
    #[error("returned query {received:?} does not match production query {expected:?}")]
    UnexpectedReturnedQuery {
        expected: Option<BitQuery>,
        received: BitQuery,
    },
    #[error(
        "returned exhaustive width {received} does not match production verification width {expected:?}"
    )]
    UnexpectedVerificationWidth { expected: Option<u8>, received: u8 },
    #[error(
        "exhaustive receiver width {width} supplied {received} responses instead of {expected}"
    )]
    MalformedExhaustiveTestimony {
        width: u8,
        expected: u64,
        received: u64,
    },
    #[error("testimony occurrence {0:?} obstructs every admitted program")]
    TestimonyObstructsEcology(EventId),
    #[error("the bit-causal standing is malformed")]
    MalformedStanding,
    #[error("the finite bit ecology exceeded an exact carrier")]
    CarrierOverflow,
    #[error("native bit-machine realization is unavailable on this platform")]
    NativeRealizationUnavailable,
    #[error("native bit-machine memory allocation failed")]
    NativeAllocationFailed,
    #[error("native bit-machine memory protection failed")]
    NativeProtectionFailed,
    #[error(transparent)]
    Diagram(#[from] crate::DiagramError),
}

fn validate_width_range(maximum_width: u8, initial_width: u8) -> Result<(), BitCausalError> {
    if maximum_width == 0
        || maximum_width > 8
        || initial_width == 0
        || initial_width > maximum_width
    {
        return Err(BitCausalError::InvalidWidthRange);
    }
    Ok(())
}

fn bit_mask(width: u8) -> Result<u8, BitCausalError> {
    if width == 0 || width > 8 {
        return Err(BitCausalError::InvalidWidthRange);
    }
    Ok(if width == 8 {
        u8::MAX
    } else {
        (1_u8 << width) - 1
    })
}

fn rotate_word(value: u8, rotation: u8, width: u8) -> Result<u8, BitCausalError> {
    let mask = bit_mask(width)?;
    let rotation = rotation % width;
    let value = u16::from(value & mask);
    if rotation == 0 {
        return Ok(value as u8);
    }
    let left = value << rotation;
    let right = value >> (width - rotation);
    Ok(((left | right) & u16::from(mask)) as u8)
}

fn enumerate_program_ecology(
    maximum_width: u8,
) -> Result<Vec<BitTransducerProgram>, BitCausalError> {
    let mask = bit_mask(maximum_width)?;
    let mut programs = Vec::new();
    for state_input_law in BitBinaryLaw::ALL {
        for state_rotation in 0..maximum_width {
            for immediate_law in BitImmediateLaw::ALL {
                for immediate in 0..=mask {
                    if immediate == 0 && immediate_law != BitImmediateLaw::Xor {
                        continue;
                    }
                    for output_law in BitBinaryLaw::ALL {
                        for input_rotation in 0..maximum_width {
                            programs.push(BitTransducerProgram {
                                state_input_law,
                                state_rotation,
                                immediate_law,
                                immediate,
                                output_law,
                                input_rotation,
                            });
                        }
                    }
                }
            }
        }
    }
    Ok(programs)
}

fn validate_testimony(
    receiver_widths: &BTreeSet<u8>,
    query: BitQuery,
    response: BitResponse,
) -> Result<(), BitCausalError> {
    query.validate()?;
    response.validate(query.width)?;
    if !receiver_widths.contains(&query.width) {
        return Err(BitCausalError::MissingReceiverWidth(query.width));
    }
    Ok(())
}

fn filter_candidates(
    candidates: &[BitTransducerProgram],
    query: BitQuery,
    response: BitResponse,
) -> Result<(Vec<BitTransducerProgram>, BitSearchWork), BitCausalError> {
    let mut retained = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        if candidate.evaluate(query)? == response {
            retained.push(*candidate);
        }
    }
    Ok((
        retained,
        BitSearchWork {
            candidate_evaluations: u64::try_from(candidates.len())
                .map_err(|_| BitCausalError::CarrierOverflow)?,
            compared_program_pairs: 0,
            visited_query_vertices: 0,
        },
    ))
}

fn validate_exhaustive_testimony(testimony: &BitExhaustiveTestimony) -> Result<(), BitCausalError> {
    validate_exhaustive_responses(testimony.width, &testimony.responses)
}

fn validate_exhaustive_responses(
    width: u8,
    responses: &[BitResponse],
) -> Result<(), BitCausalError> {
    bit_mask(width)?;
    let expected = 1_u64 << (2 * width);
    let received = u64::try_from(responses.len()).map_err(|_| BitCausalError::CarrierOverflow)?;
    if received != expected {
        return Err(BitCausalError::MalformedExhaustiveTestimony {
            width,
            expected,
            received,
        });
    }
    for response in responses {
        response.validate(width)?;
    }
    Ok(())
}

fn filter_candidates_exhaustively(
    candidates: &[BitTransducerProgram],
    width: u8,
    responses: &[BitResponse],
) -> Result<(Vec<BitTransducerProgram>, BitSearchWork), BitCausalError> {
    validate_exhaustive_responses(width, responses)?;
    let mut retained = Vec::with_capacity(candidates.len());
    let mut candidate_evaluations = 0_u64;
    for candidate in candidates {
        let (compatible, evaluations) = candidate_matches_exhaustive(*candidate, width, responses)?;
        candidate_evaluations = candidate_evaluations
            .checked_add(evaluations)
            .ok_or(BitCausalError::CarrierOverflow)?;
        if compatible {
            retained.push(*candidate);
        }
    }
    Ok((
        retained,
        BitSearchWork {
            candidate_evaluations,
            compared_program_pairs: 0,
            visited_query_vertices: u64::try_from(responses.len())
                .map_err(|_| BitCausalError::CarrierOverflow)?,
        },
    ))
}

fn candidate_matches_exhaustive(
    candidate: BitTransducerProgram,
    width: u8,
    responses: &[BitResponse],
) -> Result<(bool, u64), BitCausalError> {
    let mask = u32::from(bit_mask(width)?);
    let mut evaluations = 0_u64;
    for (encoded, expected) in responses.iter().enumerate() {
        let encoded = u32::try_from(encoded).map_err(|_| BitCausalError::CarrierOverflow)?;
        let query = BitQuery::new(
            width,
            ((encoded >> width) & mask) as u8,
            (encoded & mask) as u8,
        )?;
        evaluations = evaluations
            .checked_add(1)
            .ok_or(BitCausalError::CarrierOverflow)?;
        if candidate.evaluate(query)? != *expected {
            return Ok((false, evaluations));
        }
    }
    Ok((true, evaluations))
}

fn next_verification_width(
    next_query: Option<BitQuery>,
    receiver_widths: &BTreeSet<u8>,
    certified_widths: &BTreeSet<u8>,
) -> Option<u8> {
    next_query
        .is_none()
        .then(|| receiver_widths.difference(certified_widths).next().copied())
        .flatten()
}

fn query_from_gray(width: u8, ordinal: u32) -> Result<BitQuery, BitCausalError> {
    let gray = ordinal ^ (ordinal >> 1);
    let mask = u32::from(bit_mask(width)?);
    BitQuery::new(width, ((gray >> width) & mask) as u8, (gray & mask) as u8)
}

fn select_distinguishing_query(
    candidates: &[BitTransducerProgram],
    receiver_widths: &BTreeSet<u8>,
) -> Result<(Option<BitQuery>, BitSearchWork), BitCausalError> {
    let reference = *candidates
        .first()
        .ok_or(BitCausalError::MalformedStanding)?;
    let mut work = BitSearchWork::default();
    for candidate in candidates.iter().rev() {
        if *candidate == reference {
            continue;
        }
        work.compared_program_pairs = work
            .compared_program_pairs
            .checked_add(1)
            .ok_or(BitCausalError::CarrierOverflow)?;
        for width in receiver_widths.iter().rev() {
            let vertices = 1_u32 << (2 * width);
            for ordinal in 0..vertices {
                let query = query_from_gray(*width, ordinal)?;
                work.visited_query_vertices = work
                    .visited_query_vertices
                    .checked_add(1)
                    .ok_or(BitCausalError::CarrierOverflow)?;
                let left = reference.evaluate(query)?;
                let right = candidate.evaluate(query)?;
                work.candidate_evaluations = work
                    .candidate_evaluations
                    .checked_add(2)
                    .ok_or(BitCausalError::CarrierOverflow)?;
                if left != right {
                    return Ok((Some(query), work));
                }
            }
        }
    }
    Ok((None, work))
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BitCubicalGeometryReceipt {
    pub schema: String,
    pub width: u8,
    pub input_dimensions: u8,
    pub output_dimensions: u8,
    pub vertex_count: u64,
    /// Each row is one input direction; each column is one output bit.
    /// Counts are over directed cube edges, so both orientations are retained.
    pub directed_edge_flip_counts: Vec<Vec<u64>>,
    /// Algebraic-normal-form degree of every next-state/output bit.
    pub algebraic_degrees: Vec<u8>,
}

pub fn bit_cubical_geometry(
    program: BitTransducerProgram,
    width: u8,
) -> Result<BitCubicalGeometryReceipt, BitCausalError> {
    let input_dimensions = width
        .checked_mul(2)
        .ok_or(BitCausalError::CarrierOverflow)?;
    let output_dimensions = input_dimensions;
    let vertex_count = 1_usize << input_dimensions;
    let mut values = Vec::with_capacity(vertex_count);
    for encoded in 0..vertex_count {
        let mask = usize::from(bit_mask(width)?);
        let query = BitQuery::new(
            width,
            ((encoded >> width) & mask) as u8,
            (encoded & mask) as u8,
        )?;
        values.push(program.evaluate(query)?.packed(width)?);
    }

    let mut directed_edge_flip_counts =
        vec![vec![0_u64; usize::from(output_dimensions)]; usize::from(input_dimensions)];
    for (encoded, value) in values.iter().copied().enumerate() {
        for input_axis in 0..usize::from(input_dimensions) {
            let difference = value ^ values[encoded ^ (1_usize << input_axis)];
            for (output_axis, count) in directed_edge_flip_counts[input_axis].iter_mut().enumerate()
            {
                if difference & (1_u16 << output_axis) != 0 {
                    *count += 1;
                }
            }
        }
    }

    let mut algebraic_degrees = Vec::with_capacity(usize::from(output_dimensions));
    for output_axis in 0..usize::from(output_dimensions) {
        let mut coefficients = values
            .iter()
            .map(|value| u8::from(value & (1_u16 << output_axis) != 0))
            .collect::<Vec<_>>();
        for input_axis in 0..usize::from(input_dimensions) {
            for support in 0..vertex_count {
                if support & (1_usize << input_axis) != 0 {
                    coefficients[support] ^= coefficients[support ^ (1_usize << input_axis)];
                }
            }
        }
        let degree = coefficients
            .iter()
            .enumerate()
            .filter_map(|(support, coefficient)| {
                (*coefficient != 0).then_some(support.count_ones() as u8)
            })
            .max()
            .unwrap_or(0);
        algebraic_degrees.push(degree);
    }

    Ok(BitCubicalGeometryReceipt {
        schema: "holonic-engine.bit-cubical-geometry-receipt.v1".to_owned(),
        width,
        input_dimensions,
        output_dimensions,
        vertex_count: u64::try_from(vertex_count).map_err(|_| BitCausalError::CarrierOverflow)?,
        directed_edge_flip_counts,
        algebraic_degrees,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct X86BitInstruction {
    pub offset: u64,
    pub encoded_octets: u64,
    pub law: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct X86BitProgramImage {
    pub schema: String,
    pub abi: String,
    pub source: BitTransducerProgram,
    pub code: Vec<u8>,
    pub instructions: Vec<X86BitInstruction>,
}

impl X86BitProgramImage {
    pub fn encoded_octets(&self) -> u64 {
        u64::try_from(self.code.len()).expect("usize always fits the exact u64 carrier")
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub fn compile_x86_64_bit_program(
    program: BitTransducerProgram,
) -> Result<X86BitProgramImage, BitCausalError> {
    program.validate(8)?;
    let mut code = Vec::new();
    let mut instructions = Vec::new();
    let mut emit = |bytes: &[u8], law: &str| -> Result<(), BitCausalError> {
        let offset = u64::try_from(code.len()).map_err(|_| BitCausalError::CarrierOverflow)?;
        code.extend_from_slice(bytes);
        instructions.push(X86BitInstruction {
            offset,
            encoded_octets: u64::try_from(bytes.len())
                .map_err(|_| BitCausalError::CarrierOverflow)?,
            law: law.to_owned(),
        });
        Ok(())
    };

    emit(&[0x89, 0xf8], "move-packed-input-to-state")?;
    emit(&[0x25, 0xff, 0x00, 0x00, 0x00], "restrict-state")?;
    emit(&[0x89, 0xf9], "move-packed-input-to-input")?;
    emit(&[0xc1, 0xe9, 0x08], "shift-input-octet")?;
    emit(&[0x81, 0xe1, 0xff, 0x00, 0x00, 0x00], "restrict-input")?;
    emit(
        match program.state_input_law {
            BitBinaryLaw::Xor => &[0x31, 0xc8],
            BitBinaryLaw::WrappingAdd => &[0x01, 0xc8],
            BitBinaryLaw::WrappingSubtract => &[0x29, 0xc8],
            BitBinaryLaw::And => &[0x21, 0xc8],
            BitBinaryLaw::Or => &[0x09, 0xc8],
        },
        program.state_input_law.law_name(),
    )?;
    emit(&[0x25, 0xff, 0x00, 0x00, 0x00], "restrict-mixed-state")?;
    emit(&[0xc0, 0xc0, program.state_rotation], "rotate-state")?;
    let immediate_bytes = match program.immediate_law {
        BitImmediateLaw::Xor => [0x34, program.immediate],
        BitImmediateLaw::WrappingAdd => [0x04, program.immediate],
    };
    emit(&immediate_bytes, program.immediate_law.law_name())?;
    emit(&[0x89, 0xc2], "retain-next-state")?;
    emit(&[0xc0, 0xc1, program.input_rotation], "rotate-input")?;
    emit(
        match program.output_law {
            BitBinaryLaw::Xor => &[0x30, 0xc8],
            BitBinaryLaw::WrappingAdd => &[0x00, 0xc8],
            BitBinaryLaw::WrappingSubtract => &[0x28, 0xc8],
            BitBinaryLaw::And => &[0x20, 0xc8],
            BitBinaryLaw::Or => &[0x08, 0xc8],
        },
        program.output_law.law_name(),
    )?;
    emit(&[0x25, 0xff, 0x00, 0x00, 0x00], "restrict-output")?;
    emit(&[0xc1, 0xe0, 0x08], "place-output-octet")?;
    emit(&[0x81, 0xe2, 0xff, 0x00, 0x00, 0x00], "restrict-next-state")?;
    emit(&[0x09, 0xd0], "pack-response")?;
    emit(&[0xc3], "return")?;

    Ok(X86BitProgramImage {
        schema: "holonic-engine.x86-bit-program-image.v1".to_owned(),
        abi: "x86_64-system-v-u16-to-u16".to_owned(),
        source: program,
        code,
        instructions,
    })
}

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub fn compile_x86_64_bit_program(
    _program: BitTransducerProgram,
) -> Result<X86BitProgramImage, BitCausalError> {
    Err(BitCausalError::NativeRealizationUnavailable)
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod native_x86 {
    use std::ffi::{c_int, c_void};
    use std::ptr;

    use super::{BitCausalError, BitQuery, BitResponse, X86BitProgramImage};

    const PROT_READ: c_int = 0x1;
    const PROT_WRITE: c_int = 0x2;
    const PROT_EXEC: c_int = 0x4;
    const MAP_PRIVATE: c_int = 0x02;
    const MAP_ANONYMOUS: c_int = 0x20;

    unsafe extern "C" {
        fn mmap(
            address: *mut c_void,
            length: usize,
            protection: c_int,
            flags: c_int,
            descriptor: c_int,
            offset: isize,
        ) -> *mut c_void;
        fn mprotect(address: *mut c_void, length: usize, protection: c_int) -> c_int;
        fn munmap(address: *mut c_void, length: usize) -> c_int;
    }

    pub struct ExecutableX86BitProgram {
        allocation: *mut c_void,
        length: usize,
    }

    impl ExecutableX86BitProgram {
        pub fn new(image: &X86BitProgramImage) -> Result<Self, BitCausalError> {
            if image.code.is_empty() {
                return Err(BitCausalError::NativeAllocationFailed);
            }
            // SAFETY: The requested anonymous mapping is checked against the
            // platform failure sentinel before any write. The mapping is
            // private to this object and is released in `Drop`.
            let allocation = unsafe {
                mmap(
                    ptr::null_mut(),
                    image.code.len(),
                    PROT_READ | PROT_WRITE,
                    MAP_PRIVATE | MAP_ANONYMOUS,
                    -1,
                    0,
                )
            };
            if allocation as isize == -1 {
                return Err(BitCausalError::NativeAllocationFailed);
            }
            // SAFETY: `allocation` names at least `image.code.len()` writable
            // bytes and the source slice is valid and non-overlapping.
            unsafe {
                ptr::copy_nonoverlapping(
                    image.code.as_ptr(),
                    allocation.cast::<u8>(),
                    image.code.len(),
                );
            }
            // SAFETY: The same live mapping is changed from writable to
            // executable/readable before it can be invoked.
            if unsafe { mprotect(allocation, image.code.len(), PROT_READ | PROT_EXEC) } != 0 {
                // SAFETY: The mapping is still live and owned here.
                unsafe {
                    munmap(allocation, image.code.len());
                }
                return Err(BitCausalError::NativeProtectionFailed);
            }
            Ok(Self {
                allocation,
                length: image.code.len(),
            })
        }

        pub fn execute(&self, query: BitQuery) -> Result<BitResponse, BitCausalError> {
            if query.width != 8 {
                return Err(BitCausalError::NativeRealizationUnavailable);
            }
            let packed = u16::from(query.state) | u16::from(query.input) << 8;
            // SAFETY: The allocation contains code emitted by the closed
            // compiler above for exactly this System V signature and remains
            // executable for the lifetime of `self`.
            let function: unsafe extern "C" fn(u16) -> u16 =
                unsafe { std::mem::transmute(self.allocation) };
            // SAFETY: The emitted function preserves the ABI and accesses no
            // memory beyond architectural registers.
            let received = unsafe { function(packed) };
            BitResponse::new(8, received as u8, (received >> 8) as u8)
        }
    }

    impl Drop for ExecutableX86BitProgram {
        fn drop(&mut self) {
            // SAFETY: This object uniquely owns the still-live mapping.
            unsafe {
                munmap(self.allocation, self.length);
            }
        }
    }
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
pub use native_x86::ExecutableX86BitProgram;

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
pub struct ExecutableX86BitProgram;

#[cfg(not(all(target_os = "linux", target_arch = "x86_64")))]
impl ExecutableX86BitProgram {
    pub fn new(_image: &X86BitProgramImage) -> Result<Self, BitCausalError> {
        Err(BitCausalError::NativeRealizationUnavailable)
    }

    pub fn execute(&self, _query: BitQuery) -> Result<BitResponse, BitCausalError> {
        Err(BitCausalError::NativeRealizationUnavailable)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CausalWorld;

    fn target_program(maximum_width: u8) -> BitTransducerProgram {
        BitTransducerProgram {
            state_input_law: BitBinaryLaw::WrappingAdd,
            state_rotation: maximum_width - 1,
            immediate_law: BitImmediateLaw::Xor,
            immediate: bit_mask(maximum_width).unwrap() ^ 0b0010,
            output_law: BitBinaryLaw::WrappingAdd,
            input_rotation: maximum_width / 2,
        }
    }

    fn return_until_complete(
        world: &mut CausalWorld<BitCausalLaw>,
        target: BitTransducerProgram,
        next_event: &mut u64,
    ) {
        loop {
            if let Some(query) = world.standing().next_query() {
                let response = target.evaluate(query).unwrap();
                world
                    .receive(&BitCausalEvent::ReturnObservation {
                        event: EventId(*next_event),
                        receiver: BitLineageId(1),
                        query,
                        response,
                    })
                    .unwrap();
                *next_event += 1;
                continue;
            }
            if let Some(width) = world.standing().verification_width() {
                let mask = u32::from(bit_mask(width).unwrap());
                let responses = (0..1_u32 << (2 * width))
                    .map(|encoded| {
                        target
                            .evaluate(
                                BitQuery::new(
                                    width,
                                    ((encoded >> width) & mask) as u8,
                                    (encoded & mask) as u8,
                                )
                                .unwrap(),
                            )
                            .unwrap()
                    })
                    .collect();
                world
                    .receive(&BitCausalEvent::ReturnExhaustiveReceiver {
                        event: EventId(*next_event),
                        receiver: BitLineageId(1),
                        width,
                        responses,
                    })
                    .unwrap();
                *next_event += 1;
                continue;
            }
            break;
        }
    }

    #[test]
    fn exact_queries_reconstruct_a_recurrent_bit_family_across_receiver_widths() {
        let maximum_width = 4;
        let target = target_program(maximum_width);
        let law = BitCausalLaw::new(maximum_width, 1).unwrap();
        let standing = BitCausalStanding::new(maximum_width, 1).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let mut next_event = 100;
        for width in 1..=maximum_width {
            if width > 1 {
                world
                    .receive(&BitCausalEvent::FoundReceiver {
                        event: EventId(next_event),
                        width,
                    })
                    .unwrap();
                next_event += 1;
            }
            return_until_complete(&mut world, target, &mut next_event);
        }
        let certificate = world.standing().certificate().unwrap();
        assert_eq!(certificate.receiver_widths, BTreeSet::from([1, 2, 3, 4]));
        for candidate in world.standing().candidates() {
            for width in 1..=maximum_width {
                for encoded in 0..1_u32 << (2 * width) {
                    let query = BitQuery::new(
                        width,
                        (encoded >> width) as u8,
                        (encoded & u32::from(bit_mask(width).unwrap())) as u8,
                    )
                    .unwrap();
                    assert_eq!(candidate.evaluate(query), target.evaluate(query));
                }
            }
        }
        world.standing().validate().unwrap();
    }

    #[test]
    fn a_returned_observation_cannot_replace_the_production_query() {
        let law = BitCausalLaw::new(3, 1).unwrap();
        let standing = BitCausalStanding::new(3, 1).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let before = world.standing().clone();
        let wrong = BitQuery::new(1, 1, 1).unwrap();
        let target = target_program(3);
        assert!(matches!(
            world.receive(&BitCausalEvent::ReturnObservation {
                event: EventId(100),
                receiver: BitLineageId(1),
                query: wrong,
                response: target.evaluate(wrong).unwrap(),
            }),
            Err(BitCausalError::UnexpectedReturnedQuery { .. })
        ));
        assert_eq!(world.standing(), &before);
    }

    #[test]
    fn imported_landmark_is_retained_as_lineage_relative_testimony() {
        let law = BitCausalLaw::new(3, 1).unwrap();
        let standing = BitCausalStanding::new(3, 1).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let target = target_program(3);
        let query = BitQuery::new(1, 0, 0).unwrap();
        let before = world.standing().candidates().len();
        world
            .receive(&BitCausalEvent::InheritLandmark {
                event: EventId(100),
                lineage: BitLineageId(9),
                query,
                response: target.evaluate(query).unwrap(),
            })
            .unwrap();
        assert!(world.standing().candidates().len() < before);
        assert!(matches!(
            world.standing().testimonies().next().unwrap().source,
            BitTestimonySource::ImportedLandmark(BitLineageId(9))
        ));
    }

    #[test]
    fn a_reference_partitions_plural_answers_without_conditioning_standing() {
        let standing = BitCausalStanding::new(3, 1).unwrap();
        let before = standing.clone();
        let query = BitQuery::new(3, 5, 3).unwrap();
        let inspection = standing.inspect_reference(query).unwrap();
        assert_eq!(standing, before);
        assert_eq!(inspection.query, query);
        assert!(!inspection.receiver_width_already_founded);
        assert!(inspection.response_population() > 1);
        assert_eq!(inspection.forced_response(), None);
        assert_eq!(
            inspection
                .response_fibers
                .iter()
                .map(|fiber| fiber.programs.len())
                .sum::<usize>(),
            standing.candidates().len()
        );
    }

    #[test]
    fn returned_training_changes_a_reference_while_retaining_program_alternatives() {
        let target = target_program(3);
        let law = BitCausalLaw::new(3, 3).unwrap();
        let standing = BitCausalStanding::new(3, 3).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let reference = BitQuery::new(3, 5, 3).unwrap();
        let before = world.standing().inspect_reference(reference).unwrap();
        let query = world
            .standing()
            .next_query()
            .expect("the initial ecology must request a distinguishing return");
        world
            .receive(&BitCausalEvent::ReturnObservation {
                event: EventId(100),
                receiver: BitLineageId(1),
                query,
                response: target.evaluate(query).unwrap(),
            })
            .unwrap();
        let after = world.standing().inspect_reference(reference).unwrap();
        assert_eq!(world.standing().history().len(), 1);
        assert!(after.standing_candidate_population < before.standing_candidate_population);
        assert!(after.standing_candidate_population > 1);
        assert_eq!(
            after
                .response_fibers
                .iter()
                .map(|fiber| fiber.programs.len())
                .sum::<usize>(),
            world.standing().candidates().len()
        );
    }

    #[test]
    fn a_version_class_cannot_claim_black_box_certification_without_complete_return() {
        let law = BitCausalLaw::new(2, 1).unwrap();
        let standing = BitCausalStanding::new(2, 1).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let target = target_program(2);
        let mut next_event = 100;
        while let Some(query) = world.standing().next_query() {
            world
                .receive(&BitCausalEvent::ReturnObservation {
                    event: EventId(next_event),
                    receiver: BitLineageId(1),
                    query,
                    response: target.evaluate(query).unwrap(),
                })
                .unwrap();
            next_event += 1;
        }
        assert_eq!(world.standing().verification_width(), Some(1));
        assert!(world.standing().certificate().is_none());

        let before = world.standing().clone();
        assert_eq!(
            world.receive(&BitCausalEvent::ReturnExhaustiveReceiver {
                event: EventId(next_event),
                receiver: BitLineageId(1),
                width: 1,
                responses: vec![target.evaluate(BitQuery::new(1, 0, 0).unwrap()).unwrap()],
            }),
            Err(BitCausalError::MalformedExhaustiveTestimony {
                width: 1,
                expected: 4,
                received: 1,
            })
        );
        assert_eq!(world.standing(), &before);
    }

    #[test]
    fn cubical_receipt_exposes_carry_curvature_without_floats() {
        let program = target_program(4);
        let receipt = bit_cubical_geometry(program, 4).unwrap();
        assert_eq!(receipt.vertex_count, 256);
        assert_eq!(receipt.input_dimensions, 8);
        assert_eq!(receipt.output_dimensions, 8);
        assert!(receipt.algebraic_degrees.iter().any(|degree| *degree > 1));
        assert!(
            receipt
                .directed_edge_flip_counts
                .iter()
                .flatten()
                .any(|count| *count != 0 && *count != receipt.vertex_count)
        );
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn emitted_x86_machine_code_matches_the_exact_program_on_every_octet_pair() {
        let program = BitTransducerProgram {
            state_input_law: BitBinaryLaw::WrappingAdd,
            state_rotation: 5,
            immediate_law: BitImmediateLaw::Xor,
            immediate: 0xb7,
            output_law: BitBinaryLaw::WrappingAdd,
            input_rotation: 3,
        };
        let image = compile_x86_64_bit_program(program).unwrap();
        let executable = ExecutableX86BitProgram::new(&image).unwrap();
        for state in 0..=u8::MAX {
            for input in 0..=u8::MAX {
                let query = BitQuery::new(8, state, input).unwrap();
                assert_eq!(executable.execute(query), program.evaluate(query));
            }
        }
    }
}
