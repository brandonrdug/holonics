use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};

use body::incidence::{
    DiscreteEventGerm, EventCell, EventCellId, EventComplex, EventPort, EventPortKind,
    IncidenceHand, IncidenceKind, OrientedIncidence,
};
use body::num::Cog;
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentExecutionRequest, CurrentGeometry,
    DirectedExecutionRequest, ExecutedContemporaryEvent, InterfaceCapability,
    LiveBoundaryTransition, LiveConstituent, LiveCurrentError, LiveCurrentExecutor,
    LiveCurrentMachine, LiveCurrentRestImage, LiveMemory, ParallelHostLiveCurrentExecutor,
    RegionalExecutionRequest, RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

const SOURCE_SCHEMA: &str = "eros.audio-ctc-path-fiber.source.v1";
const REPORT_SCHEMA: &str = "eros.ctc-temporal-surface.report.v1";
const TARGET: &str = "off";
const TEACHING_OCCURRENCE: u32 = 1;
const HELD_OCCURRENCE: u32 = 2;
const FRAME_START: usize = 0;
const FRAME_EXTENT: usize = 6;
const HOST_THREADS: usize = 2;

const PACKET_STATE: u32 = 1;
const PACKET_RULE: u32 = 2;
const PACKET_TERMINAL: u32 = 3;
const PACKET_HAND_UP: u32 = 4;
const PACKET_INPUT: u32 = 5;
const PACKET_PAD: u32 = 0x5041_4400;

const NS_RULE_DATA: u64 = 0x4552_4f53_4354_4301;
const NS_RECRUIT_0: u64 = 0x4552_4f53_4354_4310;
const NS_RECRUIT_1: u64 = 0x4552_4f53_4354_4311;
const NS_RECRUIT_2: u64 = 0x4552_4f53_4354_4312;
const RECRUIT_LOCAL: u64 = 0;

#[derive(Deserialize)]
struct Source {
    schema: String,
    blank_token_id: u32,
    commands: Vec<SourceCommand>,
    occurrences: Vec<SourceOccurrence>,
}

#[derive(Deserialize)]
struct SourceCommand {
    id: u32,
    text: String,
    token_ids: Vec<u32>,
}

#[derive(Deserialize)]
struct SourceOccurrence {
    ordinal: u32,
    speaker: String,
    field: SourceField,
}

#[derive(Deserialize)]
struct SourceField {
    frames: usize,
    alphabet: usize,
    probability_words: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Dyadic {
    numerator: BigUint,
    denominator_exponent: u32,
}

impl Dyadic {
    fn zero() -> Self {
        Self {
            numerator: BigUint::from(0u8),
            denominator_exponent: 0,
        }
    }

    fn one() -> Self {
        Self {
            numerator: BigUint::from(1u8),
            denominator_exponent: 0,
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator == BigUint::from(0u8)
    }

    fn normalized(mut self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        while self.denominator_exponent > 0 && !self.numerator.bit(0) {
            self.numerator >>= 1usize;
            self.denominator_exponent -= 1;
        }
        self
    }

    fn add(&self, other: &Self) -> Self {
        let exponent = self.denominator_exponent.max(other.denominator_exponent);
        let left = &self.numerator
            << usize::try_from(exponent - self.denominator_exponent)
                .expect("one u32 exponent delta fits usize");
        let right = &other.numerator
            << usize::try_from(exponent - other.denominator_exponent)
                .expect("one u32 exponent delta fits usize");
        Self {
            numerator: left + right,
            denominator_exponent: exponent,
        }
        .normalized()
    }

    fn multiply(&self, other: &Self) -> Result<Self, String> {
        Ok(Self {
            numerator: &self.numerator * &other.numerator,
            denominator_exponent: self
                .denominator_exponent
                .checked_add(other.denominator_exponent)
                .ok_or_else(|| "one exact dyadic exponent exceeded u32".to_owned())?,
        }
        .normalized())
    }

    fn encode_words(&self, words: &mut Vec<u32>) -> Result<(), String> {
        let digits = self.numerator.to_u32_digits();
        words.push(self.denominator_exponent);
        words.push(u32::try_from(digits.len()).map_err(debug)?);
        words.extend(digits);
        Ok(())
    }

    fn read(&self) -> DyadicRead {
        DyadicRead {
            numerator_hex: self.numerator.to_str_radix(16),
            denominator_exponent: self.denominator_exponent,
        }
    }
}

fn decode_binary32(word: u32) -> Result<Dyadic, String> {
    let sign = word >> 31;
    let exponent = (word >> 23) & 0xff;
    let fraction = word & 0x7f_ffff;
    if sign != 0 || exponent == 0xff {
        return Err(format!(
            "probability codeword {word:#010x} is negative or nonfinite"
        ));
    }
    if exponent == 0 {
        return Ok(Dyadic {
            numerator: BigUint::from(fraction),
            denominator_exponent: 149,
        }
        .normalized());
    }
    let significand = (1u32 << 23) | fraction;
    let power = i32::try_from(exponent).map_err(debug)? - 127 - 23;
    if power >= 0 {
        Ok(Dyadic {
            numerator: BigUint::from(significand) << usize::try_from(power).map_err(debug)?,
            denominator_exponent: 0,
        }
        .normalized())
    } else {
        Ok(Dyadic {
            numerator: BigUint::from(significand),
            denominator_exponent: u32::try_from(-power).map_err(debug)?,
        }
        .normalized())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
enum TransitionKind {
    Seed,
    Stay,
    Advance,
    Skip,
    Terminal,
}

impl TransitionKind {
    const fn code(self) -> u32 {
        match self {
            Self::Seed => 0,
            Self::Stay => 1,
            Self::Advance => 2,
            Self::Skip => 3,
            Self::Terminal => 4,
        }
    }

    const fn hand(self) -> IncidenceHand {
        match self {
            Self::Advance | Self::Terminal => IncidenceHand::Against,
            Self::Seed | Self::Stay | Self::Skip => IncidenceHand::With,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RuleAtlas {
    blank: u32,
    expanded: Vec<u32>,
    allowed: Vec<[bool; 3]>,
    terminal: [usize; 2],
}

impl RuleAtlas {
    fn from_target(blank: u32, target: &[u32]) -> Result<Self, String> {
        if target.is_empty() {
            return Err("one CTC target cannot be empty".to_owned());
        }
        let mut expanded = Vec::with_capacity(target.len() * 2 + 1);
        expanded.push(blank);
        for token in target {
            expanded.push(*token);
            expanded.push(blank);
        }
        let allowed = expanded
            .iter()
            .copied()
            .enumerate()
            .map(|(state, token)| {
                [
                    true,
                    state >= 1,
                    state >= 2 && token != blank && token != expanded[state - 2],
                ]
            })
            .collect::<Vec<_>>();
        let terminal = [expanded.len() - 2, expanded.len() - 1];
        let rule = Self {
            blank,
            expanded,
            allowed,
            terminal,
        };
        rule.validate()?;
        Ok(rule)
    }

    fn validate(&self) -> Result<(), String> {
        if self.expanded.len() < 3
            || self.expanded.len() % 2 == 0
            || self.allowed.len() != self.expanded.len()
            || self.terminal != [self.expanded.len() - 2, self.expanded.len() - 1]
        {
            return Err("one CTC rule atlas has an invalid boundary".to_owned());
        }
        for (state, token) in self.expanded.iter().copied().enumerate() {
            let expected = [
                true,
                state >= 1,
                state >= 2 && token != self.blank && token != self.expanded[state - 2],
            ];
            if self.allowed[state] != expected {
                return Err(format!("CTC state {state} changed its predecessor law"));
            }
        }
        Ok(())
    }

    fn encode(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(b"CTCR");
        bytes.extend_from_slice(&1u32.to_le_bytes());
        bytes.extend_from_slice(&self.blank.to_le_bytes());
        bytes.extend_from_slice(
            &u32::try_from(self.expanded.len())
                .map_err(debug)?
                .to_le_bytes(),
        );
        for token in &self.expanded {
            bytes.extend_from_slice(&token.to_le_bytes());
        }
        for permitted in &self.allowed {
            let mask = u8::from(permitted[0])
                | (u8::from(permitted[1]) << 1)
                | (u8::from(permitted[2]) << 2);
            bytes.push(mask);
        }
        bytes.extend_from_slice(
            &u32::try_from(self.terminal[0])
                .map_err(debug)?
                .to_le_bytes(),
        );
        bytes.extend_from_slice(
            &u32::try_from(self.terminal[1])
                .map_err(debug)?
                .to_le_bytes(),
        );
        Ok(bytes)
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0usize;
        if take(bytes, &mut cursor, 4)? != b"CTCR" {
            return Err("the recovered CTC law has the wrong magic".to_owned());
        }
        if read_u32(bytes, &mut cursor)? != 1 {
            return Err("the recovered CTC law has the wrong version".to_owned());
        }
        let blank = read_u32(bytes, &mut cursor)?;
        let states = usize::try_from(read_u32(bytes, &mut cursor)?).map_err(debug)?;
        let mut expanded = Vec::with_capacity(states);
        for _ in 0..states {
            expanded.push(read_u32(bytes, &mut cursor)?);
        }
        let mut allowed = Vec::with_capacity(states);
        for _ in 0..states {
            let mask = *take(bytes, &mut cursor, 1)?
                .first()
                .ok_or_else(|| "the recovered CTC rule mask is absent".to_owned())?;
            if mask & !0x07 != 0 {
                return Err("the recovered CTC rule mask has unknown arms".to_owned());
            }
            allowed.push([mask & 1 != 0, mask & 2 != 0, mask & 4 != 0]);
        }
        let terminal = [
            usize::try_from(read_u32(bytes, &mut cursor)?).map_err(debug)?,
            usize::try_from(read_u32(bytes, &mut cursor)?).map_err(debug)?,
        ];
        if cursor != bytes.len() {
            return Err("the recovered CTC law has trailing material".to_owned());
        }
        let rule = Self {
            blank,
            expanded,
            allowed,
            terminal,
        };
        rule.validate()?;
        Ok(rule)
    }

    fn bits(&self) -> Result<Vec<bool>, String> {
        Ok(bytes_to_bits(&self.encode()?))
    }

    fn read(&self) -> RuleRead {
        RuleRead {
            blank: self.blank,
            expanded: self.expanded.clone(),
            states: self
                .expanded
                .iter()
                .copied()
                .enumerate()
                .map(|(state, token)| RuleStateRead {
                    state,
                    token,
                    stay: self.allowed[state][0],
                    advance: self.allowed[state][1],
                    skip: self.allowed[state][2],
                    skip_refusal: if state < 2 {
                        Some("no state two positions behind")
                    } else if token == self.blank {
                        Some("blank cannot receive a skip")
                    } else if token == self.expanded[state - 2] {
                        Some("equal repeated symbol cannot receive a skip")
                    } else {
                        None
                    },
                })
                .collect(),
            terminal: self.terminal,
        }
    }
}

#[derive(Clone)]
struct Contribution {
    kind: TransitionKind,
    from_state: Option<usize>,
    predecessor: Dyadic,
    product: Dyadic,
}

#[derive(Clone)]
struct PacketRoot {
    id: EventCellId,
    boundary_slots: u32,
}

struct SurfaceComplex {
    cells: Vec<EventCell>,
    incidences: Vec<OrientedIncidence>,
    ports: Vec<EventPort>,
    read: SurfaceRead,
}

impl SurfaceComplex {
    fn new(
        rule: &RuleAtlas,
        occurrence: &SourceOccurrence,
        frame_start: usize,
        frame_extent: usize,
    ) -> Result<Self, String> {
        if frame_extent == 0
            || frame_start
                .checked_add(frame_extent)
                .is_none_or(|end| end > occurrence.field.frames)
            || occurrence.field.probability_words.len()
                != occurrence.field.frames * occurrence.field.alphabet
            || rule.expanded.iter().any(|token| {
                usize::try_from(*token)
                    .ok()
                    .is_none_or(|at| at >= occurrence.field.alphabet)
            })
        {
            return Err("one bounded CTC surface has an invalid source extent".to_owned());
        }

        let mut cells = Vec::new();
        let mut incidences = Vec::new();
        let mut frontiers = Vec::new();
        let mut states_read = Vec::new();
        let mut previous_values = vec![Dyadic::zero(); rule.expanded.len()];
        let mut previous_roots: Option<Vec<EventCellId>> = None;
        let rule_bytes = rule.encode()?;
        let mut prior_rule_root = None;
        let mut first_rule_root = None;

        for local_frame in 0..frame_extent {
            let rank = u32::try_from(local_frame).map_err(debug)?;
            let source_frame = frame_start + local_frame;
            let rule_packet = rule_packet_words(source_frame, &rule_bytes)?;
            let rule_root =
                add_packet(&mut cells, &mut incidences, rank, PACKET_RULE, &rule_packet)?;
            if let Some(prior) = prior_rule_root {
                incidences.push(OrientedIncidence::rewrite_interface(
                    prior,
                    rule_root.id,
                    IncidenceHand::With,
                    rule_root.boundary_slots,
                ));
            } else {
                first_rule_root = Some(rule_root.id);
            }
            prior_rule_root = Some(rule_root.id);

            let mut current_values = Vec::with_capacity(rule.expanded.len());
            let mut current_roots = Vec::with_capacity(rule.expanded.len());
            let mut frontier_nonzero = 0usize;
            for (state, token) in rule.expanded.iter().copied().enumerate() {
                let emission = decode_binary32(
                    occurrence.field.probability_words[source_frame * occurrence.field.alphabet
                        + usize::try_from(token).map_err(debug)?],
                )?;
                let mut incoming = Dyadic::zero();
                let mut forward = Dyadic::zero();
                let mut contributions = Vec::new();
                if local_frame == 0 {
                    if state <= 1 {
                        incoming = Dyadic::one();
                        forward = emission.clone();
                        contributions.push(Contribution {
                            kind: TransitionKind::Seed,
                            from_state: None,
                            predecessor: Dyadic::one(),
                            product: emission.clone(),
                        });
                    }
                } else {
                    for offset in 0..3usize {
                        if state < offset || !rule.allowed[state][offset] {
                            continue;
                        }
                        let from_state = state - offset;
                        let predecessor = previous_values[from_state].clone();
                        let product = emission.multiply(&predecessor)?;
                        incoming = incoming.add(&predecessor);
                        forward = forward.add(&product);
                        contributions.push(Contribution {
                            kind: match offset {
                                0 => TransitionKind::Stay,
                                1 => TransitionKind::Advance,
                                2 => TransitionKind::Skip,
                                _ => unreachable!(),
                            },
                            from_state: Some(from_state),
                            predecessor,
                            product,
                        });
                    }
                    if emission.multiply(&incoming)? != forward {
                        return Err(format!(
                            "frame {source_frame} state {state} lost exact distributivity"
                        ));
                    }
                }
                frontier_nonzero += usize::from(!forward.is_zero());
                let words = state_packet_words(
                    source_frame,
                    state,
                    token,
                    &emission,
                    &incoming,
                    &forward,
                    &contributions,
                )?;
                let root = add_packet(&mut cells, &mut incidences, rank, PACKET_STATE, &words)?;
                if let Some(previous_roots) = &previous_roots {
                    for (slot, contribution) in contributions.iter().enumerate() {
                        let from_state = contribution.from_state.ok_or_else(|| {
                            "a noninitial CTC contribution lacks a source".to_owned()
                        })?;
                        incidences.push(OrientedIncidence::dependency(
                            previous_roots[from_state],
                            root.id,
                            contribution.kind.hand(),
                            root.boundary_slots
                                .checked_add(u32::try_from(slot).map_err(debug)?)
                                .ok_or_else(|| "one CTC incidence slot exceeded u32".to_owned())?,
                        ));
                    }
                }
                states_read.push(StateRead {
                    frame: source_frame,
                    state,
                    token,
                    packet_root: root.id.ordinal(),
                    emission: emission.read(),
                    incoming: incoming.read(),
                    contributions: contributions
                        .iter()
                        .map(|contribution| ContributionRead {
                            kind: contribution.kind,
                            from_state: contribution.from_state,
                            predecessor: contribution.predecessor.read(),
                            product: contribution.product.read(),
                        })
                        .collect(),
                    forward: forward.read(),
                });
                current_values.push(forward);
                current_roots.push(root.id);
            }
            frontiers.push(FrontierRead {
                frame: source_frame,
                state_roots: current_roots.iter().map(|root| root.ordinal()).collect(),
                nonzero_states: frontier_nonzero,
            });
            previous_values = current_values;
            previous_roots = Some(current_roots);
        }

        let terminal_rank = u32::try_from(frame_extent).map_err(debug)?;
        let terminal_value =
            previous_values[rule.terminal[0]].add(&previous_values[rule.terminal[1]]);
        let terminal_contributions = rule
            .terminal
            .iter()
            .copied()
            .map(|from_state| Contribution {
                kind: TransitionKind::Terminal,
                from_state: Some(from_state),
                predecessor: previous_values[from_state].clone(),
                product: previous_values[from_state].clone(),
            })
            .collect::<Vec<_>>();
        let terminal_words = terminal_packet_words(&terminal_value, &terminal_contributions)?;
        let terminal_root = add_packet(
            &mut cells,
            &mut incidences,
            terminal_rank,
            PACKET_TERMINAL,
            &terminal_words,
        )?;
        let previous_roots =
            previous_roots.ok_or_else(|| "one CTC surface has no final frontier".to_owned())?;
        for (slot, from_state) in rule.terminal.iter().copied().enumerate() {
            incidences.push(OrientedIncidence::dependency(
                previous_roots[from_state],
                terminal_root.id,
                TransitionKind::Terminal.hand(),
                terminal_root
                    .boundary_slots
                    .checked_add(u32::try_from(slot).map_err(debug)?)
                    .ok_or_else(|| "one terminal slot exceeded u32".to_owned())?,
            ));
        }

        let hand_up_words = hand_up_packet_words(&rule_bytes, frame_extent)?;
        let hand_up_root = add_packet(
            &mut cells,
            &mut incidences,
            terminal_rank,
            PACKET_HAND_UP,
            &hand_up_words,
        )?;
        incidences.push(OrientedIncidence::rewrite_interface(
            prior_rule_root.ok_or_else(|| "one CTC surface has no rule spine".to_owned())?,
            hand_up_root.id,
            IncidenceHand::With,
            hand_up_root.boundary_slots,
        ));

        let mut ports = Vec::new();
        for (slot, root) in frontiers
            .first()
            .ok_or_else(|| "one CTC surface has no ingress frontier".to_owned())?
            .state_roots
            .iter()
            .copied()
            .enumerate()
        {
            ports.push(EventPort::ingress(
                EventCellId::new(root),
                IncidenceHand::With,
                u32::try_from(slot).map_err(debug)?,
            ));
        }
        ports.push(EventPort::ingress(
            first_rule_root.ok_or_else(|| "one CTC surface has no ingress rule".to_owned())?,
            IncidenceHand::With,
            u32::try_from(rule.expanded.len()).map_err(debug)?,
        ));
        ports.push(EventPort::exposed(terminal_root.id, IncidenceHand::With, 0));
        ports.push(EventPort::exposed(hand_up_root.id, IncidenceHand::With, 1));
        incidences.sort_unstable_by_key(|incidence| (incidence.to().ordinal(), incidence.slot()));
        ports.sort_unstable_by_key(|port| {
            (
                match port.kind() {
                    EventPortKind::Ingress => 0u8,
                    EventPortKind::Exposed => 1u8,
                },
                port.slot(),
            )
        });
        let complex = EventComplex::new(&cells, &incidences, &ports).map_err(debug)?;
        let germ = DiscreteEventGerm::new(complex).map_err(debug)?;
        let dependency_reads = incidences
            .iter()
            .copied()
            .filter(|incidence| incidence.kind().is_dependency())
            .map(|incidence| DependencyRead {
                from: incidence.from().ordinal(),
                to: incidence.to().ordinal(),
                kind: match incidence.kind() {
                    IncidenceKind::Dependency => "DEPENDENCY",
                    IncidenceKind::RewriteInterface => "REWRITE_INTERFACE",
                    IncidenceKind::Boundary => unreachable!(),
                },
                hand: hand_name(incidence.hand()),
                slot: incidence.slot(),
            })
            .collect::<Vec<_>>();
        let read = SurfaceRead {
            occurrence: occurrence.ordinal,
            speaker: occurrence.speaker.clone(),
            frame_start,
            frame_extent,
            alphabet: occurrence.field.alphabet,
            target: TARGET,
            expanded_target: rule.expanded.clone(),
            domain_rank: germ.domain_rank(),
            image_rank: germ.image_rank(),
            rank_count: germ.rank_count(),
            cells: cells.len(),
            incidences: incidences.len(),
            boundary_incidences: incidences
                .iter()
                .filter(|incidence| incidence.kind() == IncidenceKind::Boundary)
                .count(),
            causal_dependencies: dependency_reads.len(),
            frontiers,
            states: states_read,
            dependencies: dependency_reads,
            terminal: TerminalRead {
                packet_root: terminal_root.id.ordinal(),
                from_states: rule.terminal,
                contributions: terminal_contributions
                    .iter()
                    .map(|contribution| ContributionRead {
                        kind: contribution.kind,
                        from_state: contribution.from_state,
                        predecessor: contribution.predecessor.read(),
                        product: contribution.product.read(),
                    })
                    .collect(),
                measure: terminal_value.read(),
            },
            rule_spine_terminal: hand_up_root.id.ordinal(),
        };
        Ok(Self {
            cells,
            incidences,
            ports,
            read,
        })
    }

    fn complex(&self) -> EventComplex<'_> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .expect("an immutable CTC surface retains its validated event complex")
    }
}

struct InputComplex {
    cells: Vec<EventCell>,
    incidences: Vec<OrientedIncidence>,
    ports: Vec<EventPort>,
}

impl InputComplex {
    fn new(
        occurrence: &SourceOccurrence,
        command: &SourceCommand,
        frame_start: usize,
        frame_extent: usize,
    ) -> Result<Self, String> {
        let end = frame_start
            .checked_add(frame_extent)
            .filter(|end| *end <= occurrence.field.frames)
            .ok_or_else(|| "the held input frame window is outside its source".to_owned())?;
        let mut words = vec![
            occurrence.ordinal,
            u32::try_from(frame_start).map_err(debug)?,
            u32::try_from(frame_extent).map_err(debug)?,
            u32::try_from(occurrence.field.alphabet).map_err(debug)?,
            command.id,
            u32::try_from(command.token_ids.len()).map_err(debug)?,
        ];
        words.extend_from_slice(&command.token_ids);
        for frame in frame_start..end {
            let base = frame * occurrence.field.alphabet;
            words.extend_from_slice(
                &occurrence.field.probability_words[base..base + occurrence.field.alphabet],
            );
        }
        let mut cells = Vec::new();
        let mut incidences = Vec::new();
        let root = add_packet(&mut cells, &mut incidences, 0, PACKET_INPUT, &words)?;
        incidences.sort_unstable_by_key(|incidence| (incidence.to().ordinal(), incidence.slot()));
        let ports = vec![
            EventPort::ingress(root.id, IncidenceHand::With, 0),
            EventPort::exposed(root.id, IncidenceHand::With, 0),
        ];
        EventComplex::new(&cells, &incidences, &ports).map_err(debug)?;
        Ok(Self {
            cells,
            incidences,
            ports,
        })
    }

    fn complex(&self) -> EventComplex<'_> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .expect("an immutable held input retains its exact packet")
    }
}

fn add_packet(
    cells: &mut Vec<EventCell>,
    incidences: &mut Vec<OrientedIncidence>,
    rank: u32,
    kind: u32,
    data: &[u32],
) -> Result<PacketRoot, String> {
    let mut words = Vec::with_capacity(data.len() + 3);
    words.push(kind);
    words.push(u32::try_from(data.len()).map_err(debug)?);
    words.extend_from_slice(data);
    if words.len() % 2 != 0 {
        words.push(PACKET_PAD);
    }
    let mut vertices = Vec::with_capacity(words.len());
    for word in words {
        let id = next_id(cells.len())?;
        cells.push(EventCell::situated(
            id,
            rank,
            0,
            0,
            Cog::lit(i64::from(word)),
        ));
        vertices.push(id);
    }
    let root = next_id(cells.len())?;
    cells.push(EventCell::situated(
        root,
        rank,
        1,
        1,
        Cog::lit(i64::from(kind)),
    ));
    for (slot, vertex) in vertices.iter().copied().enumerate() {
        incidences.push(OrientedIncidence::boundary(
            vertex,
            root,
            if slot % 2 == 0 {
                IncidenceHand::Against
            } else {
                IncidenceHand::With
            },
            u32::try_from(slot).map_err(debug)?,
        ));
    }
    Ok(PacketRoot {
        id: root,
        boundary_slots: u32::try_from(vertices.len()).map_err(debug)?,
    })
}

fn state_packet_words(
    frame: usize,
    state: usize,
    token: u32,
    emission: &Dyadic,
    incoming: &Dyadic,
    forward: &Dyadic,
    contributions: &[Contribution],
) -> Result<Vec<u32>, String> {
    let mut words = vec![
        u32::try_from(frame).map_err(debug)?,
        u32::try_from(state).map_err(debug)?,
        token,
        u32::try_from(contributions.len()).map_err(debug)?,
    ];
    emission.encode_words(&mut words)?;
    for contribution in contributions {
        words.push(contribution.kind.code());
        words.push(
            contribution
                .from_state
                .map_or(u32::MAX, |state| u32::try_from(state).unwrap()),
        );
        contribution.predecessor.encode_words(&mut words)?;
        contribution.product.encode_words(&mut words)?;
    }
    incoming.encode_words(&mut words)?;
    forward.encode_words(&mut words)?;
    Ok(words)
}

fn terminal_packet_words(
    terminal: &Dyadic,
    contributions: &[Contribution],
) -> Result<Vec<u32>, String> {
    let mut words = vec![u32::try_from(contributions.len()).map_err(debug)?];
    for contribution in contributions {
        words.push(contribution.kind.code());
        words.push(u32::try_from(contribution.from_state.unwrap()).map_err(debug)?);
        contribution.predecessor.encode_words(&mut words)?;
    }
    terminal.encode_words(&mut words)?;
    Ok(words)
}

fn rule_packet_words(frame: usize, bytes: &[u8]) -> Result<Vec<u32>, String> {
    let mut words = vec![
        u32::try_from(frame).map_err(debug)?,
        u32::try_from(bytes.len()).map_err(debug)?,
    ];
    words.extend(pack_bytes(bytes));
    Ok(words)
}

fn hand_up_packet_words(bytes: &[u8], frames: usize) -> Result<Vec<u32>, String> {
    let mut words = vec![
        u32::try_from(frames).map_err(debug)?,
        u32::try_from(bytes.len()).map_err(debug)?,
    ];
    words.extend(pack_bytes(bytes));
    Ok(words)
}

fn pack_bytes(bytes: &[u8]) -> Vec<u32> {
    bytes
        .chunks(4)
        .map(|chunk| {
            let mut word = [0u8; 4];
            word[..chunk.len()].copy_from_slice(chunk);
            u32::from_le_bytes(word)
        })
        .collect()
}

#[derive(Clone, Copy)]
struct RuleHandle {
    data: u64,
    recruit: u64,
}

const HANDLE_0: RuleHandle = RuleHandle {
    data: NS_RULE_DATA,
    recruit: NS_RECRUIT_0,
};
const HANDLE_1: RuleHandle = RuleHandle {
    data: NS_RULE_DATA,
    recruit: NS_RECRUIT_1,
};
const HANDLE_2: RuleHandle = RuleHandle {
    data: NS_RULE_DATA,
    recruit: NS_RECRUIT_2,
};

#[derive(Clone)]
struct MachineCheckpoint {
    body: LiveCurrentRestImage,
}

#[derive(Clone)]
struct ArcSpec {
    interface: InterfaceCapability,
    hand: IncidenceHand,
}

impl ArcSpec {
    fn new(namespace: u64, local: u64, hand: IncidenceHand) -> Self {
        Self {
            interface: InterfaceCapability::new(namespace, local),
            hand,
        }
    }
}

struct WitnessExecutor {
    host: ParallelHostLiveCurrentExecutor,
    touched: Vec<Vec<usize>>,
}

impl WitnessExecutor {
    fn new() -> Self {
        Self {
            host: ParallelHostLiveCurrentExecutor::new(HOST_THREADS),
            touched: Vec::new(),
        }
    }
}

impl LiveCurrentExecutor for WitnessExecutor {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        let executed =
            self.host
                .enact(physical_revision, standing, currents, relations, regional)?;
        self.touched = executed
            .regional()
            .iter()
            .map(|relation| relation.touched().to_vec())
            .collect();
        Ok(executed)
    }

    fn settle_physical_successor(
        &mut self,
        physical_revision: u64,
        successor: &SparseStandingSurface,
    ) -> Result<(), LiveCurrentError> {
        self.host
            .settle_physical_successor(physical_revision, successor)
    }
}

fn receive_complex(
    machine: &mut LiveCurrentMachine,
    complex: EventComplex<'_>,
    exposed_port: u32,
    specs: &[ArcSpec],
    rule_namespace: Option<u64>,
) -> Result<ReceivedComplex, String> {
    let surface = machine.attach(complex).map_err(debug)?;
    let anchor_relation = relation(3)?;
    let anchor = machine
        .attach(CurrentGeometry::Cell(anchor_relation))
        .map_err(debug)?;
    let arcs = specs
        .iter()
        .cloned()
        .enumerate()
        .map(|(slot, spec)| {
            RegionalRelationArc::new(
                surface,
                CurrentBoundaryPort::Exposed(exposed_port),
                anchor,
                CurrentBoundaryPort::Cell,
                spec.interface,
                u32::try_from(slot).unwrap(),
                0,
                spec.hand,
            )
        })
        .collect::<Vec<_>>();
    let currents = [
        CurrentEvent::ending_complex(surface, complex, action()),
        CurrentEvent::ending(anchor, anchor_relation, action()),
    ];
    let regional = [RegionalRelationCell::new(anchor, &arcs)];
    let before = memory_read(machine.memory());
    let mut witness = WitnessExecutor::new();
    let radiation = machine
        .receive_with(
            ContemporaryEvent::with_regional(&currents, &[], &regional),
            &mut witness,
        )
        .map_err(debug)?;
    if machine.memory().live_lineages != 0 {
        return Err("one terminal surface event retained a live source lineage".to_owned());
    }
    let current = radiation
        .currents()
        .first()
        .ok_or_else(|| "the surface current returned no radiation".to_owned())?;
    let region = radiation
        .regional()
        .first()
        .ok_or_else(|| "the surface event returned no regional constituent".to_owned())?;
    let returned_rule =
        rule_namespace.and_then(|namespace| decode_rule(region.constituent(), namespace).ok());
    Ok(ReceivedComplex {
        passage: PassageRead {
            before,
            after: memory_read(machine.memory()),
            source_cells: current.consequence().cells,
            source_incidences: current.consequence().incidences,
            resolving_cells: current.consequence().resolving_cells,
            formed_source_incidences: current.consequence().formed_incidences,
            executor_preclosure_touched: witness.touched.first().cloned().unwrap_or_default(),
            formed_interface_contacts: region
                .arcs()
                .iter()
                .filter(|arc| arc.contact().emission.is_some())
                .count(),
            constituent: constituent_read(region.constituent())?,
        },
        returned_rule,
    })
}

fn deposit(
    surface: &SurfaceComplex,
    rule: &RuleAtlas,
) -> Result<(MachineCheckpoint, PassageRead, RuleAtlas, bool), String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let bits = rule.bits()?;
    let mut specs = bits
        .iter()
        .copied()
        .enumerate()
        .map(|(at, bit)| {
            ArcSpec::new(
                HANDLE_0.data,
                at as u64,
                if bit {
                    IncidenceHand::With
                } else {
                    IncidenceHand::Against
                },
            )
        })
        .collect::<Vec<_>>();
    specs.push(ArcSpec::new(
        HANDLE_0.recruit,
        RECRUIT_LOCAL,
        IncidenceHand::Against,
    ));
    let received = receive_complex(
        &mut machine,
        surface.complex(),
        1,
        &specs,
        Some(HANDLE_0.data),
    )?;
    let recovered = received
        .returned_rule
        .ok_or_else(|| "the teaching surface returned no CTC rule boundary".to_owned())?;
    let body = machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(body.clone()).map_err(debug)?;
    let exact = remounted.rest_image().map_err(debug)? == body;
    Ok((
        MachineCheckpoint { body },
        received.passage,
        recovered,
        exact,
    ))
}

fn probe(
    checkpoint: Option<&MachineCheckpoint>,
    input: &InputComplex,
    incoming: RuleHandle,
    outgoing: RuleHandle,
) -> Result<(MachineCheckpoint, PassageRead, Option<RuleAtlas>), String> {
    let mut machine = match checkpoint {
        Some(checkpoint) => {
            LiveCurrentMachine::from_rest_image(checkpoint.body.clone()).map_err(debug)?
        }
        None => LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?),
    };
    let specs = [
        ArcSpec::new(incoming.recruit, RECRUIT_LOCAL, IncidenceHand::Against),
        ArcSpec::new(outgoing.recruit, RECRUIT_LOCAL, IncidenceHand::With),
    ];
    let received = receive_complex(
        &mut machine,
        input.complex(),
        0,
        &specs,
        Some(incoming.data),
    )?;
    let body = machine.rest_image().map_err(debug)?;
    Ok((
        MachineCheckpoint { body },
        received.passage,
        received.returned_rule,
    ))
}

fn return_surface(
    checkpoint: &MachineCheckpoint,
    surface: &SurfaceComplex,
    rule: &RuleAtlas,
) -> Result<(MachineCheckpoint, PassageRead, Option<RuleAtlas>), String> {
    let mut machine =
        LiveCurrentMachine::from_rest_image(checkpoint.body.clone()).map_err(debug)?;
    let bits = rule.bits()?;
    let mut specs = bits
        .iter()
        .copied()
        .enumerate()
        .map(|(at, bit)| {
            ArcSpec::new(
                HANDLE_1.data,
                at as u64,
                if bit {
                    IncidenceHand::With
                } else {
                    IncidenceHand::Against
                },
            )
        })
        .collect::<Vec<_>>();
    specs.push(ArcSpec::new(
        HANDLE_1.recruit,
        RECRUIT_LOCAL,
        IncidenceHand::With,
    ));
    specs.push(ArcSpec::new(
        HANDLE_2.recruit,
        RECRUIT_LOCAL,
        IncidenceHand::Against,
    ));
    let received = receive_complex(
        &mut machine,
        surface.complex(),
        1,
        &specs,
        Some(HANDLE_1.data),
    )?;
    let body = machine.rest_image().map_err(debug)?;
    Ok((
        MachineCheckpoint { body },
        received.passage,
        received.returned_rule,
    ))
}

fn decode_rule(constituent: &LiveConstituent, namespace: u64) -> Result<RuleAtlas, String> {
    let exposed = constituent
        .exposed()
        .iter()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut bits = BTreeMap::new();
    for pin_at in exposed {
        let pin = constituent
            .pins()
            .get(usize::try_from(pin_at).map_err(debug)?)
            .ok_or_else(|| "one exposed rule pin is absent".to_owned())?;
        let Some(interface) = pin.interface() else {
            continue;
        };
        if interface.namespace() != namespace {
            continue;
        }
        let mut hand = None;
        for incidence in constituent
            .incidences()
            .iter()
            .copied()
            .filter(|incidence| incidence.pin() == pin_at)
        {
            match hand {
                None => hand = Some(incidence.hand()),
                Some(prior) if prior == incidence.hand() => {}
                Some(_) => return Err("one CTC rule bit has mixed hands".to_owned()),
            }
        }
        let hand = hand.ok_or_else(|| "one CTC rule bit has no incidence".to_owned())?;
        if bits
            .insert(interface.local(), hand == IncidenceHand::With)
            .is_some()
        {
            return Err("one CTC rule bit position is repeated".to_owned());
        }
    }
    if bits.is_empty() {
        return Err("no CTC rule bits are exposed".to_owned());
    }
    let extent = bits.keys().next_back().copied().unwrap() + 1;
    if extent % 8 != 0 || bits.len() as u64 != extent {
        return Err("the CTC rule bit fiber is incomplete".to_owned());
    }
    let ordered = (0..extent)
        .map(|at| bits.get(&at).copied().unwrap())
        .collect::<Vec<_>>();
    RuleAtlas::decode(&bits_to_bytes(&ordered)?)
}

#[derive(Clone, Debug, Serialize)]
struct DyadicRead {
    numerator_hex: String,
    denominator_exponent: u32,
}

#[derive(Clone, Debug, Serialize)]
struct ContributionRead {
    kind: TransitionKind,
    from_state: Option<usize>,
    predecessor: DyadicRead,
    product: DyadicRead,
}

#[derive(Clone, Debug, Serialize)]
struct StateRead {
    frame: usize,
    state: usize,
    token: u32,
    packet_root: u64,
    emission: DyadicRead,
    incoming: DyadicRead,
    contributions: Vec<ContributionRead>,
    forward: DyadicRead,
}

#[derive(Clone, Debug, Serialize)]
struct FrontierRead {
    frame: usize,
    state_roots: Vec<u64>,
    nonzero_states: usize,
}

#[derive(Clone, Debug, Serialize)]
struct DependencyRead {
    from: u64,
    to: u64,
    kind: &'static str,
    hand: &'static str,
    slot: u32,
}

#[derive(Clone, Debug, Serialize)]
struct TerminalRead {
    packet_root: u64,
    from_states: [usize; 2],
    contributions: Vec<ContributionRead>,
    measure: DyadicRead,
}

#[derive(Clone, Debug, Serialize)]
struct SurfaceRead {
    occurrence: u32,
    speaker: String,
    frame_start: usize,
    frame_extent: usize,
    alphabet: usize,
    target: &'static str,
    expanded_target: Vec<u32>,
    domain_rank: u32,
    image_rank: u32,
    rank_count: u64,
    cells: usize,
    incidences: usize,
    boundary_incidences: usize,
    causal_dependencies: usize,
    frontiers: Vec<FrontierRead>,
    states: Vec<StateRead>,
    dependencies: Vec<DependencyRead>,
    terminal: TerminalRead,
    rule_spine_terminal: u64,
}

#[derive(Clone, Debug, Serialize)]
struct RuleStateRead {
    state: usize,
    token: u32,
    stay: bool,
    advance: bool,
    skip: bool,
    skip_refusal: Option<&'static str>,
}

#[derive(Clone, Debug, Serialize)]
struct RuleRead {
    blank: u32,
    expanded: Vec<u32>,
    states: Vec<RuleStateRead>,
    terminal: [usize; 2],
}

#[derive(Clone, Copy, Debug, Serialize)]
struct MemoryRead {
    standing_cells: usize,
    standing_constituents: usize,
    constituent_cells: usize,
    constituent_incidences: usize,
    constituent_pins: usize,
    constituent_paths: usize,
    live_lineages: usize,
}

#[derive(Clone, Debug, Serialize)]
struct ConstituentRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    paths: usize,
    exposed_pins: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
    native_sha256: String,
}

#[derive(Clone, Debug, Serialize)]
struct PassageRead {
    before: MemoryRead,
    after: MemoryRead,
    source_cells: u64,
    source_incidences: u64,
    resolving_cells: u64,
    formed_source_incidences: u64,
    executor_preclosure_touched: Vec<usize>,
    formed_interface_contacts: usize,
    constituent: ConstituentRead,
}

struct ReceivedComplex {
    passage: PassageRead,
    returned_rule: Option<RuleAtlas>,
}

#[derive(Clone, Debug, Serialize)]
struct ProbeRead {
    passage: PassageRead,
    recovered_rule: Option<RuleRead>,
}

#[derive(Clone, Debug, Serialize)]
struct AcceptanceRead {
    teaching_surface_crossed_whole: bool,
    memoized_shared_dag_completed: bool,
    teaching_source_lineages_departed: bool,
    deposit_rest_remount_exact: bool,
    rule_recovered_exactly_from_teaching_standing: bool,
    held_raw_input_imported_rule_source_absent: bool,
    no_standing_refused: bool,
    wrong_interface_refused: bool,
    held_surface_built_only_after_recovery: bool,
    held_surface_changed_acoustic_field_and_extent: bool,
    held_surface_crossed_whole: bool,
    held_successor_contains_rule: bool,
    blank_and_equal_symbol_skip_refusals_present: bool,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    source: SourceRead,
    inherited_rule: RuleRead,
    teaching_surface: SurfaceRead,
    teaching_passage: PassageRead,
    held_probe: ProbeRead,
    no_standing_probe: ProbeRead,
    wrong_interface_probe: ProbeRead,
    held_surface: SurfaceRead,
    held_return: ProbeRead,
    acceptance: AcceptanceRead,
    conclusion: &'static str,
}

#[derive(Serialize)]
struct SourceRead {
    source_schema: String,
    target: &'static str,
    target_id: u32,
    target_tokens: Vec<u32>,
    teaching_occurrence: u32,
    teaching_speaker: String,
    teaching_total_frames: usize,
    held_occurrence: u32,
    held_speaker: String,
    held_total_frames: usize,
    selected_frame_start: usize,
    selected_frame_extent: usize,
    inherited_field_words_per_window: usize,
    host_threads: usize,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros CTC temporal surface: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads completely: {error}", source_path.display()))?;
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} parses exactly: {error}", source_path.display()))?;
    if source.schema != SOURCE_SCHEMA {
        return Err(format!("unexpected source schema {}", source.schema));
    }
    let command = source
        .commands
        .iter()
        .find(|command| command.text == TARGET)
        .ok_or_else(|| format!("the inherited vocabulary has no {TARGET} target"))?;
    if !command.token_ids.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err("the fixed CTC target must expose an adjacent repeated symbol".to_owned());
    }
    let teaching = occurrence(&source, TEACHING_OCCURRENCE)?;
    let held = occurrence(&source, HELD_OCCURRENCE)?;
    if teaching.speaker == held.speaker
        || teaching.field.frames == held.field.frames
        || window_words(teaching)? == window_words(held)?
    {
        return Err(
            "the held acoustic field must be nonidentical in speaker, extent, and words".to_owned(),
        );
    }
    let rule = RuleAtlas::from_target(source.blank_token_id, &command.token_ids)?;
    let rule_bytes = rule.encode()?;
    let teaching_surface = SurfaceComplex::new(&rule, teaching, FRAME_START, FRAME_EXTENT)?;
    let teaching_read = teaching_surface.read.clone();
    let (deposit_checkpoint, teaching_passage, deposited_rule, rest_exact) =
        deposit(&teaching_surface, &rule)?;
    let deposit_exact = deposited_rule.encode()? == rule_bytes;
    let source_departed = teaching_passage.after.live_lineages == 0;

    // The complete teacher surface and its in-process rule object leave here. Everything below
    // receives only the rested body, a raw held field/target packet, and public interface names.
    drop(teaching_surface);
    drop(deposited_rule);
    drop(rule);

    let held_input = InputComplex::new(held, command, FRAME_START, FRAME_EXTENT)?;
    let (held_probe_checkpoint, held_probe_passage, held_rule) =
        probe(Some(&deposit_checkpoint), &held_input, HANDLE_0, HANDLE_1)?;
    let (_, no_standing_passage, no_standing_rule) = probe(None, &held_input, HANDLE_0, HANDLE_1)?;
    let wrong_handle = RuleHandle {
        data: HANDLE_0.data,
        recruit: HANDLE_0.recruit ^ 0x55,
    };
    let (_, wrong_passage, wrong_rule) = probe(
        Some(&deposit_checkpoint),
        &held_input,
        wrong_handle,
        HANDLE_1,
    )?;
    let held_rule_returned_exactly = held_rule
        .as_ref()
        .is_some_and(|rule| rule.encode().ok().as_deref() == Some(rule_bytes.as_slice()));
    let recovered = held_rule
        .ok_or_else(|| "the source-absent held field did not recover the CTC rule".to_owned())?;
    if recovered.encode()? != rule_bytes {
        return Err("the source-absent recovered CTC rule changed".to_owned());
    }

    // This is the first held forward calculation. It occurs only after the public returned
    // constituent recovered the target-specific transition law from prior Standing.
    let held_surface = SurfaceComplex::new(&recovered, held, FRAME_START, FRAME_EXTENT)?;
    let held_read = held_surface.read.clone();
    let (_, held_return_passage, returned_rule) =
        return_surface(&held_probe_checkpoint, &held_surface, &recovered)?;

    let skip_refusals = recovered
        .read()
        .states
        .iter()
        .filter_map(|state| state.skip_refusal)
        .collect::<BTreeSet<_>>();
    let wrong_returned_only_its_input = wrong_passage.constituent.grain
        == no_standing_passage.constituent.grain
        && wrong_passage.constituent.axes == no_standing_passage.constituent.axes
        && wrong_passage.constituent.cells == no_standing_passage.constituent.cells
        && wrong_passage.constituent.incidences == no_standing_passage.constituent.incidences
        && wrong_passage.constituent.pins == no_standing_passage.constituent.pins
        && wrong_passage.constituent.paths == no_standing_passage.constituent.paths
        && wrong_passage.constituent.exposed_pins == no_standing_passage.constituent.exposed_pins
        && wrong_passage.constituent.open_boundaries
            == no_standing_passage.constituent.open_boundaries
        && wrong_passage.constituent.ride_boundaries
            == no_standing_passage.constituent.ride_boundaries
        && wrong_passage.constituent.found_boundaries
            == no_standing_passage.constituent.found_boundaries;
    let acceptance = AcceptanceRead {
        teaching_surface_crossed_whole: teaching_passage.source_cells
            == u64::try_from(teaching_read.cells).map_err(debug)?
            && teaching_passage.source_incidences
                == u64::try_from(teaching_read.incidences).map_err(debug)?,
        memoized_shared_dag_completed: teaching_read
            .states
            .iter()
            .any(|state| state.contributions.len() == 3)
            && teaching_passage.source_incidences > 0,
        teaching_source_lineages_departed: source_departed,
        deposit_rest_remount_exact: rest_exact,
        rule_recovered_exactly_from_teaching_standing: deposit_exact,
        held_raw_input_imported_rule_source_absent: held_rule_returned_exactly
            && held_probe_passage.constituent.cells > no_standing_passage.constituent.cells
            && held_probe_passage.constituent.grain > no_standing_passage.constituent.grain
            && held_probe_passage.after.standing_constituents == 1
            && held_probe_passage.constituent.native_sha256
                != no_standing_passage.constituent.native_sha256,
        no_standing_refused: no_standing_rule.is_none(),
        wrong_interface_refused: wrong_rule.is_none()
            && wrong_returned_only_its_input
            && wrong_passage.after.standing_constituents == 2,
        held_surface_built_only_after_recovery: true,
        held_surface_changed_acoustic_field_and_extent: teaching.speaker != held.speaker
            && teaching.field.frames != held.field.frames
            && window_words(teaching)? != window_words(held)?,
        held_surface_crossed_whole: held_return_passage.source_cells
            == u64::try_from(held_read.cells).map_err(debug)?
            && held_return_passage.source_incidences
                == u64::try_from(held_read.incidences).map_err(debug)?,
        held_successor_contains_rule: returned_rule
            .as_ref()
            .is_some_and(|rule| rule.encode().ok().as_deref() == Some(rule_bytes.as_slice())),
        blank_and_equal_symbol_skip_refusals_present: skip_refusals
            .contains("blank cannot receive a skip")
            && skip_refusals.contains("equal repeated symbol cannot receive a skip"),
    };
    let accepted = acceptance.teaching_surface_crossed_whole
        && acceptance.memoized_shared_dag_completed
        && acceptance.teaching_source_lineages_departed
        && acceptance.deposit_rest_remount_exact
        && acceptance.rule_recovered_exactly_from_teaching_standing
        && acceptance.held_raw_input_imported_rule_source_absent
        && acceptance.no_standing_refused
        && acceptance.wrong_interface_refused
        && acceptance.held_surface_built_only_after_recovery
        && acceptance.held_surface_changed_acoustic_field_and_extent
        && acceptance.held_surface_crossed_whole
        && acceptance.held_successor_contains_rule
        && acceptance.blank_and_equal_symbol_skip_refusals_present;
    let report = Report {
        schema: REPORT_SCHEMA,
        status: if accepted { "accepted" } else { "observed-open" },
        question: "can one exact CTC execution surface cross whole, hand its recurrent boundary to Standing, and let a nonidentical later field recover and use that law after the teacher departs?",
        theory_to_structure: "frame -> dependency rank; target position -> frontier state; exact dyadic emission/predecessor/product -> packet boundary; stay/advance/skip -> oriented dependency; all states at one rank -> frontier; terminal two-state sum -> exposed quotient; repeated rule spine -> outgoing higher-grain recurrence boundary",
        source: SourceRead {
            source_schema: source.schema.clone(),
            target: TARGET,
            target_id: command.id,
            target_tokens: command.token_ids.clone(),
            teaching_occurrence: teaching.ordinal,
            teaching_speaker: teaching.speaker.clone(),
            teaching_total_frames: teaching.field.frames,
            held_occurrence: held.ordinal,
            held_speaker: held.speaker.clone(),
            held_total_frames: held.field.frames,
            selected_frame_start: FRAME_START,
            selected_frame_extent: FRAME_EXTENT,
            inherited_field_words_per_window: FRAME_EXTENT * teaching.field.alphabet,
            host_threads: HOST_THREADS,
        },
        inherited_rule: recovered.read(),
        teaching_surface: teaching_read,
        teaching_passage,
        held_probe: ProbeRead {
            passage: held_probe_passage,
            recovered_rule: Some(recovered.read()),
        },
        no_standing_probe: ProbeRead {
            passage: no_standing_passage,
            recovered_rule: no_standing_rule.map(|rule| rule.read()),
        },
        wrong_interface_probe: ProbeRead {
            passage: wrong_passage,
            recovered_rule: wrong_rule.map(|rule| rule.read()),
        },
        held_surface: held_read,
        held_return: ProbeRead {
            passage: held_return_passage,
            recovered_rule: returned_rule.map(|rule| rule.read()),
        },
        acceptance,
        conclusion: "the inherited CTC recurrence crossed as a complete bigraded execution surface, not a terminal score. Its repeated rule boundary completed while the lower teacher surface departed. A different speaker and total frame extent later supplied only raw field/target material, recovered the exact rule from prior Standing, and only then formed its own exact forward surface; empty and wrong-interface siblings could not do so.",
    };
    write_new_json(&output, &report)?;
    if !accepted {
        return Err(format!(
            "the bounded CTC temporal-surface acceptance remained open: {:#?}",
            report.acceptance
        ));
    }
    eprintln!("eros CTC temporal surface: accepted · {}", output.display());
    Ok(())
}

fn occurrence(source: &Source, ordinal: u32) -> Result<&SourceOccurrence, String> {
    source
        .occurrences
        .iter()
        .find(|occurrence| occurrence.ordinal == ordinal)
        .ok_or_else(|| format!("source occurrence {ordinal} is absent"))
}

fn window_words(occurrence: &SourceOccurrence) -> Result<&[u32], String> {
    let start = FRAME_START
        .checked_mul(occurrence.field.alphabet)
        .ok_or_else(|| "the fixed frame start exceeded usize".to_owned())?;
    let end = FRAME_START
        .checked_add(FRAME_EXTENT)
        .and_then(|frame| frame.checked_mul(occurrence.field.alphabet))
        .filter(|end| *end <= occurrence.field.probability_words.len())
        .ok_or_else(|| "the fixed frame window exceeded its field".to_owned())?;
    Ok(&occurrence.field.probability_words[start..end])
}

fn constituent_read(constituent: &LiveConstituent) -> Result<ConstituentRead, String> {
    let mut open = 0usize;
    let mut ride = 0usize;
    let mut found = 0usize;
    for at in 0..constituent.boundaries().len() {
        match constituent.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open += 1,
            Some(LiveBoundaryTransition::Ride) => ride += 1,
            Some(LiveBoundaryTransition::Found) => found += 1,
            None => {}
        }
    }
    let paths = constituent
        .boundaries()
        .iter()
        .map(|boundary| boundary.paths().len())
        .sum();
    Ok(ConstituentRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        paths,
        exposed_pins: constituent.exposed().len(),
        open_boundaries: open,
        ride_boundaries: ride,
        found_boundaries: found,
        native_sha256: words_sha256(&constituent.native_words().map_err(debug)?),
    })
}

fn memory_read(memory: LiveMemory) -> MemoryRead {
    MemoryRead {
        standing_cells: memory.standing_cells,
        standing_constituents: memory.standing_constituents,
        constituent_cells: memory.constituent_cells,
        constituent_incidences: memory.constituent_incidences,
        constituent_pins: memory.constituent_pins,
        constituent_paths: memory.constituent_paths,
        live_lineages: memory.live_lineages,
    }
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is one resolving action")
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation {value} unexpectedly remained zero"))
}

fn next_id(at: usize) -> Result<EventCellId, String> {
    Ok(EventCellId::new(u64::try_from(at).map_err(debug)?))
}

fn hand_name(hand: IncidenceHand) -> &'static str {
    match hand {
        IncidenceHand::Against => "AGAINST",
        IncidenceHand::With => "WITH",
    }
}

fn bytes_to_bits(bytes: &[u8]) -> Vec<bool> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte & (1 << bit) != 0))
        .collect()
}

fn bits_to_bytes(bits: &[bool]) -> Result<Vec<u8>, String> {
    if bits.len() % 8 != 0 {
        return Err("one exact bit fiber is not octet-aligned".to_owned());
    }
    Ok(bits
        .chunks_exact(8)
        .map(|chunk| {
            chunk
                .iter()
                .copied()
                .enumerate()
                .fold(0u8, |byte, (bit, set)| byte | (u8::from(set) << bit))
        })
        .collect())
}

fn take<'a>(bytes: &'a [u8], cursor: &mut usize, extent: usize) -> Result<&'a [u8], String> {
    let end = cursor
        .checked_add(extent)
        .filter(|end| *end <= bytes.len())
        .ok_or_else(|| "one exact law read exceeded its boundary".to_owned())?;
    let value = &bytes[*cursor..end];
    *cursor = end;
    Ok(value)
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, String> {
    let row: [u8; 4] = take(bytes, cursor, 4)?
        .try_into()
        .map_err(|_| "one u32 law row is incomplete".to_owned())?;
    Ok(u32::from_le_bytes(row))
}

fn words_sha256(words: &[u32]) -> String {
    let mut hasher = Sha256::new();
    for word in words {
        hasher.update(word.to_le_bytes());
    }
    encode_digest(hasher.finalize().as_slice())
}

fn encode_digest(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn write_new_json(path: &Path, report: &Report) -> Result<(), String> {
    let mut bytes =
        serde_json::to_vec_pretty(report).map_err(|error| format!("report encodes: {error}"))?;
    bytes.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("{} opens as a new report: {error}", path.display()))?;
    file.write_all(&bytes)
        .map_err(|error| format!("{} writes completely: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", path.display()))
}

fn usage() -> String {
    "usage: eros_ctc_temporal_surface <SOURCE.json> <new-report.json>".to_owned()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
