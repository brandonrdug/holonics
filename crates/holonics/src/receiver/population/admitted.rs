//! **The admitted receivers: a response read against its request, a later human return read as an
//! observation** (HNN_FORMULA's source contract, item 7; campaign 5 on the population; #73, #148;
//! Lean `Compression/Landmark/Context/Composition.{stagedFace_nonneg, stagedFace_sum_one,
//! staged_chain_rule, staged_code}`, `Tree.{ktFace, ktFace_pos, ktFace_sum}`).
//!
//! [definition; agent-inferred] **The declared incidence** ([`Relation`]) is exterior codec
//! information: the curated source's incidence file, read at the notebook's boundary. A part opened
//! at letter tick `t` may reach one earlier part of the passage, the target, by one of the admitted
//! relations ([`RelationKind`]): a response (an agent part) reaches its request (a human part, the
//! source's `comparison-request`), and a later human part reaches the response it follows (an agent
//! part, `later-human-after-agent`). A relation whose target lies outside the passage is not
//! declared: that part's port is unheld. The data rules at history
//! (`13f8c734:docs/CONVERSATION_DATA.md`, "The primary distinction") fix what each receiver may do:
//! - **a response is observed conduct, not a gold target.** The request→response receiver predicts
//!   the response's cells, the population's own admitted future, and never scores the response as
//!   right or wrong;
//! - **a later human message is an observation, not approval.** The response→later-human receiver
//!   reads the human part conditioned on the response it follows as a **receipt only**
//!   ([`AdmittedEgg::with_receipt`]): its faces never enter the family's face, and nothing of the
//!   human return reaches the response's reading. It measures how much a human return is predicted
//!   by what it answers.
//!
//! [definition; agent-inferred] **The port: a response located on its request** (`compression::
//! landmark::context::spans`). While a part whose relation is held is open, its address across the
//! two ports is the longest suffix of its cells that recurs in the target's span followed by a byte,
//! the located continuation `(L, x̂)`: a reply that quotes its request is addressed by the request
//! itself, past the receiving tree's last `D` ticks.
//!
//! [definition; agent-inferred] **The copy stage** ([`CopyLaw`], [`CopyStage`]). At a tick whose
//! located continuation is at least the declared least length, the family factors the inner egg's
//! face `q_in` (the boundary egg, [`BoundaryEgg`]) through the stage map `σ_t(x) = copy` at
//! `x = x̂_t`, `miss` otherwise:
//!
//! ```text
//! q_t(x̂) = h_t(copy)                                    r_t(x̂) = 1
//! q_t(x)  = h_t(miss) · q_in(x)/(1 − q_in(x̂)),  x ≠ x̂    r_t(x) = q_in(x)/(1 − q_in(x̂))
//! h_t = (2 n_copy + 1, 2 n_miss + 1)/(2 n + 2)          the KT face of the partition's cell
//! cell = (min(⌊log₂ L⌋ − ⌊log₂ L_min⌋, λ − 1), clamp(⌊log₂(q_in(x̂)/(1 − q_in(x̂)))⌋, −κ, κ − 1))
//! ```
//!
//! the match length's dyadic class above the least (`λ` classes, the last absorbing) and the inner
//! egg's own odds of the located byte (`2κ` classes; none at `κ = 0`), so the copy is weighed against
//! what the inner egg already predicts. Elsewhere the face is `q_in`. `q_in(x̂) < 1` (the hazard's
//! KT face of a byte is below one), so the miss stage's conditioned face is a face.
//! [proved-derived; formal-checked] The stage map depends on the tick; the staged face is a face at
//! every tick (`stagedFace_nonneg`, `stagedFace_sum_one` at that tick's `σ_t`), and over the passage
//! the chain rule needs no fixed stage map (`staged_chain_rule`, `staged_code` with `σ = id` and the
//! stage face composed with `σ_t`): the family's code is the stage's code plus the conditioned code,
//! and at the ticks it reads the conditioned code is the inner egg's less `−log₂(1 − q_in(x̂))` on
//! each miss and all of `−log₂ q_in(x̂)` on each copy. The inner egg read alone is the port unheld,
//! so the receiver's value is exact: the inner egg's code on the same ticks against the family's.
//!
//! [definition; agent-inferred] **The incidence's code** ([`PointerReadout`]). The relation is
//! information the cells do not carry, so it is coded where it arrives, at the reading part's
//! letter, and charged beside the cells, per relation: whether a relation is held (a KT face per
//! section kind and the previous reading part's held state); when the previous reading part's was
//! held, whether the target is the same (a KT face per section kind: a response's further parts
//! answer one request); otherwise the target's rank `r` among the parts received on its port (`0`
//! the latest), its dyadic class `⌊log₂(r + 1)⌋` in unary (a KT face per level, forced where no
//! higher class is admissible) and its offset uniform over the admissible ranks of its class.
//!
//! [definition; agent-inferred] **Retention** (the source contract's item 7: the admitted future
//! family names what retention must keep). A target's span is held exactly while a declared
//! relation still reaches it (released when its last reading part closes), and the open reading
//! part's own cells while it is open: the ports the admitted receivers read, never a record of the
//! passage.
//!
//! [definition] The computational object is the helical pair interaction, read here as a receiver
//! that reads a response against its request. Of the winding guide's six general objects this owner
//! touches three: **faces and placement** (the admitted receivers, the located continuation placed on
//! the next tick, the staged face), the **tube** (a request's span to its response, a response's to
//! the human return) and the **tower thread** (the partition's dyadic classes restrict a length and
//! an odds). The helix, pair and cell holonomy stay attached through the inner egg's owners.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::{
    Act, BoundaryEgg, BoundaryReadout, Declaration, Family, Likelihood, PopulationError, Readout,
    Work, refuse,
};
use crate::compression::landmark::context::baseline::kt_probability;
use crate::compression::landmark::context::{Located, PassageCode, SectionChart, SpanReading};
use crate::ratio::Rat;

mod checkpoint;
pub use checkpoint::AdmittedStageCheckpointError;

/// The curated chart's human channel (`SectionChart::curated`: human, agent, tool).
pub const HUMAN: usize = 0;
/// The curated chart's agent channel.
pub const AGENT: usize = 1;

/// [definition] **An admitted relation's kind** (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RelationKind {
    /// A response (agent part) reaches its request (human part): `comparison-request`.
    Request,
    /// A later human part reaches the response it follows (agent part): `later-human-after-agent`.
    LaterHuman,
}

impl RelationKind {
    /// The kinds, in order.
    pub const ALL: [Self; 2] = [Self::Request, Self::LaterHuman];

    /// The kind's index in [`Self::ALL`].
    pub fn index(self) -> usize {
        self as usize
    }

    /// The reading part's channel and the target's.
    pub fn channels(self) -> (usize, usize) {
        match self {
            RelationKind::Request => (AGENT, HUMAN),
            RelationKind::LaterHuman => (HUMAN, AGENT),
        }
    }
}

/// [definition] **A declared relation** (module header): the reading part's letter tick, its kind,
/// and the target part's letter tick, earlier in the passage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Relation {
    pub letter: u64,
    pub kind: RelationKind,
    pub target: u64,
}

/// [definition; agent-inferred] **The copy stage's declared law** (module header): the least
/// located length it reads, its length classes `λ` and its odds classes on each side `κ`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CopyLaw {
    pub least: u64,
    pub lengths: u32,
    pub odds: u32,
}

impl CopyLaw {
    /// **Declare the law**; refused at a least length or a length class count of zero.
    pub fn new(least: u64, lengths: u32, odds: u32) -> Result<Self, PopulationError> {
        if least == 0 || lengths == 0 {
            return Err(refuse(
                "a copy stage's law",
                "it reads a located continuation at least one cell long, in at least one length class",
            ));
        }
        Ok(Self {
            least,
            lengths,
            odds,
        })
    }

    /// **The partition's cell** of a located continuation and the inner egg's face of its byte;
    /// none below the least length.
    pub fn cell(&self, length: u64, located: &Rat) -> Option<CopyCell> {
        if length < self.least {
            return None;
        }
        let above = length.ilog2() - self.least.ilog2();
        let odds = if self.odds == 0 {
            0
        } else {
            let bound = i64::from(self.odds);
            odds_class(located).clamp(-bound, bound - 1) as i32
        };
        Some(CopyCell {
            length: above.min(self.lengths - 1),
            odds,
        })
    }

    fn declaration(&self) -> Declaration {
        Declaration::new(
            "copy stage",
            vec![self.least, u64::from(self.lengths), u64::from(self.odds)],
        )
    }
}

/// [definition] **`⌊log₂(q/(1 − q))⌋`**, the odds class of a face `0 < q < 1`, exact.
pub fn odds_class(q: &Rat) -> i64 {
    let numerator = q.numer().magnitude();
    let rest: BigUint = q.denom().magnitude() - numerator;
    let guess = numerator.bits() as i64 - rest.bits() as i64;
    let at_least = |k: i64| {
        if k >= 0 {
            *numerator >= (&rest << k as usize)
        } else {
            (numerator << (-k) as usize) >= rest
        }
    };
    if at_least(guess) { guess } else { guess - 1 }
}

/// [definition] **A cell of the copy stage's partition**: the length class and the odds class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct CopyCell {
    pub length: u32,
    pub odds: i32,
}

/// [definition; agent-inferred] **A copy stage's readout** (module header): the ticks it read, on
/// the reading parts' bytes and at their closing letters, the copies among them, its staged faces'
/// and the inner egg's faces' products on the same ticks, and the staged code split by the chain
/// rule into the stage's faces and the conditioned faces. The face stage's staged faces are the
/// family's; a receipt stage's never enter it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StageReadout {
    pub kind: RelationKind,
    pub law: CopyLaw,
    pub ticks: [u64; 2],
    pub copies: u64,
    pub staged: [PassageCode; 2],
    pub inner: [PassageCode; 2],
    pub stage: PassageCode,
    pub conditioned: PassageCode,
    pub cells: usize,
}

/// [definition; agent-inferred] **A copy stage** (module header): its law, its readout and the KT
/// counts `[miss, copy]` per cell met, the only state it keeps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CopyStage {
    readout: StageReadout,
    counts: BTreeMap<CopyCell, [u64; 2]>,
}

impl CopyStage {
    /// A stage of a relation's kind under a law, nothing counted.
    pub fn new(kind: RelationKind, law: CopyLaw) -> Self {
        let empty = [PassageCode::new(); 2];
        Self {
            readout: StageReadout {
                kind,
                law,
                ticks: [0; 2],
                copies: 0,
                staged: empty,
                inner: empty,
                stage: PassageCode::new(),
                conditioned: PassageCode::new(),
                cells: 0,
            },
            counts: BTreeMap::new(),
        }
    }

    /// `[h(miss), h(copy)]` in a cell.
    fn face(&self, cell: CopyCell) -> [Rat; 2] {
        let counts = self.counts.get(&cell).copied().unwrap_or([0, 0]);
        let total = counts[0] + counts[1];
        [
            kt_probability(counts[0], total, 2),
            kt_probability(counts[1], total, 2),
        ]
    }

    /// The staged face of the whole chart from the inner face (the family's [`Family::face`]).
    fn restage(&self, face: &mut [Rat], located: Located) {
        let Some(cell) = self.readout.law.cell(located.length, &face[located.next]) else {
            return;
        };
        let [miss, copy] = self.face(cell);
        let scale = miss / (Rat::one() - &face[located.next]);
        for (class, entry) in face.iter_mut().enumerate() {
            *entry = if class == located.next {
                copy.clone()
            } else {
                &*entry * &scale
            };
        }
    }

    /// **Read one tick** (module header): the staged face of the arrived cell from the inner egg's
    /// face of the located byte and of the cell, then the stage counted; none below the least
    /// length.
    fn read(
        &mut self,
        located: Located,
        next: &Rat,
        arrived: &Rat,
        cell: usize,
        close: bool,
    ) -> Result<Option<Rat>, PopulationError> {
        let Some(partition) = self.readout.law.cell(located.length, next) else {
            return Ok(None);
        };
        let [miss, copy] = self.face(partition);
        let copied = cell == located.next;
        let (stage, conditioned) = if copied {
            (copy, Rat::one())
        } else {
            (miss, arrived / (Rat::one() - next))
        };
        let staged = &stage * &conditioned;
        let at = usize::from(close);
        let readout = &mut self.readout;
        readout.ticks[at] += 1;
        readout.staged[at].face(&staged)?;
        readout.inner[at].face(arrived)?;
        readout.stage.face(&stage)?;
        readout.conditioned.face(&conditioned)?;
        if copied {
            readout.copies += 1;
        }
        self.counts.entry(partition).or_insert([0, 0])[usize::from(copied)] += 1;
        readout.cells = self.counts.len();
        Ok(Some(staged))
    }

    /// The readout.
    pub fn readout(&self) -> &StageReadout {
        &self.readout
    }
}

/// [definition; agent-inferred] **The incidence's code on one relation** (module header): the
/// reading port's parts, those whose relation is held, and the product of the pointer's faces.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointerReadout {
    pub kind: RelationKind,
    pub parts: u64,
    pub held: u64,
    pub code: PassageCode,
}

/// The pointer's KT counts: held per section kind and the previous reading part's held state
/// (`[none, held]`), the same target as the previous reading part's per section kind (`[other,
/// same]`), and the rank class's unary levels (`[stop, continue]`); and the previous reading part's
/// target.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PointerCode {
    readout: PointerReadout,
    held: BTreeMap<(usize, bool), [u64; 2]>,
    same: BTreeMap<usize, [u64; 2]>,
    levels: Vec<[u64; 2]>,
    previous: Option<u64>,
}

/// A KT face of one side of a binary count, then the side counted.
fn kt_side(counts: &mut [u64; 2], side: usize) -> Rat {
    let face = kt_probability(counts[side], counts[0] + counts[1], 2);
    counts[side] += 1;
    face
}

impl PointerCode {
    fn new(kind: RelationKind) -> Self {
        Self {
            readout: PointerReadout {
                kind,
                parts: 0,
                held: 0,
                code: PassageCode::new(),
            },
            held: BTreeMap::new(),
            same: BTreeMap::new(),
            levels: Vec::new(),
            previous: None,
        }
    }

    /// **Code one reading part's pointer** at its letter (module header): none, or the target
    /// (its letter tick) with its rank among the `count` parts received on the target's port.
    fn read(
        &mut self,
        section_kind: usize,
        pointer: Option<(u64, u64, u64)>,
    ) -> Result<(), PopulationError> {
        self.readout.parts += 1;
        let previous = std::mem::replace(&mut self.previous, pointer.map(|(target, _, _)| target));
        let held = self
            .held
            .entry((section_kind, previous.is_some()))
            .or_insert([0, 0]);
        let face = kt_side(held, usize::from(pointer.is_some()));
        self.readout.code.face(&face)?;
        let Some((target, rank, count)) = pointer else {
            return Ok(());
        };
        self.readout.held += 1;
        if let Some(previous) = previous {
            let same = self.same.entry(section_kind).or_insert([0, 0]);
            let face = kt_side(same, usize::from(target == previous));
            self.readout.code.face(&face)?;
            if target == previous {
                return Ok(());
            }
        }
        let class = (rank + 1).ilog2() as usize;
        for level in 0..=class {
            // A higher class is admissible when its least rank, 2^(level+1) − 1, is below `count`.
            if (1u64 << (level + 1)) > count {
                break;
            }
            if self.levels.len() <= level {
                self.levels.resize(level + 1, [0, 0]);
            }
            let face = kt_side(&mut self.levels[level], usize::from(level < class));
            self.readout.code.face(&face)?;
        }
        let least = 1u64 << class;
        let offsets = least.min(count + 1 - least);
        if offsets > 1 {
            self.readout
                .code
                .face(&Rat::new(BigInt::one(), BigInt::from(offsets)))?;
        }
        Ok(())
    }
}

/// [definition; agent-inferred] **The admitted receivers' readout**: the inner egg's, each copy
/// stage's (the face stage first), each relation's pointer code, and the spans held now and at the
/// widest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmittedReadout {
    pub inner: BoundaryReadout,
    pub stages: Vec<StageReadout>,
    pub pointers: Vec<PointerReadout>,
    pub retained: usize,
    pub retained_cells: usize,
    pub widest_cells: usize,
    /// The open response's request operands, when that request relation is held.
    pub request_provenance: Option<RequestFaceProvenance>,
}

/// Exact operands identifying the currently open request-conditioned response face.
/// This is a current readout, not retained event history, and contains no request text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RequestFaceProvenance {
    pub response_letter_tick: u64,
    pub request_target_tick: u64,
    pub target_span_cells: usize,
    pub located_length: Option<u64>,
    pub next_byte: Option<usize>,
    pub copy_law: CopyLaw,
    pub copy_cell: Option<CopyCell>,
}

/// A target's span while a relation still reaches it.
#[derive(Clone, Debug)]
struct Span {
    channel: usize,
    ordinal: u64,
    cells: Vec<usize>,
    remaining: u64,
}

/// The open part: its letter tick, its channel, its held relation and its address on the target.
#[derive(Clone, Debug)]
struct OpenPart {
    letter: u64,
    relation: Option<(RelationKind, u64)>,
    reading: SpanReading,
}

/// [definition; agent-inferred] **The admitted receivers' egg** (module header): the inner boundary
/// egg composed with the request's span through the copy stage, the later human's receipt beside it.
#[derive(Clone)]
pub struct AdmittedEgg {
    label: String,
    description: u64,
    chart: SectionChart,
    inner: BoundaryEgg,
    relations: Vec<Relation>,
    next: usize,
    stage: CopyStage,
    receipts: Vec<CopyStage>,
    pointers: Vec<PointerCode>,
    spans: BTreeMap<u64, Span>,
    targets: BTreeMap<u64, u64>,
    open: Option<OpenPart>,
    parts: Vec<u64>,
    tick: u64,
    passage: PassageCode,
    held: usize,
    widest: usize,
}

impl AdmittedEgg {
    /// **Compose** the inner egg with the declared relations through the request's copy stage.
    /// Refused unless the chart holds the human and agent channels, the relations are in letter
    /// order with one relation a part, and each target lies before its reading part.
    pub fn new(
        label: String,
        description: u64,
        inner: BoundaryEgg,
        chart: SectionChart,
        relations: Vec<Relation>,
        law: CopyLaw,
    ) -> Result<Self, PopulationError> {
        if chart.channels() <= AGENT || chart.alphabet() != inner.alphabet() {
            return Err(refuse(
                "the admitted receivers",
                "the inner egg reads the chart, whose channels hold the human and agent ports",
            ));
        }
        if relations
            .windows(2)
            .any(|pair| pair[0].letter >= pair[1].letter)
            || relations
                .iter()
                .any(|relation| relation.target >= relation.letter)
        {
            return Err(refuse(
                "the admitted receivers' incidence",
                "one relation a part, in letter order, each target before its reading part",
            ));
        }
        let mut targets = BTreeMap::new();
        for relation in &relations {
            *targets.entry(relation.target).or_insert(0) += 1;
        }
        Ok(Self {
            label,
            description,
            chart,
            inner,
            relations,
            next: 0,
            stage: CopyStage::new(RelationKind::Request, law),
            receipts: Vec::new(),
            pointers: RelationKind::ALL
                .iter()
                .map(|&kind| PointerCode::new(kind))
                .collect(),
            spans: BTreeMap::new(),
            targets,
            open: None,
            parts: vec![0; chart.channels()],
            tick: 0,
            passage: PassageCode::new(),
            held: 0,
            widest: 0,
        })
    }

    /// **Read a receipt stage beside the face** (module header): a relation's copy stage whose
    /// faces are reported and never enter the family's face (the response→later-human receiver).
    pub fn with_receipt(mut self, kind: RelationKind, law: CopyLaw) -> Self {
        self.receipts.push(CopyStage::new(kind, law));
        self
    }

    /// The inner egg (its own likelihood is the port unheld).
    pub fn inner(&self) -> &BoundaryEgg {
        &self.inner
    }

    /// [definition; agent-inferred] **A branch at the present incidence**: a copy of this standing
    /// that declares only the relations whose reading part has opened. A relation whose letter lies
    /// ahead is the recorded future's exterior codec information, which a release branched from the
    /// present must not read: the population's admission refuses a byte at a declared future letter
    /// or target tick, so a branch carrying them would stop a release at the recorded part's length
    /// (F0's acceptance run, its dry run on F4's passage: 8 of 32 releases). Withholding them moves
    /// no face: a face reads only the open part's relation, whose target keeps its span, and a
    /// withheld relation's count on a held target only held that span longer.
    pub fn branch_at_present(&self) -> Self {
        let mut branch = self.clone();
        let withheld = branch.relations.split_off(branch.next);
        for relation in withheld {
            if let Some(count) = branch.targets.get_mut(&relation.target) {
                *count -= 1;
                if *count == 0 {
                    branch.targets.remove(&relation.target);
                }
            }
            if let Some(span) = branch.spans.get_mut(&relation.target) {
                span.remaining -= 1;
                if span.remaining == 0 {
                    branch.held -= span.cells.len();
                    branch.spans.remove(&relation.target);
                }
            }
        }
        branch
    }

    /// Check a request/response incidence while both its target and reading part are still ahead
    /// of the clock. This does not create a span early: `open_part` creates and retains that span
    /// when the target letter is actually received.
    fn validate_planned_relation(&self, relation: Relation) -> Result<(), PopulationError> {
        if relation.target >= relation.letter || relation.target < self.tick {
            return Err(refuse(
                "a planned admitted relation",
                "its target is at the current or a future part and precedes its reading part",
            ));
        }
        if self
            .relations
            .iter()
            .any(|old| old.letter == relation.letter)
        {
            return Err(refuse(
                "a planned admitted relation",
                "there is at most one relation on each reading part",
            ));
        }
        let insertion = self
            .relations
            .partition_point(|old| old.letter < relation.letter);
        if insertion < self.next {
            return Err(refuse(
                "a planned admitted relation",
                "relations remain in increasing letter order without changing a passed part",
            ));
        }
        Ok(())
    }

    fn insert_planned_relation(&mut self, relation: Relation) {
        let insertion = self
            .relations
            .partition_point(|old| old.letter < relation.letter);
        self.relations.insert(insertion, relation);
        if insertion < self.next {
            self.next += 1;
        }
        *self.targets.entry(relation.target).or_insert(0) += 1;
    }

    /// The open part's located continuation and its relation's kind, when a relation is held.
    fn located(&self) -> Option<(RelationKind, Located)> {
        let open = self.open.as_ref()?;
        let (kind, target) = open.relation?;
        let span = &self.spans.get(&target)?.cells;
        open.reading.located(span).map(|located| (kind, located))
    }

    fn request_provenance(&self) -> Option<RequestFaceProvenance> {
        let open = self.open.as_ref()?;
        let (kind, target) = open.relation?;
        if kind != RelationKind::Request {
            return None;
        }
        let span = self.spans.get(&target)?;
        let located = open.reading.located(&span.cells);
        let copy_cell = located.and_then(|located| {
            let q = self.inner.probability(located.next).ok()?;
            self.stage.readout.law.cell(located.length, &q)
        });
        Some(RequestFaceProvenance {
            response_letter_tick: open.letter,
            request_target_tick: target,
            target_span_cells: span.cells.len(),
            located_length: located.map(|value| value.length),
            next_byte: located.map(|value| value.next),
            copy_law: self.stage.readout.law,
            copy_cell,
        })
    }

    /// The least length any stage of a kind reads.
    fn least(&self, kind: RelationKind) -> Option<u64> {
        std::iter::once(&self.stage)
            .chain(&self.receipts)
            .filter(|stage| stage.readout.kind == kind)
            .map(|stage| stage.readout.law.least)
            .min()
    }

    /// **Close the open part**: its relation's target is released once no relation still reaches
    /// it.
    fn close(&mut self) {
        if let Some(OpenPart {
            relation: Some((_, target)),
            ..
        }) = self.open.take()
            && let Some(span) = self.spans.get_mut(&target)
        {
            span.remaining -= 1;
            if span.remaining == 0 {
                self.held -= span.cells.len();
                self.spans.remove(&target);
            }
        }
    }

    /// **Open a part at its letter**: the pointer coded on each relation it reads, its relation
    /// held, and its span retained when a relation reaches it.
    fn open_part(
        &mut self,
        letter: u64,
        channel: usize,
        section_kind: usize,
    ) -> Result<(), PopulationError> {
        let declared = self
            .relations
            .get(self.next)
            .filter(|relation| relation.letter == letter)
            .copied();
        let mut relation = None;
        for kind in RelationKind::ALL {
            let (reader, target_channel) = kind.channels();
            if reader != channel {
                continue;
            }
            let rank = match declared.filter(|declared| declared.kind == kind) {
                Some(declared) => {
                    let span = self
                        .spans
                        .get(&declared.target)
                        .filter(|span| span.channel == target_channel)
                        .ok_or_else(|| {
                            refuse(
                                "an admitted relation",
                                "its target is an earlier part on the target's port",
                            )
                        })?;
                    let count = self.parts[target_channel];
                    relation = Some((kind, declared.target));
                    Some((declared.target, count - 1 - span.ordinal, count))
                }
                None => None,
            };
            self.pointers[kind.index()].read(section_kind, rank)?;
        }
        if declared.is_some() {
            if relation.is_none() {
                return Err(refuse(
                    "an admitted relation",
                    "its letter opens a part on the relation's reading port",
                ));
            }
            self.next += 1;
        }
        if let Some(&remaining) = self.targets.get(&letter) {
            self.spans.insert(
                letter,
                Span {
                    channel,
                    ordinal: self.parts[channel],
                    cells: Vec::new(),
                    remaining,
                },
            );
        }
        self.parts[channel] += 1;
        self.open = Some(OpenPart {
            letter,
            relation,
            reading: SpanReading::new(),
        });
        Ok(())
    }

    /// **Read one byte of the open part**: its address on the target, and its retained span.
    fn read_byte(&mut self, cell: usize) {
        let Some(open) = self.open.as_mut() else {
            return;
        };
        if let Some((_, target)) = open.relation
            && let Some(span) = self.spans.get(&target)
        {
            open.reading.read(&span.cells, cell);
        }
        if let Some(span) = self.spans.get_mut(&open.letter) {
            span.cells.push(cell);
            self.held += 1;
        }
        self.widest = self.widest.max(self.held + open.reading.cells());
    }
}

impl Family for AdmittedEgg {
    fn admitted_checkpoint(&self) -> Option<Result<Vec<u8>, AdmittedStageCheckpointError>> {
        Some(self.encode_checkpoint())
    }

    fn admitted_received_cells(&self) -> Option<u64> {
        match self.inner.likelihood() {
            Likelihood::Enclosed(code) if code.factors() == self.tick => Some(code.factors()),
            Likelihood::Exact(_) => None,
            Likelihood::Enclosed(_) => None,
        }
    }

    fn branch_future(&self) -> Option<Box<dyn Family>> {
        Some(Box::new(self.clone()))
    }

    fn owns_planned_relation(&self) -> bool {
        true
    }

    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.inner.alphabet()
    }

    fn description(&self) -> u64 {
        self.description
    }

    /// The inner egg's face, restaged where the request's copy stage reads the next tick.
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let mut face = self.inner.face()?;
        if let Some((RelationKind::Request, located)) = self.located() {
            self.stage.restage(&mut face, located);
        }
        Ok(face)
    }

    /// **Receive one cell** (module header): the inner egg's face of the located byte read before
    /// the deposit, the inner egg's face of the cell, each stage that reads the tick, the face
    /// stage's staged face the family's; then the part advances.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let located = self.located().filter(|&(kind, located)| {
            self.least(kind)
                .is_some_and(|least| located.length >= least)
        });
        let next = match located {
            Some((_, located)) => Some(self.inner.probability(located.next)?),
            None => None,
        };
        let arrived = self.inner.receive(cell)?;
        if arrived.is_zero() {
            // The chart's pin: a byte before any section; nothing moves.
            return Ok(arrived);
        }
        let section = self.chart.section(cell);
        let close = section.is_some();
        let mut face = arrived.clone();
        if let (Some((kind, located)), Some(next)) = (located, next) {
            if kind == self.stage.readout.kind
                && let Some(staged) = self.stage.read(located, &next, &arrived, cell, close)?
            {
                face = staged;
            }
            for receipt in &mut self.receipts {
                if receipt.readout.kind == kind {
                    receipt.read(located, &next, &arrived, cell, close)?;
                }
            }
        }
        self.passage.face(&face)?;
        match section {
            Some(section) => {
                self.close();
                self.open_part(self.tick, section.channel, section.kind)?;
            }
            None => self.read_byte(cell),
        }
        self.tick += 1;
        Ok(face)
    }

    /// The inner egg admits the passage, and every declared relation within it opens on a letter
    /// of its reading port whose target is a letter of the target's port (held, when earlier).
    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        self.inner.admits(cells)?;
        let end = self.tick + cells.len() as u64;
        let letter_on = |tick: u64, channel: usize| -> bool {
            if tick >= self.tick {
                cells
                    .get((tick - self.tick) as usize)
                    .and_then(|&cell| self.chart.section(cell))
                    .is_some_and(|section| section.channel == channel)
            } else {
                self.spans
                    .get(&tick)
                    .is_some_and(|span| span.channel == channel)
            }
        };
        for relation in &self.relations[self.next..] {
            let (reader, target) = relation.kind.channels();
            if (self.tick..end).contains(&relation.target) && !letter_on(relation.target, target) {
                return Err(refuse(
                    "a planned admitted relation's target",
                    "it opens as a letter on the target port before any state changes",
                ));
            }
            if (self.tick..end).contains(&relation.letter) && !letter_on(relation.letter, reader) {
                return Err(refuse(
                    "a planned admitted relation's reading part",
                    "it opens as a letter on the reading port before any state changes",
                ));
            }
        }
        for relation in &self.relations[self.next..] {
            if relation.letter >= end {
                break;
            }
            let (reader, target) = relation.kind.channels();
            if relation.letter < self.tick
                || !letter_on(relation.letter, reader)
                || !letter_on(relation.target, target)
            {
                return Err(refuse(
                    "an admitted relation of a passage",
                    "its letter opens a part on its reading port and its target a part on the target's port",
                ));
            }
        }
        Ok(())
    }

    fn validate_planned_relation(&self, relation: Relation) -> Result<(), PopulationError> {
        self.validate_planned_relation(relation)
    }

    fn commit_planned_relation(&mut self, relation: Relation) {
        self.insert_planned_relation(relation);
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    fn readout(&self) -> Readout<'_> {
        Readout::Admitted(Box::new(AdmittedReadout {
            inner: self.inner.stages().clone(),
            stages: std::iter::once(&self.stage)
                .chain(&self.receipts)
                .map(|stage| stage.readout.clone())
                .collect(),
            pointers: self
                .pointers
                .iter()
                .map(|pointer| pointer.readout.clone())
                .collect(),
            retained: self.spans.len(),
            retained_cells: self.held,
            widest_cells: self.widest,
            request_provenance: self.request_provenance(),
        }))
    }

    /// The copy stage's law, built on the inner egg's declaration (the receipts are not the
    /// family's).
    fn declaration(&self) -> Declaration {
        Declaration::new("admitted receivers", Vec::new()).with(vec![
            self.stage.readout.law.declaration(),
            self.inner.declaration(),
        ])
    }

    /// The inner egg's work, and every stage and pointer counted.
    fn work(&self) -> Work {
        let mut work = self.inner.work();
        let stages: u64 = std::iter::once(&self.stage)
            .chain(&self.receipts)
            .map(|stage| stage.readout.ticks.iter().sum::<u64>())
            .sum();
        let pointers: u64 = self
            .pointers
            .iter()
            .map(|pointer| pointer.readout.parts)
            .sum();
        work.add(Act::Count, stages + pointers);
        work
    }
}

#[cfg(test)]
#[path = "admitted_tests.rs"]
mod tests;
