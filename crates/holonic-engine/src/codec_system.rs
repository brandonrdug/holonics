//! A [`RecoveredCodec`](crate::codec_recovery::RecoveredCodec) read as an
//! [`ObservedSystem`](crate::receiver_exact_compression::ObservedSystem), and the independent
//! cross-check that buys.
//!
//! ## Why this seam is worth wiring
//!
//! Two organs in this crate compute the same quantity by different routes and until now had no
//! common carrier to be compared over:
//!
//! ```text
//!   codec_recovery::RecoveredCodec::shortest_separating_input
//!       forward breadth-first reachability on a hand-built joint automaton with a
//!       Synced / Pending / diverged species, over two codecs at once
//!
//!   receiver_exact_compression::compress
//!       Moore partition refinement to a fixed point over one item population,
//!       then a breadth-first exhibition of the shortest word per collapsed pair
//! ```
//!
//! Point the second at the disjoint union of two codecs' conduct states and the pair
//! `(rest of the left codec, rest of the right codec)` carries exactly the quantity the first
//! returns. `CLAUDE.md` §8: *"Where an independent implementation exists, state both costs"* — and
//! before that, state whether they agree. [`cross_check`] does, and returns every disagreement as
//! the material that produced it: the input and both segmentations, never a rate.
//!
//! ## The state of a codec is not its symbol class
//!
//! `blueprint/THE_ASSEMBLY.md` step 3 says the recovered codec is *"a finite machine whose states
//! are `SymbolClass` and whose inputs are symbols."* **That reading is degenerate and this module
//! does not use it.** Under it the successor map is
//!
//! ```text
//!   successor(previous_class, symbol) = class_of(symbol)
//! ```
//!
//! which does not read its own state, so every item carries the identical successor signature and
//! the collapsed population is empty by construction. That last sentence is a theorem about the
//! declaration and asserting it in a test would be an argument written in Rust syntax rather than a
//! measurement, so the refutation is taken from the material instead:
//! `two_states_of_one_symbol_class_are_separated_by_a_word_segment_itself_exhibits` measures the
//! reachable state population against the class population on four really recovered codecs, and
//! exhibits two states of **one** symbol class together with the word after which
//! [`RecoveredCodec::segment`](crate::codec_recovery::RecoveredCodec::segment) — not this adapter —
//! returns something different from each. A machine whose states were symbol classes could not
//! carry that pair.
//!
//! The correction is that a codec is a **transducer**, not an acceptor. Reading
//! [`RecoveredCodec::segment`](crate::codec_recovery::RecoveredCodec::segment) directly, the loop
//! carries two things across a symbol — the previous class *and* whether a token is currently
//! held open — and the second is what a boundary decision is spent on:
//!
//! ```text
//!   cut  = previous is none  or  boundary[previous][class] is Cut
//!   a held token is pushed   iff  cut and the token is open
//!   the token is open after  iff  emits(class) or (open before and not cut)
//! ```
//!
//! ## The observable, derived from `segment` and not from the automaton it is checked against
//!
//! A segmentation of an input is a split of the **emitted** character stream. Two codecs over the
//! same classes and the same emission emit the same characters in the same order, so their returns
//! differ exactly when the split points differ, and a split is named by one bit per emitted
//! character: *does this character open a token, or extend the one already open?* From the loop
//! above that bit is
//!
//! ```text
//!   opens a token  iff  cut or the token was not open
//! ```
//!
//! so the per-step return of the machine is [`StepReturn`] — `Silent` on a dropped symbol,
//! `OpenedToken` or `ExtendedToken` on an emitted one — and folding it into the state makes the
//! machine a Moore machine whose output equivalence **is** segmentation equality.
//!
//! **This re-timing is load-bearing and the naive alternative is wrong.** Observing *"a token was
//! pushed at this step"* over-distinguishes: a codec that holds a token across a run of dropped
//! symbols and pushes it later returns the same tokens as one that pushed it immediately. That is
//! precisely the case `shortest_separating_input`'s `Pending` species exists to carry, it is
//! reachable on real recovered codecs — the tokenizer's whitespace gauge produces it — and an
//! adapter built on the push event would manufacture disagreements that are its own fault rather
//! than either organ's.
//!
//! ## What agrees, and what only happens to agree
//!
//! The quantity the two organs both compute is the **length** of the shortest separating input.
//! Which of several equally short words is returned is a tie-break, and it is implementation-local:
//! both enumerate symbol classes in index order and write a word with each class's least member, so
//! on the fixtures below the strings agree too. That agreement is contingent, not structural —
//! declaring [`ObservedSystem::inputs`] in the reverse order leaves every length equal and makes the
//! words differ, both still separating. [`SeparationSpecies::TieBrokenDifferently`] exists so that
//! outcome is reported as a tie rather than mistaken for a disagreement about the quantity, and
//! [`ReversedInputOrder`] is a declared carrier that produces it on committed material rather than a
//! mutation that has to be applied by hand.
//!
//! ## The declared wrong readings, and why the cross-check would otherwise prove nothing
//!
//! The two production routes are **specification-equivalent**: two codecs over one alphabet and one
//! emission emit the same characters in the same order, a segmentation is one bit per emitted
//! character, and both routes compute that bit. So [`cross_check`] returns an empty
//! [`SeparationCrossCheck::disagreements`] for every well-formed input, and on 2026-08-08 an
//! adversarial review confirmed the consequence: deleting the disagreement machinery outright —
//! `disagreements: Vec::new()`, dropping the `NerodeWordDoesNotSeparate` detection, or
//! `agrees() -> true` — passed the whole suite and a 49,152-pair probe. `CLAUDE.md` §8: *"A law that
//! returns zero proves nothing about itself... add a declared control that does, and make the grade
//! require it to return non-zero."*
//!
//! So the cross-check is taken over a **plugged** carrier and a **plugged** joint reading, and three
//! deliberately wrong readings are declared here, each wrong in one named way:
//!
//! | reading | what it observes | how it is wrong |
//! |---|---|---|
//! | [`PushEventSystem`] / [`ThePushEventAutomaton`] | *a completed token left the machine at this step* | over-distinguishes: a codec that holds a token across a dropped symbol and pushes it later returns the same tokens as one that pushed it immediately |
//! | [`ReversedInputOrder`] | the correct bit, over inputs declared in the reverse order | right about the quantity, different about which of two equally short words it names |
//! | [`CodecIndexReceiver`] | the correct bits **plus which codec it is looking at** | an absolute frame: a receiver-visible coordinate promoted into an invariant |
//!
//! Each returns a non-empty disagreement population with its species named and its word exhibited,
//! and between them all six species of [`SeparationSpecies`] are produced on committed material.
//! The agreeing controls stand beside them, so both a zero and a non-zero return are exercised.
//!
//! ## What is deliberately not exposed
//!
//! The receiver family is two receivers and both are functions of [`StepReturn`] alone:
//!
//! - `ReceiverId(0)` — did this step put a character into the token stream. Emission is shared
//!   across a comparable population, so this receiver **provably cannot** separate two codecs. It
//!   is declared anyway, so that ablation has something to remove that is not the answer.
//! - `ReceiverId(1)` — did that character open a token.
//!
//! A receiver returning the internal `token_open` flag would be finer than segmentation equality
//! and would break the correspondence above. `Observation` is documented in its own module as
//! *"an opaque exact token — never a magnitude"*; nothing here orders, sums, or thresholds one.
//! There is no score, weight, bias, gate, or float in this file.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::codec_recovery::{Boundary, Emission, RecoveredCodec, RecoveryError, SymbolClass};
use crate::receiver_exact_compression::{
    compress, InputId, ItemId, Observation, ObservedSystem, ReceiverExactCompression, ReceiverId,
};

/// The name a [`SeparationCrossCheck`] writes onto itself, so a return read back from octets can be
/// checked against what produced it rather than assumed.
pub const CROSS_CHECK_SCHEMA: &str = "holonic-engine.codec-separation-cross-check.v1";

/// What one step of a recovered codec put into the token stream.
///
/// This is the machine's return, not its internal state, and it is what the declared receivers
/// read. An opaque exact token in three species — never a magnitude, never ordered by one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum StepReturn {
    /// The step read a symbol of a `Drop` class, or no symbol has been read yet. No character
    /// reached the token stream, so nothing about the split is said here.
    Silent,
    /// The step's character opened a token.
    OpenedToken,
    /// The step's character extended the token already open.
    ExtendedToken,
}

/// One state of a recovered codec's segmentation conduct.
///
/// `codec` names which member of a declared population this state belongs to, which is what makes
/// a joint system a disjoint union rather than a product.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CodecState {
    pub codec: usize,
    /// The class of the symbol just read. `None` only at rest, before any symbol.
    pub previous: Option<SymbolClass>,
    /// Whether a token is currently held open. Internal; no receiver reads it.
    pub token_open: bool,
    /// What the step that produced this state returned.
    pub last: StepReturn,
}

/// Why a codec population could not be adapted.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AdaptationError {
    #[error("an empty codec population carries no machine to observe")]
    NoCodecs,
    #[error("a recovered codec with no symbol classes admits no input")]
    NoClasses,
    #[error("codec {codec} declares a {rows}x{columns} boundary over {classes} classes")]
    MalformedBoundary {
        codec: usize,
        rows: usize,
        columns: usize,
        classes: usize,
    },
    #[error("a cross-check needs a carrier of exactly two codecs; this one carries {population}")]
    NotAJointCarrier { population: usize },
    #[error(transparent)]
    Recovery(#[from] RecoveryError),
}

/// The one place a codec population is admitted or refused, shared by every carrier below.
///
/// Both readings must refuse the same populations or a cross-check between them is comparing organs
/// that disagree about what is answerable, so the check is written once and taken by all of them —
/// including [`RecoveredCodec::shortest_separating_input`], whose own
/// [`RecoveryError::MalformedBoundary`] refusal exists for this reason.
fn admit(codecs: &[&RecoveredCodec]) -> Result<usize, AdaptationError> {
    let Some(first) = codecs.first() else {
        return Err(AdaptationError::NoCodecs);
    };
    let classes = first.classes.len();
    if classes == 0 {
        return Err(AdaptationError::NoClasses);
    }
    for (position, codec) in codecs.iter().enumerate() {
        if codec.classes != first.classes || codec.emission != first.emission {
            return Err(RecoveryError::IncomparableCodecs.into());
        }
        let columns = codec.boundary.first().map_or(0, Vec::len);
        if codec.boundary.len() != classes || codec.boundary.iter().any(|row| row.len() != classes) {
            return Err(AdaptationError::MalformedBoundary {
                codec: position,
                rows: codec.boundary.len(),
                columns,
                classes,
            });
        }
    }
    Ok(classes)
}

/// Write a word of class indices over the recovered alphabet, with each class's least member — the
/// canonical witness [`RecoveredCodec::shortest_separating_input`] writes its own answer with.
fn write_classes(codec: &RecoveredCodec, word: &[usize]) -> Result<String, AdaptationError> {
    word.iter()
        .map(|class| {
            codec
                .class_representative(SymbolClass(u32::try_from(*class).unwrap_or(u32::MAX)))
                .ok_or(AdaptationError::NoClasses)
        })
        .collect()
}

/// A population of recovered codecs over one set of symbol classes, read as an [`ObservedSystem`].
///
/// One codec is the minimization carrier; two is the joint carrier the cross-check runs on. The
/// items are the **reachable** conduct states, so the returned [`Partition`] is a statement about
/// states the machine can actually be in.
///
/// [`Partition`]: crate::receiver_exact_compression::Partition
#[derive(Clone, Debug)]
pub struct CodecSystem<'a> {
    codecs: Vec<&'a RecoveredCodec>,
    classes: usize,
    states: Vec<CodecState>,
    index: BTreeMap<CodecState, ItemId>,
    rest: Vec<ItemId>,
}

impl<'a> CodecSystem<'a> {
    /// One codec, read as the machine whose Nerode congruence is its state minimization.
    pub fn new(codec: &'a RecoveredCodec) -> Result<Self, AdaptationError> {
        Self::joint(&[codec])
    }

    /// A comparable population, read as one machine on a disjoint state space.
    ///
    /// Refuses with the same [`RecoveryError::IncomparableCodecs`] that
    /// [`RecoveredCodec::shortest_separating_input`] refuses with, so the two organs agree on what
    /// they will not answer as well as on what they will.
    pub fn joint(codecs: &[&'a RecoveredCodec]) -> Result<Self, AdaptationError> {
        let classes = admit(codecs)?;

        let codecs: Vec<&'a RecoveredCodec> = codecs.to_vec();
        let rest_states: Vec<CodecState> = (0..codecs.len())
            .map(|codec| CodecState {
                codec,
                previous: None,
                token_open: false,
                last: StepReturn::Silent,
            })
            .collect();

        // Reachability, so `items()` names states the machine can be in and nothing else.
        let mut reached: BTreeSet<CodecState> = rest_states.iter().copied().collect();
        let mut frontier: VecDeque<CodecState> = rest_states.iter().copied().collect();
        while let Some(state) = frontier.pop_front() {
            for class in 0..classes {
                let next = step(&codecs, state, class);
                if reached.insert(next) {
                    frontier.push_back(next);
                }
            }
        }

        let states: Vec<CodecState> = reached.into_iter().collect();
        let index: BTreeMap<CodecState, ItemId> = states
            .iter()
            .enumerate()
            .map(|(position, state)| (*state, ItemId(position as u64)))
            .collect();
        let rest = rest_states
            .iter()
            .map(|state| index[state])
            .collect::<Vec<ItemId>>();

        Ok(Self {
            codecs,
            classes,
            states,
            index,
            rest,
        })
    }

    /// How many codecs this system carries.
    pub fn population(&self) -> usize {
        self.codecs.len()
    }

    /// The reachable conduct states, in the canonical order that indexes [`ItemId`].
    pub fn states(&self) -> &[CodecState] {
        &self.states
    }

    /// The state an item names.
    pub fn state_of(&self, item: ItemId) -> Option<CodecState> {
        self.states.get(item.0 as usize).copied()
    }

    /// The item a state names.
    pub fn item_of(&self, state: CodecState) -> Option<ItemId> {
        self.index.get(&state).copied()
    }

    /// The item of one codec's state before any symbol has been read.
    pub fn rest_state(&self, codec: usize) -> Option<ItemId> {
        self.rest.get(codec).copied()
    }

    /// The input naming a class, in the order [`ObservedSystem::inputs`] declares.
    pub fn input_of(&self, class: SymbolClass) -> Option<InputId> {
        ((class.0 as usize) < self.classes).then(|| InputId(u64::from(class.0)))
    }

    /// Write a word of inputs as an actual string over the recovered alphabet, using each class's
    /// least member — the same canonical witness
    /// [`RecoveredCodec::shortest_separating_input`] writes its answer with.
    pub fn word_string(&self, word: &[InputId]) -> Result<String, AdaptationError> {
        let classes: Vec<usize> = word
            .iter()
            .map(|input| usize::try_from(input.0).unwrap_or(usize::MAX))
            .collect();
        write_classes(self.codecs[0], &classes)
    }
}

/// One step of the recovered codec, taken from
/// [`RecoveredCodec::segment`](crate::codec_recovery::RecoveredCodec::segment)'s own loop.
fn step(codecs: &[&RecoveredCodec], state: CodecState, class: usize) -> CodecState {
    let codec = codecs[state.codec];
    let cut = match state.previous {
        None => true,
        Some(before) => codec.boundary[before.0 as usize][class] == Boundary::Cut,
    };
    let emits = codec.emission[class] == Emission::Emit;
    let opens = cut || !state.token_open;
    CodecState {
        codec: state.codec,
        previous: Some(SymbolClass(class as u32)),
        token_open: emits || (state.token_open && !cut),
        last: if !emits {
            StepReturn::Silent
        } else if opens {
            StepReturn::OpenedToken
        } else {
            StepReturn::ExtendedToken
        },
    }
}

impl ObservedSystem for CodecSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        (0..self.states.len())
            .map(|position| ItemId(position as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1)]
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.classes)
            .map(|class| InputId(class as u64))
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let state = self
            .state_of(item)
            .expect("an observation is taken of an item of this system");
        match receiver {
            // Did a character reach the token stream. Blind to the boundary by construction.
            ReceiverId(0) => Observation(u64::from(state.last != StepReturn::Silent)),
            // Did that character open a token. The whole of what a segmentation says.
            _ => Observation(u64::from(state.last == StepReturn::OpenedToken)),
        }
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let state = self.state_of(item)?;
        let class = usize::try_from(input.0).ok()?;
        if class >= self.classes {
            return None;
        }
        self.item_of(step(&self.codecs, state, class))
    }
}

// -------------------------------------------------------------------------------------------
// The two plug points of the cross-check
// -------------------------------------------------------------------------------------------

/// A carrier the Nerode side of the cross-check can run on: two codecs read as one observed
/// system, with the two rest items named and a way to write a word of its own inputs.
///
/// This is a plug point rather than a fixed call because a cross-check whose two sides are
/// specification-equivalent can never return a disagreement, and a law that returns zero proves
/// nothing about itself. The declared wrong readings below occupy this trait so the disagreement
/// population is exercised non-empty on committed material.
pub trait JointCarrier {
    /// The carrier, as the population [`compress`] runs on.
    fn observed(&self) -> &dyn ObservedSystem;
    /// How many codecs this carrier holds.
    fn population(&self) -> usize;
    /// The two codecs' items before any symbol, or `None` when this carrier does not hold two.
    fn rest_pair(&self) -> Option<(ItemId, ItemId)>;
    /// A word of this carrier's inputs, written over the recovered alphabet.
    fn write_word(&self, word: &[InputId]) -> Result<String, AdaptationError>;
    /// What this carrier observes, named. Carried onto the return so a cross-check says which two
    /// readings it compared rather than leaving the reader to assume the production pair.
    fn reading(&self) -> &'static str;
}

impl JointCarrier for CodecSystem<'_> {
    fn observed(&self) -> &dyn ObservedSystem {
        self
    }

    fn population(&self) -> usize {
        self.codecs.len()
    }

    fn rest_pair(&self) -> Option<(ItemId, ItemId)> {
        (self.rest.len() == 2).then(|| (self.rest[0], self.rest[1]))
    }

    fn write_word(&self, word: &[InputId]) -> Result<String, AdaptationError> {
        self.word_string(word)
    }

    fn reading(&self) -> &'static str {
        "segmentation-opening"
    }
}

/// A route to *the shortest input separating two codecs* that is not a congruence over a carrier.
///
/// [`TheJointAutomaton`] is the production one. [`ThePushEventAutomaton`] is the declared wrong one,
/// and it exists so that [`SeparationSpecies::JointAutomatonWordDoesNotSeparate`] is a refusal that
/// can fire rather than a name in an enum.
pub trait JointReading {
    fn reading(&self) -> &'static str;
    fn shortest_separating_input(
        &self,
        left: &RecoveredCodec,
        right: &RecoveredCodec,
    ) -> Result<Option<String>, AdaptationError>;
}

/// The production joint-automaton route: [`RecoveredCodec::shortest_separating_input`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TheJointAutomaton;

impl JointReading for TheJointAutomaton {
    fn reading(&self) -> &'static str {
        "joint-automaton"
    }

    fn shortest_separating_input(
        &self,
        left: &RecoveredCodec,
        right: &RecoveredCodec,
    ) -> Result<Option<String>, AdaptationError> {
        Ok(left.shortest_separating_input(right)?)
    }
}

// -------------------------------------------------------------------------------------------
// Declared wrong reading 1 — the push event
// -------------------------------------------------------------------------------------------

/// One state of the **push-event** reading. Wrong on purpose, and wrong in exactly one named way.
///
/// It carries `pushed` — *a completed token left the machine at this step* — where [`CodecState`]
/// carries the re-timed opening. That is the naive observable the module documentation rejects: a
/// codec that holds a token across a run of dropped symbols and pushes it later returns the same
/// tokens as one that pushed it immediately, so this reading manufactures separations that neither
/// codec's segmentation shows.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PushEventState {
    pub codec: usize,
    pub previous: Option<SymbolClass>,
    pub token_open: bool,
    /// Whether the step that produced this state pushed a completed token out.
    pub pushed: bool,
}

/// One step of the push-event reading. The `token_open` law is the codec's own; only what is
/// reported differs.
fn push_step(codecs: &[&RecoveredCodec], state: PushEventState, class: usize) -> PushEventState {
    let codec = codecs[state.codec];
    let cut = match state.previous {
        None => true,
        Some(before) => codec.boundary[before.0 as usize][class] == Boundary::Cut,
    };
    let emits = codec.emission[class] == Emission::Emit;
    PushEventState {
        codec: state.codec,
        previous: Some(SymbolClass(class as u32)),
        token_open: emits || (state.token_open && !cut),
        pushed: cut && state.token_open,
    }
}

/// The push-event reading as a [`JointCarrier`]. Same population, same refusals, wrong observable.
#[derive(Clone, Debug)]
pub struct PushEventSystem<'a> {
    codecs: Vec<&'a RecoveredCodec>,
    classes: usize,
    states: Vec<PushEventState>,
    index: BTreeMap<PushEventState, ItemId>,
    rest: Vec<ItemId>,
}

impl<'a> PushEventSystem<'a> {
    pub fn joint(codecs: &[&'a RecoveredCodec]) -> Result<Self, AdaptationError> {
        let classes = admit(codecs)?;
        let codecs: Vec<&'a RecoveredCodec> = codecs.to_vec();
        let rest_states: Vec<PushEventState> = (0..codecs.len())
            .map(|codec| PushEventState {
                codec,
                previous: None,
                token_open: false,
                pushed: false,
            })
            .collect();

        let mut reached: BTreeSet<PushEventState> = rest_states.iter().copied().collect();
        let mut frontier: VecDeque<PushEventState> = rest_states.iter().copied().collect();
        while let Some(state) = frontier.pop_front() {
            for class in 0..classes {
                let next = push_step(&codecs, state, class);
                if reached.insert(next) {
                    frontier.push_back(next);
                }
            }
        }

        let states: Vec<PushEventState> = reached.into_iter().collect();
        let index: BTreeMap<PushEventState, ItemId> = states
            .iter()
            .enumerate()
            .map(|(position, state)| (*state, ItemId(position as u64)))
            .collect();
        let rest = rest_states
            .iter()
            .map(|state| index[state])
            .collect::<Vec<ItemId>>();
        Ok(Self {
            codecs,
            classes,
            states,
            index,
            rest,
        })
    }

    /// The reachable states of this reading, in the order that indexes [`ItemId`].
    pub fn states(&self) -> &[PushEventState] {
        &self.states
    }

    pub fn state_of(&self, item: ItemId) -> Option<PushEventState> {
        self.states.get(item.0 as usize).copied()
    }
}

impl ObservedSystem for PushEventSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        (0..self.states.len())
            .map(|position| ItemId(position as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        vec![ReceiverId(0), ReceiverId(1)]
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.classes)
            .map(|class| InputId(class as u64))
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let state = self
            .state_of(item)
            .expect("an observation is taken of an item of this system");
        let emits = state.previous.is_some_and(|class| {
            self.codecs[state.codec].emission[class.0 as usize] == Emission::Emit
        });
        match receiver {
            ReceiverId(0) => Observation(u64::from(emits)),
            _ => Observation(u64::from(state.pushed)),
        }
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let state = self.state_of(item)?;
        let class = usize::try_from(input.0).ok()?;
        if class >= self.classes {
            return None;
        }
        self.index.get(&push_step(&self.codecs, state, class)).copied()
    }
}

impl JointCarrier for PushEventSystem<'_> {
    fn observed(&self) -> &dyn ObservedSystem {
        self
    }

    fn population(&self) -> usize {
        self.codecs.len()
    }

    fn rest_pair(&self) -> Option<(ItemId, ItemId)> {
        (self.rest.len() == 2).then(|| (self.rest[0], self.rest[1]))
    }

    fn write_word(&self, word: &[InputId]) -> Result<String, AdaptationError> {
        let classes: Vec<usize> = word
            .iter()
            .map(|input| usize::try_from(input.0).unwrap_or(usize::MAX))
            .collect();
        write_classes(self.codecs[0], &classes)
    }

    fn reading(&self) -> &'static str {
        "push-event-shadow"
    }
}

/// The push-event reading taken by a joint breadth-first search instead of a congruence — the same
/// deliberate error occupying the other plug point.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ThePushEventAutomaton;

impl JointReading for ThePushEventAutomaton {
    fn reading(&self) -> &'static str {
        "push-event-shadow-automaton"
    }

    fn shortest_separating_input(
        &self,
        left: &RecoveredCodec,
        right: &RecoveredCodec,
    ) -> Result<Option<String>, AdaptationError> {
        let classes = admit(&[left, right])?;
        let codecs = [left, right];
        let rest = |codec: usize| PushEventState {
            codec,
            previous: None,
            token_open: false,
            pushed: false,
        };
        let start = (rest(0), rest(1));
        let mut seen = BTreeSet::from([start]);
        let mut frontier = VecDeque::from([(start, Vec::<usize>::new())]);
        while let Some(((here, there), word)) = frontier.pop_front() {
            for class in 0..classes {
                let next = (
                    push_step(&codecs, here, class),
                    push_step(&codecs, there, class),
                );
                let mut extended = word.clone();
                extended.push(class);
                if next.0.pushed != next.1.pushed {
                    return write_classes(left, &extended).map(Some);
                }
                if seen.insert(next) {
                    frontier.push_back((next, extended));
                }
            }
        }
        Ok(None)
    }
}

// -------------------------------------------------------------------------------------------
// Declared wrong reading 2 — the same bit, the other tie-break
// -------------------------------------------------------------------------------------------

/// A carrier that is right about the quantity and different about the word.
///
/// Every observation, every successor and every length is the inner carrier's; only the order
/// [`ObservedSystem::inputs`] declares is reversed, which changes which of several equally short
/// separating words the breadth-first exhibition reaches first. This is what makes
/// [`SeparationSpecies::TieBrokenDifferently`] reachable on committed material.
pub struct ReversedInputOrder<'a> {
    pub inner: &'a dyn JointCarrier,
}

impl ObservedSystem for ReversedInputOrder<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.inner.observed().items()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.inner.observed().receivers()
    }

    fn inputs(&self) -> Vec<InputId> {
        let mut inputs = self.inner.observed().inputs();
        inputs.reverse();
        inputs
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        self.inner.observed().observation(item, receiver)
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.inner.observed().successor(item, input)
    }
}

impl JointCarrier for ReversedInputOrder<'_> {
    fn observed(&self) -> &dyn ObservedSystem {
        self
    }

    fn population(&self) -> usize {
        self.inner.population()
    }

    fn rest_pair(&self) -> Option<(ItemId, ItemId)> {
        self.inner.rest_pair()
    }

    fn write_word(&self, word: &[InputId]) -> Result<String, AdaptationError> {
        self.inner.write_word(word)
    }

    fn reading(&self) -> &'static str {
        "reversed-input-order"
    }
}

// -------------------------------------------------------------------------------------------
// Declared wrong reading 3 — an absolute frame
// -------------------------------------------------------------------------------------------

/// A carrier that declares one receiver too many: **which codec it is looking at**.
///
/// That is a receiver-visible coordinate promoted into an invariant, the contaminant `CLAUDE.md` §0
/// names, and its signature here is precise — the two rest states land in different *one-shot*
/// blocks, so the congruence never considers the pair and exhibits no word for it while reporting
/// them separated. [`SeparationSpecies::NerodeSeparatedWithoutExhibitingAWord`] is the refusal that
/// catches it, and this carrier is what fires it.
pub struct CodecIndexReceiver<'a> {
    pub inner: &'a CodecSystem<'a>,
}

impl CodecIndexReceiver<'_> {
    /// The receiver this carrier adds, which the inner system does not declare.
    pub fn absolute_frame(&self) -> ReceiverId {
        ReceiverId(self.inner.receivers().len() as u64)
    }
}

impl ObservedSystem for CodecIndexReceiver<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.inner.items()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        let mut receivers = self.inner.receivers();
        receivers.push(self.absolute_frame());
        receivers
    }

    fn inputs(&self) -> Vec<InputId> {
        self.inner.inputs()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        if receiver == self.absolute_frame() {
            let state = self
                .inner
                .state_of(item)
                .expect("an observation is taken of an item of this system");
            return Observation(state.codec as u64);
        }
        self.inner.observation(item, receiver)
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.inner.successor(item, input)
    }
}

impl JointCarrier for CodecIndexReceiver<'_> {
    fn observed(&self) -> &dyn ObservedSystem {
        self
    }

    fn population(&self) -> usize {
        self.inner.population()
    }

    fn rest_pair(&self) -> Option<(ItemId, ItemId)> {
        self.inner.rest_pair()
    }

    fn write_word(&self, word: &[InputId]) -> Result<String, AdaptationError> {
        self.inner.write_word(word)
    }

    fn reading(&self) -> &'static str {
        "codec-index-receiver"
    }
}

/// Where the two independent implementations of *the shortest input separating two codecs*
/// disagree.
///
/// A species is a name for a kind of disagreement, not a rating of one. The material that produced
/// it lives on [`SeparationCrossCheck`] beside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SeparationSpecies {
    /// One returned a separating input and the other proved there is none. At most one can be
    /// right, and each claims a theorem rather than a stopped search.
    ExistenceDisagreed,
    /// Both returned one, of different lengths. Whichever is longer is not the shortest.
    LengthDisagreed,
    /// Both returned a shortest input of the same length and the words differ. The quantity agrees;
    /// the tie between equally short words was broken differently. Reported, not reconciled.
    TieBrokenDifferently,
    /// The word the Nerode congruence exhibited does not in fact make the two segmentations differ.
    NerodeWordDoesNotSeparate,
    /// The word the joint automaton returned does not in fact make the two segmentations differ.
    JointAutomatonWordDoesNotSeparate,
    /// The refinement put the two rest states in different blocks and then exhibited no word for
    /// the pair. The congruence would be asserting a distinction it cannot witness.
    NerodeSeparatedWithoutExhibitingAWord,
}

/// Two independent returns of one quantity, with the material either produced.
///
/// The whole [`ReceiverExactCompression`] is carried rather than its verdict: `THE_ASSEMBLY.md`'s
/// reviewable rule is that no adapter reduces a returned structure to a boolean or a scalar on its
/// way to the next organ.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SeparationCrossCheck {
    pub schema: String,
    /// Which carrier the congruence side ran on. `segmentation-opening` is the production one.
    pub nerode_reading: String,
    /// Which route the other side took. `joint-automaton` is the production one.
    pub joint_reading: String,
    /// The full Nerode structure of the joint system — both partitions and every collapsed pair.
    pub compression: ReceiverExactCompression,
    /// The two codecs' states before any symbol, as items of the joint system.
    pub rest_states: (ItemId, ItemId),
    /// Whether the refinement placed those two states in different blocks.
    pub rest_states_separated: bool,
    /// What `compress` exhibited for that pair: the word, and it written over the alphabet.
    pub nerode: Option<(Vec<InputId>, String)>,
    /// What `RecoveredCodec::shortest_separating_input` returned.
    pub joint_automaton: Option<String>,
    /// Both codecs' segmentations at the Nerode word. The artifact, never a rate.
    pub nerode_returns: Option<(Vec<String>, Vec<String>)>,
    /// Both codecs' segmentations at the joint-automaton word.
    pub joint_automaton_returns: Option<(Vec<String>, Vec<String>)>,
    pub disagreements: Vec<SeparationSpecies>,
}

impl SeparationCrossCheck {
    /// Did the two implementations return the same quantity, tie-break included.
    pub fn agrees(&self) -> bool {
        self.disagreements.is_empty()
    }
}

/// Run both production implementations of *the shortest input separating two codecs* and return
/// both, with every disagreement exhibited.
///
/// This can fail, and failing is the point. Neither return is derived from the other: the Nerode
/// side never touches [`RecoveredCodec::shortest_separating_input`], and the joint-automaton side
/// never touches [`CodecSystem`]. They are also specification-equivalent, so on well-formed material
/// this returns an empty disagreement population every time — which is why
/// [`cross_check_over`] exists and why the declared wrong readings are part of the module rather
/// than part of a review.
pub fn cross_check(
    left: &RecoveredCodec,
    right: &RecoveredCodec,
) -> Result<SeparationCrossCheck, AdaptationError> {
    let system = CodecSystem::joint(&[left, right])?;
    cross_check_over(&system, &TheJointAutomaton, left, right)
}

/// The cross-check with both sides plugged: any [`JointCarrier`] against any [`JointReading`].
///
/// The species are decided here and nowhere else, so a declared wrong reading in either slot
/// exercises the same detection the production pair runs under.
pub fn cross_check_over(
    carrier: &dyn JointCarrier,
    joint: &dyn JointReading,
    left: &RecoveredCodec,
    right: &RecoveredCodec,
) -> Result<SeparationCrossCheck, AdaptationError> {
    let Some(rest) = carrier.rest_pair() else {
        return Err(AdaptationError::NotAJointCarrier {
            population: carrier.population(),
        });
    };
    let compression = compress(carrier.observed());

    let rest_states_separated =
        compression.conduct.block_of(rest.0) != compression.conduct.block_of(rest.1);
    // `CollapsedPair`s come out of `Partition::identified_pairs`, which emits each pair with the
    // lesser item first, and `CodecState`/`PushEventState` order on `codec` before anything else —
    // so codec 0's rest is always the lesser and the pair is always this way round. A reversed
    // second lookup stood here until 2026-08-08 and was unreachable by construction; a refusal that
    // cannot fire is not a refusal, and if this orientation is ever wrong the search below returns
    // `None` and `NerodeSeparatedWithoutExhibitingAWord` says so.
    let nerode_word = compression
        .collapsed
        .iter()
        .find(|pair| (pair.left, pair.right) == rest)
        .map(|pair| pair.distinguishing_word.clone());
    let nerode = match nerode_word {
        Some(word) => {
            let written = carrier.write_word(&word)?;
            Some((word, written))
        }
        None => None,
    };
    let joint_automaton = joint.shortest_separating_input(left, right)?;

    let segmentations = |input: &str| -> Result<(Vec<String>, Vec<String>), AdaptationError> {
        Ok((left.segment(input)?, right.segment(input)?))
    };
    let nerode_returns = match &nerode {
        Some((_, written)) => Some(segmentations(written)?),
        None => None,
    };
    let joint_automaton_returns = match &joint_automaton {
        Some(input) => Some(segmentations(input)?),
        None => None,
    };

    let mut disagreements = Vec::new();
    if rest_states_separated && nerode.is_none() {
        disagreements.push(SeparationSpecies::NerodeSeparatedWithoutExhibitingAWord);
    }
    if let Some((returned_left, returned_right)) = &nerode_returns
        && returned_left == returned_right
    {
        disagreements.push(SeparationSpecies::NerodeWordDoesNotSeparate);
    }
    if let Some((returned_left, returned_right)) = &joint_automaton_returns
        && returned_left == returned_right
    {
        disagreements.push(SeparationSpecies::JointAutomatonWordDoesNotSeparate);
    }
    match (&nerode, &joint_automaton) {
        (None, None) => {}
        (Some(_), None) | (None, Some(_)) => {
            disagreements.push(SeparationSpecies::ExistenceDisagreed);
        }
        (Some((_, written)), Some(input)) => {
            if written.chars().count() != input.chars().count() {
                disagreements.push(SeparationSpecies::LengthDisagreed);
            } else if written != input {
                disagreements.push(SeparationSpecies::TieBrokenDifferently);
            }
        }
    }

    Ok(SeparationCrossCheck {
        schema: CROSS_CHECK_SCHEMA.to_owned(),
        nerode_reading: carrier.reading().to_owned(),
        joint_reading: joint.reading().to_owned(),
        compression,
        rest_states: rest,
        rest_states_separated,
        nerode,
        joint_automaton,
        nerode_returns,
        joint_automaton_returns,
        disagreements,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::codec_recovery::{
        recover, CodecRecovery, Obstruction, OpaqueSymbolCodec, RecoveryApertures,
    };

    /// **What this test body declares as its host capacity**, since `codec_recovery` no longer
    /// picks one (`canon/THE_AUTHORED_LEVEL.md` §5.2). Reproduces the excised constants.
    const TEST_APERTURES: RecoveryApertures = RecoveryApertures {
        family_words: 65_536,
        free_entries: 12,
    };
    use crate::receiver_exact_compression::AblatedSystem;

    /// The same shape of target `codec_recovery` recovers from: a character-class state machine
    /// written as a state machine, never as a table. Word characters agglutinate, digits
    /// agglutinate only with each other, whitespace is dropped and flushes, `.`/`-` are a run
    /// class, `,`/`;` are a solo class.
    fn tokenizer() -> OpaqueSymbolCodec {
        OpaqueSymbolCodec::new(|input: &str| {
            #[derive(Clone, Copy, PartialEq)]
            enum Kind {
                Word,
                Digit,
                Space,
                Run,
                Solo,
            }
            fn kind(symbol: char) -> Kind {
                match symbol {
                    'a' | 'b' | 'q' => Kind::Word,
                    '0' | '1' => Kind::Digit,
                    ' ' | '\t' => Kind::Space,
                    '.' | '-' => Kind::Run,
                    _ => Kind::Solo,
                }
            }
            let mut tokens = Vec::new();
            let mut current = String::new();
            let mut previous: Option<Kind> = None;
            for symbol in input.chars() {
                let here = kind(symbol);
                let cut = match previous {
                    None => true,
                    Some(before) => {
                        before != here || !matches!(here, Kind::Word | Kind::Digit | Kind::Run)
                    }
                };
                if cut && !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
                if here != Kind::Space {
                    current.push(symbol);
                }
                previous = Some(here);
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        })
    }

    const TOKENIZER_ALPHABET: [char; 11] = ['a', 'b', 'q', '0', '1', ' ', '\t', '.', '-', ',', ';'];

    /// A codec whose dropped symbol **joins**. At radius two the declared family provably cannot
    /// see through it and the recovery returns two genuinely inequivalent codecs.
    fn soft_join() -> OpaqueSymbolCodec {
        OpaqueSymbolCodec::new(|input: &str| {
            let token: String = input.chars().filter(|symbol| *symbol != '_').collect();
            if token.is_empty() {
                Vec::new()
            } else {
                vec![token]
            }
        })
    }

    fn tokenizer_recovery() -> CodecRecovery {
        recover(&tokenizer(), &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible")
    }

    /// Real recovered codecs, from two different opaque targets, with materially different shapes:
    /// the tokenizer's recovered table carries no `Join` touching its dropped class, while
    /// `soft_join`'s carries three. A sweep confined to the first could not exercise a token held
    /// open across a dropped symbol, which is exactly the conduct the whole adaptation turns on.
    fn real_codecs() -> Vec<(&'static str, RecoveredCodec)> {
        let tokenizer_codec = tokenizer_recovery().codec.expect("the codec is recovered");
        let soft = recover(&soft_join(), &['a', 'b', '_'], 4, TEST_APERTURES)
            .expect("the family is admissible")
            .codec
            .expect("the codec is recovered");
        assert_eq!(soft.boundary_between('a', '_'), Some(Boundary::Join));
        let (left, right, _) = undetermined(2);
        vec![
            ("tokenizer", tokenizer_codec),
            ("soft-join", soft),
            ("undetermined-left", left),
            ("undetermined-right", right),
        ]
    }

    /// The two inequivalent codecs the `soft_join` recovery itself exhibits, and the input it named
    /// as separating them. Real recovered material, not hand-written tables.
    fn undetermined(radius: usize) -> (RecoveredCodec, RecoveredCodec, String) {
        let recovery =
            recover(&soft_join(), &['a', 'b', '_'], radius, TEST_APERTURES).expect("the family is admissible");
        let Some(Obstruction::UndeterminedCodec {
            left,
            right,
            separating_input,
            ..
        }) = recovery.obstructions.first()
        else {
            panic!("radius {radius}: expected an undetermined codec");
        };
        (left.clone(), right.clone(), separating_input.clone())
    }

    /// Every word over the class representatives, shortest first then in class order — the same
    /// order both organs under test enumerate in, computed here by brute force so it can act as a
    /// third and trivially independent minimality oracle.
    fn words_up_to(codec: &RecoveredCodec, length: usize) -> Vec<String> {
        let letters: Vec<char> = (0..codec.classes.len())
            .map(|class| {
                codec
                    .class_representative(SymbolClass(class as u32))
                    .expect("a recovered class is never empty")
            })
            .collect();
        let mut words = Vec::new();
        for size in 1..=length {
            let total = (letters.len() as u64).pow(size as u32);
            for ordinal in 0..total {
                let mut rest = ordinal;
                let mut word = vec![letters[0]; size];
                for position in (0..size).rev() {
                    word[position] = letters[(rest % letters.len() as u64) as usize];
                    rest /= letters.len() as u64;
                }
                words.push(word.into_iter().collect());
            }
        }
        words
    }

    /// The shortest word over the class representatives on which two codecs segment differently,
    /// by exhaustion. Independent of both organs under test.
    fn brute_force_separator(
        left: &RecoveredCodec,
        right: &RecoveredCodec,
        length: usize,
    ) -> Option<String> {
        words_up_to(left, length)
            .into_iter()
            .find(|word| left.segment(word).unwrap() != right.segment(word).unwrap())
    }

    /// What the last symbol of `prefix + suffix` put into the token stream, derived from
    /// [`RecoveredCodec::segment`] alone by the two identities a split of an emitted stream
    /// satisfies:
    ///
    /// ```text
    ///   the last symbol emitted   <->  segment(w) carries more characters than segment(prefix)
    ///   that character opened     <->  segment(w) carries more tokens    than segment(prefix)
    /// ```
    ///
    /// Neither identity mentions `token_open`, `boundary`, or either organ under test.
    fn final_step(codec: &RecoveredCodec, prefix: &str, suffix: &str) -> StepReturn {
        let whole = format!("{prefix}{suffix}");
        let mut shorter: Vec<char> = whole.chars().collect();
        shorter.pop().expect("the word is not empty");
        let before = codec
            .segment(&shorter.into_iter().collect::<String>())
            .expect("declared symbols only");
        let after = codec.segment(&whole).expect("declared symbols only");
        let characters =
            |tokens: &[String]| -> usize { tokens.iter().map(|token| token.chars().count()).sum() };
        if characters(&after) == characters(&before) {
            StepReturn::Silent
        } else if after.len() > before.len() {
            StepReturn::OpenedToken
        } else {
            StepReturn::ExtendedToken
        }
    }

    /// The shortest word over the class representatives that reaches an item of a single-codec
    /// system, breadth-first from rest.
    fn reaching_word(system: &CodecSystem<'_>, target: ItemId) -> Option<String> {
        let rest = system.rest_state(0)?;
        let mut seen = BTreeSet::from([rest]);
        let mut frontier = VecDeque::from([(rest, Vec::<InputId>::new())]);
        while let Some((item, word)) = frontier.pop_front() {
            if item == target {
                return system.word_string(&word).ok();
            }
            for input in system.inputs() {
                if let Some(next) = system.successor(item, input)
                    && seen.insert(next)
                {
                    let mut extended = word.clone();
                    extended.push(input);
                    frontier.push_back((next, extended));
                }
            }
        }
        None
    }

    /// Flip one boundary entry of a codec. The gauge sweep's material.
    fn flipped(codec: &RecoveredCodec, left: usize, right: usize) -> RecoveredCodec {
        let mut variant = codec.clone();
        variant.boundary[left][right] = match variant.boundary[left][right] {
            Boundary::Join => Boundary::Cut,
            Boundary::Cut => Boundary::Join,
        };
        variant
    }

    // ---------------------------------------------------------------------------------------
    // The adaptation itself
    // ---------------------------------------------------------------------------------------

    /// The successor map must be **total**. `ObservedSystem` reads `None` as a declared terminus,
    /// so a reachability set that missed a state would not fail loudly — it would silently tell
    /// `compress` that the machine stops there, and a terminus is a distinction. This is the check
    /// that makes that impossible to miss.
    /// A single-codec system cannot vary this property: a reachability walk seeded from one codec
    /// is total there by accident. The joint system is the fixture that can actually refute it, and
    /// every codec of the population must be shown to contribute states, or "total" is a statement
    /// about a population of one.
    #[test]
    fn the_adapted_successor_map_is_total_over_the_states_it_declares() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let (left, right, _) = undetermined(2);
        let single = CodecSystem::new(codec).expect("the codec is adaptable");
        let joint = CodecSystem::joint(&[&left, &right]).expect("the two codecs are comparable");

        for system in [&single, &joint] {
            assert!(!system.items().is_empty());
            for codec in 0..system.population() {
                assert!(
                    system.states().iter().any(|state| state.codec == codec),
                    "codec {codec} contributes no state"
                );
                assert!(system.rest_state(codec).is_some());
            }
            for item in system.items() {
                for input in system.inputs() {
                    assert!(
                        system.successor(item, input).is_some(),
                        "{:?} has no successor on {input:?}",
                        system.state_of(item)
                    );
                }
            }
        }
        assert_eq!(joint.population(), 2);
        let one_side = CodecSystem::new(&left).expect("the codec is adaptable");
        assert!(
            joint.states().len() > one_side.states().len(),
            "a joint system must carry more states than one of its codecs alone: {} vs {}",
            joint.states().len(),
            one_side.states().len()
        );
    }

    /// **The adapter's transition function, checked against `segment` and against nothing else.**
    ///
    /// The expected return is re-derived here from the codec's public segmentation alone, by the
    /// two identities a split of an emitted stream satisfies:
    ///
    /// ```text
    ///   the last symbol emitted   <->  segment(w) carries more characters than segment(prefix)
    ///   that character opened     <->  segment(w) carries more tokens    than segment(prefix)
    /// ```
    ///
    /// Neither identity mentions `token_open`, `boundary`, or the joint automaton, so a wrong carry
    /// of the open flag surfaces here as a wrong return one step later rather than as nothing.
    #[test]
    fn every_declared_state_matches_what_segment_itself_returns_for_the_word_that_reaches_it() {
        for (name, codec) in real_codecs() {
            let system = CodecSystem::new(&codec).expect("the codec is adaptable");
            let rest = system.rest_state(0).expect("a system rests");
            let mut exercised: BTreeSet<StepReturn> = BTreeSet::new();

            for word in words_up_to(&codec, 4) {
                let symbols: Vec<char> = word.chars().collect();
                let prefix: String = symbols[..symbols.len() - 1].iter().collect();
                let last: String = symbols[symbols.len() - 1..].iter().collect();
                let expected = final_step(&codec, &prefix, &last);
                exercised.insert(expected);

                let mut item = rest;
                for symbol in &symbols {
                    let class = codec.class_of(*symbol).expect("a declared symbol");
                    let input = system.input_of(class).expect("a declared class");
                    item = system.successor(item, input).expect("a total machine");
                }
                let state = system.state_of(item).expect("an item of this system");
                assert_eq!(
                    state.last, expected,
                    "{name}: after {word:?} segment returns {:?} against {:?}",
                    codec.segment(&word).expect("declared symbols only"),
                    codec.segment(&prefix).expect("declared symbols only")
                );
                assert_eq!(
                    state.previous,
                    codec.class_of(*symbols.last().expect("no word is empty"))
                );
            }
            assert_eq!(
                exercised.len(),
                3,
                "{name}: the material must exercise all three returns, saw {exercised:?}"
            );
        }
    }

    /// **The provably non-zero control.** A law that returns zero proves nothing about itself
    /// (`CLAUDE.md` §8), so before any agreement is claimed the quantity under test must be shown
    /// to be capable of being non-empty on real recovered material.
    #[test]
    fn the_nerode_congruence_of_a_recovered_codec_is_provably_nonzero() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let system = CodecSystem::new(codec).expect("the codec is adaptable");
        let compression = compress(&system);

        assert!(
            compression.one_shot.len() > 1,
            "the one-shot reading must already see something: {:?}",
            compression.one_shot.len()
        );
        assert!(
            compression.conduct.len() > compression.one_shot.len(),
            "conduct must refine the one-shot reading: {} -> {}",
            compression.one_shot.len(),
            compression.conduct.len()
        );
        assert!(compression.rounds >= 1, "refinement must take a round");
        assert!(
            !compression.is_exact(),
            "the one-shot reading over-collapses and the collapsed population must exhibit it"
        );

        // The census, pinned rather than described. Nine reachable states; three one-shot blocks —
        // one per `StepReturn`; eight conduct blocks; nine exhibited pairs. The congruence is
        // neither trivial nor discrete: exactly one pair survives refinement, the rest state and
        // the state after a dropped symbol, because this codec's dropped class cuts into every
        // class and therefore has the same future as having read nothing.
        assert_eq!(system.states().len(), 9);
        assert_eq!(compression.one_shot.len(), 3);
        assert_eq!(compression.conduct.len(), 8);
        assert_eq!(compression.rounds, 1);
        assert_eq!(compression.collapsed.len(), 9);
        assert_eq!(compression.refinement(), 5);
        let merged: Vec<&std::collections::BTreeSet<ItemId>> = compression
            .conduct
            .blocks
            .iter()
            .filter(|block| block.len() > 1)
            .collect();
        assert_eq!(merged.len(), 1, "exactly one conduct block merges anything");
        let merged: Vec<CodecState> = merged[0]
            .iter()
            .map(|item| system.state_of(*item).expect("an item of this system"))
            .collect();
        assert_eq!(merged.len(), 2);
        assert!(merged.iter().any(|state| state.previous.is_none()));
        assert!(merged.iter().all(|state| state.last == StepReturn::Silent));

        // The artifact, inspected rather than counted. Every exhibited pair must really separate:
        // walk both states under the returned word and confirm some receiver sees a difference.
        for pair in &compression.collapsed {
            assert!(
                !pair.distinguishing_word.is_empty(),
                "the empty word is the one-shot reading and cannot be a separator"
            );
            let mut here = pair.left;
            let mut there = pair.right;
            for input in &pair.distinguishing_word {
                here = system.successor(here, *input).expect("a total machine");
                there = system.successor(there, *input).expect("a total machine");
            }
            let seen: Vec<(Observation, Observation)> = system
                .receivers()
                .into_iter()
                .map(|receiver| {
                    (
                        system.observation(here, receiver),
                        system.observation(there, receiver),
                    )
                })
                .collect();
            assert!(
                seen.iter().any(|(left, right)| left != right),
                "the word {:?} does not separate {:?} from {:?}",
                pair.distinguishing_word,
                system.state_of(pair.left),
                system.state_of(pair.right)
            );
        }
    }

    /// **`THE_ASSEMBLY.md` step 3 is wrong about the state, and this is the material that shows it.**
    ///
    /// The design says the recovered codec is *"a finite machine whose states are `SymbolClass`."*
    /// The test that stood here until 2026-08-08 built that reading as a struct whose
    /// `successor(_item, input)` ignored its item and then asserted that its refinement was a fixed
    /// point at round zero. That assertion is forced by the declaration five lines above it — an
    /// argument written in Rust syntax, not a measurement — and it is deleted.
    ///
    /// What replaces it is measured twice over, and neither half mentions the design's struct:
    ///
    /// 1. the reachable state population of every really recovered codec is **strictly larger** than
    ///    its class population, so the design's state space is too small to hold the machine;
    /// 2. two of those states carry the **same symbol class** — the design identifies them — and are
    ///    separated by a word after which [`RecoveredCodec::segment`] itself returns something
    ///    different from each. The word, both reaching words, and both returns are exhibited.
    ///
    /// The second half reads only `segment`, so a wrong carry of the open-token flag inside this
    /// adapter cannot make it pass.
    #[test]
    fn two_states_of_one_symbol_class_are_separated_by_a_word_segment_itself_exhibits() {
        // 1. The census, measured per codec. A machine whose states were classes would return
        //    equality here on every one of them.
        let population = real_codecs();
        for (name, codec) in &population {
            let system = CodecSystem::new(codec).expect("the codec is adaptable");
            assert!(
                system.states().len() > codec.classes.len(),
                "{name}: {} reachable states over {} classes; the design's state space would \
                 have to hold them",
                system.states().len(),
                codec.classes.len()
            );
        }

        // 2. The exhibition. Searched for over the whole population rather than hand-picked, so a
        //    change in the material that removes it fails here instead of passing quietly.
        let mut exhibited = 0usize;
        for (name, codec) in &population {
            let system = CodecSystem::new(codec).expect("the codec is adaptable");
            let compression = compress(&system);
            for pair in &compression.collapsed {
                let here = system.state_of(pair.left).expect("an item of this system");
                let there = system.state_of(pair.right).expect("an item of this system");
                // The design would call these one state. Only a pair the one-shot reading merged
                // qualifies: those are the states no receiver tells apart at rest.
                if here.previous != there.previous || here.previous.is_none() {
                    continue;
                }
                let reaching =
                    |item: ItemId| reaching_word(&system, item).expect("a reachable state has a word");
                let (before_here, before_there) = (reaching(pair.left), reaching(pair.right));
                assert_ne!(before_here, before_there);
                let suffix = system
                    .word_string(&pair.distinguishing_word)
                    .expect("the word is over the recovered alphabet");
                assert!(!suffix.is_empty(), "{name}: the empty word is the rest reading");

                // The refutation, taken from `segment` and from nothing else: the last step of the
                // two extended words differs in what it put into the token stream.
                let step_here = final_step(codec, &before_here, &suffix);
                let step_there = final_step(codec, &before_there, &suffix);
                assert_ne!(
                    step_here, step_there,
                    "{name}: {before_here:?} and {before_there:?} both end in class {:?}; \
                     after {suffix:?} segment returns {:?} against {:?}",
                    here.previous,
                    codec.segment(&format!("{before_here}{suffix}")).unwrap(),
                    codec.segment(&format!("{before_there}{suffix}")).unwrap(),
                );
                assert_eq!(
                    codec.class_of(before_here.chars().last().expect("a non-empty word")),
                    codec.class_of(before_there.chars().last().expect("a non-empty word")),
                    "{name}: the two reaching words must end in one class or the design is not \
                     being refuted"
                );
                exhibited += 1;
            }
        }
        assert!(
            exhibited > 0,
            "no pair of states of one symbol class was separated anywhere in the population; \
             without one the design's reading is not refuted by this material"
        );
    }

    // ---------------------------------------------------------------------------------------
    // The cross-check
    // ---------------------------------------------------------------------------------------

    /// The two implementations, on the two genuinely inequivalent codecs the `soft_join` recovery
    /// itself exhibits, at two radii. Every claim here is checked against a third, brute-force
    /// minimality oracle as well, so a shared error in both organs would still be caught.
    #[test]
    fn the_two_implementations_agree_on_the_codecs_a_real_recovery_could_not_choose_between() {
        for (radius, expected_length) in [(2usize, 3usize), (3, 4)] {
            let (left, right, named) = undetermined(radius);
            let check = cross_check(&left, &right).expect("the two codecs are comparable");

            assert!(
                check.agrees(),
                "radius {radius}: disagreements {:?}\n  nerode {:?} -> {:?}\n  joint  {:?} -> {:?}",
                check.disagreements,
                check.nerode,
                check.nerode_returns,
                check.joint_automaton,
                check.joint_automaton_returns
            );
            assert!(check.rest_states_separated);

            let (_, nerode_input) = check.nerode.clone().expect("the pair is separated");
            let joint_input = check
                .joint_automaton
                .clone()
                .expect("the joint automaton separates them");
            assert_eq!(joint_input, named, "radius {radius}: the recovery's own word");
            assert_eq!(nerode_input.chars().count(), expected_length);
            assert_eq!(nerode_input, joint_input);

            // The third opinion: shortest by exhaustion, independent of both organs.
            let brute = brute_force_separator(&left, &right, expected_length + 1)
                .expect("some word separates them");
            assert_eq!(
                brute.chars().count(),
                expected_length,
                "radius {radius}: brute force found {brute:?}"
            );

            // The artifacts, exhibited rather than summarised.
            let (returned_left, returned_right) =
                check.nerode_returns.clone().expect("a separated pair");
            assert_ne!(returned_left, returned_right);
            assert_eq!(returned_left, left.segment(&nerode_input).unwrap());
            assert_eq!(returned_right, right.segment(&nerode_input).unwrap());
        }
    }

    /// A codec against itself. Both implementations must prove absence, not fail to find one.
    #[test]
    fn a_codec_against_itself_separates_at_no_input_under_either_implementation() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let check = cross_check(codec, codec).expect("a codec is comparable with itself");
        assert!(check.agrees(), "{:?}", check.disagreements);
        assert!(check.nerode.is_none());
        assert!(check.joint_automaton.is_none());
        assert!(!check.rest_states_separated);
    }

    /// **The sweep, and the fixture check the sweep exists for.** Thirteen codecs built by flipping
    /// boundary entries of a really recovered tokenizer, cross-checked over every pair. The
    /// population is asserted to contain **both** separable and inseparable pairs and **more than
    /// one** separating length, because a sweep in which every pair answered the same way could not
    /// distinguish the two implementations at all — the defect this project has hit five times in
    /// one day. The census is pinned rather than described, so a change in the material that
    /// quietly flattens it fails here instead of passing quietly.
    #[test]
    fn the_two_implementations_agree_across_a_gauge_sweep_that_contains_both_answers() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        assert_eq!(recovery.gauge_freedom.len(), 9, "the sweep needs its material");

        let mut population = vec![codec.clone()];
        for (left, right) in &recovery.gauge_freedom {
            population.push(flipped(codec, left.0 as usize, right.0 as usize));
        }
        // Single gauge flips all stay inside the retained population, so on their own they answer
        // "inseparable" every time. Two flips — one into the dropped class and one out of it — let
        // a token be held open across a dropped symbol, which no retained table does, and separate
        // at length three. A determined entry separates at length two. Without both the sweep
        // could not refute a length claim and could not distinguish the two implementations at all.
        let word = codec.class_of('a').expect("the word class is recovered");
        let digit = codec.class_of('0').expect("the digit class is recovered");
        let space = codec.class_of(' ').expect("the space class is recovered");
        for held in [word, digit] {
            let mut across = flipped(codec, held.0 as usize, space.0 as usize);
            across = flipped(&across, space.0 as usize, held.0 as usize);
            population.push(across);
        }
        population.push(flipped(codec, word.0 as usize, word.0 as usize));

        let mut separable = 0usize;
        let mut inseparable = 0usize;
        let mut lengths: BTreeSet<usize> = BTreeSet::new();
        for (position, left) in population.iter().enumerate() {
            for right in &population[position + 1..] {
                let check = cross_check(left, right).expect("one alphabet, one emission");
                assert!(
                    check.agrees(),
                    "disagreements {:?}\n  left {:?}\n  right {:?}\n  nerode {:?} -> {:?}\n  \
                     joint {:?} -> {:?}",
                    check.disagreements,
                    left.boundary,
                    right.boundary,
                    check.nerode,
                    check.nerode_returns,
                    check.joint_automaton,
                    check.joint_automaton_returns
                );
                match &check.joint_automaton {
                    None => {
                        inseparable += 1;
                        assert!(!check.rest_states_separated);
                    }
                    Some(input) => {
                        separable += 1;
                        lengths.insert(input.chars().count());
                        assert!(check.rest_states_separated);
                        // The third opinion again, on every separable pair in the sweep.
                        let brute = brute_force_separator(left, right, input.chars().count() + 1)
                            .expect("the returned word says one exists");
                        assert_eq!(
                            brute.chars().count(),
                            input.chars().count(),
                            "returned {input:?} but exhaustion found {brute:?}"
                        );
                        let (returned_left, returned_right) =
                            check.joint_automaton_returns.clone().expect("a separator");
                        assert_ne!(returned_left, returned_right);
                        // The Nerode side's own word, exhibited and checked to be a separator of
                        // the same minimal length rather than merely reported as agreeing.
                        let (word, written) = check.nerode.clone().expect("a separated pair");
                        assert_eq!(word.len(), input.chars().count());
                        let (nerode_left, nerode_right) =
                            check.nerode_returns.clone().expect("a separator");
                        assert_ne!(
                            nerode_left, nerode_right,
                            "the Nerode word {written:?} does not separate"
                        );
                    }
                }
            }
        }
        assert!(
            separable > 0 && inseparable > 0,
            "the sweep must contain both answers or it cannot distinguish the two \
             implementations: separable={separable} inseparable={inseparable}"
        );
        assert!(
            lengths.len() > 1,
            "every separable pair separated at the same length {lengths:?}; the sweep cannot \
             refute a length claim"
        );
        // The census, pinned. Ten mutually equivalent tables — the recovered one and its nine
        // single gauge flips, every one of which stays inside the retained population — and three
        // that leave it, pairwise distinct.
        assert_eq!(population.len(), 13);
        assert_eq!(
            (separable, inseparable),
            (33, 45),
            "the sweep's census moved; lengths {lengths:?}"
        );
        assert_eq!(lengths, BTreeSet::from([2, 3]));
    }

    /// The gauge the recovery reported really is a gauge: flipping a free entry can leave the codec
    /// observationally identical. Without this, `inseparable` above could be an artifact of the
    /// sweep rather than a property of the material.
    #[test]
    fn a_reported_gauge_entry_can_be_flipped_without_any_input_seeing_it() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let identical: Vec<(SymbolClass, SymbolClass)> = recovery
            .gauge_freedom
            .iter()
            .copied()
            .filter(|(left, right)| {
                let variant = flipped(codec, left.0 as usize, right.0 as usize);
                codec.shortest_separating_input(&variant).unwrap().is_none()
            })
            .collect();
        assert!(
            !identical.is_empty(),
            "no reported gauge entry is observationally free"
        );
        for (left, right) in identical {
            let variant = flipped(codec, left.0 as usize, right.0 as usize);
            let check = cross_check(codec, &variant).expect("comparable");
            assert!(check.agrees(), "{:?}", check.disagreements);
            assert!(check.nerode.is_none() && check.joint_automaton.is_none());
            assert_eq!(
                brute_force_separator(codec, &variant, 4),
                None,
                "exhaustion found a separator for a free entry {left:?} {right:?}"
            );
        }
    }

    // ---------------------------------------------------------------------------------------
    // The declared wrong readings — the non-zero controls the cross-check had none of
    // ---------------------------------------------------------------------------------------

    /// **The control the whole step was missing.** The two production routes are
    /// specification-equivalent, so `cross_check` returns an empty disagreement population for every
    /// well-formed input, and an adversarial review confirmed that deleting the disagreement
    /// machinery outright passed the entire suite. A law that returns zero proves nothing about
    /// itself (`CLAUDE.md` §8).
    ///
    /// So the congruence side is run over [`PushEventSystem`], which observes *a completed token
    /// left the machine at this step* instead of the re-timed opening. On a gauge pair — two tables
    /// **no input of any length separates** — that reading manufactures a separation, and both
    /// species fire: the word it exhibits does not make the segmentations differ, and it claims a
    /// separator where the joint automaton proved there is none. The agreeing production return is
    /// taken on the same two codecs immediately above it, so a zero and a non-zero return are both
    /// exercised on one material.
    #[test]
    fn the_push_event_shadow_manufactures_a_separation_a_gauge_pair_does_not_have() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let word = codec.class_of('a').expect("the word class is recovered");
        let space = codec.class_of(' ').expect("the space class is recovered");
        let gauge = flipped(codec, word.0 as usize, space.0 as usize);

        // The production pair, on this exact material: nothing to report.
        let agreeing = cross_check(codec, &gauge).expect("comparable");
        assert_eq!(agreeing.disagreements, Vec::new());
        assert!(agreeing.nerode.is_none() && agreeing.joint_automaton.is_none());
        assert_eq!(agreeing.nerode_reading, "segmentation-opening");
        assert_eq!(agreeing.joint_reading, "joint-automaton");

        // The same two codecs through the same shape, with the shadow on the congruence side.
        let shadow = PushEventSystem::joint(&[codec, &gauge]).expect("comparable");
        let check = cross_check_over(&shadow, &TheJointAutomaton, codec, &gauge)
            .expect("comparable");
        assert_eq!(check.nerode_reading, "push-event-shadow");
        assert!(!check.agrees());
        assert_eq!(
            check.disagreements,
            vec![
                SeparationSpecies::NerodeWordDoesNotSeparate,
                SeparationSpecies::ExistenceDisagreed,
            ],
            "the shadow must be caught by both species it earns"
        );

        // The artifact, exhibited rather than counted: the word the shadow claims, and the two
        // identical segmentations that refute it.
        let (claimed, written) = check.nerode.clone().expect("the shadow claims a separator");
        assert_eq!(claimed.len(), 2, "the shadow separates at {written:?}");
        assert!(check.joint_automaton.is_none());
        let (returned_left, returned_right) =
            check.nerode_returns.clone().expect("the word was segmented");
        assert_eq!(
            returned_left, returned_right,
            "if the shadow's word really separated them this control would prove nothing"
        );
        assert_eq!(returned_left, codec.segment(&written).unwrap());
        assert_eq!(
            brute_force_separator(codec, &gauge, 5),
            None,
            "exhaustion must confirm the pair has no separator at all"
        );
    }

    /// The same shadow against a pair that **is** separable, where it disagrees about the length
    /// rather than about existence.
    ///
    /// Two flips — one into the dropped class and one out of it — let a token be held open across a
    /// dropped symbol. The segmentations first differ at length three; the push event differs at
    /// length two, because one codec pushes the held token at the dropped symbol and the other
    /// carries it. That is exactly the re-timing the module's observable exists for, and
    /// [`SeparationSpecies::LengthDisagreed`] is what catches its absence.
    #[test]
    fn the_push_event_shadow_disagrees_about_the_length_where_a_token_is_held_across_a_drop() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let word = codec.class_of('a').expect("the word class is recovered");
        let space = codec.class_of(' ').expect("the space class is recovered");
        let mut across = flipped(codec, word.0 as usize, space.0 as usize);
        across = flipped(&across, space.0 as usize, word.0 as usize);

        let agreeing = cross_check(codec, &across).expect("comparable");
        assert_eq!(agreeing.disagreements, Vec::new());
        let truth = agreeing
            .joint_automaton
            .clone()
            .expect("the two tables are separable");
        assert_eq!(truth.chars().count(), 3, "the real separator is {truth:?}");

        let shadow = PushEventSystem::joint(&[codec, &across]).expect("comparable");
        let check =
            cross_check_over(&shadow, &TheJointAutomaton, codec, &across).expect("comparable");
        assert!(!check.agrees());
        assert_eq!(
            check.disagreements,
            vec![
                SeparationSpecies::NerodeWordDoesNotSeparate,
                SeparationSpecies::LengthDisagreed,
            ]
        );
        let (claimed, written) = check.nerode.clone().expect("the shadow claims a separator");
        assert_eq!(claimed.len(), 2);
        assert!(
            claimed.len() < truth.chars().count(),
            "the shadow over-distinguishes, so its word is the shorter one"
        );
        let (returned_left, returned_right) = check.nerode_returns.clone().expect("segmented");
        assert_eq!(
            returned_left, returned_right,
            "the shadow's word {written:?} must not really separate them"
        );
        // The joint automaton's own word does separate them, on the same return.
        let (joint_left, joint_right) = check
            .joint_automaton_returns
            .clone()
            .expect("the automaton returned a word");
        assert_ne!(joint_left, joint_right);
    }

    /// The shadow in the **other** plug point. `JointAutomatonWordDoesNotSeparate` guards the route
    /// the production side takes, so it can only fire against a wrong automaton, and one is declared
    /// for it rather than left as a name in an enum.
    #[test]
    fn the_push_event_automaton_is_caught_by_the_refusal_that_guards_the_automaton_side() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let word = codec.class_of('a').expect("the word class is recovered");
        let space = codec.class_of(' ').expect("the space class is recovered");
        let gauge = flipped(codec, word.0 as usize, space.0 as usize);

        let system = CodecSystem::joint(&[codec, &gauge]).expect("comparable");
        let check = cross_check_over(&system, &ThePushEventAutomaton, codec, &gauge)
            .expect("comparable");
        assert_eq!(check.nerode_reading, "segmentation-opening");
        assert_eq!(check.joint_reading, "push-event-shadow-automaton");
        assert!(!check.agrees());
        assert_eq!(
            check.disagreements,
            vec![
                SeparationSpecies::JointAutomatonWordDoesNotSeparate,
                SeparationSpecies::ExistenceDisagreed,
            ]
        );
        let claimed = check
            .joint_automaton
            .clone()
            .expect("the shadow automaton claims a separator");
        assert_eq!(claimed.chars().count(), 2);
        assert!(check.nerode.is_none(), "the congruence proved there is none");
        let (returned_left, returned_right) =
            check.joint_automaton_returns.clone().expect("segmented");
        assert_eq!(returned_left, returned_right);

        // The two shadow faces are one error stated twice: the congruence over the push event and
        // the breadth-first search over it name a word of the same length.
        let congruence = PushEventSystem::joint(&[codec, &gauge]).expect("comparable");
        let other_face = cross_check_over(&congruence, &TheJointAutomaton, codec, &gauge)
            .expect("comparable");
        let (_, shadow_word) = other_face.nerode.clone().expect("a claimed separator");
        assert_eq!(shadow_word.chars().count(), claimed.chars().count());
    }

    /// A tie is reported as a tie. The reversed-order carrier is right about the quantity and names
    /// a different word, and the species exists so that outcome is not mistaken for a disagreement.
    ///
    /// The material has to carry **two** equally short separators or the tie cannot occur: two
    /// determined entries are flipped, so `aa` and `00` both separate at length two and the two
    /// input orders reach different ones first.
    #[test]
    fn a_reversed_input_order_names_a_different_equally_short_word_and_is_reported_as_a_tie() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let word = codec.class_of('a').expect("the word class is recovered");
        let digit = codec.class_of('0').expect("the digit class is recovered");
        let mut twice = flipped(codec, word.0 as usize, word.0 as usize);
        twice = flipped(&twice, digit.0 as usize, digit.0 as usize);

        let forward = cross_check(codec, &twice).expect("comparable");
        assert_eq!(forward.disagreements, Vec::new());
        let named = forward.joint_automaton.clone().expect("separable");

        let system = CodecSystem::joint(&[codec, &twice]).expect("comparable");
        let reversed = ReversedInputOrder { inner: &system };
        let check =
            cross_check_over(&reversed, &TheJointAutomaton, codec, &twice).expect("comparable");
        assert_eq!(check.nerode_reading, "reversed-input-order");
        assert!(!check.agrees());
        assert_eq!(
            check.disagreements,
            vec![SeparationSpecies::TieBrokenDifferently]
        );

        let (_, written) = check.nerode.clone().expect("a separated pair");
        assert_ne!(written, named, "a tie needs two different words");
        assert_eq!(
            written.chars().count(),
            named.chars().count(),
            "a tie needs them equally short"
        );
        // Both really separate: this is a tie-break, not a wrong answer, and the return says so by
        // carrying neither `NerodeWordDoesNotSeparate` nor `LengthDisagreed`.
        for candidate in [&written, &named] {
            assert_ne!(
                codec.segment(candidate).unwrap(),
                twice.segment(candidate).unwrap(),
                "{candidate:?} must separate them"
            );
        }
    }

    /// A receiver that reads **which codec it is looking at** is an absolute frame, and the refusal
    /// that catches it is the one that fires when the congruence reports a separation it cannot
    /// witness.
    ///
    /// Declaring it puts the two rest states in different *one-shot* blocks, so the pair is never
    /// considered by the exhibition and no word comes back for a separation the return still claims.
    /// The material is a codec against **itself**, where every honest reading returns nothing at all.
    #[test]
    fn a_receiver_reading_which_codec_it_sees_reports_a_separation_it_cannot_witness() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");

        let honest = cross_check(codec, codec).expect("a codec is comparable with itself");
        assert_eq!(honest.disagreements, Vec::new());
        assert!(!honest.rest_states_separated);

        let system = CodecSystem::joint(&[codec, codec]).expect("comparable");
        let framed = CodecIndexReceiver { inner: &system };
        assert_eq!(framed.absolute_frame(), ReceiverId(2));
        let check =
            cross_check_over(&framed, &TheJointAutomaton, codec, codec).expect("comparable");
        assert_eq!(check.nerode_reading, "codec-index-receiver");
        assert!(!check.agrees());
        assert_eq!(
            check.disagreements,
            vec![SeparationSpecies::NerodeSeparatedWithoutExhibitingAWord]
        );
        assert!(check.rest_states_separated, "the frame claims a separation");
        assert!(check.nerode.is_none(), "and cannot exhibit a word for it");
        assert!(check.joint_automaton.is_none());
        // What an absolute frame does to a congruence, measured: it refines it, and every block it
        // returns is cut along the codec index and sits inside a block the honest reading returned.
        // That is the signature of a receiver-visible coordinate promoted into an invariant — the
        // congruence is finer everywhere and finer for a reason no input can reach.
        let honest_conduct = compress(&system).conduct;
        let framed_conduct = compress(&framed).conduct;
        assert!(
            framed_conduct.len() > honest_conduct.len(),
            "the frame must refine or it is not visible at all: {} against {}",
            honest_conduct.len(),
            framed_conduct.len()
        );
        for block in &framed_conduct.blocks {
            let first = *block.iter().next().expect("a block is not empty");
            let sides: BTreeSet<usize> = block
                .iter()
                .map(|item| system.state_of(*item).expect("an item of this system").codec)
                .collect();
            assert_eq!(sides.len(), 1, "a block of the frame spans both codecs: {block:?}");
            assert!(
                block
                    .iter()
                    .all(|item| honest_conduct.block_of(*item) == honest_conduct.block_of(first)),
                "the frame split a block the honest reading held together, which fewer \
                 distinctions cannot do: {block:?}"
            );
        }
    }

    /// **The aperture, stated.** All six species are produced by declared controls on committed
    /// material, so none of them is a name in an enum that nothing can reach. If a seventh is added
    /// without a control that fires it, this fails.
    #[test]
    fn every_separation_species_is_produced_by_a_declared_control() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let word = codec.class_of('a').expect("the word class is recovered");
        let digit = codec.class_of('0').expect("the digit class is recovered");
        let space = codec.class_of(' ').expect("the space class is recovered");
        let gauge = flipped(codec, word.0 as usize, space.0 as usize);
        let mut across = flipped(codec, word.0 as usize, space.0 as usize);
        across = flipped(&across, space.0 as usize, word.0 as usize);
        let mut twice = flipped(codec, word.0 as usize, word.0 as usize);
        twice = flipped(&twice, digit.0 as usize, digit.0 as usize);

        let mut produced: BTreeSet<SeparationSpecies> = BTreeSet::new();
        let mut record = |check: SeparationCrossCheck| {
            assert!(
                !check.disagreements.is_empty(),
                "{} against {} returned nothing",
                check.nerode_reading,
                check.joint_reading
            );
            produced.extend(check.disagreements);
        };

        let shadow_gauge = PushEventSystem::joint(&[codec, &gauge]).expect("comparable");
        record(
            cross_check_over(&shadow_gauge, &TheJointAutomaton, codec, &gauge).expect("comparable"),
        );
        let shadow_across = PushEventSystem::joint(&[codec, &across]).expect("comparable");
        record(
            cross_check_over(&shadow_across, &TheJointAutomaton, codec, &across)
                .expect("comparable"),
        );
        let real_gauge = CodecSystem::joint(&[codec, &gauge]).expect("comparable");
        record(
            cross_check_over(&real_gauge, &ThePushEventAutomaton, codec, &gauge)
                .expect("comparable"),
        );
        let real_twice = CodecSystem::joint(&[codec, &twice]).expect("comparable");
        record(
            cross_check_over(
                &ReversedInputOrder {
                    inner: &real_twice,
                },
                &TheJointAutomaton,
                codec,
                &twice,
            )
            .expect("comparable"),
        );
        let real_self = CodecSystem::joint(&[codec, codec]).expect("comparable");
        record(
            cross_check_over(
                &CodecIndexReceiver { inner: &real_self },
                &TheJointAutomaton,
                codec,
                codec,
            )
            .expect("comparable"),
        );

        assert_eq!(
            produced,
            BTreeSet::from([
                SeparationSpecies::ExistenceDisagreed,
                SeparationSpecies::LengthDisagreed,
                SeparationSpecies::TieBrokenDifferently,
                SeparationSpecies::NerodeWordDoesNotSeparate,
                SeparationSpecies::JointAutomatonWordDoesNotSeparate,
                SeparationSpecies::NerodeSeparatedWithoutExhibitingAWord,
            ]),
            "every species must be reachable by a declared control"
        );
    }

    /// The return survives being written out and read back, and says what it is.
    ///
    /// `SeparationCrossCheck` and `StepReturn` have derived `Serialize`/`Deserialize` since they
    /// were written and nothing ever round-tripped one, so the derive was a claim about octets that
    /// no material had tested.
    #[test]
    fn a_cross_check_written_out_and_read_back_is_the_same_structure() {
        let (left, right, _) = undetermined(2);
        let check = cross_check(&left, &right).expect("comparable");
        assert_eq!(check.schema, CROSS_CHECK_SCHEMA);
        assert_eq!(check.schema, "holonic-engine.codec-separation-cross-check.v1");

        let written = ron::ser::to_string(&check).expect("the return is serializable");
        let read_back: SeparationCrossCheck =
            ron::from_str(&written).expect("the octets are a cross-check");
        assert_eq!(read_back, check);
        // Not a trivial round trip: the material it carries is present on the far side.
        assert!(!read_back.compression.collapsed.is_empty());
        assert_eq!(
            read_back.nerode.expect("a separated pair").1,
            check.nerode.expect("a separated pair").1
        );

        let states = CodecSystem::new(&left).expect("adaptable");
        let written = ron::ser::to_string(states.states()).expect("states are serializable");
        let read_back: Vec<CodecState> = ron::from_str(&written).expect("the octets are states");
        assert_eq!(read_back, states.states());
        assert!(read_back.iter().any(|state| state.last == StepReturn::OpenedToken));
    }

    /// Both organs must refuse the same populations. A cross-check between two organs that disagree
    /// about what is answerable is not a cross-check.
    ///
    /// **That sentence was false when it was written, and the test could not detect it.** The body
    /// only asserted the adapter's side. On a codec whose classes and emission match but whose
    /// boundary is the wrong shape, `CodecSystem::joint` returned `MalformedBoundary` while
    /// `shortest_separating_input` **panicked** with an index out of bounds — found by adversarial
    /// review on 2026-08-08 and closed by giving `codec_recovery` the refusal it was missing. Both
    /// sides are asserted here now, and the shapes they name are compared.
    #[test]
    fn incomparable_codecs_are_refused_by_the_adapter_exactly_as_by_the_joint_automaton() {
        let recovery = tokenizer_recovery();
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let (other, _, _) = undetermined(2);

        assert_eq!(
            codec.shortest_separating_input(&other),
            Err(RecoveryError::IncomparableCodecs)
        );
        assert_eq!(
            CodecSystem::joint(&[codec, &other]).map(|_| ()),
            Err(AdaptationError::Recovery(RecoveryError::IncomparableCodecs))
        );
        assert_eq!(
            cross_check(codec, &other).map(|_| ()),
            Err(AdaptationError::Recovery(RecoveryError::IncomparableCodecs))
        );
        assert_eq!(
            CodecSystem::joint(&[]).map(|_| ()),
            Err(AdaptationError::NoCodecs)
        );

        // A boundary that is not square over the classes. Both organs, on the identical value.
        let malformed = RecoveredCodec {
            schema: codec.schema.clone(),
            classes: codec.classes.clone(),
            emission: codec.emission.clone(),
            boundary: vec![vec![Boundary::Join]],
        };
        assert_eq!(
            CodecSystem::joint(&[&malformed]).map(|_| ()),
            Err(AdaptationError::MalformedBoundary {
                codec: 0,
                rows: 1,
                columns: 1,
                classes: 5,
            })
        );
        assert_eq!(
            malformed.shortest_separating_input(codec),
            Err(RecoveryError::MalformedBoundary {
                rows: 1,
                columns: 1,
                classes: 5,
            })
        );
        assert_eq!(
            codec.shortest_separating_input(&malformed),
            Err(RecoveryError::MalformedBoundary {
                rows: 1,
                columns: 1,
                classes: 5,
            })
        );
        assert!(matches!(
            cross_check(codec, &malformed),
            Err(AdaptationError::MalformedBoundary { codec: 1, .. })
        ));
        // The push-event shadow takes the same admission, so a control cannot be exercised on
        // material the organ it controls would have refused.
        assert_eq!(
            PushEventSystem::joint(&[&malformed]).map(|_| ()),
            Err(AdaptationError::MalformedBoundary {
                codec: 0,
                rows: 1,
                columns: 1,
                classes: 5,
            })
        );
        assert_eq!(
            ThePushEventAutomaton
                .shortest_separating_input(codec, &malformed)
                .map(|_| ()),
            Err(AdaptationError::MalformedBoundary {
                codec: 1,
                rows: 1,
                columns: 1,
                classes: 5,
            })
        );

        // A codec with no classes admits no input, and both carriers say so.
        let empty = RecoveredCodec {
            schema: codec.schema.clone(),
            classes: Vec::new(),
            emission: Vec::new(),
            boundary: Vec::new(),
        };
        assert_eq!(
            CodecSystem::joint(&[&empty]).map(|_| ()),
            Err(AdaptationError::NoClasses)
        );
        assert_eq!(
            PushEventSystem::joint(&[&empty]).map(|_| ()),
            Err(AdaptationError::NoClasses)
        );

        // A carrier of one codec is not a joint carrier, and the cross-check says which it got
        // rather than reaching past the end of the rest population.
        let single = CodecSystem::new(codec).expect("adaptable");
        assert_eq!(single.rest_pair(), None);
        assert_eq!(
            cross_check_over(&single, &TheJointAutomaton, codec, codec).map(|_| ()),
            Err(AdaptationError::NotAJointCarrier { population: 1 })
        );
        let three = CodecSystem::joint(&[codec, codec, codec]).expect("adaptable");
        assert_eq!(
            cross_check_over(&three, &TheJointAutomaton, codec, codec).map(|_| ()),
            Err(AdaptationError::NotAJointCarrier { population: 3 })
        );
    }

    /// The declared receiver family, ablated. `ReceiverId(0)` is blind to boundaries by
    /// construction — emission is shared across a comparable population — so removing
    /// `ReceiverId(1)` must leave the two codecs indistinguishable, and removing either may only
    /// coarsen. The second half is the monotonicity `AblatedSystem` exists to make measurable; the
    /// first is a declared blindness stated as a theorem rather than observed as a rate.
    #[test]
    fn ablating_the_boundary_receiver_blinds_the_system_and_ablation_only_coarsens() {
        let (left, right, _) = undetermined(2);
        let system = CodecSystem::joint(&[&left, &right]).expect("comparable");
        let full = compress(&system);
        let rest = (
            system.rest_state(0).unwrap(),
            system.rest_state(1).unwrap(),
        );
        assert_ne!(
            full.conduct.block_of(rest.0),
            full.conduct.block_of(rest.1),
            "the full family must separate the two codecs or the ablation proves nothing"
        );

        let blinded = compress(&AblatedSystem {
            inner: &system,
            without: ReceiverId(1),
        });
        assert_eq!(
            blinded.conduct.block_of(rest.0),
            blinded.conduct.block_of(rest.1),
            "without the boundary receiver nothing can see the difference between two codecs"
        );

        for receiver in system.receivers() {
            let reduced = compress(&AblatedSystem {
                inner: &system,
                without: receiver,
            });
            assert!(
                reduced.conduct.len() <= full.conduct.len(),
                "ablating {receiver:?} refined {} -> {}",
                full.conduct.len(),
                reduced.conduct.len()
            );
            let reduced_pairs = reduced.conduct.identified_pairs();
            for pair in full.conduct.identified_pairs() {
                assert!(
                    reduced_pairs.contains(&pair),
                    "ablating {receiver:?} split {pair:?}, which fewer receivers cannot do"
                );
            }
        }
    }

}

// A determinism test stood here until 2026-08-08 and was deleted rather than repaired. It compared
// `cross_check(&left, &right)` against a second call with the same arguments, and an adversarial
// review measured it killed by **0 of 19** mutations — including one that broke
// `shortest_separating_input` badly enough to kill 10 of the other 11 tests. There is no `HashMap`
// or `HashSet` anywhere on this path: every container is a `BTreeMap`, a `BTreeSet` or a `VecDeque`,
// so determinism is forced by the container choice and no mutation of this organ can vary it. It was
// a theorem about the carrier wearing a measurement's name.
