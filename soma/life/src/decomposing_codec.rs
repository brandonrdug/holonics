//! The downward crossing: a decomposition whose grain is revised by what its own reading collapsed.
//!
//! ## What is absent that this supplies
//!
//! The laboratory's record names the missing direction plainly — *"`wr` is inert; founding is
//! byte-level bottom-up."* Every founding in that body reads a stream one octet at a time and grows
//! structure upward. Nothing takes a **whole** it already holds, cuts it into parts, discovers that
//! its cut was in the wrong place, and moves the cut. `blueprint/THE_ASSEMBLY.md` loop (a) is that
//! crossing: **DECOMPOSE → RE-INTEGRATE.**
//!
//! ```text
//!   a whole            ->  parts, under a declared grain          (DECOMPOSE)
//!   the parts          ->  a machine a byte-level reading conducts through
//!   that machine       ->  receiver_exact_compression::compress
//!   collapsed pairs    ->  one parented CodecVersion each, cutting at the pair's own word
//!   their join         ->  the program the next pass runs under   (RE-INTEGRATE)
//! ```
//!
//! ## The signal is the collapsed-pair population, not a verdict
//!
//! A verdict is a boolean about one artifact. A [`CollapsedPair`] is a structural statement about
//! the decomposition's own grain **with its length attached**: two positions the byte-level reading
//! merged, and the shortest word of material that shows they are not the same place. Nothing here
//! reduces that population to a count, a ratio, or a quality figure on its way anywhere. The whole
//! [`ReceiverExactCompression`] rides on [`DecompositionPass`], and every founded revision carries
//! the pair that founded it.
//!
//! ## What a program is, and why the revision is a structural change rather than a counter
//!
//! The program is a [`DecompositionGrain`]: a set of **words after which the decomposer closes a
//! part**. It is the reusable morphology — what the decomposer does to material it has never seen
//! is completely determined by it, and revising it changes later conduct on later material.
//! `CLAUDE.md` §13 obligation 1 asks for exactly that and refuses a counter in its place. There is
//! no weight, no bias, no threshold, no score, and no float in this file; the only ordering used
//! anywhere is `Ord` on words and on identities, which is canonicalization, not ranking.
//!
//! ## The receiver family, and why it is the one that can be wrong
//!
//! A part population is read as its **prefix machine**: items are the prefixes of parts, an input is
//! one symbol, and `successor(u, s)` is `u·s` when some part carries it and a declared terminus
//! otherwise. The declared receivers are byte-level and local — for each symbol, *does this symbol
//! continue here*, plus *does a part close here*. That is a radius-one reading, which is precisely
//! the reading a byte-level bottom-up founding has. Conduct sees every radius. A collapsed pair is
//! therefore a place where the grain owes the reading a boundary, and cutting at the pair's word
//! **pays that debt by moving material into the boundary** rather than by deepening the reading.
//!
//! ## The shape of the falsifier this module is built to be able to fail
//!
//! - Ablate the revision — run a second batch under the **parent** grain — and the collapsed
//!   population must not shrink. If it shrinks anyway the improvement came from the material.
//! - Run where [`ReceiverExactCompression::is_exact`] holds and **no codec version may be founded**.
//!   That is not a check bolted on: an exact pass returns [`CodecStep::Rest`], no reflection is
//!   opened, and [`DecomposingBody::revise`] has nothing to close. A mechanism that founds on every
//!   pass has a clock, not a consequence.
//! - And a foil: cut at a word of the same length that the compression did **not** return. If any
//!   cut whatsoever shrinks the population as much, the derivation is decorative and the crossing is
//!   "cutting more is better" wearing a lineage.

use core::fmt;
use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use holonic_engine::receiver_exact_compression::{
    compress, CollapsedPair, InputId, ItemId, Observation, ObservedSystem, ReceiverExactCompression,
    ReceiverId,
};
use holonic_language::{
    CodecCrossingError, CodecId, CodecLineageRefusal, CodecObstruction, CodecRevisionRefusal,
    CodecStep, ContinuationId, ContinuationState, FaceId, ReceiverId as CodecReceiverId,
    ReflectionId, ReflectiveCodecExecutor, ReflectiveRuntime, ReflectiveRuntimeError,
};
use holonic_structure::LocalSet;

const PASS_SCHEMA: &str = "life.decomposing-codec.pass.v1";

/// The receiver that reads *does a part close here*. Symbols occupy `0..=255` as receiver
/// identities, so this identity cannot collide with one of them.
pub const CLOSES_RECEIVER: u64 = 256;

/// One octet of material. Exact, and never read as a magnitude — only compared and concatenated.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub struct Symbol(pub u8);

impl Symbol {
    /// The input identity this symbol occupies. Inputs name symbols directly, which is what makes
    /// a returned `distinguishing_word` a word of material rather than an index into one.
    pub const fn input(self) -> InputId {
        InputId(self.0 as u64)
    }

    /// The receiver identity that reads *does this symbol continue here*.
    pub const fn continuation_receiver(self) -> ReceiverId {
        ReceiverId(self.0 as u64)
    }
}

/// Write a word over the alphabet so it can name a recruitment contact.
pub fn render_word(word: &[Symbol]) -> String {
    word.iter()
        .map(|symbol| {
            if symbol.0.is_ascii_graphic() {
                (symbol.0 as char).to_string()
            } else {
                format!("%{:02x}", symbol.0)
            }
        })
        .collect()
}

/// The reusable morphology: the words after which the decomposer closes a part.
///
/// A boundary is placed after position `i` of a whole when some grain word is a **suffix of the
/// whole read so far** — of the stream, not of the part currently open. A cut word may therefore
/// straddle an earlier boundary, which is what makes the grain a statement about context rather
/// than about part shape.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DecompositionGrain {
    cuts: BTreeSet<Vec<Symbol>>,
}

impl DecompositionGrain {
    /// Declare a grain. The empty word is refused: it is a suffix of every prefix, so a grain
    /// carrying it cuts after every symbol and the decomposition is the identity on octets. That is
    /// the degenerate reading in which the crossing has nothing to do, and it is refused rather
    /// than silently returning zero.
    pub fn declare(
        cuts: impl IntoIterator<Item = Vec<Symbol>>,
    ) -> Result<Self, DecompositionError> {
        let cuts: BTreeSet<Vec<Symbol>> = cuts.into_iter().collect();
        if cuts.iter().any(Vec::is_empty) {
            return Err(DecompositionError::EmptyCutWord);
        }
        if cuts.is_empty() {
            return Err(DecompositionError::EmptyGrain);
        }
        Ok(Self { cuts })
    }

    pub fn cuts(&self) -> &BTreeSet<Vec<Symbol>> {
        &self.cuts
    }

    /// The same grain with one more cut word. Monotone: a grain never loses a word, so a
    /// decomposition never coarsens along a lineage.
    pub fn with(&self, word: Vec<Symbol>) -> Result<Self, DecompositionError> {
        if word.is_empty() {
            return Err(DecompositionError::EmptyCutWord);
        }
        let mut cuts = self.cuts.clone();
        cuts.insert(word);
        Ok(Self { cuts })
    }

    /// The same grain with every word of a population added.
    pub fn with_all(
        &self,
        words: impl IntoIterator<Item = Vec<Symbol>>,
    ) -> Result<Self, DecompositionError> {
        let mut grain = self.clone();
        for word in words {
            grain = grain.with(word)?;
        }
        Ok(grain)
    }

    fn closes_after(&self, read: &[Symbol]) -> bool {
        self.cuts.iter().any(|cut| {
            read.len() >= cut.len() && &read[read.len() - cut.len()..] == cut.as_slice()
        })
    }
}

/// One whole, cut into parts, with the parts kept so the whole can be put back together.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecomposedWhole {
    pub source: Vec<Symbol>,
    pub parts: Vec<Vec<Symbol>>,
}

impl DecomposedWhole {
    /// RE-INTEGRATE: the whole, rebuilt from its parts and nothing else.
    pub fn reintegrate(&self) -> Vec<Symbol> {
        self.parts.concat()
    }
}

/// DECOMPOSE: cut a whole wherever the grain says to close, and at its end.
pub fn decompose(grain: &DecompositionGrain, whole: &[Symbol]) -> Vec<Vec<Symbol>> {
    let mut parts = Vec::new();
    let mut open: Vec<Symbol> = Vec::new();
    for (at, symbol) in whole.iter().enumerate() {
        open.push(*symbol);
        if at + 1 == whole.len() || grain.closes_after(&whole[..=at]) {
            parts.push(std::mem::take(&mut open));
        }
    }
    parts
}

/// The part population, read as the machine a byte-level reading conducts through.
///
/// Items are the **prefixes** of parts, root included. That is forced rather than chosen: with
/// items taken to be the parts themselves and inputs taken to be symbols, the only symbol-level
/// successor available is *the next part beginning with this symbol*, and part adjacency in a batch
/// is a relation and not a function — one part is routinely followed by two different parts sharing
/// a first symbol. `the_parts_alone_are_not_a_function_which_is_why_the_items_are_prefixes` exhibits
/// exactly that, on this module's own material.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartSystem {
    prefixes: Vec<Vec<Symbol>>,
    index: BTreeMap<Vec<Symbol>, ItemId>,
    complete: BTreeSet<Vec<Symbol>>,
    alphabet: Vec<Symbol>,
}

impl PartSystem {
    pub fn over_parts(parts: &[Vec<Symbol>]) -> Self {
        let mut prefixes: BTreeSet<Vec<Symbol>> = BTreeSet::from([Vec::new()]);
        let mut complete: BTreeSet<Vec<Symbol>> = BTreeSet::new();
        let mut alphabet: BTreeSet<Symbol> = BTreeSet::new();
        for part in parts {
            if part.is_empty() {
                continue;
            }
            complete.insert(part.clone());
            for at in 1..=part.len() {
                prefixes.insert(part[..at].to_vec());
            }
            alphabet.extend(part.iter().copied());
        }
        let prefixes: Vec<Vec<Symbol>> = prefixes.into_iter().collect();
        let index = prefixes
            .iter()
            .enumerate()
            .map(|(at, prefix)| (prefix.clone(), ItemId(at as u64)))
            .collect();
        Self {
            prefixes,
            index,
            complete,
            alphabet: alphabet.into_iter().collect(),
        }
    }

    pub fn prefixes(&self) -> &[Vec<Symbol>] {
        &self.prefixes
    }

    pub fn prefix_of(&self, item: ItemId) -> Option<&[Symbol]> {
        self.prefixes.get(item.0 as usize).map(Vec::as_slice)
    }

    pub fn alphabet(&self) -> &[Symbol] {
        &self.alphabet
    }

    /// The parts themselves, as opposed to their proper prefixes.
    pub fn parts(&self) -> &BTreeSet<Vec<Symbol>> {
        &self.complete
    }

    /// A returned word of inputs, read back as the word of material it names.
    ///
    /// This is the decoding boundary between the engine's `InputId` — a `u64`, which this module
    /// does not mint and cannot constrain — and an octet of material. Every `InputId` **this
    /// system** produces comes from [`Symbol::input`] and is therefore already an octet, so the
    /// refusal never fires on the module's own words. It fires across the public boundary, on an
    /// input from a foreign system, and
    /// `the_decoding_boundary_refuses_an_input_that_names_no_octet` fires it.
    pub fn word_symbols(&self, word: &[InputId]) -> Result<Vec<Symbol>, DecompositionError> {
        word.iter()
            .map(|input| {
                u8::try_from(input.0)
                    .map(Symbol)
                    .map_err(|_| DecompositionError::InputIsNotASymbol(*input))
            })
            .collect()
    }
}

impl ObservedSystem for PartSystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.prefixes.len())
            .map(|at| ItemId(at as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        let mut receivers: Vec<ReceiverId> = self
            .alphabet
            .iter()
            .map(|symbol| symbol.continuation_receiver())
            .collect();
        receivers.push(ReceiverId(CLOSES_RECEIVER));
        receivers
    }

    fn inputs(&self) -> Vec<InputId> {
        self.alphabet.iter().map(|symbol| symbol.input()).collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let Some(prefix) = self.prefix_of(item) else {
            return Observation(0);
        };
        if receiver.0 == CLOSES_RECEIVER {
            return Observation(u64::from(self.complete.contains(prefix)));
        }
        let Ok(symbol) = u8::try_from(receiver.0) else {
            return Observation(0);
        };
        let mut extended = prefix.to_vec();
        extended.push(Symbol(symbol));
        Observation(u64::from(self.index.contains_key(&extended)))
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let prefix = self.prefix_of(item)?;
        let symbol = u8::try_from(input.0).ok()?;
        let mut extended = prefix.to_vec();
        extended.push(Symbol(symbol));
        self.index.get(&extended).copied()
    }
}

/// One reading of one batch under one grain. The artifact, carried whole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecompositionPass {
    pub schema: String,
    pub grain: DecompositionGrain,
    pub decomposed: Vec<DecomposedWhole>,
    pub system: PartSystem,
    pub compression: ReceiverExactCompression,
}

impl DecompositionPass {
    /// The wholes, rebuilt from their parts. The RE-INTEGRATE half, returned rather than asserted.
    pub fn reintegration(&self) -> Vec<Vec<Symbol>> {
        self.decomposed
            .iter()
            .map(DecomposedWhole::reintegrate)
            .collect()
    }

    /// Every whole whose parts do not put it back together, with both words.
    ///
    /// This is the RE-INTEGRATE half's return: a **population**, exhibited, not a flag. On a pass
    /// [`read`] built it is empty, because [`decompose`] closes at the end of every whole — that
    /// emptiness is a property of `decompose` and carries no evidence about this accessor. What
    /// carries evidence is the accessor's behaviour on a whole whose parts really do not rebuild
    /// it, which `reintegration_exhibits_the_rebuilt_wholes_and_a_non_empty_failure_population`
    /// supplies directly, because [`DecomposedWhole`]'s fields are public and a caller may hold one
    /// this module did not cut.
    pub fn reintegration_failures(&self) -> Vec<(usize, Vec<Symbol>, Vec<Symbol>)> {
        self.decomposed
            .iter()
            .enumerate()
            .filter_map(|(at, whole)| {
                let rebuilt = whole.reintegrate();
                (rebuilt != whole.source).then_some((at, whole.source.clone(), rebuilt))
            })
            .collect()
    }

    /// The pooled parts, in the canonical order the part system indexes them by.
    pub fn parts(&self) -> &BTreeSet<Vec<Symbol>> {
        self.system.parts()
    }

    /// The population the crossing is driven by. Never a count on its way anywhere.
    pub fn collapsed(&self) -> &[CollapsedPair] {
        &self.compression.collapsed
    }

    /// The word each collapsed pair asks the grain to cut at, **in the pairs' own order**.
    ///
    /// The order is load-bearing rather than incidental: [`DecomposingBody::revise`] zips this
    /// return against [`DecompositionPass::collapsed`] positionally, so a permutation here attaches
    /// every word to the wrong pair and every founded version then cuts at a word its own retained
    /// pair did not ask for. The set of words is invariant under such a permutation, so a set
    /// assertion cannot see it;
    /// `the_byte_level_reading_over_collapses_and_every_pair_exhibits_its_own_shortest_word` pins
    /// this return **positionally**, and
    /// `every_collapsed_pair_founds_a_parented_codec_version_and_the_pass_resumes_under_their_join`
    /// recomputes each founded word from the pair the founded version retained.
    pub fn cut_words(&self) -> Result<Vec<Vec<Symbol>>, DecompositionError> {
        self.compression
            .collapsed
            .iter()
            .map(|pair| self.system.word_symbols(&pair.distinguishing_word))
            .collect()
    }
}

/// Read one batch under one grain, with no reflective machinery involved. The pure organ the
/// reflective body drives, and what a foil control is run through.
///
/// **There is no reintegration guard here, and its absence is a correction rather than an
/// omission.** Until 2026-08-08 this function compared `parts.concat()` against the whole and
/// returned a `ReintegrationRefused` error. That refusal could not fire: [`decompose`] pushes every
/// symbol into the open part and closes at the end of the whole, so `parts.concat() == whole` is an
/// identity of the loop rather than a property of the material, and deleting the guard killed no
/// test. Worse, it was the *flag* shape `blueprint/THE_ASSEMBLY.md` refuses — the crossing is
/// supposed to **return the failure population**, not refuse the batch. The population rides on
/// [`DecompositionPass::reintegration_failures`], where
/// `reintegration_exhibits_the_rebuilt_wholes_and_a_non_empty_failure_population` measures it on a
/// whole whose parts genuinely do not rebuild it.
pub fn read(
    grain: &DecompositionGrain,
    wholes: &[Vec<Symbol>],
) -> Result<DecompositionPass, DecompositionError> {
    let mut decomposed = Vec::with_capacity(wholes.len());
    let mut pooled: Vec<Vec<Symbol>> = Vec::new();
    for (at, whole) in wholes.iter().enumerate() {
        if whole.is_empty() {
            return Err(DecompositionError::EmptyWhole(at));
        }
        let parts = decompose(grain, whole);
        pooled.extend(parts.iter().cloned());
        decomposed.push(DecomposedWhole {
            source: whole.clone(),
            parts,
        });
    }
    let system = PartSystem::over_parts(&pooled);
    let compression = compress(&system);
    Ok(DecompositionPass {
        schema: PASS_SCHEMA.to_owned(),
        grain: grain.clone(),
        decomposed,
        system,
        compression,
    })
}

/// The codec body. A program is a grain plus the lineage of why this grain rather than its parent's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecompositionProgram {
    /// The declared origin grain. Byte-level: it closes on declared octets and reads a part only
    /// through the octet at its boundary.
    Origin(DecompositionGrain),
    /// A grain founded by **one** collapsed pair — the parent's grain with that pair's own shortest
    /// distinguishing word added as a cut. Its lineage is the pair, kept whole.
    CutAtDistinguishingWord {
        grain: DecompositionGrain,
        word: Vec<Symbol>,
        pair: CollapsedPair,
    },
    /// The join of every per-pair revision. This is the program the next pass runs under, and its
    /// parents are the per-pair versions rather than the reflected codec alone.
    JoinedRevision {
        grain: DecompositionGrain,
        words: Vec<Vec<Symbol>>,
    },
}

impl DecompositionProgram {
    pub fn grain(&self) -> &DecompositionGrain {
        match self {
            Self::Origin(grain)
            | Self::CutAtDistinguishingWord { grain, .. }
            | Self::JoinedRevision { grain, .. } => grain,
        }
    }
}

/// What the continuation carries between passes: the decomposer's own standing.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DecompositionStanding {
    passes: Vec<DecompositionPass>,
}

impl DecompositionStanding {
    pub fn passes(&self) -> &[DecompositionPass] {
        &self.passes
    }

    pub fn last(&self) -> Option<&DecompositionPass> {
        self.passes.last()
    }
}

/// One batch, presented.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecompositionFace {
    pub wholes: Vec<Vec<Symbol>>,
}

/// Why a decomposition, a revision, or a crossing was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecompositionError {
    EmptyCutWord,
    EmptyGrain,
    EmptyWhole(usize),
    InputIsNotASymbol(InputId),
    NoOpenReflection,
    Runtime(ReflectiveRuntimeError),
}

impl fmt::Display for DecompositionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{self:?}")
    }
}

impl std::error::Error for DecompositionError {}

impl From<ReflectiveRuntimeError> for DecompositionError {
    fn from(error: ReflectiveRuntimeError) -> Self {
        Self::Runtime(error)
    }
}

impl From<CodecRevisionRefusal<DecompositionProgram>> for DecompositionError {
    fn from(refusal: CodecRevisionRefusal<DecompositionProgram>) -> Self {
        Self::Runtime(refusal.error)
    }
}

impl From<CodecLineageRefusal<DecompositionProgram, String>> for DecompositionError {
    fn from(refusal: CodecLineageRefusal<DecompositionProgram, String>) -> Self {
        Self::Runtime(refusal.error)
    }
}

impl From<CodecCrossingError<DecompositionError, ()>> for DecompositionError {
    fn from(error: CodecCrossingError<DecompositionError, ()>) -> Self {
        match error {
            CodecCrossingError::Runtime(error)
            | CodecCrossingError::ReturnCouldNotCommit { error, .. } => Self::Runtime(error),
            CodecCrossingError::Executor(error) => error,
        }
    }
}

/// The decomposer, run as a codec.
///
/// It reflects exactly when its own reading over-collapsed, and rests otherwise. That asymmetry is
/// the whole of falsifier half two: an exact pass opens no reflection, so nothing downstream is in
/// a position to found a codec version, and the absence of a lineage entry is caused by the material
/// rather than checked for afterwards.
pub struct DecomposingExecutor;

impl ReflectiveCodecExecutor<DecompositionProgram, DecompositionStanding, DecompositionFace>
    for DecomposingExecutor
{
    type Emission = ();
    type Obstruction = DecompositionError;

    fn receive(
        &mut self,
        program: &DecompositionProgram,
        _instruction: u64,
        mut environment: DecompositionStanding,
        face: &DecompositionFace,
    ) -> Result<
        CodecStep<DecompositionStanding, ()>,
        CodecObstruction<DecompositionStanding, DecompositionError>,
    > {
        let pass = match read(program.grain(), &face.wholes) {
            Ok(pass) => pass,
            Err(obstruction) => {
                return Err(CodecObstruction {
                    environment,
                    obstruction,
                })
            }
        };
        // The receiver that asks for the lift is the one that saw the difference — an identity
        // carried into the reflection frame, never a reduction of the population, which rides
        // whole on the standing below.
        let receiver = pass
            .compression
            .collapsed
            .first()
            .map(|pair| match pair.witness {
                Some((receiver, _, _)) => receiver.0,
                None => CLOSES_RECEIVER,
            });
        environment.passes.push(pass);
        match receiver {
            Some(receiver) => Ok(CodecStep::Reflect {
                environment,
                receiver: CodecReceiverId(receiver),
                emission: (),
            }),
            None => Ok(CodecStep::Rest {
                environment,
                emission: (),
            }),
        }
    }
}

pub type DecomposingRuntime =
    ReflectiveRuntime<DecompositionProgram, DecompositionStanding, DecompositionFace, String>;

/// One codec version founded by one collapsed pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedRevision {
    pub codec: CodecId,
    pub word: Vec<Symbol>,
    pub pair: CollapsedPair,
}

/// What one revision returned: the per-pair versions, their join, and the words.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Revision {
    pub founded: Vec<FoundedRevision>,
    pub resumed: CodecId,
    pub parent: CodecId,
    pub words: BTreeSet<Vec<Symbol>>,
    pub grain: DecompositionGrain,
}

/// What one pass returned at the runtime's level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PassReturn {
    pub face: FaceId,
    pub codec: CodecId,
    pub reflection: Option<ReflectionId>,
    pub state: ContinuationState,
}

#[derive(Clone, Copy, Debug)]
struct OpenReflection {
    reflection: ReflectionId,
    face: FaceId,
}

/// A continuing decomposer: one runtime, one continuation, one lineage of grains.
pub struct DecomposingBody {
    runtime: DecomposingRuntime,
    continuation: ContinuationId,
    origin: CodecId,
    open: Option<OpenReflection>,
}

impl DecomposingBody {
    /// Mount a decomposer on a declared origin grain.
    ///
    /// The origin codec is caused by a declared origin face carrying no material — the declaration
    /// itself, which is what founded the grain. Every later codec is caused by the batch that
    /// occasioned it.
    pub fn mount(origin: DecompositionGrain) -> Result<Self, DecompositionError> {
        let mut runtime = DecomposingRuntime::default();
        let declaration = runtime
            .found_face(DecompositionFace { wholes: Vec::new() })
            .map_err(|(error, _)| DecompositionError::Runtime(error))?;
        let origin = runtime.mount_codec(DecompositionProgram::Origin(origin), declaration)?;
        let continuation = runtime
            .open_continuation(origin, DecompositionStanding::default())
            .map_err(|(error, _)| DecompositionError::Runtime(error))?;
        Ok(Self {
            runtime,
            continuation,
            origin,
            open: None,
        })
    }

    /// Present one batch under whichever codec the continuation currently carries.
    pub fn receive(&mut self, wholes: Vec<Vec<Symbol>>) -> Result<PassReturn, DecompositionError> {
        let codec = self.current_codec()?;
        let face = self
            .runtime
            .found_face(DecompositionFace { wholes })
            .map_err(|(error, _)| DecompositionError::Runtime(error))?;
        let emission = self
            .runtime
            .receive_with(self.continuation, face, &mut DecomposingExecutor)?;
        if let Some(reflection) = emission.reflection {
            self.open = Some(OpenReflection { reflection, face });
        }
        Ok(PassReturn {
            face,
            codec,
            reflection: emission.reflection,
            state: emission.state,
        })
    }

    /// Found one parented codec version per collapsed pair, then resume under their join.
    ///
    /// Refused when no reflection is open, which is exactly the case where the reading was already
    /// receiver-exact. Nothing here consults a count: the population is walked, and each member
    /// founds one version carrying the pair that founded it.
    ///
    /// **Two guards were deleted here on 2026-08-08 and their absence is the correction.** A
    /// `NothingCollapsed` refusal stood on a state this type's API cannot reach — `self.open` is set
    /// only by [`DecomposingBody::receive`], and only when the executor returned `Reflect`, which it
    /// returns only when the population is non-empty — and a `NoStanding` refusal stood on a
    /// continuation that has just committed a pass. Neither could fire; a refusal that cannot fire
    /// is not a refusal. The absence of standing is now named with the runtime's own word for it,
    /// [`ReflectiveRuntimeError::MalformedStanding`], because that is a condition of the foreign
    /// carrier rather than a declared refusal of this organ.
    pub fn revise(&mut self) -> Result<Revision, DecompositionError> {
        let Some(open) = self.open else {
            return Err(DecompositionError::NoOpenReflection);
        };
        let parent = self
            .runtime
            .reflection(open.reflection)
            .ok_or(DecompositionError::Runtime(
                ReflectiveRuntimeError::UnknownReflection(open.reflection),
            ))?
            .codec;
        let parent_grain = self
            .runtime
            .codec(parent)
            .ok_or(DecompositionError::Runtime(
                ReflectiveRuntimeError::UnknownCodec(parent),
            ))?
            .program
            .grain()
            .clone();

        let pass = self
            .standing()
            .and_then(DecompositionStanding::last)
            .ok_or(DecompositionError::Runtime(
                ReflectiveRuntimeError::MalformedStanding,
            ))?;
        let collapsed: Vec<CollapsedPair> = pass.compression.collapsed.clone();
        let words: Vec<Vec<Symbol>> = pass.cut_words()?;

        let mut founded = Vec::with_capacity(collapsed.len());
        let mut population: BTreeSet<Vec<Symbol>> = BTreeSet::new();
        for (pair, word) in collapsed.into_iter().zip(words) {
            if word.is_empty() {
                return Err(DecompositionError::EmptyCutWord);
            }
            let grain = parent_grain.with(word.clone())?;
            let codec = self.runtime.mount_codec_with_lineage(
                DecompositionProgram::CutAtDistinguishingWord {
                    grain,
                    word: word.clone(),
                    pair: pair.clone(),
                },
                open.face,
                LocalSet::from([parent]),
                LocalSet::from([render_word(&word)]),
            )?;
            population.insert(word.clone());
            founded.push(FoundedRevision { codec, word, pair });
        }

        let grain = parent_grain.with_all(population.iter().cloned())?;
        let parents: LocalSet<CodecId> = founded.iter().map(|founded| founded.codec).collect();
        let contacts: LocalSet<String> = population.iter().map(|word| render_word(word)).collect();
        let resumed = self.runtime.revise_and_resume_with_lineage(
            open.reflection,
            open.face,
            DecompositionProgram::JoinedRevision {
                grain: grain.clone(),
                words: population.iter().cloned().collect(),
            },
            parents,
            contacts,
        )?;
        self.open = None;
        Ok(Revision {
            founded,
            resumed,
            parent,
            words: population,
            grain,
        })
    }

    /// Close an open reflection without founding anything. **The ablation**: the parent grain keeps
    /// governing, and the next batch is read by the codec that already over-collapsed.
    pub fn resume_unrevised(&mut self) -> Result<(), DecompositionError> {
        let Some(open) = self.open.take() else {
            return Err(DecompositionError::NoOpenReflection);
        };
        self.runtime.resume_unchanged(open.reflection)?;
        Ok(())
    }

    pub fn runtime(&self) -> &DecomposingRuntime {
        &self.runtime
    }

    pub fn origin(&self) -> CodecId {
        self.origin
    }

    pub fn continuation(&self) -> ContinuationId {
        self.continuation
    }

    pub fn open_reflection(&self) -> Option<ReflectionId> {
        self.open.map(|open| open.reflection)
    }

    pub fn current_codec(&self) -> Result<CodecId, DecompositionError> {
        self.runtime
            .continuation(self.continuation)
            .map(|continuation| continuation.codec)
            .ok_or(DecompositionError::Runtime(
                ReflectiveRuntimeError::UnknownContinuation(self.continuation),
            ))
    }

    pub fn current_grain(&self) -> Result<&DecompositionGrain, DecompositionError> {
        let codec = self.current_codec()?;
        self.runtime
            .codec(codec)
            .map(|version| version.program.grain())
            .ok_or(DecompositionError::Runtime(
                ReflectiveRuntimeError::UnknownCodec(codec),
            ))
    }

    pub fn standing(&self) -> Option<&DecompositionStanding> {
        self.runtime
            .continuation(self.continuation)
            .and_then(|continuation| continuation.environment())
    }

    pub fn passes(&self) -> &[DecompositionPass] {
        self.standing().map_or(&[], DecompositionStanding::passes)
    }

    /// How many codec versions stand. A lineage census, read by the falsifier and by nothing in the
    /// conduct path.
    pub fn codec_population(&self) -> usize {
        self.runtime.codecs().count()
    }

    /// Every codec version a word founded. The recruitment index, keyed by the word itself.
    pub fn recruited_by(&self, word: &[Symbol]) -> Option<&LocalSet<CodecId>> {
        self.runtime.recruited_codecs(&render_word(word))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use holonic_engine::receiver_exact_compression::AblatedSystem;

    // -------------------------------------------------------------------------------------------
    // Material
    //
    // Three batches over one alphabet. Every whole carries several `.`-terminated chunks, so
    // RE-INTEGRATE is a real reassembly of several parts and not the identity on a single one.
    //
    // The structure is declared rather than stumbled on. Two independent species of ambiguity:
    //
    //   a junction   `a c d e f g` each continue only with `b`, and the six `?b` prefixes then
    //                branch differently. A radius-one reading sees "continues with b, does not
    //                close" for all of them and nothing else.
    //   a chain      `p q` continue only with `r`; `pr qr` continue only with `s`; `prs qrs`
    //                branch. The distinction is two and three steps away, so the returned words
    //                have different LENGTHS and a length claim is refutable.
    //
    // Batch C adds a second junction on `k`, whose word is NOT in the first revision's grain — so
    // the second pass improves without reaching zero, and the population is visibly a graded
    // structural signal rather than a verdict.
    // -------------------------------------------------------------------------------------------

    const BATCH_A: &[&str] = &["abx.aby.cbx.cbz.", "dby.dbz.ebx.eby.ebz.", "prsx.qrsy."];
    const BATCH_C: &[&str] = &[
        "abz.abw.cby.cbw.",
        "dbx.dbw.ebz.ebw.eby.",
        "fbx.fbw.gbz.gby.",
        "prsw.qrsz.",
        "mkx.mky.nkx.nkz.",
    ];
    const BATCH_D: &[&str] = &["abx.cbw.gby.prsz.", "mkw.nky.fbz.dbw."];

    /// Material the three batches above **cannot** produce, and which two properties of this module
    /// are invisible without.
    ///
    /// Every whole of `BATCH_A/C/D` ends on a `.`, which is a cut word, so the end-of-whole close in
    /// [`decompose`] never fires and could be deleted without a single assertion moving. And under a
    /// suffix-triggered cut every part there ends at a cut, so *a part closes here* and *this prefix
    /// is a leaf of the trie* coincide, and the close receiver could return a constant without a
    /// single assertion moving. **Both survived a mutation of this module and this fixture is why
    /// they no longer do.**
    ///
    /// The grain `{p, z, pab, .}` is what makes a part a proper prefix of another part: `pab` closes
    /// after `ab` only when a `p` precedes it, so `ab` is a whole part in one context and the opening
    /// of `abc.` in another. `pabx` then ends on no cut word at all.
    const BATCH_NESTED: &[&str] = &["pabx", "zabc.", "zxyc."];

    fn nested_grain() -> DecompositionGrain {
        DecompositionGrain::declare([word("p"), word("z"), word("pab"), word(".")])
            .expect("four non-empty cut words")
    }

    /// Wholes that end where no cut word does. Only the end-of-whole close returns their last part.
    const UNTERMINATED: &[&str] = &["abx.aby", "prsx", "mkx.mk", "z", "pabx"];

    /// Material on which the exhibition's **search order** is visible: one pair with a length-one
    /// separating word down `a` and a length-three one down the `z` chain. Under grain `{b}` each
    /// whole is one part, so the part population is exactly these four words. See
    /// `the_exhibited_word_is_the_shortest_where_a_longer_separating_word_also_exists`.
    const BRANCH_DEPTHS: &[&str] = &["uab", "va", "uzzzb", "vzzzc"];

    fn word(text: &str) -> Vec<Symbol> {
        text.bytes().map(Symbol).collect()
    }

    fn batch(wholes: &[&str]) -> Vec<Vec<Symbol>> {
        wholes.iter().map(|whole| word(whole)).collect()
    }

    fn origin_grain() -> DecompositionGrain {
        DecompositionGrain::declare([word(".")]).expect("one non-empty cut word")
    }

    /// The witness, written out: which receiver saw the difference and what the two returned.
    /// `separated by a terminus` when no receiver named it.
    fn witness_of(pair: &CollapsedPair) -> String {
        match pair.witness {
            Some((receiver, left, right)) => format!(
                "{} {}|{}",
                u8::try_from(receiver.0)
                    .map_or_else(|_| "closes".to_owned(), |symbol| render_word(&[Symbol(symbol)])),
                left.0,
                right.0
            ),
            None => "separated by a terminus".to_owned(),
        }
    }

    fn distinct_words(pass: &DecompositionPass) -> BTreeSet<String> {
        pass.cut_words()
            .expect("every returned word is over the alphabet")
            .iter()
            .map(|word| render_word(word))
            .collect()
    }

    /// The item a prefix names, found by scanning the population rather than through the system's
    /// own index, so the lookup is not the index restated.
    fn item_at(system: &PartSystem, prefix: &str) -> ItemId {
        let target = word(prefix);
        ItemId(
            system
                .prefixes()
                .iter()
                .position(|candidate| *candidate == target)
                .expect("a prefix of this system") as u64,
        )
    }

    /// **The declared control for search order.** The identical frontier walk
    /// `receiver_exact_compression::exhibit_collapsed` performs, with the queue replaced by a
    /// stack — the depth-first exhibition. It is not a second implementation of the organ and it
    /// grades nothing; it says what the *other* order would have returned, so that a fixture can
    /// prove its material is able to tell the two apart instead of assuming it.
    fn depth_first_separating_word(
        system: &PartSystem,
        left: ItemId,
        right: ItemId,
    ) -> Option<Vec<Symbol>> {
        let receivers = system.receivers();
        let inputs = system.inputs();
        let mut seen = BTreeSet::from([(Some(left), Some(right))]);
        let mut frontier: Vec<(Option<ItemId>, Option<ItemId>, Vec<InputId>)> =
            vec![(Some(left), Some(right), Vec::new())];
        while let Some((here, there, walk)) = frontier.pop() {
            if here.is_some() != there.is_some() {
                return system.word_symbols(&walk).ok();
            }
            let (Some(here_item), Some(there_item)) = (here, there) else {
                continue;
            };
            if !walk.is_empty()
                && receivers.iter().any(|receiver| {
                    system.observation(here_item, *receiver)
                        != system.observation(there_item, *receiver)
                })
            {
                return system.word_symbols(&walk).ok();
            }
            for input in &inputs {
                let next = (
                    system.successor(here_item, *input),
                    system.successor(there_item, *input),
                );
                if seen.insert(next) {
                    let mut extended = walk.clone();
                    extended.push(*input);
                    frontier.push((next.0, next.1, extended));
                }
            }
        }
        None
    }

    /// A pair, walked under a word, with no reference to how the word was found.
    fn separates(system: &PartSystem, left: ItemId, right: ItemId, walk: &[Symbol]) -> bool {
        let mut here = Some(left);
        let mut there = Some(right);
        for symbol in walk {
            here = here.and_then(|item| system.successor(item, symbol.input()));
            there = there.and_then(|item| system.successor(item, symbol.input()));
            if here.is_some() != there.is_some() {
                return true;
            }
            if here.is_none() {
                return false;
            }
        }
        let (Some(here), Some(there)) = (here, there) else {
            return false;
        };
        system
            .receivers()
            .into_iter()
            .any(|receiver| system.observation(here, receiver) != system.observation(there, receiver))
    }

    /// The shortest separating word by exhaustion. A third opinion: no partition refinement, no
    /// frontier, no visited set — the visited set being exactly the subtlety a shared bug would
    /// live in.
    fn brute_force_shortest(
        system: &PartSystem,
        left: ItemId,
        right: ItemId,
        limit: usize,
    ) -> Option<Vec<Symbol>> {
        let alphabet = system.alphabet().to_vec();
        for length in 1..=limit {
            let total = alphabet.len().checked_pow(length as u32)?;
            for ordinal in 0..total {
                let mut rest = ordinal;
                let mut walk = vec![alphabet[0]; length];
                for position in (0..length).rev() {
                    walk[position] = alphabet[rest % alphabet.len()];
                    rest /= alphabet.len();
                }
                if separates(system, left, right, &walk) {
                    return Some(walk);
                }
            }
        }
        None
    }

    // -------------------------------------------------------------------------------------------
    // DECOMPOSE and RE-INTEGRATE
    // -------------------------------------------------------------------------------------------

    /// The two halves are exact inverses, checked against a **second formulation** of the cut rule
    /// rather than against the same loop written twice: here the boundary positions are computed as
    /// a set and the parts sliced out of them, which is the statement `decompose` is supposed to
    /// realize and not the code that realizes it.
    #[test]
    fn decompose_and_reintegrate_are_exact_inverses_under_every_grain_in_the_lineage() {
        let grains = [
            origin_grain(),
            origin_grain().with(word("b")).unwrap(),
            origin_grain().with_all([word("b"), word("s"), word("rs")]).unwrap(),
            origin_grain()
                .with_all([word("b"), word("s"), word("rs"), word("k")])
                .unwrap(),
            DecompositionGrain::declare([word("bx"), word(".")]).unwrap(),
            nested_grain(),
        ];
        let mut cut_counts: BTreeSet<usize> = BTreeSet::new();
        let mut closed_by_end_of_whole = 0usize;
        for grain in &grains {
            for whole in batch(BATCH_A)
                .into_iter()
                .chain(batch(BATCH_C))
                .chain(batch(BATCH_D))
                .chain(batch(BATCH_NESTED))
                .chain(batch(UNTERMINATED))
            {
                if !grain.closes_after(&whole) {
                    closed_by_end_of_whole += 1;
                }
                let parts = decompose(grain, &whole);
                assert_eq!(parts.concat(), whole, "re-integration lost material");

                // The second frame: boundaries as a set of positions, parts as the slices between.
                let boundaries: Vec<usize> = (0..whole.len())
                    .filter(|at| *at + 1 == whole.len() || grain.closes_after(&whole[..=*at]))
                    .collect();
                let mut expected = Vec::new();
                let mut from = 0usize;
                for at in &boundaries {
                    expected.push(whole[from..=*at].to_vec());
                    from = at + 1;
                }
                assert_eq!(parts, expected, "the two formulations of the cut disagree");
                cut_counts.insert(parts.len());
            }
        }
        assert!(
            cut_counts.len() > 3,
            "the sweep must produce genuinely different part counts, saw {cut_counts:?}"
        );
        assert!(
            closed_by_end_of_whole >= 10,
            "the sweep must contain wholes that end where no cut word does, or the end-of-whole \
             close is never exercised and could be deleted: {closed_by_end_of_whole}"
        );
    }

    /// **Every declared receiver must do work no other can**, or the family is padded and an
    /// ablation of it proves nothing. Checked on material where *a part closes here* and *this
    /// prefix is a leaf* come apart — which the three main batches cannot produce, because under a
    /// suffix-triggered cut every part of theirs ends exactly at a cut.
    #[test]
    fn the_close_receiver_and_the_continuation_receivers_each_do_work_no_other_can() {
        let pass = read(&nested_grain(), &batch(BATCH_NESTED)).expect("readable");
        assert_eq!(
            pass.parts()
                .iter()
                .map(|part| render_word(part))
                .collect::<Vec<_>>(),
            vec![
                "ab".to_owned(),
                "abc.".to_owned(),
                "p".to_owned(),
                "x".to_owned(),
                "xyc.".to_owned(),
                "z".to_owned(),
            ]
        );
        // The property the main batches cannot exhibit: a complete part that still continues.
        let nested: Vec<String> = pass
            .parts()
            .iter()
            .filter(|part| {
                pass.system
                    .prefixes()
                    .iter()
                    .any(|other| other.len() > part.len() && other.starts_with(part))
            })
            .map(|part| render_word(part))
            .collect();
        assert_eq!(nested, vec!["ab".to_owned(), "x".to_owned()]);

        let full = compress(&pass.system);
        assert!(full.is_exact());

        // Ablate the close receiver: two prefixes that differ only in whether a part closes there
        // fall together, so the partition must coarsen. If it does not, the receiver is redundant.
        let without_close = compress(&AblatedSystem {
            inner: &pass.system,
            without: ReceiverId(CLOSES_RECEIVER),
        });
        assert_eq!(full.one_shot.len(), 7);
        assert_eq!(full.conduct.len(), 7);
        assert_eq!(without_close.one_shot.len(), 6);
        assert_eq!(without_close.conduct.len(), 6);
        assert_ne!(
            full.conduct, without_close.conduct,
            "the close receiver returns nothing the continuation receivers already return"
        );

        // Ablate one continuation receiver: a distinction that was one-shot becomes a collapsed
        // pair, so the population is provably capable of moving under a receiver change.
        let without_c = compress(&AblatedSystem {
            inner: &pass.system,
            without: Symbol(b'c').continuation_receiver(),
        });
        assert!(!without_c.is_exact());
        assert_eq!(without_c.collapsed.len(), 4);
        let exhibited: BTreeSet<(String, String, String)> = without_c
            .collapsed
            .iter()
            .map(|pair| {
                (
                    render_word(pass.system.prefix_of(pair.left).expect("an item")),
                    render_word(pass.system.prefix_of(pair.right).expect("an item")),
                    render_word(
                        &pass
                            .system
                            .word_symbols(&pair.distinguishing_word)
                            .expect("a word"),
                    ),
                )
            })
            .collect();
        assert_eq!(
            exhibited,
            BTreeSet::from([
                ("ab".to_owned(), "abc.".to_owned(), "c".to_owned()),
                ("ab".to_owned(), "p".to_owned(), "c".to_owned()),
                ("ab".to_owned(), "xyc.".to_owned(), "c".to_owned()),
                ("ab".to_owned(), "z".to_owned(), "c".to_owned()),
            ]),
            "blinding the `c` receiver merges `ab` into the terminal block, and conduct still \
             separates it because only `ab` has a `c` successor"
        );
    }

    /// **A finding about `blueprint/THE_ASSEMBLY.md` loop (a), exhibited rather than argued.**
    ///
    /// *"compression runs over the parts"* cannot mean items are the parts and inputs are symbols:
    /// the only symbol-level successor available on parts is *the next part beginning with this
    /// symbol*, and part adjacency is a relation, not a function. Two wholes suffice to show it, and
    /// `ObservedSystem::successor` returns `Option<ItemId>` with no room for a plural return — so
    /// the items are the parts' prefixes, and the parts are exactly the prefixes that close.
    #[test]
    fn the_parts_alone_are_not_a_function_which_is_why_the_items_are_the_parts_prefixes() {
        let grain = origin_grain();
        let material = batch(&["ab.ax.", "ab.ay."]);
        let pass = read(&grain, &material).expect("readable");

        let mut adjacency: BTreeMap<(Vec<Symbol>, Symbol), BTreeSet<Vec<Symbol>>> = BTreeMap::new();
        for whole in &pass.decomposed {
            for step in whole.parts.windows(2) {
                adjacency
                    .entry((step[0].clone(), step[1][0]))
                    .or_default()
                    .insert(step[1].clone());
            }
        }
        let ambiguous: Vec<_> = adjacency
            .iter()
            .filter(|(_, landing)| landing.len() > 1)
            .collect();
        assert_eq!(
            ambiguous.len(),
            1,
            "the material must exhibit the ambiguity: {adjacency:?}"
        );
        let ((from, symbol), landing) = ambiguous[0];
        assert_eq!(render_word(from), "ab.");
        assert_eq!(render_word(&[*symbol]), "a");
        assert_eq!(
            landing
                .iter()
                .map(|part| render_word(part))
                .collect::<Vec<_>>(),
            vec!["ax.".to_owned(), "ay.".to_owned()]
        );

        // And the prefix reading of the same material is total wherever a prefix continues at all.
        for item in pass.system.items() {
            let prefix = pass.system.prefix_of(item).expect("an item of this system");
            for input in pass.system.inputs() {
                let symbol = Symbol(u8::try_from(input.0).expect("inputs name symbols"));
                let mut extended = prefix.to_vec();
                extended.push(symbol);
                assert_eq!(
                    pass.system.successor(item, input).is_some(),
                    pass.system.prefixes().contains(&extended),
                    "the successor and the prefix population disagree at {:?}",
                    render_word(prefix)
                );
            }
        }
    }

    // -------------------------------------------------------------------------------------------
    // The reading, and the population it returns
    // -------------------------------------------------------------------------------------------

    /// **The provably non-zero control** (`CLAUDE.md` §8: a law that returns zero proves nothing
    /// about itself). The census is pinned, every pair is exhibited, every returned word is walked
    /// under a routine that knows nothing about how it was found, and its minimality is confirmed
    /// by exhaustion.
    #[test]
    fn the_byte_level_reading_over_collapses_and_every_pair_exhibits_its_own_shortest_word() {
        let pass = read(&origin_grain(), &batch(BATCH_A)).expect("readable");

        assert_eq!(pass.system.prefixes().len(), 37);
        assert_eq!(pass.parts().len(), 11);
        assert_eq!(pass.compression.one_shot.len(), 12);
        assert_eq!(pass.compression.conduct.len(), 17);
        assert_eq!(pass.compression.rounds, 2);
        assert!(!pass.compression.is_exact());
        assert_eq!(pass.collapsed().len(), 8);

        // The artifact, named. Six pairs at the `b` junction and two down the `rs` chain, each with
        // the receiver that finally saw the difference and what the two returned — the witness is
        // exhibited rather than asserted to exist, because `witness.is_some()` is `!terminus`
        // restated in the carrier's own construction and carries no evidence.
        let exhibited: Vec<(String, String, String, String)> = pass
            .collapsed()
            .iter()
            .map(|pair| {
                (
                    render_word(pass.system.prefix_of(pair.left).expect("an item")),
                    render_word(pass.system.prefix_of(pair.right).expect("an item")),
                    render_word(
                        &pass
                            .system
                            .word_symbols(&pair.distinguishing_word)
                            .expect("a word over the alphabet"),
                    ),
                    witness_of(pair),
                )
            })
            .collect();
        assert_eq!(
            exhibited,
            vec![
                ("a".to_owned(), "c".to_owned(), "b".to_owned(), "y 1|0".to_owned()),
                ("a".to_owned(), "d".to_owned(), "b".to_owned(), "x 1|0".to_owned()),
                ("a".to_owned(), "e".to_owned(), "b".to_owned(), "z 0|1".to_owned()),
                ("c".to_owned(), "d".to_owned(), "b".to_owned(), "x 1|0".to_owned()),
                ("c".to_owned(), "e".to_owned(), "b".to_owned(), "y 0|1".to_owned()),
                ("d".to_owned(), "e".to_owned(), "b".to_owned(), "x 0|1".to_owned()),
                ("p".to_owned(), "q".to_owned(), "rs".to_owned(), "x 1|0".to_owned()),
                ("pr".to_owned(), "qr".to_owned(), "s".to_owned(), "x 1|0".to_owned()),
            ]
        );
        // Three different receivers name the eight differences, in both orientations. A family in
        // which one receiver did all the work would be a family with one live member.
        assert_eq!(
            pass.collapsed()
                .iter()
                .filter_map(|pair| pair.witness.map(|(receiver, _, _)| receiver))
                .collect::<BTreeSet<_>>()
                .len(),
            3
        );

        // `cut_words` is pinned POSITIONALLY, against the pairs above. Its doc claims the pairs'
        // own order, `revise` zips it against the population positionally, and the SET of words is
        // invariant under any permutation of it — so only a positional pin can see a permutation.
        assert_eq!(
            pass.cut_words()
                .expect("every returned word is over the alphabet")
                .iter()
                .map(|word| render_word(word))
                .collect::<Vec<_>>(),
            vec!["b", "b", "b", "b", "b", "b", "rs", "s"]
        );
        assert_eq!(distinct_words(&pass), BTreeSet::from(["b".to_owned(), "rs".to_owned(), "s".to_owned()]));

        // Lengths must actually vary, or "shortest" is not a claim this material can refute.
        let lengths: BTreeSet<usize> = pass
            .collapsed()
            .iter()
            .map(|pair| pair.distinguishing_word.len())
            .collect();
        assert_eq!(lengths, BTreeSet::from([1, 2]));

        for pair in pass.collapsed() {
            assert!(
                !pair.distinguishing_word.is_empty(),
                "the empty word is the one-shot reading and held these together"
            );
            let walk = pass
                .system
                .word_symbols(&pair.distinguishing_word)
                .expect("a word over the alphabet");
            assert!(
                separates(&pass.system, pair.left, pair.right, &walk),
                "the returned word {:?} does not in fact separate the pair",
                render_word(&walk)
            );
            let brute = brute_force_shortest(&pass.system, pair.left, pair.right, walk.len() + 1)
                .expect("some word separates a collapsed pair");
            assert_eq!(
                brute.len(),
                walk.len(),
                "returned {:?} but exhaustion found {:?}",
                render_word(&walk),
                render_word(&brute)
            );
        }
    }

    /// **The declared aperture, stated as a theorem instead of left as an unexplained absence.**
    ///
    /// No collapsed pair here is separated by a terminus, and that is forced rather than lucky. The
    /// declared family carries a receiver *per symbol* reading "does this symbol continue here", so
    /// two items identified one-shot agree on which symbols continue and their successors are
    /// jointly present or jointly absent. Any deeper node whose successors split was reached from a
    /// parent that already differed on that symbol's receiver — and the exhibition breaks on a
    /// witness before enqueuing the child. So the terminus species is unreachable **for this
    /// family**, not unreachable in general, and the control below proves the difference by handing
    /// the same part population a family that cannot see continuations.
    #[test]
    fn a_terminus_separation_is_unreachable_for_this_family_and_reachable_for_a_blinder_one() {
        for material in [BATCH_A, BATCH_C, BATCH_D] {
            let pass = read(&origin_grain(), &batch(material)).expect("readable");
            assert!(
                pass.collapsed()
                    .iter()
                    .all(|pair| !pair.separated_by_terminus),
                "a terminus separation is impossible for a family reading every continuation"
            );
        }

        /// The same prefix machine, read only through *does a part close here*. A blind family
        /// cannot see that one prefix continues and another does not, so the terminus does the
        /// separating.
        struct ClosesOnly(PartSystem);
        impl ObservedSystem for ClosesOnly {
            fn items(&self) -> Vec<ItemId> {
                self.0.items()
            }
            fn receivers(&self) -> Vec<ReceiverId> {
                vec![ReceiverId(CLOSES_RECEIVER)]
            }
            fn inputs(&self) -> Vec<InputId> {
                self.0.inputs()
            }
            fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
                self.0.observation(item, receiver)
            }
            fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
                self.0.successor(item, input)
            }
        }

        let pass = read(&origin_grain(), &batch(BATCH_A)).expect("readable");
        let blinded = compress(&ClosesOnly(pass.system.clone()));
        assert!(!blinded.is_exact());
        assert!(
            blinded
                .collapsed
                .iter()
                .any(|pair| pair.separated_by_terminus),
            "the terminus species must be reachable, or its absence above says nothing"
        );
    }

    // -------------------------------------------------------------------------------------------
    // The crossing
    // -------------------------------------------------------------------------------------------

    /// One parented codec version per collapsed pair, resumed under their join, with the lineage
    /// recording which pair asked for what.
    #[test]
    fn every_collapsed_pair_founds_a_parented_codec_version_and_the_pass_resumes_under_their_join() {
        let mut body = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        assert_eq!(body.codec_population(), 1);

        let first = body.receive(batch(BATCH_A)).expect("readable");
        assert_eq!(first.codec, body.origin());
        assert!(matches!(first.state, ContinuationState::Reflected(_)));
        let reflection = first.reflection.expect("an over-collapsed reading reflects");

        // The reflection names the receiver that saw the first difference, and the population it
        // came from rides whole on the standing.
        let frame = body.runtime().reflection(reflection).expect("a frame");
        assert_eq!(frame.receiver, CodecReceiverId(u64::from(b'y')));
        assert_eq!(body.passes().len(), 1);
        assert_eq!(body.passes()[0].collapsed().len(), 8);

        let revision = body.revise().expect("a collapsed population revises");
        assert_eq!(revision.founded.len(), 8, "one version per collapsed pair");
        assert_eq!(revision.parent, body.origin());
        assert_eq!(
            revision.words,
            BTreeSet::from([word("b"), word("rs"), word("s")])
        );
        assert_eq!(
            revision.grain.cuts(),
            &BTreeSet::from([word("."), word("b"), word("rs"), word("s")])
        );
        assert_eq!(body.codec_population(), 1 + 8 + 1);

        // Each per-pair version carries its own pair and cuts at THAT pair's own word.
        //
        // Both halves are recomputed rather than compared against themselves. `revise` clones one
        // `word` binding into the program and into the `FoundedRevision`, so `word == founded.word`
        // is a value against its own clone and passes under any permutation of `cut_words`; and
        // `grain.cuts().contains(word)` is a superset test, so it passes when every version carries
        // the join of all eight words and the per-pair program is vacuous. The word is therefore
        // DERIVED from the pair the version itself retained, and the grain is checked by EQUALITY
        // against the parent grain extended by that one word.
        let reading = &body.passes()[0];
        for (at, founded) in revision.founded.iter().enumerate() {
            let version = body
                .runtime()
                .codec(founded.codec)
                .expect("a founded version stands");
            assert_eq!(version.parents.len(), 1);
            assert!(version.parents.contains(&body.origin()));
            assert_eq!(version.contacts().len(), 1);
            match &version.program {
                DecompositionProgram::CutAtDistinguishingWord { grain, word, pair } => {
                    assert_eq!(
                        pair,
                        &reading.collapsed()[at],
                        "the versions are founded in the reading's own order"
                    );
                    let derived = reading
                        .system
                        .word_symbols(&pair.distinguishing_word)
                        .expect("a word over the alphabet");
                    assert_eq!(
                        word, &derived,
                        "version {at} cuts at {:?} but its own retained pair asks for {:?}",
                        render_word(word),
                        render_word(&derived)
                    );
                    assert_eq!(&founded.word, &derived);
                    assert_eq!(
                        grain,
                        &origin_grain().with(derived.clone()).expect("non-empty"),
                        "a per-pair grain is the parent's grain plus EXACTLY this pair's word"
                    );
                }
                other => panic!("a per-pair version must cut at its pair's word, got {other:?}"),
            }
        }

        // The resumed version's parents are the per-pair versions AND the reflected codec.
        let resumed = body
            .runtime()
            .codec(revision.resumed)
            .expect("the resumed version stands");
        assert_eq!(resumed.parents.len(), 9);
        assert!(resumed.parents.contains(&body.origin()));
        for founded in &revision.founded {
            assert!(resumed.parents.contains(&founded.codec));
        }
        assert_eq!(resumed.contacts().len(), 3);
        assert_eq!(body.current_codec().unwrap(), revision.resumed);
        assert_eq!(body.current_grain().unwrap(), &revision.grain);

        // Recruitment is keyed by the word, and the POPULATION is asserted rather than its size.
        // A count cannot see a permutation of the words across the pairs: reversing eight pairs
        // leaves `b` recruiting seven, `s` two and `rs` two, because a permutation preserves a
        // multiset. The expected index below is built from the READING's pairs — each pair's own
        // derived word against the version founded at that pair's position — so a misattachment
        // moves a codec identity from one key to another and the maps disagree.
        let mut expected: BTreeMap<String, BTreeSet<CodecId>> = BTreeMap::new();
        for (at, pair) in reading.collapsed().iter().enumerate() {
            let derived = reading
                .system
                .word_symbols(&pair.distinguishing_word)
                .expect("a word over the alphabet");
            expected
                .entry(render_word(&derived))
                .or_default()
                .insert(revision.founded[at].codec);
        }
        for asked in &revision.words {
            expected
                .entry(render_word(asked))
                .or_default()
                .insert(revision.resumed);
        }
        let observed: BTreeMap<String, BTreeSet<CodecId>> = ["b", "rs", "s"]
            .into_iter()
            .map(|text| {
                (
                    text.to_owned(),
                    body.recruited_by(&word(text))
                        .expect("a word some version was founded on")
                        .iter()
                        .copied()
                        .collect::<BTreeSet<CodecId>>(),
                )
            })
            .collect();
        assert_eq!(observed, expected);
        // And pinned as an artifact, so the derivation above cannot drift with the code.
        assert_eq!(
            observed
                .iter()
                .map(|(text, codecs)| {
                    (
                        text.clone(),
                        codecs.iter().map(|codec| codec.0).collect::<Vec<_>>(),
                    )
                })
                .collect::<Vec<_>>(),
            vec![
                ("b".to_owned(), vec![1, 2, 3, 4, 5, 6, 9]),
                ("rs".to_owned(), vec![7, 9]),
                ("s".to_owned(), vec![8, 9]),
            ]
        );
        assert_eq!(body.recruited_by(&word("k")), None);

        // The reflection is closed, and a second revision of it is refused.
        assert_eq!(body.open_reflection(), None);
        assert_eq!(body.revise(), Err(DecompositionError::NoOpenReflection));
    }

    /// A reflected body does not silently keep reading. The lift must be returned — revised or
    /// resumed unchanged — before more material crosses, or a second batch would be read under a
    /// codec the first batch already asked to have replaced.
    #[test]
    fn a_body_with_an_open_reflection_refuses_the_next_batch() {
        let mut body = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        body.receive(batch(BATCH_A)).expect("readable");
        assert!(body.open_reflection().is_some());
        assert!(matches!(
            body.receive(batch(BATCH_C)),
            Err(DecompositionError::Runtime(
                ReflectiveRuntimeError::ContinuationNotRunning(_)
            ))
        ));
        assert_eq!(body.passes().len(), 1, "the refused batch left no pass");
        assert_eq!(body.codec_population(), 1);

        body.resume_unrevised().expect("an open reflection");
        assert_eq!(body.current_codec().unwrap(), body.origin());
        body.receive(batch(BATCH_C))
            .expect("a resumed body reads again");
        assert_eq!(body.passes().len(), 2);
        assert_eq!(body.passes()[1].collapsed().len(), 17);
    }

    /// The revision is a structural change in reusable morphology: it decomposes material it has
    /// never seen differently. The parts are exhibited, not counted.
    #[test]
    fn the_revised_grain_decomposes_unseen_material_differently() {
        let mut body = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        body.receive(batch(BATCH_A)).expect("readable");
        let revision = body.revise().expect("a collapsed population revises");

        let unseen = batch(BATCH_C);
        let before = decompose(&origin_grain(), &unseen[0]);
        let after = decompose(&revision.grain, &unseen[0]);
        assert_eq!(
            before.iter().map(|p| render_word(p)).collect::<Vec<_>>(),
            vec!["abz.", "abw.", "cby.", "cbw."]
        );
        assert_eq!(
            after.iter().map(|p| render_word(p)).collect::<Vec<_>>(),
            vec!["ab", "z.", "ab", "w.", "cb", "y.", "cb", "w."]
        );
        assert_eq!(before.concat(), unseen[0]);
        assert_eq!(after.concat(), unseen[0], "the finer cut still re-integrates");
    }

    // -------------------------------------------------------------------------------------------
    // FALSIFIER, half one: ablate the revision
    // -------------------------------------------------------------------------------------------

    /// Two bodies on the same material. One revises; one closes each reflection unchanged and keeps
    /// reading under the grain that over-collapsed.
    ///
    /// Both halves are required. The revised body's population must shrink **on the same batch**,
    /// and the ablated body's must not shrink relative to the batch that founded the revision —
    /// otherwise the improvement came from the material and the crossing is decorative.
    #[test]
    fn ablating_the_revision_leaves_the_collapsed_population_unshrunk() {
        let mut revised = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        revised.receive(batch(BATCH_A)).expect("readable");
        revised.revise().expect("a collapsed population revises");
        revised.receive(batch(BATCH_C)).expect("readable");
        revised.revise().expect("a collapsed population revises");
        let third = revised.receive(batch(BATCH_D)).expect("readable");

        let mut ablated = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        ablated.receive(batch(BATCH_A)).expect("readable");
        ablated.resume_unrevised().expect("an open reflection");
        ablated.receive(batch(BATCH_C)).expect("readable");
        ablated.resume_unrevised().expect("an open reflection");
        ablated.receive(batch(BATCH_D)).expect("readable");

        let revised_population: Vec<usize> =
            revised.passes().iter().map(|pass| pass.collapsed().len()).collect();
        let ablated_population: Vec<usize> =
            ablated.passes().iter().map(|pass| pass.collapsed().len()).collect();
        assert_eq!(revised_population, vec![8, 1, 0]);
        assert_eq!(ablated_population, vec![8, 17, 10]);

        // Half one: on the SAME batch, the revision shrank it and the ablation did not.
        assert!(revised_population[1] < ablated_population[1]);
        assert!(revised_population[2] < ablated_population[2]);
        // Half two: the ablated body's later populations did not shrink below the pass that
        // founded the revision, so the later material is not simply easier.
        assert!(ablated_population[1] >= ablated_population[0]);
        assert!(ablated_population[2] >= ablated_population[0]);
        // And the two bodies read the identical first batch identically, so the only difference
        // downstream is the revision.
        assert_eq!(revised.passes()[0], ablated.passes()[0]);

        // The ablated body founded nothing at all, and never rests, because its reading never
        // becomes exact.
        assert_eq!(ablated.codec_population(), 1);
        assert_eq!(ablated.current_codec().unwrap(), ablated.origin());
        assert!(ablated
            .passes()
            .iter()
            .all(|pass| pass.grain == origin_grain()));

        // The revised body's third pass was exact, so it rested rather than reflecting.
        assert_eq!(third.reflection, None);
        assert_eq!(third.state, ContinuationState::Rested);
    }

    /// **The foil.** If any cut whatsoever shrank the population as much, the derivation would be
    /// decorative and the crossing would be "cutting more is better" wearing a lineage.
    ///
    /// Three foils on the batch the second pass reads, all against the same parent grain:
    /// words that do not occur (the decomposition is bit-identical, so the population cannot move);
    /// words that do occur and do change the decomposition; and **five** single-symbol words,
    /// strictly more cuts than the revision's three and including one of the revision's own answers.
    #[test]
    fn a_foil_grain_does_not_shrink_the_population_and_more_cuts_is_not_better() {
        let material = batch(BATCH_C);
        let parent = origin_grain();
        let derived = parent
            .with_all([word("b"), word("s"), word("rs")])
            .expect("three words");

        let under = |grain: &DecompositionGrain| {
            let pass = read(grain, &material).expect("readable");
            (
                pass.collapsed().len(),
                pass.system.prefixes().len(),
                pass.parts().len(),
            )
        };

        let baseline = under(&parent);
        let revision = under(&derived);
        let absent = under(&parent.with_all([word("W"), word("Z"), word("AB")]).unwrap());
        let present = under(&parent.with_all([word("x"), word("z"), word("ab")]).unwrap());
        let more = under(
            &parent
                .with_all([word("x"), word("y"), word("z"), word("w"), word("k")])
                .unwrap(),
        );

        assert_eq!(baseline, (17, 61, 19));
        assert_eq!(revision, (1, 39, 16));
        // Absent words: the decomposition is untouched, so the population provably cannot move.
        assert_eq!(absent, baseline);
        // Present words: the decomposition really did change, and the population did not.
        assert_eq!(present, (17, 53, 21));
        assert_eq!(present.0, baseline.0);
        assert_ne!(present.1, baseline.1, "the foil must really re-cut the material");
        // Five cuts, including `k` which the SECOND revision does return, still barely moves it.
        assert_eq!(more, (16, 42, 21));
        assert!(more.0 > revision.0 * 10);
        assert!(
            revision.0 < present.0 && revision.0 < more.0 && revision.0 < absent.0,
            "the derived grain must beat every foil: derived={} absent={} present={} more={}",
            revision.0,
            absent.0,
            present.0,
            more.0
        );
    }

    // -------------------------------------------------------------------------------------------
    // FALSIFIER, half two: an exact reading founds nothing
    // -------------------------------------------------------------------------------------------

    /// A mechanism that founds on every pass has a clock, not a consequence.
    ///
    /// The exactness here is **not degenerate**: seven one-shot blocks and seven conduct blocks, so
    /// the reading is discriminating and simply has nothing left to learn. The paired control runs
    /// the identical material through the identical body under the parent grain and founds ten.
    #[test]
    fn an_exact_reading_rests_and_founds_no_codec_version() {
        let grain = origin_grain()
            .with_all([word("b"), word("s"), word("rs"), word("k")])
            .expect("four words");
        let mut body = DecomposingBody::mount(grain).expect("a declared grain");
        let pass = body.receive(batch(BATCH_D)).expect("readable");

        let reading = &body.passes()[0];
        assert!(reading.compression.is_exact());
        assert!(reading.collapsed().is_empty());
        assert_eq!(reading.compression.one_shot.len(), 7);
        assert_eq!(reading.compression.conduct.len(), 7);
        assert_eq!(reading.compression.rounds, 0);
        assert!(
            reading.compression.one_shot.len() > 1,
            "an exactness that merged everything would prove nothing"
        );
        assert_eq!(reading.parts().len(), 12);

        assert_eq!(pass.reflection, None, "an exact reading opens no reflection");
        assert_eq!(pass.state, ContinuationState::Rested);
        assert_eq!(body.open_reflection(), None);
        assert_eq!(
            body.codec_population(),
            1,
            "no codec version may be founded on an exact pass"
        );
        assert_eq!(body.revise(), Err(DecompositionError::NoOpenReflection));
        assert_eq!(body.current_codec().unwrap(), body.origin());

        // A rested body does not silently keep reading.
        assert!(matches!(
            body.receive(batch(BATCH_D)),
            Err(DecompositionError::Runtime(
                ReflectiveRuntimeError::ContinuationNotRunning(_)
            ))
        ));

        // The control: the same material, the same body, the parent grain. It founds.
        let mut control = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        control.receive(batch(BATCH_D)).expect("readable");
        assert_eq!(control.passes()[0].collapsed().len(), 10);
        let revision = control.revise().expect("a collapsed population revises");
        assert_eq!(revision.founded.len(), 10);
        assert_eq!(control.codec_population(), 12);
    }

    /// The lineage is a consequence chain and not a clock: the second revision parents on the
    /// first, and the words it returns are the ones the first grain could not resolve.
    #[test]
    fn a_second_revision_parents_on_the_first_and_returns_only_what_the_first_could_not_resolve() {
        let mut body = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        body.receive(batch(BATCH_A)).expect("readable");
        let first = body.revise().expect("a collapsed population revises");
        body.receive(batch(BATCH_C)).expect("readable");
        let second = body.revise().expect("a collapsed population revises");

        assert_eq!(second.parent, first.resumed);
        assert_eq!(second.founded.len(), 1);
        assert_eq!(second.words, BTreeSet::from([word("k")]));
        assert_eq!(
            second.grain.cuts(),
            &BTreeSet::from([word("."), word("b"), word("k"), word("rs"), word("s")])
        );
        assert!(
            first.grain.cuts().is_subset(second.grain.cuts()),
            "a grain never loses a word along its lineage"
        );

        let resumed = body.runtime().codec(second.resumed).expect("it stands");
        assert_eq!(resumed.parents.len(), 2);
        assert!(resumed.parents.contains(&first.resumed));
        assert!(resumed.parents.contains(&second.founded[0].codec));

        // **The per-pair version's OWN parent, which is where the chain can break.** The join's
        // parents above are supplied by the runtime, which inserts the reflected codec itself, so
        // they stand even when every per-pair version parents on the origin instead of on the codec
        // that was reflected. At depth one those two are the same codec and nothing can tell them
        // apart; at depth two they are different and this is the assertion that separates them.
        let per_pair = body
            .runtime()
            .codec(second.founded[0].codec)
            .expect("it stands");
        assert_eq!(per_pair.parents.len(), 1);
        assert!(
            per_pair.parents.contains(&first.resumed),
            "a per-pair version parents on the codec that was reflected, not on the origin"
        );
        assert!(!per_pair.parents.contains(&body.origin()));
        assert_ne!(first.resumed, body.origin());

        // Two deep: the second revision's parent is the first revision's join, whose own parents
        // include the origin.
        let grandparent = body.runtime().codec(first.resumed).expect("it stands");
        assert!(grandparent.parents.contains(&body.origin()));
        assert_eq!(body.codec_population(), 1 + 8 + 1 + 1 + 1);

        // And the third pass on the third batch is exact under the twice-revised grain.
        let third = body.receive(batch(BATCH_D)).expect("readable");
        assert_eq!(third.state, ContinuationState::Rested);
        assert!(body.passes()[2].compression.is_exact());
    }

    // -------------------------------------------------------------------------------------------
    // Refusals and determinism
    // -------------------------------------------------------------------------------------------

    /// The empty cut word is refused, and the refusal is load-bearing rather than tidy: it is a
    /// suffix of every prefix, so a grain carrying it cuts after every symbol and the whole crossing
    /// returns zero for a reason that has nothing to do with the material.
    #[test]
    fn the_empty_cut_word_and_the_empty_grain_are_refused_and_the_refusal_is_load_bearing() {
        assert_eq!(
            DecompositionGrain::declare([word("."), Vec::new()]),
            Err(DecompositionError::EmptyCutWord)
        );
        assert_eq!(
            DecompositionGrain::declare([]),
            Err(DecompositionError::EmptyGrain)
        );
        assert_eq!(
            origin_grain().with(Vec::new()),
            Err(DecompositionError::EmptyCutWord)
        );
        assert_eq!(
            read(&origin_grain(), &[Vec::new()]),
            Err(DecompositionError::EmptyWhole(0))
        );

        // What the refusal is protecting: cut everywhere and the reading is exact for free.
        let everywhere = DecompositionGrain::declare(
            (b'a'..=b'z').chain([b'.']).map(|symbol| vec![Symbol(symbol)]),
        )
        .expect("single-symbol words are non-empty");
        let degenerate = read(&everywhere, &batch(BATCH_C)).expect("readable");
        assert!(degenerate.compression.is_exact());
        assert!(
            degenerate.parts().iter().all(|part| part.len() == 1),
            "every part is one octet, which is the reading having nothing to decompose"
        );
    }

    /// **The grain is the whole of the reusable morphology**, checked by reaching one grain along
    /// two different histories.
    ///
    /// This test read `assert_eq!(run(), run())` until 2026-08-08 and could not fail. Nothing on
    /// the path is nondeterministic: this module holds only `BTreeMap`/`BTreeSet`,
    /// `receiver_exact_compression` and `holonic-language` contain no hash container at all, and
    /// `LocalSet` is `Vec`-backed. Determinism there was a property of the containers, not a
    /// measurement of this organ, and `CLAUDE.md` §8 calls a receipt that could not have come out
    /// otherwise no evidence.
    ///
    /// The claim `CLAUDE.md` §13 obligation 1 actually makes is falsifiable and is what stands
    /// here: what the decomposer does to material it has never seen is **completely determined by
    /// the grain**. A body that derived a grain across two batches and two revisions, and a body
    /// freshly mounted on that same grain carrying no standing and no lineage, must read a third
    /// batch identically — same parts, same prefix identities, same partitions, same population. If
    /// any standing leaked into the reading, or if a pass were read under any grain other than the
    /// one the current codec carries, the two histories separate here.
    #[test]
    fn one_grain_reached_by_two_histories_reads_unseen_material_identically() {
        let mut along_a_lineage = DecomposingBody::mount(origin_grain()).expect("a declared grain");
        along_a_lineage.receive(batch(BATCH_A)).expect("readable");
        along_a_lineage.revise().expect("revises");
        along_a_lineage.receive(batch(BATCH_C)).expect("readable");
        let second = along_a_lineage.revise().expect("revises");
        along_a_lineage.receive(batch(BATCH_D)).expect("readable");
        assert_eq!(along_a_lineage.passes().len(), 3);
        assert_eq!(along_a_lineage.codec_population(), 12);

        // The same grain, declared rather than derived. Nothing stands behind it.
        let declared = origin_grain()
            .with_all([word("b"), word("s"), word("rs"), word("k")])
            .expect("four words");
        assert_eq!(declared, second.grain);

        let mut from_a_declaration = DecomposingBody::mount(declared.clone()).expect("declared");
        let rested = from_a_declaration.receive(batch(BATCH_D)).expect("readable");
        assert_eq!(from_a_declaration.codec_population(), 1);
        assert_eq!(rested.state, ContinuationState::Rested);

        assert_eq!(
            &along_a_lineage.passes()[2],
            &from_a_declaration.passes()[0],
            "a grain reached along a lineage and the same grain declared outright must read \
             unseen material identically, or something other than the grain is carrying conduct"
        );
        // And the pure organ, driven by neither body, returns the same pass a third time.
        assert_eq!(
            &along_a_lineage.passes()[2],
            &read(&declared, &batch(BATCH_D)).expect("readable")
        );
        // The negative control, so the equality above is discriminating rather than trivially
        // true of any two readings of this batch: the parent grain returns a different pass.
        assert_ne!(
            &along_a_lineage.passes()[2],
            &read(&origin_grain(), &batch(BATCH_D)).expect("readable")
        );
    }

    /// **RE-INTEGRATE returns a population, not a flag** — measured where the population is
    /// non-empty.
    ///
    /// Until 2026-08-08 the only assertions on this surface were `reintegration_failures()
    /// .is_empty()` and `reintegration() == batch(BATCH_A)` on a pass [`read`] had just built. Both
    /// were forced: [`decompose`] closes at the end of every whole, so `parts.concat() == whole` is
    /// an identity of its loop, and `read` additionally refused the batch before returning a pass
    /// that failed it. Replacing [`DecomposedWhole::reintegrate`] with `self.source.clone()` — the
    /// identity, which is the whole surface deleted — left every assertion green.
    ///
    /// [`DecomposedWhole`]'s fields are public, so a whole whose parts do not rebuild it is
    /// material a caller can hold, and it is the only material on which this accessor says
    /// anything. The clean pass is kept beside it as the negative control.
    #[test]
    fn reintegration_exhibits_the_rebuilt_wholes_and_a_non_empty_failure_population() {
        // The organ alone: the parts, concatenated — not the source it was cut from.
        let mismatched = DecomposedWhole {
            source: word("abx.aby."),
            parts: vec![word("ab"), word("y.")],
        };
        assert_eq!(render_word(&mismatched.reintegrate()), "aby.");
        assert_ne!(mismatched.reintegrate(), mismatched.source);

        // The negative control: a pass this module cut rebuilds every whole.
        let mut pass = read(&origin_grain(), &batch(BATCH_A)).expect("readable");
        assert_eq!(pass.reintegration(), batch(BATCH_A));
        assert!(pass.reintegration_failures().is_empty());

        // The positive: one whole's parts are made to lose a symbol, and the failure population
        // must exhibit it — which whole, what it was, and what came back — rather than flag it.
        pass.decomposed[1].parts[0].pop();
        assert_eq!(
            pass.reintegration()
                .iter()
                .map(|whole| render_word(whole))
                .collect::<Vec<_>>(),
            vec![
                "abx.aby.cbx.cbz.".to_owned(),
                "dbydbz.ebx.eby.ebz.".to_owned(),
                "prsx.qrsy.".to_owned(),
            ]
        );
        assert_eq!(
            pass.reintegration_failures()
                .iter()
                .map(|(at, source, rebuilt)| (*at, render_word(source), render_word(rebuilt)))
                .collect::<Vec<_>>(),
            vec![(
                1,
                "dby.dbz.ebx.eby.ebz.".to_owned(),
                "dbydbz.ebx.eby.ebz.".to_owned()
            )]
        );
    }

    /// The decoding boundary refuses an input that names no octet.
    ///
    /// [`PartSystem::word_symbols`] takes the engine's `InputId`, a `u64` this module neither mints
    /// nor constrains. Every input **this** system produces comes from [`Symbol::input`] and is
    /// already an octet, so the refusal cannot fire on a word this module returned; it fires across
    /// the public boundary, on a word carried in from a foreign system, and that is the only place
    /// it is a refusal rather than decoration.
    #[test]
    fn the_decoding_boundary_refuses_an_input_that_names_no_octet() {
        let pass = read(&origin_grain(), &batch(BATCH_A)).expect("readable");
        assert_eq!(
            pass.system.word_symbols(&[InputId(u64::from(b'b'))]),
            Ok(vec![Symbol(b'b')])
        );
        assert_eq!(
            pass.system
                .word_symbols(&[InputId(u64::from(b'b')), InputId(256)]),
            Err(DecompositionError::InputIsNotASymbol(InputId(256)))
        );
        assert_eq!(
            pass.system.word_symbols(&[InputId(u64::MAX)]),
            Err(DecompositionError::InputIsNotASymbol(InputId(u64::MAX)))
        );
    }

    /// **Shortest is a claim about the search order, and `BATCH_A` cannot refute it.**
    ///
    /// `receiver_exact_compression::exhibit_collapsed` walks a frontier breadth-first, and that is
    /// what makes the returned word the *shortest* separating word rather than merely *a*
    /// separating one. Turning that queue into a stack — a depth-first exhibition — returns the same
    /// words on `BATCH_A`, `BATCH_C` and `BATCH_D`, so every fixture above is blind to the order it
    /// depends on. The material must be declared where the two can differ, or the minimality check
    /// is a check whose material cannot vary the property under test.
    ///
    /// Here `u` and `v` are held together one-shot — both continue on exactly `a` and `z`, neither
    /// closes — and the two ways out have different depths:
    ///
    /// ```text
    ///   u -a-> ua   (continues on b)          v -a-> va   (a whole part; continues on nothing)
    ///   u -z-> uz -z-> uzz -z-> uzzz  (b)      v -z-> vz -z-> vzz -z-> vzzz  (c)
    /// ```
    ///
    /// `a` separates them at length one; the `z` chain separates them only at length three. The
    /// inputs are pushed in ascending order, so a stack pops `z` first and returns `zzz`, and only a
    /// queue returns `a`. The longer word is exhibited below as a walk that really does separate
    /// them, so "shortest" is a refutable claim on this material rather than the only answer
    /// available.
    #[test]
    fn the_exhibited_word_is_the_shortest_where_a_longer_separating_word_also_exists() {
        let grain = DecompositionGrain::declare([word("b")]).expect("one non-empty cut word");
        let pass = read(&grain, &batch(BRANCH_DEPTHS)).expect("readable");
        assert_eq!(
            pass.parts()
                .iter()
                .map(|part| render_word(part))
                .collect::<Vec<_>>(),
            vec![
                "uab".to_owned(),
                "uzzzb".to_owned(),
                "va".to_owned(),
                "vzzzc".to_owned()
            ]
        );

        let exhibited: Vec<(String, String, String, String)> = pass
            .collapsed()
            .iter()
            .map(|pair| {
                (
                    render_word(pass.system.prefix_of(pair.left).expect("an item")),
                    render_word(pass.system.prefix_of(pair.right).expect("an item")),
                    render_word(
                        &pass
                            .system
                            .word_symbols(&pair.distinguishing_word)
                            .expect("a word over the alphabet"),
                    ),
                    witness_of(pair),
                )
            })
            .collect();
        assert_eq!(
            exhibited,
            vec![
                ("u".to_owned(), "v".to_owned(), "a".to_owned(), "b 1|0".to_owned()),
                ("uz".to_owned(), "uzz".to_owned(), "z".to_owned(), "b 0|1".to_owned()),
                ("uz".to_owned(), "vz".to_owned(), "zz".to_owned(), "b 1|0".to_owned()),
                ("uz".to_owned(), "vzz".to_owned(), "z".to_owned(), "c 0|1".to_owned()),
                ("uzz".to_owned(), "vz".to_owned(), "z".to_owned(), "b 1|0".to_owned()),
                ("uzz".to_owned(), "vzz".to_owned(), "z".to_owned(), "b 1|0".to_owned()),
                ("vz".to_owned(), "vzz".to_owned(), "z".to_owned(), "c 0|1".to_owned()),
            ]
        );

        // Every returned word is minimal, by exhaustion, on THIS material — which is the assertion
        // a depth-first exhibition breaks and `BATCH_A` cannot.
        for pair in pass.collapsed() {
            let walk = pass
                .system
                .word_symbols(&pair.distinguishing_word)
                .expect("a word over the alphabet");
            assert!(separates(&pass.system, pair.left, pair.right, &walk));
            let brute = brute_force_shortest(&pass.system, pair.left, pair.right, walk.len() + 1)
                .expect("some word separates a collapsed pair");
            assert_eq!(brute.len(), walk.len());
        }

        // The declared control: what the other search order returns. `u | v` is the pair whose two
        // exits have different depths, and a stack reaches the deep one first.
        let left = item_at(&pass.system, "u");
        let right = item_at(&pass.system, "v");
        assert_eq!((pass.collapsed()[0].left, pass.collapsed()[0].right), (left, right));
        let depth_first = depth_first_separating_word(&pass.system, left, right)
            .expect("a stack separates them too, further down");
        assert_eq!(render_word(&depth_first), "zzz");
        assert!(separates(&pass.system, left, right, &depth_first));

        // And the depth-first answer is NOT minimal, which is what closes the argument: an
        // exhibition that popped its frontier from the back would return `zzz` for this pair, and
        // the minimality loop above demands `a`. On `BATCH_A`, `BATCH_C` and `BATCH_D` the two
        // orders return the same words and no assertion anywhere could tell them apart.
        let minimal = brute_force_shortest(&pass.system, left, right, depth_first.len())
            .expect("some word separates a collapsed pair");
        assert_eq!(render_word(&minimal), "a");
        assert!(
            depth_first.len() > minimal.len(),
            "if both orders returned a word of the same length this material would prove nothing \
             about the search order and the minimality check above would be blind again"
        );
    }
}
