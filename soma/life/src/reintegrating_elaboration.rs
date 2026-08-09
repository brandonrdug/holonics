//! Re-integration over elaboration: the leader founds the channel, the return stroke rides it.
//!
//! ## The two organs, and why they had never met
//!
//! [`holonic_engine::name_elaboration`] produces the constructive meaning of a name — the transitive
//! closure of what it recruits, with the depth every constituent entered at. It **decomposes and
//! never recomposes**, so it never learns what its own decomposition collapsed.
//!
//! [`crate::decomposing_codec`] performs the other half. It cuts a whole into parts under a declared
//! grain, reads the parts as a prefix machine, compresses that reading, and **re-cuts at the
//! collapsed pair's own separating word**, so that revising the grain changes later conduct on later
//! material.
//!
//! `research/records/2026-08-08_FACES_GROW_FROM_COLLOCATION_AND_THE_ATOM_IS_NOT_EMPTY.md` §4(v)
//! names the join as owed. This module is it.
//!
//! ```text
//!   a name             ->  its constituents, in walk order            (ELABORATE = DECOMPOSE)
//!   the constituents   ->  one channel word, concatenated back        (RE-INTEGRATE)
//!   the channel        ->  parts, under a declared MeaningGrain
//!   the parts          ->  decomposing_codec::PartSystem
//!   that machine       ->  receiver_exact_compression::compress
//!   collapsed pairs    ->  one boundary each, cut at the pair's own separating word
//!   a part's first name ->  a FOUNDED ROOT of the next elaboration
//!   the next pass      ->  later current on the changed route
//! ```
//!
//! ## The channel is the leader's own steps, in the order it took them
//!
//! `reference/holobrochos-a07ff376/src/soma/FORMULA.md:852`: *"each step of the leader extends the
//! channel, the channel's tip is where the next step is taken from, and the return stroke rapidly
//! re-reads the grown channel as a finite propagating current/potential wave (the deep return),
//! never as an instantaneous whole-channel act."*
//!
//! [`Elaboration::arrivals`] is exactly that sequence: one recruitment passage per step, in walk
//! order. The channel word of a name is its root followed by the landing of every arrival, and the
//! re-integration reads that word left to right through a radius-one machine. A constituent reached
//! twice appears twice, because the leader stepped there twice, and those repetitions are the
//! collocation the boundary is later founded on.
//!
//! ## And it is not a temporal inverse and not a replay
//!
//! `FORMULA.md:8732`, deposited as causal parity: *"a lightning leader changes the medium, and the
//! return stroke is **genuinely later current RIDING that changed route**."*
//!
//! The second pass is not the first pass run backwards and not the first pass run again. It runs
//! under a grain the first pass's own collapse founded, and that grain does two things the first
//! pass had no way to do:
//!
//! - It **splits channels into parts**, and parts are **pooled across names**. A tail shared by two
//!   names becomes ONE item in the next machine. In the first pass every item was rooted at some
//!   name, so a shared sub-meaning had no item at all — [`Movement::new_items`] is the population of
//!   places the first pass could not name.
//! - It **founds roots**. The first name of a part that begins at a boundary is elaborated in its
//!   own right, from depth zero. Under a bounded aperture that reaches constituents the first pass
//!   returned only in [`Elaboration::unopened`] — named as what it does not carry.
//!   [`Movement::reached_past_the_first_aperture`] is that population, and it is the sharpest form
//!   of the causal-parity requirement: material the first pass proved it did not hold.
//!
//! ## What is not here
//!
//! No float, no weight, no threshold, no score. The only orderings are `Ord` on names, words and
//! identities, which is canonicalization. Every return is a population with its obstructions
//! retained: a boundary demanded at a name the deposit cannot open is
//! [`UnopenableBoundary`], kept and exhibited rather than dropped, and a revision whose words the
//! grain already carries rests as [`RestReason::GrainDidNotGrow`] rather than turning forever.
//!
//! ## The one codec at the seam, and its declared refusal
//!
//! [`crate::decomposing_codec`] is written over octets. Names are not octets, so the join needs a
//! bijection, and [`NameAlphabet`] is it: the deposit's names, canonically ordered, one octet each.
//! It **refuses** above 256 names rather than truncating
//! ([`ReintegrationRefusal::AlphabetExceedsTheOctetCarrier`]), because a silent truncation would
//! identify two names and every collapse downstream would then be an artifact of the seam rather
//! than of the material.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::name_elaboration::{
    Elaboration, ElaborationAperture, ElaborationDeposit, ElaborationRefusal,
};
use holonic_engine::receiver_exact_compression::{
    compress, CollapsedPair, ItemId, ReceiverExactCompression,
};

use crate::decomposing_codec::{
    decompose, DecompositionError, DecompositionGrain, PartSystem, Symbol, CLOSES_RECEIVER,
};

const PASS_SCHEMA: &str = "life.reintegrating-elaboration.pass.v1";

/// How a passage of names is written when it is exhibited.
pub const PASSAGE_SEPARATOR: &str = "\u{b7}";

/// Write a passage of names.
pub fn render_passage(names: &[String]) -> String {
    names.join(PASSAGE_SEPARATOR)
}

/// Why a re-integration was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReintegrationRefusal {
    /// More names than the octet carrier the decomposing codec is written over can hold. Refused
    /// rather than truncated: a truncation would identify two names at the seam.
    AlphabetExceedsTheOctetCarrier { names: usize },
    /// A name reached by the elaboration that the declared alphabet does not carry.
    NameIsNotInTheAlphabet { name: String },
    /// No root was declared. An elaboration of nothing is not a meaning that is empty.
    NoRootsDeclared,
    /// A collapsed pair returned an empty separating word. Impossible by construction in
    /// `receiver_exact_compression` — the empty word is the one-shot reading, which held the pair
    /// together — and refused here rather than silently founding the degenerate grain that cuts
    /// after every name.
    EmptyBoundaryWord { pair: Box<CollapsedPair> },
    /// The grain refused the boundary.
    Grain(DecompositionError),
}

impl std::fmt::Display for ReintegrationRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlphabetExceedsTheOctetCarrier { names } => write!(
                formatter,
                "{names} names do not fit the octet carrier the decomposing codec is written over"
            ),
            Self::NameIsNotInTheAlphabet { name } => {
                write!(formatter, "the alphabet does not carry {name:?}")
            }
            Self::NoRootsDeclared => write!(formatter, "no root was declared"),
            Self::EmptyBoundaryWord { .. } => {
                write!(formatter, "a collapsed pair returned an empty separating word")
            }
            Self::Grain(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for ReintegrationRefusal {}

impl From<DecompositionError> for ReintegrationRefusal {
    fn from(error: DecompositionError) -> Self {
        Self::Grain(error)
    }
}

// ---------------------------------------------------------------------------- the seam

/// The bijection between the deposit's names and the decomposing codec's octet alphabet.
///
/// Canonically ordered, so the octet a name occupies is a function of the name population and not
/// of a read order. Two runs over the same deposit therefore assign the same octets, which is what
/// makes a pass comparable to a pass bit for bit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NameAlphabet {
    names: Vec<String>,
    index: BTreeMap<String, Symbol>,
}

impl NameAlphabet {
    pub fn declare(
        names: impl IntoIterator<Item = String>,
    ) -> Result<Self, ReintegrationRefusal> {
        let ordered: BTreeSet<String> = names.into_iter().collect();
        if ordered.len() > usize::from(u8::MAX) + 1 {
            return Err(ReintegrationRefusal::AlphabetExceedsTheOctetCarrier {
                names: ordered.len(),
            });
        }
        let names: Vec<String> = ordered.into_iter().collect();
        let index = names
            .iter()
            .enumerate()
            .map(|(at, name)| (name.clone(), Symbol(at as u8)))
            .collect();
        Ok(Self { names, index })
    }

    /// Every name a deposit can put on a channel: its route keys, its declared names, and every
    /// symbol any of its artifacts recruited.
    pub fn over_deposit(deposit: &ElaborationDeposit) -> Result<Self, ReintegrationRefusal> {
        let mut names: BTreeSet<String> = deposit.route_keys().iter().cloned().collect();
        for derivation in deposit.routes() {
            names.insert(derivation.name.clone());
            names.extend(derivation.recruited.keys().cloned());
        }
        Self::declare(names)
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    pub fn names(&self) -> &[String] {
        &self.names
    }

    pub fn symbol(&self, name: &str) -> Result<Symbol, ReintegrationRefusal> {
        self.index
            .get(name)
            .copied()
            .ok_or_else(|| ReintegrationRefusal::NameIsNotInTheAlphabet {
                name: name.to_owned(),
            })
    }

    pub fn name(&self, symbol: Symbol) -> Option<&str> {
        self.names.get(usize::from(symbol.0)).map(String::as_str)
    }

    /// A word of octets, read back as the passage of names it stands for.
    pub fn passage(&self, word: &[Symbol]) -> Vec<String> {
        word.iter()
            .map(|symbol| {
                self.name(*symbol)
                    .map_or_else(|| format!("?{}", symbol.0), str::to_owned)
            })
            .collect()
    }

    /// The receiver identity, read back. The decomposing codec declares one receiver per symbol —
    /// *does this name continue here* — plus [`CLOSES_RECEIVER`], *does a part close here*.
    pub fn receiver(&self, receiver: u64) -> String {
        if receiver == CLOSES_RECEIVER {
            return "closes".to_owned();
        }
        u8::try_from(receiver)
            .ok()
            .and_then(|octet| self.name(Symbol(octet)))
            .map_or_else(|| format!("?{receiver}"), |name| format!("continues:{name}"))
    }
}

// ---------------------------------------------------------------------------- the grain

/// Where a re-integrated meaning closes a part.
///
/// The origin carries no boundary at all, which is exactly the state `name_elaboration` is in: a
/// meaning is one undifferentiated whole. [`DecompositionGrain`] refuses an empty cut population
/// because for text the boundary-free reading is degenerate; here it is the *before*, so it is
/// carried as its own case rather than faked with a word that never occurs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum MeaningGrain {
    /// No boundary. One part per channel.
    #[default]
    Unbounded,
    /// A declared boundary population, delegated to the decomposing codec's own grain.
    Bounded(DecompositionGrain),
}

impl MeaningGrain {
    pub fn origin() -> Self {
        Self::Unbounded
    }

    /// The boundary words, in canonical order. Empty at the origin.
    pub fn cuts(&self) -> BTreeSet<Vec<Symbol>> {
        match self {
            Self::Unbounded => BTreeSet::new(),
            Self::Bounded(grain) => grain.cuts().clone(),
        }
    }

    pub fn carries(&self, word: &[Symbol]) -> bool {
        match self {
            Self::Unbounded => false,
            Self::Bounded(grain) => grain.cuts().contains(word),
        }
    }

    /// The same grain with one more boundary. Monotone: a grain never loses a word.
    pub fn with(&self, word: Vec<Symbol>) -> Result<Self, ReintegrationRefusal> {
        if word.is_empty() {
            return Err(ReintegrationRefusal::Grain(DecompositionError::EmptyCutWord));
        }
        Ok(match self {
            Self::Unbounded => Self::Bounded(DecompositionGrain::declare([word])?),
            Self::Bounded(grain) => Self::Bounded(grain.with(word)?),
        })
    }

    /// Cut a channel into parts. At the origin the channel is one part, which is what makes the
    /// first pass the one that has not recomposed anything.
    pub fn cut(&self, channel: &[Symbol]) -> Vec<Vec<Symbol>> {
        match self {
            Self::Unbounded => {
                if channel.is_empty() {
                    Vec::new()
                } else {
                    vec![channel.to_vec()]
                }
            }
            Self::Bounded(grain) => decompose(grain, channel),
        }
    }

    /// Every boundary word that closes after `read`. A population rather than a pick: two words may
    /// both be suffixes of the same prefix and both are causes.
    pub fn closing_after(&self, read: &[Symbol]) -> Vec<Vec<Symbol>> {
        self.cuts()
            .into_iter()
            .filter(|cut| read.len() >= cut.len() && read[read.len() - cut.len()..] == cut[..])
            .collect()
    }
}

// ---------------------------------------------------------------------------- the channel

/// One boundary inside a channel: where it fell, and the words that closed there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Boundary {
    /// The position in the channel after which the part closed.
    pub at: usize,
    /// Every grain word that is a suffix of `channel[..at]`.
    pub words: Vec<Vec<Symbol>>,
}

/// One name's meaning, elaborated into a channel and re-integrated under a grain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReintegratedMeaning {
    pub root: String,
    /// The leader's steps: the root, then the landing of every arrival, in walk order.
    pub channel: Vec<Symbol>,
    /// The channel, cut. Under the origin grain this is one part.
    pub parts: Vec<Vec<Symbol>>,
    /// Where the grain closed, with the words that closed there.
    pub boundaries: Vec<Boundary>,
    /// The constituents the elaboration reached, by name.
    pub constituents: BTreeSet<String>,
    /// What the aperture stopped the walk at.
    pub beyond_depth: BTreeSet<String>,
    /// What opening those would have brought and this reading does not carry.
    pub unopened: BTreeSet<String>,
    /// Constituent to the first depth it entered at.
    pub signature: BTreeMap<String, usize>,
}

impl ReintegratedMeaning {
    /// RE-INTEGRATE: the channel, rebuilt from its parts and nothing else.
    pub fn reintegrate(&self) -> Vec<Symbol> {
        self.parts.concat()
    }

    /// Whether the parts put the channel back together. Returned rather than asserted, in the same
    /// shape `decomposing_codec::DecompositionPass::reintegration_failures` uses.
    pub fn rebuilds(&self) -> bool {
        self.reintegrate() == self.channel
    }

    /// The parts, as passages of names.
    pub fn passages(&self, alphabet: &NameAlphabet) -> Vec<Vec<String>> {
        self.parts
            .iter()
            .map(|part| alphabet.passage(part))
            .collect()
    }

    /// Grow the channel of one elaborated meaning.
    pub fn grow(
        alphabet: &NameAlphabet,
        meaning: &Elaboration,
        grain: &MeaningGrain,
    ) -> Result<Self, ReintegrationRefusal> {
        let mut channel = vec![alphabet.symbol(meaning.root())?];
        for arrival in meaning.arrivals() {
            channel.push(alphabet.symbol(&arrival.to)?);
        }
        let parts = grain.cut(&channel);
        let mut boundaries = Vec::new();
        let mut at = 0usize;
        for part in &parts {
            at += part.len();
            if at == channel.len() {
                // `decompose` closes at the end of every whole whatever the grain says, so the last
                // close is a property of the loop and not a boundary the grain founded.
                break;
            }
            boundaries.push(Boundary {
                at,
                words: grain.closing_after(&channel[..at]),
            });
        }
        Ok(Self {
            root: meaning.root().to_owned(),
            channel,
            parts,
            boundaries,
            constituents: meaning
                .constituents()
                .keys()
                .cloned()
                .collect::<BTreeSet<String>>(),
            beyond_depth: meaning.beyond_depth().clone(),
            unopened: meaning.unopened().clone(),
            signature: meaning
                .signature()
                .into_iter()
                .map(|(name, depth)| (name.to_owned(), depth))
                .collect(),
        })
    }
}

// ---------------------------------------------------------------------------- the pass

/// One collapsed pair, exhibited in names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CollapsedPlace {
    /// The two places in the re-integration the reading merged, as passages of names.
    pub left: Vec<String>,
    pub right: Vec<String>,
    /// The name each place is rooted at, when the place is a rooted prefix. `None` for a shared
    /// tail — a place that belongs to no single name, which is what a boundary founds.
    pub left_root: Option<String>,
    pub right_root: Option<String>,
    /// The shortest passage of names after which some receiver sees the difference.
    pub separating_word: Vec<String>,
    /// The receiver that saw it, and what the two returned.
    pub witness: Option<(String, u64, u64)>,
    /// The separation is that one place continues and the other does not.
    pub separated_by_terminus: bool,
    pub pair: CollapsedPair,
}

impl CollapsedPlace {
    pub fn exhibit(&self) -> String {
        let witness = match &self.witness {
            Some((receiver, left, right)) => {
                format!("receiver {receiver} returned {left} against {right}")
            }
            None => "a terminus, with no receiver naming it".to_owned(),
        };
        format!(
            "'{}' | '{}'  separated by '{}'  ({witness})",
            render_passage(&self.left),
            render_passage(&self.right),
            render_passage(&self.separating_word),
        )
    }
}

/// One reading of one root population under one aperture and one grain. The artifact, carried whole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReintegrationPass {
    pub schema: String,
    pub aperture: ElaborationAperture,
    pub grain: MeaningGrain,
    /// The declared roots, in the order they were presented.
    pub roots: Vec<String>,
    pub meanings: Vec<ReintegratedMeaning>,
    /// Roots the deposit refused, retained rather than dropped.
    pub refused_roots: Vec<(String, ElaborationRefusal)>,
    pub system: PartSystem,
    pub compression: ReceiverExactCompression,
}

impl ReintegrationPass {
    /// Elaborate every root, re-integrate each into a channel, cut under the grain, pool the parts,
    /// and read the pooled parts through the decomposing codec's own machine.
    pub fn read(
        deposit: &ElaborationDeposit,
        alphabet: &NameAlphabet,
        roots: &[String],
        aperture: ElaborationAperture,
        grain: &MeaningGrain,
    ) -> Result<Self, ReintegrationRefusal> {
        if roots.is_empty() {
            return Err(ReintegrationRefusal::NoRootsDeclared);
        }
        let mut meanings = Vec::with_capacity(roots.len());
        let mut refused_roots = Vec::new();
        let mut pooled: Vec<Vec<Symbol>> = Vec::new();
        for root in roots {
            match deposit.elaborate(root, aperture) {
                Ok(meaning) => {
                    let carried = ReintegratedMeaning::grow(alphabet, &meaning, grain)?;
                    pooled.extend(carried.parts.iter().cloned());
                    meanings.push(carried);
                }
                Err(refusal) => refused_roots.push((root.clone(), refusal)),
            }
        }
        let system = PartSystem::over_parts(&pooled);
        let compression = compress(&system);
        Ok(Self {
            schema: PASS_SCHEMA.to_owned(),
            aperture,
            grain: grain.clone(),
            roots: roots.to_vec(),
            meanings,
            refused_roots,
            system,
            compression,
        })
    }

    pub fn collapsed(&self) -> &[CollapsedPair] {
        &self.compression.collapsed
    }

    /// The one-shot re-integration lost nothing later conduct through the channel can see.
    pub fn is_exact(&self) -> bool {
        self.compression.is_exact()
    }

    /// Every channel whose parts do not rebuild it. A population, exhibited, never a flag.
    pub fn reintegration_failures(&self) -> Vec<&ReintegratedMeaning> {
        self.meanings
            .iter()
            .filter(|meaning| !meaning.rebuilds())
            .collect()
    }

    /// The meaning of one root under this pass.
    pub fn meaning(&self, root: &str) -> Option<&ReintegratedMeaning> {
        self.meanings.iter().find(|meaning| meaning.root == root)
    }

    /// Every name any root's elaboration reached in this pass.
    pub fn constituents(&self) -> BTreeSet<String> {
        self.meanings
            .iter()
            .flat_map(|meaning| meaning.constituents.iter().cloned())
            .collect()
    }

    /// Every name this pass named as reached-but-not-carried, with the roots that named it.
    pub fn unopened(&self) -> BTreeMap<String, BTreeSet<String>> {
        let mut carried: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for meaning in &self.meanings {
            for name in &meaning.unopened {
                carried
                    .entry(name.clone())
                    .or_default()
                    .insert(meaning.root.clone());
            }
        }
        carried
    }

    /// Every place in the machine, as a passage of names.
    pub fn places(&self, alphabet: &NameAlphabet) -> BTreeSet<Vec<String>> {
        self.system
            .prefixes()
            .iter()
            .map(|prefix| alphabet.passage(prefix))
            .collect()
    }

    /// The place an item stands at, and the root it belongs to when it is rooted at one.
    fn place_of(&self, alphabet: &NameAlphabet, item: ItemId) -> (Vec<String>, Option<String>) {
        let Some(prefix) = self.system.prefix_of(item) else {
            return (Vec::new(), None);
        };
        let passage = alphabet.passage(prefix);
        let root = passage
            .first()
            .filter(|first| self.roots.iter().any(|root| root == *first))
            .cloned();
        (passage, root)
    }

    /// The collapse, in names. Every pair, never a count.
    pub fn collapsed_places(
        &self,
        alphabet: &NameAlphabet,
    ) -> Result<Vec<CollapsedPlace>, ReintegrationRefusal> {
        self.compression
            .collapsed
            .iter()
            .map(|pair| {
                let (left, left_root) = self.place_of(alphabet, pair.left);
                let (right, right_root) = self.place_of(alphabet, pair.right);
                let word = self.system.word_symbols(&pair.distinguishing_word)?;
                Ok(CollapsedPlace {
                    left,
                    right,
                    left_root,
                    right_root,
                    separating_word: alphabet.passage(&word),
                    witness: pair.witness.map(|(receiver, first, second)| {
                        (alphabet.receiver(receiver.0), first.0, second.0)
                    }),
                    separated_by_terminus: pair.separated_by_terminus,
                    pair: pair.clone(),
                })
            })
            .collect()
    }

    /// The word each collapsed pair asks the grain to cut at, in the pairs' own order.
    pub fn boundary_words(&self) -> Result<Vec<Vec<Symbol>>, ReintegrationRefusal> {
        self.compression
            .collapsed
            .iter()
            .map(|pair| self.system.word_symbols(&pair.distinguishing_word).map_err(Into::into))
            .collect()
    }
}

// ---------------------------------------------------------------------------- the revision

/// One boundary founded by one collapsed pair. The lineage is the pair, kept whole.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedBoundary {
    pub word: Vec<Symbol>,
    pub names: Vec<String>,
    pub pair: CollapsedPair,
    pub place: CollapsedPlace,
    /// The grain already carried this word. The boundary is retained with its cause anyway; what it
    /// does not do is grow the grain.
    pub already_carried: bool,
}

/// A name the next elaboration will open in its own right, because a boundary opened a part at it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FoundedRoot {
    pub name: String,
    /// The boundary word that opened the part this name begins.
    pub word: Vec<Symbol>,
    /// The roots whose channels carried that boundary.
    pub inside: BTreeSet<String>,
}

/// A boundary demanded at a name the deposit cannot open. Retained as a typed obstruction: this is
/// the atom's permanent outside, returned by name rather than dropped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnopenableBoundary {
    pub name: String,
    pub word: Vec<Symbol>,
    pub inside: BTreeSet<String>,
}

/// What one revision returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MeaningRevision {
    pub parent: MeaningGrain,
    pub grain: MeaningGrain,
    pub founded: Vec<FoundedBoundary>,
    /// Words genuinely new to the grain. Empty means the collapse demands only boundaries the grain
    /// already carries, which is a fixed point rather than a failure.
    pub added: BTreeSet<Vec<Symbol>>,
    pub already_carried: BTreeSet<Vec<Symbol>>,
    pub founded_roots: Vec<FoundedRoot>,
    pub unopenable: Vec<UnopenableBoundary>,
}

impl MeaningRevision {
    /// Found one boundary per collapsed pair, then read what those boundaries open.
    pub fn revise(
        pass: &ReintegrationPass,
        alphabet: &NameAlphabet,
        deposit: &ElaborationDeposit,
    ) -> Result<Self, ReintegrationRefusal> {
        let parent = pass.grain.clone();
        let places = pass.collapsed_places(alphabet)?;
        let words = pass.boundary_words()?;

        let mut grain = parent.clone();
        let mut founded = Vec::with_capacity(places.len());
        let mut added: BTreeSet<Vec<Symbol>> = BTreeSet::new();
        let mut already_carried: BTreeSet<Vec<Symbol>> = BTreeSet::new();
        for ((pair, word), place) in pass
            .compression
            .collapsed
            .iter()
            .zip(words)
            .zip(places.into_iter())
        {
            if word.is_empty() {
                return Err(ReintegrationRefusal::EmptyBoundaryWord {
                    pair: Box::new(pair.clone()),
                });
            }
            let carried = parent.carries(&word);
            if carried {
                already_carried.insert(word.clone());
            } else {
                added.insert(word.clone());
            }
            grain = grain.with(word.clone())?;
            founded.push(FoundedBoundary {
                names: alphabet.passage(&word),
                word,
                pair: pair.clone(),
                place,
                already_carried: carried,
            });
        }

        // What the boundaries open. A part that begins at a boundary begins at a name, and that
        // name is elaborated in its own right by the next pass -- or, when the deposit cannot open
        // it, retained as the obstruction it is.
        let mut opened: BTreeMap<String, (Vec<Symbol>, BTreeSet<String>)> = BTreeMap::new();
        for meaning in &pass.meanings {
            let parts = grain.cut(&meaning.channel);
            let mut at = 0usize;
            for (ordinal, part) in parts.iter().enumerate() {
                if ordinal > 0 {
                    if let Some(first) = part.first() {
                        let name = alphabet
                            .name(*first)
                            .map_or_else(|| format!("?{}", first.0), str::to_owned);
                        let word = grain
                            .closing_after(&meaning.channel[..at])
                            .into_iter()
                            .next()
                            .unwrap_or_default();
                        let slot = opened.entry(name).or_insert((word, BTreeSet::new()));
                        slot.1.insert(meaning.root.clone());
                    }
                }
                at += part.len();
            }
        }

        let mut founded_roots = Vec::new();
        let mut unopenable = Vec::new();
        for (name, (word, inside)) in opened {
            if deposit.is_openable(&name) {
                founded_roots.push(FoundedRoot { name, word, inside });
            } else {
                unopenable.push(UnopenableBoundary { name, word, inside });
            }
        }

        Ok(Self {
            parent,
            grain,
            founded,
            added,
            already_carried,
            founded_roots,
            unopenable,
        })
    }

    /// The boundary that founded a word, for attribution.
    pub fn cause_of(&self, word: &[Symbol]) -> Option<&FoundedBoundary> {
        self.founded.iter().find(|boundary| boundary.word == word)
    }
}

// ---------------------------------------------------------------------------- what moved

/// One name whose meaning moved, with the boundaries that moved it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MeaningMoved {
    pub root: String,
    pub before: Vec<Vec<String>>,
    pub after: Vec<Vec<String>>,
    /// Every boundary that fell inside this name's channel, each carrying the collapsed pair and
    /// the separating word that founded it. This is the attribution, computed from the boundary
    /// that actually matched rather than inferred.
    pub caused_by: Vec<FoundedBoundary>,
}

/// A name the first pass returned as reached-but-not-carried and the second pass carries.
///
/// The two forms are kept apart on purpose. **Per-meaning**: the first pass named this constituent
/// in [`Elaboration::unopened`] from some root — it proved that *that meaning* does not hold it —
/// and a root the boundary founded now carries it. **Strict**: the first pass carried it in no
/// meaning at all. The strict form is the sharper witness and it is a flag rather than a filter,
/// because a per-meaning crossing is a real crossing even when some other root already held the
/// name, and collapsing the two would hide which of the two actually happened.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReachedPastAperture {
    pub name: String,
    /// The first pass's roots that named it in `unopened`.
    pub was_unopened_from: BTreeSet<String>,
    /// The founded root whose own elaboration reaches it.
    pub now_reached_from: String,
    /// No meaning in the first pass carried this name.
    pub absent_from_the_first_pass: bool,
}

/// What the second pass returned that the first did not.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Movement {
    pub changed: Vec<MeaningMoved>,
    pub unchanged: Vec<String>,
    /// Places in the machine the second pass has and the first did not. A shared tail has no rooted
    /// prefix, so the first pass had no item for it at all.
    pub new_places: Vec<Vec<String>>,
    pub new_roots: Vec<String>,
    /// Names carried as constituents by the second pass and not the first.
    pub new_constituents: BTreeSet<String>,
    pub reached_past_the_first_aperture: Vec<ReachedPastAperture>,
    /// Collapsed pairs the second pass returned at places the first pass did not have. A collapse
    /// the first pass could not have returned, rather than a reordering of one it did.
    pub new_collapses: Vec<CollapsedPlace>,
}

impl Movement {
    /// Read what moved between two passes, attributed to the revision that separates them.
    pub fn read(
        before: &ReintegrationPass,
        after: &ReintegrationPass,
        revision: &MeaningRevision,
        alphabet: &NameAlphabet,
    ) -> Result<Self, ReintegrationRefusal> {
        let mut changed = Vec::new();
        let mut unchanged = Vec::new();
        for earlier in &before.meanings {
            let Some(later) = after.meaning(&earlier.root) else {
                continue;
            };
            if later.parts == earlier.parts {
                unchanged.push(earlier.root.clone());
                continue;
            }
            let mut caused_by: Vec<FoundedBoundary> = Vec::new();
            for boundary in &later.boundaries {
                for word in &boundary.words {
                    if let Some(cause) = revision.cause_of(word) {
                        if !caused_by.iter().any(|held| held.word == cause.word) {
                            caused_by.push(cause.clone());
                        }
                    }
                }
            }
            changed.push(MeaningMoved {
                root: earlier.root.clone(),
                before: earlier.passages(alphabet),
                after: later.passages(alphabet),
                caused_by,
            });
        }

        let earlier_places = before.places(alphabet);
        let new_places: Vec<Vec<String>> = after
            .places(alphabet)
            .into_iter()
            .filter(|place| !earlier_places.contains(place))
            .collect();

        let earlier_roots: BTreeSet<&String> = before.roots.iter().collect();
        let new_roots: Vec<String> = after
            .roots
            .iter()
            .filter(|root| !earlier_roots.contains(root))
            .cloned()
            .collect();

        let earlier_constituents = before.constituents();
        let new_constituents: BTreeSet<String> = after
            .constituents()
            .into_iter()
            .filter(|name| !earlier_constituents.contains(name))
            .collect();

        let earlier_unopened = before.unopened();
        let mut reached_past_the_first_aperture = Vec::new();
        for root in &new_roots {
            let Some(meaning) = after.meaning(root) else {
                continue;
            };
            for name in &meaning.constituents {
                let Some(was) = earlier_unopened.get(name) else {
                    continue;
                };
                reached_past_the_first_aperture.push(ReachedPastAperture {
                    name: name.clone(),
                    was_unopened_from: was.clone(),
                    now_reached_from: root.clone(),
                    absent_from_the_first_pass: !earlier_constituents.contains(name),
                });
            }
        }

        let new_collapses: Vec<CollapsedPlace> = after
            .collapsed_places(alphabet)?
            .into_iter()
            .filter(|place| {
                !earlier_places.contains(&place.left) || !earlier_places.contains(&place.right)
            })
            .collect();

        Ok(Self {
            changed,
            unchanged,
            new_places,
            new_roots,
            new_constituents,
            reached_past_the_first_aperture,
            new_collapses,
        })
    }

    /// Whether anything moved at all. A second pass identical to the first has not re-integrated.
    pub fn is_still(&self) -> bool {
        self.changed.is_empty()
            && self.new_places.is_empty()
            && self.new_roots.is_empty()
            && self.new_constituents.is_empty()
            && self.new_collapses.is_empty()
    }
}

// ---------------------------------------------------------------------------- the turning body

/// Why the turning stopped. Every reason is a return; none of them is a failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RestReason {
    /// The re-integration lost nothing later conduct can see. There is no boundary to found, and
    /// nothing downstream is in a position to move.
    ReintegrationIsExact,
    /// The collapse demands only boundaries the grain already carries. A fixed point: the remainder
    /// is irreducible under this revision rule, and the collapsed population is retained.
    GrainDidNotGrow,
    /// The declared bound on turns was reached with the collapse still growing the grain. The state
    /// is returned with the reason, because a re-integration that does not settle is a finding.
    BoundReached,
}

/// One turn: a pass, the revision its collapse founded, and what moved when the next pass rode it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Turn {
    pub pass: ReintegrationPass,
    pub revision: Option<MeaningRevision>,
    pub movement: Option<Movement>,
}

/// The whole turning, with the turn it rested at and why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Reintegration {
    pub turns: Vec<Turn>,
    pub rest: RestReason,
    pub rested_at: usize,
}

impl Reintegration {
    /// Turn until the re-integration rests or the declared bound is reached.
    ///
    /// The grain is monotone and the boundary words are drawn from a finite population, so a turn
    /// that grows the grain can only happen finitely often; a turn that does not grow it rests
    /// immediately as [`RestReason::GrainDidNotGrow`]. The bound is therefore a declared aperture on
    /// the report rather than the thing that makes this terminate.
    pub fn run(
        deposit: &ElaborationDeposit,
        alphabet: &NameAlphabet,
        roots: &[String],
        aperture: ElaborationAperture,
        bound: usize,
    ) -> Result<Self, ReintegrationRefusal> {
        let mut grain = MeaningGrain::origin();
        let mut roots: Vec<String> = roots.to_vec();
        let mut turns: Vec<Turn> = Vec::new();
        let mut pass = ReintegrationPass::read(deposit, alphabet, &roots, aperture, &grain)?;

        loop {
            if pass.is_exact() {
                let rested_at = turns.len();
                turns.push(Turn {
                    pass,
                    revision: None,
                    movement: None,
                });
                return Ok(Self {
                    turns,
                    rest: RestReason::ReintegrationIsExact,
                    rested_at,
                });
            }
            let revision = MeaningRevision::revise(&pass, alphabet, deposit)?;
            if revision.added.is_empty() {
                let rested_at = turns.len();
                turns.push(Turn {
                    pass,
                    revision: Some(revision),
                    movement: None,
                });
                return Ok(Self {
                    turns,
                    rest: RestReason::GrainDidNotGrow,
                    rested_at,
                });
            }
            if turns.len() + 1 >= bound {
                let rested_at = turns.len();
                turns.push(Turn {
                    pass,
                    revision: Some(revision),
                    movement: None,
                });
                return Ok(Self {
                    turns,
                    rest: RestReason::BoundReached,
                    rested_at,
                });
            }

            grain = revision.grain.clone();
            for founded in &revision.founded_roots {
                if !roots.iter().any(|root| root == &founded.name) {
                    roots.push(founded.name.clone());
                }
            }
            let next = ReintegrationPass::read(deposit, alphabet, &roots, aperture, &grain)?;
            let movement = Movement::read(&pass, &next, &revision, alphabet)?;
            turns.push(Turn {
                pass,
                revision: Some(revision),
                movement: Some(movement),
            });
            pass = next;
        }
    }

    pub fn last(&self) -> &Turn {
        self.turns.last().expect("a run always carries one turn")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_engine::derivation_atlas::Derivation;

    fn derivation(name: &str, statement: &str, recruited: &[(&str, u32)]) -> Derivation {
        Derivation {
            name: name.to_owned(),
            statement: statement.to_owned(),
            recruited: recruited
                .iter()
                .map(|(symbol, count)| ((*symbol).to_owned(), *count))
                .collect(),
        }
    }

    /// Two routes whose direct recruitment differs only in material a declared-name reading cannot
    /// see, plus a declared helper that carries a further population. The shape the deposit at
    /// `standing/output` actually has.
    fn deposited_shape() -> Vec<Derivation> {
        vec![
            derivation("left", "S", &[("helper", 1), ("omega", 1), ("shared", 1)]),
            derivation("right", "S", &[("helper", 1), ("ring", 1), ("shared", 1)]),
            derivation("helper", "T", &[("deep", 1), ("further", 1)]),
        ]
    }

    fn alphabet_over(population: &[Derivation]) -> (ElaborationDeposit, NameAlphabet) {
        let deposit = ElaborationDeposit::read(population);
        let alphabet = NameAlphabet::over_deposit(&deposit).expect("a small alphabet");
        (deposit, alphabet)
    }

    // ------------------------------------------------------------------ the seam and its refusal

    #[test]
    fn the_alphabet_is_a_bijection_and_refuses_rather_than_truncating() {
        let (_, alphabet) = alphabet_over(&deposited_shape());
        for name in alphabet.names().to_vec() {
            let symbol = alphabet.symbol(&name).expect("declared");
            assert_eq!(alphabet.name(symbol), Some(name.as_str()));
        }
        assert!(matches!(
            alphabet.symbol("nowhere"),
            Err(ReintegrationRefusal::NameIsNotInTheAlphabet { .. })
        ));

        let too_many: Vec<String> = (0..300).map(|at| format!("name{at}")).collect();
        assert_eq!(
            NameAlphabet::declare(too_many).unwrap_err(),
            ReintegrationRefusal::AlphabetExceedsTheOctetCarrier { names: 300 }
        );
    }

    // ---------------------------------------------------------------------------- the channel

    #[test]
    fn the_channel_is_the_leaders_steps_in_walk_order_and_the_origin_leaves_it_whole() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &["left#0".to_owned()],
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("the route is in the deposit");

        let meaning = pass.meaning("left#0").expect("elaborated");
        assert_eq!(
            alphabet.passage(&meaning.channel),
            vec![
                "left#0".to_owned(),
                "helper".to_owned(),
                "omega".to_owned(),
                "shared".to_owned(),
            ]
        );
        // The origin carries no boundary: one part, no boundary, and the parts rebuild the channel.
        assert_eq!(meaning.parts.len(), 1);
        assert!(meaning.boundaries.is_empty());
        assert!(meaning.rebuilds());
        assert!(pass.reintegration_failures().is_empty());
    }

    #[test]
    fn a_root_the_deposit_refuses_is_retained_rather_than_aborting_the_pass() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let mut alphabet_with_stranger: BTreeSet<String> =
            alphabet.names().iter().cloned().collect();
        alphabet_with_stranger.insert("stranger".to_owned());
        let alphabet = NameAlphabet::declare(alphabet_with_stranger).expect("small");
        let pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &["left#0".to_owned(), "stranger".to_owned()],
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("one root is in the deposit");
        assert_eq!(pass.meanings.len(), 1);
        assert_eq!(
            pass.refused_roots,
            vec![(
                "stranger".to_owned(),
                ElaborationRefusal::RootIsNotInTheDeposit {
                    root: "stranger".to_owned()
                }
            )]
        );
    }

    #[test]
    fn no_root_is_refused_rather_than_read_as_a_meaning_that_is_empty() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        assert_eq!(
            ReintegrationPass::read(
                &deposit,
                &alphabet,
                &[],
                ElaborationAperture::Exhausted,
                &MeaningGrain::origin(),
            )
            .unwrap_err(),
            ReintegrationRefusal::NoRootsDeclared
        );
    }

    // ----------------------------------------------------------------- the collapse is exhibited

    #[test]
    fn the_reintegration_over_collapses_and_every_pair_carries_its_own_separating_passage() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("both routes are in the deposit");

        assert!(!pass.is_exact());
        let places = pass.collapsed_places(&alphabet).expect("names");
        assert_eq!(places.len(), pass.collapsed().len());
        for place in &places {
            // Exhibited, never counted: both places, and a non-empty separating passage.
            assert!(!place.left.is_empty());
            assert!(!place.right.is_empty());
            assert!(!place.separating_word.is_empty());
        }
        // The two routes' own places are merged by the one-shot reading and separated by conduct.
        assert!(places.iter().any(|place| {
            place.left_root.as_deref() == Some("left#0")
                && place.right_root.as_deref() == Some("right#1")
        }));
    }

    // ---------------------------------------------------------------------------- the revision

    #[test]
    fn a_revision_founds_one_boundary_per_pair_and_the_grain_is_monotone() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("both routes are in the deposit");
        let revision = MeaningRevision::revise(&pass, &alphabet, &deposit).expect("a revision");

        assert_eq!(revision.founded.len(), pass.collapsed().len());
        assert_eq!(revision.parent, MeaningGrain::origin());
        assert!(!revision.added.is_empty());
        // Monotone: every parent word survives, and every founded word is present.
        for word in revision.parent.cuts() {
            assert!(revision.grain.carries(&word));
        }
        for boundary in &revision.founded {
            assert!(revision.grain.carries(&boundary.word));
            // The lineage is the pair, kept whole.
            assert_eq!(boundary.pair, boundary.place.pair);
        }
    }

    #[test]
    fn a_boundary_at_a_name_the_deposit_cannot_open_is_retained_as_an_obstruction() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("both routes are in the deposit");
        let revision = MeaningRevision::revise(&pass, &alphabet, &deposit).expect("a revision");
        // `omega`, `ring` and `shared` are recruited and undeclared: the deposit cannot open them,
        // and a boundary that opens a part at one is returned by name rather than dropped.
        for obstruction in &revision.unopenable {
            assert!(!deposit.is_openable(&obstruction.name));
            assert!(!obstruction.inside.is_empty());
        }
        for founded in &revision.founded_roots {
            assert!(deposit.is_openable(&founded.name));
        }
    }

    // ----------------------------------------------------- the second pass rides a changed route

    #[test]
    fn the_second_pass_moves_and_every_change_names_the_pair_that_caused_it() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let run = Reintegration::run(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            8,
        )
        .expect("a run");

        let first = &run.turns[0];
        let movement = first.movement.as_ref().expect("the first turn moved");
        assert!(!movement.is_still());
        assert!(!movement.changed.is_empty());
        for moved in &movement.changed {
            assert_ne!(moved.before, moved.after);
            // The attribution: a boundary that actually matched inside this channel, carrying the
            // collapsed pair and the separating passage that founded it.
            assert!(!moved.caused_by.is_empty());
            for cause in &moved.caused_by {
                assert!(!cause.names.is_empty());
                assert_eq!(cause.pair, cause.place.pair);
            }
        }
    }

    #[test]
    fn the_second_pass_reaches_places_the_first_could_not_because_a_tail_is_rooted_at_no_name() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let run = Reintegration::run(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            8,
        )
        .expect("a run");
        let movement = run.turns[0].movement.as_ref().expect("the first turn moved");
        assert!(!movement.new_places.is_empty());
        // Every place the first pass had began at one of its roots. A place the second pass has and
        // the first did not is a shared tail, and it is rooted at no declared root.
        let first_places = run.turns[0].pass.places(&alphabet);
        for place in &movement.new_places {
            assert!(!first_places.contains(place));
        }
    }

    #[test]
    fn a_founded_root_carries_what_the_first_pass_returned_as_unopened() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let first = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("both routes are in the deposit");
        // The bounded aperture names what it stopped at: `helper` is openable and was not opened,
        // and what opening it would have brought is exhibited by name.
        assert_eq!(
            first.unopened().keys().cloned().collect::<BTreeSet<String>>(),
            BTreeSet::from(["deep".to_owned(), "further".to_owned()])
        );
        assert!(!first.constituents().contains("deep"));

        // Elaborated as a root in its own right, `helper` carries exactly that population.
        let second = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &["helper".to_owned()],
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("helper is declared");
        assert!(second.constituents().contains("deep"));
        assert!(second.constituents().contains("further"));
    }

    // -------------------------------------------------------------------------- the no-op control

    /// A channel whose every position has a distinct one-shot reading: the successor name differs
    /// at each step, so the one-shot partition is already discrete and nothing can be collapsed.
    #[test]
    fn a_reintegration_that_collapses_nothing_founds_no_boundary_and_the_next_pass_is_identical() {
        let population = vec![derivation(
            "only",
            "S",
            &[("aaa", 1), ("bbb", 1), ("ccc", 1), ("ddd", 1)],
        )];
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["only#0".to_owned()];
        let pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::Exhausted,
            &MeaningGrain::origin(),
        )
        .expect("the route is in the deposit");
        assert!(pass.is_exact());
        assert!(pass.collapsed().is_empty());

        // Nothing to found, so nothing is founded, and the next pass under the same grain is
        // bit-identical. If any revision always moved something, the revision would be noise.
        let revision = MeaningRevision::revise(&pass, &alphabet, &deposit).expect("a revision");
        assert!(revision.founded.is_empty());
        assert!(revision.added.is_empty());
        assert_eq!(revision.grain, MeaningGrain::origin());
        assert!(revision.founded_roots.is_empty());

        let again = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::Exhausted,
            &revision.grain,
        )
        .expect("the route is in the deposit");
        assert_eq!(again, pass);

        let movement = Movement::read(&pass, &again, &revision, &alphabet).expect("a movement");
        assert!(movement.is_still());

        let run = Reintegration::run(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::Exhausted,
            8,
        )
        .expect("a run");
        assert_eq!(run.rest, RestReason::ReintegrationIsExact);
        assert_eq!(run.rested_at, 0);
        assert_eq!(run.turns.len(), 1);
    }

    // -------------------------------------------------------------------------------- termination

    #[test]
    fn the_turning_rests_and_says_at_which_turn_and_why() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let run = Reintegration::run(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            16,
        )
        .expect("a run");
        assert!(matches!(
            run.rest,
            RestReason::ReintegrationIsExact | RestReason::GrainDidNotGrow
        ));
        assert_eq!(run.rested_at, run.turns.len() - 1);
        // The grain is monotone along the whole turning.
        let mut carried: BTreeSet<Vec<Symbol>> = BTreeSet::new();
        for turn in &run.turns {
            for word in &carried {
                assert!(turn.pass.grain.carries(word));
            }
            carried.extend(turn.pass.grain.cuts());
        }
    }

    #[test]
    fn a_bound_that_bites_returns_the_bound_and_the_state_rather_than_failing() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let run = Reintegration::run(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            1,
        )
        .expect("a run");
        assert_eq!(run.rest, RestReason::BoundReached);
        assert_eq!(run.turns.len(), 1);
        assert!(run.turns[0].revision.is_some());
        assert!(run.turns[0].movement.is_none());
    }

    // --------------------------------------------------------------------------------- the foil

    #[test]
    fn a_boundary_the_collapse_did_not_return_moves_a_different_population() {
        let population = deposited_shape();
        let (deposit, alphabet) = alphabet_over(&population);
        let roots = vec!["left#0".to_owned(), "right#1".to_owned()];
        let pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            &MeaningGrain::origin(),
        )
        .expect("both routes are in the deposit");
        let revision = MeaningRevision::revise(&pass, &alphabet, &deposit).expect("a revision");

        // A word of the same length the compression did not return. `left#0` is a root symbol: it
        // occurs at position zero of one channel and nowhere else, so cutting after it is a
        // boundary no collapse asked for.
        let foil_word = vec![alphabet.symbol("left#0").expect("declared")];
        assert!(!revision.added.contains(&foil_word));
        let foil = MeaningGrain::origin()
            .with(foil_word)
            .expect("a boundary");
        let foil_pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            &foil,
        )
        .expect("both routes are in the deposit");
        let derived_pass = ReintegrationPass::read(
            &deposit,
            &alphabet,
            &roots,
            ElaborationAperture::ToDepth(1),
            &revision.grain,
        )
        .expect("both routes are in the deposit");
        // The derived grain and the foil are not interchangeable: cutting anywhere is not the same
        // as cutting where the reading's own loss asked.
        assert_ne!(foil_pass.system, derived_pass.system);
    }
}
