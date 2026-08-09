//! Recovery of an opaque **symbol** codec from black-box testimony.
//!
//! ## What this is
//!
//! [`bit_causal`](crate::bit_causal) recovers an opaque recurrent **bit** transducer by returned
//! testimony alone. This module is the same operation on a different material: an opaque function
//! from a symbol stream to a segmentation — a tokenizer, a braille cell reader, a morse decoder, a
//! channel splitter — recovered from queries and nothing else.
//!
//! Brandon's position, which governs the shape of this organ: a tokenizer is a codec; braille,
//! morse, ASCII and colour channels are one operation on different surfaces; *"the symbol does not
//! dictate what the information contains"*; and *"I am most certain that the machine does not need
//! us to manually implement decoders for every traditionally divided medium."* The instrument below
//! is told which symbols exist and nothing else. It is not told that letters agglutinate, that
//! whitespace flushes, that `...` is one token and `,,` is two. It finds all of that, or it exhibits
//! the exact word it was not allowed to ask.
//!
//! ## The discipline, carried from the bit instrument
//!
//! > *"The instrument can call the black-box ABI and return its testimony. It cannot inspect the
//! > target through the production law, choose a distinguishing query, supply a candidate program,
//! > or issue a semantic certificate."*
//!
//! Here the target is an [`OpaqueSymbolCodec`], a boxed `dyn Fn(&str) -> Vec<String>`. Inspection is
//! impossible by construction: the recovery holds no handle to anything but the call. Every number
//! below is an exact integer. There is no score, no weight, no threshold, no probability, no
//! tolerance, and no ranking of candidates by magnitude.
//!
//! ## The declared query family
//!
//! ```text
//!   Family(alphabet, radius) = { w over the declared alphabet : 1 <= |w| <= radius }
//! ```
//!
//! The recovery may call the target on members of that family and on nothing else. The family is
//! **exhausted**, not sampled, so every statement of the form *"no admitted query separates these"*
//! is a theorem about the family rather than a report about a search that stopped.
//!
//! ## The recovered object is a structure, not a transcript
//!
//! [`RecoveredCodec`] is a finite machine that runs on inputs of any length, including inputs no
//! query ever visited:
//!
//! ```text
//!   state          = the class of the previous symbol
//!   emission(c)    = Emit | Drop            -- does a symbol of class c enter the token
//!   boundary(p,c)  = Join | Cut             -- does a token break between classes p and c
//! ```
//!
//! `Cut` closes the current token when it is non-empty; `Drop` contributes no characters. Word
//! characters are one class that `Join`s itself; whitespace is a `Drop` class that `Cut`s; a
//! punctuation run that agglutinates is a class that `Join`s itself; one that does not is a class
//! that `Cut`s itself. None of that vocabulary appears in the recovery — it is what the returned
//! structure turns out to say.
//!
//! ## How the structure is found
//!
//! 1. **Testimony.** Every family word is returned once and checked to be a segmentation at all:
//!    the concatenation of the returned tokens must be a subsequence of the input. A target that
//!    rewrites rather than segments fails here and the word and the return are exhibited.
//! 2. **The symbol quotient, by distinguishing context.** Two symbols are held together exactly
//!    when **no admissible context separates them**, where a context is a family word with one hole
//!    and separation means the returned token-length profiles differ. Contexts are enumerated
//!    shortest-first, so the context recorded on a [`SymbolSeparation`] is the *shortest* one that
//!    does it — the same Nerode/Moore discipline as
//!    [`receiver_exact_compression`](crate::receiver_exact_compression), where the round at which
//!    two items first separate is the length of the shortest word that distinguishes them.
//! 3. **Emission**, forced by the one-symbol word: `[]` is `Drop`, `[s]` is `Emit`. Members of one
//!    class cannot disagree, because the bare hole is itself an admissible context and would have
//!    separated them.
//! 4. **Boundaries between two `Emit` classes**, forced by the two-symbol word: `["ab"]` is `Join`,
//!    `["a","b"]` is `Cut`. At the start of a word the first symbol always opens a token, so there
//!    is no earlier state for the return to depend on.
//! 5. **Boundaries touching a `Drop` class are not forced by any short word**, because a dropped
//!    symbol contributes no character for the return to place. Every assignment of those entries is
//!    enumerated and **every** assignment consistent with the whole family is retained — the bit
//!    instrument's rule, that a compatible population is kept rather than collapsed.
//! 6. **The retained population is quotiented by observational equivalence**, computed exactly by a
//!    breadth-first search over the joint automaton of two candidate codecs
//!    ([`RecoveredCodec::shortest_separating_input`]). Two retained tables that no input separates
//!    are one codec written two ways — a **gauge freedom**, reported and not hidden. Two that some
//!    input separates are two codecs, and the family was too small to choose: that is an
//!    [`Obstruction::UndeterminedCodec`] carrying **the shortest input that would have decided it**,
//!    which is by construction longer than the radius.
//!
//! ## What this can and cannot recover
//!
//! It recovers exactly the codecs whose boundary decision depends on the **adjacent pair of symbol
//! classes** and nothing more. A target outside that shape does not return a wrong codec: every
//! assignment is refuted and [`Obstruction::NoConformingTable`] exhibits the input, the target's
//! return, and the candidate's return. A capacity mismatch is a defect even when an organ appears to
//! return, so the two apertures are **declared by the caller** in [`RecoveryApertures`], checked,
//! and refused rather than approximated.
//!
//! ## The apertures are the caller's, and there is no default
//!
//! Until 2026-08-09 the two numbers were `const FAMILY_APERTURE: u64 = 65_536` and
//! `const FREE_ENTRY_APERTURE: u64 = 12`, authored here. `canon/THE_AUTHORED_LEVEL.md` convicted
//! both: neither is derivable from the material — they are statements about the **host** the
//! recovery runs on — so neither was this organ's to pick. They now arrive in
//! [`RecoveryApertures`], which deliberately implements no `Default`: *a default is a level the
//! organ picked because the caller was never asked.*
//!
//! The **refusal shape was already lawful and is preserved**: past either aperture the recovery
//! returns `Err(RecoveryError::FamilyExceedsAperture)` or
//! `Obstruction::GaugeApertureExceeded` rather than sampling. One thing improved with the move: the
//! family refusal now names the width the material required as an exact [`BigUint`], where it
//! previously reported `u64::MAX` whenever `|alphabet|^radius` overflowed the counter — a saturated
//! stand-in in the one field whose whole job is to say what was needed.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::BigUint;
use num_traits::ToPrimitive;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// The resource apertures one recovery runs under, declared by the caller.
///
/// Both bound work rather than meaning: the family aperture is a call budget and a memory bound on
/// `sum(|alphabet|^L for L in 1..=radius)` returned words, and the free-entry aperture bounds a
/// `2^k` enumeration of the boundary entries the family leaves open. Neither is read off the
/// material; both are read off the host. **No `Default` is provided, on purpose.**
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct RecoveryApertures {
    /// The largest declared query family this recovery may exhaust. Every word is returned once, so
    /// this is a call budget as well as a memory bound.
    pub family_words: u64,
    /// The largest number of boundary entries the declared family may leave open. Every assignment
    /// is enumerated, so the search is `2^k` and this is the exponent.
    pub free_entries: u64,
}

impl RecoveryApertures {
    /// Declare both apertures. Named rather than constructed field-wise so a call site reads as a
    /// declaration.
    pub fn declared(family_words: u64, free_entries: u64) -> Self {
        Self {
            family_words,
            free_entries,
        }
    }
}

const RECOVERY_SCHEMA: &str = "holonic-engine.codec-recovery.v1";
const CODEC_SCHEMA: &str = "holonic-engine.recovered-symbol-codec.v1";
const CONFORMANCE_SCHEMA: &str = "holonic-engine.codec-conformance.v1";

/// One recovered symbol class. An opaque exact token — never a magnitude.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SymbolClass(pub u32);

/// Whether a symbol of a class enters the token it is read into.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Emission {
    /// The symbol becomes a character of the current token.
    Emit,
    /// The symbol contributes no character. Whitespace in a tokenizer; a stop bit in a frame codec.
    Drop,
}

/// Whether a token break falls between two adjacent symbol classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Boundary {
    /// No break. The token continues across this adjacency.
    Join,
    /// A break. A non-empty current token is closed here.
    Cut,
}

/// The opaque target.
///
/// A boxed law from a symbol stream to a segmentation. The recovery holds one of these and can do
/// exactly one thing with it: call it. There is no accessor for the law, no serialization of it, and
/// its [`std::fmt::Debug`] shows only how many times it has been called.
pub struct OpaqueSymbolCodec {
    law: SymbolCodecLaw,
    calls: Cell<u64>,
}

/// The law inside an [`OpaqueSymbolCodec`]. Named so it can be spoken about; there is no accessor
/// that returns one.
type SymbolCodecLaw = Box<dyn Fn(&str) -> Vec<String>>;

impl OpaqueSymbolCodec {
    pub fn new(law: impl Fn(&str) -> Vec<String> + 'static) -> Self {
        Self {
            law: Box::new(law),
            calls: Cell::new(0),
        }
    }

    /// Return the target's testimony at one input. The only admitted contact.
    pub fn returns(&self, input: &str) -> Vec<String> {
        self.calls.set(self.calls.get().saturating_add(1));
        (self.law)(input)
    }

    /// How many times the target has been called. A cost, reported rather than optimised away.
    pub fn calls(&self) -> u64 {
        self.calls.get()
    }
}

impl std::fmt::Debug for OpaqueSymbolCodec {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("OpaqueSymbolCodec")
            .field("calls", &self.calls.get())
            .finish_non_exhaustive()
    }
}

/// The recovered structure. It runs; it is not a description of a run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecoveredCodec {
    pub schema: String,
    /// The symbol quotient, ordered canonically by each class's least member.
    pub classes: Vec<BTreeSet<char>>,
    /// Indexed by class.
    pub emission: Vec<Emission>,
    /// `boundary[left][right]`.
    pub boundary: Vec<Vec<Boundary>>,
}

impl RecoveredCodec {
    pub fn class_count(&self) -> usize {
        self.classes.len()
    }

    pub fn class_of(&self, symbol: char) -> Option<SymbolClass> {
        self.classes
            .iter()
            .position(|block| block.contains(&symbol))
            .map(|index| SymbolClass(index as u32))
    }

    /// The least member of a class. The canonical witness this instrument writes words with.
    pub fn class_representative(&self, class: SymbolClass) -> Option<char> {
        self.classes
            .get(class.0 as usize)
            .and_then(|block| block.iter().next().copied())
    }

    pub fn emission_of(&self, symbol: char) -> Option<Emission> {
        self.class_of(symbol)
            .map(|class| self.emission[class.0 as usize])
    }

    pub fn boundary_between(&self, left: char, right: char) -> Option<Boundary> {
        let left = self.class_of(left)?;
        let right = self.class_of(right)?;
        Some(self.boundary[left.0 as usize][right.0 as usize])
    }

    /// The boundary must be square over the classes, because every runner below indexes it by a
    /// class on both axes.
    ///
    /// A structure that fails this is not a codec written badly — it is not a codec. Until
    /// 2026-08-08 nothing checked it and both [`segment`](Self::segment) and
    /// [`shortest_separating_input`](Self::shortest_separating_input) indexed straight into the rows:
    /// a `RecoveredCodec` carrying real classes and a one-by-one boundary **panicked** with an
    /// index out of bounds, while `codec_system::CodecSystem::joint` over the same value returned a
    /// typed refusal. Two organs that disagree about what is answerable cannot cross-check each
    /// other, so the refusal is stated here once and both runners take it.
    fn boundary_shape(&self) -> Result<(), RecoveryError> {
        let classes = self.classes.len();
        if self.boundary.len() != classes || self.boundary.iter().any(|row| row.len() != classes) {
            return Err(RecoveryError::MalformedBoundary {
                rows: self.boundary.len(),
                columns: self.boundary.first().map_or(0, Vec::len),
                classes,
            });
        }
        Ok(())
    }

    /// Run the recovered codec. Symbols outside the recovered alphabet are **refused**, never
    /// guessed at, and so is a boundary that is not square over the classes.
    pub fn segment(&self, input: &str) -> Result<Vec<String>, RecoveryError> {
        self.boundary_shape()?;
        let mut tokens = Vec::new();
        let mut current = String::new();
        let mut previous: Option<usize> = None;
        for symbol in input.chars() {
            let class = self
                .class_of(symbol)
                .ok_or(RecoveryError::UnknownSymbol { symbol })?
                .0 as usize;
            let cut = match previous {
                None => true,
                Some(before) => self.boundary[before][class] == Boundary::Cut,
            };
            if cut && !current.is_empty() {
                tokens.push(std::mem::take(&mut current));
            }
            if self.emission[class] == Emission::Emit {
                current.push(symbol);
            }
            previous = Some(class);
        }
        if !current.is_empty() {
            tokens.push(current);
        }
        Ok(tokens)
    }

    /// The **shortest input on which two codecs return different segmentations**, or `None` when no
    /// input of any length separates them.
    ///
    /// This is the distinguishing-query primitive, and it is exact rather than a bounded search.
    /// Two codecs over the same classes and the same emission emit the same characters in the same
    /// order; they can differ only in where the token breaks fall. So their joint conduct is a
    /// finite automaton on
    ///
    /// ```text
    ///   Synced { previous class, is a token open }          -- identical output so far
    ///   Pending { previous class, which side still holds }  -- one pushed a token the other holds
    /// ```
    ///
    /// with one absorbing `Diverged`. Breadth-first from the initial state returns the shortest
    /// separating class word, which is written out with each class's least member. The absence of a
    /// path to `Diverged` is a proof of observational identity over **all** inputs, not a failure to
    /// find one.
    pub fn shortest_separating_input(&self, other: &Self) -> Result<Option<String>, RecoveryError> {
        if self.classes != other.classes || self.emission != other.emission {
            return Err(RecoveryError::IncomparableCodecs);
        }
        self.boundary_shape()?;
        other.boundary_shape()?;
        let count = self.classes.len();

        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
        enum Joint {
            Synced { previous: Option<usize>, open: bool },
            Pending { previous: usize, left_holds: bool },
        }

        let start = Joint::Synced {
            previous: None,
            open: false,
        };
        let mut seen = BTreeSet::from([start]);
        let mut frontier = VecDeque::from([(start, Vec::<usize>::new())]);
        while let Some((state, word)) = frontier.pop_front() {
            for class in 0..count {
                let emits = self.emission[class] == Emission::Emit;
                let mut extended = word.clone();
                extended.push(class);
                let next = match state {
                    Joint::Synced { previous, open } => {
                        let left_cuts = previous
                            .is_none_or(|before| self.boundary[before][class] == Boundary::Cut);
                        let right_cuts = previous
                            .is_none_or(|before| other.boundary[before][class] == Boundary::Cut);
                        if left_cuts == right_cuts {
                            Some(Joint::Synced {
                                previous: Some(class),
                                open: if left_cuts { emits } else { open || emits },
                            })
                        } else if !open {
                            // Both breaks are no-ops on an empty token, so nothing was said
                            // differently and the two remain in step.
                            Some(Joint::Synced {
                                previous: Some(class),
                                open: emits,
                            })
                        } else if emits {
                            // One closed the token and began a new one with this character; the
                            // other appended it to the token it kept. The completed token differs.
                            None
                        } else {
                            Some(Joint::Pending {
                                previous: class,
                                left_holds: !left_cuts,
                            })
                        }
                    }
                    Joint::Pending {
                        previous,
                        left_holds,
                    } => {
                        let holder = if left_holds { self } else { other };
                        if holder.boundary[previous][class] == Boundary::Cut {
                            // The holder now pushes exactly the token the other already pushed.
                            // The two are back in step with identical output.
                            Some(Joint::Synced {
                                previous: Some(class),
                                open: emits,
                            })
                        } else if emits {
                            // The held token grows past the one the other already completed.
                            None
                        } else {
                            Some(Joint::Pending {
                                previous: class,
                                left_holds,
                            })
                        }
                    }
                };
                match next {
                    None => {
                        return Ok(Some(
                            extended
                                .into_iter()
                                .map(|class| {
                                    self.classes[class]
                                        .iter()
                                        .next()
                                        .copied()
                                        .expect("a recovered class is never empty")
                                })
                                .collect(),
                        ));
                    }
                    Some(state) => {
                        if seen.insert(state) {
                            frontier.push_back((state, extended));
                        }
                    }
                }
            }
        }
        Ok(None)
    }
}

/// Why two symbols are in different classes: the shortest admissible context that separates them,
/// and both returns at it.
///
/// This is the artifact, not a count.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolSeparation {
    pub left: char,
    pub right: char,
    /// The context, written as its two flanks around the hole.
    pub prefix: String,
    pub suffix: String,
    pub left_word: String,
    pub right_word: String,
    pub left_return: Vec<String>,
    pub right_return: Vec<String>,
}

impl SymbolSeparation {
    /// The length of the admissible word that carried the separation.
    pub fn context_length(&self) -> usize {
        self.prefix.chars().count() + 1 + self.suffix.chars().count()
    }
}

/// One exhibited disagreement between an opaque target and a candidate structure.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Disagreement {
    pub input: String,
    pub target: Vec<String>,
    pub recovered: Vec<String>,
}

/// A returned obstruction. Each carries the material that produced it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Obstruction {
    /// The target's return is not a segmentation of its input: the concatenated tokens are not a
    /// subsequence of the input, or a token is empty. A rewriting codec lands here.
    NotASegmentation {
        input: String,
        returned: Vec<String>,
    },
    /// The target's return at a one-symbol word is neither `[]` nor `[symbol]`, so no emission
    /// verdict is forced and none is invented.
    UnitNotSegmented {
        input: String,
        returned: Vec<String>,
    },
    /// The recovered emission implies a set of characters the return does not carry. The symbol's
    /// fate is not a property of the symbol, so no class assignment can express this target.
    EmissionDisagrees {
        input: String,
        returned: Vec<String>,
        implied: String,
    },
    /// Every assignment of the open boundary entries was refuted by the declared family. The target
    /// is outside the declared shape, and the refutations are exhibited.
    NoConformingTable {
        refuted_tables: u64,
        witnesses: Vec<Disagreement>,
    },
    /// The declared family retained two codecs that some input separates. It was too small to
    /// choose, and the shortest input that would have chosen is named — necessarily longer than the
    /// radius, or it would have been asked.
    UndeterminedCodec {
        separating_input: String,
        left: RecoveredCodec,
        right: RecoveredCodec,
        left_return: Vec<String>,
        right_return: Vec<String>,
    },
    /// The declared family leaves more boundary entries open than the enumeration aperture admits.
    GaugeApertureExceeded { free_entries: u64, aperture: u64 },
}

/// What the recovery cost, in exact counts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecoveryWork {
    pub declared_family_words: u64,
    pub target_calls: u64,
    pub contexts_examined: u64,
    pub tables_examined: u64,
    pub table_word_checks: u64,
}

/// What a recovery returns.
///
/// The invariant is exact: `codec.is_some()` if and only if `obstructions.is_empty()`. A codec is
/// never presented alongside a reason it might be wrong.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CodecRecovery {
    pub schema: String,
    pub alphabet: Vec<char>,
    pub radius: usize,
    /// The recovered symbol quotient. Empty when the recovery halted before finding it.
    pub classes: Vec<BTreeSet<char>>,
    /// Every pair the quotient separated, with the shortest context that did it.
    pub separations: Vec<SymbolSeparation>,
    pub codec: Option<RecoveredCodec>,
    pub obstructions: Vec<Obstruction>,
    /// Boundary entries the retained tables disagree on. Present only when every retained table is
    /// observationally identical, in which case these are free choices and not open questions.
    pub gauge_freedom: Vec<(SymbolClass, SymbolClass)>,
    pub retained_tables: u64,
    /// How many of the retained tables are distinct codecs. One is a recovery; more is an
    /// obstruction.
    pub inequivalent_codecs: u64,
    pub work: RecoveryWork,
}

impl CodecRecovery {
    pub fn is_recovered(&self) -> bool {
        self.codec.is_some()
    }
}

/// One held-out input the recovered codec refused because it carries an undeclared symbol.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Refusal {
    pub input: String,
    pub symbol: char,
}

/// Conformance on a held-out population. Disagreements are exhibited, never rated.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Conformance {
    pub schema: String,
    pub examined: u64,
    pub disagreements: Vec<Disagreement>,
    pub refusals: Vec<Refusal>,
}

impl Conformance {
    pub fn is_exact(&self) -> bool {
        self.disagreements.is_empty() && self.refusals.is_empty()
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum RecoveryError {
    #[error("the declared alphabet is empty")]
    EmptyAlphabet,
    #[error("a radius of {radius} admits no adjacency; the family must reach two-symbol words")]
    RadiusBelowAperture { radius: usize },
    #[error("the declared family holds {words} words, past the {aperture}-word aperture")]
    FamilyExceedsAperture { words: BigUint, aperture: u64 },
    /// The declared free-entry aperture is past what the enumeration carrier can address. Read off
    /// the carrier — the assignment ordinal is a `u64` — and not authored.
    #[error(
        "a free-entry aperture of {aperture} exceeds the {carrier_bits}-bit enumeration carrier"
    )]
    FreeEntryApertureUnrepresentable { aperture: u64, carrier_bits: u32 },
    #[error("the symbol {symbol:?} is outside the recovered alphabet")]
    UnknownSymbol { symbol: char },
    #[error("codecs over different symbol classes carry no common input to separate them on")]
    IncomparableCodecs,
    #[error("a codec over {classes} classes declares a {rows}x{columns} boundary")]
    MalformedBoundary {
        rows: usize,
        columns: usize,
        classes: usize,
    },
}

/// Recover an opaque symbol codec from testimony over the declared query family.
///
/// `alphabet` is deduplicated and ordered; `radius` is the longest word the instrument may ask
/// about; `apertures` is what this caller's host can hold. Nothing else is declared, and in
/// particular no character classes are supplied.
pub fn recover(
    target: &OpaqueSymbolCodec,
    alphabet: &[char],
    radius: usize,
    apertures: RecoveryApertures,
) -> Result<CodecRecovery, RecoveryError> {
    let alphabet: Vec<char> = alphabet.iter().copied().collect::<BTreeSet<_>>().into_iter().collect();
    if alphabet.is_empty() {
        return Err(RecoveryError::EmptyAlphabet);
    }
    if radius < 2 {
        return Err(RecoveryError::RadiusBelowAperture { radius });
    }
    if apertures.free_entries >= u64::BITS as u64 {
        return Err(RecoveryError::FreeEntryApertureUnrepresentable {
            aperture: apertures.free_entries,
            carrier_bits: u64::BITS,
        });
    }
    let symbols = alphabet.len();

    // The family's exact size, before a single word is built or a single call is made. Computed
    // over `BigUint` so an over-large declaration is refused with the width the material actually
    // required rather than with a saturated stand-in.
    let mut required = BigUint::from(0u32);
    let mut power = BigUint::from(1u32);
    for _ in 1..=radius {
        power *= symbols;
        required += &power;
    }
    if required > BigUint::from(apertures.family_words) {
        return Err(RecoveryError::FamilyExceedsAperture {
            words: required,
            aperture: apertures.family_words,
        });
    }
    // Inside the declared aperture the count fits the carrier by construction.
    let total = required
        .to_u64()
        .expect("a family inside a u64 aperture fits a u64");

    // The family, laid out by increasing length then lexicographically, so an index into it is
    // arithmetic and "shortest first" is the traversal order rather than a sort.
    let mut offsets = vec![0usize; radius + 2];
    let mut running = 0u64;
    let mut length_count = 1u64;
    for slot in offsets.iter_mut().take(radius + 1).skip(1) {
        length_count *= symbols as u64;
        *slot = running as usize;
        running += length_count;
    }
    offsets[radius + 1] = total as usize;

    let mut family: Vec<Vec<usize>> = Vec::with_capacity(total as usize);
    for length in 1..=radius {
        let count = (symbols as u64).pow(length as u32);
        for ordinal in 0..count {
            let mut digits = vec![0usize; length];
            let mut rest = ordinal;
            for position in (0..length).rev() {
                digits[position] = (rest % symbols as u64) as usize;
                rest /= symbols as u64;
            }
            family.push(digits);
        }
    }

    let mut work = RecoveryWork {
        declared_family_words: total,
        ..RecoveryWork::default()
    };

    // 1. Testimony, and the only structural demand made of it before anything is recovered: a
    //    return must be a segmentation of its input at all.
    let words: Vec<String> = family
        .iter()
        .map(|digits| digits.iter().map(|digit| alphabet[*digit]).collect())
        .collect();
    let mut testimony: Vec<Vec<String>> = Vec::with_capacity(family.len());
    for word in &words {
        testimony.push(target.returns(word));
    }
    work.target_calls = target.calls();
    for (index, returned) in testimony.iter().enumerate() {
        if !is_segmentation_of(&words[index], returned) {
            return Ok(halted(
                &alphabet,
                radius,
                Vec::new(),
                Vec::new(),
                Obstruction::NotASegmentation {
                    input: words[index].clone(),
                    returned: returned.clone(),
                },
                work,
            ));
        }
    }
    let profiles: Vec<Vec<usize>> = testimony
        .iter()
        .map(|returned| returned.iter().map(|token| token.chars().count()).collect())
        .collect();

    // 2. The symbol quotient. Contexts shortest-first, so the recorded separator is the shortest.
    let mut block = vec![0usize; symbols];
    let mut separations: Vec<SymbolSeparation> = Vec::new();
    let mut filled = vec![0usize; radius];
    'contexts: for length in 1..=radius {
        let fills = (symbols as u64).pow((length - 1) as u32);
        for hole in 0..length {
            for ordinal in 0..fills {
                if block.iter().collect::<BTreeSet<_>>().len() == symbols {
                    break 'contexts;
                }
                work.contexts_examined = work.contexts_examined.saturating_add(1);
                let mut rest = ordinal;
                for position in (0..length - 1).rev() {
                    let digit = (rest % symbols as u64) as usize;
                    rest /= symbols as u64;
                    filled[if position < hole { position } else { position + 1 }] = digit;
                }
                let indices: Vec<usize> = (0..symbols)
                    .map(|symbol| {
                        filled[hole] = symbol;
                        word_index(&offsets, symbols, &filled[..length])
                    })
                    .collect();
                for left in 0..symbols {
                    for right in left + 1..symbols {
                        if block[left] == block[right]
                            && profiles[indices[left]] != profiles[indices[right]]
                        {
                            filled[hole] = left;
                            let prefix: String =
                                filled[..hole].iter().map(|digit| alphabet[*digit]).collect();
                            let suffix: String = filled[hole + 1..length]
                                .iter()
                                .map(|digit| alphabet[*digit])
                                .collect();
                            separations.push(SymbolSeparation {
                                left: alphabet[left],
                                right: alphabet[right],
                                prefix,
                                suffix,
                                left_word: words[indices[left]].clone(),
                                right_word: words[indices[right]].clone(),
                                left_return: testimony[indices[left]].clone(),
                                right_return: testimony[indices[right]].clone(),
                            });
                        }
                    }
                }
                let mut fresh: BTreeMap<(usize, &Vec<usize>), usize> = BTreeMap::new();
                let mut refined = vec![0usize; symbols];
                for symbol in 0..symbols {
                    let key = (block[symbol], &profiles[indices[symbol]]);
                    let next = fresh.len();
                    refined[symbol] = *fresh.entry(key).or_insert(next);
                }
                block = refined;
            }
        }
    }

    // Canonical class order: by each class's least symbol, which is its least character because the
    // alphabet is ordered.
    let mut order: Vec<usize> = Vec::new();
    let mut class_of_symbol = vec![0usize; symbols];
    for symbol in 0..symbols {
        let position = order.iter().position(|seen| *seen == block[symbol]);
        class_of_symbol[symbol] = match position {
            Some(position) => position,
            None => {
                order.push(block[symbol]);
                order.len() - 1
            }
        };
    }
    let count = order.len();
    let classes: Vec<BTreeSet<char>> = (0..count)
        .map(|class| {
            (0..symbols)
                .filter(|symbol| class_of_symbol[*symbol] == class)
                .map(|symbol| alphabet[symbol])
                .collect()
        })
        .collect();
    let representative: Vec<usize> = (0..count)
        .map(|class| {
            (0..symbols)
                .find(|symbol| class_of_symbol[*symbol] == class)
                .expect("every recovered class holds a symbol")
        })
        .collect();

    // 3. Emission, forced by the one-symbol word. Members of a class cannot disagree here: the bare
    //    hole is an admissible context and would have separated them.
    let mut emission = Vec::with_capacity(count);
    for witness in representative.iter().copied() {
        let index = word_index(&offsets, symbols, &[witness]);
        emission.push(match profiles[index].as_slice() {
            [] => Emission::Drop,
            [1] => Emission::Emit,
            _ => {
                return Ok(halted(
                    &alphabet,
                    radius,
                    classes,
                    separations,
                    Obstruction::UnitNotSegmented {
                        input: words[index].clone(),
                        returned: testimony[index].clone(),
                    },
                    work,
                ));
            }
        });
    }

    // 4. The emission is a claim about every word, not only the one-symbol ones: the returned
    //    characters must be exactly the input with the dropped classes removed.
    for (index, digits) in family.iter().enumerate() {
        let implied: String = digits
            .iter()
            .filter(|digit| emission[class_of_symbol[**digit]] == Emission::Emit)
            .map(|digit| alphabet[*digit])
            .collect();
        if testimony[index].concat() != implied {
            return Ok(halted(
                &alphabet,
                radius,
                classes,
                separations,
                Obstruction::EmissionDisagrees {
                    input: words[index].clone(),
                    returned: testimony[index].clone(),
                    implied,
                },
                work,
            ));
        }
    }

    // 5. Boundaries between two Emit classes are forced by the two-symbol word: the first symbol of
    //    a word always opens a token, so the return depends on this adjacency and nothing else.
    //    Boundaries touching a Drop class are forced by nothing short, and are left open.
    let mut fixed = vec![Boundary::Cut; count * count];
    let mut free: Vec<(usize, usize)> = Vec::new();
    for left in 0..count {
        for right in 0..count {
            if emission[left] == Emission::Emit && emission[right] == Emission::Emit {
                let index = word_index(
                    &offsets,
                    symbols,
                    &[representative[left], representative[right]],
                );
                // The emission check above forces two emitted characters here, so the profile is
                // either one token of two or two tokens of one.
                fixed[left * count + right] = if profiles[index].len() == 1 {
                    Boundary::Join
                } else {
                    Boundary::Cut
                };
            } else {
                free.push((left, right));
            }
        }
    }
    if free.len() as u64 > apertures.free_entries {
        return Ok(halted(
            &alphabet,
            radius,
            classes,
            separations,
            Obstruction::GaugeApertureExceeded {
                free_entries: free.len() as u64,
                aperture: apertures.free_entries,
            },
            work,
        ));
    }

    // 6. Every assignment of the open entries, filtered by the whole family. The compatible
    //    population is retained rather than collapsed.
    let assignments = 1u64 << free.len();
    let mut retained: Vec<Vec<Boundary>> = Vec::new();
    let mut witnesses: BTreeSet<Disagreement> = BTreeSet::new();
    for assignment in 0..assignments {
        work.tables_examined = work.tables_examined.saturating_add(1);
        let mut table = fixed.clone();
        for (bit, (left, right)) in free.iter().enumerate() {
            table[left * count + right] = if assignment >> bit & 1 == 1 {
                Boundary::Join
            } else {
                Boundary::Cut
            };
        }
        let mut refuted = None;
        for (index, digits) in family.iter().enumerate() {
            work.table_word_checks = work.table_word_checks.saturating_add(1);
            if !conforms(
                &emission,
                &table,
                count,
                digits,
                &class_of_symbol,
                &profiles[index],
            ) {
                refuted = Some(index);
                break;
            }
        }
        match refuted {
            None => retained.push(table),
            Some(index) => {
                if retained.is_empty() {
                    witnesses.insert(Disagreement {
                        input: words[index].clone(),
                        target: testimony[index].clone(),
                        recovered: segment_digits(
                            &alphabet,
                            &emission,
                            &table,
                            count,
                            &family[index],
                            &class_of_symbol,
                        ),
                    });
                }
            }
        }
    }
    if retained.is_empty() {
        return Ok(halted(
            &alphabet,
            radius,
            classes,
            separations,
            Obstruction::NoConformingTable {
                refuted_tables: assignments,
                witnesses: witnesses.into_iter().collect(),
            },
            work,
        ));
    }

    // 7. Quotient the retained population by observational equivalence. Tables no input separates
    //    are one codec; tables some input separates are the obstruction, and the input is named.
    let build = |table: &[Boundary]| RecoveredCodec {
        schema: CODEC_SCHEMA.to_owned(),
        classes: classes.clone(),
        emission: emission.clone(),
        boundary: (0..count)
            .map(|left| table[left * count..(left + 1) * count].to_vec())
            .collect(),
    };
    let mut inequivalent: Vec<RecoveredCodec> = Vec::new();
    let mut obstructions: Vec<Obstruction> = Vec::new();
    for table in &retained {
        let candidate = build(table);
        let mut separated = true;
        for known in &inequivalent {
            if known.shortest_separating_input(&candidate)?.is_none() {
                separated = false;
                break;
            }
        }
        if separated {
            if let Some(first) = inequivalent.first() {
                let input = first
                    .shortest_separating_input(&candidate)?
                    .expect("an inequivalent codec carries a separating input");
                obstructions.push(Obstruction::UndeterminedCodec {
                    left_return: first.segment(&input)?,
                    right_return: candidate.segment(&input)?,
                    separating_input: input,
                    left: first.clone(),
                    right: candidate.clone(),
                });
            }
            inequivalent.push(candidate);
        }
    }

    let gauge_freedom: Vec<(SymbolClass, SymbolClass)> = free
        .iter()
        .filter(|(left, right)| {
            let first = retained[0][left * count + right];
            retained
                .iter()
                .any(|table| table[left * count + right] != first)
        })
        .map(|(left, right)| (SymbolClass(*left as u32), SymbolClass(*right as u32)))
        .collect();

    let codec = obstructions.is_empty().then(|| build(&retained[0]));
    Ok(CodecRecovery {
        schema: RECOVERY_SCHEMA.to_owned(),
        alphabet,
        radius,
        classes,
        separations,
        codec,
        obstructions,
        gauge_freedom,
        retained_tables: retained.len() as u64,
        inequivalent_codecs: inequivalent.len() as u64,
        work,
    })
}

/// Check a recovered codec against the opaque target on held-out material.
///
/// Disagreements are returned as artifacts — the input and both returns — and never as a rate. An
/// input carrying a symbol outside the recovered alphabet is recorded as a refusal, because a
/// structure that has never seen a symbol has nothing to say about it.
pub fn conform(
    codec: &RecoveredCodec,
    target: &OpaqueSymbolCodec,
    population: &[&str],
) -> Conformance {
    let mut disagreements = Vec::new();
    let mut refusals = Vec::new();
    for input in population {
        match codec.segment(input) {
            Ok(recovered) => {
                let returned = target.returns(input);
                if recovered != returned {
                    disagreements.push(Disagreement {
                        input: (*input).to_owned(),
                        target: returned,
                        recovered,
                    });
                }
            }
            Err(RecoveryError::UnknownSymbol { symbol }) => refusals.push(Refusal {
                input: (*input).to_owned(),
                symbol,
            }),
            Err(_) => unreachable!("segment refuses only on an undeclared symbol"),
        }
    }
    Conformance {
        schema: CONFORMANCE_SCHEMA.to_owned(),
        examined: population.len() as u64,
        disagreements,
        refusals,
    }
}

fn halted(
    alphabet: &[char],
    radius: usize,
    classes: Vec<BTreeSet<char>>,
    separations: Vec<SymbolSeparation>,
    obstruction: Obstruction,
    work: RecoveryWork,
) -> CodecRecovery {
    CodecRecovery {
        schema: RECOVERY_SCHEMA.to_owned(),
        alphabet: alphabet.to_vec(),
        radius,
        classes,
        separations,
        codec: None,
        obstructions: vec![obstruction],
        gauge_freedom: Vec::new(),
        retained_tables: 0,
        inequivalent_codecs: 0,
        work,
    }
}

/// Is this return a segmentation of this input at all — non-empty tokens whose concatenation is a
/// subsequence of the input, in order? A rewriting codec fails here, and so does a reordering one.
fn is_segmentation_of(input: &str, returned: &[String]) -> bool {
    if returned.iter().any(|token| token.is_empty()) {
        return false;
    }
    let mut source = input.chars().peekable();
    for symbol in returned.iter().flat_map(|token| token.chars()) {
        loop {
            match source.next() {
                None => return false,
                Some(seen) if seen == symbol => break,
                Some(_) => {}
            }
        }
    }
    true
}

fn word_index(offsets: &[usize], symbols: usize, digits: &[usize]) -> usize {
    let mut value = 0usize;
    for digit in digits {
        value = value * symbols + digit;
    }
    offsets[digits.len()] + value
}

/// Does this table reproduce the target's token-length profile at this word? Exact, allocation-free,
/// and short-circuiting at the first disagreement.
fn conforms(
    emission: &[Emission],
    table: &[Boundary],
    count: usize,
    digits: &[usize],
    class_of_symbol: &[usize],
    expected: &[usize],
) -> bool {
    let mut produced = 0usize;
    let mut open = 0usize;
    let mut previous: Option<usize> = None;
    for digit in digits {
        let class = class_of_symbol[*digit];
        let cut = previous.is_none_or(|before| table[before * count + class] == Boundary::Cut);
        if cut && open > 0 {
            if expected.get(produced) != Some(&open) {
                return false;
            }
            produced += 1;
            open = 0;
        }
        if emission[class] == Emission::Emit {
            open += 1;
        }
        previous = Some(class);
    }
    if open > 0 {
        if expected.get(produced) != Some(&open) {
            return false;
        }
        produced += 1;
    }
    produced == expected.len()
}

fn segment_digits(
    alphabet: &[char],
    emission: &[Emission],
    table: &[Boundary],
    count: usize,
    digits: &[usize],
    class_of_symbol: &[usize],
) -> Vec<String> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut previous: Option<usize> = None;
    for digit in digits {
        let class = class_of_symbol[*digit];
        let cut = previous.is_none_or(|before| table[before * count + class] == Boundary::Cut);
        if cut && !current.is_empty() {
            tokens.push(std::mem::take(&mut current));
        }
        if emission[class] == Emission::Emit {
            current.push(alphabet[*digit]);
        }
        previous = Some(class);
    }
    if !current.is_empty() {
        tokens.push(current);
    }
    tokens
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **What this test body declares as its host capacity.** A fixture is a caller and declares
    /// its own apertures; the values that used to live in the organ as `FAMILY_APERTURE = 65_536`
    /// and `FREE_ENTRY_APERTURE = 12` are reproduced here so the fixtures' returns are unchanged by
    /// the move and the orbit is measured against the level rather than against a new number.
    const TEST_APERTURES: RecoveryApertures = RecoveryApertures {
        family_words: 65_536,
        free_entries: 12,
    };

    /// A genuine character-class state machine, written as a state machine and never as a table, so
    /// the recovery has to find the quotient rather than read it.
    ///
    /// Word characters agglutinate. Digits agglutinate with each other but not with letters.
    /// Whitespace is dropped and flushes. `.` and `-` are a run class: `...` and `.-` are one token.
    /// `,` and `;` are a solo class: `,,` is two tokens.
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
                        before != here
                            || !matches!(here, Kind::Word | Kind::Digit | Kind::Run)
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

    const TOKENIZER_ALPHABET: [char; 11] =
        ['a', 'b', 'q', '0', '1', ' ', '\t', '.', '-', ',', ';'];

    /// A codec whose dropped symbol **joins**: `"a_b"` is one token. Radius 2 cannot see through it,
    /// because a dropped symbol contributes no character for a two-symbol return to place.
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

    fn class_containing(recovery: &CodecRecovery, symbol: char) -> BTreeSet<char> {
        recovery
            .classes
            .iter()
            .find(|block| block.contains(&symbol))
            .cloned()
            .unwrap_or_default()
    }

    /// The tokenizer's five classes are recovered from testimony alone. No character class, no
    /// regular expression, and no notion of "letter" was supplied.
    #[test]
    fn the_character_classes_of_a_tokenizer_are_recovered_from_testimony_alone() {
        let target = tokenizer();
        let recovery = recover(&target, &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible");
        assert!(
            recovery.obstructions.is_empty(),
            "unexpected obstructions: {:?}",
            recovery.obstructions
        );
        let codec = recovery.codec.as_ref().expect("the codec is recovered");

        assert_eq!(recovery.classes.len(), 5, "classes: {:?}", recovery.classes);
        assert_eq!(
            class_containing(&recovery, 'a'),
            BTreeSet::from(['a', 'b', 'q'])
        );
        assert_eq!(class_containing(&recovery, '0'), BTreeSet::from(['0', '1']));
        assert_eq!(class_containing(&recovery, ' '), BTreeSet::from([' ', '\t']));
        assert_eq!(class_containing(&recovery, '.'), BTreeSet::from(['.', '-']));
        assert_eq!(class_containing(&recovery, ','), BTreeSet::from([',', ';']));

        assert_eq!(codec.emission_of(' '), Some(Emission::Drop));
        assert_eq!(codec.emission_of('\t'), Some(Emission::Drop));
        for emitted in ['a', 'q', '1', '-', ';'] {
            assert_eq!(
                codec.emission_of(emitted),
                Some(Emission::Emit),
                "{emitted:?} must be emitted"
            );
        }

        // The four boundary facts the fixture actually encodes, each read off the structure.
        assert_eq!(codec.boundary_between('a', 'q'), Some(Boundary::Join));
        assert_eq!(codec.boundary_between('0', '1'), Some(Boundary::Join));
        assert_eq!(codec.boundary_between('.', '-'), Some(Boundary::Join));
        assert_eq!(codec.boundary_between(',', ';'), Some(Boundary::Cut));
        assert_eq!(codec.boundary_between('a', '0'), Some(Boundary::Cut));
        assert_eq!(codec.boundary_between('a', '.'), Some(Boundary::Cut));
    }

    /// The recovered object runs on material the query family never reached. Every held-out input is
    /// longer than the radius, so nothing here is a lookup of retained testimony.
    #[test]
    fn the_recovered_codec_conforms_exactly_on_held_out_material_longer_than_the_family() {
        let target = tokenizer();
        let recovery = recover(&target, &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible");
        let codec = recovery.codec.as_ref().expect("the codec is recovered");

        let population = [
            "aab qq  0011..a-b,;q",
            "...--,,ab",
            "\ta0 b1\t\tq",
            "a.b-q,0;1 ab",
            "  ,,,;;; ..--..  ",
            "qqq111aaa000",
            "a\t.\t,\t0\tb",
            "-.-.-.ab01,;q ",
        ];
        for input in population {
            assert!(
                input.chars().count() > recovery.radius,
                "{input:?} must be longer than the radius or it proves nothing"
            );
        }
        let conformance = conform(codec, &target, &population);
        assert!(
            conformance.is_exact(),
            "disagreements: {:?} refusals: {:?}",
            conformance.disagreements,
            conformance.refusals
        );
        assert_eq!(conformance.examined, population.len() as u64);

        // The material must be capable of varying the property: a population that only ever returns
        // one token would conform under almost any table.
        let widest = population
            .iter()
            .map(|input| codec.segment(input).expect("declared symbols only").len())
            .max()
            .expect("the population is not empty");
        assert!(widest >= 8, "the held-out material returns at most {widest} tokens");
    }

    /// `conform` must be able to return something. A conformance check that cannot exhibit a
    /// disagreement is a law that returns zero and proves nothing about itself.
    #[test]
    fn conformance_exhibits_a_disagreement_against_a_target_the_codec_does_not_describe() {
        let target = tokenizer();
        let recovery = recover(&target, &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible");
        let codec = recovery.codec.as_ref().expect("the codec is recovered");

        // Same alphabet, different law: digits now agglutinate with letters.
        let other = OpaqueSymbolCodec::new(|input: &str| {
            let mut tokens = Vec::new();
            let mut current = String::new();
            for symbol in input.chars() {
                if symbol.is_ascii_alphanumeric() {
                    current.push(symbol);
                } else {
                    if !current.is_empty() {
                        tokens.push(std::mem::take(&mut current));
                    }
                    if symbol != ' ' && symbol != '\t' {
                        tokens.push(symbol.to_string());
                    }
                }
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        });
        let conformance = conform(codec, &other, &["a0", "ab01 q"]);
        assert!(!conformance.is_exact());
        let exhibited = conformance
            .disagreements
            .iter()
            .find(|disagreement| disagreement.input == "a0")
            .expect("the disagreement is exhibited by input, not summarised as a rate");
        assert_eq!(exhibited.target, vec!["a0".to_owned()]);
        assert_eq!(exhibited.recovered, vec!["a".to_owned(), "0".to_owned()]);
    }

    /// A symbol outside the recovered alphabet is refused. The structure has nothing to say about a
    /// symbol it never received testimony for, and says that rather than guessing a class.
    #[test]
    fn material_carrying_an_undeclared_symbol_is_refused_rather_than_guessed() {
        let target = tokenizer();
        let recovery = recover(&target, &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible");
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let conformance = conform(codec, &target, &["ab qq", "ab zz"]);
        assert!(conformance.disagreements.is_empty());
        assert_eq!(
            conformance.refusals,
            vec![Refusal {
                input: "ab zz".to_owned(),
                symbol: 'z'
            }]
        );
    }

    /// Each separation carries the **shortest** admissible context that produced it, not merely a
    /// working one. Emission is visible in the bare hole; agglutination is not visible until a
    /// neighbour exists.
    #[test]
    fn a_separation_carries_the_shortest_context_that_produced_it() {
        let target = tokenizer();
        let recovery = recover(&target, &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible");

        let find = |left: char, right: char| {
            recovery
                .separations
                .iter()
                .find(|separation| {
                    (separation.left, separation.right) == (left, right)
                        || (separation.left, separation.right) == (right, left)
                })
                .unwrap_or_else(|| panic!("{left:?} and {right:?} are separated"))
        };

        // A dropped symbol against an emitted one is visible in the one-symbol word. Pairs are
        // recorded in alphabet order, so the emitted side is whichever of the two it is.
        let dropped = find('a', ' ');
        assert_eq!(dropped.context_length(), 1);
        assert_eq!((dropped.prefix.as_str(), dropped.suffix.as_str()), ("", ""));
        let (emitted, absent) = if dropped.left == 'a' {
            (&dropped.left_return, &dropped.right_return)
        } else {
            (&dropped.right_return, &dropped.left_return)
        };
        assert_eq!(*emitted, vec!["a".to_owned()]);
        assert!(absent.is_empty());

        // Two emitted symbols that differ only in what they agglutinate with need a neighbour, so
        // the shortest context that separates them has length two.
        for (left, right) in [('a', '0'), ('a', ','), ('.', ','), ('0', '.')] {
            let separation = find(left, right);
            assert_eq!(
                separation.context_length(),
                2,
                "{left:?}/{right:?} separated by {:?}|{:?}",
                separation.prefix,
                separation.suffix
            );
        }

        // Every recorded separation is between symbols the recovery really did place apart.
        for separation in &recovery.separations {
            assert_ne!(
                class_containing(&recovery, separation.left),
                class_containing(&recovery, separation.right)
            );
            assert_ne!(separation.left_return, separation.right_return);
        }
    }

    /// Enlarging the radius enlarges the context family, so the symbol quotient can only refine.
    /// The check would be vacuous if it never refined, so the strict step is asserted too.
    #[test]
    fn the_symbol_quotient_refines_monotonically_as_the_radius_grows() {
        let mut sizes = Vec::new();
        let mut previous: Option<Vec<BTreeSet<char>>> = None;
        for radius in 2..=4 {
            let target = tokenizer();
            let recovery =
                recover(&target, &TOKENIZER_ALPHABET, radius, TEST_APERTURES).expect("the family is admissible");
            sizes.push(recovery.classes.len());
            if let Some(coarser) = &previous {
                for block in &recovery.classes {
                    assert!(
                        coarser.iter().any(|before| block.is_subset(before)),
                        "radius {radius} split {block:?} out of no single earlier class"
                    );
                }
            }
            previous = Some(recovery.classes.clone());
        }
        assert_eq!(sizes, vec![5, 5, 5]);

        // Radius two is already the fixed point for this alphabet, so the strict step has to be
        // shown on material where a longer context is what does the separating.
        let staged = OpaqueSymbolCodec::new(|input: &str| {
            // 'a' and 'b' behave alike everywhere except after "aa", where 'b' breaks the token.
            let mut tokens = Vec::new();
            let mut current = String::new();
            let symbols: Vec<char> = input.chars().collect();
            for (position, symbol) in symbols.iter().enumerate() {
                let cut = position >= 2
                    && *symbol == 'b'
                    && symbols[position - 1] == 'a'
                    && symbols[position - 2] == 'a';
                if cut && !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
                current.push(*symbol);
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        });
        let coarse = recover(&staged, &['a', 'b'], 2, TEST_APERTURES).expect("the family is admissible");
        let fine = recover(&staged, &['a', 'b'], 3, TEST_APERTURES).expect("the family is admissible");
        assert_eq!(coarse.classes.len(), 1, "{:?}", coarse.classes);
        assert_eq!(fine.classes.len(), 2, "{:?}", fine.classes);
        for block in &fine.classes {
            assert!(coarse.classes.iter().any(|before| block.is_subset(before)));
        }
    }

    /// The negative control. At radius two the declared family **provably** cannot see through a
    /// dropped symbol, and the recovery returns the obstruction with the shortest word that would
    /// have decided it — a word one longer than the radius, which is exactly the word it was not
    /// allowed to ask.
    #[test]
    fn a_family_that_cannot_see_through_a_dropped_symbol_names_the_word_it_could_not_ask() {
        let target = soft_join();
        let recovery = recover(&target, &['a', 'b', '_'], 2, TEST_APERTURES).expect("the family is admissible");

        assert!(
            recovery.codec.is_none(),
            "an undetermined codec must not be presented as recovered"
        );
        assert!(recovery.inequivalent_codecs > 1);
        assert_eq!(recovery.classes.len(), 2, "{:?}", recovery.classes);

        let Some(Obstruction::UndeterminedCodec {
            separating_input,
            left,
            right,
            left_return,
            right_return,
        }) = recovery.obstructions.first()
        else {
            panic!("expected an undetermined codec, got {:?}", recovery.obstructions);
        };
        assert_eq!(
            separating_input.chars().count(),
            3,
            "separating input {separating_input:?}"
        );
        assert!(
            separating_input.chars().count() > recovery.radius,
            "a word inside the family would have been asked and would have decided this"
        );
        assert_ne!(left_return, right_return);
        assert_eq!(left.segment(separating_input).unwrap(), *left_return);
        assert_eq!(right.segment(separating_input).unwrap(), *right_return);

        // The blindness is real: the target does answer this word, and exactly one of the two
        // retained codecs is right about it.
        let truth = target.returns(separating_input);
        assert_eq!(
            [left_return == &truth, right_return == &truth]
                .iter()
                .filter(|agrees| **agrees)
                .count(),
            1,
            "target {truth:?} left {left_return:?} right {right_return:?}"
        );

        // No admissible word separates them, which is why the family could not choose.
        for word in ["a", "b", "_", "aa", "ab", "a_", "ba", "bb", "b_", "_a", "_b", "__"] {
            assert_eq!(
                left.segment(word).unwrap(),
                right.segment(word).unwrap(),
                "{word:?} is inside the family and must not separate the retained codecs"
            );
        }
    }

    /// Raising the radius closes what the shorter family left open, one adjacency at a time. The
    /// separating word the instrument names is always one longer than the radius that failed.
    #[test]
    fn raising_the_radius_determines_what_the_shorter_family_left_open() {
        let mut named = Vec::new();
        for radius in 2..=3 {
            let target = soft_join();
            let recovery =
                recover(&target, &['a', 'b', '_'], radius, TEST_APERTURES).expect("the family is admissible");
            assert!(recovery.codec.is_none(), "radius {radius}");
            let Some(Obstruction::UndeterminedCodec {
                separating_input, ..
            }) = recovery.obstructions.first()
            else {
                panic!("radius {radius}: {:?}", recovery.obstructions);
            };
            named.push(separating_input.chars().count());
        }
        assert_eq!(named, vec![3, 4]);

        let target = soft_join();
        let recovery = recover(&target, &['a', 'b', '_'], 4, TEST_APERTURES).expect("the family is admissible");
        assert!(
            recovery.obstructions.is_empty(),
            "{:?}",
            recovery.obstructions
        );
        assert_eq!(recovery.retained_tables, 1);
        assert!(recovery.gauge_freedom.is_empty());
        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        assert_eq!(codec.emission_of('_'), Some(Emission::Drop));
        assert_eq!(codec.boundary_between('a', '_'), Some(Boundary::Join));
        assert_eq!(codec.boundary_between('_', 'a'), Some(Boundary::Join));
        assert_eq!(codec.boundary_between('_', '_'), Some(Boundary::Join));

        let conformance = conform(codec, &target, &["a_b_a", "__ab__", "a__b", "ab_ba_"]);
        assert!(
            conformance.is_exact(),
            "{:?}",
            conformance.disagreements
        );
    }

    /// The tokenizer's whitespace entries are underdetermined by the family and **observationally
    /// free**: many tables are retained, and no input of any length separates them. That is a gauge
    /// freedom, reported as one, and not confused with the obstruction above.
    #[test]
    fn a_retained_population_no_input_separates_is_reported_as_gauge_and_not_as_an_obstruction() {
        let target = tokenizer();
        let recovery = recover(&target, &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible");
        assert!(recovery.obstructions.is_empty());
        assert_eq!(recovery.inequivalent_codecs, 1);

        // Four emitted classes and one dropped one leave 25 - 16 = 9 entries open. A word `x y`
        // refutes exactly the tables that both enter and leave the space class by Join, so the
        // survivors are those with no Join into the space class or none out of it:
        // (2^4 + 2^4 - 1) = 31, doubled by the free space-to-space entry.
        assert_eq!(recovery.retained_tables, 62);
        assert_eq!(recovery.gauge_freedom.len(), 9);

        let codec = recovery.codec.as_ref().expect("the codec is recovered");
        let space = codec.class_of(' ').expect("the space class is recovered");
        for (left, right) in &recovery.gauge_freedom {
            assert!(
                *left == space || *right == space,
                "a determined entry was reported as gauge: {left:?} {right:?}"
            );
        }
    }

    /// A target that rewrites rather than segments is refused with the word and the return, not
    /// approximated by a segmenting structure.
    #[test]
    fn a_target_that_rewrites_rather_than_segments_is_refused_with_its_own_return() {
        let shouting = OpaqueSymbolCodec::new(|input: &str| {
            input
                .split(' ')
                .filter(|piece| !piece.is_empty())
                .map(str::to_uppercase)
                .collect()
        });
        let recovery = recover(&shouting, &['a', 'b', ' '], 3, TEST_APERTURES).expect("the family is admissible");
        assert!(recovery.codec.is_none());
        assert_eq!(
            recovery.obstructions,
            vec![Obstruction::NotASegmentation {
                input: "a".to_owned(),
                returned: vec!["A".to_owned()],
            }]
        );
        assert!(recovery.classes.is_empty(), "nothing was recovered to report");
    }

    /// A target whose dropping is a property of the position rather than the symbol cannot be
    /// expressed by any class assignment, and the recovery says so at the first word that shows it.
    #[test]
    fn a_target_that_drops_by_position_rather_than_by_symbol_is_refused() {
        let swallowing = OpaqueSymbolCodec::new(|input: &str| {
            let token: String = input
                .chars()
                .enumerate()
                .filter(|(position, _)| *position != 1)
                .map(|(_, symbol)| symbol)
                .collect();
            if token.is_empty() {
                Vec::new()
            } else {
                vec![token]
            }
        });
        let recovery = recover(&swallowing, &['a', 'b'], 3, TEST_APERTURES).expect("the family is admissible");
        assert!(recovery.codec.is_none());
        assert_eq!(
            recovery.obstructions,
            vec![Obstruction::EmissionDisagrees {
                input: "aa".to_owned(),
                returned: vec!["a".to_owned()],
                implied: "aa".to_owned(),
            }]
        );
    }

    /// A target outside the declared shape refutes **every** table and the refutation is exhibited.
    /// The instrument returns nothing rather than the nearest wrong structure.
    #[test]
    fn a_target_outside_the_declared_shape_refutes_every_table_and_exhibits_the_refutation() {
        let capped = OpaqueSymbolCodec::new(|input: &str| {
            // Agglutinates, but a token never exceeds three characters. No pair of adjacent classes
            // can express that, because the decision is about the token's own length.
            let mut tokens = Vec::new();
            let mut current = String::new();
            for symbol in input.chars() {
                if current.chars().count() == 3 {
                    tokens.push(std::mem::take(&mut current));
                }
                current.push(symbol);
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        });
        let recovery = recover(&capped, &['a', 'b'], 4, TEST_APERTURES).expect("the family is admissible");
        assert!(recovery.codec.is_none());
        assert_eq!(recovery.classes.len(), 1, "{:?}", recovery.classes);

        let Some(Obstruction::NoConformingTable {
            refuted_tables,
            witnesses,
        }) = recovery.obstructions.first()
        else {
            panic!("expected a refuted shape, got {:?}", recovery.obstructions);
        };
        assert_eq!(*refuted_tables, 1, "no entry is left open without a dropped class");
        assert_eq!(
            *witnesses,
            vec![Disagreement {
                input: "aaaa".to_owned(),
                target: vec!["aaa".to_owned(), "a".to_owned()],
                recovered: vec!["aaaa".to_owned()],
            }]
        );
    }

    /// Past the declared enumeration aperture the recovery refuses rather than sampling the gauge.
    #[test]
    fn a_family_leaving_more_entries_open_than_the_aperture_admits_is_refused() {
        let many = OpaqueSymbolCodec::new(|input: &str| {
            // Six emitted classes, each agglutinating only with itself, plus one dropped class.
            let mut tokens = Vec::new();
            let mut current = String::new();
            let mut previous: Option<char> = None;
            for symbol in input.chars() {
                let cut = previous != Some(symbol) || symbol == 'f';
                if cut && !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
                if symbol != ' ' {
                    current.push(symbol);
                }
                previous = Some(symbol);
            }
            if !current.is_empty() {
                tokens.push(current);
            }
            tokens
        });
        let recovery = recover(&many, &['a', 'b', 'c', 'd', 'e', 'f', ' '], 3, TEST_APERTURES)
            .expect("the family is admissible");
        assert!(recovery.codec.is_none());
        assert_eq!(recovery.classes.len(), 7, "{:?}", recovery.classes);
        assert_eq!(
            recovery.obstructions,
            vec![Obstruction::GaugeApertureExceeded {
                free_entries: 13,
                aperture: TEST_APERTURES.free_entries,
            }]
        );
    }

    /// The separating input returned is the **shortest** one and not merely a working one.
    ///
    /// Two codecs over one dropped and one emitted class, differing only in the entries that touch
    /// the dropped class. They agree on every word of length one and two — a search that returned
    /// any of those would be wrong — and the first word that separates them has length three. The
    /// test computes that minimum itself by exhausting words up to length four, so a search that
    /// returned a longer working word fails here.
    #[test]
    fn the_separating_input_returned_is_the_shortest_one_and_not_merely_a_working_one() {
        let build = |joins: Boundary| RecoveredCodec {
            schema: CODEC_SCHEMA.to_owned(),
            classes: vec![BTreeSet::from(['_']), BTreeSet::from(['a', 'b'])],
            emission: vec![Emission::Drop, Emission::Emit],
            boundary: vec![
                vec![joins, joins],
                vec![joins, Boundary::Join],
            ],
        };
        let joined = build(Boundary::Join);
        let cut = build(Boundary::Cut);

        let returned = joined
            .shortest_separating_input(&cut)
            .expect("the two codecs share their classes")
            .expect("some input separates them");
        assert_ne!(
            joined.segment(&returned).unwrap(),
            cut.segment(&returned).unwrap()
        );

        // The minimum, taken by exhaustion rather than by trusting the search under test.
        let alphabet = ['_', 'a', 'b'];
        let mut minimum = None;
        'search: for length in 1..=4usize {
            let mut ordinal = 0u64;
            let total = 3u64.pow(length as u32);
            while ordinal < total {
                let mut rest = ordinal;
                let mut word = vec!['_'; length];
                for position in (0..length).rev() {
                    word[position] = alphabet[(rest % 3) as usize];
                    rest /= 3;
                }
                let word: String = word.into_iter().collect();
                if joined.segment(&word).unwrap() != cut.segment(&word).unwrap() {
                    minimum = Some(length);
                    break 'search;
                }
                ordinal += 1;
            }
        }
        assert_eq!(minimum, Some(3));
        assert_eq!(returned.chars().count(), 3, "returned {returned:?}");

        // Longer separating words exist, so "shortest" is a claim the material can refute.
        assert_ne!(
            joined.segment("a_ab").unwrap(),
            cut.segment("a_ab").unwrap()
        );

        // Absence of a separating input is a proof of identity over all inputs, not a stopped
        // search: a codec against itself has none.
        assert_eq!(joined.shortest_separating_input(&joined).unwrap(), None);

        // A decoy route, so the claim is refutable by search *order* and not only by luck. Two
        // codecs over one emitted and three dropped classes: no word of length one or two separates
        // them, exactly one word of length three does, and an eight-symbol route separates them as
        // well. A depth-first frontier reaches the eight-symbol route first and returns it. Without
        // this fixture, exchanging the queue for a stack changes nothing that any check can see —
        // the two-class material above has one route and every traversal order walks it alike.
        let decoy = |rows: [[Boundary; 4]; 4]| RecoveredCodec {
            schema: CODEC_SCHEMA.to_owned(),
            classes: ['0', '1', '2', '3']
                .into_iter()
                .map(|symbol| BTreeSet::from([symbol]))
                .collect(),
            emission: vec![
                Emission::Drop,
                Emission::Emit,
                Emission::Drop,
                Emission::Drop,
            ],
            boundary: rows.iter().map(|row| row.to_vec()).collect(),
        };
        use Boundary::{Cut as C, Join as J};
        let near = decoy([[J, C, J, J], [J, C, J, J], [J, J, C, C], [J, C, C, J]]);
        let far = decoy([[C, C, J, J], [C, C, C, J], [J, J, C, J], [J, C, C, C]]);

        let separator = near
            .shortest_separating_input(&far)
            .expect("the two codecs share their classes")
            .expect("some input separates them");
        assert_eq!(separator, "121", "returned {separator:?}");
        assert_ne!(
            near.segment(&separator).unwrap(),
            far.segment(&separator).unwrap()
        );
        for length in 1..=2usize {
            for ordinal in 0..4u32.pow(length as u32) {
                let word: String = (0..length)
                    .rev()
                    .map(|position| {
                        char::from(b'0' + (ordinal >> (2 * position) & 3) as u8)
                    })
                    .collect();
                assert_eq!(
                    near.segment(&word).unwrap(),
                    far.segment(&word).unwrap(),
                    "{word:?} separates them, so three is not the minimum"
                );
            }
        }
        assert_ne!(
            near.segment("13023021").unwrap(),
            far.segment("13023021").unwrap(),
            "the long decoy route must really separate them"
        );
    }

    /// Codecs over different symbol classes carry no common ground to be separated on, and the
    /// comparison refuses rather than returning a verdict it cannot support.
    #[test]
    fn codecs_over_different_classes_refuse_comparison() {
        let left = RecoveredCodec {
            schema: CODEC_SCHEMA.to_owned(),
            classes: vec![BTreeSet::from(['a'])],
            emission: vec![Emission::Emit],
            boundary: vec![vec![Boundary::Join]],
        };
        let right = RecoveredCodec {
            schema: CODEC_SCHEMA.to_owned(),
            classes: vec![BTreeSet::from(['b'])],
            emission: vec![Emission::Emit],
            boundary: vec![vec![Boundary::Join]],
        };
        assert_eq!(
            left.shortest_separating_input(&right),
            Err(RecoveryError::IncomparableCodecs)
        );
    }

    /// A boundary that is not square over the classes is refused by **both** runners, with the same
    /// shape named.
    ///
    /// This was an index-out-of-bounds panic in both until 2026-08-08, found by comparing this
    /// organ's refusals against `codec_system::CodecSystem::joint`'s, which already returned a typed
    /// refusal on the identical value. The two must refuse the same populations or the cross-check
    /// between them is comparing organs that disagree about what is answerable.
    #[test]
    fn a_boundary_that_is_not_square_over_the_classes_is_refused_by_both_runners() {
        let well_formed = RecoveredCodec {
            schema: CODEC_SCHEMA.to_owned(),
            classes: vec![BTreeSet::from(['a']), BTreeSet::from(['b'])],
            emission: vec![Emission::Emit, Emission::Emit],
            boundary: vec![
                vec![Boundary::Join, Boundary::Cut],
                vec![Boundary::Cut, Boundary::Join],
            ],
        };
        let short_row = RecoveredCodec {
            boundary: vec![vec![Boundary::Join], vec![Boundary::Cut, Boundary::Join]],
            ..well_formed.clone()
        };
        let missing_row = RecoveredCodec {
            boundary: vec![vec![Boundary::Join, Boundary::Cut]],
            ..well_formed.clone()
        };

        // The well-formed codec answers both, so the refusals below are about the shape and not
        // about the material being unanswerable.
        assert_eq!(well_formed.segment("ab").unwrap(), vec!["a", "b"]);
        assert_eq!(
            well_formed.shortest_separating_input(&short_row),
            Err(RecoveryError::MalformedBoundary {
                rows: 2,
                columns: 1,
                classes: 2
            })
        );
        assert_eq!(
            short_row.segment("ab"),
            Err(RecoveryError::MalformedBoundary {
                rows: 2,
                columns: 1,
                classes: 2
            })
        );
        assert_eq!(
            missing_row.segment("ab"),
            Err(RecoveryError::MalformedBoundary {
                rows: 1,
                columns: 2,
                classes: 2
            })
        );
        assert_eq!(
            missing_row.shortest_separating_input(&well_formed),
            Err(RecoveryError::MalformedBoundary {
                rows: 1,
                columns: 2,
                classes: 2
            })
        );
        // The malformed side is found wherever it sits, not only in the receiver.
        assert_eq!(
            well_formed.shortest_separating_input(&missing_row),
            Err(RecoveryError::MalformedBoundary {
                rows: 1,
                columns: 2,
                classes: 2
            })
        );
        // Incomparability is decided first, so a malformed codec over different classes still says
        // the thing that is true of both of them.
        let elsewhere = RecoveredCodec {
            classes: vec![BTreeSet::from(['x'])],
            emission: vec![Emission::Emit],
            ..missing_row.clone()
        };
        assert_eq!(
            well_formed.shortest_separating_input(&elsewhere),
            Err(RecoveryError::IncomparableCodecs)
        );
    }

    /// **The apertures are the caller's, and the orbit shows it.** One target, one alphabet, one
    /// radius; two declarations; two different returns. If the level were still the organ's this
    /// test could not be written at all — which is what makes it evidence rather than a snapshot.
    #[test]
    fn one_material_returns_differently_under_two_declared_apertures() {
        // The family aperture. Eleven symbols at radius five is 177,155 words.
        let words = 11u64 + 121 + 1331 + 14641 + 161_051;
        let narrow = recover(
            &tokenizer(),
            &TOKENIZER_ALPHABET,
            5,
            RecoveryApertures::declared(words - 1, 12),
        );
        assert_eq!(
            narrow,
            Err(RecoveryError::FamilyExceedsAperture {
                words: BigUint::from(words),
                aperture: words - 1,
            }),
            "one short of the requirement refuses AND names the requirement"
        );
        let wide = recover(
            &tokenizer(),
            &TOKENIZER_ALPHABET,
            5,
            RecoveryApertures::declared(words, 12),
        )
        .expect("the same material at the width it asked for");
        assert_eq!(wide.work.declared_family_words, words);
        assert!(wide.is_recovered(), "obstructions: {:?}", wide.obstructions);

        // The free-entry aperture, on the material that has thirteen open entries.
        let many = || {
            OpaqueSymbolCodec::new(|input: &str| {
                let mut tokens = Vec::new();
                let mut current = String::new();
                let mut previous: Option<char> = None;
                for symbol in input.chars() {
                    let cut = previous != Some(symbol) || symbol == 'f';
                    if cut && !current.is_empty() {
                        tokens.push(std::mem::take(&mut current));
                    }
                    if symbol != ' ' {
                        current.push(symbol);
                    }
                    previous = Some(symbol);
                }
                if !current.is_empty() {
                    tokens.push(current);
                }
                tokens
            })
        };
        let alphabet = ['a', 'b', 'c', 'd', 'e', 'f', ' '];
        let refused = recover(&many(), &alphabet, 3, RecoveryApertures::declared(65_536, 12))
            .expect("the family is admissible");
        assert_eq!(
            refused.obstructions,
            vec![Obstruction::GaugeApertureExceeded {
                free_entries: 13,
                aperture: 12,
            }]
        );
        let admitted = recover(&many(), &alphabet, 3, RecoveryApertures::declared(65_536, 13))
            .expect("the family is admissible");
        assert!(
            !admitted
                .obstructions
                .iter()
                .any(|obstruction| matches!(obstruction, Obstruction::GaugeApertureExceeded { .. })),
            "one more declared entry admits the enumeration: {:?}",
            admitted.obstructions
        );
        assert_eq!(admitted.work.tables_examined, 1 << 13);
    }

    /// The family refusal names the width the material required **exactly**, past what the counter
    /// it used to be kept in could hold.
    ///
    /// Until 2026-08-09 this field was a `u64` filled by `checked_mul`, so any declaration whose
    /// family overflowed the counter reported `u64::MAX` — a saturated stand-in in the one field
    /// whose whole job is to say what was needed. Forty symbols at radius twenty needs
    /// `(40^21 - 40) / 39` words, which is about `1.1e32`.
    #[test]
    fn an_overflowing_family_names_its_exact_width_rather_than_a_saturated_stand_in() {
        let alphabet: Vec<char> = (0u8..40).map(|ordinal| (b'A' + ordinal) as char).collect();
        let mut expected = BigUint::from(0u32);
        let mut power = BigUint::from(1u32);
        for _ in 1..=20 {
            power *= 40u32;
            expected += &power;
        }
        assert!(
            expected > BigUint::from(u64::MAX),
            "the fixture must exceed the carrier the field used to be kept in"
        );
        let target = tokenizer();
        assert_eq!(
            recover(&target, &alphabet, 20, RecoveryApertures::declared(65_536, 12)),
            Err(RecoveryError::FamilyExceedsAperture {
                words: expected,
                aperture: 65_536,
            })
        );
        assert_eq!(target.calls(), 0, "an aperture refusal costs no testimony");
    }

    /// A free-entry aperture past the enumeration carrier is refused by a bound read off the
    /// carrier — `u64::BITS` — rather than by a number authored here.
    #[test]
    fn a_free_entry_aperture_past_the_enumeration_carrier_is_refused() {
        let target = tokenizer();
        assert_eq!(
            recover(
                &target,
                &TOKENIZER_ALPHABET,
                3,
                RecoveryApertures::declared(65_536, u64::BITS as u64)
            ),
            Err(RecoveryError::FreeEntryApertureUnrepresentable {
                aperture: u64::BITS as u64,
                carrier_bits: u64::BITS,
            })
        );
        assert_eq!(target.calls(), 0);
    }

    /// Declared apertures are refused, not approximated.
    #[test]
    fn the_declared_apertures_are_checked_before_any_testimony_is_taken() {
        let target = tokenizer();
        assert_eq!(
            recover(&target, &[], 3, TEST_APERTURES),
            Err(RecoveryError::EmptyAlphabet)
        );
        assert_eq!(
            recover(&target, &['a', 'b'], 1, TEST_APERTURES),
            Err(RecoveryError::RadiusBelowAperture { radius: 1 })
        );
        assert!(matches!(
            recover(&target, &TOKENIZER_ALPHABET, 6, TEST_APERTURES),
            Err(RecoveryError::FamilyExceedsAperture { .. })
        ));
        assert_eq!(target.calls(), 0, "an aperture refusal costs no testimony");
    }

    /// The instrument's own cost, stated rather than optimised away, and the invariant that ties a
    /// returned codec to an empty obstruction population.
    #[test]
    fn the_recovery_states_its_cost_and_never_returns_a_codec_beside_an_obstruction() {
        let target = tokenizer();
        let recovery = recover(&target, &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("the family is admissible");
        assert_eq!(recovery.work.declared_family_words, 11 + 121 + 1331);
        assert_eq!(recovery.work.target_calls, recovery.work.declared_family_words);
        assert_eq!(recovery.work.tables_examined, 1 << 9);
        assert!(recovery.work.contexts_examined > 0);
        assert!(recovery.work.table_word_checks > 0);
        assert_eq!(recovery.is_recovered(), recovery.obstructions.is_empty());

        let blind = soft_join();
        let obstructed = recover(&blind, &['a', 'b', '_'], 2, TEST_APERTURES).expect("the family is admissible");
        assert_eq!(obstructed.is_recovered(), obstructed.obstructions.is_empty());
    }

    /// The same declaration returns the same structure. Nothing here is ordered by a magnitude, a
    /// hash seed, or an iteration accident.
    #[test]
    fn the_recovery_is_deterministic() {
        let first = recover(&tokenizer(), &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("admissible");
        let second = recover(&tokenizer(), &TOKENIZER_ALPHABET, 3, TEST_APERTURES).expect("admissible");
        assert_eq!(first, second);
    }
}
