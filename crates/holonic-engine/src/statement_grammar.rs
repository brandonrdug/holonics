//! # SUPERSEDED 2026-08-17 — THIS IS AN AUTHORED GRAMMAR AND ITS REMOVAL IS LICENSED
//!
//! **Superseding plan:** `blueprint/THE_CODEC_IS_RECOVERED_AT_EVERY_SCALE_AND_THE_FACES_ARE_A_RETURN.md`.
//! **Ruling:** Brandon, 2026-08-17 — *"Authoritatively supersede whatever the 'parser' thing you just
//! identified is, it has been a contaminant that you passed off as something foundational during
//! experiments."*
//!
//! This module authors the categories *bracket pair*, *separator*, *word character* and
//! *punctuation*, and those categories decide what is a constituent and what is a relation **before
//! the material speaks**. That is an authored grammar, which `CLAUDE.md` §0g bars in the same
//! sentence as parsers, ASTs and keyword tables. That it names no Lean noun was the defence below
//! and it is irrelevant.
//!
//! **The general organ was already in the tree when this was written.** Measured 2026-08-17, charset
//! predicates per file: this module **24**, `lean_development.rs` **34**, against
//! `crates/holonic-engine/src/codec_recovery.rs` **0** outside its tests — and 0 in
//! `suffix_ecology.rs`, `receiver_exact_compression.rs` and `chain.rs`. `codec_recovery` already
//! carried `Symbol(u32)`, `SymbolAlphabet::declared`, `RecoveredCodec::segment` and
//! `shortest_separating_input` and knows no character class at all.
//!
//! **The control has been taken and it licenses removal.** `eros supersede` founded all 7,516 Mathlib
//! files by the incidence route and compared against this module's own deposited atlas:
//!
//! ```text
//!                             parser      incidence
//!     transport edges           6,154        694,079
//!     heads / constituents      5,828        218,264
//! ```
//!
//! Nothing this module carried is lost by superseding it. Under `CLAUDE.md` §13 rule 3 superseded
//! machinery **fails closed — removed, not deprecated**, with git as the recovery surface.
//!
//! **What removal still owes, named so it is not discovered late:** `statement_composition.rs` and
//! `lean_development.rs` consume this module, and two drivers do
//! (`the_statement_is_founded.rs`, `the_material_founds_the_identity_atlas.rs`). The measurement that
//! superseded this module also establishes there is **no drop-in replacement at the statement
//! scale** — the exposure ladder founds the character codec and nothing above it — so
//! `statement_composition` must be re-founded against incidence rather than rewired, and that is a
//! construction rather than a deletion.
//!
//! Everything below this banner is **provenance**. Do not extend it, and do not cite it as a
//! recovered grammar.
//!
//! A statement grammar **recovered from the deposit's own statement population**, with its aperture
//! returned beside it and everything it cannot decompose retained as residue.
//!
//! ## The receiver question this answers
//!
//! *What structure does a population of mathematical statements exhibit to a reader that was told
//! nothing about the language they are written in — and what, exactly, can such a reader not
//! decompose?*
//!
//! ## Why the grammar is recovered here and not read out of the export codec
//!
//! [`crate::derivation_atlas::read_derivation`] is deliberately shallow: it reads what a file
//! *declares*, not what it means, and its own documentation states that a deeper reading would be a
//! semantics claim the export codec's job is not to supply. That is the standing position and this
//! module does not move it. A statement arrives here exactly as that reader left it — a normalized
//! opaque string — and the structure below is **recovered from repeated substructure across the
//! population**, which is the operation [`crate::codec_recovery`] already performs on symbols and
//! [`crate::derivation_codec_intake`] performs on identifier morphology, carried onto a third
//! surface.
//!
//! Nothing here knows the word *binder*, *type*, *application* or *Lean*. Those names appear in this
//! documentation because a reader needs them; the code founds each part from a property of the
//! population that is checkable and that fails on material which does not exhibit it.
//!
//! ## The four slots `CLAUDE.md` §4 asks for
//!
//! ```text
//!   source geometry    the deposit's statement population, as opaque normalized strings
//!   receiver map       the delimiter reading: which characters bracket, which separates
//!   transport          nesting depth through a statement, and offset succession within a region
//!   returned residual  every span no recovered part covers, retained by name with the token that
//!                      refused it -- exactly as `FoundedMorphology::cover` retains its residue
//! ```
//!
//! ## What is recovered, and the property that founds each part
//!
//! ```text
//!   the bracket pair    an ordered pair of punctuation characters (o, c) whose running depth over
//!                       EVERY statement never goes negative and ends at zero, and which opens at
//!                       least once. Recovered only when EXACTLY ONE pair qualifies.
//!
//!   the separator       a punctuation character outside the bracket pair occurring EXACTLY ONCE at
//!                       depth zero in EVERY statement. Recovered only when exactly one qualifies.
//!
//!   the split           each statement is the region before that occurrence and the region after
//!                       it. Two regions, named by position and by nothing else.
//!
//!   the binder groups   the leading region's depth-zero content, which on a qualifying population
//!                       is bracket groups and whitespace and nothing else. Inside a group the
//!                       separator occurs once at the group's own depth, splitting it into a run of
//!                       word tokens and a carried token.
//!
//!   the applied body    a trailing region carrying word tokens only reads as a first token and the
//!                       tokens after it. A trailing region carrying a punctuation token at its own
//!                       depth is NOT decomposed: it is retained whole as residue.
//!
//!   the run lengths     the lengths the population actually witnesses. Two distinct nonempty
//!                       lengths found a NONEMPTY SEQUENCE; one length founds only that length; a
//!                       length never witnessed -- notably zero -- is unfounded and says so.
//! ```
//!
//! ## The aperture is part of the return, never a footnote
//!
//! `CLAUDE.md` §8: *"An organ used past its declared aperture is a defect even when it appears to
//! return... Before borrowing a carrier, read the aperture it declares."* [`GrammarAperture`] is
//! therefore a population on the recovered grammar itself, each member carrying the material that
//! witnesses it. A caller composing against this grammar is expected to read it, and
//! [`crate::statement_composition`] refuses candidates that fall outside it **by name** rather than
//! silently declining to generate them.
//!
//! The two apertures that bind hardest on the present deposit, both recovered rather than declared:
//!
//! - a trailing region carrying a punctuation token is undecomposed, so nothing can be composed into
//!   it;
//! - **no argument position in the population ever carried a bracket group**, so an application
//!   nested inside an argument is a shape the population does not witness. That is the second half
//!   of what
//!   `research/records/2026-08-08_THE_INSTANCE_FOUNDS_ROUTES_AND_NEVER_FOUNDS_STATEMENTS.md` §6 was
//!   missing and did not name: knowing that a head is applied to an argument is necessary and is
//!   recovered here, and it is **not sufficient**, because nesting needs a witnessed argument shape
//!   the population does not supply.
//!
//! ## What this module does not own
//!
//! It does not own a reading of a file — it is handed statements. It does not own the founded
//! morphology, the licence rule, or any composition; those are
//! [`crate::statement_composition`]'s. It contains no scalar that selects, ranks, gates or discards:
//! the run lengths are populations, the arities are populations, and every refusal is a named
//! member of a retained population rather than a verdict on a magnitude.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

/// A half-open span of one statement, in bytes of the statement's own text.
///
/// Statements are refused unless ASCII ([`StatementGrammarRefusal::StatementIsNotAscii`]), so a byte
/// offset always names a character boundary and a span always names whole characters.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Span {
    pub at: usize,
    pub through: usize,
}

impl Span {
    pub const fn new(at: usize, through: usize) -> Self {
        Self { at, through }
    }

    pub fn text<'a>(&self, statement: &'a str) -> &'a str {
        &statement[self.at..self.through]
    }
}

/// What a recovered slot is, named by the position the population put it in.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SlotSpecies {
    /// A word token in the run before a bracket group's own separator.
    BinderName,
    /// The token after a bracket group's own separator.
    BinderType,
    /// The first token of a decomposable trailing region.
    BodyHead,
    /// A token after the first, in a decomposable trailing region.
    BodyArgument,
}

impl SlotSpecies {
    pub const fn name(self) -> &'static str {
        match self {
            Self::BinderName => "binder-name",
            Self::BinderType => "binder-type",
            Self::BodyHead => "body-head",
            Self::BodyArgument => "body-argument",
        }
    }

    /// The short tag this species takes in [`RecoveredStatementGrammar::render`] and in a composed
    /// declaration name.
    pub const fn tag(self) -> &'static str {
        match self {
            Self::BinderName => "name",
            Self::BinderType => "type",
            Self::BodyHead => "head",
            Self::BodyArgument => "arg",
        }
    }
}

/// One recovered position in a statement, with the identifier standing in it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Slot {
    pub species: SlotSpecies,
    pub span: Span,
    /// The token the population put here. Never interpreted, only carried.
    pub occupant: String,
}

/// One bracket group, read as a run of word tokens and a carried token.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct BinderGroup {
    pub span: Span,
    /// The tokens before the group's own separator. Nonempty on every group the population founds.
    pub names: Vec<Slot>,
    /// The token after it, when the region after the separator is a single word token. `None` when
    /// it is not, and the group is then retained as residue instead.
    pub carried: Option<Slot>,
    /// **Which bracket species opened this group**, when the population founds more than one.
    ///
    /// Recovered, never declared: the material exhibits several balanced pairs and this group was
    /// opened by one of them. On a population founding a single pair every group carries that pair,
    /// and the field says so rather than being left empty. `None` only where no family was founded
    /// at all.
    #[serde(default)]
    pub species: Option<(char, char)>,
}

impl BinderGroup {
    /// The group's own text, whole, including its brackets.
    pub fn text<'a>(&self, statement: &'a str) -> &'a str {
        self.span.text(statement)
    }
}

/// How the trailing region read.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum BodyReading {
    /// Word tokens only: the first, and the ones after it.
    Applied { head: Slot, arguments: Vec<Slot> },
    /// A punctuation token stood at the region's own depth. **Not decomposed.** The span is retained
    /// whole, and the token that refused it is named.
    Undecomposed { span: Span, refused_by: String },
}

impl BodyReading {
    pub const fn is_applied(&self) -> bool {
        matches!(self, Self::Applied { .. })
    }
}

/// One span the recovery could not place, retained by name with what refused it.
///
/// The same carrier `FoundedCover::residue` is: material the reading cannot found, kept as the
/// obstruction rather than dropped.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct GrammarResidue {
    pub span: Span,
    pub text: String,
    pub refused_by: String,
}

/// One statement, as the recovery reads it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct StatementReading {
    pub statement: String,
    /// The depth-zero occurrence of the recovered separator that split it, when one was recovered.
    pub split_at: Option<usize>,
    pub binders: Vec<BinderGroup>,
    pub body: Option<BodyReading>,
    pub residue: Vec<GrammarResidue>,
}

impl StatementReading {
    /// Every recovered slot, in offset order. The positions a composition may substitute into.
    pub fn slots(&self) -> Vec<Slot> {
        let mut slots = Vec::new();
        for group in &self.binders {
            slots.extend(group.names.iter().cloned());
            if let Some(carried) = &group.carried {
                slots.push(carried.clone());
            }
        }
        if let Some(BodyReading::Applied { head, arguments }) = &self.body {
            slots.push(head.clone());
            slots.extend(arguments.iter().cloned());
        }
        slots.sort_by_key(|slot| (slot.span.at, slot.span.through));
        slots
    }

    /// The statement with one span replaced, whitespace renormalized to the form
    /// `read_derivation` returns.
    pub fn substituted(&self, span: Span, replacement: &str) -> String {
        let mut composed = String::with_capacity(self.statement.len() + replacement.len());
        composed.push_str(&self.statement[..span.at]);
        composed.push_str(replacement);
        composed.push_str(&self.statement[span.through..]);
        normalize(&composed)
    }

    /// The statement with one bracket group removed, whitespace renormalized.
    pub fn without_group(&self, group: &BinderGroup) -> String {
        let mut composed = String::with_capacity(self.statement.len());
        composed.push_str(&self.statement[..group.span.at]);
        composed.push_str(&self.statement[group.span.through..]);
        normalize(&composed)
    }

    /// The statement with one further bracket group appended to the leading region.
    pub fn with_group(&self, group_text: &str) -> Option<String> {
        let split = self.split_at?;
        let mut composed = String::with_capacity(self.statement.len() + group_text.len() + 1);
        composed.push_str(&self.statement[..split]);
        composed.push(' ');
        composed.push_str(group_text);
        composed.push(' ');
        composed.push_str(&self.statement[split..]);
        Some(normalize(&composed))
    }
}

/// The whitespace form every statement in this body is carried in: single spaces, no ends.
///
/// It is `read_derivation`'s own normalization, restated here because a composed statement must be
/// in the same form as a deposited one or the two could never be compared.
pub fn normalize(statement: &str) -> String {
    statement
        .split_whitespace()
        .collect::<Vec<&str>>()
        .join(" ")
}

/// What the recovered grammar cannot do, with the material that witnesses each bound.
///
/// Every member is a **statement about the population**, not a preference. A caller reads this
/// before composing; [`crate::statement_composition`] refuses by naming a member of it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum GrammarAperture {
    /// More than one ordered punctuation pair balances over the whole population, so which one
    /// brackets is undecided and no depth is founded.
    BracketPairIsNotUnique { admitted: Vec<String> },
    /// No ordered punctuation pair balances. The population exhibits no nesting.
    NoBracketPairBalances,
    /// The material groups in **more than one bracket species** at once, and the depth is the
    /// nesting they generate together. Not a failure: it is the shape mathematics is written in, and
    /// each group carries which species opened it.
    BracketFamilyIsPlural {
        admitted: Vec<String>,
        /// Pairs dropped because a character was already spent as another species' character.
        discarded: Vec<String>,
    },
    /// The balanced pairs do not nest properly against each other over some statement — a closer
    /// arrived for an opener that was not the innermost one — so they generate no depth and none is
    /// used.
    BracketFamilyDoesNotNest { admitted: Vec<String> },
    /// More than one character occurs at depth zero in every statement.
    SeparatorIsNotUnique { admitted: Vec<String> },
    /// No character does, so the population founds no split.
    NoSeparatorOccursAtDepthZeroInEveryStatement,
    /// Several characters stood at depth zero in every statement and exactly one of them also
    /// recurred **inside** the bracket groups, so that one is the separator. Carried because the
    /// recovery used a second property and a return must say which properties founded it.
    SeparatorFoundedByRecurrenceInsideGroups {
        admitted: Vec<String>,
        recurring: String,
    },
    /// The separator occurs **more than once** at depth zero somewhere in the population, so a
    /// statement admits several candidate splits. The counts witnessed are carried, along with the
    /// orientation this recovery ran under. On its own this is not a loss of determinacy — the
    /// leading region's founding property usually decides — and where it does not,
    /// [`Self::SeveralOccurrencesFoundTheLeadingRegion`] fires as well.
    SeparatorOccursPlurallyAtDepthZero {
        witnessed: BTreeSet<usize>,
        orientation: SeparatorOrientation,
    },
    /// **More than one candidate split founds a leading region in one statement**, so the material
    /// does not decide and the declared orientation did. This is the only place an orientation
    /// changes a reading, and it is named per statement so a run can exhibit them rather than report
    /// a rate.
    SeveralOccurrencesFoundTheLeadingRegion {
        statement: String,
        occurrences: usize,
        orientation: SeparatorOrientation,
    },
    /// A trailing region carried a punctuation token at its own depth and was retained whole.
    BodyCarriesPunctuation { statement: String, token: String },
    /// A bracket group carried no separator at its own depth and was retained whole.
    BinderGroupCarriesNoSeparator { statement: String, group: String },
    /// The region after a bracket group's separator was not a single word token.
    BinderTypeIsNotOneToken { statement: String, group: String },
    /// The leading region carried a token outside any bracket group.
    LeadingRegionCarriesABareToken { statement: String, token: String },
    /// **No argument position anywhere in the population carried a bracket group**, so an
    /// application nested in an argument is a shape the population does not witness.
    ArgumentPositionNeverCarriedAnApplication { arguments: BTreeSet<String> },
    /// One token stood in first position of a decomposable region with two different token counts
    /// after it, so its arity is not a property of the population.
    HeadArityConflicts {
        head: String,
        arities: BTreeSet<usize>,
    },
    /// The population never witnessed a leading region with no bracket group in it, so the empty
    /// list is unfounded and a composition may not produce one.
    EmptyBinderListNeverWitnessed { witnessed: BTreeSet<usize> },
    /// The identifier never stood in first position of a decomposable region, so the population
    /// founds no arity for it. Returned on demand by
    /// [`RecoveredStatementGrammar::unfounded_head_arity`].
    HeadArityIsUnfounded { identifier: String },
}

impl std::fmt::Display for GrammarAperture {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BracketPairIsNotUnique { admitted } => write!(
                formatter,
                "{} ordered punctuation pairs balance over the population ({}), so which pair \
                 brackets is undecided",
                admitted.len(),
                admitted.join(", ")
            ),
            Self::NoBracketPairBalances => {
                write!(
                    formatter,
                    "no ordered punctuation pair balances; the population exhibits no nesting"
                )
            }
            Self::BracketFamilyIsPlural {
                admitted,
                discarded,
            } => write!(
                formatter,
                "the material groups in {} species at once ({}), and the depth is the nesting they \
                 generate together; {} further pair(s) were dropped for sharing a character ({})",
                admitted.len(),
                admitted.join(", "),
                discarded.len(),
                discarded.join(", ")
            ),
            Self::BracketFamilyDoesNotNest { admitted } => write!(
                formatter,
                "the balanced pairs {} do not nest against each other over every statement, so they \
                 generate no depth",
                admitted.join(", ")
            ),
            Self::SeparatorIsNotUnique { admitted } => write!(
                formatter,
                "{admitted:?} each occur at depth zero in every statement, so the split is undecided"
            ),
            Self::NoSeparatorOccursAtDepthZeroInEveryStatement => write!(
                formatter,
                "no character occurs at depth zero in every statement, so no split is founded"
            ),
            Self::SeparatorFoundedByRecurrenceInsideGroups {
                admitted,
                recurring,
            } => write!(
                formatter,
                "{admitted:?} each stand at depth zero in every statement; {recurring:?} is the one \
                 that recurs inside the groups, so the split is founded on it"
            ),
            Self::SeparatorOccursPlurallyAtDepthZero {
                witnessed,
                orientation,
            } => write!(
                formatter,
                "the separator occurs at depth zero {witnessed:?} times across the population, so \
                 some statement admits several candidate splits; this reading took the \
                 {orientation} of those founding a leading region"
            ),
            Self::SeveralOccurrencesFoundTheLeadingRegion {
                statement,
                occurrences,
                orientation,
            } => write!(
                formatter,
                "{occurrences} candidate splits of {statement:?} each found a leading region, so \
                 the material did not decide and the {orientation} orientation did"
            ),
            Self::BodyCarriesPunctuation { statement, token } => write!(
                formatter,
                "the trailing region of {statement:?} carries the punctuation token {token:?} at its \
                 own depth and is retained whole"
            ),
            Self::BinderGroupCarriesNoSeparator { statement, group } => write!(
                formatter,
                "the group {group:?} of {statement:?} carries no separator at its own depth"
            ),
            Self::BinderTypeIsNotOneToken { statement, group } => write!(
                formatter,
                "the region after the separator of {group:?} in {statement:?} is not a single word token"
            ),
            Self::LeadingRegionCarriesABareToken { statement, token } => write!(
                formatter,
                "the leading region of {statement:?} carries the token {token:?} outside any group"
            ),
            Self::ArgumentPositionNeverCarriedAnApplication { arguments } => write!(
                formatter,
                "no argument position in the population carried a bracket group; every argument \
                 witnessed is a bare token ({})",
                arguments
                    .iter()
                    .map(String::as_str)
                    .collect::<Vec<&str>>()
                    .join(", ")
            ),
            Self::HeadArityConflicts { head, arities } => write!(
                formatter,
                "{head} stands in first position with {arities:?} tokens after it, so its arity is \
                 not a property of the population"
            ),
            Self::EmptyBinderListNeverWitnessed { witnessed } => write!(
                formatter,
                "the population witnesses leading regions of {witnessed:?} groups and never of none, \
                 so an empty list is unfounded"
            ),
            Self::HeadArityIsUnfounded { identifier } => write!(
                formatter,
                "{identifier} never stands in first position of a decomposable region, so the \
                 population founds no arity for it"
            ),
        }
    }
}

/// Which depth-zero occurrence of the recovered separator splits a statement.
///
/// ## Why this is an axis and not a setting
///
/// A separator that occurs once admits one split and the question does not arise. A separator that
/// occurs several times admits several, and choosing among them is choosing a **direction** through
/// the statement — which is the same object `derivation_atlas::ReachOrientation` names on a
/// derivation complex, arriving here on token material.
///
/// The two are a **symmetry** on any population whose separator occurs exactly once at depth zero,
/// which is asserted in this module's tests rather than assumed. Where the material exhibits plural
/// occurrences they differ, and the difference is exactly the antecedent/consequent split: the
/// leading region carries what a statement *supposes* and the trailing region carries what it
/// *concludes*, so
///
/// ```text
///   First   the leading region is everything before the FIRST separator
///           -> on `f {n : ℕ} (s : Simplex ℝ P n) : height s = 1` the leading region is `f {n`
///   Last    the leading region is everything before the LAST separator
///           -> the same statement gives `f {n : ℕ} (s : Simplex ℝ P n)` and `height s = 1`
/// ```
///
/// Neither is called correct here. `Last` is the default of [`recover`] because it is the one under
/// which the leading region's depth-zero content is bracket groups and whitespace — the property the
/// binder-group reading is founded on — and a reading that cannot found its groups returns residue
/// rather than structure. That is a statement about which orientation the *material* supports, and
/// the falsifier is a population where `First` founds groups and `Last` does not.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SeparatorOrientation {
    /// Split at the first depth-zero occurrence.
    First,
    /// Split at the last depth-zero occurrence.
    Last,
}

impl std::fmt::Display for SeparatorOrientation {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::First => write!(formatter, "first"),
            Self::Last => write!(formatter, "last"),
        }
    }
}

/// The orientation a grammar serialized before orientations existed was recovered under.
///
/// It is not a guess. The only founding rule available then was *exactly once at depth zero in every
/// statement*, under which the first and the last occurrence are the same occurrence, so both
/// orientations name the identical split and either answer is exact.
fn orientation_of_the_writing() -> SeparatorOrientation {
    SeparatorOrientation::Last
}

/// Why a recovery was refused outright.
///
/// **`StatementIsNotAscii` was excised 2026-08-16.** It refused any statement carrying a character
/// outside ASCII, on the argument that a byte offset into a multi-byte character names no token
/// boundary. The argument was sound about the *implementation* and never about the material: the
/// walk now steps by character through [`char_at`] and [`step`], and [`depths`] carries one entry
/// per byte, so every offset this module produces is a character boundary by construction. The
/// refusal was the charset gate this module's own subject — mathematical notation — is written
/// outside of.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementGrammarRefusal {
    /// A grammar recovered from nothing would carry no relation at all. `CLAUDE.md` §8: a law that
    /// returns zero proves nothing about itself, so this is refused by type rather than returned
    /// empty for a caller to notice.
    PopulationIsEmpty,
}

impl std::fmt::Display for StatementGrammarRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PopulationIsEmpty => write!(
                formatter,
                "no statement was presented, so nothing could be recovered and nothing is returned"
            ),
        }
    }
}

impl std::error::Error for StatementGrammarRefusal {}

/// A grammar recovered from one statement population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecoveredStatementGrammar {
    population: Vec<String>,
    punctuation: BTreeSet<char>,
    bracket: Option<(char, char)>,
    #[serde(default)]
    bracket_family: Vec<(char, char)>,
    balanced_pairs: Vec<(char, char)>,
    separator: Option<String>,
    separator_candidates: Vec<String>,
    #[serde(default)]
    separator_occurrences: BTreeSet<usize>,
    #[serde(default = "orientation_of_the_writing")]
    orientation: SeparatorOrientation,
    readings: Vec<StatementReading>,
    heads: BTreeMap<String, BTreeSet<usize>>,
    binder_group_lengths: BTreeSet<usize>,
    binder_name_lengths: BTreeSet<usize>,
    aperture: Vec<GrammarAperture>,
}

impl RecoveredStatementGrammar {
    /// The statements the grammar was recovered from, in canonical order.
    pub fn population(&self) -> &[String] {
        &self.population
    }

    /// Every non-word, non-space character the population exhibits.
    pub const fn punctuation(&self) -> &BTreeSet<char> {
        &self.punctuation
    }

    /// The recovered bracket pair, when exactly one balances.
    pub const fn bracket(&self) -> Option<(char, char)> {
        self.bracket
    }

    /// Every ordered pair that balanced. The recovery is only decided when this holds exactly one.
    pub fn balanced_pairs(&self) -> &[(char, char)] {
        &self.balanced_pairs
    }

    /// The recovered separator, when exactly one qualifies.
    pub fn separator(&self) -> Option<char> {
        self.separator.as_ref().and_then(|run| run.chars().next())
    }

    /// The separator as the material writes it, which may be more than one character.
    pub fn separator_run(&self) -> Option<&str> {
        self.separator.as_deref()
    }

    /// Every character that occurred exactly once at depth zero in every statement.
    pub fn separator_candidates(&self) -> &[String] {
        &self.separator_candidates
    }

    /// **The bracket species the material groups in**, as one family generating one depth.
    ///
    /// A single-pair population returns a family of one, so this is never smaller than
    /// [`Self::bracket`] and is the accessor to read when the material may group in several ways —
    /// which mathematics does.
    pub fn bracket_family(&self) -> &[(char, char)] {
        &self.bracket_family
    }

    /// The depth-zero occurrence counts the population witnesses for the recovered separator.
    ///
    /// `{1}` says the orientation is a symmetry on this material and cannot move any reading.
    /// Anything else says the direction is load-bearing, and is the material saying so rather than a
    /// caller declaring it.
    pub fn separator_occurrences(&self) -> &BTreeSet<usize> {
        &self.separator_occurrences
    }

    /// Which depth-zero occurrence this recovery split at.
    pub fn orientation(&self) -> SeparatorOrientation {
        self.orientation
    }

    /// Whether the orientation could have changed any reading of this population.
    ///
    /// False exactly when every statement exhibits one depth-zero separator — in which case the two
    /// orientations are the same map and comparing them is a tautology, which a run reporting an
    /// orbit must say rather than present as agreement.
    pub fn orientation_is_load_bearing(&self) -> bool {
        self.separator_occurrences.iter().any(|count| *count > 1)
    }

    /// One reading per statement, in population order.
    pub fn readings(&self) -> &[StatementReading] {
        &self.readings
    }

    pub fn reading(&self, statement: &str) -> Option<&StatementReading> {
        self.readings
            .iter()
            .find(|reading| reading.statement == statement)
    }

    /// Every token that stood in first position of a decomposable region, with the token counts
    /// witnessed after it. A population, never a single number.
    pub const fn heads(&self) -> &BTreeMap<String, BTreeSet<usize>> {
        &self.heads
    }

    /// The arity the population founds for one token, or `None` when it founds none or more than
    /// one.
    pub fn founded_arity(&self, head: &str) -> Option<usize> {
        match self.heads.get(head) {
            Some(arities) if arities.len() == 1 => arities.iter().next().copied(),
            _ => None,
        }
    }

    /// `HeadArityIsUnfounded` for an identifier the population never put in first position.
    pub fn unfounded_head_arity(&self, identifier: &str) -> Option<GrammarAperture> {
        if self.heads.contains_key(identifier) {
            None
        } else {
            Some(GrammarAperture::HeadArityIsUnfounded {
                identifier: identifier.to_owned(),
            })
        }
    }

    /// The numbers of bracket groups the leading regions actually exhibit.
    ///
    /// **Two distinct nonempty lengths found a nonempty sequence.** One length founds only that
    /// length, and [`Self::sequence_is_founded`] says which happened.
    pub const fn binder_group_lengths(&self) -> &BTreeSet<usize> {
        &self.binder_group_lengths
    }

    /// The same for the token runs inside a group.
    pub const fn binder_name_lengths(&self) -> &BTreeSet<usize> {
        &self.binder_name_lengths
    }

    /// The population witnessed the leading region at more than one length, so its length is not a
    /// property of the material and a composition may change it.
    pub fn sequence_is_founded(&self) -> bool {
        self.binder_group_lengths.len() > 1
    }

    /// A leading region of this many groups is one the population witnesses, or one the founded
    /// sequence reading covers. Zero is never covered unless the population witnessed it.
    pub fn binder_length_is_founded(&self, length: usize) -> bool {
        if self.binder_group_lengths.contains(&length) {
            return true;
        }
        length > 0 && self.sequence_is_founded()
    }

    /// Every bracket group text the population exhibits anywhere, without repetition.
    pub fn witnessed_groups(&self) -> BTreeSet<String> {
        self.readings
            .iter()
            .flat_map(|reading| {
                reading
                    .binders
                    .iter()
                    .map(|group| group.text(&reading.statement).to_owned())
            })
            .collect()
    }

    /// Every occupant the population ever put in an argument position.
    pub fn witnessed_arguments(&self) -> BTreeSet<String> {
        self.readings
            .iter()
            .filter_map(|reading| match &reading.body {
                Some(BodyReading::Applied { arguments, .. }) => Some(arguments.clone()),
                _ => None,
            })
            .flatten()
            .map(|slot| slot.occupant)
            .collect()
    }

    /// **What this grammar cannot do**, with the material that witnesses each bound.
    pub fn aperture(&self) -> &[GrammarAperture] {
        &self.aperture
    }

    /// One statement written out as the recovery reads it: recovered parts in place, residue
    /// bracketed, joined by `|`.
    ///
    /// The rendering `FoundedCover::render` performs on a word, on a statement.
    pub fn render(&self, statement: &str) -> Option<String> {
        let reading = self.reading(statement)?;
        let mut parts: Vec<(usize, usize, String)> = Vec::new();
        let slots = reading.slots();
        // A delimiter inside a recovered part is that part's own material and is not written twice.
        let covered = |at: usize| -> bool {
            slots
                .iter()
                .any(|slot| slot.span.at <= at && at < slot.span.through)
                || reading
                    .residue
                    .iter()
                    .any(|residue| residue.span.at <= at && at < residue.span.through)
        };
        for (at, symbol) in reading.statement.char_indices() {
            let structural = self
                .bracket
                .is_some_and(|(open, close)| symbol == open || symbol == close)
                || self
                    .separator
                    .as_deref()
                    .is_some_and(|run| run.starts_with(symbol) && run.chars().count() == 1);
            if structural && !covered(at) {
                parts.push((at, at + 1, symbol.to_string()));
            }
        }
        for slot in &slots {
            parts.push((
                slot.span.at,
                slot.span.through,
                format!("{}:{}", slot.species.tag(), slot.occupant),
            ));
        }
        for residue in &reading.residue {
            parts.push((
                residue.span.at,
                residue.span.through,
                format!("[{}]", residue.text),
            ));
        }
        parts.sort_by_key(|(at, through, _)| (*at, *through));
        Some(
            parts
                .into_iter()
                .map(|(_, _, rendered)| rendered)
                .collect::<Vec<String>>()
                .join("|"),
        )
    }
}

// -------------------------------------------------------------------------------------------------
// The recovery
// -------------------------------------------------------------------------------------------------

/// A character a token may be made of. The reading's one orthographic rule, stated as a bound
/// exactly as `expose` and `read_derivation` state theirs.
///
/// **The ASCII restriction was excised 2026-08-16 and the rule is otherwise unchanged.** It was an
/// authored charset on material whose subject is notation: measured that day over 18,666
/// `theorem`-opening lines in `Mathlib/Geometry` and `Mathlib/Algebra`, 14,150 carry a character
/// outside ASCII and 4,516 do not, so the restriction refused **75.8%** of the material and what it
/// refused was precisely `ℝ ℕ ∠ ≅ ¬ ₁ ᵥ ⟪⟫`.
///
/// The replacement is weaker rather than wider: `is_alphanumeric` **coincides** with
/// `is_ascii_alphanumeric` on every ASCII character, so a population that would have been admitted
/// before is read bit-identically now. What it admits additionally is what the material's own script
/// treats as a letter or a digit — `ℝ` and `ℕ` are uppercase letters, `₁` is a digit, so `h₁` is one
/// token — while `∠`, `≠`, `⟪`, `↔` and `∈` remain punctuation because they are symbols. The grain
/// is thereby read off the material's own character properties rather than off a byte range this
/// module chose.
fn is_word_character(symbol: char) -> bool {
    symbol.is_alphanumeric() || symbol == '_' || symbol == '.'
}

/// The tokens of one region, each with its span, in reading order. A token is a maximal run of word
/// characters, or a single punctuation character.
fn tokens(statement: &str, span: Span) -> Vec<(Span, String)> {
    let mut found = Vec::new();
    let mut at = span.at;
    while at < span.through {
        let symbol = char_at(statement, at);
        if symbol.is_whitespace() {
            at = step(statement, at);
            continue;
        }
        if is_word_character(symbol) {
            let start = at;
            while at < span.through && is_word_character(char_at(statement, at)) {
                at = step(statement, at);
            }
            found.push((Span::new(start, at), statement[start..at].to_owned()));
            continue;
        }
        let next = step(statement, at);
        found.push((Span::new(at, next), symbol.to_string()));
        at = next;
    }
    found
}

/// The tokens of one region **at that region's own nesting depth**, where a whole bracket group
/// counts as one token.
///
/// This is what makes the trailing region's reading depend on the recovered bracket pair rather than
/// on the characters alone: a region carrying `exactCarrier (exactCarrier P)` exhibits two tokens,
/// the second of which is a group, while a region carrying `a = b` exhibits three, one of which is
/// punctuation the recovery has no place for.
fn region_tokens(
    statement: &str,
    span: Span,
    bracket: Option<(char, char)>,
    depth: &[usize],
) -> Vec<(Span, String)> {
    let Some((open, close)) = bracket else {
        return tokens(statement, span);
    };
    let own_depth = depth.get(span.at).copied().unwrap_or(0);
    let mut found = Vec::new();
    let mut at = span.at;
    while at < span.through {
        let symbol = char_at(statement, at);
        if symbol.is_whitespace() {
            at = step(statement, at);
            continue;
        }
        if symbol == open && depth[at] == own_depth {
            let mut through = step(statement, at);
            while through < span.through
                && !(char_at(statement, through) == close && depth[through] == own_depth + 1)
            {
                through = step(statement, through);
            }
            let closing = if through < span.through {
                step(statement, through)
            } else {
                span.through
            };
            let group = Span::new(at, closing.min(span.through));
            found.push((group, group.text(statement).to_owned()));
            at = group.through;
            continue;
        }
        if is_word_character(symbol) {
            let start = at;
            while at < span.through && is_word_character(char_at(statement, at)) {
                at = step(statement, at);
            }
            found.push((Span::new(start, at), statement[start..at].to_owned()));
            continue;
        }
        let next = step(statement, at);
        found.push((Span::new(at, next), symbol.to_string()));
        at = next;
    }
    found
}

/// A token the trailing region may carry: a word run, or a whole bracket group.
fn token_is_placeable(text: &str, bracket: Option<(char, char)>) -> bool {
    if text.chars().all(is_word_character) {
        return true;
    }
    match bracket {
        Some((open, close)) => text.starts_with(open) && text.ends_with(close) && text.len() >= 2,
        None => false,
    }
}

/// The depth **before** each byte of a statement, under a candidate bracket pair. `None` when the
/// pair does not balance over this statement.
///
/// **The profile is indexed by BYTE, not by character**, because every caller indexes it with an
/// offset taken from [`str::char_indices`] or from a [`Span`], and both of those are byte offsets. A
/// multi-byte character therefore occupies as many entries as it has bytes, all carrying the depth
/// that holds before it. Pushing one entry per character was correct while the module refused any
/// statement that was not ASCII and became a defect the moment notation was admitted: `ℝ` is three
/// bytes, so a per-character profile drifts two positions behind the offsets used to read it.
fn depths(statement: &str, open: char, close: char) -> Option<Vec<usize>> {
    depths_over(statement, &[(open, close)])
}

/// The depth **before** each byte of a statement, under a whole **family** of bracket pairs.
///
/// ## Why the family is the object and a single pair is not
///
/// Recovered 2026-08-16 by running the recovery on mathematics. A population of real statements
/// balances several ordered pairs at once — `()`, `{}`, `[]` and `⟨⟩` all balance over
/// `Mathlib/Geometry`, so the *unique pair* rule founds nothing, the depth profile is flat
/// everywhere, and with a flat profile every character stands at depth zero and no split can be
/// recovered either. One refusal cascades into three.
///
/// A family is not a weakening. Each pair is a **species** of grouping the material exhibits, and
/// which pair opened a group is recovered rather than declared, so the family carries a founded
/// classification the single-pair reading could not express at all. Depth is the nesting the whole
/// family generates, which is what a reading of *this statement's* structure needs; the species is
/// carried separately on each group.
///
/// `None` when the family does not nest properly over this statement — a closer arriving for an
/// opener that is not the innermost one is not a depth, and saying so is the refusal that keeps the
/// profile meaningful.
fn depths_over(statement: &str, family: &[(char, char)]) -> Option<Vec<usize>> {
    let mut expected: Vec<char> = Vec::new();
    let mut profile = Vec::with_capacity(statement.len());
    for symbol in statement.chars() {
        let before = expected.len();
        for _ in 0..symbol.len_utf8() {
            profile.push(before);
        }
        if let Some((_, close)) = family.iter().find(|(open, _)| *open == symbol) {
            expected.push(*close);
            continue;
        }
        if family.iter().any(|(_, close)| *close == symbol) {
            match expected.last() {
                Some(wanted) if *wanted == symbol => {
                    expected.pop();
                }
                _ => return None,
            }
        }
    }
    if expected.is_empty() { Some(profile) } else { None }
}

/// Whether the region before a candidate split is bracket groups and whitespace and nothing else.
///
/// This is not a new rule. It is the property the binder-group reading is already founded on, asked
/// **before** the split is chosen instead of discovered afterwards as residue. A region carrying a
/// bare token founds no groups, so a separator with such a prefix is not the statement's split; it
/// is a separator belonging to something written inside the conclusion.
fn leading_region_founds(
    statement: &str,
    split: usize,
    family: &[(char, char)],
    depth: &[usize],
) -> bool {
    if family.is_empty() {
        return false;
    }
    let mut at = 0usize;
    while at < split {
        let symbol = char_at(statement, at);
        if symbol.is_whitespace() {
            at = step(statement, at);
            continue;
        }
        let Some((_, close)) = family
            .iter()
            .find(|(open, _)| *open == symbol)
            .filter(|_| depth[at] == 0)
            .copied()
        else {
            return false;
        };
        let mut through = step(statement, at);
        while through < split && !(char_at(statement, through) == close && depth[through] == 1) {
            through = step(statement, through);
        }
        if through >= split {
            return false;
        }
        at = step(statement, through);
    }
    // a leading region of no groups at all is not founded either: the population must witness it,
    // and `binder_group_lengths` is where that is decided rather than here
    at == split && split > 0
}

/// Byte offsets where a punctuation run stands whole at a given depth.
///
/// The depth is a parameter because the same run separates at every scale of the nesting: at depth
/// zero it splits the statement, and at a group's own depth it splits the group. That recurrence is
/// what founds it as the separator in the first place.
fn run_places(statement: &str, run: &str, depth: &[usize], wanted: usize) -> Vec<usize> {
    let mut found = Vec::new();
    let mut at = 0usize;
    while let Some(offset) = statement[at..].find(run) {
        let place = at + offset;
        if depth.get(place).is_some_and(|carried| *carried == wanted) {
            // a run must stand WHOLE: the character before and after must not extend it
            let before_ok = statement[..place]
                .chars()
                .next_back()
                .is_none_or(|symbol| !run.contains(symbol));
            let after_ok = statement[place + run.len()..]
                .chars()
                .next()
                .is_none_or(|symbol| !run.contains(symbol));
            if before_ok && after_ok {
                found.push(place);
            }
        }
        at = place + run.len();
    }
    found
}

/// The character beginning at a byte offset, and how far to step to reach the next one.
///
/// Every reading below walks a statement by byte offset, because spans and depth profiles are
/// byte-indexed. Reading `bytes[at] as char` was exact while the population was ASCII and is a
/// mojibake generator on notation, so the walk goes through this pair instead.
fn char_at(statement: &str, at: usize) -> char {
    statement[at..].chars().next().unwrap_or('\u{0}')
}

/// The byte offset of the character after the one beginning at `at`.
fn step(statement: &str, at: usize) -> usize {
    at + char_at(statement, at).len_utf8()
}

/// Recover a statement grammar from a statement population.
///
/// Every part is founded by a property that holds over the **whole** population and fails on
/// material that does not exhibit it. Nothing is recovered from one statement alone: a bracket pair
/// that balances in two statements and not in the third is not recovered, and that is the point.
pub fn recover(
    population: &BTreeSet<String>,
) -> Result<RecoveredStatementGrammar, StatementGrammarRefusal> {
    recover_under(population, SeparatorOrientation::Last)
}

/// The same recovery, with the split's **orientation** declared.
///
/// See [`SeparatorOrientation`]. The two orientations coincide on any population whose separator
/// occurs exactly once at depth zero — which is every population this module was written against —
/// so a caller that does not care may use [`recover`] and a caller comparing the two has an orbit
/// rather than two runs.
pub fn recover_under(
    population: &BTreeSet<String>,
    orientation: SeparatorOrientation,
) -> Result<RecoveredStatementGrammar, StatementGrammarRefusal> {
    if population.is_empty() {
        return Err(StatementGrammarRefusal::PopulationIsEmpty);
    }
    let mut statements = Vec::with_capacity(population.len());
    for statement in population {
        statements.push(statement.clone());
    }

    let punctuation: BTreeSet<char> = statements
        .iter()
        .flat_map(|statement| statement.chars())
        .filter(|symbol| !is_word_character(*symbol) && !symbol.is_whitespace())
        .collect();

    let mut aperture: Vec<GrammarAperture> = Vec::new();

    // ------------------------------------------------------------------- the bracket pair
    // **The candidate pairs are pruned by an exact necessary condition before any depth is
    // computed.** A pair balances over every statement only if, in every statement, the opener and
    // the closer occur the *same number of times*. So each character's occurrence vector over the
    // population is built once, and only characters sharing an occurrence vector can pair.
    //
    // This is a prune and not an approximation: equal counts is implied by balance, so no pair that
    // would have been admitted is lost. Measured 2026-08-16 over the library: 194 distinct
    // punctuation characters, hence 37,442 ordered pairs, against 154,835 statements — the
    // unpruned search is a product this founding cannot run, and the pruned one tests a handful.
    let mut occurrence: BTreeMap<char, Vec<(usize, u32)>> = BTreeMap::new();
    for (at, statement) in statements.iter().enumerate() {
        let mut here: BTreeMap<char, u32> = BTreeMap::new();
        for symbol in statement.chars() {
            if punctuation.contains(&symbol) {
                *here.entry(symbol).or_insert(0) += 1;
            }
        }
        for (symbol, count) in here {
            occurrence.entry(symbol).or_default().push((at, count));
        }
    }
    let mut by_vector: BTreeMap<&Vec<(usize, u32)>, Vec<char>> = BTreeMap::new();
    for (symbol, vector) in &occurrence {
        by_vector.entry(vector).or_default().push(*symbol);
    }
    let mut balanced_pairs: Vec<(char, char)> = Vec::new();
    for cohort in by_vector.values() {
        for open in cohort {
            for close in cohort {
                if open == close {
                    continue;
                }
                let balances = statements
                    .iter()
                    .all(|statement| depths(statement, *open, *close).is_some());
                if balances {
                    balanced_pairs.push((*open, *close));
                }
            }
        }
    }
    balanced_pairs.sort_unstable();
    // **The family is what founds the depth; the single pair is the family's degenerate case.**
    // A pair whose characters are already spent as another pair's characters is dropped, because a
    // character cannot be an opener of one species and a closer of another in one nesting; the
    // dropped pairs are reported rather than silently discarded.
    let mut family: Vec<(char, char)> = Vec::new();
    let mut discarded_pairs: Vec<String> = Vec::new();
    for (open, close) in &balanced_pairs {
        let clashes = family
            .iter()
            .any(|(o, c)| o == open || o == close || c == open || c == close);
        if clashes {
            discarded_pairs.push(format!("{open}{close}"));
        } else {
            family.push((*open, *close));
        }
    }
    // and the family must nest properly over every statement, or it is not a depth
    if !family.is_empty()
        && !statements
            .iter()
            .all(|statement| depths_over(statement, &family).is_some())
    {
        aperture.push(GrammarAperture::BracketFamilyDoesNotNest {
            admitted: family
                .iter()
                .map(|(open, close)| format!("{open}{close}"))
                .collect(),
        });
        family.clear();
    }
    if family.is_empty() {
        aperture.push(GrammarAperture::NoBracketPairBalances);
    } else if family.len() > 1 {
        aperture.push(GrammarAperture::BracketFamilyIsPlural {
            admitted: family
                .iter()
                .map(|(open, close)| format!("{open}{close}"))
                .collect(),
            discarded: discarded_pairs.clone(),
        });
    }
    // The single pair, for every reading that needs one. `None` when the material groups in more
    // than one species, which is a statement about the material and not a failure.
    let bracket = if family.len() == 1 {
        Some(family[0])
    } else {
        None
    };

    let profile = |statement: &str| -> Vec<usize> {
        if family.is_empty() {
            return vec![0; statement.len()];
        }
        depths_over(statement, &family).unwrap_or_else(|| vec![0; statement.len()])
    };

    // ------------------------------------------------------------------- the separator
    //
    // **The founding property is occurrence, and the choice among occurrences is the ORIENTATION.**
    // Until 2026-08-16 the two were one rule — *exactly once at depth zero in every statement* — and
    // that rule is a property of the three-statement fixture this module was written against. It
    // fails on mathematics for a structural reason rather than an incidental one: a separator marks
    // each antecedent group **and** the consequent, so its depth-zero count varies with the number
    // of groups. Measured 2026-08-16 over 387 whole `theorem`/`lemma` statements from
    // `Mathlib/Geometry/Euclidean`, `:` occurs at depth zero in 385 of 385 and the count runs from 1
    // to 9, so the old rule recovered **nothing** and refused the whole population.
    //
    // Splitting the rule in two founds the separator where the material actually exhibits one and
    // makes the remaining freedom what it always was — a direction — which the caller declares and
    // the return carries.
    // One pass over the population rather than one pass per candidate character. The depth profile
    // is the expensive object and it does not depend on which character is being asked about, so it
    // is computed once per statement and every candidate is decided from it.
    // **A separator is a maximal RUN of punctuation, not a single character.** Founding single
    // characters is a property of one codec rather than of separators: a Lean statement writes `:`,
    // a Rust signature writes `->`, and a reading that can only found one character returns nothing
    // on the second. Measured 2026-08-17 over 3,336 Rust signatures — three bracket species founded
    // and **zero of 3,336 split**, because no single character stands at depth zero in every one.
    //
    // A run stops at a bracket character, at whitespace, and at a word character, so the family's
    // own characters never join a run and the depth stays exactly what it was.
    let family_characters: BTreeSet<char> = family
        .iter()
        .flat_map(|(open, close)| [*open, *close])
        .collect();
    let runs_of = |statement: &str, depth: &[usize]| -> (BTreeSet<String>, BTreeSet<String>) {
        let (mut shallow, mut deep) = (BTreeSet::new(), BTreeSet::new());
        let mut carried = String::new();
        let mut carried_is_shallow = true;
        let flush = |carried: &mut String, shallow_run: bool, shallow: &mut BTreeSet<String>, deep: &mut BTreeSet<String>| {
            if carried.is_empty() {
                return;
            }
            let run = std::mem::take(carried);
            if shallow_run { shallow.insert(run); } else { deep.insert(run); }
        };
        for (at, symbol) in statement.char_indices() {
            let breaks = !punctuation.contains(&symbol) || family_characters.contains(&symbol);
            if breaks {
                flush(&mut carried, carried_is_shallow, &mut shallow, &mut deep);
                continue;
            }
            let shallow_here = depth[at] == 0;
            if !carried.is_empty() && shallow_here != carried_is_shallow {
                flush(&mut carried, carried_is_shallow, &mut shallow, &mut deep);
            }
            carried_is_shallow = shallow_here;
            carried.push(symbol);
        }
        flush(&mut carried, carried_is_shallow, &mut shallow, &mut deep);
        (shallow, deep)
    };
    let mut everywhere_at_depth_zero: Option<BTreeSet<String>> = None;
    let mut ever_deeper: BTreeSet<String> = BTreeSet::new();
    for statement in &statements {
        let depth = profile(statement);
        let (here, deeper) = runs_of(statement, &depth);
        ever_deeper.extend(deeper);
        everywhere_at_depth_zero = Some(match everywhere_at_depth_zero {
            None => here,
            Some(carried) => carried.intersection(&here).cloned().collect(),
        });
    }
    let separator_candidates: Vec<String> = everywhere_at_depth_zero
        .unwrap_or_default()
        .into_iter()
        .collect();
    // **When several characters split everywhere, the one that RECURS INSIDE the groups is the
    // separator.** The old rule disambiguated by counting — *exactly once* — and that count was the
    // fixture's shape rather than a property of a separator. This is a property of one: a separator
    // marks the same junction at every scale of the nesting, so it stands at depth zero between the
    // suppositions and the conclusion **and** again inside each supposition between what is named
    // and what it is named as. A character occurring only at depth zero is an operator of the
    // conclusion, not the split.
    //
    // Measured on the population `(a : Nat) (b : Nat) : plus a b = plus b a` and its sibling: `:`
    // and `=` both stand at depth zero in every statement, and only `:` recurs inside a group.
    //
    // The test is vacuous where the population founds no group, and is then not applied — a
    // bracket-free population has one scale, so nothing can recur at a second.
    let recurring: Vec<String> = separator_candidates
        .iter()
        .filter(|run| ever_deeper.contains(*run))
        .cloned()
        .collect();
    let separator = match (separator_candidates.len(), recurring.len()) {
        (1, _) => Some(separator_candidates[0].clone()),
        (0, _) => {
            aperture.push(GrammarAperture::NoSeparatorOccursAtDepthZeroInEveryStatement);
            None
        }
        (_, 1) => {
            aperture.push(GrammarAperture::SeparatorFoundedByRecurrenceInsideGroups {
                admitted: separator_candidates.clone(),
                recurring: recurring[0].clone(),
            });
            Some(recurring[0].clone())
        }
        _ => {
            aperture.push(GrammarAperture::SeparatorIsNotUnique {
                admitted: separator_candidates.clone(),
            });
            None
        }
    };

    // The depth-zero occurrence counts the population witnesses. When this is `{1}` the orientation
    // is a symmetry and cannot move a reading; anything else is the material saying the direction is
    // load-bearing, which is why the population is retained rather than reduced to a flag.
    let mut separator_occurrences: BTreeSet<usize> = BTreeSet::new();
    if let Some(run) = separator.as_deref() {
        for statement in &statements {
            let depth = profile(statement);
            separator_occurrences.insert(run_places(statement, run, &depth, 0).len());
        }
        if separator_occurrences.iter().any(|count| *count > 1) {
            aperture.push(GrammarAperture::SeparatorOccursPlurallyAtDepthZero {
                witnessed: separator_occurrences.clone(),
                orientation,
            });
        }
    }

    // ------------------------------------------------------------------- the readings
    let mut readings = Vec::with_capacity(statements.len());
    let mut heads: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut binder_group_lengths: BTreeSet<usize> = BTreeSet::new();
    let mut binder_name_lengths: BTreeSet<usize> = BTreeSet::new();
    let mut argument_carried_a_group = false;

    for statement in &statements {
        let depth = profile(statement);
        // **Which occurrence splits is decided by the material, and only ties reach the
        // orientation.** The leading region's founding property is already stated by this module: it
        // must be bracket groups and whitespace and nothing else. So among the depth-zero
        // occurrences, the ones that *found a leading region* are the admissible splits, and where
        // exactly one does the statement has answered by itself.
        //
        // Measured 2026-08-16 over 387 whole statements from `Mathlib/Geometry/Euclidean` under the
        // recovered bracket family: the depth-zero separator count is 1 in 373 and plural in 13. In
        // every one of the 13 the plurality comes from a supposition written *inside the conclusion*
        // with no brackets — `∃! cs : Sphere P, …` — whose separator stands at depth zero and whose
        // prefix carries a bare token, so it founds no leading region and is excluded. **Both
        // directions are wrong on that material and the founding property is right**, which is why
        // the orientation is a tiebreak here rather than the rule.
        let admissible: Vec<usize> = separator
            .as_deref()
            .map(|run| run_places(statement, run, &depth, 0))
            .unwrap_or_default();
        let founding: Vec<usize> = admissible
            .iter()
            .copied()
            .filter(|at| leading_region_founds(statement, *at, &family, &depth))
            .collect();
        let choose = |from: &[usize]| -> Option<usize> {
            match orientation {
                SeparatorOrientation::First => from.first().copied(),
                SeparatorOrientation::Last => from.last().copied(),
            }
        };
        let split = match founding.len() {
            0 => choose(&admissible),
            _ => choose(&founding),
        };
        if founding.len() > 1 {
            aperture.push(GrammarAperture::SeveralOccurrencesFoundTheLeadingRegion {
                statement: statement.clone(),
                occurrences: founding.len(),
                orientation,
            });
        }
        let mut residue: Vec<GrammarResidue> = Vec::new();
        let mut binders: Vec<BinderGroup> = Vec::new();
        let mut body: Option<BodyReading> = None;

        if let Some(split) = split {
            // the leading region
            let leading = Span::new(0, split);
            if !family.is_empty() {
                let mut at = leading.at;
                while at < leading.through {
                    let symbol = char_at(statement, at);
                    if symbol.is_whitespace() {
                        at = step(statement, at);
                        continue;
                    }
                    let opens_here = family
                        .iter()
                        .find(|(open, _)| *open == symbol)
                        .filter(|_| depth[at] == 0);
                    if let Some((open, close)) = opens_here.copied() {
                        let opened = step(statement, at);
                        let mut through = opened;
                        while through < leading.through
                            && !(char_at(statement, through) == close && depth[through] == 1)
                        {
                            through = step(statement, through);
                        }
                        let closing = if through < leading.through {
                            step(statement, through)
                        } else {
                            leading.through
                        };
                        let group_span = Span::new(at, closing.min(leading.through));
                        let interior = Span::new(opened, through.min(leading.through));
                        match read_group(statement, group_span, interior, separator.as_deref(), &depth) {
                            Ok(mut group) => {
                                group.species = Some((open, close));
                                binder_name_lengths.insert(group.names.len());
                                binders.push(group);
                            }
                            Err(refused) => {
                                aperture.push(refused.clone());
                                residue.push(GrammarResidue {
                                    span: group_span,
                                    text: group_span.text(statement).to_owned(),
                                    refused_by: refused.to_string(),
                                });
                            }
                        }
                        at = group_span.through;
                        continue;
                    }
                    // a token outside any group
                    let start = at;
                    while at < leading.through
                        && !char_at(statement, at).is_whitespace()
                        && !family.iter().any(|(open, _)| *open == char_at(statement, at))
                    {
                        at = step(statement, at);
                    }
                    if at == start {
                        // an opener that did not open at this depth: consume it as its own token
                        // rather than standing still
                        at = step(statement, at);
                    }
                    let bare = Span::new(start, at);
                    let text = bare.text(statement).to_owned();
                    let refused = GrammarAperture::LeadingRegionCarriesABareToken {
                        statement: statement.clone(),
                        token: text.clone(),
                    };
                    aperture.push(refused.clone());
                    residue.push(GrammarResidue {
                        span: bare,
                        text,
                        refused_by: refused.to_string(),
                    });
                }
            }
            binder_group_lengths.insert(binders.len());

            // the trailing region
            let trailing = Span::new(split + 1, statement.len());
            let carried = region_tokens(statement, trailing, bracket, &depth);
            let punctuation_token = carried
                .iter()
                .find(|(_, text)| !token_is_placeable(text, bracket));
            if carried.is_empty() {
                // nothing after the separator: retained whole rather than read as an empty body
                let refused = GrammarAperture::BodyCarriesPunctuation {
                    statement: statement.clone(),
                    token: String::new(),
                };
                aperture.push(refused.clone());
                body = Some(BodyReading::Undecomposed {
                    span: trailing,
                    refused_by: refused.to_string(),
                });
            } else if let Some((_, token)) = punctuation_token {
                let refused = GrammarAperture::BodyCarriesPunctuation {
                    statement: statement.clone(),
                    token: token.clone(),
                };
                aperture.push(refused.clone());
                let span = Span::new(carried[0].0.at, carried[carried.len() - 1].0.through);
                body = Some(BodyReading::Undecomposed {
                    span,
                    refused_by: refused.to_string(),
                });
                residue.push(GrammarResidue {
                    span,
                    text: span.text(statement).to_owned(),
                    refused_by: refused.to_string(),
                });
            } else {
                let head = Slot {
                    species: SlotSpecies::BodyHead,
                    span: carried[0].0,
                    occupant: carried[0].1.clone(),
                };
                let arguments: Vec<Slot> = carried[1..]
                    .iter()
                    .map(|(span, text)| Slot {
                        species: SlotSpecies::BodyArgument,
                        span: *span,
                        occupant: text.clone(),
                    })
                    .collect();
                if let Some((open, _)) = bracket
                    && arguments.iter().any(|slot| slot.occupant.starts_with(open))
                {
                    argument_carried_a_group = true;
                }
                heads
                    .entry(head.occupant.clone())
                    .or_default()
                    .insert(arguments.len());
                body = Some(BodyReading::Applied { head, arguments });
            }
        } else {
            let whole = Span::new(0, statement.len());
            residue.push(GrammarResidue {
                span: whole,
                text: statement.clone(),
                refused_by: "no separator was recovered, so the statement founds no split"
                    .to_owned(),
            });
        }

        residue.sort();
        readings.push(StatementReading {
            statement: statement.clone(),
            split_at: split,
            binders,
            body,
            residue,
        });
    }

    // ------------------------------------------------------------------- the population apertures
    if !argument_carried_a_group {
        let arguments: BTreeSet<String> = readings
            .iter()
            .filter_map(|reading| match &reading.body {
                Some(BodyReading::Applied { arguments, .. }) => Some(arguments.clone()),
                _ => None,
            })
            .flatten()
            .map(|slot| slot.occupant)
            .collect();
        aperture.push(GrammarAperture::ArgumentPositionNeverCarriedAnApplication { arguments });
    }
    for (head, arities) in &heads {
        if arities.len() > 1 {
            aperture.push(GrammarAperture::HeadArityConflicts {
                head: head.clone(),
                arities: arities.clone(),
            });
        }
    }
    if !binder_group_lengths.contains(&0) {
        aperture.push(GrammarAperture::EmptyBinderListNeverWitnessed {
            witnessed: binder_group_lengths.clone(),
        });
    }
    aperture.sort();
    aperture.dedup();

    Ok(RecoveredStatementGrammar {
        population: statements,
        punctuation,
        bracket,
        bracket_family: family,
        balanced_pairs,
        separator,
        separator_candidates,
        separator_occurrences,
        orientation,
        readings,
        heads,
        binder_group_lengths,
        binder_name_lengths,
        aperture,
    })
}

/// Read one bracket group: the run before its own separator, and the token after it.
fn read_group(
    statement: &str,
    span: Span,
    interior: Span,
    separator: Option<&str>,
    depth: &[usize],
) -> Result<BinderGroup, GrammarAperture> {
    let group_text = span.text(statement).to_owned();
    let own_depth = depth.get(interior.at).copied().unwrap_or(0);
    let Some(separator) = separator else {
        return Err(GrammarAperture::BinderGroupCarriesNoSeparator {
            statement: statement.to_owned(),
            group: group_text,
        });
    };
    let cut = run_places(&statement[..interior.through], separator, depth, own_depth)
        .into_iter()
        .find(|at| *at >= interior.at);
    let Some(cut) = cut else {
        return Err(GrammarAperture::BinderGroupCarriesNoSeparator {
            statement: statement.to_owned(),
            group: group_text,
        });
    };

    let named = tokens(statement, Span::new(interior.at, cut));
    if named.is_empty()
        || named
            .iter()
            .any(|(_, text)| text.chars().any(|symbol| !is_word_character(symbol)))
    {
        return Err(GrammarAperture::BinderGroupCarriesNoSeparator {
            statement: statement.to_owned(),
            group: group_text,
        });
    }
    let carried = tokens(statement, Span::new(cut + separator.len(), interior.through));
    if carried.len() != 1
        || carried[0]
            .1
            .chars()
            .any(|symbol| !is_word_character(symbol))
    {
        return Err(GrammarAperture::BinderTypeIsNotOneToken {
            statement: statement.to_owned(),
            group: group_text,
        });
    }

    Ok(BinderGroup {
        span,
        names: named
            .into_iter()
            .map(|(span, text)| Slot {
                species: SlotSpecies::BinderName,
                span,
                occupant: text,
            })
            .collect(),
        carried: Some(Slot {
            species: SlotSpecies::BinderType,
            span: carried[0].0,
            occupant: carried[0].1.clone(),
        }),
        // stamped by the caller, which is the only place that knows which family member opened it
        species: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The deposit's own statement population, verbatim. Three statements, and the third is
    /// load-bearing: without `(a b : Nat) : a = b` the residue reading is never exercised and the
    /// grammar's aperture would be invisible on its own material.
    fn deposited() -> BTreeSet<String> {
        [
            "(P : Prop) (h : P) : exactCarrier P",
            "(a b : Nat) : a = b",
            "(h : P) : exactCarrier P",
        ]
        .into_iter()
        .map(str::to_owned)
        .collect()
    }

    #[test]
    fn the_bracket_pair_is_recovered_and_it_is_the_only_ordered_pair_that_balances() {
        let grammar = recover(&deposited()).expect("recovers");
        assert_eq!(grammar.bracket(), Some(('(', ')')));
        assert_eq!(grammar.balanced_pairs(), &[('(', ')')]);
        // the reversed pair goes negative at the first character of the first statement
        assert!(!grammar.balanced_pairs().contains(&(')', '(')));
        assert_eq!(grammar.punctuation(), &BTreeSet::from(['(', ')', ':', '=']));
    }

    #[test]
    fn the_separator_is_the_character_occurring_once_at_depth_zero_in_every_statement() {
        let grammar = recover(&deposited()).expect("recovers");
        assert_eq!(grammar.separator(), Some(':'));
        assert_eq!(grammar.separator_candidates(), &[":".to_owned()]);
        // `=` occurs once at depth zero in one statement and never in the other two.
        assert!(!grammar.separator_candidates().iter().any(|run| run == "="));
    }

    #[test]
    fn a_body_carrying_punctuation_is_retained_whole_as_residue_and_never_decomposed() {
        let grammar = recover(&deposited()).expect("recovers");
        let reading = grammar.reading("(a b : Nat) : a = b").expect("read");
        assert!(matches!(
            reading.body,
            Some(BodyReading::Undecomposed { .. })
        ));
        assert_eq!(reading.residue.len(), 1);
        assert_eq!(reading.residue[0].text, "a = b");
        assert!(grammar.aperture().iter().any(|bound| matches!(
            bound,
            GrammarAperture::BodyCarriesPunctuation { token, .. } if token == "="
        )));
        // and the two decomposable statements carry no residue at all
        for statement in [
            "(P : Prop) (h : P) : exactCarrier P",
            "(h : P) : exactCarrier P",
        ] {
            assert!(grammar.reading(statement).expect("read").residue.is_empty());
        }
    }

    #[test]
    fn the_binder_groups_are_recovered_with_their_names_and_their_carried_token() {
        let grammar = recover(&deposited()).expect("recovers");
        let reading = grammar
            .reading("(P : Prop) (h : P) : exactCarrier P")
            .expect("read");
        assert_eq!(reading.binders.len(), 2);
        assert_eq!(reading.binders[0].text(&reading.statement), "(P : Prop)");
        assert_eq!(reading.binders[0].names[0].occupant, "P");
        assert_eq!(
            reading.binders[0]
                .carried
                .as_ref()
                .expect("carried")
                .occupant,
            "Prop"
        );
        assert_eq!(reading.binders[1].text(&reading.statement), "(h : P)");

        let two_names = grammar.reading("(a b : Nat) : a = b").expect("read");
        assert_eq!(two_names.binders.len(), 1);
        assert_eq!(
            two_names.binders[0]
                .names
                .iter()
                .map(|slot| slot.occupant.as_str())
                .collect::<Vec<&str>>(),
            vec!["a", "b"]
        );
    }

    #[test]
    fn two_witnessed_lengths_found_a_nonempty_sequence_and_zero_stays_unfounded() {
        let grammar = recover(&deposited()).expect("recovers");
        assert_eq!(grammar.binder_group_lengths(), &BTreeSet::from([1, 2]));
        assert_eq!(grammar.binder_name_lengths(), &BTreeSet::from([1, 2]));
        assert!(grammar.sequence_is_founded());
        assert!(grammar.binder_length_is_founded(3));
        assert!(!grammar.binder_length_is_founded(0));
        assert!(
            grammar.aperture().iter().any(|bound| matches!(
                bound,
                GrammarAperture::EmptyBinderListNeverWitnessed { .. }
            ))
        );
    }

    #[test]
    fn one_statement_founds_its_own_length_and_not_a_sequence() {
        // The gauge must be able to act trivially, or its acting is not evidence. `CLAUDE.md` §8.
        let narrow: BTreeSet<String> = ["(h : P) : exactCarrier P".to_owned()].into();
        let grammar = recover(&narrow).expect("recovers");
        assert_eq!(grammar.binder_group_lengths(), &BTreeSet::from([1]));
        assert!(!grammar.sequence_is_founded());
        assert!(!grammar.binder_length_is_founded(2));
        assert!(grammar.binder_length_is_founded(1));
    }

    #[test]
    fn the_head_arity_is_founded_only_for_a_token_the_population_put_in_first_position() {
        let grammar = recover(&deposited()).expect("recovers");
        assert_eq!(grammar.founded_arity("exactCarrier"), Some(1));
        assert_eq!(grammar.heads().len(), 1);
        assert_eq!(grammar.founded_arity("exact_chart_carry"), None);
        assert_eq!(
            grammar.unfounded_head_arity("exact_chart_carry"),
            Some(GrammarAperture::HeadArityIsUnfounded {
                identifier: "exact_chart_carry".to_owned()
            })
        );
        assert_eq!(grammar.unfounded_head_arity("exactCarrier"), None);
    }

    #[test]
    fn no_argument_position_in_the_population_ever_carried_a_group_and_the_grammar_says_so() {
        let grammar = recover(&deposited()).expect("recovers");
        assert_eq!(
            grammar.witnessed_arguments(),
            BTreeSet::from(["P".to_owned()])
        );
        assert!(grammar.aperture().iter().any(|bound| matches!(
            bound,
            GrammarAperture::ArgumentPositionNeverCarriedAnApplication { .. }
        )));
    }

    #[test]
    fn a_population_that_does_witness_a_nested_argument_founds_it_and_the_bound_lifts() {
        // The aperture is a property of the material and not of this module: supply the shape and
        // it stops being reported. A bound that cannot lift is a bound nothing measured.
        let mut wider = deposited();
        wider.insert("(P : Prop) : exactCarrier (exactCarrier P)".to_owned());
        let grammar = recover(&wider).expect("recovers");
        assert!(!grammar.aperture().iter().any(|bound| matches!(
            bound,
            GrammarAperture::ArgumentPositionNeverCarriedAnApplication { .. }
        )));
    }

    #[test]
    fn the_rendering_puts_recovered_parts_in_place_and_brackets_the_residue() {
        let grammar = recover(&deposited()).expect("recovers");
        assert_eq!(
            grammar
                .render("(P : Prop) (h : P) : exactCarrier P")
                .expect("rendered"),
            "(|name:P|:|type:Prop|)|(|name:h|:|type:P|)|:|head:exactCarrier|arg:P"
        );
        assert_eq!(
            grammar.render("(a b : Nat) : a = b").expect("rendered"),
            "(|name:a|name:b|:|type:Nat|)|:|[a = b]"
        );
    }

    #[test]
    fn substitution_replaces_exactly_the_recovered_span_and_renormalizes() {
        let grammar = recover(&deposited()).expect("recovers");
        let reading = grammar
            .reading("(P : Prop) (h : P) : exactCarrier P")
            .expect("read");
        let head = reading
            .slots()
            .into_iter()
            .find(|slot| slot.species == SlotSpecies::BodyHead)
            .expect("a head slot");
        assert_eq!(
            reading.substituted(head.span, "exact_chart_carry"),
            "(P : Prop) (h : P) : exact_chart_carry P"
        );
        assert_eq!(
            reading.without_group(&reading.binders[0]),
            "(h : P) : exactCarrier P"
        );
        assert_eq!(
            reading.with_group("(a b : Nat)").expect("split"),
            "(P : Prop) (h : P) (a b : Nat) : exactCarrier P"
        );
    }

    /// **The orientation is a symmetry where the material exhibits one separator.** This is the arm
    /// that stops the orbit below from reading its own construction: an axis that moved every
    /// reading would be suspicious, and this one must move nothing here.
    #[test]
    fn the_two_orientations_are_one_map_where_the_separator_occurs_once() {
        let population: BTreeSet<String> = [
            "(P : Prop) (h : P) : exactCarrier P".to_owned(),
            "(h : P) : exactCarrier P".to_owned(),
        ]
        .into();
        let first = recover_under(&population, SeparatorOrientation::First).expect("recovers");
        let last = recover_under(&population, SeparatorOrientation::Last).expect("recovers");
        assert_eq!(first.separator_occurrences(), &BTreeSet::from([1]));
        assert!(!first.orientation_is_load_bearing());
        assert_eq!(first.readings(), last.readings());
    }

    /// **The shape mathematics is actually written in, and the reading that survives it.**
    ///
    /// The second statement carries a supposition *inside its conclusion*, written with no brackets
    /// — the `∃!` idiom — so its separator stands at depth zero and the statement admits two
    /// candidate splits. Measured 2026-08-16 over 387 whole statements from
    /// `Mathlib/Geometry/Euclidean` under the recovered bracket family, that is the case in 13 of
    /// them and it is the **only** source of plurality there.
    ///
    /// **Both directions are wrong on it and the founding property is right.** `Last` would split
    /// inside the conclusion; `First` happens to be right here and is wrong on any statement whose
    /// suppositions are themselves unbracketed. What decides is that a split must leave a leading
    /// region of groups and whitespace, and only one candidate does.
    #[test]
    fn the_material_decides_the_split_where_neither_direction_would() {
        let population: BTreeSet<String> = [
            "(a : Nat) (b : Nat) : plus a b = plus b a".to_owned(),
            "(s : Set) (h : Nonempty) : exists c : Point, mem c s".to_owned(),
        ]
        .into();

        let last = recover_under(&population, SeparatorOrientation::Last).expect("recovers");
        assert_eq!(last.separator(), Some(':'));
        // one statement admits one candidate, the other admits two
        assert_eq!(last.separator_occurrences(), &BTreeSet::from([1, 2]));
        assert!(last.orientation_is_load_bearing());
        assert!(last.aperture().iter().any(|bound| matches!(
            bound,
            GrammarAperture::SeparatorOccursPlurallyAtDepthZero { .. }
        )));

        let exists = last
            .reading("(s : Set) (h : Nonempty) : exists c : Point, mem c s")
            .expect("the population carries it");
        assert_eq!(exists.binders.len(), 2);
        assert_eq!(exists.binders[0].names[0].span.text(&exists.statement), "s");
        assert_eq!(exists.binders[1].names[0].span.text(&exists.statement), "h");

        // **and the orientation could not have changed it**: the material founded the split, so the
        // two orientations return the identical reading even though the occurrence count is plural
        let first = recover_under(&population, SeparatorOrientation::First).expect("recovers");
        assert_eq!(first.readings(), last.readings());
        assert!(
            !last.aperture().iter().any(|bound| matches!(
                bound,
                GrammarAperture::SeveralOccurrencesFoundTheLeadingRegion { .. }
            )),
            "no statement here leaves the choice to the orientation"
        );
    }

    #[test]
    fn an_empty_population_is_refused_by_type_rather_than_returned_empty() {
        assert_eq!(
            recover(&BTreeSet::new()),
            Err(StatementGrammarRefusal::PopulationIsEmpty)
        );
    }

    /// **The orbit of the excised charset gate.** This exact population was the fixture that
    /// asserted the refusal; it is now read, and read correctly.
    #[test]
    fn a_statement_written_in_notation_is_read_rather_than_refused() {
        let population: BTreeSet<String> = ["(α : Prop) : exactCarrier α".to_owned()].into();
        let grammar = recover(&population).expect("notation is material, not a refusal");
        assert_eq!(grammar.bracket(), Some(('(', ')')));
        assert_eq!(grammar.separator(), Some(':'));
        let reading = &grammar.readings()[0];
        // `α` is a letter in the material's own script, so it is one word token and not two bytes
        // of punctuation. That is the whole content of the excision.
        assert_eq!(reading.binders.len(), 1);
        assert_eq!(reading.binders[0].names.len(), 1);
        assert_eq!(reading.binders[0].names[0].span.text(&reading.statement), "α");
        assert!(matches!(
            &reading.body,
            Some(BodyReading::Applied { head, arguments })
                if head.span.text(&reading.statement) == "exactCarrier"
                    && arguments.len() == 1
                    && arguments[0].span.text(&reading.statement) == "α"
        ));
        assert!(reading.residue.is_empty());
    }

    /// **The other half of that orbit, and it is the one that could have gone wrong.** The depth
    /// profile is indexed by byte while the separator is found by `char_indices`, so a multi-byte
    /// character before the separator shifts one against the other unless the profile carries an
    /// entry per byte. Here `ℝ` and `α` sit before the split; with a per-character profile the
    /// depth read at the separator's offset is the depth two characters earlier, and the group is
    /// mis-founded silently.
    #[test]
    fn a_multi_byte_character_before_the_split_does_not_shift_the_depth_profile() {
        let population: BTreeSet<String> = [
            "(α : ℝ) (β : ℝ) : dist α β = dist β α".to_owned(),
            "(x : ℝ) : dist x x = zero".to_owned(),
        ]
        .into();
        let grammar = recover(&population).expect("recovers");
        assert_eq!(grammar.bracket(), Some(('(', ')')));
        assert_eq!(grammar.separator(), Some(':'));
        let two = grammar
            .reading("(α : ℝ) (β : ℝ) : dist α β = dist β α")
            .expect("the population carries it");
        assert_eq!(two.binders.len(), 2);
        assert_eq!(two.binders[0].carried.as_ref().expect("a carried token").span.text(&two.statement), "ℝ");
        assert_eq!(two.binders[1].names[0].span.text(&two.statement), "β");
    }

    #[test]
    fn a_population_with_no_balanced_pair_founds_no_bracketing_and_reports_it() {
        let population: BTreeSet<String> = ["a : b".to_owned(), "c : d".to_owned()].into();
        let grammar = recover(&population).expect("recovers");
        assert_eq!(grammar.bracket(), None);
        assert!(
            grammar
                .aperture()
                .contains(&GrammarAperture::NoBracketPairBalances)
        );
        // the split is still recovered: `:` occurs once at depth zero in both
        assert_eq!(grammar.separator(), Some(':'));
    }

    #[test]
    fn the_recovery_reads_its_own_rule_and_not_a_language_it_was_never_told_about() {
        // `a : b = c` / `d : e = f`. The ONE ordered pair that balances over this population is
        // `(':', '=')` -- `:` opens and `=` closes, exactly once each, in that order, in both
        // statements. A reader who knew Lean would never call that a bracket, and the recovery does,
        // because the recovery's rule is the balance and nothing else. That is what makes the
        // reading recovered rather than authored, and it is why the bound is reported instead of
        // being decorated with a name it did not earn.
        let population: BTreeSet<String> = ["a : b = c".to_owned(), "d : e = f".to_owned()].into();
        let grammar = recover(&population).expect("recovers");
        assert_eq!(grammar.bracket(), Some((':', '=')));
        // and having spent both characters on the bracket, nothing is left to split on
        assert_eq!(grammar.separator(), None);
        assert!(
            grammar
                .aperture()
                .contains(&GrammarAperture::NoSeparatorOccursAtDepthZeroInEveryStatement)
        );
        for reading in grammar.readings() {
            assert_eq!(reading.residue.len(), 1);
            assert_eq!(reading.residue[0].text, reading.statement);
        }
    }

    #[test]
    fn a_population_whose_bracket_pair_is_ambiguous_founds_neither_a_bracket_nor_a_split() {
        // Two ordered pairs balance here -- `('(', ')')` and `(':', '=')` -- and since 2026-08-16
        // that is a FAMILY rather than an ambiguity: both are grouping species and the depth is the
        // nesting they generate together. `bracket()` is still `None`, because a single pair is what
        // that accessor means and the material exhibits two.
        //
        // What follows is the consequence, and it is worth keeping as a bound: both characters are
        // spent on the family, so no punctuation is left to split on and the statements are retained
        // whole. A reading can found a nesting and still found no statement.
        let population: BTreeSet<String> =
            ["(a) : b = c".to_owned(), "(d) : e = f".to_owned()].into();
        let grammar = recover(&population).expect("recovers");
        assert_eq!(grammar.bracket(), None);
        assert_eq!(grammar.bracket_family().len(), 2);
        assert!(grammar.balanced_pairs().len() > 1);
        assert!(
            grammar
                .aperture()
                .iter()
                .any(|bound| matches!(bound, GrammarAperture::BracketFamilyIsPlural { .. }))
        );
        assert_eq!(grammar.separator(), None);
        assert!(grammar.aperture().contains(
            &GrammarAperture::NoSeparatorOccursAtDepthZeroInEveryStatement
        ));
        for reading in grammar.readings() {
            assert_eq!(reading.residue.len(), 1);
            assert_eq!(reading.residue[0].text, reading.statement);
        }
    }
}
