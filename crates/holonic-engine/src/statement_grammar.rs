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
    statement.split_whitespace().collect::<Vec<&str>>().join(" ")
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
    /// More than one character occurs exactly once at depth zero in every statement.
    SeparatorIsNotUnique { admitted: Vec<char> },
    /// No character does, so the population founds no split.
    NoSeparatorOccursOnceAtDepthZeroInEveryStatement,
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
    HeadArityConflicts { head: String, arities: BTreeSet<usize> },
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
                write!(formatter, "no ordered punctuation pair balances; the population exhibits no nesting")
            }
            Self::SeparatorIsNotUnique { admitted } => write!(
                formatter,
                "{admitted:?} each occur exactly once at depth zero in every statement, so the split is undecided"
            ),
            Self::NoSeparatorOccursOnceAtDepthZeroInEveryStatement => write!(
                formatter,
                "no character occurs exactly once at depth zero in every statement, so no split is founded"
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

/// Why a recovery was refused outright.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatementGrammarRefusal {
    /// The recovery indexes statements by byte offset, and a byte offset into a multi-byte character
    /// names a place no token can begin.
    StatementIsNotAscii { statement: String },
    /// A grammar recovered from nothing would carry no relation at all. `CLAUDE.md` §8: a law that
    /// returns zero proves nothing about itself, so this is refused by type rather than returned
    /// empty for a caller to notice.
    PopulationIsEmpty,
}

impl std::fmt::Display for StatementGrammarRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::StatementIsNotAscii { statement } => write!(
                formatter,
                "the statement {statement:?} is not ASCII; a byte offset in it cannot name a token boundary"
            ),
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
    balanced_pairs: Vec<(char, char)>,
    separator: Option<char>,
    separator_candidates: Vec<char>,
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
    pub const fn separator(&self) -> Option<char> {
        self.separator
    }

    /// Every character that occurred exactly once at depth zero in every statement.
    pub fn separator_candidates(&self) -> &[char] {
        &self.separator_candidates
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
                || self.separator == Some(symbol);
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
fn is_word_character(symbol: char) -> bool {
    symbol.is_ascii_alphanumeric() || symbol == '_' || symbol == '.'
}

/// The tokens of one region, each with its span, in reading order. A token is a maximal run of word
/// characters, or a single punctuation character.
fn tokens(statement: &str, span: Span) -> Vec<(Span, String)> {
    let bytes = statement.as_bytes();
    let mut found = Vec::new();
    let mut at = span.at;
    while at < span.through {
        let symbol = bytes[at] as char;
        if symbol.is_whitespace() {
            at += 1;
            continue;
        }
        if is_word_character(symbol) {
            let start = at;
            while at < span.through && is_word_character(bytes[at] as char) {
                at += 1;
            }
            found.push((Span::new(start, at), statement[start..at].to_owned()));
            continue;
        }
        found.push((Span::new(at, at + 1), symbol.to_string()));
        at += 1;
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
    let bytes = statement.as_bytes();
    let own_depth = depth.get(span.at).copied().unwrap_or(0);
    let mut found = Vec::new();
    let mut at = span.at;
    while at < span.through {
        let symbol = bytes[at] as char;
        if symbol.is_whitespace() {
            at += 1;
            continue;
        }
        if symbol == open && depth[at] == own_depth {
            let mut through = at + 1;
            while through < span.through
                && !(bytes[through] as char == close && depth[through] == own_depth + 1)
            {
                through += 1;
            }
            let group = Span::new(at, (through + 1).min(span.through));
            found.push((group, group.text(statement).to_owned()));
            at = group.through;
            continue;
        }
        if is_word_character(symbol) {
            let start = at;
            while at < span.through && is_word_character(bytes[at] as char) {
                at += 1;
            }
            found.push((Span::new(start, at), statement[start..at].to_owned()));
            continue;
        }
        found.push((Span::new(at, at + 1), symbol.to_string()));
        at += 1;
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
fn depths(statement: &str, open: char, close: char) -> Option<Vec<usize>> {
    let mut depth: i64 = 0;
    let mut profile = Vec::with_capacity(statement.len());
    for symbol in statement.chars() {
        profile.push(usize::try_from(depth).ok()?);
        if symbol == open {
            depth += 1;
        } else if symbol == close {
            depth -= 1;
            if depth < 0 {
                return None;
            }
        }
    }
    if depth == 0 {
        Some(profile)
    } else {
        None
    }
}

/// Recover a statement grammar from a statement population.
///
/// Every part is founded by a property that holds over the **whole** population and fails on
/// material that does not exhibit it. Nothing is recovered from one statement alone: a bracket pair
/// that balances in two statements and not in the third is not recovered, and that is the point.
pub fn recover(
    population: &BTreeSet<String>,
) -> Result<RecoveredStatementGrammar, StatementGrammarRefusal> {
    if population.is_empty() {
        return Err(StatementGrammarRefusal::PopulationIsEmpty);
    }
    let mut statements = Vec::with_capacity(population.len());
    for statement in population {
        if !statement.is_ascii() {
            return Err(StatementGrammarRefusal::StatementIsNotAscii {
                statement: statement.clone(),
            });
        }
        statements.push(statement.clone());
    }

    let punctuation: BTreeSet<char> = statements
        .iter()
        .flat_map(|statement| statement.chars())
        .filter(|symbol| !is_word_character(*symbol) && !symbol.is_whitespace())
        .collect();

    let mut aperture: Vec<GrammarAperture> = Vec::new();

    // ------------------------------------------------------------------- the bracket pair
    let mut balanced_pairs: Vec<(char, char)> = Vec::new();
    for open in &punctuation {
        for close in &punctuation {
            if open == close {
                continue;
            }
            let balances = statements
                .iter()
                .all(|statement| depths(statement, *open, *close).is_some());
            let opens = statements
                .iter()
                .any(|statement| statement.contains(*open));
            if balances && opens {
                balanced_pairs.push((*open, *close));
            }
        }
    }
    let bracket = match balanced_pairs.len() {
        1 => Some(balanced_pairs[0]),
        0 => {
            aperture.push(GrammarAperture::NoBracketPairBalances);
            None
        }
        _ => {
            aperture.push(GrammarAperture::BracketPairIsNotUnique {
                admitted: balanced_pairs
                    .iter()
                    .map(|(open, close)| format!("{open}{close}"))
                    .collect(),
            });
            None
        }
    };

    let profile = |statement: &str| -> Vec<usize> {
        match bracket {
            Some((open, close)) => {
                depths(statement, open, close).unwrap_or_else(|| vec![0; statement.len()])
            }
            None => vec![0; statement.len()],
        }
    };

    // ------------------------------------------------------------------- the separator
    let mut separator_candidates: Vec<char> = Vec::new();
    for symbol in &punctuation {
        if bracket.is_some_and(|(open, close)| *symbol == open || *symbol == close) {
            continue;
        }
        let once_everywhere = statements.iter().all(|statement| {
            let depth = profile(statement);
            statement
                .char_indices()
                .filter(|(at, carried)| carried == symbol && depth[*at] == 0)
                .count()
                == 1
        });
        if once_everywhere {
            separator_candidates.push(*symbol);
        }
    }
    let separator = match separator_candidates.len() {
        1 => Some(separator_candidates[0]),
        0 => {
            aperture.push(GrammarAperture::NoSeparatorOccursOnceAtDepthZeroInEveryStatement);
            None
        }
        _ => {
            aperture.push(GrammarAperture::SeparatorIsNotUnique {
                admitted: separator_candidates.clone(),
            });
            None
        }
    };

    // ------------------------------------------------------------------- the readings
    let mut readings = Vec::with_capacity(statements.len());
    let mut heads: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut binder_group_lengths: BTreeSet<usize> = BTreeSet::new();
    let mut binder_name_lengths: BTreeSet<usize> = BTreeSet::new();
    let mut argument_carried_a_group = false;

    for statement in &statements {
        let depth = profile(statement);
        let split = separator.and_then(|symbol| {
            statement
                .char_indices()
                .find(|(at, carried)| *carried == symbol && depth[*at] == 0)
                .map(|(at, _)| at)
        });
        let mut residue: Vec<GrammarResidue> = Vec::new();
        let mut binders: Vec<BinderGroup> = Vec::new();
        let mut body: Option<BodyReading> = None;

        if let Some(split) = split {
            // the leading region
            let leading = Span::new(0, split);
            if let Some((open, close)) = bracket {
                let bytes = statement.as_bytes();
                let mut at = leading.at;
                while at < leading.through {
                    let symbol = bytes[at] as char;
                    if symbol.is_whitespace() {
                        at += 1;
                        continue;
                    }
                    if symbol == open && depth[at] == 0 {
                        let mut through = at + 1;
                        while through < leading.through && !(bytes[through] as char == close && depth[through] == 1)
                        {
                            through += 1;
                        }
                        let group_span = Span::new(at, (through + 1).min(leading.through));
                        let interior = Span::new(at + 1, through.min(leading.through));
                        match read_group(statement, group_span, interior, separator, &depth) {
                            Ok(group) => {
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
                        && !(bytes[at] as char).is_whitespace()
                        && !(bytes[at] as char == open)
                    {
                        at += 1;
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
                let span = Span::new(
                    carried[0].0.at,
                    carried[carried.len() - 1].0.through,
                );
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
                if let Some((open, _)) = bracket {
                    if arguments
                        .iter()
                        .any(|slot| slot.occupant.starts_with(open))
                    {
                        argument_carried_a_group = true;
                    }
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
                refused_by: "no separator was recovered, so the statement founds no split".to_owned(),
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
        balanced_pairs,
        separator,
        separator_candidates,
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
    separator: Option<char>,
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
    let cut = statement[interior.at..interior.through]
        .char_indices()
        .map(|(offset, symbol)| (interior.at + offset, symbol))
        .find(|(at, symbol)| *symbol == separator && depth[*at] == own_depth)
        .map(|(at, _)| at);
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
    let carried = tokens(statement, Span::new(cut + 1, interior.through));
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
        assert_eq!(
            grammar.punctuation(),
            &BTreeSet::from(['(', ')', ':', '='])
        );
    }

    #[test]
    fn the_separator_is_the_character_occurring_once_at_depth_zero_in_every_statement() {
        let grammar = recover(&deposited()).expect("recovers");
        assert_eq!(grammar.separator(), Some(':'));
        assert_eq!(grammar.separator_candidates(), &[':']);
        // `=` occurs once at depth zero in one statement and never in the other two.
        assert!(!grammar.separator_candidates().contains(&'='));
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
            reading.binders[0].carried.as_ref().expect("carried").occupant,
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
        assert!(grammar.aperture().iter().any(|bound| matches!(
            bound,
            GrammarAperture::EmptyBinderListNeverWitnessed { .. }
        )));
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
        assert_eq!(grammar.witnessed_arguments(), BTreeSet::from(["P".to_owned()]));
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

    #[test]
    fn an_empty_population_is_refused_by_type_rather_than_returned_empty() {
        assert_eq!(
            recover(&BTreeSet::new()),
            Err(StatementGrammarRefusal::PopulationIsEmpty)
        );
    }

    #[test]
    fn a_non_ascii_statement_is_refused_because_a_byte_offset_would_name_no_boundary() {
        let population: BTreeSet<String> = ["(α : Prop) : exactCarrier α".to_owned()].into();
        assert!(matches!(
            recover(&population),
            Err(StatementGrammarRefusal::StatementIsNotAscii { .. })
        ));
    }

    #[test]
    fn a_population_with_no_balanced_pair_founds_no_bracketing_and_reports_it() {
        let population: BTreeSet<String> = ["a : b".to_owned(), "c : d".to_owned()].into();
        let grammar = recover(&population).expect("recovers");
        assert_eq!(grammar.bracket(), None);
        assert!(grammar
            .aperture()
            .contains(&GrammarAperture::NoBracketPairBalances));
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
        assert!(grammar
            .aperture()
            .contains(&GrammarAperture::NoSeparatorOccursOnceAtDepthZeroInEveryStatement));
        for reading in grammar.readings() {
            assert_eq!(reading.residue.len(), 1);
            assert_eq!(reading.residue[0].text, reading.statement);
        }
    }

    #[test]
    fn a_population_whose_bracket_pair_is_ambiguous_founds_neither_a_bracket_nor_a_split() {
        // Two ordered pairs balance here -- `('(', ')')` and `(':', '=')` among others -- so no
        // depth is founded; with no depth every punctuation character is at depth zero and four of
        // them occur exactly once in every statement, so the separator is ambiguous too. Both
        // bounds are returned by name and every statement is retained whole.
        let population: BTreeSet<String> =
            ["(a) : b = c".to_owned(), "(d) : e = f".to_owned()].into();
        let grammar = recover(&population).expect("recovers");
        assert_eq!(grammar.bracket(), None);
        assert!(grammar.balanced_pairs().len() > 1);
        assert!(grammar.aperture().iter().any(|bound| matches!(
            bound,
            GrammarAperture::BracketPairIsNotUnique { .. }
        )));
        assert_eq!(grammar.separator(), None);
        assert!(grammar.aperture().iter().any(|bound| matches!(
            bound,
            GrammarAperture::SeparatorIsNotUnique { .. }
        )));
        for reading in grammar.readings() {
            assert_eq!(reading.residue.len(), 1);
            assert_eq!(reading.residue[0].text, reading.statement);
        }
    }
}
