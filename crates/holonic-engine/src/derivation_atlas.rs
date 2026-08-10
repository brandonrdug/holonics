//! A deposited derivation population, read back as a circuit, and what a later production moved
//! in it.
//!
//! `examples/derivation_atlas_reader.rs` has computed this reading since the transition, but it
//! computed it *inside a `main`*, so nothing could be tested and nothing could compare two
//! readings. This module is that organ, and the reader now calls it. What is new here is the
//! second half: [`invariant_movement`] and [`route_movement`] return **what changed between two
//! readings**, which is the only form in which an analysis can be fed back to the production that
//! caused it.
//!
//! ## The circuit
//!
//! ```text
//!   0-cells   the declarations named -- theorems produced, symbols recruited, and (under
//!             `StatementIncidence::Founded`) the statements reached
//!   1-cells   a recruitment: this derivation named that symbol
//!             a reach:       this derivation proved that statement
//! ```
//!
//! There are no 2-cells **in this module**, and that is a **correction to the reader's own module
//! documentation**, which has always declared a 2-cell as *"two derivations reaching the SAME
//! statement by different recruitment"* while `main` founded none. Founding them would not be free:
//! a square 2-cell over a pair of derivations sharing two symbols **cancels exactly the grade-1
//! cycle** the same document reads as *"independent distinct routes to one result"*. Those two
//! sentences are not compatible, and this module refuses to pick one silently. It founds no 2-cell
//! and says so here.
//!
//! **The refusal is resolved by construction in [`crate::derivation_two_cells`], and the resolution
//! is not a choice between those two sentences.** The distinction this module could not draw is
//! whether two routes to one result are one proof or two, and answering it needs a denotation that
//! an orthographic reading does not carry. [`crate::name_elaboration`] supplies one — the meaning of
//! a name is the transitive closure of what it recruits, with the depth every constituent entered at
//! — so a square is founded exactly where the two routes' elaborated meanings agree, and where they
//! do not the hole is left and the disagreement retained as a typed obstruction. `β₁` after filling
//! is then the first sentence's quantity and the filled population is the second's, and both are
//! returned. This module remains the reading that founds no 2-cell, which is what makes it the
//! *before* the other one measures against.
//!
//! ## What a recruitment is, and what it is not
//!
//! A recruitment is an identifier the source names that the environment had to supply. Three
//! things are therefore **not** recruitments, and each exclusion is a rule rather than a filter:
//!
//! - **The codec's own structural vocabulary** ([`CODEC_KEYWORDS`]). `import`, `namespace`, `by`,
//!   `using`, `fun` are how the export codec writes a file; they name nothing the derivation
//!   depended on. A line whose leading word is `end` is skipped entirely: `end Soma` is the closing
//!   half of `namespace Soma`, and reading it as a second naming of `Soma` is what made **the only
//!   nonzero torsion in the entire deposit be the `end` keyword** — a receiver-visible coordinate
//!   of the file layout promoted into a homological invariant, which is the contaminant species
//!   `CLAUDE.md` §0 convicts by name. It was found by grading this reading rather than reading its
//!   output, and it is closed here.
//! - **What the line founds.** After a declaration former ([`DECLARATION_FORMERS`]) the next
//!   identifier is *bound by this file*, not recruited: `def exactCarrier`, `abbrev ExactRelay`,
//!   `theorem formal_carry`. Likewise `have <bound> := <recruitment>` binds on the left, so only
//!   the part after `:=` is read.
//! - **Single characters.** `P`, `Q`, `h`, `a`, `b`, `x` are Lean's binder convention. This is the
//!   reading's one orthographic rule and it is stated as a bound: a one-character declaration is
//!   invisible here. Two characters are not — `rw` is a recruitment, and
//!   `a_single_character_is_a_binder_and_a_two_character_identifier_is_a_recruitment` pins the cut
//!   from both sides on deposited material.
//!
//! **Declared bound: `have` is the only binding tactic this reading knows.** `obtain`, `rcases`,
//! `intro` and `set` also bind names, and a corpus containing them would have those names read as
//! recruitments. The present corpus contains none; widening the rule is a change to what the
//! reading means and belongs with a test on material that exercises it.
//!
//! **This reading was orthographic until 2026-08-08 and that made it blind to the production.** A
//! token counted as a recruitment only when namespaced or capitalized, and every declaration this
//! corpus generates is `snake_case`, so `exact_chart_carry` and `formal_carry` — the declarations
//! the generated proofs actually recruit — were invisible, and every artifact of one problem
//! returned the identical recruitment population whatever proof body the machine had composed. The
//! invariant a production/analysis loop returned was then a function of two hand-written preamble
//! strings and of nothing the production did. Sixty kernel invocations could not change it by one
//! bit. The rule above reads the proof body, and
//! `two_artifacts_of_one_declaration_with_different_bodies_recruit_different_populations` holds it
//! there.
//!
//! ## Three axes, declared, because the reading is not unique
//!
//! A deposit does not say what a 0-cell stands for, and the answer changes the invariants.
//!
//! - [`DerivationIdentity::ByDeclaration`] — one 0-cell per theorem *name*. This is what the
//!   deposited reader has always computed. Under it, **thirty-one artifacts proving one theorem are
//!   one vertex**, and `betti` at grade 1 is zero for *any* single-declaration deposit whose
//!   recruitment is a star.
//! - [`DerivationIdentity::ByRoute`] — one 0-cell per artifact, keyed `name#ordinal`.
//!
//! **`ByRoute` is not a refinement of `ByDeclaration`; it is a different relation, and that is a
//! declared property rather than a defect.** A route vertex is `name#ordinal` while a recruitment
//! of that same name lands on the bare `name` vertex, so under `ByRoute` no declaration is ever
//! recruited by another and the graph is forced **bipartite**. On a bipartite graph the oriented
//! and the unoriented incidence matrices have the same Smith normal form — a sign flip on one side
//! of the bipartition is unimodular — so **no `ByRoute` reading can see whether the boundary is a
//! difference at all.** Orientation is visible only where a declaration can be recruited by
//! another, which is `ByDeclaration`; see
//! `an_odd_recruitment_cycle_among_declarations_carries_one_cycle_and_no_torsion` and its
//! multiplicity twin.
//!
//! And the boundary coefficient:
//!
//! - [`RecruitmentCoefficient::Incidence`] — one recruitment, coefficient one. The boundary is then
//!   the incidence matrix of a graph, which is **totally unimodular**, so every invariant factor is
//!   one and **no reading under this coefficient can return torsion at any grade, for any
//!   deposit**. That is a theorem about the coefficient, not an observation about the corpus.
//! - [`RecruitmentCoefficient::Multiplicity`] — the coefficient is the exact number of times the
//!   source named the symbol. A symbol named three times cannot be un-named twice; the cokernel
//!   keeps that as torsion. Every coefficient is an exact [`ComparativeMultiplicity`]; nothing here
//!   is tuned, ranked, compared by magnitude, or floated.
//!
//! [`RecruitmentCoefficient::Multiplicity`] under [`DerivationIdentity::ByDeclaration`] is refused
//! **exactly when the merge it names actually happens** — when some declaration name carries more
//! than one artifact, so that collapsing them onto one vertex would *sum* their occurrence counts
//! and fold *how many artifacts were deposited* into a boundary coefficient. When every declaration
//! name carries exactly one artifact no summing occurs, the coefficient is that one artifact's own
//! count, and the reading is admitted. The refusal was unconditional until 2026-08-08, and the
//! unconditional form cost the module the one aperture on which orientation and torsion are visible
//! together.
//!
//! And the statement incidence:
//!
//! - [`StatementIncidence::Withheld`] — statements are lineage only. The reading is then **blind to
//!   statement identity**: two declarations proving unrelated statements that happen to share two
//!   recruited symbols close a grade-1 cycle exactly as two declarations of one statement do.
//! - [`StatementIncidence::Founded`] — each distinct statement is a 0-cell and each declaration
//!   vertex reaches its statement across a 1-cell. The cycles this attachment opens are exactly
//!   `sum over statements of (declarations reaching it - 1)` whenever the recruitment graph is
//!   already one component — **the independent routes to one result**, isolated from the
//!   shared-recruitment cycles that `Withheld` cannot distinguish them from.
//!
//! `blueprint/THE_ASSEMBLY.md:157` reads *"β₁ at grade 1 is the independent routes to one
//! result."* Of the statement-blind reading that is false, and measurably: two artifacts proving
//! two different statements, reached by one declaration each, return β₁ = 2. The design records
//! that refutation at `:160` and names the two admissible resolutions — *"either the circuit learns
//! to see statement identity and to exclude the codec's own structural keywords, or the quantity is
//! renamed to what it measures."* **This module does all three.** The statement-blind quantity is
//! named for what it counts, the codec's structural keywords are excluded, and
//! [`StatementIncidence::Founded`] is the reading in which the design's sentence is true. The
//! quantity that sentence names is [`DerivationCircuit::lineage_route_excess`], and
//! [`RouteCycleAgreement`] holds it against the homology of the two apertures so that neither can
//! drift from the other unnoticed.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::algebraic::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, GradedCausalComplex,
};
use crate::causal::EventId;
use crate::rebase_invariants::{rebase_invariants, GradeInvariants, PivotRule, RebaseInvariants};

/// The export codec's own structural vocabulary. These words are how a Lean file is written; they
/// name nothing the derivation recruited from its environment.
///
/// A **tactic** is not on this list and that is deliberate: `rw`, `simpa`, `nlinarith`, `assumption`
/// are declarations the environment supplies and the proof depends on, and reading them as
/// recruitments is what makes the reading depend on which proof body the machine composed.
pub const CODEC_KEYWORDS: [&str; 26] = [
    "at", "attribute", "by", "calc", "deriving", "do", "else", "end", "from", "fun", "have", "if",
    "import", "in", "let", "match", "mutual", "namespace", "open", "section", "set_option", "show",
    "suffices", "then", "using", "where",
];

/// Forms after which the next identifier is **founded by this file**, not recruited.
pub const DECLARATION_FORMERS: [&str; 12] = [
    "abbrev", "axiom", "class", "def", "example", "inductive", "instance", "lemma", "opaque",
    "structure", "theorem", "variable",
];

/// The formers that can **name** the derivation this reading returns.
///
/// Lean makes `lemma` and `theorem` one thing. [`read_derivation`] knows only the second, so a text
/// declaring more than one member of this list carries derivations the reading cannot name — and
/// the reading's response to that was to keep whichever `theorem` happened to be last. It is
/// refused instead; see [`DerivationApertureRefusal::PluralNamingDeclarations`].
pub const NAMING_FORMERS: [&str; 2] = ["lemma", "theorem"];

/// Modifiers Lean permits between column zero and a former. Declaration syntax, recruited by
/// nothing, and stepped over when the aperture counts what a text declares.
pub const NAMING_MODIFIERS: [&str; 6] = [
    "noncomputable",
    "private",
    "protected",
    "partial",
    "unsafe",
    "public",
];

/// Lean's comment openers. `/--` and `/-!` are `/-` with one further character, so two openers
/// cover all four forms, and `--` runs to end of line.
///
/// **The declared bound: string literals are not tracked.** A `--` inside a string is read as a
/// comment opener, which is the same bound [`crate::lean_development`] declares for the same
/// reason — carrying string state is a change to what the reading means.
pub const COMMENT_OPENERS: [&str; 2] = ["--", "/-"];

/// What one deposited artifact declares.
///
/// `recruited` is a **multiset**: the symbol and the exact number of times the source named it.
/// The reader's original carrier was a set, which discarded the count before any organ could ask
/// for it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Derivation {
    /// The theorem name the artifact declares.
    pub name: String,
    /// The statement text, normalized to single spaces and cut at `:=`. Two artifacts proving the
    /// same theorem share this exactly.
    pub statement: String,
    /// Every symbol the source named, with its exact occurrence count.
    pub recruited: BTreeMap<String, u32>,
}

impl Derivation {
    /// Every symbol named, without the counts. The support of the recruitment multiset.
    pub fn recruited_symbols(&self) -> BTreeSet<&str> {
        self.recruited.keys().map(String::as_str).collect()
    }
}

/// The identifier tokens of one line, in source order — **the rule that decides what a recruitment
/// is**, for this module and for every organ that restates it.
///
/// A token **begins** with a letter or `_`. It **continues** through letters, digits, `_`, `'`,
/// `!`, `?`, and a `.` that stands between two continuation characters. So `Nat.zero` is one token,
/// `00012` is none, `contrapose!` is one and not `contrapose`, `hab'` is one and not `hab`, and the
/// `.` of `(f x).1` opens nothing.
///
/// **Begin and continue are two classes, and that separation is the repair.** The rule was one
/// class applied by `split`, which made `'`, `!` and `?` separators: `getElem?_eq` returned as
/// `getElem` and `hab'` merged with `hab`. Widening the single class instead would have made
/// `!isEmpty` one token beginning with `!`, which the first-character filter then deletes whole —
/// so two classes is what the fix requires and not a wider one. Measured on the 103 artifacts this
/// reading admits, `contrapose!` occurs 5 times and was returned as `contrapose`; the generator
/// that writes it is `soma/life/src/lean_mathematics/ecology.rs:733`.
///
/// **Declared bound: a guillemet identifier `«a b»` is read as its interior words.** Lean permits
/// spaces inside `«…»` and no line-splitting rule can carry that; a scanner that could is a change
/// to what the reading means.
///
/// **This is `pub` because two organs restate it by hand and one of them claims they cannot
/// drift.** `collocation::lean_line_items` (`collocation.rs:944`) and
/// `derivation_capacitance::named_lines` (`derivation_capacitance.rs:530`) each carry a copy of the
/// old single-class expression; `collocation`'s own documentation says *"the three exclusions are
/// the same three and they are taken from the same two public tables, so the vocabularies cannot
/// drift apart"*, which was true of the vocabularies and never of the tokenizer, because the
/// tokenizer was not a public table. It is one now.
pub fn identifier_tokens(line: &str) -> impl Iterator<Item = &str> {
    fn continues(character: char) -> bool {
        character.is_alphanumeric()
            || character == '_'
            || character == '\''
            || character == '!'
            || character == '?'
    }

    let mut tokens = Vec::new();
    let mut index = 0usize;
    while index < line.len() {
        let character = line[index..].chars().next().expect("index is a boundary");
        if !(character.is_alphabetic() || character == '_') {
            index += character.len_utf8();
            continue;
        }
        let start = index;
        loop {
            while let Some(next) = line[index..].chars().next() {
                if !continues(next) {
                    break;
                }
                index += next.len_utf8();
            }
            if line[index..].starts_with('.')
                && line[index + 1..].chars().next().is_some_and(continues)
            {
                index += 1;
                continue;
            }
            break;
        }
        tokens.push(&line[start..index]);
    }
    tokens.into_iter()
}

/// **The aperture of [`read_derivation`], stated as the population of ways a text can fall outside
/// it.** Not a doc comment: a value, returned, carrying the material that put it there.
///
/// The reading has no comment lexer and one naming former. Against the machine's own export codec
/// — one artifact, one `theorem`, no comment text — those are not bounds at all, and the reading is
/// exact. Against a development a person wrote they are the whole story, and until 2026-08-09 the
/// reading answered anyway: over a 200-file mathlib sample it returned a `Derivation` for 139 of
/// them, named the file's **last** `theorem` in 137, and charged that one theorem a mean of 289
/// recruited symbols — up to 1,098 — including `Copyright`, `Authors`, `Apache`, `Released` and
/// `license` off the copyright header, in all 139.
///
/// `CLAUDE.md` §8: *"An organ used past its declared aperture is a defect even when it appears to
/// return."* It appeared to return. This type is that aperture made refusable.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize, thiserror::Error)]
#[serde(rename_all = "kebab-case")]
pub enum DerivationApertureRefusal {
    /// The text carries comment text, and the reading has no comment lexer — every word inside a
    /// `/- … -/` or after a `--` enters the recruitment multiset as though the derivation had named
    /// it. English prose charged to a theorem is not a recruitment population.
    #[error(
        "comment text: `{opener}` at line {first_line}, entered {opener_lines} times across \
         {total_lines} lines; this reading has no comment lexer and would charge that prose to \
         the theorem as recruitment"
    )]
    CommentText {
        /// The opener that first put the reading inside a comment.
        opener: String,
        /// One-based line it sits on.
        first_line: usize,
        /// How many lines carry an opener. A four-line `/- … -/` block carries one, so this counts
        /// **entries into** comment text and never comment lines; the reading has no lexer that
        /// could tell it where a block ends, which is the clause.
        opener_lines: usize,
        /// How many lines the text has, so the share is visible without re-reading it.
        total_lines: usize,
    },
    /// The text declares more than one of [`NAMING_FORMERS`]. The reading names one derivation, so
    /// the others would be silently absorbed — their statements discarded and their tokens charged
    /// to whichever survived.
    #[error(
        "{} naming declarations ({}); this reading names one and would absorb the rest",
        names.len(),
        names.join(", ")
    )]
    PluralNamingDeclarations {
        /// Every `theorem`/`lemma` the text declares, written `line:former name`, in source
        /// order. The population the reading would have thrown away.
        names: Vec<String>,
        /// The one the historical reading would have named: the last `theorem`.
        would_have_named: Option<String>,
    },
    /// The text declares no `theorem` at all. The reading's oldest refusal, given a name.
    #[error("no theorem is declared")]
    NoTheoremDeclared,
}

/// Every way `text` falls outside [`read_derivation`]'s aperture, in the declared order.
///
/// All of them, not the first, because a species count taken from a first-obstruction reading is a
/// measurement of the check order rather than of the material.
pub fn derivation_aperture_obstructions(text: &str) -> Vec<DerivationApertureRefusal> {
    let mut refusals = Vec::new();

    let mut comment_lines = 0usize;
    let mut first_comment: Option<(usize, &str)> = None;
    let mut total_lines = 0usize;
    for (index, line) in text.lines().enumerate() {
        total_lines += 1;
        let opener = COMMENT_OPENERS
            .iter()
            .filter_map(|opener| line.find(opener).map(|at| (at, *opener)))
            .min();
        if let Some((_, opener)) = opener {
            comment_lines += 1;
            first_comment.get_or_insert((index + 1, opener));
        }
    }
    if let Some((first_line, opener)) = first_comment {
        refusals.push(DerivationApertureRefusal::CommentText {
            opener: opener.to_owned(),
            first_line,
            opener_lines: comment_lines,
            total_lines,
        });
    }

    let naming = naming_declarations(text);
    if naming.len() > 1 {
        refusals.push(DerivationApertureRefusal::PluralNamingDeclarations {
            would_have_named: naming
                .iter()
                .rev()
                .find(|(_, former, _)| *former == "theorem")
                .map(|(_, _, name)| name.clone()),
            names: naming
                .iter()
                .map(|(line, former, name)| format!("{line}:{former} {name}"))
                .collect(),
        });
    }

    if !naming.iter().any(|(_, former, _)| *former == "theorem") {
        refusals.push(DerivationApertureRefusal::NoTheoremDeclared);
    }

    refusals
}

/// Every `theorem`/`lemma` the text declares, as `(one-based line, former, name)`.
///
/// A leading `@[…]` attribute bracket and the [`NAMING_MODIFIERS`] are stepped over, because a
/// `@[simp] theorem` is a theorem the reading would absorb exactly as silently as a bare one.
fn naming_declarations(text: &str) -> Vec<(usize, &'static str, String)> {
    let mut found = Vec::new();
    for (index, line) in text.lines().enumerate() {
        let mut rest = line.trim();
        if let Some(after) = rest.strip_prefix('@') {
            let Some(close) = after.find(']') else {
                continue;
            };
            rest = after[close + 1..].trim_start();
        }
        loop {
            let stepped = NAMING_MODIFIERS.iter().find_map(|modifier| {
                rest.strip_prefix(modifier)
                    .filter(|after| after.starts_with(char::is_whitespace))
            });
            match stepped {
                Some(after) => rest = after.trim_start(),
                None => break,
            }
        }
        for former in NAMING_FORMERS {
            let Some(after) = rest.strip_prefix(former) else {
                continue;
            };
            if !after.starts_with(char::is_whitespace) {
                continue;
            }
            let name = after
                .trim_start()
                .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\''))
                .next()
                .unwrap_or_default()
                .to_owned();
            if !name.is_empty() {
                found.push((index + 1, former, name));
            }
            break;
        }
    }
    found
}

/// Parse one Lean artifact into what it names and what it recruited, **or return the aperture
/// clause that refuses it**.
///
/// Deliberately structural and shallow: this reads what the file *declares*, not what it means. A
/// deeper reading would be a semantics claim, and the export codec's job is not to supply one. The
/// three exclusion rules — codec vocabulary, what the line founds, single-character binders — are
/// stated in the module documentation and each has a test that fails if it moves.
///
/// What is *not* in the module documentation, because a bound stated in prose is a bound nothing
/// can enforce, is [`DerivationApertureRefusal`]. A text outside the aperture returns the clause
/// that excludes it and no `Derivation` at all. For a development a person wrote — mathlib, or
/// `soma/formal` — the reader is [`crate::lean_development::read_development`], which opens every
/// top-level declaration, separates comment text, and returns what it set aside.
pub fn read_derivation_within_aperture(
    text: &str,
) -> Result<Derivation, DerivationApertureRefusal> {
    match derivation_aperture_obstructions(text).into_iter().next() {
        Some(refusal) => Err(refusal),
        // Inside the aperture the parse cannot fail: the `NoTheoremDeclared` clause has already
        // established that a `theorem` line is present for it to name.
        None => parse_within_aperture(text).ok_or(DerivationApertureRefusal::NoTheoremDeclared),
    }
}

/// [`read_derivation_within_aperture`] with the clause dropped.
///
/// Retained at this name and this signature because twelve drivers and six other modules call it,
/// almost all over the machine's own deposit, where no clause fires and the reading is exact —
/// measured at 103 of 103 artifacts under `standing/output`. `None` is now a
/// **refusal** and never a partial reading: nothing here returns a `Derivation` for material the
/// aperture excludes.
pub fn read_derivation(text: &str) -> Option<Derivation> {
    read_derivation_within_aperture(text).ok()
}

fn parse_within_aperture(text: &str) -> Option<Derivation> {
    let mut recruited: BTreeMap<String, u32> = BTreeMap::new();
    let mut name = None;
    let mut statement = None;

    for line in text.lines() {
        let trimmed = line.trim();

        if let Some(rest) = trimmed.strip_prefix("theorem ") {
            let mut parts = rest.splitn(2, ' ');
            name = parts.next().map(str::to_owned);
            statement = parts.next().map(|body| {
                body.split(":=")
                    .next()
                    .unwrap_or(body)
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
            });
        }

        // `end Soma` is the closing half of `namespace Soma`. It names nothing.
        if trimmed == "end" || trimmed.starts_with("end ") {
            continue;
        }

        // `have <bound> := <recruitment>` binds on the left.
        let read = if trimmed == "have" || trimmed.starts_with("have ") {
            match trimmed.split_once(":=") {
                Some((_, right)) => right,
                None => continue,
            }
        } else {
            trimmed
        };

        let mut founds_next = false;
        for token in identifier_tokens(read) {
            if founds_next {
                founds_next = false;
                continue;
            }
            if DECLARATION_FORMERS.contains(&token) {
                founds_next = true;
                continue;
            }
            if CODEC_KEYWORDS.contains(&token) {
                continue;
            }
            if token.chars().count() <= 1 {
                continue;
            }
            let slot = recruited.entry(token.to_owned()).or_insert(0u32);
            *slot = slot.saturating_add(1);
        }
    }

    Some(Derivation {
        name: name?,
        statement: statement.unwrap_or_default(),
        recruited,
    })
}

/// What a 0-cell stands for. Declared, because the deposit does not say and the answer moves the
/// invariants.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DerivationIdentity {
    /// One 0-cell per declared theorem name. Every artifact proving that theorem collapses onto it.
    ByDeclaration,
    /// One 0-cell per artifact, keyed by `name#ordinal` over the population's own read order.
    ByRoute,
}

/// What a recruitment 1-cell's boundary coefficient counts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RecruitmentCoefficient {
    /// One recruitment, coefficient one. Totally unimodular; torsion is identically empty.
    Incidence,
    /// The exact number of times the source named the symbol.
    Multiplicity,
}

/// Whether the statement a derivation reached is a 0-cell of the circuit or lineage only.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum StatementIncidence {
    /// Statements are carried in the route lineage and nowhere in the complex. The reading is
    /// blind to statement identity.
    Withheld,
    /// Each distinct statement is a 0-cell; each derivation vertex reaches its statement across a
    /// 1-cell of coefficient one.
    Founded,
}

/// The 0-cell key a statement takes under [`StatementIncidence::Founded`]. The prefix carries a
/// space and a `|`, neither of which occurs in a Lean identifier, so a statement vertex can never
/// collide with a recruited symbol.
pub fn statement_vertex_key(statement: &str) -> String {
    format!("|- {statement}")
}

/// The declared aperture of one reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CircuitAperture {
    pub identity: DerivationIdentity,
    pub coefficient: RecruitmentCoefficient,
    pub statements: StatementIncidence,
}

impl CircuitAperture {
    /// The reading `examples/derivation_atlas_reader.rs` has computed since it was written.
    pub const DEPOSITED_READER: Self = Self {
        identity: DerivationIdentity::ByDeclaration,
        coefficient: RecruitmentCoefficient::Incidence,
        statements: StatementIncidence::Withheld,
    };

    /// The same reading with the statements founded: the only aperture pair in which the routes to
    /// one result are separable from the shared-recruitment cycles.
    pub const STATEMENT_INCIDENT: Self = Self {
        identity: DerivationIdentity::ByDeclaration,
        coefficient: RecruitmentCoefficient::Incidence,
        statements: StatementIncidence::Founded,
    };

    /// One 0-cell per artifact.
    pub const PER_ROUTE: Self = Self {
        identity: DerivationIdentity::ByRoute,
        coefficient: RecruitmentCoefficient::Incidence,
        statements: StatementIncidence::Withheld,
    };

    /// One 0-cell per artifact, coefficients carrying the occurrence counts: the reading in which
    /// torsion is capable of being nonempty.
    pub const PER_ROUTE_MULTIPLICITY: Self = Self {
        identity: DerivationIdentity::ByRoute,
        coefficient: RecruitmentCoefficient::Multiplicity,
        statements: StatementIncidence::Withheld,
    };

    pub const DECLARED: [Self; 4] = [
        Self::DEPOSITED_READER,
        Self::STATEMENT_INCIDENT,
        Self::PER_ROUTE,
        Self::PER_ROUTE_MULTIPLICITY,
    ];
}

/// Why a reading was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivationAtlasRefusal {
    /// `Multiplicity` under `ByDeclaration` where the named declaration carries more than one
    /// artifact: merging them onto one vertex sums their occurrence counts, folding the deposited
    /// artifact population into a boundary coefficient.
    MultiplicityWouldSumRoutes { declaration: String, artifacts: usize },
    /// The complex refused a cell.
    Algebra(CausalAlgebraicError),
}

impl std::fmt::Display for DerivationAtlasRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MultiplicityWouldSumRoutes {
                declaration,
                artifacts,
            } => write!(
                formatter,
                "multiplicity coefficients under by-declaration identity would sum the {artifacts} \
                 artifacts of `{declaration}` onto one vertex, folding the deposited artifact \
                 population into a boundary coefficient"
            ),
            Self::Algebra(error) => write!(formatter, "{error}"),
        }
    }
}

impl std::error::Error for DerivationAtlasRefusal {}

impl From<CausalAlgebraicError> for DerivationAtlasRefusal {
    fn from(error: CausalAlgebraicError) -> Self {
        Self::Algebra(error)
    }
}

/// The grade-0 and grade-1 Betti numbers of a circuit, computed by union-find over the complex's
/// own 1-cell supports.
///
/// This is a **second implementation** of a quantity `rebase_invariants` obtains by integer matrix
/// reduction, and it is independent in the way §8 asks for: it reads `boundary.support()` and never
/// a coefficient, so it is orientation-blind by construction. A boundary whose two terms carry the
/// same sign is invisible to it and is *not* invisible to Smith normal form, so on any circuit
/// carrying an odd recruitment cycle the two disagree exactly when the incidence stops being a
/// difference. It is also blind to multiplicity, so it is only claimed against the
/// [`RecruitmentCoefficient::Incidence`] readings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpanningForestReading {
    pub vertices: usize,
    pub edges: usize,
    pub components: usize,
}

impl SpanningForestReading {
    pub const fn betti_0(&self) -> usize {
        self.components
    }

    /// `E - V + C`, which is never negative for a graph because a spanning forest of `C` components
    /// over `V` vertices has `V - C` edges and every edge beyond it closes a cycle.
    pub const fn betti_1(&self) -> usize {
        (self.edges + self.components).saturating_sub(self.vertices)
    }
}

/// The two readings of one quantity — *the independent routes to one result* — that
/// [`DerivationCircuit::route_cycle_agreement`] holds against each other.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RouteCycleAgreement {
    /// `betti_1(statements founded) - betti_1(statements withheld)`, taken from Smith normal form.
    pub homological: i64,
    /// `sum over statements of (declaration vertices reaching it - 1)`, taken from the route
    /// lineage the circuit already holds.
    pub lineage: i64,
    /// Whether the recruitment graph was already one component. Outside that aperture the statement
    /// attachment also *merges* components, and the two readings are not claimed equal.
    pub recruitment_connected: bool,
}

impl RouteCycleAgreement {
    /// The two readings agree, or the aperture in which they are claimed equal does not hold.
    pub const fn holds(&self) -> bool {
        !self.recruitment_connected || self.homological == self.lineage
    }
}

/// A derivation population founded as a graded complex, with the route population beside it.
#[derive(Clone, Debug)]
pub struct DerivationCircuit {
    aperture: CircuitAperture,
    complex: GradedCausalComplex,
    vertices: BTreeMap<String, CausalCellId>,
    recruitments: BTreeMap<(String, String), CausalCellId>,
    reaches: BTreeMap<(String, String), CausalCellId>,
    routes: BTreeMap<String, Vec<String>>,
}

impl DerivationCircuit {
    pub const fn aperture(&self) -> CircuitAperture {
        self.aperture
    }

    pub const fn complex(&self) -> &GradedCausalComplex {
        &self.complex
    }

    /// Every 0-cell: declarations produced, symbols recruited, and statements reached alike.
    pub const fn vertices(&self) -> &BTreeMap<String, CausalCellId> {
        &self.vertices
    }

    /// Every recruitment 1-cell, keyed by `(derivation vertex, recruited symbol)`.
    pub const fn recruitments(&self) -> &BTreeMap<(String, String), CausalCellId> {
        &self.recruitments
    }

    /// Every reach 1-cell, keyed by `(derivation vertex, statement)`. Empty under
    /// [`StatementIncidence::Withheld`].
    pub const fn reaches(&self) -> &BTreeMap<(String, String), CausalCellId> {
        &self.reaches
    }

    /// Statement to the derivation vertex of every artifact that reached it, in read order and
    /// **not deduplicated** — thirty-one artifacts of one theorem appear thirty-one times.
    pub const fn routes(&self) -> &BTreeMap<String, Vec<String>> {
        &self.routes
    }

    /// The artifact lineage behind one statement: every derivation vertex that reached it, in read
    /// order, with repetition.
    pub fn route_lineage(&self, statement: &str) -> &[String] {
        self.routes
            .get(statement)
            .map_or(&[] as &[String], Vec::as_slice)
    }

    pub fn statements(&self) -> BTreeSet<&str> {
        self.routes.keys().map(String::as_str).collect()
    }

    /// The distinct derivation vertices that reached a statement.
    pub fn vertices_reaching(&self, statement: &str) -> BTreeSet<&str> {
        self.routes
            .get(statement)
            .map(|reached| reached.iter().map(String::as_str).collect())
            .unwrap_or_default()
    }

    /// Statement to the distinct derivation vertices that reached it. The lineage's own account of
    /// the routes to each result, carried as a population.
    pub fn reaching_vertices(&self) -> BTreeMap<&str, BTreeSet<&str>> {
        self.routes
            .iter()
            .map(|(statement, reached)| {
                (
                    statement.as_str(),
                    reached.iter().map(String::as_str).collect(),
                )
            })
            .collect()
    }

    /// `sum over statements of (declaration vertices reaching it - 1)`, from the route lineage.
    ///
    /// This is the quantity `blueprint/THE_ASSEMBLY.md:129` names — the independent routes to one
    /// result — and it is *not* the grade-1 Betti number of the statement-blind reading. See
    /// [`Self::route_cycle_agreement`].
    pub fn lineage_route_excess(&self) -> usize {
        self.reaching_vertices()
            .values()
            .map(|reaching| reaching.len().saturating_sub(1))
            .sum()
    }

    /// Statements more than one **artifact** reached. Under `ByDeclaration` this can be plural
    /// while the complex sees one vertex, and that gap is the reader's oldest inconsistency.
    pub fn plural_route_statements(&self) -> BTreeSet<&str> {
        self.routes
            .iter()
            .filter(|(_, reached)| reached.len() > 1)
            .map(|(statement, _)| statement.as_str())
            .collect()
    }

    /// Statements more than one distinct **vertex** reached. This is the population that can close
    /// a grade-1 cycle.
    pub fn plural_vertex_statements(&self) -> BTreeSet<&str> {
        self.routes
            .iter()
            .filter(|(statement, _)| self.vertices_reaching(statement).len() > 1)
            .map(|(statement, _)| statement.as_str())
            .collect()
    }

    /// Statements exactly one vertex reached — the un-cross-checked population, and the target
    /// population a later production selects from when the reading is available.
    pub fn single_vertex_statements(&self) -> BTreeSet<&str> {
        self.routes
            .keys()
            .map(String::as_str)
            .filter(|statement| self.vertices_reaching(statement).len() == 1)
            .collect()
    }

    /// The un-cross-checked statements with the artifact lineage behind each, **largest lineage
    /// first**, ties broken by the statement text so the order carries no read-order frame.
    ///
    /// This is a population and not a choice: a production selecting a target takes the first entry
    /// and keeps the rest. The order is the reading's own: a statement no second declaration has
    /// ever reached is the one worth cross-checking, and the size of its lineage is the machine's
    /// own evidence that a path to it exists.
    pub fn single_vertex_statements_by_lineage(&self) -> Vec<(&str, &[String])> {
        let mut ranked: Vec<(&str, &[String])> = self
            .single_vertex_statements()
            .into_iter()
            .map(|statement| (statement, self.route_lineage(statement)))
            .collect();
        ranked.sort_by(|left, right| {
            right
                .1
                .len()
                .cmp(&left.1.len())
                .then_with(|| left.0.cmp(right.0))
        });
        ranked
    }

    /// Grade-0 and grade-1 Betti numbers by union-find over this circuit's own 1-cell supports.
    /// A second implementation; see [`SpanningForestReading`].
    pub fn spanning_forest_reading(&self) -> SpanningForestReading {
        let vertices: Vec<CausalCellId> = self
            .complex()
            .cells()
            .values()
            .filter(|cell| cell.grade == 0)
            .map(|cell| cell.id)
            .collect();
        let index: BTreeMap<CausalCellId, usize> = vertices
            .iter()
            .enumerate()
            .map(|(slot, id)| (*id, slot))
            .collect();
        let mut parent: Vec<usize> = (0..vertices.len()).collect();

        fn root(parent: &mut Vec<usize>, mut node: usize) -> usize {
            while parent[node] != node {
                parent[node] = parent[parent[node]];
                node = parent[node];
            }
            node
        }

        let mut edges = 0usize;
        for cell in self.complex().cells().values() {
            if cell.grade != 1 {
                continue;
            }
            edges += 1;
            let mut joined: Option<usize> = None;
            for endpoint in cell.boundary.support() {
                let Some(slot) = index.get(&endpoint).copied() else {
                    continue;
                };
                match joined {
                    None => joined = Some(root(&mut parent, slot)),
                    Some(left) => {
                        let right = root(&mut parent, slot);
                        if left != right {
                            parent[right] = left;
                        }
                    }
                }
            }
        }

        let components = (0..vertices.len())
            .map(|slot| root(&mut parent, slot))
            .collect::<BTreeSet<usize>>()
            .len();
        SpanningForestReading {
            vertices: vertices.len(),
            edges,
            components,
        }
    }

    pub fn invariants(&self, rule: PivotRule) -> Result<RebaseInvariants, CausalAlgebraicError> {
        rebase_invariants(&self.complex, rule)
    }
}

fn betti_at(invariants: &RebaseInvariants, grade: u32) -> usize {
    invariants
        .grades
        .iter()
        .find(|carried| carried.grade == grade)
        .map_or(0, |carried| carried.betti)
}

/// Found the circuit a derivation population presents under a declared aperture.
pub fn found_circuit(
    derivations: &[Derivation],
    aperture: CircuitAperture,
) -> Result<DerivationCircuit, DerivationAtlasRefusal> {
    if aperture.identity == DerivationIdentity::ByDeclaration
        && aperture.coefficient == RecruitmentCoefficient::Multiplicity
    {
        let mut artifacts_per_name: BTreeMap<&str, usize> = BTreeMap::new();
        for derivation in derivations {
            *artifacts_per_name
                .entry(derivation.name.as_str())
                .or_default() += 1;
        }
        if let Some((declaration, artifacts)) = artifacts_per_name
            .into_iter()
            .find(|(_, artifacts)| *artifacts > 1)
        {
            return Err(DerivationAtlasRefusal::MultiplicityWouldSumRoutes {
                declaration: declaration.to_owned(),
                artifacts,
            });
        }
    }

    let keys: Vec<String> = derivations
        .iter()
        .enumerate()
        .map(|(ordinal, derivation)| match aperture.identity {
            DerivationIdentity::ByDeclaration => derivation.name.clone(),
            DerivationIdentity::ByRoute => format!("{}#{ordinal}", derivation.name),
        })
        .collect();

    // Every 0-cell: the derivation vertices, every symbol any artifact named, and — under a founded
    // statement incidence — every statement any artifact reached.
    let mut vertex_names: BTreeSet<String> = keys.iter().cloned().collect();
    for derivation in derivations {
        vertex_names.extend(derivation.recruited.keys().cloned());
    }
    if aperture.statements == StatementIncidence::Founded {
        for derivation in derivations {
            vertex_names.insert(statement_vertex_key(&derivation.statement));
        }
    }

    // The recruitment multiset each derivation vertex carries. A declaration never recruits itself.
    let mut recruitment: BTreeMap<String, BTreeMap<String, u32>> = BTreeMap::new();
    for (key, derivation) in keys.iter().zip(derivations) {
        let slot = recruitment.entry(key.clone()).or_default();
        for (symbol, count) in &derivation.recruited {
            if symbol == &derivation.name {
                continue;
            }
            let carried = slot.entry(symbol.clone()).or_insert(0u32);
            *carried = carried.saturating_add(*count);
        }
    }

    // Which derivation vertex reached which statement, deduplicated: a declaration reaches a
    // statement once however many artifacts carried it there. The artifact count is lineage and
    // stays in `routes`; folding it into a boundary would be the same contaminant the multiplicity
    // refusal above names.
    let mut reached: BTreeSet<(String, String)> = BTreeSet::new();
    if aperture.statements == StatementIncidence::Founded {
        for (key, derivation) in keys.iter().zip(derivations) {
            reached.insert((key.clone(), derivation.statement.clone()));
        }
    }

    let mut complex = GradedCausalComplex::default();
    let mut occasion = 0u64;
    let mut vertices: BTreeMap<String, CausalCellId> = BTreeMap::new();
    for name in &vertex_names {
        occasion += 1;
        let id = complex.found_cell(
            name.clone(),
            BTreeSet::from([EventId(occasion)]),
            0,
            CausalChain::default(),
        )?;
        vertices.insert(name.clone(), id);
    }

    let mut recruitments: BTreeMap<(String, String), CausalCellId> = BTreeMap::new();
    for (key, symbols) in &recruitment {
        for (symbol, count) in symbols {
            let coefficient = match aperture.coefficient {
                RecruitmentCoefficient::Incidence => 1u32,
                RecruitmentCoefficient::Multiplicity => *count,
            };
            if coefficient == 0 {
                continue;
            }
            let mut boundary = CausalChain::default();
            boundary.add_term(vertices[key], ComparativeMultiplicity::positive(coefficient));
            boundary.add_term(
                vertices[symbol],
                ComparativeMultiplicity::negative(coefficient),
            );
            occasion += 1;
            let id = complex.found_cell(
                format!("{key}<-{symbol}"),
                BTreeSet::from([EventId(occasion)]),
                1,
                boundary,
            )?;
            recruitments.insert((key.clone(), symbol.clone()), id);
        }
    }

    let mut reaches: BTreeMap<(String, String), CausalCellId> = BTreeMap::new();
    for (key, statement) in &reached {
        let target = &vertices[&statement_vertex_key(statement)];
        let mut boundary = CausalChain::default();
        boundary.add_term(vertices[key], ComparativeMultiplicity::positive(1u32));
        boundary.add_term(*target, ComparativeMultiplicity::negative(1u32));
        occasion += 1;
        let id = complex.found_cell(
            format!("{key}|-{statement}"),
            BTreeSet::from([EventId(occasion)]),
            1,
            boundary,
        )?;
        reaches.insert((key.clone(), statement.clone()), id);
    }

    let mut routes: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for (key, derivation) in keys.iter().zip(derivations) {
        routes
            .entry(derivation.statement.clone())
            .or_default()
            .push(key.clone());
    }

    Ok(DerivationCircuit {
        aperture,
        complex,
        vertices,
        recruitments,
        reaches,
        routes,
    })
}

/// Read one population under a statement-blind aperture and its statement-founded twin, and return
/// the two accounts of the routes to one result.
///
/// The homological account is the grade-1 Betti difference the statement attachment opens; the
/// lineage account is [`DerivationCircuit::lineage_route_excess`]. They are computed from disjoint
/// material — one by Smith normal form over an integer boundary matrix, the other by counting
/// distinct vertices in the route lineage — and a founding that attached a derivation to the wrong
/// statement vertex, or founded a statement no derivation reached, breaks the agreement.
pub fn route_cycle_agreement(
    derivations: &[Derivation],
    identity: DerivationIdentity,
    rule: PivotRule,
) -> Result<RouteCycleAgreement, DerivationAtlasRefusal> {
    let withheld = found_circuit(
        derivations,
        CircuitAperture {
            identity,
            coefficient: RecruitmentCoefficient::Incidence,
            statements: StatementIncidence::Withheld,
        },
    )?;
    let founded = found_circuit(
        derivations,
        CircuitAperture {
            identity,
            coefficient: RecruitmentCoefficient::Incidence,
            statements: StatementIncidence::Founded,
        },
    )?;
    let blind = withheld.invariants(rule)?;
    let seeing = founded.invariants(rule)?;
    Ok(RouteCycleAgreement {
        homological: betti_at(&seeing, 1) as i64 - betti_at(&blind, 1) as i64,
        lineage: withheld.lineage_route_excess() as i64,
        recruitment_connected: betti_at(&blind, 0) == 1,
    })
}

/// Which field of one grade's invariants moved.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum MovedField {
    Cells,
    BoundaryRank,
    FillingRank,
    Betti,
    Torsion,
}

/// One grade's share of the difference between two readings.
///
/// Both sides are carried whole. Nothing here is a delta, a ratio, or a verdict; a caller that
/// wants the movement reads both sides and keeps them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradeMovement {
    pub grade: u32,
    pub before: Option<GradeInvariants>,
    pub after: Option<GradeInvariants>,
}

impl GradeMovement {
    /// The grade exists after and did not before.
    pub const fn founded(&self) -> bool {
        self.before.is_none() && self.after.is_some()
    }

    /// The grade existed before and does not after.
    pub const fn withdrawn(&self) -> bool {
        self.before.is_some() && self.after.is_none()
    }

    /// Which fields differ. A grade present on only one side differs in every field.
    pub fn fields_moved(&self) -> BTreeSet<MovedField> {
        let every = BTreeSet::from([
            MovedField::Cells,
            MovedField::BoundaryRank,
            MovedField::FillingRank,
            MovedField::Betti,
            MovedField::Torsion,
        ]);
        let (Some(before), Some(after)) = (&self.before, &self.after) else {
            return every;
        };
        let mut moved = BTreeSet::new();
        if before.cells != after.cells {
            moved.insert(MovedField::Cells);
        }
        if before.boundary_rank != after.boundary_rank {
            moved.insert(MovedField::BoundaryRank);
        }
        if before.filling_rank != after.filling_rank {
            moved.insert(MovedField::FillingRank);
        }
        if before.betti != after.betti {
            moved.insert(MovedField::Betti);
        }
        if before.torsion != after.torsion {
            moved.insert(MovedField::Torsion);
        }
        moved
    }
}

/// The difference between two invariant readings, as a population.
///
/// `moved` is the artifact. `is_still` is a predicate over it and carries no information the population
/// does not; it exists so a caller may branch without discarding what it branched on.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InvariantMovement {
    moved: Vec<GradeMovement>,
}

impl InvariantMovement {
    pub fn moved(&self) -> &[GradeMovement] {
        &self.moved
    }

    pub fn is_still(&self) -> bool {
        self.moved.is_empty()
    }

    pub fn grades_moved(&self) -> BTreeSet<u32> {
        self.moved.iter().map(|grade| grade.grade).collect()
    }

    pub fn fields_moved(&self) -> BTreeSet<MovedField> {
        self.moved
            .iter()
            .flat_map(|grade| grade.fields_moved())
            .collect()
    }
}

/// What a production moved in the machine's own reading of its deposits.
///
/// Pairs the two readings by grade **number**, not by position, so a reading that gained a grade is
/// visible as a founded grade rather than as a silent re-alignment. The law this owes:
/// `movement.is_still()` and `rebase_invariants::invariants_agree` must return the same verdict,
/// and `movement_and_agreement_are_one_quantity` is what holds it there.
pub fn invariant_movement(before: &RebaseInvariants, after: &RebaseInvariants) -> InvariantMovement {
    let mut left: BTreeMap<u32, &GradeInvariants> = BTreeMap::new();
    for grade in &before.grades {
        left.insert(grade.grade, grade);
    }
    let mut right: BTreeMap<u32, &GradeInvariants> = BTreeMap::new();
    for grade in &after.grades {
        right.insert(grade.grade, grade);
    }
    let grades: BTreeSet<u32> = left.keys().chain(right.keys()).copied().collect();

    let moved = grades
        .into_iter()
        .map(|grade| GradeMovement {
            grade,
            before: left.get(&grade).map(|grade| (*grade).clone()),
            after: right.get(&grade).map(|grade| (*grade).clone()),
        })
        .filter(|movement| movement.before != movement.after)
        .collect();

    InvariantMovement { moved }
}

/// What a production moved in the route population.
///
/// Every field is a population. Nothing is counted on the way out; a caller that wants a count
/// takes it from the population it was handed.
///
/// **`deepened_routes` is the lineage frame and it is the reason this organ is not blind to the
/// machine's actual production mode.** Every other field here reads `vertices_reaching`, a
/// deduplicated set, so under `ByDeclaration` a production depositing a thirty-second artifact of
/// an already-named declaration moved nothing any of them can see. That is
/// `blueprint/THE_ASSEMBLY.md`'s named failure verbatim — *"keeps the support and drops the
/// lineage"* — and `deepened_routes` reads the ordered, non-deduplicated `routes()` the circuit
/// already holds.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RouteMovement {
    founded_statements: BTreeSet<String>,
    withdrawn_statements: BTreeSet<String>,
    founded_routes: BTreeMap<String, BTreeSet<String>>,
    deepened_routes: BTreeMap<String, BTreeMap<String, usize>>,
    became_plural: BTreeSet<String>,
}

impl RouteMovement {
    /// Statements the later reading carries and the earlier one did not.
    pub const fn founded_statements(&self) -> &BTreeSet<String> {
        &self.founded_statements
    }

    /// Statements the earlier reading carried and the later one does not.
    pub const fn withdrawn_statements(&self) -> &BTreeSet<String> {
        &self.withdrawn_statements
    }

    /// Statement to the derivation vertices that reached it in the later reading and not in the
    /// earlier one.
    pub const fn founded_routes(&self) -> &BTreeMap<String, BTreeSet<String>> {
        &self.founded_routes
    }

    /// Statement to the derivation vertex to how many **further artifacts** reached that statement
    /// through that vertex in the later reading. The support may be identical on both sides and
    /// this still be non-empty; that is what it is for.
    pub const fn deepened_routes(&self) -> &BTreeMap<String, BTreeMap<String, usize>> {
        &self.deepened_routes
    }

    /// Statements that one vertex reached before and more than one reaches after. This is the
    /// population that can have opened a grade-1 cycle.
    pub const fn became_plural(&self) -> &BTreeSet<String> {
        &self.became_plural
    }

    pub fn is_still(&self) -> bool {
        self.founded_statements.is_empty()
            && self.withdrawn_statements.is_empty()
            && self.founded_routes.is_empty()
            && self.deepened_routes.is_empty()
            && self.became_plural.is_empty()
    }
}

fn lineage_multiplicity<'a>(circuit: &'a DerivationCircuit, statement: &str) -> BTreeMap<&'a str, usize> {
    let mut carried: BTreeMap<&str, usize> = BTreeMap::new();
    for vertex in circuit.route_lineage(statement) {
        *carried.entry(vertex.as_str()).or_default() += 1;
    }
    carried
}

pub fn route_movement(before: &DerivationCircuit, after: &DerivationCircuit) -> RouteMovement {
    let earlier = before.statements();
    let later = after.statements();

    let founded_statements: BTreeSet<String> = later
        .difference(&earlier)
        .map(|statement| (*statement).to_owned())
        .collect();
    let withdrawn_statements: BTreeSet<String> = earlier
        .difference(&later)
        .map(|statement| (*statement).to_owned())
        .collect();

    let mut founded_routes: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut deepened_routes: BTreeMap<String, BTreeMap<String, usize>> = BTreeMap::new();
    let mut became_plural: BTreeSet<String> = BTreeSet::new();
    for statement in &later {
        let carried = before.vertices_reaching(statement);
        let reaching = after.vertices_reaching(statement);
        let founded: BTreeSet<String> = reaching
            .difference(&carried)
            .map(|vertex| (*vertex).to_owned())
            .collect();
        if !founded.is_empty() {
            founded_routes.insert((*statement).to_owned(), founded);
        }
        if carried.len() <= 1 && reaching.len() > 1 {
            became_plural.insert((*statement).to_owned());
        }

        // The lineage frame: the ordered, non-deduplicated route population, as a multiset.
        let was = lineage_multiplicity(before, statement);
        let now = lineage_multiplicity(after, statement);
        let mut deepened: BTreeMap<String, usize> = BTreeMap::new();
        for (vertex, reached) in now {
            let further = reached.saturating_sub(was.get(vertex).copied().unwrap_or(0));
            if further > 0 {
                deepened.insert(vertex.to_owned(), further);
            }
        }
        if !deepened.is_empty() {
            deepened_routes.insert((*statement).to_owned(), deepened);
        }
    }

    RouteMovement {
        founded_statements,
        withdrawn_statements,
        founded_routes,
        deepened_routes,
        became_plural,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rebase_invariants::invariants_agree;
    use num_bigint::BigInt;

    // ---------------------------------------------------------------- verbatim deposited material
    //
    // These are byte-for-byte copies of artifacts under `standing/output/`. They are quoted rather
    // than read from disk so the test carries no filesystem frame, and they are real production
    // rather than invented material so the readings below are readings of the machine's own output.

    /// `standing/output/lean-proof-production/carrier-transport-00000.lean`
    const PRODUCTION_ROUTE_A: &str = "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n";

    /// `standing/output/lean-proof-production/carrier-transport-00012.lean` — a genuinely different
    /// proof: three `apply` steps rather than a bare `assumption`.
    const PRODUCTION_ROUTE_B: &str = "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  apply exact_chart_carry\n  apply exact_chart_carry\n  apply exact_chart_carry\n  assumption\nend Soma\n";

    /// `standing/output/lean-kernel-witness/carrier_transport-00000.lean`
    const WITNESS_CARRIER_TRANSPORT: &str = "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem carrier_transport (h : P) : exactCarrier P := h\nend Soma\n";

    /// `standing/output/agentic-research-kernel/formal_carry-00000.lean` — a **different theorem
    /// name** carrying the **same normalized statement** as `WITNESS_CARRIER_TRANSPORT`.
    const RESEARCH_FORMAL_CARRY: &str = "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem formal_carry (h : P) : exactCarrier P := by\n  assumption\nend Soma\n";

    /// `standing/output/lean-kernel-witness/every_receiver_agrees-00000.lean`
    const WITNESS_EVERY_RECEIVER_AGREES: &str =
        "namespace Soma\ntheorem every_receiver_agrees (a b : Nat) : a = b := rfl\nend Soma\n";

    /// `standing/output/agentic-research-kernel/formal_carry-00003.lean` with its recruited
    /// declaration changed to the one it declares. **Constructed, and the construction is the
    /// point:** no artifact in the present deposit names its own declaration, so the
    /// self-recruitment guard has no deposited witness. The body shape is verbatim — the generator
    /// composes `rw [<declaration>]` paths out of the problem's declaration star, and a problem
    /// whose star contains its own name emits exactly this.
    const SELF_RECRUITING_ROUTE: &str = "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)\ntheorem formal_carry (h : P) : exactCarrier P := by\n  rw [formal_carry]\n  assumption\nend Soma\n";

    fn read(text: &str) -> Derivation {
        read_derivation(text).expect("a deposited artifact declares a theorem")
    }

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

    fn torsion_at(invariants: &RebaseInvariants, grade: u32) -> Vec<BigInt> {
        invariants
            .grades
            .iter()
            .find(|carried| carried.grade == grade)
            .map(|carried| carried.torsion.clone())
            .unwrap_or_default()
    }

    fn circuit_of(derivations: &[Derivation], aperture: CircuitAperture) -> DerivationCircuit {
        found_circuit(derivations, aperture).expect("the aperture is admissible")
    }

    fn invariants_of(derivations: &[Derivation], aperture: CircuitAperture) -> RebaseInvariants {
        circuit_of(derivations, aperture)
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads")
    }

    /// Two declarations of one statement, sharing `shared` recruited symbols and one private symbol
    /// each. This is the only fixture shape in which the grade-1 law can be *varied*, which is the
    /// point: a fixture whose shared population cannot change cannot distinguish the law from a
    /// constant.
    fn two_declarations_sharing(shared: u32) -> Vec<Derivation> {
        let mut left: Vec<(String, u32)> = vec![("PrivateLeft".to_owned(), 1)];
        let mut right: Vec<(String, u32)> = vec![("PrivateRight".to_owned(), 1)];
        for index in 0..shared {
            left.push((format!("Shared{index}"), 1));
            right.push((format!("Shared{index}"), 1));
        }
        vec![
            Derivation {
                name: "alpha".to_owned(),
                statement: "one statement".to_owned(),
                recruited: left.into_iter().collect(),
            },
            Derivation {
                name: "beta".to_owned(),
                statement: "one statement".to_owned(),
                recruited: right.into_iter().collect(),
            },
        ]
    }

    /// The same population with the second declaration proving something else. Everything else —
    /// names, recruitment, counts — is identical, so any reading that differs between the two
    /// differs *because of statement identity and nothing else*.
    fn two_declarations_of_two_statements(shared: u32) -> Vec<Derivation> {
        let mut population = two_declarations_sharing(shared);
        population[1].statement = "another statement".to_owned();
        population
    }

    // ---------------------------------------------------------------- the parse

    #[test]
    fn read_derivation_returns_the_name_the_statement_and_the_exact_recruitment_counts() {
        let carried = read(PRODUCTION_ROUTE_A);
        assert_eq!(carried.name, "carrier_transport");
        assert_eq!(carried.statement, "(P : Prop) (h : P) : exactCarrier P");
        assert_eq!(
            carried.recruited,
            BTreeMap::from([
                ("KernelWitness".to_owned(), 1),
                ("Soma".to_owned(), 1),
                ("Prop".to_owned(), 1),
                ("exactCarrier".to_owned(), 1),
                ("assumption".to_owned(), 1),
            ])
        );
    }

    #[test]
    fn a_source_declaring_no_theorem_is_not_a_derivation() {
        assert_eq!(read_derivation("namespace Soma\nend Soma\n"), None);
        assert_eq!(
            read_derivation_within_aperture("namespace Soma\nend Soma\n"),
            Err(DerivationApertureRefusal::NoTheoremDeclared)
        );
    }

    // ---------------------------------------------------------------- the aperture

    /// `Mathlib/Algebra/Order/Group/Bounds.lean`, byte for byte, from the toolchain this repository
    /// already vendors. Quoted rather than read from disk so the test carries no filesystem frame,
    /// exactly as the deposited fixtures above are.
    ///
    /// It is here because it is **material that made the reading lie**: a copyright block, a module
    /// docstring, and four theorems, of which the reading named the fourth and charged it the other
    /// three plus the header.
    const MATHLIB_BOUNDS: &str = r#"/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

public section

section LinearOrderedAddCommGroup

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] {s : Set α} {a ε : α}

theorem IsGLB.exists_between_self_add (h : IsGLB s a) (hε : 0 < ε) : ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
  h.exists_between <| lt_add_of_pos_right _ hε

theorem IsGLB.exists_between_self_add' (h : IsGLB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a < b ∧ b < a + ε :=
  h.exists_between' h₂ <| lt_add_of_pos_right _ hε

theorem IsLUB.exists_between_sub_self (h : IsLUB s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
  h.exists_between <| sub_lt_self _ hε

theorem IsLUB.exists_between_sub_self' (h : IsLUB s a) (h₂ : a ∉ s) (hε : 0 < ε) :
    ∃ b ∈ s, a - ε < b ∧ b < a :=
  h.exists_between' h₂ <| sub_lt_self _ hε

end LinearOrderedAddCommGroup
"#;

    #[test]
    fn a_real_mathlib_file_is_refused_by_name_rather_than_read_as_its_last_theorem() {
        assert_eq!(read_derivation(MATHLIB_BOUNDS), None);

        let refusals = derivation_aperture_obstructions(MATHLIB_BOUNDS);
        assert_eq!(refusals.len(), 2, "{refusals:?}");

        // The copyright block opens on line one and the reading has no lexer for it. Without the
        // clause, `Copyright`, `Johannes`, `Apache`, `Released`, `LICENSE`, `Authors` and the
        // module docstring's English entered the recruitment multiset of a theorem.
        match &refusals[0] {
            DerivationApertureRefusal::CommentText {
                opener,
                first_line,
                opener_lines,
                total_lines,
            } => {
                assert_eq!(opener, "/-");
                assert_eq!(*first_line, 1);
                // The copyright block and the module docstring. A `-/` closer carries neither
                // opener, which is exactly why the reading cannot be given a comment rule here.
                assert_eq!(*opener_lines, 2);
                assert_eq!(*total_lines, 36);
            }
            other => panic!("{other:?}"),
        }

        // Four theorems. The reading names one, and the one it named is exhibited beside the
        // population it would have absorbed, so the refusal carries the fiction it replaced.
        match &refusals[1] {
            DerivationApertureRefusal::PluralNamingDeclarations {
                names,
                would_have_named,
            } => {
                assert_eq!(
                    names,
                    &[
                        "22:theorem IsGLB.exists_between_self_add".to_owned(),
                        "25:theorem IsGLB.exists_between_self_add'".to_owned(),
                        "29:theorem IsLUB.exists_between_sub_self".to_owned(),
                        "32:theorem IsLUB.exists_between_sub_self'".to_owned(),
                    ]
                );
                assert_eq!(
                    would_have_named.as_deref(),
                    Some("IsLUB.exists_between_sub_self'")
                );
            }
            other => panic!("{other:?}"),
        }
    }

    /// The distinguishing word, in `CLAUDE.md` §8's sense: one line separates a return from a
    /// refusal, and the material either side of it is the machine's own deposited artifact. A gate
    /// that cannot come apart on its declared material has not gated anything.
    #[test]
    fn one_comment_line_separates_a_deposited_artifact_from_its_own_refusal() {
        let admitted = read_derivation_within_aperture(PRODUCTION_ROUTE_A)
            .expect("the deposit is inside the aperture");
        assert_eq!(admitted.name, "carrier_transport");

        let commented = format!("-- composed by the export codec\n{PRODUCTION_ROUTE_A}");
        match read_derivation_within_aperture(&commented) {
            Err(DerivationApertureRefusal::CommentText {
                opener, first_line, ..
            }) => {
                assert_eq!(opener, "--");
                assert_eq!(first_line, 1);
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(read_derivation(&commented), None);
    }

    #[test]
    fn a_lemma_beside_a_theorem_is_a_naming_population_this_reading_cannot_name() {
        // `lemma` and `theorem` are one thing in Lean and this reading knows the second. Two
        // naming declarations are two derivations; it returns one, so it returns neither.
        let two = "namespace Soma\nlemma helper (h : P) : P := h\ntheorem carried (h : P) : P := helper h\nend Soma\n";
        match read_derivation_within_aperture(two) {
            Err(DerivationApertureRefusal::PluralNamingDeclarations {
                names,
                would_have_named,
            }) => {
                assert_eq!(
                    names,
                    &[
                        "2:lemma helper".to_owned(),
                        "3:theorem carried".to_owned()
                    ]
                );
                assert_eq!(would_have_named.as_deref(), Some("carried"));
            }
            other => panic!("{other:?}"),
        }

        // And the control: the same text with the lemma removed is admitted, so the clause is
        // firing on the plurality and not on anything else in the material.
        let one = "namespace Soma\ntheorem carried (h : P) : P := helper h\nend Soma\n";
        assert_eq!(
            read_derivation_within_aperture(one)
                .expect("one naming declaration")
                .name,
            "carried"
        );
    }

    /// An attribute bracket and a modifier do not hide a declaration from the clause. `@[simp]
    /// theorem` and `private theorem` are theorems the reading would absorb exactly as silently as
    /// a bare one.
    #[test]
    fn an_attribute_or_a_modifier_does_not_hide_a_naming_declaration_from_the_clause() {
        let decorated = "theorem carried (h : P) : P := h\n@[simp] theorem marked (h : P) : P := h\nprivate theorem hidden (h : P) : P := h\n";
        match read_derivation_within_aperture(decorated) {
            Err(DerivationApertureRefusal::PluralNamingDeclarations { names, .. }) => {
                assert_eq!(names.len(), 3, "{names:?}");
                assert!(names[1].ends_with("theorem marked"), "{names:?}");
                assert!(names[2].ends_with("theorem hidden"), "{names:?}");
            }
            other => panic!("{other:?}"),
        }
    }

    /// The prime, the bang and the question mark are **continuations**, and the witness is the
    /// machine's own production.
    ///
    /// `soma/life/src/lean_mathematics/ecology.rs:733` writes `"by\n  contrapose! {}\n  exact
    /// {application}"`, so `contrapose!` occurs 5 times across the 103 artifacts under
    /// `standing/output` and the reading returned `contrapose` for every one of them. The other two
    /// characters carry no witness in the present deposit and are declared here rather than left to
    /// be discovered: they are exercised by material this test supplies, so the rule is not a law
    /// that returns zero.
    #[test]
    fn a_prime_a_bang_and_a_question_mark_continue_an_identifier_rather_than_ending_it() {
        let produced = read(
            "namespace Soma\ntheorem formal_carry (h : P) : exactCarrier P := by\n  contrapose! exact_chart_carry\n  assumption\nend Soma\n",
        );
        assert_eq!(produced.recruited.get("contrapose!"), Some(&1));
        assert_eq!(produced.recruited.get("contrapose"), None);

        let declared = read(
            "namespace Soma\ntheorem formal_carry (h : P) : exactCarrier P := by\n  rw [getElem?_eq, hab', hab]\n  assumption\nend Soma\n",
        );
        assert_eq!(declared.recruited.get("getElem?_eq"), Some(&1));
        assert_eq!(declared.recruited.get("getElem"), None);
        // `hab` and `hab'` are two symbols, not one named twice. Under
        // `RecruitmentCoefficient::Multiplicity` the difference is a boundary coefficient.
        assert_eq!(declared.recruited.get("hab'"), Some(&1));
        assert_eq!(declared.recruited.get("hab"), Some(&1));

        // A token that BEGINS with `!` or `?` is not an identifier, and widening the single split
        // class rather than separating begin from continue would have deleted the name inside it.
        let prefixed = identifier_tokens("  exact !isEmpty ?goal").collect::<Vec<_>>();
        assert_eq!(prefixed, vec!["exact", "isEmpty", "goal"]);

        // And the `.` still joins only between two continuations.
        let projected = identifier_tokens("(f x).1 Nat.zero trailing.").collect::<Vec<_>>();
        assert_eq!(projected, vec!["f", "x", "Nat.zero", "trailing"]);
    }


    /// The negative control the clause needs: every artifact the machine's own codec deposits is
    /// inside the aperture and reads exactly as it always did. A refusal that refused the deposit
    /// would have replaced a fiction with a silence.
    #[test]
    fn every_deposited_artifact_stays_inside_the_declared_aperture() {
        for artifact in [
            PRODUCTION_ROUTE_A,
            PRODUCTION_ROUTE_B,
            WITNESS_CARRIER_TRANSPORT,
            RESEARCH_FORMAL_CARRY,
            WITNESS_EVERY_RECEIVER_AGREES,
            SELF_RECRUITING_ROUTE,
        ] {
            assert_eq!(
                derivation_aperture_obstructions(artifact),
                Vec::new(),
                "{artifact}"
            );
            assert!(read_derivation(artifact).is_some(), "{artifact}");
        }
    }

    #[test]
    fn the_codec_scope_closer_is_not_a_recruitment() {
        // `end Soma` is the closing half of `namespace Soma`. Reading it as a second naming of
        // `Soma` gave every artifact in the deposit a symbol of multiplicity two, and that -- the
        // export codec's closing convention -- was the ONLY source of nonzero torsion in the entire
        // standing. The two sources below differ by exactly that line.
        let wrapped = read(WITNESS_EVERY_RECEIVER_AGREES);
        let bare = read("theorem every_receiver_agrees (a b : Nat) : a = b := rfl\n");
        assert_eq!(wrapped.recruited.get("Soma"), Some(&1));
        assert_eq!(bare.recruited.get("Soma"), None);
        assert_eq!(wrapped.recruited.get("Nat"), bare.recruited.get("Nat"));
        assert_eq!(wrapped.recruited.get("rfl"), bare.recruited.get("rfl"));

        // And the consequence, measured: no symbol of this artifact is named twice, so the reading
        // that is *capable* of torsion returns none on it.
        let counted = invariants_of(&[wrapped], CircuitAperture::PER_ROUTE_MULTIPLICITY);
        assert!(counted.total_torsion().is_empty());
    }

    #[test]
    fn two_artifacts_of_one_declaration_with_different_bodies_recruit_different_populations() {
        // The reading was blind to the production until 2026-08-08: every artifact of one problem
        // returned the identical recruitment population, so no proof body the machine composed
        // could move the invariant by one bit. These two are deposited artifacts of ONE declaration
        // whose proof bodies differ, and their readings now differ -- in support, in counts, and in
        // torsion.
        let bare = read(PRODUCTION_ROUTE_A);
        let applied = read(PRODUCTION_ROUTE_B);
        assert_ne!(PRODUCTION_ROUTE_A, PRODUCTION_ROUTE_B);
        assert_eq!(bare.name, applied.name);
        assert_eq!(bare.statement, applied.statement);

        assert_eq!(applied.recruited.get("exact_chart_carry"), Some(&3));
        assert_eq!(bare.recruited.get("exact_chart_carry"), None);
        assert_ne!(bare.recruited_symbols(), applied.recruited_symbols());

        // and it reaches the invariants, not only the parse
        let one = invariants_of(&[bare], CircuitAperture::PER_ROUTE_MULTIPLICITY);
        let other = invariants_of(&[applied], CircuitAperture::PER_ROUTE_MULTIPLICITY);
        assert!(one.total_torsion().is_empty());
        assert_eq!(
            other.total_torsion(),
            vec![BigInt::from(3), BigInt::from(3)],
            "three `apply exact_chart_carry` steps cannot be un-applied twice"
        );
        assert!(!invariants_agree(&one, &other));
    }

    #[test]
    fn recruited_symbols_returns_every_key_and_not_only_the_first() {
        // Asserted against a literal population rather than against another `Derivation`: the only
        // check this carrier had was `assert_eq!(left.recruited_symbols(), right.recruited_symbols())`,
        // a self-comparison that degrades identically on both sides and could not see an
        // implementation returning its first key alone.
        let carried = read(PRODUCTION_ROUTE_B);
        assert_eq!(
            carried.recruited_symbols(),
            BTreeSet::from([
                "KernelWitness",
                "Prop",
                "Soma",
                "apply",
                "assumption",
                "exactCarrier",
                "exact_chart_carry",
            ])
        );
        assert_eq!(carried.recruited_symbols().len(), carried.recruited.len());
    }

    #[test]
    fn a_single_character_is_a_binder_and_a_two_character_identifier_is_a_recruitment() {
        // The reading's one orthographic rule, pinned from BOTH sides on deposited material, so
        // neither loosening nor tightening it passes. `rw` is two characters and is a declaration
        // the proof recruited; `P` and `h` are one character and are Lean's binder convention.
        let carried = read("namespace Soma\ntheorem formal_carry (h : P) : exactCarrier P := by\n  rw [exact_chart_carry]\n  assumption\nend Soma\n");
        assert_eq!(carried.recruited.get("rw"), Some(&1));
        assert_eq!(carried.recruited.get("P"), None);
        assert_eq!(carried.recruited.get("h"), None);
    }

    #[test]
    fn a_declaration_former_founds_the_identifier_that_follows_it() {
        // `def exactCarrier` and `abbrev ExactRelay` bind; they do not recruit. `have <bound> := X`
        // binds on the left. Without these rules the reading counts a file's own definitions as
        // recruitments of themselves and the local name of a `have` as a declaration.
        let defined = read(WITNESS_CARRIER_TRANSPORT);
        // `exactCarrier` is founded on the `def` line and recruited once, in the theorem statement.
        assert_eq!(defined.recruited.get("exactCarrier"), Some(&1));

        let bound = read("namespace Soma\ntheorem formal_carry (h : P) : exactCarrier P := by\n  have generated := exact_chart_carry P\n  assumption\nend Soma\n");
        assert_eq!(bound.recruited.get("generated"), None);
        assert_eq!(bound.recruited.get("exact_chart_carry"), Some(&1));

        let relayed = read("import KernelWitness\nnamespace Soma\nabbrev ExactRelay (Q : Prop) : Prop := exactCarrier Q\ntheorem carrier_transport_relayed (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n");
        assert_eq!(relayed.recruited.get("ExactRelay"), None);
        assert_eq!(relayed.recruited.get("Prop"), Some(&3));
        assert_eq!(relayed.recruited.get("exactCarrier"), Some(&2));
    }

    // ---------------------------------------------------------------- the grade-1 reading

    #[test]
    fn a_single_declaration_deposit_has_no_grade_one_cycle_whatever_it_recruits() {
        // Three artifacts of one theorem, deliberately recruiting DIFFERENT and GROWING symbol
        // populations. The recruitment varies across the sweep and the reading does not: under
        // `ByDeclaration` a single-name deposit is a star, and a star has no cycle. The zero is
        // forced by the identity choice, so it is not evidence about the production.
        let mut population = Vec::new();
        for width in 1..=6u32 {
            population.push(derivation(
                "carrier_transport",
                "one statement",
                &(0..width)
                    .map(|index| match index {
                        0 => ("Alpha", 1),
                        1 => ("Beta", 1),
                        2 => ("Gamma", 1),
                        3 => ("Delta", 1),
                        4 => ("Epsilon", 1),
                        _ => ("Zeta", 1),
                    })
                    .collect::<Vec<_>>(),
            ));
            let invariants = invariants_of(&population, CircuitAperture::DEPOSITED_READER);
            assert_eq!(
                betti_at(&invariants, 1),
                0,
                "width {width} opened a cycle under a single declaration"
            );
            assert_eq!(betti_at(&invariants, 0), 1);
        }
    }

    #[test]
    fn two_declarations_sharing_symbols_open_one_cycle_per_shared_symbol_beyond_the_first() {
        // The statement-BLIND law, swept over the only quantity that can move it, and named for
        // what it measures: shared recruitment. It is NOT "the independent routes to one result" --
        // the second half of this test proves the reading cannot tell the two apart, which is the
        // contradiction with `blueprint/THE_ASSEMBLY.md:129` this module reports.
        let expected: [(u32, usize, usize); 5] = [
            // shared, betti_1, betti_0
            (0, 0, 2),
            (1, 0, 1),
            (2, 1, 1),
            (3, 2, 1),
            (4, 3, 1),
        ];
        for (shared, cycles, components) in expected {
            let population = two_declarations_sharing(shared);
            assert_eq!(
                population[0].statement, population[1].statement,
                "the fixture's two declarations must prove ONE statement"
            );
            let invariants = invariants_of(&population, CircuitAperture::DEPOSITED_READER);
            assert_eq!(
                betti_at(&invariants, 1),
                cycles,
                "sharing {shared} symbols returned the wrong cycle population"
            );
            assert_eq!(betti_at(&invariants, 0), components);

            // and the same reading, on a population differing ONLY in statement identity
            let differing = invariants_of(
                &two_declarations_of_two_statements(shared),
                CircuitAperture::DEPOSITED_READER,
            );
            assert!(
                invariants_agree(&invariants, &differing),
                "the statement-blind reading must be blind, and it is not a route count"
            );
        }
    }

    #[test]
    fn the_grade_one_reading_depends_on_statement_identity_once_the_statements_are_founded() {
        // The repair, and the thing the statement-blind reading could not do. Two populations
        // differing in NOTHING but whether the second declaration proves the same statement as the
        // first. Under `STATEMENT_INCIDENT` they differ by exactly one cycle -- the one
        // route-to-one-result the lineage names -- and the difference is what
        // `route_cycle_agreement` re-derives from the lineage alone.
        //
        // Declared aperture: the recruitment graph must already be ONE component. Where it is not,
        // the statement attachment merges components instead of closing a cycle, and the two
        // readings coincide. `shared == 0` is that boundary and is asserted below rather than
        // hidden by starting the sweep at one.
        for shared in 1..=4u32 {
            let together = two_declarations_sharing(shared);
            let apart = two_declarations_of_two_statements(shared);
            assert_eq!(together[0].statement, together[1].statement);
            assert_ne!(apart[0].statement, apart[1].statement);
            assert_eq!(together[0].recruited, apart[0].recruited);
            assert_eq!(together[1].recruited, apart[1].recruited);
            assert_eq!(
                betti_at(
                    &invariants_of(&together, CircuitAperture::DEPOSITED_READER),
                    0
                ),
                1,
                "the aperture requires the recruitment graph to be one component"
            );

            let one = invariants_of(&together, CircuitAperture::STATEMENT_INCIDENT);
            let two = invariants_of(&apart, CircuitAperture::STATEMENT_INCIDENT);
            assert_eq!(
                betti_at(&one, 1),
                betti_at(&two, 1) + 1,
                "shared {shared}: founding the statements must see the one shared result"
            );

            let joint = circuit_of(&together, CircuitAperture::DEPOSITED_READER);
            let split = circuit_of(&apart, CircuitAperture::DEPOSITED_READER);
            assert_eq!(joint.lineage_route_excess(), 1);
            assert_eq!(split.lineage_route_excess(), 0);
        }

        // the aperture's own boundary, stated rather than avoided
        let disconnected = two_declarations_sharing(0);
        assert_eq!(
            betti_at(
                &invariants_of(&disconnected, CircuitAperture::DEPOSITED_READER),
                0
            ),
            2
        );
        assert_eq!(
            betti_at(
                &invariants_of(&disconnected, CircuitAperture::STATEMENT_INCIDENT),
                1
            ),
            betti_at(
                &invariants_of(
                    &two_declarations_of_two_statements(0),
                    CircuitAperture::STATEMENT_INCIDENT
                ),
                1
            ),
            "with the declarations in separate components the statement attachment merges rather \
             than closes, and the two readings coincide"
        );
    }

    #[test]
    fn founded_statement_incidence_opens_exactly_the_route_cycles_the_lineage_names() {
        // Two implementations of one quantity, on deposited material and on the fixtures: Smith
        // normal form over the boundary matrices of two apertures, against a count of distinct
        // vertices in the route lineage. They share no code path. A founding that attached a
        // derivation to the wrong statement vertex breaks this and nothing else here would see it.
        let populations: Vec<Vec<Derivation>> = vec![
            vec![read(PRODUCTION_ROUTE_A)],
            vec![read(PRODUCTION_ROUTE_A), read(PRODUCTION_ROUTE_B)],
            vec![read(WITNESS_CARRIER_TRANSPORT), read(RESEARCH_FORMAL_CARRY)],
            vec![
                read(PRODUCTION_ROUTE_A),
                read(WITNESS_CARRIER_TRANSPORT),
                read(RESEARCH_FORMAL_CARRY),
                read(WITNESS_EVERY_RECEIVER_AGREES),
            ],
            two_declarations_sharing(2),
            two_declarations_of_two_statements(2),
        ];
        let mut nonzero = 0;
        for population in &populations {
            for identity in [DerivationIdentity::ByDeclaration, DerivationIdentity::ByRoute] {
                let agreement = route_cycle_agreement(population, identity, PivotRule::FirstNonzero)
                    .expect("an incidence reading is admissible under either identity");
                assert!(
                    agreement.holds(),
                    "{identity:?} disagreed: {agreement:?} on {population:?}"
                );
                if agreement.recruitment_connected && agreement.lineage > 0 {
                    nonzero += 1;
                }
            }
        }
        assert!(
            nonzero > 0,
            "every case returned zero, so the agreement proved nothing about itself"
        );
    }

    #[test]
    fn control_the_grade_one_reading_is_nonzero_on_real_deposited_material() {
        // THE DECLARED NONZERO CONTROL, on verbatim deposited artifacts and no fixture.
        // `lean-kernel-witness/carrier_transport-00000` and
        // `agentic-research-kernel/formal_carry-00000` are two DIFFERENT declaration names carrying
        // the SAME normalized statement, sharing {Soma, Prop, exactCarrier}. |shared| - 1 = 2.
        let population = [read(WITNESS_CARRIER_TRANSPORT), read(RESEARCH_FORMAL_CARRY)];
        assert_eq!(population[0].statement, population[1].statement);
        assert_ne!(population[0].name, population[1].name);

        let circuit = circuit_of(&population, CircuitAperture::DEPOSITED_READER);
        assert_eq!(
            circuit.plural_vertex_statements(),
            BTreeSet::from(["(h : P) : exactCarrier P"])
        );
        let invariants = circuit
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        assert_eq!(betti_at(&invariants, 1), 2);

        // and with the statements founded, one more cycle: the route to that one result
        let seeing = invariants_of(&population, CircuitAperture::STATEMENT_INCIDENT);
        assert_eq!(betti_at(&seeing, 1), 3);
    }

    #[test]
    fn one_deposit_reads_zero_by_declaration_and_nonzero_by_route() {
        // The same material, two identities. If these agreed, every route-identity claim in this
        // module would be vacuous.
        let population = [
            read(PRODUCTION_ROUTE_A),
            read(PRODUCTION_ROUTE_B),
            read(PRODUCTION_ROUTE_A),
        ];
        let by_declaration = invariants_of(&population, CircuitAperture::DEPOSITED_READER);
        let by_route = invariants_of(&population, CircuitAperture::PER_ROUTE);
        assert_eq!(betti_at(&by_declaration, 1), 0);
        assert_eq!(betti_at(&by_route, 1), 8);
        assert!(!invariants_agree(&by_declaration, &by_route));
    }

    #[test]
    fn the_route_population_and_the_vertex_population_disagree_under_by_declaration() {
        // The reader's oldest inconsistency, pinned as a fact rather than left in prose: its own
        // output has always said "31 routes" for a statement whose complex carries one vertex.
        let population = [
            read(PRODUCTION_ROUTE_A),
            read(PRODUCTION_ROUTE_B),
            read(PRODUCTION_ROUTE_A),
        ];
        let circuit = circuit_of(&population, CircuitAperture::DEPOSITED_READER);
        let statement = "(P : Prop) (h : P) : exactCarrier P";
        assert_eq!(circuit.route_lineage(statement).len(), 3);
        assert_eq!(circuit.vertices_reaching(statement).len(), 1);
        assert_eq!(circuit.plural_route_statements(), BTreeSet::from([statement]));
        assert!(circuit.plural_vertex_statements().is_empty());
    }

    #[test]
    fn an_odd_recruitment_cycle_among_declarations_carries_one_cycle_and_no_torsion() {
        // Every `ByRoute` reading is BIPARTITE by construction -- a route vertex is `name#ordinal`
        // and can never be a recruitment target -- and on a bipartite graph the oriented and the
        // unoriented incidence matrices have the same Smith normal form. So no `ByRoute` fixture
        // can see whether the boundary is a difference at all. A recruitment cycle among
        // declarations is not bipartite, and it is real material: a proof recruits another theorem
        // by name, and that theorem recruits a third.
        //
        // Oriented, the three edges sum to zero and the reading is (betti_0, betti_1) = (1, 1) with
        // no torsion. Unoriented, the incidence determinant is 2, so the reading would be (0, 0)
        // with torsion Z/2.
        let population = [
            derivation("Alpha", "first", &[("Beta", 1)]),
            derivation("Beta", "second", &[("Gamma", 1)]),
            derivation("Gamma", "third", &[("Alpha", 1)]),
        ];
        let circuit = circuit_of(&population, CircuitAperture::DEPOSITED_READER);
        assert_eq!(circuit.vertices().len(), 3);
        assert_eq!(circuit.recruitments().len(), 3);
        let invariants = circuit
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        assert_eq!(betti_at(&invariants, 0), 1);
        assert_eq!(betti_at(&invariants, 1), 1);
        assert!(invariants.total_torsion().is_empty());
    }

    #[test]
    fn an_odd_recruitment_cycle_reads_the_same_where_torsion_is_possible() {
        // Orientation and torsion lived on DISJOINT apertures until the multiplicity refusal was
        // conditioned: the only non-bipartite reading was `ByDeclaration`, where the coefficient is
        // always one and torsion is a theorem-bound zero. Here they are the same aperture. Each
        // declaration carries exactly one artifact, so nothing is summed and the refusal does not
        // fire; one edge carries coefficient two, so torsion is possible; and the reading is still
        // (1, 1) with none, because the boundary is a difference. Unoriented the same population
        // returns (0, 0) with torsion Z/4.
        let population = [
            derivation("Alpha", "first", &[("Beta", 2)]),
            derivation("Beta", "second", &[("Gamma", 1)]),
            derivation("Gamma", "third", &[("Alpha", 1)]),
        ];
        let circuit = circuit_of(
            &population,
            CircuitAperture {
                identity: DerivationIdentity::ByDeclaration,
                coefficient: RecruitmentCoefficient::Multiplicity,
                statements: StatementIncidence::Withheld,
            },
        );
        let invariants = circuit
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        assert_eq!(betti_at(&invariants, 0), 1);
        assert_eq!(betti_at(&invariants, 1), 1);
        assert!(invariants.total_torsion().is_empty());

        // the second frame: union-find over the same 1-cells, which cannot see orientation at all
        let forest = circuit.spanning_forest_reading();
        assert_eq!(forest.betti_0(), betti_at(&invariants, 0));
        assert_eq!(forest.betti_1(), betti_at(&invariants, 1));
    }

    #[test]
    fn a_declaration_does_not_recruit_itself() {
        // A proof body may name the declaration it is proving -- `rw [formal_carry]` inside
        // `theorem formal_carry`. Left alone that founds a 1-cell whose two boundary terms cancel
        // to nothing: a grade-1 cell with an empty boundary, which reads as a cycle the material
        // does not have.
        let carried = read(SELF_RECRUITING_ROUTE);
        assert_eq!(carried.name, "formal_carry");
        assert_eq!(carried.recruited.get("formal_carry"), Some(&1));

        let circuit = circuit_of(&[carried], CircuitAperture::DEPOSITED_READER);
        assert!(!circuit
            .recruitments()
            .contains_key(&("formal_carry".to_owned(), "formal_carry".to_owned())));
        assert_eq!(circuit.vertices().len(), 6);
        assert_eq!(circuit.recruitments().len(), 5);
        let invariants = circuit
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        assert_eq!(betti_at(&invariants, 1), 0);
    }

    #[test]
    fn every_aperture_agrees_with_an_independent_spanning_forest_reading() {
        // This replaces `every_aperture_agrees_with_its_own_euler_characteristic`, which was
        // DELETED: chi from Betti numbers equals chi from cell counts by rank telescoping for ANY
        // chain complex, so it tested `rebase_invariants`' internal arithmetic and never
        // `found_circuit`. It printed `ok` under a mutation that deleted every 1-cell from the
        // complex and killed eleven other tests here.
        //
        // Union-find over the 1-cell supports is a second implementation of the same two numbers,
        // and it is independent where it matters: it reads `boundary.support()` and never a
        // coefficient, so it cannot see orientation. Claimed against the incidence readings, where
        // the boundary is unimodular and homology is exactly the graph's.
        let population = [
            read(PRODUCTION_ROUTE_A),
            read(PRODUCTION_ROUTE_B),
            read(WITNESS_CARRIER_TRANSPORT),
            read(RESEARCH_FORMAL_CARRY),
            read(WITNESS_EVERY_RECEIVER_AGREES),
            read(SELF_RECRUITING_ROUTE),
        ];
        let mut cycles_seen = 0;
        for aperture in CircuitAperture::DECLARED {
            if aperture.coefficient != RecruitmentCoefficient::Incidence {
                continue;
            }
            let circuit = circuit_of(&population, aperture);
            let invariants = circuit
                .invariants(PivotRule::FirstNonzero)
                .expect("the atlas reads");
            let forest = circuit.spanning_forest_reading();
            assert_eq!(
                forest.betti_0(),
                betti_at(&invariants, 0),
                "{aperture:?} components disagree"
            );
            assert_eq!(
                forest.betti_1(),
                betti_at(&invariants, 1),
                "{aperture:?} cycles disagree"
            );
            assert_eq!(circuit.aperture(), aperture);
            assert_eq!(forest.vertices, circuit.vertices().len());
            assert_eq!(
                forest.edges,
                circuit.recruitments().len() + circuit.reaches().len()
            );
            cycles_seen += forest.betti_1();
        }
        assert!(
            cycles_seen > 0,
            "every aperture returned a forest, so the agreement proved nothing about itself"
        );
    }

    // ---------------------------------------------------------------- torsion

    #[test]
    fn control_torsion_is_nonzero_under_multiplicity_on_one_real_artifact() {
        // THE DECLARED NONZERO CONTROL for the torsion half, and it moved material on 2026-08-08.
        // It used to rest on `every_receiver_agrees-00000` naming `Soma` twice -- once in
        // `namespace Soma` and once in `end Soma`, the export codec's closing convention. That is a
        // receiver-visible coordinate of the file layout and it is no longer read as a recruitment,
        // so that artifact now carries no torsion at all.
        //
        // What carries it instead is a recruitment the machine actually made:
        // `lean-kernel-witness/carrier_transport-00000` names `Prop` three times -- in the
        // definition of the carrier, in the section variable, and in the theorem's own binder.
        // Its boundary is
        //     Prop         [-3   0   0]
        //     Soma         [ 0  -1   0]
        //     exactCarrier [ 0   0  -1]
        //     route        [ 3   1   1]
        // whose 3x3 minors have gcd 3 and whose 2x2 minors have gcd 1, so the Smith diagonal is
        // (1, 1, 3) and H_0 carries Z/3.
        let population = [read(WITNESS_CARRIER_TRANSPORT)];
        assert_eq!(population[0].recruited.get("Prop"), Some(&3));

        let counted = invariants_of(&population, CircuitAperture::PER_ROUTE_MULTIPLICITY);
        assert_eq!(torsion_at(&counted, 0), vec![BigInt::from(3)]);
        assert_eq!(betti_at(&counted, 0), 1);
    }

    #[test]
    fn the_incidence_coefficient_returns_no_torsion_on_the_population_that_does_return_it() {
        // The same population, one axis moved. A graph incidence matrix is totally unimodular, so
        // every invariant factor is one and the reader's declared torsion signal is a constant
        // under the coefficient it has always used. This is the cross-check that the previous test
        // measured the coefficient and not the material.
        let population = [read(WITNESS_CARRIER_TRANSPORT)];
        let incidence = invariants_of(&population, CircuitAperture::PER_ROUTE);
        let counted = invariants_of(&population, CircuitAperture::PER_ROUTE_MULTIPLICITY);
        assert!(incidence.total_torsion().is_empty());
        assert!(!counted.total_torsion().is_empty());
    }

    #[test]
    fn torsion_survives_every_pivot_rule_on_a_population_that_carries_it() {
        // A pivot rule is a receiver coordinate. Run on the multiplicity reading, because on the
        // incidence reading every factor is one and the check could not fail.
        let population = [
            read(WITNESS_CARRIER_TRANSPORT),
            read(RESEARCH_FORMAL_CARRY),
            read(PRODUCTION_ROUTE_B),
        ];
        let circuit = circuit_of(&population, CircuitAperture::PER_ROUTE_MULTIPLICITY);
        let mut readings = PivotRule::ALL
            .iter()
            .map(|rule| circuit.invariants(*rule).expect("the atlas reads"));
        let first = readings.next().expect("three rules");
        assert!(!first.total_torsion().is_empty());
        for reading in readings {
            assert!(invariants_agree(&first, &reading));
        }
    }

    #[test]
    fn multiplicity_across_declarations_is_refused_when_a_name_carries_more_than_one_artifact() {
        let population = [read(PRODUCTION_ROUTE_A), read(PRODUCTION_ROUTE_B)];
        assert_eq!(population[0].name, population[1].name);
        let refusal = found_circuit(
            &population,
            CircuitAperture {
                identity: DerivationIdentity::ByDeclaration,
                coefficient: RecruitmentCoefficient::Multiplicity,
                statements: StatementIncidence::Withheld,
            },
        );
        assert_eq!(
            refusal.err(),
            Some(DerivationAtlasRefusal::MultiplicityWouldSumRoutes {
                declaration: "carrier_transport".to_owned(),
                artifacts: 2,
            })
        );
    }

    #[test]
    fn multiplicity_across_declarations_is_admitted_when_every_name_carries_one_artifact() {
        // The other side of the conditional refusal. Nothing is summed here, so the coefficient is
        // each artifact's own occurrence count and the reading is a reading rather than a fold of
        // the deposited artifact population. Without this the refusal could be widened back to the
        // whole composition and no test would notice.
        let population = [read(WITNESS_CARRIER_TRANSPORT), read(RESEARCH_FORMAL_CARRY)];
        assert_ne!(population[0].name, population[1].name);
        let circuit = circuit_of(
            &population,
            CircuitAperture {
                identity: DerivationIdentity::ByDeclaration,
                coefficient: RecruitmentCoefficient::Multiplicity,
                statements: StatementIncidence::Withheld,
            },
        );
        let invariants = circuit
            .invariants(PivotRule::FirstNonzero)
            .expect("the atlas reads");
        assert!(circuit
            .recruitments()
            .contains_key(&("carrier_transport".to_owned(), "Prop".to_owned())));
        assert!(circuit
            .recruitments()
            .contains_key(&("formal_carry".to_owned(), "Prop".to_owned())));
        assert_eq!(torsion_at(&invariants, 0), vec![BigInt::from(3)]);
    }

    // ---------------------------------------------------------------- the movement

    #[test]
    fn movement_and_agreement_are_one_quantity() {
        // Two comparators over one question -- the population and the existing boolean organ --
        // required to return the same verdict. Every case below is exercised in both directions.
        let alone = [read(WITNESS_CARRIER_TRANSPORT)];
        let paired = [read(WITNESS_CARRIER_TRANSPORT), read(RESEARCH_FORMAL_CARRY)];
        let widened = [
            read(WITNESS_CARRIER_TRANSPORT),
            read(RESEARCH_FORMAL_CARRY),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];

        let readings = [
            invariants_of(&alone, CircuitAperture::DEPOSITED_READER),
            invariants_of(&paired, CircuitAperture::DEPOSITED_READER),
            invariants_of(&widened, CircuitAperture::DEPOSITED_READER),
            invariants_of(&widened, CircuitAperture::STATEMENT_INCIDENT),
            invariants_of(&widened, CircuitAperture::PER_ROUTE_MULTIPLICITY),
            invariants_of(&[], CircuitAperture::DEPOSITED_READER),
        ];

        let mut agreed = 0;
        let mut differed = 0;
        for before in &readings {
            for after in &readings {
                let movement = invariant_movement(before, after);
                assert_eq!(
                    movement.is_still(),
                    invariants_agree(before, after),
                    "the population and the boolean disagree"
                );
                if movement.is_still() {
                    agreed += 1;
                } else {
                    differed += 1;
                }
            }
        }
        assert!(agreed > 0 && differed > 0, "the sweep exercised one branch only");
    }

    #[test]
    fn a_grade_present_on_one_side_only_is_a_founded_grade_and_not_a_realignment() {
        // The empty population carries grade 0 alone; a recruiting population carries grade 1 too.
        let none = invariants_of(&[], CircuitAperture::DEPOSITED_READER);
        let some = invariants_of(
            &[read(WITNESS_CARRIER_TRANSPORT)],
            CircuitAperture::DEPOSITED_READER,
        );
        let movement = invariant_movement(&none, &some);
        assert!(movement.grades_moved().contains(&1));
        let founded: Vec<&GradeMovement> = movement
            .moved()
            .iter()
            .filter(|grade| grade.founded())
            .collect();
        assert_eq!(founded.len(), 1);
        assert_eq!(founded[0].grade, 1);
        assert!(invariant_movement(&some, &none).moved()[1].withdrawn());
    }

    #[test]
    fn torsion_moving_between_two_readings_is_named_as_a_moved_field() {
        // Torsion is one of the two signals loop (c) is declared on, and `fields_moved` never had a
        // test that could see it: an implementation which simply never reported `MovedField::Torsion`
        // passed the whole module. These two readings differ in the torsion field and in NOTHING
        // else -- same cells, same ranks, same Betti numbers -- so the assertion is an equality
        // against a one-element set and cannot be satisfied by accident.
        let quiet = [derivation("alpha", "one statement", &[("Beta", 1), ("Gamma", 1)])];
        let twice = [derivation("alpha", "one statement", &[("Beta", 1), ("Gamma", 2)])];
        let before = invariants_of(&quiet, CircuitAperture::PER_ROUTE_MULTIPLICITY);
        let after = invariants_of(&twice, CircuitAperture::PER_ROUTE_MULTIPLICITY);
        assert!(before.total_torsion().is_empty());
        assert_eq!(after.total_torsion(), vec![BigInt::from(2)]);

        let movement = invariant_movement(&before, &after);
        assert!(!movement.is_still());
        assert_eq!(movement.grades_moved(), BTreeSet::from([0]));
        assert_eq!(
            movement.fields_moved(),
            BTreeSet::from([MovedField::Torsion])
        );
    }

    #[test]
    fn control_a_production_that_founds_a_second_declaration_moves_betti_at_grade_one() {
        // The reflective face, and the nonzero half of it. One declaration before; a second
        // declaration of the SAME statement after. betti at grade 1 moves, the movement names
        // grade 1 and names the betti field, and the route movement names the statement that became
        // plural -- as a population, not as a count.
        let before_population = [read(WITNESS_CARRIER_TRANSPORT)];
        let after_population = [read(WITNESS_CARRIER_TRANSPORT), read(RESEARCH_FORMAL_CARRY)];

        let before = circuit_of(&before_population, CircuitAperture::DEPOSITED_READER);
        let after = circuit_of(&after_population, CircuitAperture::DEPOSITED_READER);

        let earlier = before.invariants(PivotRule::FirstNonzero).expect("reads");
        let later = after.invariants(PivotRule::FirstNonzero).expect("reads");
        assert_eq!(betti_at(&earlier, 1), 0);
        assert_eq!(betti_at(&later, 1), 2);

        let movement = invariant_movement(&earlier, &later);
        assert!(!movement.is_still());
        assert!(movement.grades_moved().contains(&1));
        assert!(movement.fields_moved().contains(&MovedField::Betti));

        let routes = route_movement(&before, &after);
        assert!(routes.founded_statements().is_empty());
        assert_eq!(
            routes.became_plural(),
            &BTreeSet::from(["(h : P) : exactCarrier P".to_owned()])
        );
        assert_eq!(
            routes.founded_routes().get("(h : P) : exactCarrier P"),
            Some(&BTreeSet::from(["formal_carry".to_owned()]))
        );
        assert_eq!(
            routes.deepened_routes().get("(h : P) : exactCarrier P"),
            Some(&BTreeMap::from([("formal_carry".to_owned(), 1)]))
        );
    }

    #[test]
    fn a_production_that_deposits_the_same_material_moves_nothing() {
        // The other side of the previous test. Without this pair, a movement organ that reported
        // movement unconditionally would pass.
        let population = [read(WITNESS_CARRIER_TRANSPORT), read(RESEARCH_FORMAL_CARRY)];
        let circuit = circuit_of(&population, CircuitAperture::DEPOSITED_READER);
        let reading = circuit.invariants(PivotRule::FirstNonzero).expect("reads");
        assert!(invariant_movement(&reading, &reading).is_still());
        assert!(route_movement(&circuit, &circuit).is_still());
    }

    #[test]
    fn a_production_that_only_deepens_an_existing_lineage_still_moves_the_route_reading() {
        // THE MACHINE'S ACTUAL PRODUCTION MODE, and the reflective face was blind to it. Thirty-one
        // artifacts of one declaration are one vertex under `ByDeclaration`, so a thirty-second
        // moves no vertex, no recruitment, no invariant and no deduplicated route set. Everything
        // this organ reported was derived from `vertices_reaching`, a deduplicated `BTreeSet`,
        // while the ordered lineage sat unread one field away. `deepened_routes` reads it.
        let before_population = [read(PRODUCTION_ROUTE_A)];
        let after_population = [read(PRODUCTION_ROUTE_A), read(PRODUCTION_ROUTE_A)];
        let before = circuit_of(&before_population, CircuitAperture::DEPOSITED_READER);
        let after = circuit_of(&after_population, CircuitAperture::DEPOSITED_READER);

        // nothing the support can see moved
        assert_eq!(before.vertices().keys().collect::<Vec<_>>(), after.vertices().keys().collect::<Vec<_>>());
        assert_eq!(
            before.recruitments().keys().collect::<Vec<_>>(),
            after.recruitments().keys().collect::<Vec<_>>()
        );
        let earlier = before.invariants(PivotRule::FirstNonzero).expect("reads");
        let later = after.invariants(PivotRule::FirstNonzero).expect("reads");
        assert!(invariant_movement(&earlier, &later).is_still());

        // and the lineage did
        let routes = route_movement(&before, &after);
        assert!(routes.founded_statements().is_empty());
        assert!(routes.founded_routes().is_empty());
        assert!(routes.became_plural().is_empty());
        assert_eq!(
            routes.deepened_routes(),
            &BTreeMap::from([(
                "(P : Prop) (h : P) : exactCarrier P".to_owned(),
                BTreeMap::from([("carrier_transport".to_owned(), 1)])
            )])
        );
        assert!(!routes.is_still());
    }

    #[test]
    fn a_production_reaching_a_new_statement_founds_it_without_making_it_plural() {
        let before_population = [read(WITNESS_CARRIER_TRANSPORT)];
        let after_population = [
            read(WITNESS_CARRIER_TRANSPORT),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];
        let before = circuit_of(&before_population, CircuitAperture::DEPOSITED_READER);
        let after = circuit_of(&after_population, CircuitAperture::DEPOSITED_READER);
        let routes = route_movement(&before, &after);
        assert_eq!(
            routes.founded_statements(),
            &BTreeSet::from(["(a b : Nat) : a = b".to_owned()])
        );
        assert!(routes.became_plural().is_empty());
        assert!(routes.withdrawn_statements().is_empty());
    }

    #[test]
    fn a_statement_the_later_reading_lost_is_named_as_a_withdrawal() {
        // `withdrawn_statements` was asserted only as empty, by three tests, and no test in the
        // module ever produced a non-empty one. A refusal that cannot fire is not a refusal and a
        // field that is only ever empty is not a return.
        let wide = [
            read(WITNESS_CARRIER_TRANSPORT),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];
        let narrow = [read(WITNESS_CARRIER_TRANSPORT)];
        let before = circuit_of(&wide, CircuitAperture::DEPOSITED_READER);
        let after = circuit_of(&narrow, CircuitAperture::DEPOSITED_READER);
        let routes = route_movement(&before, &after);
        assert_eq!(
            routes.withdrawn_statements(),
            &BTreeSet::from(["(a b : Nat) : a = b".to_owned()])
        );
        assert!(routes.founded_statements().is_empty());
        assert!(routes.deepened_routes().is_empty());
        assert!(!routes.is_still());
    }

    // ---------------------------------------------------------------- withholding the reading

    #[test]
    fn withholding_the_reading_changes_the_target_population_only_when_something_is_plural() {
        // The design's falsifier for this loop: if the target population is identical with and
        // without the reading, the loop is decorative. It is identical exactly when nothing is
        // plural, and the fixture below carries both cases so the test can distinguish them.
        let nothing_plural = [
            read(WITNESS_CARRIER_TRANSPORT),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];
        let circuit = circuit_of(&nothing_plural, CircuitAperture::DEPOSITED_READER);
        assert_eq!(
            circuit.single_vertex_statements(),
            circuit.statements(),
            "with nothing plural the reading selects what withholding it would have selected"
        );

        let something_plural = [
            read(WITNESS_CARRIER_TRANSPORT),
            read(RESEARCH_FORMAL_CARRY),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];
        let circuit = circuit_of(&something_plural, CircuitAperture::DEPOSITED_READER);
        assert_ne!(circuit.single_vertex_statements(), circuit.statements());
        assert_eq!(
            circuit.single_vertex_statements(),
            BTreeSet::from(["(a b : Nat) : a = b"])
        );
    }

    #[test]
    fn the_target_population_is_ranked_by_its_lineage_and_can_select_either_statement() {
        // A production selecting a target from this reading takes the first entry. That selection
        // must be capable of returning something other than whatever a driver used to hard-code, or
        // it is an author's constant wearing an analysis's name. Two populations below, identical
        // in every other respect, and the ranking selects a DIFFERENT statement in each.
        let carrier_heavy = [
            read(PRODUCTION_ROUTE_A),
            read(PRODUCTION_ROUTE_B),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];
        let ranked = circuit_of(&carrier_heavy, CircuitAperture::DEPOSITED_READER)
            .single_vertex_statements_by_lineage()
            .iter()
            .map(|(statement, lineage)| ((*statement).to_owned(), lineage.len()))
            .collect::<Vec<_>>();
        assert_eq!(
            ranked,
            vec![
                ("(P : Prop) (h : P) : exactCarrier P".to_owned(), 2),
                ("(a b : Nat) : a = b".to_owned(), 1),
            ]
        );

        let agreement_heavy = [
            read(PRODUCTION_ROUTE_A),
            read(WITNESS_EVERY_RECEIVER_AGREES),
            read(WITNESS_EVERY_RECEIVER_AGREES),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];
        let ranked = circuit_of(&agreement_heavy, CircuitAperture::DEPOSITED_READER)
            .single_vertex_statements_by_lineage()
            .iter()
            .map(|(statement, lineage)| ((*statement).to_owned(), lineage.len()))
            .collect::<Vec<_>>();
        assert_eq!(
            ranked,
            vec![
                ("(a b : Nat) : a = b".to_owned(), 3),
                ("(P : Prop) (h : P) : exactCarrier P".to_owned(), 1),
            ]
        );

        // and a statement two declarations already reached is not in the population at all
        let cross_checked = [
            read(WITNESS_CARRIER_TRANSPORT),
            read(RESEARCH_FORMAL_CARRY),
            read(WITNESS_EVERY_RECEIVER_AGREES),
        ];
        let ranked = circuit_of(&cross_checked, CircuitAperture::DEPOSITED_READER)
            .single_vertex_statements_by_lineage()
            .iter()
            .map(|(statement, _)| (*statement).to_owned())
            .collect::<Vec<_>>();
        assert_eq!(ranked, vec!["(a b : Nat) : a = b".to_owned()]);
    }
}
