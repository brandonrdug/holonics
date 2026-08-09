//! A human-written formal development, read at the grain of its own declarations.
//!
//! [`crate::derivation_atlas::read_derivation`] reads **one artifact as one declaration**, and on
//! the material it was built for — the machine's generated proof candidates, one `theorem` per
//! file — that is exact. Pointed at a development a person wrote, it is an organ used past its
//! declared aperture, which `CLAUDE.md` §8 convicts *"even when it appears to return"*. It does
//! appear to return. Run against `soma/formal` it reads 13 files, emits 11 derivations named by
//! whichever `theorem` happened to be **last** in each file, hands each of them the whole file's
//! tokens as its recruitment, and reports **zero** recruited-and-declared names — a deposit in which
//! nothing can be opened, from material carrying 78 declared-to-declared recruitment edges.
//!
//! That number was the evidence behind a wall.
//! `research/records/2026-08-09_FOUR_RELATIONS_SEPARATE_THE_ATOM_AND_EACH_REFUTED_ITSELF_FIRST.md`
//! §7 closed with *"exactly one recruited identifier in 103 artifacts is declared… a **material**
//! constraint rather than a construction one."* The material was in the tree. The instrument could
//! not resolve it, and an instrument's blindness reported as a property of the world is the failure
//! `papers/source/synopsis/AUDIT.md:49-68` names.
//!
//! ## The three resolutions, and each is a separate defect
//!
//! 1. **Every top-level declaration is its own derivation.** All twelve
//!    [`crate::derivation_atlas::DECLARATION_FORMERS`] found, not only `theorem`. The existing
//!    reader already carries that list and uses it *only* to suppress the token after a former,
//!    never to open a declaration — so `def crossRatio` binds the name out of the recruitment
//!    population without ever entering the declared population, and `crossRatio` returns an **atom
//!    in the same file that defines it**. Every object a theorem is about was an atom by
//!    construction.
//!
//! 2. **Comment text is not recruitment, and what was dropped is returned.** Doc comments in a
//!    real development are English. Read as recruitment they deposit `An`, `At`, `Consequently`,
//!    `Different`, `Every`, `For`, `If`, `It`, `No` into the multiset — measured, not supposed —
//!    and two theorems then "co-present" `Every`, which is the exact species of tautology
//!    [`crate::collocation`] caught in its own null-bind (`Prop` sits in 101 of 103 regions, so
//!    anything lands inside it whatever the pairing). The population is **returned** as
//!    [`DevelopmentReading::commentary`] rather than silently discarded, because a reading that
//!    drops material without exhibiting it cannot be audited.
//!
//! 3. **File preamble is file-scope, not per-declaration recruitment.** `import`, `open`,
//!    `variable`, `universe`, `set_option`, `attribute` are how a file is *situated*; charging
//!    `Mathlib.Tactic.Ring` to every theorem in the file manufactures a symbol co-present in
//!    100% of that file's declarations, which is the same tautology one level up. Returned as
//!    [`DevelopmentReading::preamble`].
//!
//! A fourth follows from the third and closes a defect the existing reader convicted **and then
//! only half-repaired**. Its own documentation records that reading `end Soma` as a second naming of
//! `Soma` *"made the only nonzero torsion in the entire deposit be the `end` keyword — a
//! receiver-visible coordinate of the file layout promoted into a homological invariant"*. It skips
//! `end` lines and still charges `namespace Soma` as a recruitment of `Soma`, which is the identical
//! coordinate arriving through the other half of the same construct. Scoping tokens are returned as
//! [`DevelopmentReading::scoping`] and recruited by nothing.
//!
//! ## The aperture is declared, so that using it wrongly is detectable
//!
//! [`DeclarationGrain`] is the point of this module as much as the parsing is.
//! [`DeclarationGrain::OneArtifactOneDeclaration`] reproduces the historical aperture **and reports
//! every top-level former it did not open** as [`DevelopmentReading::unopened`]. That is the defect
//! above made visible: the old reader absorbed 52 declarations in silence and returned a plausible
//! answer. This one returns the same answer and hands back the 52.
//!
//! ## What is joined on, and the ambiguity that is returned rather than resolved
//!
//! A declaration is retained with the namespace path it was written under, but **the join is on the
//! short name as the source writes it** — inside `namespace Soma`, a body writes `congestion`, not
//! `Soma.congestion`, so qualifying the declaration while leaving the recruitment unqualified would
//! break every edge the material actually carries. Where two top-level declarations in one
//! development share a short name under different namespaces, that is a real ambiguity of the
//! material and is returned as [`DevelopmentReading::ambiguous_short_names`]. It is not resolved by
//! fiat: `OPEN` may not be closed by choosing.
//!
//! ## Declared bounds
//!
//! - **Top level only.** A declaration is a former at column zero. Structure fields, `where` blocks,
//!   `let rec`, and declarations nested inside a `section` body at an indent are not opened. A
//!   deeper grain is a different aperture and would need its own control.
//! - **Strings are not tracked.** A `--` inside a string literal is read as a comment opener. The
//!   present material contains no such literal; material that did would need the lexer to carry
//!   string state, which is a change to what the reading means.
//! - **`have` is still the only binding tactic.** Inherited verbatim from the existing reader:
//!   `obtain`, `rcases`, `intro`, `set` also bind, and a corpus containing them would read those
//!   names as recruitments.
//! - **The statement is the header up to `:=` or the end of the header**, normalized to single
//!   spaces, exactly as the existing reader normalizes it, so the two apertures produce comparable
//!   statement text on material where both apply.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::derivation_atlas::{Derivation, CODEC_KEYWORDS, DECLARATION_FORMERS};

/// Lines that situate a file rather than found anything in it.
///
/// Their tokens are returned as [`DevelopmentReading::preamble`] and charged to no declaration.
pub const PREAMBLE_FORMS: [&str; 6] = [
    "attribute",
    "import",
    "open",
    "set_option",
    "universe",
    "variable",
];

/// What one artifact is taken to carry.
///
/// Declared rather than assumed, because the two answers are each exact on their own material and
/// the wrong one returns a plausible reading instead of an error.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DeclarationGrain {
    /// One artifact declares one theorem — the machine's own generated deposit. Every later
    /// top-level former in the same text is reported unopened rather than absorbed.
    OneArtifactOneDeclaration,
    /// Every top-level declaration is its own derivation — a development a person wrote.
    EveryTopLevelDeclaration,
}

/// A top-level declaration the aperture did not open.
///
/// Under [`DeclarationGrain::OneArtifactOneDeclaration`] this population is the historical reader's
/// silent loss, made returnable.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct UnopenedDeclaration {
    /// The former that opened it: `theorem`, `def`, `structure`, …
    pub former: String,
    /// The name it founds, as written.
    pub name: String,
    /// One-based line in the text.
    pub line: usize,
}

/// One top-level declaration, with the namespace it was written under retained as lineage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredForm {
    /// The former that opened it.
    pub former: String,
    /// The name as the source writes it, which is also what a body in the same namespace recruits.
    pub name: String,
    /// The enclosing `namespace`/`section` path at the point of declaration, outermost first.
    pub namespace_path: Vec<String>,
    /// The header up to `:=`, normalized to single spaces.
    pub statement: String,
    /// Every symbol this declaration named, with the exact number of times it named it.
    pub recruited: BTreeMap<String, u32>,
    /// One-based line the former sits on.
    pub line: usize,
}

impl DeclaredForm {
    /// The fully qualified name, for provenance. **Not** the join key — see the module note.
    pub fn qualified(&self) -> String {
        if self.namespace_path.is_empty() {
            return self.name.clone();
        }
        format!("{}.{}", self.namespace_path.join("."), self.name)
    }

    /// This declaration as the atlas's carrier.
    pub fn derivation(&self) -> Derivation {
        Derivation {
            name: self.name.clone(),
            statement: self.statement.clone(),
            recruited: self.recruited.clone(),
        }
    }
}

/// One development text, read at a declared grain, with everything the reading set aside.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DevelopmentReading {
    /// The grain this reading was taken at.
    pub grain: DeclarationGrain,
    /// The declarations opened, in source order.
    pub declarations: Vec<DeclaredForm>,
    /// Top-level formers the grain did not open.
    pub unopened: Vec<UnopenedDeclaration>,
    /// Tokens occurring only inside comments, with counts. Returned, never silently dropped.
    pub commentary: BTreeMap<String, u32>,
    /// Tokens on file-scope preamble lines, with counts.
    pub preamble: BTreeMap<String, u32>,
    /// Tokens naming a `namespace`/`section` scope, with counts. File layout, never recruitment —
    /// see the module note on the half-repaired `end Soma` defect.
    pub scoping: BTreeMap<String, u32>,
    /// Short names declared more than once at top level, with the namespace path of each.
    pub ambiguous_short_names: BTreeMap<String, Vec<Vec<String>>>,
}

impl DevelopmentReading {
    /// The opened declarations as the atlas's carrier.
    pub fn derivations(&self) -> Vec<Derivation> {
        self.declarations
            .iter()
            .map(DeclaredForm::derivation)
            .collect()
    }

    /// Every short name this reading declares.
    pub fn declared_names(&self) -> BTreeSet<&str> {
        self.declarations
            .iter()
            .map(|form| form.name.as_str())
            .collect()
    }

    /// Declarations that recruit another declaration of the same reading, with the names recruited.
    ///
    /// This is the population the elaboration organ can open, and on the generated deposit it has
    /// exactly one member.
    pub fn declared_recruitment(&self) -> BTreeMap<&str, BTreeSet<&str>> {
        let declared = self.declared_names();
        let mut found: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
        for form in &self.declarations {
            let reached: BTreeSet<&str> = form
                .recruited
                .keys()
                .map(String::as_str)
                .filter(|symbol| *symbol != form.name && declared.contains(symbol))
                .collect();
            if !reached.is_empty() {
                found.insert(form.name.as_str(), reached);
            }
        }
        found
    }
}

/// Join two readings of different texts into one development population.
///
/// Ambiguity is recomputed across the whole population, because a short name declared once per file
/// in two files is ambiguous in the development and in neither file.
pub fn join(readings: Vec<DevelopmentReading>) -> DevelopmentReading {
    let grain = readings
        .first()
        .map_or(DeclarationGrain::EveryTopLevelDeclaration, |first| {
            first.grain
        });
    let mut joined = DevelopmentReading {
        grain,
        declarations: Vec::new(),
        unopened: Vec::new(),
        commentary: BTreeMap::new(),
        preamble: BTreeMap::new(),
        scoping: BTreeMap::new(),
        ambiguous_short_names: BTreeMap::new(),
    };
    for reading in readings {
        joined.declarations.extend(reading.declarations);
        joined.unopened.extend(reading.unopened);
        accumulate(&mut joined.commentary, reading.commentary);
        accumulate(&mut joined.preamble, reading.preamble);
        accumulate(&mut joined.scoping, reading.scoping);
    }
    joined.ambiguous_short_names = ambiguity(&joined.declarations);
    joined
}

fn accumulate(into: &mut BTreeMap<String, u32>, from: BTreeMap<String, u32>) {
    for (token, count) in from {
        let slot = into.entry(token).or_insert(0u32);
        *slot = slot.saturating_add(count);
    }
}

fn ambiguity(declarations: &[DeclaredForm]) -> BTreeMap<String, Vec<Vec<String>>> {
    let mut by_name: BTreeMap<String, Vec<Vec<String>>> = BTreeMap::new();
    for form in declarations {
        by_name
            .entry(form.name.clone())
            .or_default()
            .push(form.namespace_path.clone());
    }
    by_name.retain(|_, paths| paths.len() > 1);
    by_name
}

// -------------------------------------------------------------------------------------------------
// The lexer
// -------------------------------------------------------------------------------------------------

/// One source line with its comment text separated from its code text.
struct SplitLine {
    code: String,
    comment: String,
}

/// Separate comment text from code, carrying nested block-comment depth across lines.
///
/// Lean's `/- … -/` nests and `/-- … -/` is a doc comment, which is the same opener. `--` runs to
/// end of line. String literals are a declared bound and are not tracked.
fn split_comments(text: &str) -> Vec<SplitLine> {
    let mut split = Vec::new();
    let mut depth = 0usize;
    for line in text.lines() {
        let mut code = String::new();
        let mut comment = String::new();
        let bytes: Vec<char> = line.chars().collect();
        let mut index = 0usize;
        while index < bytes.len() {
            let two = if index + 1 < bytes.len() {
                (bytes[index], bytes[index + 1])
            } else {
                (bytes[index], '\0')
            };
            if two == ('/', '-') {
                depth += 1;
                comment.push(' ');
                index += 2;
                continue;
            }
            if two == ('-', '/') && depth > 0 {
                depth -= 1;
                comment.push(' ');
                index += 2;
                continue;
            }
            if depth == 0 && two == ('-', '-') {
                comment.push_str(&bytes[index..].iter().collect::<String>());
                index = bytes.len();
                continue;
            }
            if depth > 0 {
                comment.push(bytes[index]);
            } else {
                code.push(bytes[index]);
            }
            index += 1;
        }
        split.push(SplitLine { code, comment });
    }
    split
}

/// The identifier tokens of one line, in source order.
///
/// Reproduces [`crate::derivation_atlas`]'s rule exactly: a token begins with a letter or `_` and
/// continues through letters, digits, `_` and `.`, so `Nat.zero` is one token and `00012` is none.
fn identifier_tokens(line: &str) -> impl Iterator<Item = &str> {
    line.split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.'))
        .filter(|token| {
            token
                .chars()
                .next()
                .is_some_and(|first| first.is_alphabetic() || first == '_')
        })
}

/// The former opening this line, if it is a top-level declaration.
///
/// Column zero, and `noncomputable`/`private`/`protected`/`partial`/`unsafe`/`@[…]` modifiers are
/// stepped over so the former under them is found.
fn top_level_former(line: &str) -> Option<(&'static str, String)> {
    if line.starts_with(char::is_whitespace) || line.is_empty() {
        return None;
    }
    let mut rest = line.trim_end();
    // A leading attribute bracket is a modifier of the declaration under it.
    if let Some(after) = rest.strip_prefix('@') {
        let Some(close) = after.find(']') else {
            return None;
        };
        rest = after[close + 1..].trim_start();
    }
    loop {
        let stepped = ["noncomputable", "private", "protected", "partial", "unsafe"]
            .iter()
            .find_map(|modifier| {
                rest.strip_prefix(modifier)
                    .filter(|after| after.starts_with(char::is_whitespace))
            });
        match stepped {
            Some(after) => rest = after.trim_start(),
            None => break,
        }
    }
    for former in DECLARATION_FORMERS {
        // `variable` and `example` found nothing joinable: `variable` is preamble, `example` is
        // anonymous. Both are declared out here rather than filtered downstream.
        if former == "variable" || former == "example" {
            continue;
        }
        if let Some(after) = rest.strip_prefix(former) {
            if !after.starts_with(char::is_whitespace) {
                continue;
            }
            let name = after
                .trim_start()
                .split(|c: char| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '\''))
                .next()
                .unwrap_or_default()
                .to_owned();
            if name.is_empty() {
                continue;
            }
            return Some((former, name));
        }
    }
    None
}

/// Is this a file-scope preamble line?
fn is_preamble(line: &str) -> bool {
    let trimmed = line.trim_start();
    PREAMBLE_FORMS.iter().any(|form| {
        trimmed
            .strip_prefix(form)
            .is_some_and(|after| after.is_empty() || after.starts_with(char::is_whitespace))
    })
}

/// Read every token of one code line into a recruitment multiset, under the existing reader's
/// three exclusion rules: codec vocabulary, the token a former founds, single characters.
fn recruit_line(line: &str, into: &mut BTreeMap<String, u32>) {
    let trimmed = line.trim();
    if trimmed == "end" || trimmed.starts_with("end ") {
        return;
    }
    // `have <bound> := <recruitment>` binds on the left.
    let read = if trimmed == "have" || trimmed.starts_with("have ") {
        match trimmed.split_once(":=") {
            Some((_, right)) => right,
            None => return,
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
        let slot = into.entry(token.to_owned()).or_insert(0u32);
        *slot = slot.saturating_add(1);
    }
}

/// The statement of a declaration: its header up to `:=`, normalized to single spaces.
fn statement_of(header: &str, name: &str) -> String {
    let after_name = header
        .split_once(name)
        .map_or(header, |(_, right)| right)
        .split(":=")
        .next()
        .unwrap_or_default();
    after_name.split_whitespace().collect::<Vec<_>>().join(" ")
}

// -------------------------------------------------------------------------------------------------
// The reading
// -------------------------------------------------------------------------------------------------

/// Read one development text at a declared grain.
pub fn read_development(text: &str, grain: DeclarationGrain) -> DevelopmentReading {
    let split = split_comments(text);

    let mut commentary: BTreeMap<String, u32> = BTreeMap::new();
    for line in &split {
        for token in identifier_tokens(&line.comment) {
            if token.chars().count() <= 1 {
                continue;
            }
            let slot = commentary.entry(token.to_owned()).or_insert(0u32);
            *slot = slot.saturating_add(1);
        }
    }

    let mut preamble: BTreeMap<String, u32> = BTreeMap::new();
    let mut scoping: BTreeMap<String, u32> = BTreeMap::new();
    let mut declarations: Vec<DeclaredForm> = Vec::new();
    let mut unopened: Vec<UnopenedDeclaration> = Vec::new();
    let mut namespace_path: Vec<String> = Vec::new();

    // The declaration currently accumulating, and whether its header is still open.
    let mut open: Option<(DeclaredForm, bool, String)> = None;

    for (index, line) in split.iter().enumerate() {
        let code = line.code.as_str();
        let trimmed = code.trim();

        if let Some((former, name)) = top_level_former(code) {
            if let Some((form, _, _)) = open.take() {
                declarations.push(form);
            }
            let already = declarations.len();
            let opens = match grain {
                DeclarationGrain::EveryTopLevelDeclaration => true,
                DeclarationGrain::OneArtifactOneDeclaration => already == 0,
            };
            if !opens {
                unopened.push(UnopenedDeclaration {
                    former: former.to_owned(),
                    name,
                    line: index + 1,
                });
                continue;
            }
            let mut form = DeclaredForm {
                former: former.to_owned(),
                name: name.clone(),
                namespace_path: namespace_path.clone(),
                statement: String::new(),
                recruited: BTreeMap::new(),
                line: index + 1,
            };
            let header_open = !code.contains(":=");
            let mut header = statement_of(code, &name);
            if !header_open {
                form.statement = header.clone();
                header.clear();
            }
            recruit_line(code, &mut form.recruited);
            open = Some((form, header_open, header));
            continue;
        }

        if trimmed.is_empty() {
            continue;
        }

        if is_preamble(code) {
            recruit_line(code, &mut preamble);
            continue;
        }

        if let Some(rest) = trimmed.strip_prefix("namespace ") {
            if let Some(first) = rest.split_whitespace().next() {
                let slot = scoping.entry(first.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);
                namespace_path.push(first.to_owned());
            }
            if let Some((form, _, _)) = open.take() {
                declarations.push(form);
            }
            continue;
        }
        if trimmed == "end" || trimmed.starts_with("end ") {
            if let Some(first) = trimmed.strip_prefix("end ").and_then(|rest| rest.split_whitespace().next()) {
                let slot = scoping.entry(first.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);
            }
            namespace_path.pop();
            if let Some((form, _, _)) = open.take() {
                declarations.push(form);
            }
            continue;
        }
        if trimmed.starts_with("section") {
            if let Some(first) = trimmed.strip_prefix("section ").and_then(|rest| rest.split_whitespace().next()) {
                let slot = scoping.entry(first.to_owned()).or_insert(0u32);
                *slot = slot.saturating_add(1);
            }
            continue;
        }

        if let Some((form, header_open, header)) = open.as_mut() {
            if *header_open {
                let extended = format!("{header} {}", trimmed.split(":=").next().unwrap_or(""));
                *header = extended.split_whitespace().collect::<Vec<_>>().join(" ");
                if code.contains(":=") {
                    *header_open = false;
                    form.statement = header.clone();
                }
            }
            recruit_line(code, &mut form.recruited);
        }
    }

    if let Some((mut form, header_open, header)) = open.take() {
        if header_open {
            form.statement = header;
        }
        declarations.push(form);
    }

    // A declaration never recruits itself; the former founds it.
    for form in &mut declarations {
        let own = form.name.clone();
        form.recruited.remove(&own);
    }

    let ambiguous_short_names = ambiguity(&declarations);
    DevelopmentReading {
        grain,
        declarations,
        unopened,
        commentary,
        preamble,
        scoping,
        ambiguous_short_names,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const DEVELOPMENT: &str = r#"import Mathlib.Tactic.Ring
open Finset

namespace Soma

/-- Consequently every receiver agrees, if it is the same face. -/
abbrev Rel (a : Type u) (b : Type v) := a -> b -> Prop

def comp {a : Type u} (r : Rel a b) (s : Rel b c) : Rel a c :=
  fun x z => exists y, r x y

-- comp is associative, which nothing here needs.
theorem comp_assoc (r : Rel a b) :
    comp (comp r s) t = comp r (comp s t) := by
  ring

end Soma
"#;

    fn reading() -> DevelopmentReading {
        read_development(DEVELOPMENT, DeclarationGrain::EveryTopLevelDeclaration)
    }

    #[test]
    fn every_top_level_declaration_is_its_own_derivation() {
        let read = reading();
        let names: Vec<&str> = read
            .declarations
            .iter()
            .map(|form| form.name.as_str())
            .collect();
        assert_eq!(names, vec!["Rel", "comp", "comp_assoc"]);
    }

    #[test]
    fn the_former_is_retained_not_only_theorem() {
        let read = reading();
        let formers: Vec<&str> = read
            .declarations
            .iter()
            .map(|form| form.former.as_str())
            .collect();
        assert_eq!(formers, vec!["abbrev", "def", "theorem"]);
    }

    #[test]
    fn a_declaration_recruits_another_declaration_of_the_same_development() {
        let read = reading();
        let chain = read.declared_recruitment();
        // `comp` names `Rel`; `comp_assoc` names `comp` and `Rel`. That is the edge species the
        // one-artifact grain cannot carry at all.
        assert!(chain["comp"].contains("Rel"));
        assert!(chain["comp_assoc"].contains("comp"));
        assert!(chain["comp_assoc"].contains("Rel"));
    }

    #[test]
    fn comment_prose_is_returned_and_not_recruited() {
        let read = reading();
        assert!(read.commentary.contains_key("Consequently"));
        assert!(read.commentary.contains_key("every"));
        assert!(read.commentary.contains_key("associative"));
        for form in &read.declarations {
            assert!(!form.recruited.contains_key("Consequently"));
            assert!(!form.recruited.contains_key("associative"));
        }
    }

    #[test]
    fn preamble_is_file_scope_and_charged_to_no_declaration() {
        let read = reading();
        assert!(read.preamble.contains_key("Mathlib.Tactic.Ring"));
        assert!(read.preamble.contains_key("Finset"));
        for form in &read.declarations {
            assert!(!form.recruited.contains_key("Mathlib.Tactic.Ring"));
            assert!(!form.recruited.contains_key("Finset"));
        }
    }

    #[test]
    fn the_namespace_is_retained_as_lineage_and_the_join_is_the_short_name() {
        let read = reading();
        let comp = read
            .declarations
            .iter()
            .find(|form| form.name == "comp")
            .expect("comp is declared");
        assert_eq!(comp.namespace_path, vec!["Soma".to_owned()]);
        assert_eq!(comp.qualified(), "Soma.comp");
        // The body of `comp_assoc` writes `comp`, not `Soma.comp`, so the join key is the short one.
        assert!(read.declared_recruitment()["comp_assoc"].contains("comp"));
    }

    #[test]
    fn the_one_artifact_grain_reports_what_it_did_not_open() {
        let read = read_development(DEVELOPMENT, DeclarationGrain::OneArtifactOneDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].name, "Rel");
        let unopened: Vec<&str> = read
            .unopened
            .iter()
            .map(|missed| missed.name.as_str())
            .collect();
        assert_eq!(unopened, vec!["comp", "comp_assoc"]);
    }

    #[test]
    fn a_namespace_name_is_scoping_and_recruited_by_nothing() {
        // `derivation_atlas` convicted `end Soma` as *"a receiver-visible coordinate of the file
        // layout promoted into a homological invariant"* and repaired only that half; `namespace
        // Soma` was still charged as a recruitment of `Soma`. Both halves are scoping here.
        let read = reading();
        assert_eq!(read.scoping.get("Soma"), Some(&2u32));
        for form in &read.declarations {
            assert!(!form.recruited.contains_key("Soma"));
        }
    }

    #[test]
    fn a_declaration_does_not_recruit_itself() {
        let read = reading();
        for form in &read.declarations {
            assert!(!form.recruited.contains_key(&form.name));
        }
    }

    #[test]
    fn a_nested_block_comment_closes_at_the_right_depth() {
        let text = "/- outer /- inner -/ still comment -/\ndef live : Nat := 0\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].name, "live");
        assert!(read.commentary.contains_key("outer"));
        assert!(read.commentary.contains_key("inner"));
        assert!(read.commentary.contains_key("still"));
    }

    #[test]
    fn a_modifier_does_not_hide_the_former() {
        let text = "@[simp]\nnoncomputable def held : Nat := 0\nprivate theorem kept : True := trivial\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        let names: Vec<&str> = read
            .declarations
            .iter()
            .map(|form| form.name.as_str())
            .collect();
        assert_eq!(names, vec!["held", "kept"]);
    }

    #[test]
    fn a_multi_line_header_is_one_statement() {
        let text = "theorem wide\n    (a : Nat)\n    (b : Nat) :\n    a = b := by\n  omega\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].statement, "(a : Nat) (b : Nat) : a = b");
    }

    #[test]
    fn an_indented_former_is_not_a_top_level_declaration() {
        let text = "theorem outer : True := by\n  have inner := trivial\n  exact inner\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(read.declarations.len(), 1);
        assert_eq!(read.declarations[0].name, "outer");
    }

    #[test]
    fn ambiguity_across_a_joined_development_is_returned_not_resolved() {
        let one = read_development(
            "namespace A\ntheorem shared : True := trivial\nend A\n",
            DeclarationGrain::EveryTopLevelDeclaration,
        );
        let two = read_development(
            "namespace B\ntheorem shared : True := trivial\nend B\n",
            DeclarationGrain::EveryTopLevelDeclaration,
        );
        assert!(one.ambiguous_short_names.is_empty());
        assert!(two.ambiguous_short_names.is_empty());
        let joined = join(vec![one, two]);
        assert_eq!(
            joined.ambiguous_short_names["shared"],
            vec![vec!["A".to_owned()], vec!["B".to_owned()]]
        );
    }

    #[test]
    fn the_generated_deposit_shape_reads_identically_at_both_grains() {
        // One `theorem` per artifact is where the historical aperture is exact, and the two grains
        // must not disagree there — otherwise the plural reading is over-parsing.
        let artifact = "import KernelWitness\nnamespace Soma\ntheorem carrier_transport (P : Prop) (h : P) : exactCarrier P := by\n  assumption\nend Soma\n";
        let one = read_development(artifact, DeclarationGrain::OneArtifactOneDeclaration);
        let every = read_development(artifact, DeclarationGrain::EveryTopLevelDeclaration);
        assert_eq!(one.derivations(), every.derivations());
        assert!(one.unopened.is_empty());
        assert_eq!(one.declarations[0].name, "carrier_transport");
        assert_eq!(
            one.declarations[0].statement,
            "(P : Prop) (h : P) : exactCarrier P"
        );
    }

    #[test]
    fn declared_recruitment_is_empty_when_nothing_opens() {
        let text = "theorem alone : True := trivial\n";
        let read = read_development(text, DeclarationGrain::EveryTopLevelDeclaration);
        assert!(read.declared_recruitment().is_empty());
    }
}
