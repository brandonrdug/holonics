//! **An atlas of mathematical identities, founded from mathematics written as tokens.**
//!
//! ```text
//! cargo run --release --example the_material_founds_the_identity_atlas
//! ```
//!
//! ## The receiver question
//!
//! *Given a body of mathematics as text and nothing else — no grammar, no keyword table, no
//! elaborator, no kernel — what transport mechanisms does the material itself exhibit, and which of
//! them close into a group?*
//!
//! ## What is founded here and what is handed in
//!
//! Handed in: a directory of source files, and the reading that cuts a declaration's header off its
//! proof ([`lean_development::read_development`], which knows the formers `theorem`/`lemma`/`def`
//! and nothing about what a statement means).
//!
//! Founded from the population, by [`statement_grammar::recover`], which knows no noun of any
//! language: the **bracket species** the material groups in, the **separator**, the split into what
//! a statement supposes and what it concludes, and — by applying the identical organ one scale down
//! on the conclusions alone — the **relation** a conclusion asserts and the two sides it relates.
//!
//! Founded from that: for every conclusion asserting a relation between two applications of **one
//! head**, the rearrangement of the head's arguments is a **permutation**, and the permutations one
//! head exhibits **generate a group**. That group is the head's symmetry, recovered from spelling
//! alone with no semantics anywhere in the path.
//!
//! ## Why a permutation and not a statistic
//!
//! `CLAUDE.md`: *a returned partition may not be the preimage of a field the driver authored*. The
//! classifying quantity here is the permutation, and it is computed from the argument tokens of the
//! two sides — material this driver does not write and cannot vary. The falsifier is stated in the
//! run: a head whose identities generate the trivial group is reported as such, and a rearrangement
//! that is not a permutation of the same multiset is reported as a **transport that is not a
//! symmetry** rather than dropped.
//!
//! ## The compression, and its remainder
//!
//! Two identities that differ only by which letters were chosen are one identity. Replacing each
//! argument by the position of its first occurrence is a **rebase** — a relabelling with no
//! remainder — and identities sharing a rebased form are a collapsed pair. The collapsed population
//! is exhibited whole with what separates each pair, never counted and discarded.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use holonic_engine::hypergeometric_closure::{ClosureReading, ThreeSiteDials, read_return_group};
use holonic_engine::lean_development::{DeclarationGrain, header_nests, read_development};
use holonic_engine::multiquadratic::Multiquadratic;
use holonic_engine::statement_grammar::{
    GrammarAperture, RecoveredStatementGrammar, SeparatorOrientation, recover, recover_under,
};
use relational_geometry::Rat;
use relational_geometry::exact::RatVec2;
use relational_geometry::receiver_atlas;

/// The declared material. A subtree, named so the aperture is visible: this is one region of one
/// library, and every figure below is about it.
const SUBTREE: &str = "soma/formal/elementary-holonics/.lake/packages/mathlib/Mathlib/Geometry";

/// How many members of a population to print before saying how many are left. Exhibition, never a
/// filter: the populations themselves are complete and every count is of the whole.
const SHOWN: usize = 10;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels under the workspace root")
        .to_path_buf()
}

fn source_files(root: &Path, extension: &str) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(at) = pending.pop() {
        let Ok(entries) = fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                pending.push(path);
            } else if path.extension().is_some_and(|kind| kind == extension) {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// The first `width` **characters** of a string, for exhibition only.
///
/// Slicing by byte is what the library defect repaired today did; a display path may not repeat it.
fn clipped(text: &str, width: usize) -> String {
    text.chars().take(width).collect()
}

/// Which codec the material is written in.
///
/// **This is an INTAKE, and it is the only thing that changes between the runs below.** Everything
/// after it — the founded grammar, the oriented split, the relation one scale down, the permutation,
/// the group, the rebase, the transport graph, the routes — is byte-identical across codecs. If the
/// downstream reading were welded to one language, pointing it at a second would return nothing, and
/// that is the falsifier this parameter exists to expose.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Codec {
    /// Declaration headers cut off their proofs: `(binders) : conclusion`.
    Lean,
    /// Function signatures cut off their bodies: `(parameters) -> return`.
    Rust,
    /// Sentences from theory prose.
    Prose,
}

impl Codec {
    fn of(name: &str) -> Self {
        match name {
            "rust" => Self::Rust,
            "prose" => Self::Prose,
            _ => Self::Lean,
        }
    }

    fn extension(self) -> &'static str {
        match self {
            Self::Lean => "lean",
            Self::Rust => "rs",
            Self::Prose => "md",
        }
    }
}

/// Whether a signature writes its return arrow at its own depth.
fn has_top_level_arrow(statement: &str) -> bool {
    let mut expected: Vec<char> = Vec::new();
    let characters: Vec<char> = statement.chars().collect();
    for (at, symbol) in characters.iter().enumerate() {
        match symbol {
            '(' => expected.push(')'),
            '[' => expected.push(']'),
            '{' => expected.push('}'),
            ')' | ']' | '}' => {
                if expected.last() == Some(symbol) {
                    expected.pop();
                }
            }
            '-' if expected.is_empty() && characters.get(at + 1) == Some(&'>') => return true,
            _ => {}
        }
    }
    false
}

/// Every `fn` signature in a Rust source, as `(parameters) -> return`, with its name beside it.
///
/// The name is dropped from the statement for the same reason the Lean intake drops it: a name is an
/// address. Generic parameters and where-clauses are part of the header and are kept; a signature
/// whose brackets do not close is not returned, exactly as a Lean header that does not nest is not.
fn rust_signatures(text: &str) -> Vec<(String, String, BTreeSet<String>)> {
    let mut found = Vec::new();
    for raw in text.lines() {
        let line = raw.trim();
        let Some(after) = line
            .strip_prefix("pub fn ")
            .or_else(|| line.strip_prefix("fn "))
            .or_else(|| line.strip_prefix("pub(crate) fn "))
            .or_else(|| line.strip_prefix("pub const fn "))
            .or_else(|| line.strip_prefix("const fn "))
        else {
            continue;
        };
        let Some(opens) = after.find(['(', '<']) else {
            continue;
        };
        let name = after[..opens].trim().to_owned();
        if name.is_empty() {
            continue;
        }
        let mut statement = after[opens..]
            .trim_end_matches('{')
            .trim_end_matches(';')
            .trim()
            .to_owned();
        if statement.is_empty() {
            continue;
        }
        // **The elided consequent is written out.** Measured 2026-08-17 over 9,042 signatures in
        // this workspace: 5,467 carry `->` and 3,575 do not, because Rust omits the arrow when the
        // return is unit — so no run stands at depth zero in every signature and the grammar founds
        // no split at all, which is what the first run returned (0 of 3,337).
        //
        // Lean writes what a statement concludes in every statement; Rust writes it only when it is
        // not trivial. Making the omission explicit is PRESENTATION and it is reversible — `-> ()`
        // is exactly what was implied — so it adds no classification the material did not carry.
        if !has_top_level_arrow(&statement) {
            statement.push_str(" -> ()");
        }
        // the parameter names this signature itself binds, which is the same founded distinction the
        // Lean intake takes from `local_bindings`
        let mut bound: BTreeSet<String> = BTreeSet::new();
        if let (Some(open), Some(close)) = (statement.find('('), statement.rfind(')')) {
            if open < close {
                for piece in statement[open + 1..close].split(',') {
                    if let Some((left, _)) = piece.split_once(':') {
                        let word = left.trim().trim_start_matches("mut ").trim();
                        if !word.is_empty() && word.chars().all(|c| c.is_alphanumeric() || c == '_')
                        {
                            bound.insert(word.to_owned());
                        }
                    }
                }
            }
        }
        found.push((name, statement, bound));
    }
    found
}

/// Sentences of theory prose: a run ending at a full stop that follows a word character.
///
/// Code fences, headings, tables and link targets are excluded — they are a different codec inside
/// the same file, and mixing them would make the population a union rather than a material.
fn prose_sentences(text: &str) -> Vec<(String, String)> {
    let mut found = Vec::new();
    let mut fenced = false;
    for (at, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.starts_with("```") {
            fenced = !fenced;
            continue;
        }
        if fenced || line.is_empty() || line.starts_with('#') || line.starts_with('|') {
            continue;
        }
        let mut carried = String::new();
        for symbol in line.chars() {
            carried.push(symbol);
            if symbol == '.'
                && carried
                    .chars()
                    .rev()
                    .nth(1)
                    .is_some_and(char::is_alphanumeric)
            {
                let sentence = carried.trim().to_owned();
                if sentence.split_whitespace().count() >= 5 {
                    found.push((format!("line{}", at + 1), sentence));
                }
                carried.clear();
            }
        }
    }
    found
}

/// One side of a relation, read by the rule the grammar reads a trailing region by: the tokens at
/// the side's **own depth**, where a whole bracket group counts as one token and a punctuation token
/// standing at that depth refuses the reading.
///
/// Both sides go through this, which is the point. Reading the two sides by two rules would make
/// every arity comparison a comparison of the rules.
fn read_side(text: &str, family: &[(char, char)]) -> Option<(String, Vec<String>)> {
    let mut tokens: Vec<String> = Vec::new();
    let mut expected: Vec<char> = Vec::new();
    let mut carried = String::new();
    let mut group = String::new();
    for symbol in text.chars() {
        if !expected.is_empty() {
            group.push(symbol);
            if let Some((_, close)) = family.iter().find(|(open, _)| *open == symbol) {
                expected.push(*close);
            } else if expected.last() == Some(&symbol) {
                expected.pop();
                if expected.is_empty() {
                    tokens.push(std::mem::take(&mut group));
                }
            }
            continue;
        }
        if let Some((_, close)) = family.iter().find(|(open, _)| *open == symbol) {
            if !carried.is_empty() {
                tokens.push(std::mem::take(&mut carried));
            }
            expected.push(*close);
            group.push(symbol);
            continue;
        }
        if symbol.is_whitespace() {
            if !carried.is_empty() {
                tokens.push(std::mem::take(&mut carried));
            }
            continue;
        }
        if symbol.is_alphanumeric() || symbol == '_' || symbol == '.' {
            carried.push(symbol);
            continue;
        }
        // a punctuation token at this side's own depth: the side is not one application
        return None;
    }
    if !expected.is_empty() {
        return None;
    }
    if !carried.is_empty() {
        tokens.push(carried);
    }
    let mut walk = tokens.into_iter();
    let head = walk.next()?;
    // a head is a name, never a group
    if family.iter().any(|(open, _)| head.starts_with(*open)) {
        return None;
    }
    Some((head, walk.collect()))
}

// -------------------------------------------------------------------------------------------------
// The resolvers — organs that compute an exact value, against which a founded identity is tested
// -------------------------------------------------------------------------------------------------

/// An organ that returns an exact rational from exact rational arguments.
///
/// **The driver never pairs a resolver with an identity.** Every resolver is tested against every
/// founded identity of matching arity, and the arithmetic decides. Pairing them by name would make
/// the return the preimage of a table this file wrote.
struct Resolver {
    /// A name composed of its mechanism, never of a person or a library.
    name: &'static str,
    arity: usize,
    evaluate: fn(&[Rat]) -> Option<Rat>,
}

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

/// `a + b` — the additive composition.
fn additive(argument: &[Rat]) -> Option<Rat> {
    Some(&argument[0] + &argument[1])
}

/// `a - b` — **the control.** Its symmetry group is trivial, so an identity confirmed by it and by
/// nothing else would convict the whole test.
fn oriented_difference(argument: &[Rat]) -> Option<Rat> {
    Some(&argument[0] - &argument[1])
}

/// `(a - b)²` — the squared separation of two points on a line, the exact form a distance takes
/// before a root is extracted.
fn squared_separation(argument: &[Rat]) -> Option<Rat> {
    let gap = &argument[0] - &argument[1];
    Some(&gap * &gap)
}

/// `B(m, n) = (m-1)!(n-1)!/(m+n-1)!` on positive integers — exact, and rational by construction.
fn beta_on_integers(argument: &[Rat]) -> Option<Rat> {
    let whole = |value: &Rat| -> Option<i64> {
        if !value.denom().eq(&BigInt::one()) {
            return None;
        }
        let carried: i64 = value.numer().to_string().parse().ok()?;
        (carried > 0 && carried < 40).then_some(carried)
    };
    let (m, n) = (whole(&argument[0])?, whole(&argument[1])?);
    let factorial = |count: i64| -> Rat {
        let mut carried = BigInt::one();
        for step in 2..=count {
            carried *= BigInt::from(step);
        }
        Rat::from_integer(carried)
    };
    Some(factorial(m - 1) * factorial(n - 1) / factorial(m + n - 1))
}

/// The corner cosine of a triangle with sides `a`, `b`, `c`: `(a² + b² - c²)/(2ab)`, exactly
/// rational and with no angle taken.
///
/// **This is `contact_gluing::Corner`'s law, written here rather than called.** That organ returns a
/// corner only as part of a `ContactTriangle`, which needs identifiers, stems and a realizability
/// verdict this probe has no material for; the law itself is one line and is stated rather than
/// approximated. The cross ratio below, whose standing organ takes bare marks, IS called.
fn corner_cosine(argument: &[Rat]) -> Option<Rat> {
    let (a, b, c) = (&argument[0], &argument[1], &argument[2]);
    if a.is_zero() || b.is_zero() {
        return None;
    }
    Some((a * a + b * b - c * c) / (Rat::from_integer(BigInt::from(2)) * a * b))
}

/// The cross ratio of four marks on a line, computed by **the standing organ**,
/// `relational_geometry::receiver_atlas::cross_ratio`, which owns its own refusals — coincident
/// pivots, marks outside one pencil, a repeated projective member.
///
/// The four rationals are placed as four points of one horizontal pencil, which is the shape that
/// organ admits. Wiring a second cross ratio here would be the defect its own documentation names:
/// *"two `PGL(2,ℚ)` carriers in one workspace, and a second implementation agreeing with the first
/// is one computation compared with itself twice."*
fn cross_ratio(argument: &[Rat]) -> Option<Rat> {
    let marks: Vec<RatVec2> = argument
        .iter()
        .map(|coordinate| RatVec2::new(coordinate.clone(), Rat::zero()))
        .collect();
    receiver_atlas::cross_ratio(&marks).ok()
}

/// A truncated hypergeometric sum `Σ_{n<N} (a)_n (b)_n / ((c)_n n!) · z^n`, exact over the
/// rationals, in the argument order `(z, a, b, c)`.
fn hypergeometric_partial(argument: &[Rat]) -> Option<Rat> {
    let (z, a, b, c) = (&argument[0], &argument[1], &argument[2], &argument[3]);
    let mut total = Rat::zero();
    let mut rising_a = Rat::one();
    let mut rising_b = Rat::one();
    let mut rising_c = Rat::one();
    let mut factorial = Rat::one();
    let mut power = Rat::one();
    for step in 0..6i64 {
        if rising_c.is_zero() {
            return None;
        }
        total += &rising_a * &rising_b * &power / (&rising_c * &factorial);
        let offset = Rat::from_integer(BigInt::from(step));
        rising_a *= a + &offset;
        rising_b *= b + &offset;
        rising_c *= c + &offset;
        factorial *= Rat::from_integer(BigInt::from(step + 1));
        power *= z;
    }
    Some(total)
}

/// The resolvers this body owns, as a population. Nothing here is chosen for an identity.
const RESOLVERS: [Resolver; 6] = [
    Resolver {
        name: "additive-composition",
        arity: 2,
        evaluate: additive,
    },
    Resolver {
        name: "oriented-difference",
        arity: 2,
        evaluate: oriented_difference,
    },
    Resolver {
        name: "squared-separation",
        arity: 2,
        evaluate: squared_separation,
    },
    Resolver {
        name: "beta-on-integers",
        arity: 2,
        evaluate: beta_on_integers,
    },
    Resolver {
        name: "corner-cosine",
        arity: 3,
        evaluate: corner_cosine,
    },
    Resolver {
        name: "cross-ratio",
        arity: 4,
        evaluate: cross_ratio,
    },
];

/// A seventh, kept out of the array above only because it shares an arity with the cross ratio and
/// both must be reachable at that arity.
const HYPERGEOMETRIC: Resolver = Resolver {
    name: "hypergeometric-partial-sum",
    arity: 4,
    evaluate: hypergeometric_partial,
};

/// Exact argument tuples of a given arity, spread so that no two entries coincide.
///
/// Distinctness is the anti-degeneracy condition: a resolver is only admitted to the test if its
/// values **separate** across these tuples, and a resolver that returns one value everywhere would
/// satisfy every permutation and is refused by name.
fn probes(arity: usize) -> Vec<Vec<Rat>> {
    let spread: [(i64, i64); 6] = [(2, 1), (3, 1), (5, 1), (7, 2), (11, 3), (4, 1)];
    let mut found = Vec::new();
    for offset in 0..4usize {
        let tuple: Vec<Rat> = (0..arity)
            .map(|place| {
                let (numerator, denominator) = spread[(place + offset) % spread.len()];
                rational(numerator, denominator)
            })
            .collect();
        found.push(tuple);
    }
    found
}

/// Every permutation of `degree` letters, in lexicographic order.
fn permutations(degree: usize) -> Vec<Vec<usize>> {
    if degree == 0 {
        return vec![Vec::new()];
    }
    let mut found = Vec::new();
    let mut current: Vec<usize> = (0..degree).collect();
    loop {
        found.push(current.clone());
        // next lexicographic permutation
        let Some(pivot) = (0..degree - 1)
            .rev()
            .find(|at| current[*at] < current[at + 1])
        else {
            return found;
        };
        let swap = (pivot + 1..degree)
            .rev()
            .find(|at| current[*at] > current[pivot])
            .expect("a successor exists past the pivot");
        current.swap(pivot, swap);
        current[pivot + 1..].reverse();
    }
}

/// One conclusion, as the second application of the organ read it.
struct Relation {
    /// The whole statement the conclusion was split out of, retained so every atlas row can be
    /// taken back to the material it was read off.
    statement: String,
    /// The conclusion the first split returned.
    conclusion: String,
    /// The head of the left side and its argument tokens.
    left: (String, Vec<String>),
    /// The head of the right side and its argument tokens.
    right: (String, Vec<String>),
    /// Whether each head is a name **the statement's own suppositions bind**.
    ///
    /// Founded, never declared: `lean_development` already returns `local_bindings` per declaration,
    /// so a head that its own statement binds is a variable standing where an operation would, and
    /// the two are different objects. Without this the transport graph's most connected nodes are
    /// `f`, `p`, `x` and `0` — which is the graph reading its own material's alphabet.
    left_is_bound: bool,
    right_is_bound: bool,
}

/// The rearrangement two sides of one relation exhibit.
enum Rearrangement {
    /// The right side's arguments are the left side's, permuted. The permutation carries which
    /// position each argument moved to.
    Permutation(Vec<usize>),
    /// The two sides carry the same head and their arguments are not a rearrangement of one
    /// multiset — a transport, but not a symmetry. Retained by name.
    NotASymmetry { reason: String },
}

fn rearrangement(left: &[String], right: &[String]) -> Rearrangement {
    if left.len() != right.len() {
        return Rearrangement::NotASymmetry {
            reason: format!("arity {} against {}", left.len(), right.len()),
        };
    }
    let mut taken = vec![false; left.len()];
    let mut sigma = vec![0usize; left.len()];
    for (at, argument) in right.iter().enumerate() {
        let Some(from) = left
            .iter()
            .enumerate()
            .position(|(where_, carried)| carried == argument && !taken[where_])
        else {
            return Rearrangement::NotASymmetry {
                reason: format!("{argument:?} on the right stands nowhere on the left"),
            };
        };
        taken[from] = true;
        sigma[at] = from;
    }
    Rearrangement::Permutation(sigma)
}

/// `sigma ∘ tau`: apply `tau` first.
fn compose(sigma: &[usize], tau: &[usize]) -> Vec<usize> {
    tau.iter().map(|at| sigma[*at]).collect()
}

fn identity_of(degree: usize) -> Vec<usize> {
    (0..degree).collect()
}

/// The subgroup of the symmetric group that a set of permutations generates, by closure. Exact,
/// finite, and refused if the generators disagree on degree.
fn generated(generators: &BTreeSet<Vec<usize>>) -> Option<BTreeSet<Vec<usize>>> {
    let degree = generators.iter().next()?.len();
    if generators.iter().any(|sigma| sigma.len() != degree) {
        return None;
    }
    let mut closed: BTreeSet<Vec<usize>> = BTreeSet::new();
    closed.insert(identity_of(degree));
    for generator in generators {
        closed.insert(generator.clone());
    }
    loop {
        let mut grown: BTreeSet<Vec<usize>> = BTreeSet::new();
        for sigma in &closed {
            for tau in &closed {
                let product = compose(sigma, tau);
                if !closed.contains(&product) {
                    grown.insert(product);
                }
            }
        }
        if grown.is_empty() {
            return Some(closed);
        }
        closed.extend(grown);
    }
}

fn is_abelian(group: &BTreeSet<Vec<usize>>) -> bool {
    group.iter().all(|sigma| {
        group
            .iter()
            .all(|tau| compose(sigma, tau) == compose(tau, sigma))
    })
}

/// The order of one element: how many times it must be applied to return.
fn order_of(sigma: &[usize]) -> usize {
    let mut carried = sigma.to_vec();
    let mut turns = 1usize;
    while carried != identity_of(sigma.len()) {
        carried = compose(sigma, &carried);
        turns += 1;
    }
    turns
}

/// A permutation written in the notation that carries its own mechanism: which position each
/// argument came from.
fn render_permutation(sigma: &[usize]) -> String {
    let places: Vec<String> = sigma.iter().map(|from| (from + 1).to_string()).collect();
    format!("[{}]", places.join(" "))
}

/// The rebase: every argument replaced by the position of its first occurrence across the whole
/// relation. A relabelling, with no remainder, so two identities differing only in the letters
/// chosen return the same form.
fn rebased(relation: &Relation) -> String {
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    let mut place = |token: &String| -> String {
        let next = seen.len();
        let at = *seen.entry(token.clone()).or_insert(next);
        format!("x{at}")
    };
    let left: Vec<String> = relation.left.1.iter().map(&mut place).collect();
    let right: Vec<String> = relation.right.1.iter().map(&mut place).collect();
    format!(
        "{} {} = {} {}",
        relation.left.0,
        left.join(" "),
        relation.right.0,
        right.join(" ")
    )
}

fn print_aperture(grammar: &RecoveredStatementGrammar, headline: &str) {
    println!("  {headline}");
    let mut by_species: BTreeMap<String, usize> = BTreeMap::new();
    for bound in grammar.aperture() {
        let species = match bound {
            GrammarAperture::BracketFamilyIsPlural { .. } => "bracket-family-is-plural",
            GrammarAperture::BracketFamilyDoesNotNest { .. } => "bracket-family-does-not-nest",
            GrammarAperture::NoBracketPairBalances => "no-bracket-pair-balances",
            GrammarAperture::SeparatorIsNotUnique { .. } => "separator-is-not-unique",
            GrammarAperture::NoSeparatorOccursAtDepthZeroInEveryStatement => "no-separator",
            GrammarAperture::SeparatorFoundedByRecurrenceInsideGroups { .. } => {
                "separator-founded-by-recurrence"
            }
            GrammarAperture::SeparatorOccursPlurallyAtDepthZero { .. } => "separator-plural",
            GrammarAperture::SeveralOccurrencesFoundTheLeadingRegion { .. } => {
                "orientation-decided-the-split"
            }
            GrammarAperture::BodyCarriesPunctuation { .. } => "conclusion-carries-punctuation",
            GrammarAperture::BinderGroupCarriesNoSeparator { .. } => "group-carries-no-separator",
            GrammarAperture::LeadingRegionCarriesABareToken { .. } => "supposition-is-a-bare-token",
            other => {
                by_species
                    .entry(
                        format!("{other:?}")
                            .split_whitespace()
                            .next()
                            .unwrap_or("other")
                            .to_owned(),
                    )
                    .and_modify(|count| *count += 1)
                    .or_insert(1);
                continue;
            }
        };
        by_species
            .entry(species.to_owned())
            .and_modify(|count| *count += 1)
            .or_insert(1);
    }
    for (species, count) in &by_species {
        println!("    {species:<34} {count}");
    }
}

fn main() {
    let root = workspace_root();
    // the subtree is declared, and may be re-declared on the command line so the same reading can
    // be taken over a second material without the driver choosing which
    let declared = std::env::args()
        .nth(1)
        .unwrap_or_else(|| SUBTREE.to_owned());
    let codec = Codec::of(&std::env::args().nth(2).unwrap_or_else(|| "lean".to_owned()));
    let subtree = root.join(&declared);

    println!("{}", "=".repeat(100));
    println!("THE MATERIAL  --  mathematics as text, and nothing else is opened");
    println!("{}", "=".repeat(100));
    println!();

    let files = source_files(&subtree, codec.extension());
    if files.is_empty() {
        println!("  {declared} carries no source; nothing to found");
        return;
    }

    // ------------------------------------------------------------------ the statement population
    let mut statements: BTreeSet<String> = BTreeSet::new();
    let mut by_statement: BTreeMap<String, String> = BTreeMap::new();
    let mut unwhole: BTreeMap<String, String> = BTreeMap::new();
    let mut bindings_of: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    let mut declarations = 0usize;
    let mut lines = 0usize;
    for file in &files {
        let Ok(text) = fs::read_to_string(file) else {
            continue;
        };
        lines += text.lines().count();
        match codec {
            Codec::Lean => {
                let reading = read_development(&text, DeclarationGrain::EveryTopLevelDeclaration);
                for form in &reading.declarations {
                    declarations += 1;
                    if form.former != "theorem" && form.former != "lemma" {
                        continue;
                    }
                    let statement = form.statement.trim();
                    if statement.is_empty() {
                        continue;
                    }
                    if header_nests(statement) {
                        statements.insert(statement.to_owned());
                        by_statement
                            .entry(statement.to_owned())
                            .or_insert_with(|| form.name.clone());
                        bindings_of
                            .entry(statement.to_owned())
                            .or_default()
                            .extend(form.local_bindings.keys().cloned());
                    } else {
                        unwhole.insert(statement.to_owned(), form.name.clone());
                    }
                }
            }
            Codec::Rust => {
                for (name, statement, bound) in rust_signatures(&text) {
                    declarations += 1;
                    if header_nests(&statement) {
                        by_statement.entry(statement.clone()).or_insert(name);
                        bindings_of
                            .entry(statement.clone())
                            .or_default()
                            .extend(bound);
                        statements.insert(statement);
                    } else {
                        unwhole.insert(statement, name);
                    }
                }
            }
            Codec::Prose => {
                for (where_, sentence) in prose_sentences(&text) {
                    declarations += 1;
                    if header_nests(&sentence) {
                        by_statement.entry(sentence.clone()).or_insert(where_);
                        statements.insert(sentence);
                    } else {
                        unwhole.insert(sentence, where_);
                    }
                }
            }
        }
        {}
    }

    println!("  subtree                    {declared}");
    println!(
        "  codec                      {codec:?}   -- the ONLY thing that changes between runs"
    );
    println!("  source files               {}", files.len());
    println!("  lines                      {lines}");
    println!("  declarations opened        {declarations}");
    println!("  distinct theorem/lemma statements  {}", statements.len());
    println!(
        "  headers that do not nest   {}   EXCLUDED and exhibited below",
        unwhole.len()
    );
    println!();
    println!(
        "  A founding quantified over the whole population is as strong as its worst member, so"
    );
    println!(
        "  the intake is the reader's own audit of its own return: a header that opens a bracket"
    );
    println!(
        "  and does not close it is not a whole statement. Every one is named here, never dropped."
    );
    for (statement, name) in &unwhole {
        println!("    {name}");
        println!("      {}", clipped(&statement, 108));
    }
    println!();
    println!(
        "  the reader cuts a header off a proof and knows the formers. It does not know what a"
    );
    println!("  statement means, and the name is dropped here because a name is an address.");
    println!();
    for statement in statements.iter().take(4) {
        println!("    {}", clipped(&statement, 112));
    }

    // ------------------------------------------------------------------ the near-miss census
    //
    // A founding rule quantified over the whole population is only as strong as its worst member,
    // and when a species is missing from the family the reason is invisible in the family itself.
    // This census makes the cascade a measurement: for each candidate pair, how many statements
    // refuse it, and which. It is the instrument that found the reader's `:=` defect.
    println!();
    println!("{}", "=".repeat(100));
    println!("[0]  THE NEAR-MISS CENSUS  --  what a species costs, and who refuses it");
    println!("{}", "=".repeat(100));
    println!();

    let candidates: [(char, char); 8] = [
        ('(', ')'),
        ('{', '}'),
        ('[', ']'),
        ('⟨', '⟩'),
        ('⦃', '⦄'),
        ('⟮', '⟯'),
        ('⁅', '⁆'),
        ('⟪', '⟫'),
    ];
    let mut refusals: Vec<((char, char), Vec<&String>)> = Vec::new();
    for (open, close) in candidates {
        let refusing: Vec<&String> = statements
            .iter()
            .filter(|statement| {
                let mut depth = 0i64;
                for symbol in statement.chars() {
                    if symbol == open {
                        depth += 1;
                    } else if symbol == close {
                        depth -= 1;
                        if depth < 0 {
                            return true;
                        }
                    }
                }
                depth != 0
            })
            .collect();
        refusals.push(((open, close), refusing));
    }
    refusals.sort_by_key(|(_, refusing)| refusing.len());
    println!(
        "  {:<8} {:>10}   {}",
        "species", "refusing", "the statements that refuse it"
    );
    for ((open, close), refusing) in &refusals {
        println!("  {open}{close:<7} {:>10}", refusing.len());
        for statement in refusing.iter().take(2) {
            println!("             {}", clipped(&statement, 96));
        }
        if refusing.len() > 2 {
            println!("             ... {} more", refusing.len() - 2);
        }
    }

    // ------------------------------------------------------------------ the grammar
    println!();
    println!("{}", "=".repeat(100));
    println!("[1]  THE GRAMMAR, FOUNDED  --  the bracket species, the separator, the split");
    println!("{}", "=".repeat(100));
    println!();

    let Ok(grammar) = recover(&statements) else {
        println!("  the population founds no grammar");
        return;
    };

    let family: Vec<String> = grammar
        .bracket_family()
        .iter()
        .map(|(open, close)| format!("{open}{close}"))
        .collect();
    println!(
        "  bracket species founded    {}   [{}]",
        family.len(),
        family.join(" ")
    );
    println!("  the single-pair reading    {:?}", grammar.bracket());
    println!("  separator                  {:?}", grammar.separator());
    println!(
        "  depth-zero occurrences     {:?}",
        grammar.separator_occurrences()
    );
    println!(
        "  orientation load-bearing   {}   (this reading took the {} founding occurrence)",
        grammar.orientation_is_load_bearing(),
        grammar.orientation()
    );
    println!();
    println!(
        "  A family of {} species is what the material groups in. One pair could not found the",
        family.len()
    );
    println!(
        "  depth at all here, and with a flat depth no split is founded either -- one refusal"
    );
    println!("  cascading into three. Each group carries WHICH species opened it, recovered.");
    println!();
    print_aperture(&grammar, "the aperture, by species:");

    // the species census, which is the founded classification the family made expressible
    let mut species_census: BTreeMap<String, usize> = BTreeMap::new();
    let mut split_founded = 0usize;
    for reading in grammar.readings() {
        if reading.split_at.is_some() {
            split_founded += 1;
        }
        for group in &reading.binders {
            if let Some((open, close)) = group.species {
                species_census
                    .entry(format!("{open}{close}"))
                    .and_modify(|count| *count += 1)
                    .or_insert(1);
            }
        }
    }
    println!();
    println!(
        "  statements split           {split_founded} of {}",
        grammar.readings().len()
    );
    println!("  suppositions by species    (nobody named these; the material exhibits them)");
    for (species, count) in &species_census {
        println!("    {species}   {count}");
    }

    // ------------------------------------------------------------------ the orientation orbit
    println!();
    println!("{}", "=".repeat(100));
    println!("[2]  THE ORIENTATION ORBIT  --  both readings, over the same material");
    println!("{}", "=".repeat(100));
    println!();

    let first = recover_under(&statements, SeparatorOrientation::First).expect("recovers");
    let moved: Vec<(&str, Option<usize>, Option<usize>)> = grammar
        .readings()
        .iter()
        .zip(first.readings())
        .filter(|(last, first)| last.split_at != first.split_at)
        .map(|(last, first)| (last.statement.as_str(), first.split_at, last.split_at))
        .collect();
    println!(
        "  statements whose split moved between the two orientations   {}",
        moved.len()
    );
    println!();
    println!(
        "  The split is chosen by the MATERIAL wherever one candidate leaves a leading region"
    );
    println!("  of groups and whitespace. The orientation is the tiebreak, and where the material");
    println!("  decides, the two readings are the same map -- which is what makes the difference");
    println!("  below evidence rather than an artifact of the instrument.");
    for (statement, at_first, at_last) in moved.iter().take(3) {
        println!();
        println!("    {}", clipped(&statement, 110));
        println!("      first  {at_first:?}      last  {at_last:?}");
    }

    // ------------------------------------------------------------------ the relation, one scale down
    println!();
    println!("{}", "=".repeat(100));
    println!("[3]  THE SAME ORGAN, ONE SCALE DOWN  --  the conclusion's own split");
    println!("{}", "=".repeat(100));
    println!();

    let mut conclusions: BTreeSet<String> = BTreeSet::new();
    let mut conclusion_of: BTreeMap<String, String> = BTreeMap::new();
    for reading in grammar.readings() {
        let Some(split) = reading.split_at else {
            continue;
        };
        let conclusion = reading.statement[split + 1..].trim();
        if conclusion.is_empty() {
            continue;
        }
        conclusions.insert(conclusion.to_owned());
        conclusion_of
            .entry(conclusion.to_owned())
            .or_insert_with(|| reading.statement.clone());
    }
    println!("  conclusions                {}", conclusions.len());
    println!();
    println!(
        "  A conclusion is a statement at a smaller scale, so the identical organ is applied to"
    );
    println!(
        "  it. Nothing is told that `=` relates two sides; the population exhibits a character"
    );
    println!("  standing at depth zero throughout, and the recovery founds it.");
    println!();

    // The relation population: conclusions that carry a relation founded over the sub-population.
    // `recover` over ALL conclusions would refuse, because not every conclusion is a relation. The
    // population is therefore the conclusions sharing a candidate, which the material selects.
    let family_chars: BTreeSet<char> = grammar
        .bracket_family()
        .iter()
        .flat_map(|(open, close)| [*open, *close])
        .collect();
    let mut relation_candidates: BTreeMap<char, BTreeSet<String>> = BTreeMap::new();
    for conclusion in &conclusions {
        // a relation is asserted at the conclusion's OWN depth; a symbol inside a group belongs to
        // the group, which is the same law the split is founded on, one scale down
        let mut expected: Vec<char> = Vec::new();
        let mut once: BTreeSet<char> = BTreeSet::new();
        for symbol in conclusion.chars() {
            if let Some((_, close)) = grammar
                .bracket_family()
                .iter()
                .find(|(open, _)| *open == symbol)
            {
                expected.push(*close);
                continue;
            }
            if family_chars.contains(&symbol) {
                if expected.last() == Some(&symbol) {
                    expected.pop();
                }
                continue;
            }
            if expected.is_empty() && !symbol.is_alphanumeric() && !symbol.is_whitespace() {
                once.insert(symbol);
            }
        }
        for symbol in once {
            relation_candidates
                .entry(symbol)
                .or_default()
                .insert(conclusion.clone());
        }
    }
    let mut relations_by_symbol: Vec<(char, usize)> = relation_candidates
        .iter()
        .map(|(symbol, carried)| (*symbol, carried.len()))
        .collect();
    relations_by_symbol.sort_by_key(|(symbol, count)| (std::cmp::Reverse(*count), *symbol));
    println!("  the relation symbols the conclusions exhibit, by how many carry them:");
    for (symbol, count) in relations_by_symbol.iter().take(SHOWN) {
        println!("    {symbol:?}   {count}");
    }

    // ------------------------------------------------------------------ identities and permutations
    println!();
    println!("{}", "=".repeat(100));
    println!(
        "[4]  THE IDENTITY ATLAS  --  every identity is a permutation, and the heads found groups"
    );
    println!("{}", "=".repeat(100));
    println!();

    let relation_symbol = relations_by_symbol
        .first()
        .map(|(symbol, _)| *symbol)
        .unwrap_or('=');
    let population: BTreeSet<String> = relation_candidates
        .get(&relation_symbol)
        .cloned()
        .unwrap_or_default();
    println!(
        "  the relation founded       {relation_symbol:?}   carried by {} conclusions",
        population.len()
    );

    let sides = recover(&population).ok();
    let mut relations: Vec<Relation> = Vec::new();
    if let Some(sides) = &sides {
        println!("  its own recovered split    {:?}", sides.separator());
        for reading in sides.readings() {
            let Some(split) = reading.split_at else {
                continue;
            };
            let symbol_width = reading.statement[split..]
                .chars()
                .next()
                .map_or(1, char::len_utf8);
            let Some(left) = read_side(reading.statement[..split].trim(), grammar.bracket_family())
            else {
                continue;
            };
            let Some(right) = read_side(
                reading.statement[split + symbol_width..].trim(),
                grammar.bracket_family(),
            ) else {
                continue;
            };
            let whole = conclusion_of
                .get(&reading.statement)
                .cloned()
                .unwrap_or_else(|| reading.statement.clone());
            let bound = bindings_of.get(&whole).cloned().unwrap_or_default();
            let left_is_bound = bound.contains(&left.0);
            let right_is_bound = bound.contains(&right.0);
            relations.push(Relation {
                statement: whole,
                conclusion: reading.statement.clone(),
                left,
                right,
                left_is_bound,
                right_is_bound,
            });
        }
    }
    println!("  relations both sides read  {}", relations.len());

    // the ones relating one head to itself: these are the identities that can carry a symmetry
    let mut by_head: BTreeMap<String, Vec<&Relation>> = BTreeMap::new();
    let mut cross_head = 0usize;
    for relation in &relations {
        if relation.left.0 == relation.right.0 {
            by_head
                .entry(relation.left.0.clone())
                .or_default()
                .push(relation);
        } else {
            cross_head += 1;
        }
    }
    println!(
        "  relating ONE head to itself {}   relating two heads {cross_head}",
        by_head.values().map(Vec::len).sum::<usize>()
    );
    println!();
    println!("  A relation between two applications of one head rearranges its arguments. That");
    println!(
        "  rearrangement is a permutation -- an element of a group -- and it is computed from"
    );
    println!("  the argument tokens alone. This driver writes neither side.");
    println!();

    let mut groups: Vec<(String, BTreeSet<Vec<usize>>, BTreeSet<Vec<usize>>, usize)> = Vec::new();
    let mut not_symmetries: Vec<(&Relation, String)> = Vec::new();
    for (head, family) in &by_head {
        let mut generators: BTreeSet<Vec<usize>> = BTreeSet::new();
        let mut witnesses = 0usize;
        for relation in family {
            match rearrangement(&relation.left.1, &relation.right.1) {
                Rearrangement::Permutation(sigma) => {
                    if sigma != identity_of(sigma.len()) {
                        generators.insert(sigma);
                    }
                    witnesses += 1;
                }
                Rearrangement::NotASymmetry { reason } => {
                    not_symmetries.push((relation, reason));
                }
            }
        }
        if generators.is_empty() {
            continue;
        }
        // generators of one degree only: a head applied at two arities is two operations
        let mut by_degree: BTreeMap<usize, BTreeSet<Vec<usize>>> = BTreeMap::new();
        for sigma in generators {
            by_degree.entry(sigma.len()).or_default().insert(sigma);
        }
        for (_, of_one_degree) in by_degree {
            if let Some(closed) = generated(&of_one_degree) {
                groups.push((head.clone(), of_one_degree, closed, witnesses));
            }
        }
    }
    groups.sort_by_key(|(head, _, closed, _)| (std::cmp::Reverse(closed.len()), head.clone()));

    println!(
        "  {:<34} {:>6} {:>7} {:>9}  {}",
        "head", "degree", "order", "abelian", "generators"
    );
    for (head, generators, closed, _) in groups.iter().take(SHOWN * 2) {
        let degree = closed.iter().next().map_or(0, Vec::len);
        let rendered: Vec<String> = generators
            .iter()
            .map(|sigma| render_permutation(sigma))
            .collect();
        println!(
            "  {head:<34} {degree:>6} {:>7} {:>9}  {}",
            closed.len(),
            is_abelian(closed),
            rendered.join(" ")
        );
    }
    if groups.len() > SHOWN * 2 {
        println!(
            "  ... {} further heads, all retained",
            groups.len() - SHOWN * 2
        );
    }

    println!();
    println!("  and the identity each generator IS, in the material's own words:");
    let mut shown = 0usize;
    for (head, _, _, _) in &groups {
        let Some(family) = by_head.get(head) else {
            continue;
        };
        for relation in family {
            if let Rearrangement::Permutation(sigma) =
                rearrangement(&relation.left.1, &relation.right.1)
            {
                if sigma == identity_of(sigma.len()) {
                    continue;
                }
                println!();
                println!("    {}", relation.conclusion);
                println!(
                    "      head {:?}   sigma {}   order of this element {}",
                    head,
                    render_permutation(&sigma),
                    order_of(&sigma)
                );
                shown += 1;
                break;
            }
        }
        if shown >= 6 {
            break;
        }
    }

    println!();
    println!(
        "  THE FALSIFIER  --  transports that are NOT symmetries, retained rather than dropped:"
    );
    println!("    {}", not_symmetries.len());
    for (relation, reason) in not_symmetries.iter().take(4) {
        println!();
        println!("    {}", clipped(&relation.conclusion, 108));
        println!("      refused as a symmetry: {reason}");
    }

    // ------------------------------------------------------------------ the compression
    println!();
    println!("{}", "=".repeat(100));
    println!("[5]  THE COMPRESSION  --  identities identified up to a rebase, with the remainder");
    println!("{}", "=".repeat(100));
    println!();

    let mut by_rebase: BTreeMap<String, Vec<&Relation>> = BTreeMap::new();
    for relation in &relations {
        by_rebase
            .entry(rebased(relation))
            .or_default()
            .push(relation);
    }
    let collapsed: Vec<(&String, &Vec<&Relation>)> = by_rebase
        .iter()
        .filter(|(_, carried)| carried.len() > 1)
        .collect();
    let singletons = by_rebase.len() - collapsed.len();
    println!("  relations                  {}", relations.len());
    println!("  rebased forms              {}", by_rebase.len());
    println!(
        "  forms carrying more than one   {}   singletons {singletons}",
        collapsed.len()
    );
    println!();
    println!("  A rebase renames; it does not lose. Two identities sharing a rebased form are one");
    println!(
        "  identity in two alphabets, and that is a compression whose remainder is ZERO. What"
    );
    println!("  the rebase cannot identify is the remainder, and it is the singleton population.");
    println!();
    for (form, carried) in collapsed.iter().take(SHOWN * 3) {
        println!("    {form}");
        for relation in carried.iter().take(3) {
            println!("      <- {}", clipped(&relation.conclusion, 96));
        }
        if carried.len() > 3 {
            println!("      ... {} more", carried.len() - 3);
        }
    }
    if collapsed.len() > SHOWN * 3 {
        println!(
            "    ... {} further forms, all retained",
            collapsed.len() - SHOWN * 3
        );
    }

    // ------------------------------------------------------------------ the transport atlas
    println!();
    println!("{}", "=".repeat(100));
    println!("[6]  THE TRANSPORT ATLAS  --  what each head admits, and the verdict on each");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  A head's transports are the rebased forms its identities take. Read as a table this"
    );
    println!("  is what a reference page for that operation would carry, and nothing in it was");
    println!("  written here: every row is one statement of the corpus with its letters rebased.");
    println!();
    println!("  A same-head relation is one of THREE species, founded from the two argument lists");
    println!("  and from nothing else:");
    println!();
    println!(
        "    SYMMETRY      the right arguments are the left ones rearranged -- a permutation,"
    );
    println!("                  and an element of the head's own group");
    println!(
        "    SUBSTITUTION  the same arity, with some position carrying a different construction"
    );
    println!("                  -- the head is invariant under changing that position");
    println!("    ARITY MOVE    the two sides apply the head to different numbers of arguments");
    println!();
    println!("  The verdict is on the SYMMETRY question only, two-sided and decided by zero-ness:");
    println!("  ADMITTED where every same-head relation is a symmetry, CONFLICTED where the head");
    println!("  carries both a symmetry and a substitution -- which says its behaviour depends on");
    println!("  something its name does not carry, and is the junction reading, not a fault.");
    println!();
    println!(
        "  APERTURE: a head with no symmetry here is one THIS MATERIAL states none for. `dist`"
    );
    println!(
        "  is symmetric and mathlib says so in `Topology`, which this subtree does not contain."
    );
    println!();

    #[derive(Default)]
    struct HeadReading {
        symmetries: usize,
        substitutions: usize,
        arity_moves: usize,
        forms: BTreeSet<String>,
    }

    let mut heads: BTreeMap<String, HeadReading> = BTreeMap::new();
    for relation in &relations {
        let entry = heads.entry(relation.left.0.clone()).or_default();
        entry.forms.insert(rebased(relation));
        if relation.left.0 != relation.right.0 {
            continue;
        }
        match rearrangement(&relation.left.1, &relation.right.1) {
            Rearrangement::Permutation(_) => entry.symmetries += 1,
            Rearrangement::NotASymmetry { .. } => {
                if relation.left.1.len() == relation.right.1.len() {
                    entry.substitutions += 1;
                } else {
                    entry.arity_moves += 1;
                }
            }
        }
    }
    let mut ranked: Vec<(&String, &HeadReading)> = heads
        .iter()
        .filter(|(_, reading)| reading.forms.len() > 1)
        .collect();
    ranked.sort_by_key(|(head, reading)| (std::cmp::Reverse(reading.forms.len()), (*head).clone()));

    let verdict = |reading: &HeadReading| match (
        reading.symmetries,
        reading.substitutions + reading.arity_moves,
    ) {
        (0, 0) => "OPEN -- no same-head relation here",
        (_, 0) => "ADMITTED",
        (0, _) => "NO SYMMETRY STATED IN THIS MATERIAL",
        _ => "CONFLICTED -- a junction",
    };
    for (head, reading) in ranked.iter().take(SHOWN) {
        println!(
            "  {head}   {} transports   symmetry {} substitution {} arity {}   {}",
            reading.forms.len(),
            reading.symmetries,
            reading.substitutions,
            reading.arity_moves,
            verdict(reading)
        );
        for form in reading.forms.iter().take(SHOWN) {
            println!("      {form}");
        }
        if reading.forms.len() > SHOWN {
            println!("      ... {} more", reading.forms.len() - SHOWN);
        }
        println!();
    }
    let admitted = heads
        .values()
        .filter(|reading| {
            reading.symmetries > 0 && reading.substitutions + reading.arity_moves == 0
        })
        .count();
    let conflicted = heads
        .values()
        .filter(|reading| reading.symmetries > 0 && reading.substitutions + reading.arity_moves > 0)
        .count();
    let silent = heads
        .values()
        .filter(|reading| {
            reading.symmetries == 0 && reading.substitutions + reading.arity_moves > 0
        })
        .count();
    println!(
        "  heads reached {}   ADMITTED {admitted}   CONFLICTED {conflicted}   no symmetry stated \
         {silent}   the rest carry no same-head relation at all",
        heads.len()
    );

    // ------------------------------------------------------------------ the transport graph
    println!();
    println!("{}", "=".repeat(100));
    println!("[7]  THE TRANSPORT GRAPH  --  how to get from one operation to another");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  A relation between TWO heads is an edge: it says this operation may be re-presented"
    );
    println!("  as that one. The rebased form is the edge's own label, and composing two edges is");
    println!("  composing two transports -- a route through the atlas rather than a lookup in it.");
    println!();

    let mut edges: BTreeMap<(String, String), BTreeSet<String>> = BTreeMap::new();
    let mut variable_headed: Vec<&Relation> = Vec::new();
    let mut numeral_headed: Vec<&Relation> = Vec::new();
    for relation in &relations {
        if relation.left.0 == relation.right.0 {
            continue;
        }
        // a head its own statement binds is a variable standing where an operation would; the
        // reader founds that, and the two are not the same node
        //
        // And a head written entirely in digits is a NUMERAL, which is an orthographic property of
        // the material and not a list this file wrote. Numerals are the target of very many
        // transports, so leaving them in makes them the graph's hubs and routes every deep chain
        // through them — measured, on the library's twelve-step chain, which passed through `0`
        // and `1`.
        let is_numeral = |head: &str| head.chars().all(|symbol| symbol.is_numeric());
        if relation.left_is_bound || relation.right_is_bound {
            variable_headed.push(relation);
            continue;
        }
        if is_numeral(&relation.left.0) || is_numeral(&relation.right.0) {
            numeral_headed.push(relation);
            continue;
        }
        edges
            .entry((relation.left.0.clone(), relation.right.0.clone()))
            .or_default()
            .insert(rebased(relation));
    }
    println!(
        "  relations whose head is a name the statement itself binds   {}",
        variable_headed.len()
    );
    println!(
        "  relations whose head is a numeral                            {}",
        numeral_headed.len()
    );
    println!("  held out of the graph, because a bound name is a variable and not an operation:");
    for relation in variable_headed.iter().take(3) {
        println!("    {}", clipped(&relation.conclusion, 104));
    }
    println!();
    let mut degree: BTreeMap<&str, (usize, usize)> = BTreeMap::new();
    for (from, to) in edges.keys() {
        degree.entry(from.as_str()).or_default().0 += 1;
        degree.entry(to.as_str()).or_default().1 += 1;
    }
    let mut by_reach: Vec<(&&str, &(usize, usize))> = degree.iter().collect();
    by_reach.sort_by_key(|(head, (out, into))| (std::cmp::Reverse(out + into), **head));
    println!("  heads               {}", degree.len());
    println!("  directed edges      {}", edges.len());
    println!();
    println!("  {:<40} {:>6} {:>8}", "head", "out", "in");
    for (head, (out, into)) in by_reach.iter().take(SHOWN) {
        println!("  {head:<40} {out:>6} {into:>8}");
    }

    // routes of two: an operation reached through an intermediary it is never directly related to
    let mut routes: Vec<(String, String, String)> = Vec::new();
    for ((from, middle), _) in &edges {
        for ((second, to), _) in &edges {
            if second != middle || to == from {
                continue;
            }
            if edges.contains_key(&(from.clone(), to.clone())) {
                continue;
            }
            routes.push((from.clone(), middle.clone(), to.clone()));
        }
    }
    routes.sort();
    routes.dedup();
    // --- the route atlas: how far a transport composes
    //
    // Walking every simple route is exponential and does not return on this graph -- measured, by
    // running it to a ten-minute wall at library scale while returning in seconds on one subtree.
    // The exact linear form contracts each strongly connected component to a point, which is
    // precisely "an operation reachable from itself is one loop rather than unboundedly many
    // routes", then takes the longest chain on the acyclic quotient by topological order. Nothing
    // is sampled and no depth is capped.
    let mut successors: BTreeMap<&str, Vec<&str>> = BTreeMap::new();
    let mut nodes: BTreeSet<&str> = BTreeSet::new();
    for (from, to) in edges.keys() {
        successors
            .entry(from.as_str())
            .or_default()
            .push(to.as_str());
        nodes.insert(from.as_str());
        nodes.insert(to.as_str());
    }
    let order: Vec<&str> = nodes.iter().copied().collect();
    let index_of: BTreeMap<&str, usize> =
        order.iter().enumerate().map(|(at, n)| (*n, at)).collect();
    let count = order.len();

    // Kosaraju: two linear passes, iterative so a deep graph cannot exhaust the stack
    let mut reversed: Vec<Vec<usize>> = vec![Vec::new(); count];
    let mut forward: Vec<Vec<usize>> = vec![Vec::new(); count];
    for (from, to) in edges.keys() {
        let (left, right) = (index_of[from.as_str()], index_of[to.as_str()]);
        forward[left].push(right);
        reversed[right].push(left);
    }
    let mut seen = vec![false; count];
    let mut finished: Vec<usize> = Vec::with_capacity(count);
    for start in 0..count {
        if seen[start] {
            continue;
        }
        let mut work = vec![(start, 0usize)];
        seen[start] = true;
        while let Some((node, at)) = work.pop() {
            if at < forward[node].len() {
                work.push((node, at + 1));
                let next = forward[node][at];
                if !seen[next] {
                    seen[next] = true;
                    work.push((next, 0));
                }
            } else {
                finished.push(node);
            }
        }
    }
    let mut component = vec![usize::MAX; count];
    let mut components = 0usize;
    for start in finished.iter().rev().copied() {
        if component[start] != usize::MAX {
            continue;
        }
        let mut work = vec![start];
        component[start] = components;
        while let Some(node) = work.pop() {
            for next in &reversed[node] {
                if component[*next] == usize::MAX {
                    component[*next] = components;
                    work.push(*next);
                }
            }
        }
        components += 1;
    }
    let mut members = vec![0usize; components];
    for at in 0..count {
        members[component[at]] += 1;
    }
    let cyclic = members.iter().filter(|size| **size > 1).count();

    let mut quotient: Vec<BTreeSet<usize>> = vec![BTreeSet::new(); components];
    let mut incoming = vec![0usize; components];
    for (from, to) in edges.keys() {
        let (left, right) = (
            component[index_of[from.as_str()]],
            component[index_of[to.as_str()]],
        );
        if left != right && quotient[left].insert(right) {
            incoming[right] += 1;
        }
    }
    let mut ready: Vec<usize> = (0..components).filter(|at| incoming[*at] == 0).collect();
    let mut depth = vec![0usize; components];
    let mut through: Vec<Option<usize>> = vec![None; components];
    let mut settled = 0usize;
    while let Some(node) = ready.pop() {
        settled += 1;
        let onward: Vec<usize> = quotient[node].iter().copied().collect();
        for next in onward {
            if depth[node] + 1 > depth[next] {
                depth[next] = depth[node] + 1;
                through[next] = Some(node);
            }
            incoming[next] -= 1;
            if incoming[next] == 0 {
                ready.push(next);
            }
        }
    }
    let mut depth_census: BTreeMap<usize, usize> = BTreeMap::new();
    for carried in &depth {
        *depth_census.entry(*carried).or_insert(0) += 1;
    }
    println!();
    println!("  THE ROUTE ATLAS -- the longest transport chain, exactly, with loops contracted");
    println!("  operations {count}   components {components}   of which carry a loop {cyclic}");
    println!("  components settled by the topological order {settled} of {components}");
    println!("  longest chain ending at a component, by length:");
    for (length, at_that_depth) in depth_census.iter().rev().take(10) {
        println!("    {length:>3} steps   {at_that_depth} components");
    }
    if components == 0 {
        println!();
        println!("  the transport graph is EMPTY on this material, so there is no chain to walk.");
        println!("  That is a return about the codec: a transport edge is a relation between two");
        println!("  named constructions, and this codec does not assert those where the reading");
        println!("  looked. Section [3] above says where its conclusions actually live.");
        println!();
        println!("  two-step routes with NO direct edge   0");
        return;
    }
    let deepest_at = (0..components).max_by_key(|at| depth[*at]).unwrap_or(0);
    let mut chain: Vec<usize> = vec![deepest_at];
    let mut walk = deepest_at;
    while let Some(previous) = through[walk] {
        chain.push(previous);
        walk = previous;
    }
    chain.reverse();
    let mut representative: Vec<&str> = vec![""; components];
    for at in (0..count).rev() {
        representative[component[at]] = order[at];
    }
    println!();
    println!(
        "  the deepest transport chain the corpus licenses and states in no single theorem ({} steps):",
        chain.len().saturating_sub(1)
    );
    let rendered: Vec<&str> = chain.iter().map(|at| representative[*at]).collect();
    for window in rendered.chunks(6) {
        println!("    {}", window.join("  ->  "));
    }

    println!();
    println!("  two-step routes with NO direct edge   {}", routes.len());
    println!("  These are the compositions the corpus never states in one theorem. Each is a");
    println!("  transport the material licenses and does not spell out.");
    for (from, middle, to) in routes.iter().take(SHOWN) {
        println!("    {from}  ->  {middle}  ->  {to}");
    }
    if routes.len() > SHOWN {
        println!("    ... {} more", routes.len() - SHOWN);
    }

    // ------------------------------------------------------------------ the emission
    println!();
    println!("{}", "=".repeat(100));
    println!("[8]  THE EMISSION  --  the atlas as processed data");
    println!("{}", "=".repeat(100));
    println!();

    let leaf = declared
        .rsplit('/')
        .next()
        .unwrap_or("material")
        .to_lowercase();
    let deposit = root.join("meta").join(format!("IDENTITY_ATLAS_{leaf}.tsv"));
    let mut rows = vec![["kind", "head", "detail", "form", "witness"].join("\t")];
    for (head, generators, closed, _) in &groups {
        let degree = closed.iter().next().map_or(0, Vec::len);
        for sigma in generators {
            rows.push(
                [
                    "symmetry",
                    head.as_str(),
                    &format!(
                        "degree {degree} order {} abelian {}",
                        closed.len(),
                        is_abelian(closed)
                    ),
                    &render_permutation(sigma),
                    "",
                ]
                .join("\t"),
            );
        }
    }
    for (head, reading) in &heads {
        for form in &reading.forms {
            rows.push(
                [
                    "transport",
                    head.as_str(),
                    &format!(
                        "symmetry {} substitution {} arity {}",
                        reading.symmetries, reading.substitutions, reading.arity_moves
                    ),
                    form.as_str(),
                    "",
                ]
                .join("\t"),
            );
        }
    }
    for ((from, to), forms) in &edges {
        for form in forms {
            rows.push(["edge", from.as_str(), to.as_str(), form.as_str(), ""].join("\t"));
        }
    }
    for (form, carried) in &by_rebase {
        for relation in carried {
            rows.push(
                [
                    "identity",
                    relation.left.0.as_str(),
                    "",
                    form.as_str(),
                    relation.statement.as_str(),
                ]
                .join("\t"),
            );
        }
    }
    let written = rows.len() - 1;
    match fs::write(&deposit, rows.join("\n") + "\n") {
        Ok(()) => {
            println!(
                "  wrote {}   {written} rows",
                deposit.strip_prefix(&root).unwrap_or(&deposit).display()
            );
            println!();
            println!("  Columns: kind, head, detail, form, witness. Four kinds:");
            println!("    symmetry    a head, its group's degree and order, and one generator");
            println!(
                "    transport   a head and one rebased form it takes, with its species census"
            );
            println!(
                "    edge        one head re-presented as another, labelled by the rebased form"
            );
            println!(
                "    identity    one rebased form and the statement of the corpus it came from"
            );
            println!();
            println!(
                "  The witness column carries the corpus statement verbatim, so every row in the"
            );
            println!(
                "  atlas can be taken back to the material it was read off. An atlas whose rows"
            );
            println!("  cannot be reopened is a summary, and a summary is not a deposit.");
        }
        Err(refusal) => println!("  the deposit was refused: {refusal}"),
    }

    // ------------------------------------------------------------------ the crossing word
    println!();
    println!("{}", "=".repeat(100));
    println!("[9]  THE PROOF IS A WORD  --  crossings as binary states over a causal order");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  A proof is a sequence of moves. Each move is a CROSSING and its state is binary --"
    );
    println!("  the move is either in the word or not -- so a proof is a subset, and two proofs");
    println!("  compose by symmetric difference. That is exactly the grading group of");
    println!("  `multiquadratic`, the twisted group algebra of (Z/2)^n over Q, whose own opening");
    println!("  says the crossing-word algebra and the turn-composition algebra are one algebra.");
    println!();
    println!(
        "  Each distinct move is given a distinct PRIME, so the generators are independent by"
    );
    println!("  construction. A move used twice contributes sqrt(p)*sqrt(p) = p and leaves the");
    println!("  grading: it CANCELS. So the word of a proof splits exactly two ways --");
    println!();
    println!("    the GRADE        the moves used an ODD number of times -- what survives");
    println!(
        "    the COEFFICIENT  the product of primes used an EVEN number of times -- what cancelled"
    );
    println!();
    println!(
        "  BOUND, stated because it is real: this algebra is COMMUTATIVE, so the word forgets"
    );
    println!(
        "  the order in which the moves were made and keeps only their parity. It records what"
    );
    println!(
        "  survived cancellation, never the sequence. A carrier that keeps the order would have"
    );
    println!(
        "  to be non-commutative, and that is `structure_group::curvature_commutator`'s subject."
    );
    println!();

    // the moves a proof made, read off the declaration's own tactic population
    let mut moves_of: BTreeMap<String, BTreeMap<String, u32>> = BTreeMap::new();
    for file in &files {
        let Ok(text) = fs::read_to_string(file) else {
            continue;
        };
        let reading = read_development(&text, DeclarationGrain::EveryTopLevelDeclaration);
        for form in &reading.declarations {
            if form.former != "theorem" && form.former != "lemma" {
                continue;
            }
            let statement = form.statement.trim();
            if statement.is_empty() || form.tactics.is_empty() {
                continue;
            }
            moves_of
                .entry(statement.to_owned())
                .or_insert_with(|| form.tactics.clone());
        }
    }

    // each distinct move gets a distinct prime, assigned in the material's own sorted order
    let mut vocabulary: BTreeSet<&str> = BTreeSet::new();
    for tactics in moves_of.values() {
        for tactic in tactics.keys() {
            vocabulary.insert(tactic.as_str());
        }
    }
    let mut primes: Vec<u64> = Vec::new();
    let mut candidate = 2u64;
    while primes.len() < vocabulary.len() {
        if (2..candidate)
            .take_while(|d| d * d <= candidate)
            .all(|d| candidate % d != 0)
        {
            primes.push(candidate);
        }
        candidate += 1;
    }
    let prime_of: BTreeMap<&str, u64> = vocabulary
        .iter()
        .copied()
        .zip(primes.iter().copied())
        .collect();
    println!("  distinct moves in this material   {}", vocabulary.len());
    println!("  proofs read                       {}", moves_of.len());

    // the word of one proof: (grade, cancelled)
    let word_of = |tactics: &BTreeMap<String, u32>| -> (BTreeSet<String>, Rat) {
        let mut grade: BTreeSet<String> = BTreeSet::new();
        let mut cancelled = Rat::one();
        for (tactic, count) in tactics {
            if count % 2 == 1 {
                grade.insert(tactic.clone());
            }
            let pairs = count / 2;
            if pairs > 0 {
                let prime = Rat::from_integer(BigInt::from(prime_of[tactic.as_str()]));
                for _ in 0..pairs {
                    cancelled *= &prime;
                }
            }
        }
        (grade, cancelled)
    };

    // the identification with the algebra, verified rather than asserted, on the words small
    // enough to materialise 2^n coefficients for
    const GENERATOR_APERTURE: usize = 8;
    let kernel_bound = primes
        .last()
        .copied()
        .map_or(64u64, |largest| (largest as f64).sqrt() as u64 + 2);
    let mut verified = 0usize;
    let mut refused_for_aperture = 0usize;
    for tactics in moves_of.values() {
        let (grade, cancelled) = word_of(tactics);
        if grade.len() > GENERATOR_APERTURE {
            refused_for_aperture += 1;
            continue;
        }
        // build the same word by actually multiplying in the algebra
        let mut carried = Multiquadratic::one();
        let mut ok = true;
        for (tactic, count) in tactics {
            let radicand = Rat::from_integer(BigInt::from(prime_of[tactic.as_str()]));
            // `squarefree_kernel` refuses a kernel above `bound²`, so the bound must reach the
            // square root of the largest prime this material needs. Measured: 3,423 distinct moves
            // puts the largest prime near 32,000, and a bound of 64 refused every word — the
            // certificate reached 19 of 79,189 for that reason and for no reason in the algebra.
            let Ok(root) = Multiquadratic::square_root(&radicand, kernel_bound) else {
                ok = false;
                break;
            };
            for _ in 0..*count {
                match carried.multiply(&root, GENERATOR_APERTURE) {
                    Ok(product) => carried = product,
                    Err(_) => {
                        ok = false;
                        break;
                    }
                }
            }
            if !ok {
                break;
            }
        }
        if !ok {
            refused_for_aperture += 1;
            continue;
        }
        let algebra_grade: BTreeSet<String> = carried
            .generators()
            .iter()
            .filter_map(|generator| {
                let value = generator.to_string().parse::<u64>().ok()?;
                prime_of
                    .iter()
                    .find(|(_, prime)| **prime == value)
                    .map(|(tactic, _)| (*tactic).to_owned())
            })
            .collect();
        assert_eq!(
            algebra_grade, grade,
            "the parity reading and the algebra must agree on every word they both reach"
        );
        // the top coefficient is the cancelled rational scaling the surviving root product
        let top = carried
            .coefficients()
            .last()
            .cloned()
            .unwrap_or_else(Rat::zero);
        assert_eq!(top, cancelled, "and on what cancelled");
        verified += 1;
    }
    println!(
        "  words verified AGAINST the algebra {verified}   refused past the {GENERATOR_APERTURE}-generator aperture {refused_for_aperture}"
    );
    // the aperture is a resource statement about the CARRIER and not about the reading: an element
    // materialises 2^n rational coefficients and one product costs 4^n, so the grade sizes the
    // material exhibits say exactly how far the certificate can reach and where the parity reading
    // carries alone
    let mut grade_census: BTreeMap<usize, usize> = BTreeMap::new();
    for tactics in moves_of.values() {
        let (grade, _) = word_of(tactics);
        *grade_census.entry(grade.len()).or_insert(0) += 1;
    }
    println!("  grade sizes the material exhibits — the parity reading carries every one:");
    let mut listed = 0usize;
    let mut tail = 0usize;
    for (size, at_that_size) in &grade_census {
        if listed < 12 {
            println!("    {size:>3} surviving moves   {at_that_size} proofs");
            listed += 1;
        } else {
            tail += at_that_size;
        }
    }
    if tail > 0 {
        println!("    larger grades      {tail} proofs");
    }
    println!(
        "  Both the grade and the cancelled rational are asserted equal to what multiplying in"
    );
    println!(
        "  `multiquadratic` returns, so the parity reading is the algebra and not a paraphrase."
    );
    println!();

    // now compare proofs of ONE identity family -- the compression above supplies the pairs
    let mut same_grade = 0usize;
    let mut different_grade: Vec<(
        &String,
        BTreeSet<String>,
        BTreeSet<String>,
        &String,
        &String,
    )> = Vec::new();
    for (form, carried) in &by_rebase {
        if carried.len() < 2 {
            continue;
        }
        let mut words: Vec<(&String, BTreeSet<String>, Rat)> = Vec::new();
        for relation in carried {
            let Some(tactics) = moves_of.get(&relation.statement) else {
                continue;
            };
            let (grade, cancelled) = word_of(tactics);
            words.push((&relation.statement, grade, cancelled));
        }
        for pair in words.windows(2) {
            let (left_statement, left_grade, _) = &pair[0];
            let (right_statement, right_grade, _) = &pair[1];
            if left_grade == right_grade {
                same_grade += 1;
            } else {
                different_grade.push((
                    form,
                    left_grade.clone(),
                    right_grade.clone(),
                    left_statement,
                    right_statement,
                ));
            }
        }
    }
    println!("  PAIRS OF PROOFS REACHING ONE REBASED IDENTITY");
    println!(
        "    same grade      {same_grade}   the two proofs differ only by moves that cancelled"
    );
    println!(
        "    grade differs   {}   the symmetric difference is the remainder",
        different_grade.len()
    );
    println!();
    println!(
        "  A pair with the same grade is a REBASE between two proofs: they survive to the same"
    );
    println!("  element and what separated them cancelled. A pair whose grades differ carries a");
    println!("  remainder, and the remainder is named -- it is the moves one proof needs an odd");
    println!("  number of times and the other does not.");
    for (form, left, right, left_statement, right_statement) in different_grade.iter().take(4) {
        let only_left: Vec<&str> = left.difference(right).map(String::as_str).collect();
        let only_right: Vec<&str> = right.difference(left).map(String::as_str).collect();
        println!();
        println!("    {form}");
        println!("      {}", clipped(left_statement, 96));
        println!("      {}", clipped(right_statement, 96));
        println!(
            "      REMAINDER   only the first: [{}]   only the second: [{}]",
            only_left.join(" "),
            only_right.join(" ")
        );
    }

    // ------------------------------------------------------------------ the resolvers
    println!();
    println!("{}", "=".repeat(100));
    println!(
        "[10]  THE IDENTITY MEETS ARITHMETIC  --  the founded claim, put to organs that compute"
    );
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  Everything above is a report about a CORPUS: what the writing exhibits. A symmetry"
    );
    println!(
        "  becomes a claim about mathematics only when something computes it. These are organs"
    );
    println!("  that return an exact rational from exact rational arguments, and each one's own");
    println!("  symmetry group is recovered the same way -- by testing every permutation of its");
    println!("  arguments and admitting one only if it holds on EVERY probe.");
    println!();
    println!("  The driver never pairs a resolver with an identity. Matching is by arity, every");
    println!("  same-arity pair is tested, and the arithmetic decides.");
    println!();

    let mut all_resolvers: Vec<&Resolver> = RESOLVERS.iter().collect();
    all_resolvers.push(&HYPERGEOMETRIC);

    struct ResolvedGroup {
        name: &'static str,
        arity: usize,
        group: BTreeSet<Vec<usize>>,
        separates: bool,
    }
    let mut resolved: Vec<ResolvedGroup> = Vec::new();
    for resolver in &all_resolvers {
        let tuples = probes(resolver.arity);
        let values: Vec<Option<Rat>> = tuples
            .iter()
            .map(|tuple| (resolver.evaluate)(tuple))
            .collect();
        let live: Vec<&Rat> = values.iter().flatten().collect();
        let separates = live.windows(2).any(|pair| pair[0] != pair[1]);
        let mut group: BTreeSet<Vec<usize>> = BTreeSet::new();
        for sigma in permutations(resolver.arity) {
            let holds = tuples.iter().all(|tuple| {
                let moved: Vec<Rat> = sigma.iter().map(|from| tuple[*from].clone()).collect();
                match ((resolver.evaluate)(tuple), (resolver.evaluate)(&moved)) {
                    (Some(before), Some(after)) => before == after,
                    // a probe the resolver refuses cannot witness a symmetry either way
                    _ => true,
                }
            });
            if holds {
                group.insert(sigma);
            }
        }
        // the value-preserving permutations form a subgroup; asserting closure catches a defect in
        // the test rather than proving a theorem
        for sigma in &group {
            for tau in &group {
                assert!(
                    group.contains(&compose(sigma, tau)),
                    "{}'s admitted permutations must be closed under composition",
                    resolver.name
                );
            }
        }
        resolved.push(ResolvedGroup {
            name: resolver.name,
            arity: resolver.arity,
            group,
            separates,
        });
    }

    println!(
        "  {:<30} {:>6} {:>7} {:>11}  {}",
        "resolver", "arity", "order", "separates", "group"
    );
    for reading in &resolved {
        let rendered: Vec<String> = reading
            .group
            .iter()
            .filter(|sigma| **sigma != identity_of(reading.arity))
            .map(|sigma| render_permutation(sigma))
            .collect();
        println!(
            "  {:<30} {:>6} {:>7} {:>11}  {}",
            reading.name,
            reading.arity,
            reading.group.len(),
            reading.separates,
            if rendered.is_empty() {
                "identity only".to_owned()
            } else {
                rendered.join(" ")
            }
        );
    }
    println!();
    println!("  `oriented-difference` is the control and returns the identity alone: an identity");
    println!("  confirmed by it and by nothing else would convict the whole test. `cross-ratio`");
    println!("  returns a group of order 4 on four letters -- recovered by exact arithmetic, not");
    println!("  quoted -- and that is the classical invariance of the cross ratio.");
    println!();
    println!(
        "  A resolver that does not SEPARATE is refused: a constant satisfies every permutation"
    );
    println!("  and would confirm anything put to it.");
    println!();
    println!(
        "  HOW MUCH THE TEST CAN SAY, BY ARITY. A permutation group on n letters sits inside a"
    );
    println!(
        "  symmetric group of order n!, so a confirmation at arity 2 distinguishes one of TWO"
    );
    println!("  possibilities and at arity 4 one of twenty-four:");
    for arity in 2..=4usize {
        let total: usize = (1..=arity).product();
        println!(
            "    arity {arity}   permutations {total:>3}   subsets of them a confirmation rules out {:>3}",
            total - 1
        );
    }
    println!();
    println!(
        "  So four confirmations of a two-letter symmetry are NOT four independent facts: every"
    );
    println!(
        "  symmetric binary operation confirms every stated exchange, and the only thing that"
    );
    println!(
        "  can fail there is the control. The discrimination is at the higher arities, and the"
    );
    println!("  cross ratio against the hypergeometric sum is where this run actually separates.");

    println!();
    println!("  THE JOIN  --  each corpus-founded group against every resolver of its arity");
    println!();
    let mut confirmed = 0usize;
    let mut refuted = 0usize;
    let mut unreached = 0usize;
    for (head, _, closed, _) in &groups {
        let degree = closed.iter().next().map_or(0, Vec::len);
        let candidates: Vec<&ResolvedGroup> = resolved
            .iter()
            .filter(|reading| reading.arity == degree && reading.separates)
            .collect();
        if candidates.is_empty() {
            unreached += 1;
            println!(
                "  {head}   degree {degree}   NO RESOLVER OF THIS ARITY -- unreached, not refuted"
            );
            continue;
        }
        let rendered: Vec<String> = closed
            .iter()
            .filter(|sigma| **sigma != identity_of(degree))
            .map(|sigma| render_permutation(sigma))
            .collect();
        println!("  {head}   the corpus states [{}]", rendered.join(" "));
        for reading in candidates {
            let contained = closed.iter().all(|sigma| reading.group.contains(sigma));
            let missing: Vec<String> = closed
                .iter()
                .filter(|sigma| !reading.group.contains(*sigma))
                .map(|sigma| render_permutation(sigma))
                .collect();
            if contained {
                confirmed += 1;
                println!(
                    "      CONFIRMED by {:<28} its own group has order {}",
                    reading.name,
                    reading.group.len()
                );
            } else {
                refuted += 1;
                println!(
                    "      refuted   by {:<28} arithmetic breaks [{}]",
                    reading.name,
                    missing.join(" ")
                );
            }
        }
    }
    println!();
    println!("  corpus groups CONFIRMED by a computing organ   {confirmed}");
    println!("  refuted by one                                 {refuted}");
    println!("  of an arity no resolver reaches                {unreached}");
    println!();
    println!(
        "  A refutation is not a defect in the corpus and not one in the resolver: it says the"
    );
    println!("  two are different operations that share an arity, which is exactly what a test");
    println!("  matched on arity alone should say most of the time. What carries evidence is that");
    println!("  the test CAN refute, and does.");

    // ------------------------------------------------------------------ the closure locus
    println!();
    println!("{}", "=".repeat(100));
    println!("[11]  THE SYMMETRY MEETS THE CLASSIFICATION  --  does the corpus's permutation");
    println!("      preserve what the organ decides?");
    println!("{}", "=".repeat(100));
    println!();
    println!("  The previous station asked a VALUE question: does an organ return the same number");
    println!(
        "  when its arguments are permuted. This asks a STRUCTURE question, which is stronger:"
    );
    println!("  does the permutation preserve the CLASSIFICATION the organ computes?");
    println!();
    println!("  `hypergeometric_closure` decides whether a three-site turning equation's solution");
    println!(
        "  closes -- whether its return group is finite -- by sorting integers on a circle. Its"
    );
    println!(
        "  dials must be exact rationals. A universally quantified statement is a claim about"
    );
    println!(
        "  EVERY instance, so it licenses instantiation: the parameter family is swept HERE, by"
    );
    println!("  this body, and the corpus supplies only the permutation.");
    println!();

    // the swept family: the machine's own material, exact, and it must exhibit every species or
    // the test is vacuous
    let mut dial_values: Vec<Rat> = Vec::new();
    for denominator in 2..=5i64 {
        for numerator in 0..=denominator {
            let value = rational(numerator, denominator);
            if !dial_values.contains(&value) {
                dial_values.push(value);
            }
        }
    }
    dial_values.sort();
    let mut swept: Vec<([Rat; 3], &'static str)> = Vec::new();
    for a in &dial_values {
        for b in &dial_values {
            for c in &dial_values {
                let dials = ThreeSiteDials::new(a.clone(), b.clone(), c.clone());
                let species = match read_return_group(&dials) {
                    Ok(reading) => match reading.closure {
                        ClosureReading::Closes { .. } => "closes",
                        ClosureReading::DoesNotClose { .. } => "does-not-close",
                        ClosureReading::Splits { .. } => "splits",
                    },
                    Err(_) => "refused",
                };
                swept.push(([a.clone(), b.clone(), c.clone()], species));
            }
        }
    }
    let mut census: BTreeMap<&str, usize> = BTreeMap::new();
    for (_, species) in &swept {
        *census.entry(species).or_insert(0) += 1;
    }
    println!(
        "  dial values swept          {}   triples {}",
        dial_values.len(),
        swept.len()
    );
    print!("  the classification         ");
    for (species, count) in &census {
        print!("{species} {count}   ");
    }
    println!();
    let vacuous = census.len() < 2;
    println!(
        "  the sweep separates        {}   {}",
        !vacuous,
        if vacuous {
            "VACUOUS -- one species only, so every permutation would preserve it"
        } else {
            "more than one species, so a permutation CAN break the classification"
        }
    );
    println!();

    let by_triple: BTreeMap<&[Rat; 3], &str> = swept
        .iter()
        .map(|(triple, species)| (triple, *species))
        .collect();
    let preserves = |tau: &[usize]| -> Option<[Rat; 3]> {
        for (triple, species) in &swept {
            let moved: [Rat; 3] = [
                triple[tau[0]].clone(),
                triple[tau[1]].clone(),
                triple[tau[2]].clone(),
            ];
            if by_triple.get(&moved) != Some(species) {
                return Some(moved);
            }
        }
        None
    };

    println!("  THE CLOSURE LOCUS'S OWN SYMMETRY GROUP, computed by the organ over that sweep:");
    let mut locus_group: BTreeSet<Vec<usize>> = BTreeSet::new();
    for tau in permutations(3) {
        match preserves(&tau) {
            None => {
                locus_group.insert(tau.clone());
                println!(
                    "    {}   PRESERVES the classification everywhere",
                    render_permutation(&tau)
                );
            }
            Some(counterexample) => {
                let rendered: Vec<String> = counterexample
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect();
                println!(
                    "    {}   breaks it at ({})",
                    render_permutation(&tau),
                    rendered.join(", ")
                );
            }
        }
    }
    for sigma in &locus_group {
        for tau in &locus_group {
            assert!(
                locus_group.contains(&compose(sigma, tau)),
                "the classification-preserving permutations must be closed under composition"
            );
        }
    }
    println!("    order {}", locus_group.len());
    println!();

    // now the corpus's own permutations, restricted EXHAUSTIVELY rather than chosen
    println!("  THE JOIN  --  every corpus permutation, restricted to every 3-subset it maps to");
    println!("  itself. Nothing is chosen: a subset the permutation does not preserve is not a");
    println!("  restriction at all, and every one that is, is tested.");
    println!();
    let mut agreed = 0usize;
    let mut disagreed = 0usize;
    let mut unrestrictable = 0usize;
    for (head, generators, _, _) in &groups {
        for sigma in generators {
            let degree = sigma.len();
            let mut restrictions: Vec<(Vec<usize>, Vec<usize>)> = Vec::new();
            // every 3-subset of positions that sigma maps to itself
            for mask in 0u32..(1u32 << degree) {
                if mask.count_ones() != 3 {
                    continue;
                }
                let places: Vec<usize> = (0..degree).filter(|at| mask & (1 << at) != 0).collect();
                if !places.iter().all(|at| places.contains(&sigma[*at])) {
                    continue;
                }
                let restricted: Vec<usize> = places
                    .iter()
                    .map(|at| {
                        places
                            .iter()
                            .position(|place| *place == sigma[*at])
                            .expect("the subset is preserved")
                    })
                    .collect();
                if !restrictions
                    .iter()
                    .any(|(carried, _)| *carried == restricted)
                {
                    restrictions.push((restricted, places.clone()));
                }
            }
            if restrictions.is_empty() {
                unrestrictable += 1;
                println!(
                    "  {head}   {}   no 3-subset is preserved -- the organ is unreachable from it",
                    render_permutation(sigma)
                );
                continue;
            }
            for (restricted, places) in &restrictions {
                let holds = locus_group.contains(restricted);
                if holds {
                    agreed += 1;
                } else {
                    disagreed += 1;
                }
                let named: Vec<String> = places.iter().map(|at| (at + 1).to_string()).collect();
                println!(
                    "  {head}   {} on positions ({}) restricts to {}   {}",
                    render_permutation(sigma),
                    named.join(" "),
                    render_permutation(restricted),
                    if holds {
                        "IN the closure locus's group"
                    } else {
                        "NOT in it -- the organ's classification is not invariant under it"
                    }
                );
            }
        }
    }
    println!();
    println!("  corpus permutations lying in the closure locus's group   {agreed}");
    println!("  lying outside it                                         {disagreed}");
    println!("  carrying no 3-subset the organ could be reached from     {unrestrictable}");
    println!();
    println!("  This is the join the earlier plan called shut. It was shut only because a codec's");
    println!("  surface was read as a limit: mathlib writes the parameters as variables, and a");
    println!(
        "  universally quantified claim is a claim about every instance. The corpus supplies a"
    );
    println!(
        "  permutation; this body supplies the parameter family and the organ that classifies"
    );
    println!("  it; and the question is whether the two commute.");

    // ------------------------------------------------------------------ what this is not
    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT THIS RUN DOES NOT CLAIM");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  The atlas is over ONE subtree of ONE library, named at the head of this run. A head"
    );
    println!("  whose group is trivial is absent from the table because it generated nothing, not");
    println!("  because it has no symmetry -- the material here did not state one.");
    println!();
    println!(
        "  Nothing was elaborated, type-checked or submitted to a kernel. A group returned here"
    );
    println!(
        "  is the group the WRITING exhibits, which is a claim about the corpus and not about"
    );
    println!(
        "  the mathematics behind it. The two agree exactly when the corpus states its head's"
    );
    println!("  symmetries, and that is a property of the corpus.");
    println!();
    println!("  The permutation is computed from argument tokens this driver does not author. The");
    println!("  arm that would convict it is above: rearrangements that are not permutations are");
    println!("  RETAINED and named, so the classification can fail and is observed failing.");
}
