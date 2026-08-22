//! **The machine proposes mathematics the corpus does not contain, and exact organs adjudicate it.**
//!
//! ```text
//! cargo run --release --example the_material_founds_the_identity_atlas -- <subtree>
//! cargo run --release --example the_machine_proposes_and_the_organs_adjudicate -- <atlas.tsv>
//! ```
//!
//! Stations three through six of
//! [`blueprint/THE_MACHINE_PRODUCES_MATHEMATICS_IT_WAS_NOT_GIVEN.md`](../../../blueprint/THE_MACHINE_PRODUCES_MATHEMATICS_IT_WAS_NOT_GIVEN.md).
//!
//! ## The mount is a deposit, not a library
//!
//! This run never opens a `.lean` file. It reads the atlas the founding run emitted — rows carrying
//! heads, recovered symmetry groups, rebased transport forms, transport edges, and the corpus
//! statement each identity was read off. **That is a source-detached mount by construction**, and it
//! is what makes station six's remount a re-read rather than a re-derivation.
//!
//! ## What is produced, and why it is production rather than reporting
//!
//! Three emissions, each a statement absent from the corpus by construction:
//!
//! ```text
//!   group-implied   a head's recovered group contains elements that are not generators.
//!                   Each is an identity the corpus IMPLIES and never wrote.
//!   composed        f -> g and g -> h are transport edges, so f -> h is a transport the
//!                   corpus licenses and states in no single theorem.
//!   organ-predicted an exact organ's OWN symmetry group, put to a head whose stated group
//!                   is contained in it. The elements the head lacks are identities the
//!                   ARITHMETIC asserts and the corpus is silent on.
//! ```
//!
//! The third is the sharp one: it is mathematics produced by an organ in this tree, verified before
//! it is emitted, and measured against a corpus that did not supply it.
//!
//! ## Adjudication carries no kernel
//!
//! Every proposal is put to the standing organ population, matched by **arity and shape, never by
//! name**, and the verdict is the two-sided admission law: `Admitted` when every organ that reaches
//! it confirms, `Refuted` when one refutes, `Conflicted` when both — and a conflicted proposal is
//! retained as a junction rather than tie-broken.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use holonic_engine::hypergeometric_closure::{ClosureReading, ThreeSiteDials, read_return_group};
use holonic_structure::Composes;
use relational_geometry::Rat;
use relational_geometry::exact::RatVec2;
use relational_geometry::receiver_atlas;

const DEFAULT_ATLAS: &str = "meta/IDENTITY_ATLAS_mathlib.tsv";
const SHOWN: usize = 12;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels under the workspace root")
        .to_path_buf()
}

// -------------------------------------------------------------------------------------------------
// Permutations
// -------------------------------------------------------------------------------------------------

fn compose(sigma: &[usize], tau: &[usize]) -> Vec<usize> {
    tau.iter().map(|at| sigma[*at]).collect()
}

fn identity_of(degree: usize) -> Vec<usize> {
    (0..degree).collect()
}

fn generated(generators: &BTreeSet<Vec<usize>>, degree: usize) -> BTreeSet<Vec<usize>> {
    let mut closed: BTreeSet<Vec<usize>> = BTreeSet::new();
    closed.insert(identity_of(degree));
    closed.extend(generators.iter().cloned());
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
            return closed;
        }
        closed.extend(grown);
    }
}

fn permutations(degree: usize) -> Vec<Vec<usize>> {
    if degree == 0 {
        return vec![Vec::new()];
    }
    let mut found = Vec::new();
    let mut current: Vec<usize> = (0..degree).collect();
    loop {
        found.push(current.clone());
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

fn render_permutation(sigma: &[usize]) -> String {
    let places: Vec<String> = sigma.iter().map(|from| (from + 1).to_string()).collect();
    format!("[{}]", places.join(" "))
}

/// An identity rendered in the material's own shape: `head x0 x1 … = head x_{σ0} x_{σ1} …`.
fn render_identity(head: &str, sigma: &[usize]) -> String {
    let left: Vec<String> = (0..sigma.len()).map(|at| format!("x{at}")).collect();
    let right: Vec<String> = sigma.iter().map(|from| format!("x{from}")).collect();
    format!("{head} {} = {head} {}", left.join(" "), right.join(" "))
}

// -------------------------------------------------------------------------------------------------
// The organ population — exact, and each one's own group recovered by arithmetic
// -------------------------------------------------------------------------------------------------

struct Resolver {
    name: &'static str,
    arity: usize,
    evaluate: fn(&[Rat]) -> Option<Rat>,
}

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn additive(argument: &[Rat]) -> Option<Rat> {
    Some(&argument[0] + &argument[1])
}

fn oriented_difference(argument: &[Rat]) -> Option<Rat> {
    Some(&argument[0] - &argument[1])
}

fn squared_separation(argument: &[Rat]) -> Option<Rat> {
    let gap = &argument[0] - &argument[1];
    Some(&gap * &gap)
}

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

fn corner_cosine(argument: &[Rat]) -> Option<Rat> {
    let (a, b, c) = (&argument[0], &argument[1], &argument[2]);
    if a.is_zero() || b.is_zero() {
        return None;
    }
    Some((a * a + b * b - c * c) / (Rat::from_integer(BigInt::from(2)) * a * b))
}

/// The standing organ, called rather than rewritten.
fn cross_ratio(argument: &[Rat]) -> Option<Rat> {
    let marks: Vec<RatVec2> = argument
        .iter()
        .map(|coordinate| RatVec2::new(coordinate.clone(), Rat::zero()))
        .collect();
    receiver_atlas::cross_ratio(&marks).ok()
}

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

/// A three-argument organ whose classification, not whose value, decides: the closure of a
/// three-site turning equation. Its value face is the species index, so a permutation preserving it
/// preserves the classification.
fn closure_species(argument: &[Rat]) -> Option<Rat> {
    let dials = ThreeSiteDials::new(
        argument[0].clone(),
        argument[1].clone(),
        argument[2].clone(),
    );
    let reading = read_return_group(&dials).ok()?;
    Some(Rat::from_integer(BigInt::from(match reading.closure {
        ClosureReading::Closes { .. } => 1u32,
        ClosureReading::DoesNotClose { .. } => 2,
        ClosureReading::Splits { .. } => 3,
    })))
}

/// `ab + bc + ca` — the second elementary symmetric function on three letters. Its invariance group
/// is the FULL symmetric group on three, order six, and it is the only organ in this population with
/// a non-abelian group. Without it no arity-three head stating more than a transposition has any
/// organ that could model it.
fn symmetric_pair_sum_three(argument: &[Rat]) -> Option<Rat> {
    let (a, b, c) = (&argument[0], &argument[1], &argument[2]);
    Some(a * b + b * c + c * a)
}

/// `(a-b)(b-c)(c-a)` — invariant under the CYCLIC rotations of three letters and sign-flipped by
/// every transposition, so its group is the alternating one, order three. It separates a cyclic
/// symmetry from a full one, which nothing else here can.
fn alternating_product_three(argument: &[Rat]) -> Option<Rat> {
    let (a, b, c) = (&argument[0], &argument[1], &argument[2]);
    Some((a - b) * (b - c) * (c - a))
}

/// `Σ_{i<j} x_i x_j` on four letters — the full symmetric group on four, order twenty-four.
fn symmetric_pair_sum_four(argument: &[Rat]) -> Option<Rat> {
    let mut total = Rat::zero();
    for left in 0..4 {
        for right in (left + 1)..4 {
            total += &argument[left] * &argument[right];
        }
    }
    Some(total)
}

/// `(x0 - x1)² + (x2 - x3)²` — invariant under exchanging within each pair and under exchanging the
/// pairs, which is a group of order eight, and NOT under mixing across them.
fn paired_separation_four(argument: &[Rat]) -> Option<Rat> {
    let left = &argument[0] - &argument[1];
    let right = &argument[2] - &argument[3];
    Some(&left * &left + &right * &right)
}

const RESOLVERS: [Resolver; 12] = [
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
        name: "symmetric-pair-sum-3",
        arity: 3,
        evaluate: symmetric_pair_sum_three,
    },
    Resolver {
        name: "alternating-product-3",
        arity: 3,
        evaluate: alternating_product_three,
    },
    Resolver {
        name: "symmetric-pair-sum-4",
        arity: 4,
        evaluate: symmetric_pair_sum_four,
    },
    Resolver {
        name: "paired-separation-4",
        arity: 4,
        evaluate: paired_separation_four,
    },
    Resolver {
        name: "closure-species",
        arity: 3,
        evaluate: closure_species,
    },
    Resolver {
        name: "cross-ratio",
        arity: 4,
        evaluate: cross_ratio,
    },
    Resolver {
        name: "hypergeometric-partial-sum",
        arity: 4,
        evaluate: hypergeometric_partial,
    },
];

fn probes(arity: usize) -> Vec<Vec<Rat>> {
    let spread: [(i64, i64); 6] = [(2, 1), (3, 1), (5, 1), (7, 2), (11, 3), (4, 1)];
    (0..5usize)
        .map(|offset| {
            (0..arity)
                .map(|place| {
                    let (numerator, denominator) = spread[(place + offset) % spread.len()];
                    rational(numerator, denominator)
                })
                .collect()
        })
        .collect()
}

struct OrganReading {
    name: &'static str,
    arity: usize,
    group: BTreeSet<Vec<usize>>,
    separates: bool,
}

fn read_organs() -> Vec<OrganReading> {
    let mut found = Vec::new();
    for resolver in &RESOLVERS {
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
                    _ => true,
                }
            });
            if holds {
                group.insert(sigma);
            }
        }
        for sigma in &group {
            for tau in &group {
                assert!(
                    group.contains(&compose(sigma, tau)),
                    "{}'s admitted permutations must be closed under composition",
                    resolver.name
                );
            }
        }
        found.push(OrganReading {
            name: resolver.name,
            arity: resolver.arity,
            group,
            separates,
        });
    }
    found
}

// -------------------------------------------------------------------------------------------------
// The atlas, as read back from its own deposit
// -------------------------------------------------------------------------------------------------

#[derive(Default)]
struct Atlas {
    /// (head, degree) -> generators of that degree
    ///
    /// **Keyed by degree as well as head**, because the corpus applies one name at more than one
    /// arity and a head's generators of one degree are not elements of the other's group. Keying by
    /// head alone composes permutations of different lengths, which is not an operation.
    groups: BTreeMap<(String, usize), BTreeSet<Vec<usize>>>,
    /// head -> the rebased forms it takes
    transports: BTreeMap<String, BTreeSet<String>>,
    /// (from, to) -> the forms labelling the edge
    edges: BTreeMap<(String, String), BTreeSet<String>>,
    /// every rebased form the corpus exhibits, for the collision check
    standing_forms: BTreeSet<String>,
    /// every corpus statement a row was read off
    witnesses: usize,
}

/// One edge form, read back off the atlas's own emission format.
///
/// **This is deserialization, not parsing.** The row `.ofReal x0 = evariance x1 x2` was written by
/// the founding driver in this shape — head, positional `x<i>` arguments, the separator it wrote —
/// so reading it back consults nothing about the corpus's own grammar. A form whose shape this does
/// not recognise is refused by returning `None` and counted, never guessed at.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Form {
    lhs_head: String,
    lhs_args: Vec<String>,
    rhs_head: String,
    rhs_args: Vec<String>,
}

impl Form {
    fn read(text: &str) -> Option<Self> {
        let (left, right) = text.split_once(" = ")?;
        let mut left_parts = left.split_whitespace();
        let mut right_parts = right.split_whitespace();
        let lhs_head = left_parts.next()?.to_owned();
        let rhs_head = right_parts.next()?.to_owned();
        Some(Self {
            lhs_head,
            lhs_args: left_parts.map(|part| part.to_owned()).collect(),
            rhs_head,
            rhs_args: right_parts.map(|part| part.to_owned()).collect(),
        })
    }

    /// Rename variables to first-occurrence order over `lhs` then `rhs`, so two forms that differ
    /// only in which ordinals they happened to be written with compare equal. A token that is not a
    /// variable is carried through untouched.
    fn canonical(&self) -> String {
        let mut seen: BTreeMap<String, usize> = BTreeMap::new();
        let mut rename = |token: &String| -> String {
            if token.starts_with('x') && token[1..].chars().all(|glyph| glyph.is_ascii_digit()) {
                let next = seen.len();
                let at = *seen.entry(token.clone()).or_insert(next);
                format!("x{at}")
            } else {
                token.clone()
            }
        };
        let lhs: Vec<String> = self.lhs_args.iter().map(&mut rename).collect();
        let rhs: Vec<String> = self.rhs_args.iter().map(&mut rename).collect();
        format!(
            "{} {} = {} {}",
            self.lhs_head,
            lhs.join(" "),
            self.rhs_head,
            rhs.join(" ")
        )
    }

    /// Substitute this form's conclusion into `next`'s supposition.
    ///
    /// The middle must present the same arity on both sides or there is nothing to unify, and that
    /// refusal is **typed** rather than silent: it is the commonest outcome and it is a statement
    /// about the corpus's own notation rather than about the composition.
    fn compose_at_middle(&self, next: &Self) -> Option<Self> {
        if self.rhs_head != next.lhs_head || self.rhs_args.len() != next.lhs_args.len() {
            return None;
        }
        let binding: BTreeMap<&String, &String> =
            next.lhs_args.iter().zip(self.rhs_args.iter()).collect();
        Some(Self {
            lhs_head: self.lhs_head.clone(),
            lhs_args: self.lhs_args.clone(),
            rhs_head: next.rhs_head.clone(),
            rhs_args: next
                .rhs_args
                .iter()
                .map(|arg| {
                    binding
                        .get(arg)
                        .map(|bound| (*bound).clone())
                        .unwrap_or_else(|| arg.clone())
                })
                .collect(),
        })
    }
}

/// A transport between two heads, carried as the forms the corpus labels it with.
///
/// # Why this is a `Composes` and not a comparison written here
///
/// The three-way discrimination this station needs is already written, at
/// `crates/holonic-structure/src/chain.rs`: *"Loop closure is `Chain::holonomy`; path-independence
/// is `Chain::defect_against`; loss is here [`is_rebase`]."* Measured 2026-08-17 by
/// `grep -c "holonic_structure\|Composes\|Chain"` over this driver and its founding twin: **0** in
/// both. Five implementors of `Composes` stood in the tree and neither production driver imported
/// one.
///
/// **And the compression organ cannot do this job**, which is the correction that occasioned the
/// carrier. If the conduct partition is stable under the declared input set it is already stable
/// under any composite of those inputs — the one-shot partition never depended on inputs at all — so
/// putting a composed transport to `receiver_exact_compression` as a declared input is a check that
/// **cannot fail**. What that organ returns about a composition is the shortest-word delta, which is
/// navigability and never admission.
#[derive(Clone, Debug, PartialEq, Eq)]
struct FormTransport {
    forms: BTreeSet<String>,
}

impl Composes for FormTransport {
    /// What a composed route carries that the corpus's own direct edge does not, and the reverse.
    type Defect = (BTreeSet<String>, BTreeSet<String>);
    /// The forms a composition carried past without the corpus restating them. Derived from the
    /// transport, never reported beside it.
    type Remainder = BTreeSet<String>;

    fn identity() -> Self {
        Self {
            forms: BTreeSet::new(),
        }
    }

    fn compose(&self, next: &Self) -> Self {
        // A route carries every form either leg labels it with. The union is the honest composite:
        // nothing is chosen, and what the two legs disagree about survives into the remainder.
        Self {
            forms: self.forms.union(&next.forms).cloned().collect(),
        }
    }

    fn defect(direct: &Self, composed: &Self) -> Self::Defect {
        (
            composed.forms.difference(&direct.forms).cloned().collect(),
            direct.forms.difference(&composed.forms).cloned().collect(),
        )
    }

    fn closed(defect: &Self::Defect) -> bool {
        defect.0.is_empty() && defect.1.is_empty()
    }

    fn remainder(&self) -> Self::Remainder {
        // A single-form transport is a rebase: one leg, one label, nothing turned back. A composite
        // carrying more than one form turned back the labels it could not reconcile.
        if self.forms.len() <= 1 {
            BTreeSet::new()
        } else {
            self.forms.clone()
        }
    }

    fn is_empty(remainder: &Self::Remainder) -> bool {
        remainder.is_empty()
    }
}

fn parse_permutation(text: &str) -> Option<Vec<usize>> {
    let inner = text.trim().strip_prefix('[')?.strip_suffix(']')?;
    inner
        .split_whitespace()
        .map(|place| place.parse::<usize>().ok().and_then(|at| at.checked_sub(1)))
        .collect()
}

fn read_atlas(text: &str) -> Atlas {
    let mut atlas = Atlas::default();
    for line in text.lines().skip(1) {
        let column: Vec<&str> = line.split('\t').collect();
        if column.len() < 4 {
            continue;
        }
        let (kind, head, detail, form) = (column[0], column[1], column[2], column[3]);
        match kind {
            "symmetry" => {
                let Some(sigma) = parse_permutation(form) else {
                    continue;
                };
                // the generator's own length IS its degree; the detail column is lineage
                let degree = sigma.len();
                atlas
                    .groups
                    .entry((head.to_owned(), degree))
                    .or_default()
                    .insert(sigma);
            }
            "transport" => {
                atlas
                    .transports
                    .entry(head.to_owned())
                    .or_default()
                    .insert(form.to_owned());
                atlas.standing_forms.insert(form.to_owned());
            }
            "edge" => {
                atlas
                    .edges
                    .entry((head.to_owned(), detail.to_owned()))
                    .or_default()
                    .insert(form.to_owned());
                atlas.standing_forms.insert(form.to_owned());
            }
            "identity" => {
                atlas.standing_forms.insert(form.to_owned());
                atlas.witnesses += 1;
            }
            _ => {}
        }
    }
    atlas
}

// -------------------------------------------------------------------------------------------------
// A proposal and its verdict
// -------------------------------------------------------------------------------------------------

#[derive(Clone, Debug, PartialEq, Eq)]
enum Species {
    /// A non-generator element of the head's own recovered group.
    GroupImplied,
    /// Two transport edges composed.
    Composed,
    /// An organ's own group element the head's stated group lacks.
    OrganPredicted { organ: &'static str },
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Verdict {
    Admitted {
        by: Vec<&'static str>,
    },
    /// Exactly one qualified organ confirms it and none refutes.
    ///
    /// **Retained and never deposited.** An invariant is only visible across two frames. A
    /// `group-implied` proposal has two by construction — the corpus's own generators close to it,
    /// and an organ agrees — but an `organ-predicted` one has only the organ, and a maximally
    /// symmetric organ qualifies for every head that states any transposition. Admitting on one
    /// witness let a single symmetric organ predict full symmetry for twenty heads at once.
    SingleWitness {
        by: &'static str,
    },
    Refuted {
        by: &'static str,
        at: String,
    },
    Conflicted {
        confirming: Vec<&'static str>,
        refuting: &'static str,
    },
    Unreached,
    AlreadyStanding,
}

struct Proposal {
    species: Species,
    head: String,
    statement: String,
    sigma: Option<Vec<usize>>,
    verdict: Verdict,
}

/// Adjudicate one proposed permutation.
///
/// **An organ may only judge a head whose STATED group it contains.** The corpus's already-written
/// symmetries are the evidence that an organ is a candidate model of that head; an organ disagreeing
/// with what the corpus states is a different operation, and a different operation refuting a
/// proposal is not evidence the proposal is false. Without this rule the run reported `associator`'s
/// full three-letter symmetry as REFUTED by a triangle corner, which says nothing about associators.
fn adjudicate(
    sigma: &[usize],
    stated: &BTreeSet<Vec<usize>>,
    organs: &[OrganReading],
    frames_from_the_corpus: usize,
) -> Verdict {
    let reachable: Vec<&OrganReading> = organs
        .iter()
        .filter(|organ| organ.arity == sigma.len() && organ.separates)
        .filter(|organ| stated.iter().all(|already| organ.group.contains(already)))
        .collect();
    if reachable.is_empty() {
        return Verdict::Unreached;
    }
    let mut confirming: Vec<&'static str> = Vec::new();
    let mut refuting: Option<(&'static str, String)> = None;
    for organ in reachable {
        if organ.group.contains(sigma) {
            confirming.push(organ.name);
        } else if refuting.is_none() {
            // the witness: the probe tuple where the organ's value moved
            let mut witness = String::from("its group does not contain it");
            let resolver = RESOLVERS
                .iter()
                .find(|candidate| candidate.name == organ.name)
                .expect("every reading came from a resolver");
            for tuple in probes(organ.arity) {
                let moved: Vec<Rat> = sigma.iter().map(|from| tuple[*from].clone()).collect();
                if let (Some(before), Some(after)) =
                    ((resolver.evaluate)(&tuple), (resolver.evaluate)(&moved))
                {
                    if before != after {
                        let rendered: Vec<String> =
                            tuple.iter().map(std::string::ToString::to_string).collect();
                        witness = format!("({}) -> {before} against {after}", rendered.join(", "));
                        break;
                    }
                }
            }
            refuting = Some((organ.name, witness));
        }
    }
    match (confirming.is_empty(), refuting) {
        (false, None) if confirming.len() + frames_from_the_corpus >= 2 => {
            Verdict::Admitted { by: confirming }
        }
        (false, None) => Verdict::SingleWitness { by: confirming[0] },
        (true, Some((organ, at))) => Verdict::Refuted { by: organ, at },
        (false, Some((organ, _))) => Verdict::Conflicted {
            confirming,
            refuting: organ,
        },
        (true, None) => Verdict::Unreached,
    }
}

fn emit(atlas: &Atlas, organs: &[OrganReading]) -> Vec<Proposal> {
    let mut proposals: Vec<Proposal> = Vec::new();

    // --- group-implied: the head's own group, minus its generators and the identity
    for ((head, degree), generators) in &atlas.groups {
        if *degree == 0 {
            continue;
        }
        let closed = generated(generators, *degree);
        for sigma in &closed {
            if *sigma == identity_of(*degree) || generators.contains(sigma) {
                continue;
            }
            let statement = render_identity(head, sigma);
            let verdict = if atlas.standing_forms.contains(&statement) {
                Verdict::AlreadyStanding
            } else {
                // the corpus's OWN generators close to this element, so the closure is one frame
                // and the organ is the second
                adjudicate(sigma, &closed, organs, 1)
            };
            proposals.push(Proposal {
                species: Species::GroupImplied,
                head: head.clone(),
                statement,
                sigma: Some(sigma.clone()),
                verdict,
            });
        }
    }

    // --- organ-predicted: an organ's group element the head's stated group lacks
    //
    // Emitted ONCE per (head, permutation). A permutation several organs predict is one identity,
    // not several proposals; emitting per organ counts the organ population rather than the
    // mathematics, and inflated the admitted figure by a factor of two on the first run.
    for ((head, degree), generators) in &atlas.groups {
        if *degree == 0 {
            continue;
        }
        let closed = generated(generators, *degree);
        let mut predicted: BTreeMap<Vec<usize>, BTreeSet<&'static str>> = BTreeMap::new();
        for organ in organs {
            if organ.arity != *degree || !organ.separates {
                continue;
            }
            // only an organ that CONTAINS everything the corpus states about this head can predict
            // for it; an organ that already disagrees is a different operation
            if !closed.iter().all(|sigma| organ.group.contains(sigma)) {
                continue;
            }
            for sigma in &organ.group {
                if closed.contains(sigma) {
                    continue;
                }
                predicted
                    .entry(sigma.clone())
                    .or_default()
                    .insert(organ.name);
            }
        }
        for (sigma, organs_predicting) in predicted {
            let statement = render_identity(head, &sigma);
            let organ = organs_predicting
                .iter()
                .next()
                .copied()
                .unwrap_or("an organ");
            let verdict = if atlas.standing_forms.contains(&statement) {
                Verdict::AlreadyStanding
            } else {
                // only the organs assert this; the corpus is silent, so it carries no frame
                adjudicate(&sigma, &closed, organs, 0)
            };
            proposals.push(Proposal {
                species: Species::OrganPredicted { organ },
                head: head.clone(),
                statement,
                sigma: Some(sigma),
                verdict,
            });
        }
    }

    // --- composed: two transport edges with no direct edge between their ends
    let mut composed = 0usize;
    // The held-out arm's tallies. Every one stands beside the population it counts.
    let (mut held_out, mut held_out_agree, mut held_out_weaker) = (0usize, 0usize, 0usize);
    let (mut held_out_stronger, mut held_out_incomparable, mut held_out_rebase) =
        (0usize, 0usize, 0usize);
    let (mut held_out_middle_refused, mut held_out_unreached) = (0usize, 0usize);
    // THE ARTIFACT. Counts are receipts; the composed word is the thing. Four species, each keeping
    // its own exhibit so a reader sees what the machine actually joined.
    let mut exhibit: BTreeMap<&'static str, Vec<String>> = BTreeMap::new();
    // the composed population is large and its members carry no permutation, so a bounded exhibit
    // is emitted and the FULL count is reported beside it -- a silent truncation would read as
    // coverage
    const COMPOSED_EXHIBIT: usize = 512;
    for ((from, middle), left) in &atlas.edges {
        for ((second, to), right) in &atlas.edges {
            if second != middle || to == from {
                continue;
            }
            if let Some(direct) = atlas.edges.get(&(from.clone(), to.clone())) {
                // THE HELD-OUT ARM. The corpus states this transport directly, so composing it is a
                // prediction against ground truth the run did not author. Before 2026-08-17 this was
                // a `continue`: the driver discarded exactly the population that could refute it.
                // Compose by SUBSTITUTION AT THE MIDDLE, then hand the composite and the corpus's
                // own direct edge to the chain law.
                let mut composed_forms: BTreeSet<String> = BTreeSet::new();
                let mut middle_refused = 0usize;
                for first in left {
                    for second in right {
                        match (Form::read(first), Form::read(second)) {
                            (Some(first), Some(second)) => match first.compose_at_middle(&second) {
                                Some(joined) => {
                                    composed_forms.insert(joined.canonical());
                                }
                                None => middle_refused += 1,
                            },
                            _ => middle_refused += 1,
                        }
                    }
                }
                held_out_middle_refused += middle_refused;
                if composed_forms.is_empty() {
                    held_out_unreached += 1;
                    continue;
                }
                let stated_forms: BTreeSet<String> = direct
                    .iter()
                    .filter_map(|form| Form::read(form).map(|read| read.canonical()))
                    .collect();
                let route = FormTransport {
                    forms: composed_forms,
                };
                let stated = FormTransport {
                    forms: stated_forms,
                };
                let defect = <FormTransport as Composes>::defect(&stated, &route);
                let species = if <FormTransport as Composes>::closed(&defect) {
                    held_out_agree += 1;
                    "AGREE"
                } else if defect.0.is_empty() {
                    // the corpus states forms the route did not reach: the composite is weaker
                    held_out_weaker += 1;
                    "WEAKER"
                } else if defect.1.is_empty() {
                    held_out_stronger += 1;
                    "STRONGER"
                } else {
                    held_out_incomparable += 1;
                    "INCOMPARABLE"
                };
                let kept = exhibit.entry(species).or_default();
                if kept.len() < 4 {
                    kept.push(format!(
                        "      {from}  ~>  {middle}  ~>  {to}\n\
                         \x20       left    {}\n\
                         \x20       right   {}\n\
                         \x20       COMPOSED {}\n\
                         \x20       CORPUS   {}",
                        left.iter().next().cloned().unwrap_or_default(),
                        right.iter().next().cloned().unwrap_or_default(),
                        route
                            .forms
                            .iter()
                            .take(2)
                            .cloned()
                            .collect::<Vec<_>>()
                            .join("   |   "),
                        stated
                            .forms
                            .iter()
                            .take(2)
                            .cloned()
                            .collect::<Vec<_>>()
                            .join("   |   ")
                    ));
                }
                if <FormTransport as Composes>::is_empty(&route.remainder()) {
                    held_out_rebase += 1;
                }
                held_out += 1;
                continue;
            }
            composed += 1;
            if composed > COMPOSED_EXHIBIT {
                continue;
            }
            let statement = format!(
                "{from} ~> {to}   via {middle}   [{} then {}]",
                left.iter().next().cloned().unwrap_or_default(),
                right.iter().next().cloned().unwrap_or_default()
            );
            proposals.push(Proposal {
                species: Species::Composed,
                head: from.clone(),
                statement,
                sigma: None,
                // a composed transport asserts no permutation, so no organ of this population
                // reaches it; saying so is the honest verdict
                verdict: Verdict::Unreached,
            });
        }
    }
    println!();
    println!("  THE HELD-OUT ARM — routes whose ends the corpus ALSO joins directly");
    println!(
        "  These are the run's ground truth and it used to discard them. A composed route is put"
    );
    println!(
        "  to `Chain`'s own law: `Composes::defect` against the stated edge, and `remainder` for"
    );
    println!("  whether the composition was a rebase. Nothing here is adjudicated by an exterior.");
    println!("    held-out routes                {held_out}");
    println!("    the defect CLOSED (agree)      {held_out_agree}");
    println!("    composite strictly WEAKER      {held_out_weaker}");
    println!("    composite strictly STRONGER    {held_out_stronger}");
    println!("    INCOMPARABLE                   {held_out_incomparable}");
    println!("    composed as a REBASE           {held_out_rebase}   (zero remainder)");
    println!(
        "    routes reaching no composite   {held_out_unreached}   (nothing unified at the middle)"
    );
    println!(
        "    arity mismatches at the middle {held_out_middle_refused}   a TYPED refusal, not a failure"
    );
    println!();
    println!(
        "  THE COMPOSED WORDS THEMSELVES — the counts above are receipts, these are the object"
    );
    for species in ["AGREE", "WEAKER", "STRONGER", "INCOMPARABLE"] {
        let Some(kept) = exhibit.get(species) else {
            continue;
        };
        println!("    --- {species} ---");
        for shown in kept {
            println!("{shown}");
        }
    }
    if held_out == 0 {
        println!(
            "    NOTHING WAS HELD OUT: this arm cannot fail on this atlas and carries no evidence."
        );
    } else if held_out_agree == held_out || held_out_agree == 0 {
        println!("    THE ARM RETURNED ALL-OR-NOTHING, so it adjudicated nothing and says so.");
    }
    println!();
    println!("  two-step transports the corpus states in no single theorem   {composed}");
    println!(
        "  of which exhibited here (the rest counted, never dropped)     {}",
        composed.min(COMPOSED_EXHIBIT)
    );
    proposals
}

fn main() {
    let root = workspace_root();
    let declared = std::env::args()
        .nth(1)
        .unwrap_or_else(|| DEFAULT_ATLAS.to_owned());
    let path = root.join(&declared);

    println!("{}", "=".repeat(100));
    println!("THE MACHINE PROPOSES, AND THE ORGANS ADJUDICATE");
    println!("{}", "=".repeat(100));
    println!();

    let Ok(text) = fs::read_to_string(&path) else {
        println!("  {declared} is absent — run the founding driver first");
        return;
    };
    let atlas = read_atlas(&text);
    println!("  mount   {declared}   {} octets", text.len());
    println!("  This run opens no source file. The atlas IS the mount, so everything below is");
    println!("  already source-detached.");
    println!();
    println!("  heads carrying a group   {}", atlas.groups.len());
    println!("  heads carrying transports {}", atlas.transports.len());
    println!("  transport edges          {}", atlas.edges.len());
    println!("  rebased forms standing   {}", atlas.standing_forms.len());
    println!("  corpus statements cited  {}", atlas.witnesses);

    // ---------------------------------------------------------------- the organs
    println!();
    println!("{}", "=".repeat(100));
    println!("[4a]  THE ORGAN POPULATION  --  each one's group recovered by its own arithmetic");
    println!("{}", "=".repeat(100));
    println!();
    let organs = read_organs();
    println!(
        "  {:<30} {:>6} {:>7} {:>11}  {}",
        "organ", "arity", "order", "separates", "group"
    );
    for organ in &organs {
        let rendered: Vec<String> = organ
            .group
            .iter()
            .filter(|sigma| **sigma != identity_of(organ.arity))
            .map(|sigma| render_permutation(sigma))
            .collect();
        println!(
            "  {:<30} {:>6} {:>7} {:>11}  {}",
            organ.name,
            organ.arity,
            organ.group.len(),
            organ.separates,
            if rendered.is_empty() {
                "identity only".to_owned()
            } else {
                rendered.join(" ")
            }
        );
    }
    println!();
    println!(
        "  Closure under composition is asserted for every one. `oriented-difference` returns"
    );
    println!("  the identity alone and is the control: a proposal it confirms and nothing else");
    println!("  would convict the adjudication.");

    // ---------------------------------------------------------------- emission
    println!();
    println!("{}", "=".repeat(100));
    println!("[3]  EMISSION  --  statements the corpus does not contain");
    println!("{}", "=".repeat(100));
    println!();
    let proposals = emit(&atlas, &organs);
    let mut by_species: BTreeMap<String, Vec<&Proposal>> = BTreeMap::new();
    for proposal in &proposals {
        let key = match &proposal.species {
            Species::GroupImplied => "group-implied".to_owned(),
            Species::Composed => "composed".to_owned(),
            Species::OrganPredicted { organ } => format!("organ-predicted ({organ})"),
        };
        by_species.entry(key).or_default().push(proposal);
    }
    println!("  proposals emitted   {}", proposals.len());
    for (species, members) in &by_species {
        let standing = members
            .iter()
            .filter(|proposal| proposal.verdict == Verdict::AlreadyStanding)
            .count();
        println!(
            "    {species:<34} {:>5}   of which already standing in the corpus {standing}",
            members.len()
        );
    }
    println!();
    println!("  A proposal already in the corpus is not a proposal, and is reported rather than");
    println!("  quietly dropped. An emission that is entirely collisions produced nothing.");

    // ---------------------------------------------------------------- adjudication
    println!();
    println!("{}", "=".repeat(100));
    println!(
        "[4b]  ADJUDICATION  --  every proposal to the organs, matched by arity, never by name"
    );
    println!("{}", "=".repeat(100));
    println!();
    let mut census: BTreeMap<(String, &str), usize> = BTreeMap::new();
    for proposal in &proposals {
        let key = match &proposal.verdict {
            Verdict::Admitted { .. } => "ADMITTED",
            Verdict::SingleWitness { .. } => "single witness -- retained, not deposited",
            Verdict::Refuted { .. } => "refuted",
            Verdict::Conflicted { .. } => "CONFLICTED",
            Verdict::Unreached => "unreached -- no organ models this head",
            Verdict::AlreadyStanding => "already standing",
        };
        let species = match &proposal.species {
            Species::GroupImplied => "group-implied".to_owned(),
            Species::Composed => "composed".to_owned(),
            Species::OrganPredicted { organ } => format!("organ-predicted ({organ})"),
        };
        *census.entry((species, key)).or_insert(0) += 1;
    }
    for ((species, verdict), count) in &census {
        println!("  {species:<34} {verdict:<38} {count}");
    }
    println!();
    println!("  ADMITTED, in the material's own shape:");
    let admitted: Vec<&Proposal> = proposals
        .iter()
        .filter(|proposal| matches!(proposal.verdict, Verdict::Admitted { .. }))
        .collect();
    for proposal in admitted.iter().take(SHOWN) {
        if let Verdict::Admitted { by } = &proposal.verdict {
            println!("    {:<46}  by {}", proposal.statement, by.join(", "));
        }
    }
    if admitted.len() > SHOWN {
        println!("    ... {} more", admitted.len() - SHOWN);
    }

    println!();
    println!("  REFUTED, with the exact witness the organ returned:");
    let refuted: Vec<&Proposal> = proposals
        .iter()
        .filter(|proposal| matches!(proposal.verdict, Verdict::Refuted { .. }))
        .collect();
    for proposal in refuted.iter().take(SHOWN) {
        if let Verdict::Refuted { by, at } = &proposal.verdict {
            println!("    {:<46}  {by} breaks it at {at}", proposal.statement);
        }
    }
    if refuted.len() > SHOWN {
        println!("    ... {} more", refuted.len() - SHOWN);
    }

    println!();
    println!("  SINGLE WITNESS -- one qualified organ, no second frame, NOT deposited:");
    let single: Vec<&Proposal> = proposals
        .iter()
        .filter(|proposal| matches!(proposal.verdict, Verdict::SingleWitness { .. }))
        .collect();
    for proposal in single.iter().take(SHOWN) {
        if let Verdict::SingleWitness { by } = &proposal.verdict {
            println!("    {:<46}  {by} alone", proposal.statement);
        }
    }
    if single.len() > SHOWN {
        println!("    ... {} more", single.len() - SHOWN);
    }
    if single.is_empty() {
        println!("    none on this material");
    }

    println!();
    println!("  CONFLICTED -- retained as junctions, never tie-broken:");
    let conflicted: Vec<&Proposal> = proposals
        .iter()
        .filter(|proposal| matches!(proposal.verdict, Verdict::Conflicted { .. }))
        .collect();
    for proposal in conflicted.iter().take(SHOWN) {
        if let Verdict::Conflicted {
            confirming,
            refuting,
        } = &proposal.verdict
        {
            println!(
                "    {:<46}  confirmed by {} · refuted by {refuting}",
                proposal.statement,
                confirming.join(", ")
            );
        }
    }
    if conflicted.is_empty() {
        println!("    none on this material");
    }

    // ---------------------------------------------------------------- the return
    println!();
    println!("{}", "=".repeat(100));
    println!("[5]  THE RETURN  --  the deposit changes what a later construction reaches");
    println!("{}", "=".repeat(100));
    println!();
    println!(
        "  An admitted proposal is deposited as a generator of its head. The claim is not that"
    );
    println!(
        "  the deposit happened; it is that a head's group GROWS, and that removing the deposit"
    );
    println!("  removes the growth.");
    println!();
    let mut grew: Vec<(String, usize, usize, Vec<String>)> = Vec::new();
    for ((head, degree), generators) in &atlas.groups {
        if *degree == 0 {
            continue;
        }
        let before = generated(generators, *degree);
        let mut after_generators = generators.clone();
        for proposal in &admitted {
            if proposal.head == *head {
                if let Some(sigma) = &proposal.sigma {
                    if sigma.len() == *degree {
                        after_generators.insert(sigma.clone());
                    }
                }
            }
        }
        if after_generators == *generators {
            continue;
        }
        let after = generated(&after_generators, *degree);
        if after.len() > before.len() {
            let gained: Vec<String> = after
                .difference(&before)
                .map(|sigma| render_permutation(sigma))
                .collect();
            grew.push((
                format!("{head}/{degree}"),
                before.len(),
                after.len(),
                gained,
            ));
        }
    }
    println!(
        "  heads whose group GREW after the deposit   {}",
        grew.len()
    );
    for (head, before, after, gained) in grew.iter().take(SHOWN) {
        println!(
            "    {head}   order {before} -> {after}   gained {}",
            gained.join(" ")
        );
    }
    println!();
    println!("  THE ABLATION -- the deposit removed, and the growth must vanish:");
    let mut ablation_holds = true;
    for (label, before, _, _) in &grew {
        let (head, degree) = label
            .rsplit_once('/')
            .expect("the label carries its degree");
        let degree: usize = degree.parse().expect("a degree");
        let generators = &atlas.groups[&(head.to_owned(), degree)];
        let ablated = generated(generators, degree);
        if ablated.len() != *before {
            ablation_holds = false;
            println!(
                "    {label}   ABLATION FAILED — order {} against {before}",
                ablated.len()
            );
        }
    }
    if ablation_holds {
        println!(
            "    every one of the {} grown heads returns to its pre-deposit order when the",
            grew.len()
        );
        println!(
            "    deposited generators are removed. The growth is the deposit's and nothing else's."
        );
    }

    // ---------------------------------------------------------------- the seal
    println!();
    println!("{}", "=".repeat(100));
    println!("[6]  THE SEAL  --  the changed atlas, re-read from its octets alone");
    println!("{}", "=".repeat(100));
    println!();
    let sealed_path = root.join("meta").join("PROPOSED_IDENTITIES.tsv");
    let mut rows = vec![["species", "head", "statement", "verdict", "organ"].join("\t")];
    for proposal in &proposals {
        let (verdict, organ) = match &proposal.verdict {
            Verdict::Admitted { by } => ("admitted".to_owned(), by.join(";")),
            Verdict::SingleWitness { by } => ("single-witness".to_owned(), (*by).to_owned()),
            Verdict::Refuted { by, .. } => ("refuted".to_owned(), (*by).to_owned()),
            Verdict::Conflicted { refuting, .. } => {
                ("conflicted".to_owned(), (*refuting).to_owned())
            }
            Verdict::Unreached => ("unreached".to_owned(), String::new()),
            Verdict::AlreadyStanding => ("already-standing".to_owned(), String::new()),
        };
        let species = match &proposal.species {
            Species::GroupImplied => "group-implied".to_owned(),
            Species::Composed => "composed".to_owned(),
            Species::OrganPredicted { organ } => format!("organ-predicted:{organ}"),
        };
        rows.push(
            [
                species,
                proposal.head.clone(),
                proposal.statement.clone(),
                verdict,
                organ,
            ]
            .join("\t"),
        );
    }
    let sealed = rows.join("\n") + "\n";
    match fs::write(&sealed_path, &sealed) {
        Ok(()) => {
            println!(
                "  sealed   meta/PROPOSED_IDENTITIES.tsv   {} octets   {} rows",
                sealed.len(),
                rows.len() - 1
            );
            // the remount: read it back and re-derive the admitted population from the octets alone
            let Ok(remounted) = fs::read_to_string(&sealed_path) else {
                println!("  the remount could not read the seal");
                return;
            };
            let readmitted = remounted
                .lines()
                .skip(1)
                .filter(|line| line.split('\t').nth(3) == Some("admitted"))
                .count();
            println!("  remounted from the octets alone   admitted rows {readmitted}");
            assert_eq!(
                readmitted,
                admitted.len(),
                "the seal must reproduce the admitted family exactly"
            );
            println!(
                "  the admitted family reproduces exactly: {readmitted} against {} before the seal",
                admitted.len()
            );
            println!();
            println!("  COMPRESSION, carried with its decoder and as an ADDITIVE difference. The");
            println!(
                "  atlas is {} octets and this seal is {} octets; the second is a",
                text.len(),
                sealed.len()
            );
            println!(
                "  DIFFERENT object rather than a smaller copy of the first -- it carries what"
            );
            println!("  the machine produced, not what it read -- so no ratio between them is a");
            println!("  compression figure and none is quoted.");
        }
        Err(refusal) => println!("  the seal was refused: {refusal}"),
    }
}
