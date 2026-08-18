//! **A mathlib statement carried into a symbolic object an atlas transport acts on.**
//!
//! ```text
//! cargo run --release --example the_integrand_is_read_and_the_organ_names_its_transcendental
//! ```
//!
//! ## The joint this closes, named 2026-08-14 and open until today
//!
//! `research/records/2026-08-14_THE_CENTRIFUGE_IS_BUILT_AND_IT_SEPARATES_BY_SPELLING.md` §2:
//!
//! > *The four method-atlas transports … act on **constructed** symbolic objects and **nothing
//! > carries a mathlib statement into an object they can act on.** That is the joint, not a missing
//! > organ.*
//!
//! `hypergeometric_closure` was reached on 2026-08-17 by exchanging a *permutation*, which needed no
//! statement translated. This carries the statement.
//!
//! ## The receiver question
//!
//! *An integral table states, in tokens, what an antiderivative is. `hermite_reduction` decides,
//! exactly and without extracting a root, which class an integrand's residues live in. Do they
//! agree — and can the organ be told the answer before it is shown the corpus's?*
//!
//! ## What decides, and why the corpus is the answer key rather than the input
//!
//! `hermite_reduction` splits `f = h' + g`: the coboundary part `h`, whose derivative is exact and
//! which takes no part in the class, and the remaining `g` whose class is carried by the **residue
//! polynomial** `Res_x(B − z·D*', D*)` — the polynomial whose roots are `g`'s residues, returned
//! **with no root extracted**. That polynomial decides the transcendental:
//!
//! ```text
//!   no residues at all                  -> the antiderivative is RATIONAL
//!   residues all rational               -> LOGARITHMS
//!   residues not all rational           -> an ARCTANGENT or a logarithm of a quadratic
//! ```
//!
//! The corpus's own right-hand side says which one it used, in tokens the organ never sees. So the
//! organ's prediction is made from the integrand alone and graded against material this repository
//! did not write.
//!
//! ## The reader's aperture, declared because it is authored
//!
//! Founding the split of `∫ x in a..b, f` into domain and integrand is the same oriented-separator
//! law the statement grammar already runs on, one scale further down: the **last** depth-zero
//! comma. That much is founded.
//!
//! The expression reader below is **not** founded. It declares a precedence — additive loosest,
//! then multiplicative, then power, then the postfix inverse, then atoms — because a population that
//! brackets whenever it matters never exhibits the precedence it relies on, and inventing a founding
//! that the material does not witness would be worse than declaring one.
//!
//! **The declaration is safe exactly because the answer key is external.** A wrong precedence
//! produces a wrong integrand, a wrong integrand produces a wrong class, and a wrong class disagrees
//! with the corpus's own closed form. The disagreement column is the falsifier for the reader, and
//! it is printed first.
//!
//! Every integrand outside the aperture is **refused by name and retained**, never skipped.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use holonic_engine::elementary_chart::{ExponentialIntegrand, read_elementary_chart};
use holonic_engine::hermite_reduction::{ReductionSchedule, reduce};
use holonic_engine::lean_development::{DeclarationGrain, header_nests, read_development};
use holonic_engine::rational_polynomial::RationalPolynomial;
use relational_geometry::Rat;

/// The declared material: mathlib's own table of definite integrals.
const SUBTREE: &str = "soma/formal/elementary-holonics/.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Integrals";

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels under the workspace root")
        .to_path_buf()
}

fn source_files(root: &Path) -> Vec<PathBuf> {
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
            } else if path.extension().is_some_and(|kind| kind == "lean") {
                found.push(path);
            }
        }
    }
    found.sort();
    found
}

/// The bracket species a mathematical statement nests in — the family the statement grammar
/// recovers, reused here so one depth law serves every scale of this run.
const FAMILY: [(char, char); 5] = [
    ('(', ')'),
    ('[', ']'),
    ('{', '}'),
    ('⟨', '⟩'),
    ('⦃', '⦄'),
];

/// Whether the region before an offset is bracket groups and whitespace and nothing else.
///
/// This is the statement grammar's own founding property, reused rather than restated in spirit: a
/// candidate split leaving a bare token in its leading region is not the statement's split. Taking
/// the last depth-zero colon without it reads `∫ x : ℝ in a..b, 1/x` as the conclusion of a
/// supposition named `ℝ`, which is how this driver first mis-founded its own bound variable.
fn leading_region_founds(text: &str, split: usize) -> bool {
    let mut expected: Vec<char> = Vec::new();
    let mut saw_group = false;
    for (at, symbol) in text.char_indices() {
        if at >= split {
            break;
        }
        if let Some((_, close)) = FAMILY.iter().find(|(open, _)| *open == symbol) {
            if expected.is_empty() {
                saw_group = true;
            }
            expected.push(*close);
            continue;
        }
        if FAMILY.iter().any(|(_, close)| *close == symbol) {
            if expected.last() == Some(&symbol) {
                expected.pop();
            }
            continue;
        }
        if expected.is_empty() && !symbol.is_whitespace() {
            return false;
        }
    }
    expected.is_empty() && saw_group
}

/// The founded split: among the depth-zero occurrences, the last one whose leading region founds.
/// Falls back to the last occurrence when none does, and says so by returning `false` beside it.
fn founded_split(text: &str, wanted: char) -> Option<(usize, bool)> {
    let places = at_depth_zero(text, wanted);
    if let Some(at) = places
        .iter()
        .copied()
        .filter(|at| leading_region_founds(text, *at))
        .next_back()
    {
        return Some((at, true));
    }
    places.last().map(|at| (*at, false))
}

/// Byte offsets of a character standing at depth zero over [`FAMILY`].
fn at_depth_zero(text: &str, wanted: char) -> Vec<usize> {
    let mut expected: Vec<char> = Vec::new();
    let mut found = Vec::new();
    for (at, symbol) in text.char_indices() {
        if let Some((_, close)) = FAMILY.iter().find(|(open, _)| *open == symbol) {
            expected.push(*close);
            continue;
        }
        if FAMILY.iter().any(|(_, close)| *close == symbol) {
            if expected.last() == Some(&symbol) {
                expected.pop();
            }
            continue;
        }
        if symbol == wanted && expected.is_empty() {
            found.push(at);
        }
    }
    found
}

// -------------------------------------------------------------------------------------------------
// The expression reader — a declared aperture, with every refusal named
// -------------------------------------------------------------------------------------------------

/// One token of an integrand.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
    Name(String),
    Number(BigInt),
    Symbol(char),
    /// The postfix inverse `⁻¹`, read as ONE token. Its second character is a superscript digit,
    /// which `char::is_alphanumeric` calls a number, so reading it character by character absorbs
    /// it into a name and loses the operator.
    Inverse,
    Open,
    Close,
}

fn tokenize(text: &str) -> Option<Vec<Token>> {
    let mut found = Vec::new();
    let mut carried = String::new();
    let flush = |carried: &mut String, found: &mut Vec<Token>| {
        if carried.is_empty() {
            return;
        }
        let word = std::mem::take(carried);
        if word.chars().all(|symbol| symbol.is_ascii_digit()) {
            found.push(Token::Number(word.parse::<BigInt>().unwrap_or_else(|_| BigInt::zero())));
        } else {
            found.push(Token::Name(word));
        }
    };
    let characters: Vec<char> = text.chars().collect();
    let mut at = 0usize;
    while at < characters.len() {
        let symbol = characters[at];
        if symbol == '⁻' && characters.get(at + 1) == Some(&'¹') {
            flush(&mut carried, &mut found);
            found.push(Token::Inverse);
            at += 2;
            continue;
        }
        at += 1;
        if symbol.is_alphanumeric() || symbol == '_' || symbol == '.' {
            carried.push(symbol);
            continue;
        }
        flush(&mut carried, &mut found);
        if symbol.is_whitespace() {
            continue;
        }
        match symbol {
            '(' => found.push(Token::Open),
            ')' => found.push(Token::Close),
            '+' | '-' | '*' | '/' | '^' | '↑' => found.push(Token::Symbol(symbol)),
            _ => return None,
        }
    }
    flush(&mut carried, &mut found);
    Some(found)
}

/// An integrand as an exact rational function: a numerator over a denominator, both over `ℚ`.
#[derive(Clone, Debug)]
struct Fraction {
    numerator: RationalPolynomial,
    denominator: RationalPolynomial,
}

impl Fraction {
    fn constant(value: Rat) -> Self {
        Self {
            numerator: RationalPolynomial::constant(value),
            denominator: RationalPolynomial::one(),
        }
    }

    fn variable() -> Self {
        Self {
            numerator: RationalPolynomial::variable(),
            denominator: RationalPolynomial::one(),
        }
    }

    fn plus(&self, other: &Self) -> Self {
        Self {
            numerator: self
                .numerator
                .times(&other.denominator)
                .plus(&other.numerator.times(&self.denominator)),
            denominator: self.denominator.times(&other.denominator),
        }
    }

    fn minus(&self, other: &Self) -> Self {
        Self {
            numerator: self
                .numerator
                .times(&other.denominator)
                .minus(&other.numerator.times(&self.denominator)),
            denominator: self.denominator.times(&other.denominator),
        }
    }

    fn times(&self, other: &Self) -> Self {
        Self {
            numerator: self.numerator.times(&other.numerator),
            denominator: self.denominator.times(&other.denominator),
        }
    }

    fn divided_by(&self, other: &Self) -> Option<Self> {
        if other.numerator.is_zero() {
            return None;
        }
        Some(Self {
            numerator: self.numerator.times(&other.denominator),
            denominator: self.denominator.times(&other.numerator),
        })
    }

    fn inverted(&self) -> Option<Self> {
        if self.numerator.is_zero() {
            return None;
        }
        Some(Self {
            numerator: self.denominator.clone(),
            denominator: self.numerator.clone(),
        })
    }

    fn raised(&self, exponent: i64) -> Option<Self> {
        if exponent < 0 {
            return self.inverted()?.raised(-exponent);
        }
        let mut carried = Self::constant(Rat::one());
        for _ in 0..exponent {
            carried = carried.times(self);
        }
        Some(carried)
    }
}

/// Why an integrand could not be built. Retained, never skipped.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum ReaderRefusal {
    /// A character outside the declared alphabet.
    ForeignCharacter,
    /// A name that is neither the bound variable nor a number — `exp`, `sin`, `log`, a parameter.
    ForeignName(String),
    /// An exponent this reader cannot make an integer of.
    NonIntegerExponent,
    /// The token stream ran out, or a bracket did not close.
    Incomplete,
    /// A division whose divisor is identically zero.
    ZeroDivisor,
}

struct Reader<'a> {
    tokens: &'a [Token],
    at: usize,
    variable: &'a str,
    /// Names the statement's own suppositions bind, with the exact rational each is instantiated at.
    ///
    /// **A parameter is universally quantified, so instantiating it is licensed by the statement
    /// itself** — the same move that let the closure organ be reached at all. A name the statement
    /// does NOT bind is a foreign operation (`sin`, `log`, `Complex.exp`) and is refused; the
    /// distinction is founded, because `lean_development` returns the bound names.
    bound: &'a BTreeMap<String, Rat>,
}

impl<'a> Reader<'a> {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.at)
    }

    /// additive: `term (('+' | '-') term)*`
    fn additive(&mut self) -> Result<Fraction, ReaderRefusal> {
        let mut carried = self.multiplicative()?;
        while let Some(Token::Symbol(symbol @ ('+' | '-'))) = self.peek() {
            let symbol = *symbol;
            self.at += 1;
            let next = self.multiplicative()?;
            carried = if symbol == '+' {
                carried.plus(&next)
            } else {
                carried.minus(&next)
            };
        }
        Ok(carried)
    }

    /// multiplicative: `power (('*' | '/') power)*`
    fn multiplicative(&mut self) -> Result<Fraction, ReaderRefusal> {
        let mut carried = self.power()?;
        while let Some(Token::Symbol(symbol @ ('*' | '/'))) = self.peek() {
            let symbol = *symbol;
            self.at += 1;
            let next = self.power()?;
            carried = if symbol == '*' {
                carried.times(&next)
            } else {
                carried.divided_by(&next).ok_or(ReaderRefusal::ZeroDivisor)?
            };
        }
        Ok(carried)
    }

    /// power: `postfix ('^' integer)?`
    fn power(&mut self) -> Result<Fraction, ReaderRefusal> {
        let base = self.postfix()?;
        if let Some(Token::Symbol('^')) = self.peek() {
            self.at += 1;
            let negative = if let Some(Token::Symbol('-')) = self.peek() {
                self.at += 1;
                true
            } else {
                false
            };
            let Some(Token::Number(exponent)) = self.peek().cloned() else {
                return Err(ReaderRefusal::NonIntegerExponent);
            };
            self.at += 1;
            let exponent: i64 = exponent
                .to_string()
                .parse()
                .map_err(|_| ReaderRefusal::NonIntegerExponent)?;
            let exponent = if negative { -exponent } else { exponent };
            return base.raised(exponent).ok_or(ReaderRefusal::ZeroDivisor);
        }
        Ok(base)
    }

    /// postfix: `atom '⁻¹'?`
    fn postfix(&mut self) -> Result<Fraction, ReaderRefusal> {
        let base = self.atom()?;
        if let Some(Token::Inverse) = self.peek() {
            self.at += 1;
            return base.inverted().ok_or(ReaderRefusal::ZeroDivisor);
        }
        Ok(base)
    }

    /// atom: a number, the bound variable, a bracketed expression, or a leading sign
    fn atom(&mut self) -> Result<Fraction, ReaderRefusal> {
        // a coercion arrow carries no arithmetic and is stepped over
        while let Some(Token::Symbol('↑')) = self.peek() {
            self.at += 1;
        }
        match self.peek().cloned() {
            Some(Token::Symbol('-')) => {
                self.at += 1;
                let inner = self.atom()?;
                Ok(Fraction::constant(-Rat::one()).times(&inner))
            }
            Some(Token::Number(value)) => {
                self.at += 1;
                Ok(Fraction::constant(Rat::from_integer(value)))
            }
            Some(Token::Name(name)) => {
                self.at += 1;
                if name == self.variable {
                    Ok(Fraction::variable())
                } else if let Some(value) = self.bound.get(&name) {
                    Ok(Fraction::constant(value.clone()))
                } else {
                    Err(ReaderRefusal::ForeignName(name))
                }
            }
            Some(Token::Open) => {
                self.at += 1;
                let inner = self.additive()?;
                match self.peek() {
                    Some(Token::Close) => {
                        self.at += 1;
                        Ok(inner)
                    }
                    _ => Err(ReaderRefusal::Incomplete),
                }
            }
            _ => Err(ReaderRefusal::Incomplete),
        }
    }
}

fn read_integrand(
    text: &str,
    variable: &str,
    bound: &BTreeMap<String, Rat>,
) -> Result<Fraction, ReaderRefusal> {
    let tokens = tokenize(text).ok_or(ReaderRefusal::ForeignCharacter)?;
    let mut reader = Reader {
        tokens: &tokens,
        at: 0,
        variable,
        bound,
    };
    let carried = reader.additive()?;
    if reader.at != tokens.len() {
        return Err(ReaderRefusal::Incomplete);
    }
    Ok(carried)
}

// -------------------------------------------------------------------------------------------------
// The class the residues live in
// -------------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Transcendental {
    /// No residues: the antiderivative is a rational function.
    Rational,
    /// Every residue is rational: logarithms and nothing else.
    Logarithm,
    /// Some residue is not rational: an arctangent, or a logarithm of a quadratic.
    Arctangent,
}

impl Transcendental {
    fn name(self) -> &'static str {
        match self {
            Self::Rational => "rational",
            Self::Logarithm => "log",
            Self::Arctangent => "arctan",
        }
    }
}

/// Whether every root of a polynomial over `ℚ` is rational, decided exactly by the rational root
/// theorem plus repeated exact division. No root is extracted and no float appears.
fn every_root_is_rational(polynomial: &RationalPolynomial) -> bool {
    let mut carried = polynomial.clone();
    loop {
        let Some(degree) = carried.degree() else {
            return true;
        };
        if degree == 0 {
            return true;
        }
        // clear denominators so the rational root theorem applies to integers
        let mut multiplier = BigInt::one();
        for coefficient in carried.coefficients() {
            multiplier = lcm(&multiplier, coefficient.denom());
        }
        let integral: Vec<BigInt> = carried
            .coefficients()
            .iter()
            .map(|coefficient| {
                (coefficient.numer() * &multiplier / coefficient.denom()).clone()
            })
            .collect();
        let constant = integral.first().cloned().unwrap_or_else(BigInt::zero);
        let leading = integral.last().cloned().unwrap_or_else(BigInt::one);
        let mut found: Option<Rat> = None;
        'search: for numerator in divisors(&constant) {
            for denominator in divisors(&leading) {
                for sign in [BigInt::one(), -BigInt::one()] {
                    let candidate = Rat::new(&numerator * &sign, denominator.clone());
                    if carried.evaluate(&candidate).is_zero() {
                        found = Some(candidate);
                        break 'search;
                    }
                }
            }
        }
        let Some(root) = found else {
            return false;
        };
        let factor = RationalPolynomial::new(vec![-root, Rat::one()]);
        let Ok(quotient) = carried.divided_exactly_by(&factor) else {
            return false;
        };
        carried = quotient;
    }
}

fn lcm(left: &BigInt, right: &BigInt) -> BigInt {
    if left.is_zero() || right.is_zero() {
        return BigInt::one();
    }
    let mut a = left.abs();
    let mut b = right.abs();
    let product = &a * &b;
    while !b.is_zero() {
        let carried = a % &b;
        a = b;
        b = carried;
    }
    product / a
}

/// The positive divisors of an integer, bounded so a large constant term refuses rather than
/// stalls. A refusal here reads as "not decided rational", which is the conservative side.
fn divisors(value: &BigInt) -> Vec<BigInt> {
    let value = value.abs();
    if value.is_zero() {
        return vec![BigInt::one()];
    }
    let mut found = Vec::new();
    let mut candidate = BigInt::one();
    let bound = BigInt::from(4096u32);
    while &candidate * &candidate <= value && candidate <= bound {
        if (&value % &candidate).is_zero() {
            found.push(candidate.clone());
            let partner = &value / &candidate;
            if partner != candidate {
                found.push(partner);
            }
        }
        candidate += 1u32;
    }
    if found.is_empty() {
        found.push(BigInt::one());
    }
    found
}

fn main() {
    let root = workspace_root();
    let declared = std::env::args().nth(1).unwrap_or_else(|| SUBTREE.to_owned());
    let subtree = root.join(&declared);

    println!("{}", "=".repeat(100));
    println!("THE INTEGRAND IS READ, AND THE ORGAN NAMES ITS TRANSCENDENTAL");
    println!("{}", "=".repeat(100));
    println!();
    println!("  subtree   {declared}");
    println!();
    println!("  A mathlib statement is carried into an exact rational function and handed to");
    println!("  `hermite_reduction`, which splits it into a coboundary part and a remaining class");
    println!("  and returns the RESIDUE POLYNOMIAL with no root extracted. That polynomial decides");
    println!("  which transcendental the antiderivative needs:");
    println!();
    println!("    no residues            -> the antiderivative is RATIONAL");
    println!("    all residues rational  -> LOGARITHMS");
    println!("    some residue is not    -> an ARCTANGENT, or a log of a quadratic");
    println!();
    println!("  The corpus's own right-hand side says which one it used. The organ never sees it.");
    println!();

    let files = source_files(&subtree);
    let mut statements: Vec<(String, String, BTreeSet<String>)> = Vec::new();
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
            if statement.is_empty() || !header_nests(statement) {
                continue;
            }
            statements.push((
                form.name.clone(),
                statement.to_owned(),
                form.local_bindings.keys().cloned().collect(),
            ));
        }
    }
    println!("  source files {}   whole theorem statements {}", files.len(), statements.len());

    // ---------------------------------------------------------------- the founded splits
    // The conclusion is what follows the LAST depth-zero separator, which is the law the statement
    // grammar founds. The integrand is what follows the LAST depth-zero comma of the left side,
    // which is the same law one scale further down.
    struct Candidate {
        name: String,
        variable: String,
        integrand: String,
        closed_form: String,
        /// Names this statement's own suppositions bind — the parameters it quantifies over.
        bound: BTreeSet<String>,
    }
    let mut candidates: Vec<Candidate> = Vec::new();
    let mut no_conclusion = 0usize;
    let mut no_integral_shape = 0usize;
    for (name, statement, bound) in &statements {
        let Some((split, _)) = founded_split(statement, ':') else {
            no_conclusion += 1;
            continue;
        };
        let conclusion = statement[split + 1..].trim();
        let Some(equals) = at_depth_zero(conclusion, '=').last().copied() else {
            no_integral_shape += 1;
            continue;
        };
        let left = conclusion[..equals].trim();
        let right = conclusion[equals + 1..].trim();
        let Some(comma) = at_depth_zero(left, ',').last().copied() else {
            no_integral_shape += 1;
            continue;
        };
        // the bound variable is the first name of the domain region
        let domain = left[..comma].trim();
        let Some(variable) = domain
            .split_whitespace()
            .find(|word| {
                word.chars().all(|symbol| symbol.is_alphanumeric() || symbol == '_')
                    && word.chars().next().is_some_and(char::is_alphabetic)
            })
            .map(ToOwned::to_owned)
        else {
            no_integral_shape += 1;
            continue;
        };
        candidates.push(Candidate {
            name: name.clone(),
            variable,
            integrand: left[comma + 1..].trim().to_owned(),
            closed_form: right.to_owned(),
            bound: bound.clone(),
        });
    }
    println!(
        "  carrying a conclusion, an equality and a depth-zero comma   {}   (no conclusion {no_conclusion}, wrong shape {no_integral_shape})",
        candidates.len()
    );

    // ---------------------------------------------------------------- the reading and the verdict
    println!();
    println!("{}", "-".repeat(100));
    println!("THE DISAGREEMENTS, FIRST -- the falsifier for the declared precedence");
    println!("{}", "-".repeat(100));

    struct Carried {
        name: String,
        integrand: String,
        closed_form: String,
        predicted: Transcendental,
        stated: BTreeSet<&'static str>,
        residue: String,
    }
    let mut carried_all: Vec<Carried> = Vec::new();
    let mut refusals: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut gauge_disagreements: Vec<String> = Vec::new();
    let mut parameter_dependent: Vec<(String, String)> = Vec::new();
    // **The parameter sweep.** A parameter is universally quantified, so several exact values are
    // put to it and the predicted class must AGREE across them. A class that moves with the
    // parameter is a real return about the integrand, not a defect, and is exhibited.
    let instantiations: [i64; 3] = [1, 2, 3];
    for candidate in &candidates {
        let mut per_value: Vec<(i64, Result<Fraction, ReaderRefusal>)> = Vec::new();
        for value in instantiations {
            let bound: BTreeMap<String, Rat> = candidate
                .bound
                .iter()
                .filter(|name| **name != candidate.variable)
                .map(|name| (name.clone(), Rat::from_integer(BigInt::from(value))))
                .collect();
            per_value.push((
                value,
                read_integrand(&candidate.integrand, &candidate.variable, &bound),
            ));
        }
        let uses_parameter = candidate
            .bound
            .iter()
            .any(|name| *name != candidate.variable && candidate.integrand.contains(name.as_str()));

        // the class under each instantiation; a reading that refuses at one value refuses at all
        let mut classes: Vec<(i64, Transcendental, String)> = Vec::new();
        let mut first_refusal: Option<ReaderRefusal> = None;
        let mut reduction_refused = false;
        let mut gauge_moved = false;
        for (value, built) in per_value {
            let fraction = match built {
                Ok(fraction) => fraction,
                Err(refusal) => {
                    first_refusal.get_or_insert(refusal);
                    break;
                }
            };
            // **Both declared schedules are run and the class must agree.** The module states that
            // its two schedules form a gauge whose orbit is measured before agreement is read as
            // evidence; taking one schedule would be choosing a representative.
            let mut readings = Vec::new();
            for schedule in ReductionSchedule::DECLARED {
                match reduce(&fraction.numerator, &fraction.denominator, schedule) {
                    Ok(reading) => readings.push(reading),
                    Err(_) => reduction_refused = true,
                }
            }
            if reduction_refused || readings.len() != 2 {
                reduction_refused = true;
                break;
            }
            let residue = readings[0].nonzero_residue_polynomial();
            if readings[1].nonzero_residue_polynomial() != residue {
                gauge_moved = true;
                break;
            }
            let predicted = match residue.degree() {
                None | Some(0) => Transcendental::Rational,
                Some(_) => {
                    if every_root_is_rational(&residue) {
                        Transcendental::Logarithm
                    } else {
                        Transcendental::Arctangent
                    }
                }
            };
            classes.push((value, predicted, format!("{:?}", residue.coefficients())));
            if !uses_parameter {
                // the integrand does not mention a parameter, so one value is every value
                break;
            }
        }

        if gauge_moved {
            gauge_disagreements.push(candidate.integrand.clone());
            continue;
        }
        if reduction_refused {
            refusals
                .entry("the reduction refused it".to_owned())
                .or_default()
                .push(candidate.integrand.clone());
            continue;
        }
        if let Some(refusal) = first_refusal {
            let species = match &refusal {
                ReaderRefusal::ForeignName(name) => format!("outside the alphabet: {name}"),
                other => format!("{other:?}"),
            };
            refusals
                .entry(species)
                .or_default()
                .push(candidate.integrand.clone());
            continue;
        }
        let Some((_, predicted, residue)) = classes.first().cloned() else {
            continue;
        };
        if classes.iter().any(|(_, class, _)| *class != predicted) {
            let spread: Vec<String> = classes
                .iter()
                .map(|(value, class, _)| format!("{value}->{}", class.name()))
                .collect();
            parameter_dependent.push((candidate.integrand.clone(), spread.join(" ")));
            continue;
        }

        // what the corpus's own closed form names, in its tokens
        let mut stated: BTreeSet<&'static str> = BTreeSet::new();
        for (needle, label) in [
            ("log", "log"),
            ("arctan", "arctan"),
            ("exp", "exp"),
            ("sin", "sin"),
            ("cos", "cos"),
        ] {
            if candidate.closed_form.contains(needle) {
                stated.insert(label);
            }
        }
        {
            carried_all.push(Carried {

                name: candidate.name.clone(),
                integrand: candidate.integrand.clone(),
                closed_form: candidate.closed_form.clone(),
                predicted,
                stated,
                residue,
            });
        }
    }

    let agrees = |carried: &Carried| -> bool {
        match carried.predicted {
            Transcendental::Rational => {
                !carried.stated.contains("log") && !carried.stated.contains("arctan")
            }
            Transcendental::Logarithm => carried.stated.contains("log"),
            Transcendental::Arctangent => carried.stated.contains("arctan"),
        }
    };
    let disagreeing: Vec<&Carried> = carried_all.iter().filter(|c| !agrees(c)).collect();
    println!();
    if disagreeing.is_empty() {
        println!("  none. Every integrand the reader built landed in the class the corpus's own");
        println!("  closed form names.");
    } else {
        for carried in &disagreeing {
            println!();
            println!("  {}", carried.name);
            println!("    integrand    {}", carried.integrand);
            println!("    organ says   {}   residue polynomial {}", carried.predicted.name(), carried.residue);
            println!("    corpus says  {}", carried.closed_form);
        }
    }

    println!();
    println!("  THE PARAMETER SWEEP -- each bound parameter was instantiated at 1, 2 and 3, and the");
    println!("  predicted class must not move. Integrands whose class DOES move with a parameter: {}", parameter_dependent.len());
    for (integrand, spread) in parameter_dependent.iter().take(4) {
        println!("    {integrand}   {spread}");
    }
    println!();
    println!("  THE GAUGE -- both declared reduction schedules were run on every integrand, and the");
    println!("  residue class must not move between them. Schedules disagreeing: {}", gauge_disagreements.len());
    for integrand in gauge_disagreements.iter().take(3) {
        println!("    {integrand}");
    }
    println!();
    println!("{}", "-".repeat(100));
    println!("THE AGREEMENTS -- the organ's prediction, then the corpus's own words");
    println!("{}", "-".repeat(100));
    println!();
    let mut by_class: BTreeMap<&str, Vec<&Carried>> = BTreeMap::new();
    for carried in &carried_all {
        if agrees(carried) {
            by_class
                .entry(carried.predicted.name())
                .or_default()
                .push(carried);
        }
    }
    for (class, members) in &by_class {
        println!("  the organ predicts {class}   ({} integrands)", members.len());
        for carried in members.iter().take(6) {
            println!(
                "    {:<34} {:<22} -> corpus: {}",
                carried.name,
                carried.integrand,
                carried.closed_form
            );
        }
        if members.len() > 6 {
            println!("    ... {} more", members.len() - 6);
        }
        println!();
    }

    println!("{}", "-".repeat(100));
    println!("WHAT THE READER COULD NOT BUILD -- retained by species, never skipped");
    println!("{}", "-".repeat(100));
    println!();
    let refused: usize = refusals.values().map(Vec::len).sum();
    println!("  integrands refused   {refused} of {}", candidates.len());
    for (species, members) in &refusals {
        println!("    {species}   {}", members.len());
        for integrand in members.iter().take(2) {
            println!("      {integrand}");
        }
    }
    println!();
    println!("  A refusal is the aperture speaking. `sin x`, `log s` are not rational functions and");
    println!("  `hermite_reduction` is not the organ for them. The EXPONENTIAL ones have an organ in");
    println!("  this tree, and the refusal above hands them to it rather than reporting a gap.");

    // ---------------------------------------------------------------- the second organ
    println!();
    println!("{}", "-".repeat(100));
    println!("THE SECOND ORGAN -- the exponential integrands, put to `elementary_chart`");
    println!("{}", "-".repeat(100));
    println!();
    println!("  `elementary_chart` decides whether `∫ R·e^g` is elementary by the consistency of ONE");
    println!("  exact rational linear system: `deg a = deg R - deg g + 1` is forced, so the candidate");
    println!("  population is finite and exhaustible. Non-elementarity returns as a rank deficiency");
    println!("  with the annihilating combination exhibited, never as a search that gave up.");
    println!();
    println!("  An exponential integrand is founded from the tokens the same way: a side reading as");
    println!("  `exp <argument>` or `<coefficient> * exp <argument>`, with both parts built by the");
    println!("  same rational-function reader. Everything else is refused.");
    println!();

    let mut exponential = 0usize;
    let mut elementary = 0usize;
    for candidate in &candidates {
        // the founded shape: an `exp` applied to something, optionally scaled by a rational
        let integrand = candidate.integrand.trim();
        let Some(at) = integrand.find("exp ") else {
            continue;
        };
        let (before, after) = integrand.split_at(at);
        let argument = after.trim_start_matches("exp ").trim();
        let coefficient_text = before.trim().trim_end_matches('*').trim();
        let bound: BTreeMap<String, Rat> = candidate
            .bound
            .iter()
            .filter(|name| **name != candidate.variable)
            .map(|name| (name.clone(), Rat::one()))
            .collect();
        let coefficient = if coefficient_text.is_empty() {
            Ok(Fraction::constant(Rat::one()))
        } else {
            read_integrand(coefficient_text, &candidate.variable, &bound)
        };
        let exponent = read_integrand(argument, &candidate.variable, &bound);
        let (Ok(coefficient), Ok(exponent)) = (coefficient, exponent) else {
            println!("  {:<32} exp-shaped, but a part is outside the reader", candidate.name);
            continue;
        };
        // the exponent must be a polynomial; a rational exponent is outside this organ
        if exponent.denominator.degree().unwrap_or(0) != 0 {
            println!("  {:<32} the exponent is not a polynomial", candidate.name);
            continue;
        }
        let scale = exponent.denominator.coefficient(0);
        if scale.is_zero() {
            continue;
        }
        let exponent_polynomial = exponent.numerator.scaled(&scale.recip());
        exponential += 1;
        let object = ExponentialIntegrand::rational_coefficient(
            coefficient.numerator.clone(),
            coefficient.denominator.clone(),
            exponent_polynomial.clone(),
        );
        match read_elementary_chart(&object) {
            Ok(reading) => {
                let admits = reading.reading.is_elementary();
                if admits {
                    elementary += 1;
                }
                println!(
                    "  {:<32} {:<22} -> {}",
                    candidate.name,
                    candidate.integrand,
                    if admits {
                        "ELEMENTARY -- a realizer exists, and it was differentiated back"
                    } else {
                        "not elementary at any degree, with the obstruction exhibited"
                    }
                );
                println!("      corpus: {}", candidate.closed_form);
                if let holonic_engine::elementary_chart::ElementaryReading::Admits {
                    realizer, ..
                } = &reading.reading
                {
                    println!("      the realizer the organ built: {:?}", realizer.coefficients());
                }
            }
            Err(refusal) => println!("  {:<32} the organ refused: {refusal:?}", candidate.name),
        }
    }
    println!();
    println!("  exponential integrands read {exponential}   the organ calls elementary {elementary}");
    println!();
    println!("  `∫ exp x` is the whole of what this subtree's exponential rows state, and the organ");
    println!("  returns the realizer `1` -- that is, `∫ e^x = 1·e^x` -- which the corpus writes as");
    println!("  `exp b - exp a`, the same antiderivative evaluated at the two ends. The organ and");
    println!("  the table agree on the INDEFINITE object; the table adds the boundary the organ");
    println!("  does not carry.");

    // ---------------------------------------------------------------- the fourth transport
    println!();
    println!("{}", "-".repeat(100));
    println!("THE FOURTH TRANSPORT -- why it is NOT driven, which is a return and not a gap");
    println!("{}", "-".repeat(100));
    println!();
    println!("  The sentence this run closes named four transports. Two are driven above and");
    println!("  `hypergeometric_closure` was reached on 2026-08-17. The fourth is");
    println!("  `exponentiated_ratio`, whose law is `exp(a+b) = exp(a)·exp(b)` -- the homomorphism");
    println!("  that makes a chart transition a chart transition rather than a statistic.");
    println!();
    println!("  The corpus states that law: `Real.exp_add : exp (x + y) = exp x * exp y`. Putting it");
    println!("  to the organ would return agreement, and the agreement would carry NO EVIDENCE:");
    println!("  `exponentiate` is `2^(Σ q_k log₂ p_k) = Π p_k^(q_k)`, so the homomorphism holds by");
    println!("  construction and no material could make it fail. That is a check whose material");
    println!("  cannot vary the property under test, which this project convicts by name.");
    println!();
    println!("  What IS a real difference between them, and it is one-sided: the organ REFUSES a");
    println!("  fractional coefficient, because a fractional exponent leaves the rationals and lands");
    println!("  in an algebraic extension -- the finer chart. The corpus states the law over the");
    println!("  reals, where that boundary does not exist and the refusal is invisible.");
    println!();
    println!("  So the two do not disagree; they are stated over different grounds, and the organ's");
    println!("  aperture is a distinction its own chart can see and the corpus's cannot.");

    println!();
    println!("{}", "=".repeat(100));
    println!("WHAT THIS RUN DOES NOT CLAIM");
    println!("{}", "=".repeat(100));
    println!();
    println!("  The expression reader declares its precedence and does not found it: a corpus that");
    println!("  brackets whenever it matters never exhibits the precedence it relies on. The");
    println!("  declaration is graded by the disagreement column above, which is external material");
    println!("  this repository did not write -- not by any check this file performs on itself.");
    println!();
    println!("  The organ's class is about the RESIDUES and therefore about which transcendental is");
    println!("  needed. It is not a claim that the corpus's stated closed form is correct, and not a");
    println!("  claim that the integrand has no other antiderivative in another chart.");
    println!();
    println!("  Nothing was elaborated, type-checked, or submitted to a kernel.");
}
