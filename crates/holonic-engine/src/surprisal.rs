//! Surprisal as an exact symbolic form, never as a number.
//!
//! ## What this implements, and what it deliberately does not
//!
//! `canon/THE_RECOVERED_LAW.md` §1, Brandon-ratified 2026-07-14, states the instrument:
//!
//! > *"Surprisal and cross-entropy are exact instruments. For a 2/3 gear word `p = 2^-a 3^-b`,
//! > `S = a + b·log₂3`, exact symbolically. No smoothing constant is owed: if `Q_B(a) = 0` the live
//! > event FOUNDs a new relation and changes the support."*
//!
//! and §3 places Shannon precisely:
//!
//! > *"`H(X)` is an exact scalar receiver measure. It does not by itself retain caused incidence,
//! > chronology, topology, holonomy, obstruction, morphology, apparatus, or lineage. Those are not
//! > objections to Shannon theory; they identify what its declared quotient intentionally forgets."*
//!
//! Measured 2026-08-08, before this module existed: `shannon`, `entropy`, `surprisal`,
//! `cross_entropy`, `kullback`, `log2` and `mutual_information` returned **zero files** across every
//! library crate and every `soma/` library. The body implemented the part Shannon's quotient
//! *forgets* — `receiver_exact_compression`'s collapsed-pair population, each pair carrying the
//! shortest word that separates it — and not the quotient. The fiber without the base, so nothing
//! could say what a quotient **cost**.
//!
//! The only `-log₂` ever written in this lineage was a **string formatter** that emitted
//! `"-log2(3/4)"` as text and never evaluated a logarithm. Then it was deleted. That instinct was
//! right and this module is its typed form.
//!
//! ## The carrier is a form, not a value
//!
//! For a positive rational `p = Π pᵢ^{eᵢ}` with `eᵢ ∈ ℤ`, surprisal is
//!
//! ```text
//!   S(p) = -log₂ p = Σᵢ (-eᵢ) · log₂ pᵢ
//! ```
//!
//! which is a **ℚ-linear form in the logarithms of the primes**. It is stored as its coefficient
//! map and **never evaluated**. `CLAUDE.md` §2b's rule for signs and
//! `canon/THE_MATHEMATICS_TABLET.md` §1's rule for floats are the same rule here: a decimal
//! surprisal keeps the magnitude and discards the term structure that produced it, and the term
//! structure is what lets a later receiver differentiate, compose, or continue it.
//!
//! ## Three facts that make this a carrier rather than a notation
//!
//! **Vanishing and equality are decided EXACTLY, with no enclosure.** If `Σ qᵢ log₂ pᵢ = 0` with
//! `qᵢ ∈ ℚ`, clear denominators to get `Π pᵢ^{nᵢ} = 1` with `nᵢ ∈ ℤ`; unique factorization forces
//! every `nᵢ = 0`. So `{log₂ p : p prime}` is ℚ-linearly independent and the zero test is integer
//! arithmetic on the coefficients. This is elementary — **no transcendence theory is invoked and
//! none is needed.** It is why `S(P) = S(Q)` is decidable here while `S(P) < S(Q)` is not.
//!
//! **Ordering two distinct forms is not exact, and says so.** [`SymbolicSurprisal::compare`] returns
//! [`ExactOrdering`], whose `Open` variant is the honest answer when the certified enclosures
//! overlap. From `exact_value`'s own opening: *"Values which cannot yet be ordered from their exact
//! certificates return `Open` rather than falling through to an epsilon comparison."*
//!
//! **Zero support is not infinity.** [`Support::Unsupported`] is a typed refusal carrying the event
//! that had no standing, and the law is that the live event **FOUNDs a new relation and changes the
//! support** — never that a smoothing constant is added. [`Support::found`] is that transition and
//! the declared control exercises it.
//!
//! ## What this is not
//!
//! Not a distribution inside the body. Not a governor, a selector, a threshold, or a crown. `CLAUDE.md`
//! §13 rule 2: **a scalar that measures is lawful, a scalar that governs is not.** Nothing here
//! chooses a deed; every return is a form or a typed refusal, and the four-state ordering means even
//! a comparison may decline to decide.

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use relational_geometry::exact_analysis::log_rational_interval;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::{ExactInterval, ExactOrdering};

/// Series terms taken when enclosing `log₂ p`. Declared, not tuned.
const LOG_SERIES_TERMS: u32 = 64;
/// Working bits for the enclosure grain. A grain change, never a float conversion.
const LOG_SERIES_BITS: u32 = 192;

/// The declared grain an enclosure is taken at: series terms and working bits, carried as one
/// receiver coordinate instead of two loose arguments.
///
/// **A receiver coordinate, never a tuning knob.** Nothing in this module selects a grain; a caller
/// declares one and every return carries it, so a verdict is not separable from the grain that
/// reached it. Two verdicts on one pair at two grains are two readings and not a disagreement —
/// `Open` is a statement about the receiver's grain, never about the forms.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Grain {
    pub terms: u32,
    pub bits: u32,
}

impl Grain {
    /// The grain [`SymbolicSurprisal::enclosure`] and [`SymbolicSurprisal::compare`] take.
    pub const DECLARED: Self = Self {
        terms: LOG_SERIES_TERMS,
        bits: LOG_SERIES_BITS,
    };

    pub const fn at(terms: u32, bits: u32) -> Self {
        Self { terms, bits }
    }
}

impl std::fmt::Display for Grain {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "grain(terms={}, bits={})", self.terms, self.bits)
    }
}

/// `S = Σ_p coefficient(p) · log₂ p`, exact, stored and never evaluated.
///
/// A coefficient is a `Rat` so that a fractional power — a `√2` gear word, `p^{1/2}` — is
/// representable without leaving the carrier. The map holds no zero coefficients: a term that
/// cancels is removed, because unlike `ComparativeMultiplicity`'s arms these coefficients are a
/// **basis expansion** and not a pair of passages. Vanishing here is genuine absence of a term.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymbolicSurprisal {
    terms: BTreeMap<u64, Rat>,
}

impl SymbolicSurprisal {
    /// The zero form. `S(1) = 0` — a certainty carries no surprisal.
    pub fn zero() -> Self {
        Self::default()
    }

    /// `S = coefficient · log₂ prime`, for one prime.
    pub fn term(prime: u64, coefficient: Rat) -> Result<Self, SurprisalError> {
        let mut form = Self::default();
        form.add_term(prime, coefficient)?;
        Ok(form)
    }

    fn add_term(&mut self, prime: u64, coefficient: Rat) -> Result<(), SurprisalError> {
        if prime < 2 {
            return Err(SurprisalError::NotAPrime(prime));
        }
        if coefficient.is_zero() {
            return Ok(());
        }
        let next = match self.terms.get(&prime) {
            Some(current) => current.clone() + coefficient,
            None => coefficient,
        };
        if next.is_zero() {
            self.terms.remove(&prime);
        } else {
            self.terms.insert(prime, next);
        }
        Ok(())
    }

    /// The surprisal of a probability, exactly: `S(p) = -log₂ p`.
    ///
    /// `p` must be a positive rational at most one. `p = 1` returns the zero form. `p = 0` is not a
    /// probability this carrier accepts — that is [`Support::Unsupported`]'s case and it FOUNDs.
    pub fn of_probability(probability: &Rat) -> Result<Self, SurprisalError> {
        if !probability.is_positive() {
            return Err(SurprisalError::NonPositiveProbability);
        }
        if probability > &Rat::one() {
            return Err(SurprisalError::ProbabilityAboveOne);
        }
        let numerator = probability.numer().magnitude().clone();
        let denominator = probability.denom().magnitude().clone();
        let mut form = Self::default();
        // S(a/b) = -log2(a) + log2(b): the denominator's primes enter positively.
        for (prime, exponent) in factor_biguint(&denominator)? {
            form.add_term(prime, Rat::from_integer(BigInt::from(exponent)))?;
        }
        for (prime, exponent) in factor_biguint(&numerator)? {
            form.add_term(prime, -Rat::from_integer(BigInt::from(exponent)))?;
        }
        Ok(form)
    }

    /// The terms, in ascending prime order. The returned artifact.
    pub fn terms(&self) -> &BTreeMap<u64, Rat> {
        &self.terms
    }

    /// **Exact.** True when every coefficient vanishes, which by ℚ-linear independence of
    /// `{log₂ p}` is true exactly when the form is zero as a real number.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// `self + other`, exactly. The additive face of a multiplicative chain.
    pub fn plus(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (prime, coefficient) in &other.terms {
            // Both operands are already validated, so the prime bound cannot fail here.
            let _ = result.add_term(*prime, coefficient.clone());
        }
        result
    }

    /// `self - other`, exactly.
    pub fn minus(&self, other: &Self) -> Self {
        self.plus(&other.scaled(&-Rat::one()))
    }

    /// `factor · self`, exactly.
    pub fn scaled(&self, factor: &Rat) -> Self {
        if factor.is_zero() {
            return Self::zero();
        }
        Self {
            terms: self
                .terms
                .iter()
                .map(|(prime, coefficient)| (*prime, coefficient.clone() * factor.clone()))
                .collect(),
        }
    }

    /// A certified enclosure of the form's real value, in bits.
    ///
    /// Each `log₂ p` is enclosed by `log_rational_interval` and scaled by its exact coefficient;
    /// the sum of intervals is the return. This is the only place a numeric reading is taken, and
    /// it returns a **set**, never a point.
    pub fn enclosure(&self) -> Result<ExactInterval, SurprisalError> {
        self.enclosure_at(LOG_SERIES_TERMS, LOG_SERIES_BITS)
    }

    /// The same enclosure at a **declared grain**.
    ///
    /// The grain is a receiver coordinate, not a tuning knob: a coarser one returns a wider set and
    /// therefore decides fewer comparisons. `the_ordering_is_non_vacuous_and_the_grain_is_what_moves_it`
    /// exhibits one pair returning `Open` at a coarse grain and `Greater` at a fine one, which is what
    /// proves the four-state carrier is doing work rather than decorating a two-state answer.
    pub fn enclosure_at(&self, terms: u32, bits: u32) -> Result<ExactInterval, SurprisalError> {
        let mut lower = Rat::zero();
        let mut upper = Rat::zero();
        let log_two = log_rational_interval(&Rat::from_integer(2.into()), terms, bits)
            .map_err(|_| SurprisalError::EnclosureUnavailable)?;
        for (prime, coefficient) in &self.terms {
            // log2(p) = ln(p) / ln(2), enclosed by dividing the two enclosures outward.
            let natural =
                log_rational_interval(&Rat::from_integer(BigInt::from(*prime)), terms, bits)
                    .map_err(|_| SurprisalError::EnclosureUnavailable)?;
            if !log_two.lower.is_positive() {
                return Err(SurprisalError::EnclosureUnavailable);
            }
            let base_lower = natural.lower / log_two.upper.clone();
            let base_upper = natural.upper / log_two.lower.clone();
            let (term_lower, term_upper) = if coefficient.is_negative() {
                (
                    base_upper.clone() * coefficient.clone(),
                    base_lower.clone() * coefficient.clone(),
                )
            } else {
                (
                    base_lower.clone() * coefficient.clone(),
                    base_upper.clone() * coefficient.clone(),
                )
            };
            lower += term_lower;
            upper += term_upper;
        }
        ExactInterval::new(lower, upper).map_err(|_| SurprisalError::EnclosureUnavailable)
    }

    /// The same enclosure at a declared [`Grain`].
    pub fn enclosure_grain(&self, grain: Grain) -> Result<ExactInterval, SurprisalError> {
        self.enclosure_at(grain.terms, grain.bits)
    }

    /// Compare two forms, returning `Open` when the certified enclosures cannot separate them.
    ///
    /// Equality is decided **exactly** first, by the coefficient test — so `Equal` is never a
    /// numeric accident. Only strict ordering consults enclosures, and only that path can return
    /// `Open`.
    pub fn compare(&self, other: &Self) -> Result<ExactOrdering, SurprisalError> {
        self.compare_at(other, LOG_SERIES_TERMS, LOG_SERIES_BITS)
    }

    /// The same comparison at a declared grain. Equality is still decided **exactly**, before any
    /// enclosure is taken, so no grain can make two distinct forms compare `Equal`.
    pub fn compare_at(
        &self,
        other: &Self,
        terms: u32,
        bits: u32,
    ) -> Result<ExactOrdering, SurprisalError> {
        let difference = self.minus(other);
        if difference.is_zero() {
            return Ok(ExactOrdering::Equal);
        }
        let enclosure = difference.enclosure_at(terms, bits)?;
        if enclosure.lower.is_positive() {
            Ok(ExactOrdering::Greater)
        } else if enclosure.upper.is_negative() {
            Ok(ExactOrdering::Less)
        } else {
            Ok(ExactOrdering::Open)
        }
    }

    /// The same comparison at a declared [`Grain`]. Equality is still decided **exactly**, before
    /// any enclosure is taken, so no grain can make two distinct forms compare `Equal`.
    pub fn compare_grain(
        &self,
        other: &Self,
        grain: Grain,
    ) -> Result<ExactOrdering, SurprisalError> {
        self.compare_at(other, grain.terms, grain.bits)
    }

    /// The form written as its prime-exponent vector — the returned artifact, never a decimal.
    pub fn named(&self) -> String {
        if self.terms.is_empty() {
            return "0".to_owned();
        }
        self.terms
            .iter()
            .map(|(prime, coefficient)| {
                if coefficient == &Rat::one() {
                    format!("log2({prime})")
                } else {
                    format!("{coefficient}*log2({prime})")
                }
            })
            .collect::<Vec<_>>()
            .join(" + ")
    }
}

/// What a receiver's standing returns for one event.
///
/// The `Unsupported` arm is the law's own case: zero standing support is **not** infinite surprisal
/// and takes no smoothing constant. It is a typed refusal that a live event resolves by FOUNDing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Support {
    Supported(SymbolicSurprisal),
    /// The receiver's standing has no relation carrying this event.
    Unsupported,
}

impl Support {
    /// Read one event's surprisal against a receiver's standing population.
    ///
    /// `standing` is the exact occurrence count per event, so the quotient is
    /// `p(a) = N(a) / Σ N(a')` — the embodied distribution, `canon/THE_RECOVERED_LAW.md` §1, not a
    /// tabulated one. An event absent from the population, or present with zero count, returns
    /// `Unsupported`.
    pub fn read(standing: &BTreeMap<u64, BigUint>, event: u64) -> Result<Self, SurprisalError> {
        let total: BigUint = standing.values().sum();
        if total.is_zero() {
            return Ok(Self::Unsupported);
        }
        match standing.get(&event) {
            None => Ok(Self::Unsupported),
            Some(count) if count.is_zero() => Ok(Self::Unsupported),
            Some(count) => {
                let probability = Rat::new(BigInt::from(count.clone()), BigInt::from(total));
                Ok(Self::Supported(SymbolicSurprisal::of_probability(
                    &probability,
                )?))
            }
        }
    }

    /// The FOUND: an unsupported event enters the standing and **changes the support**.
    ///
    /// This is the law's alternative to smoothing, and it is a real mutation of the population —
    /// every other event's surprisal moves, because the denominator moved. The declared control
    /// exercises exactly that.
    pub fn found(standing: &mut BTreeMap<u64, BigUint>, event: u64) {
        *standing.entry(event).or_insert_with(BigUint::zero) += BigUint::one();
    }
}

/// Read a whole **population** of events against one standing: one [`Support`] per event.
///
/// [`Support::read`] answers for a single event and re-sums the standing on every call, so a caller
/// holding a population pays that sum once per member. Cost is the smaller half of the reason this
/// exists. The larger half is the **shape of the return**: a population of typed answers with every
/// `Unsupported` arm retained *in place, named by its event*, rather than a reading that collapses
/// the moment one event has no standing — which is what [`cross_entropy`] must do, correctly, because
/// a weighted sum has nowhere to put a refusal.
///
/// The events read are the **population's** own and not the standing's. An event the population
/// carries and the standing does not returns [`Support::Unsupported`] — the arm the law resolves by
/// FOUNDing, and the arm a situated comparison exists to exhibit.
pub fn read_population(
    population: &BTreeMap<u64, BigUint>,
    standing: &BTreeMap<u64, BigUint>,
) -> Result<BTreeMap<u64, Support>, SurprisalError> {
    let total: BigUint = standing.values().sum();
    let mut read = BTreeMap::new();
    for event in population.keys() {
        let support = match standing.get(event) {
            _ if total.is_zero() => Support::Unsupported,
            None => Support::Unsupported,
            Some(count) if count.is_zero() => Support::Unsupported,
            Some(count) => {
                let probability =
                    Rat::new(BigInt::from(count.clone()), BigInt::from(total.clone()));
                Support::Supported(SymbolicSurprisal::of_probability(&probability)?)
            }
        };
        read.insert(*event, support);
    }
    Ok(read)
}

/// `H(P,Q) = Σ_a P(a) · S_Q(a)` — the depth incurred when one population is received through
/// another's standing code.
///
/// Returns `Unsupported` for the whole reading when any event `P` carries has no support in `Q`.
/// That is not a failure: it is the case the law says FOUNDs, and collapsing it to a large finite
/// number would be the smoothing constant this carrier refuses.
pub fn cross_entropy(
    population: &BTreeMap<u64, BigUint>,
    code: &BTreeMap<u64, BigUint>,
) -> Result<Support, SurprisalError> {
    let total: BigUint = population.values().sum();
    if total.is_zero() {
        return Ok(Support::Unsupported);
    }
    let mut form = SymbolicSurprisal::zero();
    for (event, count) in population {
        if count.is_zero() {
            continue;
        }
        let weight = Rat::new(BigInt::from(count.clone()), BigInt::from(total.clone()));
        match Support::read(code, *event)? {
            Support::Unsupported => return Ok(Support::Unsupported),
            Support::Supported(depth) => form = form.plus(&depth.scaled(&weight)),
        }
    }
    Ok(Support::Supported(form))
}

/// `H(P) = Σ_a P(a) · S_P(a)` — the population received through its own code.
pub fn entropy(population: &BTreeMap<u64, BigUint>) -> Result<Support, SurprisalError> {
    cross_entropy(population, population)
}

fn factor_biguint(value: &BigUint) -> Result<Vec<(u64, u32)>, SurprisalError> {
    if value.is_zero() {
        return Err(SurprisalError::NonPositiveProbability);
    }
    let mut remaining: BigUint = value.clone();
    let mut factors = Vec::new();
    let mut prime: u64 = 2;
    while &BigUint::from(prime) * &BigUint::from(prime) <= remaining {
        let divisor = BigUint::from(prime);
        let mut exponent = 0u32;
        while (&remaining % &divisor).is_zero() {
            remaining /= &divisor;
            exponent += 1;
        }
        if exponent > 0 {
            factors.push((prime, exponent));
        }
        prime += if prime == 2 { 1 } else { 2 };
    }
    if remaining > BigUint::one() {
        let leftover: u64 = (&remaining)
            .try_into()
            .map_err(|_| SurprisalError::CarrierOverflow)?;
        factors.push((leftover, 1));
    }
    Ok(factors)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum SurprisalError {
    #[error("a surprisal term requires a prime at least two, received {0}")]
    NotAPrime(u64),
    #[error("a probability must be positive; zero support is Unsupported and FOUNDs")]
    NonPositiveProbability,
    #[error("a probability may not exceed one")]
    ProbabilityAboveOne,
    #[error("the certified logarithm enclosure was unavailable at the declared grain")]
    EnclosureUnavailable,
    #[error("a residual prime factor exceeded the machine-word carrier")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn population(entries: &[(u64, u32)]) -> BTreeMap<u64, BigUint> {
        entries
            .iter()
            .map(|(event, count)| (*event, BigUint::from(*count)))
            .collect()
    }

    /// The law's own worked example, returned as a form rather than a number.
    #[test]
    fn a_two_three_gear_word_returns_a_plus_b_log_two_three() {
        // p = 2^-3 · 3^-2 = 1/72, so S = 3 + 2·log2(3).
        let form = SymbolicSurprisal::of_probability(&rat(1, 72)).unwrap();
        assert_eq!(form.terms().get(&2), Some(&Rat::from_integer(3.into())));
        assert_eq!(form.terms().get(&3), Some(&Rat::from_integer(2.into())));
        assert_eq!(form.terms().len(), 2);
        assert_eq!(form.named(), "3*log2(2) + 2*log2(3)");
    }

    /// Certainty carries no surprisal, and the zero test is exact.
    #[test]
    fn a_certainty_returns_the_zero_form_and_the_test_is_exact() {
        let form = SymbolicSurprisal::of_probability(&Rat::one()).unwrap();
        assert!(form.is_zero());
        assert_eq!(form.named(), "0");
        assert_eq!(form.enclosure().unwrap(), ExactInterval::point(Rat::zero()));
    }

    /// **Control 1 — additivity.** The multiplicative chain becomes an additive depth face, exactly,
    /// with no rounding anywhere. This is the property a float carrier cannot have.
    #[test]
    fn surprisal_is_additive_over_a_conditional_chain_exactly() {
        let chain = [rat(1, 2), rat(2, 3), rat(3, 5), rat(5, 7)];
        let mut product = Rat::one();
        let mut summed = SymbolicSurprisal::zero();
        for step in &chain {
            product *= step.clone();
            summed = summed.plus(&SymbolicSurprisal::of_probability(step).unwrap());
        }
        let whole = SymbolicSurprisal::of_probability(&product).unwrap();
        assert_eq!(
            whole, summed,
            "S(prod p_k) = sum S(p_k) as forms, not merely as numbers"
        );
        // The telescoping cancelled every intermediate prime: 1/2 · 2/3 · 3/5 · 5/7 = 1/7.
        assert_eq!(whole.named(), "log2(7)");
    }

    /// **Control 2 — canonicalisation.** Two constructions of one rational return one form.
    #[test]
    fn two_constructions_of_one_probability_return_one_form() {
        let direct = SymbolicSurprisal::of_probability(&rat(3, 12)).unwrap();
        let reduced = SymbolicSurprisal::of_probability(&rat(1, 4)).unwrap();
        assert_eq!(direct, reduced);
        assert_eq!(direct.named(), "2*log2(2)");
    }

    /// **Control 3 — Gibbs, and it is the falsifier.** `H(P,Q) >= H(P)`, with equality exactly when
    /// the code is the population. A wrong implementation violates a real theorem here.
    #[test]
    fn cross_entropy_never_undercuts_the_populations_own_entropy() {
        let p = population(&[(1, 3), (2, 1)]);
        let q = population(&[(1, 1), (2, 1)]);

        let Support::Supported(own) = entropy(&p).unwrap() else {
            panic!("the population supports itself");
        };
        let Support::Supported(through_q) = cross_entropy(&p, &q).unwrap() else {
            panic!("q supports every event of p");
        };

        // H(P,Q) - H(P) = D_KL(P || Q) >= 0, and it is STRICT here because P != Q.
        let divergence = through_q.minus(&own);
        assert!(
            !divergence.is_zero(),
            "P and Q differ, so the divergence does"
        );
        assert_eq!(
            divergence.compare(&SymbolicSurprisal::zero()).unwrap(),
            ExactOrdering::Greater,
            "Gibbs: coding P through Q costs strictly more than coding P through P"
        );

        // And equality holds exactly when the code is the population — decided with no enclosure.
        let Support::Supported(through_self) = cross_entropy(&p, &p).unwrap() else {
            panic!("supported");
        };
        assert_eq!(
            through_self.compare(&own).unwrap(),
            ExactOrdering::Equal,
            "H(P,P) = H(P), and this is the EXACT branch — the coefficients cancel"
        );
    }

    /// **Control 4 — the four-state ordering is non-vacuous.** The declared material must produce
    /// both a definite verdict and an `Open`, or the carrier is decorative and this is `CLAUDE.md`
    /// §8's trivial-orbit defect wearing a passing result.
    #[test]
    fn the_ordering_is_non_vacuous_and_the_grain_is_what_moves_it() {
        let eighth = SymbolicSurprisal::of_probability(&rat(1, 8)).unwrap();
        let half = SymbolicSurprisal::of_probability(&rat(1, 2)).unwrap();
        assert_eq!(
            eighth.compare(&half).unwrap(),
            ExactOrdering::Greater,
            "1/8 is more surprising than 1/2"
        );

        // Equality is decided on coefficients, with NO enclosure taken. No grain can change it.
        let ninth = SymbolicSurprisal::of_probability(&rat(1, 9)).unwrap();
        let two_log_three = SymbolicSurprisal::term(3, Rat::from_integer(2.into())).unwrap();
        assert_eq!(ninth.compare(&two_log_three).unwrap(), ExactOrdering::Equal);
        assert_eq!(
            ninth.compare_at(&two_log_three, 1, 4).unwrap(),
            ExactOrdering::Equal,
            "the exact branch is reached before any enclosure, so the coarsest grain still decides it"
        );

        // THE CONTROL. One pair, two declared grains, two different verdicts. `log2(3)` and
        // `log2(5)` differ by about 0.737, so a grain coarse enough to widen each enclosure past
        // that cannot separate them -- and the carrier says `Open` instead of guessing.
        let log_three = SymbolicSurprisal::term(3, Rat::one()).unwrap();
        let log_five = SymbolicSurprisal::term(5, Rat::one()).unwrap();

        let fine = log_five.compare(&log_three).unwrap();
        assert_eq!(
            fine,
            ExactOrdering::Greater,
            "log2(5) > log2(3) at the declared grain"
        );

        let coarse = log_five.compare_at(&log_three, 1, 4).unwrap();
        assert_eq!(
            coarse,
            ExactOrdering::Open,
            "at a grain too coarse to separate them the carrier declines to decide, and THAT is \
             the four-state ordering doing work rather than decorating a two-state answer"
        );

        // And the refusal is not permanent: refine the grain and the same pair decides.
        assert_eq!(
            log_five.compare_at(&log_three, 48, 128).unwrap(),
            ExactOrdering::Greater,
            "an Open is a statement about the receiver's grain, never about the forms"
        );
    }

    /// Cross-entropy through a code with no support for one of the population's events returns
    /// `Unsupported` for the whole reading rather than a large finite number.
    #[test]
    fn an_unsupported_event_refuses_the_whole_reading_rather_than_smoothing_it() {
        let p = population(&[(1, 1), (7, 1)]);
        let q = population(&[(1, 1), (2, 1)]);
        assert_eq!(cross_entropy(&p, &q).unwrap(), Support::Unsupported);
    }

    /// The enclosure is a set containing the value, and it is taken only when asked.
    #[test]
    fn the_enclosure_contains_the_value_and_is_never_a_point_for_an_irrational_form() {
        // S(1/3) = log2(3) ~ 1.5849625007...
        let form = SymbolicSurprisal::of_probability(&rat(1, 3)).unwrap();
        let enclosure = form.enclosure().unwrap();
        assert!(
            enclosure.lower < enclosure.upper,
            "an irrational form encloses, never points"
        );
        assert!(enclosure.lower > rat(158, 100) && enclosure.upper < rat(159, 100));
    }

    /// A prime below two is refused by name rather than silently accepted.
    #[test]
    fn a_term_below_two_is_refused_by_name() {
        assert_eq!(
            SymbolicSurprisal::term(1, Rat::one()),
            Err(SurprisalError::NotAPrime(1))
        );
    }

    /// **The population constructor agrees with the single-event read, member for member.**
    ///
    /// Two independent implementations of one reading, and the parity is what makes the cheaper one
    /// admissible. The `Unsupported` arm is exercised here too: `7` is in the population and not in
    /// the standing, so it must be returned by name and in place rather than collapsing the reading.
    #[test]
    fn the_population_read_agrees_with_the_single_event_read_and_retains_the_refusal() {
        let emitted = population(&[(1, 3), (2, 1), (7, 5)]);
        let standing = population(&[(1, 1), (2, 3)]);

        let read = read_population(&emitted, &standing).unwrap();
        assert_eq!(read.len(), 3, "one answer per member of the POPULATION");
        for event in emitted.keys() {
            assert_eq!(
                read.get(event),
                Some(&Support::read(&standing, *event).unwrap()),
                "member {event} must agree with the single-event read"
            );
        }
        assert_eq!(
            read.get(&7),
            Some(&Support::Unsupported),
            "retained in place, by name"
        );
        assert!(matches!(read.get(&1), Some(Support::Supported(_))));

        // An empty standing supports nothing, and says so per member rather than erroring.
        let none = read_population(&emitted, &BTreeMap::new()).unwrap();
        assert!(
            none.values()
                .all(|support| *support == Support::Unsupported)
        );
    }

    /// The grain carried as one receiver coordinate is the same reading as the two loose arguments.
    #[test]
    fn a_declared_grain_is_the_same_reading_as_its_two_coordinates() {
        let log_three = SymbolicSurprisal::term(3, Rat::one()).unwrap();
        let log_five = SymbolicSurprisal::term(5, Rat::one()).unwrap();

        let coarse = Grain::at(1, 4);
        assert_eq!(
            log_five.compare_grain(&log_three, coarse).unwrap(),
            log_five.compare_at(&log_three, 1, 4).unwrap()
        );
        assert_eq!(
            log_five.compare_grain(&log_three, coarse).unwrap(),
            ExactOrdering::Open
        );
        assert_eq!(
            log_five.compare_grain(&log_three, Grain::DECLARED).unwrap(),
            ExactOrdering::Greater,
            "the declared grain is the one `compare` takes"
        );
        assert_eq!(
            log_five.enclosure_grain(Grain::DECLARED).unwrap(),
            log_five.enclosure().unwrap()
        );
        assert_eq!(format!("{coarse}"), "grain(terms=1, bits=4)");
    }

    /// A probability above one, or at zero, is refused — the latter because that case FOUNDs.
    #[test]
    fn an_impossible_probability_is_refused_and_zero_is_routed_to_the_found() {
        assert_eq!(
            SymbolicSurprisal::of_probability(&rat(3, 2)),
            Err(SurprisalError::ProbabilityAboveOne)
        );
        assert_eq!(
            SymbolicSurprisal::of_probability(&Rat::zero()),
            Err(SurprisalError::NonPositiveProbability)
        );
    }
}
