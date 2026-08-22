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
        // **REPAIRED 2026-08-18: this was `if prime < 2`, which is not a primality check.**
        //
        // The whole exactness argument of this module rests on the ℚ-linear independence of
        // `{log₂ p : p prime}` — that is what makes `is_zero` true *exactly* when the form is zero
        // as a real number. A composite admitted here breaks it on inputs the public constructor
        // accepts: `term(2, 2).minus(&term(4, 1))` is zero as a real number, and before this repair
        // `is_zero()` returned `false` and `compare` returned `Open`, never `Equal`.
        //
        // Trial division to `√prime` is exact, terminates, and costs nothing at the extents this
        // carrier admits — a `u64` prime index, where the loop is at most 2^32 steps and in practice
        // a handful.
        if !is_prime(prime) {
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

/// The complete reading of one population through another's standing code, with the
/// unsupported half **exhibited** rather than collapsed.
///
/// [`cross_entropy`] returns `Unsupported` for the whole reading the moment one event has no
/// support, discarding the form it had already accumulated over every supported one. That is the
/// correct *face* — a weighted sum has nowhere to put a refusal — and it is the wrong *fiber*,
/// because held-out material almost always carries a novel event, so the aggregate refuses on
/// exactly the material a compression reading must score. Measured 2026-08-14 on this repository's
/// own records: three of four readings collapsed wholesale, one of them discarding 450 supported
/// events out of 700 to report the 250 that were not.
///
/// **Nothing here smooths.** The unsupported events are returned by name, and their weight is
/// returned beside the form rather than folded into it. That is the two-part account the law
/// already implies: the supported half is what the standing code carries, the unsupported half is
/// what must be **founded**, and founding is a real mutation of the standing —
/// [`Support::found`] — not a constant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CrossEntropyFiber {
    /// Every event the population carries has support in the code.
    Supported(SymbolicSurprisal),
    /// Some events have support and some do not.
    ///
    /// `form_over_supported` is `Σ_{a supported} P(a)·S_Q(a)` — weighted by the **whole**
    /// population, so it is a genuine partial sum of the same quantity and never a renormalised
    /// one. `supported_mass + unsupported_mass = 1` exactly.
    Partial {
        form_over_supported: SymbolicSurprisal,
        supported_mass: Rat,
        /// Every event the code cannot carry, by name, in canonical order.
        unsupported: Vec<u64>,
        unsupported_mass: Rat,
    },
    /// No event the population carries has support, or the population is empty.
    Unsupported { unsupported: Vec<u64> },
}

impl CrossEntropyFiber {
    /// The form over whatever was supported. `None` only when nothing was.
    pub fn form(&self) -> Option<&SymbolicSurprisal> {
        match self {
            Self::Supported(form) => Some(form),
            Self::Partial {
                form_over_supported,
                ..
            } => Some(form_over_supported),
            Self::Unsupported { .. } => None,
        }
    }

    /// The events that must be founded before this reading is complete.
    pub fn unsupported(&self) -> &[u64] {
        match self {
            Self::Supported(_) => &[],
            Self::Partial { unsupported, .. } | Self::Unsupported { unsupported } => unsupported,
        }
    }

    /// The coarse face: the reading [`cross_entropy`] returns.
    ///
    /// A `Partial` fiber has a real form and a real refusal, and the face keeps only the refusal —
    /// which is why the face is lawful and the fiber is what a comparison needs.
    pub fn face(&self) -> Support {
        match self {
            Self::Supported(form) => Support::Supported(form.clone()),
            Self::Partial { .. } | Self::Unsupported { .. } => Support::Unsupported,
        }
    }
}

/// `H(P,Q) = Σ_a P(a) · S_Q(a)`, with the unsupported population retained.
///
/// This is the fiber; [`cross_entropy`] is its face.
pub fn cross_entropy_fiber(
    population: &BTreeMap<u64, BigUint>,
    code: &BTreeMap<u64, BigUint>,
) -> Result<CrossEntropyFiber, SurprisalError> {
    let total: BigUint = population.values().sum();
    if total.is_zero() {
        return Ok(CrossEntropyFiber::Unsupported {
            unsupported: Vec::new(),
        });
    }
    let mut form = SymbolicSurprisal::zero();
    let mut supported_mass = Rat::zero();
    let mut unsupported_mass = Rat::zero();
    let mut unsupported = Vec::new();
    for (event, count) in population {
        if count.is_zero() {
            continue;
        }
        let weight = Rat::new(BigInt::from(count.clone()), BigInt::from(total.clone()));
        match Support::read(code, *event)? {
            Support::Unsupported => {
                unsupported.push(*event);
                unsupported_mass += &weight;
            }
            Support::Supported(depth) => {
                form = form.plus(&depth.scaled(&weight));
                supported_mass += &weight;
            }
        }
    }
    if unsupported.is_empty() {
        return Ok(CrossEntropyFiber::Supported(form));
    }
    if supported_mass.is_zero() {
        return Ok(CrossEntropyFiber::Unsupported { unsupported });
    }
    Ok(CrossEntropyFiber::Partial {
        form_over_supported: form,
        supported_mass,
        unsupported,
        unsupported_mass,
    })
}

/// `H(P,Q) = Σ_a P(a) · S_Q(a)` — the depth incurred when one population is received through
/// another's standing code.
///
/// Returns `Unsupported` for the whole reading when any event `P` carries has no support in `Q`.
/// That is not a failure: it is the case the law says FOUNDs, and collapsing it to a large finite
/// number would be the smoothing constant this carrier refuses.
///
/// **This is the coarse face of [`cross_entropy_fiber`]**, kept because a weighted sum genuinely
/// has nowhere to put a refusal and callers who want that contract should have it. A caller who
/// needs to know *what* was unsupported, or what the supported majority cost, takes the fiber.
pub fn cross_entropy(
    population: &BTreeMap<u64, BigUint>,
    code: &BTreeMap<u64, BigUint>,
) -> Result<Support, SurprisalError> {
    Ok(cross_entropy_fiber(population, code)?.face())
}

#[cfg(test)]
mod fiber_tests {
    use super::*;

    fn population(pairs: &[(u64, u32)]) -> BTreeMap<u64, BigUint> {
        pairs
            .iter()
            .map(|(event, count)| (*event, BigUint::from(*count)))
            .collect()
    }

    /// The fiber returns the supported form AND the unsupported names, where the
    /// face returns only the refusal. Both are true of their own receiver.
    #[test]
    fn a_partial_reading_keeps_the_form_the_face_discards() {
        let held_out = population(&[(2, 3), (3, 1), (5, 4)]);
        let code = population(&[(2, 10), (3, 10)]);
        let fiber = cross_entropy_fiber(&held_out, &code).expect("exact");
        let CrossEntropyFiber::Partial {
            form_over_supported,
            supported_mass,
            unsupported,
            unsupported_mass,
        } = &fiber
        else {
            panic!("event 5 has no support, so the reading is partial: {fiber:?}");
        };
        assert_eq!(unsupported, &vec![5]);
        assert!(!form_over_supported.is_zero());
        assert_eq!(supported_mass + unsupported_mass, Rat::one());
        assert_eq!(
            unsupported_mass,
            &Rat::new(BigInt::from(4), BigInt::from(8))
        );
        // The face keeps only the refusal, which is why it is a face.
        assert_eq!(fiber.face(), Support::Unsupported);
        assert_eq!(
            cross_entropy(&held_out, &code).expect("exact"),
            Support::Unsupported
        );
    }

    /// The partial form is the SAME quantity restricted, never a renormalised
    /// one: dropping the unsupported events from the population must return a
    /// different form, because the weights would change.
    #[test]
    fn the_partial_form_is_weighted_by_the_whole_population_not_the_supported_part() {
        let held_out = population(&[(2, 3), (3, 1), (5, 4)]);
        let code = population(&[(2, 10), (3, 10)]);
        let CrossEntropyFiber::Partial {
            form_over_supported,
            ..
        } = cross_entropy_fiber(&held_out, &code).expect("exact")
        else {
            panic!("partial");
        };
        let restricted = population(&[(2, 3), (3, 1)]);
        let CrossEntropyFiber::Supported(renormalised) =
            cross_entropy_fiber(&restricted, &code).expect("exact")
        else {
            panic!("fully supported");
        };
        assert_ne!(
            form_over_supported, renormalised,
            "the partial form must carry the whole population's weights; if it equalled the \
             renormalised reading it would have silently redistributed the unsupported mass"
        );
    }

    /// Fully supported and fully unsupported both still return their own arm,
    /// so the three arms are a partition rather than two arms and a fallback.
    #[test]
    fn all_three_arms_are_reachable_on_declared_material() {
        let code = population(&[(2, 10), (3, 10)]);
        assert!(matches!(
            cross_entropy_fiber(&population(&[(2, 1), (3, 1)]), &code).expect("exact"),
            CrossEntropyFiber::Supported(_)
        ));
        assert!(matches!(
            cross_entropy_fiber(&population(&[(2, 1), (5, 1)]), &code).expect("exact"),
            CrossEntropyFiber::Partial { .. }
        ));
        assert!(matches!(
            cross_entropy_fiber(&population(&[(5, 1), (7, 1)]), &code).expect("exact"),
            CrossEntropyFiber::Unsupported { .. }
        ));
    }

    /// Founding an unsupported event moves the reading off the `Partial` arm,
    /// which is the law's own alternative to smoothing exercised end to end.
    #[test]
    fn founding_the_unsupported_population_closes_the_partial_arm() {
        let held_out = population(&[(2, 3), (5, 4)]);
        let mut code = population(&[(2, 10)]);
        let before = cross_entropy_fiber(&held_out, &code).expect("exact");
        assert_eq!(before.unsupported(), &[5]);
        for event in before.unsupported().to_vec() {
            Support::found(&mut code, event);
        }
        let after = cross_entropy_fiber(&held_out, &code).expect("exact");
        assert!(matches!(after, CrossEntropyFiber::Supported(_)));
        assert!(after.unsupported().is_empty());
        // And the founding moved every other event's depth, because the
        // denominator moved. A smoothing constant would not have.
        assert_ne!(before.form(), after.form());
    }

    /// The face is exactly the old contract, on every arm.
    #[test]
    fn the_face_reproduces_the_reading_the_coarse_entry_point_returns() {
        let code = population(&[(2, 10), (3, 10)]);
        for members in [
            vec![(2u64, 1u32), (3, 1)],
            vec![(2, 1), (5, 1)],
            vec![(5, 1), (7, 1)],
        ] {
            let held_out = population(&members);
            assert_eq!(
                cross_entropy_fiber(&held_out, &code).expect("exact").face(),
                cross_entropy(&held_out, &code).expect("exact")
            );
        }
    }
}

/// `H(P) = Σ_a P(a) · S_P(a)` — the population received through its own code.
pub fn entropy(population: &BTreeMap<u64, BigUint>) -> Result<Support, SurprisalError> {
    cross_entropy(population, population)
}

/// **Exact primality by trial division.** No probabilistic test, no table, no bound below which a
/// number is assumed prime: the argument this module's exactness rests on is about primes, so the
/// carrier admits a prime or refuses.
fn is_prime(value: u64) -> bool {
    if value < 2 {
        return false;
    }
    if value % 2 == 0 {
        return value == 2;
    }
    let mut divisor = 3u64;
    while divisor.saturating_mul(divisor) <= value {
        if value % divisor == 0 {
            return false;
        }
        divisor += 2;
    }
    true
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
    #[error("a section modulus needs a population; an empty one has no axis to be a moment about")]
    EmptyPopulation,
}

/// **The section modulus of a surprisal population: the second moment about its own mean, against
/// the extreme deviation, carried as an UNDIVIDED PAIR.**
///
/// Section modulus is `S = I/c` — a second moment about a gauge-fixed axis, over the distance to
/// the extreme fibre — and it says that strength lives in the *distribution* about the axis rather
/// than in the total. Two facts make it the right reading here rather than an analogy.
///
/// **The gauge is the same one.** A section's neutral axis is chosen so the first moment vanishes;
/// this reading takes the population's own mean, so the first moment vanishes by construction. The
/// exponentiated ratio family is invariant under an additive shift of every member, which is
/// exactly that gauge, and `the_section_modulus_is_unmoved_by_the_additive_gauge` holds it to it.
///
/// **The two ingredients are the two limits.** The second moment is the reading at unit
/// temperature; the extreme fibre is what the zero-temperature limit selects, which is the
/// governor `CLAUDE.md` bans. So the pair prices the banned collapse **without taking it**: a body
/// whose second moment vanishes against a nonzero extreme fibre has collapsed onto a single fibre
/// and carries no bending load.
///
/// The quotient is never formed. Both members are exact rational enclosures, and the horizon law
/// says a ratio crosses as a pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionModulus {
    /// `I` — the mean squared deviation from the population's own mean.
    pub second_moment: ExactInterval,
    /// `c` — an enclosure of the largest deviation from that mean.
    pub extreme_fibre: ExactInterval,
    pub members: usize,
}

fn squared_bounds(interval: &ExactInterval) -> (Rat, Rat) {
    let lower = interval.lower.clone();
    let upper = interval.upper.clone();
    let low_square = &lower * &lower;
    let high_square = &upper * &upper;
    let straddles = lower <= Rat::zero() && upper >= Rat::zero();
    let least = if straddles {
        Rat::zero()
    } else if low_square <= high_square {
        low_square.clone()
    } else {
        high_square.clone()
    };
    let greatest = if low_square >= high_square {
        low_square
    } else {
        high_square
    };
    (least, greatest)
}

/// Read the section modulus of a population of surprisal forms.
///
/// Everything is exact: the mean is a surprisal form, each deviation is a surprisal form, and the
/// numbers come from `SymbolicSurprisal::enclosure`, which returns an exact rational interval.
pub fn section_modulus(
    population: &BTreeMap<u64, SymbolicSurprisal>,
) -> Result<SectionModulus, SurprisalError> {
    let members = population.len();
    if members == 0 {
        return Err(SurprisalError::EmptyPopulation);
    }
    let extent = Rat::from_integer(BigInt::from(
        u64::try_from(members).map_err(|_| SurprisalError::EmptyPopulation)?,
    ));
    let mut mean = SymbolicSurprisal::zero();
    for form in population.values() {
        mean = mean.plus(form);
    }
    let mean = mean.scaled(&(Rat::one() / &extent));

    let mut moment_low = Rat::zero();
    let mut moment_high = Rat::zero();
    let mut fibre_low = Rat::zero();
    let mut fibre_high = Rat::zero();
    for form in population.values() {
        let deviation = form.minus(&mean).enclosure()?;
        let (least, greatest) = squared_bounds(&deviation);
        moment_low += least;
        moment_high += greatest;
        let magnitude_low = if deviation.lower <= Rat::zero() && deviation.upper >= Rat::zero() {
            Rat::zero()
        } else if deviation.lower > Rat::zero() {
            deviation.lower.clone()
        } else {
            -deviation.upper.clone()
        };
        let magnitude_high = {
            let low = if deviation.lower < Rat::zero() {
                -deviation.lower.clone()
            } else {
                deviation.lower.clone()
            };
            let high = if deviation.upper < Rat::zero() {
                -deviation.upper.clone()
            } else {
                deviation.upper.clone()
            };
            if low >= high { low } else { high }
        };
        if magnitude_low > fibre_low {
            fibre_low = magnitude_low;
        }
        if magnitude_high > fibre_high {
            fibre_high = magnitude_high;
        }
    }
    Ok(SectionModulus {
        second_moment: ExactInterval::new(moment_low / &extent, moment_high / &extent)
            .map_err(|_| SurprisalError::EmptyPopulation)?,
        extreme_fibre: ExactInterval::new(fibre_low, fibre_high)
            .map_err(|_| SurprisalError::EmptyPopulation)?,
        members,
    })
}

#[cfg(test)]
mod tests {

    fn modulus_population(terms: &[(u64, &[(u64, i64)])]) -> BTreeMap<u64, SymbolicSurprisal> {
        terms
            .iter()
            .map(|(name, factors)| {
                let mut form = SymbolicSurprisal::zero();
                for (prime, coefficient) in factors.iter() {
                    form = form.plus(
                        &SymbolicSurprisal::term(
                            *prime,
                            Rat::from_integer(BigInt::from(*coefficient)),
                        )
                        .expect("a prime term"),
                    );
                }
                (*name, form)
            })
            .collect()
    }

    /// **The gauge, and it is softmax's own.** Adding one constant form to every member shifts the
    /// mean by exactly that form, so every deviation is unmoved and BOTH readings must be
    /// bit-identical. If this ever moved, the reading would be measuring absolute position, which
    /// is the gauge direction and carries nothing.
    #[test]
    fn the_section_modulus_is_unmoved_by_the_additive_gauge() {
        let base = modulus_population(&[(1, &[(2, 1)]), (2, &[(3, 1)]), (3, &[(2, 3)])]);
        let shift =
            SymbolicSurprisal::term(5, Rat::from_integer(BigInt::from(7))).expect("a prime term");
        let shifted: BTreeMap<u64, SymbolicSurprisal> = base
            .iter()
            .map(|(name, form)| (*name, form.plus(&shift)))
            .collect();

        let before = section_modulus(&base).expect("a section modulus");
        let after = section_modulus(&shifted).expect("a section modulus");
        assert_eq!(before, after, "the additive gauge must move nothing");
    }

    /// **And it must move under a change that provably alters the spread**, or it is measuring
    /// nothing. Widening the population strictly increases both the second moment and the extreme
    /// fibre. Without this arm the gauge test above would pass on a reading that always returned
    /// zero.
    #[test]
    fn the_section_modulus_moves_when_the_spread_moves() {
        let narrow = modulus_population(&[(1, &[(2, 1)]), (2, &[(2, 2)]), (3, &[(2, 3)])]);
        let wide = modulus_population(&[(1, &[(2, 1)]), (2, &[(2, 2)]), (3, &[(2, 30)])]);

        let narrow = section_modulus(&narrow).expect("a section modulus");
        let wide = section_modulus(&wide).expect("a section modulus");
        assert!(
            wide.second_moment.lower > narrow.second_moment.upper,
            "a wider population must carry a strictly larger second moment"
        );
        assert!(
            wide.extreme_fibre.lower > narrow.extreme_fibre.upper,
            "a wider population must carry a strictly larger extreme fibre"
        );
    }

    /// **The collapse the ban forbids, priced without taking it.** A population whose members are
    /// all equal has zero deviation, so the second moment vanishes against a zero extreme fibre —
    /// it has collapsed onto a single fibre and carries no bending load. The quotient is never
    /// formed, so nothing divides by that zero.
    #[test]
    fn a_collapsed_population_carries_no_bending_load() {
        let flat = modulus_population(&[(1, &[(2, 4)]), (2, &[(2, 4)]), (3, &[(2, 4)])]);
        let reading = section_modulus(&flat).expect("a section modulus");
        assert!(reading.second_moment.upper.is_zero());
        assert!(reading.extreme_fibre.upper.is_zero());
        assert_eq!(reading.members, 3);
    }
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

#[cfg(test)]
mod primality_repair_tests {
    use super::*;

    /// **The defect this repair closes, asserted.** Before 2026-08-18 `add_term` tested `prime < 2`,
    /// so `term(4, …)` was admitted and the ℚ-linear-independence argument failed on an input the
    /// public constructor accepts: `2·log₂2 − 1·log₂4` is zero as a real number, and `is_zero()`
    /// returned `false`.
    #[test]
    fn a_composite_is_refused_by_name_so_the_zero_test_stays_exact() {
        assert_eq!(
            SymbolicSurprisal::term(4, Rat::one()),
            Err(SurprisalError::NotAPrime(4))
        );
        assert_eq!(
            SymbolicSurprisal::term(9, Rat::one()),
            Err(SurprisalError::NotAPrime(9))
        );
        assert_eq!(
            SymbolicSurprisal::term(1, Rat::one()),
            Err(SurprisalError::NotAPrime(1))
        );
        // And the primes it must still admit, including the two edges the loop can get wrong.
        for prime in [2u64, 3, 5, 7, 11, 13, 9_223_372_036_854_775_783] {
            assert!(
                SymbolicSurprisal::term(prime, Rat::one()).is_ok(),
                "{prime} is prime and must be admitted"
            );
        }
    }

    /// The exactness the refusal protects: two forms that are equal as real numbers are `is_zero`
    /// after subtraction, and no admitted pair can be equal-but-not-detected.
    #[test]
    fn the_zero_test_is_exact_on_every_admitted_form() {
        let two = SymbolicSurprisal::term(2, Rat::from_integer(2.into())).unwrap();
        let also_two = SymbolicSurprisal::term(2, Rat::from_integer(2.into())).unwrap();
        assert!(two.minus(&also_two).is_zero());
        let three = SymbolicSurprisal::term(3, Rat::one()).unwrap();
        assert!(!two.minus(&three).is_zero());
    }
}
