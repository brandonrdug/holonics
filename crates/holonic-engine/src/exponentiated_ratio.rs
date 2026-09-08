//! The chart transition between the additive and multiplicative charts — and
//! softmax read as one, rather than as a statistic.
//!
//! ## The ontology, ratified 2026-08-14
//!
//! Brandon: *"softmax doesn't actually seem like a statistics function to me, it
//! seems like it's merely associated with statistics and got grouped in… you're
//! literally setting the invariant property to be that
//! `f(x) = softmax(x) = (chart of Λ) / (infinitesimal discrete paths/arcs that
//! compose Λ)`, because of the exponentiation… Like `C/r` in our modifications of
//! Einstein's equations. It's a rebasing thing, it's not a statistics thing."*
//!
//! That is the correct reading and it is what this module implements.
//!
//! **The exponential is the arc-to-whole map.** `e^x = lim_n (1 + x/n)^n` is
//! exactly *compose `n` infinitesimal arcs of size `x/n` multiplicatively and
//! return the whole*. So `x` lives in the **additive chart** — the infinitesimal,
//! the per-step, the tangent — and `e^x` lives in the **multiplicative chart** —
//! the accumulated, the whole, the group element. `exp` is the transition between
//! them, which is the Lie exponential `𝔤 → G` and nothing statistical whatever.
//!
//! **`C/r` is the same species.** For the circle the additive chart is the angle
//! and the multiplicative chart is `e^{iθ}` on the unit circle, and `2π` is the
//! additive extent that closes the multiplicative loop. **π and `e` are the two
//! constants of one chart transition** — π is how much extent closes it, `e` is
//! the base that makes it natural. Neither is a statistic either.
//!
//! ## Why the transition closes exactly here, which is not luck
//!
//! **`ℚ⁺` is the free abelian group on the primes.** That is the fundamental
//! theorem of arithmetic stated as a group law, and it says the multiplicative
//! chart of the positive rationals has the primes as its generators. `log₂` is
//! an isomorphism onto the additive subgroup with integer coefficients in `{log₂ p}`.
//! Its ℚ-linear span additionally admits rational powers of primes, which need
//! not be rational. ℚ-linear independence makes the symbolic zero test exact;
//! integral prime valuations are the rational-output domain of `exponentiate`.
//!
//! **[`SymbolicSurprisal`] supplies an additive symbolic chart containing
//! `log₂(ℚ⁺)`**; `−log p` is one receiver's reading. This module implements the
//! inverse transition on the integral prime-valuation subdomain:
//!
//! ```text
//!   additive chart          log₂           multiplicative chart
//!   Σ n_k · log₂ p_k     <---------->      Π p_k^{n_k}
//!   integral valuations     exp₂           an exact rational
//!
//!   a + b                                  exp₂(a) · exp₂(b)
//! ```
//!
//! **The homomorphism law is the whole content**, and `the_additive_chart_is_carried_to_the_multiplicative_one_by_a_homomorphism`
//! is its check. The algebraic chart law is independent of whether a receiver
//! later uses that construction statistically.
//!
//! A **fractional** coefficient does not fail — it lands in a finer chart, the
//! algebraic extension, which is what a root is. This module refuses it by name
//! rather than enclosing it, because an enclosure would be a magnitude standing
//! in for a chart it has not entered.
//!
//! ## Softmax, read in that chart
//!
//! ```text
//! softmax(x)_i = e^{x_i} / Σ_j e^{x_j}
//! ```
//!
//! It is invariant under `x → x + c`, so **the absolute position in the additive
//! chart is gauge and only the differences transport**. `p_i/p_j = e^{x_i − x_j}`
//! is the transition applied to a difference, which is the whole of its work. And
//! `Z` is a **declared null** that fixes the total at one; it enters no ratio and
//! it is the only division.
//!
//! So softmax factors as **a chart transition, then a gauge fixing.** Its
//! statistical use is one receiver's face of that. Normalization declares total
//! mass one without changing any pairwise ratio; it is a valid receiver chart,
//! not a forbidden absolute measure. **This module holds the ratio family and
//! supplies the normalized face when its receiver is declared.**
//!
//! ## Temperature changes the ratio chart
//!
//! `softmax(x/T)` sends every ratio to `ratio^{1/T}`, so **temperature is a root
//! extraction on the ratio** — a rebase of the winding, not a new quantity, and
//! the same operation that carries a fractional coefficient into the finer chart.
//! `T = 1` is the identity; `T → ∞` sends every ratio to one, which is no
//! distinction at all. As `T → 0+`, ratios tend to zero, one or infinity according
//! to the ordering of their scores. **The normalized face concentrates on the
//! maximizing set**, uniformly there for a finite population of fixed scores;
//! it selects one member only when the maximizer is unique.
//!
//! This owner retains finite positive reciprocal temperatures and every member's
//! ratio against every other. **It performs no winner selection.**
//!
//! ## What is returned
//!
//! Not a distribution. A **cocycle**: the family of exact pairwise ratios, which
//! satisfies `r(i,j)·r(j,k) = r(i,k)` identically and is therefore a genuine
//! ratio family rather than a table. A distribution is recoverable by **declaring
//! a null**, and the ratios do not move when the null does — a gauge orbit that
//! is exhibited rather than asserted.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::surprisal::SymbolicSurprisal;

/// `2^form`, exactly, when the form's coefficients are integers.
///
/// `2^{Σ q_k log₂ p_k} = Π p_k^{q_k}`, so an integral coefficient vector
/// exponentiates into ℚ and nothing is approximated. A fractional coefficient
/// leaves ℚ and is refused by name.
pub fn exponentiate(form: &SymbolicSurprisal) -> Result<Rat, RatioError> {
    let mut value = Rat::one();
    for (prime, coefficient) in form.terms() {
        if !coefficient.denom().is_one() {
            return Err(RatioError::FractionalCoefficient {
                prime: *prime,
                coefficient: coefficient.to_string(),
            });
        }
        let exponent = coefficient.numer().clone();
        let base = Rat::from_integer(BigInt::from(*prime));
        let magnitude = u32::try_from(exponent.magnitude().clone())
            .map_err(|_| RatioError::ExponentTooWide { prime: *prime })?;
        let raised = num_traits::pow(base, magnitude as usize);
        if exponent.is_negative() {
            value /= raised;
        } else {
            value *= raised;
        }
    }
    Ok(value)
}

/// `p_self / p_other`, exactly.
///
/// With `p = 2^{−S}` this is `2^{other − self}`: the *difference* of the two
/// forms, exponentiated. Note the order — a **larger** surprisal is a **smaller**
/// probability, so the form that subtracts is the one in the numerator's
/// exponent.
pub fn probability_ratio(
    numerator: &SymbolicSurprisal,
    denominator: &SymbolicSurprisal,
) -> Result<Rat, RatioError> {
    exponentiate(&denominator.minus(numerator))
}

/// Every member's exact ratio against every other, with nothing normalised.
///
/// This is the invariant half of softmax. It is a **cocycle** — see
/// [`RatioFamily::cocycle_holds`] — and it is complete: no member is dropped,
/// ranked, or crowned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RatioFamily {
    schema: String,
    /// The integer reciprocal temperature this family was rebased by, `1` for a family read
    /// directly off a surprisal population.
    ///
    /// **Added 2026-08-18.** Without it a rebased family was bit-indistinguishable from a warm one,
    /// so a reading could not say which frame it was taken in — the absolute-frame defect, one
    /// level in.
    rebased_by: u32,
    members: Vec<u64>,
    /// `(i, j) -> p_i / p_j`, for every ordered pair of distinct members.
    ratios: BTreeMap<(u64, u64), Rat>,
}

impl RatioFamily {
    /// Read the family off a population of surprisal forms.
    ///
    /// Members are carried by their own identifiers throughout; nothing here
    /// mints an index, and the return is keyed by the caller's names.
    pub fn read(population: &BTreeMap<u64, SymbolicSurprisal>) -> Result<Self, RatioError> {
        if population.len() < 2 {
            return Err(RatioError::FamilyTooSmall {
                members: population.len(),
            });
        }
        let members: Vec<u64> = population.keys().copied().collect();
        let mut ratios = BTreeMap::new();
        for left in &members {
            for right in &members {
                if left == right {
                    continue;
                }
                let ratio = probability_ratio(&population[left], &population[right])?;
                ratios.insert((*left, *right), ratio);
            }
        }
        Ok(Self {
            schema: SCHEMA.to_owned(),
            rebased_by: 1,
            members,
            ratios,
        })
    }

    /// The integer reciprocal temperature this family stands in. `1` is the frame it was read in.
    pub const fn rebased_by_reciprocal(&self) -> u32 {
        self.rebased_by
    }

    pub fn members(&self) -> &[u64] {
        &self.members
    }

    /// `p_left / p_right`, exact.
    pub fn ratio(&self, left: u64, right: u64) -> Option<&Rat> {
        if left == right {
            return None;
        }
        self.ratios.get(&(left, right))
    }

    /// **The cocycle law**, checked over every triple: `r(i,j)·r(j,k) = r(i,k)`.
    ///
    /// This is what makes the return a ratio *family* rather than a table of
    /// unrelated numbers, and it is the algebraic statement that the absolute
    /// values were gauge: any assignment of values consistent with these ratios
    /// differs from any other by one overall factor, and nothing else.
    pub fn cocycle_holds(&self) -> bool {
        for left in &self.members {
            for middle in &self.members {
                for right in &self.members {
                    if left == middle || middle == right || left == right {
                        continue;
                    }
                    let (Some(a), Some(b), Some(c)) = (
                        self.ratio(*left, *middle),
                        self.ratio(*middle, *right),
                        self.ratio(*left, *right),
                    ) else {
                        return false;
                    };
                    if a * b != *c {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// The distribution this family induces **once a null is declared**.
    ///
    /// Naming one member as the reference fixes the gauge, and the weights are
    /// then `w_m = r(m, reference)` normalised by their own total. That total is
    /// the partition function, and it appears **here**, in a function whose name
    /// says a null was declared, rather than silently inside the ratio.
    ///
    /// The returned weights sum to exactly one, over ℚ, with no float anywhere.
    /// **Which member is the null is a receiver's declaration**, and
    /// [`RatioFamily::null_orbit_is_trivial`] exhibits that the choice does not
    /// move the distribution — which is the statement that the normalisation
    /// carries no information the ratios did not already carry.
    pub fn normalised_against(&self, reference: u64) -> Result<BTreeMap<u64, Rat>, RatioError> {
        if !self.members.contains(&reference) {
            return Err(RatioError::UnknownMember(reference));
        }
        let mut weights: BTreeMap<u64, Rat> = BTreeMap::new();
        let mut total = Rat::zero();
        for member in &self.members {
            let weight = if *member == reference {
                Rat::one()
            } else {
                self.ratio(*member, reference)
                    .ok_or(RatioError::UnknownMember(*member))?
                    .clone()
            };
            total += &weight;
            weights.insert(*member, weight);
        }
        if total.is_zero() {
            return Err(RatioError::NullTotalVanishes);
        }
        for weight in weights.values_mut() {
            *weight /= &total;
        }
        Ok(weights)
    }

    /// Whether the declared null moves the distribution. It must not.
    ///
    /// A `true` here is the gauge statement: the normalisation is a frame choice
    /// and the ratios are the content. A `false` would mean the family is not a
    /// cocycle, and that is a defect rather than a finding.
    pub fn null_orbit_is_trivial(&self) -> Result<bool, RatioError> {
        let first = self.normalised_against(self.members[0])?;
        for member in &self.members[1..] {
            if self.normalised_against(*member)? != first {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Every ratio raised to the **integer power** `reciprocal_temperature`.
    ///
    /// Temperature is not a new quantity: `softmax(x/T)` sends `r` to `r^{1/T}`,
    /// so it is a rebase of the winding the ratio already carries, and this is
    /// that rebase for `T = 1/n` with `n` a positive integer.
    ///
    /// **CORRECTED 2026-08-18, twice.** The doc said this takes *"the **root**,
    /// taken only where it stays in ℚ"* and *"refuses where the root leaves ℚ"*.
    /// It takes an integer power; no root is taken, none can leave ℚ, and
    /// [`RatioError`] correctly carries no variant for it — the promised refusal
    /// was both unreachable and unimplemented. The **root** case, `T > 1`, is not
    /// implemented here at all and would need the algebraic carrier.
    ///
    /// And the doc said *"no path here reaches `T → 0`, which is argmax — the
    /// limit this module exists not to take."* That was backwards: the parameter
    /// **is** `1/T`, so `T → 0` is `reciprocal_temperature → ∞` and the parameter
    /// drives straight at it. What holds the ban is not this argument — it is
    /// that every ratio is returned and none is crowned, at any `n`. The limit is
    /// never *taken* because nothing here selects; the parameter can approach it
    /// and the return stays a complete family.
    ///
    /// **`reciprocal = 0` is refused.** That is `T → ∞`, where every ratio
    /// becomes one and no member is distinguishable from any other; it is a
    /// degenerate frame rather than a hot one.
    pub fn rebased_by(&self, reciprocal_temperature: u32) -> Result<Self, RatioError> {
        if reciprocal_temperature == 0 {
            return Err(RatioError::DegenerateTemperature);
        }
        let mut ratios = BTreeMap::new();
        for (pair, ratio) in &self.ratios {
            ratios.insert(
                *pair,
                num_traits::pow(ratio.clone(), reciprocal_temperature as usize),
            );
        }
        Ok(Self {
            schema: self.schema.clone(),
            // The rebases compose: `(r^m)^n = r^{mn}`, so the frame this family stands in is the
            // product, not the last exponent applied.
            rebased_by: self.rebased_by.saturating_mul(reciprocal_temperature),
            members: self.members.clone(),
            ratios,
        })
    }
}

const SCHEMA: &str = "holonic-engine.exponentiated-ratio-family.v1";

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum RatioError {
    #[error(
        "the coefficient {coefficient} on log2({prime}) is not an integer, so the exponential \
         leaves the rationals; an enclosure here would be a magnitude standing in for a ratio"
    )]
    FractionalCoefficient { prime: u64, coefficient: String },
    #[error("the exponent on log2({prime}) is wider than this carrier addresses")]
    ExponentTooWide { prime: u64 },
    #[error("a ratio family needs at least two members; {members} were supplied")]
    FamilyTooSmall { members: usize },
    #[error("the member {0} is not in this family")]
    UnknownMember(u64),
    #[error("the declared null's total vanishes, so no distribution is induced")]
    NullTotalVanishes,
    #[error(
        "a reciprocal temperature of zero sends every ratio to one, which is no distinction at all"
    )]
    DegenerateTemperature,
}

#[cfg(test)]
mod tests {
    use super::*;
    use relational_geometry::exact::rat;

    fn surprisal_of(numerator: i64, denominator: i64) -> SymbolicSurprisal {
        SymbolicSurprisal::of_probability(&rat(numerator, denominator)).expect("a probability")
    }

    /// **The law that says this is a chart transition and not a statistic.**
    ///
    /// The additive chart's addition is carried to the multiplicative chart's
    /// multiplication, exactly: `exp(a + b) = exp(a) · exp(b)`. That is the
    /// defining property of a group homomorphism, and no statistic has one.
    #[test]
    fn the_additive_chart_is_carried_to_the_multiplicative_one_by_a_homomorphism() {
        let a = surprisal_of(1, 3);
        let b = surprisal_of(2, 5);
        let sum = a.plus(&b);
        assert_eq!(
            exponentiate(&sum).expect("integral"),
            exponentiate(&a).expect("integral") * exponentiate(&b).expect("integral")
        );
        // And the identity maps to the identity, which is the rest of the law.
        assert_eq!(
            exponentiate(&SymbolicSurprisal::zero()).expect("integral"),
            Rat::one()
        );
        // The inverse direction is the same law read the other way: surprisal is
        // additive over a product, because log is.
        let product = rat(1, 3) * rat(2, 5);
        let of_product = SymbolicSurprisal::of_probability(&product).expect("a probability");
        assert_eq!(of_product, a.plus(&b));
    }

    /// The primes are the generators of the multiplicative chart, which is the
    /// fundamental theorem of arithmetic stated as a group law — and it is why
    /// the transition closes in the rationals at all.
    #[test]
    fn each_prime_is_one_generator_of_the_multiplicative_chart() {
        for prime in [2u64, 3, 5, 7, 11] {
            let one_step = SymbolicSurprisal::term(prime, Rat::one()).expect("a prime");
            assert_eq!(
                exponentiate(&one_step).expect("integral"),
                Rat::from_integer(BigInt::from(prime)),
                "one unit of the log2({prime}) axis is exactly the prime itself"
            );
        }
        // And a general rational is the product of its generators, with the
        // exponents read straight off the additive chart.
        let form = SymbolicSurprisal::of_probability(&rat(9, 14)).expect("a probability");
        let recovered = exponentiate(&form.scaled(&-Rat::one())).expect("integral");
        assert_eq!(recovered, rat(9, 14));
    }

    /// The round trip is exact: `2^{-S(p)} = p`, with no enclosure taken.
    #[test]
    fn exponentiating_a_surprisal_returns_the_probability_it_came_from() {
        for (numerator, denominator) in [(1, 2), (1, 3), (3, 4), (5, 12), (1, 1)] {
            let probability = rat(numerator, denominator);
            let form = SymbolicSurprisal::of_probability(&probability).expect("a probability");
            let recovered =
                exponentiate(&form.scaled(&-Rat::one())).expect("integral coefficients");
            assert_eq!(recovered, probability);
        }
    }

    /// The ratio is exact and is what softmax's numerator computes, without the
    /// division that follows it.
    #[test]
    fn the_ratio_of_two_probabilities_is_returned_exactly() {
        let half = surprisal_of(1, 2);
        let quarter = surprisal_of(1, 4);
        assert_eq!(
            probability_ratio(&half, &quarter).expect("exact"),
            rat(2, 1)
        );
        assert_eq!(
            probability_ratio(&quarter, &half).expect("exact"),
            rat(1, 2)
        );
        // And a ratio that is not an integer.
        let third = surprisal_of(1, 3);
        assert_eq!(probability_ratio(&half, &third).expect("exact"), rat(3, 2));
    }

    /// **The gauge statement.** Adding a constant to every surprisal — which is
    /// what `x → x + c` is on this side — moves no ratio at all.
    #[test]
    fn a_constant_added_to_every_form_moves_no_ratio() {
        let population: BTreeMap<u64, SymbolicSurprisal> = BTreeMap::from([
            (2, surprisal_of(1, 2)),
            (3, surprisal_of(1, 3)),
            (5, surprisal_of(1, 6)),
        ]);
        let shift = surprisal_of(1, 8);
        let shifted: BTreeMap<u64, SymbolicSurprisal> = population
            .iter()
            .map(|(member, form)| (*member, form.plus(&shift)))
            .collect();
        assert_ne!(population, shifted, "the fixture must actually shift");

        let before = RatioFamily::read(&population).expect("a family");
        let after = RatioFamily::read(&shifted).expect("a family");
        assert_eq!(before.ratios, after.ratios);
    }

    /// The family is a cocycle, which is what makes it a ratio family rather
    /// than a table.
    #[test]
    fn the_ratios_compose_exactly_over_every_triple() {
        let population: BTreeMap<u64, SymbolicSurprisal> = BTreeMap::from([
            (2, surprisal_of(1, 2)),
            (3, surprisal_of(1, 3)),
            (5, surprisal_of(1, 6)),
            (7, surprisal_of(5, 12)),
        ]);
        let family = RatioFamily::read(&population).expect("a family");
        assert!(family.cocycle_holds());
        // Spot-check one triple by hand so the law is not only self-reported.
        let a = family.ratio(2, 3).expect("a ratio").clone();
        let b = family.ratio(3, 5).expect("a ratio").clone();
        assert_eq!(&a * &b, *family.ratio(2, 5).expect("a ratio"));
    }

    /// **The declared null is a frame and carries no information.** Every choice
    /// of reference induces the identical distribution.
    #[test]
    fn the_declared_null_does_not_move_the_distribution_it_induces() {
        let population: BTreeMap<u64, SymbolicSurprisal> = BTreeMap::from([
            (2, surprisal_of(1, 2)),
            (3, surprisal_of(1, 3)),
            (5, surprisal_of(1, 6)),
        ]);
        let family = RatioFamily::read(&population).expect("a family");
        assert!(family.null_orbit_is_trivial().expect("a distribution"));

        let weights = family.normalised_against(2).expect("a distribution");
        let total: Rat = weights.values().cloned().sum();
        assert_eq!(total, Rat::one(), "the weights sum to exactly one, over Q");
        // The source population was already a distribution, so the induced one
        // must be it — recovered from ratios alone with no float anywhere.
        assert_eq!(weights[&2], rat(1, 2));
        assert_eq!(weights[&3], rat(1, 3));
        assert_eq!(weights[&5], rat(1, 6));
    }

    /// Temperature is a root on the ratio, and it moves the family. A rebase
    /// that moved nothing would make the coordinate decorative.
    #[test]
    fn temperature_rebases_the_winding_and_the_orbit_is_not_trivial() {
        let population: BTreeMap<u64, SymbolicSurprisal> =
            BTreeMap::from([(2, surprisal_of(1, 2)), (3, surprisal_of(1, 8))]);
        let family = RatioFamily::read(&population).expect("a family");
        let warm = family.ratio(2, 3).expect("a ratio").clone();
        assert_eq!(warm, rat(4, 1));

        let colder = family.rebased_by(2).expect("a positive reciprocal");
        assert_eq!(*colder.ratio(2, 3).expect("a ratio"), rat(16, 1));
        assert_ne!(colder.ratios, family.ratios);
        // A rebase is still a cocycle: the law survives the temperature.
        assert!(colder.cocycle_holds());
    }

    /// The degenerate frame is refused by name rather than returned as uniform.
    #[test]
    fn a_reciprocal_temperature_of_zero_is_refused() {
        let population: BTreeMap<u64, SymbolicSurprisal> =
            BTreeMap::from([(2, surprisal_of(1, 2)), (3, surprisal_of(1, 4))]);
        let family = RatioFamily::read(&population).expect("a family");
        assert_eq!(family.rebased_by(0), Err(RatioError::DegenerateTemperature));
    }

    /// A fractional coefficient leaves the rationals and is refused, rather than
    /// enclosed — an enclosure would be a magnitude standing in for a ratio.
    #[test]
    fn a_half_power_leaves_the_rationals_and_is_refused_by_name() {
        let root_two = SymbolicSurprisal::term(2, rat(1, 2)).expect("a prime");
        assert!(matches!(
            exponentiate(&root_two),
            Err(RatioError::FractionalCoefficient { prime: 2, .. })
        ));
    }

    /// Nothing here ranks. The family returns every ordered pair and commits to
    /// none, so there is no member a caller could not reach.
    #[test]
    fn every_ordered_pair_is_present_and_no_member_is_crowned() {
        let population: BTreeMap<u64, SymbolicSurprisal> = BTreeMap::from([
            (2, surprisal_of(1, 2)),
            (3, surprisal_of(1, 3)),
            (5, surprisal_of(1, 6)),
        ]);
        let family = RatioFamily::read(&population).expect("a family");
        assert_eq!(family.members().len(), 3);
        assert_eq!(family.ratios.len(), 3 * 2);
        for left in family.members() {
            for right in family.members() {
                assert_eq!(family.ratio(*left, *right).is_some(), left != right);
            }
        }
    }

    #[test]
    fn a_family_of_one_is_refused_because_a_ratio_needs_two() {
        let population: BTreeMap<u64, SymbolicSurprisal> =
            BTreeMap::from([(2, surprisal_of(1, 2))]);
        assert_eq!(
            RatioFamily::read(&population),
            Err(RatioError::FamilyTooSmall { members: 1 })
        );
    }
}

#[cfg(test)]
mod frame_tests {
    use super::*;
    use crate::surprisal::SymbolicSurprisal;

    fn population() -> BTreeMap<u64, SymbolicSurprisal> {
        let mut carried = BTreeMap::new();
        for (name, numerator) in [(0u64, 1i64), (1, 2), (2, 4)] {
            let probability = Rat::new(BigInt::from(numerator), BigInt::from(8i64));
            carried.insert(
                name,
                SymbolicSurprisal::of_probability(&probability).expect("a probability"),
            );
        }
        carried
    }

    /// **A rebased family must not be bit-indistinguishable from a warm one.** Before 2026-08-18 the
    /// reciprocal was applied and then forgotten, so a reading could not say which frame it stood
    /// in — the absolute-frame defect one level in.
    #[test]
    fn the_family_carries_the_frame_it_was_rebased_into() {
        let read = RatioFamily::read(&population()).expect("a family");
        assert_eq!(read.rebased_by_reciprocal(), 1);
        let cooled = read.rebased_by(3).expect("a positive reciprocal");
        assert_eq!(cooled.rebased_by_reciprocal(), 3);
        // The rebases compose, so the frame is the product rather than the last exponent.
        let twice = cooled.rebased_by(2).expect("a positive reciprocal");
        assert_eq!(twice.rebased_by_reciprocal(), 6);
        assert_ne!(read, cooled, "two frames must not be equal as values");
    }

    /// The ban is held by the return, not by the parameter: at any reciprocal the family is complete
    /// and no member is crowned. `T -> 0` is `reciprocal -> infinity`, which the parameter can
    /// approach; what it can never do is make the family select.
    #[test]
    fn every_member_survives_every_frame() {
        let read = RatioFamily::read(&population()).expect("a family");
        for reciprocal in [1u32, 2, 7, 64, u32::MAX] {
            let rebased = read.rebased_by(reciprocal).expect("a positive reciprocal");
            assert_eq!(rebased.members(), read.members());
            for left in read.members() {
                for right in read.members() {
                    if left != right {
                        assert!(rebased.ratio(*left, *right).is_some());
                    }
                }
            }
        }
        assert_eq!(read.rebased_by(0), Err(RatioError::DegenerateTemperature));
    }
}
