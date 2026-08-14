//! Hermite reduction: the coboundary move, and the invariant it may not touch.
//!
//! # Two species of move, and merging them destroys the invariant
//!
//! A table of integration methods carries **two different kinds of move** and
//! they are not interchangeable:
//!
//! - A **chart transition** — substitution — carries a Jacobian and changes the
//!   coordinates the integrand is written in.
//! - A **coboundary move** — integration by parts, and Hermite reduction —
//!   stays in one chart and changes the *representative* by an exact term.
//!
//! Hermite reduction writes `f = h' + g` with `h` rational. **`h'` is exact, so
//! it contributes nothing to the cohomology class, and that is precisely why
//! the method works**: the integral depends only on the class, so replacing `f`
//! by `g` cannot change the answer. Every complete algorithm in this area is
//! the same two phases — *reduce, then extract the class*.
//!
//! # The invariant, and why it is a gauge with a real orbit
//!
//! A rational function's derivative has **zero residue at every pole**. So for
//! every `α`,
//!
//! ```text
//! Res_α(f) = Res_α(h') + Res_α(g) = 0 + Res_α(g) = Res_α(g)
//! ```
//!
//! **The representative moves and the residues do not.** That is a gauge whose
//! orbit is non-trivial *by construction* rather than by hope — which is what a
//! declared schedule family must exhibit before agreement between its members
//! counts as evidence. This module therefore declares two reduction schedules
//! and **measures** that they visit different states.
//!
//! The orbit is larger than it looks. Descending one factor can bring it level
//! with another at the same multiplicity, after which the squarefree
//! decomposition returns their **product** and a single step descends both — so
//! **the two schedules take different numbers of steps on the same material**,
//! not merely the same steps in a different order.
//!
//! The class itself is returned without extracting a single root, by the
//! **Rothstein–Trager resultant**
//!
//! ```text
//! R(z) = Res_x( B(x) − z·D*'(x), D*(x) )
//! ```
//!
//! whose roots are exactly the residues of `g = B/D*`. It is a polynomial over
//! `ℚ`, computed by an exact Sylvester determinant, and **it is the object the
//! two schedules must agree on**. No root is isolated, no float appears, and
//! nothing is compared by magnitude.
//!
//! # The mechanism of one step
//!
//! With `D = U·V^m`, `V` squarefree of multiplicity `m ≥ 2` and `gcd(V, U) = 1`,
//! the polynomials `V'U` and `V` are coprime, so `B` and `C` exist with
//! `B·V'U + C·V = A` and `deg B < deg V`. Then
//!
//! ```text
//! ∫ A/(U V^m)  =  −B/((m−1)V^(m−1))  +  ∫ [C + B'U/(m−1)] / (U V^(m−1))
//! ```
//!
//! and the pole order has descended by one. Iterate until every multiplicity is
//! one. The identity is verified in this module by differentiating the produced
//! `h` back and comparing rational functions exactly.
//!
//! # Aperture
//!
//! `ℚ(x)` only. No algebraic or logarithmic extension, no field tower, and no
//! derivation on anything but a polynomial. This is the reduction phase; it
//! does not integrate, and the log part is returned as its Rothstein–Trager
//! polynomial rather than as a sum of logarithms.

use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::rational_polynomial::{
    resultant_in_eliminated_variable, BivariatePolynomial, ExactPolynomialError,
    RationalPolynomial,
};

/// `numerator / denominator` over `ℚ(x)`, kept as a pair and never divided.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalFunction {
    pub numerator: RationalPolynomial,
    pub denominator: RationalPolynomial,
}

impl RationalFunction {
    pub fn new(
        numerator: RationalPolynomial,
        denominator: RationalPolynomial,
    ) -> Result<Self, HermiteError> {
        if denominator.is_zero() {
            return Err(HermiteError::ZeroDenominator);
        }
        Ok(Self {
            numerator,
            denominator,
        })
    }

    pub fn zero() -> Self {
        Self {
            numerator: RationalPolynomial::zero(),
            denominator: RationalPolynomial::new(vec![Rat::one()]),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.numerator.is_zero()
    }

    /// `a/b + c/d = (ad + cb)/(bd)`, with no common-factor cancellation. The
    /// pair is the carrier; reducing it would be a choice this module is not
    /// asked to make.
    pub fn plus(&self, other: &Self) -> Self {
        Self {
            numerator: self
                .numerator
                .times(&other.denominator)
                .plus(&other.numerator.times(&self.denominator)),
            denominator: self.denominator.times(&other.denominator),
        }
    }

    /// The quotient rule, exactly.
    pub fn derivative(&self) -> Self {
        Self {
            numerator: self
                .numerator
                .derivative()
                .times(&self.denominator)
                .minus(&self.numerator.times(&self.denominator.derivative())),
            denominator: self.denominator.times(&self.denominator),
        }
    }

    /// Equality as rational functions: `a/b = c/d` iff `ad = cb`. Cross
    /// multiplication rather than canonical form, so no cancellation is
    /// required and no representative is privileged.
    pub fn equals(&self, other: &Self) -> bool {
        self.numerator.times(&other.denominator) == other.numerator.times(&self.denominator)
    }

    pub fn written(&self, variable: &str) -> String {
        format!(
            "({}) / ({})",
            self.numerator.written(variable),
            self.denominator.written(variable)
        )
    }
}

/// Which multiplicity to descend first when several are available.
///
/// The two members are a declared gauge. Nothing about the mathematics prefers
/// one, so if they visit the same states the family is vacuous and this module
/// says so rather than reporting their agreement as evidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ReductionSchedule {
    HighestMultiplicityFirst,
    LowestMultiplicityFirst,
}

impl ReductionSchedule {
    pub const DECLARED: [Self; 2] = [
        Self::HighestMultiplicityFirst,
        Self::LowestMultiplicityFirst,
    ];
}

/// One visited state, retained so the orbit can be measured rather than assumed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReductionState {
    /// The multiplicity descended at this step.
    pub descended: u32,
    /// The squarefree factor whose order dropped.
    pub factor: RationalPolynomial,
    /// The remaining integrand after the step.
    pub remaining: RationalFunction,
}

/// What the reduction returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HermiteReading {
    pub schema: String,
    pub schedule: ReductionSchedule,
    /// The polynomial part, split off before reduction. It integrates to a
    /// polynomial and takes no part in the class.
    pub polynomial_part: RationalPolynomial,
    /// `h`, the accumulated exact term. Its derivative is a coboundary.
    pub exact_part: RationalFunction,
    /// `g = B/D*`, with a squarefree denominator. The class lives here.
    pub remaining: RationalFunction,
    /// Every intermediate representative, in order.
    pub states: Vec<ReductionState>,
    /// `Res_x(B − z·D*', D*)`, whose roots are the residues of `g`. The
    /// invariant the schedules must agree on.
    pub residue_polynomial: RationalPolynomial,
    /// Whether `f = h' + g` was verified by differentiating `h` back.
    pub returns_under_differentiation: bool,
    /// Whether the remaining denominator is squarefree, which is the reduction's
    /// own termination condition.
    pub remaining_denominator_is_squarefree: bool,
}

impl HermiteReading {
    /// The residue polynomial with every factor of `z` divided out.
    ///
    /// **This is the strictly invariant object, and the difference is a real
    /// law rather than bookkeeping.** A coboundary `d/dx(1/V^k)` may introduce
    /// a pole the original integrand did not have — but the residue at any pole
    /// of a rational function's derivative is **zero**, so what it introduces is
    /// a root at `z = 0` and nothing else. Adding an exact term therefore
    /// multiplies the residue polynomial by a power of `z` and leaves every
    /// other root exactly where it was.
    ///
    /// So `residue_polynomial` is invariant when the pole set is fixed, and
    /// this is invariant unconditionally.
    pub fn nonzero_residue_polynomial(&self) -> RationalPolynomial {
        let coefficients = self.residue_polynomial.coefficients();
        let first = coefficients
            .iter()
            .position(|coefficient| !coefficient.is_zero())
            .unwrap_or(coefficients.len());
        RationalPolynomial::new(coefficients[first..].to_vec())
    }
}

/// Reduce `numerator / denominator` under a declared schedule.
pub fn reduce(
    numerator: &RationalPolynomial,
    denominator: &RationalPolynomial,
    schedule: ReductionSchedule,
) -> Result<HermiteReading, HermiteError> {
    if denominator.is_zero() {
        return Err(HermiteError::ZeroDenominator);
    }
    let source = RationalFunction::new(numerator.clone(), denominator.clone())?;

    // Split off the polynomial part once; it integrates to a polynomial and has
    // no poles, so it carries no residue and belongs to neither the exact part
    // nor the class.
    let (polynomial_part, mut current_numerator) = numerator.divided_by(denominator)?;
    let mut current_denominator = denominator.made_monic();
    // `divided_by` returned a remainder against the unnormalised denominator;
    // rescale so the pair matches the monic denominator being carried.
    if let Some(leading) = denominator.leading() {
        let inverse = Rat::one() / leading;
        current_numerator = current_numerator.scaled(&inverse);
    }

    let mut exact_part = RationalFunction::zero();
    let mut states = Vec::new();

    // The step bound is READ OFF THE MATERIAL, never authored.
    //
    // Let `N = sum_i (i - 1)·deg V_i` over the initial squarefree
    // decomposition — the total excess pole order counted at every root. One
    // step on a factor `V` drops the order of EVERY root of `V` by one, so `N`
    // decreases by `deg V >= 1` per step and the reduction terminates in at
    // most `N` steps.
    //
    // It is an UPPER bound and not the step count, because descending one
    // factor can bring it level with another at the same multiplicity, after
    // which the decomposition returns their product and a single step descends
    // both. The two declared schedules therefore take DIFFERENT numbers of
    // steps on the same material. Exceeding `N` is not a wall reached; it is
    // proof the descent is not descending.
    let derived_step_bound: usize = current_denominator
        .squarefree_decomposition()?
        .iter()
        .map(|(factor, multiplicity)| {
            (*multiplicity as usize).saturating_sub(1) * factor.degree().unwrap_or(0)
        })
        .sum();

    loop {
        let decomposition = current_denominator.squarefree_decomposition()?;
        let target = match schedule {
            ReductionSchedule::HighestMultiplicityFirst => decomposition
                .iter()
                .filter(|(_, multiplicity)| *multiplicity >= 2)
                .max_by_key(|(_, multiplicity)| *multiplicity),
            ReductionSchedule::LowestMultiplicityFirst => decomposition
                .iter()
                .filter(|(_, multiplicity)| *multiplicity >= 2)
                .min_by_key(|(_, multiplicity)| *multiplicity),
        };
        let Some((factor, multiplicity)) = target.cloned() else {
            break;
        };

        // D = U · V^m
        let mut power = RationalPolynomial::new(vec![Rat::one()]);
        for _ in 0..multiplicity {
            power = power.times(&factor);
        }
        let outside = current_denominator.divided_exactly_by(&power)?;

        // B·(V'U) + C·V = A, with deg B < deg V.
        let carrier = factor.derivative().times(&outside);
        let (common, cofactor, _) = carrier.extended_monic_gcd(&factor)?;
        if common.degree() != Some(0) {
            return Err(HermiteError::FactorNotCoprime);
        }
        let (_, b) = current_numerator.times(&cofactor).divided_by(&factor)?;
        let c = current_numerator
            .minus(&b.times(&carrier))
            .divided_exactly_by(&factor)?;

        let descent = Rat::from_integer((multiplicity - 1).into());
        let mut lowered = RationalPolynomial::new(vec![Rat::one()]);
        for _ in 0..(multiplicity - 1) {
            lowered = lowered.times(&factor);
        }

        // h += −B / ((m−1) V^{m−1})
        exact_part = exact_part.plus(&RationalFunction::new(
            b.negated(),
            lowered.scaled(&descent),
        )?);

        // A_new = C + B'·U/(m−1),  D_new = U·V^{m−1}
        let inverse_descent = Rat::one() / &descent;
        current_numerator = c.plus(&b.derivative().times(&outside).scaled(&inverse_descent));
        current_denominator = outside.times(&lowered);

        states.push(ReductionState {
            descended: multiplicity,
            factor: factor.clone(),
            remaining: RationalFunction::new(
                current_numerator.clone(),
                current_denominator.clone(),
            )?,
        });

        if states.len() > derived_step_bound {
            return Err(HermiteError::ReductionDidNotTerminate {
                states: states.len(),
                derived_bound: derived_step_bound,
            });
        }
    }

    let remaining = RationalFunction::new(current_numerator, current_denominator)?;
    let residue_polynomial = rothstein_trager(&remaining)?;

    // The second frame: f = polynomial_part + h' + g, checked as rational
    // functions by cross multiplication. Nothing here consults the reduction.
    let rebuilt = exact_part
        .derivative()
        .plus(&remaining)
        .plus(&RationalFunction::new(
            polynomial_part.clone(),
            RationalPolynomial::new(vec![Rat::one()]),
        )?);
    let returns_under_differentiation = rebuilt.equals(&source);

    let remaining_denominator_is_squarefree = remaining
        .denominator
        .squarefree_decomposition()?
        .iter()
        .all(|(_, multiplicity)| *multiplicity == 1);

    Ok(HermiteReading {
        schema: SCHEMA.to_owned(),
        schedule,
        polynomial_part,
        exact_part,
        remaining,
        states,
        residue_polynomial,
        returns_under_differentiation,
        remaining_denominator_is_squarefree,
    })
}

/// `Res_x(B − z·D', D)` — the polynomial whose roots are the residues.
///
/// No root is extracted. The residues are carried as the object that has them
/// as roots, which is exact, is a `ℚ`-polynomial, and can be compared for
/// equality without any isolation, magnitude, or ordering.
pub fn rothstein_trager(
    function: &RationalFunction,
) -> Result<RationalPolynomial, HermiteError> {
    let denominator = function.denominator.made_monic();
    let Some(degree) = denominator.degree() else {
        return Err(HermiteError::ZeroDenominator);
    };
    if degree == 0 {
        // No poles, so no residues; the empty root set is the constant 1.
        return Ok(RationalPolynomial::new(vec![Rat::one()]));
    }
    let derivative = denominator.derivative();
    // B(x) − z·D'(x), as a polynomial in x whose coefficients are linear in z.
    let left = BivariatePolynomial::new(
        (0..=degree)
            .map(|power| {
                RationalPolynomial::new(vec![
                    function.numerator.coefficient(power),
                    -derivative.coefficient(power),
                ])
            })
            .collect(),
    );
    // D(x), constant in z.
    let right = BivariatePolynomial::new(
        (0..=degree)
            .map(|power| RationalPolynomial::new(vec![denominator.coefficient(power)]))
            .collect(),
    );
    // A single pole leaves `B − z·D'` constant in x, and the Sylvester route
    // declares degree ≥ 1 in the eliminated variable as its aperture. The
    // resultant is elementary there — `Res_x(c, g) = c^(deg g)` — so it is
    // computed directly rather than by calling a carrier past its aperture.
    if left.degree() == Some(0) {
        let mut resultant = RationalPolynomial::new(vec![Rat::one()]);
        for _ in 0..degree {
            resultant = resultant.times(&left.coefficient(0));
        }
        return Ok(resultant.made_monic());
    }
    let (resultant, _) = resultant_in_eliminated_variable(&left, &right)?;
    Ok(resultant.made_monic())
}

const SCHEMA: &str = "holonic-engine.hermite-reduction.v1";

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum HermiteError {
    #[error("a rational function cannot have a zero denominator")]
    ZeroDenominator,
    #[error(
        "a squarefree factor and the cofactor of its own derivative shared a root, which \
         contradicts the squarefree decomposition that produced them"
    )]
    FactorNotCoprime,
    #[error(
        "the reduction visited {states} states against the {derived_bound} the initial squarefree \
         decomposition permits, so the pole order is not descending"
    )]
    ReductionDidNotTerminate {
        states: usize,
        derived_bound: usize,
    },
    #[error("the exact polynomial carrier refused: {0}")]
    Polynomial(#[from] ExactPolynomialError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use relational_geometry::exact::rat;

    fn polynomial(coefficients: &[i64]) -> RationalPolynomial {
        RationalPolynomial::new(coefficients.iter().map(|value| rat(*value, 1)).collect())
    }

    /// `∫ 1/x² = −1/x`, entirely exact: the class is empty.
    #[test]
    fn a_pure_double_pole_reduces_to_nothing_and_the_whole_integral_is_the_exact_part() {
        let reading = reduce(
            &polynomial(&[1]),
            &polynomial(&[0, 0, 1]),
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("the fixture reduces");
        assert!(reading.returns_under_differentiation);
        assert!(reading.remaining.is_zero(), "{}", reading.remaining.written("x"));
        assert_eq!(reading.states.len(), 1);
    }

    /// `1/(x²(x−1))` has a genuine log part and a genuine exact part.
    #[test]
    fn a_mixed_pole_splits_into_an_exact_part_and_a_squarefree_remainder() {
        let denominator = polynomial(&[0, 0, 1]).times(&polynomial(&[-1, 1]));
        let reading = reduce(
            &polynomial(&[1]),
            &denominator,
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("the fixture reduces");
        assert!(reading.returns_under_differentiation);
        assert!(reading.remaining_denominator_is_squarefree);
        assert!(!reading.remaining.is_zero());
        assert!(!reading.exact_part.is_zero());
    }

    /// The declared schedules must genuinely visit different states, or their
    /// agreement below is a check whose material cannot vary the property under
    /// test. This asserts the orbit is non-trivial BEFORE reading agreement as
    /// evidence.
    #[test]
    fn the_two_schedules_visit_different_states_so_the_gauge_is_not_vacuous() {
        // D = (x−1)² · (x+1)³ — two multiplicities available at the first step.
        let denominator = polynomial(&[-1, 1])
            .times(&polynomial(&[-1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]));
        let numerator = polynomial(&[1, 2, 3]);
        let highest = reduce(
            &numerator,
            &denominator,
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("reduces");
        let lowest = reduce(
            &numerator,
            &denominator,
            ReductionSchedule::LowestMultiplicityFirst,
        )
        .expect("reduces");
        let highest_first: Vec<u32> = highest.states.iter().map(|state| state.descended).collect();
        let lowest_first: Vec<u32> = lowest.states.iter().map(|state| state.descended).collect();
        assert_ne!(
            highest_first, lowest_first,
            "the two schedules descended the same multiplicities in the same order, so this \
             material cannot separate them and their agreement would be vacuous"
        );
    }

    /// The invariant. Different representatives, identical residues.
    #[test]
    fn the_representative_moves_and_the_residue_polynomial_does_not() {
        let denominator = polynomial(&[-1, 1])
            .times(&polynomial(&[-1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]));
        let numerator = polynomial(&[1, 2, 3]);
        let mut residues = Vec::new();
        let mut exact_parts = Vec::new();
        for schedule in ReductionSchedule::DECLARED {
            let reading = reduce(&numerator, &denominator, schedule).expect("reduces");
            assert!(
                reading.returns_under_differentiation,
                "schedule {schedule:?} did not differentiate back"
            );
            assert!(reading.remaining_denominator_is_squarefree);
            residues.push(reading.residue_polynomial.clone());
            exact_parts.push(reading.exact_part.clone());
        }
        assert_eq!(
            residues[0], residues[1],
            "the residues moved under a coboundary move, which would refute the whole mechanism"
        );
        assert!(
            exact_parts[0].equals(&exact_parts[1]),
            "the exact parts are equal as rational functions even though the paths differed"
        );
    }

    /// A coboundary added at a pole the integrand ALREADY has must leave the
    /// residue polynomial itself untouched.
    ///
    /// This is the falsifier stated positively. If a coboundary could move the
    /// class, the entire reduce-then-extract shape collapses.
    #[test]
    fn adding_an_exact_term_at_a_standing_pole_does_not_move_the_class() {
        let base = RationalFunction::new(polynomial(&[1]), polynomial(&[-1, 1]))
            .expect("a nonzero denominator");
        // d/dx( 1/(x−1) ) — exact, and it introduces no new pole location.
        let coboundary = RationalFunction::new(polynomial(&[1]), polynomial(&[-1, 1]))
            .expect("a nonzero denominator")
            .derivative();
        let moved = base.plus(&coboundary);

        let plain = reduce(
            &base.numerator,
            &base.denominator,
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("reduces");
        let shifted = reduce(
            &moved.numerator,
            &moved.denominator,
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("reduces");

        assert!(plain.returns_under_differentiation);
        assert!(shifted.returns_under_differentiation);
        assert!(
            !moved.equals(&base),
            "the fixture did not actually move the representative"
        );
        assert_eq!(
            plain.residue_polynomial, shifted.residue_polynomial,
            "an exact term moved the cohomology class"
        );
    }

    /// A coboundary at a NEW pole location adds exactly one thing: a residue of
    /// zero. The residue polynomial gains a factor of `z` and nothing else.
    ///
    /// This is the law that makes `nonzero_residue_polynomial` the
    /// unconditional invariant, and it was found by a test failing: adding
    /// `d/dx(1/x²)` to `1/(x−1)` took the polynomial `z − 1` to `z² − z`. The
    /// class did not move; the pole set grew, at residue zero.
    #[test]
    fn a_coboundary_at_a_new_pole_adds_a_zero_residue_and_nothing_else() {
        let base = RationalFunction::new(polynomial(&[1]), polynomial(&[-1, 1]))
            .expect("a nonzero denominator");
        let coboundary = RationalFunction::new(polynomial(&[1]), polynomial(&[0, 0, 1]))
            .expect("a nonzero denominator")
            .derivative();
        let moved = base.plus(&coboundary);

        let plain = reduce(
            &base.numerator,
            &base.denominator,
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("reduces");
        let shifted = reduce(
            &moved.numerator,
            &moved.denominator,
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("reduces");

        assert!(shifted.returns_under_differentiation);
        assert_ne!(
            plain.residue_polynomial, shifted.residue_polynomial,
            "the fixture did not actually introduce a new pole"
        );
        assert_eq!(
            plain.nonzero_residue_polynomial(),
            shifted.nonzero_residue_polynomial(),
            "an exact term moved a NONZERO residue, which no coboundary can do"
        );
        // And the change is exactly a factor of z: one new pole, residue zero.
        assert_eq!(
            shifted.residue_polynomial.degree().unwrap_or(0),
            plain.residue_polynomial.degree().unwrap_or(0) + 1
        );
    }

    /// The control: a change that is NOT a coboundary must move the class, or
    /// the invariant is insensitive and proves nothing.
    #[test]
    fn a_change_that_is_not_a_coboundary_does_move_the_class() {
        let plain = reduce(
            &polynomial(&[1]),
            &polynomial(&[-1, 1]),
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("reduces");
        let altered = reduce(
            &polynomial(&[2]),
            &polynomial(&[-1, 1]),
            ReductionSchedule::HighestMultiplicityFirst,
        )
        .expect("reduces");
        assert_ne!(
            plain.residue_polynomial, altered.residue_polynomial,
            "doubling the residue left the residue polynomial unmoved, so it is not measuring \
             the residues at all"
        );
    }

    #[test]
    fn the_squarefree_decomposition_carries_multiplicities_and_rebuilds_its_input() {
        // (x−1)²(x+1)³
        let source = polynomial(&[-1, 1])
            .times(&polynomial(&[-1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]));
        let decomposition = source
            .squarefree_decomposition()
            .expect("a nonzero polynomial");
        let mut rebuilt = polynomial(&[1]);
        for (factor, multiplicity) in &decomposition {
            for _ in 0..*multiplicity {
                rebuilt = rebuilt.times(factor);
            }
        }
        assert_eq!(rebuilt, source.made_monic());
        let mut multiplicities: Vec<u32> = decomposition
            .iter()
            .map(|(_, multiplicity)| *multiplicity)
            .collect();
        multiplicities.sort_unstable();
        assert_eq!(multiplicities, vec![2, 3]);
    }

    #[test]
    fn the_extended_gcd_returns_a_relation_that_holds_exactly() {
        let left = polynomial(&[-1, 0, 1]);
        let right = polynomial(&[1, 1, 1]);
        let (gcd, s, t) = left
            .extended_monic_gcd(&right)
            .expect("both are nonzero");
        assert_eq!(left.times(&s).plus(&right.times(&t)), gcd);
    }

    /// The step bound is read off the material, and the SCHEDULES TAKE
    /// DIFFERENT NUMBERS OF STEPS.
    ///
    /// This test was written asserting the count was exactly `N` and it failed
    /// at 2 against 3. The mechanism is worth keeping: descending `(x+1)³` to
    /// `(x+1)²` brings it level with `(x−1)²`, so the squarefree decomposition
    /// then returns their PRODUCT at multiplicity two and one step descends
    /// both. Descending `(x−1)²` first never creates that coincidence.
    ///
    /// So `N` is an upper bound, the step count is schedule-dependent, and the
    /// invariant is unmoved anyway — which is a sharper statement about the
    /// gauge than equal step counts would have been.
    #[test]
    fn the_schedules_take_different_step_counts_under_one_derived_bound() {
        let denominator = polynomial(&[-1, 1])
            .times(&polynomial(&[-1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]))
            .times(&polynomial(&[1, 1]));
        let bound: usize = denominator
            .squarefree_decomposition()
            .expect("nonzero")
            .iter()
            .map(|(factor, multiplicity)| {
                ((*multiplicity as usize) - 1) * factor.degree().unwrap_or(0)
            })
            .sum();
        assert_eq!(bound, 3);
        let counts: Vec<usize> = ReductionSchedule::DECLARED
            .iter()
            .map(|schedule| {
                reduce(&polynomial(&[1, 2, 3]), &denominator, *schedule)
                    .expect("reduces")
                    .states
                    .len()
            })
            .collect();
        assert!(
            counts.iter().all(|count| *count <= bound),
            "a schedule exceeded the bound the material derives: {counts:?} against {bound}"
        );
        assert_ne!(
            counts[0], counts[1],
            "the schedules took the same number of steps, so the merge this test exists to \
             exhibit did not occur on this material"
        );
    }

    #[test]
    fn a_zero_denominator_is_refused_rather_than_divided_by() {
        assert_eq!(
            reduce(
                &polynomial(&[1]),
                &RationalPolynomial::zero(),
                ReductionSchedule::HighestMultiplicityFirst
            ),
            Err(HermiteError::ZeroDenominator)
        );
    }
}
