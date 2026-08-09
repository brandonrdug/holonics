//! Exact univariate and bivariate polynomials over `Q`, and the complete rational-root census
//! that decides whether a chart change can be taken inside `Q`.
//!
//! This module exists to carry one question: **a chart transition asks for a number; is that
//! number in the chart's own field?** The answer is never a tolerance and never a bool. It is a
//! census — the auxiliary polynomial whose root the transition needs, its exact distinct real root
//! count by Sturm, one isolating certificate per real root, and the *complete* population of its
//! rational roots.
//!
//! ## Why the rational census is complete, and why Sturm alone would not be
//!
//! Sturm's theorem counts and isolates **real** roots. It says nothing about rationality: a root
//! isolated in `(1, 2)` may be `3/2` or `sqrt(2)`. So a "Sturm certificate that a polynomial has no
//! rational root" is not a thing Sturm can issue, and this module does not pretend otherwise. What
//! it issues is a **pair**, and the pair is conclusive:
//!
//! ```text
//!   Sturm            -> the exact number of distinct real roots, with an isolating interval
//!                       and a sign-variation certificate for each
//!   Gauss + bisection -> the exact, COMPLETE set of rational roots
//! ```
//!
//! The second half is complete for a reason worth stating, because it is what removes any need to
//! factor a large integer. Let `A` be the primitive integer form of the polynomial, of degree `n`
//! with leading coefficient `c`. Then
//!
//! ```text
//!   B(z) = c^(n-1) * A(z/c)
//! ```
//!
//! is a **monic** integer polynomial, and `t` is a rational root of `A` exactly when `z = c*t` is
//! an *integer* root of `B` — because a rational root `p/q` of `A` in lowest terms has `q | c`
//! (Gauss), so `c*t` is an integer. Integer roots of `B` are then located by bisecting on
//! **half-integer endpoints**: a monic integer polynomial has no rational root that is not an
//! integer, so no half-integer is ever a root and every Sturm count is taken at a legal boundary.
//! An interval `(k - 1/2, k + 1/2)` contains exactly one integer, so the descent terminates with a
//! single exact evaluation per candidate. No divisor enumeration, no factoring, no bound on the
//! size of the constant term.
//!
//! ## What the bivariate half is for
//!
//! Killing two coefficients of a quintic at once leaves two simultaneous conditions in two
//! transform parameters. Eliminating one of them is a resultant, and a resultant of polynomials
//! whose coefficients are themselves polynomials is a Sylvester determinant over `Q[t]`. That is
//! computed here by fraction-free Bareiss elimination in the polynomial ring, with a typed refusal
//! when a division comes out inexact — the same discipline, and the same refusal species, as
//! [`crate::arithmetic_monodromy`]'s integer Bareiss determinant. Nothing is evaluated at a point
//! and nothing is approximated.
//!
//! No float, no tolerance, no threshold, no ranking. Every returned population is returned whole.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::{AlgebraicRoot, ExactInterval, IntegerPolynomial};

/// One exact polynomial over `Q` in a single variable.
///
/// Coefficients ascend in degree. The empty vector is the zero polynomial; a nonzero polynomial
/// never carries a zero leading coefficient, so `degree` is unambiguous.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct RationalPolynomial {
    coefficients: Vec<Rat>,
}

impl RationalPolynomial {
    pub fn new(mut coefficients: Vec<Rat>) -> Self {
        while coefficients.last().is_some_and(Zero::is_zero) {
            coefficients.pop();
        }
        Self { coefficients }
    }

    pub fn zero() -> Self {
        Self {
            coefficients: Vec::new(),
        }
    }

    pub fn one() -> Self {
        Self::constant(Rat::one())
    }

    pub fn constant(value: Rat) -> Self {
        Self::new(vec![value])
    }

    /// The polynomial `t`.
    pub fn variable() -> Self {
        Self::new(vec![Rat::zero(), Rat::one()])
    }

    pub fn from_integers(coefficients: &[BigInt]) -> Self {
        Self::new(
            coefficients
                .iter()
                .cloned()
                .map(Rat::from_integer)
                .collect(),
        )
    }

    pub fn from_integer_polynomial(polynomial: &IntegerPolynomial) -> Self {
        Self::from_integers(&polynomial.coefficients)
    }

    pub fn coefficients(&self) -> &[Rat] {
        &self.coefficients
    }

    pub fn is_zero(&self) -> bool {
        self.coefficients.is_empty()
    }

    /// `None` exactly for the zero polynomial: the zero polynomial has no degree, and saying it
    /// has degree zero is the kind of quiet lie that lets a degenerate elimination pass as a
    /// successful one.
    pub fn degree(&self) -> Option<usize> {
        self.coefficients.len().checked_sub(1)
    }

    pub fn leading(&self) -> Option<&Rat> {
        self.coefficients.last()
    }

    pub fn coefficient(&self, degree: usize) -> Rat {
        self.coefficients
            .get(degree)
            .cloned()
            .unwrap_or_else(Rat::zero)
    }

    pub fn is_monic(&self) -> bool {
        self.leading().is_some_and(|value| value.is_one())
    }

    pub fn evaluate(&self, point: &Rat) -> Rat {
        self.coefficients
            .iter()
            .rev()
            .fold(Rat::zero(), |value, coefficient| {
                value * point + coefficient
            })
    }

    pub fn plus(&self, other: &Self) -> Self {
        let extent = self.coefficients.len().max(other.coefficients.len());
        let mut coefficients = Vec::with_capacity(extent);
        for degree in 0..extent {
            coefficients.push(self.coefficient(degree) + other.coefficient(degree));
        }
        Self::new(coefficients)
    }

    pub fn minus(&self, other: &Self) -> Self {
        self.plus(&other.negated())
    }

    pub fn negated(&self) -> Self {
        Self {
            coefficients: self.coefficients.iter().map(|value| -value).collect(),
        }
    }

    pub fn scaled(&self, factor: &Rat) -> Self {
        Self::new(
            self.coefficients
                .iter()
                .map(|coefficient| coefficient * factor)
                .collect(),
        )
    }

    pub fn times(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut coefficients =
            vec![Rat::zero(); self.coefficients.len() + other.coefficients.len() - 1];
        for (left_degree, left) in self.coefficients.iter().enumerate() {
            if left.is_zero() {
                continue;
            }
            for (right_degree, right) in other.coefficients.iter().enumerate() {
                coefficients[left_degree + right_degree] += left * right;
            }
        }
        Self::new(coefficients)
    }

    /// `self` composed with `inner`: `self(inner(t))`, by Horner in the polynomial ring.
    pub fn composed_with(&self, inner: &Self) -> Self {
        self.coefficients
            .iter()
            .rev()
            .fold(Self::zero(), |value, coefficient| {
                value
                    .times(inner)
                    .plus(&Self::constant(coefficient.clone()))
            })
    }

    pub fn derivative(&self) -> Self {
        Self::new(
            self.coefficients
                .iter()
                .enumerate()
                .skip(1)
                .map(|(degree, coefficient)| coefficient * Rat::from_integer(BigInt::from(degree)))
                .collect(),
        )
    }

    /// Euclidean division over the field `Q`.
    pub fn divided_by(&self, divisor: &Self) -> Result<(Self, Self), ExactPolynomialError> {
        if divisor.is_zero() {
            return Err(ExactPolynomialError::DivisionByZeroPolynomial);
        }
        let divisor_degree = divisor.degree().expect("a nonzero divisor has a degree");
        let divisor_leading = divisor.leading().expect("a nonzero divisor leads").clone();
        let mut remainder = self.coefficients.clone();
        let mut quotient =
            vec![Rat::zero(); self.coefficients.len().saturating_sub(divisor_degree)];
        while remainder.len() > divisor_degree {
            let shift = remainder.len() - 1 - divisor_degree;
            let factor = remainder[remainder.len() - 1].clone() / &divisor_leading;
            if !factor.is_zero() {
                quotient[shift] = factor.clone();
                for (degree, coefficient) in divisor.coefficients.iter().enumerate() {
                    remainder[shift + degree] -= &factor * coefficient;
                }
            }
            remainder.pop();
            while remainder.last().is_some_and(Zero::is_zero) {
                remainder.pop();
            }
        }
        Ok((Self::new(quotient), Self::new(remainder)))
    }

    /// Exact division, refusing rather than truncating when the remainder is nonzero.
    ///
    /// Bareiss elimination over a polynomial ring is only fraction-free because every intermediate
    /// entry is a minor and therefore divisible. A nonzero remainder here means that invariant has
    /// been violated, so it is a refusal and never a rounded quotient.
    pub fn divided_exactly_by(&self, divisor: &Self) -> Result<Self, ExactPolynomialError> {
        let (quotient, remainder) = self.divided_by(divisor)?;
        if remainder.is_zero() {
            Ok(quotient)
        } else {
            Err(ExactPolynomialError::NonExactPolynomialDivision)
        }
    }

    /// The monic greatest common divisor, or the zero polynomial when both inputs are zero.
    pub fn monic_gcd(&self, other: &Self) -> Result<Self, ExactPolynomialError> {
        let mut left = self.clone();
        let mut right = other.clone();
        while !right.is_zero() {
            let (_, remainder) = left.divided_by(&right)?;
            left = right;
            right = remainder;
        }
        Ok(left.made_monic())
    }

    pub fn made_monic(&self) -> Self {
        match self.leading() {
            None => Self::zero(),
            Some(leading) => {
                let inverse = Rat::one() / leading;
                self.scaled(&inverse)
            }
        }
    }

    /// The squarefree part `p / gcd(p, p')`, which has the same distinct roots with multiplicity
    /// one.
    pub fn squarefree_part(&self) -> Result<Self, ExactPolynomialError> {
        if self.is_zero() {
            return Err(ExactPolynomialError::ZeroPolynomial);
        }
        let gcd = self.monic_gcd(&self.derivative())?;
        if gcd.is_zero() {
            return Ok(self.made_monic());
        }
        Ok(self.divided_exactly_by(&gcd)?.made_monic())
    }

    /// The primitive integer representative: denominators cleared, integer content removed, sign
    /// fixed so the leading coefficient is positive.
    ///
    /// This is the same normalisation `canonical_homogeneous` performs on a projective tuple, and
    /// for the same reason: the particular denominators an earlier chart calculation happened to
    /// introduce are arithmetic history, not content.
    pub fn primitive_integer_form(&self) -> Result<IntegerPolynomial, ExactPolynomialError> {
        if self.is_zero() {
            return Err(ExactPolynomialError::ZeroPolynomial);
        }
        let mut common_denominator = BigInt::one();
        for coefficient in &self.coefficients {
            let denominator = coefficient.denom().clone();
            let divisor = integer_gcd(&common_denominator, &denominator);
            common_denominator = common_denominator / divisor * denominator;
        }
        let mut integers = self
            .coefficients
            .iter()
            .map(|coefficient| coefficient.numer() * (&common_denominator / coefficient.denom()))
            .collect::<Vec<_>>();
        let content = integers
            .iter()
            .filter(|value| !value.is_zero())
            .map(|value| value.abs())
            .reduce(|left, right| integer_gcd(&left, &right))
            .unwrap_or_else(BigInt::one);
        if !content.is_zero() {
            for value in &mut integers {
                *value /= &content;
            }
        }
        if integers.last().is_some_and(Signed::is_negative) {
            for value in &mut integers {
                *value = -value.clone();
            }
        }
        IntegerPolynomial::new(integers).map_err(|_| ExactPolynomialError::ZeroPolynomial)
    }

    /// Presentation as `a*t^k + ...` with exact rational coefficients and no decimal expansion
    /// anywhere.
    pub fn written(&self, variable: &str) -> String {
        if self.is_zero() {
            return "0".to_owned();
        }
        let mut written = String::new();
        for (degree, coefficient) in self.coefficients.iter().enumerate().rev() {
            if coefficient.is_zero() {
                continue;
            }
            let negative = coefficient.is_negative();
            let size = coefficient.abs();
            let magnitude = if size.is_one() && degree != 0 {
                String::new()
            } else if size.denom().is_one() {
                format!("{}", size.numer())
            } else {
                format!("({}/{})", size.numer(), size.denom())
            };
            let power = match degree {
                0 => String::new(),
                1 => variable.to_owned(),
                _ => format!("{variable}^{degree}"),
            };
            let term = match (magnitude.as_str(), power.as_str()) {
                ("", "") => "1".to_owned(),
                ("", power) => power.to_owned(),
                (magnitude, "") => magnitude.to_owned(),
                (magnitude, power) => format!("{magnitude}*{power}"),
            };
            if written.is_empty() {
                written = if negative { format!("-{term}") } else { term };
            } else {
                written.push_str(if negative { " - " } else { " + " });
                written.push_str(&term);
            }
        }
        written
    }
}

fn integer_gcd(left: &BigInt, right: &BigInt) -> BigInt {
    let mut left = left.abs();
    let mut right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

/// One real root of the auxiliary polynomial, isolated with its Sturm sign-variation certificate,
/// together with the exact statement of whether it is rational.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CensusedRealRoot {
    pub isolating: AlgebraicRoot,
    /// Present exactly when this root is rational, and then it is the root itself.
    pub rational_value: Option<Rat>,
}

/// The complete return of asking a polynomial for its rational roots.
///
/// `rational_roots` is exhaustive, not a sample: see this module's head for why. The real-root
/// half is separate on purpose — a real root that is not rational is exactly the obstruction a
/// chart transition hits, and it is retained here with a certificate rather than discarded.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RationalRootCensus {
    pub source: RationalPolynomial,
    pub primitive: IntegerPolynomial,
    /// `B(z) = c^(n-1) A(z/c)`, monic over `Z`, whose integer roots are `c` times the rational
    /// roots of `A`.
    pub monic_companion: IntegerPolynomial,
    pub leading_coefficient: BigInt,
    /// Cauchy bound: every real root of the companion lies strictly inside.
    pub bounding_interval: ExactInterval,
    pub distinct_real_roots: u32,
    pub roots: Vec<CensusedRealRoot>,
    /// Every rational root of `source`, exactly and completely.
    pub rational_roots: Vec<Rat>,
    pub work: CensusWork,
}

impl RationalRootCensus {
    pub fn has_rational_root(&self) -> bool {
        !self.rational_roots.is_empty()
    }

    /// Real roots that are not rational: the retained half of the census.
    pub fn irrational_real_roots(&self) -> Vec<&CensusedRealRoot> {
        self.roots
            .iter()
            .filter(|root| root.rational_value.is_none())
            .collect()
    }
}

/// Exact work, in operations, never in elapsed time.
///
/// `CLAUDE.md` §8: a cost is measured in work, and a clock may measure but may never select.
/// Nothing in this module consults a clock.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CensusWork {
    pub sturm_counts: u64,
    pub bisection_steps: u64,
    pub exact_evaluations: u64,
}

/// Count and isolate the real roots and return every rational root, exactly.
pub fn rational_root_census(
    polynomial: &RationalPolynomial,
) -> Result<RationalRootCensus, ExactPolynomialError> {
    let primitive = polynomial.primitive_integer_form()?;
    let degree = primitive.degree();
    let leading = primitive
        .coefficients
        .last()
        .cloned()
        .ok_or(ExactPolynomialError::ZeroPolynomial)?;
    if degree == 0 {
        return Err(ExactPolynomialError::ConstantPolynomial);
    }
    let companion_coefficients = primitive
        .coefficients
        .iter()
        .enumerate()
        .map(|(index, coefficient)| {
            let exponent = u32::try_from(degree - 1 - index.min(degree - 1)).unwrap_or(0);
            if index == degree {
                BigInt::one()
            } else {
                coefficient * leading.pow(exponent)
            }
        })
        .collect::<Vec<_>>();
    let monic_companion = IntegerPolynomial::new(companion_coefficients)
        .map_err(|_| ExactPolynomialError::ZeroPolynomial)?;

    let bound = monic_companion
        .coefficients
        .iter()
        .take(degree)
        .map(|coefficient| coefficient.abs())
        .max()
        .unwrap_or_else(BigInt::one)
        + BigInt::one();
    let half = Rat::new(BigInt::one(), BigInt::from(2));
    let lower = -Rat::from_integer(bound.clone()) - &half;
    let upper = Rat::from_integer(bound) + &half;
    let bounding_interval = ExactInterval::new(lower.clone(), upper.clone())
        .map_err(|_| ExactPolynomialError::MalformedInterval)?;

    let mut work = CensusWork::default();
    let distinct_real_roots = sturm_count(&monic_companion, &lower, &upper, &mut work)?;

    let mut integer_roots = Vec::new();
    let mut leaves = Vec::new();
    descend_half_integer(
        &monic_companion,
        &lower,
        &upper,
        distinct_real_roots,
        &mut integer_roots,
        &mut leaves,
        &mut work,
    )?;

    let squarefree = RationalPolynomial::from_integer_polynomial(&monic_companion)
        .squarefree_part()?
        .primitive_integer_form()?;
    let mut isolated = Vec::new();
    for (leaf_lower, leaf_upper, count) in leaves {
        isolate_within(
            &squarefree,
            &leaf_lower,
            &leaf_upper,
            count,
            0,
            &mut isolated,
            &mut work,
        )?;
    }

    let leading_rational = Rat::from_integer(leading.clone());
    let mut rational_roots = integer_roots
        .iter()
        .map(|value| Rat::from_integer(value.clone()) / &leading_rational)
        .collect::<Vec<_>>();
    rational_roots.sort();
    rational_roots.dedup();

    let mut roots = Vec::new();
    for (lower, upper) in isolated {
        let isolating = AlgebraicRoot::isolate(
            monic_companion.clone(),
            ExactInterval::new(lower.clone(), upper.clone())
                .map_err(|_| ExactPolynomialError::MalformedInterval)?,
        )
        .map_err(|_| ExactPolynomialError::IsolationRefused)?;
        let rational_value = rational_roots
            .iter()
            .find(|candidate| {
                let scaled = *candidate * &leading_rational;
                lower < scaled && scaled < upper
            })
            .cloned();
        roots.push(CensusedRealRoot {
            isolating,
            rational_value,
        });
    }

    for root in &rational_roots {
        work.exact_evaluations += 1;
        if !polynomial.evaluate(root).is_zero() {
            return Err(ExactPolynomialError::CensusRootDoesNotVanish);
        }
    }

    Ok(RationalRootCensus {
        source: polynomial.clone(),
        primitive,
        monic_companion,
        leading_coefficient: leading,
        bounding_interval,
        distinct_real_roots,
        roots,
        rational_roots,
        work,
    })
}

fn sturm_count(
    polynomial: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
    work: &mut CensusWork,
) -> Result<u32, ExactPolynomialError> {
    work.sturm_counts += 1;
    let interval = ExactInterval::new(lower.clone(), upper.clone())
        .map_err(|_| ExactPolynomialError::MalformedInterval)?;
    polynomial
        .distinct_root_count(&interval)
        .map_err(|_| ExactPolynomialError::SturmRefused)
}

/// Bisect on half-integer endpoints until every surviving interval has width one, recording the
/// integer roots found and handing the leaves on for isolation.
///
/// A monic integer polynomial has no non-integer rational root, so a half-integer is never a root
/// and every Sturm count below is taken at a legal boundary. That is the whole reason this descent
/// needs no divisor enumeration.
#[allow(clippy::too_many_arguments)]
fn descend_half_integer(
    polynomial: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
    count: u32,
    integer_roots: &mut Vec<BigInt>,
    leaves: &mut Vec<(Rat, Rat, u32)>,
    work: &mut CensusWork,
) -> Result<(), ExactPolynomialError> {
    if count == 0 {
        return Ok(());
    }
    let width = upper - lower;
    if width <= Rat::one() {
        let candidate = (lower + upper) / Rat::from_integer(BigInt::from(2));
        work.exact_evaluations += 1;
        if candidate.is_integer() && polynomial.evaluate(&candidate).is_zero() {
            integer_roots.push(candidate.to_integer());
        }
        leaves.push((lower.clone(), upper.clone(), count));
        return Ok(());
    }
    work.bisection_steps += 1;
    let middle = Rat::from_integer(
        ((lower + upper) / Rat::from_integer(BigInt::from(2)))
            .floor()
            .to_integer(),
    ) + Rat::new(BigInt::one(), BigInt::from(2));
    if !(*lower < middle && middle < *upper) {
        return Err(ExactPolynomialError::BisectionStalled);
    }
    let left = sturm_count(polynomial, lower, &middle, work)?;
    let right = sturm_count(polynomial, &middle, upper, work)?;
    if left + right != count {
        return Err(ExactPolynomialError::SturmCountsDisagree);
    }
    descend_half_integer(
        polynomial,
        lower,
        &middle,
        left,
        integer_roots,
        leaves,
        work,
    )?;
    descend_half_integer(
        polynomial,
        &middle,
        upper,
        right,
        integer_roots,
        leaves,
        work,
    )
}

const MAXIMUM_ISOLATION_DEPTH: u32 = 200;

/// Split a leaf until each surviving interval holds exactly one root of the squarefree part.
fn isolate_within(
    squarefree: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
    count: u32,
    depth: u32,
    isolated: &mut Vec<(Rat, Rat)>,
    work: &mut CensusWork,
) -> Result<(), ExactPolynomialError> {
    if count == 0 {
        return Ok(());
    }
    if count == 1 {
        isolated.push((lower.clone(), upper.clone()));
        return Ok(());
    }
    if depth >= MAXIMUM_ISOLATION_DEPTH {
        return Err(ExactPolynomialError::IsolationDepthExhausted);
    }
    let middle = interior_non_root(squarefree, lower, upper, work)?;
    work.bisection_steps += 1;
    let left = sturm_count(squarefree, lower, &middle, work)?;
    let right = sturm_count(squarefree, &middle, upper, work)?;
    if left + right != count {
        return Err(ExactPolynomialError::SturmCountsDisagree);
    }
    isolate_within(squarefree, lower, &middle, left, depth + 1, isolated, work)?;
    isolate_within(squarefree, &middle, upper, right, depth + 1, isolated, work)
}

/// A point strictly inside `(lower, upper)` at which the polynomial does not vanish.
///
/// A squarefree polynomial of degree `d` has at most `d` roots, so at most `d + 1` declared
/// candidates are ever needed and the search is bounded rather than hopeful.
fn interior_non_root(
    squarefree: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
    work: &mut CensusWork,
) -> Result<Rat, ExactPolynomialError> {
    let width = upper - lower;
    let candidates: [(i64, i64); 13] = [
        (1, 2),
        (1, 3),
        (2, 3),
        (1, 4),
        (3, 4),
        (1, 5),
        (2, 5),
        (3, 5),
        (4, 5),
        (1, 6),
        (5, 6),
        (1, 7),
        (2, 7),
    ];
    for (numerator, denominator) in candidates {
        let point = lower + &width * Rat::new(BigInt::from(numerator), BigInt::from(denominator));
        work.exact_evaluations += 1;
        if !squarefree.evaluate(&point).is_zero() {
            return Ok(point);
        }
    }
    Err(ExactPolynomialError::NoInteriorNonRoot)
}

/// One polynomial in two variables, presented as a polynomial in the variable that will be
/// eliminated whose coefficients live in `Q[t]`.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct BivariatePolynomial {
    coefficients: Vec<RationalPolynomial>,
}

impl BivariatePolynomial {
    pub fn new(mut coefficients: Vec<RationalPolynomial>) -> Self {
        while coefficients.last().is_some_and(RationalPolynomial::is_zero) {
            coefficients.pop();
        }
        Self { coefficients }
    }

    pub fn zero() -> Self {
        Self {
            coefficients: Vec::new(),
        }
    }

    /// A constant in the eliminated variable, carrying a polynomial in the retained one.
    pub fn retained(polynomial: RationalPolynomial) -> Self {
        Self::new(vec![polynomial])
    }

    /// The eliminated variable itself.
    pub fn eliminated_variable() -> Self {
        Self::new(vec![RationalPolynomial::zero(), RationalPolynomial::one()])
    }

    pub fn coefficients(&self) -> &[RationalPolynomial] {
        &self.coefficients
    }

    pub fn is_zero(&self) -> bool {
        self.coefficients.is_empty()
    }

    pub fn degree(&self) -> Option<usize> {
        self.coefficients.len().checked_sub(1)
    }

    pub fn coefficient(&self, degree: usize) -> RationalPolynomial {
        self.coefficients
            .get(degree)
            .cloned()
            .unwrap_or_else(RationalPolynomial::zero)
    }

    pub fn plus(&self, other: &Self) -> Self {
        let extent = self.coefficients.len().max(other.coefficients.len());
        Self::new(
            (0..extent)
                .map(|degree| self.coefficient(degree).plus(&other.coefficient(degree)))
                .collect(),
        )
    }

    pub fn times(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        let mut coefficients = vec![
            RationalPolynomial::zero();
            self.coefficients.len() + other.coefficients.len() - 1
        ];
        for (left_degree, left) in self.coefficients.iter().enumerate() {
            if left.is_zero() {
                continue;
            }
            for (right_degree, right) in other.coefficients.iter().enumerate() {
                coefficients[left_degree + right_degree] =
                    coefficients[left_degree + right_degree].plus(&left.times(right));
            }
        }
        Self::new(coefficients)
    }

    pub fn scaled_by_rational(&self, factor: &Rat) -> Self {
        Self::new(
            self.coefficients
                .iter()
                .map(|coefficient| coefficient.scaled(factor))
                .collect(),
        )
    }

    /// Substitute an exact rational for the retained variable, leaving a univariate polynomial in
    /// the eliminated one.
    pub fn with_retained(&self, point: &Rat) -> RationalPolynomial {
        RationalPolynomial::new(
            self.coefficients
                .iter()
                .map(|coefficient| coefficient.evaluate(point))
                .collect(),
        )
    }
}

/// Fraction-free Sylvester resultant in the eliminated variable, over the ring `Q[t]`.
///
/// The refusal species is deliberately the same one [`crate::arithmetic_monodromy`] uses for its
/// integer Bareiss determinant: a division that does not come out exactly means the minor
/// invariant has failed, and that is reported rather than rounded.
pub fn resultant_in_eliminated_variable(
    left: &BivariatePolynomial,
    right: &BivariatePolynomial,
) -> Result<(RationalPolynomial, ResultantWork), ExactPolynomialError> {
    let left_degree = left.degree().ok_or(ExactPolynomialError::ZeroPolynomial)?;
    let right_degree = right.degree().ok_or(ExactPolynomialError::ZeroPolynomial)?;
    if left_degree == 0 || right_degree == 0 {
        return Err(ExactPolynomialError::ResultantDegreeTooLow);
    }
    let size = left_degree + right_degree;
    let mut sylvester = vec![vec![RationalPolynomial::zero(); size]; size];
    for row in 0..right_degree {
        for offset in 0..=left_degree {
            sylvester[row][row + offset] = left.coefficient(left_degree - offset);
        }
    }
    for row in 0..left_degree {
        for offset in 0..=right_degree {
            sylvester[right_degree + row][row + offset] = right.coefficient(right_degree - offset);
        }
    }
    bareiss_polynomial_determinant(sylvester)
}

/// Exact work of the polynomial Bareiss elimination, in operations.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ResultantWork {
    pub matrix_extent: u64,
    pub exact_divisions: u64,
    pub polynomial_multiplications: u64,
    pub row_swaps: u64,
}

fn bareiss_polynomial_determinant(
    mut matrix: Vec<Vec<RationalPolynomial>>,
) -> Result<(RationalPolynomial, ResultantWork), ExactPolynomialError> {
    let size = matrix.len();
    let mut work = ResultantWork {
        matrix_extent: size as u64,
        ..ResultantWork::default()
    };
    if size == 0 || matrix.iter().any(|row| row.len() != size) {
        return Err(ExactPolynomialError::MalformedDeterminant);
    }
    if size == 1 {
        return Ok((matrix[0][0].clone(), work));
    }
    let mut previous_pivot = RationalPolynomial::one();
    let mut sign = Rat::one();
    for pivot_index in 0..size - 1 {
        let pivot_row = (pivot_index..size).find(|row| !matrix[*row][pivot_index].is_zero());
        let Some(pivot_row) = pivot_row else {
            return Ok((RationalPolynomial::zero(), work));
        };
        if pivot_row != pivot_index {
            matrix.swap(pivot_row, pivot_index);
            work.row_swaps += 1;
            sign = -sign;
        }
        let pivot = matrix[pivot_index][pivot_index].clone();
        for row in pivot_index + 1..size {
            for column in pivot_index + 1..size {
                let numerator = matrix[row][column]
                    .times(&pivot)
                    .minus(&matrix[row][pivot_index].times(&matrix[pivot_index][column]));
                work.polynomial_multiplications += 2;
                work.exact_divisions += 1;
                matrix[row][column] = numerator.divided_exactly_by(&previous_pivot)?;
            }
            matrix[row][pivot_index] = RationalPolynomial::zero();
        }
        previous_pivot = pivot;
    }
    Ok((matrix[size - 1][size - 1].scaled(&sign), work))
}

/// Power sums `s_k = sum of the k-th powers of the roots` of a monic polynomial, by the Newton
/// identities, over `Q` and with no root ever computed.
///
/// `s_0` is the degree. For `k <= n` the identity is
/// `s_k = sum_{i<k} (-1)^(i-1) e_i s_{k-i} + (-1)^(k-1) k e_k`, and for `k > n` the trailing term
/// drops out.
pub fn newton_power_sums(
    monic: &RationalPolynomial,
    highest: usize,
) -> Result<Vec<Rat>, ExactPolynomialError> {
    if !monic.is_monic() {
        return Err(ExactPolynomialError::NotMonic);
    }
    let degree = monic.degree().ok_or(ExactPolynomialError::ZeroPolynomial)?;
    if degree == 0 {
        return Err(ExactPolynomialError::ConstantPolynomial);
    }
    // e_k = (-1)^k * (coefficient of x^(n-k))
    let elementary = (1..=degree)
        .map(|k| {
            let coefficient = monic.coefficient(degree - k);
            if k % 2 == 0 {
                coefficient
            } else {
                -coefficient
            }
        })
        .collect::<Vec<_>>();
    let mut sums = vec![Rat::from_integer(BigInt::from(degree))];
    for k in 1..=highest {
        let mut value = Rat::zero();
        for i in 1..k.min(degree + 1) {
            let term = &elementary[i - 1] * &sums[k - i];
            if i % 2 == 1 {
                value += term;
            } else {
                value -= term;
            }
        }
        if k <= degree {
            let term = Rat::from_integer(BigInt::from(k)) * &elementary[k - 1];
            if k % 2 == 1 {
                value += term;
            } else {
                value -= term;
            }
        }
        sums.push(value);
    }
    Ok(sums)
}

/// The monic polynomial whose roots are the values `y_i`, recovered from their power sums by the
/// Newton identities run backwards.
pub fn monic_from_power_sums(
    power_sums: &[Rat],
    degree: usize,
) -> Result<RationalPolynomial, ExactPolynomialError> {
    if power_sums.len() <= degree {
        return Err(ExactPolynomialError::InsufficientPowerSums);
    }
    let mut elementary = vec![Rat::one()];
    for k in 1..=degree {
        let mut value = Rat::zero();
        for i in 1..=k {
            let term = &elementary[k - i] * &power_sums[i];
            if i % 2 == 1 {
                value += term;
            } else {
                value -= term;
            }
        }
        elementary.push(value / Rat::from_integer(BigInt::from(k)));
    }
    let mut coefficients = vec![Rat::zero(); degree + 1];
    for k in 0..=degree {
        let sign = if k % 2 == 0 { Rat::one() } else { -Rat::one() };
        coefficients[degree - k] = sign * &elementary[k];
    }
    Ok(RationalPolynomial::new(coefficients))
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactPolynomialError {
    #[error("the zero polynomial has no degree, no primitive form, and no root census")]
    ZeroPolynomial,
    #[error("a constant polynomial has no roots to census")]
    ConstantPolynomial,
    #[error("division by the zero polynomial")]
    DivisionByZeroPolynomial,
    #[error("a Bareiss polynomial division was not exact")]
    NonExactPolynomialDivision,
    #[error("the Sylvester matrix was malformed")]
    MalformedDeterminant,
    #[error("a resultant needs both arguments to have positive degree in the eliminated variable")]
    ResultantDegreeTooLow,
    #[error("the polynomial is not monic")]
    NotMonic,
    #[error("too few power sums were supplied to rebuild the elementary symmetric functions")]
    InsufficientPowerSums,
    #[error("an interval was malformed")]
    MalformedInterval,
    #[error("the Sturm count refused at this interval")]
    SturmRefused,
    #[error("Sturm counts on the two halves did not sum to the count on the whole")]
    SturmCountsDisagree,
    #[error("bisection produced a midpoint outside its own interval")]
    BisectionStalled,
    #[error("no declared interior candidate avoided the root set")]
    NoInteriorNonRoot,
    #[error("root isolation exhausted its declared depth")]
    IsolationDepthExhausted,
    #[error("root isolation was refused by the Sturm certificate")]
    IsolationRefused,
    #[error("a censused rational root did not vanish on the source polynomial")]
    CensusRootDoesNotVanish,
}

#[cfg(test)]
mod tests {
    use relational_geometry::{integer, rat};

    use super::*;

    fn polynomial(values: &[i64]) -> RationalPolynomial {
        RationalPolynomial::new(values.iter().map(|value| integer(*value)).collect())
    }

    #[test]
    fn exact_division_refuses_rather_than_truncating() {
        let dividend = polynomial(&[1, 0, 1]);
        let divisor = polynomial(&[1, 1]);
        assert_eq!(
            dividend.divided_exactly_by(&divisor),
            Err(ExactPolynomialError::NonExactPolynomialDivision)
        );
        let square = divisor.times(&divisor);
        assert_eq!(square.divided_exactly_by(&divisor).unwrap(), divisor);
    }

    #[test]
    fn the_rational_census_is_complete_where_a_divisor_search_would_have_to_factor() {
        // 6x^2 - 5x + 1 = (3x - 1)(2x - 1): both roots rational, neither an integer, and the
        // leading coefficient is not one. This is the case a naive "integer roots" search misses.
        let census = rational_root_census(&polynomial(&[1, -5, 6])).unwrap();
        assert_eq!(census.rational_roots, vec![rat(1, 3), rat(1, 2)]);
        assert_eq!(census.distinct_real_roots, 2);
    }

    #[test]
    fn a_real_root_that_is_not_rational_is_retained_with_its_certificate() {
        // x^2 - 2 has two real roots and no rational root. The refusal is a population of two
        // certified irrationals, not a bool.
        let census = rational_root_census(&polynomial(&[-2, 0, 1])).unwrap();
        assert!(census.rational_roots.is_empty());
        assert_eq!(census.distinct_real_roots, 2);
        assert_eq!(census.irrational_real_roots().len(), 2);
        for root in census.irrational_real_roots() {
            assert_eq!(
                root.isolating.certificate.variations_at_lower
                    - root.isolating.certificate.variations_at_upper,
                1
            );
        }
    }

    #[test]
    fn a_polynomial_with_no_real_root_returns_an_empty_population_not_an_error() {
        let census = rational_root_census(&polynomial(&[1, 0, 1])).unwrap();
        assert_eq!(census.distinct_real_roots, 0);
        assert!(census.rational_roots.is_empty());
        assert!(census.roots.is_empty());
    }

    #[test]
    fn a_large_constant_term_costs_a_logarithm_and_never_a_factorisation() {
        // x^2 - 1000003x + 1000002 = (x - 1)(x - 1000002). The constant term is the product of two
        // primes; a divisor enumeration would have to factor it. The bisection does not.
        let census = rational_root_census(&polynomial(&[1_000_002, -1_000_003, 1])).unwrap();
        assert_eq!(census.rational_roots, vec![integer(1), integer(1_000_002)]);
        assert!(
            census.work.bisection_steps < 64,
            "bisection is logarithmic in the bound, not linear: {} steps",
            census.work.bisection_steps
        );
    }

    #[test]
    fn newton_identities_round_trip_through_the_power_sums() {
        // (x-1)(x-2)(x-3)(x-4)(x-5) has power sums 5, 15, 55, 225, 979, 4425.
        let roots = [1_i64, 2, 3, 4, 5];
        let quintic = roots.iter().fold(RationalPolynomial::one(), |value, root| {
            value.times(&polynomial(&[-root, 1]))
        });
        let sums = newton_power_sums(&quintic, 5).unwrap();
        assert_eq!(
            sums,
            vec![
                integer(5),
                integer(15),
                integer(55),
                integer(225),
                integer(979),
                integer(4425)
            ]
        );
        assert_eq!(monic_from_power_sums(&sums, 5).unwrap(), quintic);
    }

    #[test]
    fn power_sums_run_past_the_degree_by_the_linear_recurrence() {
        // x^2 - x - 1: the power sums are the Lucas numbers 2, 1, 3, 4, 7, 11, 18.
        let sums = newton_power_sums(&polynomial(&[-1, -1, 1]), 6).unwrap();
        assert_eq!(
            sums,
            vec![
                integer(2),
                integer(1),
                integer(3),
                integer(4),
                integer(7),
                integer(11),
                integer(18)
            ]
        );
    }

    #[test]
    fn the_polynomial_resultant_eliminates_a_variable_exactly() {
        // Res_v(v - t, v^2 - 2) = t^2 - 2: substituting the first into the second.
        let first = BivariatePolynomial::new(vec![
            RationalPolynomial::new(vec![Rat::zero(), -Rat::one()]),
            RationalPolynomial::one(),
        ]);
        let second = BivariatePolynomial::new(vec![
            RationalPolynomial::constant(integer(-2)),
            RationalPolynomial::zero(),
            RationalPolynomial::one(),
        ]);
        let (resultant, work) = resultant_in_eliminated_variable(&first, &second).unwrap();
        assert_eq!(resultant, polynomial(&[-2, 0, 1]));
        assert_eq!(work.matrix_extent, 3);
    }

    #[test]
    fn the_resultant_vanishes_identically_when_the_two_curves_share_a_component() {
        // Both carry the factor (v - t); the elimination is degenerate and says so by returning
        // the zero polynomial rather than a spurious finite root set.
        let shared = BivariatePolynomial::new(vec![
            RationalPolynomial::new(vec![Rat::zero(), -Rat::one()]),
            RationalPolynomial::one(),
        ]);
        let left = shared.times(&BivariatePolynomial::new(vec![
            RationalPolynomial::constant(integer(1)),
            RationalPolynomial::one(),
        ]));
        let right = shared.times(&BivariatePolynomial::new(vec![
            RationalPolynomial::constant(integer(2)),
            RationalPolynomial::one(),
        ]));
        let (resultant, _) = resultant_in_eliminated_variable(&left, &right).unwrap();
        assert!(resultant.is_zero());
    }

    #[test]
    fn composition_and_reduction_agree_with_direct_evaluation() {
        let outer = polynomial(&[1, 2, 3]);
        let inner = polynomial(&[-1, 1]);
        let composed = outer.composed_with(&inner);
        for point in [-3_i64, 0, 1, 7] {
            assert_eq!(
                composed.evaluate(&integer(point)),
                outer.evaluate(&inner.evaluate(&integer(point)))
            );
        }
    }

    #[test]
    fn the_written_form_carries_no_decimal_expansion() {
        let written = RationalPolynomial::new(vec![rat(1, 3), rat(-2, 7), Rat::one()]).written("t");
        assert!(
            !written.contains('.'),
            "a float reached a presented row: {written}"
        );
        assert_eq!(written, "t^2 - (2/7)*t + (1/3)");
        assert_eq!(
            RationalPolynomial::new(vec![
                -Rat::one(),
                -Rat::one(),
                Rat::zero(),
                Rat::zero(),
                Rat::zero(),
                Rat::one()
            ])
            .written("x"),
            "x^5 - x - 1"
        );
    }
}
