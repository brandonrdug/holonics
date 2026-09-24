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
//! ## How deep the bisection may go, and why nobody chooses that
//!
//! A bisection that splits an interval until each piece holds one root needs a floor: the point at
//! which two roots are provably too far apart to share a piece. That floor is **not a budget**. It
//! is Mahler's root separation bound, and it is computed from the polynomial's own discriminant and
//! coefficient norm:
//!
//! ```text
//!   sep(f)  >  sqrt( 3 |disc(f)| / n^(n+2) ) * ||f||_2^(1-n)
//! ```
//!
//! for `f` squarefree of degree `n >= 2` (Mahler, *An inequality for the discriminant of a
//! polynomial*, Michigan Math. J. **11** (1964) 257-262; stated in this `||f||_2` form at Wolfram
//! MathWorld, *Root Separation*). Squaring keeps every quantity exactly rational:
//!
//! ```text
//!   sep(f)^2  >  3 |disc(f)| / ( n^(n+2) * (sum a_i^2)^(n-1) )  =:  S
//! ```
//!
//! `disc(f) = (-1)^(n(n-1)/2) Res(f, f') / a_n` is an integer, `sum a_i^2` is an integer, and `S`
//! is an exact positive rational. So the number of splits needed is *read off the polynomial*:
//! an interval of width `w` is split at most until `w^2 <= S`, at which point it cannot hold two
//! distinct roots. A recursion that passes that depth is a **contradiction between Sturm and the
//! discriminant**, and is refused as one — not as a budget overrun.
//!
//! `S` is invariant under scaling `f` by a nonzero constant, exactly as the separation it bounds
//! is: `disc(cf) = c^(2n-2) disc(f)` and `||cf||_2^2 = c^2 ||f||_2^2` cancel.
//!
//! No float, no tolerance, no threshold, no ranking. Every returned population is returned whole.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use crate::geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::{
    AlgebraicRoot, ExactInterval, ExactValueError, IntegerPolynomial, SturmChain,
    check_declared_sturm_work,
};
use crate::exact_work::ExactWork;

mod root_separation;
pub use root_separation::{RootSeparation, RootSeparationBound};

/// One exact polynomial over `Q` in a single variable.
///
/// Coefficients ascend in degree. The empty vector is the zero polynomial; a nonzero polynomial
/// never carries a zero leading coefficient, so `degree` is unambiguous.
///
/// **The wire enforces that normal form.** The derived `Deserialize` skipped
/// [`RationalPolynomial::new`]'s trim, so a remounted instance carrying a trailing zero reported a
/// degree one too high — and `degree()` is what every division, gcd, resultant and census reads
/// first. A wire whose leading coefficient is zero is refused as
/// [`ExactPolynomialError::UntrimmedPolynomialWire`] rather than silently re-normalized into a
/// different polynomial than the one it named. `Default` is the zero polynomial, which is the
/// normal form of zero, so it is not a bypass.
#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(try_from = "RationalPolynomialWire")]
pub struct RationalPolynomial {
    coefficients: Vec<Rat>,
}

#[derive(Deserialize)]
struct RationalPolynomialWire {
    coefficients: Vec<Rat>,
}

impl TryFrom<RationalPolynomialWire> for RationalPolynomial {
    type Error = ExactPolynomialError;

    fn try_from(wire: RationalPolynomialWire) -> Result<Self, Self::Error> {
        if wire.coefficients.last().is_some_and(Zero::is_zero) {
            return Err(ExactPolynomialError::UntrimmedPolynomialWire {
                declared: wire.coefficients.len(),
            });
        }
        let polynomial = Self::new(wire.coefficients);
        Ok(polynomial)
    }
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
        self.plus_impl(other, None)
    }

    pub fn plus_with_work(&self, other: &Self) -> (Self, ExactWork) {
        let mut work = ExactWork::nothing();
        let result = self.plus_impl(other, Some(&mut work));
        (result, work)
    }

    fn plus_impl(&self, other: &Self, mut work: Option<&mut ExactWork>) -> Self {
        let extent = self.coefficients.len().max(other.coefficients.len());
        let mut coefficients = Vec::with_capacity(extent);
        for degree in 0..extent {
            let value = self.coefficient(degree) + other.coefficient(degree);
            if let Some(work) = work.as_deref_mut() {
                work.added(1);
                work.wrote(&value);
            }
            coefficients.push(value);
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
        self.scaled_impl(factor, None)
    }

    pub fn scaled_with_work(&self, factor: &Rat) -> (Self, ExactWork) {
        let mut work = ExactWork::nothing();
        let result = self.scaled_impl(factor, Some(&mut work));
        (result, work)
    }

    fn scaled_impl(&self, factor: &Rat, mut work: Option<&mut ExactWork>) -> Self {
        let coefficients = self
            .coefficients
            .iter()
            .map(|coefficient| {
                let value = coefficient * factor;
                if let Some(work) = work.as_deref_mut() {
                    work.multiplied(1);
                    work.wrote(&value);
                }
                value
            })
            .collect();
        Self::new(coefficients)
    }

    pub fn times(&self, other: &Self) -> Self {
        self.times_impl(other, None)
    }

    pub fn times_with_work(&self, other: &Self) -> (Self, ExactWork) {
        let mut work = ExactWork::nothing();
        let result = self.times_impl(other, Some(&mut work));
        (result, work)
    }

    fn times_impl(&self, other: &Self, mut work: Option<&mut ExactWork>) -> Self {
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
                let product = left * right;
                let coefficient = &mut coefficients[left_degree + right_degree];
                *coefficient += &product;
                if let Some(work) = work.as_deref_mut() {
                    work.multiplied(1);
                    work.added(1);
                    work.wrote(coefficient);
                }
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
        self.divided_by_impl(divisor, None)
    }

    pub fn divided_by_with_work(
        &self,
        divisor: &Self,
    ) -> Result<(Self, Self, ExactWork), ExactPolynomialError> {
        let mut work = ExactWork::nothing();
        let (quotient, remainder) = self.divided_by_impl(divisor, Some(&mut work))?;
        Ok((quotient, remainder, work))
    }

    fn divided_by_impl(
        &self,
        divisor: &Self,
        mut work: Option<&mut ExactWork>,
    ) -> Result<(Self, Self), ExactPolynomialError> {
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
            if let Some(work) = work.as_deref_mut() {
                work.divided(1);
                work.wrote(&factor);
            }
            if !factor.is_zero() {
                quotient[shift] = factor.clone();
                for (degree, coefficient) in divisor.coefficients.iter().enumerate() {
                    remainder[shift + degree] -= &factor * coefficient;
                    if let Some(work) = work.as_deref_mut() {
                        work.multiplied(1);
                        work.added(1);
                        work.wrote(&remainder[shift + degree]);
                    }
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
    ///
    /// [proved-derived; formal-checked] The Lean owner is
    /// `Foundation/RootCount.lean::theSquarefreePartSharesItsRoots`, and **it is conditional**: it
    /// takes `p = gcd(p, p') * q` as a hypothesis and proves from it that `q` has exactly the roots
    /// of `p`. It does not prove that any particular `q` is that quotient. What discharges the
    /// hypothesis is the line below — [`RationalPolynomial::divided_exactly_by`] returns
    /// [`ExactPolynomialError::NonExactPolynomialDivision`] unless the remainder is exactly zero —
    /// so the factorization the theorem assumes is *checked here, at every use*, by the library and
    /// not only by a test. [`RationalPolynomial::made_monic`] then scales by a nonzero constant,
    /// which is a unit and moves no root, so the conclusion transfers to what this returns.
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

    /// The squarefree decomposition, with multiplicities.
    ///
    /// Returns the monic pairwise-coprime squarefree `V_i` with
    /// `p = leading · ∏ V_i^i`, **keyed by the multiplicity `i ≥ 1`**. Each
    /// multiplicity carries at most one factor — `V_i` is by construction the
    /// product of every irreducible factor occurring exactly `i` times — so
    /// multiplicity is a genuine index rather than a field beside one, and the
    /// map is the honest carrier. Constant factors are omitted.
    ///
    /// `squarefree_part` returns the radical and forgets how deep each root
    /// sits. Every reduction that has to *descend* a pole order needs the depth,
    /// which is why this exists beside it. Musser's algorithm, exactly over `ℚ`.
    pub fn squarefree_decomposition(
        &self,
    ) -> Result<std::collections::BTreeMap<u32, Self>, ExactPolynomialError> {
        if self.is_zero() {
            return Err(ExactPolynomialError::ZeroPolynomial);
        }
        let monic = self.made_monic();
        let common = monic.monic_gcd(&monic.derivative())?;
        // `w` carries every distinct root once; `y` carries what remains after
        // one order has been peeled off each.
        let mut w = monic.divided_exactly_by(&common)?;
        let mut y = common;
        let mut decomposition = std::collections::BTreeMap::new();
        let mut multiplicity = 1_u32;
        while w.degree().map(|degree| degree > 0).unwrap_or(false) {
            let z = w.monic_gcd(&y)?;
            let factor = w.divided_exactly_by(&z)?;
            if factor.degree().map(|degree| degree > 0).unwrap_or(false) {
                decomposition.insert(multiplicity, factor.made_monic());
            }
            y = y.divided_exactly_by(&z)?;
            w = z;
            multiplicity = multiplicity
                .checked_add(1)
                .ok_or(ExactPolynomialError::DegreeTooLarge)?;
        }
        Ok(decomposition)
    }

    /// The extended Euclidean relation `s·self + t·other = gcd`, monic gcd.
    ///
    /// Returned as `(gcd, s, t)`. A reduction that must split a numerator
    /// across two coprime denominators is exactly this identity, and computing
    /// it is what lets the split be *derived* rather than searched for.
    pub fn extended_monic_gcd(
        &self,
        other: &Self,
    ) -> Result<(Self, Self, Self), ExactPolynomialError> {
        let (mut old_remainder, mut remainder) = (self.clone(), other.clone());
        let (mut old_s, mut s) = (Self::new(vec![Rat::one()]), Self::zero());
        let (mut old_t, mut t) = (Self::zero(), Self::new(vec![Rat::one()]));
        while !remainder.is_zero() {
            let (quotient, next) = old_remainder.divided_by(&remainder)?;
            old_remainder = std::mem::replace(&mut remainder, next);
            let next_s = old_s.minus(&quotient.times(&s));
            old_s = std::mem::replace(&mut s, next_s);
            let next_t = old_t.minus(&quotient.times(&t));
            old_t = std::mem::replace(&mut t, next_t);
        }
        let Some(leading) = old_remainder.leading().cloned() else {
            return Err(ExactPolynomialError::ZeroPolynomial);
        };
        let inverse = Rat::one() / leading;
        Ok((
            old_remainder.scaled(&inverse),
            old_s.scaled(&inverse),
            old_t.scaled(&inverse),
        ))
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

    /// The primitive integer form **with the polynomial's own sign kept**.
    ///
    /// [definition] [`RationalPolynomial::primitive_integer_form`] normalizes the leading
    /// coefficient positive, which is gauge for a question about *one* polynomial — a Sturm chain
    /// of `−f` reads exactly what the chain of `f` reads, by
    /// `Foundation/RootCount.lean`'s `theReadingIsInvariantUnderCommonNonzeroRescaling`. It is
    /// **not** gauge for a question about a *pair*: the Cauchy index `I(q/p)` changes sign when one
    /// of the two is flipped and the other is not. Anything reading a numerator against a
    /// denominator takes this form instead.
    pub fn signed_primitive_integer_form(&self) -> Result<IntegerPolynomial, ExactPolynomialError> {
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

// ===============================================================================================
// the root separation bound: how far a bisection may go, read off the polynomial

/// `Res(f, g)` by the Euclidean recurrence over `Q`, with the exact step count.
///
/// ```text
///   res(f, g) = g_0^deg(f)                                         when deg g = 0
///   res(f, g) = 0                                                  when f mod g = 0 and deg g >= 1
///   res(f, g) = (-1)^(deg f * deg g) lc(g)^(deg f - deg r) res(g, r),   r = f mod g
/// ```
///
/// This is the **second** route to a resultant in this module. [`resultant_in_eliminated_variable`]
/// takes the Sylvester determinant by fraction-free Bareiss elimination; this one runs the
/// Euclidean recurrence. `the_two_resultant_routes_agree` holds them against each other, which is
/// what makes either figure a measurement rather than a single unchecked route.
pub fn euclidean_resultant(
    left: &RationalPolynomial,
    right: &RationalPolynomial,
) -> Result<(Rat, u64), ExactPolynomialError> {
    let mut first = left.clone();
    let mut second = right.clone();
    let mut accumulated = Rat::one();
    let mut steps = 0_u64;
    loop {
        let first_degree = first.degree().ok_or(ExactPolynomialError::ZeroPolynomial)?;
        let second_degree = second
            .degree()
            .ok_or(ExactPolynomialError::ZeroPolynomial)?;
        if second_degree > first_degree {
            if (first_degree * second_degree) % 2 == 1 {
                accumulated = -accumulated;
            }
            std::mem::swap(&mut first, &mut second);
            steps += 1;
            continue;
        }
        if second_degree == 0 {
            let constant = second.coefficient(0);
            let power =
                u32::try_from(first_degree).map_err(|_| ExactPolynomialError::DegreeTooLarge)?;
            return Ok((accumulated * constant.pow(power as i32), steps));
        }
        let (_, remainder) = first.divided_by(&second)?;
        steps += 1;
        if remainder.is_zero() {
            return Ok((Rat::zero(), steps));
        }
        let remainder_degree = remainder
            .degree()
            .expect("a nonzero remainder has a degree");
        if (first_degree * second_degree) % 2 == 1 {
            accumulated = -accumulated;
        }
        let leading = second.leading().expect("a nonzero divisor leads").clone();
        let drop = u32::try_from(first_degree - remainder_degree)
            .map_err(|_| ExactPolynomialError::DegreeTooLarge)?;
        accumulated *= leading.pow(drop as i32);
        first = second;
        second = remainder;
    }
}

/// `disc(f) = (-1)^(n(n-1)/2) Res(f, f') / a_n`, exact.
///
/// MathWorld, *Polynomial Discriminant*: `D(p) = (-1)^(n(n-1)/2) R(p, p') / a_n` in characteristic
/// zero. The return is refused rather than rounded if it comes out non-integral, because the
/// discriminant of an integer polynomial is an integer and a fractional one means the resultant is
/// wrong.
pub fn integer_discriminant(
    polynomial: &IntegerPolynomial,
) -> Result<(BigInt, u64), ExactPolynomialError> {
    let degree = polynomial.degree();
    if degree < 2 {
        return Err(ExactPolynomialError::DiscriminantDegreeTooLow { degree });
    }
    let rational = RationalPolynomial::from_integer_polynomial(polynomial);
    let (resultant, steps) = euclidean_resultant(&rational, &rational.derivative())?;
    let leading = rational
        .leading()
        .expect("a nonzero polynomial leads")
        .clone();
    let mut value = resultant / leading;
    if (degree * (degree - 1) / 2) % 2 == 1 {
        value = -value;
    }
    if !value.is_integer() {
        return Err(ExactPolynomialError::NonIntegralDiscriminant);
    }
    Ok((value.to_integer(), steps))
}

/// Mahler's root separation bound, exactly, for a squarefree integer polynomial.
///
/// ```text
///   sep(f)^2  >  3 |disc(f)| / ( n^(n+2) * (||f||_2^2)^(n-1) )
/// ```
///
/// A vanishing discriminant is refused by name: it means the polynomial is not squarefree, and the
/// bound is only stated for squarefree polynomials.
pub fn root_separation(
    polynomial: &IntegerPolynomial,
) -> Result<RootSeparation, ExactPolynomialError> {
    let degree = polynomial.degree();
    if degree < 2 {
        return Ok(RootSeparation::NothingToSeparate { degree });
    }
    let (discriminant, euclidean_steps) = integer_discriminant(polynomial)?;
    if discriminant.is_zero() {
        return Err(ExactPolynomialError::VanishingDiscriminant);
    }
    let coefficient_norm_squared = polynomial
        .coefficients
        .iter()
        .map(|value| value * value)
        .sum::<BigInt>();
    let exponent = u32::try_from(degree + 2).map_err(|_| ExactPolynomialError::DegreeTooLarge)?;
    let power = u32::try_from(degree - 1).map_err(|_| ExactPolynomialError::DegreeTooLarge)?;
    let denominator = BigInt::from(degree).pow(exponent) * coefficient_norm_squared.pow(power);
    let squared_lower_bound = Rat::new(BigInt::from(3) * discriminant.abs(), denominator);
    Ok(RootSeparation::Bounded(RootSeparationBound {
        degree,
        discriminant,
        coefficient_norm_squared,
        squared_lower_bound,
        euclidean_steps,
    }))
}

/// Cauchy's lower bound on the **nonzero** roots: every root `x != 0` of `f` has
/// `|x| >= |a_m| / ( |a_m| + max_{i>m} |a_i| )`, where `a_m` is the lowest nonzero coefficient.
///
/// This is Cauchy's upper bound applied to the reversal of `f / x^m`, whose roots are the
/// reciprocals. `None` exactly when `f` is a monomial and therefore has no nonzero root.
pub fn nonzero_root_lower_bound(polynomial: &IntegerPolynomial) -> Option<Rat> {
    let degree = polynomial.degree();
    let lowest = polynomial
        .coefficients
        .iter()
        .position(|value| !value.is_zero())?;
    if lowest == degree {
        return None;
    }
    let anchor = polynomial.coefficients[lowest].abs();
    let largest = polynomial.coefficients[lowest + 1..=degree]
        .iter()
        .map(|value| value.abs())
        .max()
        .unwrap_or_else(BigInt::zero);
    Some(Rat::new(anchor.clone(), anchor + largest))
}

// -------------------------------------------------------------------------------------------------
// where the roots are: a bound that carries its own certificate
// -------------------------------------------------------------------------------------------------

/// **The declared ceiling on the doublings a certified root bound may take.**
///
/// [definition] The doubling terminates as mathematics: above `max Re(root)` the shifted polynomial
/// is coefficientwise nonnegative, because a real polynomial all of whose roots have negative real
/// part factors into linear and quadratic factors with positive coefficients. So this is a
/// hostile-input guard on a caller-declared coefficient size, not an approximation budget, and a
/// polynomial that exhausts it returns [`ExactPolynomialError::RootBoundDoublingExhausted`].
pub const ROOT_BOUND_DOUBLING_CEILING: u32 = 4096;

/// **The declared ceiling on the half-integer descent's recursion depth.**
///
/// [definition] The census's first descent halves its interval to unit width, so its depth is
/// `log2` of the enclosure's width — a number the caller's coefficients decide. It is a *recursive*
/// descent, so the load it puts on the machine stack is a load no `Result` can carry, and a
/// polynomial whose enclosure is wider than `2^4096` is refused by name instead. The certified
/// enclosure makes this ceiling far less reachable than the absolute Cauchy bound did.
pub const HALF_INTEGER_DESCENT_CEILING: u32 = 4096;

/// `f(x + shift)`, exactly, by repeated synthetic division.
///
/// The returned coefficient `i` is `f^(i)(shift) / i!`, ascending as everywhere else here. The cost
/// is `O(deg^2)` integer additions and multiplications, which is negligible beside one Sturm count.
pub fn taylor_shifted(coefficients: &[BigInt], shift: &BigInt) -> Vec<BigInt> {
    let mut shifted = coefficients.to_vec();
    let length = shifted.len();
    if length < 2 {
        return shifted;
    }
    for start in 0..length - 1 {
        for index in (start..length - 1).rev() {
            let carried = &shifted[index + 1] * shift;
            shifted[index] += carried;
        }
    }
    shifted
}

/// **The certificate that `bound` exceeds every real root of `f`.**
///
/// If every coefficient of `f(x + bound)` is nonnegative and its constant coefficient `f(bound)` is
/// strictly positive, then `f(y) >= f(bound) > 0` for every `y >= bound`, so `f` has no real root
/// at or above `bound`. That is a **proof about this polynomial**, computed in `O(deg^2)` integer
/// operations, not a bound quoted from a theorem whose constant has to be trusted.
fn exceeds_every_real_root(coefficients: &[BigInt], bound: &BigInt) -> bool {
    let shifted = taylor_shifted(coefficients, bound);
    shifted.first().is_some_and(Signed::is_positive)
        && shifted.iter().all(|value| !value.is_negative())
}

/// The least integer `m >= 1` with `m^power * anchor >= magnitude`, by bracketing and bisection.
fn least_integer_root(magnitude: &BigInt, anchor: &BigInt, power: u32) -> BigInt {
    let reached = |candidate: &BigInt| -> bool { candidate.pow(power) * anchor >= *magnitude };
    let mut high = BigInt::one();
    if reached(&high) {
        return high;
    }
    while !reached(&high) {
        high *= 2;
    }
    let mut low = BigInt::one();
    while &low + 1 < high {
        let middle = (&low + &high) / 2;
        if reached(&middle) {
            high = middle;
        } else {
            low = middle;
        }
    }
    high
}

/// The starting guess for an upper bound on the positive roots of a polynomial with **positive**
/// leading coefficient: `2 * max_k (|a_{n-k}| / a_n)^(1/k)` over the `k` at which `a_{n-k} < 0`
/// (Kioustelidis; the one-sided form of Fujiwara's bound, and the bound the continued-fraction
/// isolation algorithms use). Only the negative coefficients enter, which is exactly what makes it
/// **one-sided** and therefore tight for an operator whose spectrum lies on one side of zero.
///
/// This is a *guess*: [`certified_upper_bound`] verifies it and doubles until the certificate
/// holds, so nothing downstream depends on the constant `2` being the sharpest one.
fn kioustelidis_guess(coefficients: &[BigInt]) -> BigInt {
    let Some(degree) = coefficients.len().checked_sub(1) else {
        return BigInt::one();
    };
    let leading = coefficients[degree].abs();
    let mut largest = BigInt::zero();
    for step in 1..=degree {
        let coefficient = &coefficients[degree - step];
        if !coefficient.is_negative() {
            continue;
        }
        let Ok(power) = u32::try_from(step) else {
            continue;
        };
        let candidate = least_integer_root(&coefficient.abs(), &leading, power);
        if candidate > largest {
            largest = candidate;
        }
    }
    if largest.is_zero() {
        // No negative coefficient: `f(y) >= a_0 > 0` already holds past the origin.
        BigInt::one()
    } else {
        BigInt::from(2) * largest
    }
}

/// The absolute Cauchy bound `max_{i<n} |a_i| / |a_n| + 1`, rounded up to an integer.
///
/// Every root satisfies `|x| < ` this, so it is both the bound the certified enclosure replaces and
/// the **backstop** it never does worse than: a root's real part is at most its modulus, so the
/// Taylor-shift certificate is guaranteed to hold here.
fn absolute_cauchy_bound(coefficients: &[BigInt]) -> BigInt {
    let Some(degree) = coefficients.len().checked_sub(1) else {
        return BigInt::one();
    };
    let widest = coefficients[..degree]
        .iter()
        .map(Signed::abs)
        .max()
        .unwrap_or_else(BigInt::zero);
    let leading = coefficients[degree].abs();
    if leading.is_zero() {
        return BigInt::one();
    }
    (&widest + &leading - BigInt::one()) / &leading + BigInt::one()
}

/// An upper bound on the real roots, **verified by [`exceeds_every_real_root`]** and doubled until
/// it verifies. `coefficients` must have a positive leading coefficient.
///
/// The search starts at the smaller of the `k`-th root guess and the absolute Cauchy bound and is
/// capped at the latter, so the returned bound is **never wider than the bound it replaced** even
/// where the one-sided guess happens to be the looser of the two.
fn certified_upper_bound(coefficients: &[BigInt]) -> Result<(BigInt, u32), ExactPolynomialError> {
    let cauchy = absolute_cauchy_bound(coefficients);
    let mut bound = kioustelidis_guess(coefficients)
        .max(BigInt::one())
        .min(cauchy.clone());
    let mut doublings = 0_u32;
    loop {
        if exceeds_every_real_root(coefficients, &bound) {
            return Ok((bound, doublings));
        }
        if bound >= cauchy || doublings >= ROOT_BOUND_DOUBLING_CEILING {
            return Err(ExactPolynomialError::RootBoundDoublingExhausted {
                ceiling: ROOT_BOUND_DOUBLING_CEILING,
            });
        }
        bound = (bound * BigInt::from(2)).min(cauchy.clone());
        doublings += 1;
    }
}

/// `f(-x)` with the leading coefficient normalized positive: the reflection whose positive roots
/// are the negatives of `f`'s negative roots.
fn reflected_with_positive_leading(coefficients: &[BigInt]) -> Vec<BigInt> {
    let mut reflected: Vec<BigInt> = coefficients
        .iter()
        .enumerate()
        .map(|(degree, coefficient)| {
            if degree % 2 == 0 {
                coefficient.clone()
            } else {
                -coefficient
            }
        })
        .collect();
    if reflected.last().is_some_and(Signed::is_negative) {
        for value in &mut reflected {
            *value = -value.clone();
        }
    }
    reflected
}

/// **Where the real roots are, with the proof attached and the two sides counted separately.**
///
/// [proved-derived; implemented-exact] `rational_root_census` used to descend from the *absolute*
/// Cauchy bound `max |a_i| / |a_n| + 1` of the monic companion. That bound is a magnitude, and a
/// magnitude is read off the widest coefficient: a degree-eight companion built from 103-bit matrix
/// entries has a constant term near `8 x 103` bits by Hadamard, so the Cauchy bound is `2^770` wide
/// while the eigenvalues themselves cannot pass `2^106`
/// (`lattice_gauge.rs`, the rebase note). Descending from there is a thousand Sturm counts per root
/// before the first one is separated, which is why both R1 and R3 routed around this owner.
///
/// This enclosure is different in three ways, each of which matters on a physical operator:
///
/// 1. **It is a `k`-th root bound, not a magnitude.** The guess is
///    `2 max_k (|a_{n-k}| / a_n)^(1/k)`, so the same `2^770` constant term contributes
///    `2 * (2^770)^(1/8) ~ 2^97` rather than `2^770`.
/// 2. **The two sides are counted separately.** The positive bound reads only the *negative*
///    coefficients and the negative bound reads the reflection's, so a positive semidefinite
///    operator — whose companion has no sign change on one side — gets a bound of `1` there instead
///    of a symmetric copy of the other side.
/// 3. **It carries its own certificate.** Each side's bound `B` is returned only once
///    `f(x + B)` has come out coefficientwise nonnegative with `f(B) > 0`, which *proves* there is
///    no root at or above `B`. The bound is therefore not trusted from a quoted constant; the
///    constant only decides where the verification starts.
///
/// `cauchy_bound` is retained beside them so a reader can see, on their own material, what was
/// replaced.
/// A remounted enclosure passes through [`RealRootEnclosure::assembled`]: the wire carries the same
/// fields, and one whose interval does not agree with its own two bounds — or whose bounds are not
/// positive, or which claims to be narrower than the Cauchy bound it reports — is refused at the
/// boundary rather than reconstructed past the constructor. The *certificate* itself is a statement
/// about a polynomial the enclosure does not carry, so a remounted enclosure is testimony about
/// that polynomial; what is checkable without it is checked.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "RealRootEnclosureWire")]
pub struct RealRootEnclosure {
    /// Every real root is strictly below this.
    pub positive_bound: BigInt,
    /// Every real root is strictly above `-negative_bound`.
    pub negative_bound: BigInt,
    /// `[-(negative_bound + 1/2), positive_bound + 1/2]`. **Half-integer endpoints**, so a monic
    /// integer polynomial can never have a root on one and every Sturm count taken against it is
    /// at a legal boundary.
    pub interval: ExactInterval,
    /// The absolute Cauchy bound this replaced, retained as the comparison.
    pub cauchy_bound: BigInt,
    /// How many doublings the certificate needed past the guess. Zero means the guess certified.
    pub doublings: u32,
    /// Set when a caller's declared enclosure was tighter on that side **and certified**.
    pub declared_positive: bool,
    pub declared_negative: bool,
}

#[derive(Deserialize)]
struct RealRootEnclosureWire {
    positive_bound: BigInt,
    negative_bound: BigInt,
    interval: ExactInterval,
    cauchy_bound: BigInt,
    doublings: u32,
    declared_positive: bool,
    declared_negative: bool,
}

impl TryFrom<RealRootEnclosureWire> for RealRootEnclosure {
    type Error = ExactPolynomialError;

    fn try_from(wire: RealRootEnclosureWire) -> Result<Self, Self::Error> {
        Self::assembled(
            wire.positive_bound,
            wire.negative_bound,
            wire.interval,
            wire.cauchy_bound,
            wire.doublings,
            wire.declared_positive,
            wire.declared_negative,
        )
    }
}

impl RealRootEnclosure {
    /// The one way an enclosure comes into existence, including from a wire.
    fn assembled(
        positive_bound: BigInt,
        negative_bound: BigInt,
        interval: ExactInterval,
        cauchy_bound: BigInt,
        doublings: u32,
        declared_positive: bool,
        declared_negative: bool,
    ) -> Result<Self, ExactPolynomialError> {
        if !positive_bound.is_positive()
            || !negative_bound.is_positive()
            || !cauchy_bound.is_positive()
        {
            return Err(ExactPolynomialError::MalformedRootEnclosure);
        }
        if positive_bound > cauchy_bound || negative_bound > cauchy_bound {
            return Err(ExactPolynomialError::MalformedRootEnclosure);
        }
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        if interval.upper != Rat::from_integer(positive_bound.clone()) + &half
            || interval.lower != -Rat::from_integer(negative_bound.clone()) - &half
        {
            return Err(ExactPolynomialError::MalformedRootEnclosure);
        }
        Ok(Self {
            positive_bound,
            negative_bound,
            interval,
            cauchy_bound,
            doublings,
            declared_positive,
            declared_negative,
        })
    }

    /// The width of the Cauchy interval this replaced against the width of the certified
    /// enclosure, as an exact ratio: `(2·cauchy + 1) / (positive + negative + 1)`, both intervals
    /// being widened to half-integer endpoints. A readout, never a decision.
    pub fn narrowing(&self) -> Rat {
        let replaced = BigInt::from(2) * &self.cauchy_bound + BigInt::one();
        let certified = &self.positive_bound + &self.negative_bound + BigInt::one();
        Rat::new(replaced, certified)
    }
}

/// **The certified real-root enclosure of an integer polynomial.**
pub fn certified_real_root_enclosure(
    polynomial: &IntegerPolynomial,
) -> Result<RealRootEnclosure, ExactPolynomialError> {
    certified_enclosure_within(polynomial, None)
}

/// The certified enclosure, optionally narrowed by a caller's declaration.
///
/// [definition] A caller's interval is a **declaration**, so it is verified rather than believed:
/// the narrower of the two endpoints is taken on each side and put through
/// [`exceeds_every_real_root`], and a declaration that does not certify is discarded in favour of
/// this owner's own bound. A census can therefore never be made incomplete by a caller who
/// declared an interval that does not actually enclose the roots.
fn certified_enclosure_within(
    polynomial: &IntegerPolynomial,
    declared: Option<&ExactInterval>,
) -> Result<RealRootEnclosure, ExactPolynomialError> {
    polynomial.check_declared_size()?;
    let degree = polynomial.degree();
    if degree == 0 {
        return Err(ExactPolynomialError::ConstantPolynomial);
    }
    let mut forward = polynomial.coefficients.clone();
    if forward.last().is_some_and(Signed::is_negative) {
        for value in &mut forward {
            *value = -value.clone();
        }
    }
    let backward = reflected_with_positive_leading(&forward);

    let (mut positive_bound, forward_doublings) = certified_upper_bound(&forward)?;
    let (mut negative_bound, backward_doublings) = certified_upper_bound(&backward)?;
    let mut declared_positive = false;
    let mut declared_negative = false;

    if let Some(interval) = declared {
        // The caller's upper endpoint, rounded outward to an integer; taken only if it is tighter
        // and only if it certifies.
        let candidate = interval.upper.ceil().to_integer().max(BigInt::one());
        if candidate < positive_bound && exceeds_every_real_root(&forward, &candidate) {
            positive_bound = candidate;
            declared_positive = true;
        }
        let candidate = (-interval.lower.clone())
            .ceil()
            .to_integer()
            .max(BigInt::one());
        if candidate < negative_bound && exceeds_every_real_root(&backward, &candidate) {
            negative_bound = candidate;
            declared_negative = true;
        }
    }

    let cauchy_bound = absolute_cauchy_bound(&polynomial.coefficients);

    let half = Rat::new(BigInt::one(), BigInt::from(2));
    let interval = ExactInterval::new(
        -Rat::from_integer(negative_bound.clone()) - &half,
        Rat::from_integer(positive_bound.clone()) + &half,
    )
    .map_err(|_| ExactPolynomialError::MalformedInterval)?;

    RealRootEnclosure::assembled(
        positive_bound,
        negative_bound,
        interval,
        cauchy_bound,
        forward_doublings.max(backward_doublings),
        declared_positive,
        declared_negative,
    )
}

/// **The declared ceiling on an isolation's bisection depth at this owner.**
///
/// [definition] `depth_bound` is a caller's declaration and it sizes both the descent and the
/// worklist, so the owner carries a ceiling of its own — the same discipline
/// `hodge_receiver::ISOLATION_DEPTH_CEILING` already applies to its own entry point, moved to where
/// the descent actually is. Each bisection halves an interval, so this narrows any enclosure by
/// `2^-1024`.
pub const ISOLATION_DEPTH_CEILING: u32 = 1024;

/// **Isolate every real root of an integer polynomial inside a declared enclosure.**
///
/// [proved-derived; implemented-exact] One [`SturmChain`] is built and **every** count below is
/// taken against it, which is the whole difference between this and a descent that rebuilt the
/// sequence per count. The split point is the midpoint, moved toward the lower endpoint while the
/// polynomial vanishes there; a polynomial of degree `d` has at most `d` roots and the candidates
/// are distinct, so `d + 1` attempts cannot all be roots and the move terminates by pigeonhole
/// rather than by a budget.
///
/// The descent is an **explicit worklist**, not recursion: the depth is a caller's declaration and
/// a recursive descent would put a caller-sized load on the machine stack, which no `Result` can
/// carry. The left half of each split is taken first, so the returned intervals are ascending, and
/// the worklist never holds more than `depth_bound + 1` pending intervals.
///
/// Endpoints of the returned intervals are never roots, so each is a lawful Sturm certificate and
/// can be handed to [`crate::exact_value::AlgebraicRoot::isolate`] unchanged.
pub fn isolate_real_roots(
    polynomial: &IntegerPolynomial,
    enclosure: &ExactInterval,
    depth_bound: u32,
) -> Result<Vec<ExactInterval>, ExactPolynomialError> {
    let chain = polynomial.sturm_chain()?;
    isolate_against_chain(polynomial, &chain, enclosure, depth_bound).map(|(intervals, _)| intervals)
}

/// [`isolate_real_roots`] against a chain the caller already built, also returning the depth the
/// descent actually reached.
///
/// **The chain must be the chain of this polynomial, and that is now verified.** Pairing `x² + 1`
/// with the chain of `x` used to return `Ok` with an interval containing no root at all. A
/// [`SturmChain`] carries its own source polynomial, so this entry is a thin wrapper over
/// [`isolate_with_chain`], which takes the chain alone and cannot be mispaired.
pub fn isolate_against_chain(
    polynomial: &IntegerPolynomial,
    chain: &SturmChain,
    enclosure: &ExactInterval,
    depth_bound: u32,
) -> Result<(Vec<ExactInterval>, u32), ExactPolynomialError> {
    if chain.polynomial() != polynomial || !chain.is_sturm_chain() {
        return Err(ExactValueError::ChainPolynomialMismatch {
            chain_degree: chain.polynomial().degree(),
            declared_degree: polynomial.degree(),
        }
        .into());
    }
    isolate_with_chain(chain, enclosure, depth_bound)
}

/// **Isolate every real root of the chain's own polynomial inside a declared enclosure.**
///
/// The chain is the only argument that names a polynomial, so there is no pairing to get wrong.
/// [`isolate_real_roots`] and [`isolate_against_chain`] both reduce to this.
pub fn isolate_with_chain(
    chain: &SturmChain,
    enclosure: &ExactInterval,
    depth_bound: u32,
) -> Result<(Vec<ExactInterval>, u32), ExactPolynomialError> {
    if !chain.is_sturm_chain() {
        return Err(ExactValueError::ChainIsNotASturmChain.into());
    }
    let polynomial = chain.polynomial();
    if depth_bound > ISOLATION_DEPTH_CEILING {
        return Err(ExactPolynomialError::IsolationDepthBoundTooLarge {
            bound: depth_bound,
            ceiling: ISOLATION_DEPTH_CEILING,
        });
    }
    let degree = polynomial.degree();
    let two = Rat::from_integer(BigInt::from(2));
    let mut isolated: Vec<ExactInterval> = Vec::new();
    let mut reached = 0_u32;
    // Last in, first out; the left half is pushed last so it is taken first and the isolating
    // intervals leave in ascending order.
    let mut pending: Vec<(Rat, Rat, u32)> =
        vec![(enclosure.lower.clone(), enclosure.upper.clone(), 0)];
    while let Some((low, high, depth)) = pending.pop() {
        reached = reached.max(depth);
        let interval = ExactInterval::new(low.clone(), high.clone())
            .map_err(|_| ExactPolynomialError::MalformedInterval)?;
        let count = chain.distinct_root_count(&interval)?;
        if count == 0 {
            continue;
        }
        if count == 1 {
            isolated.push(interval);
            continue;
        }
        if depth >= depth_bound {
            return Err(ExactPolynomialError::IsolationDepthExceeded { bound: depth_bound });
        }
        let mut middle = (&low + &high) / &two;
        let mut attempts = 0_usize;
        while chain.vanishes_at(&middle) {
            middle = (&low + &middle) / &two;
            attempts += 1;
            if attempts > degree + 1 {
                return Err(ExactPolynomialError::NoInteriorNonRoot);
            }
        }
        pending.push((middle.clone(), high, depth + 1));
        pending.push((low, middle, depth + 1));
    }
    Ok((isolated, reached))
}

/// The interior points a bisection may split at, read off the degree.
///
/// A polynomial of degree `d` has at most `d` roots, so `d + 1` distinct interior points contain at
/// least one non-root — by pigeonhole, with no list to run out. The points are `k / (d + 2)` of the
/// way across, ordered by distance from the middle, so the **first** candidate is the midpoint
/// whenever `d` is even and the nearest point to it otherwise.
///
/// This replaces a hand-written list of thirteen fractions, which silently could not serve a
/// polynomial of degree thirteen or above.
pub fn interior_split_schedule(degree: usize) -> Vec<Rat> {
    let parts = BigInt::from(degree + 2);
    let mut fractions: Vec<Rat> = (1..=degree + 1)
        .map(|step| Rat::new(BigInt::from(step), parts.clone()))
        .collect();
    let middle = Rat::new(BigInt::one(), BigInt::from(2));
    fractions.sort_by(|left, right| {
        let left_gap = (left - &middle).abs();
        let right_gap = (right - &middle).abs();
        left_gap.cmp(&right_gap).then_with(|| left.cmp(right))
    });
    fractions
}

/// The largest fraction of an interval either child of a split may retain.
///
/// For a schedule of split points `f`, the two children keep `f` and `1 - f`, so the worst case is
/// `max_f max(f, 1 - f)`. It is what turns a split count into a width guarantee, and it is read off
/// the schedule rather than assumed to be one half.
pub fn worst_retained_fraction(schedule: &[Rat]) -> Result<Rat, ExactPolynomialError> {
    let mut worst: Option<Rat> = None;
    for fraction in schedule {
        if !fraction.is_positive() || fraction >= &Rat::one() {
            return Err(ExactPolynomialError::InvalidSplitFraction);
        }
        let retained = fraction.clone().max(Rat::one() - fraction);
        worst = Some(match worst {
            None => retained,
            Some(current) => current.max(retained),
        });
    }
    worst.ok_or(ExactPolynomialError::EmptySplitSchedule)
}

/// The smallest `r` with `initial_squared * retained^(2r) <= target_squared`.
///
/// Everything is kept squared so that a bound whose square root is irrational — which every root
/// separation bound's is — never has to be taken. Found by bracketing and then bisecting on `r`, so
/// the cost is logarithmic in the answer and every comparison is an exact integer comparison.
pub fn squared_shrinking_steps(
    initial_squared: &Rat,
    retained: &Rat,
    target_squared: &Rat,
) -> Result<u64, ExactPolynomialError> {
    if !initial_squared.is_positive()
        || !target_squared.is_positive()
        || !retained.is_positive()
        || retained >= &Rat::one()
    {
        return Err(ExactPolynomialError::InvalidShrinkingStep);
    }
    // `initial * (rn/rd)^(2r) <= target`  <=>  `initial_n * target_d * rn^(2r) <= target_n *
    // initial_d * rd^(2r)`, all positive integers.
    let left_constant = initial_squared.numer() * target_squared.denom();
    let right_constant = target_squared.numer() * initial_squared.denom();
    let step_numerator = retained.numer().clone();
    let step_denominator = retained.denom().clone();
    let reached = |steps: u64| -> Result<bool, ExactPolynomialError> {
        let exponent = u32::try_from(steps.saturating_mul(2))
            .map_err(|_| ExactPolynomialError::DegreeTooLarge)?;
        Ok(&left_constant * step_numerator.pow(exponent)
            <= &right_constant * step_denominator.pow(exponent))
    };
    if reached(0)? {
        return Ok(0);
    }
    let mut high = 1_u64;
    while !reached(high)? {
        high = high
            .checked_mul(2)
            .ok_or(ExactPolynomialError::DegreeTooLarge)?;
    }
    let mut low = high / 2;
    while low + 1 < high {
        let middle = low + (high - low) / 2;
        if reached(middle)? {
            high = middle;
        } else {
            low = middle;
        }
    }
    Ok(high)
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
///
/// **A remounted census is re-derived where the data to re-derive it is here.** `source` alone
/// determines `primitive`, `leading_coefficient` and `monic_companion`, so the wire rebuilds all
/// three — behind [`MONIC_COMPANION_BIT_CEILING`], because that is precisely the blow-up the
/// census's own entry gates — and refuses on disagreement. What cannot be rebuilt without
/// redoing the descent is checked for agreement with itself: every rational root vanishes on
/// `source`, every isolated root belongs to the companion, the two counts agree, the bounding
/// interval is the enclosure's own, and the derived splitting depth is inside this owner's
/// ceiling. Each carried [`CensusedRealRoot`] re-runs its own Sturm isolation through
/// [`AlgebraicRoot`]'s wire before any of this.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "RationalRootCensusWire")]
pub struct RationalRootCensus {
    pub source: RationalPolynomial,
    pub primitive: IntegerPolynomial,
    /// `B(z) = c^(n-1) A(z/c)`, monic over `Z`, whose integer roots are `c` times the rational
    /// roots of `A`.
    pub monic_companion: IntegerPolynomial,
    pub leading_coefficient: BigInt,
    /// The certified enclosure the descent ran over: every real root of the companion lies
    /// strictly inside, and [`RationalRootCensus::enclosure`] carries the proof.
    pub bounding_interval: ExactInterval,
    pub distinct_real_roots: u32,
    pub roots: Vec<CensusedRealRoot>,
    /// Every rational root of `source`, exactly and completely.
    pub rational_roots: Vec<Rat>,
    /// Mahler's bound on the squared distance between two roots of the squarefree part, read off
    /// its own discriminant. This is what decides how far the isolation is allowed to descend.
    pub separation: RootSeparation,
    /// The splits the bound above permits, given the widest leaf the half-integer descent handed on
    /// and the worst fraction the declared split schedule can retain. A recursion that passes this
    /// is a contradiction, not an exhausted budget.
    pub isolation_depth_bound: u64,
    /// The worst fraction either child of a split may retain, read off the split schedule.
    pub split_schedule_retained: Rat,
    /// **Where the roots were looked for, and the certificate that they are all in there.** See
    /// [`RealRootEnclosure`]: the bound is a `k`-th root bound, split positive from negative, and
    /// each side is returned only once the Taylor shift proves there is no root past it.
    pub enclosure: RealRootEnclosure,
    pub work: CensusWork,
}

#[derive(Deserialize)]
struct RationalRootCensusWire {
    source: RationalPolynomial,
    primitive: IntegerPolynomial,
    monic_companion: IntegerPolynomial,
    leading_coefficient: BigInt,
    bounding_interval: ExactInterval,
    distinct_real_roots: u32,
    roots: Vec<CensusedRealRoot>,
    rational_roots: Vec<Rat>,
    separation: RootSeparation,
    isolation_depth_bound: u64,
    split_schedule_retained: Rat,
    enclosure: RealRootEnclosure,
    work: CensusWork,
}

fn census_clause(clause: &'static str) -> ExactPolynomialError {
    ExactPolynomialError::MalformedCensus { clause }
}

impl TryFrom<RationalRootCensusWire> for RationalRootCensus {
    type Error = ExactPolynomialError;

    fn try_from(wire: RationalRootCensusWire) -> Result<Self, Self::Error> {
        // Re-derived, not believed.
        let primitive = wire.source.primitive_integer_form()?;
        if primitive != wire.primitive {
            return Err(census_clause("the primitive integer form is not the source's"));
        }
        let leading = primitive
            .coefficients
            .last()
            .cloned()
            .ok_or(ExactPolynomialError::ZeroPolynomial)?;
        if leading != wire.leading_coefficient {
            return Err(census_clause(
                "the leading coefficient is not the primitive form's",
            ));
        }
        // The companion is the blow-up this owner gates, so the gate is taken before it is rebuilt.
        check_companion_declared_size(&primitive, &leading)?;
        if monic_companion_of(&primitive, &leading)? != wire.monic_companion {
            return Err(census_clause(
                "the monic companion is not the one the primitive form generates",
            ));
        }
        if wire.bounding_interval != wire.enclosure.interval {
            return Err(census_clause(
                "the bounding interval is not the certified enclosure's own",
            ));
        }
        if wire.distinct_real_roots as usize != wire.roots.len() {
            return Err(census_clause(
                "the distinct real root count does not match the isolated population",
            ));
        }
        if wire.isolation_depth_bound > SEPARATION_SPLITTING_DEPTH_CEILING {
            return Err(ExactPolynomialError::SeparationSplittingDepthTooLarge {
                bound: wire.isolation_depth_bound,
                ceiling: SEPARATION_SPLITTING_DEPTH_CEILING,
            });
        }
        let leading_rational = Rat::from_integer(leading.clone());
        let mut previous: Option<&ExactInterval> = None;
        for root in &wire.roots {
            if root.isolating.polynomial != wire.monic_companion {
                return Err(census_clause(
                    "an isolated root does not belong to the monic companion",
                ));
            }
            if previous.is_some_and(|last| last.upper > root.isolating.isolating_interval.lower) {
                return Err(census_clause(
                    "the isolating intervals are not ascending and disjoint",
                ));
            }
            previous = Some(&root.isolating.isolating_interval);
            if let Some(value) = &root.rational_value {
                let scaled = value * &leading_rational;
                if scaled <= root.isolating.isolating_interval.lower
                    || scaled >= root.isolating.isolating_interval.upper
                    || !wire.monic_companion.evaluate(&scaled).is_zero()
                {
                    return Err(ExactPolynomialError::CensusedRootValueDisagrees {
                        value: value.to_string(),
                    });
                }
                if !wire.rational_roots.contains(value) {
                    return Err(census_clause(
                        "a root declared rational is absent from the rational population",
                    ));
                }
            }
        }
        for value in &wire.rational_roots {
            if !wire.source.evaluate(value).is_zero() {
                return Err(ExactPolynomialError::CensusRootDoesNotVanish);
            }
        }
        if wire.rational_roots.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(census_clause(
                "the rational population is not ascending and deduplicated",
            ));
        }
        Ok(RationalRootCensus {
            source: wire.source,
            primitive,
            monic_companion: wire.monic_companion,
            leading_coefficient: leading,
            bounding_interval: wire.bounding_interval,
            distinct_real_roots: wire.distinct_real_roots,
            roots: wire.roots,
            rational_roots: wire.rational_roots,
            separation: wire.separation,
            isolation_depth_bound: wire.isolation_depth_bound,
            split_schedule_retained: wire.split_schedule_retained,
            enclosure: wire.enclosure,
            work: wire.work,
        })
    }
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
    /// The deepest the isolation actually descended. Compared against
    /// [`RationalRootCensus::isolation_depth_bound`], this is the whole content of the claim that
    /// the depth is read off the material: the bound is what the discriminant permits, and this is
    /// what the polynomial asked for.
    pub isolation_depth_reached: u64,
}

/// Every rational root of a polynomial over `Q`, reconstructed from one prime receiver by lifting.
///
/// [`rational_root_census`] answers the same question by Sturm bisection on half-integer endpoints
/// from an absolute Cauchy bound. That is complete and needs no factoring, but its descent runs
/// from the bound down to unit width, and the bound is a coefficient of the monic companion
/// `c^(n-1) A(z/c)` — for a degree-eight polynomial whose coefficients carry fifty digits it is
/// three hundred and fifty digits wide, so the descent is a thousand Sturm evaluations on
/// three-hundred-digit rationals per root. Measured 2026-08-27: the section solver of
/// `mordell_weil_realizers` did not return in 175 seconds on the first published family.
///
/// This route reads the root off a **local face and lifts it**. Let `F` be the primitive integer
/// form of the squarefree part, degree `n`, leading `F_n`, constant `F_0 != 0` (a zero root is
/// divided out first). A rational root `a/b` in lowest terms has `b | F_n` and `a | F_0`, so
/// `|a| <= |F_0|` and `b <= |F_n|`. At a prime `p` not dividing `F_n`, the residue `a b^-1` is a
/// root of `F mod p`; when that residue is simple (`F'(r) != 0 mod p`) Newton's step lifts it
/// uniquely to every `p^k`, and once `p^k > 2 |F_0| |F_n|` rational reconstruction recovers
/// `a/b` from the lift uniquely. Every candidate is then **verified by exact evaluation**, so the
/// return is a certificate, not a heuristic; and every simple residue is lifted, so the return is
/// complete at any prime at which every residue root is simple. A prime at which some residue root
/// is not simple divides the discriminant; it is refused by name and the next prime is taken, and
/// there are finitely many such primes.
///
/// Reading: a rational number is a global object seen through one prime receiver as a residue;
/// the lift is transport along the `p`-adic direction, and the reconstruction is the return to the
/// global chart. The exact evaluation is the receiver's check that the returned object is the one
/// the question asked for.
pub fn rational_roots_by_lifting(
    polynomial: &RationalPolynomial,
) -> Result<Vec<Rat>, ExactPolynomialError> {
    let degree = polynomial
        .degree()
        .ok_or(ExactPolynomialError::ZeroPolynomial)?;
    if degree == 0 {
        return Err(ExactPolynomialError::ConstantPolynomial);
    }
    let squarefree = polynomial.squarefree_part()?.primitive_integer_form()?;
    let mut coefficients: Vec<BigInt> = squarefree.coefficients.clone();
    let mut roots: Vec<Rat> = Vec::new();
    while coefficients.first().is_some_and(|c| c.is_zero()) {
        roots.push(Rat::zero());
        coefficients.remove(0);
    }
    if coefficients.len() <= 1 {
        roots.sort();
        roots.dedup();
        return Ok(roots);
    }
    let leading = coefficients.last().cloned().unwrap_or_else(BigInt::one);
    let constant = coefficients.first().cloned().unwrap_or_else(BigInt::one);
    let numerator_bound = constant.abs();
    let denominator_bound = leading.abs();
    let reconstruction_modulus = BigInt::from(2) * &numerator_bound * &denominator_bound;
    let derivative: Vec<BigInt> = coefficients
        .iter()
        .enumerate()
        .skip(1)
        .map(|(index, c)| c * BigInt::from(index))
        .collect();

    let mut prime: u64 = 1009;
    let mut primes_tried = 0usize;
    'primes: loop {
        while !is_small_prime(prime) {
            prime += 2;
        }
        primes_tried += 1;
        if primes_tried > 64 {
            return Err(ExactPolynomialError::LiftingPrimesExhausted);
        }
        let modulus = BigInt::from(prime);
        if (&leading % &modulus).is_zero() {
            prime += 2;
            continue;
        }
        // residue roots, by exhausting the receiver
        let reduced: Vec<u64> = coefficients.iter().map(|c| residue_u64(c, prime)).collect();
        let reduced_derivative: Vec<u64> =
            derivative.iter().map(|c| residue_u64(c, prime)).collect();
        let mut residues = Vec::new();
        // `Z/p` is exhausted, so the receiver's whole population is looked at; `prime` advances
        // only on the way out of this sweep.
        let population = prime;
        for r in 0..population {
            if evaluate_mod_u64(&reduced, r, prime) == 0 {
                if evaluate_mod_u64(&reduced_derivative, r, prime) == 0 {
                    // a non-simple residue: this prime divides the discriminant; take the next
                    prime += 2;
                    continue 'primes;
                }
                residues.push(r);
            }
        }
        // lift each simple residue quadratically until reconstruction is unique
        for residue in residues {
            let mut lifted = BigInt::from(residue);
            let mut lift_modulus = modulus.clone();
            while lift_modulus <= reconstruction_modulus {
                let next_modulus = &lift_modulus * &lift_modulus;
                let value = evaluate_mod_big(&coefficients, &lifted, &next_modulus);
                let slope = evaluate_mod_big(&derivative, &lifted, &lift_modulus);
                let Some(inverse) = inverse_mod_big(&slope, &lift_modulus) else {
                    // cannot happen for a simple residue; refuse rather than guess
                    return Err(ExactPolynomialError::LiftingPrimesExhausted);
                };
                lifted = floor_mod(&(&lifted - value * inverse), &next_modulus);
                lift_modulus = next_modulus;
            }
            if let Some((a, b)) = rational_reconstruction(
                &lifted,
                &lift_modulus,
                &numerator_bound,
                &denominator_bound,
            ) {
                let candidate = Rat::new(a, b);
                if polynomial.evaluate(&candidate).is_zero() {
                    roots.push(candidate);
                }
            }
        }
        break;
    }
    roots.sort();
    roots.dedup();
    Ok(roots)
}

/// The representative of `value` in `[0, modulus)`, for a positive modulus.
fn floor_mod(value: &BigInt, modulus: &BigInt) -> BigInt {
    let residue = value % modulus;
    if residue.is_negative() {
        residue + modulus
    } else {
        residue
    }
}

fn is_small_prime(value: u64) -> bool {
    if value < 2 {
        return false;
    }
    let mut divisor = 2u64;
    while divisor * divisor <= value {
        if value.is_multiple_of(divisor) {
            return false;
        }
        divisor += 1;
    }
    true
}

fn residue_u64(value: &BigInt, prime: u64) -> u64 {
    let modulus = BigInt::from(prime);
    let residue = floor_mod(value, &modulus);
    residue.to_u64_digits().1.first().copied().unwrap_or(0)
}

fn evaluate_mod_u64(coefficients: &[u64], point: u64, prime: u64) -> u64 {
    let mut accumulated: u128 = 0;
    for c in coefficients.iter().rev() {
        accumulated = (accumulated * u128::from(point) + u128::from(*c)) % u128::from(prime);
    }
    accumulated as u64
}

fn evaluate_mod_big(coefficients: &[BigInt], point: &BigInt, modulus: &BigInt) -> BigInt {
    let mut accumulated = BigInt::zero();
    for c in coefficients.iter().rev() {
        accumulated = floor_mod(&(accumulated * point + c), modulus);
    }
    accumulated
}

fn inverse_mod_big(value: &BigInt, modulus: &BigInt) -> Option<BigInt> {
    let (mut old_r, mut r): (BigInt, BigInt) = (floor_mod(value, modulus), modulus.clone());
    let (mut old_t, mut t) = (BigInt::one(), BigInt::zero());
    while !r.is_zero() {
        let quotient = &old_r / &r;
        let next_r = &old_r - &quotient * &r;
        old_r = std::mem::replace(&mut r, next_r);
        let next_t = &old_t - &quotient * &t;
        old_t = std::mem::replace(&mut t, next_t);
    }
    if old_r.is_one() {
        Some(floor_mod(&old_t, modulus))
    } else {
        None
    }
}

/// Wang's rational reconstruction: the unique `a/b` with `|a| <= numerator_bound`,
/// `0 < b <= denominator_bound`, `a = u b (mod m)`, provided `m > 2 · numerator_bound ·
/// denominator_bound`. `None` when no such pair exists, which is itself a return: the lifted
/// residue is not the image of any rational inside the declared bounds.
pub(crate) fn rational_reconstruction(
    u: &BigInt,
    m: &BigInt,
    numerator_bound: &BigInt,
    denominator_bound: &BigInt,
) -> Option<(BigInt, BigInt)> {
    let (mut r0, mut r1) = (m.clone(), floor_mod(u, m));
    let (mut t0, mut t1) = (BigInt::zero(), BigInt::one());
    while r1 > *numerator_bound {
        let quotient = &r0 / &r1;
        let next_r = &r0 - &quotient * &r1;
        r0 = std::mem::replace(&mut r1, next_r);
        let next_t = &t0 - &quotient * &t1;
        t0 = std::mem::replace(&mut t1, next_t);
    }
    if t1.is_zero() {
        return None;
    }
    let (a, b) = if t1.is_negative() {
        (-r1, -t1)
    } else {
        (r1, t1)
    };
    if b > *denominator_bound {
        return None;
    }
    let mut x = a.abs();
    let mut y = b.clone();
    while !y.is_zero() {
        let t = &x % &y;
        x = y;
        y = t;
    }
    if !x.is_one() {
        return None;
    }
    Some((a, b))
}

/// Count and isolate the real roots and return every rational root, exactly.
///
/// The descent runs over [`certified_real_root_enclosure`] of the monic companion: a `k`-th root
/// bound, split positive from negative, each side carrying its own Taylor-shift certificate. See
/// that type for what it replaced and why both R1 and R3 had routed around this owner.
pub fn rational_root_census(
    polynomial: &RationalPolynomial,
) -> Result<RationalRootCensus, ExactPolynomialError> {
    census_within(polynomial, None)
}

/// **Census the roots inside a caller-declared enclosing interval.**
///
/// [definition] The interval is declared **in the polynomial's own variable** and is a claim that
/// every real root lies inside it — the claim a positive semidefinite operator's `[0, tr Δ]`
/// makes. It is *verified*, never believed: it is mapped into the monic companion's variable by the
/// positive leading coefficient, rounded outward to the half-integer grid the descent needs, and
/// each side is put through the same Taylor-shift certificate the owner's own bound passes. A side
/// that does not certify falls back to the owner's bound, so a census can never be made incomplete
/// by a wrong declaration; [`RationalRootCensus::enclosure`] records which side the caller's
/// declaration actually supplied.
pub fn rational_root_census_within(
    polynomial: &RationalPolynomial,
    enclosure: &ExactInterval,
) -> Result<RationalRootCensus, ExactPolynomialError> {
    census_within(polynomial, Some(enclosure))
}

/// **The declared ceiling on the monic companion's coefficient width.**
///
/// [definition] The census descends over `B(z) = c^(n-1) A(z/c)`, whose coefficients are
/// `a_i · c^(n-1-i)`: the companion's widest coefficient carries
///
/// ```text
///   bits(B)  ≤  max_i bits(a_i)  +  (degree − 1) · bits(c)
/// ```
///
/// bits. **That product is a caller-declared extent and it is the one that actually decides the
/// work**: every `leading.pow(exponent)` in the companion, every coefficient of the Sturm chain
/// built over it, and every exact evaluation in the half-integer descent is sized by it. It used to
/// be computed and only then handed to [`IntegerPolynomial::check_declared_size`] — a degree-100
/// polynomial with a sixty-four-bit leading coefficient did not finish in sixty seconds, and an
/// over-ceiling declaration took hundreds of times longer to *refuse* than the gated path did,
/// because the refusal happened after the blow-up rather than before it.
///
/// Four kilobits is about 1230 decimal digits in a single companion coefficient. Every exact
/// spectrum this workspace presents is monic or near-monic — a characteristic polynomial has
/// `c = 1`, so its companion is the polynomial itself and this quantity is `max_i bits(a_i)` — so
/// the ceiling is generous for the material and refuses only the blow-up. Refused by name with
/// [`ExactPolynomialError::MonicCompanionTooWide`], before the companion is formed.
pub const MONIC_COMPANION_BIT_CEILING: u64 = 1 << 12;

/// The predicted width of the monic companion of a primitive integer polynomial, in bits, and the
/// refusal when it is past [`MONIC_COMPANION_BIT_CEILING`] or past the Sturm owner's own ceilings.
///
/// **Taken on declared numbers alone**: no companion is formed, no coefficient is multiplied, and
/// nothing is allocated. This is the whole of the gate, so a test can reach the refusal and know
/// that no blow-up preceded it.
fn check_companion_declared_size(
    primitive: &IntegerPolynomial,
    leading: &BigInt,
) -> Result<u64, ExactPolynomialError> {
    primitive.check_declared_size()?;
    let degree = primitive.degree();
    let widest = primitive
        .coefficients
        .iter()
        .map(BigInt::bits)
        .max()
        .unwrap_or(0);
    let leading_bits = leading.bits();
    let companion_bits = widest.saturating_add(
        (degree as u64)
            .saturating_sub(1)
            .saturating_mul(leading_bits),
    );
    if companion_bits > MONIC_COMPANION_BIT_CEILING {
        return Err(ExactPolynomialError::MonicCompanionTooWide {
            degree,
            leading_bits,
            bits: companion_bits,
            ceiling: MONIC_COMPANION_BIT_CEILING,
        });
    }
    // The companion is what the Sturm chain is actually built over, so the chain's own combined
    // work ceiling is taken against the companion's predicted width rather than the source's.
    check_declared_sturm_work(degree, companion_bits)?;
    Ok(companion_bits)
}

/// `B(z) = c^(n-1) A(z/c)`, the monic companion of a primitive integer polynomial.
///
/// **Call [`check_companion_declared_size`] first.** The `leading.pow(exponent)` below runs the
/// exponent up to `degree - 1`, which is the blow-up that gate exists for; this routine forms the
/// coefficients and nothing else. Factored out so the census and the census's own wire build the
/// same object rather than two transcriptions of it.
fn monic_companion_of(
    primitive: &IntegerPolynomial,
    leading: &BigInt,
) -> Result<IntegerPolynomial, ExactPolynomialError> {
    let degree = primitive.degree();
    if degree == 0 {
        return Err(ExactPolynomialError::ConstantPolynomial);
    }
    let coefficients = primitive
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
    IntegerPolynomial::new(coefficients).map_err(|_| ExactPolynomialError::ZeroPolynomial)
}

fn census_within(
    polynomial: &RationalPolynomial,
    declared: Option<&ExactInterval>,
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
    // **Before the companion is formed.** `coefficient * leading.pow(exponent)` below runs the
    // exponent up to `degree - 1`, so the declared sizes are refused here rather than discovered
    // inside that product.
    check_companion_declared_size(&primitive, &leading)?;
    let monic_companion = monic_companion_of(&primitive, &leading)?;

    // The caller's declaration lives in `A`'s variable; the descent lives in the companion's, and
    // `z = c·t` with `c > 0` by the primitive normalization, so the map preserves order.
    let scale = Rat::from_integer(leading.clone());
    let companion_declaration = declared
        .map(|interval| {
            ExactInterval::new(&interval.lower * &scale, &interval.upper * &scale)
                .map_err(|_| ExactPolynomialError::MalformedInterval)
        })
        .transpose()?;
    let enclosure = certified_enclosure_within(&monic_companion, companion_declaration.as_ref())?;
    let bounding_interval = enclosure.interval.clone();
    let lower = bounding_interval.lower.clone();
    let upper = bounding_interval.upper.clone();

    let mut work = CensusWork::default();
    let companion_chain = monic_companion.sturm_chain()?;
    let distinct_real_roots = sturm_count(&companion_chain, &lower, &upper, &mut work)?;

    let mut integer_roots = Vec::new();
    let mut leaves = Vec::new();
    descend_half_integer(
        &companion_chain,
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

    // The floor of the descent, read off the squarefree part rather than chosen: Mahler's bound
    // from its own discriminant, against the widest leaf the half-integer descent produced and the
    // worst fraction the declared split schedule can retain.
    let separation = root_separation(&squarefree)?;
    let split_schedule_retained =
        worst_retained_fraction(&interior_split_schedule(squarefree.degree()))?;
    let widest_leaf = leaves
        .iter()
        .map(|(leaf_lower, leaf_upper, _)| leaf_upper - leaf_lower)
        .max()
        .unwrap_or_else(Rat::zero);
    let isolation_depth_bound = if widest_leaf.is_positive() {
        separation.splitting_depth(&widest_leaf, &split_schedule_retained)?
    } else {
        0
    };
    // **Before descending.** The depth is read off the caller's own coefficients and nothing
    // bounded it; it sizes both the descent and its worklist, so a bound past this owner's ceiling
    // is refused here rather than taken.
    if isolation_depth_bound > SEPARATION_SPLITTING_DEPTH_CEILING {
        return Err(ExactPolynomialError::SeparationSplittingDepthTooLarge {
            bound: isolation_depth_bound,
            ceiling: SEPARATION_SPLITTING_DEPTH_CEILING,
        });
    }

    let squarefree_chain = squarefree.sturm_chain()?;
    let mut isolated = Vec::new();
    for leaf in &leaves {
        isolate_within(
            &squarefree_chain,
            &separation,
            isolation_depth_bound,
            leaf,
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
        separation,
        isolation_depth_bound,
        split_schedule_retained,
        enclosure,
        work,
    })
}

fn sturm_count(
    chain: &SturmChain,
    lower: &Rat,
    upper: &Rat,
    work: &mut CensusWork,
) -> Result<u32, ExactPolynomialError> {
    work.sturm_counts += 1;
    let interval = ExactInterval::new(lower.clone(), upper.clone())
        .map_err(|_| ExactPolynomialError::MalformedInterval)?;
    chain
        .distinct_root_count(&interval)
        .map_err(|_| ExactPolynomialError::SturmRefused)
}

/// Bisect on half-integer endpoints until every surviving interval has width one, recording the
/// integer roots found and handing the leaves on for isolation.
///
/// A monic integer polynomial has no non-integer rational root, so a half-integer is never a root
/// and every Sturm count below is taken at a legal boundary. That is the whole reason this descent
/// needs no divisor enumeration.
///
/// **The descent is an explicit worklist, not recursion.** The depth is `log2` of the enclosure's
/// width and the enclosure's width comes from the caller's own coefficients, so a recursive form
/// put a caller-sized load on the machine stack: it reached about four thousand frames before its
/// ceiling fired, and on a small-stack thread that is an abort no `Result` can carry.
/// [`isolate_against_chain`] in this same file already carried a worklist for exactly this reason.
/// The ceiling is now checked **before** each descent rather than on the way down, and the
/// worklist holds at most one pending interval per depth, so the memory is bounded by the ceiling
/// too. Depth-first with the left half taken first, so the leaves leave in ascending order —
/// exactly the recursion's order.
fn descend_half_integer(
    chain: &SturmChain,
    lower: &Rat,
    upper: &Rat,
    count: u32,
    integer_roots: &mut Vec<BigInt>,
    leaves: &mut Vec<(Rat, Rat, u32)>,
    work: &mut CensusWork,
) -> Result<(), ExactPolynomialError> {
    // The chain carries the polynomial it belongs to, so there is no second argument to mispair.
    let polynomial = chain.polynomial();
    let two = Rat::from_integer(BigInt::from(2));
    let half = Rat::new(BigInt::one(), BigInt::from(2));
    // Last in, first out; the right half is pushed first so the left is taken first.
    let mut pending: Vec<(Rat, Rat, u32, u32)> =
        vec![(lower.clone(), upper.clone(), count, 0)];
    while let Some((low, high, count, depth)) = pending.pop() {
        if count == 0 {
            continue;
        }
        // **The descent depth is a declared size.** Each step halves the interval, so the depth is
        // `log2` of the enclosure's width, and the enclosure's width comes from the caller's
        // coefficients. It is refused before the step is taken, not after.
        if depth > HALF_INTEGER_DESCENT_CEILING {
            return Err(ExactPolynomialError::HalfIntegerDescentTooDeep {
                ceiling: HALF_INTEGER_DESCENT_CEILING,
            });
        }
        let width = &high - &low;
        if width <= Rat::one() {
            let candidate = (&low + &high) / &two;
            work.exact_evaluations += 1;
            if candidate.is_integer() && polynomial.evaluate(&candidate).is_zero() {
                integer_roots.push(candidate.to_integer());
            }
            leaves.push((low, high, count));
            continue;
        }
        work.bisection_steps += 1;
        let middle = Rat::from_integer(((&low + &high) / &two).floor().to_integer()) + &half;
        if !(low < middle && middle < high) {
            return Err(ExactPolynomialError::BisectionStalled);
        }
        let left = sturm_count(chain, &low, &middle, work)?;
        let right = sturm_count(chain, &middle, &high, work)?;
        if left + right != count {
            return Err(ExactPolynomialError::SturmCountsDisagree);
        }
        pending.push((middle.clone(), high, right, depth + 1));
        pending.push((low, middle, left, depth + 1));
    }
    Ok(())
}

/// **The declared ceiling on a splitting depth derived from the separation bound.**
///
/// [measured] `RootSeparation::splitting_depth` reads its depth off the polynomial's own
/// discriminant, which makes it *material* rather than a budget — but it is material a **caller**
/// supplied, it is returned as an unbounded `u64`, and nothing bounded it: a degree-two polynomial
/// with roots `1/2 ± 2^-(k+1)` derives 7232 at `k = 1000`, and a descent handed that number will
/// take it. The depth sizes both the descent and its worklist — which holds at most one pending
/// interval per depth — so this owner carries a ceiling and refuses **before** descending rather
/// than on the way down.
///
/// **Set against measured material, not chosen.** The bound is a worst case and is almost never
/// approached, so the ceiling is placed above every bound this repository's own material derives
/// rather than above every depth it reaches (release profile):
///
/// ```text
///   polynomial                        derived bound   depth reached
///   x^6 − 2(10^12 x − 1)^2                     1483             158
///   x^6 − 2(10^16 x − 1)^2                     1966             212
///   x^6 − 2(10^100 x − 1)^2                   12105            1326
///   x^6 − 2(10^300 x − 1)^2                   36246            3985
///   x^6 − 2(10^600 x − 1)^2                   72458            7972
///   x^2 + x − 2^4000                          4820               0
///   x^6 + x − 2^4000                         51919               0
/// ```
///
/// `1 << 17` is 131072, above every one of those. The excised hard-coded depth of two hundred is
/// the cautionary case: a *small* ceiling here refuses Mignotte's family, which is genuine
/// material, and that is why this is a hostile-input guard on an unbounded declaration rather than
/// a budget. `x^12 + x − 2^4000` derives about 198000 and is refused by name.
pub const SEPARATION_SPLITTING_DEPTH_CEILING: u64 = 1 << 17;

/// Split a leaf until each surviving interval holds exactly one root of the squarefree part.
///
/// **Both separation refusals below are defect reports, not budget overruns.** The material — the
/// polynomial's own discriminant, through [`root_separation`] — states how narrow an interval has
/// to be before it can hold at most one root, and how many splits at the declared schedule's worst
/// retained fraction reach that width. Passing either means Sturm and the discriminant disagree
/// about the same polynomial. The ceiling on `depth_bound` itself is a different thing and is
/// checked by the caller, once, before any descent starts.
///
/// **The descent is an explicit worklist, not recursion**, for the same reason
/// [`isolate_against_chain`] carries one: `depth_bound` comes from the caller's own coefficients
/// and a recursive form puts that number of frames on the machine stack, which no `Result` can
/// carry. Depth-first, left half first, so the isolating intervals leave in ascending order.
fn isolate_within(
    chain: &SturmChain,
    separation: &RootSeparation,
    depth_bound: u64,
    leaf: &(Rat, Rat, u32),
    isolated: &mut Vec<(Rat, Rat)>,
    work: &mut CensusWork,
) -> Result<(), ExactPolynomialError> {
    // The chain carries its own squarefree polynomial; the leaf carries its interval and its count.
    let squarefree = chain.polynomial();
    let (lower, upper, count) = leaf;
    let mut pending: Vec<(Rat, Rat, u32, u64)> = vec![(lower.clone(), upper.clone(), *count, 0)];
    while let Some((low, high, count, depth)) = pending.pop() {
        if count == 0 {
            continue;
        }
        work.isolation_depth_reached = work.isolation_depth_reached.max(depth);
        if count == 1 {
            isolated.push((low, high));
            continue;
        }
        // The sharp form, independent of any schedule: an interval this narrow cannot hold two
        // roots.
        if separation.holds_at_most_one_root(&(&high - &low)) {
            return Err(ExactPolynomialError::SeparationBoundContradicted { count });
        }
        if depth >= depth_bound {
            return Err(ExactPolynomialError::IsolationPastTheSeparationBound { depth_bound });
        }
        let middle = interior_non_root(squarefree, &low, &high, work)?;
        work.bisection_steps += 1;
        let left = sturm_count(chain, &low, &middle, work)?;
        let right = sturm_count(chain, &middle, &high, work)?;
        if left + right != count {
            return Err(ExactPolynomialError::SturmCountsDisagree);
        }
        pending.push((middle.clone(), high, right, depth + 1));
        pending.push((low, middle, left, depth + 1));
    }
    Ok(())
}

/// A point strictly inside `(lower, upper)` at which the polynomial does not vanish.
///
/// The candidates come from [`interior_split_schedule`], which reads their count off the degree:
/// a polynomial of degree `d` has at most `d` roots, so `d + 1` distinct interior points cannot all
/// be roots. `NoInteriorNonRoot` is therefore unreachable for a genuine polynomial and is retained
/// as the defect report it is.
fn interior_non_root(
    squarefree: &IntegerPolynomial,
    lower: &Rat,
    upper: &Rat,
    work: &mut CensusWork,
) -> Result<Rat, ExactPolynomialError> {
    let width = upper - lower;
    for fraction in interior_split_schedule(squarefree.degree()) {
        let point = lower + &width * fraction;
        work.exact_evaluations += 1;
        if !squarefree.evaluate(&point).is_zero() {
            return Ok(point);
        }
    }
    Err(ExactPolynomialError::NoInteriorNonRoot)
}


// -------------------------------------------------------------------------------------------------
// counting roots by half-plane: Routh-Hurwitz in its Sturm form
// -------------------------------------------------------------------------------------------------

/// **How far [`half_plane_count`] may halve its shift before refusing.**
///
/// The loop terminates as mathematics — there are finitely many distinct real parts — so this is a
/// hostile-input guard and not an approximation budget. A polynomial that exhausts it returns
/// [`ExactPolynomialError::HalfPlaneRefinementExhausted`] naming the reached depth.
pub const HALF_PLANE_REFINEMENT_CEILING: u32 = 96;

/// The exact population of a real polynomial's roots by half-plane, with multiplicity.
/// **The three populations partition the roots with multiplicity**, so the wire checks that they
/// sum to the declared degree. [`HalfPlaneCount::is_hurwitz`] is a stability reading taken straight
/// off these numbers; a wire that carried three unrelated integers could report a Hurwitz operator
/// that is not one.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "HalfPlaneCountWire")]
pub struct HalfPlaneCount {
    pub degree: usize,
    /// `Re λ < 0`.
    pub left: usize,
    /// `Re λ = 0`.
    pub axis: usize,
    /// `Re λ > 0`.
    pub right: usize,
    /// The rational shift at which the counts closed. `None` for the inertia route, where no shift
    /// is needed because the spectrum is real.
    pub shift_witness: Option<Rat>,
    /// How many halvings the shift needed. Zero on the first try.
    pub refinements: u32,
}

#[derive(Deserialize)]
struct HalfPlaneCountWire {
    degree: usize,
    left: usize,
    axis: usize,
    right: usize,
    shift_witness: Option<Rat>,
    refinements: u32,
}

impl TryFrom<HalfPlaneCountWire> for HalfPlaneCount {
    type Error = ExactPolynomialError;

    fn try_from(wire: HalfPlaneCountWire) -> Result<Self, Self::Error> {
        let total = wire
            .left
            .checked_add(wire.axis)
            .and_then(|partial| partial.checked_add(wire.right));
        if total != Some(wire.degree) {
            return Err(ExactPolynomialError::MalformedHalfPlaneCount {
                degree: wire.degree,
                left: wire.left,
                axis: wire.axis,
                right: wire.right,
            });
        }
        if wire.refinements > HALF_PLANE_REFINEMENT_CEILING {
            return Err(ExactPolynomialError::HalfPlaneRefinementExhausted {
                ceiling: HALF_PLANE_REFINEMENT_CEILING,
            });
        }
        Ok(Self {
            degree: wire.degree,
            left: wire.left,
            axis: wire.axis,
            right: wire.right,
            shift_witness: wire.shift_witness,
            refinements: wire.refinements,
        })
    }
}

impl HalfPlaneCount {
    pub fn total(&self) -> usize {
        self.left + self.axis + self.right
    }

    /// Every mode decays: the whole spectrum is in the open left half-plane.
    pub fn is_hurwitz(&self) -> bool {
        self.degree > 0 && self.left == self.degree
    }
}

/// `p(iω) = P(ω) + i Q(ω)`, as two real polynomials.
fn imaginary_axis_parts(
    polynomial: &RationalPolynomial,
) -> (RationalPolynomial, RationalPolynomial) {
    let coefficients = polynomial.coefficients();
    let mut real = vec![Rat::zero(); coefficients.len()];
    let mut imaginary = vec![Rat::zero(); coefficients.len()];
    for (power, coefficient) in coefficients.iter().enumerate() {
        // `i^power` cycles `1, i, −1, −i`.
        match power % 4 {
            0 => real[power] = coefficient.clone(),
            1 => imaginary[power] = coefficient.clone(),
            2 => real[power] = -coefficient,
            _ => imaginary[power] = -coefficient,
        }
    }
    (
        RationalPolynomial::new(real),
        RationalPolynomial::new(imaginary),
    )
}

/// The number of distinct real roots, over the certified enclosure of this owner.
///
/// The enclosure's endpoints are half-integers strictly past a certified bound on the roots, so
/// they can never be roots themselves, which is what
/// [`crate::exact_value::SturmChain::distinct_root_count`] requires.
pub fn distinct_real_root_count(
    polynomial: &RationalPolynomial,
) -> Result<u32, ExactPolynomialError> {
    let Some(degree) = polynomial.degree() else {
        return Err(ExactPolynomialError::ZeroPolynomial);
    };
    if degree == 0 {
        return Ok(0);
    }
    let primitive = polynomial.primitive_integer_form()?;
    let enclosure = certified_real_root_enclosure(&primitive)?;
    Ok(primitive
        .sturm_chain()?
        .distinct_root_count(&enclosure.interval)?)
}

/// The number of real roots **with multiplicity**.
pub fn real_root_count_with_multiplicity(
    polynomial: &RationalPolynomial,
) -> Result<usize, ExactPolynomialError> {
    if polynomial.is_zero() {
        return Err(ExactPolynomialError::ZeroPolynomial);
    }
    if polynomial.degree() == Some(0) {
        return Ok(0);
    }
    let mut total = 0usize;
    for (multiplicity, factor) in polynomial.squarefree_decomposition()? {
        let distinct = distinct_real_root_count(&factor)? as usize;
        total = total
            .checked_add(
                distinct
                    .checked_mul(multiplicity as usize)
                    .ok_or(ExactPolynomialError::DegreeTooLarge)?,
            )
            .ok_or(ExactPolynomialError::DegreeTooLarge)?;
    }
    Ok(total)
}

/// The number of roots of `p` on the imaginary axis, with multiplicity.
///
/// If `p` has a root `iω₀` of order `m` then `p(iω)` has a zero of order `m` at the real point
/// `ω₀`, so `(ω−ω₀)^m` divides both `P` and `Q` and at least one of the two order-`m` coefficients
/// is nonzero — hence **the multiplicity of `iω₀` in `p` is exactly the multiplicity of `ω₀` as a
/// real root of `gcd(P,Q)`**.
pub fn axis_root_count(polynomial: &RationalPolynomial) -> Result<usize, ExactPolynomialError> {
    if polynomial.is_zero() {
        return Err(ExactPolynomialError::ZeroPolynomial);
    }
    let (real, imaginary) = imaginary_axis_parts(polynomial);
    let common = match (real.is_zero(), imaginary.is_zero()) {
        (true, true) => return Err(ExactPolynomialError::ZeroPolynomial),
        (true, false) => imaginary,
        (false, true) => real,
        (false, false) => real.monic_gcd(&imaginary)?,
    };
    real_root_count_with_multiplicity(&common)
}

/// **The Cauchy index `I_{−∞}^{+∞}(numerator / denominator)`, exactly.**
///
/// `V(−∞) − V(+∞)` over the signed remainder sequence `f_0 = denominator`, `f_1 = numerator`,
/// `f_{i+1} = −rem(f_{i−1}, f_i)`. The sequence is built over `Z` by
/// [`crate::exact_value::SturmChain::from_pair`], with the same positive-multiple sign discipline
/// the Sturm chain uses: a sign at `±∞` is a leading coefficient's sign with a parity flip, and a
/// positive rescaling cannot move it.
pub fn cauchy_index(
    numerator: &RationalPolynomial,
    denominator: &RationalPolynomial,
) -> Result<i64, ExactPolynomialError> {
    if denominator.is_zero() {
        return Err(ExactPolynomialError::ZeroPolynomial);
    }
    if numerator.is_zero() {
        return Ok(0);
    }
    // **The two signs are relative, so neither is normalized.** Flipping the numerator and not the
    // denominator flips the index; `primitive_integer_form` would do exactly that.
    let chain = SturmChain::from_pair(
        &denominator.signed_primitive_integer_form()?,
        &numerator.signed_primitive_integer_form()?,
    )?;
    Ok(chain.cauchy_index())
}

/// The open-right-half-plane root count of a polynomial **with no roots on the imaginary axis**.
///
/// The argument principle on the half-plane contour gives `Δ arg p(iω) = π(n − 2k)` for `k` the
/// right-half-plane count; writing the continuous argument against `arctan` and counting the jumps
/// of the ratio at the denominator's zeros gives `k = (n + I(Q/P))/2` for `n` even and
/// `k = (n − I(P/Q))/2` for `n` odd.
fn right_half_plane_count_axis_free(
    polynomial: &RationalPolynomial,
) -> Result<usize, ExactPolynomialError> {
    let Some(degree) = polynomial.degree() else {
        return Err(ExactPolynomialError::ZeroPolynomial);
    };
    if degree == 0 {
        return Ok(0);
    }
    let (real, imaginary) = imaginary_axis_parts(polynomial);
    let index = if degree % 2 == 0 {
        cauchy_index(&imaginary, &real)?
    } else {
        -cauchy_index(&real, &imaginary)?
    };
    let doubled = degree as i64 + index;
    if doubled < 0 || doubled % 2 != 0 {
        return Err(ExactPolynomialError::HalfPlaneParityFailure { degree, index });
    }
    Ok((doubled / 2) as usize)
}

/// **The exact half-plane population of a real polynomial's roots, with multiplicity.**
///
/// [proved-derived; implemented-exact] Three steps, none of them a tolerance:
///
/// 1. **Axis roots, with multiplicity**, from [`axis_root_count`].
/// 2. **Left and right, by the Cauchy index** of the signed remainder sequence — Routh–Hurwitz in
///    its Sturm form — through [`cauchy_index`].
/// 3. **The shift, with a self-certifying stop.** `p` itself may have axis roots, so the left and
///    right counts are read at a rational shift `σ > 0`: `#{Re λ < −σ}` from `p(s−σ)` and
///    `#{Re λ > σ}` from `p(s+σ)`. The loop halves `σ` until `left + axis + right = n`, which is
///    exactly the certificate that no non-axis root has `|Re λ| ≤ σ`. It terminates because there
///    are finitely many distinct real parts, and it carries
///    [`HALF_PLANE_REFINEMENT_CEILING`] so a hostile polynomial returns a named refusal rather than
///    running forever.
///
/// [definition] **This is the one owner.** `causal_chord::half_plane_count` is a thin re-entry into
/// it that maps the refusal into that module's own species; there is no second implementation.
/// When the operator is symmetric the whole question is already answered by Sylvester's signature
/// and `causal_chord::half_plane_from_symmetric` routes to `crate::inertia::inertia` instead. The
/// two are held to exact agreement by
/// `receiver::causal_chord::tests::the_half_plane_count_agrees_with_the_inertia_of_a_symmetric_operator`.
pub fn half_plane_count(
    polynomial: &RationalPolynomial,
) -> Result<HalfPlaneCount, ExactPolynomialError> {
    let Some(degree) = polynomial.degree() else {
        return Err(ExactPolynomialError::ZeroPolynomial);
    };
    if degree == 0 {
        return Ok(HalfPlaneCount::default());
    }
    let axis = axis_root_count(polynomial)?;
    let mut shift = Rat::one();
    let two = Rat::from_integer(BigInt::from(2));
    for refinements in 0..HALF_PLANE_REFINEMENT_CEILING {
        let towards_left =
            polynomial.composed_with(&RationalPolynomial::new(vec![-shift.clone(), Rat::one()]));
        let towards_right =
            polynomial.composed_with(&RationalPolynomial::new(vec![shift.clone(), Rat::one()]));
        if axis_root_count(&towards_left)? == 0 && axis_root_count(&towards_right)? == 0 {
            let right = right_half_plane_count_axis_free(&towards_right)?;
            let left = degree - right_half_plane_count_axis_free(&towards_left)?;
            if left + axis + right == degree {
                return Ok(HalfPlaneCount {
                    degree,
                    left,
                    axis,
                    right,
                    shift_witness: Some(shift),
                    refinements,
                });
            }
        }
        shift /= &two;
    }
    Err(ExactPolynomialError::HalfPlaneRefinementExhausted {
        ceiling: HALF_PLANE_REFINEMENT_CEILING,
    })
}

/// One polynomial in two variables, presented as a polynomial in the variable that will be
/// eliminated whose coefficients live in `Q[t]`.
/// The wire enforces the same trimmed normal form [`BivariatePolynomial::new`] produces, for the
/// same reason [`RationalPolynomial`]'s does: `degree()` is read off the coefficient count.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "BivariatePolynomialWire")]
pub struct BivariatePolynomial {
    coefficients: Vec<RationalPolynomial>,
}

#[derive(Deserialize)]
struct BivariatePolynomialWire {
    coefficients: Vec<RationalPolynomial>,
}

impl TryFrom<BivariatePolynomialWire> for BivariatePolynomial {
    type Error = ExactPolynomialError;

    fn try_from(wire: BivariatePolynomialWire) -> Result<Self, Self::Error> {
        if wire.coefficients.last().is_some_and(RationalPolynomial::is_zero) {
            return Err(ExactPolynomialError::UntrimmedPolynomialWire {
                declared: wire.coefficients.len(),
            });
        }
        Ok(Self::new(wire.coefficients))
    }
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

/// The monic gcd of two polynomials over `Q`, computed modulo word primes.
///
/// The Euclidean remainder sequence over `Q` grows its coefficients exponentially in the
/// degree, which is why `monic_gcd` is unusable past a few dozen degrees with large
/// coefficients. The image of the sequence modulo a prime does not grow at all. For every prime
/// dividing neither leading coefficient of the primitive integer forms, the gcd of the images has
/// degree **at least** that of the true gcd, with equality except at finitely many unlucky
/// primes; the minimal-degree rule discards the unlucky ones as soon as a luckier prime appears.
/// Each monic image is scaled by the gcd of the two leading coefficients — which the true gcd's
/// leading coefficient divides — so the integer combination is well defined, combined by the
/// Chinese remainder theorem in the symmetric range, and **admitted only when its primitive part
/// divides both inputs exactly**. A candidate that does not divide is refused by the division,
/// never returned; the return is bit-identical to `monic_gcd`.
pub fn modular_monic_gcd(
    left: &RationalPolynomial,
    right: &RationalPolynomial,
) -> Result<RationalPolynomial, ExactPolynomialError> {
    if left.is_zero() {
        return Ok(right.made_monic());
    }
    if right.is_zero() {
        return Ok(left.made_monic());
    }
    let a = left.primitive_integer_form()?.coefficients;
    let b = right.primitive_integer_form()?.coefficients;
    if a.len() == 1 || b.len() == 1 {
        return Ok(RationalPolynomial::one());
    }
    let lead = integer_gcd(a.last().unwrap(), b.last().unwrap());
    let lead_product = a.last().unwrap() * b.last().unwrap();
    let mut prime: u64 = 0x7fff_ffff;
    let mut best_degree = usize::MAX;
    let mut modulus = BigInt::one();
    let mut combined: Vec<BigInt> = Vec::new();
    let mut previous: Option<Vec<BigInt>> = None;
    for _ in 0..4096 {
        while !is_small_prime(prime) || residue_u64(&lead_product, prime) == 0 {
            prime -= 2;
        }
        let image = gcd_mod_prime(
            a.iter().map(|c| residue_u64(c, prime)).collect(),
            b.iter().map(|c| residue_u64(c, prime)).collect(),
            prime,
        );
        let degree = image.len() - 1;
        if degree == 0 {
            return Ok(RationalPolynomial::one());
        }
        if degree > best_degree {
            prime -= 2;
            continue;
        }
        if degree < best_degree {
            best_degree = degree;
            modulus = BigInt::one();
            combined = vec![BigInt::zero(); degree + 1];
            previous = None;
        }
        let lead_p = residue_u64(&lead, prime);
        let scaled: Vec<u64> = image
            .iter()
            .map(|c| ((u128::from(*c) * u128::from(lead_p)) % u128::from(prime)) as u64)
            .collect();
        let prime_big = BigInt::from(prime);
        let inverse = inverse_mod_big(&modulus, &prime_big).expect("coprime moduli");
        let next_modulus = &modulus * &prime_big;
        let half = &next_modulus / 2;
        for (c, r) in combined.iter_mut().zip(scaled.iter()) {
            let residue = floor_mod(c, &prime_big);
            let step = floor_mod(&((BigInt::from(*r) - residue) * &inverse), &prime_big);
            let mut lifted = floor_mod(&(&*c + &modulus * step), &next_modulus);
            if lifted > half {
                lifted -= &next_modulus;
            }
            *c = lifted;
        }
        modulus = next_modulus;
        if previous.as_ref() == Some(&combined) {
            let candidate = RationalPolynomial::from_integers(&combined).made_monic();
            let (_, ra) = left.divided_by(&candidate)?;
            let (_, rb) = right.divided_by(&candidate)?;
            if ra.is_zero() && rb.is_zero() {
                return Ok(candidate);
            }
        }
        previous = Some(combined.clone());
        prime -= 2;
    }
    Err(ExactPolynomialError::LiftingPrimesExhausted)
}

/// The monic gcd of two polynomials over `F_p`, ascending coefficients, for a word prime.
fn gcd_mod_prime(mut a: Vec<u64>, mut b: Vec<u64>, prime: u64) -> Vec<u64> {
    fn trim(v: &mut Vec<u64>) {
        while v.last() == Some(&0) {
            v.pop();
        }
    }
    fn power_mod(mut base: u64, mut exponent: u64, prime: u64) -> u64 {
        let mut result: u64 = 1;
        base %= prime;
        while exponent > 0 {
            if exponent & 1 == 1 {
                result = ((u128::from(result) * u128::from(base)) % u128::from(prime)) as u64;
            }
            base = ((u128::from(base) * u128::from(base)) % u128::from(prime)) as u64;
            exponent >>= 1;
        }
        result
    }
    trim(&mut a);
    trim(&mut b);
    while !b.is_zero_poly() {
        // a ← a mod b
        let inverse = power_mod(*b.last().unwrap(), prime - 2, prime);
        while a.len() >= b.len() && !a.is_empty() {
            let shift = a.len() - b.len();
            let factor =
                ((u128::from(*a.last().unwrap()) * u128::from(inverse)) % u128::from(prime)) as u64;
            for (k, c) in b.iter().enumerate() {
                let sub = ((u128::from(*c) * u128::from(factor)) % u128::from(prime)) as u64;
                a[shift + k] = (a[shift + k] + prime - sub) % prime;
            }
            trim(&mut a);
        }
        std::mem::swap(&mut a, &mut b);
    }
    let inverse = power_mod(*a.last().unwrap(), prime - 2, prime);
    a.iter()
        .map(|c| ((u128::from(*c) * u128::from(inverse)) % u128::from(prime)) as u64)
        .collect()
}

trait ZeroPoly {
    fn is_zero_poly(&self) -> bool;
}
impl ZeroPoly for Vec<u64> {
    fn is_zero_poly(&self) -> bool {
        self.is_empty()
    }
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
    #[error("no prime among the first sixty-four tried left every residue root simple")]
    LiftingPrimesExhausted,
    #[error("Sturm counts on the two halves did not sum to the count on the whole")]
    SturmCountsDisagree,
    #[error("bisection produced a midpoint outside its own interval")]
    BisectionStalled,
    #[error("no declared interior candidate avoided the root set")]
    NoInteriorNonRoot,
    #[error(
        "root isolation passed the {depth_bound} splits the root separation bound derived from the discriminant permits; Sturm and the discriminant disagree about this polynomial"
    )]
    IsolationPastTheSeparationBound { depth_bound: u64 },
    #[error(
        "an interval no wider than the root separation bound still reported {count} distinct roots; Sturm and the discriminant contradict each other"
    )]
    SeparationBoundContradicted { count: u32 },
    #[error(
        "a discriminant needs degree at least two, and this polynomial has degree {degree}: a linear polynomial has no pair of roots to separate"
    )]
    DiscriminantDegreeTooLow { degree: usize },
    #[error("the discriminant of an integer polynomial came out non-integral")]
    NonIntegralDiscriminant,
    #[error(
        "the discriminant vanished, so the polynomial is not squarefree and Mahler's bound does not apply to it"
    )]
    VanishingDiscriminant,
    #[error("a split schedule fraction is not strictly inside (0, 1)")]
    InvalidSplitFraction,
    #[error("a split schedule with no candidates retains everything")]
    EmptySplitSchedule,
    #[error(
        "a shrinking count needs a positive width, a positive target, and a retained fraction strictly inside (0, 1)"
    )]
    InvalidShrinkingStep,
    #[error("a degree or exponent exceeded what an exact power can carry")]
    DegreeTooLarge,
    #[error("root isolation was refused by the Sturm certificate")]
    IsolationRefused,
    #[error("a censused rational root did not vanish on the source polynomial")]
    CensusRootDoesNotVanish,
    #[error(
        "a root enclosure whose interval does not agree with its own bounds, or whose bounds are \
         not positive, is not an enclosure and is refused at the boundary"
    )]
    MalformedRootEnclosure,
    #[error(
        "the half-integer descent passed its declared depth ceiling of {ceiling}; the enclosure is \
         wider than a recursive descent may be asked to halve"
    )]
    HalfIntegerDescentTooDeep { ceiling: u32 },
    #[error(
        "a certified root bound did not close after {ceiling} doublings; the polynomial is refused \
         rather than enclosed by an unverified bound"
    )]
    RootBoundDoublingExhausted { ceiling: u32 },
    #[error(
        "a declared isolation depth of {bound} is past this owner's ceiling of {ceiling}: the \
         depth sizes both the descent and its worklist, so it is refused rather than accepted"
    )]
    IsolationDepthBoundTooLarge { bound: u32, ceiling: u32 },
    #[error("root isolation passed the declared depth bound of {bound}")]
    IsolationDepthExceeded { bound: u32 },
    #[error(
        "the root separation bound derived a splitting depth of {bound}, past this owner's ceiling \
         of {ceiling}: the depth sizes both the descent and its worklist, so it is refused before \
         the descent rather than taken"
    )]
    SeparationSplittingDepthTooLarge { bound: u64, ceiling: u64 },
    #[error(
        "the monic companion of a degree-{degree} polynomial with a {leading_bits}-bit leading \
         coefficient carries coefficients of up to {bits} bits, past the declared ceiling of \
         {ceiling}: the companion is refused before it is formed rather than after"
    )]
    MonicCompanionTooWide {
        degree: usize,
        leading_bits: u64,
        bits: u64,
        ceiling: u64,
    },
    #[error(
        "a remounted rational polynomial declares {declared} coefficients whose leading entry is \
         zero; the constructor trims that away, so the declaration names a degree one higher than \
         the polynomial has and is refused rather than re-normalized"
    )]
    UntrimmedPolynomialWire { declared: usize },
    #[error(
        "a remounted root separation does not agree with the bound its own material derives, or \
         claims there is no pair of roots to separate at a degree that has one"
    )]
    MalformedRootSeparation,
    #[error(
        "a remounted half-plane count puts {left} + {axis} + {right} roots into a degree-{degree} \
         polynomial; the three populations partition the roots with multiplicity, so the \
         declaration is refused"
    )]
    MalformedHalfPlaneCount {
        degree: usize,
        left: usize,
        axis: usize,
        right: usize,
    },
    #[error(
        "a remounted censused root carries the rational value {value}, which is not a root of the \
         polynomial inside its own isolating interval"
    )]
    CensusedRootValueDisagrees { value: String },
    #[error(
        "a remounted census does not agree with itself: {clause}"
    )]
    MalformedCensus { clause: &'static str },
    #[error(
        "the half-plane count did not close after {ceiling} shift refinements; the polynomial is \
         refused rather than reported from an unclosed count"
    )]
    HalfPlaneRefinementExhausted { ceiling: u32 },
    #[error("the Cauchy index {index} has the wrong parity against degree {degree}")]
    HalfPlaneParityFailure { degree: usize, index: i64 },
    #[error(transparent)]
    Value(#[from] ExactValueError),
}

#[cfg(test)]
#[path = "rational_polynomial/tests.rs"]
mod tests;
