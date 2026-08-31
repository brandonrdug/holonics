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
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_value::{AlgebraicRoot, ExactInterval, IntegerPolynomial};

mod root_separation;
pub use root_separation::{RootSeparation, RootSeparationBound};

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
    /// Mahler's bound on the squared distance between two roots of the squarefree part, read off
    /// its own discriminant. This is what decides how far the isolation is allowed to descend.
    pub separation: RootSeparation,
    /// The splits the bound above permits, given the widest leaf the half-integer descent handed on
    /// and the worst fraction the declared split schedule can retain. A recursion that passes this
    /// is a contradiction, not an exhausted budget.
    pub isolation_depth_bound: u64,
    /// The worst fraction either child of a split may retain, read off the split schedule.
    pub split_schedule_retained: Rat,
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
        for r in 0..prime {
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
        if value % divisor == 0 {
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
fn rational_reconstruction(
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

    let mut isolated = Vec::new();
    for (leaf_lower, leaf_upper, count) in leaves {
        isolate_within(
            &squarefree,
            &separation,
            isolation_depth_bound,
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
        separation,
        isolation_depth_bound,
        split_schedule_retained,
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

/// Split a leaf until each surviving interval holds exactly one root of the squarefree part.
///
/// **Both refusals below are defect reports, not budget overruns.** The material — the polynomial's
/// own discriminant, through [`root_separation`] — states how narrow an interval has to be before
/// it can hold at most one root, and how many splits at the declared schedule's worst retained
/// fraction reach that width. Passing either means Sturm and the discriminant disagree about the
/// same polynomial.
#[allow(clippy::too_many_arguments)]
fn isolate_within(
    squarefree: &IntegerPolynomial,
    separation: &RootSeparation,
    depth_bound: u64,
    lower: &Rat,
    upper: &Rat,
    count: u32,
    depth: u64,
    isolated: &mut Vec<(Rat, Rat)>,
    work: &mut CensusWork,
) -> Result<(), ExactPolynomialError> {
    if count == 0 {
        return Ok(());
    }
    work.isolation_depth_reached = work.isolation_depth_reached.max(depth);
    if count == 1 {
        isolated.push((lower.clone(), upper.clone()));
        return Ok(());
    }
    // The sharp form, independent of any schedule: an interval this narrow cannot hold two roots.
    if separation.holds_at_most_one_root(&(upper - lower)) {
        return Err(ExactPolynomialError::SeparationBoundContradicted { count });
    }
    if depth >= depth_bound {
        return Err(ExactPolynomialError::IsolationPastTheSeparationBound { depth_bound });
    }
    let middle = interior_non_root(squarefree, lower, upper, work)?;
    work.bisection_steps += 1;
    let left = sturm_count(squarefree, lower, &middle, work)?;
    let right = sturm_count(squarefree, &middle, upper, work)?;
    if left + right != count {
        return Err(ExactPolynomialError::SturmCountsDisagree);
    }
    isolate_within(
        squarefree,
        separation,
        depth_bound,
        lower,
        &middle,
        left,
        depth + 1,
        isolated,
        work,
    )?;
    isolate_within(
        squarefree,
        separation,
        depth_bound,
        &middle,
        upper,
        right,
        depth + 1,
        isolated,
        work,
    )
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
}

#[cfg(test)]
#[path = "rational_polynomial/tests.rs"]
mod tests;
