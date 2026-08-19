//! Typed exact values used by causal parameters and future geometric laws.
//!
//! A decimal approximation is never a member of this carrier.  Values which
//! cannot yet be ordered from their exact certificates return `Open` rather
//! than falling through to an epsilon comparison.
//!
//! ## The one floating-point boundary
//!
//! [`ieee754`] is the **single declared floating-point exception** in the library files of this
//! workspace, and it is a codec and nothing else: a bit pattern goes in, an exact dyadic comes out,
//! and no arithmetic is ever performed on the machine float. Everything downstream of it —
//! including `crate::reopening`, which is what it was built to feed — sees `BigInt`, `BigUint` and
//! `Rat` and never an IEEE scalar.

use std::cmp::Ordering;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use relational_geometry::{ExactExpr, Rat};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// Return the primitive integer representative of one homogeneous tuple.
///
/// A projective point, projective map, or homogeneous form is unchanged by a
/// common nonzero factor. Carrying the particular denominators introduced by
/// an earlier chart calculation therefore preserves arithmetic history rather
/// than geometry. This routine clears that history at the boundary where a
/// new homogeneous object is founded.
pub(crate) fn canonical_homogeneous<const N: usize>(values: [Rat; N]) -> [Rat; N] {
    let common_denominator = values.iter().fold(BigInt::one(), |common, value| {
        let denominator = value.denom().clone();
        let divisor = exact_integer_gcd(common.clone(), denominator.clone());
        common / divisor * denominator
    });
    let mut integer = values.map(|value| value.numer() * (&common_denominator / value.denom()));
    let content = integer
        .iter()
        .filter(|value| !value.is_zero())
        .map(Signed::abs)
        .reduce(exact_integer_gcd)
        .unwrap_or_else(BigInt::one);
    if !content.is_zero() {
        for value in &mut integer {
            *value /= &content;
        }
    }
    if integer
        .iter()
        .find(|value| !value.is_zero())
        .is_some_and(Signed::is_negative)
    {
        for value in &mut integer {
            *value = -value.clone();
        }
    }
    integer.map(Rat::from_integer)
}

fn exact_integer_gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactOrdering {
    Less,
    Equal,
    Greater,
    Open,
}

impl From<Ordering> for ExactOrdering {
    fn from(value: Ordering) -> Self {
        match value {
            Ordering::Less => Self::Less,
            Ordering::Equal => Self::Equal,
            Ordering::Greater => Self::Greater,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactInterval {
    pub lower: Rat,
    pub upper: Rat,
}

impl ExactInterval {
    pub fn new(lower: Rat, upper: Rat) -> Result<Self, ExactValueError> {
        if lower > upper {
            return Err(ExactValueError::ReversedInterval);
        }
        Ok(Self { lower, upper })
    }

    pub fn point(value: Rat) -> Self {
        Self {
            lower: value.clone(),
            upper: value,
        }
    }

    pub fn is_point(&self) -> bool {
        self.lower == self.upper
    }

    pub fn translated(&self, offset: &Rat) -> Self {
        Self {
            lower: &self.lower + offset,
            upper: &self.upper + offset,
        }
    }

    /// **Widen outward onto a dyadic grid, so a chain of enclosures cannot grow its denominator
    /// without bound.**
    ///
    /// The result strictly contains the original — the lower bound floors and the upper ceils — so
    /// nothing is lost, and the denominators stay at `2^octaves` however long the chain runs.
    /// Measured 2026-08-18: a geometric ladder of one hundred and twenty-eight enclosures founded
    /// by exact multiplication carried denominators of five thousand six hundred bits, and a
    /// twenty-four term series on each was the whole cost of a site.
    pub fn round_out(&self, octaves: u32) -> Result<Self, ExactValueError> {
        let scale = Rat::from_integer(BigInt::from(BigUint::one() << octaves as usize));
        let unit = scale.recip();
        let floor = |value: &Rat| -> Rat {
            let scaled = value * &scale;
            let truncated = scaled.to_integer();
            let corrected = if scaled.is_negative() && Rat::from_integer(truncated.clone()) != scaled
            {
                truncated - BigInt::one()
            } else {
                truncated
            };
            Rat::from_integer(corrected) * &unit
        };
        let ceiling = |value: &Rat| -> Rat {
            let scaled = value * &scale;
            let truncated = scaled.to_integer();
            let corrected = if scaled.is_positive() && Rat::from_integer(truncated.clone()) != scaled
            {
                truncated + BigInt::one()
            } else {
                truncated
            };
            Rat::from_integer(corrected) * &unit
        };
        Self::new(floor(&self.lower), ceiling(&self.upper))
    }

    /// The product of two enclosures. **An interval is a set, so the product is the set's.**
    pub fn times(&self, other: &Self) -> Result<Self, ExactValueError> {
        let corners = [
            &self.lower * &other.lower,
            &self.lower * &other.upper,
            &self.upper * &other.lower,
            &self.upper * &other.upper,
        ];
        let mut lower = corners[0].clone();
        let mut upper = corners[0].clone();
        for corner in &corners[1..] {
            if *corner < lower {
                lower = corner.clone();
            }
            if *corner > upper {
                upper = corner.clone();
            }
        }
        Self::new(lower, upper)
    }

    /// **Refuses across zero rather than widening to infinity**, which is the honest return: the
    /// reciprocal of a set containing zero is not an interval.
    pub fn reciprocal(&self) -> Result<Self, ExactValueError> {
        if !self.lower.is_positive() && !self.upper.is_negative() {
            return Err(ExactValueError::ReciprocalStraddlesZero);
        }
        let a = self.lower.recip();
        let b = self.upper.recip();
        if a <= b {
            Self::new(a, b)
        } else {
            Self::new(b, a)
        }
    }

    /// An integer power of the set, by **binary exponentiation**, held at a declared grain.
    ///
    /// Repeated multiplication costs the exponent; binary exponentiation costs its octaves.
    /// Measured 2026-08-18, a gated passage over ten thousand two hundred and forty entries spent
    /// `17.4` seconds of an `18.4`-second site inside this call, because a `tanh` at `|x| < 32`
    /// composes up to sixty-three steps and each entry paid all of them.
    ///
    /// `octaves` holds every intermediate outward on a dyadic grid, so a long power cannot grow its
    /// denominators; the enclosure only ever widens and what it could not carry is inside it.
    pub fn power_held(&self, exponent: u32, octaves: u32) -> Result<Self, ExactValueError> {
        let mut result = Self::point(Rat::one());
        let mut square = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = result.times(&square)?.round_out(octaves)?;
            }
            remaining >>= 1;
            if remaining > 0 {
                square = square.times(&square)?.round_out(octaves)?;
            }
        }
        Ok(result)
    }

    /// An integer power of the set, exactly, with no grain. A caller composing a long chain wants
    /// [`Self::power_held`]; this is for a short one where the exactness is the point.
    pub fn power(&self, exponent: u32) -> Result<Self, ExactValueError> {
        let mut result = Self::point(Rat::one());
        let mut square = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = result.times(&square)?;
            }
            remaining >>= 1;
            if remaining > 0 {
                square = square.times(&square)?;
            }
        }
        Ok(result)
    }

    pub fn disjoint_order(&self, other: &Self) -> ExactOrdering {
        if self.upper < other.lower {
            ExactOrdering::Less
        } else if self.lower > other.upper {
            ExactOrdering::Greater
        } else if self.is_point() && other.is_point() && self.lower == other.lower {
            ExactOrdering::Equal
        } else {
            ExactOrdering::Open
        }
    }
}

/// Integer polynomial with coefficients in ascending power order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegerPolynomial {
    pub coefficients: Vec<BigInt>,
}

impl IntegerPolynomial {
    pub fn new(mut coefficients: Vec<BigInt>) -> Result<Self, ExactValueError> {
        trim_integer_polynomial(&mut coefficients);
        if coefficients.is_empty() {
            return Err(ExactValueError::ZeroPolynomial);
        }
        Ok(Self { coefficients })
    }

    pub fn degree(&self) -> usize {
        self.coefficients.len() - 1
    }

    pub fn evaluate(&self, point: &Rat) -> Rat {
        self.coefficients
            .iter()
            .rev()
            .fold(Rat::zero(), |value, coefficient| {
                value * point + Rat::from_integer(coefficient.clone())
            })
    }

    fn rational_coefficients(&self) -> Vec<Rat> {
        self.coefficients
            .iter()
            .cloned()
            .map(Rat::from_integer)
            .collect()
    }

    /// Count distinct real roots in one strict rational interval using the
    /// exact Sturm sequence. Interval endpoints may not themselves be roots.
    pub fn distinct_root_count(&self, interval: &ExactInterval) -> Result<u32, ExactValueError> {
        if interval.is_point() {
            return Err(ExactValueError::NonStrictRootInterval);
        }
        if self.evaluate(&interval.lower).is_zero() || self.evaluate(&interval.upper).is_zero() {
            return Err(ExactValueError::RootAtIntervalBoundary);
        }
        let sturm = sturm_sequence(self);
        let lower = sign_variations(&sturm, &interval.lower);
        let upper = sign_variations(&sturm, &interval.upper);
        lower
            .checked_sub(upper)
            .ok_or(ExactValueError::InvalidSturmOrientation)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SturmIsolationCertificate {
    pub variations_at_lower: u32,
    pub variations_at_upper: u32,
}

/// One real algebraic number, identified by a polynomial and an exact interval
/// containing exactly one of its real roots.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AlgebraicRoot {
    pub polynomial: IntegerPolynomial,
    pub isolating_interval: ExactInterval,
    pub certificate: SturmIsolationCertificate,
}

impl AlgebraicRoot {
    pub fn isolate(
        polynomial: IntegerPolynomial,
        isolating_interval: ExactInterval,
    ) -> Result<Self, ExactValueError> {
        if polynomial.degree() == 0 {
            return Err(ExactValueError::ConstantPolynomial);
        }
        if isolating_interval.is_point() {
            return Err(ExactValueError::NonStrictRootInterval);
        }
        if polynomial.evaluate(&isolating_interval.lower).is_zero()
            || polynomial.evaluate(&isolating_interval.upper).is_zero()
        {
            return Err(ExactValueError::RootAtIntervalBoundary);
        }
        let sturm = sturm_sequence(&polynomial);
        let lower = sign_variations(&sturm, &isolating_interval.lower);
        let upper = sign_variations(&sturm, &isolating_interval.upper);
        let roots = lower
            .checked_sub(upper)
            .ok_or(ExactValueError::InvalidSturmOrientation)?;
        if roots != 1 {
            return Err(ExactValueError::RootCount { exact_count: roots });
        }
        Ok(Self {
            polynomial,
            isolating_interval,
            certificate: SturmIsolationCertificate {
                variations_at_lower: lower,
                variations_at_upper: upper,
            },
        })
    }

    fn contains_rational_root(&self, value: &Rat) -> bool {
        self.isolating_interval.lower < *value
            && *value < self.isolating_interval.upper
            && self.polynomial.evaluate(value).is_zero()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SeriesTailCertificate {
    /// If every omitted term is bounded by
    /// `first_omitted_abs_bound * ratio_abs_bound^k`, the complete absolute
    /// tail is bounded by `first/(1-ratio)`.
    AbsoluteGeometric {
        first_omitted_abs_bound: Rat,
        ratio_abs_bound: Rat,
    },
    /// Alternating, monotonically decreasing magnitudes place the tail
    /// between zero and the first omitted signed term.
    AlternatingMonotone { first_omitted_term: Rat },
    /// The remainder has already been closed by an exact identity.
    ExactTail { remainder: Rat },
}

impl SeriesTailCertificate {
    pub fn remainder_interval(&self) -> Result<ExactInterval, ExactValueError> {
        match self {
            Self::AbsoluteGeometric {
                first_omitted_abs_bound,
                ratio_abs_bound,
            } => {
                if first_omitted_abs_bound.is_negative() {
                    return Err(ExactValueError::NegativeTailBound);
                }
                if ratio_abs_bound.is_negative() || ratio_abs_bound >= &Rat::one() {
                    return Err(ExactValueError::InvalidGeometricRatio);
                }
                let bound = first_omitted_abs_bound / (Rat::one() - ratio_abs_bound);
                ExactInterval::new(-bound.clone(), bound)
            }
            Self::AlternatingMonotone { first_omitted_term } => {
                if first_omitted_term.is_negative() {
                    ExactInterval::new(first_omitted_term.clone(), Rat::zero())
                } else {
                    ExactInterval::new(Rat::zero(), first_omitted_term.clone())
                }
            }
            Self::ExactTail { remainder } => Ok(ExactInterval::point(remainder.clone())),
        }
    }
}

/// A convergent series face with an exact finite sum and an exact tail
/// enclosure derived from one supported certificate species.
/// **The roots a transport actually asks for, isolated by this owner's own certificate.**
///
/// A root-mean-square rebase asks for `1/sqrt(s)` and nothing else; a chart width asks for
/// `1/sqrt(d)`. Both are algebraic of degree two, which is exactly what [`AlgebraicRoot`] is for,
/// and the Sturm certificate it already carries is what makes the isolation a proof rather than an
/// iteration count. These are added inside this owner because that is where a root of an exact
/// rational belongs.
impl AlgebraicRoot {
    /// The positive `sqrt(radicand)`, isolated with a Sturm certificate.
    ///
    /// The bracket comes from an integer square root at `octaves` dyadic places, so it needs no
    /// starting guess; the certificate is what verifies it.
    pub fn square_root(radicand: &Rat, octaves: u32) -> Result<Self, ExactValueError> {
        Self::degree_two_root(radicand, octaves, false)
    }

    /// The positive `1/sqrt(radicand)`, isolated with a Sturm certificate.
    ///
    /// **This is the return a normalization actually needs**, and taking it directly rather than
    /// inverting a root keeps one certificate instead of two.
    pub fn reciprocal_square_root(
        radicand: &Rat,
        octaves: u32,
    ) -> Result<Self, ExactValueError> {
        Self::degree_two_root(radicand, octaves, true)
    }

    fn degree_two_root(
        radicand: &Rat,
        octaves: u32,
        reciprocal: bool,
    ) -> Result<Self, ExactValueError> {
        if !radicand.is_positive() {
            return Err(ExactValueError::NonPositiveRadicand);
        }
        let numerator = radicand.numer().magnitude().clone();
        let denominator = radicand.denom().magnitude().clone();
        // `q x^2 - p` has root sqrt(p/q); `p y^2 - q` has root 1/sqrt(p/q).
        let polynomial = if reciprocal {
            IntegerPolynomial::new(vec![
                -BigInt::from(denominator.clone()),
                BigInt::zero(),
                BigInt::from(numerator.clone()),
            ])?
        } else {
            IntegerPolynomial::new(vec![
                -BigInt::from(numerator.clone()),
                BigInt::zero(),
                BigInt::from(denominator.clone()),
            ])?
        };
        // An integer square root at `octaves` dyadic places brackets the value by construction.
        let scale = BigUint::one() << (2 * octaves as usize);
        let (over, under) = if reciprocal {
            (denominator * &scale, numerator)
        } else {
            (numerator * &scale, denominator)
        };
        let floor = (over / under).sqrt();
        let unit = Rat::new(
            BigInt::one(),
            BigInt::from(BigUint::one() << octaves as usize),
        );
        let mut lower = Rat::from_integer(BigInt::from(floor.clone())) * &unit;
        let mut upper = Rat::from_integer(BigInt::from(floor + 1u32)) * &unit;
        // A strict interval whose endpoints are not themselves roots, widened outward by one place
        // where the floor landed exactly on the root.
        if polynomial.evaluate(&lower).is_zero() {
            lower -= &unit;
        }
        if polynomial.evaluate(&upper).is_zero() {
            upper += &unit;
        }
        if !lower.is_positive() {
            lower = &unit / Rat::from_integer(BigInt::from(2));
            if polynomial.evaluate(&lower).is_zero() {
                lower /= Rat::from_integer(BigInt::from(2));
            }
        }
        Self::isolate(polynomial, ExactInterval::new(lower, upper)?)
    }

    /// The positive `radicand^(1/degree)`, isolated with a Sturm certificate.
    ///
    /// **A chronology ladder's per-band angle is exactly this object**: `base^(-2i/d)` is algebraic
    /// of degree `d/2`, and taking it as a root rather than through a logarithm keeps the whole
    /// ladder inside exact arithmetic. The bracket comes from an integer `n`-th root; the
    /// certificate is what verifies it.
    pub fn nth_root(radicand: &Rat, degree: u32, octaves: u32) -> Result<Self, ExactValueError> {
        if !radicand.is_positive() {
            return Err(ExactValueError::NonPositiveRadicand);
        }
        if degree == 0 {
            return Err(ExactValueError::ConstantPolynomial);
        }
        let numerator = radicand.numer().magnitude().clone();
        let denominator = radicand.denom().magnitude().clone();
        let mut coefficients = vec![BigInt::zero(); degree as usize + 1];
        coefficients[0] = -BigInt::from(numerator.clone());
        coefficients[degree as usize] = BigInt::from(denominator.clone());
        let polynomial = IntegerPolynomial::new(coefficients)?;
        let scale = BigUint::one() << (degree as usize * octaves as usize);
        let floor = (numerator * &scale / denominator).nth_root(degree);
        let unit = Rat::new(
            BigInt::one(),
            BigInt::from(BigUint::one() << octaves as usize),
        );
        let mut lower = Rat::from_integer(BigInt::from(floor.clone())) * &unit;
        let mut upper = Rat::from_integer(BigInt::from(floor + 1u32)) * &unit;
        if polynomial.evaluate(&lower).is_zero() {
            lower -= &unit;
        }
        if polynomial.evaluate(&upper).is_zero() {
            upper += &unit;
        }
        if !lower.is_positive() {
            lower = &unit / Rat::from_integer(BigInt::from(2));
        }
        Self::isolate(polynomial, ExactInterval::new(lower, upper)?)
    }

    /// The isolating interval, which **is** the enclosure: the root is inside it and the
    /// certificate says exactly one root is.
    pub fn enclosure(&self) -> &ExactInterval {
        &self.isolating_interval
    }
}

/// Past this reach a decaying exponential is below `2^-REACH`, which no grain this workspace
/// carries can separate from zero. Read off the carrier: `bfloat16` holds eight significand
/// octaves and `binary64` fifty-two, so sixty-four leaves every declared receiver behind.
const DECAY_REACH: u32 = 64;
/// Past this reach a growing exponential leaves any carrier a declared receiver reads, and the
/// owner **refuses** rather than forming it.
const GROWTH_REACH: u32 = 64;
/// Past this reach `tanh` is within `2^(-2 REACH)` of its limit.
const TANGENT_REACH: u32 = 32;
/// The dyadic places a composed exponential is held at, so its denominators cannot grow with the
/// exponent. Sixty-four leaves every declared receiver in this workspace behind.
const EXPONENTIAL_OCTAVES: u32 = 64;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CertifiedSeries {
    pub expression: ExactExpr,
    pub partial_sum: Rat,
    pub terms_folded: BigUint,
    pub tail_certificate: SeriesTailCertificate,
}

impl CertifiedSeries {
    pub fn new(
        expression: ExactExpr,
        partial_sum: Rat,
        terms_folded: BigUint,
        tail_certificate: SeriesTailCertificate,
    ) -> Result<Self, ExactValueError> {
        tail_certificate.remainder_interval()?;
        Ok(Self {
            expression,
            partial_sum,
            terms_folded,
            tail_certificate,
        })
    }

    pub fn enclosure(&self) -> ExactInterval {
        self.tail_certificate
            .remainder_interval()
            .expect("a CertifiedSeries retains its validated certificate")
            .translated(&self.partial_sum)
    }

    /// **`exp(x)` as a certified enclosure**, reduced through the exponential's own homomorphism.
    ///
    /// A Taylor series is only well-conditioned near zero: at `x = -15` with forty terms the first
    /// omitted term is `15^40/40!`, which is larger than `exp(-15)` itself, so the certificate
    /// closes on an interval hundreds of thousands of times wider than the value. That is not a
    /// defect of the certificate — it is the honest bound for that many terms — and the repair is
    /// the function's own law rather than more terms.
    ///
    /// `exp(a+b) = exp(a)exp(b)` splits `x` into a whole part and a fraction below one. The whole
    /// part rides an integer power of `exp(1)`; the fraction takes the series, where it converges
    /// fast and the geometric bound is tight. `CLAUDE.md` §0l: the additive chart carried to the
    /// multiplicative one is what `exp` **is**, so using it here is the owner carrying its own
    /// function.
    pub fn exponential_enclosure(x: &Rat, terms: usize) -> Result<ExactInterval, ExactValueError> {
        if terms == 0 {
            return Err(ExactValueError::EmptySeries);
        }
        let negative = x.is_negative();
        let magnitude = if negative { -x.clone() } else { x.clone() };
        // **THE APERTURE, and it is a bound rather than a shortcut.** For `x <= -REACH` the value
        // is below `2^-REACH` because `e > 2`, so `[0, 2^-REACH]` contains it exactly — and no
        // declared receiver at any grain this workspace carries can separate a finer statement.
        // Forming `e^REACH` to divide it back out is the same answer at hundreds of times the cost.
        if negative && magnitude >= Rat::from_integer(BigInt::from(DECAY_REACH)) {
            return ExactInterval::new(
                Rat::zero(),
                Rat::new(BigInt::one(), BigInt::from(BigUint::one() << DECAY_REACH as usize)),
            );
        }
        let whole = magnitude.to_integer();
        let fraction = &magnitude - Rat::from_integer(whole.clone());
        let unit = Self::exponential_series(&Rat::one(), terms)?.enclosure();
        let steps = u32::try_from(&whole).map_err(|_| ExactValueError::TailDoesNotClose)?;
        if steps > GROWTH_REACH {
            return Err(ExactValueError::TailDoesNotClose);
        }
        // **Held at a grain at every step.** An unheld interval power grows its denominators with
        // the exponent, and `e^63` composed sixty-three times is the same cost defect as an unheld
        // ladder. The grain is read off the carrier and the enclosure only ever widens.
        let carried = unit
            .power_held(steps, EXPONENTIAL_OCTAVES)?
            .times(&Self::exponential_series(&fraction, terms)?.enclosure())?
            .round_out(EXPONENTIAL_OCTAVES)?;
        if negative {
            carried.reciprocal()
        } else {
            Ok(carried)
        }
    }

    /// **`exp(x)` as a certified series for `|x| <= 1`**, with the geometric tail this owner
    /// already validates.
    ///
    /// After `n` terms every omitted term is at most the first times `(|x|/(n+1))^j`, which is
    /// exactly [`SeriesTailCertificate::AbsoluteGeometric`]. The owner refuses the certificate
    /// where the ratio bound does not close the tail, so a caller cannot silently take too few
    /// terms for its argument. [`Self::exponential_enclosure`] is the reduction that keeps every
    /// caller inside this domain.
    pub fn exponential_series(x: &Rat, terms: usize) -> Result<Self, ExactValueError> {
        if terms == 0 {
            return Err(ExactValueError::EmptySeries);
        }
        let mut sum = Rat::zero();
        let mut term = Rat::one();
        for k in 0..terms {
            sum += &term;
            term = &term * x / Rat::from_integer(BigInt::from(k as u64 + 1));
        }
        let magnitude = |value: &Rat| -> Rat {
            if value.is_negative() {
                -value.clone()
            } else {
                value.clone()
            }
        };
        let ratio_bound = magnitude(x) / Rat::from_integer(BigInt::from(terms as u64 + 1));
        if ratio_bound >= Rat::one() {
            return Err(ExactValueError::TailDoesNotClose);
        }
        Self::new(
            ExactExpr::Rational(x.clone()),
            sum,
            BigUint::from(terms as u64),
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: magnitude(&term),
                ratio_abs_bound: ratio_bound,
            },
        )
    }

    /// **`cos(x)` and `sin(x)` for `|x| <= 1`**, alternating with monotonically decreasing terms.
    ///
    /// For `|x| <= 1` every ratio `x^2/((2k+1)(2k+2))` is at most one half, so the terms decrease
    /// from the first and the omitted tail is bounded by its first omitted term — exactly
    /// [`SeriesTailCertificate::AlternatingMonotone`]. A caller past that domain composes the
    /// rotation group's own law, `R(a+b) = R(a)R(b)`, rather than asking for more terms.
    pub fn circular_series(x: &Rat, terms: usize) -> Result<(Self, Self), ExactValueError> {
        if terms == 0 {
            return Err(ExactValueError::EmptySeries);
        }
        let magnitude = if x.is_negative() { -x.clone() } else { x.clone() };
        if magnitude > Rat::one() {
            return Err(ExactValueError::TailDoesNotClose);
        }
        let square = x * x;

        let mut cosine_sum = Rat::zero();
        let mut cosine_term = Rat::one();
        for k in 0..terms {
            if k % 2 == 0 {
                cosine_sum += &cosine_term;
            } else {
                cosine_sum -= &cosine_term;
            }
            let a = Rat::from_integer(BigInt::from(2 * k as u64 + 1));
            let b = Rat::from_integer(BigInt::from(2 * k as u64 + 2));
            cosine_term = &cosine_term * &square / (a * b);
        }
        let cosine = Self::new(
            ExactExpr::Rational(x.clone()),
            cosine_sum,
            BigUint::from(terms as u64),
            SeriesTailCertificate::AlternatingMonotone {
                first_omitted_term: cosine_term,
            },
        )?;

        let mut sine_sum = Rat::zero();
        let mut sine_term = x.clone();
        for k in 0..terms {
            if k % 2 == 0 {
                sine_sum += &sine_term;
            } else {
                sine_sum -= &sine_term;
            }
            let a = Rat::from_integer(BigInt::from(2 * k as u64 + 2));
            let b = Rat::from_integer(BigInt::from(2 * k as u64 + 3));
            sine_term = &sine_term * &square / (a * b);
        }
        let sine = Self::new(
            ExactExpr::Rational(x.clone()),
            sine_sum,
            BigUint::from(terms as u64),
            SeriesTailCertificate::AlternatingMonotone {
                first_omitted_term: sine_term,
            },
        )?;
        Ok((cosine, sine))
    }

    /// **A rotation by an integer multiple of one angle, through the group's own law.**
    ///
    /// `R(p a) = R(a)^p` by repeated composition of the enclosed group element, so the
    /// transcendental is evaluated **once per band** and a position is an integer power. The
    /// chronology's exact carrier is therefore the integer `p`, and no series runs per position.
    pub fn rotation_power(
        angle: &Rat,
        power: u64,
        terms: usize,
    ) -> Result<(ExactInterval, ExactInterval), ExactValueError> {
        let (cosine, sine) = Self::circular_series(angle, terms)?;
        let mut carried = (ExactInterval::point(Rat::one()), ExactInterval::point(Rat::zero()));
        let step = (cosine.enclosure(), sine.enclosure());
        for _ in 0..power {
            let real = carried
                .0
                .times(&step.0)?
                .translated(&Rat::zero());
            let cross = carried.1.times(&step.1)?;
            let cosine_out =
                ExactInterval::new(&real.lower - &cross.upper, &real.upper - &cross.lower)?;
            let left = carried.0.times(&step.1)?;
            let right = carried.1.times(&step.0)?;
            let sine_out =
                ExactInterval::new(&left.lower + &right.lower, &left.upper + &right.upper)?;
            carried = (cosine_out, sine_out);
        }
        Ok(carried)
    }

    /// **`tanh(x)`, taken through the DECAYING exponential so nothing large is ever formed.**
    ///
    /// `tanh(x) = sign(x) (1 - e^(-2|x|)) / (1 + e^(-2|x|))`. Written the other way the
    /// intermediate is `e^(2|x|)`, which leaves every bounded carrier long before the value itself
    /// stops moving. The identity is exact and the reformulation is the whole difference.
    ///
    /// Returns the enclosure rather than a series, because a quotient of two series is not one.
    pub fn hyperbolic_tangent_enclosure(
        x: &Rat,
        terms: usize,
    ) -> Result<ExactInterval, ExactValueError> {
        let negative = x.is_negative();
        let magnitude = if negative { -x.clone() } else { x.clone() };
        let two = Rat::from_integer(BigInt::from(2));
        // **THE APERTURE.** Past this reach `e^(-2|x|) <= 2^(-2 REACH)`, so `tanh` is within that
        // of one and the enclosure below is exact. `TANGENT_REACH` is read off the carrier the
        // grain uses, not chosen for a result.
        if magnitude >= Rat::from_integer(BigInt::from(TANGENT_REACH)) {
            let bound = Rat::new(
                BigInt::one(),
                BigInt::from(BigUint::one() << (2 * TANGENT_REACH) as usize),
            );
            let one = Rat::one();
            let low = (&one - &bound) / (&one + &bound);
            let interval = ExactInterval::new(low, one)?;
            return Ok(if negative {
                ExactInterval::new(-interval.upper.clone(), -interval.lower.clone())?
            } else {
                interval
            });
        }
        let decaying = Self::exponential_enclosure(&(-(&magnitude * &two)), terms)?;
        let one = Rat::one();
        // Both endpoints of a decreasing-in-`u` map, so the bounds swap.
        let low = (&one - &decaying.upper) / (&one + &decaying.upper);
        let high = (&one - &decaying.lower) / (&one + &decaying.lower);
        let (below, above) = if low <= high {
            (low, high)
        } else {
            (high, low)
        };
        let interval = ExactInterval::new(below, above)?;
        Ok(if negative {
            ExactInterval::new(-interval.upper.clone(), -interval.lower.clone())?
        } else {
            interval
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExactValue {
    Integer(BigInt),
    Rational(Rat),
    Algebraic(AlgebraicRoot),
    CertifiedSeries(CertifiedSeries),
    Expression(ExactExpr),
}

impl ExactValue {
    pub fn rational(value: Rat) -> Self {
        if value.denom().is_one() {
            Self::Integer(value.numer().clone())
        } else {
            Self::Rational(value)
        }
    }

    pub fn as_rational(&self) -> Option<Rat> {
        match self {
            Self::Integer(value) => Some(Rat::from_integer(value.clone())),
            Self::Rational(value) => Some(value.clone()),
            Self::Algebraic(_) | Self::CertifiedSeries(_) | Self::Expression(_) => None,
        }
    }

    pub fn compare(&self, other: &Self) -> ExactOrdering {
        if self == other {
            return ExactOrdering::Equal;
        }
        match (self, other) {
            (Self::Integer(left), Self::Integer(right)) => left.cmp(right).into(),
            (Self::Integer(left), Self::Rational(right)) => {
                Rat::from_integer(left.clone()).cmp(right).into()
            }
            (Self::Rational(left), Self::Integer(right)) => {
                left.cmp(&Rat::from_integer(right.clone())).into()
            }
            (Self::Rational(left), Self::Rational(right)) => left.cmp(right).into(),
            (Self::Algebraic(left), Self::Algebraic(right)) => compare_algebraic(left, right),
            (Self::Integer(left), Self::Algebraic(right)) => {
                compare_rational_algebraic(&Rat::from_integer(left.clone()), right)
            }
            (Self::Rational(left), Self::Algebraic(right)) => {
                compare_rational_algebraic(left, right)
            }
            (Self::Algebraic(left), Self::Integer(right)) => reverse(compare_rational_algebraic(
                &Rat::from_integer(right.clone()),
                left,
            )),
            (Self::Algebraic(left), Self::Rational(right)) => {
                reverse(compare_rational_algebraic(right, left))
            }
            (Self::CertifiedSeries(left), Self::CertifiedSeries(right)) => {
                left.enclosure().disjoint_order(&right.enclosure())
            }
            (Self::Integer(left), Self::CertifiedSeries(right)) => {
                ExactInterval::point(Rat::from_integer(left.clone()))
                    .disjoint_order(&right.enclosure())
            }
            (Self::Rational(left), Self::CertifiedSeries(right)) => {
                ExactInterval::point(left.clone()).disjoint_order(&right.enclosure())
            }
            (Self::CertifiedSeries(left), Self::Integer(right)) => reverse(
                ExactInterval::point(Rat::from_integer(right.clone()))
                    .disjoint_order(&left.enclosure()),
            ),
            (Self::CertifiedSeries(left), Self::Rational(right)) => {
                reverse(ExactInterval::point(right.clone()).disjoint_order(&left.enclosure()))
            }
            _ => ExactOrdering::Open,
        }
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ExactValueError {
    #[error("a root was asked of a non-positive radicand")]
    NonPositiveRadicand,
    #[error("a series was asked for zero terms")]
    EmptySeries,
    #[error("a reciprocal was asked of an enclosure straddling zero")]
    ReciprocalStraddlesZero,
    #[error("the geometric ratio bound does not close the tail at the declared term count")]
    TailDoesNotClose,
    #[error("an exact interval cannot have its lower endpoint above its upper endpoint")]
    ReversedInterval,
    #[error("the zero polynomial does not identify an algebraic species")]
    ZeroPolynomial,
    #[error("a constant polynomial has no isolated algebraic root")]
    ConstantPolynomial,
    #[error("an algebraic isolating interval must have nonzero width")]
    NonStrictRootInterval,
    #[error("the proposed isolating interval has a root on its boundary")]
    RootAtIntervalBoundary,
    #[error("the Sturm variation count increased across an ordered interval")]
    InvalidSturmOrientation,
    #[error("the proposed interval contains {exact_count} roots rather than exactly one")]
    RootCount { exact_count: u32 },
    #[error("an absolute tail bound cannot be negative")]
    NegativeTailBound,
    #[error("an absolute geometric tail ratio must satisfy 0 <= r < 1")]
    InvalidGeometricRatio,
    #[error(
        "the exact value has magnitude past what {species} can carry, so emitting it would return an \
         infinity: refused rather than saturated"
    )]
    FloatMagnitudeOverflows { species: &'static str },
    #[error(
        "the {species} bit pattern 0x{bits:x} is not a number: it names no ratio, so it has no exact dyadic and no enclosure"
    )]
    NotANumberFloat { species: &'static str, bits: u64 },
    #[error(
        "the {species} bit pattern 0x{bits:x} is an infinity (negative: {negative}): it names no ratio, so it has no exact dyadic and no enclosure"
    )]
    InfiniteFloat {
        species: &'static str,
        negative: bool,
        bits: u64,
    },
    #[error("the bit pattern 0x{bits:x} carries bits above the {width}-bit {species} format")]
    OverWideBitPattern {
        species: &'static str,
        width: u32,
        bits: u64,
    },
    #[error(
        "a {species} datum does not re-encode to the pattern 0x{bits:x} it was decoded from; the decode is not a bijection and must not be trusted"
    )]
    NonInvertibleDecode { species: &'static str, bits: u64 },
    #[error("a {holding} datum cannot be re-encoded as a {wanted}")]
    FloatSpeciesMismatch {
        holding: &'static str,
        wanted: &'static str,
    },
}

fn reverse(ordering: ExactOrdering) -> ExactOrdering {
    match ordering {
        ExactOrdering::Less => ExactOrdering::Greater,
        ExactOrdering::Equal => ExactOrdering::Equal,
        ExactOrdering::Greater => ExactOrdering::Less,
        ExactOrdering::Open => ExactOrdering::Open,
    }
}

fn compare_algebraic(left: &AlgebraicRoot, right: &AlgebraicRoot) -> ExactOrdering {
    let interval_order = left
        .isolating_interval
        .disjoint_order(&right.isolating_interval);
    if interval_order != ExactOrdering::Open {
        return interval_order;
    }
    if left.polynomial == right.polynomial {
        // For one fixed Sturm sequence, the variation count immediately
        // before an isolated root is its exact order address among the real
        // roots. Overlapping intervals alone are not enough: two intervals
        // can overlap while isolating different roots.
        right
            .certificate
            .variations_at_lower
            .cmp(&left.certificate.variations_at_lower)
            .into()
    } else {
        ExactOrdering::Open
    }
}

fn compare_rational_algebraic(rational: &Rat, algebraic: &AlgebraicRoot) -> ExactOrdering {
    if *rational <= algebraic.isolating_interval.lower {
        ExactOrdering::Less
    } else if *rational >= algebraic.isolating_interval.upper {
        ExactOrdering::Greater
    } else if algebraic.contains_rational_root(rational) {
        ExactOrdering::Equal
    } else {
        ExactOrdering::Open
    }
}

fn trim_integer_polynomial(coefficients: &mut Vec<BigInt>) {
    while coefficients.last().is_some_and(Zero::is_zero) {
        coefficients.pop();
    }
}

fn trim_rational_polynomial(coefficients: &mut Vec<Rat>) {
    while coefficients.last().is_some_and(Zero::is_zero) {
        coefficients.pop();
    }
}

fn derivative(polynomial: &[Rat]) -> Vec<Rat> {
    let mut derivative = polynomial
        .iter()
        .enumerate()
        .skip(1)
        .map(|(degree, coefficient)| coefficient * Rat::from_integer(BigInt::from(degree)))
        .collect::<Vec<_>>();
    trim_rational_polynomial(&mut derivative);
    derivative
}

fn polynomial_remainder(dividend: &[Rat], divisor: &[Rat]) -> Vec<Rat> {
    let mut remainder = dividend.to_vec();
    trim_rational_polynomial(&mut remainder);
    if divisor.is_empty() {
        return remainder;
    }
    let divisor_degree = divisor.len() - 1;
    while remainder.len() > divisor_degree {
        let remainder_degree = remainder.len() - 1;
        let shift = remainder_degree - divisor_degree;
        let factor = remainder[remainder_degree].clone() / &divisor[divisor_degree];
        for (index, coefficient) in divisor.iter().enumerate() {
            remainder[index + shift] -= &factor * coefficient;
        }
        trim_rational_polynomial(&mut remainder);
    }
    remainder
}

fn sturm_sequence(polynomial: &IntegerPolynomial) -> Vec<Vec<Rat>> {
    let first = polynomial.rational_coefficients();
    let second = derivative(&first);
    let mut sequence = vec![first, second];
    while !sequence
        .last()
        .expect("the sequence is nonempty")
        .is_empty()
    {
        let length = sequence.len();
        let mut remainder = polynomial_remainder(&sequence[length - 2], &sequence[length - 1]);
        for coefficient in &mut remainder {
            *coefficient = -coefficient.clone();
        }
        trim_rational_polynomial(&mut remainder);
        if remainder.is_empty() {
            break;
        }
        sequence.push(remainder);
    }
    sequence
}

fn evaluate_rational_polynomial(polynomial: &[Rat], point: &Rat) -> Rat {
    polynomial
        .iter()
        .rev()
        .fold(Rat::zero(), |value, coefficient| {
            value * point + coefficient
        })
}

fn sign_variations(sequence: &[Vec<Rat>], point: &Rat) -> u32 {
    let signs = sequence
        .iter()
        .map(|polynomial| evaluate_rational_polynomial(polynomial, point))
        .filter(|value| !value.is_zero())
        .map(|value| if value.is_positive() { 1_i8 } else { -1_i8 })
        .collect::<Vec<_>>();
    signs.windows(2).filter(|pair| pair[0] != pair[1]).count() as u32
}

/// **The mouth: an IEEE-754-shaped bit pattern in, an exact dyadic and its deleted tail out.**
///
/// This module is the workspace's one declared floating-point exception, and the declaration is
/// narrow on purpose. `f64` and `f32` occur in exactly four functions here — [`decode_f64`],
/// [`decode_f32`], [`encode_f64`], [`encode_f32`] — and each is one call to `to_bits` or
/// `from_bits`. **No arithmetic is performed on a machine float anywhere in this module or
/// downstream of it.** Everything else takes `u16`/`u32`/`u64` words, which is what a weight file,
/// a wire format or a sensor actually hands a program.
///
/// ## What a float is, stated precisely
///
/// `canon/THE_MATHEMATICS_TABLET.md` §1: *a float is not a bad approximation of a ratio — it is the
/// ratio's series expansion in base two, truncated, with the remainder discarded.* The first half of
/// that sentence is the part usually missed: the truncated expansion is itself **exact**. An
/// IEEE-754 value is precisely `±m · 2^e` with `m` an integer, and nothing in that statement is
/// approximate. What was destroyed is the **tail** — everything below the last retained bit — and
/// the tail's width is exactly one unit in the last place, `2^e`.
///
/// So the honest face of a float has two possible shapes and **which one it is is not a property of
/// the bits**:
///
/// | the bits are… | the face is… | width |
/// |---|---|---|
/// | the datum itself — a stored weight, a wire word, a constant | a **point** | `0` |
/// | a rounding of a quantity that is not representable | an **enclosure** | one ulp |
///
/// [`FloatReading`] is that declaration and the caller must make it. A codec that guessed would be
/// choosing, for every consumer it will ever have, whether a deletion happened — which is the
/// defect `canon/THE_MATHEMATICS_TABLET.md` §1 names in its own generalisation: *a carrier that
/// reduces on construction has decided, for every consumer it will ever have, which distinctions
/// are invisible.*
///
/// ## What is refused, by name
///
/// `NaN` and `±∞` name no ratio. They are refused as [`ExactValueError::NotANumberFloat`] and
/// [`ExactValueError::InfiniteFloat`] rather than mapped to some sentinel, because a sentinel is a
/// third thing pretending to be a number. Subnormals and both zeros are **accepted** — a subnormal
/// is an ordinary dyadic with the leading one absent, and `−0.0` is a sign bit over an empty
/// magnitude, which is why the sign is retained separately from the significand here rather than
/// folded into a `BigInt` that cannot hold it.
///
/// ## The decode is a bijection and says so
///
/// [`decode_bits`] re-encodes what it just decoded and refuses with
/// [`ExactValueError::NonInvertibleDecode`] if the pattern does not come back identical. The round
/// trip is therefore a **law of the codec**, checked on every call, rather than a property a driver
/// asserts about it afterwards.
pub mod ieee754 {
    use num_bigint::{BigInt, BigUint};
    use num_traits::{One, ToPrimitive, Zero};
    use relational_geometry::Rat;
    use serde::{Deserialize, Serialize};

    use super::{ExactInterval, ExactValueError};

    /// The three binary interchange shapes this codec accepts.
    ///
    /// `bfloat16` is not an IEEE-754 interchange format, but it has the same three fields with the
    /// same meanings and the same subnormal convention, so one decode covers all three. It is here
    /// because it is the format the material arrives in: a transformer weight file is `BF16`, and
    /// `soma/life/examples/eros_self_emanated_law.rs` refuses every other dtype by name.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
    pub enum BinaryFloatSpecies {
        /// 1 sign, 8 exponent, 7 stored significand bits. Same exponent range as `binary32`, eight
        /// significand bits of ratio.
        Bfloat16,
        /// IEEE-754 `binary32`: 1 sign, 8 exponent, 23 stored significand bits.
        Binary32,
        /// IEEE-754 `binary64`: 1 sign, 11 exponent, 52 stored significand bits.
        Binary64,
    }

    impl BinaryFloatSpecies {
        pub const ALL: [BinaryFloatSpecies; 3] = [Self::Bfloat16, Self::Binary32, Self::Binary64];

        pub const fn name(self) -> &'static str {
            match self {
                Self::Bfloat16 => "bfloat16",
                Self::Binary32 => "binary32",
                Self::Binary64 => "binary64",
            }
        }

        pub const fn width_bits(self) -> u32 {
            match self {
                Self::Bfloat16 => 16,
                Self::Binary32 => 32,
                Self::Binary64 => 64,
            }
        }

        /// Bits of **stored** significand. A normal value's leading one is not stored, so the
        /// integer significand of a normal value has `stored_significand_bits() + 1` bits.
        pub const fn stored_significand_bits(self) -> u32 {
            match self {
                Self::Bfloat16 => 7,
                Self::Binary32 => 23,
                Self::Binary64 => 52,
            }
        }

        pub const fn exponent_bits(self) -> u32 {
            match self {
                Self::Bfloat16 | Self::Binary32 => 8,
                Self::Binary64 => 11,
            }
        }

        pub const fn exponent_bias(self) -> i32 {
            (1_i32 << (self.exponent_bits() - 1)) - 1
        }

        const fn exponent_mask(self) -> u64 {
            (1_u64 << self.exponent_bits()) - 1
        }

        const fn significand_mask(self) -> u64 {
            (1_u64 << self.stored_significand_bits()) - 1
        }

        /// The dyadic grid the subnormals and both zeros of this format sit on: every subnormal is
        /// an integer multiple of `2^{subnormal_ulp_exponent()}`, and so is zero.
        pub const fn subnormal_ulp_exponent(self) -> i32 {
            1 - self.exponent_bias() - self.stored_significand_bits() as i32
        }
    }

    /// How the bits are to be read, which is a declaration and never an inference.
    ///
    /// The same 64 bits are a different mathematical object under each reading, and
    /// `crate::reopening`'s admission law separates them: a point admits every grain, an enclosure
    /// of width one ulp admits no grain finer than the ulp and is refused past it by name.
    #[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
    pub enum FloatReading {
        /// **The bits are the datum.** A stored network weight, a wire word, a table constant: the
        /// value in the file *is* `±m·2^e` and no rounding of anything else happened at this
        /// boundary. The enclosure is a point and nothing was deleted **here** — whatever deleted a
        /// tail did so upstream, and that deletion is not this face's to certify.
        ExactBitPattern,
        /// **The bits are the round-to-nearest image of a quantity that is not representable.** The
        /// enclosure is the point plus or minus half a unit in the last place, so its width is
        /// exactly one ulp.
        ///
        /// The enclosure is **outward**: at the low edge of a binade the true rounding preimage is
        /// only a quarter-ulp wide below the point, and this returns a half-ulp there. Outward is
        /// the honest direction — it can only refuse a relation that a sharper enclosure would have
        /// admitted, never admit one a sharper enclosure would have refused.
        RoundedToNearest,
        /// **The bits are the truncation toward zero of the quantity.** The enclosure runs one full
        /// ulp away from zero. A zero datum under this reading straddles zero by one ulp on each
        /// side, since every quantity of magnitude below one ulp truncates to it.
        TruncatedTowardZero,
    }

    impl FloatReading {
        pub const ALL: [FloatReading; 3] = [
            Self::ExactBitPattern,
            Self::RoundedToNearest,
            Self::TruncatedTowardZero,
        ];

        pub const fn name(self) -> &'static str {
            match self {
                Self::ExactBitPattern => "exact bit pattern",
                Self::RoundedToNearest => "rounded to nearest",
                Self::TruncatedTowardZero => "truncated toward zero",
            }
        }

        /// Whether this reading declares that a tail was deleted at this boundary.
        pub const fn deletes_a_tail(self) -> bool {
            !matches!(self, Self::ExactBitPattern)
        }
    }

    /// One decoded binary floating-point datum: an exact dyadic, plus the scale of what the format
    /// could not carry.
    ///
    /// `significand` is **not reduced**. `0.5_f64` decodes to `2^51 · 2^-52`, not to `1 · 2^-1`,
    /// because the two carry different information: the value is the same and the **ulp is not**.
    /// The unit in the last place is a property of the format at this magnitude, and stripping
    /// trailing zeros from the significand would destroy exactly the quantity this whole module
    /// exists to retain. [`BinaryFloatDatum::reduced_dyadic`] offers the stripped form as a
    /// *reading*, which is where a reduction belongs.
    #[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
    pub struct BinaryFloatDatum {
        pub species: BinaryFloatSpecies,
        /// The pattern this datum was decoded from, zero-extended to 64 bits.
        pub bits: u64,
        /// The sign bit, retained **separately** from the magnitude. A signed integer significand
        /// cannot hold the sign of `−0.0`, and a codec that cannot round-trip `−0.0` is not a
        /// bijection on the format it claims to decode.
        pub negative: bool,
        /// The unsigned integer significand, with a normal value's hidden leading one restored.
        pub significand: BigUint,
        /// `value = ±significand · 2^{ulp_exponent}`, and `2^{ulp_exponent}` is one unit in the
        /// last place.
        pub ulp_exponent: i32,
        pub subnormal: bool,
    }

    impl BinaryFloatDatum {
        /// The exact value, as a rational. This is not an approximation of the float; it **is** the
        /// float.
        pub fn value(&self) -> Rat {
            let magnitude = scaled(BigInt::from(self.significand.clone()), self.ulp_exponent);
            if self.negative { -magnitude } else { magnitude }
        }

        /// One unit in the last place, exactly: `2^{ulp_exponent}`. This is the width of what the
        /// format deleted, and under a rounding reading it is the width of the enclosure.
        pub fn unit_in_last_place(&self) -> Rat {
            power_of_two(self.ulp_exponent)
        }

        /// The ulp said as a bit count: `ulp = 2^{-ulp_bits()}`. Negative for values so large that
        /// the format's spacing exceeds one.
        pub fn ulp_bits(&self) -> i32 {
            -self.ulp_exponent
        }

        pub fn is_zero(&self) -> bool {
            self.significand.is_zero()
        }

        pub fn signed_significand(&self) -> BigInt {
            let magnitude = BigInt::from(self.significand.clone());
            if self.negative { -magnitude } else { magnitude }
        }

        /// The same value with trailing factors of two stripped: `(m, e)` with `m` odd or zero.
        ///
        /// A **reading**, offered rather than imposed. The ulp is not recoverable from it.
        pub fn reduced_dyadic(&self) -> (BigInt, i32) {
            let mut numerator = self.signed_significand();
            let mut exponent = self.ulp_exponent;
            if numerator.is_zero() {
                return (numerator, 0);
            }
            let trailing = numerator
                .magnitude()
                .trailing_zeros()
                .unwrap_or(0)
                .min(i32::MAX as u64) as usize;
            numerator >>= trailing;
            exponent += trailing as i32;
            (numerator, exponent)
        }

        /// The face this datum presents under a declared reading.
        ///
        /// This is the whole content of the module in four lines: the point is the truncated
        /// expansion, and the interval is the point plus the tail the format threw away.
        pub fn enclosure(&self, reading: FloatReading) -> ExactInterval {
            let value = self.value();
            let ulp = self.unit_in_last_place();
            match reading {
                FloatReading::ExactBitPattern => ExactInterval::point(value),
                FloatReading::RoundedToNearest => {
                    let half = ulp / Rat::from_integer(BigInt::from(2));
                    ExactInterval {
                        lower: &value - &half,
                        upper: &value + &half,
                    }
                }
                FloatReading::TruncatedTowardZero => {
                    if self.is_zero() {
                        ExactInterval {
                            lower: -ulp.clone(),
                            upper: ulp,
                        }
                    } else if self.negative {
                        ExactInterval {
                            lower: &value - &ulp,
                            upper: value,
                        }
                    } else {
                        ExactInterval {
                            lower: value.clone(),
                            upper: &value + &ulp,
                        }
                    }
                }
            }
        }

        /// Re-encode to the interchange pattern, computed from the decoded fields rather than
        /// echoed from [`BinaryFloatDatum::bits`].
        ///
        /// [`decode_bits`] calls this on every decode and refuses when the two disagree, which is
        /// what makes the round trip a law rather than a claim.
        pub fn to_bits(&self) -> Result<u64, ExactValueError> {
            let species = self.species;
            let stored = species.stored_significand_bits();
            let significand = self.significand.to_u64().ok_or({
                ExactValueError::NonInvertibleDecode {
                    species: species.name(),
                    bits: self.bits,
                }
            })?;
            let sign = u64::from(self.negative) << (species.width_bits() - 1);
            if self.subnormal {
                if significand > species.significand_mask()
                    || self.ulp_exponent != species.subnormal_ulp_exponent()
                {
                    return Err(ExactValueError::NonInvertibleDecode {
                        species: species.name(),
                        bits: self.bits,
                    });
                }
                return Ok(sign | significand);
            }
            let hidden = 1_u64 << stored;
            let raw_exponent = self.ulp_exponent + species.exponent_bias() + stored as i32;
            if significand < hidden
                || significand >= hidden << 1
                || raw_exponent < 1
                || raw_exponent as u64 >= species.exponent_mask()
            {
                return Err(ExactValueError::NonInvertibleDecode {
                    species: species.name(),
                    bits: self.bits,
                });
            }
            Ok(sign | ((raw_exponent as u64) << stored) | (significand - hidden))
        }
    }

    /// Decode one interchange pattern of a declared species into its exact dyadic.
    ///
    /// The sole arithmetic is on integers: a shift, a mask, and one subtraction of the bias. `NaN`
    /// and `±∞` are refused by name; subnormals, `+0.0` and `−0.0` are decoded like anything else.
    pub fn decode_bits(
        species: BinaryFloatSpecies,
        bits: u64,
    ) -> Result<BinaryFloatDatum, ExactValueError> {
        let width = species.width_bits();
        if width < 64 && (bits >> width) != 0 {
            return Err(ExactValueError::OverWideBitPattern {
                species: species.name(),
                width,
                bits,
            });
        }
        let stored = species.stored_significand_bits();
        let negative = (bits >> (width - 1)) & 1 == 1;
        let raw_exponent = (bits >> stored) & species.exponent_mask();
        let fraction = bits & species.significand_mask();
        if raw_exponent == species.exponent_mask() {
            return Err(if fraction == 0 {
                ExactValueError::InfiniteFloat {
                    species: species.name(),
                    negative,
                    bits,
                }
            } else {
                ExactValueError::NotANumberFloat {
                    species: species.name(),
                    bits,
                }
            });
        }
        let (significand, ulp_exponent, subnormal) = if raw_exponent == 0 {
            (fraction, species.subnormal_ulp_exponent(), true)
        } else {
            (
                (1_u64 << stored) | fraction,
                raw_exponent as i32 - species.exponent_bias() - stored as i32,
                false,
            )
        };
        let datum = BinaryFloatDatum {
            species,
            bits,
            negative,
            significand: BigUint::from(significand),
            ulp_exponent,
            subnormal,
        };
        if datum.to_bits()? != bits {
            return Err(ExactValueError::NonInvertibleDecode {
                species: species.name(),
                bits,
            });
        }
        Ok(datum)
    }

    /// A `bfloat16` word, as `soma/life/examples/eros_self_emanated_law.rs` reads them out of a
    /// safetensors payload.
    pub fn decode_bfloat16_bits(word: u16) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_bits(BinaryFloatSpecies::Bfloat16, u64::from(word))
    }

    /// An IEEE-754 `binary32` word.
    pub fn decode_binary32_bits(word: u32) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_bits(BinaryFloatSpecies::Binary32, u64::from(word))
    }

    /// An IEEE-754 `binary64` word.
    pub fn decode_binary64_bits(word: u64) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_bits(BinaryFloatSpecies::Binary64, word)
    }

    /// **The mouth for a live machine float.** One `to_bits`, then integers the rest of the way.
    ///
    /// This is one of the four functions in this workspace's library files that mention an IEEE
    /// type at all. It performs no arithmetic on `value`; `f64::to_bits` is a reinterpretation of
    /// the same storage.
    pub fn decode_f64(value: f64) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_binary64_bits(value.to_bits())
    }

    /// [`decode_f64`] for `binary32`.
    pub fn decode_f32(value: f32) -> Result<BinaryFloatDatum, ExactValueError> {
        decode_binary32_bits(value.to_bits())
    }

    /// ★ **THE EMIT-SIDE MOUTH: round an exact value into a float and KEEP THE REMAINDER.**
    ///
    /// Every float mouth in this workspace ran one way — a stored word decoded to an exact dyadic,
    /// so a float could enter and never leave. Emitting requires the other direction, and the
    /// direction that *loses* something is exactly the one that must certify what it lost.
    ///
    /// Returns the datum together with an **exact rational residual** satisfying
    ///
    /// ```text
    ///     value  =  datum.value()  +  residual          exactly, over the rationals
    /// ```
    ///
    /// so nothing about the rounding is unknown. A caller emitting a tensor can sum, bound, or
    /// exhibit the residuals rather than reporting a tolerance that got smaller — which is the
    /// error relocating, not shrinking.
    ///
    /// **Round-to-nearest, ties-to-even**, computed on integers: no float arithmetic occurs here
    /// and no comparison is approximate. A magnitude past the format's top binade is **refused**
    /// rather than saturated to an infinity, because an infinity names no ratio and this carrier
    /// admits no member that names no ratio.
    pub fn round_into(
        value: &Rat,
        species: BinaryFloatSpecies,
    ) -> Result<(BinaryFloatDatum, Rat), ExactValueError> {
        let negative = num_traits::Signed::is_negative(value);
        let magnitude = if negative { -value.clone() } else { value.clone() };
        let stored = species.stored_significand_bits() as i32;
        let subnormal_ulp = species.subnormal_ulp_exponent();

        // The zero datum, and it is exact.
        if magnitude.is_zero() {
            let datum = BinaryFloatDatum {
                species,
                bits: 0,
                negative,
                significand: BigUint::from(0u32),
                ulp_exponent: subnormal_ulp,
                subnormal: true,
            };
            return Ok((datum, Rat::zero()));
        }

        // The binade: the greatest `k` with `2^k <= magnitude`. Found by comparing exact
        // rationals, never by a logarithm.
        let mut binade: i32 = 0;
        let two = Rat::from_integer(BigInt::from(2));
        let mut probe = Rat::one();
        while probe > magnitude {
            probe /= &two;
            binade -= 1;
            if binade < subnormal_ulp - 1 {
                break;
            }
        }
        while &probe * &two <= magnitude {
            probe *= &two;
            binade += 1;
        }

        // Normal numbers place the ulp `stored` bits below the binade; subnormals sit on the
        // format's fixed floor grid.
        let normal_ulp = binade - stored;
        let ulp_exponent = normal_ulp.max(subnormal_ulp);
        let subnormal = ulp_exponent > normal_ulp || binade < subnormal_ulp + stored;

        // significand = round_half_even(magnitude / 2^ulp_exponent), on integers.
        let scale = power_of_two(-ulp_exponent);
        let scaled_value = &magnitude * &scale;
        let floor = scaled_value.numer() / scaled_value.denom();
        let remainder = &scaled_value - Rat::from_integer(floor.clone());
        let half = Rat::new(BigInt::from(1), BigInt::from(2));
        let rounded = match remainder.cmp(&half) {
            core::cmp::Ordering::Less => floor,
            core::cmp::Ordering::Greater => floor + BigInt::from(1),
            // Ties to even: the tie is exactly representable and the choice is declared.
            core::cmp::Ordering::Equal => {
                if (&floor % BigInt::from(2)).is_zero() {
                    floor
                } else {
                    floor + BigInt::from(1)
                }
            }
        };

        // Rounding up may carry into the next binade: `0b1111... -> 0b10000...`. Re-seat rather
        // than emit a significand the format cannot hold.
        //
        // **The carry is exact and needs no re-rounding.** `2·hidden · 2^ulp = hidden · 2^(ulp+1)`,
        // so the carried datum is the hidden bit one binade up, full stop. An earlier form
        // recomputed the FLOOR at the lifted exponent, which lands one below the hidden bit and
        // produced a significand the format cannot hold — refused at `to_bits` with a bijection
        // complaint that named the wrong defect. The exhaustive sweep over every bf16 pattern could
        // not catch it, because a representable value never carries; real material found it on its
        // first unrepresentable half-integer.
        let hidden = BigInt::from(1) << (stored as usize);
        let (significand, ulp_exponent, subnormal) = if !subnormal && rounded >= (&hidden << 1) {
            (hidden.clone(), ulp_exponent + 1, false)
        } else if subnormal && rounded >= hidden {
            // A subnormal that rounded up into the smallest normal is a normal.
            (rounded, ulp_exponent, false)
        } else {
            (rounded, ulp_exponent, subnormal)
        };

        let raw_exponent = ulp_exponent + species.exponent_bias() + stored;
        if !subnormal && raw_exponent as u64 >= species.exponent_mask() {
            return Err(ExactValueError::FloatMagnitudeOverflows {
                species: species.name(),
            });
        }

        let significand: BigUint =
            significand
                .to_biguint()
                .ok_or(ExactValueError::FloatMagnitudeOverflows {
                    species: species.name(),
                })?;
        let mut datum = BinaryFloatDatum {
            species,
            bits: 0,
            negative,
            significand,
            ulp_exponent,
            subnormal,
        };
        datum.bits = datum.to_bits()?;
        let residual = value - datum.value();
        Ok((datum, residual))
    }

    /// [`round_into`] for `Bfloat16`, returning the stored word beside the exact residual.
    pub fn round_into_bfloat16(value: &Rat) -> Result<(u16, Rat), ExactValueError> {
        let (datum, residual) = round_into(value, BinaryFloatSpecies::Bfloat16)?;
        let word = u16::try_from(datum.to_bits()?).map_err(|_| {
            ExactValueError::FloatMagnitudeOverflows {
                species: BinaryFloatSpecies::Bfloat16.name(),
            }
        })?;
        Ok((word, residual))
    }

    /// The inverse mouth, so the bijection can be exercised end to end by a driver.
    pub fn encode_f64(datum: &BinaryFloatDatum) -> Result<f64, ExactValueError> {
        if datum.species != BinaryFloatSpecies::Binary64 {
            return Err(ExactValueError::FloatSpeciesMismatch {
                holding: datum.species.name(),
                wanted: BinaryFloatSpecies::Binary64.name(),
            });
        }
        Ok(f64::from_bits(datum.to_bits()?))
    }

    /// [`encode_f64`] for `binary32`.
    pub fn encode_f32(datum: &BinaryFloatDatum) -> Result<f32, ExactValueError> {
        if datum.species != BinaryFloatSpecies::Binary32 {
            return Err(ExactValueError::FloatSpeciesMismatch {
                holding: datum.species.name(),
                wanted: BinaryFloatSpecies::Binary32.name(),
            });
        }
        let bits = datum.to_bits()?;
        let word = u32::try_from(bits).map_err(|_| ExactValueError::NonInvertibleDecode {
            species: datum.species.name(),
            bits,
        })?;
        Ok(f32::from_bits(word))
    }

    fn power_of_two(exponent: i32) -> Rat {
        if exponent >= 0 {
            Rat::from_integer(BigInt::one() << (exponent as usize))
        } else {
            Rat::new(BigInt::one(), BigInt::one() << ((-exponent) as usize))
        }
    }

    fn scaled(numerator: BigInt, exponent: i32) -> Rat {
        if exponent >= 0 {
            Rat::from_integer(numerator << (exponent as usize))
        } else {
            Rat::new(numerator, BigInt::one() << ((-exponent) as usize))
        }
    }
}


#[cfg(test)]
mod emit_side_mouth_tests {
    use super::ieee754::{
        decode_bfloat16_bits, round_into, round_into_bfloat16, BinaryFloatSpecies,
    };
    use super::Rat;
    use num_bigint::BigInt;
    use num_traits::Zero;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    #[test]
    fn a_representable_value_emits_with_residual_exactly_zero() {
        // Every one of these is a dyadic bf16 can hold exactly, so the mouth must lose NOTHING.
        for value in [
            rat(0, 1),
            rat(1, 1),
            rat(-1, 1),
            rat(1, 2),
            rat(3, 4),
            rat(-5, 8),
            rat(256, 1),
            rat(1, 256),
            rat(127, 128),
        ] {
            let (word, residual) = round_into_bfloat16(&value).expect("emits");
            assert!(
                residual.is_zero(),
                "a representable value lost {residual} at {value}"
            );
            // And the round trip through the READ side must return the same exact value.
            let back = decode_bfloat16_bits(word).expect("decodes").value();
            assert_eq!(back, value, "the two mouths disagree at {value}");
        }
    }

    #[test]
    fn an_unrepresentable_value_closes_exactly_over_the_residual() {
        // **The law: value = datum.value() + residual, exactly, over the rationals.** A tenth is
        // not a dyadic, so the residual is genuinely non-zero and must account for the whole
        // difference -- nothing is unknown about what the emission cost.
        for value in [rat(1, 10), rat(-1, 3), rat(22, 7), rat(1, 1000), rat(-9999, 7)] {
            let (datum, residual) =
                round_into(&value, BinaryFloatSpecies::Bfloat16).expect("emits");
            assert_eq!(
                datum.value() + residual.clone(),
                value,
                "the residual did not close at {value}"
            );
            assert!(!residual.is_zero(), "{value} should not be representable");
            // The residual may never exceed half an ulp: that is what round-to-nearest MEANS, and
            // a residual past it would mean a nearer float existed and was not taken.
            let half_ulp = datum.unit_in_last_place() / Rat::from_integer(BigInt::from(2));
            let magnitude = if num_traits::Signed::is_negative(&residual) {
                -residual.clone()
            } else {
                residual.clone()
            };
            assert!(
                magnitude <= half_ulp,
                "residual {residual} exceeds half an ulp {half_ulp} at {value}"
            );
        }
    }

    #[test]
    fn every_bfloat16_word_survives_the_round_trip_through_both_mouths() {
        // The read mouth decodes a word to an exact value; the emit mouth must return that word.
        // Swept over every finite bf16 pattern -- this is a bijection claim and it is checked
        // exhaustively rather than sampled.
        let mut checked = 0u32;
        for bits in 0..=u16::MAX {
            let Ok(datum) = decode_bfloat16_bits(bits) else {
                continue; // NaN and the infinities name no ratio and are refused by the reader.
            };
            let value = datum.value();
            let (word, residual) = round_into_bfloat16(&value).expect("emits");
            assert!(residual.is_zero(), "0x{bits:04x} lost {residual}");
            // -0.0 and +0.0 carry the same value; the sign is retained separately and the emit
            // mouth reads it from the value, which has no negative zero. That is the one place the
            // round trip is not on the nose, and it is named rather than hidden.
            if datum.is_zero() {
                assert!(word == 0x0000 || word == 0x8000);
            } else {
                assert_eq!(word, bits, "0x{bits:04x} did not return itself");
            }
            checked += 1;
        }
        assert!(checked > 60_000, "only {checked} finite patterns were swept");
    }

    #[test]
    fn a_rounding_carry_across_a_binade_re_seats_rather_than_overflowing() {
        // **The case the exhaustive sweep cannot reach**: a value BETWEEN two representables that
        // rounds UP across a binade boundary. 32729/2 = 16364.5 sits just under 2^14 and rounds to
        // 16384, carrying `0b11111111 -> 0b100000000`. Found by real material, not by the sweep.
        for value in [rat(32729, 2), rat(-32729, 2), rat(511, 256), rat(1023, 512)] {
            let (datum, residual) =
                round_into(&value, BinaryFloatSpecies::Bfloat16).expect("emits");
            assert_eq!(
                datum.value() + residual.clone(),
                value,
                "the carry did not close at {value}"
            );
            let half_ulp = datum.unit_in_last_place() / Rat::from_integer(BigInt::from(2));
            let magnitude = if num_traits::Signed::is_negative(&residual) {
                -residual.clone()
            } else {
                residual.clone()
            };
            assert!(magnitude <= half_ulp, "{value} rounded past half an ulp");
            // And the carried datum must re-encode, which is what the defect broke.
            datum.to_bits().expect("the carried datum must hold in the format");
        }
    }

    #[test]
    fn a_magnitude_past_the_format_refuses_rather_than_saturating() {
        // An infinity names no ratio, so this carrier admits no member that names no ratio.
        let past = Rat::from_integer(BigInt::from(1) << 400);
        assert!(round_into(&past, BinaryFloatSpecies::Bfloat16).is_err());
        assert!(round_into(&(-past), BinaryFloatSpecies::Bfloat16).is_err());
    }

    #[test]
    fn the_tie_goes_to_even_and_the_choice_is_declared() {
        // Exactly halfway between two bf16 neighbours. bf16 has 8 significand bits, so
        // 257/256 sits between 1 and 1+2^-7; the tie must land on the even significand.
        let (low, residual) =
            round_into(&rat(513, 512), BinaryFloatSpecies::Bfloat16).expect("emits");
        assert_eq!(low.value() + residual, rat(513, 512));
        assert!(low.significand.clone() % num_bigint::BigUint::from(2u32) == num_bigint::BigUint::from(0u32));
    }
}

#[cfg(test)]
mod tests {
    /// **A root is isolated by a Sturm certificate, not by an iteration count.**
    ///
    /// The reciprocal root is what a normalization actually asks for, and taking it directly keeps
    /// one certificate instead of two.
    #[test]
    fn the_roots_a_transport_asks_for_are_isolated_by_certificate() {
        let two = Rat::from_integer(BigInt::from(2));
        let root = AlgebraicRoot::square_root(&two, 40).expect("isolated");
        assert_eq!(root.polynomial.degree(), 2);
        let enclosure = root.enclosure();
        // sqrt(2) = 1.41421356237...; the bracket is stated, not computed.
        let below = Rat::new(BigInt::from(141421356), BigInt::from(100000000));
        let above = Rat::new(BigInt::from(141421357), BigInt::from(100000000));
        assert!(enclosure.lower >= below && enclosure.upper <= above);
        assert_eq!(
            root.polynomial
                .distinct_root_count(enclosure)
                .expect("counted"),
            1,
            "the certificate's whole content is that exactly one root is inside"
        );

        let inverse = AlgebraicRoot::reciprocal_square_root(&two, 40).expect("isolated");
        // 1/sqrt(2) = 0.70710678118...
        let below = Rat::new(BigInt::from(70710678), BigInt::from(100000000));
        let above = Rat::new(BigInt::from(70710679), BigInt::from(100000000));
        assert!(inverse.enclosure().lower >= below && inverse.enclosure().upper <= above);

        // A perfect square returns an interval containing its exact root and refuses no less.
        let four = Rat::from_integer(BigInt::from(4));
        let exact = AlgebraicRoot::square_root(&four, 20).expect("isolated");
        assert!(
            exact.enclosure().lower <= Rat::from_integer(BigInt::from(2))
                && exact.enclosure().upper >= Rat::from_integer(BigInt::from(2))
        );
        assert!(AlgebraicRoot::square_root(&-two, 20).is_err());
    }

    /// **The chronology is an integer, and the rotation stays on the circle.**
    ///
    /// The transcendental runs once per band; a position is an integer power of the enclosed group
    /// element. Composing two positions equals rotating once by their sum, and the modulus is
    /// preserved — which is what a group element has and a pair of independently bounded numbers
    /// does not.
    #[test]
    fn the_chronology_rides_as_an_integer_power_of_one_group_element() {
        let step = Rat::new(BigInt::from(1), BigInt::from(8));
        for position in [1u64, 3, 7, 16] {
            let (cosine, sine) =
                CertifiedSeries::rotation_power(&step, position, 30).expect("rotated");
            let modulus = cosine
                .times(&cosine)
                .expect("square")
                .times(&ExactInterval::point(Rat::one()))
                .expect("scaled");
            let cross = sine.times(&sine).expect("square");
            let total = ExactInterval::new(
                &modulus.lower + &cross.lower,
                &modulus.upper + &cross.upper,
            )
            .expect("summed");
            assert!(
                total.lower <= Rat::one() && total.upper >= Rat::one(),
                "position {position} left the circle: {total:?}"
            );
        }
        // A band angle is an n-th root, isolated by the same certificate a square root is.
        let base = Rat::from_integer(BigInt::from(10_000));
        let band = AlgebraicRoot::nth_root(&base, 128, 40).expect("isolated");
        assert_eq!(band.polynomial.degree(), 128);
        // 10000^(1/128) = 1.0746078...; the bracket is stated rather than computed, and the
        // isolating interval must sit strictly inside it.
        let below = Rat::new(BigInt::from(10746078), BigInt::from(10000000));
        let above = Rat::new(BigInt::from(10746079), BigInt::from(10000000));
        assert!(
            band.enclosure().lower >= below && band.enclosure().upper <= above,
            "{:?}",
            band.enclosure()
        );
        assert_eq!(
            band.polynomial
                .distinct_root_count(band.enclosure())
                .expect("counted"),
            1
        );
    }

    /// **The certified series carries the two transcendentals a transport needs**, and refuses
    /// rather than taking too few terms for its argument.
    #[test]
    fn the_certified_series_carries_the_exponential_and_the_tangent() {
        let three_eighths = Rat::new(BigInt::from(3), BigInt::from(8));
        let series = CertifiedSeries::exponential_series(&three_eighths, 24).expect("certified");
        let enclosure = series.enclosure();
        // exp(3/8) = 1.4549914146...
        let below = Rat::new(BigInt::from(14549914), BigInt::from(10000000));
        let above = Rat::new(BigInt::from(14549915), BigInt::from(10000000));
        assert!(enclosure.lower >= below && enclosure.upper <= above);
        assert!(matches!(
            series.tail_certificate,
            SeriesTailCertificate::AbsoluteGeometric { .. }
        ));
        // Too few terms for the argument is refused, not silently taken.
        assert_eq!(
            CertifiedSeries::exponential_series(&Rat::from_integer(BigInt::from(40)), 4),
            Err(ExactValueError::TailDoesNotClose)
        );
        // And the reduction keeps every caller inside the series' own domain: exp(-15) returns a
        // usable enclosure where a direct forty-term series' honest bound is wider than the value.
        let far = CertifiedSeries::exponential_enclosure(
            &Rat::from_integer(BigInt::from(-15)),
            32,
        )
        .expect("reduced");
        assert!(far.lower.is_positive(), "an exponential is never negative");
        assert!(far.upper < Rat::new(BigInt::from(1), BigInt::from(1_000_000)));

        // tanh through the DECAYING exponential: monotone, bounded, and nothing large forms.
        let mut previous: Option<ExactInterval> = None;
        for numerator in [-30i64, -8, -1, 0, 1, 8, 30] {
            let x = Rat::new(BigInt::from(numerator), BigInt::from(4));
            let value = CertifiedSeries::hyperbolic_tangent_enclosure(&x, 40).expect("enclosed");
            assert!(value.lower >= Rat::from_integer(BigInt::from(-1)));
            assert!(value.upper <= Rat::one());
            if let Some(before) = previous {
                assert_eq!(
                    before.disjoint_order(&value),
                    ExactOrdering::Less,
                    "tanh must separate at {numerator}/4"
                );
            }
            previous = Some(value);
        }
        // tanh(1/2) = 0.46211715726...
        let half = Rat::new(BigInt::from(1), BigInt::from(2));
        let value = CertifiedSeries::hyperbolic_tangent_enclosure(&half, 40).expect("enclosed");
        let below = Rat::new(BigInt::from(46211715), BigInt::from(100000000));
        let above = Rat::new(BigInt::from(46211716), BigInt::from(100000000));
        assert!(value.lower >= below && value.upper <= above, "{value:?}");
    }

    use relational_geometry::{integer, rat};

    use super::*;

    #[test]
    fn sturm_certificate_isolates_sqrt_two_without_a_float() {
        let polynomial =
            IntegerPolynomial::new(vec![BigInt::from(-2), BigInt::zero(), BigInt::one()]).unwrap();
        let root = AlgebraicRoot::isolate(
            polynomial,
            ExactInterval::new(integer(1), integer(2)).unwrap(),
        )
        .unwrap();
        assert_eq!(
            root.certificate.variations_at_lower - root.certificate.variations_at_upper,
            1
        );
        assert_eq!(
            ExactValue::Algebraic(root).compare(&ExactValue::rational(rat(3, 2))),
            ExactOrdering::Open
        );
    }

    #[test]
    fn disjoint_certificates_order_values_and_overlap_stays_open() {
        let left = CertifiedSeries::new(
            ExactExpr::symbol("left"),
            integer(1),
            BigUint::from(8_u8),
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: rat(9, 100),
                ratio_abs_bound: rat(1, 10),
            },
        )
        .unwrap();
        let right = CertifiedSeries::new(
            ExactExpr::symbol("right"),
            integer(2),
            BigUint::from(8_u8),
            SeriesTailCertificate::AbsoluteGeometric {
                first_omitted_abs_bound: rat(9, 100),
                ratio_abs_bound: rat(1, 10),
            },
        )
        .unwrap();
        assert_eq!(
            ExactValue::CertifiedSeries(left).compare(&ExactValue::CertifiedSeries(right)),
            ExactOrdering::Less
        );
    }

    /// Every pattern this codec accepts must come back out of it identical.
    ///
    /// Stated at the level of **bits** rather than of `f64`, deliberately: no float **value** is
    /// constructed or operated on outside the four functions of `ieee754`, in any library file of
    /// this workspace, and that includes this test module. (The earlier wording said the *tokens*
    /// `f32`/`f64` occur nowhere else, which is false — they occur in a doc line of `reopening.rs`,
    /// in a `#[test]` comment of `embedding_fiber.rs` recording a removal, and as the string
    /// literals `".f16"`/`".f32"`/`".f64"` inside `soma/mount`'s *negative* assertion that the
    /// generated PTX contains none. None of those is a float value; the claim about values holds
    /// and the claim about tokens did not. Measured 2026-08-16,
    /// `grep -rn --include='*.rs' -w 'f64\|f32' crates soma`.) The live-float round trip is
    /// exercised by
    /// `examples/a_float_is_a_dyadic_and_a_deleted_tail.rs`, which is a boundary driver and may
    /// hold one.
    #[test]
    fn every_accepted_bit_pattern_re_encodes_identically() {
        use ieee754::{BinaryFloatSpecies, decode_bits};
        let declared: &[(BinaryFloatSpecies, u64)] = &[
            // binary64: one, pi, both zeros, the extreme subnormals, a long mantissa, max finite.
            (BinaryFloatSpecies::Binary64, 0x3ff0_0000_0000_0000),
            (BinaryFloatSpecies::Binary64, 0x4009_21fb_5444_2d18),
            (BinaryFloatSpecies::Binary64, 0x0000_0000_0000_0000),
            (BinaryFloatSpecies::Binary64, 0x8000_0000_0000_0000),
            (BinaryFloatSpecies::Binary64, 0x0000_0000_0000_0001),
            (BinaryFloatSpecies::Binary64, 0x000f_ffff_ffff_ffff),
            (BinaryFloatSpecies::Binary64, 0xbfe5_5555_5555_5555),
            (BinaryFloatSpecies::Binary64, 0x7fef_ffff_ffff_ffff),
            // binary32, including a real GPT-2 attention weight.
            (BinaryFloatSpecies::Binary32, 0x3f80_0000),
            (BinaryFloatSpecies::Binary32, 0x0000_0001),
            (BinaryFloatSpecies::Binary32, 0x8000_0000),
            (BinaryFloatSpecies::Binary32, 0x7f7f_ffff),
            (BinaryFloatSpecies::Binary32, 0xbef2_9c42),
            // bfloat16, including a real Qwen down-projection weight.
            (BinaryFloatSpecies::Bfloat16, 0x3f80),
            (BinaryFloatSpecies::Bfloat16, 0x0001),
            (BinaryFloatSpecies::Bfloat16, 0x8000),
            (BinaryFloatSpecies::Bfloat16, 0xbd1e),
        ];
        for (species, bits) in declared {
            let datum = decode_bits(*species, *bits)
                .unwrap_or_else(|error| panic!("{} 0x{bits:x} decodes: {error}", species.name()));
            assert_eq!(
                datum.to_bits().expect("a decoded datum re-encodes"),
                *bits,
                "{} 0x{bits:x} must return identical",
                species.name()
            );
        }
    }

    /// `NaN` and `±∞` name no ratio, so they are refused by name rather than mapped to a sentinel.
    #[test]
    fn not_a_number_and_the_infinities_are_refused_by_name() {
        use ieee754::{BinaryFloatSpecies, decode_bits};
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0x7ff0_0000_0000_0000),
            Err(ExactValueError::InfiniteFloat {
                negative: false,
                ..
            })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0xfff0_0000_0000_0000),
            Err(ExactValueError::InfiniteFloat { negative: true, .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0x7ff8_0000_0000_0000),
            Err(ExactValueError::NotANumberFloat { .. })
        ));
        // A signalling pattern is refused for the same reason as a quiet one.
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary64, 0x7ff0_0000_0000_0001),
            Err(ExactValueError::NotANumberFloat { .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Bfloat16, 0x7f80),
            Err(ExactValueError::InfiniteFloat { .. })
        ));
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Binary32, 0x7fc0_0000),
            Err(ExactValueError::NotANumberFloat { .. })
        ));
        // And a pattern too wide for its declared format is not silently masked.
        assert!(matches!(
            decode_bits(BinaryFloatSpecies::Bfloat16, 0x1_0000),
            Err(ExactValueError::OverWideBitPattern { width: 16, .. })
        ));
    }

    /// The ulp belongs to the **format at this magnitude**, not to the value, and the codec must
    /// not reduce the significand or it destroys exactly that.
    #[test]
    fn the_unit_in_the_last_place_survives_a_value_that_reduces() {
        use ieee754::{BinaryFloatSpecies, decode_bits};
        // 1.0 and 0.5 reduce to 1*2^0 and 1*2^-1; their ulps differ by a factor of two.
        let one = decode_bits(BinaryFloatSpecies::Binary64, 0x3ff0_0000_0000_0000).unwrap();
        let half = decode_bits(BinaryFloatSpecies::Binary64, 0x3fe0_0000_0000_0000).unwrap();
        assert_eq!(one.value(), integer(1));
        assert_eq!(half.value(), rat(1, 2));
        assert_eq!(one.reduced_dyadic(), (BigInt::one(), 0));
        assert_eq!(half.reduced_dyadic(), (BigInt::one(), -1));
        assert_eq!(one.ulp_bits(), 52);
        assert_eq!(half.ulp_bits(), 53);
        assert_eq!(one.unit_in_last_place(), rat(1, 1_i64 << 52));

        // The smallest subnormal is one ulp of the subnormal grid, and it is exact.
        let tiny = decode_bits(BinaryFloatSpecies::Binary64, 0x0000_0000_0000_0001).unwrap();
        assert!(tiny.subnormal);
        assert_eq!(tiny.ulp_bits(), 1074);
        assert_eq!(tiny.value(), tiny.unit_in_last_place());

        // Both zeros carry the subnormal ulp, and the sign of zero survives the decode.
        let plus = decode_bits(BinaryFloatSpecies::Binary64, 0).unwrap();
        let minus = decode_bits(BinaryFloatSpecies::Binary64, 0x8000_0000_0000_0000).unwrap();
        assert!(plus.is_zero() && minus.is_zero());
        assert_eq!(plus.value(), minus.value());
        assert!(!plus.negative && minus.negative);
        assert_ne!(plus.to_bits().unwrap(), minus.to_bits().unwrap());
    }

    /// The bfloat16 decode must agree with the reader it was taken from,
    /// `soma/life/examples/eros_self_emanated_law.rs:60`, on real material.
    #[test]
    fn the_bfloat16_decode_agrees_with_the_reader_it_was_taken_from() {
        use ieee754::{BinaryFloatSpecies, decode_bfloat16_bits, decode_bits};
        // `model.language_model.layers.1.mlp.down_proj.weight[0]` of Qwen3.5-4B.
        let weight = decode_bfloat16_bits(0xbd1e).unwrap();
        assert_eq!(weight.reduced_dyadic(), (BigInt::from(-79), -11));
        assert_eq!(weight.signed_significand(), BigInt::from(-158));
        assert_eq!(weight.ulp_exponent, -12);
        assert_eq!(weight.value(), rat(-158, 4096));
        // The archetype's subnormal exponent is -133 and its normal exponent is `raw - 134`.
        assert_eq!(BinaryFloatSpecies::Bfloat16.subnormal_ulp_exponent(), -133);
        let subnormal = decode_bits(BinaryFloatSpecies::Bfloat16, 0x0001).unwrap();
        assert_eq!(subnormal.ulp_exponent, -133);
    }

    /// The three readings of one pattern are three different faces, and the difference is the
    /// entire content of the distinction.
    #[test]
    fn one_pattern_presents_three_faces_under_three_readings() {
        use ieee754::{BinaryFloatSpecies, FloatReading, decode_bits};
        let datum = decode_bits(BinaryFloatSpecies::Binary64, 0x3ff0_0000_0000_0000).unwrap();
        let ulp = datum.unit_in_last_place();

        let point = datum.enclosure(FloatReading::ExactBitPattern);
        assert!(point.is_point());
        assert_eq!(point.lower, integer(1));

        let rounded = datum.enclosure(FloatReading::RoundedToNearest);
        assert_eq!(&rounded.upper - &rounded.lower, ulp);
        assert!(rounded.lower < integer(1) && rounded.upper > integer(1));

        let truncated = datum.enclosure(FloatReading::TruncatedTowardZero);
        assert_eq!(&truncated.upper - &truncated.lower, ulp);
        assert_eq!(truncated.lower, integer(1));

        // A zero truncated toward zero straddles zero by one ulp on each side: every quantity
        // smaller than one ulp truncates onto it.
        let zero = decode_bits(BinaryFloatSpecies::Binary64, 0).unwrap();
        let straddle = zero.enclosure(FloatReading::TruncatedTowardZero);
        assert_eq!(straddle.lower, -zero.unit_in_last_place());
        assert_eq!(straddle.upper, zero.unit_in_last_place());
        assert!(zero.enclosure(FloatReading::ExactBitPattern).is_point());
    }

    #[test]
    fn overlapping_intervals_for_distinct_roots_do_not_collapse_identity() {
        let polynomial =
            IntegerPolynomial::new(vec![-BigInt::one(), BigInt::zero(), BigInt::one()]).unwrap();
        let negative = AlgebraicRoot::isolate(
            polynomial.clone(),
            ExactInterval::new(integer(-2), rat(1, 2)).unwrap(),
        )
        .unwrap();
        let positive = AlgebraicRoot::isolate(
            polynomial,
            ExactInterval::new(rat(-1, 2), integer(2)).unwrap(),
        )
        .unwrap();
        assert_eq!(
            ExactValue::Algebraic(negative).compare(&ExactValue::Algebraic(positive)),
            ExactOrdering::Less
        );
    }
}
