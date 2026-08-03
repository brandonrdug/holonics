//! Typed exact values used by causal parameters and future geometric laws.
//!
//! A decimal approximation is never a member of this carrier.  Values which
//! cannot yet be ordered from their exact certificates return `Open` rather
//! than falling through to an epsilon comparison.

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

#[cfg(test)]
mod tests {
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
