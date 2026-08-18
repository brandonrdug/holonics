//! Rational enclosures for receiver-relative complex analysis.
//!
//! No IEEE scalar enters this module.  Transcendental values are carried as
//! closed intervals with `BigRational` endpoints obtained from finite series
//! plus explicit rational remainders.  A complex zero is therefore observed
//! as a refinement lineage of rational receiver boxes, never as a decimal
//! coordinate.

use std::cmp::{max, min};
use std::fmt;

use num_bigint::{BigInt, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact::{Rat, format_rat, integer, ratio};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RatInterval {
    pub lower: Rat,
    pub upper: Rat,
}

impl RatInterval {
    pub fn new(lower: Rat, upper: Rat) -> Self {
        assert!(lower <= upper, "an interval must be ordered");
        Self { lower, upper }
    }

    pub fn point(value: Rat) -> Self {
        Self {
            lower: value.clone(),
            upper: value,
        }
    }

    pub fn symmetric(radius: Rat) -> Self {
        assert!(!radius.is_negative(), "a radius cannot be negative");
        Self::new(-radius.clone(), radius)
    }

    pub fn hull(&self, other: &Self) -> Self {
        Self::new(
            min(self.lower.clone(), other.lower.clone()),
            max(self.upper.clone(), other.upper.clone()),
        )
    }

    pub fn midpoint(&self) -> Rat {
        (&self.lower + &self.upper) / integer(2)
    }

    pub fn width(&self) -> Rat {
        &self.upper - &self.lower
    }

    pub fn contains_zero(&self) -> bool {
        self.lower <= Rat::zero() && self.upper >= Rat::zero()
    }

    pub fn abs_upper(&self) -> Rat {
        max(self.lower.abs(), self.upper.abs())
    }

    pub fn add(&self, other: &Self) -> Self {
        Self::new(&self.lower + &other.lower, &self.upper + &other.upper)
    }

    pub fn translate(&self, value: &Rat) -> Self {
        Self::new(&self.lower + value, &self.upper + value)
    }

    pub fn neg(&self) -> Self {
        Self::new(-self.upper.clone(), -self.lower.clone())
    }

    pub fn subtract(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub fn multiply(&self, other: &Self) -> Self {
        let products = [
            &self.lower * &other.lower,
            &self.lower * &other.upper,
            &self.upper * &other.lower,
            &self.upper * &other.upper,
        ];
        let lower = products.iter().min().expect("four products").clone();
        let upper = products.iter().max().expect("four products").clone();
        Self::new(lower, upper)
    }

    pub fn scale(&self, value: &Rat) -> Self {
        self.multiply(&Self::point(value.clone()))
    }

    pub fn square(&self) -> Self {
        let lower_square = &self.lower * &self.lower;
        let upper_square = &self.upper * &self.upper;
        if self.contains_zero() {
            Self::new(Rat::zero(), max(lower_square, upper_square))
        } else {
            Self::new(
                min(lower_square.clone(), upper_square.clone()),
                max(lower_square, upper_square),
            )
        }
    }

    pub fn reciprocal(&self) -> Result<Self, ExactAnalysisError> {
        if self.contains_zero() {
            return Err(ExactAnalysisError::DivisionByIntervalContainingZero);
        }
        Ok(Self::new(
            Rat::one() / &self.upper,
            Rat::one() / &self.lower,
        ))
    }

    pub fn divide(&self, other: &Self) -> Result<Self, ExactAnalysisError> {
        Ok(self.multiply(&other.reciprocal()?))
    }

    /// Enclose this interval on the grid `2^-bits Z`.
    ///
    /// This is a grain change, not a floating conversion: both returned
    /// endpoints are exact ratios and rounding always moves outwards.
    pub fn round_out(&self, bits: u32) -> Self {
        Self::new(
            dyadic_floor(&self.lower, bits),
            dyadic_ceil(&self.upper, bits),
        )
    }
}

impl fmt::Display for RatInterval {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "[{},{}]",
            format_rat(&self.lower),
            format_rat(&self.upper)
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RatComplex {
    pub re: Rat,
    pub im: Rat,
}

impl RatComplex {
    pub fn new(re: Rat, im: Rat) -> Self {
        Self { re, im }
    }

    pub fn zero() -> Self {
        Self::new(Rat::zero(), Rat::zero())
    }

    pub fn cross(&self, other: &Self) -> Rat {
        &self.re * &other.im - &self.im * &other.re
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComplexInterval {
    pub re: RatInterval,
    pub im: RatInterval,
}

impl ComplexInterval {
    pub fn new(re: RatInterval, im: RatInterval) -> Self {
        Self { re, im }
    }

    pub fn point(value: RatComplex) -> Self {
        Self::new(RatInterval::point(value.re), RatInterval::point(value.im))
    }

    pub fn zero() -> Self {
        Self::point(RatComplex::zero())
    }

    pub fn midpoint(&self) -> RatComplex {
        RatComplex::new(self.re.midpoint(), self.im.midpoint())
    }

    pub fn hull(&self, other: &Self) -> Self {
        Self::new(self.re.hull(&other.re), self.im.hull(&other.im))
    }

    pub fn contains_origin(&self) -> bool {
        self.re.contains_zero() && self.im.contains_zero()
    }

    pub fn add(&self, other: &Self) -> Self {
        Self::new(self.re.add(&other.re), self.im.add(&other.im))
    }

    pub fn neg(&self) -> Self {
        Self::new(self.re.neg(), self.im.neg())
    }

    pub fn subtract(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    pub fn scale(&self, value: &Rat) -> Self {
        Self::new(self.re.scale(value), self.im.scale(value))
    }

    pub fn multiply(&self, other: &Self) -> Self {
        let real = self
            .re
            .multiply(&other.re)
            .subtract(&self.im.multiply(&other.im));
        let imaginary = self
            .re
            .multiply(&other.im)
            .add(&self.im.multiply(&other.re));
        Self::new(real, imaginary)
    }

    pub fn conjugate(&self) -> Self {
        Self::new(self.re.clone(), self.im.neg())
    }

    pub fn reciprocal(&self) -> Result<Self, ExactAnalysisError> {
        let norm = self.re.square().add(&self.im.square());
        if norm.contains_zero() {
            return Err(ExactAnalysisError::DivisionByIntervalContainingZero);
        }
        Ok(Self::new(
            self.re.divide(&norm)?,
            self.im.neg().divide(&norm)?,
        ))
    }

    pub fn divide(&self, other: &Self) -> Result<Self, ExactAnalysisError> {
        Ok(self.multiply(&other.reciprocal()?))
    }

    pub fn add_disc(&self, radius: &Rat) -> Self {
        let error = RatInterval::symmetric(radius.clone());
        Self::new(self.re.add(&error), self.im.add(&error))
    }

    pub fn l1_upper(&self) -> Rat {
        self.re.abs_upper() + self.im.abs_upper()
    }

    pub fn round_out(&self, bits: u32) -> Self {
        Self::new(self.re.round_out(bits), self.im.round_out(bits))
    }
}

impl fmt::Display for ComplexInterval {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}+i{}", self.re, self.im)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComplexReceiverBox {
    pub sigma: RatInterval,
    pub tau: RatInterval,
}

impl ComplexReceiverBox {
    pub fn new(sigma: RatInterval, tau: RatInterval) -> Self {
        Self { sigma, tau }
    }

    pub fn point(sigma: Rat, tau: Rat) -> Self {
        Self::new(RatInterval::point(sigma), RatInterval::point(tau))
    }

    pub fn midpoint(&self) -> RatComplex {
        RatComplex::new(self.sigma.midpoint(), self.tau.midpoint())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactSeriesConfig {
    /// Every intermediate enclosure is returned to this exact dyadic grain.
    pub dyadic_bits: u32,
    pub euler_maclaurin_start: u32,
    pub euler_maclaurin_order: u32,
    pub log_terms: u32,
    pub exponential_terms: u32,
    pub trigonometric_terms: u32,
}

impl Default for ExactSeriesConfig {
    fn default() -> Self {
        Self {
            dyadic_bits: 160,
            euler_maclaurin_start: 24,
            euler_maclaurin_order: 14,
            log_terms: 48,
            exponential_terms: 28,
            trigonometric_terms: 24,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaEvaluation {
    pub receiver: ComplexReceiverBox,
    pub value: ComplexInterval,
    pub finite_terms: u32,
    pub correction_order: u32,
    pub remainder_radius: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaJetEvaluation {
    pub receiver: ComplexReceiverBox,
    pub value: ComplexInterval,
    pub derivative: ComplexInterval,
    pub remainder_radius: Rat,
    pub derivative_remainder_radius: Rat,
}

#[derive(Debug, Error)]
pub enum ExactAnalysisError {
    #[error("division by an interval containing zero")]
    DivisionByIntervalContainingZero,
    #[error("the logarithm requires a positive rational input")]
    NonPositiveLogarithm,
    #[error("the Euler--Maclaurin receiver must have positive real part")]
    NonPositiveSigma,
    #[error("the Euler--Maclaurin receiver intersects the zeta pole")]
    ZetaPoleInReceiver,
    #[error("a boundary segment remained unresolved at depth {0}")]
    UnresolvedBoundary(u32),
    #[error("no exact ray avoided every polygon vertex")]
    NoAdmissibleWindingRay,
    #[error("Borwein's chain needs a depth of at least one")]
    BorweinDepthTooSmall,
    #[error("Borwein weight {0} did not clear its denominator and is not an integer")]
    BorweinWeightNotIntegral(u32),
}

fn factorial(value: u32) -> BigInt {
    (1..=value).fold(BigInt::one(), |product, term| product * BigInt::from(term))
}

fn floor_div(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    debug_assert!(denominator.is_positive());
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if numerator.is_negative() && !remainder.is_zero() {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

fn dyadic_floor(value: &Rat, bits: u32) -> Rat {
    let denominator = BigInt::one() << bits;
    let scaled_numerator = value.numer() << bits;
    ratio(floor_div(&scaled_numerator, value.denom()), denominator)
}

fn dyadic_ceil(value: &Rat, bits: u32) -> Rat {
    -dyadic_floor(&(-value.clone()), bits)
}

fn atanh_log_unit_interval(value: &Rat, terms: u32, bits: u32) -> RatInterval {
    debug_assert!(*value >= Rat::one() && *value <= integer(2));
    let z = (value - Rat::one()) / (value + Rat::one());
    let mut partial = RatInterval::point(Rat::zero());
    let mut power = RatInterval::point(z.clone());
    let square = &z * &z;
    for index in 0..terms {
        let coefficient = integer(2) / integer(i64::from(2 * index + 1));
        let term = power.scale(&coefficient).round_out(bits);
        partial = partial.add(&term).round_out(bits);
        power = power
            .multiply(&RatInterval::point(square.clone()))
            .round_out(bits);
    }
    let next_degree = 2 * terms + 1;
    let remainder =
        integer(2) * power.upper / (integer(i64::from(next_degree)) * (Rat::one() - square));
    RatInterval::new(partial.lower, partial.upper + remainder).round_out(bits)
}

pub fn log_rational_interval(
    value: &Rat,
    terms: u32,
    bits: u32,
) -> Result<RatInterval, ExactAnalysisError> {
    if !value.is_positive() {
        return Err(ExactAnalysisError::NonPositiveLogarithm);
    }
    if value.is_one() {
        return Ok(RatInterval::point(Rat::zero()));
    }

    let mut reduced = value.clone();
    let mut exponent = 0i64;
    while reduced >= integer(2) {
        reduced /= integer(2);
        exponent += 1;
    }
    while reduced < Rat::one() {
        reduced *= integer(2);
        exponent -= 1;
    }

    let reduced_log = atanh_log_unit_interval(&reduced, terms, bits);
    let log_two = atanh_log_unit_interval(&integer(2), terms, bits);
    let scale = integer(exponent);
    Ok(reduced_log.add(&log_two.scale(&scale)).round_out(bits))
}

fn exp_nonnegative_point(value: &Rat, terms: u32, bits: u32) -> RatInterval {
    debug_assert!(!value.is_negative());
    if value.is_zero() {
        return RatInterval::point(Rat::one());
    }

    let mut reduced = value.clone();
    let mut squarings = 0u32;
    let eighth = ratio(BigInt::one(), BigInt::from(8));
    while reduced > eighth {
        reduced /= integer(2);
        squarings += 1;
    }

    let mut partial = RatInterval::point(Rat::one());
    let mut term = RatInterval::point(Rat::one());
    for index in 1..=terms {
        let coefficient = &reduced / integer(i64::from(index));
        term = term.scale(&coefficient).round_out(bits);
        partial = partial.add(&term).round_out(bits);
    }
    let next = term.upper * &reduced / integer(i64::from(terms + 1));
    let remainder = next / (Rat::one() - &reduced);
    let mut result = RatInterval::new(partial.lower, partial.upper + remainder).round_out(bits);
    for _ in 0..squarings {
        result = result.square().round_out(bits);
    }
    result
}

pub fn exp_rational_interval(value: &Rat, terms: u32, bits: u32) -> RatInterval {
    if value.is_negative() {
        let positive = exp_nonnegative_point(&(-value.clone()), terms, bits);
        RatInterval::new(Rat::one() / positive.upper, Rat::one() / positive.lower).round_out(bits)
    } else {
        exp_nonnegative_point(value, terms, bits)
    }
}

pub fn exp_interval(value: &RatInterval, terms: u32, bits: u32) -> RatInterval {
    let lower = exp_rational_interval(&value.lower, terms, bits).lower;
    let upper = exp_rational_interval(&value.upper, terms, bits).upper;
    RatInterval::new(lower, upper).round_out(bits)
}

fn sin_cos_small(value: &Rat, terms: u32, bits: u32) -> (RatInterval, RatInterval) {
    let square = value * value;

    let mut sine = RatInterval::point(value.clone());
    let mut sine_term = RatInterval::point(value.clone());
    for index in 1..terms {
        let denominator = integer(i64::from((2 * index) * (2 * index + 1)));
        let coefficient = -square.clone() / denominator;
        sine_term = sine_term.scale(&coefficient).round_out(bits);
        sine = sine.add(&sine_term).round_out(bits);
    }
    let sine_error = sine_term
        .scale(&(-square.clone() / integer(i64::from((2 * terms) * (2 * terms + 1)))))
        .abs_upper();

    let mut cosine = RatInterval::point(Rat::one());
    let mut cosine_term = RatInterval::point(Rat::one());
    for index in 1..terms {
        let denominator = integer(i64::from((2 * index - 1) * (2 * index)));
        let coefficient = -square.clone() / denominator;
        cosine_term = cosine_term.scale(&coefficient).round_out(bits);
        cosine = cosine.add(&cosine_term).round_out(bits);
    }
    let cosine_error = cosine_term
        .scale(&(-square / integer(i64::from((2 * terms - 1) * (2 * terms)))))
        .abs_upper();

    (
        RatInterval::new(&sine.lower - &sine_error, &sine.upper + &sine_error).round_out(bits),
        RatInterval::new(&cosine.lower - &cosine_error, &cosine.upper + &cosine_error)
            .round_out(bits),
    )
}

pub fn sin_cos_rational_interval(value: &Rat, terms: u32, bits: u32) -> (RatInterval, RatInterval) {
    let mut reduced = value.clone();
    let mut doublings = 0u32;
    let eighth = ratio(BigInt::one(), BigInt::from(8));
    while reduced.abs() > eighth {
        reduced /= integer(2);
        doublings += 1;
    }

    let (mut sine, mut cosine) = sin_cos_small(&reduced, terms, bits);
    for _ in 0..doublings {
        let next_sine = sine.multiply(&cosine).scale(&integer(2)).round_out(bits);
        let next_cosine = cosine.square().subtract(&sine.square()).round_out(bits);
        sine = next_sine;
        cosine = next_cosine;
    }
    (sine, cosine)
}

pub fn cis_interval(angle: &RatInterval, terms: u32, bits: u32) -> ComplexInterval {
    let center = angle.midpoint();
    let radius = max(
        (&center - &angle.lower).abs(),
        (&angle.upper - &center).abs(),
    );
    let (sine, cosine) = sin_cos_rational_interval(&center, terms, bits);
    let error = RatInterval::symmetric(radius);
    ComplexInterval::new(cosine.add(&error), sine.add(&error)).round_out(bits)
}

fn negative_complex_power(
    base: u32,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<ComplexInterval, ExactAnalysisError> {
    let logarithm = log_rational_interval(
        &Rat::from_integer(BigInt::from(base)),
        config.log_terms,
        config.dyadic_bits,
    )?;
    let amplitude_exponent = receiver.sigma.multiply(&logarithm).neg();
    let amplitude = exp_interval(
        &amplitude_exponent,
        config.exponential_terms,
        config.dyadic_bits,
    );
    let angle = receiver.tau.multiply(&logarithm).neg();
    Ok(
        cis_interval(&angle, config.trigonometric_terms, config.dyadic_bits)
            .multiply(&ComplexInterval::new(
                amplitude,
                RatInterval::point(Rat::zero()),
            ))
            .round_out(config.dyadic_bits),
    )
}

#[derive(Clone, Debug)]
struct ComplexDual {
    value: ComplexInterval,
    derivative: ComplexInterval,
}

impl ComplexDual {
    fn constant(value: ComplexInterval) -> Self {
        Self {
            value,
            derivative: ComplexInterval::zero(),
        }
    }

    fn add(&self, other: &Self, bits: u32) -> Self {
        Self {
            value: self.value.add(&other.value).round_out(bits),
            derivative: self.derivative.add(&other.derivative).round_out(bits),
        }
    }

    fn multiply(&self, other: &Self, bits: u32) -> Self {
        Self {
            value: self.value.multiply(&other.value).round_out(bits),
            derivative: self
                .derivative
                .multiply(&other.value)
                .add(&self.value.multiply(&other.derivative))
                .round_out(bits),
        }
    }

    fn scale(&self, scalar: &Rat, bits: u32) -> Self {
        Self {
            value: self.value.scale(scalar).round_out(bits),
            derivative: self.derivative.scale(scalar).round_out(bits),
        }
    }

    fn reciprocal(&self, bits: u32) -> Result<Self, ExactAnalysisError> {
        let inverse = self.value.reciprocal()?.round_out(bits);
        Ok(Self {
            value: inverse.clone(),
            derivative: self
                .derivative
                .neg()
                .multiply(&inverse.multiply(&inverse))
                .round_out(bits),
        })
    }

    fn divide(&self, other: &Self, bits: u32) -> Result<Self, ExactAnalysisError> {
        Ok(self.multiply(&other.reciprocal(bits)?, bits))
    }
}

fn negative_complex_power_dual(
    base: u32,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<ComplexDual, ExactAnalysisError> {
    let logarithm = log_rational_interval(
        &Rat::from_integer(BigInt::from(base)),
        config.log_terms,
        config.dyadic_bits,
    )?;
    let value = negative_complex_power(base, receiver, config)?;
    let derivative_factor = ComplexInterval::new(logarithm.neg(), RatInterval::point(Rat::zero()));
    Ok(ComplexDual {
        derivative: value
            .multiply(&derivative_factor)
            .round_out(config.dyadic_bits),
        value,
    })
}

fn bernoulli_number(index: u32) -> Rat {
    let mut values = vec![Rat::zero(); (index + 1) as usize];
    for m in 0..=index {
        values[m as usize] = ratio(BigInt::one(), BigInt::from(m + 1));
        for j in (1..=m).rev() {
            let position = (j - 1) as usize;
            values[position] = integer(i64::from(j)) * (&values[position] - &values[j as usize]);
        }
    }
    values[0].clone()
}

fn receiver_dual(receiver: &ComplexReceiverBox) -> ComplexDual {
    ComplexDual {
        value: ComplexInterval::new(receiver.sigma.clone(), receiver.tau.clone()),
        derivative: ComplexInterval::point(RatComplex::new(Rat::one(), Rat::zero())),
    }
}

fn rising_complex(receiver: &ComplexReceiverBox, count: u32) -> ComplexInterval {
    let mut result = ComplexInterval::point(RatComplex::new(Rat::one(), Rat::zero()));
    for index in 0..count {
        let factor = ComplexInterval::new(
            receiver.sigma.translate(&integer(i64::from(index))),
            receiver.tau.clone(),
        );
        result = result.multiply(&factor);
    }
    result
}

fn rising_complex_dual(receiver: &ComplexReceiverBox, count: u32, bits: u32) -> ComplexDual {
    let mut result = ComplexDual::constant(ComplexInterval::point(RatComplex::new(
        Rat::one(),
        Rat::zero(),
    )));
    let s = receiver_dual(receiver);
    for index in 0..count {
        let factor = s.add(
            &ComplexDual::constant(ComplexInterval::point(RatComplex::new(
                integer(i64::from(index)),
                Rat::zero(),
            ))),
            bits,
        );
        result = result.multiply(&factor, bits);
    }
    result
}

fn zeta_euler_maclaurin(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<(ComplexInterval, Rat), ExactAnalysisError> {
    if !receiver.sigma.lower.is_positive() {
        return Err(ExactAnalysisError::NonPositiveSigma);
    }
    if receiver.sigma.contains_zero()
        || (receiver.sigma.lower <= Rat::one()
            && receiver.sigma.upper >= Rat::one()
            && receiver.tau.contains_zero())
    {
        return Err(ExactAnalysisError::ZetaPoleInReceiver);
    }

    let start = config.euler_maclaurin_start;
    let order = config.euler_maclaurin_order;
    assert!(start >= 2, "Euler--Maclaurin start must be at least two");
    assert!(order >= 1, "Euler--Maclaurin order must be positive");

    let mut value = ComplexInterval::zero();
    for base in 1..start {
        value = value
            .add(&negative_complex_power(base, receiver, config)?)
            .round_out(config.dyadic_bits);
    }

    let start_power = negative_complex_power(start, receiver, config)?;
    let s_minus_one =
        ComplexInterval::new(receiver.sigma.translate(&-Rat::one()), receiver.tau.clone());
    let leading = start_power
        .scale(&integer(i64::from(start)))
        .divide(&s_minus_one)?;
    value = value
        .add(&leading)
        .add(&start_power.scale(&ratio(BigInt::one(), BigInt::from(2))))
        .round_out(config.dyadic_bits);

    for correction in 1..=order {
        let even = 2 * correction;
        let bernoulli = bernoulli_number(even);
        let coefficient = bernoulli / Rat::from_integer(factorial(even));
        let start_scale = ratio(BigInt::one(), BigInt::from(start).pow(even - 1));
        let term = rising_complex(receiver, even - 1)
            .multiply(&start_power)
            .scale(&(coefficient * start_scale));
        value = value.add(&term).round_out(config.dyadic_bits);
    }

    let even = 2 * order;
    let bernoulli = bernoulli_number(even).abs();
    let factorial_even = Rat::from_integer(factorial(even));
    let mut rising_bound = Rat::one();
    let tau_bound = receiver.tau.abs_upper();
    for index in 0..even {
        let real_bound = receiver
            .sigma
            .translate(&integer(i64::from(index)))
            .abs_upper();
        rising_bound *= real_bound + &tau_bound;
    }
    let start_amplitude = {
        let logarithm = log_rational_interval(
            &Rat::from_integer(BigInt::from(start)),
            config.log_terms,
            config.dyadic_bits,
        )?;
        exp_interval(
            &receiver.sigma.multiply(&logarithm).neg(),
            config.exponential_terms,
            config.dyadic_bits,
        )
        .upper
    };
    let denominator_power = Rat::from_integer(BigInt::from(start).pow(even - 1));
    let integral_denominator = &receiver.sigma.lower + integer(i64::from(even - 1));
    let remainder = bernoulli * rising_bound * start_amplitude
        / (factorial_even * denominator_power * integral_denominator);
    Ok((
        value.add_disc(&remainder).round_out(config.dyadic_bits),
        remainder,
    ))
}

fn zeta_euler_maclaurin_dual(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<(ComplexDual, Rat, Rat), ExactAnalysisError> {
    if !receiver.sigma.lower.is_positive() {
        return Err(ExactAnalysisError::NonPositiveSigma);
    }
    if receiver.sigma.lower <= Rat::one()
        && receiver.sigma.upper >= Rat::one()
        && receiver.tau.contains_zero()
    {
        return Err(ExactAnalysisError::ZetaPoleInReceiver);
    }

    let bits = config.dyadic_bits;
    let start = config.euler_maclaurin_start;
    let order = config.euler_maclaurin_order;
    let mut value = ComplexDual::constant(ComplexInterval::zero());
    for base in 1..start {
        value = value.add(&negative_complex_power_dual(base, receiver, config)?, bits);
    }

    let start_power = negative_complex_power_dual(start, receiver, config)?;
    let s_minus_one = receiver_dual(receiver).add(
        &ComplexDual::constant(ComplexInterval::point(RatComplex::new(
            -Rat::one(),
            Rat::zero(),
        ))),
        bits,
    );
    let leading = start_power
        .scale(&integer(i64::from(start)), bits)
        .divide(&s_minus_one, bits)?;
    value = value.add(&leading, bits).add(
        &start_power.scale(&ratio(BigInt::one(), BigInt::from(2)), bits),
        bits,
    );

    for correction in 1..=order {
        let even = 2 * correction;
        let coefficient = bernoulli_number(even) / Rat::from_integer(factorial(even));
        let start_scale = ratio(BigInt::one(), BigInt::from(start).pow(even - 1));
        let term = rising_complex_dual(receiver, even - 1, bits)
            .multiply(&start_power, bits)
            .scale(&(coefficient * start_scale), bits);
        value = value.add(&term, bits);
    }

    let even = 2 * order;
    let bernoulli = bernoulli_number(even).abs();
    let factorial_even = Rat::from_integer(factorial(even));
    let tau_bound = receiver.tau.abs_upper();
    let mut rising_bound = Rat::one();
    let mut rising_derivative_bound = Rat::zero();
    for index in 0..even {
        let factor_bound = receiver
            .sigma
            .translate(&integer(i64::from(index)))
            .abs_upper()
            + &tau_bound;
        rising_derivative_bound = &rising_derivative_bound * &factor_bound + &rising_bound;
        rising_bound *= factor_bound;
    }
    let logarithm = log_rational_interval(
        &Rat::from_integer(BigInt::from(start)),
        config.log_terms,
        bits,
    )?;
    let start_amplitude = exp_interval(
        &receiver.sigma.multiply(&logarithm).neg(),
        config.exponential_terms,
        bits,
    )
    .upper;
    let denominator_power = Rat::from_integer(BigInt::from(start).pow(even - 1));
    let decay = start_amplitude / denominator_power;
    let decay_order = &receiver.sigma.lower + integer(i64::from(even - 1));
    let integral = &bernoulli * &decay / &decay_order;
    let integral_derivative = &bernoulli
        * &decay
        * (&logarithm.upper / &decay_order + Rat::one() / (&decay_order * &decay_order));
    let remainder = &rising_bound * &integral / &factorial_even;
    let derivative_remainder =
        (rising_derivative_bound * integral + rising_bound * integral_derivative) / factorial_even;

    value.value = value.value.add_disc(&remainder).round_out(bits);
    value.derivative = value
        .derivative
        .add_disc(&derivative_remainder)
        .round_out(bits);
    Ok((value, remainder, derivative_remainder))
}

pub fn eta_evaluate(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<EtaEvaluation, ExactAnalysisError> {
    let (zeta, remainder) = zeta_euler_maclaurin(receiver, config)?;
    let two_power = negative_complex_power(2, receiver, config)?.scale(&integer(2));
    let factor =
        ComplexInterval::point(RatComplex::new(Rat::one(), Rat::zero())).subtract(&two_power);
    Ok(EtaEvaluation {
        receiver: receiver.clone(),
        value: factor.multiply(&zeta).round_out(config.dyadic_bits),
        finite_terms: config.euler_maclaurin_start - 1,
        correction_order: config.euler_maclaurin_order,
        remainder_radius: remainder,
    })
}

pub fn eta_evaluate_jet(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<EtaJetEvaluation, ExactAnalysisError> {
    let bits = config.dyadic_bits;
    let (zeta, remainder, derivative_remainder) = zeta_euler_maclaurin_dual(receiver, config)?;
    let two_power = negative_complex_power_dual(2, receiver, config)?;
    let factor = ComplexDual::constant(ComplexInterval::point(RatComplex::new(
        Rat::one(),
        Rat::zero(),
    )))
    .add(&two_power.scale(&integer(-2), bits), bits);
    let eta = factor.multiply(&zeta, bits);
    Ok(EtaJetEvaluation {
        receiver: receiver.clone(),
        value: eta.value,
        derivative: eta.derivative,
        remainder_radius: remainder,
        derivative_remainder_radius: derivative_remainder,
    })
}

/// A rational upper bound for `|eta''(s)|` throughout one receiver box.
///
/// The finite prefix is bounded termwise.  The alternating tail is bounded by
/// summation by parts applied to
/// `g(x) = (log x)^2 x^-s`, using
/// `|g(N)| + integral_N^infinity |g'(x)| dx`.
pub fn eta_second_derivative_bound(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    tail_start: u32,
) -> Result<Rat, ExactAnalysisError> {
    if !receiver.sigma.lower.is_positive() {
        return Err(ExactAnalysisError::NonPositiveSigma);
    }
    assert!(tail_start >= 2, "the derivative tail must start after one");

    let sigma = receiver.sigma.lower.clone();
    let mut finite = Rat::zero();
    for base in 2..tail_start {
        let logarithm = log_rational_interval(
            &Rat::from_integer(BigInt::from(base)),
            config.log_terms,
            config.dyadic_bits,
        )?;
        let amplitude = exp_interval(
            &RatInterval::point(-&sigma).multiply(&logarithm),
            config.exponential_terms,
            config.dyadic_bits,
        )
        .upper;
        finite += amplitude * &logarithm.upper * &logarithm.upper;
    }

    let logarithm = log_rational_interval(
        &Rat::from_integer(BigInt::from(tail_start)),
        config.log_terms,
        config.dyadic_bits,
    )?;
    let amplitude = exp_interval(
        &RatInterval::point(-&sigma).multiply(&logarithm),
        config.exponential_terms,
        config.dyadic_bits,
    )
    .upper;
    let inverse_sigma = Rat::one() / &sigma;
    let inverse_sigma_square = &inverse_sigma * &inverse_sigma;
    let inverse_sigma_cube = &inverse_sigma_square * &inverse_sigma;
    let log = logarithm.upper;
    let log_square = &log * &log;
    let first_log_integral = &log * &inverse_sigma + &inverse_sigma_square;
    let second_log_integral = &log_square * &inverse_sigma
        + integer(2) * &log * &inverse_sigma_square
        + integer(2) * inverse_sigma_cube;
    let s_bound = receiver.sigma.abs_upper() + receiver.tau.abs_upper();
    let tail =
        &amplitude * (log_square + integer(2) * first_log_integral + s_bound * second_log_integral);
    Ok(dyadic_ceil(&(finite + tail), config.dyadic_bits))
}

/// One term of the head chain, with the two faces it is built from **retained**.
///
/// `n^(-s) = exp(-sigma·log n) · cis(-tau·log n)`: an amplitude and a turn.
/// [`negative_complex_power`] forms both and returns only their product, so the
/// magnitude and the winding arrive already multiplied and a reader cannot ask
/// which one moved. This carries both, together with the term's **address** in
/// the free abelian group on the primes — `n = prod p^a`, which is the collapsed
/// face that unique factorization reopens.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaChainTerm {
    pub base: u32,
    /// `n = prod p^a`, the reopened address.
    pub address: Vec<PrimeValuation>,
    pub log_base: RatInterval,
    /// `exp(-sigma·log n)` — the magnitude face.
    pub amplitude: RatInterval,
    /// `-tau·log n` — the turn, in the additive chart, before `cis` carries it up.
    pub turn: RatInterval,
    pub value: ComplexInterval,
}

/// One Euler--Maclaurin correction, read as a crossing rather than as an error term.
///
/// The correction of index `2k` is
/// `B_(2k)/(2k)! · (s)_(2k-1) · N^(-s) / N^(2k-1)`, and its three parts are three
/// different objects: an **exact rational** weight, a **shift-orbit product**
/// `(s)_(2k-1) = s(s+1)...(s+2k-2)` which is the rising factorial, and a decay.
///
/// The odd-index Bernoulli numbers vanish, so only **odd crossing orders** occur;
/// that is a parity selection rule and it decides which terms exist before any
/// magnitude is computed. The sign of `B_(2k)` alternates, so the hand alternates
/// with the crossing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EulerMaclaurinCrossing {
    /// `2k - 1`, the order of the derivative crossing.
    pub crossing_order: u32,
    pub bernoulli_index: u32,
    pub bernoulli: Rat,
    /// `B_(2k)/(2k)!`, exact.
    pub coefficient: Rat,
    /// The sign of `B_(2k)`: which way this crossing turns.
    pub hand: i32,
    /// `(s)_(2k-1)`, the rising factorial — the shift orbit of `s`, multiplied out.
    pub pochhammer: ComplexInterval,
    pub value: ComplexInterval,
}

/// The Euler--Maclaurin evaluation returned as the chain it is, not as its sum.
///
/// `zeta(s) = sum_(n<N) n^(-s) + N^(1-s)/(s-1) + N^(-s)/2 + sum_k crossing_k + R`
///
/// The identity behind it is an operator statement: `sigma = e^(partial)`, so
/// `1/(e^partial - 1) = 1/partial · sum_n B_n partial^n / n!`. **Summation is
/// integration composed with a series in the derivative whose coefficients are
/// the Bernoulli rationals** — a chart transition between the difference chart
/// and the differential one, with `B_n` as its connection coefficients.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaChainDecomposition {
    pub receiver: ComplexReceiverBox,
    pub head: Vec<EtaChainTerm>,
    /// `N^(1-s)/(s-1)` — the integral term the chart transition pays for.
    pub integral_term: ComplexInterval,
    /// `N^(-s)/2` — the boundary half-term.
    pub boundary_half: ComplexInterval,
    pub crossings: Vec<EulerMaclaurinCrossing>,
    pub remainder_radius: Rat,
    pub zeta: ComplexInterval,
    /// `1 - 2^(1-s)`, the alternating rebase carrying zeta to eta.
    pub alternating_factor: ComplexInterval,
    pub eta: ComplexInterval,
}

fn prime_address(mut base: u32) -> Vec<PrimeValuation> {
    let mut address = Vec::new();
    let mut prime = 2;
    while prime * prime <= base {
        let mut exponent = 0;
        while base % prime == 0 {
            base /= prime;
            exponent += 1;
        }
        if exponent > 0 {
            address.push(PrimeValuation { prime, exponent });
        }
        prime += 1;
    }
    if base > 1 {
        address.push(PrimeValuation {
            prime: base,
            exponent: 1,
        });
    }
    address
}

fn negative_complex_power_parts(
    base: u32,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<EtaChainTerm, ExactAnalysisError> {
    let logarithm = log_rational_interval(
        &Rat::from_integer(BigInt::from(base)),
        config.log_terms,
        config.dyadic_bits,
    )?;
    let amplitude_exponent = receiver.sigma.multiply(&logarithm).neg();
    let amplitude = exp_interval(
        &amplitude_exponent,
        config.exponential_terms,
        config.dyadic_bits,
    );
    let turn = receiver.tau.multiply(&logarithm).neg();
    let value = cis_interval(&turn, config.trigonometric_terms, config.dyadic_bits)
        .multiply(&ComplexInterval::new(
            amplitude.clone(),
            RatInterval::point(Rat::zero()),
        ))
        .round_out(config.dyadic_bits);
    Ok(EtaChainTerm {
        base,
        address: prime_address(base),
        log_base: logarithm,
        amplitude,
        turn,
        value,
    })
}

/// Return the Euler--Maclaurin chain for `eta` at one receiver, term by term.
///
/// Every quantity is exact: the head terms are amplitudes and turns over `Rat`,
/// the Bernoulli numbers are exact rationals, the rising factorial is an exact
/// interval product, and the remainder is a certified radius. Nothing here is a
/// float and nothing is rounded to a decimal face.
pub fn eta_chain_decomposition(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<EtaChainDecomposition, ExactAnalysisError> {
    if !receiver.sigma.lower.is_positive() {
        return Err(ExactAnalysisError::NonPositiveSigma);
    }
    if receiver.sigma.lower <= Rat::one()
        && receiver.sigma.upper >= Rat::one()
        && receiver.tau.contains_zero()
    {
        return Err(ExactAnalysisError::ZetaPoleInReceiver);
    }
    let bits = config.dyadic_bits;
    let start = config.euler_maclaurin_start;
    let order = config.euler_maclaurin_order;

    let mut head = Vec::new();
    let mut value = ComplexInterval::zero();
    for base in 1..start {
        let term = negative_complex_power_parts(base, receiver, config)?;
        value = value.add(&term.value).round_out(bits);
        head.push(term);
    }

    let start_power = negative_complex_power(start, receiver, config)?;
    let s_minus_one =
        ComplexInterval::new(receiver.sigma.translate(&-Rat::one()), receiver.tau.clone());
    let integral_term = start_power
        .scale(&integer(i64::from(start)))
        .divide(&s_minus_one)?
        .round_out(bits);
    let boundary_half = start_power
        .scale(&ratio(BigInt::one(), BigInt::from(2)))
        .round_out(bits);
    value = value
        .add(&integral_term)
        .add(&boundary_half)
        .round_out(bits);

    let mut crossings = Vec::new();
    for correction in 1..=order {
        let even = 2 * correction;
        let bernoulli = bernoulli_number(even);
        let coefficient = bernoulli.clone() / Rat::from_integer(factorial(even));
        let start_scale = ratio(BigInt::one(), BigInt::from(start).pow(even - 1));
        let pochhammer = rising_complex(receiver, even - 1);
        let term = pochhammer
            .multiply(&start_power)
            .scale(&(coefficient.clone() * start_scale))
            .round_out(bits);
        value = value.add(&term).round_out(bits);
        let hand = if bernoulli.numer().is_negative() {
            -1
        } else if bernoulli.numer().is_zero() {
            0
        } else {
            1
        };
        crossings.push(EulerMaclaurinCrossing {
            crossing_order: even - 1,
            bernoulli_index: even,
            bernoulli,
            coefficient,
            hand,
            pochhammer,
            value: term,
        });
    }

    let (zeta, remainder_radius) = zeta_euler_maclaurin(receiver, config)?;
    let two_power = negative_complex_power(2, receiver, config)?.scale(&integer(2));
    let alternating_factor =
        ComplexInterval::point(RatComplex::new(Rat::one(), Rat::zero())).subtract(&two_power);
    let eta = alternating_factor.multiply(&zeta).round_out(bits);
    Ok(EtaChainDecomposition {
        receiver: receiver.clone(),
        head,
        integral_term,
        boundary_half,
        crossings,
        remainder_radius,
        zeta,
        alternating_factor,
        eta,
    })
}

/// One term of Borwein's finite alternating chain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BorweinTerm {
    pub index: u32,
    /// `d_k - d_n`, an exact integer. Borwein's weights are integers, not samples.
    pub weight: BigInt,
    /// `(-1)^k` — the alternating hand.
    pub hand: i32,
    /// `(k+1)^(-s)`.
    pub power: ComplexInterval,
    pub value: ComplexInterval,
}

/// Borwein's chain for `eta`, exact in its weights and **uncertified** in its tail.
///
/// `eta(s) = (-1/d_n) sum_(k<n) (-1)^k (d_k - d_n) (k+1)^(-s) + gamma_n(s)`
/// with `d_k = n sum_(i<=k) (n+i-1)! 4^i / ((n-i)! (2i)!)`, every `d_k` an integer.
///
/// **This type is deliberately not an [`EtaEvaluation`].** Borwein's remainder
/// obeys `|gamma_n(s)| <= 3/(3+sqrt 8)^n · 1/|Gamma(s)|`, and this body owns no
/// Gamma function — measured 2026-08-16, `grep -rniF "gamma"` over `crates` and
/// `soma` returns only variable names. So the tail cannot be certified here and
/// the value must never be presented as an enclosure. What it is good for is a
/// **second frame**: an independent chain whose value may be checked against the
/// certified Euler--Maclaurin enclosure, and an invariant is only visible across
/// two frames.
///
/// The decay base is `3 + sqrt 8 = 3 + 2 sqrt 2 = (1 + sqrt 2)^2`, the square of
/// the fundamental unit of the ring adjoining `sqrt 2`. The condensation's rate
/// is a fundamental unit, not a tuned constant.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaBorweinChain {
    pub receiver: ComplexReceiverBox,
    pub depth: u32,
    pub weights: Vec<BigInt>,
    pub d_final: BigInt,
    pub terms: Vec<BorweinTerm>,
    pub value: ComplexInterval,
}

fn borwein_weights(depth: u32) -> Result<Vec<BigInt>, ExactAnalysisError> {
    if depth == 0 {
        return Err(ExactAnalysisError::BorweinDepthTooSmall);
    }
    let outer = Rat::from_integer(BigInt::from(depth));
    let mut running = Rat::zero();
    let mut weights = Vec::with_capacity(depth as usize + 1);
    for index in 0..=depth {
        let numerator = factorial(depth + index - 1) * BigInt::from(4u32).pow(index);
        let denominator = factorial(depth - index) * factorial(2 * index);
        running += Rat::new(numerator, denominator);
        let value = &outer * &running;
        if !value.denom().is_one() {
            return Err(ExactAnalysisError::BorweinWeightNotIntegral(index));
        }
        weights.push(value.numer().clone());
    }
    Ok(weights)
}

/// Build Borwein's chain at one receiver. See [`EtaBorweinChain`] for the bound
/// this cannot certify and why the type is separate.
pub fn eta_borwein_chain(
    receiver: &ComplexReceiverBox,
    depth: u32,
    config: &ExactSeriesConfig,
) -> Result<EtaBorweinChain, ExactAnalysisError> {
    let weights = borwein_weights(depth)?;
    let d_final = weights[depth as usize].clone();
    let mut accumulated = ComplexInterval::zero();
    let mut terms = Vec::new();
    for index in 0..depth {
        let weight = &weights[index as usize] - &d_final;
        let hand = if index % 2 == 0 { 1 } else { -1 };
        let power = negative_complex_power(index + 1, receiver, config)?;
        let scaled = Rat::from_integer(&weight * BigInt::from(hand));
        let term = power.scale(&scaled).round_out(config.dyadic_bits);
        accumulated = accumulated.add(&term).round_out(config.dyadic_bits);
        terms.push(BorweinTerm {
            index,
            weight,
            hand,
            power,
            value: term,
        });
    }
    let value = accumulated
        .scale(&(-Rat::one() / Rat::from_integer(d_final.clone())))
        .round_out(config.dyadic_bits);
    Ok(EtaBorweinChain {
        receiver: receiver.clone(),
        depth,
        weights,
        d_final,
        terms,
        value,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeValuation {
    pub prime: u32,
    pub exponent: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaCurrentTerm {
    pub ordinal: u32,
    pub hand: i8,
    pub valuations: Vec<PrimeValuation>,
    pub contribution: ComplexInterval,
    pub partial_sum: ComplexInterval,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EtaCurrentReceipt {
    pub receiver: ComplexReceiverBox,
    pub terms: Vec<EtaCurrentTerm>,
    pub tail_radius: Rat,
}

fn prime_valuations(mut value: u32) -> Vec<PrimeValuation> {
    let mut result = Vec::new();
    let mut candidate = 2u32;
    while candidate * candidate <= value {
        if value % candidate == 0 {
            let mut exponent = 0u32;
            while value % candidate == 0 {
                value /= candidate;
                exponent += 1;
            }
            result.push(PrimeValuation {
                prime: candidate,
                exponent,
            });
        }
        candidate += if candidate == 2 { 1 } else { 2 };
    }
    if value > 1 {
        result.push(PrimeValuation {
            prime: value,
            exponent: 1,
        });
    }
    result
}

/// Retain the ordered direct eta current at one rational receiver.
///
/// The tail radius follows summation by parts for `x^-s`:
/// `|R_N| <= N^-sigma (1 + |s|/sigma)`.
pub fn eta_partial_current(
    sigma: Rat,
    tau: Rat,
    term_count: u32,
    config: &ExactSeriesConfig,
) -> Result<EtaCurrentReceipt, ExactAnalysisError> {
    assert!(term_count >= 1, "an eta current needs at least one term");
    let receiver = ComplexReceiverBox::point(sigma.clone(), tau.clone());
    let mut partial = ComplexInterval::zero();
    let mut terms = Vec::with_capacity(term_count as usize);
    for ordinal in 1..=term_count {
        let hand = if ordinal % 2 == 1 { 1 } else { -1 };
        let contribution = negative_complex_power(ordinal, &receiver, config)?
            .scale(&integer(i64::from(hand)))
            .round_out(config.dyadic_bits);
        partial = partial.add(&contribution).round_out(config.dyadic_bits);
        terms.push(EtaCurrentTerm {
            ordinal,
            hand,
            valuations: prime_valuations(ordinal),
            contribution,
            partial_sum: partial.clone(),
        });
    }

    let tail_start = term_count + 1;
    let logarithm = log_rational_interval(
        &Rat::from_integer(BigInt::from(tail_start)),
        config.log_terms,
        config.dyadic_bits,
    )?;
    let amplitude = exp_interval(
        &RatInterval::point(-&sigma).multiply(&logarithm),
        config.exponential_terms,
        config.dyadic_bits,
    )
    .upper;
    let s_bound = sigma.abs() + tau.abs();
    let tail_radius = dyadic_ceil(
        &(amplitude * (Rat::one() + s_bound / sigma)),
        config.dyadic_bits,
    );
    Ok(EtaCurrentReceipt {
        receiver,
        terms,
        tail_radius,
    })
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct BoundarySegmentReceipt {
    pub start: RatComplex,
    pub end: RatComplex,
    pub start_value: ComplexInterval,
    pub end_value: ComplexInterval,
    pub image: ComplexInterval,
    pub depth: u32,
}

/// The ray crossings of one closed boundary, held as two arms and never netted.
///
/// A winding number is what survives after the two hands are subtracted, and the subtraction is
/// exactly the deletion `CLAUDE.md` §2b names: it keeps the magnitude and discards which passages
/// produced it. Both arms are kept here, **by segment index**, so a receiver can ask not only *how
/// many times did the image enclose the origin* but *where on this boundary is the image doing
/// work*. Those are different questions and only the second can say which half to subdivide.
///
/// `winding()` is the group completion and is what the argument principle counts; it is a reading
/// of the arms and never replaces them. A boundary whose image crosses the ray four times and
/// encloses nothing is not the same object as one that never approaches it, and `winding == 0`
/// cannot tell them apart.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RayCrossings {
    /// Indices of the polygon segments crossing the ray upward, in boundary order.
    pub with_the_turn: Vec<usize>,
    /// Indices of the polygon segments crossing the ray downward, in boundary order.
    pub against_the_turn: Vec<usize>,
}

impl RayCrossings {
    /// The argument-principle winding: the two arms, group-completed.
    pub fn winding(&self) -> i32 {
        self.with_the_turn.len() as i32 - self.against_the_turn.len() as i32
    }

    /// Every crossing, both hands. Zero exactly when the image never meets the ray.
    pub fn total(&self) -> usize {
        self.with_the_turn.len() + self.against_the_turn.len()
    }

    /// The image crosses the ray and still encloses nothing.
    ///
    /// This is the case a net winding cannot report, and it is the one that says a half is worth
    /// subdividing rather than discarding.
    pub fn cancels(&self) -> bool {
        self.total() > 0 && self.winding() == 0
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindingReceipt {
    pub receiver: ComplexReceiverBox,
    /// `crossings.winding()`, carried for readers that want the group completion directly.
    pub winding: i32,
    pub crossings: RayCrossings,
    pub ray_parameter: i64,
    pub segments: Vec<BoundarySegmentReceipt>,
    pub polygon: Vec<RatComplex>,
}

fn receiver_segment(start: &RatComplex, end: &RatComplex) -> ComplexReceiverBox {
    ComplexReceiverBox::new(
        RatInterval::new(
            min(start.re.clone(), end.re.clone()),
            max(start.re.clone(), end.re.clone()),
        ),
        RatInterval::new(
            min(start.im.clone(), end.im.clone()),
            max(start.im.clone(), end.im.clone()),
        ),
    )
}

fn certify_boundary_segment(
    start: RatComplex,
    start_image: ComplexInterval,
    end: RatComplex,
    end_image: ComplexInterval,
    depth: u32,
    max_depth: u32,
    config: &ExactSeriesConfig,
    second_derivative_bound: &Rat,
    output: &mut Vec<BoundarySegmentReceipt>,
) -> Result<(), ExactAnalysisError> {
    let receiver = receiver_segment(&start, &end);
    let midpoint = RatComplex::new(
        (&start.re + &end.re) / integer(2),
        (&start.im + &end.im) / integer(2),
    );
    let midpoint_jet = eta_evaluate_jet(
        &ComplexReceiverBox::point(midpoint.re.clone(), midpoint.im.clone()),
        config,
    )?;
    let midpoint_image = midpoint_jet.value;
    let derivative_bound = midpoint_jet.derivative.l1_upper();
    let parameter_radius = (receiver.sigma.width() + receiver.tau.width()) / integer(2);
    let transport_radius = &parameter_radius * derivative_bound
        + &parameter_radius * &parameter_radius * second_derivative_bound / integer(2);
    let mut image = midpoint_image.add_disc(&transport_radius);
    image = image.hull(&start_image).hull(&end_image);

    if !image.contains_origin() {
        output.push(BoundarySegmentReceipt {
            start,
            end,
            start_value: start_image,
            end_value: end_image,
            image,
            depth,
        });
        return Ok(());
    }
    if depth >= max_depth {
        return Err(ExactAnalysisError::UnresolvedBoundary(depth));
    }
    certify_boundary_segment(
        start.clone(),
        start_image,
        midpoint.clone(),
        midpoint_image.clone(),
        depth + 1,
        max_depth,
        config,
        second_derivative_bound,
        output,
    )?;
    certify_boundary_segment(
        midpoint,
        midpoint_image,
        end,
        end_image,
        depth + 1,
        max_depth,
        config,
        second_derivative_bound,
        output,
    )
}

fn transformed_ray_point(point: &RatComplex, parameter: i64) -> RatComplex {
    let k = integer(parameter);
    RatComplex::new(&point.re + &k * &point.im, &point.im - k * &point.re)
}

fn polygon_winding(polygon: &[RatComplex]) -> Result<(RayCrossings, i64), ExactAnalysisError> {
    for parameter in 0..=32i64 {
        let transformed = polygon
            .iter()
            .map(|point| transformed_ray_point(point, parameter))
            .collect::<Vec<_>>();
        if transformed.iter().any(|point| point.im.is_zero()) {
            continue;
        }
        let mut crossings = RayCrossings::default();
        for index in 0..transformed.len() {
            let start = &transformed[index];
            let end = &transformed[(index + 1) % transformed.len()];
            let cross = start.cross(end);
            if start.im.is_negative() && end.im.is_positive() && cross.is_positive() {
                crossings.with_the_turn.push(index);
            } else if start.im.is_positive() && end.im.is_negative() && cross.is_negative() {
                crossings.against_the_turn.push(index);
            }
        }
        return Ok((crossings, parameter));
    }
    Err(ExactAnalysisError::NoAdmissibleWindingRay)
}

pub fn eta_boundary_winding(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    max_depth: u32,
) -> Result<WindingReceipt, ExactAnalysisError> {
    let lower_left = RatComplex::new(receiver.sigma.lower.clone(), receiver.tau.lower.clone());
    let lower_right = RatComplex::new(receiver.sigma.upper.clone(), receiver.tau.lower.clone());
    let upper_right = RatComplex::new(receiver.sigma.upper.clone(), receiver.tau.upper.clone());
    let upper_left = RatComplex::new(receiver.sigma.lower.clone(), receiver.tau.upper.clone());

    let mut segments = Vec::new();
    let second_derivative_bound = eta_second_derivative_bound(receiver, config, 64)?;
    let lower_left_image = eta_evaluate(
        &ComplexReceiverBox::point(lower_left.re.clone(), lower_left.im.clone()),
        config,
    )?
    .value;
    let lower_right_image = eta_evaluate(
        &ComplexReceiverBox::point(lower_right.re.clone(), lower_right.im.clone()),
        config,
    )?
    .value;
    let upper_right_image = eta_evaluate(
        &ComplexReceiverBox::point(upper_right.re.clone(), upper_right.im.clone()),
        config,
    )?
    .value;
    let upper_left_image = eta_evaluate(
        &ComplexReceiverBox::point(upper_left.re.clone(), upper_left.im.clone()),
        config,
    )?
    .value;
    for (start, start_image, end, end_image) in [
        (
            lower_left.clone(),
            lower_left_image.clone(),
            lower_right.clone(),
            lower_right_image.clone(),
        ),
        (
            lower_right,
            lower_right_image,
            upper_right.clone(),
            upper_right_image.clone(),
        ),
        (
            upper_right,
            upper_right_image,
            upper_left.clone(),
            upper_left_image.clone(),
        ),
        (upper_left, upper_left_image, lower_left, lower_left_image),
    ] {
        certify_boundary_segment(
            start,
            start_image,
            end,
            end_image,
            0,
            max_depth,
            config,
            &second_derivative_bound,
            &mut segments,
        )?;
    }

    let mut polygon = Vec::with_capacity(segments.len());
    for segment in &segments {
        polygon.push(segment.start_value.midpoint());
    }
    let (crossings, ray_parameter) = polygon_winding(&polygon)?;
    Ok(WindingReceipt {
        receiver: receiver.clone(),
        winding: crossings.winding(),
        crossings,
        ray_parameter,
        segments,
        polygon,
    })
}

pub fn interval_common_continued_fraction(
    interval: &RatInterval,
    maximum_terms: u32,
) -> Vec<BigInt> {
    assert!(
        interval.lower.is_positive(),
        "continued-fraction receiver must be positive"
    );
    let mut lower = interval.lower.clone();
    let mut upper = interval.upper.clone();
    let mut word = Vec::new();
    for _ in 0..maximum_terms {
        let lower_floor = rational_floor(&lower);
        let upper_floor = rational_floor(&upper);
        if lower_floor != upper_floor {
            break;
        }
        word.push(lower_floor.clone());
        lower -= Rat::from_integer(lower_floor.clone());
        upper -= Rat::from_integer(upper_floor);
        if lower.is_zero() || upper.is_zero() {
            break;
        }
        let next_lower = Rat::one() / upper;
        let next_upper = Rat::one() / lower;
        lower = next_lower;
        upper = next_upper;
    }
    word
}

fn rational_floor(value: &Rat) -> BigInt {
    let numerator = value.numer();
    let denominator = value.denom();
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if value.is_negative() && !remainder.is_zero() {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

pub fn integer_digit_count(value: &Rat) -> usize {
    let numerator = value.numer().abs().to_str_radix(10).len();
    let denominator = value.denom().to_str_radix(10).len();
    max(numerator, denominator)
}

pub fn rational_to_i64(value: &BigInt) -> Option<i64> {
    if value.sign() == Sign::NoSign {
        Some(0)
    } else {
        value.to_i64()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::rat;

    #[test]
    fn interval_arithmetic_retains_order_and_excludes_false_zero() {
        let left = RatInterval::new(rat(1, 3), rat(1, 2));
        let right = RatInterval::new(rat(2, 3), rat(3, 4));
        assert_eq!(left.add(&right), RatInterval::new(rat(1, 1), rat(5, 4)));
        assert_eq!(
            left.multiply(&right),
            RatInterval::new(rat(2, 9), rat(3, 8))
        );
        assert!(!left.contains_zero());
    }

    #[test]
    fn rational_transcendental_series_enclose_elementary_identities() {
        let log_two = log_rational_interval(&integer(2), 32, 128).unwrap();
        let exp_log_two = exp_interval(&log_two, 24, 128);
        assert!(exp_log_two.lower < integer(2));
        assert!(exp_log_two.upper > integer(2));

        let (sine, cosine) = sin_cos_rational_interval(&Rat::zero(), 12, 128);
        assert!(sine.lower <= Rat::zero() && sine.upper >= Rat::zero());
        assert!(cosine.lower <= Rat::one() && cosine.upper >= Rat::one());
    }

    #[test]
    fn eta_two_overlaps_pi_squared_over_twelve_without_float() {
        let config = ExactSeriesConfig {
            euler_maclaurin_start: 12,
            euler_maclaurin_order: 8,
            ..ExactSeriesConfig::default()
        };
        let eta = eta_evaluate(&ComplexReceiverBox::point(integer(2), Rat::zero()), &config)
            .unwrap()
            .value;

        // Machin: pi = 16 atan(1/5) - 4 atan(1/239).
        fn atan(value: Rat, terms: u32) -> RatInterval {
            let mut partial = Rat::zero();
            let mut power = value.clone();
            let square = &value * &value;
            for index in 0..terms {
                let signed = if index % 2 == 0 {
                    power.clone()
                } else {
                    -power.clone()
                };
                partial += signed / integer(i64::from(2 * index + 1));
                power *= &square;
            }
            let next = power / integer(i64::from(2 * terms + 1));
            RatInterval::new(
                min(partial.clone(), &partial - &next),
                max(partial.clone(), partial + next),
            )
        }
        let fifth = atan(rat(1, 5), 18);
        let two_hundred_thirty_ninth = atan(rat(1, 239), 6);
        let pi = fifth
            .scale(&integer(16))
            .subtract(&two_hundred_thirty_ninth.scale(&integer(4)));
        let expected = pi.square().scale(&rat(1, 12));
        assert!(eta.re.lower <= expected.upper && expected.lower <= eta.re.upper);
        assert!(eta.im.contains_zero());
    }

    fn corner(re: i64, im: i64) -> RatComplex {
        RatComplex::new(integer(re), integer(im))
    }

    /// Three boundaries, three distinct returns, and the middle one is invisible to a net winding.
    ///
    /// The declared control for `RayCrossings`. Until 2026-08-08 `polygon_winding` accumulated
    /// `+= 1` / `-= 1` into an `i32` and deposited no crossing, so the first two rows below were
    /// one return. `winding == 0` was doing two jobs — *the image never approached the ray* and
    /// *the image crossed it and came back* — and the η-zero bisection discards a half on exactly
    /// that predicate. Discarding is right in both cases by the argument principle; they are not
    /// the same evidence about where the boundary is doing work.
    #[test]
    fn a_boundary_that_crosses_the_ray_and_encloses_nothing_is_not_a_boundary_that_never_met_it() {
        // Entirely in the upper half plane: the ray is never crossed.
        let (away, _) = polygon_winding(&[corner(1, 1), corner(3, 1), corner(3, 2), corner(1, 2)])
            .expect("an admissible ray");
        assert_eq!(away.total(), 0);
        assert_eq!(away.winding(), 0);
        assert!(!away.cancels());

        // To the right of the origin, straddling the axis: crossed once each hand, encloses nothing.
        let (straddling, _) =
            polygon_winding(&[corner(2, 1), corner(2, -1), corner(3, -1), corner(3, 1)])
                .expect("an admissible ray");
        assert_eq!(
            straddling.winding(),
            0,
            "it encloses nothing and must say so"
        );
        assert_eq!(
            straddling.total(),
            2,
            "and it met the ray twice getting there"
        );
        assert!(straddling.cancels());
        assert_eq!(straddling.with_the_turn.len(), 1);
        assert_eq!(straddling.against_the_turn.len(), 1);
        assert_ne!(
            straddling.with_the_turn, straddling.against_the_turn,
            "the two hands are at different places on the boundary and the receipt says where"
        );

        // Around the origin: one crossing, one turn.
        let (enclosing, _) =
            polygon_winding(&[corner(1, -1), corner(1, 1), corner(-1, 1), corner(-1, -1)])
                .expect("an admissible ray");
        assert_eq!(enclosing.winding(), 1);
        assert_eq!(enclosing.total(), 1);
        assert!(!enclosing.cancels());

        // The property under test genuinely varies across the declared material: a check whose
        // fixtures cannot separate the two readings would be the trivial-orbit defect.
        assert_eq!(
            [away.winding(), straddling.winding(), enclosing.winding()],
            [0, 0, 1]
        );
        assert_eq!(
            [away.total(), straddling.total(), enclosing.total()],
            [0, 2, 1]
        );
    }

    /// Reversing a boundary swaps the hands and negates the winding, and moves nothing else.
    #[test]
    fn the_two_hands_swap_under_reversal_while_the_crossing_population_does_not() {
        let forward = [corner(1, -1), corner(1, 1), corner(-1, 1), corner(-1, -1)];
        let mut backward = forward.to_vec();
        backward.reverse();

        let (ahead, _) = polygon_winding(&forward).expect("an admissible ray");
        let (behind, _) = polygon_winding(&backward).expect("an admissible ray");

        assert_eq!(ahead.winding(), -behind.winding());
        assert_eq!(
            ahead.total(),
            behind.total(),
            "the same passages, the other way"
        );
        assert_eq!(ahead.with_the_turn.len(), behind.against_the_turn.len());
        assert_eq!(ahead.against_the_turn.len(), behind.with_the_turn.len());
    }


    fn probe_config() -> ExactSeriesConfig {
        ExactSeriesConfig {
            dyadic_bits: 96,
            euler_maclaurin_start: 12,
            euler_maclaurin_order: 10,
            log_terms: 28,
            exponential_terms: 18,
            trigonometric_terms: 16,
        }
    }

    fn probe_point() -> ComplexReceiverBox {
        ComplexReceiverBox::point(rat(1, 2), rat(14, 1))
    }

    /// The chain must reproduce the value the plain evaluator returns. If the
    /// decomposition drifted from `zeta_euler_maclaurin` this fires.
    #[test]
    fn the_chain_returns_the_same_eta_as_the_plain_evaluation() {
        let config = probe_config();
        let point = probe_point();
        let chain = eta_chain_decomposition(&point, &config).expect("the chain");
        let plain = eta_evaluate(&point, &config).expect("the plain evaluation");
        assert_eq!(chain.eta, plain.value);
        assert_eq!(chain.head.len() as u32, config.euler_maclaurin_start - 1);
        assert_eq!(chain.crossings.len() as u32, config.euler_maclaurin_order);
    }

    /// The odd-index Bernoulli numbers vanish, so every crossing this chain carries
    /// has ODD order. That is a parity selection rule: it decides which terms exist
    /// before any magnitude is computed.
    #[test]
    fn every_euler_maclaurin_crossing_has_odd_order_and_an_alternating_hand() {
        let chain = eta_chain_decomposition(&probe_point(), &probe_config()).expect("the chain");
        let mut expected_hand = 1;
        for crossing in &chain.crossings {
            assert_eq!(
                crossing.crossing_order % 2,
                1,
                "crossing order {} is even",
                crossing.crossing_order
            );
            assert!(!crossing.bernoulli.numer().is_zero());
            assert_eq!(
                crossing.hand, expected_hand,
                "the hand did not alternate at order {}",
                crossing.crossing_order
            );
            expected_hand = -expected_hand;
        }
    }

    /// Every head term carries its address in the free abelian group on the primes,
    /// and the address must multiply back to the term's own base.
    #[test]
    fn every_head_term_address_reopens_to_its_base() {
        let chain = eta_chain_decomposition(&probe_point(), &probe_config()).expect("the chain");
        for term in &chain.head {
            let rebuilt = term
                .address
                .iter()
                .fold(1u32, |product, valuation| {
                    product * valuation.prime.pow(valuation.exponent)
                });
            assert_eq!(rebuilt, term.base, "address did not reopen to its base");
        }
    }

    /// Borwein's weights are integers — `borwein_weights` refuses otherwise — and
    /// the first is always one.
    #[test]
    fn borwein_weights_are_integers_and_open_at_one() {
        for depth in 1u32..=14 {
            let weights = borwein_weights(depth).expect("integral weights");
            assert_eq!(weights.len(), depth as usize + 1);
            assert_eq!(weights[0], BigInt::one(), "d_0 must be 1 at depth {depth}");
        }
        assert!(borwein_weights(0).is_err(), "depth zero must refuse");
    }

    /// The two frames. Borwein carries no certificate here — his bound needs Gamma,
    /// which this body does not own — so the check is that his chain lands inside the
    /// Euler--Maclaurin enclosure once it is deep enough, AND that it does NOT when it
    /// is shallow. Without the second arm the first could not fail.
    #[test]
    fn the_two_frames_meet_only_once_borwein_is_deep_enough() {
        let config = probe_config();
        let point = probe_point();
        let certified = eta_evaluate(&point, &config).expect("the certified frame").value;
        let overlaps = |left: &RatInterval, right: &RatInterval| {
            left.lower <= right.upper && right.lower <= left.upper
        };
        let agrees = |depth: u32| {
            let borwein = eta_borwein_chain(&point, depth, &config).expect("the Borwein chain");
            overlaps(&borwein.value.re, &certified.re) && overlaps(&borwein.value.im, &certified.im)
        };
        assert!(!agrees(6), "a shallow Borwein chain must NOT reach the enclosure");
        assert!(agrees(32), "a deep Borwein chain must reach the enclosure");
    }

    #[test]
    fn common_continued_fraction_stops_at_the_first_unresolved_turn() {
        let interval = RatInterval::new(rat(14, 1), rat(57, 4));
        assert_eq!(
            interval_common_continued_fraction(&interval, 8),
            vec![BigInt::from(14)]
        );
    }
}
