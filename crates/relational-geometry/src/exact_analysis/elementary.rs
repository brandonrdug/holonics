//! Elementary exact rational and complex series.

use super::*;
use std::cell::RefCell;
use std::collections::HashMap;

thread_local! {
    /// Enclosures of integer logarithms, keyed by base and precision.
    static INTEGER_LOGARITHMS: RefCell<HashMap<(u32, u32, u32), RatInterval>> =
        RefCell::new(HashMap::new());
}

/// `log n` for an integer base, memoized per thread. Exact: the enclosure is the series' own.
pub fn log_integer_interval(
    base: u32,
    terms: u32,
    bits: u32,
) -> Result<RatInterval, ExactAnalysisError> {
    let key = (base, terms, bits);
    if let Some(found) = INTEGER_LOGARITHMS.with(|memo| memo.borrow().get(&key).cloned()) {
        return Ok(found);
    }
    let value = log_rational_interval(&Rat::from_integer(BigInt::from(base)), terms, bits)?;
    INTEGER_LOGARITHMS.with(|memo| {
        memo.borrow_mut().insert(key, value.clone());
    });
    Ok(value)
}

pub(super) fn atanh_log_unit_interval(value: &Rat, terms: u32, bits: u32) -> RatInterval {
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

pub(super) fn exp_nonnegative_point(value: &Rat, terms: u32, bits: u32) -> RatInterval {
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

pub(super) fn sin_cos_small(value: &Rat, terms: u32, bits: u32) -> (RatInterval, RatInterval) {
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

pub(crate) fn negative_complex_power(
    base: u32,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<ComplexInterval, ExactAnalysisError> {
    let logarithm = log_integer_interval(base, config.log_terms, config.dyadic_bits)?;
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
