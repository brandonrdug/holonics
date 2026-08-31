//! Exact elementary constants and Riemann--Siegel tide.

use super::*;

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

pub(super) fn rational_floor(value: &Rat) -> BigInt {
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

// --- the tide: an exact enclosure of the Riemann--Siegel theta ------------------------------

/// Euler's arctangent series for `|q| <= 1`:
/// `atan(q) = q/(1+q^2) · sum_k (2k)!!/(2k+1)!! · (q^2/(1+q^2))^k`, all terms positive, ratio
/// below `r = q^2/(1+q^2) <= 1/2`, so the tail after the first omitted term is at most that term
/// over `1 - r`. The term count is not declared: terms are taken until the next one is under the
/// grain.
pub(super) fn atan_unit_interval(q: &Rat, bits: u32) -> RatInterval {
    if q.is_zero() {
        return RatInterval::point(Rat::zero());
    }
    let square = q * q;
    let one_plus = Rat::one() + &square;
    let r = &square / &one_plus;
    let grain = ratio(BigInt::one(), BigInt::one() << (bits + 4) as usize);
    let mut term = q / &one_plus;
    let mut partial = RatInterval::point(term.clone());
    let mut k = 0u32;
    loop {
        k += 1;
        term = &term * &r * integer(i64::from(2 * k)) / integer(i64::from(2 * k + 1));
        if term.abs() < grain || k > 4096 {
            break;
        }
        partial = partial
            .add(&RatInterval::point(term.clone()))
            .round_out(bits);
    }
    let tail = term.abs() / (Rat::one() - &r);
    RatInterval::new(&partial.lower - &tail, &partial.upper + &tail).round_out(bits)
}

/// `pi` by Machin: `16 atan(1/5) - 4 atan(1/239)`.
pub fn pi_interval(bits: u32) -> RatInterval {
    atan_unit_interval(&rat(1, 5), bits)
        .scale(&integer(16))
        .subtract(&atan_unit_interval(&rat(1, 239), bits).scale(&integer(4)))
        .round_out(bits)
}

/// `atan(q)` for any rational `q`, by `atan(q) = pi/2 - atan(1/q)` beyond one.
pub fn atan_interval(q: &Rat, bits: u32) -> RatInterval {
    if q.abs() <= Rat::one() {
        return atan_unit_interval(q, bits);
    }
    let half_pi = pi_interval(bits).scale(&rat(1, 2));
    let reciprocal = atan_unit_interval(&(Rat::one() / q), bits);
    if q.is_positive() {
        half_pi.subtract(&reciprocal).round_out(bits)
    } else {
        half_pi.neg().subtract(&reciprocal).round_out(bits)
    }
}

/// The principal logarithm of the point `x + iy` with `x > 0`: `log|z| = log(x^2+y^2)/2`,
/// `arg z = atan(y/x)`.
pub fn complex_log_point(
    x: &Rat,
    y: &Rat,
    config: &ExactSeriesConfig,
) -> Result<ComplexInterval, ExactAnalysisError> {
    if !x.is_positive() {
        return Err(ExactAnalysisError::NonPositiveLogarithm);
    }
    let bits = config.dyadic_bits;
    let modulus_square = x * x + y * y;
    let log_modulus =
        log_rational_interval(&modulus_square, config.log_terms, bits)?.scale(&rat(1, 2));
    let argument = atan_interval(&(y / x), bits);
    Ok(ComplexInterval::new(log_modulus, argument).round_out(bits))
}

/// The principal `log Gamma` at the point `x + iy`, `x > 0`, by a shift of sixteen and Stirling's
/// series at the config's order, with the remainder disc
/// `|B_(2m+2)| / ((2m+1)(2m+2) |z|^(2m+1)) · sec(arg z / 2)^(2m+2)`, where `sec^2(arg z/2) <= 2`
/// on the right half-plane. The shift is apparatus: its consequence — the size of the disc — is
/// exhibited in the enclosure and never decides anything.
pub fn log_gamma_point(
    x: &Rat,
    y: &Rat,
    config: &ExactSeriesConfig,
) -> Result<ComplexInterval, ExactAnalysisError> {
    if !x.is_positive() {
        return Err(ExactAnalysisError::NonPositiveLogarithm);
    }
    let bits = config.dyadic_bits;
    let shift = 16i64;
    let mut shifted_logs = ComplexInterval::zero();
    for k in 0..shift {
        shifted_logs = shifted_logs
            .add(&complex_log_point(&(x + integer(k)), y, config)?)
            .round_out(bits);
    }
    let xs = x + integer(shift);
    let z = ComplexInterval::point(RatComplex::new(xs.clone(), y.clone()));
    let log_z = complex_log_point(&xs, y, config)?;
    let half = rat(1, 2);
    let z_minus_half = ComplexInterval::point(RatComplex::new(&xs - &half, y.clone()));
    let pi = pi_interval(bits);
    let log_two_pi = RatInterval::new(
        log_rational_interval(&(integer(2) * &pi.lower), config.log_terms, bits)?.lower,
        log_rational_interval(&(integer(2) * &pi.upper), config.log_terms, bits)?.upper,
    );
    let mut stirling = z_minus_half
        .multiply(&log_z)
        .subtract(&z)
        .add(&ComplexInterval::new(
            log_two_pi.scale(&half),
            RatInterval::point(Rat::zero()),
        ))
        .round_out(bits);
    let inverse = z.reciprocal()?.round_out(bits);
    let inverse_square = inverse.multiply(&inverse).round_out(bits);
    let mut power = inverse.clone();
    let order = config.euler_maclaurin_order;
    for k in 1..=order {
        let even = 2 * k;
        let coefficient =
            bernoulli_number(even) / (integer(i64::from(even)) * integer(i64::from(even - 1)));
        stirling = stirling.add(&power.scale(&coefficient)).round_out(bits);
        power = power.multiply(&inverse_square).round_out(bits);
    }
    let even = 2 * order + 2;
    let modulus_lower = if xs >= y.abs() { xs.clone() } else { y.abs() };
    let mut disc =
        bernoulli_number(even).abs() / (integer(i64::from(even - 1)) * integer(i64::from(even)));
    for _ in 0..(even - 1) {
        disc /= &modulus_lower;
    }
    disc *= Rat::from_integer(BigInt::one() << (order + 1) as usize);
    Ok(stirling
        .subtract(&shifted_logs)
        .add_disc(&disc)
        .round_out(bits))
}

/// The Riemann--Siegel theta, `theta(t) = Im log Gamma(1/4 + it/2) - (t/2) log pi`, as an exact
/// enclosure. On the critical line `zeta(1/2 + it) = e^(-i theta(t)) Z(t)` with `Z` real, so this
/// is the tide the zero count rides: `N(T) = theta(T)/pi + 1 + S(T)`.
pub fn riemann_siegel_theta(
    t: &Rat,
    config: &ExactSeriesConfig,
) -> Result<RatInterval, ExactAnalysisError> {
    let bits = config.dyadic_bits;
    let half_t = t * rat(1, 2);
    let log_gamma = log_gamma_point(&rat(1, 4), &half_t, config)?;
    let pi = pi_interval(bits);
    let log_pi = RatInterval::new(
        log_rational_interval(&pi.lower, config.log_terms, bits)?.lower,
        log_rational_interval(&pi.upper, config.log_terms, bits)?.upper,
    );
    Ok(log_gamma
        .im
        .subtract(&log_pi.scale(&half_t))
        .round_out(bits))
}
