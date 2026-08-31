//! Exact eta chain and current transport.

use super::*;

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

pub(super) fn prime_address(mut base: u32) -> Vec<PrimeValuation> {
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

pub(super) fn negative_complex_power_parts(
    base: u32,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<EtaChainTerm, ExactAnalysisError> {
    let logarithm = log_integer_interval(base, config.log_terms, config.dyadic_bits)?;
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

pub(super) fn borwein_weights(depth: u32) -> Result<Vec<BigInt>, ExactAnalysisError> {
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

pub(super) fn prime_valuations(mut value: u32) -> Vec<PrimeValuation> {
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
    let logarithm = log_integer_interval(tail_start, config.log_terms, config.dyadic_bits)?;
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
