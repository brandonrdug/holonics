//! Exact Euler--Maclaurin evaluation and receiver jets.

use super::*;

/// A second-order jet in `s`: an enclosure of a value and of its first and second derivatives.
///
/// The first derivative is what a boundary certification transports along a segment; the second
/// is what certifies the boundary of the *derivative* — the saddles between the zeros' basins.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ComplexJet2 {
    pub value: ComplexInterval,
    pub first: ComplexInterval,
    pub second: ComplexInterval,
}

impl ComplexJet2 {
    fn constant(value: ComplexInterval) -> Self {
        Self {
            value,
            first: ComplexInterval::zero(),
            second: ComplexInterval::zero(),
        }
    }

    fn add(&self, other: &Self, bits: u32) -> Self {
        Self {
            value: self.value.add(&other.value).round_out(bits),
            first: self.first.add(&other.first).round_out(bits),
            second: self.second.add(&other.second).round_out(bits),
        }
    }

    fn multiply(&self, other: &Self, bits: u32) -> Self {
        Self {
            value: self.value.multiply(&other.value).round_out(bits),
            first: self
                .first
                .multiply(&other.value)
                .add(&self.value.multiply(&other.first))
                .round_out(bits),
            second: self
                .second
                .multiply(&other.value)
                .add(&self.first.multiply(&other.first).scale(&integer(2)))
                .add(&self.value.multiply(&other.second))
                .round_out(bits),
        }
    }

    fn scale(&self, scalar: &Rat, bits: u32) -> Self {
        Self {
            value: self.value.scale(scalar).round_out(bits),
            first: self.first.scale(scalar).round_out(bits),
            second: self.second.scale(scalar).round_out(bits),
        }
    }

    /// `(1/g)' = -g'/g^2`, `(1/g)'' = 2 g'^2/g^3 - g''/g^2`.
    fn reciprocal(&self, bits: u32) -> Result<Self, ExactAnalysisError> {
        let inverse = self.value.reciprocal()?.round_out(bits);
        let inverse_square = inverse.multiply(&inverse).round_out(bits);
        let inverse_cube = inverse_square.multiply(&inverse).round_out(bits);
        Ok(Self {
            value: inverse,
            first: self.first.neg().multiply(&inverse_square).round_out(bits),
            second: self
                .first
                .multiply(&self.first)
                .multiply(&inverse_cube)
                .scale(&integer(2))
                .subtract(&self.second.multiply(&inverse_square))
                .round_out(bits),
        })
    }

    fn divide(&self, other: &Self, bits: u32) -> Result<Self, ExactAnalysisError> {
        Ok(self.multiply(&other.reciprocal(bits)?, bits))
    }
}

pub(super) fn negative_complex_power_jet2(
    base: u32,
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
) -> Result<ComplexJet2, ExactAnalysisError> {
    let bits = config.dyadic_bits;
    let logarithm = log_integer_interval(base, config.log_terms, bits)?;
    let value = negative_complex_power(base, receiver, config)?;
    let minus_log = ComplexInterval::new(logarithm.neg(), RatInterval::point(Rat::zero()));
    let first = value.multiply(&minus_log).round_out(bits);
    let second = first.multiply(&minus_log).round_out(bits);
    Ok(ComplexJet2 {
        value,
        first,
        second,
    })
}

pub(crate) fn bernoulli_number(index: u32) -> Rat {
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

pub(super) fn receiver_jet2(receiver: &ComplexReceiverBox) -> ComplexJet2 {
    ComplexJet2 {
        value: ComplexInterval::new(receiver.sigma.clone(), receiver.tau.clone()),
        first: ComplexInterval::point(RatComplex::new(Rat::one(), Rat::zero())),
        second: ComplexInterval::zero(),
    }
}

pub(super) fn rising_complex(receiver: &ComplexReceiverBox, count: u32) -> ComplexInterval {
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

/// The certified Euler--Maclaurin remainder at a declared start `N` and order `m`: the disc
/// `zeta_euler_maclaurin` adds to its enclosure, exposed so the start can be **derived** from it.
///
/// ```text
///     |R| <= |B_2m| / (2m)!  ·  prod_(i<2m) (|sigma + i| + |tau|)  ·  N^(1 - sigma - 2m) / (sigma + 2m - 1)
/// ```
///
/// The rising product is the receiver's whole `|s|_(2m)` and the power of `N` is what pays it
/// down; nothing here depends on the value of the series, only on the box.
pub fn euler_maclaurin_remainder_bound(
    receiver: &ComplexReceiverBox,
    start: u32,
    order: u32,
    config: &ExactSeriesConfig,
) -> Result<Rat, ExactAnalysisError> {
    if !receiver.sigma.lower.is_positive() {
        return Err(ExactAnalysisError::NonPositiveSigma);
    }
    assert!(start >= 2, "Euler--Maclaurin start must be at least two");
    assert!(order >= 1, "Euler--Maclaurin order must be positive");
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
        let logarithm = log_integer_interval(start, config.log_terms, config.dyadic_bits)?;
        exp_interval(
            &receiver.sigma.multiply(&logarithm).neg(),
            config.exponential_terms,
            config.dyadic_bits,
        )
        .upper
    };
    let denominator_power = Rat::from_integer(BigInt::from(start).pow(even - 1));
    let integral_denominator = &receiver.sigma.lower + integer(i64::from(even - 1));
    Ok(bernoulli * rising_bound * start_amplitude
        / (factorial_even * denominator_power * integral_denominator))
}

/// Derive the Euler--Maclaurin start from the receiver box instead of declaring it.
///
/// A declared start is an authored level. This owner carried `12` from 2026-08-08, and the atlas
/// built on it certified every band up to height thirty-six and then stopped: the remainder grows
/// like `((|tau| + 2m) / N)^(2m)`, so at height sixty no boundary depth could exclude the origin
/// and at height one hundred the enclosure was wider than the function. The height is the
/// material; the start is read off it.
///
/// The returned start is the **least** `N` whose certified remainder is at most `2^-grain_bits`,
/// found by doubling and then bisecting — the remainder is strictly decreasing in `N`, so the
/// least such `N` is well defined. The grain is the one declaration, a receiver coordinate that
/// travels with every return built on the config. Every other field is carried unchanged.
pub fn derive_euler_maclaurin_start(
    receiver: &ComplexReceiverBox,
    base: &ExactSeriesConfig,
    grain_bits: u32,
) -> Result<ExactSeriesConfig, ExactAnalysisError> {
    let order = base.euler_maclaurin_order;
    let grain = ratio(BigInt::one(), BigInt::one() << grain_bits as usize);
    let passes = |start: u32| -> Result<bool, ExactAnalysisError> {
        Ok(euler_maclaurin_remainder_bound(receiver, start, order, base)? <= grain)
    };
    let mut upper = 2u32;
    while !passes(upper)? {
        upper = upper
            .checked_mul(2)
            .ok_or(ExactAnalysisError::EulerMaclaurinStartUnderivable)?;
    }
    let mut lower = upper / 2;
    if lower < 2 {
        lower = 1;
    }
    while upper - lower > 1 {
        let middle = lower + (upper - lower) / 2;
        if passes(middle)? {
            upper = middle;
        } else {
            lower = middle;
        }
    }
    Ok(ExactSeriesConfig {
        euler_maclaurin_start: upper,
        ..base.clone()
    })
}

pub(super) fn zeta_euler_maclaurin(
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

    let remainder = euler_maclaurin_remainder_bound(receiver, start, order, config)?;
    Ok((
        value.add_disc(&remainder).round_out(config.dyadic_bits),
        remainder,
    ))
}

/// The head of the Euler--Maclaurin jet, `sum_(n<N) n^(-s)` with its `s`-derivative
/// `-sum_(n<N) log(n) n^(-s)`, as one enclosure pair. This is the part of the evaluation whose
/// cost is `O(N)` series per point, and it is the part a resident apparatus may supply: the tail
/// below is `O(order)` and stays here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HeadJet {
    pub value: ComplexInterval,
    pub derivative: ComplexInterval,
    /// `sum_(n<N) log(n)^2 n^(-s)`: the second derivative of the head, for the saddles.
    pub second: ComplexInterval,
}

/// The Euler--Maclaurin jet of `zeta` to second order at a receiver box, with the head either
/// summed here or supplied. The three returned radii are the certified remainders of the value,
/// the first and the second derivative; each has already been added to its enclosure.
///
/// The rising products `(s)_(2k-1)` are formed **incrementally** — each correction multiplies the
/// previous product by two more factors — where the earlier owner rebuilt every product from
/// `s`; that was `sum_(k<=m) (2k-1)` jet multiplications per point against `2m` here, and it
/// changes no law, only the rounding sequence.
pub fn zeta_euler_maclaurin_jet2_with_head(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    head: Option<&HeadJet>,
) -> Result<(ComplexJet2, [Rat; 3]), ExactAnalysisError> {
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
    let mut value = match head {
        Some(head) => ComplexJet2 {
            value: head.value.clone(),
            first: head.derivative.clone(),
            second: head.second.clone(),
        },
        None => {
            let mut summed = ComplexJet2::constant(ComplexInterval::zero());
            for base in 1..start {
                summed = summed.add(&negative_complex_power_jet2(base, receiver, config)?, bits);
            }
            summed
        }
    };

    let start_power = negative_complex_power_jet2(start, receiver, config)?;
    let s_minus_one = receiver_jet2(receiver).add(
        &ComplexJet2::constant(ComplexInterval::point(RatComplex::new(
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

    let shifted = |index: u32| -> ComplexJet2 {
        let mut factor = receiver_jet2(receiver);
        factor.value = ComplexInterval::new(
            receiver.sigma.translate(&integer(i64::from(index))),
            receiver.tau.clone(),
        );
        factor
    };
    let mut rising = ComplexJet2::constant(ComplexInterval::point(RatComplex::new(
        Rat::one(),
        Rat::zero(),
    )));
    let mut rising_count = 0u32;
    for correction in 1..=order {
        let even = 2 * correction;
        while rising_count < even - 1 {
            rising = rising.multiply(&shifted(rising_count), bits);
            rising_count += 1;
        }
        let coefficient = bernoulli_number(even) / Rat::from_integer(factorial(even));
        let start_scale = ratio(BigInt::one(), BigInt::from(start).pow(even - 1));
        let term = rising
            .multiply(&start_power, bits)
            .scale(&(coefficient * start_scale), bits);
        value = value.add(&term, bits);
    }

    let even = 2 * order;
    let bernoulli = bernoulli_number(even).abs();
    let factorial_even = Rat::from_integer(factorial(even));
    let bounds = rising_bounds(receiver, even, 2);
    let logarithm = log_integer_interval(start, config.log_terms, bits)?;
    let start_amplitude = exp_interval(
        &receiver.sigma.multiply(&logarithm).neg(),
        config.exponential_terms,
        bits,
    )
    .upper;
    let denominator_power = Rat::from_integer(BigInt::from(start).pow(even - 1));
    let decay = start_amplitude / denominator_power;
    let decay_order = &receiver.sigma.lower + integer(i64::from(even - 1));
    let integral = |power: u32| -> Rat {
        &bernoulli * &decay * log_power_tail_factor(&logarithm.upper, &decay_order, power)
    };
    let (i0, i1, i2) = (integral(0), integral(1), integral(2));
    let remainder = &bounds[0] * &i0 / &factorial_even;
    let derivative_remainder = (&bounds[1] * &i0 + &bounds[0] * &i1) / &factorial_even;
    let second_remainder =
        (&bounds[2] * &i0 + integer(2) * &bounds[1] * &i1 + &bounds[0] * &i2) / &factorial_even;

    value.value = value.value.add_disc(&remainder).round_out(bits);
    value.first = value.first.add_disc(&derivative_remainder).round_out(bits);
    value.second = value.second.add_disc(&second_remainder).round_out(bits);
    Ok((value, [remainder, derivative_remainder, second_remainder]))
}

/// Bounds on `|(s)_count^(j)|` over the receiver box for `j <= order`, by the product rule on
/// bounds: appending a factor `(s + i)` with `|s + i| <= f` gives `R_j <- R_j f + j R_(j-1)`.
pub(super) fn rising_bounds(receiver: &ComplexReceiverBox, count: u32, order: u32) -> Vec<Rat> {
    let tau_bound = receiver.tau.abs_upper();
    let mut bounds = vec![Rat::zero(); order as usize + 1];
    bounds[0] = Rat::one();
    for index in 0..count {
        let factor = receiver
            .sigma
            .translate(&integer(i64::from(index)))
            .abs_upper()
            + &tau_bound;
        for j in (1..=order as usize).rev() {
            bounds[j] = &bounds[j] * &factor + integer(j as i64) * &bounds[j - 1];
        }
        bounds[0] *= &factor;
    }
    bounds
}

/// `N^a · ∫_N^∞ x^(-a-1) log(x)^k dx = sum_(t<=k) k!/t! · log(N)^t / a^(k-t+1)`, the factor by which
/// a tail integral with `log^k` exceeds the bare decay `N^(-a)`.
pub(super) fn log_power_tail_factor(log_n: &Rat, a: &Rat, k: u32) -> Rat {
    let mut total = Rat::zero();
    let mut falling = Rat::one(); // k!/t! for t = k, then k, k(k-1), ...
    for t in (0..=k).rev() {
        let mut term = &falling * log_n.clone().pow(t as i32);
        for _ in 0..(k - t + 1) {
            term /= a;
        }
        total += term;
        falling *= integer(i64::from(t));
    }
    total
}

/// `binom(k, j)` as a rational.
pub(super) fn binomial(k: u32, j: u32) -> Rat {
    let mut value = Rat::one();
    for i in 0..j {
        value = value * integer(i64::from(k - i)) / integer(i64::from(i + 1));
    }
    value
}

/// A uniform bound over the receiver box on `|zeta^(k)(s)|`, `k <= 3`, from the Euler--Maclaurin
/// representation at the config's start and order: every piece is differentiated by Leibniz and
/// bounded by its magnitude at the box's lower `sigma` and upper `|tau|`. It is crude and it is
/// exact; it enters only as the second-order term of a segment's transport.
pub fn zeta_derivative_bound_uniform(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    k: u32,
) -> Result<Rat, ExactAnalysisError> {
    if !receiver.sigma.lower.is_positive() {
        return Err(ExactAnalysisError::NonPositiveSigma);
    }
    if !receiver.tau.lower.is_positive() {
        return Err(ExactAnalysisError::ZetaPoleInReceiver);
    }
    assert!(k <= 3, "the uniform bound is written to third order");
    let bits = config.dyadic_bits;
    let start = config.euler_maclaurin_start;
    let order = config.euler_maclaurin_order;
    let sigma = receiver.sigma.lower.clone();
    let amplitude = |base: u32| -> Result<(Rat, Rat), ExactAnalysisError> {
        let logarithm = log_integer_interval(base, config.log_terms, bits)?;
        let magnitude = exp_interval(
            &RatInterval::point(-&sigma).multiply(&logarithm),
            config.exponential_terms,
            bits,
        )
        .upper;
        Ok((magnitude, logarithm.upper))
    };
    // the head
    let mut total = Rat::zero();
    for base in 1..start {
        let (magnitude, log) = amplitude(base)?;
        total += magnitude * log.pow(k as i32);
    }
    let (start_magnitude, log_n) = amplitude(start)?;
    // `N · N^(-s) / (s - 1)`: Leibniz over `N^(1-s)` and `(s-1)^(-1)`, with `|s - 1| >= tau`
    let tau = receiver.tau.lower.clone();
    let mut leading = Rat::zero();
    for j in 0..=k {
        let i = k - j;
        let mut factorial_i = Rat::one();
        for f in 1..=i {
            factorial_i *= integer(i64::from(f));
        }
        leading += binomial(k, j) * log_n.clone().pow(j as i32) * &factorial_i
            / tau.clone().pow((i + 1) as i32);
    }
    total += integer(i64::from(start)) * &start_magnitude * leading;
    // `N^(-s) / 2`
    total += &start_magnitude * log_n.clone().pow(k as i32) / integer(2);
    // the corrections
    for correction in 1..=order {
        let even = 2 * correction;
        let coefficient = bernoulli_number(even).abs() / Rat::from_integer(factorial(even));
        let scale = ratio(BigInt::one(), BigInt::from(start).pow(even - 1));
        let bounds = rising_bounds(receiver, even - 1, k);
        let mut piece = Rat::zero();
        for i in 0..=k {
            piece += binomial(k, i) * &bounds[i as usize] * log_n.clone().pow((k - i) as i32);
        }
        total += coefficient * scale * &start_magnitude * piece;
    }
    // the remainder
    let even = 2 * order;
    let bernoulli = bernoulli_number(even).abs();
    let factorial_even = Rat::from_integer(factorial(even));
    let bounds = rising_bounds(receiver, even, k);
    let decay = &start_magnitude / Rat::from_integer(BigInt::from(start).pow(even - 1));
    let decay_order = &sigma + integer(i64::from(even - 1));
    let mut piece = Rat::zero();
    for i in 0..=k {
        piece += binomial(k, i)
            * &bounds[i as usize]
            * &bernoulli
            * &decay
            * log_power_tail_factor(&log_n, &decay_order, k - i);
    }
    total += piece / factorial_even;
    Ok(dyadic_ceil(&total, bits))
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
    eta_evaluate_jet_with_head(receiver, config, None)
}

/// [`eta_evaluate_jet`] with the `O(N)` head supplied by another apparatus. The head must be a
/// valid enclosure of `sum_(n<N) n^(-s)` and of its derivative at `N = config.euler_maclaurin_start`
/// over the receiver box; the tail, the corrections, the certified remainder and the `eta` factor
/// are formed here exactly as on the serial path.
pub fn eta_evaluate_jet_with_head(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    head: Option<&HeadJet>,
) -> Result<EtaJetEvaluation, ExactAnalysisError> {
    let eta = eta_evaluate_jet2_with_head(receiver, config, head)?;
    Ok(EtaJetEvaluation {
        receiver: receiver.clone(),
        value: eta.jet.value,
        derivative: eta.jet.first,
        remainder_radius: eta.remainders[0].clone(),
        derivative_remainder_radius: eta.remainders[1].clone(),
    })
}

/// A second-order jet evaluation with its three certified remainder radii.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Jet2Evaluation {
    pub receiver: ComplexReceiverBox,
    pub jet: ComplexJet2,
    pub remainders: [Rat; 3],
}

/// `zeta`, `zeta'`, `zeta''` at the receiver, head supplied or summed.
pub fn zeta_evaluate_jet2_with_head(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    head: Option<&HeadJet>,
) -> Result<Jet2Evaluation, ExactAnalysisError> {
    let (jet, remainders) = zeta_euler_maclaurin_jet2_with_head(receiver, config, head)?;
    Ok(Jet2Evaluation {
        receiver: receiver.clone(),
        jet,
        remainders,
    })
}

/// `eta`, `eta'`, `eta''` at the receiver: the `zeta` jet times the jet of `1 - 2^(1-s)`.
pub fn eta_evaluate_jet2_with_head(
    receiver: &ComplexReceiverBox,
    config: &ExactSeriesConfig,
    head: Option<&HeadJet>,
) -> Result<Jet2Evaluation, ExactAnalysisError> {
    let bits = config.dyadic_bits;
    let (zeta, remainders) = zeta_euler_maclaurin_jet2_with_head(receiver, config, head)?;
    let two_power = negative_complex_power_jet2(2, receiver, config)?;
    let factor = ComplexJet2::constant(ComplexInterval::point(RatComplex::new(
        Rat::one(),
        Rat::zero(),
    )))
    .add(&two_power.scale(&integer(-2), bits), bits);
    Ok(Jet2Evaluation {
        receiver: receiver.clone(),
        jet: factor.multiply(&zeta, bits),
        remainders,
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
        let logarithm = log_integer_interval(base, config.log_terms, config.dyadic_bits)?;
        let amplitude = exp_interval(
            &RatInterval::point(-&sigma).multiply(&logarithm),
            config.exponential_terms,
            config.dyadic_bits,
        )
        .upper;
        finite += amplitude * &logarithm.upper * &logarithm.upper;
    }

    let logarithm = log_integer_interval(tail_start, config.log_terms, config.dyadic_bits)?;
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
