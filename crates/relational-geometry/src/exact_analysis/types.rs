//! Shared exact interval, receiver, and evaluation types.

use super::*;

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
    #[error(
        "no Euler--Maclaurin start below 2^32 certifies the remainder under the declared grain"
    )]
    EulerMaclaurinStartUnderivable,
    #[error("Borwein's chain needs a depth of at least one")]
    BorweinDepthTooSmall,
    #[error("Borwein weight {0} did not clear its denominator and is not an integer")]
    BorweinWeightNotIntegral(u32),
}

pub(crate) fn factorial(value: u32) -> BigInt {
    (1..=value).fold(BigInt::one(), |product, term| product * BigInt::from(term))
}

pub(super) fn floor_div(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    debug_assert!(denominator.is_positive());
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if numerator.is_negative() && !remainder.is_zero() {
        quotient - BigInt::one()
    } else {
        quotient
    }
}

pub(super) fn dyadic_floor(value: &Rat, bits: u32) -> Rat {
    let denominator = BigInt::one() << bits;
    let scaled_numerator = value.numer() << bits;
    ratio(floor_div(&scaled_numerator, value.denom()), denominator)
}

pub(crate) fn dyadic_ceil(value: &Rat, bits: u32) -> Rat {
    -dyadic_floor(&(-value.clone()), bits)
}
