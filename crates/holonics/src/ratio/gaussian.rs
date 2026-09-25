//! **The Gaussian rational** `re + i·im`: the exact complex scalar, the field `ℚ(i)`.
//!
//! [definition] An element of `ℚ(i)`: two exact rationals. Its operations are the field's; a
//! division by zero is a typed refusal. The unit circle of this field is the parametron's carrier
//! ([`crate::holon::parametron::Carrier::as_gaussian`]); the physical instances (fluid potentials,
//! wave amplitudes) and the causal chord's resolvent probe carry their complex values in it. Lean
//! works over `ℂ` (`Physics/Fluid/Singularity`, `Physics/Fluid/ComplexFluid`,
//! `Physics/Wave/Interference`); every value computed here is a Gaussian-rational instance of those
//! statements.

use num_traits::{One, Zero};
use thiserror::Error;

use super::surprisal::SurprisalError;
use super::{ExactField, Rat, integer};

/// Every refusal of the Gaussian rationals and of the log ratio carried over them.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum GaussianError {
    #[error("{what} has no inverse: its value is zero")]
    ZeroDivisor { what: &'static str },
    #[error(
        "segment {segment} of the continuation passes through zero, where the ratio has no logarithm"
    )]
    ThroughZero { segment: usize },
    #[error("the modulus left the rationals: a prime valuation of the quadrance ratio is odd")]
    ModulusNotRational,
    #[error(transparent)]
    Surprisal(#[from] SurprisalError),
}

/// [definition] **A Gaussian rational** `re + i·im`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GaussianRat {
    pub re: Rat,
    pub im: Rat,
}

impl GaussianRat {
    pub fn new(re: Rat, im: Rat) -> Self {
        Self { re, im }
    }

    pub fn from_i64(re: i64, im: i64) -> Self {
        Self::new(integer(re), integer(im))
    }

    /// The real number `r`.
    pub fn real(re: Rat) -> Self {
        Self::new(re, Rat::zero())
    }

    pub fn zero() -> Self {
        Self::real(Rat::zero())
    }

    pub fn one() -> Self {
        Self::real(Rat::one())
    }

    /// The quarter turn `i`.
    pub fn i() -> Self {
        Self::new(Rat::zero(), Rat::one())
    }

    pub fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero()
    }

    pub fn is_real(&self) -> bool {
        self.im.is_zero()
    }

    pub fn add(&self, other: &Self) -> Self {
        Self::new(&self.re + &other.re, &self.im + &other.im)
    }

    pub fn sub(&self, other: &Self) -> Self {
        Self::new(&self.re - &other.re, &self.im - &other.im)
    }

    pub fn neg(&self) -> Self {
        Self::new(-self.re.clone(), -self.im.clone())
    }

    pub fn mul(&self, other: &Self) -> Self {
        Self::new(
            &self.re * &other.re - &self.im * &other.im,
            &self.re * &other.im + &self.im * &other.re,
        )
    }

    /// Multiply by a rational.
    pub fn scale(&self, factor: &Rat) -> Self {
        Self::new(&self.re * factor, &self.im * factor)
    }

    /// The conjugate `re − i·im`: the Swing of the imaginary axis.
    pub fn conj(&self) -> Self {
        Self::new(self.re.clone(), -self.im.clone())
    }

    /// `|z|² = re² + im²`, the quadrance.
    pub fn norm_sq(&self) -> Rat {
        &self.re * &self.re + &self.im * &self.im
    }

    /// `z⁻¹ = conj z / |z|²`, refused at zero.
    pub fn inverse(&self) -> Result<Self, GaussianError> {
        let quadrance = self.norm_sq();
        if quadrance.is_zero() {
            return Err(GaussianError::ZeroDivisor {
                what: "a Gaussian rational",
            });
        }
        Ok(self.conj().scale(&(Rat::one() / quadrance)))
    }

    /// `self / other`, refused at `other = 0`.
    pub fn div(&self, other: &Self) -> Result<Self, GaussianError> {
        Ok(self.mul(&other.inverse()?))
    }

    /// `zⁿ` for `n ≥ 0`.
    pub fn pow(&self, exponent: u32) -> Self {
        (0..exponent).fold(Self::one(), |power, _| power.mul(self))
    }
}

impl ExactField for GaussianRat {
    fn from_rat(value: Rat) -> Self {
        Self::real(value)
    }

    fn plus(&self, other: &Self) -> Self {
        self.add(other)
    }

    fn minus(&self, other: &Self) -> Self {
        self.sub(other)
    }

    fn times(&self, other: &Self) -> Self {
        self.mul(other)
    }

    fn reciprocal(&self) -> Option<Self> {
        self.inverse().ok()
    }

    fn vanishes(&self) -> bool {
        self.is_zero()
    }

    fn as_gaussian(&self) -> GaussianRat {
        self.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::rat;

    /// The field laws the physical laws rest on: `i² = −1`, `z z̄ = |z|²`, `z · z⁻¹ = 1`, and zero
    /// has no inverse.
    #[test]
    fn the_gaussian_rationals_are_a_field_with_conjugation() {
        let i = GaussianRat::i();
        assert_eq!(i.mul(&i), GaussianRat::from_i64(-1, 0));
        let z = GaussianRat::new(rat(3, 2), rat(-5, 7));
        assert_eq!(z.mul(&z.conj()), GaussianRat::real(z.norm_sq()));
        assert_eq!(z.mul(&z.inverse().unwrap()), GaussianRat::one());
        assert!(GaussianRat::zero().inverse().is_err());
        assert_eq!(z.pow(3), z.mul(&z).mul(&z));
    }
}
