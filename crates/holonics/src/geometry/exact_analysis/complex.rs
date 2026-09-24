//! Exact rational complex-coordinate carrier.

use super::*;

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
