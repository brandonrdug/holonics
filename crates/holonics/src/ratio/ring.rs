//! Exact machine rings used for ratio arithmetic and the portable section realization.
//!
//! `ModularWords` is a host-side chart over `Z/modulus`. At `MERSENNE61`, its reduction dispatches
//! to the exact section arithmetic in [`section`], which the CUDA kernels mirror; every other
//! modulus uses the general exact `u128` path.

use std::fmt;

pub mod section;

use self::section as section_cuda;
use thiserror::Error;

/// A modulus that cannot name a ring with at least two elements.
#[derive(Debug, Clone, Copy, Error, PartialEq, Eq)]
pub enum RingRefusal {
    /// A ring modulus must be at least two.
    #[error("modulus {modulus} does not name a ring with two distinct elements")]
    ModulusTooSmall { modulus: u64 },
}

/// A named exact associative-commutative accumulation law.
///
/// A checked integer carrier may refuse when its exact result leaves `i64`; modular addition is
/// total and exact in its declared quotient ring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccumulationLaw {
    /// Exact addition in `ℤ` while results fit the `i64` carrier.
    IntegerAdd,
    /// Exact addition in `Z/modulus`.
    ModularAdd {
        /// The modulus defining the quotient ring.
        modulus: u64,
    },
}

impl AccumulationLaw {
    /// A stable descriptive name for a receipt.
    pub fn name(self) -> String {
        match self {
            AccumulationLaw::IntegerAdd => String::from("exact-integer-add"),
            AccumulationLaw::ModularAdd { modulus } => format!("exact-modular-add-{modulus}"),
        }
    }
}

/// An exact commutative semiring. `Option` carries refusal when a partial carrier cannot represent
/// the exact sum or product; no implementation wraps or approximates.
pub trait ExactRing {
    /// The ring's value type.
    type Value: Copy + PartialEq + Eq + fmt::Debug;

    /// The additive identity.
    fn zero(&self) -> Self::Value;
    /// Exact addition, or `None` when the exact sum leaves the representation.
    fn add(&self, left: Self::Value, right: Self::Value) -> Option<Self::Value>;
    /// Exact multiplication, or `None` when the exact product leaves the representation.
    fn mul(&self, left: Self::Value, right: Self::Value) -> Option<Self::Value>;
    /// The accumulation law this ring realizes.
    fn law(&self) -> AccumulationLaw;
}

/// Exact integers carried in `i64`; operations refuse instead of wrapping when a result leaves
/// that carrier.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CheckedIntegers;

impl ExactRing for CheckedIntegers {
    type Value = i64;

    fn zero(&self) -> i64 {
        0
    }

    fn add(&self, left: i64, right: i64) -> Option<i64> {
        left.checked_add(right)
    }

    fn mul(&self, left: i64, right: i64) -> Option<i64> {
        left.checked_mul(right)
    }

    fn law(&self) -> AccumulationLaw {
        AccumulationLaw::IntegerAdd
    }
}

/// Exact words of `Z/modulus`, total in both operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModularWords {
    modulus: u64,
}

impl ModularWords {
    /// The Mersenne prime modulus `2^61 - 1`, shared with the portable section realization.
    pub const MERSENNE61: ModularWords = ModularWords {
        modulus: section_cuda::MODULUS,
    };

    /// Words of `Z/modulus`, for a modulus naming a ring with two distinct elements.
    pub fn new(modulus: u64) -> Result<ModularWords, RingRefusal> {
        if modulus < 2 {
            return Err(RingRefusal::ModulusTooSmall { modulus });
        }
        Ok(ModularWords { modulus })
    }

    /// The modulus.
    pub const fn modulus(&self) -> u64 {
        self.modulus
    }

    /// The canonical residue of an arbitrary word.
    pub fn canonical(&self, value: u64) -> u64 {
        if self.modulus == section_cuda::MODULUS {
            section_cuda::canonical(value)
        } else {
            value % self.modulus
        }
    }

    /// Whether a word is the canonical representative of its class in `[0, modulus)`.
    pub fn is_canonical(&self, value: u64) -> bool {
        if self.modulus == section_cuda::MODULUS {
            section_cuda::is_canonical(value)
        } else {
            value < self.modulus
        }
    }
}

impl ExactRing for ModularWords {
    type Value = u64;

    fn zero(&self) -> u64 {
        0
    }

    fn add(&self, left: u64, right: u64) -> Option<u64> {
        if self.modulus == section_cuda::MODULUS {
            Some(section_cuda::add(left, right))
        } else {
            Some((((left as u128) + (right as u128)) % (self.modulus as u128)) as u64)
        }
    }

    fn mul(&self, left: u64, right: u64) -> Option<u64> {
        if self.modulus == section_cuda::MODULUS {
            Some(section_cuda::mul(left, right))
        } else {
            Some((((left as u128) * (right as u128)) % (self.modulus as u128)) as u64)
        }
    }

    fn law(&self) -> AccumulationLaw {
        AccumulationLaw::ModularAdd {
            modulus: self.modulus,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Words spanning the canonical range, its boundary and the non-canonical top of `u64`.
    fn words() -> Vec<u64> {
        let modulus = section_cuda::MODULUS;
        let mut words = vec![
            0,
            1,
            2,
            3,
            modulus - 2,
            modulus - 1,
            modulus,
            modulus + 1,
            u64::MAX,
        ];
        let mut state = 0x9e37_79b9_7f4a_7c15_u64;
        for _ in 0..512 {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            words.push(state);
            words.push(state % modulus);
        }
        words
    }

    #[test]
    fn the_mersenne_ring_uses_the_shared_portable_arithmetic() {
        let ring = ModularWords::MERSENNE61;
        let modulus = section_cuda::MODULUS;
        assert_eq!(ring.modulus(), modulus);
        assert_eq!(
            ring.law(),
            AccumulationLaw::ModularAdd { modulus },
            "the ring names its exact accumulation law"
        );
        let words = words();
        for &left in &words {
            assert_eq!(ring.canonical(left), section_cuda::canonical(left));
            assert_eq!(ring.is_canonical(left), section_cuda::is_canonical(left));
            assert_eq!(ring.canonical(left), left % modulus);
            for &right in words.iter().step_by(7) {
                let sum = ring.add(left, right).expect("total");
                let product = ring.mul(left, right).expect("total");
                assert_eq!(sum, section_cuda::add(left, right));
                assert_eq!(product, section_cuda::mul(left, right));
                let m = u128::from(modulus);
                assert_eq!(u128::from(sum), (u128::from(left) + u128::from(right)) % m);
                assert_eq!(
                    u128::from(product),
                    (u128::from(left) * u128::from(right)) % m
                );
            }
        }
    }

    #[test]
    fn other_moduli_are_exact_and_invalid_moduli_name_the_ring_clause() {
        let ring = ModularWords::new(1_000_003).expect("a ring");
        assert_eq!(ring.add(1_000_002, 5), Some(4));
        assert_eq!(ring.mul(1_000_002, 1_000_002), Some(1));
        assert_eq!(
            ModularWords::new(1).unwrap_err(),
            RingRefusal::ModulusTooSmall { modulus: 1 }
        );
        assert_eq!(
            ModularWords::new(0).unwrap_err(),
            RingRefusal::ModulusTooSmall { modulus: 0 }
        );
        assert_eq!(CheckedIntegers.add(i64::MAX, 1), None);
        assert_eq!(CheckedIntegers.mul(3, -4), Some(-12));
    }
}
