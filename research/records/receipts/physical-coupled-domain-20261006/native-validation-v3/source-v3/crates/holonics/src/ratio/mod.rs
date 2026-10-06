//! **Ratio: one per two, before it is a number.**
//!
//! A ratio keeps its two comparands, their units and its presentation
//! ([object](../../../../docs/ELEMENTARY_OBJECTS.md#9-ratio)). The exact rational [`Rat`] is the
//! scalar of every law. Around it:
//!
//! - [`ring`]: exact machine rings, division with remainder and residue in `ℤ/m`;
//! - [`exponentiated`]: the chart transition between the additive and multiplicative charts, and
//!   the normalized kernel read as that transition;
//! - [`surprisal`]: surprisal as an exact symbolic form, the log face of a ratio, and the one
//!   `log₂` of a positive rational ([`surprisal::SymbolicSurprisal::log2_of_ratio`]);
//! - [`gaussian`]: the Gaussian rationals `ℚ(i)`, the exact complex scalar, and [`LogRatio`], the
//!   log of an undivided ratio with its winding, continued along a path by lifting;
//! - [`ExactField`]: the field operations shared by `ℚ` and `ℚ(i)`, over which the Möbius
//!   navigator of `compression::landmark` is written once;
//! - [`linear`]: the exact linear carrier over ℚ, whose inversion returns the complete preimage
//!   fibre (particular plus kernel) instead of inventing a reciprocal;
//! - [`Presentation`]: a ratio carried as its undivided pair, ordered by cross-multiplication in
//!   the four-state [`ExactOrdering`].
//!
//! Lean: `Objects/{Ratio,RatioPhase,RatioBlock}`, `Foundation/TransportLift`,
//! `Geometry/{PhaseCarry,CrossRatio}`.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;

pub mod algebraic;
pub mod disk;
pub mod exponentiated;
pub mod gaussian;
pub mod linear;
mod log_ratio;
pub mod polynomial;
mod presentation;
pub(crate) mod primality;
pub mod ring;
pub mod surprisal;
pub mod work;

pub use gaussian::{GaussianError, GaussianRat};
pub use log_ratio::LogRatio;
pub use presentation::Presentation;

/// The exact rational: a ratio of two integers in lowest terms.
pub type Rat = BigRational;

/// The rational `numerator / denominator`. A zero denominator is refused by panic: a literal ratio
/// with nothing to compare against is a caller defect, not a value.
pub fn rat(numerator: i64, denominator: i64) -> Rat {
    assert_ne!(
        denominator, 0,
        "an exact ratio cannot have denominator zero"
    );
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

/// [definition] **An exact field of scalars**: `ℚ` and its quadratic extension `ℚ(i)`. The
/// operations are the field's, with the inverse refused at zero; every scalar embeds in `ℚ(i)`
/// ([`ExactField::as_gaussian`]), where a refusal reports it. A law written once over this trait
/// (the Möbius navigator's block, trace, determinant, action and fixed points) is one law for both
/// fields, as Lean's `Mobius K` is one structure over every field.
pub trait ExactField: Clone + PartialEq + Eq + std::fmt::Debug {
    /// The rational `value` in this field.
    fn from_rat(value: Rat) -> Self;
    fn plus(&self, other: &Self) -> Self;
    fn minus(&self, other: &Self) -> Self;
    fn times(&self, other: &Self) -> Self;
    /// `1/self`, `None` at zero.
    fn reciprocal(&self) -> Option<Self>;
    fn vanishes(&self) -> bool;
    /// The scalar in `ℚ(i)`.
    fn as_gaussian(&self) -> GaussianRat;
}

impl ExactField for Rat {
    fn from_rat(value: Rat) -> Self {
        value
    }

    fn plus(&self, other: &Self) -> Self {
        self + other
    }

    fn minus(&self, other: &Self) -> Self {
        self - other
    }

    fn times(&self, other: &Self) -> Self {
        self * other
    }

    fn reciprocal(&self) -> Option<Self> {
        (!num_traits::Zero::is_zero(self)).then(|| self.recip())
    }

    fn vanishes(&self) -> bool {
        num_traits::Zero::is_zero(self)
    }

    fn as_gaussian(&self) -> GaussianRat {
        GaussianRat::real(self.clone())
    }
}

/// The integer `value` as a rational.
pub fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// **Finite rational order without a recursive continued-fraction comparison.**
///
/// Compare the integer pairs by `n_left d_right` and `n_right d_left`, reversing the
/// order when the denominator signs differ. Equal denominators or numerators need no
/// products. The products may be wider than their operands; this is a stack bound, not
/// a claim that multiplication is always cheaper than division.
///
/// A raw negative denominator is supported. A raw zero denominator is not a rational
/// and is refused by panic, as in [`rat`]. No scalar quotient is formed.
pub fn compare(left: &Rat, right: &Rat) -> Ordering {
    use num_traits::{Signed, Zero};
    assert!(
        !left.denom().is_zero() && !right.denom().is_zero(),
        "a rational comparison requires nonzero denominators"
    );
    if left.denom() == right.denom() {
        let order = left.numer().cmp(right.numer());
        return if left.denom().is_negative() {
            order.reverse()
        } else {
            order
        };
    }
    let flipped = left.denom().is_negative() ^ right.denom().is_negative();
    let order = if left.numer() == right.numer() {
        if left.numer().is_zero() {
            return Ordering::Equal;
        }
        let order = left.denom().cmp(right.denom());
        if left.numer().is_negative() {
            order
        } else {
            order.reverse()
        }
    } else {
        (left.numer() * right.denom()).cmp(&(right.numer() * left.denom()))
    };
    if flipped { order.reverse() } else { order }
}

#[cfg(test)]
mod comparison_tests {
    use super::*;

    #[test]
    fn signed_and_unreduced_pairs_keep_the_exact_finite_order() {
        for n in -2..=2 {
            for d in [-3, -1, 1, 3] {
                for m in -2..=2 {
                    for e in [-3, -1, 1, 3] {
                        let left = Rat::new_raw(n.into(), d.into());
                        let right = Rat::new_raw(m.into(), e.into());
                        assert_eq!(compare(&left, &right), rat(n, d).cmp(&rat(m, e)));
                    }
                }
            }
        }
    }

    #[test]
    #[should_panic(expected = "a rational comparison requires nonzero denominators")]
    fn a_raw_zero_denominator_has_no_finite_order() {
        compare(&Rat::new_raw(1.into(), 0.into()), &integer(1));
    }
}

/// **Euclid's greatest common divisor** of two integers, nonnegative, with `gcd(0, 0) = 0`: the
/// remainder face of division, iterated. The crate's one owner of it.
pub(crate) fn gcd(left: &BigInt, right: &BigInt) -> BigInt {
    use num_traits::{Signed, Zero};
    let mut a = left.abs();
    let mut b = right.abs();
    while !b.is_zero() {
        let remainder = &a % &b;
        a = std::mem::replace(&mut b, remainder);
    }
    a
}

/// **The four-state order of two exact readings.** `Open` is not a tie: it is returned when the
/// exact certificates cannot separate the two, and it keeps both operands rather than breaking the
/// tie by an epsilon.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
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
