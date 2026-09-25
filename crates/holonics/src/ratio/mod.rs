//! **Ratio: one per two, before it is a number.**
//!
//! A ratio keeps its two comparands, their units and its presentation
//! ([object](../../../../docs/ELEMENTARY_OBJECTS.md#9-ratio)). The exact rational [`Rat`] is the
//! scalar of every law. Around it:
//!
//! - [`ring`]: exact machine rings, division with remainder and residue in `ℤ/m`;
//! - [`exponentiated`]: the chart transition between the additive and multiplicative charts, and
//!   the normalized kernel read as that transition;
//! - [`surprisal`]: surprisal as an exact symbolic form, the log face of a ratio;
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
pub mod exponentiated;
pub mod linear;
pub mod polynomial;
mod presentation;
pub(crate) mod primality;
pub mod ring;
pub mod surprisal;
pub mod work;

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

/// The integer `value` as a rational.
pub fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
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
