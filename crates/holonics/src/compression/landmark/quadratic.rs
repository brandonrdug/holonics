//! **A root of a rational quadratic, carried as its constraint: `p + q√D` over ℚ.**
//!
//! [definition] A landmark that is not rational (a boost's Doppler ratio, a Möbius navigator's
//! irrational fixed point) is a root of a quadratic over ℚ. It is carried in the quadratic field
//! `ℚ(√D)` as the pair `(p, q)` with the declared radicand `D ≥ 0`, never as a real: sums,
//! products, conjugates, norms and inverses stay in the field, and its sign and order are decided
//! exactly (a real `√D` is never formed). When `D` is a rational square the value folds to a
//! rational.
//!
//! [definition; agent-inferred] Values built from one construction share one radicand. Two
//! different nonzero radicands name two representations of possibly different fields; combining
//! them is refused rather than guessed, since recognizing `√8 = 2√2` would need a squarefree
//! factorization the construction never asked for.

use std::cmp::Ordering;

use num_traits::{One, Signed, Zero};

use crate::compression::landmark::LandmarkError;
use crate::ratio::Rat;

/// **The exact square root of a rational**, or `None` when it is not a rational square.
pub fn rational_square_root(value: &Rat) -> Option<Rat> {
    if value.is_negative() {
        return None;
    }
    let (numerator, denominator) = (value.numer(), value.denom());
    let (numerator_root, denominator_root) = (numerator.sqrt(), denominator.sqrt());
    (&(&numerator_root * &numerator_root) == numerator
        && &(&denominator_root * &denominator_root) == denominator)
        .then(|| Rat::new(numerator_root, denominator_root))
}

/// [definition] **`p + q√D`**: an element of the quadratic field `ℚ(√D)`, `D ≥ 0`. The normal form
/// keeps `q = 0 ⇔ D = 0` and never a rational-square `D` beside a nonzero `q`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct QuadraticSurd {
    rational: Rat,
    radical: Rat,
    radicand: Rat,
}

impl QuadraticSurd {
    /// `p + q√D`, refused for a negative radicand; a rational-square radicand folds.
    pub fn new(rational: Rat, radical: Rat, radicand: Rat) -> Result<Self, LandmarkError> {
        if radicand.is_negative() {
            return Err(LandmarkError::NegativeRadicand { radicand });
        }
        if radical.is_zero() || radicand.is_zero() {
            return Ok(Self::rational(rational));
        }
        if let Some(root) = rational_square_root(&radicand) {
            return Ok(Self::rational(rational + radical * root));
        }
        Ok(Self {
            rational,
            radical,
            radicand,
        })
    }

    /// A rational, `p + 0·√0`.
    pub fn rational(value: Rat) -> Self {
        Self {
            rational: value,
            radical: Rat::zero(),
            radicand: Rat::zero(),
        }
    }

    /// `p`.
    pub fn rational_part(&self) -> &Rat {
        &self.rational
    }

    /// `q`.
    pub fn radical_part(&self) -> &Rat {
        &self.radical
    }

    /// `D`, zero for a rational.
    pub fn radicand(&self) -> &Rat {
        &self.radicand
    }

    /// The rational value, when `q = 0`.
    pub fn as_rational(&self) -> Option<&Rat> {
        self.radical.is_zero().then_some(&self.rational)
    }

    /// The Galois conjugate `p − q√D`.
    pub fn conjugate(&self) -> Self {
        Self {
            rational: self.rational.clone(),
            radical: -self.radical.clone(),
            radicand: self.radicand.clone(),
        }
    }

    /// The field norm `(p + q√D)(p − q√D) = p² − q²D`, a rational.
    pub fn norm(&self) -> Rat {
        &self.rational * &self.rational - &self.radical * &self.radical * &self.radicand
    }

    /// The trace `2p`, a rational.
    pub fn trace(&self) -> Rat {
        &self.rational + &self.rational
    }

    fn shared_radicand(&self, other: &Self) -> Result<Rat, LandmarkError> {
        if self.radical.is_zero() {
            Ok(other.radicand.clone())
        } else if other.radical.is_zero() || self.radicand == other.radicand {
            Ok(self.radicand.clone())
        } else {
            Err(LandmarkError::RadicandMismatch {
                left: self.radicand.clone(),
                right: other.radicand.clone(),
            })
        }
    }

    /// `self + other` in the shared field.
    pub fn add(&self, other: &Self) -> Result<Self, LandmarkError> {
        let radicand = self.shared_radicand(other)?;
        Self::new(
            &self.rational + &other.rational,
            &self.radical + &other.radical,
            radicand,
        )
    }

    /// `self − other` in the shared field.
    pub fn sub(&self, other: &Self) -> Result<Self, LandmarkError> {
        self.add(&other.scaled(&-Rat::one()))
    }

    /// `self · other = (p₁p₂ + q₁q₂D) + (p₁q₂ + p₂q₁)√D`.
    pub fn mul(&self, other: &Self) -> Result<Self, LandmarkError> {
        let radicand = self.shared_radicand(other)?;
        Self::new(
            &self.rational * &other.rational + &self.radical * &other.radical * &radicand,
            &self.rational * &other.radical + &other.rational * &self.radical,
            radicand,
        )
    }

    /// `c · self` for a rational `c`.
    pub fn scaled(&self, factor: &Rat) -> Self {
        if factor.is_zero() {
            return Self::rational(Rat::zero());
        }
        Self {
            rational: &self.rational * factor,
            radical: &self.radical * factor,
            radicand: self.radicand.clone(),
        }
    }

    /// `self + c` for a rational `c`.
    pub fn shifted(&self, offset: &Rat) -> Self {
        Self {
            rational: &self.rational + offset,
            radical: self.radical.clone(),
            radicand: self.radicand.clone(),
        }
    }

    /// `1/self = conj/norm`; the norm vanishes only at zero, which is refused.
    pub fn inverse(&self) -> Result<Self, LandmarkError> {
        let norm = self.norm();
        if norm.is_zero() {
            return Err(LandmarkError::ZeroDivisor);
        }
        Ok(self.conjugate().scaled(&norm.recip()))
    }

    /// `self / other`.
    pub fn div(&self, other: &Self) -> Result<Self, LandmarkError> {
        self.mul(&other.inverse()?)
    }

    /// `selfⁿ`, by repeated squaring in the field.
    pub fn power(&self, exponent: u32) -> Result<Self, LandmarkError> {
        let mut result = Self::rational(Rat::one());
        let mut base = self.clone();
        let mut remaining = exponent;
        while remaining > 0 {
            if remaining & 1 == 1 {
                result = result.mul(&base)?;
            }
            base = base.mul(&base)?;
            remaining >>= 1;
        }
        Ok(result)
    }

    /// **The exact sign**, deciding `p + q√D` against zero without forming `√D`: equal signs (or a
    /// zero part) decide it at once, and otherwise `p²` against `q²D` does.
    pub fn signum(&self) -> Ordering {
        let rational = self.rational.cmp(&Rat::zero());
        let radical = self.radical.cmp(&Rat::zero());
        if radical == Ordering::Equal {
            return rational;
        }
        if rational == Ordering::Equal || rational == radical {
            return radical;
        }
        let rational_square = &self.rational * &self.rational;
        let radical_square = &self.radical * &self.radical * &self.radicand;
        match rational_square.cmp(&radical_square) {
            Ordering::Greater => rational,
            _ => radical,
        }
    }

    /// The exact order of two values of one field.
    pub fn compare(&self, other: &Self) -> Result<Ordering, LandmarkError> {
        Ok(self.sub(other)?.signum())
    }

    /// The exact order of the absolute values, by the sign of `self² − other²`.
    pub fn compare_magnitude(&self, other: &Self) -> Result<Ordering, LandmarkError> {
        Ok(self.mul(self)?.sub(&other.mul(other)?)?.signum())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    fn golden_square() -> QuadraticSurd {
        QuadraticSurd::new(rat(3, 2), rat(1, 2), integer(5)).unwrap()
    }

    /// A rational square folds, a negative radicand is refused, and `√(64/9)` is `8/3`.
    #[test]
    fn a_rational_square_radicand_folds() {
        assert_eq!(rational_square_root(&rat(64, 9)), Some(rat(8, 3)));
        assert_eq!(rational_square_root(&rat(5, 4)), None);
        assert_eq!(rational_square_root(&integer(-4)), None);
        assert_eq!(
            QuadraticSurd::new(integer(1), integer(2), rat(9, 4)).unwrap(),
            QuadraticSurd::rational(integer(4))
        );
        assert!(matches!(
            QuadraticSurd::new(integer(1), integer(1), integer(-2)),
            Err(LandmarkError::NegativeRadicand { .. })
        ));
    }

    /// `φ² = (3 + √5)/2` satisfies `x² − 3x + 1 = 0`, its norm is `1` and its conjugate is its
    /// inverse; field arithmetic never leaves `ℚ(√5)`.
    #[test]
    fn the_field_operations_keep_the_constraint() {
        let root = golden_square();
        let square = root.mul(&root).unwrap();
        let constraint = square
            .sub(&root.scaled(&integer(3)))
            .unwrap()
            .shifted(&integer(1));
        assert_eq!(constraint, QuadraticSurd::rational(integer(0)));
        assert_eq!(root.norm(), integer(1));
        assert_eq!(root.inverse().unwrap(), root.conjugate());
        assert_eq!(root.trace(), integer(3));
        assert_eq!(
            root.power(3).unwrap(),
            square.mul(&root).unwrap(),
            "repeated squaring agrees with the product"
        );
        let other = QuadraticSurd::new(integer(1), integer(1), integer(2)).unwrap();
        assert!(matches!(
            root.add(&other),
            Err(LandmarkError::RadicandMismatch { .. })
        ));
    }

    /// The sign is exact on both sides of a near cancellation: `3 − √8 > 0`, `3 − √10 < 0`, and
    /// `−3 + √10 > 0`.
    #[test]
    fn the_sign_is_decided_exactly() {
        let sign = |p: i64, q: i64, d: i64| {
            QuadraticSurd::new(integer(p), integer(q), integer(d))
                .unwrap()
                .signum()
        };
        assert_eq!(sign(3, -1, 8), Ordering::Greater);
        assert_eq!(sign(3, -1, 10), Ordering::Less);
        assert_eq!(sign(-3, 1, 10), Ordering::Greater);
        assert_eq!(sign(0, -1, 2), Ordering::Less);
        assert_eq!(sign(2, 1, 3), Ordering::Greater);
        assert_eq!(
            golden_square()
                .compare_magnitude(&golden_square().conjugate())
                .unwrap(),
            Ordering::Greater
        );
    }
}
