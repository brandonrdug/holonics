//! **One per two, undivided: a ratio carried as its presentation.**
//!
//! [definition] A ratio keeps its two comparands; `1/2` is one per two before it is a number
//! ([objects §9](../../../../docs/ELEMENTARY_OBJECTS.md#9-ratio)). A [`Presentation`] carries the
//! numerator and the denominator as a pair, compares by cross-multiplication, and yields a scalar
//! quotient only as a face, which does not exist when the denominator vanishes (the nonunit
//! fibre is kept instead of a reciprocal being invented).
//!
//! | Lean `Geometry/CrossRatio` | Rust |
//! |---|---|
//! | `RatioPresentation` | [`Presentation`] |
//! | `RatioPresentation.ProjectivelyEq` | [`Presentation::projectively_equal`] |
//! | `RatioPresentation.scale`, `ratioPresentation_projectivelyEq_scale` | [`Presentation::scaled`] |
//! | `RatioPresentation.blockTransport` (diagonal), `Holarchy/Receipt.followRatio`, `followRatio_eq` | [`Presentation::follow`] |

use num_traits::{Signed, Zero};

use crate::ratio::{ExactOrdering, Rat};

/// A numerator and a denominator, never divided.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Presentation {
    numerator: Rat,
    denominator: Rat,
}

impl Presentation {
    pub fn new(numerator: Rat, denominator: Rat) -> Self {
        Self {
            numerator,
            denominator,
        }
    }

    pub fn numerator(&self) -> &Rat {
        &self.numerator
    }

    pub fn denominator(&self) -> &Rat {
        &self.denominator
    }

    /// Both comparands scaled by one common factor: the same ratio, another presentation.
    pub fn scaled(&self, factor: &Rat) -> Self {
        Self::new(factor * &self.numerator, factor * &self.denominator)
    }

    /// [definition] **The ratio's own composition**: `self` followed by `next`, the diagonal block
    /// transport with `next`'s entries, `(n'·n : d'·d)` (`Holarchy/Receipt.followRatio_eq`). Both
    /// pairs stay undivided; a composite whose two entries vanish is the degenerate `(0 : 0)`, which
    /// [`Self::projectively_equal`] never promotes to equality.
    pub fn follow(&self, next: &Self) -> Self {
        Self::new(
            &next.numerator * &self.numerator,
            &next.denominator * &self.denominator,
        )
    }

    /// Whether both comparands vanish: the pair `(0 : 0)`, which names no point.
    pub fn is_degenerate(&self) -> bool {
        self.numerator.is_zero() && self.denominator.is_zero()
    }

    /// `p.num · q.den = q.num · p.den`: equality in the projective line, decided without
    /// division. The degenerate pair `(0, 0)` names no point and is equal to nothing.
    pub fn projectively_equal(&self, other: &Self) -> bool {
        !self.is_degenerate()
            && !other.is_degenerate()
            && &self.numerator * &other.denominator == &other.numerator * &self.denominator
    }

    /// The order of two ratios by cross-multiplication, reading each denominator's sign first.
    /// A vanishing denominator has no place on the finite line, so the comparison is `Open`.
    pub fn compare(&self, other: &Self) -> ExactOrdering {
        if self.denominator.is_zero() || other.denominator.is_zero() {
            return ExactOrdering::Open;
        }
        let left = &self.numerator * &other.denominator;
        let right = &other.numerator * &self.denominator;
        let flipped = self.denominator.is_negative() ^ other.denominator.is_negative();
        let order = left.cmp(&right);
        ExactOrdering::from(if flipped { order.reverse() } else { order })
    }

    /// The scalar face, when the denominator is a unit of ℚ.
    pub fn quotient(&self) -> Option<Rat> {
        (!self.denominator.is_zero()).then(|| &self.numerator / &self.denominator)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    /// Scaling both comparands leaves the ratio projectively fixed; cross-multiplication orders
    /// presentations through negative denominators, and a zero denominator keeps its fibre.
    #[test]
    fn a_presentation_is_its_ratio_under_scaling_and_orders_without_division() {
        let half = Presentation::new(integer(1), integer(2));
        assert!(half.scaled(&rat(-3, 7)).projectively_equal(&half));
        let third = Presentation::new(integer(-1), integer(-3));
        assert_eq!(half.compare(&third), ExactOrdering::Greater);
        assert_eq!(third.compare(&half), ExactOrdering::Less);
        let pole = Presentation::new(integer(1), integer(0));
        assert_eq!(pole.quotient(), None);
        assert_eq!(pole.compare(&half), ExactOrdering::Open);
        assert!(!Presentation::new(integer(0), integer(0)).projectively_equal(&half));
    }
}
