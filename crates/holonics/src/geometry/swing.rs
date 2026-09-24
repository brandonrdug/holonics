//! **The Swing: the primitive act of situated relating and transport.**
//!
//! [proved-derived; formal-checked] A body swings past an anchor on a board every motion leaves
//! invariant ([objects §3](../../../../docs/ELEMENTARY_OBJECTS.md#the-swing-the-navigators-elementary-motion)).
//! Projectively the Swing is harmonic conjugation, `(A, A′; B, D) = −1` with anchor `B` and board
//! `D`; in the chart sending the anchor to `0` and the board to `∞` it is negation. Freezing the
//! board at infinity leaves the affine chart, the point reflection `S_a x = 2a − x`, a half-turn
//! `e^{iπ}` about the anchor:
//!
//! ```text
//! S_a x − a = −(x − a),   S_a S_a = 1,   S_a a = a
//! S_b S_a x = x + 2(b − a)                 two Swings compose to a translation
//! S_b S_a − S_a S_b = 4(b − a)             and do not commute
//! Q − O = s (P − O)                        the pantograph about O; its scale −1 is the Swing
//! ```
//!
//! The cross ratio is carried as its undivided [`Presentation`] (`swingPair`), so a vanishing
//! denominator is a named fibre rather than an invented infinity.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Geometry/AffineSwing.swing`, `theSwingNegatesTheDisplacementFromTheAnchor`, `theSwingIsAnInvolution`, `theAnchorIsFixed` | [`swing`] |
//! | `Geometry/AffineSwing.twoSwingsAreADoubledTranslation`, `theSwingsDoNotCommute` | [`composed_translation`] |
//! | `Millennium/HolonicPantographicSwingJets.pantographicPoint`, `pantographicPoint_neg_one_eq_swing` | [`pantograph`] |
//! | `Millennium/Swing.constraintChart`, `harmonicConjugate`, `theSwingIsNegationInTheConstraintChart` | [`constraint_chart`], [`harmonic_conjugate`] |
//! | `Geometry/CrossRatio.swingPair`, `crossRatio`, `swingPair_affine_projectively` | [`swing_pair`] |

use num_traits::Zero;

use crate::geometry::RatVec3;
use crate::ratio::{Presentation, Rat, integer};

/// **The Swing** `S_a x = 2a − x`: the half-turn of `x` about the anchor `a`.
pub fn swing(anchor: &RatVec3, body: &RatVec3) -> RatVec3 {
    anchor.scale(&integer(2)).subtract(body)
}

/// The translation two Swings compose to: `S_second ∘ S_first` moves every point by
/// `2(second − first)`.
pub fn composed_translation(first: &RatVec3, second: &RatVec3) -> RatVec3 {
    second.subtract(first).scale(&integer(2))
}

/// **The pantograph** `O + s (P − O)`: scaling about the anchor `O`. Serial passages multiply
/// their scales, and the scale `−1` is the Swing.
pub fn pantograph(anchor: &RatVec3, scale: &Rat, input: &RatVec3) -> RatVec3 {
    anchor.add(&input.subtract(anchor).scale(scale))
}

/// The chart the anchor `b` and the board `d` declare on a line: `x ↦ (x − b)/(x − d)`, sending
/// the anchor to `0` and the board to `∞`. Carried as its presentation.
pub fn constraint_chart(anchor: &Rat, board: &Rat, x: &Rat) -> Presentation {
    Presentation::new(x - anchor, x - board)
}

/// **The projective Swing**: the harmonic conjugate of `a` with respect to the anchor `b` and the
/// board `d`, `((a − b) d + (a − d) b) / (2a − b − d)`. `None` when `a` is the midpoint of anchor
/// and board, whose conjugate is the board's point at infinity.
pub fn harmonic_conjugate(anchor: &Rat, board: &Rat, a: &Rat) -> Option<Rat> {
    let denominator = integer(2) * a - anchor - board;
    if denominator.is_zero() {
        return None;
    }
    Some(((a - anchor) * board + (a - board) * anchor) / denominator)
}

/// **The Swing pair** `((c − a)(d − b), (c − b)(d − a))`: the cross ratio of four marks on a line,
/// undivided. An affine change of coordinates scales both comparands by one square, so the pair
/// is projectively invariant.
pub fn swing_pair(a: &Rat, b: &Rat, c: &Rat, d: &Rat) -> Presentation {
    Presentation::new((c - a) * (d - b), (c - b) * (d - a))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::rat;

    fn point(x: i64, y: i64, z: i64) -> RatVec3 {
        RatVec3::from_i64(x, y, z)
    }

    /// Lean `Geometry/AffineSwing`: the Swing negates displacement from its anchor, is an
    /// involution fixing the anchor, two Swings compose to the doubled translation, and they do
    /// not commute (`S_b S_a − S_a S_b = 4(b − a)`).
    #[test]
    fn the_swing_is_a_half_turn_and_two_swings_are_a_translation() {
        let (a, b, x) = (point(1, 2, 0), point(-3, 5, 7), point(4, -1, 2));
        assert_eq!(
            swing(&a, &x).subtract(&a),
            x.subtract(&a).scale(&integer(-1))
        );
        assert_eq!(swing(&a, &swing(&a, &x)), x);
        assert_eq!(swing(&a, &a), a);
        let ba = swing(&b, &swing(&a, &x));
        assert_eq!(ba, x.add(&composed_translation(&a, &b)));
        let ab = swing(&a, &swing(&b, &x));
        assert_eq!(ba.subtract(&ab), b.subtract(&a).scale(&integer(4)));
    }

    /// Lean `pantographicPoint_neg_one_eq_swing` and composition: scale `−1` is the Swing, and two
    /// pantographs about one anchor multiply their scales.
    #[test]
    fn the_pantograph_at_minus_one_is_the_swing_and_scales_multiply() {
        let (anchor, input) = (point(2, 0, -1), point(5, 3, 3));
        assert_eq!(
            pantograph(&anchor, &integer(-1), &input),
            swing(&anchor, &input)
        );
        let (s, t) = (rat(2, 3), rat(-5, 2));
        assert_eq!(
            pantograph(&anchor, &t, &pantograph(&anchor, &s, &input)),
            pantograph(&anchor, &(&s * &t), &input)
        );
    }

    /// Lean `Millennium/Swing.theSwingIsNegationInTheConstraintChart`: in the chart sending the
    /// anchor to `0` and the board to `∞`, the harmonic conjugate is negation, and its cross ratio
    /// with anchor and board is `−1`.
    #[test]
    fn the_projective_swing_is_negation_in_the_constraint_chart() {
        let (anchor, board, a) = (rat(1, 2), integer(3), rat(-4, 5));
        let conjugate = harmonic_conjugate(&anchor, &board, &a).expect("not the midpoint");
        let chart = constraint_chart(&anchor, &board, &a).quotient().unwrap();
        let swung = constraint_chart(&anchor, &board, &conjugate)
            .quotient()
            .unwrap();
        assert_eq!(swung, -chart);
        assert_eq!(
            swing_pair(&a, &conjugate, &anchor, &board).quotient(),
            Some(integer(-1))
        );
        let midpoint = (&anchor + &board) / integer(2);
        assert_eq!(harmonic_conjugate(&anchor, &board, &midpoint), None);
    }

    /// Lean `Geometry/CrossRatio.swingPair_affine_projectively`: an affine change of the line
    /// scales both comparands of the Swing pair by one square.
    #[test]
    fn the_swing_pair_is_invariant_under_affine_charts() {
        let marks = [integer(0), integer(1), rat(3, 2), integer(-4)];
        let (u, v) = (rat(-7, 3), integer(5));
        let moved: Vec<Rat> = marks.iter().map(|m| &u * m + &v).collect();
        let before = swing_pair(&marks[0], &marks[1], &marks[2], &marks[3]);
        let after = swing_pair(&moved[0], &moved[1], &moved[2], &moved[3]);
        assert_eq!(after, before.scaled(&(&u * &u)));
        assert!(after.projectively_equal(&before));
    }
}
