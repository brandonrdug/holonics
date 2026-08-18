//! **The contact between two constructions, as an exact ratio that crosses a horizon.**
//!
//! A bracket `<a|b>` is a magnitude and does not cross a frame boundary. The **squared cosine**
//!
//! ```text
//!     cos²(a,b)  =  <a|b>² / (<a|a> <b|b>)
//! ```
//!
//! does, and the reason is arithmetic rather than declared. Where a construction enters as exact
//! integers over a common power of two — which is what
//! [`crate::embedding_fiber::align_bfloat16`] returns and what the declared IEEE mouth admits — the
//! dyadic frame appears as `2^{2(e_a+e_b)}` in the numerator and as `2^{2e_a}·2^{2e_b}` in the
//! denominator, and **cancels identically**. This module computes that exponent difference rather
//! than asserting it, and refuses a contact whose frames did not cancel to exactly zero.
//!
//! **Nothing here is divided.** The face is carried as the pair `(numerator, denominator)` and
//! ordered by cross-multiplication through [`crate::exact_value::ExactOrdering`], so the four-state
//! ordering with `Open` survives and no epsilon is ever reached for.
//!
//! **The quotient by the phase circle deletes the hand, so the hand is carried beside it.** `cos²`
//! is `|·|²`, and squaring sends `θ` and `θ+π` to one place. A contact that returned only the
//! squared face would have committed exactly the deletion this corpus refuses everywhere else, so
//! [`ExactContact::hand`] returns the [`Aim`] the square erased.
//!
//! **The two faces close.** By Lagrange's identity — which holds in **every** diagonal signature by
//! Cauchy–Binet, and whose Euclidean-only restriction was a defect repaired in [`crate::clifford`] —
//!
//! ```text
//!     <a|b>²  +  ‖a ∧ b‖²  =  <a|a> <b|b>
//! ```
//!
//! so the cohere face and the turn face are two numerators over **one** denominator and they sum to
//! it exactly. That is the Pythagorean statement as an exact integer identity over real material,
//! and [`ExactContact::closes`] checks it rather than trusting it.
//!
//! **This module implements no bracket of its own.** It is a join: [`ExactContact::of_arrow`] takes
//! the spans and the aim a [`crate::clifford::Arrow`] already computed under a **declared**
//! signature, and [`ExactContact::of_brackets`] takes the three integers a resident readout already
//! computed on the card, for the case where materialising `d(d−1)/2` blade coordinates at map width
//! would be absurd. Neither entry point assumes a metric; both consume one a caller declared.

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use thiserror::Error;

use crate::clifford::{Aim, Arrow};
use crate::exact_value::ExactOrdering;

/// Why a contact could not be read.
///
/// **`NullTraversal` is not an input error.** A construction whose span is zero returns nothing when
/// traversed — in a definite signature that is the zero construction, and in an indefinite one it is
/// the null cone, which is a real place with real inhabitants. The refusal names which side it was
/// and carries the other side's span, because a contact against a null construction has no squared
/// cosine and reporting one would manufacture a direction where the traversal has none.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ContactError {
    #[error(
        "the {side} construction's span is zero: its traversal returns nothing, so no squared \
         cosine exists against it (the other span is {other_span})"
    )]
    NullTraversal { side: Side, other_span: BigInt },
    #[error(
        "the dyadic frames did not cancel: the numerator carries 2^{numerator_exponent} and the \
         denominator carries 2^{denominator_exponent}, a residual of {residual}"
    )]
    FrameSurvived {
        numerator_exponent: i64,
        denominator_exponent: i64,
        residual: i64,
    },
    #[error("a span is not an integer multiple of one: {which} is {value}")]
    NotIntegral { which: &'static str, value: Rat },
}

/// Which side of a contact a refusal is about. Named, never an index.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Side {
    Left,
    Right,
}

impl std::fmt::Display for Side {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Left => write!(f, "left"),
            Self::Right => write!(f, "right"),
        }
    }
}

/// **One face of a contact, carried as a pair and never divided.**
///
/// The denominator is the contact's shared span product and is the same for both faces, which is
/// what makes them addable. A caller that wants a decimal has left the carrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RatioFace {
    pub numerator: BigInt,
    pub denominator: BigInt,
}

impl RatioFace {
    /// Compare two faces **by cross-multiplication**, with no division anywhere.
    ///
    /// The denominators' hands are read first and the comparison flipped where a denominator is
    /// negative — which happens off the definite signatures and is not an error. A zero denominator
    /// cannot occur here because [`ExactContact::read`] refuses it at construction, and if one is
    /// somehow presented the ordering returns `Open` rather than inventing a relation.
    pub fn compare(&self, other: &Self) -> ExactOrdering {
        if self.denominator.is_zero() || other.denominator.is_zero() {
            return ExactOrdering::Open;
        }
        let left = &self.numerator * &other.denominator;
        let right = &other.numerator * &self.denominator;
        let hands = self.denominator.is_negative() ^ other.denominator.is_negative();
        let raw = left.cmp(&right);
        let oriented = if hands { raw.reverse() } else { raw };
        ExactOrdering::from(oriented)
    }

    /// The face as an exact rational, for a caller composing it with other exact material.
    ///
    /// **This is not a division into a decimal** — `Rat` carries the pair — but it does discard the
    /// particular numerator and denominator by reducing them, so a caller comparing populations
    /// should use [`RatioFace::compare`] and keep the pair.
    pub fn as_rational(&self) -> Rat {
        Rat::new(self.numerator.clone(), self.denominator.clone())
    }
}

/// **A contact read exactly, with its frame cancelled and its hand retained.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactContact {
    aim: BigInt,
    left_span: BigInt,
    right_span: BigInt,
    /// `2^{this}` was the frame the numerator carried before cancellation, as an integer count of
    /// octaves. Retained so a reading can say what it crossed, never used in the ratio.
    numerator_exponent: i64,
    denominator_exponent: i64,
}

impl ExactContact {
    /// Read a contact from three brackets already computed under a declared metric.
    ///
    /// `left_exponent` and `right_exponent` are the common powers of two the two constructions were
    /// aligned onto, exactly as [`crate::embedding_fiber::AlignedMaterial::exponent`] reports them.
    /// Pass `0` for both where the material is already integral.
    pub fn of_brackets(
        aim: BigInt,
        left_span: BigInt,
        right_span: BigInt,
        left_exponent: i32,
        right_exponent: i32,
    ) -> Result<Self, ContactError> {
        // <a|b> carries 2^(e_a + e_b); squaring it carries twice that.
        let numerator_exponent = 2 * (i64::from(left_exponent) + i64::from(right_exponent));
        // <a|a> carries 2^(2 e_a) and <b|b> carries 2^(2 e_b); their product carries the sum.
        let denominator_exponent = 2 * i64::from(left_exponent) + 2 * i64::from(right_exponent);
        Self::read(
            aim,
            left_span,
            right_span,
            numerator_exponent,
            denominator_exponent,
        )
    }

    /// Read a contact from an [`Arrow`], which already carries the **declared** signature.
    ///
    /// This is the join the blueprint's chain calls for: the arrow owns the metric, the blade and
    /// the aim; this owns the horizon-crossing face. The arrow's spans must be integral, which they
    /// are for any material entering through the dyadic mouth, and the refusal names the offender
    /// rather than rounding.
    pub fn of_arrow(arrow: &Arrow) -> Result<Self, ContactError> {
        let integral = |value: &Rat, which: &'static str| -> Result<BigInt, ContactError> {
            if value.denom() != &BigInt::from(1) {
                return Err(ContactError::NotIntegral {
                    which,
                    value: value.clone(),
                });
            }
            Ok(value.numer().clone())
        };
        let aim = integral(arrow.aim(), "the aim")?;
        let left_span = integral(arrow.left_span(), "the left span")?;
        let right_span = integral(arrow.right_span(), "the right span")?;
        Self::read(aim, left_span, right_span, 0, 0)
    }

    fn read(
        aim: BigInt,
        left_span: BigInt,
        right_span: BigInt,
        numerator_exponent: i64,
        denominator_exponent: i64,
    ) -> Result<Self, ContactError> {
        if left_span.is_zero() {
            return Err(ContactError::NullTraversal {
                side: Side::Left,
                other_span: right_span,
            });
        }
        if right_span.is_zero() {
            return Err(ContactError::NullTraversal {
                side: Side::Right,
                other_span: left_span,
            });
        }
        let residual = numerator_exponent - denominator_exponent;
        if residual != 0 {
            return Err(ContactError::FrameSurvived {
                numerator_exponent,
                denominator_exponent,
                residual,
            });
        }
        Ok(Self {
            aim,
            left_span,
            right_span,
            numerator_exponent,
            denominator_exponent,
        })
    }

    /// The shared denominator both faces are carried over: `<a|a> <b|b>`.
    pub fn span_product(&self) -> BigInt {
        &self.left_span * &self.right_span
    }

    /// **The cohere face** — `<a|b>² / (<a|a> <b|b>)`, the squared cosine, undivided.
    pub fn cohere_square(&self) -> RatioFace {
        RatioFace {
            numerator: &self.aim * &self.aim,
            denominator: self.span_product(),
        }
    }

    /// **The turn face** — `‖a ∧ b‖² / (<a|a> <b|b>)`, the squared sine, undivided.
    ///
    /// Its numerator is Lagrange's identity, which is why [`ExactContact::closes`] is an identity
    /// rather than a measurement.
    pub fn turn_square(&self) -> RatioFace {
        RatioFace {
            numerator: self.span_product() - &self.aim * &self.aim,
            denominator: self.span_product(),
        }
    }

    /// **The hand the square deleted.** `cos²` is the quotient by the phase circle and sends `θ` and
    /// `θ+π` to one place; this is what that quotient collapsed.
    ///
    /// `Ortho` is not nothing — it is the founding hand, the case where the cohere face is exactly
    /// zero and the whole contact sits in the turn face.
    pub fn hand(&self) -> Aim {
        if self.aim.is_zero() {
            Aim::Ortho
        } else if self.aim.is_negative() {
            Aim::Anti
        } else {
            Aim::Cohere
        }
    }

    /// The aim itself, exact and undivided. **A logit is this alone** — the in-span, absorbable part
    /// of a contact, with the turn and the hand discarded.
    pub const fn aim(&self) -> &BigInt {
        &self.aim
    }

    pub const fn left_span(&self) -> &BigInt {
        &self.left_span
    }

    pub const fn right_span(&self) -> &BigInt {
        &self.right_span
    }

    /// **Does the contact close?** `<a|b>² + ‖a∧b‖² = <a|a><b|b>`, exactly, as integers.
    ///
    /// This is checked rather than trusted, and it is the whole reason the two faces may be reported
    /// over one denominator.
    pub fn closes(&self) -> bool {
        let cohere = self.cohere_square();
        let turn = self.turn_square();
        cohere.numerator + turn.numerator == self.span_product()
    }

    /// The frame that cancelled, retained so a reading can name what it crossed.
    ///
    /// Both are octave counts and the pair is always equal by construction, because a contact whose
    /// frames did not cancel is refused at [`ExactContact::read`]. A reading that wants to say *the
    /// dyadic exponent crossed with residual zero* takes it from here rather than asserting it.
    pub const fn cancelled_frame(&self) -> (i64, i64) {
        (self.numerator_exponent, self.denominator_exponent)
    }

    /// Compare two contacts by their cohere face, with no division.
    ///
    /// **This orders; it does not select.** Nothing here returns a maximum, and `Open` is a genuine
    /// fourth state rather than a tie broken by convention.
    pub fn compare_cohere(&self, other: &Self) -> ExactOrdering {
        self.cohere_square().compare(&other.cohere_square())
    }
}

/// Verify a contact's turn face against the blade's own coordinates.
///
/// **This is the two-frame check.** The turn numerator comes from Lagrange; the arrow's
/// [`Arrow::area_squared`] computes the same quantity a second way, from the blade coordinates
/// weighted by the declared metric. Agreement is evidence the metric was carried on both sides; a
/// disagreement exhibits the arrow rather than widening anything.
pub fn turn_agrees_with_blade(arrow: &Arrow, contact: &ExactContact) -> Option<(Rat, Rat)> {
    let area = arrow.area_squared();
    let from_blade = area.value;
    let from_lagrange = Rat::from_integer(contact.turn_square().numerator);
    if from_blade == from_lagrange {
        None
    } else {
        Some((from_blade, from_lagrange))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clifford::Signature;

    fn euclidean(axes: usize) -> Signature {
        Signature::euclidean(axes)
    }

    fn rats(values: &[i64]) -> Vec<Rat> {
        values.iter().map(|v| Rat::from_integer((*v).into())).collect()
    }

    #[test]
    fn the_dyadic_frame_cancels_identically_and_the_residual_is_exhibited() {
        // Two constructions aligned onto wildly different powers of two. The face must not move.
        let contact_low =
            ExactContact::of_brackets(11.into(), 5.into(), 29.into(), 0, 0).expect("reads");
        let contact_high =
            ExactContact::of_brackets(11.into(), 5.into(), 29.into(), -40, 17).expect("reads");
        assert_eq!(contact_low.cohere_square(), contact_high.cohere_square());
        assert_eq!(contact_low.turn_square(), contact_high.turn_square());
        let (numerator, denominator) = contact_high.cancelled_frame();
        assert_eq!(numerator, denominator, "the frames must cancel exactly");
        assert_eq!(numerator - denominator, 0);
    }

    #[test]
    fn the_two_faces_close_over_one_denominator() {
        for (aim, left, right) in [(3i64, 5i64, 29i64), (-7, 13, 41), (0, 2, 3), (6, 4, 9)] {
            let contact =
                ExactContact::of_brackets(aim.into(), left.into(), right.into(), 0, 0).expect("reads");
            assert!(contact.closes(), "cos² + sin² must be exactly 1 at {aim}");
            let cohere = contact.cohere_square();
            let turn = contact.turn_square();
            assert_eq!(cohere.denominator, turn.denominator);
            assert_eq!(cohere.numerator + turn.numerator, contact.span_product());
        }
    }

    #[test]
    fn the_square_deletes_the_hand_and_the_hand_is_returned_beside_it() {
        let cohering = ExactContact::of_brackets(7.into(), 5.into(), 29.into(), 0, 0).expect("reads");
        let anti = ExactContact::of_brackets((-7).into(), 5.into(), 29.into(), 0, 0).expect("reads");
        // The squared face cannot tell them apart -- that is the quotient by the phase circle.
        assert_eq!(cohering.cohere_square(), anti.cohere_square());
        // And the hand is what the quotient collapsed.
        assert_eq!(cohering.hand(), Aim::Cohere);
        assert_eq!(anti.hand(), Aim::Anti);
        assert_ne!(cohering.aim(), anti.aim());
    }

    #[test]
    fn a_null_traversal_refuses_rather_than_returning_a_direction() {
        let refused = ExactContact::of_brackets(0.into(), 0.into(), 29.into(), 0, 0);
        assert!(matches!(
            refused,
            Err(ContactError::NullTraversal {
                side: Side::Left,
                ..
            })
        ));
        let refused_right = ExactContact::of_brackets(0.into(), 5.into(), 0.into(), 0, 0);
        assert!(matches!(
            refused_right,
            Err(ContactError::NullTraversal {
                side: Side::Right,
                ..
            })
        ));
    }

    #[test]
    fn ordering_is_by_cross_multiplication_and_never_divides() {
        // 1/3 against 2/5: 1*5 = 5 < 2*3 = 6.
        let smaller = RatioFace {
            numerator: 1.into(),
            denominator: 3.into(),
        };
        let larger = RatioFace {
            numerator: 2.into(),
            denominator: 5.into(),
        };
        assert_eq!(smaller.compare(&larger), ExactOrdering::Less);
        assert_eq!(larger.compare(&smaller), ExactOrdering::Greater);
        assert_eq!(smaller.compare(&smaller), ExactOrdering::Equal);
        // A negative denominator flips the reading and is not an error.
        let flipped = RatioFace {
            numerator: (-1).into(),
            denominator: (-3).into(),
        };
        assert_eq!(flipped.compare(&larger), ExactOrdering::Less);
    }

    #[test]
    fn the_contact_joins_the_arrow_and_the_turn_agrees_with_the_blade() {
        let signature = euclidean(3);
        let left = rats(&[2, 1, 0]);
        let right = rats(&[1, 3, 1]);
        let arrow = Arrow::between(&signature, &left, &right).expect("arrow");
        let contact = ExactContact::of_arrow(&arrow).expect("contact");
        assert!(contact.closes());
        assert_eq!(
            turn_agrees_with_blade(&arrow, &contact),
            None,
            "Lagrange and the metric-weighted blade must agree"
        );
    }

    #[test]
    fn the_join_holds_off_euclidean_where_the_repaired_blade_carries_the_metric() {
        // Minkowski: the signature whose metric the blade dropped until 2026-08-18.
        let signature = Signature::declared(rats(&[-1, 1, 1]));
        let left = rats(&[2, 1, 0]);
        let right = rats(&[2, 0, 1]);
        let arrow = Arrow::between(&signature, &left, &right).expect("arrow");
        let contact = ExactContact::of_arrow(&arrow).expect("contact");
        assert_eq!(
            turn_agrees_with_blade(&arrow, &contact),
            None,
            "Cauchy-Binet holds in every diagonal signature"
        );
        assert!(contact.closes());
        // And the indefinite signature speaks through the faces rather than through a failure:
        // both spans are negative, so the shared denominator is positive while the TURN face is
        // NEGATIVE and the cohere face exceeds one. The identity still closes exactly. A definite
        // signature is a special case here, not the meaning of the symbol.
        assert_eq!(contact.left_span(), &BigInt::from(-3));
        assert_eq!(contact.right_span(), &BigInt::from(-3));
        assert_eq!(contact.span_product(), BigInt::from(9));
        assert_eq!(contact.cohere_square().numerator, BigInt::from(16));
        assert_eq!(contact.turn_square().numerator, BigInt::from(-7));
        assert_eq!(contact.hand(), Aim::Anti);
    }

    #[test]
    fn the_modules_own_minkowski_fixture_is_two_null_traversals_and_the_contact_refuses() {
        // `a = (1,1,0)` and `b = (1,0,1)` under `q = (-1,1,1)` are BOTH on the null cone: the span
        // is `-1 + 1 = 0` for each. This is not degenerate input, it is the light cone, and a
        // squared cosine against a construction whose traversal returns nothing does not exist.
        // The refusal names the side and hands back the other span rather than reporting a
        // direction the geometry does not have.
        let signature = Signature::declared(rats(&[-1, 1, 1]));
        let arrow = Arrow::between(&signature, &rats(&[1, 1, 0]), &rats(&[1, 0, 1])).expect("arrow");
        assert!(arrow.left_span().is_zero() && arrow.right_span().is_zero());
        assert!(matches!(
            ExactContact::of_arrow(&arrow),
            Err(ContactError::NullTraversal {
                side: Side::Left,
                ..
            })
        ));
    }
}
