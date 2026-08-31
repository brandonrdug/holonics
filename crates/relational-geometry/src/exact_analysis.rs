//! Rational enclosures for receiver-relative complex analysis.

use crate::exact::{Rat, format_rat, integer, rat, ratio};
use num_bigint::{BigInt, Sign};
use num_traits::{One, Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use std::cmp::{max, min};
use std::fmt;
use thiserror::Error;

mod chains;
mod complex;
mod constants;
mod elementary;
mod special;
mod types;
mod winding;

pub use chains::*;
pub use complex::*;
pub use constants::*;
pub use elementary::*;
pub use special::*;
pub use types::*;
pub use winding::*;

pub(super) use elementary::negative_complex_power;
pub(super) use special::bernoulli_number;
pub(super) use types::{dyadic_ceil, factorial};
#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::rat;

    #[test]
    fn interval_arithmetic_retains_order_and_excludes_false_zero() {
        let left = RatInterval::new(rat(1, 3), rat(1, 2));
        let right = RatInterval::new(rat(2, 3), rat(3, 4));
        assert_eq!(left.add(&right), RatInterval::new(rat(1, 1), rat(5, 4)));
        assert_eq!(
            left.multiply(&right),
            RatInterval::new(rat(2, 9), rat(3, 8))
        );
        assert!(!left.contains_zero());
    }

    #[test]
    fn rational_transcendental_series_enclose_elementary_identities() {
        let log_two = log_rational_interval(&integer(2), 32, 128).unwrap();
        let exp_log_two = exp_interval(&log_two, 24, 128);
        assert!(exp_log_two.lower < integer(2));
        assert!(exp_log_two.upper > integer(2));

        let (sine, cosine) = sin_cos_rational_interval(&Rat::zero(), 12, 128);
        assert!(sine.lower <= Rat::zero() && sine.upper >= Rat::zero());
        assert!(cosine.lower <= Rat::one() && cosine.upper >= Rat::one());
    }

    #[test]
    fn eta_two_overlaps_pi_squared_over_twelve_without_float() {
        let config = ExactSeriesConfig {
            euler_maclaurin_start: 12,
            euler_maclaurin_order: 8,
            ..ExactSeriesConfig::default()
        };
        let eta = eta_evaluate(&ComplexReceiverBox::point(integer(2), Rat::zero()), &config)
            .unwrap()
            .value;

        // Machin: pi = 16 atan(1/5) - 4 atan(1/239).
        fn atan(value: Rat, terms: u32) -> RatInterval {
            let mut partial = Rat::zero();
            let mut power = value.clone();
            let square = &value * &value;
            for index in 0..terms {
                let signed = if index % 2 == 0 {
                    power.clone()
                } else {
                    -power.clone()
                };
                partial += signed / integer(i64::from(2 * index + 1));
                power *= &square;
            }
            let next = power / integer(i64::from(2 * terms + 1));
            RatInterval::new(
                min(partial.clone(), &partial - &next),
                max(partial.clone(), partial + next),
            )
        }
        let fifth = atan(rat(1, 5), 18);
        let two_hundred_thirty_ninth = atan(rat(1, 239), 6);
        let pi = fifth
            .scale(&integer(16))
            .subtract(&two_hundred_thirty_ninth.scale(&integer(4)));
        let expected = pi.square().scale(&rat(1, 12));
        assert!(eta.re.lower <= expected.upper && expected.lower <= eta.re.upper);
        assert!(eta.im.contains_zero());
    }

    fn corner(re: i64, im: i64) -> RatComplex {
        RatComplex::new(integer(re), integer(im))
    }

    /// Three boundaries, three distinct returns, and the middle one is invisible to a net winding.
    ///
    /// The declared control for `RayCrossings`. Until 2026-08-08 `polygon_winding` accumulated
    /// `+= 1` / `-= 1` into an `i32` and deposited no crossing, so the first two rows below were
    /// one return. `winding == 0` was doing two jobs — *the image never approached the ray* and
    /// *the image crossed it and came back* — and the η-zero bisection discards a half on exactly
    /// that predicate. Discarding is right in both cases by the argument principle; they are not
    /// the same evidence about where the boundary is doing work.
    #[test]
    fn a_boundary_that_crosses_the_ray_and_encloses_nothing_is_not_a_boundary_that_never_met_it() {
        // Entirely in the upper half plane: the ray is never crossed.
        let (away, _) = polygon_winding(&[corner(1, 1), corner(3, 1), corner(3, 2), corner(1, 2)])
            .expect("an admissible ray");
        assert_eq!(away.total(), 0);
        assert_eq!(away.winding(), 0);
        assert!(!away.cancels());

        // To the right of the origin, straddling the axis: crossed once each hand, encloses nothing.
        let (straddling, _) =
            polygon_winding(&[corner(2, 1), corner(2, -1), corner(3, -1), corner(3, 1)])
                .expect("an admissible ray");
        assert_eq!(
            straddling.winding(),
            0,
            "it encloses nothing and must say so"
        );
        assert_eq!(
            straddling.total(),
            2,
            "and it met the ray twice getting there"
        );
        assert!(straddling.cancels());
        assert_eq!(straddling.with_the_turn.len(), 1);
        assert_eq!(straddling.against_the_turn.len(), 1);
        assert_ne!(
            straddling.with_the_turn, straddling.against_the_turn,
            "the two hands are at different places on the boundary and the receipt says where"
        );

        // Around the origin: one crossing, one turn.
        let (enclosing, _) =
            polygon_winding(&[corner(1, -1), corner(1, 1), corner(-1, 1), corner(-1, -1)])
                .expect("an admissible ray");
        assert_eq!(enclosing.winding(), 1);
        assert_eq!(enclosing.total(), 1);
        assert!(!enclosing.cancels());

        // The property under test genuinely varies across the declared material: a check whose
        // fixtures cannot separate the two readings would be the trivial-orbit defect.
        assert_eq!(
            [away.winding(), straddling.winding(), enclosing.winding()],
            [0, 0, 1]
        );
        assert_eq!(
            [away.total(), straddling.total(), enclosing.total()],
            [0, 2, 1]
        );
    }

    /// Reversing a boundary swaps the hands and negates the winding, and moves nothing else.
    #[test]
    fn the_two_hands_swap_under_reversal_while_the_crossing_population_does_not() {
        let forward = [corner(1, -1), corner(1, 1), corner(-1, 1), corner(-1, -1)];
        let mut backward = forward.to_vec();
        backward.reverse();

        let (ahead, _) = polygon_winding(&forward).expect("an admissible ray");
        let (behind, _) = polygon_winding(&backward).expect("an admissible ray");

        assert_eq!(ahead.winding(), -behind.winding());
        assert_eq!(
            ahead.total(),
            behind.total(),
            "the same passages, the other way"
        );
        assert_eq!(ahead.with_the_turn.len(), behind.against_the_turn.len());
        assert_eq!(ahead.against_the_turn.len(), behind.with_the_turn.len());
    }

    fn probe_config() -> ExactSeriesConfig {
        ExactSeriesConfig {
            dyadic_bits: 96,
            euler_maclaurin_start: 12,
            euler_maclaurin_order: 10,
            log_terms: 28,
            exponential_terms: 18,
            trigonometric_terms: 16,
        }
    }

    fn probe_point() -> ComplexReceiverBox {
        ComplexReceiverBox::point(rat(1, 2), rat(14, 1))
    }

    /// The chain must reproduce the value the plain evaluator returns. If the
    /// decomposition drifted from `zeta_euler_maclaurin` this fires.
    #[test]
    fn the_chain_returns_the_same_eta_as_the_plain_evaluation() {
        let config = probe_config();
        let point = probe_point();
        let chain = eta_chain_decomposition(&point, &config).expect("the chain");
        let plain = eta_evaluate(&point, &config).expect("the plain evaluation");
        assert_eq!(chain.eta, plain.value);
        assert_eq!(chain.head.len() as u32, config.euler_maclaurin_start - 1);
        assert_eq!(chain.crossings.len() as u32, config.euler_maclaurin_order);
    }

    /// The odd-index Bernoulli numbers vanish, so every crossing this chain carries
    /// has ODD order. That is a parity selection rule: it decides which terms exist
    /// before any magnitude is computed.
    #[test]
    fn every_euler_maclaurin_crossing_has_odd_order_and_an_alternating_hand() {
        let chain = eta_chain_decomposition(&probe_point(), &probe_config()).expect("the chain");
        let mut expected_hand = 1;
        for crossing in &chain.crossings {
            assert_eq!(
                crossing.crossing_order % 2,
                1,
                "crossing order {} is even",
                crossing.crossing_order
            );
            assert!(!crossing.bernoulli.numer().is_zero());
            assert_eq!(
                crossing.hand, expected_hand,
                "the hand did not alternate at order {}",
                crossing.crossing_order
            );
            expected_hand = -expected_hand;
        }
    }

    /// Every head term carries its address in the free abelian group on the primes,
    /// and the address must multiply back to the term's own base.
    #[test]
    fn every_head_term_address_reopens_to_its_base() {
        let chain = eta_chain_decomposition(&probe_point(), &probe_config()).expect("the chain");
        for term in &chain.head {
            let rebuilt = term.address.iter().fold(1u32, |product, valuation| {
                product * valuation.prime.pow(valuation.exponent)
            });
            assert_eq!(rebuilt, term.base, "address did not reopen to its base");
        }
    }

    /// Borwein's weights are integers — `borwein_weights` refuses otherwise — and
    /// the first is always one.
    #[test]
    fn borwein_weights_are_integers_and_open_at_one() {
        for depth in 1u32..=14 {
            let weights = borwein_weights(depth).expect("integral weights");
            assert_eq!(weights.len(), depth as usize + 1);
            assert_eq!(weights[0], BigInt::one(), "d_0 must be 1 at depth {depth}");
        }
        assert!(borwein_weights(0).is_err(), "depth zero must refuse");
    }

    /// The two frames. Borwein carries no certificate here — his bound needs Gamma,
    /// which this body does not own — so the check is that his chain lands inside the
    /// Euler--Maclaurin enclosure once it is deep enough, AND that it does NOT when it
    /// is shallow. Without the second arm the first could not fail.
    #[test]
    fn the_two_frames_meet_only_once_borwein_is_deep_enough() {
        let config = probe_config();
        let point = probe_point();
        let certified = eta_evaluate(&point, &config)
            .expect("the certified frame")
            .value;
        let overlaps = |left: &RatInterval, right: &RatInterval| {
            left.lower <= right.upper && right.lower <= left.upper
        };
        let agrees = |depth: u32| {
            let borwein = eta_borwein_chain(&point, depth, &config).expect("the Borwein chain");
            overlaps(&borwein.value.re, &certified.re) && overlaps(&borwein.value.im, &certified.im)
        };
        assert!(
            !agrees(6),
            "a shallow Borwein chain must NOT reach the enclosure"
        );
        assert!(agrees(32), "a deep Borwein chain must reach the enclosure");
    }

    #[test]
    fn common_continued_fraction_stops_at_the_first_unresolved_turn() {
        let interval = RatInterval::new(rat(14, 1), rat(57, 4));
        assert_eq!(
            interval_common_continued_fraction(&interval, 8),
            vec![BigInt::from(14)]
        );
    }
}
