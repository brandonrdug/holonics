//! **Two clocks: the Farey lock and the convergent near-returns.**
//!
//! [definition] Lean `Aeon/Clock/Lock` and the aeon record ("two clocks and their crossing axes").
//! Two navigators share one joint motion and the first advances `α = p/q` turns per turn of the
//! second. On the lift of their joint clock torus ([`ClockLift`]) they are the rings of periods
//! `q` and `p` under the diagonal motion (one micro-step of each per joint step), so over any aeon
//! the first clock reads `α` times the second. The aeon of `k` turns of the second clock reads
//! `(k α, k)` (Lean `jointReading`), and it is a **cycle** exactly when it closes on the torus,
//! exactly when both readings are whole (`IsCycle`).
//!
//! - **The lock.** With `p, q` coprime an aeon of `k` turns is a cycle exactly when `q | k`
//!   (`cycle_iff_period_dvd`); `p/q` is the pair's Farey lock address
//!   ([`crate::navigator::address::LockAddress`]) and `q` its period (`lock_at_address`).
//! - **The near-return grains** are the continued-fraction convergents `p_n/q_n` of `α`, read from
//!   the lock address's partial quotients. The aeon of `q_n` turns misses closure by
//!   `q_n α − p_n` turns, exactly, with `|q_n α − p_n| ≤ 1/q_(n+1)` below the last convergent,
//!   which closes (`convergent_near_return`, `rational_ratio_locks_at_a_convergent`). Consecutive
//!   convergents are Farey neighbours, so a lock between them costs their mediant's period
//!   (`between_consecutive_convergents_costs_the_mediant`).
//!
//! [open] Lean states the near-return bound and the neighbour law for irrational `α`
//! (`Aeon/Clock/Lock.convergent_near_return`, `convergents_are_farey_neighbours`, from Mathlib's
//! `GenContFract.abs_sub_convs_le` and the determinant formula, which need only non-termination
//! at `n`). The rational form checked here, at every `n` below the last convergent, is owed there
//! (#62). An irrational ratio has no exact rational chart and is not constructed.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use crate::aeon::AeonError;
use crate::aeon::groupoid::{Aeon, ClockLift, Cycle};
use crate::aeon::reading::{Reading, TorusClock, reading};
use crate::navigator::address::LockAddress;
use crate::ratio::Rat;

/// [definition] **Two clocks** of frequency ratio `α = p/q > 0` on the lift of their joint torus.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TwoClocks {
    ratio: Rat,
    lift: ClockLift,
}

/// [definition] **A convergent** `p_n/q_n` of the frequency ratio: the aeon of `turns = q_n` turns
/// of the second clock is its near-return, and `windings = p_n` the whole turns it nearly closes on.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Convergent {
    pub windings: BigInt,
    pub turns: BigInt,
}

impl Convergent {
    /// `p_n / q_n` as a ratio.
    pub fn ratio(&self) -> Rat {
        Rat::new(self.windings.clone(), self.turns.clone())
    }
}

impl TwoClocks {
    /// Two clocks whose first advances `ratio` turns per turn of the second; the ratio is a
    /// positive rate.
    pub fn new(ratio: Rat) -> Result<Self, AeonError> {
        if !ratio.is_positive() {
            return Err(AeonError::NotAPositiveRate);
        }
        let period = |value: &BigInt| {
            value
                .to_biguint()
                .expect("a positive reduced ratio has positive parts")
        };
        let lift = ClockLift::new(vec![period(ratio.denom()), period(ratio.numer())])?;
        Ok(Self { ratio, lift })
    }

    pub fn ratio(&self) -> &Rat {
        &self.ratio
    }

    pub fn lift(&self) -> &ClockLift {
        &self.lift
    }

    /// **The aeon of `turns` turns of the second clock**: `p · turns` joint steps from rest, each
    /// one micro-step of each navigator.
    pub fn aeon(&self, turns: &BigUint) -> Result<Aeon<ClockLift>, AeonError> {
        let joint_steps = self.ratio.numer().magnitude() * turns;
        let joint_steps =
            usize::try_from(joint_steps).map_err(|_| AeonError::BeyondAddressSpace)?;
        let mut moves = Vec::with_capacity(2 * joint_steps);
        for _ in 0..joint_steps {
            moves.push((0, true));
            moves.push((1, true));
        }
        self.lift.walk(vec![BigInt::zero(), BigInt::zero()], &moves)
    }

    /// **The joint reading** of an aeon: the first clock's reading and the second's. Lean
    /// `jointReading`.
    pub fn joint_reading(&self, aeon: &Aeon<ClockLift>) -> Result<(Reading, Reading), AeonError> {
        Ok((
            reading(&TorusClock::navigator(&self.lift, 0)?, aeon)?,
            reading(&TorusClock::navigator(&self.lift, 1)?, aeon)?,
        ))
    }

    /// Whether an aeon of the joint motion is a cycle: it closes on the torus. Lean `IsCycle`.
    pub fn is_cycle(&self, aeon: &Aeon<ClockLift>) -> bool {
        Cycle::close(&self.lift, aeon.clone()).is_ok()
    }

    /// **The Farey lock address** of the pair: the Stern–Brocot word of `p/q`, whose period is `q`.
    pub fn lock_address(&self) -> Result<LockAddress, AeonError> {
        Ok(LockAddress::from_ratio(
            self.ratio.numer(),
            self.ratio.denom(),
        )?)
    }

    /// **The convergents** `p_n/q_n`, from the lock address's partial quotients:
    /// `p_n = a_n p_(n−1) + p_(n−2)`, `q_n = a_n q_(n−1) + q_(n−2)`, from `p_(−1)/q_(−1) = 1/0`
    /// and `p_(−2)/q_(−2) = 0/1`. The last is `α` itself.
    pub fn convergents(&self) -> Result<Vec<Convergent>, AeonError> {
        let quotients = self.lock_address()?.partial_quotients();
        let (mut previous, mut before) = (
            (BigInt::one(), BigInt::zero()),
            (BigInt::zero(), BigInt::one()),
        );
        let mut convergents = Vec::with_capacity(quotients.len());
        for quotient in quotients {
            let quotient = BigInt::from(quotient);
            let next = (
                &quotient * &previous.0 + &before.0,
                &quotient * &previous.1 + &before.1,
            );
            convergents.push(Convergent {
                windings: next.0.clone(),
                turns: next.1.clone(),
            });
            before = previous;
            previous = next;
        }
        Ok(convergents)
    }

    /// **The near-return of a convergent**: the first clock's reading over the aeon of `q_n` turns
    /// of the second, less the `p_n` whole windings it nearly closes on, `q_n α − p_n` turns.
    pub fn near_return(&self, convergent: &Convergent) -> Result<Rat, AeonError> {
        let turns = convergent
            .turns
            .to_biguint()
            .ok_or(AeonError::NotAPositiveRate)?;
        let (first, _) = self.joint_reading(&self.aeon(&turns)?)?;
        Ok(first.turns() - Rat::from_integer(convergent.windings.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::navigator::address::{are_neighbours, mediant, simplest_between};
    use crate::ratio::rat;
    use num_traits::Zero;

    fn coprime_ratios() -> impl Iterator<Item = Rat> {
        (1i64..=9).flat_map(|p| {
            (1i64..=9)
                .map(move |q| rat(p, q))
                .filter(move |ratio| ratio.numer() == &BigInt::from(p))
        })
    }

    /// **Two clocks lock at their Farey address.** For coprime `p/q` the aeon of `k` turns of the
    /// second clock is a cycle exactly when `q | k`, exactly when both readings are whole; the
    /// aeon of `q·m` turns reads `(p m, q m)` whole windings, and `q` is the lock address's
    /// period. Lean `Lock.lock_at_address`, `cycle_iff_period_dvd`, `jointReading_isCycle_iff`,
    /// `Winding.torus_closes_iff`.
    #[test]
    fn two_clocks_lock_at_their_farey_address() {
        for ratio in coprime_ratios() {
            let clocks = TwoClocks::new(ratio.clone()).unwrap();
            let (p, q) = (ratio.numer().clone(), ratio.denom().clone());
            assert_eq!(clocks.lock_address().unwrap().period().unwrap(), q);
            for k in 0u32..=(3 * 9) {
                let aeon = clocks.aeon(&BigUint::from(k)).unwrap();
                let (first, second) = clocks.joint_reading(&aeon).unwrap();
                assert_eq!(first.turns(), &ratio * Rat::from_integer(BigInt::from(k)));
                let divides = (BigInt::from(k) % &q).is_zero();
                assert_eq!(clocks.is_cycle(&aeon), divides);
                assert_eq!(first.is_whole() && second.is_whole(), divides);
                if divides {
                    let m = BigInt::from(k) / &q;
                    assert_eq!(first.windings(), &(&p * &m));
                    assert_eq!(second.windings(), &(&q * &m));
                }
            }
        }
        assert_eq!(TwoClocks::new(rat(-1, 2)), Err(AeonError::NotAPositiveRate));
    }

    /// **The convergents are the near-return grains.** Below the last convergent the aeon of
    /// `q_n` turns misses closure by `|q_n α − p_n| ≤ 1/q_(n+1)` turns, exactly; the last
    /// convergent is `α` and its aeon is a cycle. Lean `Lock.convergent_near_return` (stated for
    /// irrational `α`), `rational_ratio_locks_at_a_convergent`.
    #[test]
    fn the_convergents_are_the_near_return_grains() {
        for ratio in coprime_ratios().chain([rat(13, 8), rat(5, 13)]) {
            let clocks = TwoClocks::new(ratio.clone()).unwrap();
            let convergents = clocks.convergents().unwrap();
            let last = convergents.last().unwrap();
            assert_eq!(last.ratio(), ratio);
            assert!(clocks.near_return(last).unwrap().is_zero());
            assert!(clocks.is_cycle(&clocks.aeon(&last.turns.to_biguint().unwrap()).unwrap()));
            for pair in convergents.windows(2) {
                let miss = clocks.near_return(&pair[0]).unwrap();
                assert!(miss.abs() <= Rat::new(BigInt::one(), pair[1].turns.clone()));
            }
        }
    }

    /// **Consecutive convergents are Farey neighbours**, `p_n q_(n+1) − q_n p_(n+1) = ±1`, so the
    /// cheapest lock strictly between them is their mediant, of period `q_n + q_(n+1)`. Lean
    /// `Lock.convergents_are_farey_neighbours` (stated for irrational `α`),
    /// `between_consecutive_convergents_costs_the_mediant`.
    #[test]
    fn consecutive_convergents_are_farey_neighbours() {
        for ratio in [rat(13, 8), rat(5, 13), rat(22, 7), rat(9, 4)] {
            let convergents = TwoClocks::new(ratio).unwrap().convergents().unwrap();
            for pair in convergents.windows(2) {
                let (a, b) = (pair[0].ratio(), pair[1].ratio());
                let (lower, upper) = if a < b { (a, b) } else { (b, a) };
                assert!(are_neighbours(&lower, &upper));
                let between = simplest_between(&lower, &upper).unwrap();
                assert_eq!(between, mediant(&lower, &upper));
                assert_eq!(between.denom(), &(&pair[0].turns + &pair[1].turns));
            }
        }
    }
}
