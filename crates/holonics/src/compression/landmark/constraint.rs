//! **Constraint identities are navigators: π and `e` through their partial navigators, read by
//! certified digit windows.**
//!
//! [definition] π and `e` are **constraint identities**: the identity is the navigator and carries
//! no error; a digit window is a receiver face, and error enters only in how that face is attained.
//! The **partial navigator** of a ratio series is the compiled block of its ratio word (Lean
//! `Mathematics/RatioSeriesTransport`): a block `(n, α, β)` acts on the carried pair (current term,
//! partial sum) by `(t, s) ↦ (αt, s + βt)`, blocks compose associatively, and any bracketing of a
//! word (binary splitting in particular) compiles to one block ([`RatioBlock`]).
//!
//! ```text
//! e:  t_i = 1/i!, r_i = 1/(i+1);   s_N ≤ e ≤ s_N + (N+2)/((N+1)!(N+1)) = U_N                 certified tail
//! π:  π = 16 arctan(1/5) − 4 arctan(1/239)                                               Machin
//!     arctan x: t_i = (−1)ⁱx^(2i+1)/(2i+1), r_i = −x²(2i+1)/(2i+3);  S_(2N+1) ≤ arctan x ≤ S_(2N)
//!     L_N = 16 S⁽⁵⁾_(2N+1) − 4 S⁽²³⁹⁾_(2N) ≤ π ≤ 16 S⁽⁵⁾_(2N) − 4 S⁽²³⁹⁾_(2N+1) = U_N
//! window(b, k, l, x) = ⌊b^(k+l) x⌋ mod b^l
//! certificate:  L ≤ x ≤ U  and  ⌊b^(k+l) L⌋ = ⌊b^(k+l) U⌋  ⇒  window(b, k, l, x) = ⌊b^(k+l) L⌋ mod b^l
//! ```
//!
//! [proved-derived; implemented-exact] **A window is returned only with its certificate**: the
//! floors of both enclosure ends agree at the scale `b^(k+l)` ([`WindowCertificate`]; Lean
//! `Mathematics/RadixWindowReceiver.window_eq_of_endpoint_floors_eq`). After `N` blocks the
//! enclosure is exactly Lean's: `(eConvergent N, eUpper N)` for `e` and `(piLower N, piUpper N)` for
//! π, so a returned certificate is the hypothesis of `e_window_certified` or `pi_window_certified`.
//! A convergent without the certificate does not read the window: the block of `0` ratios reads the
//! digit `0` of `e`, whose first digit is `7` (`uncertified_block_misreads`). The search for the
//! first certifying block terminates, since every window of π and `e` has a finite certificate
//! (`pi_window_certificate_exists`, `e_window_certificate_exists`): both are irrational, so off
//! every radix grid (`off_grid_of_irrational`, `exp_one_irrational`; Mathlib `irrational_pi`), and
//! their enclosure widths fall to zero. An on-grid value can have convergent enclosures that never
//! certify ([`certify_window`]; Lean `on_grid_never_certifies`), while an exact enclosure
//! `L = U = x` certifies at once.
//!
//! [definition; agent-inferred] **π through Machin's arms, not Leibniz.** Leibniz's series at `x = 1`
//! needs about `b^(k+l)` terms for a window at offset `k`; the arm `arctan(1/5)` gains `log₁₀ 25`
//! digits per ratio (Lean `machin`, over Mathlib's `Real.four_mul_arctan_inv_5_sub_arctan_inv_239`,
//! and `arm_enclosure`, `pi_enclosure`).
//!
//! | Lean | Rust |
//! |---|---|
//! | `RatioSeriesTransport.step`, `execute`, `Block`, `Block.act`, `Block.single`, `Block.compose`, `compile`, `compile_act` | [`RatioBlock`], [`execute`] |
//! | `ConstraintIdentity.unitBlock`, `compose_assoc`, `unit_compose`, `compose_unit`, `execute_append`, `compile_append` | [`RatioBlock::compile`] (binary splitting), tests |
//! | `ConstraintIdentity.partial_navigator_act`, `execute_ratioWord` | tests |
//! | `Identity.ratio_routes_are_an_identity`, `RatioSeriesTransport.distinct_routes_same_block` | tests |
//! | `ConstraintIdentity.eRatio`, `eTerm_succ`, `eConvergent`, `eUpper`, `e_enclosure`, `e_mem_enclosure`, `exp_one_irrational` | [`ConstraintIdentity::E`], [`ConstraintIdentity::enclosure`] |
//! | `RatioSeriesTransport.arctanTerm_succ`, `arctanRatio`; `ConstraintIdentity.armSum`, `arm_enclosure`, `machin`, `piLower`, `piUpper`, `pi_enclosure` | [`ConstraintIdentity::Pi`], [`ConstraintIdentity::enclosure`] |
//! | `RadixWindowReceiver.window`, `window_eq_of_endpoint_floors_eq` | [`certify_window`], [`WindowCertificate`] |
//! | `ConstraintIdentity.e_window_certified`, `e_window_certificate_exists`, `pi_window_certified`, `pi_window_certificate_exists`, `off_grid_of_irrational` | [`ConstraintIdentity::window`] |
//! | `ConstraintIdentity.uncertified_block_misreads`, `on_grid_never_certifies` | tests |

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::compression::landmark::LandmarkError;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::{Rat, integer};

/// The carried pair `(current term, partial sum)`.
pub type SeriesState = (Rat, Rat);

/// **One ratio step** `(t, s) ↦ (rt, s + rt)`, executed along a word (Lean `step`, `execute`).
pub fn execute(word: &[Rat], state: &SeriesState) -> SeriesState {
    word.iter().fold(state.clone(), |(term, sum), ratio| {
        let next = ratio * &term;
        let sum = sum + &next;
        (next, sum)
    })
}

/// [definition] **The partial navigator of a ratio word**: its length and the two coefficients that
/// replay its action, `(t, s) ↦ (αt, s + βt)` (Lean `RatioSeriesTransport.Block`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RatioBlock {
    length: usize,
    alpha: Rat,
    beta: Rat,
}

impl RatioBlock {
    /// The empty block `(0, 1, 0)` (Lean `unitBlock`).
    pub fn unit() -> Self {
        Self {
            length: 0,
            alpha: Rat::one(),
            beta: Rat::zero(),
        }
    }

    /// The block of one ratio, `(1, r, r)` (Lean `Block.single`).
    pub fn single(ratio: Rat) -> Self {
        Self {
            length: 1,
            alpha: ratio.clone(),
            beta: ratio,
        }
    }

    /// **Chronological composition**, `self` and then `second`:
    /// `(n₁ + n₂, α₂α₁, β₁ + β₂α₁)` (Lean `Block.compose`).
    pub fn compose(&self, second: &Self) -> Self {
        Self {
            length: self.length + second.length,
            alpha: &second.alpha * &self.alpha,
            beta: &self.beta + &second.beta * &self.alpha,
        }
    }

    /// **The block of a ratio word, by binary splitting**: the word's halves are compiled and
    /// composed, which any bracketing gives (Lean `compose_assoc`, `compile_append`).
    pub fn compile(word: &[Rat]) -> Self {
        match word {
            [] => Self::unit(),
            [ratio] => Self::single(ratio.clone()),
            _ => {
                let (first, second) = word.split_at(word.len() / 2);
                Self::compile(first).compose(&Self::compile(second))
            }
        }
    }

    /// The block's action on the carried pair (Lean `Block.act`, `compile_act`).
    pub fn act(&self, state: &SeriesState) -> SeriesState {
        (&self.alpha * &state.0, &state.1 + &self.beta * &state.0)
    }

    /// The number of ratios compiled.
    pub fn length(&self) -> usize {
        self.length
    }

    /// `α`, the product of the ratios.
    pub fn alpha(&self) -> &Rat {
        &self.alpha
    }

    /// `β`, the sum of the partial products.
    pub fn beta(&self) -> &Rat {
        &self.beta
    }
}

/// [definition] **A certified digit window**: `l` digits in radix `b` after offset `k`, read from an
/// enclosure whose two ends have one floor at the scale `b^(k+l)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WindowCertificate {
    pub radix: u32,
    pub offset: u32,
    pub length: u32,
    /// `⌊b^(k+l) x⌋ mod b^l`.
    pub window: BigInt,
    /// The common floor `⌊b^(k+l) L⌋ = ⌊b^(k+l) U⌋`.
    pub floor: BigInt,
    /// The enclosure `L ≤ x ≤ U` that certifies it.
    pub enclosure: ExactInterval,
    /// The number of partial-navigator blocks that produced the enclosure.
    pub blocks: usize,
}

/// **The window certificate of one enclosure**: `Some(window)` exactly when the floors of both
/// ends agree at the scale `b^(k+l)` (Lean `window_eq_of_endpoint_floors_eq`), else `None`. A radix
/// below two, and an offset and length whose sum passes `u32::MAX`, are refused.
pub fn certify_window(
    enclosure: &ExactInterval,
    radix: u32,
    offset: u32,
    length: u32,
) -> Result<Option<(BigInt, BigInt)>, LandmarkError> {
    Ok(WindowScale::new(radix, offset, length)?.certify(enclosure))
}

/// The scale `b^(k+l)` and the modulus `b^l` of one window, computed once.
struct WindowScale {
    scale: Rat,
    modulus: BigInt,
}

impl WindowScale {
    fn new(radix: u32, offset: u32, length: u32) -> Result<Self, LandmarkError> {
        if radix < 2 {
            return Err(LandmarkError::Radix { radix });
        }
        let exponent = offset
            .checked_add(length)
            .ok_or(LandmarkError::WindowExtent { offset, length })?;
        Ok(Self {
            scale: Rat::from_integer(BigInt::from(radix).pow(exponent)),
            modulus: BigInt::from(radix).pow(length),
        })
    }

    /// `(window, floor)` when both ends share one floor at the scale.
    fn certify(&self, enclosure: &ExactInterval) -> Option<(BigInt, BigInt)> {
        let lower = (&self.scale * &enclosure.lower).floor().to_integer();
        let upper = (&self.scale * &enclosure.upper).floor().to_integer();
        if lower != upper {
            return None;
        }
        let window = ((&lower % &self.modulus) + &self.modulus) % &self.modulus;
        Some((window, lower))
    }
}

/// [definition] **The two constraint identities** read through their partial navigators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintIdentity {
    /// `e = Σ 1/i!`.
    E,
    /// `π = 16 arctan(1/5) − 4 arctan(1/239)`.
    Pi,
}

/// The partial sums `(S_(2N), S_(2N+1))` of the arm `arctan x` after `N` blocks of two ratios.
struct Arm {
    square: Rat,
    index: usize,
    state: SeriesState,
}

impl Arm {
    fn new(x: Rat) -> Self {
        Self {
            square: &x * &x,
            index: 0,
            state: (x.clone(), x),
        }
    }

    /// Lean `arctanRatio x i = −x²(2i + 1)/(2i + 3)`.
    fn ratio(&self, index: usize) -> Rat {
        let odd = Rat::from_integer(BigInt::from(index) * 2 + 1);
        -(&self.square * &odd) / (odd + integer(2))
    }

    /// `(S_(2N+1), S_(2N))`: the alternating enclosure of the arm.
    fn enclosure(&self) -> (Rat, Rat) {
        let next = execute(&[self.ratio(self.index)], &self.state);
        (next.1, self.state.1.clone())
    }

    /// Advance by the compiled block of the next two ratios.
    fn advance(&mut self) {
        let block = RatioBlock::compile(&[self.ratio(self.index), self.ratio(self.index + 1)]);
        self.state = block.act(&self.state);
        self.index += 2;
    }
}

/// The enclosures of one identity, block by block.
enum Enclosures {
    E {
        blocks: usize,
        state: SeriesState,
    },
    Pi {
        blocks: usize,
        fifth: Arm,
        two_thirty_ninth: Arm,
    },
}

impl Enclosures {
    fn new(identity: ConstraintIdentity) -> Self {
        match identity {
            ConstraintIdentity::E => Self::E {
                blocks: 0,
                state: (Rat::one(), Rat::one()),
            },
            ConstraintIdentity::Pi => Self::Pi {
                blocks: 0,
                fifth: Arm::new(Rat::new(BigInt::one(), BigInt::from(5))),
                two_thirty_ninth: Arm::new(Rat::new(BigInt::one(), BigInt::from(239))),
            },
        }
    }

    fn blocks(&self) -> usize {
        match self {
            Self::E { blocks, .. } | Self::Pi { blocks, .. } => *blocks,
        }
    }

    /// The enclosure at the current block count.
    fn current(&self) -> Result<ExactInterval, LandmarkError> {
        match self {
            Self::E { blocks, state } => {
                let next_index = Rat::from_integer(BigInt::from(*blocks) + 1);
                let next_term = &state.0 / &next_index;
                let upper = &state.1 + next_term * (&next_index + Rat::one()) / &next_index;
                Ok(ExactInterval::new(state.1.clone(), upper)?)
            }
            Self::Pi {
                fifth,
                two_thirty_ninth,
                ..
            } => {
                let (fifth_low, fifth_high) = fifth.enclosure();
                let (far_low, far_high) = two_thirty_ninth.enclosure();
                Ok(ExactInterval::new(
                    integer(16) * fifth_low - integer(4) * far_high,
                    integer(16) * fifth_high - integer(4) * far_low,
                )?)
            }
        }
    }

    fn advance(&mut self) {
        match self {
            Self::E { blocks, state } => {
                let ratio = Rat::new(BigInt::one(), BigInt::from(*blocks) + 1);
                *state = RatioBlock::single(ratio).act(state);
                *blocks += 1;
            }
            Self::Pi {
                blocks,
                fifth,
                two_thirty_ninth,
            } => {
                fifth.advance();
                two_thirty_ninth.advance();
                *blocks += 1;
            }
        }
    }
}

impl ConstraintIdentity {
    /// **The enclosure after `blocks` partial-navigator blocks**: for `e`, the convergent `s_N` and
    /// its certified tail, `[eConvergent N, eUpper N]` (Lean `e_mem_enclosure`); for π, Machin's two
    /// arms each between consecutive partial sums, `[piLower N, piUpper N]` (`pi_enclosure`).
    pub fn enclosure(&self, blocks: usize) -> Result<ExactInterval, LandmarkError> {
        let mut enclosures = Enclosures::new(*self);
        for _ in 0..blocks {
            enclosures.advance();
        }
        enclosures.current()
    }

    /// **The certified window** of `length` digits in `radix` after `offset`: the first block whose
    /// enclosure ends share one floor, returned with that certificate (Lean `e_window_certified`,
    /// `pi_window_certified`; one exists, `e_window_certificate_exists`,
    /// `pi_window_certificate_exists`).
    pub fn window(
        &self,
        radix: u32,
        offset: u32,
        length: u32,
    ) -> Result<WindowCertificate, LandmarkError> {
        let scale = WindowScale::new(radix, offset, length)?;
        let mut enclosures = Enclosures::new(*self);
        loop {
            let enclosure = enclosures.current()?;
            if let Some((window, floor)) = scale.certify(&enclosure) {
                return Ok(WindowCertificate {
                    radix,
                    offset,
                    length,
                    window,
                    floor,
                    enclosure,
                    blocks: enclosures.blocks(),
                });
            }
            enclosures.advance();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::rat;
    use num_traits::Signed;

    fn ratios(values: &[(i64, i64)]) -> Vec<Rat> {
        values.iter().map(|(p, q)| rat(*p, *q)).collect()
    }

    fn window(identity: ConstraintIdentity, radix: u32, offset: u32, length: u32) -> BigInt {
        identity.window(radix, offset, length).unwrap().window
    }

    /// Lean `compose_assoc`, `unit_compose`, `compose_unit`, `execute_append`, `compile_append`,
    /// `compile_act`: blocks compose associatively with the empty block as unit, binary splitting
    /// compiles every bracketing to one block, and the block replays the word's execution.
    #[test]
    fn partial_navigators_compose_associatively() {
        let word = ratios(&[(1, 2), (-3, 5), (7, 3), (2, 9), (-1, 4), (5, 1), (3, 8)]);
        let sequential = word.iter().fold(RatioBlock::unit(), |block, ratio| {
            block.compose(&RatioBlock::single(ratio.clone()))
        });
        assert_eq!(RatioBlock::compile(&word), sequential);
        let (a, b, c) = (
            RatioBlock::compile(&word[..2]),
            RatioBlock::compile(&word[2..5]),
            RatioBlock::compile(&word[5..]),
        );
        assert_eq!(a.compose(&b).compose(&c), a.compose(&b.compose(&c)));
        assert_eq!(RatioBlock::unit().compose(&a), a);
        assert_eq!(a.compose(&RatioBlock::unit()), a);
        let state = (rat(3, 7), rat(-2, 5));
        assert_eq!(
            RatioBlock::compile(&word).act(&state),
            execute(&word, &state)
        );
        assert_eq!(
            execute(&word, &state),
            execute(&word[4..], &execute(&word[..4], &state))
        );
        assert_eq!(RatioBlock::compile(&word).length(), word.len());
    }

    /// Lean `partial_navigator_act`, `eTerm_succ`: the block of the first `n` ratios `1/(i + 1)`
    /// carries `(1, 1)` to `(1/n!, Σ_(i≤n) 1/i!)`.
    #[test]
    fn a_partial_navigator_returns_the_convergent() {
        let mut factorial = Rat::one();
        let mut sum = Rat::one();
        for n in 1..16i64 {
            factorial *= integer(n);
            sum += factorial.recip();
            let word: Vec<Rat> = (0..n).map(|i| rat(1, i + 1)).collect();
            assert_eq!(
                RatioBlock::compile(&word).act(&(Rat::one(), Rat::one())),
                (factorial.recip(), sum.clone())
            );
        }
    }

    /// Lean `ratio_routes_are_an_identity`, `distinct_routes_same_block`,
    /// `equal_block_different_interior`: `[1, 1, 1]` and `[1/2, 3, 2/3]` are two constructions with
    /// one block, though their first partial sums differ.
    #[test]
    fn two_ratio_routes_are_one_block() {
        let left = ratios(&[(1, 1), (1, 1), (1, 1)]);
        let right = ratios(&[(1, 2), (3, 1), (2, 3)]);
        assert_ne!(left, right);
        assert_eq!(RatioBlock::compile(&left), RatioBlock::compile(&right));
        let start = (Rat::one(), Rat::zero());
        assert_ne!(
            execute(&left[..1], &start).1,
            execute(&right[..1], &start).1
        );
    }

    /// Lean `e_mem_enclosure`, `e_enclosure`, `exp_one_irrational`: the enclosures
    /// `[s_N, U_N]` nest around `e` and shrink. `e_enclosure`'s sharper lower end
    /// `s_N + 1/(N + 1)!` is the next convergent `s_(N+1)`, still below `U_N`; so `N!(e − s_N)` lies
    /// in `[1/(N + 1), (N + 2)/(N + 1)²] ⊂ (0, 1)`, strictly between two consecutive integers: `e`
    /// is irrational from its own enclosure.
    #[test]
    fn the_e_enclosure_is_certified_and_proves_irrationality() {
        let mut previous = ConstraintIdentity::E.enclosure(0).unwrap();
        let mut factorial = Rat::one();
        let mut sum = Rat::one();
        for n in 1..25i64 {
            factorial *= integer(n);
            sum += factorial.recip();
            let enclosure = ConstraintIdentity::E
                .enclosure(usize::try_from(n).unwrap())
                .unwrap();
            assert_eq!(enclosure.lower, sum);
            assert!(previous.lower <= enclosure.lower && enclosure.upper <= previous.upper);
            assert!(&enclosure.upper - &enclosure.lower < &previous.upper - &previous.lower);
            let sharper = ConstraintIdentity::E
                .enclosure(usize::try_from(n + 1).unwrap())
                .unwrap()
                .lower;
            assert!(sharper <= enclosure.upper);
            let low = (&sharper - &sum) * &factorial;
            let high = (&enclosure.upper - &sum) * &factorial;
            assert_eq!(low, rat(1, n + 1));
            assert_eq!(high, rat(n + 2, (n + 1) * (n + 1)));
            assert!(low.is_positive() && high < Rat::one());
            previous = enclosure;
        }
    }

    /// The partial sum of the arm `arctan x` after `n` ratios from `(x, x)` (Lean `armSum`).
    fn arm_sum(x: &Rat, n: usize) -> Rat {
        let word: Vec<Rat> = (0..n)
            .map(|i| {
                let odd = integer(i64::try_from(2 * i + 1).unwrap());
                -(x * x * &odd) / (odd + integer(2))
            })
            .collect();
        RatioBlock::compile(&word).act(&(x.clone(), x.clone())).1
    }

    /// Lean `eConvergent`, `eUpper`, `piLower`, `piUpper`, `e_window_certified`,
    /// `pi_window_certified`: **the enclosure after `N` blocks is exactly Lean's**, the partial
    /// navigator's convergent with its certified tail for `e` and Machin's `(L_N, U_N)` for π, so a
    /// returned certificate is the hypothesis of the certified-window theorem: the floors of both
    /// ends agree and the window is that floor's residue.
    #[test]
    fn a_certificate_is_the_floor_equality_of_the_lean_enclosure() {
        let (fifth, far) = (rat(1, 5), rat(1, 239));
        for n in 0..8usize {
            let e = ConstraintIdentity::E.enclosure(n).unwrap();
            let word: Vec<Rat> = (0..n)
                .map(|i| rat(1, i64::try_from(i).unwrap() + 1))
                .collect();
            let convergent = RatioBlock::compile(&word).act(&(Rat::one(), Rat::one())).1;
            let (term, count) = (
                RatioBlock::compile(&word).alpha().clone(),
                integer(i64::try_from(n).unwrap()),
            );
            let upper = &convergent
                + &term * (&count + integer(2)) / ((&count + Rat::one()) * (&count + Rat::one()));
            assert_eq!((e.lower, e.upper), (convergent, upper));
            let pi = ConstraintIdentity::Pi.enclosure(n).unwrap();
            let lower =
                integer(16) * arm_sum(&fifth, 2 * n + 1) - integer(4) * arm_sum(&far, 2 * n);
            let upper =
                integer(16) * arm_sum(&fifth, 2 * n) - integer(4) * arm_sum(&far, 2 * n + 1);
            assert_eq!((pi.lower, pi.upper), (lower, upper));
        }
        for (identity, radix, offset, length) in [
            (ConstraintIdentity::E, 10, 20, 10),
            (ConstraintIdentity::E, 16, 0, 8),
            (ConstraintIdentity::Pi, 10, 40, 10),
            (ConstraintIdentity::Pi, 2, 0, 16),
        ] {
            let certificate = identity.window(radix, offset, length).unwrap();
            assert_eq!(
                certificate.enclosure,
                identity.enclosure(certificate.blocks).unwrap()
            );
            let scale = Rat::from_integer(BigInt::from(radix).pow(offset + length));
            for end in [&certificate.enclosure.lower, &certificate.enclosure.upper] {
                assert_eq!((&scale * end).floor().to_integer(), certificate.floor);
            }
            let modulus = BigInt::from(radix).pow(length);
            assert_eq!(
                certificate.window,
                ((&certificate.floor % &modulus) + &modulus) % &modulus
            );
            if certificate.blocks > 0 {
                let earlier = identity.enclosure(certificate.blocks - 1).unwrap();
                assert_eq!(
                    certify_window(&earlier, radix, offset, length).unwrap(),
                    None
                );
            }
        }
    }

    /// Lean `uncertified_block_misreads`: **the certificate is load-bearing.** The block of `0`
    /// ratios returns the convergent `1`, whose floor at radix ten reads the digit `0`, while the
    /// first digit of `e` after the point is `7`; that block's enclosure `[1, 3]` does not certify.
    #[test]
    fn an_uncertified_block_misreads() {
        let convergent = RatioBlock::compile(&[]).act(&(Rat::one(), Rat::one())).1;
        assert_eq!(convergent, Rat::one());
        let floor = (integer(10) * &convergent).floor().to_integer();
        assert_eq!(floor % BigInt::from(10), BigInt::zero());
        assert_eq!(window(ConstraintIdentity::E, 10, 0, 1), BigInt::from(7));
        let first = ConstraintIdentity::E.enclosure(0).unwrap();
        assert_eq!(
            (first.lower.clone(), first.upper.clone()),
            (integer(1), integer(3))
        );
        assert_eq!(certify_window(&first, 10, 0, 1).unwrap(), None);
    }

    /// Mathlib `four_mul_arctan_inv_5_sub_arctan_inv_239` with each arm's alternating enclosure: the
    /// π enclosures nest, shrink by more than a decimal digit per block, and close between the
    /// convergents `333/106 < π < 355/113`.
    #[test]
    fn the_machin_enclosure_nests_around_pi() {
        let mut previous = ConstraintIdentity::Pi.enclosure(0).unwrap();
        assert!(previous.lower <= rat(355, 113) && rat(333, 106) <= previous.upper);
        for blocks in 1..20 {
            let enclosure = ConstraintIdentity::Pi.enclosure(blocks).unwrap();
            assert!(previous.lower <= enclosure.lower && enclosure.upper <= previous.upper);
            let width = &enclosure.upper - &enclosure.lower;
            assert!(width * integer(10) < &previous.upper - &previous.lower);
            previous = enclosure;
        }
        assert!(previous.lower < rat(355, 113) && rat(333, 106) < previous.lower);
    }

    /// **Known windows of π, certified**: decimal `14159`, `89793` at offset `10`, `6939937510` at
    /// offset `40`, `06286208` at offset `70`; hexadecimal `243F6A88` and `85A308D3`; binary
    /// `0010010000111111`. Each returned window carries equal endpoint floors.
    #[test]
    fn known_windows_of_pi_are_certified() {
        use ConstraintIdentity::Pi;
        assert_eq!(window(Pi, 10, 0, 5), BigInt::from(14159));
        assert_eq!(window(Pi, 10, 10, 5), BigInt::from(89793));
        assert_eq!(window(Pi, 10, 40, 10), BigInt::from(6_939_937_510u64));
        assert_eq!(window(Pi, 10, 70, 8), BigInt::from(6_286_208));
        assert_eq!(window(Pi, 16, 0, 8), BigInt::from(0x243F_6A88u64));
        assert_eq!(window(Pi, 16, 8, 8), BigInt::from(0x85A3_08D3u64));
        assert_eq!(window(Pi, 2, 0, 16), BigInt::from(0x243F));
        let certificate = Pi.window(10, 40, 10).unwrap();
        let scale = Rat::from_integer(BigInt::from(10).pow(50));
        assert_eq!(
            (&scale * &certificate.enclosure.lower).floor().to_integer(),
            certificate.floor
        );
        assert_eq!(
            (&scale * &certificate.enclosure.upper).floor().to_integer(),
            certificate.floor
        );
    }

    /// **Known windows of `e`, certified**: decimal `7182818284`, `0287471352` at offset `20`,
    /// `6277240766` at offset `60`; hexadecimal `B7E15162`; binary `1011011111100001`.
    #[test]
    fn known_windows_of_e_are_certified() {
        use ConstraintIdentity::E;
        assert_eq!(window(E, 10, 0, 10), BigInt::from(7_182_818_284u64));
        assert_eq!(window(E, 10, 20, 10), BigInt::from(287_471_352));
        assert_eq!(window(E, 10, 60, 10), BigInt::from(6_277_240_766u64));
        assert_eq!(window(E, 16, 0, 8), BigInt::from(0xB7E1_5162u64));
        assert_eq!(window(E, 2, 0, 16), BigInt::from(0xB7E1));
        assert_eq!(E.window(1, 0, 1), Err(LandmarkError::Radix { radix: 1 }));
    }

    /// **An offset and length past `u32::MAX` are refused, not wrapped or panicked on**, both by
    /// [`certify_window`] and by [`ConstraintIdentity::window`].
    #[test]
    fn an_overflowing_window_extent_is_refused() {
        let enclosure = ConstraintIdentity::E.enclosure(10).unwrap();
        let refusal = LandmarkError::WindowExtent {
            offset: u32::MAX,
            length: 1,
        };
        assert_eq!(
            certify_window(&enclosure, 10, u32::MAX, 1),
            Err(refusal.clone())
        );
        assert_eq!(ConstraintIdentity::Pi.window(10, u32::MAX, 1), Err(refusal));
        assert_eq!(
            ConstraintIdentity::E.window(10, 1, u32::MAX),
            Err(LandmarkError::WindowExtent {
                offset: 1,
                length: u32::MAX
            })
        );
    }

    /// Lean `on_grid_never_certifies`: the enclosures
    /// `1 − 1/(N + 1) ≤ 1 ≤ 1` shrink to zero width yet never share a floor at radix ten, while the
    /// exact enclosure `1 ≤ 1 ≤ 1` certifies the window `0` at once.
    #[test]
    fn an_on_grid_value_is_not_certified_by_one_sided_enclosures() {
        for n in 0..400i64 {
            let enclosure = ExactInterval::new(Rat::one() - rat(1, n + 1), Rat::one()).unwrap();
            assert_eq!(certify_window(&enclosure, 10, 0, 1).unwrap(), None);
        }
        let exact = ExactInterval::point(Rat::one());
        assert_eq!(
            certify_window(&exact, 10, 0, 1).unwrap(),
            Some((BigInt::zero(), BigInt::from(10)))
        );
    }
}
