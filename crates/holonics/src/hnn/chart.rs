//! **The word on declared lattices: certified inverse charts and carried transients** (Decision 24;
//! Lean `HNN/LatticeWord`).
//!
//! [definition] Every inverse the word executes is a **lattice chart** `X̂` on `2^(−L_c)ℤ`, carried
//! as the integer matrix `Q` of its coordinates ([`ChartWords`]: `X̂ = Q·2^(−L_c)`, signed 64-bit
//! words), with an exact **certificate** `δ = ‖1 − A X̂‖∞`, the largest absolute row sum of the right
//! residual, computed in integers and read as a ratio ([`certificate`]). The chart is refined by
//! rounded Newton–Schulz steps until `δ` is at most the declared target ([`refine`]):
//!
//! ```text
//! A = Ā/D                       the operator's integer coordinates over one positive denominator
//! P = Ā Q                       exact, scale 1/(D·2^L_c)
//! N = Q (2D·2^L_c·1 − P)        exact, scale 1/(D·2^(2L_c))       X(2 − AX), Lean `nsStep`
//! Q' = ⌊(2N + S)/(2S)⌋,  S = D·2^L_c          the nearest point of 2^(−L_c)ℤ, ties upward
//! δ' = max_i Σ_j |(S·1 − Ā Q')_ij| / S        the certificate, exact
//! ```
//!
//! The rounded step keeps the certificate below `δ² + ‖A‖∞·n·2^(−L_c)/2`
//! (`rounded_refinement_certificate`); for `δ ≤ c ≤ 1/2` and a rounding term at most `c/2` it never
//! grows past `c` (`roundedIter_certificate`). A window **warm-starts** from the chart the last
//! window left for the same operator, since a deposit moves `A` by `D_A` and the start's residual
//! grows by at most `‖D_A‖∞‖X̂‖∞` (`warm_start_certificate`); the warm start is taken when that
//! certificate is at most `1/2`, the certified regime ([`ChartStart::Warm`]).
//!
//! [definition; agent-inferred] **The cold start is Newton–Schulz from the scaled transpose**
//! `2^(−p)Aᵀ`, `2^p ≥ ‖A‖₁‖A‖∞` ([`ChartStart::Transpose`]), for the first chart of an operator and
//! for a warm start above `1/2`. Its right residual `1 − 2^(−p)AAᵀ` is symmetric with spectrum in
//! `[0, 1 − 2^(−p)σ_min²]`, and every operator the word inverts has `σ_min ≥ 1` by passivity (the
//! ring's `I − ½K` has symmetric part `1 + ½ffᵀ ⪰ 1`, the contact's `m ⪰ 1`), so it reaches the
//! certified regime in `p + ⌈log₂(1 + ⌈log₂ n⌉)⌉ + 1` steps, all in integers. The two other starts
//! are refused by the data: a scaled identity needs `‖1 − A‖∞ < 1`, which campaign 1's initial ring
//! element already breaks (its unit slices give `‖½K‖∞ = 9/8`), and a deposit moves campaign 1's
//! ring elements by 1.4 to 2.3 in the certificate's norm, outside the warm start's regime; one exact
//! inverse, rounded, certifies at the rounding term alone but costs 27.7 ms for the 26-wide ring
//! (measured on the standing real cut), so it is kept only as the fallback when the cold phase's
//! step bound passes ([`ChartStart::Exact`]; it exists for every operator the word admits,
//! `cayley_denominator_det_rat` for the ring, positive definiteness for the contact). A refinement
//! in the certified regime that does not lower the certificate is refused
//! ([`HnnError::ChartCertificate`]), never rounded.
//!
//! [definition] **Integer products under the ℓ1 certificate** (the device's carrier,
//! `holonics-cuda::hnn::lattice`): a chart's coordinates are signed 64-bit words; each product
//! entry is a sum of 128-bit products, admitted only when its bound `Σ_j |q_ij x_j|` stays below
//! `2^127`, whatever its value, so the refusal depends on the exact terms alone
//! ([`HnnError::Carrier`]). An operand enters a product as its integral chart (integers over one
//! denominator, `crate::ratio::linear::vector::integral`): a carried transient on `2^(−L_w)ℤ` is
//! its coordinates over `2^(L_w)`.
//!
//! [definition] **Error feedback** ([`carry`], Lean `feedback_tick`): an image `y` plus the carried
//! remainder `r` splits at the nearest point of `2^(−L_w)ℤ`, ties upward, into the carried value `x`
//! and the next remainder, `x + r' = y + r` (the Ratio's `div_rem`, `hnn::Lattice::div_rem`). Over
//! a word, `Σ_t x_t + r_T = Σ_t y_t + r_0` (`feedback_accounting`), and the word releases `r_T`
//! at its end ([`Remainders`]).
//!
//! [definition; agent-inferred] **The declared precisions** ([`WordLattice::by_rule`]), from the
//! finest receiver grain `L_R`, the receiving fan-in `X_w = 2d_R` (the ℓ1 of the operand one read
//! sums, as for `R`'s `L_ℓ`), the widest local solve `w` and the word's junction steps `e_max`:
//!
//! ```text
//! δ = 2^(−D_c),  D_c = ⌈log₂(8 L_R X_w w e_max)⌉      the certificate's target
//! L_c = 2 D_c                                           the charts' lattice
//! L_w = ⌈log₂(4 L_R X_w e_max s)⌉,  s = 3               the transients' lattice
//! ```
//!
//! - Every inverse the word executes has `‖A⁻¹‖₂ ≤ 1` by passivity (the ring's `I − ½K` has
//!   symmetric part `1 + ½ffᵀ ⪰ 1`; the contact's `m = 1 + (G/2h)(2C + hD + ½h²K) ⪰ 1`), so
//!   `|A⁻¹_ij| ≤ 1` and `‖A⁻¹‖∞ ≤ w`. The executed solve deviates from the exact one by
//!   `‖(A⁻¹ − X̂)y‖∞ ≤ ‖A⁻¹‖∞ δ ‖y‖∞ ≤ w δ ‖y‖∞` (`A⁻¹ − X̂ = A⁻¹R`, the step of
//!   `inverse_chart_deviation`), at most `2wδ` on the element's unit-scale operand `2b + W_c c`;
//!   a read of `X_w` unit coefficients then moves by at most `2 X_w w δ` a tick, and over `e_max`
//!   ticks by at most `1/(4L_R)`. The adjoint's deviation is the same bound read on the ℓ1 side
//!   (`executed_adjoint_deviation`, `inverse_chart_adjoint_deviation`).
//! - `L_c = 2D_c` puts the rounding term `‖A‖∞ w 2^(−L_c)/2` at most `δ/2` whenever
//!   `‖A‖∞ w ≤ 2^(D_c)`, the hypothesis of `roundedIter_certificate` at `c = δ`; past it the
//!   refinement refuses.
//! - Each carried transient moves by less than one unit a split (`feedback_tick_deviation`), and a
//!   path crosses at most `s = 3` splits a tick ([`SPLITS`]: the junction's anchor, the contact's
//!   solved `ζ`, then the contact's state or arriving wave; the element's storage is the second on
//!   its own path), so a read moves by less than `3 X_w 2^(−L_w)` a tick and `1/(4L_R)` over the
//!   word.
//! - Together a read moves by less than `1/(2L_R)`, below the receiver's grain. The waves' unit
//!   scale and a non-expansive propagation of a deviation through the later ticks are the
//!   assumptions, as for `L_ℓ`; the counterfactual bound of the carried transient against the exact
//!   word's trajectory is owed in #62 (the Lean header's open item).
//!
//! Campaign 1 (`L_R = 16`, `X_w = 22`, `w = 26`, `e_max = 4`): `D_c = ⌈log₂ 292,864⌉ = 19`,
//! `L_c = 38`, `L_w = ⌈log₂ 16,896⌉ = 15`.
//!
//! | Lean (`HNN/LatticeWord`) | Rust |
//! |---|---|
//! | `nsStep`, `rounded_refinement_certificate`, `roundedIter_certificate`, `latticeChart` | [`refine`], [`newton_schulz_step`], [`ChartWords`] |
//!
//! [open] Owed in #62 (Lean): the scaled transpose's convergence (`σ_min ≥ 1` by passivity) is an
//! efficiency claim only, since every certificate is computed exactly and the exact inverse is the
//! fallback.
//! | `rowNorm` (the certificate), `warm_start_certificate`, `inverse_chart_deviation` | [`certificate`], [`Charts`] (the warm start), [`WordLattice::by_rule`] |
//! | `feedback_tick`, `feedback_accounting_zero`, `carried_word_accounting` | [`carry`], [`Remainders`] |
//! | `executed_adjoint_pairing`, `executed_adjoint_unique` | [`ChartWords::apply_transpose`] |

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::hnn::HnnError;
use crate::hnn::constitution::Lattice;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::integral;

/// The ℓ1 certificate's bound: a sum of 128-bit products is admitted below `2^127`.
const CARRIER: u128 = 1 << 127;

// -------------------------------------------------------------------------------------------
// the declared precisions

/// [definition; agent-inferred] **The word's declared precisions** (module header): the charts'
/// lattice `L_c`, the certificate's target `δ = 2^(−D_c)` and the transients' lattice `L_w`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WordLattice {
    chart: u32,
    target: u32,
    transient: u32,
}

/// [definition; agent-inferred] **The most splits one path crosses in a tick**: the junction's
/// anchor, the contact's solved `ζ`, and the contact's state or arriving wave (module header).
pub const SPLITS: u64 = 3;

/// `⌈log₂ x⌉` of a positive integer (zero at one).
fn ceil_log2(x: u128) -> u32 {
    if x <= 1 {
        0
    } else {
        128 - (x - 1).leading_zeros()
    }
}

impl WordLattice {
    /// **The rule** (module header): from the finest receiver grain `L_R`, the receiving fan-in
    /// `X_w`, the widest local solve `w` and the junction steps `e_max`.
    pub fn by_rule(grain: u64, fan_in: u64, width: u64, steps: u64) -> Self {
        // A quarter of the grain over the word's reads: 4 L_R X_w e_max.
        let reach = 4u128
            .saturating_mul(u128::from(grain.max(1)))
            .saturating_mul(u128::from(fan_in.max(1)))
            .saturating_mul(u128::from(steps.max(1)));
        // The solve's deviation on its operand's scale, 2wδ.
        let target = ceil_log2(
            reach
                .saturating_mul(2)
                .saturating_mul(u128::from(width.max(1))),
        );
        Self {
            chart: 2 * target,
            target,
            transient: ceil_log2(reach.saturating_mul(u128::from(SPLITS))),
        }
    }

    /// Precisions as declared: `L_c`, `D_c`, `L_w`.
    pub const fn new(chart: u32, target: u32, transient: u32) -> Self {
        Self {
            chart,
            target,
            transient,
        }
    }

    /// `L_c`.
    pub fn chart_exponent(&self) -> u32 {
        self.chart
    }

    /// `D_c`: the target is `2^(−D_c)`.
    pub fn target_exponent(&self) -> u32 {
        self.target
    }

    /// `L_w`.
    pub fn transient_exponent(&self) -> u32 {
        self.transient
    }

    /// The charts' lattice `2^(−L_c)ℤ`.
    pub fn chart(&self) -> Lattice {
        Lattice::new(self.chart)
    }

    /// The transients' lattice `2^(−L_w)ℤ`.
    pub fn transient(&self) -> Lattice {
        Lattice::new(self.transient)
    }

    /// The certificate's target `δ = 2^(−D_c)`.
    pub fn target(&self) -> Rat {
        Rat::new(BigInt::one(), BigInt::one() << self.target as usize)
    }
}

// -------------------------------------------------------------------------------------------
// the chart

/// [definition] **A lattice chart's coordinates**: `rows × columns` signed 64-bit words `Q`,
/// row-major, the chart being `Q·2^(−exponent)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartWords {
    rows: usize,
    columns: usize,
    exponent: u32,
    words: Vec<i64>,
}

fn carrier(what: &'static str) -> HnnError {
    HnnError::Carrier { what }
}

/// An exact ratio as a signed 64-bit word, or the carrier's refusal.
fn word(value: &BigInt, what: &'static str) -> Result<i64, HnnError> {
    value.to_i64().ok_or_else(|| carrier(what))
}

/// **An operand's integral chart in the carrier**: its entries as signed 64-bit words over one
/// positive denominator, or the carrier's refusal.
fn operand(vector: &[Rat]) -> Result<(Vec<i64>, BigInt), HnnError> {
    let (numerators, denominator) = integral(vector);
    let words = numerators
        .iter()
        .map(|n| word(n, "an operand's coordinate beyond the 64-bit word"))
        .collect::<Result<Vec<i64>, HnnError>>()?;
    Ok((words, denominator))
}

/// `Σ_j q_j x_j` under the ℓ1 certificate: admitted when `Σ_j |q_j x_j| < 2^127`.
fn certified_dot(pairs: impl Iterator<Item = (i128, i128)>) -> Result<i128, HnnError> {
    let (mut bound, mut sum) = (0u128, 0i128);
    for (q, x) in pairs {
        if q == 0 || x == 0 {
            continue;
        }
        let magnitude = q
            .unsigned_abs()
            .checked_mul(x.unsigned_abs())
            .ok_or_else(|| carrier("a product's ℓ1 certificate at 2^127"))?;
        bound = bound
            .checked_add(magnitude)
            .filter(|b| *b < CARRIER)
            .ok_or_else(|| carrier("a product's ℓ1 certificate at 2^127"))?;
        // |sum| ≤ bound < 2^127: every partial sum is a word of the carrier.
        sum += q * x;
    }
    Ok(sum)
}

impl ChartWords {
    /// A chart from its coordinates, each refused past the 64-bit word.
    pub(crate) fn of_coordinates(
        rows: usize,
        columns: usize,
        exponent: u32,
        coordinates: &[BigInt],
    ) -> Result<Self, HnnError> {
        let words = coordinates
            .iter()
            .map(|q| word(q, "a chart coordinate beyond the 64-bit word"))
            .collect::<Result<Vec<i64>, HnnError>>()?;
        Ok(Self {
            rows,
            columns,
            exponent,
            words,
        })
    }

    /// **The lattice chart of an exact matrix** (Lean `latticeChart`): every entry at its nearest
    /// point of `2^(−exponent)ℤ`, ties upward.
    pub fn of_matrix(matrix: &ExactRatMatrix, exponent: u32) -> Result<Self, HnnError> {
        let lattice = Lattice::new(exponent);
        let coordinates: Vec<BigInt> = matrix
            .entries()
            .iter()
            .map(|entry| lattice.div_rem(entry).0)
            .collect();
        Self::of_coordinates(matrix.rows(), matrix.columns(), exponent, &coordinates)
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn columns(&self) -> usize {
        self.columns
    }

    /// The lattice exponent `L`: the chart is `Q·2^(−L)`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// The coordinates `Q`, row-major.
    pub fn words(&self) -> &[i64] {
        &self.words
    }

    fn scale(&self) -> BigInt {
        BigInt::one() << self.exponent as usize
    }

    /// The chart's entry `Q_ij·2^(−L)`, exactly.
    pub fn entry(&self, row: usize, column: usize) -> Rat {
        Rat::new(
            BigInt::from(self.words[row * self.columns + column]),
            self.scale(),
        )
    }

    /// The chart as an exact matrix.
    pub fn to_matrix(&self) -> Result<ExactRatMatrix, HnnError> {
        Ok(ExactRatMatrix::shaped(
            self.rows,
            self.columns,
            (0..self.rows)
                .map(|i| (0..self.columns).map(|j| self.entry(i, j)).collect())
                .collect(),
        )?)
    }

    /// The chart's bits: each word's magnitude bits and its sign, a reading.
    pub fn bits(&self) -> u64 {
        self.words
            .iter()
            .map(|w| u64::from(64 - w.unsigned_abs().leading_zeros()) + 1)
            .sum()
    }

    /// **`X̂ x`**, exactly: the operand's integral chart against the coordinates, each entry an
    /// integer sum under the ℓ1 certificate, read over `2^L · D`.
    pub fn apply(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        if vector.len() != self.columns {
            return Err(HnnError::Shape {
                what: "a chart's operand",
                expected: self.columns,
                found: vector.len(),
            });
        }
        let (x, denominator) = operand(vector)?;
        let scale = self.scale() * denominator;
        (0..self.rows)
            .map(|i| {
                let row = &self.words[i * self.columns..(i + 1) * self.columns];
                let sum = certified_dot(
                    row.iter()
                        .zip(&x)
                        .map(|(q, x)| (i128::from(*q), i128::from(*x))),
                )?;
                Ok(Rat::new(BigInt::from(sum), scale.clone()))
            })
            .collect()
    }

    /// **`X̂ᵀ λ`**, exactly: the executed adjoint (Lean `executed_adjoint_unique`), each entry an
    /// integer sum under the ℓ1 certificate.
    pub fn apply_transpose(&self, vector: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        if vector.len() != self.rows {
            return Err(HnnError::Shape {
                what: "a transposed chart's operand",
                expected: self.rows,
                found: vector.len(),
            });
        }
        let (x, denominator) = operand(vector)?;
        let scale = self.scale() * denominator;
        (0..self.columns)
            .map(|j| {
                let sum = certified_dot((0..self.rows).map(|i| {
                    (
                        i128::from(self.words[i * self.columns + j]),
                        i128::from(x[i]),
                    )
                }))?;
                Ok(Rat::new(BigInt::from(sum), scale.clone()))
            })
            .collect()
    }
}

// -------------------------------------------------------------------------------------------
// the operator in integers

/// A square operator `A = Ā/D` as its integer coordinates over one positive denominator.
struct Operator {
    n: usize,
    entries: Vec<i128>,
    denominator: i128,
}

impl Operator {
    fn of(matrix: &ExactRatMatrix) -> Result<Self, HnnError> {
        let (numerators, denominator) = integral(matrix.entries());
        let as_word = |value: &BigInt| {
            value
                .to_i128()
                .ok_or_else(|| carrier("an operator's coordinate beyond the 128-bit word"))
        };
        Ok(Self {
            n: matrix.rows(),
            entries: numerators.iter().map(as_word).collect::<Result<_, _>>()?,
            denominator: as_word(&denominator)?,
        })
    }

    /// `S = D·2^L`, the scale of `A X̂`.
    fn scale(&self, exponent: u32) -> Result<i128, HnnError> {
        1i128
            .checked_shl(exponent)
            .filter(|unit| *unit > 0)
            .and_then(|unit| unit.checked_mul(self.denominator))
            .ok_or_else(|| carrier("the certificate's scale D·2^L_c beyond the 128-bit word"))
    }

    /// `Ā Q`, each entry under the ℓ1 certificate.
    fn times(&self, chart: &ChartWords) -> Result<Vec<i128>, HnnError> {
        let n = self.n;
        let mut product = Vec::with_capacity(n * n);
        for i in 0..n {
            let row = &self.entries[i * n..(i + 1) * n];
            for j in 0..n {
                product.push(certified_dot(
                    (0..n).map(|k| (row[k], i128::from(chart.words[k * n + j]))),
                )?);
            }
        }
        Ok(product)
    }

    /// `S·1 − Ā Q` at scale `1/S`: the right residual's integer coordinates.
    fn residual(&self, chart: &ChartWords) -> Result<(Vec<i128>, i128), HnnError> {
        let scale = self.scale(chart.exponent)?;
        let mut residual = self.times(chart)?;
        for (index, entry) in residual.iter_mut().enumerate() {
            let diagonal = if index / self.n == index % self.n {
                scale
            } else {
                0
            };
            *entry = diagonal
                .checked_sub(*entry)
                .ok_or_else(|| carrier("a residual's coordinate beyond the 128-bit word"))?;
        }
        Ok((residual, scale))
    }
}

/// **The certificate** `δ = ‖1 − A X̂‖∞` (Lean `rowNorm`), exact: the largest absolute row sum of
/// the right residual's integer coordinates, over their scale.
fn certificate_of(operator: &Operator, chart: &ChartWords) -> Result<Rat, HnnError> {
    let (residual, scale) = operator.residual(chart)?;
    let n = operator.n;
    let mut largest = 0u128;
    for i in 0..n {
        let mut sum = 0u128;
        for entry in &residual[i * n..(i + 1) * n] {
            sum = sum
                .checked_add(entry.unsigned_abs())
                .ok_or_else(|| carrier("a certificate's row sum beyond the 128-bit word"))?;
        }
        largest = largest.max(sum);
    }
    Ok(Rat::new(BigInt::from(largest), BigInt::from(scale)))
}

/// **The certificate of a chart of `A⁻¹`**: `‖1 − A X̂‖∞`, exact.
pub fn certificate(matrix: &ExactRatMatrix, chart: &ChartWords) -> Result<Rat, HnnError> {
    certificate_of(&Operator::of(matrix)?, chart)
}

/// `⌊(2n + d)/(2d)⌋` for `d > 0`: the nearest integer to `n/d`, ties upward.
fn nearest(numerator: i128, denominator: i128) -> Result<i128, HnnError> {
    let twice = numerator
        .checked_mul(2)
        .and_then(|n| n.checked_add(denominator))
        .ok_or_else(|| carrier("a refinement's rounding beyond the 128-bit word"))?;
    let divisor = denominator
        .checked_mul(2)
        .ok_or_else(|| carrier("a refinement's rounding beyond the 128-bit word"))?;
    Ok(twice.div_euclid(divisor))
}

/// **One rounded Newton–Schulz step** (Lean `nsStep` then `latticeChart`): `X(2 − AX)` in integers
/// at scale `1/(D·2^(2L_c))`, rounded to `2^(−L_c)ℤ`, ties upward.
fn newton_schulz(operator: &Operator, chart: &ChartWords) -> Result<ChartWords, HnnError> {
    let n = operator.n;
    let (residual, scale) = operator.residual(chart)?;
    // 2S·1 − ĀQ = S·1 + (S·1 − ĀQ).
    let mut twice = residual;
    for i in 0..n {
        twice[i * n + i] = twice[i * n + i]
            .checked_add(scale)
            .ok_or_else(|| carrier("a refinement's coordinate beyond the 128-bit word"))?;
    }
    let mut words = Vec::with_capacity(n * n);
    for i in 0..n {
        let row = &chart.words[i * n..(i + 1) * n];
        for j in 0..n {
            let sum = certified_dot((0..n).map(|k| (i128::from(row[k]), twice[k * n + j])))?;
            let rounded = nearest(sum, scale)?;
            words.push(
                i64::try_from(rounded)
                    .map_err(|_| carrier("a chart coordinate beyond the 64-bit word"))?,
            );
        }
    }
    Ok(ChartWords {
        rows: n,
        columns: n,
        exponent: chart.exponent,
        words,
    })
}

/// **One rounded Newton–Schulz step** of a chart of `A⁻¹` (Lean `nsStep`, then `latticeChart`):
/// `X(2 − AX)` in integers, rounded to the chart's lattice, ties upward. The host's value of the
/// step a device kernel computes.
pub fn newton_schulz_step(
    matrix: &ExactRatMatrix,
    chart: &ChartWords,
) -> Result<ChartWords, HnnError> {
    newton_schulz(&Operator::of(matrix)?, chart)
}

/// [definition] **Where a window's refinement started**: the chart the last window left (warm),
/// Newton–Schulz from the scaled transpose `2^(−p)Aᵀ` (cold), or one exact inverse, rounded (the
/// fallback when neither reaches the certified regime).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChartStart {
    Warm,
    Transpose,
    Exact,
}

/// [definition] **What a chart's refinement reports**: the chart's key and width, its certificate
/// against the target, where it started, and the rounded Newton–Schulz steps it took this window
/// (the cold start's included).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReading {
    pub key: ChartKey,
    pub width: usize,
    pub certificate: Rat,
    pub target: Rat,
    pub steps: u32,
    pub start: ChartStart,
}

/// [definition] **Which operator a chart inverts**: a ring's `I − ½K_r`, or a contact's `m_a` at the
/// carry `n_a` of its conductance (the contact's operator moves with `G_a = 2^(n_a) Y_a`, so each
/// carry keeps its own chart, moved only by deposits).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChartKey {
    Ring(usize),
    Contact { contact: usize, carry: BigInt },
}

/// `⌈log₂(a/b)⌉` of a positive ratio of integers.
fn ceil_log2_ratio(numerator: &BigInt, denominator: &BigInt) -> i64 {
    // The least e with a ≤ b·2^e.
    let mut exponent = numerator.bits() as i64 - denominator.bits() as i64 - 1;
    let fits = |e: i64| {
        if e >= 0 {
            numerator <= &(denominator << e as usize)
        } else {
            (numerator << (-e) as usize) <= *denominator
        }
    };
    while !fits(exponent) {
        exponent += 1;
    }
    while fits(exponent - 1) {
        exponent -= 1;
    }
    exponent
}

impl Operator {
    /// **The scaled transpose** `2^(−p)Aᵀ` on the chart's lattice, with `2^p ≥ ‖A‖₁‖A‖∞ ≥ ‖A‖₂²`,
    /// and the cold phase's step bound `k = p + ⌈log₂(1 + ⌈log₂ n⌉)⌉ + 1`.
    ///
    /// [definition; agent-inferred] The right residual `1 − 2^(−p)AAᵀ` is symmetric with spectrum in
    /// `[0, 1 − 2^(−p)σ_min²]`, and every operator the word inverts has `σ_min ≥ 1` by passivity
    /// (module header), so `k` exact refinements leave `‖R_k‖₂ ≤ (1 − 2^(−p))^(2^k) ≤
    /// exp(−2^(k−p))` and `‖R_k‖∞ ≤ √n‖R_k‖₂ ≤ 1/2` once `2^(k−p) ≥ log₂(2√n)`; one step more
    /// absorbs the roundings (each at most `‖A‖∞ n 2^(−L_c)/2`).
    fn transpose_start(&self, exponent: u32) -> Result<(ChartWords, u32), HnnError> {
        let n = self.n;
        let (mut rows, mut columns) = (0u128, 0u128);
        for i in 0..n {
            let (mut row, mut column) = (0u128, 0u128);
            for j in 0..n {
                row = row.saturating_add(self.entries[i * n + j].unsigned_abs());
                column = column.saturating_add(self.entries[j * n + i].unsigned_abs());
            }
            rows = rows.max(row);
            columns = columns.max(column);
        }
        let product = BigInt::from(rows) * BigInt::from(columns);
        let square = BigInt::from(self.denominator) * BigInt::from(self.denominator);
        let power = ceil_log2_ratio(&product.max(BigInt::one()), &square).max(0) as u32;
        // (2^(−p)Aᵀ)_ij = Ā_ji 2^(L_c − p)/D, at its nearest lattice point, ties upward.
        let shift = i64::from(exponent) - i64::from(power);
        let mut words = Vec::with_capacity(n * n);
        for i in 0..n {
            for j in 0..n {
                let entry = BigInt::from(self.entries[j * n + i]);
                let (top, bottom) = if shift >= 0 {
                    (entry << shift as usize, BigInt::from(self.denominator))
                } else {
                    (entry, BigInt::from(self.denominator) << (-shift) as usize)
                };
                // ⌊(2t + b)/(2b)⌋, b > 0: the nearest integer to t/b, ties upward.
                let (twice, divisor) = ((&top << 1usize) + &bottom, &bottom << 1usize);
                let mut rounded = &twice / &divisor;
                if (&twice % &divisor).is_negative() {
                    rounded -= 1;
                }
                words.push(word(&rounded, "a chart coordinate beyond the 64-bit word")?);
            }
        }
        // k = p + ⌈log₂(1 + ⌈log₂ n⌉)⌉ + 1.
        let width_bits = u64::from(ceil_log2(n.max(1) as u128));
        let bound = power + ceil_log2(u128::from(1 + width_bits)) + 1;
        Ok((
            ChartWords {
                rows: n,
                columns: n,
                exponent,
                words,
            },
            bound,
        ))
    }
}

/// **Refine a chart of `A⁻¹` to the declared target** (module header): warm-started from `start`
/// when it has the operator's shape and lattice and its certificate is at most `1/2` (the
/// certified regime, `roundedIter_certificate` at `c = 1/2`); otherwise cold, by rounded
/// Newton–Schulz steps from the scaled transpose until the certificate is at most `1/2`
/// (the scaled transpose's step bound); and if that bound passes, from one exact inverse,
/// rounded. Then rounded Newton–Schulz steps until the certificate is at most `δ`, each lowering
/// it; a step that does not is refused.
pub fn refine(
    key: ChartKey,
    matrix: &ExactRatMatrix,
    start: Option<&ChartWords>,
    lattice: &WordLattice,
) -> Result<(ChartWords, ChartReading), HnnError> {
    let n = matrix.rows();
    let exponent = lattice.chart_exponent();
    let operator = Operator::of(matrix)?;
    let target = lattice.target();
    let half = Rat::new(BigInt::one(), BigInt::from(2));
    let warm = start
        .filter(|chart| chart.rows == n && chart.columns == n && chart.exponent == exponent)
        .map(|chart| certificate_of(&operator, chart).map(|delta| (chart.clone(), delta)))
        .transpose()?
        .filter(|(_, delta)| *delta <= half);
    let mut steps = 0u32;
    let (mut chart, mut delta, begun) = match warm {
        Some((chart, delta)) => (chart, delta, ChartStart::Warm),
        None => {
            let (mut chart, bound) = operator.transpose_start(exponent)?;
            let mut delta = certificate_of(&operator, &chart)?;
            while delta > half && steps < bound {
                chart = newton_schulz(&operator, &chart)?;
                delta = certificate_of(&operator, &chart)?;
                steps += 1;
            }
            if delta <= half {
                (chart, delta, ChartStart::Transpose)
            } else {
                let chart = ChartWords::of_matrix(&matrix.inverse()?, exponent)?;
                let delta = certificate_of(&operator, &chart)?;
                (chart, delta, ChartStart::Exact)
            }
        }
    };
    while delta > target {
        let next = newton_schulz(&operator, &chart)?;
        let next_delta = certificate_of(&operator, &next)?;
        if next_delta >= delta {
            return Err(HnnError::ChartCertificate {
                chart: key,
                certificate: Box::new(next_delta),
                target: Box::new(target),
            });
        }
        chart = next;
        delta = next_delta;
        steps += 1;
    }
    Ok((
        chart,
        ChartReading {
            key,
            width: n,
            certificate: delta,
            target,
            steps,
            start: begun,
        },
    ))
}

// -------------------------------------------------------------------------------------------
// the charts a resident keeps

/// [definition; agent-inferred] **The executed charts a resident keeps between windows**: the last
/// chart of each ring's `(I − ½K_r)⁻¹` and each contact's `m_a⁻¹` per conductance carry, the start
/// of the next window's refinement (the warm start). A chart is a function of its operator only
/// through its certificate: every window re-certifies it against the published constitution and
/// refines it when the certificate is above the target, so a read at an unchanged operator returns
/// the same chart. The charts are the executed operators' representation, like the constitution's
/// solved charts, so the resident counts their bits ([`Charts::bits`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Charts {
    charts: BTreeMap<ChartKey, ChartWords>,
}

impl Charts {
    /// No chart yet: every first refinement is seeded.
    pub fn new() -> Self {
        Self::default()
    }

    pub fn get(&self, key: &ChartKey) -> Option<&ChartWords> {
        self.charts.get(key)
    }

    pub(crate) fn insert(&mut self, key: ChartKey, chart: ChartWords) {
        self.charts.insert(key, chart);
    }

    /// The charts kept.
    pub fn len(&self) -> usize {
        self.charts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.charts.is_empty()
    }

    /// Their bits, a reading.
    pub fn bits(&self) -> u64 {
        self.charts.values().map(ChartWords::bits).sum()
    }
}

// -------------------------------------------------------------------------------------------
// the carried transient

/// **Error feedback at the transients' lattice** (Lean `feedback_tick`): each image plus its
/// carried remainder is split at the nearest point of the lattice, ties upward; the remainders are
/// replaced by the new ones and the carried values returned, `x + r' = y + r` entry by entry.
pub fn carry(lattice: &Lattice, image: &[Rat], remainder: &mut [Rat]) -> Vec<Rat> {
    image
        .iter()
        .zip(remainder.iter_mut())
        .map(|(y, r)| {
            let (quotient, rest) = lattice.div_rem(&(y + &*r));
            *r = rest;
            Rat::from_integer(quotient) * lattice.unit()
        })
        .collect()
}

/// [definition] **Released remainders, read**: how many are nonzero, the largest in magnitude, their
/// ℓ1 sum and their exact bits (each by its numerator's and denominator's bits). The word releases
/// its forward remainders at its end and the return its adjoint remainders at the open; neither is
/// carried to another word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Remainders {
    pub entries: u64,
    pub largest: Rat,
    pub total: Rat,
    pub bits: u64,
}

impl Default for Remainders {
    fn default() -> Self {
        Self {
            entries: 0,
            largest: Rat::zero(),
            total: Rat::zero(),
            bits: 0,
        }
    }
}

impl Remainders {
    /// Read a family of released remainders.
    pub fn of<'a>(values: impl IntoIterator<Item = &'a Rat>) -> Self {
        let mut read = Self::default();
        for value in values {
            if value.is_zero() {
                continue;
            }
            let magnitude = value.abs();
            read.entries += 1;
            read.bits += value.numer().bits() + value.denom().bits();
            read.total += &magnitude;
            if magnitude > read.largest {
                read.largest = magnitude;
            }
        }
        read
    }

    /// Two readings joined.
    pub fn join(&self, other: &Self) -> Self {
        Self {
            entries: self.entries + other.entries,
            largest: if other.largest > self.largest {
                other.largest.clone()
            } else {
                self.largest.clone()
            },
            total: &self.total + &other.total,
            bits: self.bits + other.bits,
        }
    }
}
