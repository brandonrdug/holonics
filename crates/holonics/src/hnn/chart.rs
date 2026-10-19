//! **The word on declared lattices: certified inverse charts and carried transients** (the lattice word;
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
//! grows past `c` (`roundedIter_certificate`). An epoch's read **warm-starts** from the chart the
//! last epoch left for the same operator, since a deposit moves `A` by `D_A` and the start's
//! residual grows by at most `‖D_A‖∞‖X̂‖∞` (`warm_start_certificate`); the warm start is taken when
//! that certificate is at most `1/2`, the certified regime ([`ChartStart::Warm`]).
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
//! ([`HnnError::Carrier`]). Under that bound every partial sum, in any order, lies in
//! `(−2^127, 2^127)`, so the 128-bit ring read is the integer sum (Lean
//! `HNN/LatticeWord.{carrier_partial_sum, carrier_ring_read}`). An operand enters a product as its integral chart (integers over one
//! denominator, `crate::ratio::linear::vector::integral`): a carried transient on `2^(−L_w)ℤ` is
//! its coordinates over `2^(L_w)`.
//!
//! [definition; representation extension] `ChartWords::apply` and its transpose retain that
//! single-word read and its exact refusal for operands whose integral coordinates all fit i64.
//! Wider operands are signed radix-2^32 limbs. Each limb separately satisfies the same primitive
//! certificate; BigInt reconstruction computes `Q n = Σ_k 2^(32k) Q n_k` exactly. The assembled
//! wide product is NOT asserted to satisfy the original whole-operand bound. No chart coordinate,
//! tolerance or rounding law changes. Host operator refinement also uses these limbs when exact
//! scale, entry, residual or Newton product bounds exceed the single-word representation. The
//! choice precedes the products; all primitive limb dots retain the strict bound above. Chart
//! coordinates and the refinement order remain unchanged. Cost is proportional to the limb count; allocation
//! extents are checked. The shared host response tube uses this representation on both backends;
//! direct CUDA lattice mounting remains i64-limited and is not extended here.
//! [open] The limb reconstruction identity's Lean counterpart remains owed in #62.
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
//! | `rowNorm` (the certificate), `warm_start_certificate`, `inverse_chart_deviation` | [`certificate`], [`Charts`] (the warm start), [`WordLattice::by_rule`] |
//! | `feedback_tick`, `feedback_accounting_zero`, `carried_word_accounting` | [`carry`], [`Remainders`] |
//! | `executed_adjoint_pairing`, `executed_adjoint_unique` | [`ChartWords::apply_transpose`] |
//! | `carrier_partial_sum`, `carrier_ring_read` | `certified_dot` (the ℓ1 certificate) |
//! | `foldl_certify`, `Reduction.{bound_eq, order_free, refused_iff, read_of_bound_lt}` | `certified_dot` (the certificate's order-free refusal) |
//!
//! [open] Owed in #62 (Lean): the scaled transpose's convergence (`σ_min ≥ 1` by passivity) is an
//! efficiency claim only, since every certificate is computed exactly and the exact inverse is the
//! fallback.

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

/// An exact operand, retaining the existing single-word path whenever every coordinate fits.
/// [definition; representation extension] Wider coordinates are signed radix-2^32 limbs, each read
/// under the existing integer-dot certificate. Reconstruction is exact BigInt arithmetic:
/// `Q n = Σ_k 2^(32k) Q n_k`. This extends operand representation, not chart coordinates,
/// tolerance, or any individual limb's carrier certificate.
struct Operand {
    limbs: Vec<Vec<i64>>,
    denominator: BigInt,
}

fn operand(vector: &[Rat]) -> Result<Operand, HnnError> {
    let (numerators, denominator) = integral(vector);
    if let Some(words) = numerators
        .iter()
        .map(ToPrimitive::to_i64)
        .collect::<Option<Vec<_>>>()
    {
        return Ok(Operand {
            limbs: vec![words],
            denominator,
        });
    }
    Operand::from_integers(&numerators, denominator)
}

impl Operand {
    /// Force signed radix-2^32 limbs for an operator product; each dot keeps the primitive bound.
    fn from_integers(numerators: &[BigInt], denominator: BigInt) -> Result<Self, HnnError> {
        let count = numerators
            .iter()
            .map(|n| n.bits().div_ceil(32))
            .max()
            .unwrap_or(0);
        let count = usize::try_from(count).map_err(|_| carrier("operand limb count"))?;
        checked_limb_extent(count, numerators.len())?;
        // Borrow the existing digits; do not allocate a second copy before validating the extent.
        let mut digits = Vec::new();
        digits
            .try_reserve_exact(numerators.len())
            .map_err(|_| carrier("operand digit iterators"))?;
        digits.extend(numerators.iter().map(|n| (n.sign(), n.iter_u32_digits())));
        let mut limbs = Vec::new();
        limbs
            .try_reserve_exact(count)
            .map_err(|_| carrier("operand limb allocation"))?;
        for _ in 0..count {
            let mut limb = Vec::new();
            limb.try_reserve_exact(numerators.len())
                .map_err(|_| carrier("operand limb allocation"))?;
            for (sign, digits) in &mut digits {
                let digit = i64::from(digits.next().unwrap_or(0));
                limb.push(if *sign == num_bigint::Sign::Minus {
                    -digit
                } else {
                    digit
                });
            }
            limbs.push(limb);
        }
        Ok(Operand { limbs, denominator })
    }
}

fn checked_limb_extent(count: usize, width: usize) -> Result<(), HnnError> {
    count
        .checked_mul(width)
        .and_then(|n| n.checked_mul(std::mem::size_of::<i64>()))
        .filter(|bytes| *bytes <= isize::MAX as usize)
        .ok_or_else(|| carrier("operand limb allocation extent"))?;
    Ok(())
}

/// Check the actual element size, then reserve before building an operator workspace.
fn checked_workspace_extent<T>(length: usize) -> Result<(), HnnError> {
    length
        .checked_mul(std::mem::size_of::<T>())
        .filter(|bytes| *bytes <= isize::MAX as usize)
        .ok_or_else(|| carrier("operator workspace extent"))?;
    Ok(())
}

fn workspace<T>(length: usize) -> Result<Vec<T>, HnnError> {
    checked_workspace_extent::<T>(length)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(length)
        .map_err(|_| carrier("operator workspace allocation"))?;
    Ok(values)
}

impl Operand {
    fn dot(&self, mut coefficients: impl FnMut(usize) -> i64) -> Result<BigInt, HnnError> {
        let mut sum = BigInt::zero();
        for limb in self.limbs.iter().rev() {
            let partial = certified_dot(
                limb.iter()
                    .enumerate()
                    .map(|(j, x)| (i128::from(coefficients(j)), i128::from(*x))),
            )?;
            sum = (sum << 32usize) + BigInt::from(partial);
        }
        Ok(sum)
    }
}

/// `Σ_j q_j x_j` under the ℓ1 certificate: admitted when `Σ_j |q_j x_j| < 2^127`, so every partial
/// sum is a word of the carrier (`carrier_partial_sum`, `carrier_ring_read`). The running bound is
/// the certificate's left comb (`foldl_certify`): it refuses at the first prefix that reaches
/// `2^127`, which is exactly when the whole sum of magnitudes does, so its refusals are the card's
/// block tree's (`Reduction.order_free`, `Reduction.refused_iff`).
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
    /// A chart from its coordinates, each refused past the 64-bit word. Public for a realization
    /// that refines the chart off the host and returns its coordinates.
    pub fn of_coordinates(
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
        let operand = operand(vector)?;
        let scale = self.scale() * &operand.denominator;
        (0..self.rows)
            .map(|i| {
                let row = &self.words[i * self.columns..(i + 1) * self.columns];
                let sum = operand.dot(|j| row[j])?;
                Ok(Rat::new(sum, scale.clone()))
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
        let operand = operand(vector)?;
        let scale = self.scale() * &operand.denominator;
        (0..self.columns)
            .map(|j| {
                let sum = operand.dot(|i| self.words[i * self.columns + j])?;
                Ok(Rat::new(sum, scale.clone()))
            })
            .collect()
    }
}

// -------------------------------------------------------------------------------------------
// the operator in integers

/// A square operator `A = Ā/D` as its integer coordinates over one positive denominator.
struct Operator {
    n: usize,
    entries: Vec<BigInt>,
    narrow_entries: Option<Vec<i128>>,
    denominator: BigInt,
    // Transient diagnostics only; never part of a chart or checkpoint.
    wide_reasons: std::cell::Cell<u16>,
}

/// Why the host selected limb products before executing an operator refinement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OperatorWideReason {
    Entry,
    Scale,
    Product,
    Residual,
    CertificateRow,
    RefinementProduct,
    Rounding,
}

/// Exact widths of the operator reached by this read, rather than a backend capability claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OperatorReading {
    pub key: ChartKey,
    pub width: usize,
    pub denominator_bits: u64,
    pub scale_bits: u64,
    pub entry_bits: u64,
    pub wide_reasons: Vec<OperatorWideReason>,
}

impl Operator {
    fn of(matrix: &ExactRatMatrix) -> Result<Self, HnnError> {
        let n = matrix.rows();
        let extent = n
            .checked_mul(n)
            .ok_or_else(|| carrier("operator square extent"))?;
        checked_workspace_extent::<BigInt>(extent)?;
        if matrix.columns() != n || matrix.entries().len() != extent {
            return Err(carrier("a non-square inverse operator"));
        }
        let (entries, denominator) = integral(matrix.entries());
        let narrow_entries = if entries.iter().all(|x| x.to_i128().is_some()) {
            let mut words = workspace(entries.len())?;
            words.extend(
                entries
                    .iter()
                    .map(|x| x.to_i128().expect("checked integer coordinate")),
            );
            Some(words)
        } else {
            None
        };
        Ok(Self {
            n,
            entries,
            narrow_entries,
            denominator,
            wide_reasons: std::cell::Cell::new(0),
        })
    }

    fn validate_chart(&self, chart: &ChartWords) -> Result<(), HnnError> {
        if chart.rows != self.n
            || chart.columns != self.n
            || chart.words.len() != self.entries.len()
        {
            return Err(HnnError::Unadmitted {
                reason: "an inverse chart outside its operator shape",
            });
        }
        Ok(())
    }

    fn scale(&self, exponent: u32) -> BigInt {
        &self.denominator << exponent as usize
    }

    fn wide(&self, reason: OperatorWideReason) -> bool {
        self.wide_reasons
            .set(self.wide_reasons.get() | (1 << reason as u16));
        false
    }

    /// Select the representation from structural absolute bounds BEFORE a primitive is run.
    /// Row-l1(Abar)*max|Q| bounds every product dot independently of cancellation.
    fn narrow(&self, chart: &ChartWords, newton: bool) -> bool {
        let max = BigInt::from(i128::MAX);
        let carrier = BigInt::one() << 127usize;
        if self.narrow_entries.is_none() {
            return self.wide(OperatorWideReason::Entry);
        }
        let scale = self.scale(chart.exponent);
        if scale > max {
            return self.wide(OperatorWideReason::Scale);
        }
        let qmax = chart
            .words
            .iter()
            .map(|x| BigInt::from(*x).abs())
            .max()
            .unwrap_or_default();
        let mut product = BigInt::zero();
        let mut qrow = BigInt::zero();
        for i in 0..self.n {
            let row = self.entries[i * self.n..(i + 1) * self.n]
                .iter()
                .map(Signed::abs)
                .sum::<BigInt>();
            product = product.max(row * &qmax);
            qrow = qrow.max(
                chart.words[i * self.n..(i + 1) * self.n]
                    .iter()
                    .map(|x| BigInt::from(*x).abs())
                    .sum(),
            );
        }
        if product >= carrier {
            return self.wide(OperatorWideReason::Product);
        }
        let residual = &scale + &product;
        if residual > max {
            return self.wide(OperatorWideReason::Residual);
        }
        if &residual * self.n > BigInt::from(u128::MAX) {
            return self.wide(OperatorWideReason::CertificateRow);
        }
        if newton {
            let twice = (&scale << 1usize) + product;
            if twice > max {
                return self.wide(OperatorWideReason::RefinementProduct);
            }
            let bound = qrow * twice;
            if bound >= carrier {
                return self.wide(OperatorWideReason::RefinementProduct);
            }
            if (&bound << 1usize) + &scale > max || (&scale << 1usize) > max {
                return self.wide(OperatorWideReason::Rounding);
            }
        }
        true
    }

    fn reading(&self, key: ChartKey, exponent: u32) -> OperatorReading {
        let reasons = [
            OperatorWideReason::Entry,
            OperatorWideReason::Scale,
            OperatorWideReason::Product,
            OperatorWideReason::Residual,
            OperatorWideReason::CertificateRow,
            OperatorWideReason::RefinementProduct,
            OperatorWideReason::Rounding,
        ];
        OperatorReading {
            key,
            width: self.n,
            denominator_bits: self.denominator.bits(),
            scale_bits: self.scale(exponent).bits(),
            entry_bits: self.entries.iter().map(BigInt::bits).max().unwrap_or(0),
            wide_reasons: reasons
                .into_iter()
                .filter(|r| self.wide_reasons.get() & (1 << *r as u16) != 0)
                .collect(),
        }
    }

    fn residual_narrow(&self, chart: &ChartWords) -> Result<(Vec<i128>, i128), HnnError> {
        let scale = self
            .scale(chart.exponent)
            .to_i128()
            .expect("preflight scale");
        let mut residual = workspace(self.entries.len())?;
        for i in 0..self.n {
            for j in 0..self.n {
                let sum = certified_dot((0..self.n).map(|k| {
                    (
                        self.narrow_entries.as_ref().expect("preflight entries")[i * self.n + k],
                        i128::from(chart.words[k * self.n + j]),
                    )
                }))?;
                residual.push(if i == j { scale - sum } else { -sum });
            }
        }
        Ok((residual, scale))
    }

    fn residual_wide(&self, chart: &ChartWords) -> Result<(Vec<BigInt>, BigInt), HnnError> {
        let scale = self.scale(chart.exponent);
        let mut residual = workspace(self.entries.len())?;
        for i in 0..self.n {
            let row =
                Operand::from_integers(&self.entries[i * self.n..(i + 1) * self.n], BigInt::one())?;
            for j in 0..self.n {
                let sum = row.dot(|k| chart.words[k * self.n + j])?;
                residual.push(if i == j { &scale - sum } else { -sum });
            }
        }
        Ok((residual, scale))
    }
}

/// **The certificate** `δ = ‖1 − A X̂‖∞` (Lean `rowNorm`), exact: the largest absolute row sum of
/// the right residual's integer coordinates, over their scale.
fn certificate_of(operator: &Operator, chart: &ChartWords) -> Result<Rat, HnnError> {
    operator.validate_chart(chart)?;
    if operator.n == 0 {
        return Ok(Rat::zero());
    }
    if operator.narrow(chart, false) {
        let (residual, scale) = operator.residual_narrow(chart)?;
        let largest = residual
            .chunks(operator.n)
            .map(|row| row.iter().map(|x| x.unsigned_abs()).sum::<u128>())
            .max()
            .unwrap_or(0);
        Ok(Rat::new(BigInt::from(largest), BigInt::from(scale)))
    } else {
        let (residual, scale) = operator.residual_wide(chart)?;
        let largest = residual
            .chunks(operator.n)
            .map(|row| row.iter().map(Signed::abs).sum::<BigInt>())
            .max()
            .unwrap_or_default();
        Ok(Rat::new(largest, scale))
    }
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

/// The identical ties-up quotient in an exact integer representation (division truncates at zero).
fn nearest_wide(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let top = (numerator << 1usize) + denominator;
    let bottom = denominator << 1usize;
    let mut quotient = &top / &bottom;
    if (&top % &bottom).is_negative() {
        quotient -= 1;
    }
    quotient
}

/// **One rounded Newton–Schulz step** (Lean `nsStep` then `latticeChart`): `X(2 − AX)` in integers
/// at scale `1/(D·2^(2L_c))`, rounded to `2^(−L_c)ℤ`, ties upward.
fn newton_schulz(operator: &Operator, chart: &ChartWords) -> Result<ChartWords, HnnError> {
    operator.validate_chart(chart)?;
    let n = operator.n;
    if !operator.narrow(chart, true) {
        let (mut twice, scale) = operator.residual_wide(chart)?;
        for i in 0..n {
            twice[i * n + i] += &scale;
        }
        let mut words = workspace(operator.entries.len())?;
        words.resize(operator.entries.len(), 0i64);
        for j in 0..n {
            let mut column = workspace(n)?;
            column.extend((0..n).map(|k| twice[k * n + j].clone()));
            let operand = Operand::from_integers(&column, BigInt::one())?;
            for i in 0..n {
                let sum = operand.dot(|k| chart.words[i * n + k])?;
                words[i * n + j] = word(
                    &nearest_wide(&sum, &scale),
                    "a chart coordinate beyond the 64-bit word",
                )?;
            }
        }
        return Ok(ChartWords {
            rows: n,
            columns: n,
            exponent: chart.exponent,
            words,
        });
    }
    let (residual, scale) = operator.residual_narrow(chart)?;
    // 2S·1 − ĀQ = S·1 + (S·1 − ĀQ).
    let mut twice = residual;
    for i in 0..n {
        twice[i * n + i] = twice[i * n + i]
            .checked_add(scale)
            .ok_or_else(|| carrier("a refinement's coordinate beyond the 128-bit word"))?;
    }
    let mut words = workspace(operator.entries.len())?;
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
#[cfg(test)]
pub(crate) fn newton_schulz_step(
    matrix: &ExactRatMatrix,
    chart: &ChartWords,
) -> Result<ChartWords, HnnError> {
    newton_schulz(&Operator::of(matrix)?, chart)
}

/// [definition] **Where an epoch's refinement started**: the chart the last epoch left (warm),
/// Newton–Schulz from the scaled transpose `2^(−p)Aᵀ` (cold), or one exact inverse, rounded (the
/// fallback when neither reaches the certified regime).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChartStart {
    /// The same immutable batch producer supplied this already certified ring solve.
    Reused,
    Warm,
    Transpose,
    Exact,
}

/// [definition] **What a chart's refinement reports**: the chart's key and width, its certificate
/// against the target, where it started, and the rounded Newton–Schulz steps it took in this
/// epoch's read (the cold start's included).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReading {
    pub key: ChartKey,
    pub width: usize,
    pub certificate: Rat,
    pub target: Rat,
    pub steps: u32,
    pub start: ChartStart,
    /// Transient host operator diagnostics; absent on owners that do not provide them.
    /// On Reused this records the original preparation's width and wide reasons; it
    /// does not claim any new operator arithmetic happened in the reused call.
    pub operator: Option<OperatorReading>,
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
        let (mut rows, mut columns) = (BigInt::zero(), BigInt::zero());
        for i in 0..n {
            let row = (0..n)
                .map(|j| self.entries[i * n + j].abs())
                .sum::<BigInt>();
            let column = (0..n)
                .map(|j| self.entries[j * n + i].abs())
                .sum::<BigInt>();
            rows = rows.max(row);
            columns = columns.max(column);
        }
        let product = rows * columns;
        let square = &self.denominator * &self.denominator;
        let power = u32::try_from(ceil_log2_ratio(&product.max(BigInt::one()), &square).max(0))
            .map_err(|_| carrier("transpose start exponent"))?;
        // (2^(−p)Aᵀ)_ij = Ā_ji 2^(L_c − p)/D, at its nearest lattice point, ties upward.
        let shift = i64::from(exponent) - i64::from(power);
        let mut words = workspace(self.entries.len())?;
        for i in 0..n {
            for j in 0..n {
                let entry = self.entries[j * n + i].clone();
                let (top, bottom) = if shift >= 0 {
                    (entry << shift as usize, self.denominator.clone())
                } else {
                    (entry, self.denominator.clone() << (-shift) as usize)
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
        let bound = power
            .checked_add(ceil_log2(u128::from(1 + width_bits)))
            .and_then(|k| k.checked_add(1))
            .ok_or_else(|| carrier("transpose start step bound"))?;
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

/// **The cold start of a chart of `A⁻¹`**: the scaled transpose `2^(−p)Aᵀ` on the chart's lattice
/// `2^(−exponent)ℤ` and the cold phase's step bound `p + ⌈log₂(1 + ⌈log₂ n⌉)⌉ + 1` ([`refine`]'s
/// own start). Public for a realization that refines the chart off the host from the same start.
pub fn transpose_start(
    matrix: &ExactRatMatrix,
    exponent: u32,
) -> Result<(ChartWords, u32), HnnError> {
    Operator::of(matrix)?.transpose_start(exponent)
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
            key: key.clone(),
            width: n,
            certificate: delta,
            target,
            steps,
            start: begun,
            operator: Some(operator.reading(key.clone(), exponent)),
        },
    ))
}

// -------------------------------------------------------------------------------------------
// the charts a resident keeps

/// [definition; agent-inferred] **The executed charts a resident keeps between epochs**: the last
/// chart of each ring's `(I − ½K_r)⁻¹` and each contact's `m_a⁻¹` per conductance carry, the start
/// of the next epoch's refinement (the warm start). A chart is a function of its operator only
/// through its certificate: every epoch's read re-certifies it against the published constitution
/// and refines it when the certificate is above the target, so a read at an unchanged operator
/// returns the same chart. The charts are the executed operators' representation, like the
/// constitution's solved charts, so the resident counts their bits ([`Charts::bits`]).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Charts {
    charts: BTreeMap<ChartKey, ChartWords>,
}

impl Charts {
    /// No chart yet: every first refinement is seeded.
    pub fn new() -> Self {
        Self::default()
    }

    /// Import kept charts from another realization without translating through text.
    ///
    /// This is the checked counterpart to [`Charts::read`]: it preserves each exact key and
    /// `ChartWords` value and refuses malformed shapes or duplicate keys. A realization should
    /// still validate that the keys and chart exponents belong to its declared field/material.
    pub fn from_entries(
        entries: impl IntoIterator<Item = (ChartKey, ChartWords)>,
    ) -> Result<Self, HnnError> {
        let mut charts = BTreeMap::new();
        for (key, chart) in entries {
            let Some(expected) = chart.rows.checked_mul(chart.columns) else {
                return Err(HnnError::Unadmitted {
                    reason: "a kept chart whose shape overflows its coordinate count",
                });
            };
            if expected != chart.words.len() {
                return Err(HnnError::Shape {
                    what: "a kept chart's words against its shape",
                    expected,
                    found: chart.words.len(),
                });
            }
            if charts.insert(key, chart).is_some() {
                return Err(HnnError::Unadmitted {
                    reason: "duplicate kept chart keys",
                });
            }
        }
        Ok(Self { charts })
    }

    /// Check that every persisted chart names a solve of this field and its declared word grid.
    pub fn validate_for(&self, field: &crate::hnn::field::Field) -> Result<(), HnnError> {
        if self.is_empty() {
            return Ok(());
        }
        let Some(lattice) = field.word_lattice() else {
            return Err(HnnError::Unadmitted {
                reason: "kept charts on a field without a declared word lattice",
            });
        };
        for (key, chart) in &self.charts {
            let width = match key {
                ChartKey::Ring(ring) => field.rings().get(*ring).map(|ring| ring.width()),
                ChartKey::Contact { contact, .. } => field
                    .contacts()
                    .get(*contact)
                    .map(|contact| contact.width()),
            }
            .ok_or(HnnError::Unadmitted {
                reason: "a kept chart key outside its field",
            })?;
            if chart.rows != width || chart.columns != width {
                return Err(HnnError::Shape {
                    what: "a kept chart's dimensions against its field operator",
                    expected: width,
                    found: chart.rows.max(chart.columns),
                });
            }
            if chart.exponent != lattice.chart_exponent() {
                return Err(HnnError::Shape {
                    what: "a kept chart's exponent against the field word lattice",
                    expected: lattice.chart_exponent() as usize,
                    found: chart.exponent as usize,
                });
            }
        }
        Ok(())
    }

    pub fn get(&self, key: &ChartKey) -> Option<&ChartWords> {
        self.charts.get(key)
    }

    /// The keys of the charts kept, in order.
    pub fn keys(&self) -> impl Iterator<Item = &ChartKey> {
        self.charts.keys()
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

    /// [definition; agent-inferred, October 4; the reception carry §10] **The charts' text**, a part
    /// of a continuing state (the next epoch's refinements start from them): `charts n`, then per
    /// chart its key (`ring g` or `contact a n_a`) with `rows columns exponent`, and its words on
    /// one line.
    pub fn write(&self, s: &mut String) {
        *s += &format!("charts {}\n", self.charts.len());
        for (key, chart) in &self.charts {
            match key {
                ChartKey::Ring(ring) => *s += &format!("ring {ring}"),
                ChartKey::Contact { contact, carry } => *s += &format!("contact {contact} {carry}"),
            }
            *s += &format!(" {} {} {}\n", chart.rows, chart.columns, chart.exponent);
            crate::hnn::state_text::line(s, "words", &chart.words);
        }
    }

    /// **The charts read back from their text** ([`Charts::write`]); refused, typed, on any line out
    /// of its form or a chart whose words are not `rows × columns`.
    pub fn read<'a>(
        head: &str,
        next: crate::hnn::state_text::Next<'_, 'a>,
    ) -> Result<Self, HnnError> {
        use crate::hnn::state_text::{keyed, refused, value, values};
        let what = "the charts";
        let count: usize = value(keyed(head, "charts", what)?.first(), what)?;
        let mut charts = Vec::with_capacity(count);
        for _ in 0..count {
            let words: Vec<&str> = next("a chart's key")?.split_whitespace().collect();
            let (key, shape) = match words.first().copied() {
                Some("ring") if words.len() == 5 => {
                    (ChartKey::Ring(value(words.get(1), what)?), &words[2..])
                }
                Some("contact") if words.len() == 6 => (
                    ChartKey::Contact {
                        contact: value(words.get(1), what)?,
                        carry: value(words.get(2), what)?,
                    },
                    &words[3..],
                ),
                _ => return refused("a chart's key"),
            };
            let (rows, columns, exponent): (usize, usize, u32) = (
                value(shape.first(), what)?,
                value(shape.get(1), what)?,
                value(shape.get(2), what)?,
            );
            let words: Vec<i64> = values(&keyed(next("a chart's words")?, "words", what)?, what)?;
            if Some(words.len()) != rows.checked_mul(columns) {
                return refused("a chart's words against its shape");
            }
            charts.push((
                key,
                ChartWords {
                    rows,
                    columns,
                    exponent,
                    words,
                },
            ));
        }
        Self::from_entries(charts)
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

#[cfg(test)]
mod witness {
    use super::*;
    use crate::ratio::{integer, rat};

    #[test]
    fn wide_ties_up_and_signed_limbs_preserve_exact_integer_algebra() {
        for (n, d, want) in [
            (-3, 2, -1),
            (-2, 3, -1),
            (-1, 2, 0),
            (-5, 2, -2),
            (1, 2, 1),
            (0, 3, 0),
        ] {
            assert_eq!(
                nearest_wide(&BigInt::from(n), &BigInt::from(d)),
                BigInt::from(want)
            );
            assert_eq!(nearest(n, d).unwrap(), want);
        }
        let big: BigInt = (BigInt::one() << 173usize) + 17;
        let entries = [big.clone(), -big.clone(), BigInt::zero(), BigInt::from(-1)];
        let op = Operand::from_integers(&entries, BigInt::one()).unwrap();
        assert_eq!(op.dot(|_| 3).unwrap(), BigInt::from(-3));
        // The representation never relaxes the per-limb certificate.
        assert!(matches!(
            certified_dot([(i128::MAX, 2)].into_iter()),
            Err(HnnError::Carrier { .. })
        ));
    }

    #[test]
    fn wide_entry_selection_and_workspace_extents_are_checked() {
        let a = ExactRatMatrix::shaped(
            1,
            1,
            vec![vec![Rat::from_integer(BigInt::one() << 140usize)]],
        )
        .unwrap();
        let operator = Operator::of(&a).unwrap();
        let chart = ChartWords::of_coordinates(1, 1, 0, &[BigInt::zero()]).unwrap();
        assert_eq!(certificate_of(&operator, &chart).unwrap(), Rat::one());
        assert_eq!(newton_schulz(&operator, &chart).unwrap(), chart);
        let read = operator.reading(ChartKey::Ring(3), 0);
        assert_eq!(read.entry_bits, 141);
        assert_eq!(read.wide_reasons, vec![OperatorWideReason::Entry]);
        assert!(checked_workspace_extent::<BigInt>(usize::MAX).is_err());
        assert!(checked_limb_extent(usize::MAX, 2).is_err());
    }

    /// **Two certified charts of one operator can split one image into different representatives**
    /// (the October 8 trace of the carry-chain regressions). The word's face reads the junction's
    /// carried representatives (`Word::anchor`), never their remainders, and a representative is the
    /// chart's image split at the transients' lattice ([`carry`]), so the read is not invariant
    /// under the choice among certified charts: where a chart puts an image exactly on a tie of the
    /// transients' lattice (ties upward) and another certified chart of the same operator puts it one
    /// chart unit below, the two representatives differ by one transient unit. This is why the
    /// resident's kept charts are a retained operand. The read through them is the law's, and the
    /// retention quotient must not merge residents that differ only in their charts, while a chain
    /// whose images straddle no tie reads them equal (the regressions' printed separation count).
    #[test]
    fn two_certified_charts_of_one_operator_split_one_image_differently() {
        let lattice = WordLattice::new(28, 12, 12);
        let entries = |rows: [[i64; 2]; 2]| -> Vec<Vec<Rat>> {
            rows.iter()
                .map(|row| row.iter().map(|&x| integer(x)).collect())
                .collect()
        };
        let operator_matrix = ExactRatMatrix::shaped(2, 2, entries([[3, 1], [1, 2]])).unwrap();
        let operator = Operator::of(&operator_matrix).unwrap();
        let target = lattice.target();
        // The rounded exact inverse, certified at the target.
        let exact = ChartWords::of_matrix(
            &operator_matrix.inverse().unwrap(),
            lattice.chart_exponent(),
        )
        .unwrap();
        assert!(certificate_of(&operator, &exact).unwrap() <= target);
        // A second certified chart of the same operator: its first coordinate one chart unit lower.
        let mut coordinates: Vec<BigInt> = exact
            .words()
            .iter()
            .map(|&word| BigInt::from(word))
            .collect();
        coordinates[0] -= BigInt::one();
        let other =
            ChartWords::of_coordinates(2, 2, lattice.chart_exponent(), &coordinates).unwrap();
        assert!(certificate_of(&operator, &other).unwrap() <= target);
        assert_ne!(exact, other);
        // A right side whose first image under the first chart lies exactly on a tie of the
        // transients' lattice: X̂₀₀ s = u/2 with u = 2^(−L_w).
        let transients = lattice.transient();
        let tie = transients.unit() * rat(1, 2);
        let right = vec![&tie / exact.entry(0, 0), Rat::zero()];
        let image = |chart: &ChartWords| chart.to_matrix().unwrap().apply(&right).unwrap();
        let (first, second) = (image(&exact), image(&other));
        assert_eq!(first[0], tie);
        assert!(second[0] < tie);
        let (mut kept, mut cold) = (vec![Rat::zero(); 2], vec![Rat::zero(); 2]);
        let read_kept = carry(&transients, &first, &mut kept);
        let read_cold = carry(&transients, &second, &mut cold);
        // Ties upward: the first reads one transient unit, the second zero.
        assert_eq!(read_kept[0], transients.unit());
        assert!(read_cold[0].is_zero());
        assert_ne!(read_kept, read_cold);
        // Each split is exact: representative plus remainder is the chart's image.
        for (read, (rest, image)) in [
            (&read_kept, (&kept, &first)),
            (&read_cold, (&cold, &second)),
        ] {
            for i in 0..2 {
                assert_eq!(&read[i] + &rest[i], image[i].clone());
            }
        }
    }
}

/// A same-return cotangent chart refinement, chosen from the actual transported seed groups.
/// Each nonzero group's largest coordinate is resolved at the declared unit-scale precision.
/// This changes no forward Word operand, phase, sample, or next-Word carry. It is not an exact
/// adjoint certificate: the executed return still releases its measured rounding residual.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnPrecision {
    declared: Option<Lattice>,
    lattice: Option<Lattice>,
    levels: u32,
    seed_groups: usize,
    smallest_nonzero_group_peak: Rat,
}
impl ReturnPrecision {
    pub fn for_seeds(declared: Option<Lattice>, seeds: &[Vec<Rat>]) -> Result<Self, HnnError> {
        let peaks: Vec<Rat> = seeds
            .iter()
            .filter_map(|seed| {
                seed.iter()
                    .map(Signed::abs)
                    .max()
                    .filter(|peak| !peak.is_zero())
            })
            .collect();
        let smallest = peaks.iter().min().cloned().unwrap_or_else(Rat::zero);
        let mut levels = 0;
        if declared.is_some() && !smallest.is_zero() && smallest < Rat::one() {
            let difference = smallest
                .denom()
                .bits()
                .saturating_sub(smallest.numer().bits());
            levels = u32::try_from(difference).map_err(|_| HnnError::CountOverflow)?;
            if (smallest.numer() << levels as usize) < *smallest.denom() {
                levels = levels.checked_add(1).ok_or(HnnError::CountOverflow)?;
            }
        }
        let lattice = declared
            .map(|at| {
                at.exponent()
                    .checked_add(levels)
                    .map(Lattice::new)
                    .ok_or(HnnError::CountOverflow)
            })
            .transpose()?;
        Ok(Self {
            declared,
            lattice,
            levels,
            seed_groups: peaks.len(),
            smallest_nonzero_group_peak: smallest,
        })
    }
    pub fn levels(&self) -> u32 {
        self.levels
    }
    pub fn lattice(&self) -> Option<Lattice> {
        self.lattice
    }
    pub fn declared_lattice(&self) -> Option<Lattice> {
        self.declared
    }
    pub fn seed_groups(&self) -> usize {
        self.seed_groups
    }
    pub fn smallest_nonzero_group_peak(&self) -> &Rat {
        &self.smallest_nonzero_group_peak
    }
}

#[cfg(test)]
mod operand_limb_regression {
    use super::*;
    use crate::ratio::linear::vector::dot;

    #[test]
    fn captured_arrival_operand_is_exact_in_forward_and_adjoint() {
        let ns: [i128; 22] = [
            -3152519739158986752,
            -9295429630893613056,
            -3851478401327464448,
            -7867972387360907101,
            -4424336273928904704,
            -13521607521218011136,
            -1268213655067500544,
            -7842752229447360349,
            756604737398726656,
            -13679417346519949149,
            -1877100324688297984,
            -8840749906873024349,
            -8517207615284600832,
            -5529703460830994269,
            6243790523386748928,
            -5786224801245626368,
            3429941476205330432,
            -3228180212899053568,
            -162129586585346048,
            -3177739897072533504,
            -3242591731706773504,
            -4712566650080591872,
        ];
        let d = BigInt::one() << 68usize;
        let v: Vec<_> = ns
            .into_iter()
            .map(|n| Rat::new(BigInt::from(n), d.clone()))
            .collect();
        let parsed = operand(&v).unwrap();
        assert_eq!(parsed.limbs.len(), 2);
        let words: Vec<i64> = (0..22 * 22).map(|i| (i as i64 % 17) - 8).collect();
        let chart = ChartWords {
            rows: 22,
            columns: 22,
            exponent: 7,
            words,
        };
        let oracle = chart.to_matrix().unwrap();
        assert_eq!(chart.apply(&v).unwrap(), oracle.apply(&v).unwrap());
        let transposed = chart.apply_transpose(&v).unwrap();
        let expected: Vec<_> = (0..22)
            .map(|j| {
                (0..22)
                    .map(|i| Rat::new(BigInt::from(chart.words[i * 22 + j]), chart.scale()) * &v[i])
                    .sum()
            })
            .collect();
        assert_eq!(transposed, expected);
        let x: Vec<_> = (0..22)
            .map(|i| Rat::from_integer(BigInt::from(i)))
            .collect();
        assert_eq!(dot(&v, &chart.apply(&x).unwrap()), dot(&transposed, &x));
    }

    #[test]
    fn ordinary_operand_and_its_dot_certificate_stay_single_word() {
        let v = vec![Rat::from_integer(BigInt::from(i64::MAX)); 3];
        assert_eq!(operand(&v).unwrap().limbs.len(), 1);
        let chart = ChartWords {
            rows: 1,
            columns: 3,
            exponent: 0,
            words: vec![i64::MAX; 3],
        };
        assert!(matches!(chart.apply(&v), Err(HnnError::Carrier { .. })));
    }
    #[test]
    fn wide_operands_reconstruct_sign_zero_and_beyond_whole_carrier() {
        assert!(checked_limb_extent(usize::MAX, 2).is_err());
        assert!(checked_limb_extent(2, usize::MAX).is_err());
        assert!(checked_limb_extent(6, 3).is_ok());
        // Intentional extended boundary: -2^63 * 2^64 = -2^127 exceeds the old
        // strict whole-dot bound, while every primitive limb remains certified.
        let chart = ChartWords {
            rows: 1,
            columns: 1,
            exponent: 0,
            words: vec![i64::MIN],
        };
        let x = vec![Rat::from_integer(BigInt::one() << 64usize)];
        assert_eq!(
            chart.apply(&x).unwrap(),
            vec![Rat::from_integer(-(BigInt::one() << 127usize))]
        );
        let chart = ChartWords {
            rows: 3,
            columns: 3,
            exponent: 7,
            words: vec![3, -4, 1, -2, 5, 0, 7, 1, -6],
        };
        let huge = (BigInt::one() << 161usize) + BigInt::from(19);
        let x = vec![
            Rat::new(huge.clone(), BigInt::from(7)),
            Rat::new(-huge, BigInt::from(11)),
            Rat::zero(),
        ];
        let oracle = chart.to_matrix().unwrap();
        assert!(operand(&x).unwrap().limbs.len() > 4);
        assert_eq!(chart.apply(&x).unwrap(), oracle.apply(&x).unwrap());
        assert_eq!(
            chart.apply_transpose(&x).unwrap(),
            oracle.transpose().unwrap().apply(&x).unwrap()
        );
    }
}
