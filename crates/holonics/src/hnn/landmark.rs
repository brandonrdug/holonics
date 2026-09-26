//! **The receiving parametron's storage as a tree of landmarks, executed on a declared dyadic
//! lattice** (Decision 28, count-only; #73).
//!
//! [definition] The computational object is the helical pair interaction; this owner is the
//! receiving parametron's storage, read as a tree of landmarks. Of the winding guide's six general
//! objects it touches three: **faces and placement** (the receiving face, read at the receiver's
//! grain), the **tower thread** (the suffix restriction: each address letter restricts to the
//! newest cell, and a cell's odometer digits descend its dyadic cell), and the **pair** (each edge
//! of an opened path compares a node's face with its child's, `R_(d→d+1) = q_(d+1)/q_d`). The
//! **helix** enters only as the chart's carry and phase (the β exponent is a carry, its mantissa
//! the phase within the octave). A tree has no two-cells, so no **cell holonomy** is claimed, and
//! the **tube** is the passage itself, one cell per tick.
//!
//! ```text
//! address    a_j = [x_(j−1), …, x_(j−D)]  newest first,  x_i = Boundary for i < 0        per cell
//! digits     a cell c emits its B = ⌈log₂|A|⌉ odometer digits; digit i is read in the tree of its
//!            dyadic cell h (its digit prefix), a forced digit (empty upper half) opens nothing
//! KT         k_s(b) = (2n_s(b) + 1)/(2n_s + 2) in half-units, b ∈ {0, 1}
//! lattice    q̂_D = ⟦k_D(0)⟧ ;  q̂_d = ⟦λ̂_d k_d(0) + (1 − λ̂_d) q̂_(d+1)⟧ ;  λ̂_d = ⟦β_d/(1 + β_d)⟧₀¹
//!            ⟦x⟧ = nearest multiple of 2^(−M_p) (ties up) inside [2^(−M_p), 1 − 2^(−M_p)]
//! split      (q̂_0, 1 − q̂_0) at each opened digit;  cell face = ∏ of its digits' splits
//! deposit    β'_d = β_d k_d(b)/q̂_(d+1)(b) bottom-up (the lattice face), then n_d(b) += 1
//! ```
//!
//! [definition] **Typed address letters** ([`Letter`]): `Boundary` (before the cut's first cell)
//! and `Cell(code)`. The address of cell `j` is its preceding `D` cells, newest first, read per
//! cell: causal, with no window pooling ([`address`]). A letter's code is `0` for the boundary and
//! `1 + code` for a cell.
//!
//! [definition] **The emission is the cell's odometer digits.** Digit `i` of class `c` is read at
//! its joint address: its digit prefix (the dyadic cell it descends) as a forced split, then the
//! context letters mixed by the tree of that dyadic cell, each node holding binary KT masses in
//! half-units. A dyadic cell whose upper half holds no class of the chart forces its digit with
//! face 1 and stores nothing, so every `|A| ≥ 2` is normalized. The whole-cell emission
//! (`|A|`-ary masses at each node) is retired: on the standing cut it never earned a split (the
//! record of September 26), and its depth-one forced case, Decision 27's region table, keeps its
//! law in Lean (`HNN/LandmarkTree.depth_one_is_decision_27`).
//!
//! [definition; agent-inferred, the primary's law] **Every quantity on the hot path is a
//! fixed-width integer on a declared dyadic lattice, with certified residuals, and the executed
//! face stays exactly normalized.** Each path face is a numerator of `2^(−M_p)` (`u64`), each stop
//! weight `λ̂` likewise, each count a half-unit integer (`u32`), each `β` an odd/odd ratio of `W`
//! bits with a binary exponent, and every product and quotient is formed in `u128`. The face is
//! positive and normalized for any `λ̂ ∈ [0, 1]` (`path_face_normalized`,
//! `lattice_path_laws`): the digit's executed split is `(q̂_0, 1 − q̂_0)`, and a cell's face is the
//! width of its descended interval (`cell_faces_partition`), a dyadic of at most `B · M_p` bits.
//!
//! [proved-derived; agent-inferred] **The widths**, derived from the passage `n*`, the grain `L_R`,
//! the digits `B` and the depth `D` (no literal is tuned). Write `K = 2n* + 2` (a binary KT face is
//! at least `1/K`, `digit_face_ge`), `ε = 2^(−M_p−1)` and `μ̂ = ⌊2^(M_p)/K⌋/2^(M_p)` (every lattice
//! face is at least `μ̂`, `lattice_path_floor`: rounding to nearest never crosses the lattice point
//! below a convex combination of values at least `1/K`). Let `ρ_d` be `|ln q̂_d − ln q_d|` for the ideal tree
//! weighting `q`, `Δ_d = |ln β̂_d − ln β_d|` the chart's drift at the node, and `θ_d` a level's
//! rounding in `ln` (the stop weight's and the face's, at most `2^(−M_p)/min(q̂_d, k_d, q̂_(d+1))`,
//! the leaf's `ε/min(q̂_D, k_D)`).
//! - **Down the path**, `ρ_d ≤ Δ_d + ρ_(d+1) + θ_d` (`mix_ratio_bound`: the mixture
//!   `(βk + q)/(1 + β)` moves by at most the factors by which `β` and `q` move), so
//!   `ρ_0 ≤ Σ_(d<D) Δ_d + (2D + 1) ε/μ̂`; in absolute terms `|q̂_0 − q_0| ≤ (D + 1)ε + Σ|λ̂ − λ|`
//!   (`lattice_path_deviation`).
//! - **Over the passage**, `β̂ = E/P̂` with `P̂` the executed child's sequential probability, so the
//!   node's step telescopes (`lattice_step_telescope`) and its weight is 1-Lipschitz in `ln P̂`
//!   (`weight_log_lipschitz`): the drift is bounded by the rounding and rebases **summed over the
//!   subtree**, never compounded, `Δ_d ≤ n_s (2(D − d) − 1)(ε/μ̂ + 2^(1−W))` with `n_s ≤ n*` the
//!   node's arrivals and `2^(1−W)` a rebase's `|ln(1 − r)|` (`rebase_log_residual`).
//! - **A cell** has at most `B` opened digits and `Σ_(d<D) (2(D − d) − 1) = D²`, so
//!   `|log₂ q̂ − log₂ q| ≤ (3/2) B [(n* D² + 2D + 1) ε/μ̂ + n* D² 2^(1−W)]` (`log₂ e < 3/2`).
//!   Each of the two sources is held within a quarter grain:
//!   - `M_p` is the least `M` with `2^M ≥ 3 B L_R K (n* D² + 2D + 1)` ([`face_bits`]);
//!   - `W` is the least width with `2^W ≥ 12 B L_R n* D²` ([`carrier_width`]);
//!   - the certificates are summed on the grid `2^(−C)`, `C = M_p + W`: every rounding term is at
//!     least `2^(−M_p)` and every rebase term at least `2^(−W)`, so rounding each up on the grid
//!     inflates it by at most `1 + 2^(−min(M_p, W))`.
//!
//!   At the standing cut (`n* = 6,148 = 2²·29·53`, `L_R = 16`, `B = 8`, `D = 4`): `M_p = 39`,
//!   `W = 28`, `C = 67`; the rule's bound per cell ([`Landmarks::face_rule`]) is below half a grain.
//!   Every product above then fits `u128` (the declaration is refused otherwise).
//!
//! [definition] **The certificate is carried, not recomputed** (the per-cell residual without the
//! ideal). Each node carries two bounds on the grid `2^(−C)`: `drift` ≥ `Δ` and `excess` ≥
//! `|L̂ − L|`, its routed subsequence's executed code length against the ideal in `ln`. A deposit
//! adds, bottom-up along the opened path, the read's `θ_d` plus twice the rebase's `1/m'` to the
//! node's excess and the child's excess increment plus the rebase's `1/m'` to its drift
//! (`|ln(1 − r)| ≤ r/(1 − r) < 1/m'` for the kept mantissa `m' ∈ [2^(W−1), 2^W)`). A read's
//! residual is `ρ_0 ≤ Σ drift + Σ θ` per opened digit, and a cell's ([`CellReading::residual`]) is
//! the digits' sum in `log₂` (times `3/2`), never above the rule.
//!
//! [definition; agent-inferred] **The arena** (the layout the card ports). Nodes are founded at
//! first arrival and numbered in founding order, `u32`; every per-node value is a flat vector
//! indexed by the node: its depth and its two half-unit masses `2C_0, 2C_1` (their sum is the
//! total; the arena the oracle shares), and its chart: `β`, the cached stop weight `λ̂`, its
//! rebases and its two certificates. `roots[h]` is the root of the tree at dyadic cell `h` (the heap
//! index `2^i + prefix`), and `children` a hash table from `(parent << 32) | letter code` to the
//! child. An unfounded node reads as the prior: a path read stops at its first unfounded node, whose
//! face is exactly `1/2`. `Clone` copies the arena, linear in the founded nodes (about a hundred
//! bytes a node with its table entry: at the standing cut's 63,320 nodes a few megabytes, about a
//! millisecond), and `PartialEq` compares the table as a map (std's `HashMap`).
//!
//! [definition] **Faces.** [`Landmarks::probability`] is one class's executed face, exact;
//! [`Landmarks::face`] all classes with their grain exponents, `Σ_c q̂(c) = 1` exactly: the face the
//! receiving read and the card consume. It reads each splitting dyadic cell's path once, bounded by
//! its splitting ancestor's founded depth (a node founded in a dyadic cell's tree is founded in its
//! ancestors'), multiplies the splits down the dyadic heap, and decides each grain exponent
//! `⌊L_R log₂ q̂⌋` by a certified binary logarithm (exact integer squaring, [`binary_log`]) with
//! the exact comparison (`grain_exponent`) as its fallback.
//!
//! [definition; agent-inferred] **The ideal tree weighting is a reference oracle**
//! ([`IdealLandmarks`]): the same arena with `β` in ℚ and every face exact, consumed by the tests
//! and by the notebook's report of the executed face's cost. It is never on the hot path. Over the
//! standing cut an exact `β` reaches about `10^5` bits a node (the KT mass of thousands of routed
//! cells) and each face a sum of such, so at scale the oracle carries `β` at the reference width
//! `W_o = O + ⌈log₂(3 B n*² D²)⌉` ([`IdealLandmarks::reference_width`], `O` the enclosure grid's
//! octaves), whose rebases keep its code length within `2^(−O)` of the ideal over the whole
//! passage. On the tests it carries `β` exactly.
//!
//! [definition; agent-inferred] **The depth** `D` is chosen on the development cells only
//! ([`choose_depth`]): `D` increases from `max(1, forced)` while the development prequential code
//! length decreases strictly (disjoint exact enclosures), every `D` tried is reported, and `⌈log₂⌉`
//! of the family tried is charged as description bits. The held-out cells never choose anything.
//!
//! [definition; agent-inferred, from the retention and deposition laws] **The measurement is
//! prequential** ([`prequential`], Decision 29): every cell is scored at the current standing
//! before its own deposit, then deposited, for the tree and the online baselines alike. The tree's
//! faces and the oracle's are read by [`code_length`], `log₂ d − log₂ n` of `q = n/d` by the
//! certified binary logarithm ([`binary_log`]) within the enclosure grid `2^(−O)`, microseconds
//! even on the oracle's faces of thousands of bits; the baselines read their own faces through
//! `hnn::ratio::log2_enclosure` (`hnn::reference`), a series of milliseconds a face. Both are
//! certified enclosures of `−log₂ q`, and every ordering is decided by disjoint enclosures.
//!
//! [definition; agent-inferred] **The host realization** (the hardware law). Within
//! [`prequential`] the tree and the baselines run together: each reads the shared immutable cut
//! and writes only its own state and sums, so their effects commute and every value is the serial
//! one. Within one tree the cells stay serial: they share mutable counts along their paths.
//!
//! | Law | Lean `HNN/LandmarkTree` | Rust |
//! |---|---|---|
//! | the typed suffix address; an unfounded node reads the prior, and founding at first arrival keeps the law | `unfounded_reads_prior`, `founded_tree_same_law` | [`Letter`], [`address`], [`Landmarks::deposit`] |
//! | the path face is positive and normalized for any `λ ∈ [0, 1]`; on the lattice too | `path_face_normalized`, `lattice_path_laws` | [`Landmarks::face`], [`Landmarks::probability`] |
//! | the lattice path's floor, and its absolute deviation adding down the path | `lattice_path_floor`, `lattice_path_deviation` | [`face_bits`] |
//! | the mixture moves by at most the factors of `β` and of the child's face | `mix_ratio_bound` | [`CellReading::residual`] |
//! | the likelihood-ratio step of β, the opened-path update, and its executed telescope with a rebase | `weight_step`, `landmark_step`, `lattice_step_telescope`, `lattice_node_telescope`, `weight_log_lipschitz` | [`Landmarks::deposit`], [`ChartReport`] |
//! | a rebase's residual | `rebase_log_residual` | [`Beta::carry`], [`carrier_width`] |
//! | the telescope on an opened path | `path_telescope_exact` | [`OpenedPath::edge_ratios`] |
//! | the executed dyadic split and the cells' partition; the forced digits when `\|A\| < 2^B` | `executed_split_laws`, `cell_faces_partition`, `forced_digits_normalized` | [`Landmarks::probability`], [`Landmarks::face`] |
//! | a digit face's floor and the rounding's residual (the first-order bound fails downward) | `digit_face_ge`, `digit_log_residual`, `host_digit_bound_fails_downward` | [`Landmarks::face_rule`] |
//! | the ideal tree weighting (the oracle) | `landmark_step`, `mixture_is_probability`, `kraft_and_dominance` | [`IdealLandmarks`] |
//!
//! [open] Owed in #62 (Lean `HNN/LandmarkTree`'s `[open]`): the passage-level composition of the
//! drift bound (the subtree sum over the tree and the passage, from `lattice_node_telescope`,
//! `weight_log_lipschitz` and `mix_ratio_bound`) into the per-cell rule, and the certified binary
//! logarithm's squaring invariant; both are checked by the tests, the first cell by cell against
//! the oracle on the standing cut.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::compression::cost::ceil_log2;
use crate::hnn::HnnError;
use crate::hnn::ratio::{LOG_OCTAVES, interval_sum};
use crate::hnn::receiving::grain_exponent;
use crate::hnn::reference::{BaselineCodes, Baselines, Cut};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;

// -------------------------------------------------------------------------------------------
// letters and addresses

/// [definition] **A typed address letter**: the boundary before the cut's first cell, or a cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Letter {
    Boundary,
    Cell(usize),
}

impl Letter {
    /// The letter's code: `0` for the boundary, `1 + code` for a cell.
    pub fn code(self) -> u64 {
        match self {
            Letter::Boundary => 0,
            Letter::Cell(code) => 1 + code as u64,
        }
    }
}

/// [definition] **The address of cell `position`**: `[x_(j−1), …, x_(j−D)]`, newest first, with
/// `Boundary` for every position before the cut's first cell.
pub fn address(cells: &[usize], position: usize, depth: usize) -> Vec<Letter> {
    (1..=depth)
        .map(|back| {
            position
                .checked_sub(back)
                .map_or(Letter::Boundary, |at| Letter::Cell(cells[at]))
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the declaration and its derived widths

/// [definition] **A landmark tree's declaration**: the exterior chart's `|A|`, the address depth
/// `D`, the forced splits (context depths `d < forced` mix nothing, `λ_d = 0`), the declared
/// population `n*` bounding the passage, and the receiver's grain `L_R`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkDeclaration {
    pub alphabet: usize,
    pub depth: usize,
    pub forced: usize,
    pub population: u64,
    pub grain: u64,
}

/// `B = ⌈log₂|A|⌉`, the odometer digits of a cell.
pub fn odometer_digits(alphabet: usize) -> u64 {
    ceil_log2(&BigUint::from(alphabet))
}

/// `K = 2n* + 2`: a binary KT face after at most `n*` arrivals is at least `1/K`.
fn floor_reciprocal(population: u64) -> BigUint {
    BigUint::from(population) * 2u32 + 2u32
}

/// [definition; agent-inferred] **The path lattice's width** `M_p`: the least `M` with
/// `2^M ≥ 3 B L_R (2n* + 2)(n* D² + 2D + 1)`, which holds the lattice's rounding within a quarter
/// grain a cell (module header, "The widths").
pub fn face_bits(population: u64, digits: u64, grain: u64, depth: u64) -> u64 {
    let (n, d) = (BigUint::from(population), BigUint::from(depth));
    let terms = &n * &d * &d + &d * 2u32 + 1u32;
    ceil_log2(
        &(BigUint::from(3u32)
            * BigUint::from(digits)
            * BigUint::from(grain)
            * floor_reciprocal(population)
            * terms),
    )
}

/// [definition; agent-inferred] **The β carrier width** `W`: the least width (at least 2) with
/// `2^W ≥ 12 B L_R n* D²`, which holds the rebases' drift within a quarter grain a cell (module
/// header, "The widths").
pub fn carrier_width(population: u64, digits: u64, grain: u64, depth: u64) -> u64 {
    let d = BigUint::from(depth);
    ceil_log2(
        &(BigUint::from(12u32)
            * BigUint::from(digits)
            * BigUint::from(grain)
            * BigUint::from(population)
            * &d
            * &d),
    )
    .max(2)
}

/// [definition; agent-inferred] **The widths a declaration derives** (module header, "The
/// widths"): the digits `B`, the path lattice `M_p`, the β carrier `W` and the certificates' grid
/// `C = M_p + W`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Widths {
    pub digits: u64,
    pub face: u64,
    pub carrier: u64,
    pub certificate: u64,
}

impl Widths {
    /// The widths the rule derives from a declaration.
    pub fn derived(declaration: &LandmarkDeclaration) -> Self {
        let digits = odometer_digits(declaration.alphabet);
        let depth = declaration.depth as u64;
        let carrier = carrier_width(declaration.population, digits, declaration.grain, depth);
        Self::with_carrier(declaration, carrier)
    }

    /// The derived widths with a declared carrier `W` in place of the rule's.
    fn with_carrier(declaration: &LandmarkDeclaration, carrier: u64) -> Self {
        let digits = odometer_digits(declaration.alphabet);
        let face = face_bits(
            declaration.population,
            digits,
            declaration.grain,
            declaration.depth as u64,
        );
        Self {
            digits,
            face,
            carrier,
            certificate: face + carrier,
        }
    }

    /// The largest `u128` operand the widths ask for, in bits: the lattice mixture
    /// `2M + κ + 3`, the stop weight `2W + M + 3` and the β step's mantissa `2W + κ + M + 1`, with
    /// `κ` the bits of `2n* + 2`.
    fn operand_bits(&self, population: u64) -> u64 {
        let kappa = floor_reciprocal(population).bits();
        let (m, w) = (self.face, self.carrier);
        (2 * m + kappa + 3)
            .max(2 * w + m + 3)
            .max(2 * w + kappa + m + 1)
    }
}

/// `log₂ e < 3/2`, the constant of the certified residual (`ln 2 > 2/3`).
fn log2_e_bound() -> Rat {
    Rat::new(BigInt::from(3), BigInt::from(2))
}

fn two_power(exponent: i64) -> Rat {
    let shift = exponent.unsigned_abs() as usize;
    if exponent >= 0 {
        Rat::from_integer(BigInt::one() << shift)
    } else {
        Rat::new_raw(BigInt::one(), BigInt::one() << shift)
    }
}

/// `⌈a/b⌉` in `u128`.
fn ceil_div(a: u128, b: u128) -> u128 {
    a.div_ceil(b)
}

/// The greatest common divisor of two odd integers (binary: subtract, then shed twos).
fn odd_gcd(mut a: u128, mut b: u128) -> u128 {
    while a != b {
        if a > b {
            a -= b;
            a >>= a.trailing_zeros();
        } else {
            b -= a;
            b >>= b.trailing_zeros();
        }
    }
    a
}

fn shape(what: &'static str, expected: usize, found: usize) -> HnnError {
    HnnError::Shape {
        what,
        expected,
        found,
    }
}

// -------------------------------------------------------------------------------------------
// the β chart

/// [definition; agent-inferred] **A carried mixture ratio** `β = (numerator/denominator) · 2^exponent`,
/// numerator and denominator odd and coprime, each below `2^W` (module header, "The widths").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Beta {
    numerator: u64,
    denominator: u64,
    exponent: i64,
}

impl Beta {
    /// `β = 1`: the ratio at first arrival.
    pub const ONE: Beta = Beta {
        numerator: 1,
        denominator: 1,
        exponent: 0,
    };

    /// The carried value, exact.
    pub fn value(&self) -> Rat {
        let (mut numerator, mut denominator) =
            (BigInt::from(self.numerator), BigInt::from(self.denominator));
        let shift = self.exponent.unsigned_abs() as usize;
        if self.exponent >= 0 {
            numerator <<= shift;
        } else {
            denominator <<= shift;
        }
        // Odd coprime parts times a power of two on one side stay coprime.
        Rat::new_raw(numerator, denominator)
    }

    /// The binary exponent (the carry).
    pub fn exponent(&self) -> i64 {
        self.exponent
    }

    /// **Carry the positive ratio `(numerator/denominator) · 2^exponent` at width `W`**: its twos
    /// moved into the exponent and its odd parts reduced; exact when both fit `W` bits, otherwise
    /// rebased to its mantissa `m' = ⌊v 2^s⌋ ∈ [2^(W−1), 2^W)`, which is returned: the relative
    /// residual `r = 1 − m'/(v 2^s)` has `|ln(1 − r)| < 1/m' ≤ 2^(1−W)` (Lean
    /// `HNN/LandmarkTree.rebase_log_residual`). The operands must be positive, with
    /// `W + bits(denominator) ≤ 128`.
    pub fn carry(
        numerator: u128,
        denominator: u128,
        exponent: i64,
        width: u64,
    ) -> (Self, Option<u128>) {
        debug_assert!(numerator > 0 && denominator > 0);
        let (twos_n, twos_d) = (numerator.trailing_zeros(), denominator.trailing_zeros());
        let (mut a, mut b) = (numerator >> twos_n, denominator >> twos_d);
        let exponent = exponent + i64::from(twos_n) - i64::from(twos_d);
        let common = odd_gcd(a, b);
        (a, b) = (a / common, b / common);
        let bits = |x: u128| u64::from(u128::BITS - x.leading_zeros());
        if bits(a) <= width && bits(b) <= width {
            return (
                Self {
                    numerator: a as u64,
                    denominator: b as u64,
                    exponent,
                },
                None,
            );
        }
        // `a/b ∈ (2^(t−1), 2^(t+1))`, `t = bits(a) − bits(b)`, so `a 2^s/b ∈ (2^(W−1), 2^(W+1))`
        // at `s = W − t`.
        let floor = |shift: i64| -> u128 {
            if shift >= 0 {
                (a << shift) / b
            } else {
                a / (b << shift.unsigned_abs())
            }
        };
        let mut shift = width as i64 - (bits(a) as i64 - bits(b) as i64);
        let mut mantissa = floor(shift);
        if bits(mantissa) > width {
            shift -= 1;
            mantissa = floor(shift);
        }
        debug_assert_eq!(bits(mantissa), width);
        let twos = mantissa.trailing_zeros();
        (
            Self {
                numerator: (mantissa >> twos) as u64,
                denominator: 1,
                exponent: exponent - shift + i64::from(twos),
            },
            Some(mantissa),
        )
    }

    /// **The stop weight** `λ̂ = ⟦β/(1 + β)⟧` on the lattice `2^(−M)`, as its numerator in
    /// `[0, 2^M]` (round to nearest, ties up). At `|exponent| > M + W` the rounding is decided
    /// (`λ̂ = 1` or `0`: the other side is below half a lattice step), so every operand stays within
    /// `2W + M + 3` bits.
    pub fn stop_weight(&self, face_bits: u64, width: u64) -> u64 {
        let full = 1u64 << face_bits;
        let reach = face_bits + width + 1;
        let (a, b) = (u128::from(self.numerator), u128::from(self.denominator));
        let twice = 1u128 << (face_bits + 1);
        if self.exponent >= 0 {
            // 2^M λ = 2^M − z, z = 2^M b/g, g = a 2^e + b; ⌊2^M − z + ½⌋ = 2^M − ⌈z − ½⌉.
            if self.exponent as u64 >= reach {
                return full;
            }
            let g = (a << self.exponent) + b;
            let t = twice * b;
            let up = if t <= g { 0 } else { (t - g).div_ceil(2 * g) };
            full - up as u64
        } else {
            // 2^M λ = 2^M a/h, h = a + b 2^|e|.
            let shift = self.exponent.unsigned_abs();
            if shift >= reach {
                return 0;
            }
            let h = a + (b << shift);
            ((twice * a + h) / (2 * h)) as u64
        }
    }
}

/// [definition] **The β chart's report**: the carrier `W`, the rebases in all and at the
/// most-rebased node, and the largest drift certificate over the nodes, `|log₂ β̂ − log₂ β|` in
/// bits (the node's `drift` times `3/2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReport {
    pub carrier: u64,
    pub rebases: u64,
    pub node_rebases: u64,
    pub drift: Rat,
}

// -------------------------------------------------------------------------------------------
// the odometer and the arena

/// The dyadic chart of the alphabet: which cells split and which digits a class opens.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Odometer {
    alphabet: usize,
    digits: u64,
}

impl Odometer {
    /// Whether the dyadic cell at `level` with `prefix` holds a class.
    fn holds(&self, level: u64, prefix: usize) -> bool {
        (prefix << (self.digits - level)) < self.alphabet
    }

    /// Whether the dyadic cell at `level` with `prefix` splits: its upper half holds a class.
    fn splits(&self, level: u64, prefix: usize) -> bool {
        (((prefix << 1) | 1) << (self.digits - level - 1)) < self.alphabet
    }

    /// **The trees a class's digits open**, with its digit in each: the splitting dyadic cells of
    /// its descent (a forced digit opens nothing).
    fn emitted(&self, class: usize) -> Vec<(usize, usize)> {
        (0..self.digits)
            .filter_map(|level| {
                let prefix = class >> (self.digits - level);
                let digit = (class >> (self.digits - level - 1)) & 1;
                self.splits(level, prefix)
                    .then_some(((1usize << level) | prefix, digit))
            })
            .collect()
    }
}

/// The arena's topology and masses, shared by the executed tree and the oracle: the roots per
/// dyadic cell, the child table, each node's depth and its two half-unit masses.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Arena {
    roots: Vec<Option<u32>>,
    children: HashMap<u64, u32>,
    depths: Vec<u32>,
    halves: Vec<[u32; 2]>,
}

fn key(parent: u32, letter: Letter) -> u64 {
    (u64::from(parent) << 32) | letter.code()
}

impl Arena {
    fn new(cells: usize) -> Self {
        Self {
            roots: vec![None; cells],
            children: HashMap::new(),
            depths: Vec::new(),
            halves: Vec::new(),
        }
    }

    fn len(&self) -> usize {
        self.halves.len()
    }

    /// The founded nodes along an address in the tree at dyadic cell `h`, from its root, at most
    /// `limit` of them.
    fn open(&self, dyadic: usize, address: &[Letter], limit: usize) -> Vec<u32> {
        let mut nodes = Vec::with_capacity(address.len() + 1);
        if limit == 0 {
            return nodes;
        }
        let Some(root) = self.roots[dyadic] else {
            return nodes;
        };
        nodes.push(root);
        for letter in address {
            if nodes.len() >= limit {
                break;
            }
            match self
                .children
                .get(&key(*nodes.last().expect("a root"), *letter))
            {
                Some(&child) => nodes.push(child),
                None => break,
            }
        }
        nodes
    }

    /// `(2C_b, 2N)`, the node's KT mass of `b` and its total, in half-units.
    fn kt(&self, node: u32, symbol: usize) -> (u64, u64) {
        let [zero, one] = self.halves[node as usize];
        (
            u64::from(self.halves[node as usize][symbol]),
            u64::from(zero) + u64::from(one),
        )
    }

    fn found(&mut self, depth: usize) -> u32 {
        let node = u32::try_from(self.len()).expect("the arena is checked within 32 bits");
        self.depths
            .push(u32::try_from(depth).expect("a depth within 32 bits"));
        self.halves.push([1, 1]);
        node
    }

    /// Found the path's missing nodes (the root, then each child along the address), returning
    /// how many were founded.
    fn extend(&mut self, dyadic: usize, address: &[Letter], nodes: &mut Vec<u32>) -> usize {
        let before = self.len();
        if nodes.is_empty() {
            let root = self.found(0);
            self.roots[dyadic] = Some(root);
            nodes.push(root);
        }
        while nodes.len() < address.len() + 1 {
            let parent = *nodes.last().expect("a root");
            let child = self.found(nodes.len());
            self.children
                .insert(key(parent, address[nodes.len() - 1]), child);
            nodes.push(child);
        }
        self.len() - before
    }

    /// One arrival of `symbol` counted at the path's nodes of depth at least `forced`.
    fn count(&mut self, nodes: &[u32], forced: usize, symbol: usize) {
        for &node in nodes.iter().skip(forced) {
            self.halves[node as usize][symbol] += 2;
        }
    }

    fn founded_within(&self, nodes: usize) -> Result<(), HnnError> {
        if self.len() + nodes >= u32::MAX as usize {
            return Err(shape(
                "a landmark arena within 32-bit node numbers",
                u32::MAX as usize,
                self.len(),
            ));
        }
        Ok(())
    }
}

fn check(
    declaration: &LandmarkDeclaration,
    address: &[Letter],
    class: usize,
) -> Result<(), HnnError> {
    if address.len() != declaration.depth {
        return Err(shape(
            "an address of the declared depth",
            declaration.depth,
            address.len(),
        ));
    }
    let alphabet = declaration.alphabet;
    if class >= alphabet {
        return Err(HnnError::CellOutside {
            code: class,
            alphabet,
        });
    }
    for letter in address {
        if let Letter::Cell(code) = letter
            && *code >= alphabet
        {
            return Err(HnnError::CellOutside {
                code: *code,
                alphabet,
            });
        }
    }
    Ok(())
}

fn check_declaration(declaration: &LandmarkDeclaration) -> Result<(), HnnError> {
    if declaration.alphabet < 2 || declaration.alphabet >= u32::MAX as usize {
        return Err(shape(
            "a landmark tree over at least two classes, within 32 bits",
            2,
            declaration.alphabet,
        ));
    }
    if declaration.population == 0 || declaration.grain == 0 {
        return Err(HnnError::NonpositiveDeclaration);
    }
    if declaration.population >= u64::from(u32::MAX / 2) || declaration.grain > u64::from(u32::MAX)
    {
        return Err(shape(
            "a population whose half-unit counts and a grain that fit 32 bits",
            (u32::MAX / 2) as usize,
            usize::try_from(declaration.population).unwrap_or(usize::MAX),
        ));
    }
    if declaration.forced > declaration.depth {
        return Err(shape(
            "forced splits within the address depth",
            declaration.depth,
            declaration.forced,
        ));
    }
    Ok(())
}

// -------------------------------------------------------------------------------------------
// the executed tree

/// [definition] **One cell's reading** at the standing before its deposit: the executed face of the
/// cell, exact (a dyadic), and the certified bound on `|log₂ q̂ − log₂ q|` against the ideal tree
/// weighting, in bits (module header, "The certificate").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellReading {
    pub executed: Rat,
    pub residual: Rat,
}

/// [definition] **One opened path**: the dyadic cell `h` whose tree it descends, the digit it
/// emits there, how many of its nodes are founded, its faces `q_0, …, q_(min(f, D))` of that digit
/// (the executed lattice faces from [`Landmarks::opened`], the ideal ones from
/// [`IdealLandmarks::opened`]; the first unfounded depth reads the prior `1/2`), and at each founded
/// depth the node's KT face `k_d` of the digit and its carried `β_d`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedPath {
    pub dyadic: usize,
    pub symbol: usize,
    pub founded: usize,
    pub faces: Vec<Rat>,
    pub masses: Vec<Rat>,
    pub betas: Vec<Rat>,
}

impl OpenedPath {
    /// **The edge ratios** `R_(d→d+1) = q_(d+1)/q_d` along the path, whose logarithms are the
    /// path's additive cochain: `q_0 · Π_d R_(d→d+1) = q_f`.
    pub fn edge_ratios(&self) -> Vec<Rat> {
        self.faces
            .windows(2)
            .map(|pair| &pair[1] / &pair[0])
            .collect()
    }
}

/// [definition] **All classes' executed faces at one address**, each with its grain exponent
/// `2^(k_c) ≤ q̂(c)^(L_R) < 2^(k_c+1)`; `Σ_c q̂(c) = 1` exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkFace {
    pub grain: u64,
    pub probabilities: Vec<Rat>,
    pub exponents: Vec<BigInt>,
}

/// The executed chart of one node: its carried β, the cached stop weight `λ̂` (a numerator of
/// `2^(−M_p)`), its rebases, and its certificates on `2^(−C)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Chart {
    beta: Beta,
    stop: u64,
    rebases: u32,
    drift: u128,
    excess: u128,
}

/// One tree's executed read at an address: the founded nodes from the root, and the lattice faces
/// of the digit `0`, `q̂_d(0)` as numerators of `2^(−M_p)`, at `d = 0, …, min(f, D)` (the first
/// unfounded depth `f` reads the prior `2^(M_p − 1)`).
#[derive(Clone, Debug)]
struct LatticeRead {
    dyadic: usize,
    symbol: usize,
    nodes: Vec<u32>,
    faces: Vec<u64>,
}

/// [definition] **The landmark tree, executed** (module header): the declaration, its derived
/// widths, the arena with each node's chart, and the chart's counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Landmarks {
    declaration: LandmarkDeclaration,
    widths: Widths,
    odometer: Odometer,
    arena: Arena,
    charts: Vec<Chart>,
    rebases: u64,
    passed: u64,
}

impl Landmarks {
    /// **Declare a tree**, empty: every node unfounded, so every face is uniform. Refused at an
    /// alphabet below two classes or past 32 bits, a zero population or grain, a population or
    /// grain past 32 bits, a forced depth past the address depth, or derived widths whose
    /// operands exceed `u128`.
    pub fn new(declaration: LandmarkDeclaration) -> Result<Self, HnnError> {
        check_declaration(&declaration)?;
        let widths = Widths::derived(&declaration);
        Self::with_widths(declaration, widths)
    }

    /// **Declare a tree at a declared carrier width `W`** in place of the rule's. A width below the
    /// rule's gives up the rule's place below the grain ([`Landmarks::face_rule`] reports it); the
    /// executed face stays exactly normalized and every certificate stays valid.
    pub fn with_carrier(declaration: LandmarkDeclaration, carrier: u64) -> Result<Self, HnnError> {
        check_declaration(&declaration)?;
        let widths = Widths::with_carrier(&declaration, carrier);
        Self::with_widths(declaration, widths)
    }

    fn with_widths(declaration: LandmarkDeclaration, widths: Widths) -> Result<Self, HnnError> {
        let operands = widths.operand_bits(declaration.population);
        if !(2..=63).contains(&widths.carrier)
            || widths.face > 62
            || widths.certificate > 126
            || operands > u64::from(u128::BITS)
        {
            return Err(shape(
                "derived widths whose operands fit u128",
                u128::BITS as usize,
                usize::try_from(operands).unwrap_or(usize::MAX),
            ));
        }
        let odometer = Odometer {
            alphabet: declaration.alphabet,
            digits: widths.digits,
        };
        Ok(Self {
            declaration,
            widths,
            odometer,
            arena: Arena::new(1 << widths.digits),
            charts: Vec::new(),
            rebases: 0,
            passed: 0,
        })
    }

    /// The declaration.
    pub fn declaration(&self) -> &LandmarkDeclaration {
        &self.declaration
    }

    /// The derived widths.
    pub fn widths(&self) -> Widths {
        self.widths
    }

    /// `B = ⌈log₂|A|⌉`, the odometer digits of a cell.
    pub fn digits(&self) -> u64 {
        self.widths.digits
    }

    /// `M_p`, the path lattice's width.
    pub fn face_bits(&self) -> u64 {
        self.widths.face
    }

    /// The founded nodes.
    pub fn nodes(&self) -> usize {
        self.arena.len()
    }

    /// The cells passed (deposited).
    pub fn passed(&self) -> u64 {
        self.passed
    }

    /// **The tree's exact stored bits**, in `ClassMasses::bits`' style: every half-unit mass `2C`
    /// (odd) as the ratio `(2C)/2`, `bits(2C) + 2`, at the nodes of depth at least `forced`; at
    /// each mixing node (depth in `[forced, D)`), β's odd numerator and odd denominator,
    /// `max(1, bits) + 1` each, and its exponent, `max(1, bits|e|) + 2` with its sign; each founded
    /// child's letter, `max(1, bits(code)) + 1`; and one bit a splitting dyadic cell for its root's
    /// presence.
    /// The totals (the masses' sum), the cached stop weight (read from β) and the certificates are
    /// readings kept beside them and are not counted.
    pub fn bits(&self) -> u64 {
        let slot = |value: u64| u64::from((u64::BITS - value.leading_zeros()).max(1)) + 1;
        let (forced, depth) = (
            self.declaration.forced as u32,
            self.declaration.depth as u32,
        );
        let nodes: u64 = (0..self.arena.len())
            .map(|node| {
                let at = self.arena.depths[node];
                if at < forced {
                    return 0;
                }
                let masses: u64 = self.arena.halves[node]
                    .iter()
                    .map(|&units| u64::from(u32::BITS - units.leading_zeros()) + 2)
                    .sum();
                let beta = if at < depth {
                    let beta = &self.charts[node].beta;
                    slot(beta.numerator)
                        + slot(beta.denominator)
                        + slot(beta.exponent.unsigned_abs())
                        + 1
                } else {
                    0
                };
                masses + beta
            })
            .sum();
        let letters: u64 = self
            .arena
            .children
            .keys()
            .map(|key| slot(key & u64::from(u32::MAX)))
            .sum();
        let splitting = (0..self.widths.digits)
            .flat_map(|level| (0..1usize << level).map(move |prefix| (level, prefix)))
            .filter(|&(level, prefix)| self.odometer.splits(level, prefix))
            .count() as u64;
        nodes + letters + splitting
    }

    /// **The β chart's report** (module header).
    pub fn chart(&self) -> ChartReport {
        let drift = self
            .charts
            .iter()
            .map(|chart| chart.drift)
            .max()
            .unwrap_or(0);
        ChartReport {
            carrier: self.widths.carrier,
            rebases: self.rebases,
            node_rebases: self
                .charts
                .iter()
                .map(|chart| u64::from(chart.rebases))
                .max()
                .unwrap_or(0),
            drift: self.certified_bits(drift),
        }
    }

    /// A certificate on `2^(−C)` in `ln`, read in bits: times `3/2 > log₂ e`.
    fn certified_bits(&self, units: u128) -> Rat {
        Rat::new(
            BigInt::from(units) * 3,
            BigInt::from(2u32) << self.widths.certificate as usize,
        )
    }

    /// **The rule's a-priori bound per cell**, in bits (module header, "The widths"):
    /// `(1 + 2^(−min(M_p, W))) (3/2) B [(n* D² + 2D + 1) ε/μ̂ + n* D² 2^(1−W)]` with
    /// `ε/μ̂ = 1/(2⌊2^(M_p)/K⌋)`, `K = 2n* + 2`; below half a grain at the derived widths.
    pub fn face_rule(&self) -> Rat {
        let Widths {
            digits,
            face,
            carrier,
            ..
        } = self.widths;
        let (n, d) = (
            BigInt::from(self.declaration.population),
            BigInt::from(self.declaration.depth),
        );
        let paths = &n * &d * &d;
        let floor = (BigInt::one() << face as usize)
            / BigInt::from(floor_reciprocal(self.declaration.population));
        let rounding = Rat::new(&paths + &d * 2 + 1, floor * 2);
        let rebases = Rat::from_integer(paths) * two_power(1 - carrier as i64);
        let grid = Rat::one() + two_power(-(face.min(carrier) as i64));
        grid * log2_e_bound() * Rat::from_integer(BigInt::from(digits)) * (rounding + rebases)
    }

    fn full(&self) -> u64 {
        1u64 << self.widths.face
    }

    /// `⟦2^M u/v⟧`: the lattice numerator nearest `u/v` (ties up), inside `[1, 2^M − 1]`.
    fn round(&self, numerator: u128, denominator: u128) -> u64 {
        let rounded = (2 * numerator + denominator) / (2 * denominator);
        (rounded as u64).clamp(1, self.full() - 1)
    }

    /// The leaf's lattice face `⟦k(0)⟧`.
    fn leaf(&self, node: u32) -> u64 {
        let (u, v) = self.arena.kt(node, 0);
        self.round(u128::from(u) << self.widths.face, u128::from(v))
    }

    /// The mixing node's lattice face `⟦λ̂ k(0) + (1 − λ̂) q̂'⟧`, on `2^M v` as the common
    /// denominator.
    fn mix(&self, node: u32, below: u64) -> u64 {
        let (u, v) = self.arena.kt(node, 0);
        let face = self.widths.face;
        let stop = u128::from(self.charts[node as usize].stop);
        let full = u128::from(self.full());
        let numerator =
            ((stop * u128::from(u)) << face) + (full - stop) * u128::from(below) * u128::from(v);
        self.round(numerator, u128::from(v) << face)
    }

    /// **One tree's executed read** at an address, at most `limit` founded nodes.
    fn read(&self, dyadic: usize, symbol: usize, address: &[Letter], limit: usize) -> LatticeRead {
        let depth = self.declaration.depth;
        let nodes = self.arena.open(dyadic, address, limit);
        let top = nodes.len().min(depth);
        let mut faces = vec![0u64; top + 1];
        faces[top] = if nodes.len() == depth + 1 {
            self.leaf(nodes[depth])
        } else {
            self.full() / 2
        };
        for d in (0..top).rev() {
            faces[d] = if d < self.declaration.forced {
                faces[d + 1]
            } else {
                self.mix(nodes[d], faces[d + 1])
            };
        }
        LatticeRead {
            dyadic,
            symbol,
            nodes,
            faces,
        }
    }

    /// Every tree a class opens, read at the current standing.
    fn reads(&self, address: &[Letter], class: usize) -> Vec<LatticeRead> {
        let limit = self.declaration.depth + 1;
        self.odometer
            .emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| self.read(dyadic, symbol, address, limit))
            .collect()
    }

    /// A lattice face of `symbol` from the digit-`0` numerator.
    fn side(&self, zero: u64, symbol: usize) -> u64 {
        if symbol == 0 {
            zero
        } else {
            self.full() - zero
        }
    }

    /// **A level's rounding bound** `θ_d` of `symbol` on `2^(−C)`: `2^(−M)/min(q̂_d, k_d, q̂_(d+1))`
    /// at a mixing node, `2^(−M−1)/min(q̂_D, k_D)` at a founded leaf, zero at a forced or unfounded
    /// depth (their faces pass exactly).
    fn rounding(&self, read: &LatticeRead, d: usize) -> u128 {
        let Widths {
            face, certificate, ..
        } = self.widths;
        if d >= read.nodes.len() || d < self.declaration.forced {
            return 0;
        }
        let (u, v) = self.arena.kt(read.nodes[d], read.symbol);
        let here = u128::from(self.side(read.faces[d], read.symbol));
        let kt =
            |shift: u64| ceil_div(u128::from(v) << (certificate - face - shift), u128::from(u));
        if d == self.declaration.depth {
            let lattice = ceil_div(1u128 << (certificate - 1), here);
            lattice.max(kt(1))
        } else {
            let below = u128::from(self.side(read.faces[d + 1], read.symbol));
            let lattice = ceil_div(1u128 << certificate, here.min(below));
            lattice.max(kt(0))
        }
    }

    /// `ρ_0 ≤ Σ drift + Σ θ` of one read on `2^(−C)`.
    fn certificate(&self, read: &LatticeRead) -> u128 {
        let mixing = read.nodes.len().min(self.declaration.depth);
        let drift = (self.declaration.forced..mixing)
            .map(|d| self.charts[read.nodes[d] as usize].drift)
            .fold(0u128, u128::saturating_add);
        (0..read.faces.len())
            .map(|d| self.rounding(read, d))
            .fold(drift, u128::saturating_add)
    }

    /// The cell's reading from its trees' reads.
    fn reading(&self, reads: &[LatticeRead]) -> CellReading {
        let mut numerator = BigUint::one();
        let mut certificate = 0u128;
        for read in reads {
            numerator *= self.side(read.faces[0], read.symbol);
            certificate = certificate.saturating_add(self.certificate(read));
        }
        CellReading {
            executed: dyadic(numerator, reads.len() as u64 * self.widths.face),
            residual: self.certified_bits(certificate),
        }
    }

    /// **The executed face of one class** at an address, exact.
    pub fn probability(&self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        Ok(self.score(address, class)?.executed)
    }

    /// **Score one class** at an address at the current standing: its executed face and its
    /// certified residual, with nothing deposited.
    pub fn score(&self, address: &[Letter], class: usize) -> Result<CellReading, HnnError> {
        check(&self.declaration, address, class)?;
        Ok(self.reading(&self.reads(address, class)))
    }

    /// **The opened paths of one class** at an address, with their executed lattice faces.
    pub fn opened(&self, address: &[Letter], class: usize) -> Result<Vec<OpenedPath>, HnnError> {
        check(&self.declaration, address, class)?;
        let scale = BigInt::one() << self.widths.face as usize;
        Ok(self
            .reads(address, class)
            .into_iter()
            .map(|read| OpenedPath {
                dyadic: read.dyadic,
                symbol: read.symbol,
                founded: read.nodes.len(),
                faces: read
                    .faces
                    .iter()
                    .map(|&zero| {
                        Rat::new(BigInt::from(self.side(zero, read.symbol)), scale.clone())
                    })
                    .collect(),
                masses: read
                    .nodes
                    .iter()
                    .map(|&node| {
                        let (u, v) = self.arena.kt(node, read.symbol);
                        Rat::new(BigInt::from(u), BigInt::from(v))
                    })
                    .collect(),
                betas: read
                    .nodes
                    .iter()
                    .map(|&node| self.charts[node as usize].beta.value())
                    .collect(),
            })
            .collect())
    }

    /// **All classes' executed faces at an address**, with their grain exponents at `grain`
    /// (module header, "Faces").
    pub fn face(&self, address: &[Letter], grain: u64) -> Result<LandmarkFace, HnnError> {
        check(&self.declaration, address, 0)?;
        let digits = self.widths.digits;
        let cells = 1usize << digits;
        // The heap over dyadic cells: each cell's founded bound, and each class's descent.
        let mut limit = vec![0usize; 2 * cells];
        let mut numerators: Vec<Option<BigUint>> = vec![None; 2 * cells];
        let mut opened = vec![0u64; 2 * cells];
        limit[1] = self.declaration.depth + 1;
        numerators[1] = Some(BigUint::one());
        for level in 0..digits {
            for prefix in 0..(1usize << level) {
                if !self.odometer.holds(level, prefix) {
                    continue;
                }
                let h = (1usize << level) | prefix;
                let numerator = numerators[h].take().expect("a held cell's descent");
                if self.odometer.splits(level, prefix) {
                    let read = self.read(h, 0, address, limit[h]);
                    let zero = read.faces[0];
                    let founded = read.nodes.len();
                    for (child, split) in [(2 * h, zero), (2 * h + 1, self.full() - zero)] {
                        limit[child] = founded;
                        numerators[child] = Some(&numerator * split);
                        opened[child] = opened[h] + 1;
                    }
                } else {
                    limit[2 * h] = limit[h];
                    opened[2 * h] = opened[h];
                    numerators[2 * h] = Some(numerator);
                }
            }
        }
        let mut probabilities = Vec::with_capacity(self.declaration.alphabet);
        let mut exponents = Vec::with_capacity(self.declaration.alphabet);
        for class in 0..self.declaration.alphabet {
            let leaf = cells | class;
            let numerator = numerators[leaf].take().expect("a class's descent");
            let exponent = opened[leaf] * self.widths.face;
            exponents.push(dyadic_grain_exponent(&numerator, exponent, grain)?);
            probabilities.push(dyadic(numerator, exponent));
        }
        Ok(LandmarkFace {
            grain,
            probabilities,
            exponents,
        })
    }

    /// **Deposit one cell** on the paths it opens, read at the current standing (module header):
    /// each mixing node's β steps by `k(b)/q̂_(d+1)(b)` bottom-up and its certificates grow, the
    /// path's missing nodes are founded with `β = 1`, then each node's mass of the digit grows.
    /// Refused before anything moves at a bad address or class, or past the declared population.
    pub fn deposit(&mut self, address: &[Letter], class: usize) -> Result<(), HnnError> {
        check(&self.declaration, address, class)?;
        let reads = self.reads(address, class);
        self.apply(address, reads)
    }

    /// **Receive one cell**: score it at the current standing, then deposit it.
    pub fn receive(&mut self, address: &[Letter], class: usize) -> Result<CellReading, HnnError> {
        check(&self.declaration, address, class)?;
        let reads = self.reads(address, class);
        let reading = self.reading(&reads);
        self.apply(address, reads)?;
        Ok(reading)
    }

    fn apply(&mut self, address: &[Letter], reads: Vec<LatticeRead>) -> Result<(), HnnError> {
        if self.passed >= self.declaration.population {
            return Err(HnnError::PopulationReached {
                population: self.declaration.population,
            });
        }
        self.arena
            .founded_within(reads.len() * (address.len() + 1))?;
        let Widths {
            face,
            carrier,
            certificate,
            ..
        } = self.widths;
        let (depth, forced) = (self.declaration.depth, self.declaration.forced);
        for read in reads {
            // Bottom-up over the founded nodes: θ and the rebases add to the excess, the child's
            // excess increment and the rebase to the drift.
            let mut carried = 0u128;
            for d in (forced..read.nodes.len()).rev() {
                let theta = self.rounding(&read, d);
                let node = read.nodes[d] as usize;
                let mut rebase = 0u128;
                if d < depth {
                    let (u, v) = self.arena.kt(read.nodes[d], read.symbol);
                    let below = self.side(read.faces[d + 1], read.symbol);
                    let chart = &mut self.charts[node];
                    let (beta, rebased) = Beta::carry(
                        u128::from(chart.beta.numerator) * u128::from(u),
                        u128::from(chart.beta.denominator) * u128::from(v) * u128::from(below),
                        chart.beta.exponent + face as i64,
                        carrier,
                    );
                    chart.beta = beta;
                    chart.stop = beta.stop_weight(face, carrier);
                    if let Some(mantissa) = rebased {
                        rebase = ceil_div(1u128 << certificate, mantissa);
                        chart.rebases += 1;
                        self.rebases += 1;
                    }
                    chart.drift = chart.drift.saturating_add(carried).saturating_add(rebase);
                }
                let increment = theta
                    .saturating_add(rebase.saturating_mul(2))
                    .saturating_add(carried);
                let chart = &mut self.charts[node];
                chart.excess = chart.excess.saturating_add(increment);
                carried = increment;
            }
            let LatticeRead {
                dyadic,
                symbol,
                mut nodes,
                ..
            } = read;
            let founded = self.arena.extend(dyadic, address, &mut nodes);
            self.charts.extend(std::iter::repeat_n(
                Chart {
                    beta: Beta::ONE,
                    stop: self.full() / 2,
                    rebases: 0,
                    drift: 0,
                    excess: 0,
                },
                founded,
            ));
            self.arena.count(&nodes, forced, symbol);
        }
        self.passed += 1;
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------
// dyadic faces: the certified binary logarithm

/// A dyadic `numerator/2^exponent`, reduced.
fn dyadic(numerator: BigUint, exponent: u64) -> Rat {
    let twos = numerator.trailing_zeros().unwrap_or(0).min(exponent);
    Rat::new_raw(
        BigInt::from(numerator >> twos),
        BigInt::one() << (exponent - twos) as usize,
    )
}

/// [definition; agent-inferred] **The fixed point of the binary logarithm's squaring**: `P`
/// fraction bits for `y ∈ [1, 2]`, the widest with `y² ≤ 4` held in `P + 3 ≤ 128` bits.
const FIXED: u32 = u128::BITS - 3;

/// `(hi, lo)` with `a b = hi 2^128 + lo`.
fn wide_mul(a: u128, b: u128) -> (u128, u128) {
    let mask = u128::from(u64::MAX);
    let (a1, a0, b1, b0) = (a >> 64, a & mask, b >> 64, b & mask);
    let (p00, p01, p10, p11) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
    let middle = (p00 >> 64) + (p01 & mask) + (p10 & mask);
    (
        p11 + (p01 >> 64) + (p10 >> 64) + (middle >> 64),
        (p00 & mask) | (middle << 64),
    )
}

/// `⌊x²/2^P⌋` and `⌈x²/2^P⌉` for `x ≤ 2^(P+1) + 1`.
fn square(x: u128) -> (u128, u128) {
    let (hi, lo) = wide_mul(x, x);
    let floor = (hi << (u128::BITS - FIXED)) | (lo >> FIXED);
    let exact = lo & ((1u128 << FIXED) - 1) == 0;
    (floor, floor + u128::from(!exact))
}

/// [definition; agent-inferred] **A certified binary logarithm** of a positive integer `m`:
/// `log₂ m ∈ [whole + fraction/2^bits, whole + (fraction + 1)/2^bits]`, exactly `whole` when `m`
/// is a power of two (`exact`), and otherwise strictly inside (it is then irrational).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinaryLog {
    pub whole: u64,
    pub fraction: u128,
    pub bits: u32,
    pub exact: bool,
}

/// **The binary logarithm by exact squaring** (agent-inferred; the invariant's Lean statement is
/// owed in #62): `y = m/2^whole ∈ [1, 2)` is held between two fixed-point integers on `2^(−P)`,
/// rounded outward; each step squares both, and a bit is emitted only when both bounds agree on
/// `y² ≥ 2` (then both halve, outward). It stops at `bits` fraction bits, when `decided` accepts,
/// or when the bounds straddle `2` (a shorter, still certified enclosure). At most 128 bits.
pub fn binary_log(
    m: &BigUint,
    bits: u32,
    mut decided: impl FnMut(&BinaryLog) -> bool,
) -> BinaryLog {
    debug_assert!(!m.is_zero() && bits <= u128::BITS);
    let whole = m.bits() - 1;
    let mut log = BinaryLog {
        whole,
        fraction: 0,
        bits: 0,
        exact: m.count_ones() == 1,
    };
    if log.exact {
        return log;
    }
    let fixed = u64::from(FIXED);
    let (mut lower, mut upper) = if whole <= fixed {
        let y = (m << (fixed - whole) as usize)
            .to_u128()
            .expect("P + 1 bits");
        (y, y)
    } else {
        let shifted = m >> (whole - fixed) as usize;
        let y = shifted.to_u128().expect("P + 1 bits");
        (y, y + 1)
    };
    let two = 1u128 << (FIXED + 1);
    while log.bits < bits && !decided(&log) {
        let (low, _) = square(lower);
        let (_, high) = square(upper);
        let bit = if low >= two {
            true
        } else if high < two {
            false
        } else {
            break;
        };
        log.fraction = (log.fraction << 1) | u128::from(bit);
        log.bits += 1;
        (lower, upper) = if bit {
            (low >> 1, (high + 1) >> 1)
        } else {
            (low, high)
        };
    }
    log
}

/// `⌊L log₂ m⌋`, decided by the certified binary logarithm within 64 fraction bits (every operand
/// within `u128` for `L < 2^32` and `m` of fewer than `2^31` bits), or `None`.
fn grain_floor(m: &BigUint, grain: u64) -> Option<BigInt> {
    if grain == 0 {
        return Some(BigInt::zero());
    }
    let limit = u32::BITS - 1;
    if grain > u64::from(u32::MAX) || m.bits() > 1u64 << limit {
        return None;
    }
    let floors = |log: &BinaryLog| {
        let base = (u128::from(log.whole) << log.bits) | log.fraction;
        let grain = u128::from(grain);
        (
            (grain * base) >> log.bits,
            (grain * (base + 1) - 1) >> log.bits,
        )
    };
    let log = binary_log(m, u64::BITS, |log| {
        let (lower, upper) = floors(log);
        lower == upper
    });
    if log.exact {
        return Some(BigInt::from(log.whole) * grain);
    }
    let (lower, upper) = floors(&log);
    (lower == upper).then(|| BigInt::from(lower))
}

/// **The grain exponent of a dyadic face** `m/2^J` at `L`: `⌊L log₂ m⌋ − L J`, decided by the
/// certified binary logarithm, the exact comparison (`grain_exponent`) when it does not decide.
fn dyadic_grain_exponent(
    numerator: &BigUint,
    exponent: u64,
    grain: u64,
) -> Result<BigInt, HnnError> {
    match grain_floor(numerator, grain) {
        Some(floor) => Ok(floor - BigInt::from(grain) * BigInt::from(exponent)),
        None => grain_exponent(numerator, &(BigUint::one() << exponent as usize), grain),
    }
}

// -------------------------------------------------------------------------------------------
// the reference oracle

/// [definition] **The ideal tree weighting, the reference oracle** (module header): the executed
/// tree's arena with `β` in ℚ and every path face exact, `q_D = k_D`,
/// `q_d = (β k_d + q_(d+1))/(1 + β)`, the deposit `β' = β k/q_(d+1)` on the exact faces. With no
/// width `β` is exact (the tests); at a width it is rebased past it with the residual `1/m'`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdealLandmarks {
    declaration: LandmarkDeclaration,
    odometer: Odometer,
    arena: Arena,
    beta: Vec<Rat>,
    width: Option<u64>,
    rebases: u64,
}

struct IdealRead {
    dyadic: usize,
    symbol: usize,
    nodes: Vec<u32>,
    faces: Vec<Rat>,
}

impl IdealLandmarks {
    /// **Declare the oracle**, empty, with `β` exact (`width = None`) or carried at a width.
    pub fn new(declaration: LandmarkDeclaration, width: Option<u64>) -> Result<Self, HnnError> {
        check_declaration(&declaration)?;
        let digits = odometer_digits(declaration.alphabet);
        Ok(Self {
            odometer: Odometer {
                alphabet: declaration.alphabet,
                digits,
            },
            arena: Arena::new(1 << digits),
            declaration,
            beta: Vec::new(),
            width,
            rebases: 0,
        })
    }

    /// [definition; agent-inferred] **The reference width** `W_o = O + ⌈log₂(3 B n*² D²)⌉`: the
    /// oracle's rebases move a cell's code length by at most `(3/2) B n* D² 2^(1−W_o)` bits
    /// (the executed chart's drift rule with no rounding), so by at most `2^(−O)` over the passage.
    pub fn reference_width(declaration: &LandmarkDeclaration) -> u64 {
        let (n, d) = (
            BigUint::from(declaration.population),
            BigUint::from(declaration.depth),
        );
        let digits = BigUint::from(odometer_digits(declaration.alphabet));
        u64::from(LOG_OCTAVES) + ceil_log2(&(BigUint::from(3u32) * digits * &n * &n * &d * &d))
    }

    /// The oracle's own rule per cell, in bits: `(3/2) B n* D² 2^(1−W_o)` (zero with `β` exact).
    pub fn drift_rule(&self) -> Rat {
        let Some(width) = self.width else {
            return Rat::zero();
        };
        let (n, d) = (
            BigInt::from(self.declaration.population),
            BigInt::from(self.declaration.depth),
        );
        log2_e_bound()
            * Rat::from_integer(BigInt::from(self.odometer.digits) * n * &d * &d)
            * two_power(1 - width as i64)
    }

    /// The rebases so far.
    pub fn rebases(&self) -> u64 {
        self.rebases
    }

    fn kt(&self, node: u32, symbol: usize) -> Rat {
        let (u, v) = self.arena.kt(node, symbol);
        Rat::new(BigInt::from(u), BigInt::from(v))
    }

    fn read(&self, dyadic: usize, symbol: usize, address: &[Letter]) -> IdealRead {
        let depth = self.declaration.depth;
        let nodes = self.arena.open(dyadic, address, depth + 1);
        let top = nodes.len().min(depth);
        let mut faces = vec![Rat::new(BigInt::one(), BigInt::from(2)); top + 1];
        if nodes.len() == depth + 1 {
            faces[depth] = self.kt(nodes[depth], symbol);
        }
        for d in (0..top).rev() {
            faces[d] = if d < self.declaration.forced {
                faces[d + 1].clone()
            } else {
                let beta = &self.beta[nodes[d] as usize];
                (beta * self.kt(nodes[d], symbol) + &faces[d + 1]) / (Rat::one() + beta)
            };
        }
        IdealRead {
            dyadic,
            symbol,
            nodes,
            faces,
        }
    }

    fn reads(&self, address: &[Letter], class: usize) -> Vec<IdealRead> {
        self.odometer
            .emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| self.read(dyadic, symbol, address))
            .collect()
    }

    /// **The ideal face of one class** at an address, exact.
    pub fn probability(&self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        check(&self.declaration, address, class)?;
        Ok(self
            .reads(address, class)
            .iter()
            .map(|read| read.faces[0].clone())
            .product())
    }

    /// **The opened paths of one class** at an address, with their ideal faces.
    pub fn opened(&self, address: &[Letter], class: usize) -> Result<Vec<OpenedPath>, HnnError> {
        check(&self.declaration, address, class)?;
        Ok(self
            .reads(address, class)
            .into_iter()
            .map(|read| OpenedPath {
                dyadic: read.dyadic,
                symbol: read.symbol,
                founded: read.nodes.len(),
                masses: read
                    .nodes
                    .iter()
                    .map(|&node| self.kt(node, read.symbol))
                    .collect(),
                betas: read
                    .nodes
                    .iter()
                    .map(|&node| self.beta[node as usize].clone())
                    .collect(),
                faces: read.faces,
            })
            .collect())
    }

    /// **Receive one cell**: its ideal face at the current standing, then its deposit.
    pub fn receive(&mut self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        check(&self.declaration, address, class)?;
        let reads = self.reads(address, class);
        self.arena
            .founded_within(reads.len() * (address.len() + 1))?;
        let face = reads.iter().map(|read| read.faces[0].clone()).product();
        let (depth, forced) = (self.declaration.depth, self.declaration.forced);
        for read in reads {
            for d in (forced..read.nodes.len().min(depth)).rev() {
                let node = read.nodes[d] as usize;
                let stepped =
                    &self.beta[node] * self.kt(read.nodes[d], read.symbol) / &read.faces[d + 1];
                let (beta, rebased) = carried_ratio(&stepped, self.width);
                self.beta[node] = beta;
                self.rebases += u64::from(rebased);
            }
            let IdealRead {
                dyadic,
                symbol,
                mut nodes,
                ..
            } = read;
            let founded = self.arena.extend(dyadic, address, &mut nodes);
            self.beta.extend(std::iter::repeat_n(Rat::one(), founded));
            self.arena.count(&nodes, forced, symbol);
        }
        Ok(face)
    }
}

/// A positive ratio carried at an optional width: exact when both odd parts fit, otherwise its
/// mantissa `⌊v 2^s⌋ ∈ [2^(W−1), 2^W)` times `2^(−s)`.
fn carried_ratio(value: &Rat, width: Option<u64>) -> (Rat, bool) {
    let Some(width) = width else {
        return (value.clone(), false);
    };
    let (numerator, denominator) = (value.numer().magnitude(), value.denom().magnitude());
    let odd = |x: &BigUint| x >> x.trailing_zeros().unwrap_or(0);
    if odd(numerator).bits() <= width && odd(denominator).bits() <= width {
        return (value.clone(), false);
    }
    let (m, shift) = mantissa(numerator, denominator, width);
    (Rat::from_integer(BigInt::from(m)) * two_power(-shift), true)
}

/// **The `W`-bit mantissa of a positive ratio** `a/b`: `m = ⌊a 2^s / b⌋ ∈ [2^(W−1), 2^W)` and its
/// shift `s`, so `m 2^(−s) ≤ a/b < (m + 1) 2^(−s)`.
fn mantissa(a: &BigUint, b: &BigUint, width: u64) -> (BigUint, i64) {
    let floor = |shift: i64| -> BigUint {
        if shift >= 0 {
            (a << shift as usize) / b
        } else {
            a / (b << shift.unsigned_abs() as usize)
        }
    };
    let mut shift = width as i64 - (a.bits() as i64 - b.bits() as i64);
    let mut m = floor(shift);
    if m.bits() > width {
        shift -= 1;
        m = floor(shift);
    }
    debug_assert_eq!(m.bits(), width);
    (m, shift)
}

// -------------------------------------------------------------------------------------------
// the measurement

/// [definition] **Code lengths on one population**, each an enclosure summed by `interval_sum`
/// over `cells` cells: the tree's executed face and the online baselines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coded {
    pub tree: ExactInterval,
    pub uniform: ExactInterval,
    pub order_zero: ExactInterval,
    pub order_one: ExactInterval,
    pub ppm: ExactInterval,
    pub cells: u64,
}

/// [definition] **One tree's run**: its declaration and widths, its chart's report, its founded
/// nodes and stored bits, the rule's a-priori residual a cell and the largest per-cell certified
/// residual over the run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeRun {
    pub declaration: LandmarkDeclaration,
    pub widths: Widths,
    pub chart: ChartReport,
    pub nodes: usize,
    pub bits: u64,
    pub face_rule: Rat,
    pub largest_residual: Rat,
}

/// [definition] **The prequential measurement** ([`prequential`]): the development and held-out
/// populations' code lengths and the tree's run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prequential {
    pub development: Coded,
    pub held_out: Coded,
    pub run: TreeRun,
}

/// [definition] **A depth sweep on the development cells** ([`choose_depth`]): every depth tried with
/// its development code length, the chosen depth and the description bits the choice is charged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DepthSweep {
    pub tried: Vec<(usize, ExactInterval)>,
    pub chosen: usize,
    pub description_bits: u64,
}

fn zero() -> ExactInterval {
    ExactInterval::point(Rat::zero())
}

/// [definition; agent-inferred] **A face's code length** `−log₂ q`, enclosed (module header, "The
/// measurement"): for `q = n/d`, `log₂ d − log₂ n`, each by the certified [`binary_log`] at
/// `O + 1` fraction bits (`O` the enclosure grid's octaves, `hnn::ratio`'s `LOG_OCTAVES`), so the
/// enclosure is at most `2^(−O)` wide on the grid `interval_sum` rounds every sum out to; exact when
/// both are powers of two (a dyadic face with a power-of-two numerator).
pub fn code_length(probability: &Rat) -> Result<ExactInterval, HnnError> {
    if !probability.is_positive() {
        return Err(shape("a positive face's code length", 1, 0));
    }
    let bits = LOG_OCTAVES + 1;
    let bounds = |value: &BigUint| -> (Rat, Rat) {
        let log = binary_log(value, bits, |_| false);
        let whole = BigInt::from(log.whole) << log.bits as usize;
        let scale = BigInt::one() << log.bits as usize;
        let lower = &whole + BigInt::from(log.fraction);
        let upper = if log.exact { lower.clone() } else { &lower + 1 };
        (Rat::new(lower, scale.clone()), Rat::new(upper, scale))
    };
    let (numerator, denominator) = (
        bounds(probability.numer().magnitude()),
        bounds(probability.denom().magnitude()),
    );
    ExactInterval::new(&denominator.0 - &numerator.1, &denominator.1 - &numerator.0)
        .map_err(|_| shape("an ordered enclosure of a code length", 0, 1))
}

/// A tree's prequential sums over one stream, `[development, held-out]`, and the run.
fn run_tree(
    cells: &[usize],
    held_out: &(dyn Fn(usize) -> bool + Sync),
    declaration: &LandmarkDeclaration,
) -> Result<([ExactInterval; 2], TreeRun), HnnError> {
    let mut tree = Landmarks::new(declaration.clone())?;
    let mut sums = [zero(), zero()];
    let mut largest_residual = Rat::zero();
    for (position, &class) in cells.iter().enumerate() {
        let reading = tree.receive(&address(cells, position, declaration.depth), class)?;
        let part = usize::from(held_out(position));
        sums[part] = interval_sum(&sums[part], &code_length(&reading.executed)?)?;
        if reading.residual > largest_residual {
            largest_residual = reading.residual;
        }
    }
    Ok((
        sums,
        TreeRun {
            declaration: declaration.clone(),
            widths: tree.widths(),
            chart: tree.chart(),
            nodes: tree.nodes(),
            bits: tree.bits(),
            face_rule: tree.face_rule(),
            largest_residual,
        },
    ))
}

/// The baselines' prequential sums over one stream, `[development, held-out]`, and the counts.
fn run_baselines(
    cells: &[usize],
    held_out: &(dyn Fn(usize) -> bool + Sync),
    alphabet: usize,
) -> Result<([BaselineCodes; 2], [u64; 2]), HnnError> {
    let mut baselines = Baselines::new(alphabet)?;
    let empty = || BaselineCodes {
        uniform: zero(),
        order_zero: zero(),
        order_one: zero(),
        ppm: zero(),
    };
    let (mut sums, mut counts) = ([empty(), empty()], [0u64; 2]);
    for (position, &class) in cells.iter().enumerate() {
        let codes = baselines.code_cell(class)?;
        let part = usize::from(held_out(position));
        let sum = &mut sums[part];
        sum.uniform = interval_sum(&sum.uniform, &codes.uniform)?;
        sum.order_zero = interval_sum(&sum.order_zero, &codes.order_zero)?;
        sum.order_one = interval_sum(&sum.order_one, &codes.order_one)?;
        sum.ppm = interval_sum(&sum.ppm, &codes.ppm)?;
        counts[part] += 1;
    }
    Ok((sums, counts))
}

/// **The prequential measurement on a cut** (module header): the tree and the online baselines
/// over the same cells in the same order, each cell scored at the current standing and then
/// deposited, with enclosures on the development and held-out populations.
pub fn prequential(cut: &Cut, declaration: &LandmarkDeclaration) -> Result<Prequential, HnnError> {
    let held_out = |position: usize| cut.held_out(position);
    let (tree, baselines) = rayon::join(
        || run_tree(&cut.cells, &held_out, declaration),
        || run_baselines(&cut.cells, &held_out, declaration.alphabet),
    );
    let ([development_tree, held_tree], run) = tree?;
    let ([development, held], counts) = baselines?;
    let coded = |tree: ExactInterval, baselines: BaselineCodes, cells: u64| Coded {
        tree,
        uniform: baselines.uniform,
        order_zero: baselines.order_zero,
        order_one: baselines.order_one,
        ppm: baselines.ppm,
        cells,
    };
    Ok(Prequential {
        development: coded(development_tree, development, counts[0]),
        held_out: coded(held_tree, held, counts[1]),
        run,
    })
}

/// **The development stream**: the cut with its held-out cells removed.
pub fn development(cut: &Cut) -> Vec<usize> {
    cut.cells
        .iter()
        .enumerate()
        .filter(|(position, _)| !cut.held_out(*position))
        .map(|(_, &cell)| cell)
        .collect()
}

/// **Choose the address depth on the development cells** (module header): `D = max(1, forced), …`
/// while the development prequential code length decreases strictly; the declaration's own depth
/// is ignored, and each depth derives its own widths.
pub fn choose_depth(cut: &Cut, declaration: &LandmarkDeclaration) -> Result<DepthSweep, HnnError> {
    let cells = development(cut);
    let never = |_: usize| false;
    let mut tried: Vec<(usize, ExactInterval)> = Vec::new();
    let mut depth = declaration.forced.max(1);
    loop {
        let declared = LandmarkDeclaration {
            depth,
            ..declaration.clone()
        };
        let ([bits, _], _) = run_tree(&cells, &never, &declared)?;
        let decreased = tried
            .last()
            .is_none_or(|(_, previous)| bits.upper < previous.lower);
        tried.push((depth, bits));
        if !decreased || depth >= cells.len() {
            break;
        }
        depth += 1;
    }
    let chosen =
        if tried.len() >= 2 && tried[tried.len() - 1].1.upper >= tried[tried.len() - 2].1.lower {
            tried[tried.len() - 2].0
        } else {
            tried[tried.len() - 1].0
        };
    let description_bits = ceil_log2(&BigUint::from(tried.len()));
    Ok(DepthSweep {
        tried,
        chosen,
        description_bits,
    })
}

/// [definition] **The executed face's cost against the oracle** ([`oracle_cost`]), per population
/// `[development, held-out]`: the oracle's reference width and rebases, both code lengths, the
/// largest observed per-cell deviation (the upper bound `|q̂ − q|/min(q̂, q) · 3/2` bits of
/// `|log₂(q̂/q)|`), the largest certificate, the oracle's own rule a cell, and whether every cell's
/// observed deviation lay within its certificate plus the oracle's rule (the certificate bounds the
/// distance to the ideal, the oracle's rule the oracle's).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OracleCost {
    pub reference_width: u64,
    pub rebases: u64,
    pub executed: [ExactInterval; 2],
    pub ideal: [ExactInterval; 2],
    pub largest_deviation: Rat,
    pub largest_certificate: Rat,
    pub drift_rule: Rat,
    pub certified: bool,
}

/// **The executed face against the reference oracle on a cut** (module header): both trees receive
/// every cell in order at the reference width `W_o`; each cell's executed and ideal faces are
/// read by [`code_length`] and compared exactly. Not on the hot path.
pub fn oracle_cost(cut: &Cut, declaration: &LandmarkDeclaration) -> Result<OracleCost, HnnError> {
    let reference_width = IdealLandmarks::reference_width(declaration);
    let mut tree = Landmarks::new(declaration.clone())?;
    let mut oracle = IdealLandmarks::new(declaration.clone(), Some(reference_width))?;
    let drift_rule = oracle.drift_rule();
    let (mut executed, mut ideal) = ([zero(), zero()], [zero(), zero()]);
    let (mut largest_deviation, mut largest_certificate) = (Rat::zero(), Rat::zero());
    let mut certified = true;
    for (position, &class) in cut.cells.iter().enumerate() {
        let here = address(&cut.cells, position, declaration.depth);
        let reading = tree.receive(&here, class)?;
        let face = oracle.receive(&here, class)?;
        let part = usize::from(cut.held_out(position));
        executed[part] = interval_sum(&executed[part], &code_length(&reading.executed)?)?;
        ideal[part] = interval_sum(&ideal[part], &code_length(&face)?)?;
        let least = if reading.executed < face {
            &reading.executed
        } else {
            &face
        };
        let deviation = (&reading.executed - &face).abs() / least * log2_e_bound();
        certified &= deviation <= &reading.residual + &drift_rule;
        if deviation > largest_deviation {
            largest_deviation = deviation;
        }
        if reading.residual > largest_certificate {
            largest_certificate = reading.residual;
        }
    }
    Ok(OracleCost {
        reference_width,
        rebases: oracle.rebases(),
        executed,
        ideal,
        largest_deviation,
        largest_certificate,
        drift_rule,
        certified,
    })
}
