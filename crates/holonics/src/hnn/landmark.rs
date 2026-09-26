//! **The receiving parametron's storage as a tree of landmarks** (Decision 28, count-only; #73).
//!
//! [definition] The computational object is the helical pair interaction; this owner is the
//! receiving parametron's storage, read as a tree of landmarks. Of the winding guide's six general
//! objects it touches three: **faces and placement** (the receiving face, read at the receiver's
//! grain), the **tower thread** (the suffix restriction: each address letter restricts to the
//! newest cell, and a cell's odometer digits descend its dyadic cell), and the **pair** (each edge
//! of an opened path compares a node's face with its child's, `R_(d→d+1) = q_(d+1)/q_d`). The
//! **helix** enters only as the chart's carry and phase (the β exponent is a carry, its mantissa
//! the phase within the octave). A tree has no two-cells, so no **cell holonomy** is claimed, and
//! the **tube** is the passage itself, one cell per tick. Decision 27's region table is the
//! depth-one, forced-split case ([`LandmarkDeclaration::forced`]).
//!
//! ```text
//! address      a_j = [x_(j−1), …, x_(j−D)]  newest first,  x_i = Boundary for i < 0      per cell
//! KT           k_s(c) = C_s(c)/N_s ,  C_s(c) = n_s(c) + ½ ,  in half-units 2C = 2n + 1
//! ratio        β_s = E_s / Π_b W_bs   (1 at first arrival),   λ_s = β_s/(1 + β_s)
//! path face    q_D = k_D ;   q_d = λ_d k_d + (1 − λ_d) q_(d+1)      (λ_d = 0 at a forced split)
//! deposit      β'_d = β_d k_d(c) / q_(d+1)(c)  bottom-up, then n_d(c) += 1, on the opened path only
//! telescope    q_0(c) = q_D(c) · Π_(d<D) q_d(c)/q_(d+1)(c)
//! ```
//!
//! [definition] **Typed address letters** ([`Letter`]): `Boundary` (before the cut's first cell)
//! and `Cell(code)`. The address of cell `j` is its preceding `D` cells, newest first, read per
//! cell: causal, with no window pooling ([`address`]). A letter's code is `0` for the boundary and
//! `1 + code` for a cell, the same numbering as `hnn::masses::Regions::PrecedingCell` (region `0`
//! is the empty window).
//!
//! [definition] **The emission** ([`Emission`]) declares how the predicted cell is coded.
//! - `Digits`: the cell's `B = ⌈log₂|A|⌉` binary odometer digits, most significant first. Digit
//!   `i` is predicted at the joint address: its digit prefix (the dyadic cell it descends) as a
//!   forced split, then the context letters mixed by the tree, each node holding binary KT masses in
//!   half-units. A dyadic cell whose upper half holds no class of the chart forces its digit with
//!   face 1 and stores nothing, so every `|A| ≥ 2` is normalized, not only powers of two.
//! - `Cell`: the whole cell, with `|A|`-ary KT masses at each node (Decision 27's parity case).
//!
//! [definition; agent-inferred] **The arena** (the layout the card ports next). Nodes are founded at
//! first arrival and numbered in founding order, `u32`. Every per-node value is a flat vector
//! indexed by the node:
//! - `roots[h]`: the root of the tree at dyadic cell `h` (the heap index `2^i + prefix`, `h = 1` the
//!   whole cell; `Cell` uses `h = 1` only), founded at its first arrival;
//! - `children`: a hash table from `(parent << 32) | letter code` to the child node;
//! - `totals[node]`: `2N`, the node's total in half-units (the prior is one half-unit per symbol);
//! - `Digits`: `binary[2·node + v]`, `2C` of digit value `v`; `Cell`: a hash table from
//!   `(node << 32) | class` to `2C`, a missing entry reading the prior's one half-unit;
//! - `beta[node]`: the carried mixture ratio ([`Beta`]: odd numerator, odd denominator, both below
//!   `2^W`, and a binary exponent), and `rebased[node]`, its rebases.
//!
//! An unfounded node reads as the prior: its subtree has seen nothing, so each of its nodes has
//! `E = W = 1`, `β = 1`, and its face is uniform. A path read stops at its first unfounded node,
//! whose face is exactly the uniform prior.
//!
//! [definition] **The path face** `q_d` is exact in ℚ given the carried β. Any `λ ∈ [0, 1]` gives a
//! positive normalized face (a convex combination of positive normalized KT faces), so the executed
//! face is exactly scored whatever the chart. **The deposit** changes only the opened path: each
//! old node's β by the likelihood-ratio step (read at the standing before the deposit), then each
//! node's count of the emitted symbol; the path's missing nodes are founded with `β = 1` (their
//! step `k/q` is `prior/prior = 1`). A forced split keeps neither counts nor β: nothing reads them.
//!
//! [definition; agent-inferred] **The β chart.** β is carried exactly, as a reduced ratio of odd
//! integers times a power of two, while both odd parts fit the carrier width `W`. When one outgrows
//! it, β is **rebased**: its mantissa `m = ⌊β 2^s⌋ ∈ [2^(W−1), 2^W)` is kept with the exponent
//! `−s` carried as an integer (the exponent is the carry, the mantissa the phase within the octave),
//! with the certified relative residual `r = 1 − m/(β 2^s) ∈ [0, 2^(1−W))`, so
//! `|log₂(1 − r)| < 2^(3−W)` for `W ≥ 2`. **`W` is derived from the passage and the grain**: the
//! accumulated log₂ residual over `n` updates at a node stays below one receiver grain `1/L_R` when
//! `n · 2^(3−W) < 1/L_R`, so `W` is the least width with `2^W > 8 L_R n*` over the declared
//! population `n*` ([`carrier_width`]; `W = 20` at `n* = 6,148`, `L_R = 16`). The rebases and
//! their summed bound `rebases · 2^(3−W)`, total and at the most-rebased node, are reported
//! ([`ChartReport`]). On a short fixture no rebase occurs and the face is the ideal tree weighting
//! exactly. Deposits past `n*` are refused ([`HnnError::PopulationReached`]): the certificates hold
//! only within it.
//!
//! [definition; agent-inferred, the primary's amendment] **The executed `Digits` face is a dyadic
//! partition**, one fixed-width law for the host and the card. At each digit the exact ideal face
//! `q(0)` of that digit's opened path is rounded to the nearest multiple of `2^(−M_f)` inside
//! `[2^(−M_f), 1 − 2^(−M_f)]`, and `q̂(1) = 1 − q̂(0)`. A cell's executed face is the product of its
//! digits' dyadic splits: the width of its descended dyadic interval (arithmetic coding's partition),
//! exactly normalized over the classes, positive, a dyadic of at most `B · M_f` bits. **`M_f` is
//! derived**: every digit face is a convex combination of binary KT faces, so
//! `q ≥ μ = 1/(2n* + 2)`; rounding moves `q` by at most `ε = 2^(−M_f−1)`, so
//! `|ln(q̂/q)| ≤ ε/(μ − ε)` per digit, in either direction, and `ε/(μ − ε) ≤ 2^(−M_f)(2n* + 2)`
//! when `2n* + 2 ≤ 2^(M_f)` (the first-order form `ε(2n* + 2)` fails when rounding moves the face
//! down). A cell's `B` digits together stay within `log₂ e/(4 L_R)`, below one grain `1/L_R`, when
//! `M_f = ⌈log₂(2n* + 2)⌉ + ⌈log₂(B L_R)⌉ + 2` ([`face_bits`]; `M_f = 23` at `n* = 6,148`, `B = 8`,
//! `L_R = 16`). The rule's a-priori bound per cell is `B · ε/(μ − ε) · 3/2`
//! ([`Landmarks::face_rule`], `log₂ e < 3/2`). Each cell's own certified residual against the ideal
//! face is `Σ_digits |q̂ − q| / min(q̂, q) · 3/2` (`|ln x| ≤ |x − 1|/min(x, 1)`), reported per cell
//! ([`CellReading::residual`]) and never above the rule's bound.
//! The deposit's β step uses the exact ideal faces. `Cell` stays exact in ℚ.
//!
//! [definition] **Faces.** [`Landmarks::probability`] is the executed face of one class, exact;
//! [`Landmarks::ideal_probability`] the ideal ℚ mixture (the same for `Cell`); [`Landmarks::face`]
//! all classes with their grain exponents (`hnn::masses::grain_exponent`), `Σ_c q(c) = 1` exactly:
//! the face the combined receiving read and the card consume.
//!
//! [definition; agent-inferred] **The depth** `D` is chosen on the development cells only
//! ([`choose_depth`]): `D` increases from 1 while the development prequential code length
//! decreases strictly (disjoint exact enclosures); the last `D` that decreased is chosen, every `D`
//! tried is reported, and `⌈log₂⌉` of the family tried is charged as description bits. The
//! development stream is the cut with its held-out cells removed; the held-out cells never choose
//! anything.
//!
//! [definition; agent-inferred, from the retention and deposition laws] **The measurement is
//! prequential** ([`prequential`]): every cell, development and held-out alike, is scored at the
//! current standing before its own deposit, then deposited. The online baselines
//! (`hnn::reference::Baselines`) already do exactly this, so the comparison is symmetric: the
//! located failure's third issue was that campaign 1's held-out cells were never deposited while
//! the baselines learned. "Held out" means the design was never chosen on these cells. Every coder
//! (tree `Digits`, its ideal face beside it, tree `Cell`, uniform, order-0 and order-1 KT, PPM-2)
//! is scored by the same rule, [`code_length`]: `log2_enclosure` of the face's reciprocal, summed by
//! `interval_sum`, where a face wider than `G = 98` significant bits ([`reading_bits`]: the
//! enclosure grid's 96 octaves and 2) is first bounded below by its `G`-bit mantissa and its
//! enclosure widened outward by the certified `3 · 2^(−G)`, below the grid every sum is rounded out
//! to. [agent-inferred] Only the trees' exact faces are that wide: a baseline's face is a product of
//! at most `PPM_ORDER + 2` ratios of integers at most `n* + |A|`, within `G` bits whenever
//! `n* + |A| ≤ 2^24` (the standing cut: `6,148 + 256`), so the baselines read exactly as
//! `log2_enclosure` reads them. `log2_enclosure`'s series on a face of thousands of bits costs one
//! to two orders of magnitude more than on its mantissa, and the widening only loosens the tree's
//! own enclosure, never a baseline's.
//!
//! [definition; agent-inferred] **The host realization** (the hardware law, `hnn::realization`'s
//! pattern). Within [`prequential`] the two trees and the baselines run together, and within
//! [`choose_depths`] the two emissions' sweeps: each region reads the shared immutable cut and
//! writes only its own tree and sums, so their effects commute and every value is the serial one.
//! Within one tree the cells stay serial: they share mutable counts along their paths and are
//! applied in the receiver's order.
//!
//! | Law | Lean `HNN/LandmarkTree` | Rust |
//! |---|---|---|
//! | the typed suffix address; an unfounded node reads the prior, and founding at first arrival keeps the law | `unfounded_reads_prior`, `founded_tree_same_law` | [`Letter`], [`address`], [`Landmarks::receive`] |
//! | the path face is positive and normalized for any `λ ∈ [0, 1]` | `path_face_normalized` | [`Landmarks::face`], [`Landmarks::ideal_probability`] |
//! | the likelihood-ratio step of β and the opened-path update | `weight_step`, `landmark_step` | [`Landmarks::receive`] |
//! | the telescope on an opened path | `path_telescope_exact` | [`OpenedPath::edge_ratios`] |
//! | Decision 27's region table is depth one with the root's split forced | `depth_one_is_decision_27` | [`LandmarkDeclaration::forced`] |
//! | the executed dyadic split and the cells' partition; the forced digits when `\|A\| < 2^B` | `executed_split_laws`, `cell_faces_partition`, `forced_digits_normalized` | [`Landmarks::probability`], [`Landmarks::face`] |
//! | a digit face's floor and the rounding's residual (the first-order bound fails downward) | `digit_face_ge`, `digit_log_residual`, `digit_log_residual_kt`, `host_digit_bound_fails_downward` | [`face_bits`], [`Landmarks::face_rule`], [`CellReading::residual`] |
//!
//! The β chart's per-node bound (`rebases · 2^(3−W)`) and the wide-face reading are stated here and
//! checked by the tests; their Lean statements are owed in #62 unless the Lean worker's branch
//! states them.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::compression::cost::ceil_log2;
use crate::hnn::HnnError;
use crate::hnn::masses::grain_exponent;
use crate::hnn::ratio::{LOG_OCTAVES, interval_sum, log2_enclosure};
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
    /// The letter's code: `0` for the boundary, `1 + code` for a cell (the preceding-cell region's
    /// numbering, `hnn::masses::Regions::PrecedingCell`).
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

/// [definition] **How the predicted cell is coded** (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Emission {
    Digits,
    Cell,
}

/// [definition] **A landmark tree's declaration**: the exterior chart's `|A|`, the address depth
/// `D`, the emission, the forced splits (context depths `d < forced` mix nothing, `λ_d = 0`), the
/// declared population `n*` bounding the passage, and the receiver's grain `L_R`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkDeclaration {
    pub alphabet: usize,
    pub depth: usize,
    pub emission: Emission,
    pub forced: usize,
    pub population: u64,
    pub grain: u64,
}

/// [definition; agent-inferred] **The β carrier width** `W`: the least width with `2^W > 8 L_R n*`,
/// so `n · 2^(3−W) < 1/L_R` for every `n ≤ n*` (module header).
pub fn carrier_width(population: u64, grain: u64) -> u64 {
    (BigUint::from(population) * BigUint::from(grain) * 8u32).bits()
}

/// [definition; agent-inferred] **The executed face's width** `M_f = ⌈log₂(2n* + 2)⌉ +
/// ⌈log₂(B L_R)⌉ + 2` over `B` digits (module header).
pub fn face_bits(population: u64, digits: u64, grain: u64) -> u64 {
    ceil_log2(&(BigUint::from(population) * 2u32 + 2u32))
        + ceil_log2(&(BigUint::from(digits) * BigUint::from(grain)))
        + 2
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

// -------------------------------------------------------------------------------------------
// the β chart

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
    // `a/b ∈ (2^(t−1), 2^(t+1))`, so `a 2^s / b ∈ (2^(W−1), 2^(W+1))` at `s = W − t`.
    let mut shift = width as i64 - (a.bits() as i64 - b.bits() as i64);
    let mut m = floor(shift);
    if m.bits() > width {
        shift -= 1;
        m = floor(shift);
    }
    debug_assert_eq!(m.bits(), width);
    (m, shift)
}

/// [definition; agent-inferred] **A carried mixture ratio** `β = (numerator/denominator) · 2^exponent`,
/// numerator and denominator odd and coprime, each below `2^W` (module header, "The β chart").
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

    /// **Carry a positive value at width `W`**: exactly when both odd parts fit, otherwise rebased
    /// to `m 2^(e−s)` with `m = ⌊v 2^s⌋ ∈ [2^(W−1), 2^W)`; the flag says whether it was rebased.
    pub fn carried(value: &Rat, width: u64) -> (Self, bool) {
        let (numerator, denominator) = (value.numer().magnitude(), value.denom().magnitude());
        let (twos_n, twos_d) = (
            numerator.trailing_zeros().unwrap_or(0),
            denominator.trailing_zeros().unwrap_or(0),
        );
        let (a, b) = (numerator >> twos_n, denominator >> twos_d);
        let exponent = twos_n as i64 - twos_d as i64;
        if a.bits() <= width && b.bits() <= width {
            return (
                Self {
                    numerator: a.to_u64().expect("an odd part within the carrier width"),
                    denominator: b.to_u64().expect("an odd part within the carrier width"),
                    exponent,
                },
                false,
            );
        }
        let (m, shift) = mantissa(&a, &b, width);
        let twos = m.trailing_zeros().unwrap_or(0);
        (
            Self {
                numerator: (m >> twos)
                    .to_u64()
                    .expect("a mantissa within the carrier width"),
                denominator: 1,
                exponent: exponent - shift + twos as i64,
            },
            true,
        )
    }
}

/// [definition] **The β chart's report**: the width `W`, the rebases in all and at the most-rebased
/// node, and their summed log₂ residual bounds `rebases · 2^(3−W)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReport {
    pub width: u64,
    pub rebases: u64,
    pub node_rebases: u64,
    pub residual_bound: Rat,
    pub node_bound: Rat,
}

// -------------------------------------------------------------------------------------------
// the tree

/// [definition] **One cell's reading** at the standing before its deposit: the executed face of the
/// cell, the ideal ℚ mixture's, and the certified bound on `|log₂(executed/ideal)|` (zero for
/// `Cell`, whose executed face is the ideal).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CellReading {
    pub executed: Rat,
    pub ideal: Rat,
    pub residual: Rat,
}

/// [definition] **One opened path**: the dyadic cell `h` whose tree it descends (`1` for `Cell`),
/// the symbol it emits there, how many of its nodes are founded, and its ideal faces
/// `q_0, …, q_D` of that symbol (an unfounded depth reads the prior).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedPath {
    pub dyadic: usize,
    pub symbol: usize,
    pub founded: usize,
    pub faces: Vec<Rat>,
}

impl OpenedPath {
    /// **The edge ratios** `R_(d→d+1) = q_(d+1)/q_d` along the path, whose logarithms are the
    /// path's additive cochain: `q_0 · Π_d R_(d→d+1) = q_D`.
    pub fn edge_ratios(&self) -> Vec<Rat> {
        self.faces
            .windows(2)
            .map(|pair| &pair[1] / &pair[0])
            .collect()
    }
}

/// [definition] **All classes' executed faces at one address**, each with its grain exponent
/// `2^(k_c) ≤ q(c)^(L_R) < 2^(k_c+1)`; `Σ_c q(c) = 1` exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkFace {
    pub grain: u64,
    pub probabilities: Vec<Rat>,
    pub exponents: Vec<BigInt>,
}

/// One tree's read at an address: its dyadic cell, the emitted symbol, its founded nodes and its
/// faces.
struct TreeRead {
    dyadic: usize,
    symbol: usize,
    nodes: Vec<u32>,
    faces: Vec<Rat>,
}

/// [definition] **The landmark tree** (module header): the declaration, its derived widths, the
/// arena and the chart's counts.
#[derive(Clone, Debug)]
pub struct Landmarks {
    declaration: LandmarkDeclaration,
    digits: u64,
    width: u64,
    face_bits: u64,
    roots: Vec<Option<u32>>,
    children: HashMap<u64, u32>,
    totals: Vec<u64>,
    binary: Vec<u64>,
    masses: HashMap<u64, u64>,
    beta: Vec<Beta>,
    rebased: Vec<u64>,
    rebases: u64,
    passed: u64,
}

fn key(high: u64, low: u64) -> u64 {
    (high << 32) | low
}

fn shape(what: &'static str, expected: usize, found: usize) -> HnnError {
    HnnError::Shape {
        what,
        expected,
        found,
    }
}

impl Landmarks {
    /// **Declare a tree**, empty: every node unfounded, so every face is uniform. Refused at an
    /// alphabet below two classes or past 32 bits, a zero population or grain, a forced depth past
    /// the address depth, or a carrier width past 63 bits.
    pub fn new(declaration: LandmarkDeclaration) -> Result<Self, HnnError> {
        let width = carrier_width(declaration.population, declaration.grain);
        Self::with_width(declaration, width)
    }

    /// **Declare a tree at a declared carrier width `W`** in place of the rule's. A width below the
    /// rule's gives up the node bound's place below one grain ([`ChartReport::node_bound`] reports
    /// it); the executed face stays exactly scored.
    pub fn with_width(declaration: LandmarkDeclaration, width: u64) -> Result<Self, HnnError> {
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
        if declaration.forced > declaration.depth {
            return Err(shape(
                "forced splits within the address depth",
                declaration.depth,
                declaration.forced,
            ));
        }
        if !(2..=63).contains(&width) {
            return Err(shape(
                "a β carrier width of 2 to 63 bits",
                63,
                usize::try_from(width).unwrap_or(usize::MAX),
            ));
        }
        let digits = ceil_log2(&BigUint::from(declaration.alphabet));
        let face_bits = face_bits(declaration.population, digits, declaration.grain);
        let roots = match declaration.emission {
            Emission::Digits => vec![None; 1 << digits],
            Emission::Cell => vec![None; 2],
        };
        Ok(Self {
            declaration,
            digits,
            width,
            face_bits,
            roots,
            children: HashMap::new(),
            totals: Vec::new(),
            binary: Vec::new(),
            masses: HashMap::new(),
            beta: Vec::new(),
            rebased: Vec::new(),
            rebases: 0,
            passed: 0,
        })
    }

    /// The declaration.
    pub fn declaration(&self) -> &LandmarkDeclaration {
        &self.declaration
    }

    /// `B = ⌈log₂|A|⌉`, the odometer digits of a cell.
    pub fn digits(&self) -> u64 {
        self.digits
    }

    /// `M_f`, the executed `Digits` face's width (module header).
    pub fn face_bits(&self) -> u64 {
        self.face_bits
    }

    /// The founded nodes.
    pub fn nodes(&self) -> usize {
        self.totals.len()
    }

    /// The cells passed (deposited).
    pub fn passed(&self) -> u64 {
        self.passed
    }

    /// **The β chart's report** (module header).
    pub fn chart(&self) -> ChartReport {
        let unit = two_power(3 - self.width as i64);
        let node_rebases = self.rebased.iter().copied().max().unwrap_or(0);
        ChartReport {
            width: self.width,
            rebases: self.rebases,
            node_rebases,
            residual_bound: Rat::from_integer(BigInt::from(self.rebases)) * &unit,
            node_bound: Rat::from_integer(BigInt::from(node_rebases)) * &unit,
        }
    }

    /// **The executed face's a-priori residual per cell** (`Digits`; zero for `Cell`):
    /// `B · ε/(μ − ε) · 3/2` with `ε = 2^(−M_f−1)` and `μ = 1/(2n* + 2)`, the rule's bound on
    /// `|log₂(executed/ideal)|` (Lean `HNN/LandmarkTree.{digit_log_residual,
    /// digit_log_residual_kt}`), within `log₂ e/(4 L_R)` by the choice of `M_f`.
    pub fn face_rule(&self) -> Rat {
        if self.declaration.emission == Emission::Cell {
            return Rat::zero();
        }
        let half_unit = two_power(-(self.face_bits as i64) - 1);
        let floor = Rat::new(
            BigInt::one(),
            BigInt::from(2 * self.declaration.population + 2),
        );
        Rat::from_integer(BigInt::from(self.digits)) * &half_unit / (floor - &half_unit)
            * log2_e_bound()
    }

    fn symbols(&self) -> u64 {
        match self.declaration.emission {
            Emission::Digits => 2,
            Emission::Cell => self.declaration.alphabet as u64,
        }
    }

    fn check(&self, address: &[Letter], class: usize) -> Result<(), HnnError> {
        if address.len() != self.declaration.depth {
            return Err(shape(
                "an address of the declared depth",
                self.declaration.depth,
                address.len(),
            ));
        }
        let alphabet = self.declaration.alphabet;
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

    /// Whether the dyadic cell at level `level` with prefix `prefix` splits: its upper half holds a
    /// class of the chart.
    fn splits(&self, level: u64, prefix: usize) -> bool {
        (((prefix << 1) | 1) << (self.digits - level - 1)) < self.declaration.alphabet
    }

    /// **The trees a class's emission opens**, with the symbol emitted in each: for `Digits` the
    /// splitting dyadic cells of its descent and its digit there (a forced digit opens nothing), for
    /// `Cell` the whole cell.
    fn emitted(&self, class: usize) -> Vec<(usize, usize)> {
        match self.declaration.emission {
            Emission::Cell => vec![(1, class)],
            Emission::Digits => (0..self.digits)
                .filter_map(|level| {
                    let prefix = class >> (self.digits - level);
                    let digit = (class >> (self.digits - level - 1)) & 1;
                    self.splits(level, prefix)
                        .then_some(((1usize << level) | prefix, digit))
                })
                .collect(),
        }
    }

    /// The founded nodes along an address in the tree at dyadic cell `h`, from its root.
    fn open(&self, dyadic: usize, address: &[Letter]) -> Vec<u32> {
        let mut nodes = Vec::with_capacity(address.len() + 1);
        let Some(root) = self.roots[dyadic] else {
            return nodes;
        };
        nodes.push(root);
        for letter in address {
            let parent = u64::from(*nodes.last().expect("a root"));
            match self.children.get(&key(parent, letter.code())) {
                Some(&child) => nodes.push(child),
                None => break,
            }
        }
        nodes
    }

    /// `(2C_s(c), 2N_s)`, the KT mass and total in half-units.
    fn kt(&self, node: u32, symbol: usize) -> (u64, u64) {
        let index = node as usize;
        let mass = match self.declaration.emission {
            Emission::Digits => self.binary[2 * index + symbol],
            Emission::Cell => self
                .masses
                .get(&key(u64::from(node), symbol as u64))
                .copied()
                .unwrap_or(1),
        };
        (mass, self.totals[index])
    }

    /// **The opened path's ideal faces** `q_0, …, q_D` of one symbol (module header).
    fn faces(&self, nodes: &[u32], symbol: usize) -> Vec<Rat> {
        let depth = self.declaration.depth;
        let prior = Rat::new(BigInt::one(), BigInt::from(self.symbols()));
        let mut faces = vec![prior; depth + 1];
        if nodes.len() == depth + 1 {
            let (mass, total) = self.kt(nodes[depth], symbol);
            faces[depth] = Rat::new(BigInt::from(mass), BigInt::from(total));
        }
        for d in (0..nodes.len().min(depth)).rev() {
            faces[d] = if d < self.declaration.forced {
                faces[d + 1].clone()
            } else {
                let beta = self.beta[nodes[d] as usize].value();
                let (mass, total) = self.kt(nodes[d], symbol);
                let (u, v) = (BigInt::from(mass), BigInt::from(total));
                let (n, m) = (beta.numer(), beta.denom());
                let (p, q) = (faces[d + 1].numer(), faces[d + 1].denom());
                // (β k + q')/(1 + β) with β = n/m, k = u/v, q' = p/q.
                Rat::new(n * &u * q + m * p * &v, (n + m) * &v * q)
            };
        }
        faces
    }

    /// Every tree a class opens, read at the current standing.
    fn read_trees(&self, address: &[Letter], class: usize) -> Vec<TreeRead> {
        self.emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| {
                let nodes = self.open(dyadic, address);
                let faces = self.faces(&nodes, symbol);
                TreeRead {
                    dyadic,
                    symbol,
                    nodes,
                    faces,
                }
            })
            .collect()
    }

    /// **The executed split** `q̂(0) = m/2^(M_f)` of an ideal digit face `q(0)`: the nearest
    /// multiple, `m = ⌊q(0) 2^(M_f) + ½⌋`, held inside `[1, 2^(M_f) − 1]`.
    fn split(&self, ideal_zero: &Rat) -> Rat {
        let scale = BigInt::one() << self.face_bits as usize;
        let (numerator, denominator) = (ideal_zero.numer(), ideal_zero.denom());
        let two = BigInt::from(2);
        let rounded: BigInt = (numerator * &scale * &two + denominator) / (denominator * &two);
        let top: BigInt = &scale - BigInt::one();
        let m = rounded.clamp(BigInt::one(), top);
        Rat::new(m, scale)
    }

    /// The cell's reading from its trees' reads.
    fn reading(&self, reads: &[TreeRead]) -> CellReading {
        let mut executed = Rat::one();
        let mut ideal = Rat::one();
        let mut residual = Rat::zero();
        for read in reads {
            let q = &read.faces[0];
            ideal *= q;
            match self.declaration.emission {
                Emission::Cell => executed *= q,
                Emission::Digits => {
                    let zero = if read.symbol == 0 {
                        q.clone()
                    } else {
                        Rat::one() - q
                    };
                    let split = self.split(&zero);
                    let face = if read.symbol == 0 {
                        split
                    } else {
                        Rat::one() - split
                    };
                    let least = if &face < q { face.clone() } else { q.clone() };
                    residual += (&face - q).abs() / least * log2_e_bound();
                    executed *= face;
                }
            }
        }
        CellReading {
            executed,
            ideal,
            residual,
        }
    }

    /// **The executed face of one class** at an address, exact.
    pub fn probability(&self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        self.check(address, class)?;
        Ok(self.reading(&self.read_trees(address, class)).executed)
    }

    /// **The ideal ℚ mixture's face of one class** at an address (the executed face for `Cell`).
    pub fn ideal_probability(&self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        self.check(address, class)?;
        Ok(self.reading(&self.read_trees(address, class)).ideal)
    }

    /// **The opened paths of one class** at an address, with their ideal faces.
    pub fn opened(&self, address: &[Letter], class: usize) -> Result<Vec<OpenedPath>, HnnError> {
        self.check(address, class)?;
        Ok(self
            .read_trees(address, class)
            .into_iter()
            .map(|read| OpenedPath {
                dyadic: read.dyadic,
                symbol: read.symbol,
                founded: read.nodes.len(),
                faces: read.faces,
            })
            .collect())
    }

    /// **All classes' executed faces at an address**, with their grain exponents at `grain`.
    pub fn face(&self, address: &[Letter], grain: u64) -> Result<LandmarkFace, HnnError> {
        self.check(address, 0)?;
        let alphabet = self.declaration.alphabet;
        let probabilities: Vec<Rat> = match self.declaration.emission {
            Emission::Cell => {
                let nodes = self.open(1, address);
                let weights = self.weights(&nodes);
                (0..alphabet)
                    .map(|class| self.mixed(&nodes, &weights, class))
                    .collect()
            }
            Emission::Digits => {
                // The executed split of every splitting dyadic cell, then each class's descent.
                let mut splits: Vec<Option<Rat>> = vec![None; 1 << self.digits];
                for level in 0..self.digits {
                    for prefix in 0..(1usize << level) {
                        if (prefix << (self.digits - level)) < alphabet
                            && self.splits(level, prefix)
                        {
                            let dyadic = (1usize << level) | prefix;
                            let nodes = self.open(dyadic, address);
                            let zero = self.faces(&nodes, 0).swap_remove(0);
                            splits[dyadic] = Some(self.split(&zero));
                        }
                    }
                }
                (0..alphabet)
                    .map(|class| {
                        let mut face = Rat::one();
                        for (dyadic, digit) in self.emitted(class) {
                            let split = splits[dyadic].as_ref().expect("a splitting cell");
                            face *= if digit == 0 {
                                split.clone()
                            } else {
                                Rat::one() - split
                            };
                        }
                        face
                    })
                    .collect()
            }
        };
        let exponents = probabilities
            .iter()
            .map(|p| grain_exponent(p.numer().magnitude(), p.denom().magnitude(), grain))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(LandmarkFace {
            grain,
            probabilities,
            exponents,
        })
    }

    /// The path's mixture weights over its read depths: `w_d = λ_d Π_(d'<d) (1 − λ_(d'))` at each
    /// founded interior depth and the rest at the terminal (the depth-`D` node, or the first
    /// unfounded depth reading the prior), so `q(c) = Σ_d w_d k_d(c)`.
    fn weights(&self, nodes: &[u32]) -> Vec<Rat> {
        let depth = self.declaration.depth;
        let interior = nodes.len().min(depth);
        let mut weights = Vec::with_capacity(interior + 1);
        let mut rest = Rat::one();
        for (d, &node) in nodes.iter().enumerate().take(interior) {
            if d < self.declaration.forced {
                weights.push(Rat::zero());
                continue;
            }
            let beta = self.beta[node as usize].value();
            let lambda = &beta / (Rat::one() + &beta);
            weights.push(&rest * &lambda);
            rest *= Rat::one() - lambda;
        }
        weights.push(rest);
        weights
    }

    /// `Σ_d w_d k_d(c)` over a path's read depths.
    fn mixed(&self, nodes: &[u32], weights: &[Rat], class: usize) -> Rat {
        let prior = Rat::new(BigInt::one(), BigInt::from(self.symbols()));
        weights
            .iter()
            .enumerate()
            .map(|(d, weight)| {
                let k = nodes.get(d).map_or_else(
                    || prior.clone(),
                    |&node| {
                        let (mass, total) = self.kt(node, class);
                        Rat::new(BigInt::from(mass), BigInt::from(total))
                    },
                );
                weight * k
            })
            .fold(Rat::zero(), |sum, term| sum + term)
    }

    /// **Receive one cell**: read its faces at the current standing, then deposit it on the paths it
    /// opened (module header). Refused before anything moves at a bad address or class, or past the
    /// declared population.
    pub fn receive(&mut self, address: &[Letter], class: usize) -> Result<CellReading, HnnError> {
        self.check(address, class)?;
        if self.passed >= self.declaration.population {
            return Err(HnnError::PopulationReached {
                population: self.declaration.population,
            });
        }
        let reads = self.read_trees(address, class);
        if self.totals.len() + reads.len() * (address.len() + 1) >= u32::MAX as usize {
            return Err(shape(
                "a landmark arena within 32-bit node numbers",
                u32::MAX as usize,
                self.totals.len(),
            ));
        }
        let reading = self.reading(&reads);
        for read in reads {
            self.deposit(address, read);
        }
        self.passed += 1;
        Ok(reading)
    }

    fn found(&mut self) -> u32 {
        let node = u32::try_from(self.totals.len()).expect("the arena is checked within 32 bits");
        self.totals.push(self.symbols());
        if self.declaration.emission == Emission::Digits {
            self.binary.extend([1, 1]);
        }
        self.beta.push(Beta::ONE);
        self.rebased.push(0);
        node
    }

    /// The deposit on one opened path: the old nodes' β steps bottom-up at the standing before it,
    /// the path's missing nodes founded, then each node's count of the symbol.
    fn deposit(&mut self, address: &[Letter], read: TreeRead) {
        let depth = self.declaration.depth;
        let forced = self.declaration.forced;
        let TreeRead {
            dyadic,
            symbol,
            mut nodes,
            faces,
        } = read;
        for d in (forced..nodes.len().min(depth)).rev() {
            let node = nodes[d];
            let (mass, total) = self.kt(node, symbol);
            let step = Rat::new(BigInt::from(mass), BigInt::from(total)) / &faces[d + 1];
            let (beta, rebased) =
                Beta::carried(&(self.beta[node as usize].value() * step), self.width);
            self.beta[node as usize] = beta;
            if rebased {
                self.rebased[node as usize] += 1;
                self.rebases += 1;
            }
        }
        if nodes.is_empty() {
            let root = self.found();
            self.roots[dyadic] = Some(root);
            nodes.push(root);
        }
        while nodes.len() < depth + 1 {
            let parent = u64::from(*nodes.last().expect("a root"));
            let letter = address[nodes.len() - 1].code();
            let child = self.found();
            self.children.insert(key(parent, letter), child);
            nodes.push(child);
        }
        for &node in nodes.iter().skip(forced) {
            let index = node as usize;
            match self.declaration.emission {
                Emission::Digits => self.binary[2 * index + symbol] += 2,
                Emission::Cell => {
                    *self
                        .masses
                        .entry(key(u64::from(node), symbol as u64))
                        .or_insert(1) += 2;
                }
            }
            self.totals[index] += 2;
        }
    }
}

// -------------------------------------------------------------------------------------------
// the measurement

/// [definition] **Code lengths on one population**, each an enclosure summed by `interval_sum`
/// over `cells` cells: the tree `Digits` (its executed dyadic face, and its ideal ℚ face beside
/// it), the tree `Cell`, and the online baselines.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Coded {
    pub digits: ExactInterval,
    pub digits_ideal: ExactInterval,
    pub cell: ExactInterval,
    pub uniform: ExactInterval,
    pub order_zero: ExactInterval,
    pub order_one: ExactInterval,
    pub ppm: ExactInterval,
    pub cells: u64,
}

/// [definition] **One tree's run**: its declaration, its chart's report, its founded nodes, its
/// executed face's width and a-priori residual, and the largest per-cell certified residual
/// against the ideal face over the run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeRun {
    pub declaration: LandmarkDeclaration,
    pub chart: ChartReport,
    pub nodes: usize,
    pub face_bits: u64,
    pub face_rule: Rat,
    pub largest_residual: Rat,
}

/// [definition] **The prequential measurement** ([`prequential`]): the development and held-out
/// populations' code lengths and each tree's run.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prequential {
    pub development: Coded,
    pub held_out: Coded,
    pub digits: TreeRun,
    pub cell: TreeRun,
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

/// [definition; agent-inferred] **The significant bits a wide face is read at**: `G = O + 2`, with
/// `O` the enclosure grid's octaves (`2^(−O)`, `hnn::ratio`'s `LOG_OCTAVES`), so the reading's
/// widening `3 · 2^(−G)` lies below the grid `interval_sum` rounds every sum out to.
pub fn reading_bits() -> u64 {
    u64::from(LOG_OCTAVES) + 2
}

/// [definition; agent-inferred] **A cell's code length** `−log₂ q`, enclosed (module header, "The
/// reading"): `log2_enclosure(1/q)` when `q`'s numerator and denominator fit `G` bits
/// ([`reading_bits`]); otherwise `q` is bounded below by its `G`-bit mantissa,
/// `q⁻ = m 2^(−s) ≤ q < q⁻ (1 + 1/m)`, and `−log₂ q ∈ [ℓ⁻ − 3 · 2^(−G), ℓ⁺]` with
/// `[ℓ⁻, ℓ⁺] = log2_enclosure(1/q⁻)`, since `log₂(1 + 1/m) ≤ log₂ e / m < 3 · 2^(−G)`.
pub fn code_length(probability: &Rat) -> Result<ExactInterval, HnnError> {
    let width = reading_bits();
    let (numerator, denominator) = (
        probability.numer().magnitude(),
        probability.denom().magnitude(),
    );
    if numerator.bits() <= width && denominator.bits() <= width {
        return log2_enclosure(&probability.recip());
    }
    let (m, shift) = mantissa(numerator, denominator, width);
    let lower = Rat::from_integer(BigInt::from(m)) * two_power(-shift);
    let read = log2_enclosure(&lower.recip())?;
    let widening = Rat::from_integer(BigInt::from(3)) * two_power(-(width as i64));
    ExactInterval::new(read.lower - widening, read.upper)
        .map_err(|_| shape("an ordered enclosure of a code length", 0, 1))
}

/// A tree's prequential sums over one stream: `[development, held-out]` executed and ideal, and the
/// run.
struct TreeSums {
    executed: [ExactInterval; 2],
    ideal: [ExactInterval; 2],
    run: TreeRun,
}

fn run_tree(
    cells: &[usize],
    held_out: &(dyn Fn(usize) -> bool + Sync),
    declaration: &LandmarkDeclaration,
) -> Result<TreeSums, HnnError> {
    let mut tree = Landmarks::new(declaration.clone())?;
    let (mut executed, mut ideal) = ([zero(), zero()], [zero(), zero()]);
    let mut largest_residual = Rat::zero();
    for (position, &class) in cells.iter().enumerate() {
        let reading = tree.receive(&address(cells, position, declaration.depth), class)?;
        let part = usize::from(held_out(position));
        executed[part] = interval_sum(&executed[part], &code_length(&reading.executed)?)?;
        ideal[part] = if declaration.emission == Emission::Cell {
            executed[part].clone()
        } else {
            interval_sum(&ideal[part], &code_length(&reading.ideal)?)?
        };
        if reading.residual > largest_residual {
            largest_residual = reading.residual;
        }
    }
    Ok(TreeSums {
        executed,
        ideal,
        run: TreeRun {
            declaration: declaration.clone(),
            chart: tree.chart(),
            nodes: tree.nodes(),
            face_bits: tree.face_bits(),
            face_rule: tree.face_rule(),
            largest_residual,
        },
    })
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

/// **The prequential measurement on a cut** (module header): the tree `Digits`, the tree `Cell` and
/// the online baselines over the same cells in the same order, each cell scored at the current
/// standing and then deposited, with enclosures on the development and held-out populations.
/// Refused unless the declarations are one `Digits` and one `Cell` over the same alphabet.
pub fn prequential(
    cut: &Cut,
    digits: &LandmarkDeclaration,
    cell: &LandmarkDeclaration,
) -> Result<Prequential, HnnError> {
    if digits.emission != Emission::Digits
        || cell.emission != Emission::Cell
        || digits.alphabet != cell.alphabet
    {
        return Err(shape(
            "one Digits and one Cell declaration over one alphabet",
            digits.alphabet,
            cell.alphabet,
        ));
    }
    let held_out = |position: usize| cut.held_out(position);
    let ((digit_sums, cell_sums), baselines) = rayon::join(
        || {
            rayon::join(
                || run_tree(&cut.cells, &held_out, digits),
                || run_tree(&cut.cells, &held_out, cell),
            )
        },
        || run_baselines(&cut.cells, &held_out, digits.alphabet),
    );
    let (digit_sums, cell_sums) = (digit_sums?, cell_sums?);
    let (baseline_sums, counts) = baselines?;
    let [development, held] = baseline_sums;
    let coded = |part: usize, baselines: BaselineCodes| Coded {
        digits: digit_sums.executed[part].clone(),
        digits_ideal: digit_sums.ideal[part].clone(),
        cell: cell_sums.executed[part].clone(),
        uniform: baselines.uniform,
        order_zero: baselines.order_zero,
        order_one: baselines.order_one,
        ppm: baselines.ppm,
        cells: counts[part],
    };
    Ok(Prequential {
        development: coded(0, development),
        held_out: coded(1, held),
        digits: digit_sums.run.clone(),
        cell: cell_sums.run.clone(),
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
/// while the development prequential code length of the executed face decreases strictly; the
/// declaration's own depth is ignored.
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
        let bits = run_tree(&cells, &never, &declared)?.executed[0].clone();
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

/// **Both emissions' depth sweeps**, run together (module header, the host realization).
pub fn choose_depths(
    cut: &Cut,
    digits: &LandmarkDeclaration,
    cell: &LandmarkDeclaration,
) -> Result<(DepthSweep, DepthSweep), HnnError> {
    let (digits, cell) = rayon::join(|| choose_depth(cut, digits), || choose_depth(cut, cell));
    Ok((digits?, cell?))
}
