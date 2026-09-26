//! **The receiving parametron's storage as a tree of landmarks, executed on a declared dyadic
//! lattice, addressed by typed bundles** (Decision 28; campaign 2's receiving letters; #73).
//!
//! [definition] The computational object is the helical pair interaction; this owner is the
//! receiving parametron's storage, read as a tree of landmarks. Of the winding guide's six general
//! objects it touches four: **faces and placement** (the receiving face, read at the receiver's
//! grain), the **tower thread** (the bundle restriction: an address restricts by dropping its oldest
//! whole bundle, and a cell's odometer digits descend its dyadic cell), the **pair** (each edge of an
//! opened path compares a node's face with its child's, `R_(d→d+1) = q_(d+1)/q_d`) and the
//! **helix** (a ring's phase class is the phase of a circle-plus-carry read at its grain; the β
//! chart's exponent is a carry and its mantissa the phase within the octave). A tree has no
//! two-cells, so no **cell holonomy** is claimed, and the **tube** is the passage itself, one cell
//! per tick.
//!
//! ```text
//! bundle     b_i = (x_i, f_i)   the tick of cell i: its cell and its declared features' letters, read
//!                              from the retained state after the tick (Lean HNN/LandmarkAddress)
//! address    a_j = [b_(j−1), …, b_(j−D)]  newest bundle first,  b_i = Boundary for i < 0      per cell
//! branches   cells:   [x_(j−1), …, x_(j−D)]                                     D letters
//!            bundles: [x_(j−1), f¹_(j−1), …, f^r_(j−1), x_(j−2), …]               D(1 + r) letters
//! digits     a cell c emits its B = ⌈log₂|A|⌉ odometer digits; digit i is read in the trees of its
//!            dyadic cell h (its digit prefix), a forced digit (empty upper half) opens nothing
//! KT         k_s(b) = (2n_s(b) + 1)/(2n_s + 2) in half-units, b ∈ {0, 1}
//! lattice    q̂_D = ⟦k_D(0)⟧ ;  q̂_d = ⟦λ̂_d k_d(0) + (1 − λ̂_d) q̂_(d+1)⟧ ;  λ̂_d = ⟦β_d/(1 + β_d)⟧₀¹
//!            ⟦x⟧ = nearest multiple of 2^(−M_p) (ties up) inside [2^(−M_p), 1 − 2^(−M_p)]
//! join       q̂_h = ⟦λ̂_h q̂_cells + (1 − λ̂_h) q̂_bundles⟧ ,  λ̂_h = ⟦β_h/(1 + β_h)⟧,  β_h = W_cells/W_bundles
//! split      (q̂, 1 − q̂) at each opened digit;  cell face = ∏ of its digits' splits
//! deposit    β'_d = β_d k_d(b)/q̂_(d+1)(b) bottom-up on each branch, β'_h = β_h q̂_cells(b)/q̂_bundles(b),
//!            then n_d(b) += 1
//! ```
//!
//! [definition] **Typed address letters** ([`Letter`]): `Boundary` (before the cut's first cell),
//! `Cell(code)` (a tick of the cell-only family) and `Bundle` (a tick's cell with its declared
//! features' letters, [`Bundle`]). The address of cell `j` is its preceding `D` bundles, newest
//! first, read per cell: causal, with no window pooling ([`address`], [`letter_address`]). A
//! bundle's code is `0` for the boundary and `1 + x + |A| · f` for a cell `x` with the features'
//! mixed-radix code `f` ([`LetterFamily::bundle_code`], injective: Lean
//! `HNN/LandmarkAddress.bundle_code_injective`); in a tree each typed letter is a child's key under
//! its parent, `0` for the boundary and `1 + value` otherwise.
//!
//! [definition; agent-inferred] **The declared family and its finite partitions** ([`LetterFamily`],
//! [`Feature`]), each derived from a declaration, never a literal:
//! - a ring's **phase class** `⌊g·phase⌋ mod g` at the ring's declared grain `g` (its period `d_g`,
//!   the ring's own port chart, where the fibre is empty; or the half-turn sheet `g = 2` of its
//!   parametron), `g` letters (Lean `phase_partition_finite`);
//! - a contact's **reading** (its owner's, `hnn::contact::ContactReading`, read by
//!   `hnn::receiving::LetterReader` from the retained clock and constitution): its **lock address**,
//!   `Unlocked` at the declared tolerance or a reduced `(p, q)`, `1 ≤ p ≤ P`, `1 ≤ q ≤ Q`, with `Q`
//!   the greatest denominator whose first return (`q` turns of the contact's second ring, Lean
//!   `Aeon/Clock/Lock.cycle_iff_period_dvd`) is observable within the aeon and `P` the first ring's
//!   bound alike (`hnn::contact::LockDeclaration::derived`; Lean `lock_partition_finite`), times
//!   its **site kind** over the proved `SiteKind` cases (`navigator::trace::SiteKind`, five). The
//!   slot's letter is the contact owner's (`ContactReading::letter`), so the partition and its rank
//!   have one owner.
//!
//! [definition; agent-inferred, Sol's review §2] **The enlarged tree keeps the cell-only branch.**
//! With no features declared the tree is campaign 1's cell tree, unchanged. With `r ≥ 1` features
//! each dyadic cell `h` carries two branches, the cell tree over `[x_(j−1), …]` and the bundle tree
//! over the flattened bundle word, joined at `h` by a two-face mixture weighed by its own
//! likelihood ratio (Lean `HNN/LandmarkTree.sequential_mixture`): the join's weight is
//! `½ W_cells + ½ W_bundles`, so the enlarged code length is at most the cell tree's plus one bit a
//! dyadic cell, and for every cell-only pruned tree `S` at most `Γ(S) + 1` plus its leaves' code
//! (Lean `HNN/LandmarkAddress.cell_only_dominance_with_feature_charge`), before the features'
//! description and the certified drift. The bundle tree restricts by whole bundles
//! (`bundle_restrict`): its node at `d(1 + r)` letters is the address restricted to `d` bundles.
//!
//! [definition] **The emission is the cell's odometer digits.** Digit `i` of class `c` is read at
//! its joint address: its digit prefix (the dyadic cell it descends) as a forced split, then the
//! context letters mixed by the trees of that dyadic cell, each node holding binary KT masses in
//! half-units. A dyadic cell whose upper half holds no class of the chart forces its digit with
//! face 1 and stores nothing, so every `|A| ≥ 2` is normalized. The whole-cell emission
//! (`|A|`-ary masses at each node) is retired: on the standing cut it never earned a split (the
//! record of September 26). Its depth-one forced case is Decision 27's region table (order-1's
//! `|A|`-ary KT face), whose law is kept in Lean only (`HNN/LandmarkTree.depth_one_is_decision_27`).
//!
//! [definition; agent-inferred, the primary's law] **Every quantity on the hot path is a
//! fixed-width integer on a declared dyadic lattice, with certified residuals, and the executed
//! face stays exactly normalized.** Each path face is a numerator of `2^(−M_p)` (`u64`), each stop
//! weight `λ̂` likewise, each count a half-unit integer (`u32`), each `β` an odd/odd ratio of `W`
//! bits with a binary exponent, and every product and quotient is formed in `u128`. The face is
//! positive and normalized for any `λ̂ ∈ [0, 1]` (`path_face_normalized`, `lattice_path_laws`): the
//! digit's executed split is `(q̂, 1 − q̂)`, and a cell's face is the width of its descended interval
//! (`cell_faces_partition`), a dyadic of at most `B · M_p` bits.
//!
//! [proved-derived; agent-inferred] **The widths**, derived from the passage `n*`, the grain `L_R`,
//! the digits `B` and the path depth `P` (no literal is tuned): `P = D` for the cell tree, and
//! `P = D + D(1 + r) + 2` for the enlarged tree, whose join adds both branches' residuals (the
//! drift terms `D² + (D(1 + r))² + 2(D + D(1 + r)) + 2 ≤ P²` and the rounding terms
//! `2D + 1 + 2D(1 + r) + 1 + 2 ≤ 2P + 1`). Write `K = 2n* + 2` (a binary KT face is at least
//! `1/K`, `digit_face_ge`), `ε = 2^(−M_p−1)` and `μ̂ = ⌊2^(M_p)/K⌋/2^(M_p)` (every lattice face is at
//! least `μ̂`, `lattice_path_floor`). Let `ρ_d` be `|ln q̂_d − ln q_d|` for the ideal tree
//! weighting `q`, `Δ_d = |ln β̂_d − ln β_d|` the chart's drift at the node, and `θ_d` a level's
//! rounding in `ln` (the stop weight's and the face's, at most `2^(−M_p)/min(q̂_d, k_d, q̂_(d+1))`,
//! the leaf's `ε/min(q̂_D, k_D)`, the join's `2^(−M_p)/min(q̂_h, q̂_cells, q̂_bundles)`).
//! - **Down the path**, `ρ_d ≤ Δ_d + ρ_(d+1) + θ_d` (`mix_ratio_bound`), so
//!   `ρ_0 ≤ Σ_(d<P) Δ_d + (2P + 1) ε/μ̂`; in absolute terms `|q̂_0 − q_0| ≤ (P + 1)ε + Σ|λ̂ − λ|`
//!   (`lattice_path_deviation`).
//! - **Over the passage**, `β̂ = E/P̂` with `P̂` the executed child's sequential probability, so the
//!   node's step telescopes (`lattice_step_telescope`) and its weight is 1-Lipschitz in `ln P̂`
//!   (`weight_log_lipschitz`): the drift is bounded by the rounding and rebases **summed over the
//!   subtree**, never compounded, `Δ_d ≤ n_s (2(P − d) − 1)(ε/μ̂ + 2^(1−W) + ρ_c)` with `n_s ≤ n*`
//!   the node's arrivals, `2^(1−W)` a mantissa rebase's `|ln(1 − r)|` (`rebase_log_residual`) and
//!   `ρ_c` a carrier rebase's (below).
//! - **A cell** has at most `B` opened digits and `Σ_(d<P) (2(P − d) − 1) = P²`, so
//!   `|log₂ q̂ − log₂ q| ≤ (3/2) B [(n* P² + 2P + 1) ε/μ̂ + n* P² (2^(1−W) + ρ_c)]` (`log₂ e < 3/2`).
//!   Each source is held within a quarter grain:
//!   - `M_p` is the least `M` with `2^M ≥ 3 B L_R K (n* P² + 2P + 1)` ([`face_bits`]);
//!   - `W` is the least width with `2^W ≥ 12 B L_R n* P²` ([`carrier_width`]);
//!   - the carrier rebase keeps a denominator of `R = 126 − W ≥ W` bits, so `ρ_c < 2^(1−R)` and its
//!     share is below a quarter grain too (the rebase is taken only when its product can overflow;
//!     otherwise `ρ_c = 0` and the rule is campaign 1's);
//!   - the certificates are summed on the grid `2^(−C)`, `C = M_p + W`: every rounding term is at
//!     least `2^(−M_p)` and every rebase term at least `2^(−W)`, so rounding each up on the grid
//!     inflates it by at most `1 + 2^(−min(M_p, W))`.
//!
//!   At the standing cut (`n* = 6,148 = 2²·29·53`, `L_R = 16`, `B = 8`, `D = 4`, cells only):
//!   `M_p = 39`, `W = 28`, `C = 67`; the rule's bound per cell ([`Landmarks::face_rule`]) is below
//!   half a grain.
//!
//! [definition; agent-inferred, Sol's review §4] **The carrier rebases past `u128`.** The β step's
//! carrier `(N, D) = (β_n k_n, β_d k_d x)` (odd parts of `β`, the KT face `k = k_n/k_d` in half-units,
//! the child's lattice numerator `x`) is carried exactly while its mantissa's division fits `u128`.
//! Before it can overflow (`2W + κ + M_p + 1 > 128`, `κ` the bits of `K`), the carrier rebases by a
//! common power of two, `N 2^s = 2^e N̂` exactly and `D = 2^e D̂ + r_D` with `D̂` of `R` bits, and the
//! remainder `r_D` is released: the ratio lies in `(N̂/(D̂ + 1), N̂/D̂]`, whose logarithmic width is
//! below `1/D̂` (Lean `HNN/LandmarkCarrier.{rebase_decode, rebase_ratio_enclosed}`). That width is
//! added to the node's drift and excess certificates, the same terms that carry a mantissa rebase
//! through every later KT, path and mixture step (`rebase_step_enclosed`, `rebase_log_residual_sum`,
//! `width_or_rebase_total`). The widths are never reduced to fit the carrier: `M_p` and `W` stay the
//! rule's. The declaration is refused only when a lattice product itself passes `u128`
//! (`2M_p + κ + 3`, `2W + M_p + 3` or `W + κ + M_p` above 128 bits, or `R < W`). Campaign 1's
//! `|A| = 256`, `D = 4` tree was refused from 87,382 cells; it now declares to `2^19` cells.
//!
//! [definition] **The certificate is carried, not recomputed** (the per-cell residual without the
//! ideal). Each node and each join carries two bounds on the grid `2^(−C)`: `drift` ≥ `Δ` and
//! `excess` ≥ `|L̂ − L|`, its routed subsequence's executed code length against the ideal in `ln`. A
//! deposit adds, bottom-up along each opened path, the read's `θ_d` plus twice the rebases' units
//! to the node's excess and the child's excess increment plus the rebases' units to its drift
//! (`|ln(1 − r)| ≤ r/(1 − r) < 1/m'` for the kept mantissa `m' ∈ [2^(W−1), 2^W)`, and `1/D̂` for a
//! carrier release); a join adds both branch roots' increments. A read's residual is
//! `ρ ≤ Σ drift + Σ θ` per opened digit over both branches and the join, and a cell's
//! ([`CellReading::residual`]) is the digits' sum in `log₂` (times `3/2`), never above the rule.
//!
//! [definition; agent-inferred] **The arena** (the layout the card ports). Nodes are founded at
//! first arrival and numbered in founding order, `u32`; every per-node value is a flat vector
//! indexed by the node: its depth with its branch in the top bit and its two half-unit masses
//! `2C_0, 2C_1` (their sum is the total; the arena the oracle shares), and its chart: `β`, the cached
//! stop weight `λ̂`, its rebases and its two certificates. `roots[t]` is the root of tree
//! `t = branch · 2^B + h` (the heap index `h = 2^i + prefix` of the dyadic cell), `children` a hash
//! table from `(parent << 32) | letter` to the child, and `joins[h]` each dyadic cell's join chart
//! (enlarged trees only). An unfounded node reads as the prior: a path read stops at its first
//! unfounded node, whose face is exactly `1/2`. `Clone` copies the arena, linear in the founded
//! nodes: 92 bytes a node in the flat vectors on x86-64 (the chart 80, the masses 8, the depth 4)
//! and a 16-byte table entry with its control byte; `PartialEq` compares the table as a map (std's
//! `HashMap`). The reads and the deposit are one law (`Law`) acting on any standing (`Standing`):
//! the tree's own, or a window's working overlay (below).
//!
//! [definition; agent-inferred] **A window in cell order** ([`Landmarks::window_faces`], Decision 29
//! within a window; consumed by `hnn::receiving::ReceivingPhases::tree_faces`). A receiving window
//! compares `A` cells at once, and phase `j` reads the tree at the standing after the window's
//! earlier phases' deposits: their targets are known at compare, so those deposits are applied, in
//! cell order, to a working overlay (`Working`). The nodes and joins a deposit writes are copied
//! from the tree at their first write, the nodes it founds are numbered after the tree's, and every
//! other node reads through to the tree, which is never written. The deposit then applies the same
//! steps to the published tree in the same order, by the same law, so each overlay's face is the
//! face the deposited tree reads (the test
//! `landmark_window_faces_read_each_phase_after_the_earlier_deposits`). [established-bounded;
//! measured] On the standing cut's cell tree before its last window (63,280 nodes; exterior wall
//! time on one host, the mean over 50 runs in integer µs): a clone takes 211 µs; the window's two
//! faces read in cell order take 122 µs and read with nothing known 73 µs. [agent-inferred] An
//! overlay admits arrivals past the declared population by the window's own earlier cells while
//! the widths' operands at that count fit `u128`; its faces are exact executed faces, normalized
//! for any stop weight, and its certificates are not read.
//!
//! [definition] **Faces.** [`Landmarks::probability`] is one class's executed face, exact;
//! [`Landmarks::face`] all classes with their grain exponents, `Σ_c q̂(c) = 1` exactly: the face the
//! receiving read and the card consume. It reads each splitting dyadic cell's paths once, each
//! branch bounded by its splitting ancestor's founded depth in that branch (a node founded in a
//! dyadic cell's tree is founded in its ancestors'), multiplies the splits down the dyadic heap, and
//! decides each grain exponent `⌊L_R log₂ q̂⌋` by a certified binary logarithm (exact integer
//! squaring, [`binary_log`]) with the exact comparison (`grain_exponent`) as its fallback.
//! [`Landmarks::splits`] returns the splits alone (the digit-0 numerator at every splitting dyadic
//! cell), the quantity the card's read returns and the host completes ([`LandmarkFace::of_splits`]).
//!
//! [definition; agent-inferred] **The ideal tree weighting is a reference oracle**
//! ([`IdealLandmarks`]): the same arena with `β` in ℚ and every face exact, the join included,
//! consumed by the tests and by the notebook's report of the executed face's cost. It is never on
//! the hot path; at scale it carries `β` at the reference width
//! `W_o = O + ⌈log₂(3 B n*² P²)⌉` ([`IdealLandmarks::reference_width`], `O` the enclosure grid's
//! octaves), whose rebases keep its code length within `2^(−O)` of the ideal over the passage.
//!
//! [definition; agent-inferred] **The depth and the family** are chosen on the development cells
//! only ([`choose_depth`]): `D` increases from `max(1, forced)` while the development prequential
//! code length decreases strictly (disjoint exact enclosures), every `D` tried is reported, and
//! `⌈log₂⌉` of the family tried is charged as description bits. The held-out cells never choose
//! anything.
//!
//! [definition; agent-inferred, from the retention and deposition laws] **The measurement is
//! prequential** ([`prequential`], Decision 29): every cell is scored at the current standing
//! before its own deposit, then deposited, for the tree and the online baselines alike. The tree's
//! faces and the oracle's are read by [`code_length`], `log₂ d − log₂ n` of `q = n/d` by the
//! certified binary logarithm ([`binary_log`]) within the enclosure grid `2^(−O)`; the baselines
//! read their own faces through `hnn::reference`. Both are certified enclosures of `−log₂ q`, and
//! every ordering is decided by disjoint enclosures.
//!
//! [definition; agent-inferred] **The host realization** (the hardware law). Within
//! [`prequential`] the tree and the baselines run together: each reads the shared immutable cut
//! and writes only its own state and sums, so their effects commute and every value is the serial
//! one. Within one tree the cells stay serial: they share mutable counts along their paths.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the typed suffix address; an unfounded node reads the prior, and founding at first arrival keeps the law | `HNN/LandmarkTree.{unfounded_reads_prior, founded_tree_same_law}` | [`Letter`], [`address`], [`Landmarks::deposit`] |
//! | the bundle: causal, restricted by whole bundles, its code injective, its partitions finite | `HNN/LandmarkAddress.{bundle_causal, bundle_restrict, feature_scale_square, bundle_code_injective, phase_partition_finite, lock_partition_finite}` | [`Bundle`], [`LetterFamily`], [`Feature`] (the contact slot's letter is `hnn::contact::ContactReading::letter`), [`letter_address`] |
//! | the enlarged tree keeps the cell-only branch | `HNN/LandmarkAddress.cell_only_dominance_with_feature_charge` | the join (`Law::digit`), [`Landmarks::face_rule`] |
//! | the path face is positive and normalized for any `λ ∈ [0, 1]`; on the lattice too | `HNN/LandmarkTree.{path_face_normalized, lattice_path_laws}` | [`Landmarks::face`], [`Landmarks::probability`] |
//! | the lattice path's floor, its deviation adding down the path, and the executed face's bound with the address residual | `HNN/LandmarkTree.{lattice_path_floor, lattice_path_deviation, executed_face_bound}` | [`face_bits`], [`CellReading::residual`] |
//! | the mixture moves by at most the factors of `β` and of the child's face | `HNN/LandmarkTree.mix_ratio_bound` | [`CellReading::residual`] |
//! | the likelihood-ratio step of β, the opened-path update, and its executed telescope with a rebase | `HNN/LandmarkTree.{weight_step, landmark_step, lattice_step_telescope, lattice_node_telescope, weight_log_lipschitz}` | [`Landmarks::deposit`], [`ChartReport`] |
//! | a mantissa rebase's residual; the carrier's rebase, its enclosure and its total | `HNN/LandmarkTree.rebase_log_residual`; `HNN/LandmarkCarrier.{rebase_decode, rebase_ratio_enclosed, rebase_step_enclosed, rebase_log_residual_sum, width_or_rebase_total}` | [`Beta::carry`], [`Beta::step`], [`carrier_width`] |
//! | the telescope on an opened path | `HNN/LandmarkTree.path_telescope_exact` | [`OpenedPath::edge_ratios`] |
//! | the executed dyadic split and the cells' partition; the forced digits when `\|A\| < 2^B` | `HNN/LandmarkTree.{executed_split_laws, cell_faces_partition, forced_digits_normalized}` | [`Landmarks::probability`], [`Landmarks::face`] |
//! | a digit face's floor and the rounding's residual (the first-order bound fails downward) | `HNN/LandmarkTree.{digit_face_ge, digit_log_residual, host_digit_bound_fails_downward}` | [`Landmarks::face_rule`] |
//! | the ideal tree weighting (the oracle) | `HNN/LandmarkTree.{landmark_step, mixture_is_probability, kraft_and_dominance, sequential_mixture}` | [`IdealLandmarks`] |
//! | a window's phases in cell order: each reads the standing after the earlier phases' deposits | `HNN/LandmarkTree.{landmark_step, treeWeight_arrive_off}` | [`Landmarks::window_faces`] |
//!
//! [open] Owed in #62 (Lean `HNN/LandmarkTree`'s `[open]`): the passage-level composition of the
//! drift bound (the subtree sum over the tree and the passage, from `lattice_node_telescope`,
//! `weight_log_lipschitz` and `mix_ratio_bound`) into the per-cell rule, and the certified binary
//! logarithm's squaring invariant; both are checked by the tests, the first cell by cell against
//! the oracle.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::compression::cost::ceil_log2;
use crate::hnn::HnnError;
use crate::hnn::contact::{ContactReading, LockDeclaration};
use crate::hnn::field::Field;
use crate::hnn::ratio::{LOG_OCTAVES, interval_sum};
use crate::hnn::realization::indexed;
use crate::hnn::receiving::grain_exponent;
use crate::hnn::reference::{BaselineCodes, Baselines, Cut};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;

// -------------------------------------------------------------------------------------------
// letters, bundles and the declared family

/// [definition] **A typed bundle**: an earlier tick's cell with its declared features' letters,
/// their mixed-radix code over the family's slots ([`LetterFamily::encode`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bundle {
    pub cell: usize,
    pub features: u32,
}

/// [definition] **A typed address letter**: the boundary before the cut's first cell, a cell of
/// the cell-only family, or a bundle of a declared family.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Letter {
    Boundary,
    Cell(usize),
    Bundle(Bundle),
}

impl Letter {
    /// The cell letter's code: `0` for the boundary, `1 + code` for a cell (a bundle's cell).
    pub fn code(self) -> u64 {
        match self {
            Letter::Boundary => 0,
            Letter::Cell(code) | Letter::Bundle(Bundle { cell: code, .. }) => 1 + code as u64,
        }
    }

    /// The tick's cell, or none at the boundary.
    pub fn cell(self) -> Option<usize> {
        match self {
            Letter::Boundary => None,
            Letter::Cell(code) | Letter::Bundle(Bundle { cell: code, .. }) => Some(code),
        }
    }
}

/// [definition] **One declared feature slot of a bundle**.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Feature {
    /// Ring `ring`'s phase class `⌊g·phase⌋ mod g` at its declared grain `g`.
    Phase { ring: usize, grain: u64 },
    /// Contact `contact`'s reading (`hnn::contact::ContactReading`): its lock address in the lock
    /// family at its derived bound `(P, Q)`, and its site kind.
    Contact {
        contact: usize,
        bound: LockDeclaration,
    },
}

impl Feature {
    /// **A contact's letter**, its bound derived from the field (`LockDeclaration::derived`: `Q`
    /// the greatest denominator whose first return, `q` turns of the contact's second ring, Lean
    /// `Aeon/Clock/Lock.cycle_iff_period_dvd`, is observable within the aeon, and `P` the first
    /// ring's alike; Lean `HNN/LandmarkAddress.lock_partition_finite`), never a literal.
    pub fn contact(field: &Field, contact: usize) -> Self {
        Feature::Contact {
            contact,
            bound: LockDeclaration::derived(field, contact),
        }
    }

    /// **The slot's finite alphabet**: `g` phase classes, or the contact's letters (its lock
    /// family's letters times the five site kinds, `hnn::contact::ContactReading::letters`).
    pub fn size(&self) -> Result<u64, HnnError> {
        match self {
            Feature::Phase { grain, .. } => Ok(*grain),
            Feature::Contact { bound, .. } => ContactReading::letters(bound),
        }
    }

    /// A contact reading's value in this slot (`hnn::contact::ContactReading::letter`).
    pub fn contact_value(&self, reading: &ContactReading) -> Result<u64, HnnError> {
        match self {
            Feature::Contact { bound, .. } => reading.letter(bound),
            Feature::Phase { .. } => Err(shape("a contact slot for a contact reading", 1, 0)),
        }
    }
}

/// [definition] **The declared letter family**: the feature slots each bundle carries after its
/// cell, in order. The empty family is the cell-only tree (campaign 1).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct LetterFamily {
    features: Vec<Feature>,
    /// Each slot's alphabet `s_i`, read once at the declaration.
    sizes: Vec<u64>,
}

impl LetterFamily {
    /// The cell-only family.
    pub fn cells() -> Self {
        Self::default()
    }

    /// **Declare a family**, refused at an empty slot or when the slots' product passes 32 bits.
    pub fn new(features: Vec<Feature>) -> Result<Self, HnnError> {
        let mut product = 1u64;
        let mut sizes = Vec::with_capacity(features.len());
        for feature in &features {
            let size = feature.size()?;
            if size == 0 {
                return Err(shape("a feature slot of at least one letter", 1, 0));
            }
            product = product.saturating_mul(size);
            if product > u64::from(u32::MAX) {
                return Err(shape(
                    "a family whose features' code fits 32 bits",
                    u32::MAX as usize,
                    usize::try_from(product).unwrap_or(usize::MAX),
                ));
            }
            sizes.push(size);
        }
        Ok(Self { features, sizes })
    }

    pub fn features(&self) -> &[Feature] {
        &self.features
    }

    /// Each slot's alphabet `s_i`.
    pub fn sizes(&self) -> &[u64] {
        &self.sizes
    }

    /// `r`, the feature slots.
    pub fn slots(&self) -> usize {
        self.features.len()
    }

    pub fn is_empty(&self) -> bool {
        self.features.is_empty()
    }

    /// Whether a slot reads a contact (its readings need the constitution's site kinds).
    pub fn reads_contacts(&self) -> bool {
        self.features
            .iter()
            .any(|feature| matches!(feature, Feature::Contact { .. }))
    }

    /// `Π_i s_i`, the features' codes.
    pub fn codes(&self) -> u64 {
        self.sizes.iter().product()
    }

    /// **The features' mixed-radix code** `Σ_i v_i Π_(k<i) s_k`, refused at a value outside its slot.
    pub fn encode(&self, values: &[u64]) -> Result<u32, HnnError> {
        if values.len() != self.features.len() {
            return Err(shape(
                "one value per feature slot",
                self.features.len(),
                values.len(),
            ));
        }
        let mut code = 0u64;
        let mut radix = 1u64;
        for (value, &size) in values.iter().zip(&self.sizes) {
            if *value >= size {
                return Err(shape(
                    "a feature value within its slot",
                    usize::try_from(size).unwrap_or(usize::MAX),
                    usize::try_from(*value).unwrap_or(usize::MAX),
                ));
            }
            code += value * radix;
            radix *= size;
        }
        Ok(u32::try_from(code).expect("the family's codes fit 32 bits"))
    }

    /// The slot values of a features' code.
    pub fn decode(&self, code: u32) -> Vec<u64> {
        let mut rest = u64::from(code);
        self.sizes
            .iter()
            .map(|&size| {
                let value = rest % size;
                rest /= size;
                value
            })
            .collect()
    }

    /// **The bundle's code** (Lean `HNN/LandmarkAddress.bundle_code_injective`): `0` for the
    /// boundary and `1 + x + |A| · f` for a cell `x` with the features' code `f`.
    pub fn bundle_code(&self, letter: Letter, alphabet: usize) -> u64 {
        match letter {
            Letter::Boundary => 0,
            Letter::Cell(cell) => 1 + cell as u64,
            Letter::Bundle(Bundle { cell, features }) => {
                1 + cell as u64 + alphabet as u64 * u64::from(features)
            }
        }
    }

    /// `1 + |A| · Π_i s_i`, the bundles' codes with the boundary.
    pub fn bundle_codes(&self, alphabet: usize) -> u64 {
        1 + alphabet as u64 * self.codes()
    }

    /// **The letters a bundle writes into the bundle tree**: its cell, then its slots, each `0` at
    /// the boundary and `1 + value` otherwise.
    fn flatten_into(&self, letter: Letter, flat: &mut Vec<u32>) {
        match letter {
            Letter::Boundary => flat.extend(std::iter::repeat_n(0, 1 + self.slots())),
            Letter::Cell(cell) => flat.push(1 + cell as u32),
            Letter::Bundle(Bundle { cell, features }) => {
                flat.push(1 + cell as u32);
                flat.extend(self.decode(features).into_iter().map(|v| 1 + v as u32));
            }
        }
    }
}

/// [definition] **The address of cell `position`**: `[x_(j−1), …, x_(j−D)]`, newest first, with
/// `Boundary` for every position before the cut's first cell (the cell-only family).
pub fn address(cells: &[usize], position: usize, depth: usize) -> Vec<Letter> {
    (1..=depth)
        .map(|back| {
            position
                .checked_sub(back)
                .map_or(Letter::Boundary, |at| Letter::Cell(cells[at]))
        })
        .collect()
}

/// [definition] **The address of cell `position` in a stream of ticks' letters**:
/// `[b_(j−1), …, b_(j−D)]`, newest first, `Boundary` before the stream's first tick.
pub fn letter_address(letters: &[Letter], position: usize, depth: usize) -> Vec<Letter> {
    (1..=depth)
        .map(|back| {
            position
                .checked_sub(back)
                .map_or(Letter::Boundary, |at| letters[at])
        })
        .collect()
}

/// **The cell-only family's letters** of a stream: each tick's cell.
pub fn cell_letters(cells: &[usize]) -> Vec<Letter> {
    cells.iter().map(|&cell| Letter::Cell(cell)).collect()
}

// -------------------------------------------------------------------------------------------
// the declaration and its derived widths

/// [definition] **A landmark tree's declaration**: the exterior chart's `|A|`, the address depth
/// `D` in bundles, the forced splits of the cell tree (context depths `d < forced` mix nothing,
/// `λ_d = 0`), the declared population `n*` bounding the passage, the receiver's grain `L_R`, and
/// the declared letter family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LandmarkDeclaration {
    pub alphabet: usize,
    pub depth: usize,
    pub forced: usize,
    pub population: u64,
    pub grain: u64,
    pub family: LetterFamily,
}

impl LandmarkDeclaration {
    /// **The branches' depths in letters**: the cell tree's `D`, then, with features declared, the
    /// bundle tree's `D(1 + r)`.
    pub fn branch_depths(&self) -> Vec<usize> {
        if self.family.is_empty() {
            vec![self.depth]
        } else {
            vec![self.depth, self.depth * (1 + self.family.slots())]
        }
    }

    /// **Each branch's letters of an address** (the tree's keys under their parents): the cells'
    /// codes, then, with features declared, the flattened bundles (module header, "branches").
    pub fn letters(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.branch_depths()
            .iter()
            .enumerate()
            .map(|(branch, &depth)| {
                let mut flat = Vec::with_capacity(depth);
                for &letter in address {
                    if branch == 0 {
                        flat.push(letter.code() as u32);
                    } else {
                        self.family.flatten_into(letter, &mut flat);
                    }
                }
                flat
            })
            .collect()
    }

    fn odometer(&self) -> Odometer {
        Odometer {
            alphabet: self.alphabet,
            digits: odometer_digits(self.alphabet),
        }
    }

    /// **The digits a class opens**: `(h, b)`, the splitting dyadic cells of its descent with its
    /// digit in each (a forced digit opens nothing).
    pub fn emitted(&self, class: usize) -> Vec<(usize, usize)> {
        self.odometer().emitted(class)
    }

    /// **The splitting dyadic cells**, heap-ordered: the order of [`Splits::numerators`].
    pub fn splitting(&self) -> Vec<usize> {
        self.odometer().splitting()
    }

    /// **The path depth `P` the widths' rule reads** (module header, "The widths"): `D`, or
    /// `D + D(1 + r) + 2` for the enlarged tree.
    pub fn path_depth(&self) -> u64 {
        let depths = self.branch_depths();
        if depths.len() == 1 {
            depths[0] as u64
        } else {
            depths.iter().map(|&d| d as u64).sum::<u64>() + 2
        }
    }
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
/// `2^M ≥ 3 B L_R (2n* + 2)(n* P² + 2P + 1)`, which holds the lattice's rounding within a quarter
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
/// `2^W ≥ 12 B L_R n* P²`, which holds the rebases' drift within a quarter grain a cell (module
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
/// widths"): the digits `B`, the path lattice `M_p`, the β carrier `W`, the certificates' grid
/// `C = M_p + W`, and the carrier rebase's denominator width `R = 126 − W` when the β step's
/// product can pass `u128` (else `0`: no carrier rebase is ever taken).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Widths {
    pub digits: u64,
    pub face: u64,
    pub carrier: u64,
    pub certificate: u64,
    pub rebase: u64,
}

impl Widths {
    /// The widths the rule derives from a declaration.
    pub fn derived(declaration: &LandmarkDeclaration) -> Self {
        let digits = odometer_digits(declaration.alphabet);
        let carrier = carrier_width(
            declaration.population,
            digits,
            declaration.grain,
            declaration.path_depth(),
        );
        Self::with_carrier(declaration, carrier)
    }

    /// The derived widths with a declared carrier `W` in place of the rule's.
    fn with_carrier(declaration: &LandmarkDeclaration, carrier: u64) -> Self {
        let digits = odometer_digits(declaration.alphabet);
        let face = face_bits(
            declaration.population,
            digits,
            declaration.grain,
            declaration.path_depth(),
        );
        let kappa = floor_reciprocal(declaration.population).bits();
        let rebase = if 2 * carrier + kappa + face + 1 > u64::from(u128::BITS) {
            126u64.saturating_sub(carrier)
        } else {
            0
        };
        Self {
            digits,
            face,
            carrier,
            certificate: face + carrier,
            rebase,
        }
    }

    /// The largest `u128` operand the widths ask for, in bits: the lattice mixture `2M + κ + 3`,
    /// the stop weight `2W + M + 3`, the β step's carrier `W + κ + M` and, unless the carrier
    /// rebases, its mantissa division `2W + κ + M + 1`, with `κ` the bits of `2n* + 2`.
    fn operand_bits(&self, population: u64) -> u64 {
        let kappa = floor_reciprocal(population).bits();
        let (m, w) = (self.face, self.carrier);
        let division = if self.rebase > 0 {
            self.rebase + w + 1
        } else {
            2 * w + kappa + m + 1
        };
        (2 * m + kappa + 3)
            .max(2 * w + m + 3)
            .max(w + kappa + m)
            .max(division)
    }

    /// Whether the widths at a population admit every product in `u128`, the carrier rebase
    /// keeping at least `W` bits.
    fn admitted(&self, population: u64) -> bool {
        let kappa = floor_reciprocal(population).bits();
        let rebase_needed = 2 * self.carrier + kappa + self.face + 1 > u64::from(u128::BITS);
        let rebase_kept = !rebase_needed || 126u64.saturating_sub(self.carrier) >= self.carrier;
        rebase_kept
            && (2 * self.face + kappa + 3)
                .max(2 * self.carrier + self.face + 3)
                .max(self.carrier + kappa + self.face)
                <= u64::from(u128::BITS)
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

fn bits128(x: u128) -> u64 {
    u64::from(u128::BITS - x.leading_zeros())
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

/// [definition] **One carried step of β**: the carried ratio, the kept mantissa when the odd parts
/// were rebased to `W` bits, and the carrier's rebased denominator `D̂` when its remainder was
/// released (module header, "The carrier rebases past `u128`").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Carried {
    pub beta: Beta,
    pub mantissa: Option<u128>,
    pub released: Option<u128>,
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

    /// The odd numerator, the odd denominator and the binary exponent (the carry).
    pub fn parts(&self) -> (u64, u64, i64) {
        (self.numerator, self.denominator, self.exponent)
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
        let carried = Self::step(numerator, denominator, exponent, width, 0);
        debug_assert!(carried.released.is_none());
        (carried.beta, carried.mantissa)
    }

    /// **One step of the carried ratio with the carrier's rebase** (module header, "The carrier
    /// rebases past `u128`"; Lean `HNN/LandmarkCarrier`): the ratio `(N/D) · 2^exponent` carried
    /// at width `W` as [`Beta::carry`] carries it, except that when the mantissa's division
    /// `N 2^s / D` would pass `u128` (`W + bits(D) > 128`), `D`'s odd part first rebases to its
    /// top `R` bits (`rebase`, `R ≥ W`): `D = 2^e D̂ + r_D`, the exponent takes `−e`, and a
    /// nonzero remainder is released, the carried ratio then lying in `[1, 1 + 1/D̂)` times the
    /// exact one (`released = Some(D̂)`). The operands must be positive.
    pub fn step(
        numerator: u128,
        denominator: u128,
        exponent: i64,
        width: u64,
        rebase: u64,
    ) -> Carried {
        debug_assert!(numerator > 0 && denominator > 0);
        let (twos_n, twos_d) = (numerator.trailing_zeros(), denominator.trailing_zeros());
        let (mut a, mut b) = (numerator >> twos_n, denominator >> twos_d);
        let mut exponent = exponent + i64::from(twos_n) - i64::from(twos_d);
        let mut released = None;
        if width + bits128(b) > u64::from(u128::BITS) {
            debug_assert!(rebase >= width);
            // The carrier's rebase: keep `D`'s top `R` bits; `N 2^s` is exact at any `s ≥ e`.
            let e = bits128(b) - rebase;
            let kept = b >> e;
            if kept << e != b {
                released = Some(kept);
            }
            b = kept;
            exponent -= e as i64;
            let twos = b.trailing_zeros();
            b >>= twos;
            exponent -= i64::from(twos);
        }
        let common = odd_gcd(a, b);
        (a, b) = (a / common, b / common);
        if bits128(a) <= width && bits128(b) <= width && released.is_none() {
            return Carried {
                beta: Self {
                    numerator: a as u64,
                    denominator: b as u64,
                    exponent,
                },
                mantissa: None,
                released,
            };
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
        let mut shift = width as i64 - (bits128(a) as i64 - bits128(b) as i64);
        let mut mantissa = floor(shift);
        if bits128(mantissa) > width {
            shift -= 1;
            mantissa = floor(shift);
        }
        debug_assert_eq!(bits128(mantissa), width);
        let twos = mantissa.trailing_zeros();
        Carried {
            beta: Self {
                numerator: (mantissa >> twos) as u64,
                denominator: 1,
                exponent: exponent - shift + i64::from(twos),
            },
            mantissa: Some(mantissa),
            released,
        }
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
/// most-rebased node or join, the carrier's releases, and the largest drift certificate over the
/// nodes and joins, `|log₂ β̂ − log₂ β|` in bits (the `drift` times `3/2`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartReport {
    pub carrier: u64,
    pub rebases: u64,
    pub node_rebases: u64,
    pub released: u64,
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

    /// Every splitting dyadic cell, heap-ordered (a parent before its children).
    fn splitting(&self) -> Vec<usize> {
        (0..self.digits)
            .flat_map(|level| (0..1usize << level).map(move |prefix| (level, prefix)))
            .filter(|&(level, prefix)| self.splits(level, prefix))
            .map(|(level, prefix)| (1usize << level) | prefix)
            .collect()
    }
}

/// The top bit of a node's depth word: its branch (the bundle tree).
const BRANCH_BIT: u32 = 1 << 31;

/// The arena's topology and masses, shared by the executed tree and the oracle: the roots per
/// tree, the child table, each node's depth (its branch in the top bit) and its two half-unit
/// masses.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Arena {
    roots: Vec<Option<u32>>,
    children: HashMap<u64, u32>,
    depths: Vec<u32>,
    halves: Vec<[u32; 2]>,
}

fn key(parent: u32, letter: u32) -> u64 {
    (u64::from(parent) << 32) | u64::from(letter)
}

/// **The founded nodes as a read opens them**: the root of each tree, the child behind a letter,
/// each node's two half-unit masses and the count of founded nodes. The arena answers them (for
/// the oracle and the executed tree), and so does a window's working overlay ([`Working`]).
trait Topology {
    fn root(&self, tree: usize) -> Option<u32>;
    fn child(&self, parent: u32, letter: u32) -> Option<u32>;
    fn halves(&self, node: u32) -> [u32; 2];
    fn len(&self) -> usize;

    /// The founded nodes along an address in tree `t`, from its root, at most `limit` of them.
    fn open(&self, tree: usize, address: &[u32], limit: usize) -> Vec<u32> {
        let mut nodes = Vec::with_capacity(address.len() + 1);
        if limit == 0 {
            return nodes;
        }
        let Some(root) = self.root(tree) else {
            return nodes;
        };
        nodes.push(root);
        for letter in address {
            if nodes.len() >= limit {
                break;
            }
            match self.child(*nodes.last().expect("a root"), *letter) {
                Some(child) => nodes.push(child),
                None => break,
            }
        }
        nodes
    }

    /// `(2C_b, 2N)`, the node's KT mass of `b` and its total, in half-units.
    fn kt(&self, node: u32, symbol: usize) -> (u64, u64) {
        let [zero, one] = self.halves(node);
        (
            u64::from([zero, one][symbol]),
            u64::from(zero) + u64::from(one),
        )
    }

    /// Refused when founding `nodes` more would pass 31-bit node numbers.
    fn founded_within(&self, nodes: usize) -> Result<(), HnnError> {
        if self.len() + nodes >= BRANCH_BIT as usize {
            return Err(shape(
                "a landmark arena within 31-bit node numbers",
                BRANCH_BIT as usize,
                self.len(),
            ));
        }
        Ok(())
    }
}

impl Topology for Arena {
    fn root(&self, tree: usize) -> Option<u32> {
        self.roots[tree]
    }

    fn child(&self, parent: u32, letter: u32) -> Option<u32> {
        self.children.get(&key(parent, letter)).copied()
    }

    fn halves(&self, node: u32) -> [u32; 2] {
        self.halves[node as usize]
    }

    fn len(&self) -> usize {
        self.halves.len()
    }
}

impl Arena {
    fn new(trees: usize) -> Self {
        Self {
            roots: vec![None; trees],
            children: HashMap::new(),
            depths: Vec::new(),
            halves: Vec::new(),
        }
    }

    fn found(&mut self, branch: usize, depth: usize) -> u32 {
        let node = u32::try_from(self.len()).expect("the arena is checked within 31 bits");
        let depth = u32::try_from(depth).expect("a depth within 31 bits");
        self.depths
            .push(depth | if branch == 1 { BRANCH_BIT } else { 0 });
        self.halves.push([1, 1]);
        node
    }

    /// Found the path's missing nodes in tree `t` of `branch` (the root, then each child along the
    /// address), returning how many were founded.
    fn extend(
        &mut self,
        tree: usize,
        branch: usize,
        address: &[u32],
        nodes: &mut Vec<u32>,
    ) -> usize {
        let before = self.len();
        if nodes.is_empty() {
            let root = self.found(branch, 0);
            self.roots[tree] = Some(root);
            nodes.push(root);
        }
        while nodes.len() < address.len() + 1 {
            let parent = *nodes.last().expect("a root");
            let child = self.found(branch, nodes.len());
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
}

/// **The executed tree's standing as a deposit moves it** (module header, "The arena"): the
/// founded nodes with their charts, the joins, the rebases and the cells passed. The tree's own
/// [`Nodes`] carry it, and so does a window's working overlay ([`Working`]).
trait Standing: Topology {
    fn chart(&self, node: u32) -> &Chart;
    fn chart_mut(&mut self, node: u32) -> &mut Chart;
    fn join(&self, dyadic: usize) -> &Chart;
    fn join_mut(&mut self, dyadic: usize) -> &mut Chart;
    fn halves_mut(&mut self, node: u32) -> &mut [u32; 2];
    /// Found a node at `depth` of `branch` in tree `t`, its root (`parent` absent) or the child
    /// behind `(parent, letter)`, with the prior masses `[1, 1]` and `chart`.
    fn found(
        &mut self,
        tree: usize,
        branch: usize,
        parent: Option<(u32, u32)>,
        depth: usize,
        chart: Chart,
    ) -> u32;
    fn passed(&self) -> u64;
    fn pass(&mut self);
    fn rebased(&mut self);
    fn released(&mut self);
}

/// The executed tree's own standing: the arena, each node's chart, each dyadic cell's join chart
/// (enlarged trees), the rebases, the carrier's releases and the cells passed.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Nodes {
    arena: Arena,
    charts: Vec<Chart>,
    joins: Vec<Chart>,
    rebases: u64,
    releases: u64,
    passed: u64,
}

impl Topology for Nodes {
    fn root(&self, tree: usize) -> Option<u32> {
        self.arena.root(tree)
    }

    fn child(&self, parent: u32, letter: u32) -> Option<u32> {
        self.arena.child(parent, letter)
    }

    fn halves(&self, node: u32) -> [u32; 2] {
        self.arena.halves[node as usize]
    }

    fn len(&self) -> usize {
        self.arena.len()
    }
}

impl Standing for Nodes {
    fn chart(&self, node: u32) -> &Chart {
        &self.charts[node as usize]
    }

    fn chart_mut(&mut self, node: u32) -> &mut Chart {
        &mut self.charts[node as usize]
    }

    fn join(&self, dyadic: usize) -> &Chart {
        &self.joins[dyadic]
    }

    fn join_mut(&mut self, dyadic: usize) -> &mut Chart {
        &mut self.joins[dyadic]
    }

    fn halves_mut(&mut self, node: u32) -> &mut [u32; 2] {
        &mut self.arena.halves[node as usize]
    }

    fn found(
        &mut self,
        tree: usize,
        branch: usize,
        parent: Option<(u32, u32)>,
        depth: usize,
        chart: Chart,
    ) -> u32 {
        let node = self.arena.found(branch, depth);
        self.charts.push(chart);
        match parent {
            None => self.arena.roots[tree] = Some(node),
            Some((parent, letter)) => {
                self.arena.children.insert(key(parent, letter), node);
            }
        }
        node
    }

    fn passed(&self) -> u64 {
        self.passed
    }

    fn pass(&mut self) {
        self.passed += 1;
    }

    fn rebased(&mut self) {
        self.rebases += 1;
    }

    fn released(&mut self) {
        self.releases += 1;
    }
}

/// [definition; agent-inferred] **A working overlay on the tree** (module header, "A window in
/// cell order"): the nodes and joins a window's earlier phases' deposits wrote, each copied from
/// the tree at its first write, and the nodes they founded, numbered after the tree's; every other
/// node reads through to the tree, which is never written.
#[derive(Clone, Debug)]
struct Working<'a> {
    base: &'a Nodes,
    charts: HashMap<u32, Chart>,
    joins: HashMap<usize, Chart>,
    halves: HashMap<u32, [u32; 2]>,
    founded: Vec<([u32; 2], Chart)>,
    roots: HashMap<usize, u32>,
    children: HashMap<u64, u32>,
    passed: u64,
}

impl<'a> Working<'a> {
    fn on(base: &'a Nodes) -> Self {
        Self {
            base,
            charts: HashMap::new(),
            joins: HashMap::new(),
            halves: HashMap::new(),
            founded: Vec::new(),
            roots: HashMap::new(),
            children: HashMap::new(),
            passed: 0,
        }
    }

    /// The index of a node the overlay founded, or `None` for a node of the tree.
    fn fresh(&self, node: u32) -> Option<usize> {
        (node as usize).checked_sub(self.base.len())
    }
}

impl Topology for Working<'_> {
    fn root(&self, tree: usize) -> Option<u32> {
        self.roots
            .get(&tree)
            .copied()
            .or_else(|| self.base.root(tree))
    }

    fn child(&self, parent: u32, letter: u32) -> Option<u32> {
        self.children
            .get(&key(parent, letter))
            .copied()
            .or_else(|| self.base.child(parent, letter))
    }

    fn halves(&self, node: u32) -> [u32; 2] {
        match self.fresh(node) {
            Some(index) => self.founded[index].0,
            None => self
                .halves
                .get(&node)
                .copied()
                .unwrap_or_else(|| self.base.halves(node)),
        }
    }

    fn len(&self) -> usize {
        self.base.len() + self.founded.len()
    }
}

impl Standing for Working<'_> {
    fn chart(&self, node: u32) -> &Chart {
        match self.fresh(node) {
            Some(index) => &self.founded[index].1,
            None => self
                .charts
                .get(&node)
                .unwrap_or_else(|| self.base.chart(node)),
        }
    }

    fn chart_mut(&mut self, node: u32) -> &mut Chart {
        match self.fresh(node) {
            Some(index) => &mut self.founded[index].1,
            None => {
                let base = self.base;
                self.charts.entry(node).or_insert_with(|| *base.chart(node))
            }
        }
    }

    fn join(&self, dyadic: usize) -> &Chart {
        self.joins
            .get(&dyadic)
            .unwrap_or_else(|| self.base.join(dyadic))
    }

    fn join_mut(&mut self, dyadic: usize) -> &mut Chart {
        let base = self.base;
        self.joins
            .entry(dyadic)
            .or_insert_with(|| *base.join(dyadic))
    }

    fn halves_mut(&mut self, node: u32) -> &mut [u32; 2] {
        match self.fresh(node) {
            Some(index) => &mut self.founded[index].0,
            None => {
                let base = self.base;
                self.halves.entry(node).or_insert_with(|| base.halves(node))
            }
        }
    }

    fn found(
        &mut self,
        tree: usize,
        _branch: usize,
        parent: Option<(u32, u32)>,
        _depth: usize,
        chart: Chart,
    ) -> u32 {
        let node = u32::try_from(self.len()).expect("the arena is checked within 31 bits");
        self.founded.push(([1, 1], chart));
        match parent {
            None => {
                self.roots.insert(tree, node);
            }
            Some((parent, letter)) => {
                self.children.insert(key(parent, letter), node);
            }
        }
        node
    }

    fn passed(&self) -> u64 {
        self.base.passed + self.passed
    }

    fn pass(&mut self) {
        self.passed += 1;
    }

    fn rebased(&mut self) {}

    fn released(&mut self) {}
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
    let family = &declaration.family;
    for letter in address {
        match *letter {
            Letter::Boundary => {}
            Letter::Cell(code) | Letter::Bundle(Bundle { cell: code, .. }) if code >= alphabet => {
                return Err(HnnError::CellOutside { code, alphabet });
            }
            Letter::Cell(_) if !family.is_empty() => {
                return Err(shape(
                    "a bundle letter of the declared family",
                    family.slots(),
                    0,
                ));
            }
            Letter::Bundle(Bundle { features, .. })
                if family.is_empty() || u64::from(features) >= family.codes() =>
            {
                return Err(shape(
                    "a bundle's features within the declared family",
                    usize::try_from(family.codes()).unwrap_or(usize::MAX),
                    features as usize,
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

fn check_declaration(declaration: &LandmarkDeclaration) -> Result<(), HnnError> {
    if declaration.alphabet < 2 || declaration.alphabet >= u32::MAX as usize / 2 {
        return Err(shape(
            "a landmark tree over at least two classes, within 31 bits",
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
    let largest = declaration
        .family
        .sizes()
        .iter()
        .copied()
        .max()
        .unwrap_or(0);
    if largest >= u64::from(u32::MAX) {
        return Err(shape(
            "a feature slot's letters within 32 bits",
            u32::MAX as usize,
            usize::try_from(largest).unwrap_or(usize::MAX),
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

/// [definition] **One opened path**: the dyadic cell `h` whose tree it descends and the branch (`0`
/// the cells, `1` the bundles), the digit it emits there, how many of its nodes are founded, its
/// faces `q_0, …, q_(min(f, D))` of that digit (the executed lattice faces from
/// [`Landmarks::opened`], the ideal ones from [`IdealLandmarks::opened`]; the first unfounded depth
/// reads the prior `1/2`), and at each founded depth the node's KT face `k_d` of the digit and its
/// carried `β_d`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedPath {
    pub dyadic: usize,
    pub branch: usize,
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

/// [definition; agent-inferred] **The splits of one address** ([`Landmarks::splits`]): at each
/// splitting dyadic cell `h` (heap-ordered, [`Landmarks::splitting`]), the executed digit-0 face's
/// numerator on `2^(−M_p)`. The class faces are their products down the dyadic heap
/// ([`LandmarkFace::of_splits`]); this is what a card's read returns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Splits {
    pub face_bits: u64,
    pub numerators: Vec<u64>,
}

impl LandmarkFace {
    /// **The all-class face from its splits** (module header, "Faces"): each class's face the
    /// product of its opened digits' splits, each grain exponent decided by the certified binary
    /// logarithm with the exact comparison as its fallback. Refused unless there is one split per
    /// splitting dyadic cell.
    pub fn of_splits(
        declaration: &LandmarkDeclaration,
        splits: &Splits,
        grain: u64,
    ) -> Result<Self, HnnError> {
        let odometer = Odometer {
            alphabet: declaration.alphabet,
            digits: odometer_digits(declaration.alphabet),
        };
        let splitting = odometer.splitting();
        if splits.numerators.len() != splitting.len() {
            return Err(shape(
                "one split per splitting dyadic cell",
                splitting.len(),
                splits.numerators.len(),
            ));
        }
        let cells = 1usize << odometer.digits;
        let mut split = vec![None; cells];
        for (&h, &zero) in splitting.iter().zip(&splits.numerators) {
            split[h] = Some(zero);
        }
        let full = 1u64 << splits.face_bits;
        // The heap over dyadic cells: each class's descent, multiplied down the splits.
        let mut numerators: Vec<Option<BigUint>> = vec![None; 2 * cells];
        let mut opened = vec![0u64; 2 * cells];
        numerators[1] = Some(BigUint::one());
        for level in 0..odometer.digits {
            for prefix in 0..(1usize << level) {
                if !odometer.holds(level, prefix) {
                    continue;
                }
                let h = (1usize << level) | prefix;
                let numerator = numerators[h].take().expect("a held cell's descent");
                match split[h] {
                    Some(zero) => {
                        for (child, side) in [(2 * h, zero), (2 * h + 1, full - zero)] {
                            numerators[child] = Some(&numerator * side);
                            opened[child] = opened[h] + 1;
                        }
                    }
                    None => {
                        opened[2 * h] = opened[h];
                        numerators[2 * h] = Some(numerator);
                    }
                }
            }
        }
        let mut probabilities = Vec::with_capacity(declaration.alphabet);
        let mut exponents = Vec::with_capacity(declaration.alphabet);
        for class in 0..declaration.alphabet {
            let leaf = cells | class;
            let numerator = numerators[leaf].take().expect("a class's descent");
            let exponent = opened[leaf] * splits.face_bits;
            exponents.push(dyadic_grain_exponent(&numerator, exponent, grain)?);
            probabilities.push(dyadic(numerator, exponent));
        }
        Ok(Self {
            grain,
            probabilities,
            exponents,
        })
    }
}

/// **The class faces of a window's splits** ([`LandmarkFace::of_splits`] per phase): the phases
/// read alone and run together (`hnn::realization`: each reads its own splits and writes its own
/// face).
pub fn faces_of_splits(
    declaration: &LandmarkDeclaration,
    splits: &[Splits],
    grain: u64,
) -> Result<Vec<LandmarkFace>, HnnError> {
    indexed(splits.len(), |j| {
        LandmarkFace::of_splits(declaration, &splits[j], grain)
    })
}

/// The executed chart of one node or join: its carried β, the cached stop weight `λ̂` (a numerator
/// of `2^(−M_p)`), its rebases, and its certificates on `2^(−C)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Chart {
    beta: Beta,
    stop: u64,
    rebases: u32,
    drift: u128,
    excess: u128,
}

/// One branch's executed read at an address: the tree it descends, the founded nodes from the
/// root, and the lattice faces of the digit `0`, `q̂_d(0)` as numerators of `2^(−M_p)`, at
/// `d = 0, …, min(f, D_b)` (the first unfounded depth `f` reads the prior `2^(M_p − 1)`).
#[derive(Clone, Debug)]
struct LatticeRead {
    tree: usize,
    branch: usize,
    symbol: usize,
    nodes: Vec<u32>,
    faces: Vec<u64>,
}

/// One digit's executed read: its dyadic cell, its digit, each branch's read and the digit-0 face
/// at the top (the join's in an enlarged tree, the cell branch's otherwise).
#[derive(Clone, Debug)]
struct DigitRead {
    dyadic: usize,
    symbol: usize,
    reads: Vec<LatticeRead>,
    face: u64,
}

/// One branch of the law: its depth in letters and its forced depths.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Branch {
    depth: usize,
    forced: usize,
}

/// The tree's law, apart from its standing: the declaration, its derived widths, the odometer and
/// the branches. Its reads and its deposit act on any [`Standing`], the tree's own or a working
/// overlay.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Law {
    declaration: LandmarkDeclaration,
    widths: Widths,
    odometer: Odometer,
    branches: Vec<Branch>,
}

/// [definition] **The landmark tree, executed** (module header): the declaration, its derived
/// widths, the arena with each node's chart and each join, and the chart's counts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Landmarks {
    law: Law,
    nodes: Nodes,
}

impl Law {
    fn new(declaration: LandmarkDeclaration, widths: Widths) -> Self {
        let odometer = Odometer {
            alphabet: declaration.alphabet,
            digits: widths.digits,
        };
        let branches = declaration
            .branch_depths()
            .into_iter()
            .enumerate()
            .map(|(branch, depth)| Branch {
                depth,
                forced: if branch == 0 { declaration.forced } else { 0 },
            })
            .collect();
        Self {
            declaration,
            widths,
            odometer,
            branches,
        }
    }

    fn full(&self) -> u64 {
        1u64 << self.widths.face
    }

    fn cells(&self) -> usize {
        1usize << self.widths.digits
    }

    fn joined(&self) -> bool {
        self.branches.len() > 1
    }

    /// Tree `t = branch · 2^B + h`.
    fn tree(&self, branch: usize, dyadic: usize) -> usize {
        branch * self.cells() + dyadic
    }

    /// **Each branch's letters** of an address: the cells, then the flattened bundles.
    fn flatten(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.declaration.letters(address)
    }

    /// `⟦2^M u/v⟧`: the lattice numerator nearest `u/v` (ties up), inside `[1, 2^M − 1]`.
    fn round(&self, numerator: u128, denominator: u128) -> u64 {
        let rounded = (2 * numerator + denominator) / (2 * denominator);
        (rounded as u64).clamp(1, self.full() - 1)
    }

    /// A certificate on `2^(−C)` in `ln`, read in bits: times `3/2 > log₂ e`.
    fn certified_bits(&self, units: u128) -> Rat {
        Rat::new(
            BigInt::from(units) * 3,
            BigInt::from(2u32) << self.widths.certificate as usize,
        )
    }

    /// The fresh chart of a node or join: `β = 1`, `λ̂ = 1/2`, no certificate.
    fn fresh(&self) -> Chart {
        Chart {
            beta: Beta::ONE,
            stop: self.full() / 2,
            rebases: 0,
            drift: 0,
            excess: 0,
        }
    }

    /// The leaf's lattice face `⟦k(0)⟧`.
    fn leaf(&self, nodes: &impl Standing, node: u32) -> u64 {
        let (u, v) = nodes.kt(node, 0);
        self.round(u128::from(u) << self.widths.face, u128::from(v))
    }

    /// The mixing node's lattice face `⟦λ̂ k(0) + (1 − λ̂) q̂'⟧`, on `2^M v` as the common
    /// denominator.
    fn mix(&self, nodes: &impl Standing, node: u32, below: u64) -> u64 {
        let (u, v) = nodes.kt(node, 0);
        let face = self.widths.face;
        let stop = u128::from(nodes.chart(node).stop);
        let full = u128::from(self.full());
        let numerator =
            ((stop * u128::from(u)) << face) + (full - stop) * u128::from(below) * u128::from(v);
        self.round(numerator, u128::from(v) << face)
    }

    /// The join's lattice face `⟦λ̂_h q̂_cells + (1 − λ̂_h) q̂_bundles⟧`.
    fn join_face(&self, nodes: &impl Standing, dyadic: usize, cells: u64, bundles: u64) -> u64 {
        let stop = u128::from(nodes.join(dyadic).stop);
        let full = u128::from(self.full());
        self.round(
            stop * u128::from(cells) + (full - stop) * u128::from(bundles),
            full,
        )
    }

    /// **One branch's executed read** at its letters in tree `t`, at most `limit` founded nodes.
    fn read(
        &self,
        nodes: &impl Standing,
        branch: usize,
        dyadic: usize,
        symbol: usize,
        letters: &[u32],
        limit: usize,
    ) -> LatticeRead {
        let Branch { depth, forced } = self.branches[branch];
        let tree = self.tree(branch, dyadic);
        let path = nodes.open(tree, letters, limit);
        let top = path.len().min(depth);
        let mut faces = vec![0u64; top + 1];
        faces[top] = if path.len() == depth + 1 {
            self.leaf(nodes, path[depth])
        } else {
            self.full() / 2
        };
        for d in (0..top).rev() {
            faces[d] = if d < forced {
                faces[d + 1]
            } else {
                self.mix(nodes, path[d], faces[d + 1])
            };
        }
        LatticeRead {
            tree,
            branch,
            symbol,
            nodes: path,
            faces,
        }
    }

    /// **One digit's executed read**: each branch's read, joined in an enlarged tree.
    fn digit(
        &self,
        nodes: &impl Standing,
        dyadic: usize,
        symbol: usize,
        letters: &[Vec<u32>],
        limits: &[usize],
    ) -> DigitRead {
        let reads: Vec<LatticeRead> = (0..self.branches.len())
            .map(|branch| {
                self.read(
                    nodes,
                    branch,
                    dyadic,
                    symbol,
                    &letters[branch],
                    limits[branch],
                )
            })
            .collect();
        let face = if self.joined() {
            self.join_face(nodes, dyadic, reads[0].faces[0], reads[1].faces[0])
        } else {
            reads[0].faces[0]
        };
        DigitRead {
            dyadic,
            symbol,
            reads,
            face,
        }
    }

    /// Every digit a class opens, read at the standing.
    fn reads(&self, nodes: &impl Standing, address: &[Letter], class: usize) -> Vec<DigitRead> {
        let letters = self.flatten(address);
        let limits: Vec<usize> = self.branches.iter().map(|b| b.depth + 1).collect();
        self.odometer
            .emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| self.digit(nodes, dyadic, symbol, &letters, &limits))
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
    fn rounding(&self, nodes: &impl Standing, read: &LatticeRead, d: usize) -> u128 {
        let Widths {
            face, certificate, ..
        } = self.widths;
        let Branch { depth, forced } = self.branches[read.branch];
        if d >= read.nodes.len() || d < forced {
            return 0;
        }
        let (u, v) = nodes.kt(read.nodes[d], read.symbol);
        let here = u128::from(self.side(read.faces[d], read.symbol));
        let kt =
            |shift: u64| ceil_div(u128::from(v) << (certificate - face - shift), u128::from(u));
        if d == depth {
            let lattice = ceil_div(1u128 << (certificate - 1), here);
            lattice.max(kt(1))
        } else {
            let below = u128::from(self.side(read.faces[d + 1], read.symbol));
            let lattice = ceil_div(1u128 << certificate, here.min(below));
            lattice.max(kt(0))
        }
    }

    /// **The join's rounding bound** `θ_h = 2^(−M)/min(q̂_h, q̂_cells, q̂_bundles)` on `2^(−C)`.
    fn join_rounding(&self, digit: &DigitRead) -> u128 {
        let side = |zero: u64| u128::from(self.side(zero, digit.symbol));
        let least = side(digit.face)
            .min(side(digit.reads[0].faces[0]))
            .min(side(digit.reads[1].faces[0]));
        ceil_div(1u128 << self.widths.certificate, least)
    }

    /// `ρ ≤ Σ drift + Σ θ` of one branch's read on `2^(−C)`.
    fn certificate(&self, nodes: &impl Standing, read: &LatticeRead) -> u128 {
        let Branch { depth, forced } = self.branches[read.branch];
        let mixing = read.nodes.len().min(depth);
        let drift = (forced..mixing)
            .map(|d| nodes.chart(read.nodes[d]).drift)
            .fold(0u128, u128::saturating_add);
        (0..read.faces.len())
            .map(|d| self.rounding(nodes, read, d))
            .fold(drift, u128::saturating_add)
    }

    /// One digit's certificate: its branches' and, in an enlarged tree, the join's drift and
    /// rounding.
    fn digit_certificate(&self, nodes: &impl Standing, digit: &DigitRead) -> u128 {
        let branches = digit
            .reads
            .iter()
            .map(|read| self.certificate(nodes, read))
            .fold(0u128, u128::saturating_add);
        if self.joined() {
            branches
                .saturating_add(nodes.join(digit.dyadic).drift)
                .saturating_add(self.join_rounding(digit))
        } else {
            branches
        }
    }

    /// The cell's reading from its digits' reads.
    fn reading(&self, nodes: &impl Standing, digits: &[DigitRead]) -> CellReading {
        let mut numerator = BigUint::one();
        let mut certificate = 0u128;
        for digit in digits {
            numerator *= self.side(digit.face, digit.symbol);
            certificate = certificate.saturating_add(self.digit_certificate(nodes, digit));
        }
        CellReading {
            executed: dyadic(numerator, digits.len() as u64 * self.widths.face),
            residual: self.certified_bits(certificate),
        }
    }

    /// **The splits at an address** (module header, "Faces"): each splitting dyadic cell's digit-0
    /// face, heap-ordered, each branch's read bounded by its splitting ancestor's founded depth.
    fn splits(&self, nodes: &impl Standing, address: &[Letter]) -> Splits {
        let letters = self.flatten(address);
        let branches = self.branches.len();
        let cells = self.cells();
        let mut limit = vec![vec![0usize; 2 * cells]; branches];
        for (branch, limit) in limit.iter_mut().enumerate() {
            limit[1] = self.branches[branch].depth + 1;
        }
        let mut numerators = Vec::new();
        for level in 0..self.widths.digits {
            for prefix in 0..(1usize << level) {
                if !self.odometer.holds(level, prefix) {
                    continue;
                }
                let h = (1usize << level) | prefix;
                if self.odometer.splits(level, prefix) {
                    let limits: Vec<usize> = (0..branches).map(|b| limit[b][h]).collect();
                    let digit = self.digit(nodes, h, 0, &letters, &limits);
                    for (branch, read) in digit.reads.iter().enumerate() {
                        limit[branch][2 * h] = read.nodes.len();
                        limit[branch][2 * h + 1] = read.nodes.len();
                    }
                    numerators.push(digit.face);
                } else {
                    for limit in limit.iter_mut() {
                        limit[2 * h] = limit[h];
                    }
                }
            }
        }
        Splits {
            face_bits: self.widths.face,
            numerators,
        }
    }

    /// **All classes' executed faces at an address** (module header, "Faces").
    fn face(
        &self,
        nodes: &impl Standing,
        address: &[Letter],
        grain: u64,
    ) -> Result<LandmarkFace, HnnError> {
        LandmarkFace::of_splits(&self.declaration, &self.splits(nodes, address), grain)
    }

    /// **One carried β step** on `2^(−C)`: the step `β' = β u/(v x) 2^s`, its rebase units
    /// `⌈2^C/m'⌉` and `⌈2^C/D̂⌉` (a mantissa kept, a carrier released), and whether it rebased.
    fn beta_step(&self, beta: Beta, u: u128, v: u128, x: u128, shift: i64) -> (Carried, u128) {
        let Widths {
            carrier,
            certificate,
            rebase,
            ..
        } = self.widths;
        let (n, d, e) = beta.parts();
        let carried = Beta::step(
            u128::from(n) * u,
            u128::from(d) * v * x,
            e + shift,
            carrier,
            rebase,
        );
        let units = carried
            .mantissa
            .map_or(0, |m| ceil_div(1u128 << certificate, m))
            .saturating_add(
                carried
                    .released
                    .map_or(0, |kept| ceil_div(1u128 << certificate, kept)),
            );
        (carried, units)
    }

    /// Record a carried step's rebases on the standing and its chart.
    fn record(nodes: &mut impl Standing, carried: &Carried) -> u32 {
        if carried.mantissa.is_some() {
            nodes.rebased();
        }
        if carried.released.is_some() {
            nodes.released();
        }
        u32::from(carried.mantissa.is_some())
    }

    /// **Deposit one branch's read** on a standing: each mixing node's β steps by `k(b)/q̂_(d+1)(b)`
    /// bottom-up and its certificates grow, the path's missing nodes are founded with `β = 1`, then
    /// each node's mass of the digit grows. Returns the root's excess increment.
    fn apply_branch(&self, nodes: &mut impl Standing, letters: &[u32], read: LatticeRead) -> u128 {
        let face = self.widths.face;
        let Branch { depth, forced } = self.branches[read.branch];
        // Bottom-up over the founded nodes: θ and the rebases add to the excess, the child's
        // excess increment and the rebases to the drift.
        let mut carried = 0u128;
        for d in (forced..read.nodes.len()).rev() {
            let theta = self.rounding(nodes, &read, d);
            let node = read.nodes[d];
            let mut rebase = 0u128;
            if d < depth {
                let (u, v) = nodes.kt(node, read.symbol);
                let below = self.side(read.faces[d + 1], read.symbol);
                let beta = nodes.chart(node).beta;
                let (step, units) = self.beta_step(
                    beta,
                    u128::from(u),
                    u128::from(v),
                    u128::from(below),
                    face as i64,
                );
                rebase = units;
                let rebased = Self::record(nodes, &step);
                let chart = nodes.chart_mut(node);
                chart.beta = step.beta;
                chart.stop = step.beta.stop_weight(face, self.widths.carrier);
                chart.rebases += rebased;
                chart.drift = chart.drift.saturating_add(carried).saturating_add(rebase);
            }
            let increment = theta
                .saturating_add(rebase.saturating_mul(2))
                .saturating_add(carried);
            let chart = nodes.chart_mut(node);
            chart.excess = chart.excess.saturating_add(increment);
            carried = increment;
        }
        let LatticeRead {
            tree,
            branch,
            symbol,
            nodes: mut path,
            ..
        } = read;
        let fresh = self.fresh();
        if path.is_empty() {
            path.push(nodes.found(tree, branch, None, 0, fresh));
        }
        while path.len() < letters.len() + 1 {
            let parent = *path.last().expect("a root");
            let letter = letters[path.len() - 1];
            path.push(nodes.found(tree, branch, Some((parent, letter)), path.len(), fresh));
        }
        for &node in path.iter().skip(forced) {
            nodes.halves_mut(node)[symbol] += 2;
        }
        carried
    }

    /// **Deposit one cell's reads** on a standing (module header): each branch's opened path, then
    /// each join's β by `q̂_cells(b)/q̂_bundles(b)` with its certificates. Refused before anything
    /// moves once the standing has passed `admitted` cells, or past 31-bit node numbers.
    fn apply(
        &self,
        nodes: &mut impl Standing,
        address: &[Letter],
        digits: Vec<DigitRead>,
        admitted: u64,
    ) -> Result<(), HnnError> {
        if nodes.passed() >= admitted {
            return Err(HnnError::PopulationReached {
                population: self.declaration.population,
            });
        }
        let letters = self.flatten(address);
        let founding: usize = letters.iter().map(|l| l.len() + 1).sum();
        nodes.founded_within(digits.len() * founding)?;
        let face = self.widths.face;
        for digit in digits {
            let theta = if self.joined() {
                self.join_rounding(&digit)
            } else {
                0
            };
            let DigitRead {
                dyadic,
                symbol,
                reads,
                ..
            } = digit;
            let sides: Vec<u64> = reads
                .iter()
                .map(|read| self.side(read.faces[0], symbol))
                .collect();
            let mut increments = 0u128;
            for read in reads {
                let branch = read.branch;
                increments =
                    increments.saturating_add(self.apply_branch(nodes, &letters[branch], read));
            }
            if self.joined() {
                let beta = nodes.join(dyadic).beta;
                let (step, units) =
                    self.beta_step(beta, u128::from(sides[0]), 1, u128::from(sides[1]), 0);
                let rebased = Self::record(nodes, &step);
                let chart = nodes.join_mut(dyadic);
                chart.beta = step.beta;
                chart.stop = step.beta.stop_weight(face, self.widths.carrier);
                chart.rebases += rebased;
                chart.drift = chart.drift.saturating_add(increments).saturating_add(units);
                chart.excess = chart
                    .excess
                    .saturating_add(theta)
                    .saturating_add(units.saturating_mul(2))
                    .saturating_add(increments);
            }
        }
        nodes.pass();
        Ok(())
    }
}

impl Landmarks {
    /// **Declare a tree**, empty: every node unfounded, so every face is uniform. Refused at an
    /// alphabet below two classes or past 31 bits, a zero population or grain, a population or
    /// grain past 32 bits, a forced depth past the address depth, or derived widths whose
    /// products exceed `u128` (module header, "The carrier rebases past `u128`").
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
            || !widths.admitted(declaration.population)
        {
            return Err(shape(
                "derived widths whose operands fit u128",
                u128::BITS as usize,
                usize::try_from(operands).unwrap_or(usize::MAX),
            ));
        }
        let law = Law::new(declaration, widths);
        let trees = law.branches.len() * law.cells();
        let joins = if law.joined() {
            vec![law.fresh(); law.cells()]
        } else {
            Vec::new()
        };
        Ok(Self {
            nodes: Nodes {
                arena: Arena::new(trees),
                charts: Vec::new(),
                joins,
                rebases: 0,
                releases: 0,
                passed: 0,
            },
            law,
        })
    }

    /// The declaration.
    pub fn declaration(&self) -> &LandmarkDeclaration {
        &self.law.declaration
    }

    /// The derived widths.
    pub fn widths(&self) -> Widths {
        self.law.widths
    }

    /// `B = ⌈log₂|A|⌉`, the odometer digits of a cell.
    pub fn digits(&self) -> u64 {
        self.law.widths.digits
    }

    /// `M_p`, the path lattice's width.
    pub fn face_bits(&self) -> u64 {
        self.law.widths.face
    }

    /// The splitting dyadic cells, heap-ordered: the order of [`Splits::numerators`].
    pub fn splitting(&self) -> Vec<usize> {
        self.law.odometer.splitting()
    }

    /// The founded nodes.
    pub fn nodes(&self) -> usize {
        self.nodes.len()
    }

    /// The cells passed (deposited).
    pub fn passed(&self) -> u64 {
        self.nodes.passed
    }

    /// **The tree's exact stored bits**: every half-unit mass `2C` (odd) as the ratio `(2C)/2`,
    /// `bits(2C) + 2`, at the nodes of depth at least their branch's `forced`; at each mixing node
    /// (depth below its branch's) and each join, β's odd numerator and odd denominator,
    /// `max(1, bits) + 1` each, and its exponent, `max(1, bits|e|) + 2` with its sign; each founded
    /// child's letter, `max(1, bits(letter)) + 1`; and one bit a splitting dyadic cell and branch
    /// for its root's presence. The totals (the masses' sum), the cached stop weight (read from β)
    /// and the certificates are readings kept beside them and are not counted.
    pub fn bits(&self) -> u64 {
        let slot = |value: u64| u64::from((u64::BITS - value.leading_zeros()).max(1)) + 1;
        let beta_bits = |beta: &Beta| {
            slot(beta.numerator) + slot(beta.denominator) + slot(beta.exponent.unsigned_abs()) + 1
        };
        let arena = &self.nodes.arena;
        let nodes: u64 = (0..arena.len())
            .map(|node| {
                let word = arena.depths[node];
                let branch = &self.law.branches[usize::from(word & BRANCH_BIT != 0)];
                let at = (word & !BRANCH_BIT) as usize;
                if at < branch.forced {
                    return 0;
                }
                let masses: u64 = arena.halves[node]
                    .iter()
                    .map(|&units| u64::from(u32::BITS - units.leading_zeros()) + 2)
                    .sum();
                let beta = if at < branch.depth {
                    beta_bits(&self.nodes.charts[node].beta)
                } else {
                    0
                };
                masses + beta
            })
            .sum();
        let letters: u64 = arena
            .children
            .keys()
            .map(|key| slot(key & u64::from(u32::MAX)))
            .sum();
        let splitting = self.law.odometer.splitting();
        let joins: u64 = if self.law.joined() {
            splitting
                .iter()
                .map(|&h| beta_bits(&self.nodes.joins[h].beta))
                .sum()
        } else {
            0
        };
        nodes + letters + joins + (splitting.len() * self.law.branches.len()) as u64
    }

    /// **The β chart's report** (module header).
    pub fn chart(&self) -> ChartReport {
        let charts = self.nodes.charts.iter().chain(&self.nodes.joins);
        let (mut drift, mut node_rebases) = (0u128, 0u64);
        for chart in charts {
            drift = drift.max(chart.drift);
            node_rebases = node_rebases.max(u64::from(chart.rebases));
        }
        ChartReport {
            carrier: self.law.widths.carrier,
            rebases: self.nodes.rebases,
            node_rebases,
            released: self.nodes.releases,
            drift: self.law.certified_bits(drift),
        }
    }

    /// **The rule's a-priori bound per cell**, in bits (module header, "The widths"):
    /// `(1 + 2^(−min(M_p, W))) (3/2) B [(n* P² + 2P + 1) ε/μ̂ + n* P² (2^(1−W) + ρ_c)]` with
    /// `ε/μ̂ = 1/(2⌊2^(M_p)/K⌋)`, `K = 2n* + 2`, and `ρ_c = 2^(1−R)` when the carrier rebases (else
    /// `0`); below one grain at the derived widths, below half a grain without the carrier's rebase.
    pub fn face_rule(&self) -> Rat {
        let Widths {
            digits,
            face,
            carrier,
            rebase,
            ..
        } = self.law.widths;
        let declaration = &self.law.declaration;
        let (n, d) = (
            BigInt::from(declaration.population),
            BigInt::from(declaration.path_depth()),
        );
        let paths = &n * &d * &d;
        let floor = (BigInt::one() << face as usize)
            / BigInt::from(floor_reciprocal(declaration.population));
        let rounding = Rat::new(&paths + &d * 2 + 1, floor * 2);
        let mut rebase_term = two_power(1 - carrier as i64);
        if rebase > 0 {
            rebase_term += two_power(1 - rebase as i64);
        }
        let rebases = Rat::from_integer(paths) * rebase_term;
        let grid = Rat::one() + two_power(-(face.min(carrier) as i64));
        grid * log2_e_bound() * Rat::from_integer(BigInt::from(digits)) * (rounding + rebases)
    }

    /// **The executed face of one class** at an address, exact.
    pub fn probability(&self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        Ok(self.score(address, class)?.executed)
    }

    /// **Score one class** at an address at the current standing: its executed face and its
    /// certified residual, with nothing deposited.
    pub fn score(&self, address: &[Letter], class: usize) -> Result<CellReading, HnnError> {
        check(&self.law.declaration, address, class)?;
        let reads = self.law.reads(&self.nodes, address, class);
        Ok(self.law.reading(&self.nodes, &reads))
    }

    /// **The opened paths of one class** at an address, with their executed lattice faces: per
    /// opened digit, each branch's path.
    pub fn opened(&self, address: &[Letter], class: usize) -> Result<Vec<OpenedPath>, HnnError> {
        check(&self.law.declaration, address, class)?;
        let law = &self.law;
        let scale = BigInt::one() << law.widths.face as usize;
        Ok(law
            .reads(&self.nodes, address, class)
            .into_iter()
            .flat_map(|digit| {
                let dyadic = digit.dyadic;
                digit.reads.into_iter().map(move |read| (dyadic, read))
            })
            .map(|(dyadic, read)| OpenedPath {
                dyadic,
                branch: read.branch,
                symbol: read.symbol,
                founded: read.nodes.len(),
                faces: read
                    .faces
                    .iter()
                    .map(|&zero| Rat::new(BigInt::from(law.side(zero, read.symbol)), scale.clone()))
                    .collect(),
                masses: read
                    .nodes
                    .iter()
                    .map(|&node| {
                        let (u, v) = self.nodes.kt(node, read.symbol);
                        Rat::new(BigInt::from(u), BigInt::from(v))
                    })
                    .collect(),
                betas: read
                    .nodes
                    .iter()
                    .map(|&node| self.nodes.charts[node as usize].beta.value())
                    .collect(),
            })
            .collect())
    }

    /// **The splits at an address** (module header, "Faces"): each splitting dyadic cell's
    /// executed digit-0 numerator, heap-ordered.
    pub fn splits(&self, address: &[Letter]) -> Result<Splits, HnnError> {
        check(&self.law.declaration, address, 0)?;
        Ok(self.law.splits(&self.nodes, address))
    }

    /// **All classes' executed faces at an address**, with their grain exponents at `grain`
    /// (module header, "Faces").
    pub fn face(&self, address: &[Letter], grain: u64) -> Result<LandmarkFace, HnnError> {
        check(&self.law.declaration, address, 0)?;
        self.law.face(&self.nodes, address, grain)
    }

    /// [definition; agent-inferred] **A window's faces in cell order** (module header, "A window
    /// in cell order"; Decision 29 within a window): phase `j`'s all-class face at `addresses[j]`,
    /// read at the standing after the deposits of the phases before it whose classes are known
    /// (`known[i]` at `addresses[i]`, `i < j`), each on a working overlay of the nodes those
    /// deposits wrote; the tree itself is unchanged. With nothing known every phase reads the
    /// current standing. The overlays are built in cell order, then the phases read together
    /// (`hnn::realization`: each reads its own overlay, and nothing is written). Refused at an
    /// address or class outside the declaration.
    pub fn window_faces(
        &self,
        addresses: &[Vec<Letter>],
        known: &[usize],
        grain: u64,
    ) -> Result<Vec<LandmarkFace>, HnnError> {
        let splits = self.window_splits(addresses, known)?;
        faces_of_splits(&self.law.declaration, &splits, grain)
    }

    /// **A window's splits in cell order**: [`Landmarks::window_faces`]'s reads, each phase's
    /// splits alone (the quantity the card's read returns).
    pub fn window_splits(
        &self,
        addresses: &[Vec<Letter>],
        known: &[usize],
    ) -> Result<Vec<Splits>, HnnError> {
        let law = &self.law;
        for address in addresses {
            check(&law.declaration, address, 0)?;
        }
        let deposits = known.len().min(addresses.len().saturating_sub(1));
        for (address, &class) in addresses.iter().zip(known).take(deposits) {
            check(&law.declaration, address, class)?;
        }
        let admitted = self.working_admission(deposits as u64);
        let mut working = Working::on(&self.nodes);
        let mut standings = Vec::with_capacity(deposits);
        for (address, &class) in addresses.iter().zip(known).take(deposits) {
            let reads = law.reads(&working, address, class);
            law.apply(&mut working, address, reads, admitted)?;
            standings.push(working.clone());
        }
        indexed(addresses.len(), |j| {
            Ok::<_, HnnError>(match j.min(deposits).checked_sub(1) {
                Some(index) => law.splits(&standings[index], &addresses[j]),
                None => law.splits(&self.nodes, &addresses[j]),
            })
        })
    }

    /// [agent-inferred] **The arrivals a working overlay admits**: the declared population, and
    /// past it the window's own earlier cells (a deposit's re-read at its successor reads the
    /// window's cells again) while the widths' operands at that count still fit `u128`. A working
    /// read's faces are exact executed faces, normalized for any stop weight; its certificates are
    /// not read.
    fn working_admission(&self, deposits: u64) -> u64 {
        let population = self.law.declaration.population;
        let reach = population + deposits;
        if reach < u64::from(u32::MAX / 2) && self.law.widths.admitted(reach) {
            reach
        } else {
            population
        }
    }

    /// **Deposit one cell** on the paths it opens, read at the current standing (module header):
    /// each mixing node's β steps by `k(b)/q̂_(d+1)(b)` bottom-up and its certificates grow, the
    /// path's missing nodes are founded with `β = 1`, then each node's mass of the digit grows, and
    /// each join's β steps. Refused before anything moves at a bad address or class, or past the
    /// declared population.
    pub fn deposit(&mut self, address: &[Letter], class: usize) -> Result<(), HnnError> {
        check(&self.law.declaration, address, class)?;
        let reads = self.law.reads(&self.nodes, address, class);
        let population = self.law.declaration.population;
        self.law.apply(&mut self.nodes, address, reads, population)
    }

    /// **Receive one cell**: score it at the current standing, then deposit it.
    pub fn receive(&mut self, address: &[Letter], class: usize) -> Result<CellReading, HnnError> {
        check(&self.law.declaration, address, class)?;
        let reads = self.law.reads(&self.nodes, address, class);
        let reading = self.law.reading(&self.nodes, &reads);
        let population = self.law.declaration.population;
        self.law
            .apply(&mut self.nodes, address, reads, population)?;
        Ok(reading)
    }

    /// **The arena as flat words** (module header, "The arena"; the layout the card ports): the
    /// roots per tree (`u32::MAX` unfounded), the children as `(key, child)` pairs, each node's
    /// depth word and masses, each node's chart `(β_n, β_d, β_e, λ̂)`, and each join's.
    pub fn arena(&self) -> ArenaView<'_> {
        ArenaView { tree: self }
    }
}

/// [definition] **A read-only view of the executed arena** ([`Landmarks::arena`]), for a device
/// realization that mirrors the tree.
#[derive(Clone, Copy, Debug)]
pub struct ArenaView<'a> {
    tree: &'a Landmarks,
}

/// One node's or join's chart as words: `β`'s odd numerator, odd denominator and exponent, and the
/// stop weight's numerator.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChartWords {
    pub numerator: u64,
    pub denominator: u64,
    pub exponent: i64,
    pub stop: u64,
}

impl ArenaView<'_> {
    /// The trees, `branches · 2^B`.
    pub fn trees(&self) -> usize {
        self.tree.nodes.arena.roots.len()
    }

    /// The branches' depths in letters.
    pub fn branch_depths(&self) -> Vec<usize> {
        self.tree.law.branches.iter().map(|b| b.depth).collect()
    }

    /// The cell branch's forced depths.
    pub fn forced(&self) -> usize {
        self.tree.law.branches[0].forced
    }

    /// Each tree's root, `u32::MAX` unfounded.
    pub fn roots(&self) -> Vec<u32> {
        self.tree
            .nodes
            .arena
            .roots
            .iter()
            .map(|root| root.unwrap_or(u32::MAX))
            .collect()
    }

    /// The child table as `(parent << 32 | letter, child)` pairs, in no order.
    pub fn children(&self) -> Vec<(u64, u32)> {
        self.tree
            .nodes
            .arena
            .children
            .iter()
            .map(|(&key, &child)| (key, child))
            .collect()
    }

    /// Each node's two half-unit masses.
    pub fn halves(&self) -> &[[u32; 2]] {
        &self.tree.nodes.arena.halves
    }

    /// Each node's chart.
    pub fn charts(&self) -> Vec<ChartWords> {
        self.tree.nodes.charts.iter().map(chart_words).collect()
    }

    /// Each dyadic cell's join chart (empty unless enlarged).
    pub fn joins(&self) -> Vec<ChartWords> {
        self.tree.nodes.joins.iter().map(chart_words).collect()
    }

    /// Each branch's letters of an address (the cells, then the flattened bundles).
    pub fn letters(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.tree.law.flatten(address)
    }
}

fn chart_words(chart: &Chart) -> ChartWords {
    let (numerator, denominator, exponent) = chart.beta.parts();
    ChartWords {
        numerator,
        denominator,
        exponent,
        stop: chart.stop,
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
/// `q_d = (β k_d + q_(d+1))/(1 + β)`, the deposit `β' = β k/q_(d+1)` on the exact faces, and in an
/// enlarged tree each join `q_h = (β_h q_cells + q_bundles)/(1 + β_h)`, `β'_h = β_h q_cells/q_bundles`.
/// With no width `β` is exact (the tests); at a width it is rebased past it with the residual
/// `1/m'`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdealLandmarks {
    declaration: LandmarkDeclaration,
    odometer: Odometer,
    branches: Vec<Branch>,
    arena: Arena,
    beta: Vec<Rat>,
    joins: Vec<Rat>,
    width: Option<u64>,
    rebases: u64,
}

struct IdealRead {
    branch: usize,
    nodes: Vec<u32>,
    faces: Vec<Rat>,
}

struct IdealDigit {
    dyadic: usize,
    symbol: usize,
    reads: Vec<IdealRead>,
    face: Rat,
}

impl IdealLandmarks {
    /// **Declare the oracle**, empty, with `β` exact (`width = None`) or carried at a width.
    pub fn new(declaration: LandmarkDeclaration, width: Option<u64>) -> Result<Self, HnnError> {
        check_declaration(&declaration)?;
        let digits = odometer_digits(declaration.alphabet);
        let branches: Vec<Branch> = declaration
            .branch_depths()
            .into_iter()
            .enumerate()
            .map(|(branch, depth)| Branch {
                depth,
                forced: if branch == 0 { declaration.forced } else { 0 },
            })
            .collect();
        let cells = 1usize << digits;
        let joins = if branches.len() > 1 {
            vec![Rat::one(); cells]
        } else {
            Vec::new()
        };
        Ok(Self {
            odometer: Odometer {
                alphabet: declaration.alphabet,
                digits,
            },
            arena: Arena::new(branches.len() * cells),
            branches,
            declaration,
            beta: Vec::new(),
            joins,
            width,
            rebases: 0,
        })
    }

    /// [definition; agent-inferred] **The reference width** `W_o = O + ⌈log₂(3 B n*² P²)⌉`: the
    /// oracle's rebases move a cell's code length by at most `(3/2) B n* P² 2^(1−W_o)` bits
    /// (the executed chart's drift rule with no rounding), so by at most `2^(−O)` over the passage.
    pub fn reference_width(declaration: &LandmarkDeclaration) -> u64 {
        let (n, d) = (
            BigUint::from(declaration.population),
            BigUint::from(declaration.path_depth()),
        );
        let digits = BigUint::from(odometer_digits(declaration.alphabet));
        u64::from(LOG_OCTAVES) + ceil_log2(&(BigUint::from(3u32) * digits * &n * &n * &d * &d))
    }

    /// The oracle's own rule per cell, in bits: `(3/2) B n* P² 2^(1−W_o)` (zero with `β` exact).
    pub fn drift_rule(&self) -> Rat {
        let Some(width) = self.width else {
            return Rat::zero();
        };
        let (n, d) = (
            BigInt::from(self.declaration.population),
            BigInt::from(self.declaration.path_depth()),
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

    fn flatten(&self, address: &[Letter]) -> Vec<Vec<u32>> {
        self.declaration.letters(address)
    }

    fn read(&self, branch: usize, dyadic: usize, symbol: usize, letters: &[u32]) -> IdealRead {
        let Branch { depth, forced } = self.branches[branch];
        let tree = branch * (1usize << self.odometer.digits) + dyadic;
        let nodes = self.arena.open(tree, letters, depth + 1);
        let top = nodes.len().min(depth);
        let mut faces = vec![Rat::new(BigInt::one(), BigInt::from(2)); top + 1];
        if nodes.len() == depth + 1 {
            faces[depth] = self.kt(nodes[depth], symbol);
        }
        for d in (0..top).rev() {
            faces[d] = if d < forced {
                faces[d + 1].clone()
            } else {
                let beta = &self.beta[nodes[d] as usize];
                (beta * self.kt(nodes[d], symbol) + &faces[d + 1]) / (Rat::one() + beta)
            };
        }
        IdealRead {
            branch,
            nodes,
            faces,
        }
    }

    fn reads(&self, address: &[Letter], class: usize) -> Vec<IdealDigit> {
        let letters = self.flatten(address);
        self.odometer
            .emitted(class)
            .into_iter()
            .map(|(dyadic, symbol)| {
                let reads: Vec<IdealRead> = (0..self.branches.len())
                    .map(|branch| self.read(branch, dyadic, symbol, &letters[branch]))
                    .collect();
                let face = if reads.len() > 1 {
                    let beta = &self.joins[dyadic];
                    (beta * &reads[0].faces[0] + &reads[1].faces[0]) / (Rat::one() + beta)
                } else {
                    reads[0].faces[0].clone()
                };
                IdealDigit {
                    dyadic,
                    symbol,
                    reads,
                    face,
                }
            })
            .collect()
    }

    /// **The ideal face of one class** at an address, exact.
    pub fn probability(&self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        check(&self.declaration, address, class)?;
        Ok(self
            .reads(address, class)
            .iter()
            .map(|digit| digit.face.clone())
            .product())
    }

    /// **The opened paths of one class** at an address, with their ideal faces.
    pub fn opened(&self, address: &[Letter], class: usize) -> Result<Vec<OpenedPath>, HnnError> {
        check(&self.declaration, address, class)?;
        let mut paths = Vec::new();
        for digit in self.reads(address, class) {
            for read in digit.reads {
                paths.push(OpenedPath {
                    dyadic: digit.dyadic,
                    branch: read.branch,
                    symbol: digit.symbol,
                    founded: read.nodes.len(),
                    masses: read
                        .nodes
                        .iter()
                        .map(|&node| self.kt(node, digit.symbol))
                        .collect(),
                    betas: read
                        .nodes
                        .iter()
                        .map(|&node| self.beta[node as usize].clone())
                        .collect(),
                    faces: read.faces,
                });
            }
        }
        Ok(paths)
    }

    /// **Receive one cell**: its ideal face at the current standing, then its deposit.
    pub fn receive(&mut self, address: &[Letter], class: usize) -> Result<Rat, HnnError> {
        check(&self.declaration, address, class)?;
        let digits = self.reads(address, class);
        let letters = self.flatten(address);
        let founding: usize = letters.iter().map(|l| l.len() + 1).sum();
        self.arena.founded_within(digits.len() * founding)?;
        let face = digits.iter().map(|digit| digit.face.clone()).product();
        let cells = 1usize << self.odometer.digits;
        for digit in digits {
            if digit.reads.len() > 1 {
                let stepped =
                    &self.joins[digit.dyadic] * &digit.reads[0].faces[0] / &digit.reads[1].faces[0];
                let (beta, rebased) = carried_ratio(&stepped, self.width);
                self.joins[digit.dyadic] = beta;
                self.rebases += u64::from(rebased);
            }
            for read in digit.reads {
                let Branch { depth, forced } = self.branches[read.branch];
                for d in (forced..read.nodes.len().min(depth)).rev() {
                    let node = read.nodes[d] as usize;
                    let stepped = &self.beta[node] * self.kt(read.nodes[d], digit.symbol)
                        / &read.faces[d + 1];
                    let (beta, rebased) = carried_ratio(&stepped, self.width);
                    self.beta[node] = beta;
                    self.rebases += u64::from(rebased);
                }
                let IdealRead {
                    branch, mut nodes, ..
                } = read;
                let tree = branch * cells + digit.dyadic;
                let founded = self
                    .arena
                    .extend(tree, branch, &letters[branch], &mut nodes);
                self.beta.extend(std::iter::repeat_n(Rat::one(), founded));
                self.arena.count(&nodes, forced, digit.symbol);
            }
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

/// Refused unless there is one letter per cell.
fn aligned(cells: &[usize], letters: &[Letter]) -> Result<(), HnnError> {
    if cells.len() != letters.len() {
        return Err(shape(
            "one tick's letter per cell",
            cells.len(),
            letters.len(),
        ));
    }
    Ok(())
}

/// A tree's prequential sums over one stream, `[development, held-out]`, and the run.
fn run_tree(
    cells: &[usize],
    letters: &[Letter],
    held_out: &(dyn Fn(usize) -> bool + Sync),
    declaration: &LandmarkDeclaration,
) -> Result<([ExactInterval; 2], TreeRun), HnnError> {
    aligned(cells, letters)?;
    let mut tree = Landmarks::new(declaration.clone())?;
    let mut sums = [zero(), zero()];
    let mut largest_residual = Rat::zero();
    for (position, &class) in cells.iter().enumerate() {
        let reading = tree.receive(&letter_address(letters, position, declaration.depth), class)?;
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

/// **The prequential measurement on a cut** (module header): the tree over the ticks' letters and
/// the online baselines over the same cells in the same order, each cell scored at the current
/// standing and then deposited, with enclosures on the development and held-out populations.
pub fn prequential(
    cut: &Cut,
    letters: &[Letter],
    declaration: &LandmarkDeclaration,
) -> Result<Prequential, HnnError> {
    let held_out = |position: usize| cut.held_out(position);
    let (tree, baselines) = rayon::join(
        || run_tree(&cut.cells, letters, &held_out, declaration),
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

/// **The development letters**: the ticks' letters at the development positions.
pub fn development_letters(cut: &Cut, letters: &[Letter]) -> Vec<Letter> {
    letters
        .iter()
        .enumerate()
        .filter(|(position, _)| !cut.held_out(*position))
        .map(|(_, &letter)| letter)
        .collect()
}

/// **The development code length of one declaration** (the harness's unit): the tree's
/// prequential code length over the development cells and their letters, and its run.
pub fn development_run(
    cut: &Cut,
    letters: &[Letter],
    declaration: &LandmarkDeclaration,
) -> Result<(ExactInterval, TreeRun), HnnError> {
    aligned(&cut.cells, letters)?;
    let cells = development(cut);
    let letters = development_letters(cut, letters);
    let never = |_: usize| false;
    let ([bits, _], run) = run_tree(&cells, &letters, &never, declaration)?;
    Ok((bits, run))
}

/// **Choose the address depth on the development cells** (module header): `D = max(1, forced), …`
/// while the development prequential code length decreases strictly; the declaration's own depth
/// is ignored, and each depth derives its own widths.
pub fn choose_depth(
    cut: &Cut,
    letters: &[Letter],
    declaration: &LandmarkDeclaration,
) -> Result<DepthSweep, HnnError> {
    aligned(&cut.cells, letters)?;
    let cells = development(cut);
    let letters = development_letters(cut, letters);
    let never = |_: usize| false;
    let mut tried: Vec<(usize, ExactInterval)> = Vec::new();
    let mut depth = declaration.forced.max(1);
    loop {
        let declared = LandmarkDeclaration {
            depth,
            ..declaration.clone()
        };
        let ([bits, _], _) = run_tree(&cells, &letters, &never, &declared)?;
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
pub fn oracle_cost(
    cut: &Cut,
    letters: &[Letter],
    declaration: &LandmarkDeclaration,
) -> Result<OracleCost, HnnError> {
    aligned(&cut.cells, letters)?;
    let reference_width = IdealLandmarks::reference_width(declaration);
    let mut tree = Landmarks::new(declaration.clone())?;
    let mut oracle = IdealLandmarks::new(declaration.clone(), Some(reference_width))?;
    let drift_rule = oracle.drift_rule();
    let (mut executed, mut ideal) = ([zero(), zero()], [zero(), zero()]);
    let (mut largest_deviation, mut largest_certificate) = (Rat::zero(), Rat::zero());
    let mut certified = true;
    for (position, &class) in cut.cells.iter().enumerate() {
        let here = letter_address(letters, position, declaration.depth);
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
