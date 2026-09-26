//! **The resident HNN on the card** (rebuild step 5; #76 with #12–#15 and #50; design:
//! [THE_REBUILD](../../../../docs/plans/THE_REBUILD.md), step 4 design (c), "Realization on the
//! card").
//!
//! [definition] One library for the laws, one backend for the card: every law here is a law of
//! `holonics::hnn`, realized on the card with exact integers, and each kernel family has a parity
//! test against its host owner or an exact host oracle of its contract (`tests.rs`,
//! `word_tests.rs`). What is built:
//!
//! - [`card`]: the [`Card`] (one context owning its image, stream and [`CardBuffer`]s, #15), its
//!   [`DeviceCensus`], and the layouts derived from it with their [`Realization`];
//! - `kernels/exact_integer.cuh`: the signed 128-bit word ring `ℤ/2^128`, read on
//!   `(−2^127, 2^127)` under the l1 certificate (#12);
//! - [`lattice`]: a constitution locus carried on its lattice (Decision 22) as its signed 64-bit
//!   coordinates, and the exact read `A x` against a resident operand, with an optional gather for
//!   a ring rotation;
//! - [`moment`]: the phase-binned source moment resident on the card, and its ingest (the
//!   selective steps' scan with carries, then the counts' histogram);
//! - [`word`] (Decision 24, Lean `HNN/LatticeWord`): the word's carried tick and its adjoint on
//!   lattice charts, the error-feedback split with the remainder carried on the card and released
//!   at the word's end, resident chaining (tick by tick, a captured graph of `k` ticks, or a whole
//!   window's word as one graph with its load and release copies); and the inverse charts'
//!   Newton–Schulz refinement with its exact certificate `‖1 − AX̂‖∞`, warm-started when a deposit
//!   moves the operator.
//!
//! # The realizations (hardware law)
//!
//! | Kernel | Block | Thread | A thread loops over | Reduction |
//! |---|---|---|---|---|
//! | `hnn_lattice_read` | one output entry `(row i, vector b)`; grid `(rows, vectors)` | one residue class `j ≡ t` of the row's columns; `threads` = the least power of two covering the row, at least a warp, within the census | `⌈columns/threads⌉` columns of its row | shared-memory tree of ring words and saturated certificates |
//! | `hnn_moment_ingest` | the whole cell sequence (one block) | one cell of each tile of `threads` cells; `threads` = the greatest power of two the census and the rings' scans admit | the tiles, in order, carrying the rings' phases | per ring a block scan per tile; the counts are atomic additions |
//! | `hnn_word_tick`, `hnn_word_adjoint_tick` | one output entry (row `i` of region `g`); grid = the flattened rows `Σ_g n_g`, every region of the stage at once | one residue class `j ≡ t` of the row (of `Q`, or of `Qᵀ`'s column); `threads` as the read's, over the widest region | `⌈n_max/threads⌉` columns | the shared tree; thread 0 adds the remainder and splits |
//! | `hnn_inverse_residual`, `hnn_inverse_refine` | one output entry `(i, j)` of pair `g`; grid `(Σ_g n_g, n_max)`, blocks with `j ≥ n_g` return at once | one residue class `k ≡ t` of the contraction; `threads` as the read's | `⌈n_max/threads⌉` terms | the shared tree; the refinement's thread 0 splits at `2^S` and moves the chart |
//! | `hnn_inverse_certificate` | one chart | one residue class `i ≡ t` of the chart's rows; `threads` = the least power of two covering the widest chart, at least a warp | its rows, and within each the row's `n` columns | a shared tree of maxima |
//!
//! Campaign 1 on the RTX 4080 SUPER (census in the GPU test's output): `E_0 M_0[c]` is `10 × 5`
//! blocks of 256 threads, one column each; `R P v` is `512 × A` blocks of 32 threads (one warp; 22
//! of them active); the ingest is one block of 1,024 threads, one tile per 1,024 cells (a mean
//! aeon on uniform bytes, 1,190 cells, is two tiles). A tick of the four rings (widths 10, 14, 22,
//! 26) is 72 blocks of one warp, one column per thread; the four rings' inverse charts are
//! `72 × 26` blocks of one warp (1,456 of them active) for the residual and for the refinement,
//! and 4 blocks of one warp for the certificate.
//!
//! # The device execution port: what runs resident
//!
//! [definition; agent-inferred] **The plan for `holonics::hnn::ExecutionPort` on the card.** The
//! device's `Resident` is a [`Card`] holding, per retained learned locus, its [`ResidentLattice`]
//! (the lattice coordinates of `E_g`, `R`, `W_c,g`, the pair port's factors `e_ρ, a_ρ, b_ρ`, the
//! element's `f_g` and slices, the channels' `c_a, b_a, F_a`), the open [`ResidentMoment`]s with
//! the rings' phase classes, the word's charts ([`ResidentCharts`]) with its carried state and
//! adjoint covector ([`ResidentCarry`]), the inverse charts with their operators and residuals
//! ([`ResidentInverses`]), the pending ratios' anchors and the staged deposits' covectors. The host
//! keeps the declaration (`Field`), the lift's unbounded words (windings), the constitution's exact
//! remainders, the first law's ledger and the handles.
//!
//! [definition; agent-inferred] **Resident with Decision 24's kernels** ([`word`]): the word's
//! ticks and their reverse (the adjoint ticks through the executed charts, stage by stage in
//! reverse order; the charts are fixed within a window, so the reverse needs no tape of states);
//! the error feedback, the remainders carried on the card and released at the word's end;
//! every inverse chart (the rings' Cayley denominators `1 − E/2`, the contact solves `m`, the
//! normal laws' `H`) refined by Newton–Schulz on the card and certified exactly, warm-started
//! from the last window's chart when a deposit moves its operator. **What the host still does per
//! window:** it forms the charts' words when the constitution changes (the ring element
//! `2X̂ − 1 = (2ξ − 2^(L_c)·1)·2^(−L_c)` read off the refined chart, the junction and contact
//! charts, each a transfer of `n²` words, and each operator a deposit moved), reads the
//! certificates (one transfer of 32 octets per chart) and decides from them whether to refine
//! again, loads each word's opening state and reads its release (one transfer each way), and
//! keeps everything that is not a fixed-width integer: the lift's windings, the faces in `ℚ(θ)`,
//! the Holon ratio and its winding, the normal law's prox step and budget, and the first law.
//!
//! | Method | Resident on the card | Stays on the host | Crosses the bus |
//! |---|---|---|---|
//! | `census` | the [`DeviceCensus`] and each entry's lowered limits; the pending capacity is the card's memory over one pending ratio's resident words, now fixed width: per word a carry of `24·Σ n_g` octets plus two status blocks, and its page-locked staging | the budget `B_Θ` | nothing |
//! | `mount` | every retained locus's coordinates ([`LatticeCoordinates::of_matrix`] at its declared lattice; off-lattice or beyond-word entries are refused at the mount, by position), the lock charts, the phase classes | the field, the lift's words, the remainders and solved charts | the coordinates once |
//! | `ingest` | **built:** [`ResidentMoment::ingest`], the steps' scan with carries in carry order, the counts `M_g`, `C_g(δ)`, the window and the phases updated in place, the stop at the joint clock's carry-out | the lift's words `λ_g += advance_g` | in: the window's cells (4 octets each); out: the receipt `(consumed, carried out, advance_g)`, `8(2 + G)` octets |
//! | `locate_keys` | per ring in carry order, the candidates × the crib's menu edges: permutations and phase classes in `ℤ/d_g`, a filter (fixed width today; not built) | the gauge-fixing convention and the published clocks' windings | in: the crib's cells; out: the fibres' sizes, orbits and failing loops |
//! | `refine` | the open `s_g(0) = P_g^(τ_g) Σ_c P_g^(−c)(E_g M_g[c] + E_g^(δ) C_g(δ)[c])`: **built:** `E_g M_g[c]` as [`Card::read`] against [`ResidentMoment::phase_operand`] (the fold over phases is a permutation and an exact sum; the pair port is a two-sided read `a_ρᵀ C b_ρ` of the resident counts, the same ring and certificate); the ticks: **built:** [`Card::tick`] over every region of a stage at once, resident between ticks, launched one by one, as a captured graph of `k` ticks ([`Card::capture_word`]) or as a window's whole word with its load and release copies ([`Card::capture_window`], [`ResidentCarry::run_window`]); the inverse charts: **built:** [`ResidentInverses::refine`] and [`ResidentInverses::certificates`]; the receiving read `f = R P_R^(τ_R) v_R(e_j)`: **built:** [`Card::read`] with the rotation as a [`Gather`], for a lattice anchor; the grain cells: at `L_R = 2^4` a dyadic logit's cell is a bit slice of its word (`n = S >> e`, `k = (S >> (e − 4)) mod 16`, the fibre the low `e − 4` bits) | the faces `p̂ ∝ 2^(n + k/L_R)` in `ℚ(θ)` (`CarriedPower`) and every enclosure (`ExactInterval`) a person reads | in: each word's opening state, `8·Σ n_g` octets; out: the word's release (state, remainders, statuses), `≈ 20·Σ n_g` octets in one transfer; the certificates, 32 octets per chart; per receiving epoch the grain cells (a carry word and a phase class per class) and the largest fibre, never the logits |
//! | `compare` | the covector's odometer chart `p̃ − q` as integer numerators `w_c − q_c W` over one denominator `W = Σ_c 2^(n_c − n_min)(L_R + k_c)`; its pullback through `R` (the transposed read), `P_R` (the inverse gather), the ticks in reverse (**built:** [`Card::adjoint_tick`], the transposes of the executed charts, `executed_adjoint_pairing`), and the encoder covector `Σ_c P^(c−τ) g ⊗ M_g[c]` against the resident counts | the Holon ratio `ℓ = log R` (its KL part `−log₂ p̂_t` in `ℚ(θ)`, its phase part and winding), the scalar `W`, the staged deposit's samples until the normal law is fixed width | in: the targets' cells; out: the ratio's readings; the covector numerators stay resident |
//! | `deposit` | the published coordinates of the loci reached (only entries whose applied step `q` is nonzero, `DepositReading::stepped`) | the successor: the normal law's prox step at the carried Gram, the budgeted carry with its remainders and released tails, the budget stop; the solved chart `H'⁻¹` becomes a lattice chart refined on the card ([`ResidentInverses::replace_operator`], `warm_start_certificate`) in place of exact ℚ | in: the stepped entries `(index, coordinate)` per locus reached; the moved operators' words |
//! | `release` | the width: the largest fibre over the receiving phases, a max-reduction of the bit slices | the decision rule, the RIDE/FOUND reading | out: the width |
//! | `close_aeon` | the collapse's releases: each released locus's buffers freed; the retained loci's coordinates unchanged (the collapse releases no remainder and moves no retained entry) | the diamond's reach and observe recursions and structural rank over ℚ, the released remainders' report, the first law | in: nothing beyond the released loci's handles |
//! | `read`, `discard` | freeing a handle's buffers | the handles' exact bits | out: the lift's words and the handles' bits |
//!
//! Its census arithmetic reads: "`ℤ/2^128` ring words under the l1 certificate, extended to a word
//! times a carrier word; lattice coordinates in signed 64-bit words; the only rounding is the
//! nearest-point split, its remainder carried (ticks) or bounded by half a unit (charts); every
//! refusal reported".
//!
//! # Port records (#76)
//!
//! Each port: history path → new owner → law → test.
//!
//! | History (`13f8c734`) | Owner | Law | Test |
//! |---|---|---|---|
//! | `crates/holonics-cuda/kernels/exact_resident_section.cu` (the `wide` carrier: `magnitude`, the word product, `REFUSED_CARRIER`) and `kernels/exact_integer.cuh` (the signed-magnitude carrier with its overflow flag) | `kernels/exact_integer.cuh` | the ring `ℤ/2^128` read on `(−2^127, 2^127)` under the l1 certificate, order-independent (#12) | `tests::lattice_read_matches_the_host_on_small_fixtures` (GPU: the certificate at `2^127 − 1` admitted and past it refused; the signed minimum squared) |
//! | `crates/holonics-cuda/build.rs` | `build.rs` | the architecture read off the device (floor said aloud); the explicit dialect; `nvcc` located, and its absence reported by a refusing card | `tests::the_card_opens_with_its_census` (GPU) |
//! | `crates/holonic-mount` handles without their context (#15; history `holonics-cuda::cuda`) | [`card::Card`], [`card::CardBuffer`] | common context ownership: a buffer borrows its card; a foreign buffer is refused | `tests::a_foreign_buffer_is_refused` (GPU) |
//! | `kernels/exact_resident_adjoint.cuh::section_receiver_return` (one block per row, threads striding the row, a shared tree) and `kernels/exact_packet_linear.cuh::section_packet_contract` (the exact contraction, realized by one thread over every row) | `kernels/hnn.cu::hnn_lattice_read`, [`lattice`] | the lattice read `y = A x` at `2^(−(L_A + L_x))`, one block per entry | `tests::lattice_read_matches_the_host_on_small_fixtures`, `tests::campaign_one_reads_and_ingest_match_the_host` (GPU) |
//! | `crates/holonics-cuda/src/launch_law.rs` (D1: "no bound is authored") | [`card::read_layout`], [`card::ingest_layout`] | the layout derived from the census, refused past it | `tests::read_layout_is_derived_from_the_census`, `tests::ingest_layout_is_derived_from_the_census` |
//! | none (new) | `kernels/hnn.cu::hnn_moment_ingest`, [`moment`] | `SourceMoment::ingest` with `Field::selective_step` | `tests::moment_ingest_matches_the_host_moment`, `tests::campaign_one_reads_and_ingest_match_the_host` (GPU) |
//! | none (new) | `kernels/hnn.cu::{hnn_word_tick, hnn_word_adjoint_tick}`, `exact_integer.cuh::hnn_nearest`, [`word`] | Lean `HNN/LatticeWord.{feedback_tick, feedback_accounting, executed_adjoint_pairing}` | `word_tests::the_tick_accounts_exactly`; GPU: `word_tick_matches_the_oracle_on_small_fixtures`, `word_tick_accounting_holds_on_the_card`, `word_ticks_match_the_oracle_at_campaign_one_shapes`, `resident_word_equals_the_oracle_word_and_is_measured` |
//! | none (new; history's float proposal is not ported, below) | `kernels/hnn.cu::{hnn_inverse_residual, hnn_inverse_refine, hnn_inverse_certificate}`, `exact_integer.cuh::hnn_bounded_product`, [`word`] | Lean `HNN/LatticeWord.{nsStep, newton_schulz_right, rounded_refinement_certificate, warm_start_certificate}` | GPU: `word_tests::newton_schulz_matches_the_oracle_on_small_fixtures`, `newton_schulz_matches_the_oracle_at_campaign_one_shapes` |
//!
//! **Not ported**, with the reason:
//! - `kernels/enclosure_cayley.cuh`: its Cayley step proposes by a double-precision LU, a float
//!   inside a law. The ring element's inverse is now the Newton–Schulz lattice chart
//!   ([`ResidentInverses`]), exact integers with an exact certificate.
//! - `kernels/exact_resident_adjoint.cuh`'s receiver return: a `tanh`/`exp` chart with enclosures,
//!   retired by the faces in `ℚ(θ)`.
//! - `exact_integer.cuh`'s multi-limb `ExactInteger<N>`, the directed shifts, dyadic scaling,
//!   square roots and 256-bit products of `exact_resident_section.cu`: no HNN kernel consumes them.
//! - #13's `IntegerAdd` enclosure radius: the device carries exact values, no radius.
//! - #14's per-region operator registry: each locus is its own [`ResidentLattice`]; no consumer
//!   needs a registry yet.
//! - #50's modular elimination: its HNN consumer, the solved chart `H'⁻¹`, stays exact on the host.
//!
//! [open] Owed in #62: the ring law's formal statement (for integers `p_j` with
//! `Σ_j |p_j| < 2^(w−1)`, the `ℤ/2^w` residue of `Σ_j p_j` read on `(−2^(w−1), 2^(w−1))` equals the
//! integer sum, in every order).

#![deny(clippy::float_arithmetic)]

pub mod card;
pub mod lattice;
pub mod moment;
pub mod word;

#[cfg(test)]
mod tests;
#[cfg(test)]
mod word_tests;

pub use card::{
    Card, CardBuffer, DeviceCensus, EntryCensus, KERNELS, Layout, Operand, Realization,
    certificate_layout, ingest_layout, read_layout,
};
pub use lattice::{Gather, LatticeCoordinates, LatticeRead, ResidentLattice, ResidentRead};
pub use moment::{MomentCounts, ResidentMoment};
pub use word::{
    CarryRelease, Certificate, ChartRelease, InversePair, Orientation, Refusal, ResidentCarry,
    ResidentCharts, ResidentInverses, WordChart, WordGraph,
};

use holonics::hnn::HnnError;
use thiserror::Error;

use crate::cuda::CudaError;

/// Every refusal of the resident HNN: a typed return, never a panic and never a rounded value.
#[derive(Debug, Error)]
pub enum DeviceError {
    #[error("the CUDA driver refused: {0}")]
    Driver(Box<CudaError>),
    #[error("the HNN kernels are not built ({reason})")]
    NoKernels { reason: &'static str },
    #[error("the driver reported {what} = {value}; a census extent is positive")]
    Census { what: &'static str, value: i32 },
    #[error("a buffer of another card was offered; a card's launches read only its own buffers")]
    ForeignBuffer,
    #[error("{entry}: the census cannot carry the launch: {clause}")]
    Launch {
        entry: &'static str,
        clause: &'static str,
    },
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("entry ({row}, {column}) is not on the lattice 2^-{exponent} Z")]
    OffLattice {
        row: usize,
        column: usize,
        exponent: u32,
    },
    #[error(
        "entry ({row}, {column})'s lattice coordinate takes {bits} bits, beyond the signed 64-bit word"
    )]
    Word {
        row: usize,
        column: usize,
        bits: u64,
    },
    #[error(
        "the read's l1 certificate reaches 2^127 at the entries (vector, row) {entries:?}; they are refused, never rounded"
    )]
    Carrier { entries: Vec<(usize, usize)> },
    #[error("a gather index lies outside its operand at the entries (vector, row) {entries:?}")]
    Malformed { entries: Vec<(usize, usize)> },
    #[error("{what}: the exponent {exponent} exceeds its ceiling {ceiling}")]
    Exponent {
        what: &'static str,
        exponent: u32,
        ceiling: u32,
    },
    #[error(
        "region {region}, entry {entry}: the opening remainder lies outside its cell [-2^({exponent}-1), 2^({exponent}-1))"
    )]
    OffCell {
        region: usize,
        entry: usize,
        exponent: u32,
    },
    #[error(
        "the word refused the entries (region, entry, refusal) {entries:?}; they are reported, never rounded"
    )]
    Refused {
        entries: Vec<(usize, usize, word::Refusal)>,
    },
    #[error("a kernel wrote the status word {status}, which names no refusal")]
    Status { status: u32 },
    #[error("a word's graph launches only on the carry and parity it was captured on")]
    Graph,
    #[error(transparent)]
    Hnn(#[from] HnnError),
}
