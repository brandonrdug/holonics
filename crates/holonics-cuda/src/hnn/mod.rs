//! **The resident HNN on the card** (rebuild step 5; #76 with #12–#15 and #50; design:
//! [THE_REBUILD](../../../../docs/plans/THE_REBUILD.md), step 4 design (c), "Realization on the
//! card").
//!
//! [definition] One library for the laws, one backend for the card: every law here is a law of
//! `holonics::hnn`, realized on the card with exact integers, and each kernel family has a parity
//! test against its host owner or an exact host oracle of its contract (`tests.rs`,
//! `word_tests.rs`), and the execution port a parity test against the host reference return by
//! return (`port_tests.rs`). What is built:
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
//!   moves the operator;
//! - [`port`] (Decision 25): **the execution port resident on the card**, [`Resident`] with its
//!   resident [`Mounted`], every `InteractionReturn` the host reference's; the exposure protocol
//!   runs over it (`holonics::hnn::reference::expose`), and [`Traffic`] reads what crossed the bus.
//!   It composes `publication` (the published constitution's loci at their declared lattices, the
//!   moved words scattered at each publication), `store` (the executed charts keyed as the host's
//!   `Charts`, refined step for step as `holonics::hnn::chart::refine` refines them, every
//!   Newton–Schulz step and certificate on the card), `execute` (one word's plan, buffers, launches
//!   and record: `kernels/hnn_word.cuh`) and `readout` (the host's exact readings of the card's
//!   record: the faces in `ℚ(θ)`, the tick balances, the release and the word's return).
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
//! | `hnn_word_forward`, `hnn_word_reverse` | the whole word: one block runs its open, every tick (or reverse step) and its receiving read, the stages ordered by barriers | one row of the stage (`row ≡ t`): a ring row, a contact row, an arrival coordinate, an incidence, a logit; `threads` = the least power of two covering the widest stage, at least a warp, within the entry's and the census's ceilings ([`word_layout`]) | `⌈rows/threads⌉` rows of each stage, and within a row its own sums | none across rows: each row's sums are certified in its own thread; the conductance's parts are one thread's loop over its channel or ring |
//! | `hnn_pair_weights` | one weight `(phase c, rank ρ)`; grid `(d_g, m)` | one residue class `x ≡ t` of the current cells; `threads` as the read's over `|A|` | the earlier cells, `C_c[x, y] a_ρ[x] b_ρ[y]` | the shared tree |
//! | `hnn_copy_words` | one copy (a chart gathered into a word's operands, or kept) | a residue class of the copy's words | `⌈words/threads⌉` words | none |
//! | `hnn_scatter_words` | a grid striding a publication's moved words | one moved word | — | none |
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
//! [definition; agent-inferred] **The port, built** ([`port`], Decisions 24–25). Every word the port
//! executes (a refine's, a compare's read again, a deposit's and a collapse's re-read, a release's)
//! runs on the card, from the charts' refinement through the receiving read, in one launch after
//! the refinement's; its return runs on the card in one launch. The host keeps what the port plan
//! assigns it and what is not a fixed-width integer, and reads it exactly from the card's record.
//! Parity is the law: `port_tests.rs` runs the exposure protocol on the host reference and on this
//! port in lockstep and asserts every return equal (faces, receipts, balances, bits, code lengths,
//! deposits, releases, boundaries, keys, refusals), on the chain control, on generic constitutions
//! with every locus live, on campaign 1's field, and on the standing real cut's first 24 windows.
//!
//! | Method | On the card | On the host, and why | Crosses the bus |
//! |---|---|---|---|
//! | `mount` | the constitution's loci at their declared lattices (the publication), an empty chart store | the field, the Holarchy's certificate, the admitted receivers' observability ranks (exact words, once) | the loci once, whole |
//! | `ingest` | [`ResidentMoment::ingest`] | the lift `λ` and the host's mirror of the moment (a pending ratio's operand, which the deposit's samples and the state's bits read), checked equal to the card's at every ingest | the cells (4 octets each) and the receipt |
//! | `locate_keys` | the moments' phases re-keyed | the key location (discrete, `keys::locate_closing`) | one word per ring |
//! | `refine` | the counts frozen at the cut ([`MomentSnapshot`]); the charts' refinement (`store`: warm, cold and target phases, every Newton–Schulz step and certificate); the word (`execute`: the open `E_g M_g[c]` and the pair port, every tick with its splits and remainders, the receiving read) | the operators `I − ½K`, `m_a` and each step's decision from its certificate (a cold start's transpose and the exact fallback formed on the host, `n²` words); the faces in `ℚ(θ)`; each tick's balance (its terms pass the 128-bit carrier) and the release, read exactly from the record | the plan and weights (≈ 5 kB), the moved operators and charts, 32 octets per certificate, the record and logits (≈ 55 kB) |
//! | `compare` | the word's return (`hnn_word_reverse`): every element's, transit's and junction's reverse step with their carried remainders | the Holon ratio and its covector; the covector's pull through `Rᵀ` and its first split (it lives on `(1/W)ℤ`, not a lattice); the conductance's division by each ring's admittance sum (not dyadic); the composition onto the loci (`reference::compose`) | the carried reads (`8·A·2d_R` octets), the return's record (≈ 25 kB) |
//! | `deposit` | the successor's loci (the predecessor copied on the card, the moved words scattered), the arrived re-read | the normal laws' prox steps, the budgeted carry, the budget, the successor's operators, the code length | the moved words (16 octets each) and a word |
//! | `release`, `close_aeon` | a word (the release's read, a collapse's re-read), the descended loci | the width and decision, the collapse, the first law, the boundary | a word, the moved words |
//! | `read`, `discard` | freeing a handle's buffers | the handles' bits | nothing |
//!
//! Its census arithmetic reads: "exact integers on the card: `ℤ/2^128` ring words under the l1
//! certificate, lattice coordinates in signed 64-bit words, the nearest-point split with its
//! remainder carried; ℚ and ℚ(θ) on the host; every refusal reported". A declaration the card's
//! dyadic words cannot carry is refused at the plan, never rounded: a hop that is not a power of
//! two, a non-dyadic admittance, an exponent past the carrier (a shielded contact whose `G/2h` lies
//! below `2^(−100)` would shift a state past `2^127`).
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
//! | none (new) | `kernels/hnn_word.cuh::{hnn_word_forward, hnn_word_reverse, hnn_pair_weights, hnn_copy_words, hnn_scatter_words}`, [`port`] | `holonics::hnn::{word::Word, port::Word::pull_back, receiving::ReceivingPhases::read, moment::SourceMoment::open_storage, chart::refine}` and the reference's `ExecutionPort` | GPU: `port_tests::the_card_port_returns_the_reference_on_{the_chain, a_generic_constitution, campaign_one, the_standing_cut}`, `the_card_port_refuses_as_the_reference` |
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
//! - #50's modular elimination: its HNN consumer, the solved chart `H'⁻¹`, is now a certified lattice chart (Decision 24), so no modular elimination is needed.
//!
//! [open] Owed in #62: the ring law's formal statement (for integers `p_j` with
//! `Σ_j |p_j| < 2^(w−1)`, the `ℤ/2^w` residue of `Σ_j p_j` read on `(−2^(w−1), 2^(w−1))` equals the
//! integer sum, in every order).

#![deny(clippy::float_arithmetic)]

pub mod card;
mod dyadic;
mod execute;
pub mod lattice;
pub mod moment;
pub mod port;
mod publication;
mod readout;
mod store;
pub mod word;

#[cfg(test)]
mod port_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod word_tests;

pub use card::{
    Card, CardBuffer, DeviceCensus, EntryCensus, KERNELS, Layout, Operand, Realization,
    certificate_layout, copy_layout, ingest_layout, read_layout, word_layout,
};
pub use lattice::{Gather, LatticeCoordinates, LatticeRead, ResidentLattice, ResidentRead};
pub use moment::{MomentCounts, MomentSnapshot, ResidentMoment};
pub use port::{Mounted, Resident, Traffic};
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
