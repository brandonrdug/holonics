//! **The word on the card: the carried tick, its adjoint, and the inverse charts** (Decision 24;
//! kernels `hnn_word_tick`, `hnn_word_adjoint_tick`, `hnn_inverse_residual`, `hnn_inverse_refine`
//! and `hnn_inverse_certificate` in `kernels/hnn.cu`).
//!
//! [definition] **The contract** (Lean `HNN/LatticeWord`, `HNN/LatticeDeposit.quot`/`rem`), shared
//! with the host owner in `holonics::hnn`. Every quantity is an integer coordinate on a declared
//! lattice, and the only rounding is the nearest-point split, ties upward, whose remainder is
//! carried or bounded:
//!
//! ```text
//! split_L(s) = (q, r) ,  s = q·2^L + r ,  −2^(L−1) ≤ r < 2^(L−1)     (L = 0: q = s, r = 0)
//!
//! chart        Q = q·2^(−L_c)   (n × n signed 64-bit words, n ≤ 64 in campaign 1)
//! state        x = ξ·2^(−L_w)   (n words);  remainder r on 2^(−(L_c+L_w))ℤ (n words)
//! tick         (ξ', r') = split_(L_c)(qξ + r)         ξ'·2^(L_c) + r' = qξ + r   (feedback_tick)
//! adjoint      (λ', ρ') = split_(L_c)(qᵀλ + ρ)        ⟨λ, qξ⟩ = ⟨qᵀλ, ξ⟩       (executed_adjoint_pairing)
//! word         k ticks; Σ_t ξ_(t+1)·2^(L_c) + r_k = Σ_t qξ_t + r_0   (feedback_accounting)
//!
//! inverse      A = a·2^(−L_A), X̂ = ξ·2^(−L_c), S = L_A + L_c ≤ 126
//! residual     ρ = 2^S·1 − aξ               (R = 1 − AX̂ on 2^(−S)ℤ)
//! refinement   ξ'' = split_S(ξ(2^(S+1)·1 − aξ)).q = ξ + split_S(ξρ).q     (nsStep, right form)
//!              the discarded remainder |e| ≤ 2^(S−1): |Δ| ≤ 2^(−L_c)/2
//! certificate  ‖1 − AX̂‖∞ = max_i Σ_j |ρ_ij| / 2^S       (exact; rounded_refinement_certificate)
//! ```
//!
//! [definition] **Refusals, never rounding**, per entry, in this order:
//! - [`Refusal::Operand`]: the entry reads a coordinate refused upstream (a tick reads its region's
//!   whole state; a residual entry `(i, j)` reads column `j` of the chart; a refinement entry reads
//!   row `i` of the chart and column `j` of the residual; a certificate reads its whole residual);
//! - [`Refusal::Carrier`]: its l1 certificate reaches `2^127` (`kernels/exact_integer.cuh`): for a
//!   tick `Σ_j |q_ij ξ_j| + |r_i|`, for a residual `2^S δ_ij + Σ_k |a_ik ξ_kj|`, for a refinement
//!   `Σ_k |ξ_ik| |ρ_kj|` (a word times a carrier word), for a certificate the row sum itself;
//! - [`Refusal::Word`]: the new state or chart coordinate lies outside the signed 64-bit word.
//!
//! A refused entry holds zero and its status; the refusal travels with the current (an operand
//! refusal at the next tick) and is reported where the word is released ([`CarryRelease`]).
//!
//! [definition] **The ceilings are derived, not authored.** A tick's remainder
//! `−2^(L_c−1) ≤ r < 2^(L_c−1)` is a signed 64-bit word exactly when `L_c ≤ 64`
//! ([`TICK_EXPONENT_CEILING`]); an inverse's `2^S` is a carrier word exactly when `S ≤ 126`
//! ([`INVERSE_EXPONENT_CEILING`]). A word opens with its remainders in their cells
//! (`feedback_rem_bounds`' hypothesis), refused by position otherwise ([`DeviceError::OffCell`]).
//!
//! [definition] **Resident chaining.** A [`ResidentCarry`] keeps the state, its statuses (two of
//! each, alternating) and the remainders on the card; [`Card::tick`] and [`Card::adjoint_tick`]
//! launch one stage over every region at once (regions are independent within a stage) and move
//! nothing across the bus; [`ResidentCarry::load`] writes a word's opening state in place and
//! [`ResidentCarry::release`] reads back the final state, the released remainders and the statuses,
//! each one stream-ordered copy through page-locked staging, with one host wait per word.
//! [`Card::capture_word`] binds `k` ticks as one graph ([`WordGraph`]); [`Card::capture_window`]
//! binds a whole window's word (the load, the ticks, the release) as one graph, run by
//! [`ResidentCarry::run_window`]: one launch and one wait per word. [`ResidentInverses`] keeps the
//! operators, the charts (alternating), the residual and the certificates on the card, refines in
//! place, and takes a deposit's moved operator in place for the warm start.

use core::ffi::c_void;

use holonics::ratio::Rat;
use num_bigint::BigInt;
use num_traits::One;

use crate::cuda::{GraphCensus, GraphExec, PinnedHost};
use crate::ffi::CUdeviceptr;
use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer, Layout, certificate_layout, read_layout};
use crate::hnn::lattice::LatticeCoordinates;

/// The entries' names in the image.
pub const TICK_ENTRY: &str = "hnn_word_tick";
pub const ADJOINT_ENTRY: &str = "hnn_word_adjoint_tick";
pub const RESIDUAL_ENTRY: &str = "hnn_inverse_residual";
pub const REFINE_ENTRY: &str = "hnn_inverse_refine";
pub const CERTIFICATE_ENTRY: &str = "hnn_inverse_certificate";

/// The largest chart exponent of a tick: the remainder `−2^(L_c−1) ≤ r < 2^(L_c−1)` is a signed
/// 64-bit word exactly when `L_c ≤ 64`.
pub const TICK_EXPONENT_CEILING: u32 = i64::BITS;

/// The largest `S = L_A + L_c` of an inverse pair: `2^S` lies in the carrier `(−2^127, 2^127)`
/// exactly when `S ≤ 126`.
pub const INVERSE_EXPONENT_CEILING: u32 = i128::BITS - 2;

// The status words (`kernels/exact_integer.cuh`).
const EXACT: u32 = 0;
const REFUSED_CARRIER: u32 = 1;
const REFUSED_WORD: u32 = 4;
const REFUSED_OPERAND: u32 = 8;

/// A kernel's argument list: a pointer to each argument, in declared order.
macro_rules! arguments {
    ($($value:ident),* $(,)?) => {
        [$(&mut $value as *mut _ as *mut c_void),*]
    };
}

// -------------------------------------------------------------------------------------------
// refusals

/// [definition] **Why an entry was refused** (see the module header). Nothing is rounded instead.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Refusal {
    /// The entry's l1 certificate reached `2^127`.
    Carrier,
    /// The new coordinate lies outside the signed 64-bit word.
    Word,
    /// The entry reads a coordinate refused upstream.
    Operand,
}

impl Refusal {
    /// The refusal a status word carries, `None` when exact.
    pub fn of_status(status: u32) -> Result<Option<Self>, DeviceError> {
        match status {
            EXACT => Ok(None),
            REFUSED_CARRIER => Ok(Some(Self::Carrier)),
            REFUSED_WORD => Ok(Some(Self::Word)),
            REFUSED_OPERAND => Ok(Some(Self::Operand)),
            other => Err(DeviceError::Status { status: other }),
        }
    }
}

// -------------------------------------------------------------------------------------------
// the region tables

/// The tables every launch over several regions reads, and their host copies.
struct Regions<'c> {
    widths: Vec<usize>,
    chart_base: Vec<usize>,
    rows: usize,
    squares: usize,
    widest: usize,
    width_words: CardBuffer<'c, u32>,
    chart_base_words: CardBuffer<'c, u64>,
    row_base_words: CardBuffer<'c, u64>,
    shift_words: CardBuffer<'c, u32>,
    row_region: CardBuffer<'c, u32>,
}

fn wire(value: usize, what: &'static str) -> Result<u32, DeviceError> {
    u32::try_from(value).map_err(|_| DeviceError::Shape {
        what,
        expected: u32::MAX as usize,
        found: value,
    })
}

impl<'c> Regions<'c> {
    fn mount(card: &'c Card, widths: &[usize], shifts: &[u32]) -> Result<Self, DeviceError> {
        if widths.is_empty() {
            return Err(DeviceError::Shape {
                what: "a word's regions (at least one)",
                expected: 1,
                found: 0,
            });
        }
        let (mut row_base, mut chart_base) = (Vec::new(), Vec::new());
        let (mut rows, mut squares) = (0usize, 0usize);
        let mut row_region = Vec::new();
        for (g, &width) in widths.iter().enumerate() {
            if width == 0 {
                return Err(DeviceError::Shape {
                    what: "a region's width (at least one)",
                    expected: 1,
                    found: 0,
                });
            }
            row_base.push(rows);
            chart_base.push(squares);
            rows += width;
            squares += width * width;
            let region = wire(g, "a region index within the 32-bit wire")?;
            row_region.extend(core::iter::repeat_n(region, width));
        }
        wire(rows, "the word's rows within the 32-bit wire")?;
        let width_words = widths
            .iter()
            .map(|width| wire(*width, "a region's width within the 32-bit wire"))
            .collect::<Result<Vec<u32>, DeviceError>>()?;
        let as_words = |bases: &[usize]| bases.iter().map(|b| *b as u64).collect::<Vec<u64>>();
        Ok(Self {
            widest: widths.iter().copied().max().unwrap_or(0),
            width_words: card.upload(&width_words)?,
            chart_base_words: card.upload(&as_words(&chart_base))?,
            row_base_words: card.upload(&as_words(&row_base))?,
            shift_words: card.upload(shifts)?,
            row_region: card.upload(&row_region)?,
            widths: widths.to_vec(),
            chart_base,
            rows,
            squares,
        })
    }

    /// The octets the tables took across the bus.
    fn octets(&self) -> usize {
        let regions = self.widths.len();
        regions * (4 + 8 + 8 + 4) + self.rows * 4
    }
}

// -------------------------------------------------------------------------------------------
// the word's charts

/// [definition] **A region's chart**: `Q = q·2^(−L_c)`, `n × n` signed 64-bit words row-major,
/// carrying a state on `2^(−L_w)ℤ`. `L_c ≤ 64` ([`TICK_EXPONENT_CEILING`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordChart {
    width: usize,
    chart_exponent: u32,
    state_exponent: u32,
    words: Vec<i64>,
}

impl WordChart {
    pub fn new(
        width: usize,
        chart_exponent: u32,
        state_exponent: u32,
        words: Vec<i64>,
    ) -> Result<Self, DeviceError> {
        if width == 0 || words.len() != width * width {
            return Err(DeviceError::Shape {
                what: "a chart's n × n words (n at least one)",
                expected: width * width,
                found: words.len(),
            });
        }
        if chart_exponent > TICK_EXPONENT_CEILING {
            return Err(DeviceError::Exponent {
                what: "a tick's chart exponent L_c (its remainder a signed 64-bit word)",
                exponent: chart_exponent,
                ceiling: TICK_EXPONENT_CEILING,
            });
        }
        Ok(Self {
            width,
            chart_exponent,
            state_exponent,
            words,
        })
    }

    /// A square lattice array as a chart: `L_c` is its lattice exponent.
    pub fn of_coordinates(
        coordinates: &LatticeCoordinates,
        state_exponent: u32,
    ) -> Result<Self, DeviceError> {
        if coordinates.rows() != coordinates.columns() {
            return Err(DeviceError::Shape {
                what: "a chart's columns against its rows",
                expected: coordinates.rows(),
                found: coordinates.columns(),
            });
        }
        Self::new(
            coordinates.rows(),
            coordinates.exponent(),
            state_exponent,
            coordinates.words().to_vec(),
        )
    }

    pub fn width(&self) -> usize {
        self.width
    }

    /// `L_c`.
    pub fn chart_exponent(&self) -> u32 {
        self.chart_exponent
    }

    /// `L_w`.
    pub fn state_exponent(&self) -> u32 {
        self.state_exponent
    }

    /// The words `q`, row-major.
    pub fn words(&self) -> &[i64] {
        &self.words
    }

    /// `q_ij`.
    pub fn word(&self, row: usize, column: usize) -> i64 {
        self.words[row * self.width + column]
    }
}

/// [definition] **The word's charts resident on a card**: every region's chart in one buffer, the
/// region tables, and the tick's layout derived from the census at the mount.
pub struct ResidentCharts<'c> {
    card: &'c Card,
    words: CardBuffer<'c, i64>,
    regions: Regions<'c>,
    exponents: Vec<(u32, u32)>,
    forward: Layout,
    adjoint: Layout,
}

impl<'c> ResidentCharts<'c> {
    /// **Mount the charts** (a transfer): the words and the region tables, and the layouts of the
    /// tick and the adjoint tick.
    pub fn mount(card: &'c Card, charts: &[WordChart]) -> Result<Self, DeviceError> {
        let widths: Vec<usize> = charts.iter().map(WordChart::width).collect();
        let shifts: Vec<u32> = charts.iter().map(WordChart::chart_exponent).collect();
        let regions = Regions::mount(card, &widths, &shifts)?;
        let words: Vec<i64> = charts
            .iter()
            .flat_map(|chart| chart.words.iter().copied())
            .collect();
        let forward = read_layout(
            card.census(),
            &card.entry(TICK_ENTRY)?,
            regions.rows,
            regions.widest,
            1,
        )?;
        let adjoint = read_layout(
            card.census(),
            &card.entry(ADJOINT_ENTRY)?,
            regions.rows,
            regions.widest,
            1,
        )?;
        Ok(Self {
            card,
            words: card.upload(&words)?,
            regions,
            exponents: charts
                .iter()
                .map(|chart| (chart.chart_exponent, chart.state_exponent))
                .collect(),
            forward,
            adjoint,
        })
    }

    /// The regions' widths.
    pub fn widths(&self) -> &[usize] {
        &self.regions.widths
    }

    /// The flattened rows, `Σ_g n_g`.
    pub fn rows(&self) -> usize {
        self.regions.rows
    }

    /// Each region's `(L_c, L_w)`.
    pub fn exponents(&self) -> &[(u32, u32)] {
        &self.exponents
    }

    /// The tick's layout (the adjoint's is [`ResidentCharts::adjoint_layout`]).
    pub fn layout(&self) -> &Layout {
        &self.forward
    }

    pub fn adjoint_layout(&self) -> &Layout {
        &self.adjoint
    }

    /// The octets the mount took across the bus: the words and the tables.
    pub fn mounted_octets(&self) -> usize {
        self.regions.squares * 8 + self.regions.octets()
    }
}

// -------------------------------------------------------------------------------------------
// the carried vector

/// [definition] **The carried vector's one allocation**, in octets:
/// `[status₀ | state₀ | remainder | state₁ | status₁]`, each status block (a 4-octet word per row)
/// padded to 8 octets. The ticks alternate between parity 0 and 1; at parity 0 the release is the
/// prefix `[status₀ | state₀ | remainder]`, at parity 1 the suffix `[remainder | state₁ | status₁]`,
/// so a release is one contiguous transfer either way.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CarryLayout {
    rows: usize,
    status: usize,
}

impl CarryLayout {
    fn new(rows: usize) -> Self {
        Self {
            rows,
            status: (4 * rows).next_multiple_of(8),
        }
    }

    fn total(&self) -> usize {
        2 * self.status + 24 * self.rows
    }

    fn state(&self, parity: usize) -> usize {
        self.status + 16 * self.rows * parity
    }

    fn status_at(&self, parity: usize) -> usize {
        (self.status + 24 * self.rows) * parity
    }

    fn remainder(&self) -> usize {
        self.status + 8 * self.rows
    }

    /// The released range `(offset, octets)` at a parity.
    fn release(&self, parity: usize) -> (usize, usize) {
        let octets = self.status + 16 * self.rows;
        (self.remainder() * parity, octets)
    }
}

fn octets_of(words: &[i64]) -> Vec<u8> {
    words.iter().flat_map(|word| word.to_ne_bytes()).collect()
}

fn words_of(octets: &[u8]) -> Vec<i64> {
    octets
        .chunks_exact(8)
        .map(|chunk| i64::from_ne_bytes(chunk.try_into().expect("eight octets")))
        .collect()
}

fn statuses_of(octets: &[u8], rows: usize) -> Vec<u32> {
    octets
        .chunks_exact(4)
        .take(rows)
        .map(|chunk| u32::from_ne_bytes(chunk.try_into().expect("four octets")))
        .collect()
}

/// [definition] **A carried vector resident on a card**: a word's state (or an adjoint's
/// covector), one word per flattened row, its statuses (two of each, alternating from tick to
/// tick) and the carried remainders, in place, in one allocation ([`CarryLayout`]).
pub struct ResidentCarry<'c> {
    card: &'c Card,
    widths: Vec<usize>,
    exponents: Vec<u32>,
    layout: CarryLayout,
    // Declared before the staging: the buffer's release synchronizes the card's stream, so no copy
    // still reads or writes the staging when it is freed.
    octets: CardBuffer<'c, u8>,
    staging: PinnedHost,
    staged: bool,
    current: usize,
    ticks: u64,
}

impl<'c> ResidentCarry<'c> {
    /// **Open a carried vector** on the charts' regions: one allocation, then
    /// [`ResidentCarry::load`].
    pub fn open(
        charts: &ResidentCharts<'c>,
        state: &[i64],
        remainder: Option<&[i64]>,
    ) -> Result<Self, DeviceError> {
        let card = charts.card;
        let layout = CarryLayout::new(charts.rows());
        let mut carry = Self {
            card,
            widths: charts.regions.widths.clone(),
            exponents: charts.exponents.iter().map(|(lc, _)| *lc).collect(),
            layout,
            octets: card.alloc(layout.total())?,
            staging: card.pinned(layout.release(0).1)?,
            staged: false,
            current: 0,
            ticks: 0,
        };
        carry.load(state, remainder)?;
        Ok(carry)
    }

    /// **Load a word's opening in place**, with no allocation and no host synchronization: the
    /// statuses exact and the remainders zero (zeroed on the card), then the state `ξ`, region by
    /// region, and the remainders when given, each in its cell `[−2^(L_c−1), 2^(L_c−1))` (refused
    /// by position otherwise), copied from page-locked staging on the card's stream. The tick
    /// count restarts.
    pub fn load(&mut self, state: &[i64], remainder: Option<&[i64]>) -> Result<(), DeviceError> {
        let rows = self.layout.rows;
        if state.len() != rows {
            return Err(DeviceError::Shape {
                what: "the opening state's rows",
                expected: rows,
                found: state.len(),
            });
        }
        if let Some(remainder) = remainder {
            if remainder.len() != rows {
                return Err(DeviceError::Shape {
                    what: "the opening remainders' rows",
                    expected: rows,
                    found: remainder.len(),
                });
            }
            let mut row = 0;
            for (region, (&width, &exponent)) in self.widths.iter().zip(&self.exponents).enumerate()
            {
                for entry in 0..width {
                    let value = i128::from(remainder[row]);
                    let inside = if exponent == 0 {
                        value == 0
                    } else {
                        let half = 1i128 << (exponent - 1);
                        -half <= value && value < half
                    };
                    if !inside {
                        return Err(DeviceError::OffCell {
                            region,
                            entry,
                            exponent,
                        });
                    }
                    row += 1;
                }
            }
        }
        // A copy of the last load may still read the staging.
        if self.staged {
            self.card.synchronize()?;
            self.staged = false;
        }
        let words = 8 * rows;
        let staging = self.staging.as_mut_octets();
        staging[..words].copy_from_slice(&octets_of(state));
        if let Some(remainder) = remainder {
            staging[words..2 * words].copy_from_slice(&octets_of(remainder));
        }
        let (_, prefix) = self.layout.release(0);
        self.card.zero_octets(&self.octets, 0, prefix)?;
        // SAFETY: the staging is written again only after a synchronization of the card's stream
        // (above, or in `release`), which passes these copies.
        unsafe {
            self.card
                .stage_in(&self.octets, self.layout.state(0), &self.staging, 0, words)?;
            if remainder.is_some() {
                self.card.stage_in(
                    &self.octets,
                    self.layout.remainder(),
                    &self.staging,
                    words,
                    words,
                )?;
            }
        }
        self.staged = true;
        self.current = 0;
        self.ticks = 0;
        Ok(())
    }

    /// The ticks run since the open or the last load.
    pub fn ticks(&self) -> u64 {
        self.ticks
    }

    fn pointer(&self, offset: usize) -> CUdeviceptr {
        self.octets.device_ptr() + offset as CUdeviceptr
    }

    /// **Release the word** (one transfer and the word's one host synchronization): the final
    /// state, the remainders it releases, and the statuses, after every tick ordered before it.
    pub fn release(&mut self) -> Result<CarryRelease, DeviceError> {
        let (offset, octets) = self.layout.release(self.current);
        // SAFETY: the staging is read only after the synchronization that passes the copy, and
        // `load` waits on a synchronization before writing it again.
        unsafe {
            self.card
                .stage_out(&self.octets, offset, &mut self.staging, 0, octets)?;
        }
        self.card.synchronize()?;
        self.staged = false;
        Ok(self.released())
    }

    /// The release the staging holds after a synchronization that passed its copy.
    fn released(&self) -> CarryRelease {
        let layout = self.layout;
        let rows = layout.rows;
        let (offset, octets) = layout.release(self.current);
        let read = &self.staging.as_octets()[..octets];
        let at = |absolute: usize| absolute - offset;
        let state = words_of(&read[at(layout.state(self.current))..][..8 * rows]);
        let remainder = words_of(&read[at(layout.remainder())..][..8 * rows]);
        let status = statuses_of(&read[at(layout.status_at(self.current))..], rows);
        let mut row_base = Vec::with_capacity(self.widths.len());
        let mut base = 0;
        for width in &self.widths {
            row_base.push(base);
            base += width;
        }
        CarryRelease {
            widths: self.widths.clone(),
            row_base,
            state,
            remainder,
            status,
            ticks: self.ticks,
        }
    }

    /// **Run a window's word bound as one graph** ([`Card::capture_window`]): the opening state
    /// into the staging, one launch (the load, every tick, the release), one host wait. The
    /// remainders open at zero (`feedback_accounting_zero`).
    pub fn run_window(
        &mut self,
        graph: &WordGraph<'_>,
        state: &[i64],
    ) -> Result<CarryRelease, DeviceError> {
        let rows = self.layout.rows;
        if !graph.window || !graph.binds(self) {
            return Err(DeviceError::Graph);
        }
        if state.len() != rows {
            return Err(DeviceError::Shape {
                what: "the opening state's rows",
                expected: rows,
                found: state.len(),
            });
        }
        if self.staged {
            self.card.synchronize()?;
            self.staged = false;
        }
        self.staging.as_mut_octets()[..8 * rows].copy_from_slice(&octets_of(state));
        self.card.launch_graph(&graph.exec)?;
        self.card.synchronize()?;
        self.current = (graph.ticks & 1) as usize;
        self.ticks = graph.ticks;
        Ok(self.released())
    }

    /// The octets a release takes across the bus: per row the state and remainder words and the
    /// status (padded to 8 octets).
    pub fn released_octets(&self) -> usize {
        self.layout.release(self.current).1
    }

    /// The octets a load takes across the bus: the state, and the remainders when given.
    pub fn loaded_octets(&self, remainder: bool) -> usize {
        8 * self.layout.rows * (1 + usize::from(remainder))
    }
}

/// [definition] **A released word** on the host: the state (or covector), the remainders and the
/// statuses, region by region.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarryRelease {
    widths: Vec<usize>,
    row_base: Vec<usize>,
    state: Vec<i64>,
    remainder: Vec<i64>,
    status: Vec<u32>,
    ticks: u64,
}

impl CarryRelease {
    /// Every row's state word `ξ`, region by region.
    pub fn state(&self) -> &[i64] {
        &self.state
    }

    /// Every row's released remainder `r`.
    pub fn remainder(&self) -> &[i64] {
        &self.remainder
    }

    /// Every row's status word.
    pub fn status(&self) -> &[u32] {
        &self.status
    }

    /// Region `g`'s state.
    pub fn region_state(&self, region: usize) -> &[i64] {
        let start = self.row_base[region];
        &self.state[start..start + self.widths[region]]
    }

    /// Region `g`'s remainders.
    pub fn region_remainder(&self, region: usize) -> &[i64] {
        let start = self.row_base[region];
        &self.remainder[start..start + self.widths[region]]
    }

    /// The ticks the word ran.
    pub fn ticks(&self) -> u64 {
        self.ticks
    }

    /// The refused entries `(region, entry, refusal)`.
    pub fn refusals(&self) -> Result<Vec<(usize, usize, Refusal)>, DeviceError> {
        let mut refused = Vec::new();
        for (region, (&start, &width)) in self.row_base.iter().zip(&self.widths).enumerate() {
            for entry in 0..width {
                if let Some(refusal) = Refusal::of_status(self.status[start + entry])? {
                    refused.push((region, entry, refusal));
                }
            }
        }
        Ok(refused)
    }

    /// The release when every entry is exact, or the refused entries.
    pub fn exact(self) -> Result<Self, DeviceError> {
        let refused = self.refusals()?;
        if refused.is_empty() {
            Ok(self)
        } else {
            Err(DeviceError::Refused { entries: refused })
        }
    }
}

/// Which chart a tick executes: `Q` (the word) or `Qᵀ` (its adjoint).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Orientation {
    Forward,
    Adjoint,
}

impl Card {
    /// **One tick of every region**, resident: `(ξ', r') = split_(L_c)(qξ + r)` (see the module
    /// header). Nothing crosses the bus.
    pub fn tick(
        &self,
        charts: &ResidentCharts<'_>,
        carry: &mut ResidentCarry<'_>,
    ) -> Result<(), DeviceError> {
        self.stage(charts, carry, Orientation::Forward)
    }

    /// **One adjoint tick of every region**, resident: `(λ', ρ') = split_(L_c)(qᵀλ + ρ)`.
    pub fn adjoint_tick(
        &self,
        charts: &ResidentCharts<'_>,
        carry: &mut ResidentCarry<'_>,
    ) -> Result<(), DeviceError> {
        self.stage(charts, carry, Orientation::Adjoint)
    }

    /// One stage in either orientation.
    pub fn stage(
        &self,
        charts: &ResidentCharts<'_>,
        carry: &mut ResidentCarry<'_>,
        orientation: Orientation,
    ) -> Result<(), DeviceError> {
        self.owns(&charts.words)?;
        self.owns(&carry.octets)?;
        if carry.widths != charts.regions.widths {
            return Err(DeviceError::Shape {
                what: "the carry's regions against the charts'",
                expected: charts.rows(),
                found: carry.widths.iter().sum(),
            });
        }
        let (entry, layout) = match orientation {
            Orientation::Forward => (TICK_ENTRY, &charts.forward),
            Orientation::Adjoint => (ADJOINT_ENTRY, &charts.adjoint),
        };
        let regions = &charts.regions;
        let (from, to) = (carry.current, 1 - carry.current);
        let mut words = charts.words.device_ptr();
        let mut widths = regions.width_words.device_ptr();
        let mut chart_base = regions.chart_base_words.device_ptr();
        let mut state_base = regions.row_base_words.device_ptr();
        let mut shifts = regions.shift_words.device_ptr();
        let mut row_region = regions.row_region.device_ptr();
        let mut entries = regions.rows as u32;
        let mut state = carry.pointer(carry.layout.state(from));
        let mut state_status = carry.pointer(carry.layout.status_at(from));
        let mut next = carry.pointer(carry.layout.state(to));
        let mut next_status = carry.pointer(carry.layout.status_at(to));
        let mut remainder = carry.pointer(carry.layout.remainder());
        let mut params = arguments![
            words,
            widths,
            chart_base,
            state_base,
            shifts,
            row_region,
            entries,
            state,
            state_status,
            next,
            next_status,
            remainder,
        ];
        self.launch(entry, layout, &mut params)?;
        carry.current = to;
        carry.ticks += 1;
        Ok(())
    }

    /// **Bind a word of `ticks` ticks as one graph** on a carry (nothing runs until
    /// [`WordGraph::launch`]). The graph borrows the charts it reads; the carry's parity and tick
    /// count are left as they were.
    pub fn capture_word<'w>(
        &'w self,
        charts: &'w ResidentCharts<'_>,
        carry: &mut ResidentCarry<'_>,
        ticks: usize,
        orientation: Orientation,
    ) -> Result<WordGraph<'w>, DeviceError> {
        let (parity, counted) = (carry.current, carry.ticks);
        self.begin_capture()?;
        let mut issued = Ok(());
        for _ in 0..ticks {
            issued = self.stage(charts, carry, orientation);
            if issued.is_err() {
                break;
            }
        }
        let captured = self.end_capture();
        carry.current = parity;
        carry.ticks = counted;
        issued?;
        let (exec, census) = captured?;
        Ok(WordGraph {
            card: self,
            charts,
            exec,
            census,
            ticks: ticks as u64,
            parity,
            carry: carry.octets.device_ptr(),
            layout: carry.layout,
            window: false,
        })
    }

    /// **Bind a whole window's word as one graph** on a carry: the statuses and remainders zeroed
    /// and the opening state copied from the carry's staging, `ticks` ticks, and the release copied
    /// back into the staging. [`ResidentCarry::run_window`] runs it: one launch and one host wait
    /// per word, the host touching only the staging.
    pub fn capture_window<'w>(
        &'w self,
        charts: &'w ResidentCharts<'_>,
        carry: &mut ResidentCarry<'_>,
        ticks: usize,
        orientation: Orientation,
    ) -> Result<WordGraph<'w>, DeviceError> {
        if carry.staged {
            self.synchronize()?;
            carry.staged = false;
        }
        let (parity, counted) = (carry.current, carry.ticks);
        carry.current = 0;
        self.begin_capture()?;
        let issued = self.window_nodes(charts, carry, ticks, orientation);
        let captured = self.end_capture();
        carry.current = parity;
        carry.ticks = counted;
        issued?;
        let (exec, census) = captured?;
        Ok(WordGraph {
            card: self,
            charts,
            exec,
            census,
            ticks: ticks as u64,
            parity: 0,
            carry: carry.octets.device_ptr(),
            layout: carry.layout,
            window: true,
        })
    }

    /// The window graph's nodes, issued under capture.
    fn window_nodes(
        &self,
        charts: &ResidentCharts<'_>,
        carry: &mut ResidentCarry<'_>,
        ticks: usize,
        orientation: Orientation,
    ) -> Result<(), DeviceError> {
        let layout = carry.layout;
        self.zero_octets(&carry.octets, 0, layout.release(0).1)?;
        // SAFETY: `run_window` writes the staging only before the launch and reads it only after
        // the synchronization that passes the graph.
        unsafe {
            self.stage_in(
                &carry.octets,
                layout.state(0),
                &carry.staging,
                0,
                8 * layout.rows,
            )?;
        }
        for _ in 0..ticks {
            self.stage(charts, carry, orientation)?;
        }
        let (offset, octets) = layout.release(carry.current);
        unsafe {
            self.stage_out(&carry.octets, offset, &mut carry.staging, 0, octets)?;
        }
        Ok(())
    }
}

/// [definition] **A word bound as one graph** on one carry's buffers, launched at once with no
/// host work between its nodes: either `ticks` ticks ([`Card::capture_word`], launched by
/// [`WordGraph::launch`] on that carry at the parity it was captured at), or a whole window's word
/// with its load and release copies ([`Card::capture_window`], run by
/// [`ResidentCarry::run_window`]). It borrows the charts its nodes read, so they outlive it, and
/// it launches only on a carry of its card at the address and layout it was captured on; any
/// other use is refused ([`DeviceError::Graph`]).
pub struct WordGraph<'w> {
    card: &'w Card,
    charts: &'w ResidentCharts<'w>,
    exec: GraphExec,
    census: GraphCensus,
    ticks: u64,
    parity: usize,
    carry: CUdeviceptr,
    layout: CarryLayout,
    window: bool,
}

impl Drop for WordGraph<'_> {
    fn drop(&mut self) {
        // The instantiated graph is released in its card's context, after its launches.
        let _ = self.card.current();
        let _ = self.card.synchronize();
    }
}

impl WordGraph<'_> {
    /// The graph's nodes and edges, read back from the driver.
    pub fn census(&self) -> &GraphCensus {
        &self.census
    }

    /// The charts the graph reads.
    pub fn charts(&self) -> &ResidentCharts<'_> {
        self.charts
    }

    /// Whether this graph was captured on this carry (its card, address and layout).
    fn binds(&self, carry: &ResidentCarry<'_>) -> bool {
        core::ptr::eq(self.card, carry.card)
            && carry.octets.device_ptr() == self.carry
            && carry.layout == self.layout
    }

    pub fn ticks(&self) -> u64 {
        self.ticks
    }

    /// **Run the word**: one launch, every tick resident.
    pub fn launch(&self, carry: &mut ResidentCarry<'_>) -> Result<(), DeviceError> {
        if self.window || !self.binds(carry) || carry.current != self.parity {
            return Err(DeviceError::Graph);
        }
        self.card.launch_graph(&self.exec)?;
        carry.current ^= (self.ticks & 1) as usize;
        carry.ticks += self.ticks;
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------
// the inverse charts

/// [definition] **An inverse pair**: the operator `A = a·2^(−L_A)` and its chart
/// `X̂ = ξ·2^(−L_c)`, `n × n` signed 64-bit words each, row-major; `S = L_A + L_c ≤ 126`
/// ([`INVERSE_EXPONENT_CEILING`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InversePair {
    width: usize,
    operator_exponent: u32,
    chart_exponent: u32,
    operator: Vec<i64>,
    chart: Vec<i64>,
}

impl InversePair {
    pub fn new(
        width: usize,
        operator_exponent: u32,
        chart_exponent: u32,
        operator: Vec<i64>,
        chart: Vec<i64>,
    ) -> Result<Self, DeviceError> {
        for words in [&operator, &chart] {
            if width == 0 || words.len() != width * width {
                return Err(DeviceError::Shape {
                    what: "an inverse pair's n × n words (n at least one)",
                    expected: width * width,
                    found: words.len(),
                });
            }
        }
        let shift = operator_exponent.checked_add(chart_exponent);
        if shift.is_none_or(|shift| shift > INVERSE_EXPONENT_CEILING) {
            return Err(DeviceError::Exponent {
                what: "an inverse pair's S = L_A + L_c (2^S a carrier word)",
                exponent: shift.unwrap_or(u32::MAX),
                ceiling: INVERSE_EXPONENT_CEILING,
            });
        }
        Ok(Self {
            width,
            operator_exponent,
            chart_exponent,
            operator,
            chart,
        })
    }

    /// The pair of two square lattice arrays of one width.
    pub fn of_coordinates(
        operator: &LatticeCoordinates,
        chart: &LatticeCoordinates,
    ) -> Result<Self, DeviceError> {
        for array in [operator, chart] {
            if array.rows() != array.columns() || array.rows() != operator.rows() {
                return Err(DeviceError::Shape {
                    what: "an inverse pair's square arrays of one width",
                    expected: operator.rows(),
                    found: array.columns(),
                });
            }
        }
        Self::new(
            operator.rows(),
            operator.exponent(),
            chart.exponent(),
            operator.words().to_vec(),
            chart.words().to_vec(),
        )
    }

    pub fn width(&self) -> usize {
        self.width
    }

    /// `L_A`.
    pub fn operator_exponent(&self) -> u32 {
        self.operator_exponent
    }

    /// `L_c`.
    pub fn chart_exponent(&self) -> u32 {
        self.chart_exponent
    }

    /// `S = L_A + L_c`, the residual's exponent.
    pub fn shift(&self) -> u32 {
        self.operator_exponent + self.chart_exponent
    }

    /// The words `a`, row-major.
    pub fn operator(&self) -> &[i64] {
        &self.operator
    }

    /// The words `ξ`, row-major.
    pub fn chart(&self) -> &[i64] {
        &self.chart
    }
}

/// [definition] **A chart's certificate**: `‖1 − AX̂‖∞ = numerator · 2^(−exponent)`, exact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Certificate {
    numerator: u128,
    exponent: u32,
}

impl Certificate {
    /// `max_i Σ_j |ρ_ij|`.
    pub fn numerator(&self) -> u128 {
        self.numerator
    }

    /// `S`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// The exact rational.
    pub fn value(&self) -> Rat {
        Rat::new(
            BigInt::from(self.numerator),
            BigInt::one() << self.exponent as usize,
        )
    }
}

/// [definition] **Inverse charts resident on a card**: the operators, the charts (two buffers,
/// alternating from refinement to refinement) with their statuses, the residual of the current
/// charts with its statuses, and the certificates, with the layouts derived at the mount.
pub struct ResidentInverses<'c> {
    card: &'c Card,
    regions: Regions<'c>,
    shifts: Vec<u32>,
    operators: CardBuffer<'c, i64>,
    charts: [CardBuffer<'c, i64>; 2],
    chart_status: [CardBuffer<'c, u32>; 2],
    residual: CardBuffer<'c, i128>,
    residual_status: CardBuffer<'c, u32>,
    reading: CardBuffer<'c, u128>,
    current: usize,
    fresh: bool,
    refinements: u64,
    residual_layout: Layout,
    refine_layout: Layout,
    certificate_layout: Layout,
}

/// [definition] **Charts read back** (a transfer): every pair's words and statuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartRelease {
    widths: Vec<usize>,
    chart_base: Vec<usize>,
    words: Vec<i64>,
    status: Vec<u32>,
}

impl ChartRelease {
    /// Pair `g`'s chart words, row-major.
    pub fn chart(&self, pair: usize) -> &[i64] {
        let start = self.chart_base[pair];
        &self.words[start..start + self.widths[pair] * self.widths[pair]]
    }

    /// Pair `g`'s statuses, row-major.
    pub fn status(&self, pair: usize) -> &[u32] {
        let start = self.chart_base[pair];
        &self.status[start..start + self.widths[pair] * self.widths[pair]]
    }

    /// The refused entries `(pair, row, column, refusal)`.
    pub fn refusals(&self) -> Result<Vec<(usize, usize, usize, Refusal)>, DeviceError> {
        let mut refused = Vec::new();
        for (pair, &width) in self.widths.iter().enumerate() {
            for (at, &status) in self.status(pair).iter().enumerate() {
                if let Some(refusal) = Refusal::of_status(status)? {
                    refused.push((pair, at / width, at % width, refusal));
                }
            }
        }
        Ok(refused)
    }
}

impl<'c> ResidentInverses<'c> {
    /// **Mount inverse pairs** (transfers): the operators, the charts with every status exact, the
    /// tables; the layouts of the residual, the refinement and the certificate.
    pub fn mount(card: &'c Card, pairs: &[InversePair]) -> Result<Self, DeviceError> {
        let widths: Vec<usize> = pairs.iter().map(InversePair::width).collect();
        let shifts: Vec<u32> = pairs.iter().map(InversePair::shift).collect();
        let regions = Regions::mount(card, &widths, &shifts)?;
        let operators: Vec<i64> = pairs
            .iter()
            .flat_map(|pair| pair.operator.iter().copied())
            .collect();
        let charts: Vec<i64> = pairs
            .iter()
            .flat_map(|pair| pair.chart.iter().copied())
            .collect();
        let census = card.census();
        let residual_layout = read_layout(
            census,
            &card.entry(RESIDUAL_ENTRY)?,
            regions.rows,
            regions.widest,
            regions.widest,
        )?;
        let refine_layout = read_layout(
            census,
            &card.entry(REFINE_ENTRY)?,
            regions.rows,
            regions.widest,
            regions.widest,
        )?;
        let certificate_layout = certificate_layout(
            census,
            &card.entry(CERTIFICATE_ENTRY)?,
            pairs.len(),
            regions.widest,
        )?;
        let squares = regions.squares;
        Ok(Self {
            card,
            shifts,
            operators: card.upload(&operators)?,
            charts: [card.upload(&charts)?, card.alloc(squares)?],
            chart_status: [card.zeroed(squares)?, card.alloc(squares)?],
            residual: card.alloc(squares)?,
            residual_status: card.alloc(squares)?,
            reading: card.alloc(2 * pairs.len())?,
            regions,
            current: 0,
            fresh: false,
            refinements: 0,
            residual_layout,
            refine_layout,
            certificate_layout,
        })
    }

    /// The layouts of the residual, the refinement and the certificate.
    pub fn layouts(&self) -> [&Layout; 3] {
        [
            &self.residual_layout,
            &self.refine_layout,
            &self.certificate_layout,
        ]
    }

    /// The refinements run since the mount.
    pub fn refinements(&self) -> u64 {
        self.refinements
    }

    /// The residual `ρ = 2^S·1 − aξ` of the current charts, resident (skipped when it is already
    /// the current charts').
    fn residual(&mut self) -> Result<(), DeviceError> {
        if self.fresh {
            return Ok(());
        }
        let regions = &self.regions;
        let mut operators = self.operators.device_ptr();
        let mut charts = self.charts[self.current].device_ptr();
        let mut chart_status = self.chart_status[self.current].device_ptr();
        let mut widths = regions.width_words.device_ptr();
        let mut chart_base = regions.chart_base_words.device_ptr();
        let mut row_base = regions.row_base_words.device_ptr();
        let mut shifts = regions.shift_words.device_ptr();
        let mut row_region = regions.row_region.device_ptr();
        let mut rows = regions.rows as u32;
        let mut residual = self.residual.device_ptr();
        let mut residual_status = self.residual_status.device_ptr();
        let mut params = arguments![
            operators,
            charts,
            chart_status,
            widths,
            chart_base,
            row_base,
            shifts,
            row_region,
            rows,
            residual,
            residual_status,
        ];
        self.card
            .launch(RESIDUAL_ENTRY, &self.residual_layout, &mut params)?;
        self.fresh = true;
        Ok(())
    }

    /// **One Newton–Schulz refinement of every chart**, resident: the residual (when not current),
    /// then `ξ'' = ξ + split_S(ξρ).q` into the other chart buffer. Nothing crosses the bus.
    pub fn refine(&mut self) -> Result<(), DeviceError> {
        self.residual()?;
        let regions = &self.regions;
        let (from, to) = (self.current, 1 - self.current);
        let mut charts = self.charts[from].device_ptr();
        let mut chart_status = self.chart_status[from].device_ptr();
        let mut residual = self.residual.device_ptr();
        let mut residual_status = self.residual_status.device_ptr();
        let mut widths = regions.width_words.device_ptr();
        let mut chart_base = regions.chart_base_words.device_ptr();
        let mut row_base = regions.row_base_words.device_ptr();
        let mut shifts = regions.shift_words.device_ptr();
        let mut row_region = regions.row_region.device_ptr();
        let mut rows = regions.rows as u32;
        let mut next = self.charts[to].device_ptr();
        let mut next_status = self.chart_status[to].device_ptr();
        let mut params = arguments![
            charts,
            chart_status,
            residual,
            residual_status,
            widths,
            chart_base,
            row_base,
            shifts,
            row_region,
            rows,
            next,
            next_status,
        ];
        self.card
            .launch(REFINE_ENTRY, &self.refine_layout, &mut params)?;
        self.current = to;
        self.fresh = false;
        self.refinements += 1;
        Ok(())
    }

    /// **The current charts' certificates** (the residual when not current, the reduction, and one
    /// transfer of a numerator and a status word per chart): each exact, or its refusal.
    pub fn certificates(&mut self) -> Result<Vec<Result<Certificate, Refusal>>, DeviceError> {
        self.residual()?;
        let regions = &self.regions;
        let mut residual = self.residual.device_ptr();
        let mut residual_status = self.residual_status.device_ptr();
        let mut widths = regions.width_words.device_ptr();
        let mut chart_base = regions.chart_base_words.device_ptr();
        let pairs = regions.widths.len();
        let mut charts = pairs as u32;
        let mut reading = self.reading.device_ptr();
        let mut params = arguments![
            residual,
            residual_status,
            widths,
            chart_base,
            charts,
            reading,
        ];
        self.card
            .launch(CERTIFICATE_ENTRY, &self.certificate_layout, &mut params)?;
        let read = self.card.fetch(&self.reading)?;
        let (numerators, statuses) = read.split_at(pairs);
        numerators
            .iter()
            .zip(statuses)
            .zip(&self.shifts)
            .map(|((&numerator, &status), &exponent)| {
                let status =
                    u32::try_from(status).map_err(|_| DeviceError::Status { status: u32::MAX })?;
                Ok(match Refusal::of_status(status)? {
                    None => Ok(Certificate {
                        numerator,
                        exponent,
                    }),
                    Some(refusal) => Err(refusal),
                })
            })
            .collect()
    }

    /// **A deposit moved an operator** (a transfer of its words): pair `g`'s `a` is replaced in
    /// place and its chart kept, the warm start (`warm_start_certificate`: the residual grows by at
    /// most `‖D‖∞‖X̂‖∞`, which the next refinements square away).
    pub fn replace_operator(&mut self, pair: usize, words: &[i64]) -> Result<(), DeviceError> {
        let width = *self.regions.widths.get(pair).ok_or(DeviceError::Shape {
            what: "a mounted pair",
            expected: self.regions.widths.len(),
            found: pair,
        })?;
        if words.len() != width * width {
            return Err(DeviceError::Shape {
                what: "the operator's n × n words",
                expected: width * width,
                found: words.len(),
            });
        }
        self.card
            .write(&self.operators, self.regions.chart_base[pair], words)?;
        self.fresh = false;
        Ok(())
    }

    /// **The current charts read back** (a transfer).
    pub fn charts(&self) -> Result<ChartRelease, DeviceError> {
        Ok(ChartRelease {
            widths: self.regions.widths.clone(),
            chart_base: self.regions.chart_base.clone(),
            words: self.card.fetch(&self.charts[self.current])?,
            status: self.card.fetch(&self.chart_status[self.current])?,
        })
    }

    /// **The current residual read back** (a transfer): `ρ` and its statuses, pair by pair.
    pub fn residual_words(&mut self) -> Result<(Vec<i128>, Vec<u32>), DeviceError> {
        self.residual()?;
        Ok((
            self.card.fetch(&self.residual)?,
            self.card.fetch(&self.residual_status)?,
        ))
    }
}
