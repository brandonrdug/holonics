//! **The executed charts resident on the card, keyed, and their refinement** (Decision 24; kernels
//! `hnn_inverse_residual`, `hnn_inverse_refine`, `hnn_inverse_certificate`, `hnn_copy_words`).
//!
//! [definition] The host owner is `holonics::hnn::chart::{refine, Charts}`: the resident keeps the
//! last chart of each operator it inverts, keyed by [`ChartKey`] (a ring's `I − ½K_r`, a contact's
//! `m_a` per conductance carry), and every word refines each of its charts from that start. The
//! [`ChartStore`] keeps those charts on the card, with each key's last operator words, and runs the
//! host's refinement **step for step** on a word's pairs together:
//!
//! - **warm**: a kept chart of the operator's width is certified against the new operator; at most
//!   `½` it is the start (`ChartStart::Warm`);
//! - **cold**: otherwise the scaled transpose `2^(−p)Aᵀ` (`holonics::hnn::chart::transpose_start`,
//!   formed on the host from the operator's words and uploaded, `n²` words), refined while its
//!   certificate is above `½` and its steps within the bound (`ChartStart::Transpose`);
//! - **fallback**: past the bound, one exact inverse on the host, rounded to the chart's lattice
//!   and uploaded (`ChartStart::Exact`);
//! - **target**: then rounded Newton–Schulz steps while the certificate is above `δ = 2^(−D_c)`,
//!   each required to lower it, or the word is refused (`HnnError::ChartCertificate`) and no key's
//!   chart moves.
//!
//! Every step and certificate runs on the card; the host reads one certificate per pair per step
//! (`2 × 16` octets) and decides, as the host owner does, from the exact ratio. The certificates are
//! the same exact rationals as the host's (`max_i Σ_j |ρ_ij| / 2^S` is representation-free), and a
//! rounded step's chart is the nearest lattice point of `X̂(2 − AX̂)` whatever the operator's
//! denominator, so the charts are the host's charts.
//!
//! [definition] **The workspace.** A word refines its pairs in a workspace of two chart blocks per
//! pair (the kept charts copied in, or the cold starts written), so a refusal mid-way leaves every
//! kept chart as it was, as the host's `Operands::at_cut_charted` leaves the resident's charts when
//! a refinement refuses. On success the moved charts are copied back to their keys (and read once
//! to the host's mirror of the charts' bits), and the word copies its own charts from the workspace
//! into its operands.

use std::collections::BTreeMap;

use core::ffi::c_void;

use holonics::hnn::chart::transpose_start;
use holonics::hnn::{ChartKey, ChartReading, ChartStart, ChartWords, HnnError, WordLattice};
use holonics::ratio::Rat;
use holonics::ratio::linear::ExactRatMatrix;
use num_bigint::BigInt;
use num_traits::One;

use crate::ffi::CUdeviceptr;
use crate::hnn::DeviceError;
use crate::hnn::card::{Card, CardBuffer, Layout, certificate_layout, copy_layout, read_layout};
use crate::hnn::dyadic::{DyadicMatrix, refused, value};
use crate::hnn::word::{
    CERTIFICATE_ENTRY, INVERSE_EXPONENT_CEILING, REFINE_ENTRY, RESIDUAL_ENTRY, Refusal,
};

/// The copies' entry in the image.
pub const COPY_ENTRY: &str = "hnn_copy_words";

macro_rules! arguments {
    ($($value:ident),* $(,)?) => {
        [$(&mut $value as *mut _ as *mut c_void),*]
    };
}

/// One key's place in the store.
#[derive(Clone, Debug)]
struct Slot {
    width: usize,
    offset: usize,
    present: bool,
    operator: Option<DyadicMatrix>,
}

/// [definition] **A pair a word refines**: its key and its operator, exact and as words.
pub(crate) struct Pair<'a> {
    pub(crate) key: ChartKey,
    pub(crate) matrix: &'a ExactRatMatrix,
    pub(crate) words: &'a DyadicMatrix,
}

/// [definition] **A word's refined charts in the workspace**: per pair its width and the offset of
/// its final chart's words in the workspace, with the pairs' readings in order.
pub(crate) struct Refined {
    pub(crate) charts: Vec<(usize, usize)>,
    pub(crate) readings: Vec<ChartReading>,
}

/// The phase of one pair's refinement (the host owner's `refine`, state by state).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    CheckWarm,
    StartCold,
    Cold { bound: u32 },
    Fallback,
    Target,
    Stepped,
    Done,
    Refused,
}

struct State {
    key: ChartKey,
    width: usize,
    shift: u32,
    base: usize,
    half: usize,
    phase: Phase,
    steps: u32,
    start: ChartStart,
    delta: Option<Rat>,
    certify: bool,
    step: bool,
    refusal: Option<HnnError>,
}

/// [definition] **The executed charts resident on a card**, keyed (module header).
pub(crate) struct ChartStore<'c> {
    card: &'c Card,
    exponent: u32,
    target: Rat,
    slots: BTreeMap<ChartKey, Slot>,
    used: usize,
    operators: CardBuffer<'c, i64>,
    kept: CardBuffer<'c, i64>,
    work: CardBuffer<'c, i64>,
    work_status: CardBuffer<'c, u32>,
    residual: CardBuffer<'c, i128>,
    residual_status: CardBuffer<'c, u32>,
    reading: CardBuffer<'c, u128>,
    /// The host's mirror of the kept charts: their words, read when a refinement moved them.
    mirror: BTreeMap<ChartKey, ChartWords>,
    /// The pairs' tables, kept between refinements and rewritten for each.
    tables: Option<Tables<'c>>,
    /// The octets the store's refinements took across the bus, and the launches it made.
    pub(crate) octets: usize,
    pub(crate) launches: u64,
}

fn device(error: DeviceError) -> HnnError {
    error.into_hnn()
}

impl<'c> ChartStore<'c> {
    /// **An empty store** for the word's declared precisions: no key kept, every first
    /// refinement cold.
    pub(crate) fn new(card: &'c Card, lattice: &WordLattice) -> Result<Self, HnnError> {
        let words = 1;
        Ok(Self {
            card,
            exponent: lattice.chart_exponent(),
            target: lattice.target(),
            slots: BTreeMap::new(),
            used: 0,
            operators: card.alloc(words).map_err(device)?,
            kept: card.alloc(words).map_err(device)?,
            work: card.alloc(words).map_err(device)?,
            work_status: card.alloc(words).map_err(device)?,
            residual: card.alloc(words).map_err(device)?,
            residual_status: card.alloc(words).map_err(device)?,
            reading: card.alloc(2).map_err(device)?,
            mirror: BTreeMap::new(),
            tables: None,
            octets: 0,
            launches: 0,
        })
    }

    /// The kept charts' bits, a reading (`holonics::hnn::Charts::bits`).
    pub(crate) fn bits(&self) -> u64 {
        self.mirror.values().map(ChartWords::bits).sum()
    }

    /// The workspace's words (the word's operands copy their charts from it).
    pub(crate) fn workspace(&self) -> &CardBuffer<'c, i64> {
        &self.work
    }

    /// Place a key, growing the kept charts and operators on the card when full (the kept words
    /// copied over on the card).
    fn place(&mut self, key: &ChartKey, width: usize) -> Result<(), HnnError> {
        if let Some(slot) = self.slots.get(key)
            && slot.width == width
        {
            return Ok(());
        }
        let offset = self.used;
        let need = offset + width * width;
        if need > self.kept.len() {
            let capacity = need.max(2 * self.kept.len());
            let kept = self.card.alloc::<i64>(capacity).map_err(device)?;
            let operators = self.card.alloc::<i64>(capacity).map_err(device)?;
            if self.used > 0 {
                self.card
                    .copy_within(&self.kept, 0, &kept, 0, self.used)
                    .map_err(device)?;
                self.card
                    .copy_within(&self.operators, 0, &operators, 0, self.used)
                    .map_err(device)?;
            }
            self.kept = kept;
            self.operators = operators;
        }
        self.used = need;
        self.slots.insert(
            key.clone(),
            Slot {
                width,
                offset,
                present: false,
                operator: None,
            },
        );
        Ok(())
    }

    /// Size the workspace for `words` chart words per half (two halves per pair).
    fn reserve(&mut self, words: usize, pairs: usize) -> Result<(), HnnError> {
        if 2 * words > self.work.len() {
            self.work = self.card.alloc(2 * words).map_err(device)?;
            self.work_status = self.card.alloc(2 * words).map_err(device)?;
        }
        if words > self.residual.len() {
            self.residual = self.card.alloc(words).map_err(device)?;
            self.residual_status = self.card.alloc(words).map_err(device)?;
        }
        if 2 * pairs > self.reading.len() {
            self.reading = self.card.alloc(2 * pairs).map_err(device)?;
        }
        Ok(())
    }

    /// **Refine a word's pairs** (module header), rings then contacts in the host's order: their
    /// readings in that order, and where each final chart lies in the workspace. A refusal leaves
    /// every kept chart as it was and returns the first pair's refusal in order.
    pub(crate) fn refine(&mut self, pairs: &[Pair<'_>]) -> Result<Refined, HnnError> {
        let card = self.card;
        let lc = self.exponent;
        // Place every key and move its operator words onto the card when they changed.
        let mut words = 0usize;
        let mut states = Vec::with_capacity(pairs.len());
        for pair in pairs {
            let n = pair.words.rows;
            if pair.words.columns != n {
                return Err(refused("a chart's operator is square"));
            }
            self.place(&pair.key, n)?;
            let shift = pair.words.exponent + lc;
            if shift > INVERSE_EXPONENT_CEILING {
                return Err(refused(
                    "an operator's S = L_A + L_c past the carrier's 126 (2^S a carrier word)",
                ));
            }
            let slot = self.slots.get_mut(&pair.key).expect("placed");
            if slot.operator.as_ref() != Some(pair.words) {
                card.write(&self.operators, slot.offset, &pair.words.words)
                    .map_err(device)?;
                self.octets += 8 * pair.words.words.len();
                slot.operator = Some(pair.words.clone());
            }
            states.push(State {
                key: pair.key.clone(),
                width: n,
                shift,
                base: words,
                half: 0,
                phase: if slot.present {
                    Phase::CheckWarm
                } else {
                    Phase::StartCold
                },
                steps: 0,
                start: ChartStart::Warm,
                delta: None,
                certify: false,
                step: false,
                refusal: None,
            });
            words += n * n;
        }
        self.reserve(words, pairs.len())?;
        card.zero_octets(&self.work_status, 0, 4 * 2 * words)
            .map_err(device)?;
        // The kept charts are the warm starts, copied into each pair's first block.
        let warm: Vec<[u64; 3]> = states
            .iter()
            .filter(|state| state.phase == Phase::CheckWarm)
            .map(|state| {
                let slot = &self.slots[&state.key];
                [
                    slot.offset as u64,
                    (2 * state.base) as u64,
                    (state.width * state.width) as u64,
                ]
            })
            .collect();
        if !warm.is_empty() {
            copy_words(card, &self.kept, &self.work, &warm).map_err(device)?;
            self.launches += 1;
        }
        for state in &mut states {
            if state.phase == Phase::CheckWarm {
                state.certify = true;
            }
        }
        // The pairs' fixed tables.
        let mut tables = self.tables.take().filter(|t| t.fits(&states));
        let tables = match tables.take() {
            Some(tables) => tables,
            None => Tables::alloc(card, &states)?,
        };
        tables.load(card, &states, &self.slots)?;
        let refined = self.run(&tables, pairs, states);
        self.tables = Some(tables);
        refined
    }

    /// The refinement's loop over the pairs' phases, and the commit.
    fn run(
        &mut self,
        tables: &Tables<'c>,
        pairs: &[Pair<'_>],
        mut states: Vec<State>,
    ) -> Result<Refined, HnnError> {
        let card = self.card;
        let lc = self.exponent;
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        loop {
            // Cold starts and fallbacks are written into the pair's current block.
            for (state, pair) in states.iter_mut().zip(pairs) {
                let written = match state.phase {
                    Phase::StartCold => {
                        let (chart, bound) = transpose_start(pair.matrix, lc)?;
                        state.phase = Phase::Cold { bound };
                        state.start = ChartStart::Transpose;
                        state.steps = 0;
                        Some(chart)
                    }
                    Phase::Fallback => {
                        let chart = ChartWords::of_matrix(&pair.matrix.inverse()?, lc)?;
                        state.phase = Phase::Target;
                        state.start = ChartStart::Exact;
                        Some(chart)
                    }
                    _ => None,
                };
                if let Some(chart) = written {
                    let at = 2 * state.base + state.half * state.width * state.width;
                    card.write(&self.work, at, chart.words()).map_err(device)?;
                    card.zero_octets(&self.work_status, 4 * at, 4 * chart.words().len())
                        .map_err(device)?;
                    self.octets += 8 * chart.words().len();
                    state.certify = true;
                    state.delta = None;
                }
            }
            // Certify the pairs that need it.
            if states.iter().any(|state| state.certify) {
                let deltas = self.certify(tables, &states)?;
                for (state, delta) in states.iter_mut().zip(deltas) {
                    if !state.certify {
                        continue;
                    }
                    state.certify = false;
                    match delta {
                        Ok(delta) => {
                            let previous = state.delta.replace(delta.clone());
                            match state.phase {
                                Phase::CheckWarm => {
                                    if delta <= half {
                                        state.start = ChartStart::Warm;
                                        state.phase = Phase::Target;
                                    } else {
                                        state.phase = Phase::StartCold;
                                    }
                                }
                                Phase::Stepped => {
                                    let before =
                                        previous.expect("a stepped chart had its certificate");
                                    if delta >= before {
                                        state.phase = Phase::Refused;
                                        state.refusal = Some(HnnError::ChartCertificate {
                                            chart: state.key.clone(),
                                            certificate: Box::new(delta),
                                            target: Box::new(self.target.clone()),
                                        });
                                    } else {
                                        state.phase = Phase::Target;
                                    }
                                }
                                _ => {}
                            }
                        }
                        Err(refusal) => {
                            state.phase = Phase::Refused;
                            state.refusal = Some(refusal);
                        }
                    }
                }
            }
            // Decide each pair's next move from its certificate.
            for state in &mut states {
                state.step = false;
                let Some(delta) = state.delta.clone() else {
                    continue;
                };
                if let Phase::Cold { bound } = state.phase {
                    if delta > half && state.steps < bound {
                        state.step = true;
                    } else if delta <= half {
                        state.phase = Phase::Target;
                    } else {
                        state.phase = Phase::Fallback;
                    }
                }
                if state.phase == Phase::Target {
                    if delta > self.target {
                        state.step = true;
                        state.phase = Phase::Stepped;
                    } else {
                        state.phase = Phase::Done;
                    }
                }
            }
            if states.iter().any(|state| state.step) {
                self.step(tables, &states)?;
                for state in &mut states {
                    if state.step {
                        state.half = 1 - state.half;
                        state.steps += 1;
                        state.certify = true;
                    }
                }
            }
            if states
                .iter()
                .all(|state| matches!(state.phase, Phase::Done | Phase::Refused))
            {
                break;
            }
        }
        if let Some(refusal) = states.iter_mut().find_map(|state| state.refusal.take()) {
            return Err(refusal);
        }
        // Commit the moved charts to their keys, and read them to the host's mirror.
        let moved: Vec<&State> = states
            .iter()
            .filter(|state| state.steps > 0 || state.start != ChartStart::Warm)
            .collect();
        if !moved.is_empty() {
            let table: Vec<[u64; 3]> = moved
                .iter()
                .map(|state| {
                    let n2 = state.width * state.width;
                    [
                        (2 * state.base + state.half * n2) as u64,
                        self.slots[&state.key].offset as u64,
                        n2 as u64,
                    ]
                })
                .collect();
            copy_words(card, &self.work, &self.kept, &table).map_err(device)?;
            self.launches += 1;
            for state in &moved {
                let n2 = state.width * state.width;
                let at = 2 * state.base + state.half * n2;
                let chart = card.fetch_range(&self.work, at, n2).map_err(device)?;
                self.octets += 8 * n2;
                let coordinates: Vec<BigInt> = chart.iter().map(|w| BigInt::from(*w)).collect();
                self.mirror.insert(
                    state.key.clone(),
                    ChartWords::of_coordinates(state.width, state.width, lc, &coordinates)?,
                );
            }
        }
        for state in &states {
            self.slots.get_mut(&state.key).expect("placed").present = true;
        }
        Ok(Refined {
            charts: states
                .iter()
                .map(|state| {
                    (
                        state.width,
                        2 * state.base + state.half * state.width * state.width,
                    )
                })
                .collect(),
            readings: states
                .iter()
                .map(|state| ChartReading {
                    key: state.key.clone(),
                    width: state.width,
                    certificate: state.delta.clone().expect("a finished chart is certified"),
                    target: self.target.clone(),
                    steps: state.steps,
                    start: state.start,
                })
                .collect(),
        })
    }

    /// The residual of every pair that needs a certificate, then every pair's certificate (one
    /// read of a numerator and a status per pair).
    fn certify(
        &mut self,
        tables: &Tables<'c>,
        states: &[State],
    ) -> Result<Vec<Result<Rat, HnnError>>, HnnError> {
        let card = self.card;
        let active: Vec<u32> = states.iter().map(|s| u32::from(s.certify)).collect();
        let chart_base: Vec<u64> = states
            .iter()
            .map(|s| (2 * s.base + s.half * s.width * s.width) as u64)
            .collect();
        card.write(&tables.active, 0, &active).map_err(device)?;
        card.write(&tables.chart_base, 0, &chart_base)
            .map_err(device)?;
        let mut operators = self.operators.device_ptr();
        let mut operator_base = tables.operator_base.device_ptr();
        let mut charts = self.work.device_ptr();
        let mut chart_status = self.work_status.device_ptr();
        let mut chart_base_ptr = tables.chart_base.device_ptr();
        let mut widths = tables.widths.device_ptr();
        let mut row_base = tables.row_base.device_ptr();
        let mut shifts = tables.shifts.device_ptr();
        let mut row_region = tables.row_region.device_ptr();
        let mut rows = tables.rows as u32;
        let mut active_ptr = tables.active.device_ptr();
        let mut residual = self.residual.device_ptr();
        let mut residual_status = self.residual_status.device_ptr();
        let mut residual_base = tables.residual_base.device_ptr();
        let mut params = arguments![
            operators,
            operator_base,
            charts,
            chart_status,
            chart_base_ptr,
            widths,
            row_base,
            shifts,
            row_region,
            rows,
            active_ptr,
            residual,
            residual_status,
            residual_base,
        ];
        card.owns(&self.operators).map_err(device)?;
        card.launch(RESIDUAL_ENTRY, &tables.residual_layout, &mut params)
            .map_err(device)?;
        let mut residual = self.residual.device_ptr();
        let mut residual_status = self.residual_status.device_ptr();
        let mut residual_base = tables.residual_base.device_ptr();
        let mut widths = tables.widths.device_ptr();
        let mut count = states.len() as u32;
        let mut reading = self.reading.device_ptr();
        let mut params = arguments![
            residual,
            residual_status,
            residual_base,
            widths,
            count,
            reading
        ];
        card.launch(CERTIFICATE_ENTRY, &tables.certificate_layout, &mut params)
            .map_err(device)?;
        self.launches += 2;
        let read = card
            .fetch_range(&self.reading, 0, 2 * states.len())
            .map_err(device)?;
        self.octets += 32 * states.len();
        let (numerators, statuses) = read.split_at(states.len());
        Ok(states
            .iter()
            .zip(numerators.iter().zip(statuses))
            .map(|(state, (&numerator, &status))| {
                let status = u32::try_from(status).unwrap_or(u32::MAX);
                match Refusal::of_status(status).map_err(device)? {
                    None => Ok(value(BigInt::from(numerator), state.shift)),
                    Some(_) => Err(HnnError::Carrier {
                        what: "a chart's certificate on the card (carrier, word or operand)",
                    }),
                }
            })
            .collect())
    }

    /// One rounded Newton–Schulz step of the pairs that step, each into its other block.
    fn step(&mut self, tables: &Tables<'c>, states: &[State]) -> Result<(), HnnError> {
        let card = self.card;
        let active: Vec<u32> = states.iter().map(|s| u32::from(s.step)).collect();
        let chart_base: Vec<u64> = states
            .iter()
            .map(|s| (2 * s.base + s.half * s.width * s.width) as u64)
            .collect();
        let next_base: Vec<u64> = states
            .iter()
            .map(|s| (2 * s.base + (1 - s.half) * s.width * s.width) as u64)
            .collect();
        card.write(&tables.active, 0, &active).map_err(device)?;
        card.write(&tables.chart_base, 0, &chart_base)
            .map_err(device)?;
        card.write(&tables.next_base, 0, &next_base)
            .map_err(device)?;
        let mut charts = self.work.device_ptr();
        let mut chart_status = self.work_status.device_ptr();
        let mut chart_base_ptr = tables.chart_base.device_ptr();
        let mut residual = self.residual.device_ptr();
        let mut residual_status = self.residual_status.device_ptr();
        let mut residual_base = tables.residual_base.device_ptr();
        let mut widths = tables.widths.device_ptr();
        let mut row_base = tables.row_base.device_ptr();
        let mut shifts = tables.shifts.device_ptr();
        let mut row_region = tables.row_region.device_ptr();
        let mut rows = tables.rows as u32;
        let mut active_ptr = tables.active.device_ptr();
        let mut next = self.work.device_ptr();
        let mut next_status = self.work_status.device_ptr();
        let mut next_base_ptr = tables.next_base.device_ptr();
        let mut params = arguments![
            charts,
            chart_status,
            chart_base_ptr,
            residual,
            residual_status,
            residual_base,
            widths,
            row_base,
            shifts,
            row_region,
            rows,
            active_ptr,
            next,
            next_status,
            next_base_ptr,
        ];
        card.launch(REFINE_ENTRY, &tables.refine_layout, &mut params)
            .map_err(device)?;
        self.launches += 1;
        Ok(())
    }
}

/// The pair tables of one refinement, with the launches' layouts.
struct Tables<'c> {
    rows: usize,
    pairs: usize,
    widest: usize,
    widths: CardBuffer<'c, u32>,
    row_base: CardBuffer<'c, u64>,
    shifts: CardBuffer<'c, u32>,
    row_region: CardBuffer<'c, u32>,
    operator_base: CardBuffer<'c, u64>,
    residual_base: CardBuffer<'c, u64>,
    chart_base: CardBuffer<'c, u64>,
    next_base: CardBuffer<'c, u64>,
    active: CardBuffer<'c, u32>,
    residual_layout: Layout,
    refine_layout: Layout,
    certificate_layout: Layout,
}

impl<'c> Tables<'c> {
    /// Tables with room for these pairs (and at least as many as a word of this shape).
    fn alloc(card: &'c Card, states: &[State]) -> Result<Self, HnnError> {
        let pairs = states.len().max(1);
        let rows: usize = states.iter().map(|s| s.width).sum::<usize>().max(1);
        let widest = states.iter().map(|s| s.width).max().unwrap_or(1);
        let census = card.census();
        Ok(Self {
            rows,
            pairs,
            widest,
            widths: card.alloc(pairs).map_err(device)?,
            row_base: card.alloc(pairs).map_err(device)?,
            shifts: card.alloc(pairs).map_err(device)?,
            row_region: card.alloc(rows).map_err(device)?,
            operator_base: card.alloc(pairs).map_err(device)?,
            residual_base: card.alloc(pairs).map_err(device)?,
            chart_base: card.alloc(pairs).map_err(device)?,
            next_base: card.alloc(pairs).map_err(device)?,
            active: card.alloc(pairs).map_err(device)?,
            residual_layout: read_layout(
                census,
                &card.entry(RESIDUAL_ENTRY).map_err(device)?,
                rows,
                widest,
                widest,
            )
            .map_err(device)?,
            refine_layout: read_layout(
                census,
                &card.entry(REFINE_ENTRY).map_err(device)?,
                rows,
                widest,
                widest,
            )
            .map_err(device)?,
            certificate_layout: certificate_layout(
                census,
                &card.entry(CERTIFICATE_ENTRY).map_err(device)?,
                pairs,
                widest,
            )
            .map_err(device)?,
        })
    }

    /// Whether these tables were derived for exactly this shape of pairs (their layouts cover it).
    fn fits(&self, states: &[State]) -> bool {
        let rows: usize = states.iter().map(|s| s.width).sum();
        let widest = states.iter().map(|s| s.width).max().unwrap_or(1);
        states.len() == self.pairs && rows == self.rows && widest == self.widest
    }

    /// Write a refinement's fixed tables (one transfer each).
    fn load(
        &self,
        card: &Card,
        states: &[State],
        slots: &BTreeMap<ChartKey, Slot>,
    ) -> Result<(), HnnError> {
        let mut row_base = Vec::with_capacity(states.len());
        let mut row_region = Vec::with_capacity(self.rows);
        let mut rows = 0usize;
        for (g, state) in states.iter().enumerate() {
            row_base.push(rows as u64);
            rows += state.width;
            row_region.extend(core::iter::repeat_n(g as u32, state.width));
        }
        let widths: Vec<u32> = states.iter().map(|s| s.width as u32).collect();
        let shifts: Vec<u32> = states.iter().map(|s| s.shift).collect();
        let operator_base: Vec<u64> = states.iter().map(|s| slots[&s.key].offset as u64).collect();
        let residual_base: Vec<u64> = states.iter().map(|s| s.base as u64).collect();
        card.write(&self.widths, 0, &widths).map_err(device)?;
        card.write(&self.row_base, 0, &row_base).map_err(device)?;
        card.write(&self.shifts, 0, &shifts).map_err(device)?;
        card.write(&self.row_region, 0, &row_region)
            .map_err(device)?;
        card.write(&self.operator_base, 0, &operator_base)
            .map_err(device)?;
        card.write(&self.residual_base, 0, &residual_base)
            .map_err(device)?;
        Ok(())
    }
}

/// **Copies between resident arrays** (`hnn_copy_words`): each `(from, to, words)` of `source`
/// into `target`, one launch.
pub(crate) fn copy_words(
    card: &Card,
    source: &CardBuffer<'_, i64>,
    target: &CardBuffer<'_, i64>,
    table: &[[u64; 3]],
) -> Result<(), DeviceError> {
    if table.is_empty() {
        return Ok(());
    }
    card.owns(source)?;
    card.owns(target)?;
    let widest = table.iter().map(|copy| copy[2] as usize).max().unwrap_or(1);
    let layout = copy_layout(card.census(), &card.entry(COPY_ENTRY)?, table.len(), widest)?;
    let flat: Vec<u64> = table.iter().flatten().copied().collect();
    let staged = card.upload(&flat)?;
    let mut source_ptr: CUdeviceptr = source.device_ptr();
    let mut target_ptr: CUdeviceptr = target.device_ptr();
    let mut table_ptr = staged.device_ptr();
    let mut copies = table.len() as u32;
    let mut params = arguments![source_ptr, target_ptr, table_ptr, copies];
    card.launch(COPY_ENTRY, &layout, &mut params)?;
    Ok(())
}
