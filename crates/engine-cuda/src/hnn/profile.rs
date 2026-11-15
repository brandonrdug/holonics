//! The card realization's profile (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::hnn::field::*;
#[allow(unused_imports)]
use core::ffi::c_void;
#[allow(unused_imports)]
use std::time::Instant;
#[allow(unused_imports)]
use holonics_engine::field::{band_bits, landmarks_of, BlankClocks, CarryGates, Constitution, Declaration, ReadLogits, Realization, HeldRows, NearOffsets, RealizationCounters, RowCurrent, Region, Scale, TickRead, NEAR, SHARE_BITS, STATE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{level_cut, level_section, PACE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{TowerError, TowerFace, MATERIAL_BITS};
#[allow(unused_imports)]
use crate::cuda::{Dim3, Module};
#[allow(unused_imports)]
use crate::hnn::card::{Card, CardBuffer, CardError};

/// The card's time on the field: forwards (reads), returns, their wall time and the site pairs met.
#[derive(Clone, Copy, Debug, Default)]
pub struct FieldTimes {
    pub reads: u64,
    pub read_ns: u128,
    pub returns: u64,
    pub return_ns: u128,
    /// The site pairs the contact met, `Σ |S_i^h|` over every row, head and tick of every read
    /// (counted on the card).
    pub pairs: u128,
    pub batches: u64,
    /// The largest batch's counted allocations (weights, contact return and per-site carriers), in
    /// octets.
    pub peak_store: u64,
    /// The landmark reads ([`Realization::read_landmarks`]) and their wall time, apart from the
    /// reads and pairs above.
    pub landmarks: u64,
    pub landmark_ns: u128,
    /// [measurement; theory, November 12, P50 step 1 and P51] The clock's skins ([`skin_octets`]): the largest batch's store, the octets a reserved
    /// support entry and a site (zero where no head is paced), the support entries `E2` and the dense pairs summed over the batches, and the largest
    /// batch's `E2` beside its dense pairs.
    pub skin_store: u64,
    pub skin_entry_octets: u64,
    pub skin_site_octets: u64,
    pub skin_entries: u128,
    pub skin_dense_pairs: u128,
    pub skin_peak_entries: u64,
    pub skin_peak_pairs: u64,
    /// [measurement; theory, November 12, P50 step 2] A clock's near phases and skins: octets a site.
    pub clock_site_octets: u64,
    /// The batches' cut: four fifths of the batch budget less the exponential's face, the last run's.
    pub batch_cut: u64,
}

/// [measurement; theory, November 12, P54 item 1] The ruler build's arrays whose words' bits it reads, by clock (`field_yard_bits_*`).
/// [measurement; theory, November 13, P56 item 1] After them, the share `e` by head and by the receiver's kind (definite, open), heads 0 to 3.
pub const BITS_NAMES: [&str; 30] = [
    "e_score", "e_share", "sb", "ds", "dpb", "skin_l0", "skin_l1", "skin_l2", "skin_l3", "skin_l4", "skin_l5", "skin_l6", "skin_l7", "vf", "qf", "pq", "qf32", "pq32", "ce", "sc", "sw", "sv",
    "e_share_h0_definite", "e_share_h0_open", "e_share_h1_definite", "e_share_h1_open", "e_share_h2_definite", "e_share_h2_open", "e_share_h3_definite", "e_share_h3_open",
];

pub const BITS_TICKS: usize = 4;

pub const BITS_BINS: usize = 129;

/// [measurement; P57 item 1] One launch as a trace reads it (`FieldProfile::trace`).
#[derive(Clone, Debug, Default)]
pub struct LaunchRecord {
    pub run: u64,
    pub phase: &'static str,
    pub entry: &'static str,
    pub grid: [u32; 3],
    pub block: u32,
    pub shared: u32,
    pub ns: u128,
    pub head: Option<u32>,
}

/// [measurement; P57 item 1] An entry's lowering on the mounted card: registers a thread, static shared and local octets, the
/// largest block, and the blocks a multiprocessor keeps resident at the launch's block and dynamic shared octets.
#[derive(Clone, Copy, Debug, Default)]
pub struct EntryAttributes {
    pub registers: u32,
    pub static_shared: u32,
    pub local: usize,
    pub max_threads: u32,
    pub blocks_a_multiprocessor: u32,
}

/// [measurement; theory, November 13, P61 item 3] A site's map's launch kind: the entry, its rows and cols, whether it reads only the open
/// sites, and whether it adds into its output (`add` for a forward map, `accumulate` for a transposed one).
pub type MapKind = (&'static str, u32, u32, bool, bool);

/// [measurement; P61 item 3] A kind's operands read by the bits ruler: the largest weight (`wmax`) and each operand's largest word in bits;
/// its sites and those whose row stands under `2^31`, by operand; its tiles of [`MAP_TILE`] sites and those whose sums stand in 64 bits under
/// the limb test ([`tile_proves`]), and in 96 bits (a third carry word, a reading only); its launches whose every tile proves.
#[derive(Clone, Debug, Default)]
pub struct MapBits {
    pub launches: u64,
    pub w_bits: u32,
    pub bits: [u32; 2],
    pub sites: u64,
    pub under31: [u64; 2],
    pub tiles: u64,
    pub proved64: u64,
    pub proved96: u64,
    pub launches_all64: u64,
    pub launches_all96: u64,
}

/// [measurement; P61 item 3] The sites a tile of the tiled form holds (a block's 64 sites at a 64 by 64 map).
pub const MAP_TILE: usize = 64;

/// [definition; P61 item 4c, `agent-inferred`] **A tile's sums stand in `bits` bits** where its magnitudes prove it: `k` terms a sum, each a
/// product of two operands of largest magnitudes `a` and `b` (a weight on 32 bits, a word on 32 or 64). An operand under `2^31` is one signed
/// limb; one over it enters as two 32-bit limbs (the low one unsigned, under `2^32`, the high one signed, at most `(m >> 32) + 1`), and each
/// limb's sum stands alone. One operand on two limbs: `k · 2^32 · b` and `k · ((a >> 32) + 1) · b` under `2^(bits − 1)`; both on two limbs: the
/// low limbs' product reaches `2^64`, so only the wide form stands under 64 bits. Both under `2^31`: `k · a · b` under `2^(bits − 1)`.
pub fn tile_proves(k: u128, a: u128, b: u128, bits: u32) -> bool {
    let top = 1u128 << (bits - 1);
    let small = |m: u128| m < (1u128 << 31);
    let under = |x: Option<u128>| x.is_some_and(|v| v < top);
    let prod = |x: u128, y: u128, z: u128| x.checked_mul(y).and_then(|v| v.checked_mul(z));
    match (small(a), small(b)) {
        (true, true) => under(prod(k, a, b)),
        (false, true) => under(prod(k, 1u128 << 32, b)) && under(prod(k, (a >> 32) + 1, b)),
        (true, false) => under(prod(k, a, 1u128 << 32)) && under(prod(k, a, (b >> 32) + 1)),
        (false, false) => bits > 64 && under(prod(k, 1u128 << 32, 1u128 << 32)) && under(prod(k, (a >> 32) + 1, (b >> 32) + 1)) && under(prod(k, (a >> 32) + 1, 1u128 << 32)),
    }
}

/// [measurement; P57 item 1] The launches a trace keeps: a section's are about 510, so four sections and the run's opening.
pub const TRACE_LAUNCHES: usize = 2600;

/// [agent-inferred, November 1] A declared reading (`Resident::profile`): every launch timed alone,
/// the card synchronized before and after it, by entry; every transfer and allocation timed after the
/// card's stream has drained, so a run's wall time splits into kernels, copies, allocations and the
/// host's own work. It moves nothing the field computes.
#[derive(Clone, Debug, Default)]
pub struct FieldProfile {
    pub kernels: std::collections::BTreeMap<&'static str, (u64, u128)>,
    /// [measurement; theory, November 11] Each entry's blocks × block-threads summed over its launches (a reading of the launches' grids; the mean grid is this over the launches).
    pub threads: std::collections::BTreeMap<&'static str, u128>,
    pub copies: (u64, u128),
    pub allocations: (u64, u128),
    /// [measurement; theory, November 12, P50 step 0] The launches made a head at a time (the contact's return: its rows, its
    /// columns, the skin's return, the spread), by entry and head: launches and ns.
    pub by_head: std::collections::BTreeMap<(&'static str, u32), (u64, u128)>,
    /// The site pairs the forward contact met a head, `Σ_i |S_i^h|` over every row and tick of the runs counted in `FieldTimes::pairs`.
    pub pairs_by_head: Vec<u128>,
    /// Each head's kind as the declaration reads it: `still`, `paced` (a turned ring set that is no depth ring, whose skin reads its
    /// own clock) or `depth`.
    pub head_kinds: Vec<&'static str>,
    /// [measurement; theory, November 13, P56 item 4] Each copy and take by its call site's line in this file (`copy` or `take`): count and ns.
    pub by_site: std::collections::BTreeMap<(&'static str, u32), (u64, u128)>,
    /// [measurement; theory, November 13, P56 item 4] A zeroed take's zeroing by its call site's line: count, ns (timed alone, the stream drained
    /// before and after) and octets zeroed.
    pub zeroed: std::collections::BTreeMap<u32, (u64, u128, u128)>,
    /// [measurement; theory, November 13, P61 item 3] A site's maps by launch kind (entry, rows, cols, only_unresolved, add or accumulate):
    /// launches, ns and products (sites times rows times cols as launched).
    pub maps: std::collections::BTreeMap<MapKind, (u64, u128, u128)>,
    /// [measurement; P61 item 3] Under `FIELD_TRACE`, each kind's operands' magnitudes and its tiles' proofs ([`MapBits`]).
    pub map_bits: std::collections::BTreeMap<MapKind, MapBits>,
    /// [measurement; theory, November 13, P57 item 1] Under `FIELD_TRACE` (with the profile): every launch in order, up to
    /// [`TRACE_LAUNCHES`], with the run it belongs to, the last phase marked, its grid, block, dynamic shared octets, its timed ns
    /// and its head; and each entry's attributes as the driver lowered it, at each block and dynamic shared it was launched with.
    pub trace_on: bool,
    pub trace: Vec<LaunchRecord>,
    /// Each traced run's batches' region lengths in sites.
    pub trace_regions: Vec<(u64, Vec<usize>)>,
    pub attributes: std::collections::BTreeMap<(&'static str, u32, u32), EntryAttributes>,
    /// [measurement; theory, November 13, P58 item 1] The pool by a take's call site's line and its size class in octets: hits, misses (an
    /// allocation), the kept buffers a miss freed and their octets.
    /// [realization; P58 item 1] and the plain takes served by a larger kept buffer in place of an allocation.
    pub pool: std::collections::BTreeMap<(u32, u64), [u64; 5]>,
    /// [measurement; theory, November 13, G142] At each take that allocated, by its line and class: the takes, and the live, kept and over-budget
    /// octets summed at that take (live and kept before it; over budget the octets by which live, kept and the new buffer passed the batch's
    /// budget). Each kept buffer the budget freed, by its octets. The largest live set the batch's takes reached, and the budget.
    pub pool_pressure: std::collections::BTreeMap<(u32, u64), [u128; 4]>,
    pub pool_freed: std::collections::BTreeMap<u64, u64>,
    pub pool_peak: (u64, u64),
    /// [measurement; G143] The phase (the last mark) of the live set's peak and the live octets by take line there; and each phase's largest live set.
    pub peak_phase: &'static str,
    pub peak_by_line: Vec<(u32, u64)>,
    pub phase_peak: std::collections::BTreeMap<&'static str, u64>,
    /// [measurement; theory, November 13, P56 item 4] Every timed launch, copy, take and zeroing summed (ns): what a phase's wall holds of the card's.
    pub timed_ns: u128,
}

/// [measurement; theory, November 12, P50 step 0b] The card's yardsticks ([`Resident::yardsticks`]): each reading as (rate a
/// second, count, seconds).
#[derive(Clone, Debug)]
pub struct Yardsticks {
    pub multiprocessors: u32,
    pub product_blocks: u32,
    pub stream_blocks: u32,
    /// Narrow products, one thread a cell (site, output) of a 64 by 64 map.
    pub cell: (f64, u64, f64),
    /// Narrow products, one thread a tile of four outputs by four sites.
    pub tile: (f64, u64, f64),
    pub store_octets: u64,
    pub read: (f64, u64, f64),
    pub write: (f64, u64, f64),
    pub gather_rows: u32,
    pub gather_entries: u32,
    /// Eight words (32 octets) a gather at a random entry of a random row.
    pub gather: (f64, u64, f64),
}

impl<'c> Resident<'c> {

    pub fn times(&self) -> FieldTimes {
        self.times
    }

    /// Time every launch, transfer and allocation from here on ([`FieldProfile`]).
    pub fn profile(&mut self) {
        self.profile = Some(std::cell::RefCell::new(FieldProfile { trace_on: std::env::var_os("FIELD_TRACE").is_some(), ..Default::default() }));
    }

    /// Time the host between the marks of a batch (`mark`), without synchronizing: where the wall time of a
    /// pass goes between the host's work and its waits on the card.
    pub fn trace_phases(&mut self) {
        self.phases = Some(std::cell::RefCell::new((Instant::now(), Default::default())));
    }

    /// The phases read so far, when traced: name, marks and wall ns.
    pub fn phased(&self) -> Option<Vec<(&'static str, u64, u128)>> {
        self.phases.as_ref().map(|p| p.borrow().1.iter().map(|(k, v)| (*k, v.0, v.1)).collect())
    }

    pub(crate) fn mark(&self, name: &'static str) {
        self.last_mark.set(name);
        if let Some(p) = &self.phases {
            let mut p = p.borrow_mut();
            let ns = p.0.elapsed().as_nanos();
            p.0 = Instant::now();
            let slot = p.1.entry(name).or_insert((0, 0));
            slot.0 += 1;
            slot.1 += ns;
            if let Some(profile) = &self.profile {
                let total = profile.borrow().timed_ns;
                let mut c = self.phase_card.borrow_mut();
                let delta = total.saturating_sub(c.0);
                c.0 = total;
                *c.1.entry(name).or_insert(0) += delta;
            }
        }
    }

    /// [measurement; theory, November 13, P56 item 4] Each phase's timed card ns, when traced and profiled.
    pub fn phase_card(&self) -> Vec<(&'static str, u128)> {
        self.phase_card.borrow().1.iter().map(|(k, v)| (*k, *v)).collect()
    }

    /// The profile read so far, when profiled.
    pub fn profiled(&self) -> Option<FieldProfile> {
        self.profile.as_ref().map(|p| p.borrow().clone())
    }

    /// [measurement; theory, November 12, P50 step 0b] **The card's yardsticks** (`kernels/field.cu`, `field_yard_*`): narrow
    /// products a second from a site's map held in shared memory (one thread a cell, and one thread a tile of four outputs by
    /// four sites), and octets a second on a store of 2^28 words of 32 bits read in order, written in order, and gathered eight
    /// words at a random entry of a random row of `entries` entries. Each reading is timed alone, after a calibrating launch,
    /// to at least `seconds` of the card's time. No law and no state: the field's buffers are not touched.
    pub fn yardsticks(&self, entries: u32, seconds: f64) -> std::result::Result<Yardsticks, CardError> {
        let card = self.card;
        card.current()?;
        let sms = card.census().multiprocessors.max(1);
        let timed = |entry: &'static str, grid: u32, params: &mut [*mut c_void], launches: u32| -> std::result::Result<f64, CardError> {
            let function = self.module.function(entry)?;
            card.synchronize()?;
            let started = Instant::now();
            for _ in 0..launches {
                function.launch_on_shared(card.stream(), Dim3::x(grid), Dim3 { x: 256, y: 1, z: 1 }, 0, params)?;
            }
            card.synchronize()?;
            Ok(started.elapsed().as_secs_f64())
        };
        // A calibrating run at `trial`, then the count that takes `seconds` at its rate (at least the trial's).
        let scaled = |trial: u32, took: f64| -> u32 { ((f64::from(trial) * seconds / took.max(1e-9)).ceil() as u64).clamp(u64::from(trial), u64::from(u32::MAX)) as u32 };
        let n = 64u64;
        let table: Vec<u32> = (0..n * n).map(|c| (c as u32).wrapping_mul(0x9E37_79B9) ^ 0x7F4A_7C15).collect();
        let (table, input) = (card.upload(&table)?, card.upload(&table.iter().rev().copied().collect::<Vec<u32>>())?);
        let blocks = sms * 64;
        let out = card.alloc::<u64>(blocks as usize * 256)?;
        let (mut tp, mut ip, mut op) = (table.device_ptr(), input.device_ptr(), out.device_ptr());
        let mut products = |entry: &'static str, per_pass: u64| -> std::result::Result<(f64, u64, f64), CardError> {
            let mut passes = 64u32;
            let took = timed(entry, blocks, &mut [arg(&mut tp), arg(&mut ip), arg(&mut op), arg(&mut passes)], 1)?;
            let mut passes = scaled(passes, took);
            let took = timed(entry, blocks, &mut [arg(&mut tp), arg(&mut ip), arg(&mut op), arg(&mut passes)], 1)?;
            let count = u64::from(blocks) * per_pass * u64::from(passes);
            Ok((count as f64 / took, count, took))
        };
        let cell = products("field_yard_products_cell", 256 * n)?;
        let tile = products("field_yard_products_tile", 256 * n * 16)?;
        // The store: 2^28 words, every word written before it is read.
        let words = 1usize << 28;
        let store = card.alloc::<u32>(words)?;
        let (mut sp, mut quads, mut seed) = (store.device_ptr(), (words / 4) as u64, 0x5EED_u32);
        let stride_blocks = sms * 32;
        let sums = card.alloc::<u64>(stride_blocks as usize * 256)?;
        let mut sum_p = sums.device_ptr();
        let octets = (words * 4) as u64;
        let streamed = |entry: &'static str, params: &mut [*mut c_void]| -> std::result::Result<(f64, u64, f64), CardError> {
            let took = timed(entry, stride_blocks, params, 4)?;
            let launches = scaled(4, took);
            let took = timed(entry, stride_blocks, params, launches)?;
            let moved = octets * u64::from(launches);
            Ok((moved as f64 / took, moved, took))
        };
        let write = streamed("field_yard_write", &mut [arg(&mut sp), arg(&mut quads), arg(&mut seed)])?;
        let read = streamed("field_yard_read", &mut [arg(&mut sp), arg(&mut quads), arg(&mut sum_p)])?;
        let entries = entries.max(1);
        let mut rows = (words as u64 / (u64::from(entries) * 8)) as u32;
        let mut entries_a = entries;
        let mut gathers = 64u32;
        let took = timed("field_yard_gather", stride_blocks, &mut [arg(&mut sp), arg(&mut rows), arg(&mut entries_a), arg(&mut gathers), arg(&mut seed), arg(&mut sum_p)], 1)?;
        let mut gathers = scaled(gathers, took);
        let took = timed("field_yard_gather", stride_blocks, &mut [arg(&mut sp), arg(&mut rows), arg(&mut entries_a), arg(&mut gathers), arg(&mut seed), arg(&mut sum_p)], 1)?;
        let moved = u64::from(stride_blocks) * 256 * u64::from(gathers) * 32;
        let gather = (moved as f64 / took, moved, took);
        Ok(Yardsticks { multiprocessors: sms, product_blocks: blocks, stream_blocks: stride_blocks, cell, tile, store_octets: octets, read, write, gather_rows: rows, gather_entries: entries, gather })
    }

    /// A transfer or an allocation, timed after the stream drains when profiled.
    #[track_caller]
    pub(crate) fn timed<T>(&self, kind: Kind, f: impl FnOnce() -> T) -> T {
        let Some(profile) = &self.profile else { return f() };
        let line = std::panic::Location::caller().line();
        let _ = self.card.synchronize();
        let started = Instant::now();
        let out = f();
        let ns = started.elapsed().as_nanos();
        let mut p = profile.borrow_mut();
        let (slot, name) = match kind {
            Kind::Copy => (&mut p.copies, "copy"),
            Kind::Alloc => (&mut p.allocations, "take"),
        };
        slot.0 += 1;
        slot.1 += ns;
        let site = p.by_site.entry((name, line)).or_insert((0, 0));
        site.0 += 1;
        site.1 += ns;
        p.timed_ns += ns;
        out
    }

    /// [measurement; theory, November 13, P61 item 3] **A site's map's launch read by kind**, under the profile: its launches, ns (the launch just
    /// made) and products (`words.t · rows · cols`). Under `FIELD_TRACE` its operands are read by the bits ruler (`field_yard_rows_max`, each site's
    /// largest word a row), and its tiles of [`MAP_TILE`] sites judged by [`tile_proves`]: `k` terms a sum, the weight's largest `wmax` (read from
    /// the material where not given) against the one operand (a forward or transposed map), or the covector against the input (an outer sum, `k`
    /// the tile's sites). A reading: nothing the field computes moves.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn map_record(&self, kind: MapKind, words: &Words, k: Option<usize>, wmax: Option<u64>, weight: Option<(u64, usize)>, operands: &[(u64, bool, usize, usize)]) -> Result<()> {
        let Some(profile) = &self.profile else { return Ok(()) };
        let products = u128::from(words.t) * u128::from(kind.1) * u128::from(kind.2.max(1));
        let trace = {
            let mut p = profile.borrow_mut();
            let slot = p.maps.entry(kind).or_insert((0, 0, 0));
            (slot.0, slot.1, slot.2) = (slot.0 + 1, slot.1 + self.last_ns.get(), slot.2 + products);
            p.trace_on
        };
        if !trace || words.t == 0 {
            return Ok(());
        }
        let card = self.card;
        let sites = words.t as usize;
        let rows_max = |ptr: u64, x64: bool, n: usize, stride: usize, width: usize| -> Result<Vec<u64>> {
            let out = self.timed(Kind::Alloc, || self.take::<u64>(n)).map_err(device)?;
            let (mut a, mut kind64, mut nn, mut st, mut wd, mut o) = (ptr, if x64 { 64u32 } else { 32u32 }, n as u64, stride as u64, width as u32, out.device_ptr());
            self.launch("field_yard_rows_max", Self::cells(n as u64), THREADS, &mut [arg(&mut a), arg(&mut kind64), arg(&mut nn), arg(&mut st), arg(&mut wd), arg(&mut o)])?;
            Ok(self.timed(Kind::Copy, || card.fetch_range(&out, 0, n)).map_err(device)?)
        };
        let wmax = match (wmax, weight) {
            (Some(w), _) => u128::from(w),
            (None, Some((offset, len))) => u128::from(rows_max(words.theta + 4 * offset, false, 1, len, len)?[0]),
            (None, None) => 1,
        };
        let maxima: Vec<Vec<u64>> = operands.iter().map(|&(ptr, x64, stride, width)| rows_max(ptr, x64, sites, stride, width)).collect::<Result<_>>()?;
        let bits = |m: u64| 64 - m.leading_zeros();
        let mut p = profile.borrow_mut();
        let b = p.map_bits.entry(kind).or_default();
        b.launches += 1;
        b.w_bits = b.w_bits.max(bits(wmax as u64));
        b.sites += sites as u64;
        for (j, m) in maxima.iter().enumerate().take(2) {
            b.bits[j] = b.bits[j].max(m.iter().copied().map(bits).max().unwrap_or(0));
            b.under31[j] += m.iter().filter(|&&v| v < 1 << 31).count() as u64;
        }
        let (mut all64, mut all96) = (true, true);
        for start in (0..sites).step_by(MAP_TILE) {
            let end = (start + MAP_TILE).min(sites);
            let tile = |j: usize| -> u128 { maxima.get(j).map_or(1, |m| u128::from(m[start..end].iter().copied().max().unwrap_or(0))) };
            let (kk, a, c) = match k {
                Some(terms) => (terms as u128, tile(0), wmax),
                None => ((end - start) as u128, tile(0), tile(1)),
            };
            let (p64, p96) = (tile_proves(kk, a, c, 64), tile_proves(kk, a, c, 96));
            b.tiles += 1;
            b.proved64 += u64::from(p64);
            b.proved96 += u64::from(p96);
            all64 &= p64;
            all96 &= p96;
        }
        b.launches_all64 += u64::from(all64);
        b.launches_all96 += u64::from(all96);
        Ok(())
    }

    /// [measurement; theory, November 12, P50 step 3] The turn's series against the wide one on the card (`field_series_check`): for each argument
    /// `b`, the narrow series' face and `exp_series_dev(0, b)`'s, `[narrow re, narrow im, wide re, wide im]`.
    pub fn series_check(&self, bs: &[i64]) -> Result<Vec<i64>> {
        let card = self.card;
        let up = self.timed(Kind::Copy, || self.take_up(bs)).map_err(device)?;
        let out = self.timed(Kind::Alloc, || self.take::<i64>((4 * bs.len()).max(1))).map_err(device)?;
        let (mut bp, mut count, mut op) = (up.device_ptr(), bs.len() as u64, out.device_ptr());
        self.launch("field_series_check", Self::cells(bs.len() as u64), THREADS, &mut [arg(&mut bp), arg(&mut count), arg(&mut op)])?;
        card.fetch_range(&out, 0, 4 * bs.len()).map_err(device)
    }

    /// [measurement; theory, November 12, P54 item 1] The ruler build's histogram slot of one array at one clock.
    #[cfg(feature = "ruler-bits")]
    pub(crate) fn bits_slot(&self, array: usize, tick: usize) -> Result<u64> {
        let mut b = self.bits.borrow_mut();
        if b.is_none() {
            *b = Some(self.card.zeroed::<u64>(BITS_NAMES.len() * BITS_TICKS * BITS_BINS).map_err(device)?);
        }
        Ok(b.as_ref().map_or(0, |b| b.device_ptr()) + (((array * BITS_TICKS + tick.min(BITS_TICKS - 1)) * BITS_BINS) * 8) as u64)
    }

    #[cfg(feature = "ruler-bits")]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn bits_pairs(&self, words: &mut Words, h: usize, kind: u32, mode: u32, arr: u64, array: usize, tick: usize, sites: usize) -> Result<()> {
        let mut slot = self.bits_slot(array, tick)?;
        let (mut hh, mut kd, mut md, mut ap) = (h as u32, kind, mode, arr);
        self.launch("field_yard_bits_pairs", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut kd), arg(&mut md), arg(&mut ap), arg(&mut slot)])
    }

    #[cfg(feature = "ruler-bits")]
    pub(crate) fn bits_words(&self, arr: u64, kind: u32, count: usize, array: usize, tick: usize) -> Result<()> {
        let mut slot = self.bits_slot(array, tick)?;
        let (mut ap, mut kd, mut n) = (arr, kind, count as u64);
        self.launch("field_yard_bits_words", Self::cells(count as u64), THREADS, &mut [arg(&mut ap), arg(&mut kd), arg(&mut n), arg(&mut slot)])
    }

    /// [measurement; theory, November 12, P54 item 1] The ruler build's histograms: `[array][tick][bits]`, the arrays in `BITS_NAMES`' order.
    #[cfg(feature = "ruler-bits")]
    pub fn bits_histograms(&self) -> Option<Vec<u64>> {
        self.bits.borrow().as_ref().and_then(|b| self.card.fetch(b).ok())
    }
}
