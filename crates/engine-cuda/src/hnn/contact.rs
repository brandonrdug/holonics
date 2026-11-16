//! The card realization's contact (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).

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
use holonics_engine::contact::WEIGHT_BITS;
#[allow(unused_imports)]
use crate::cuda::{Dim3, Module};
#[allow(unused_imports)]
use crate::hnn::card::{Card, CardBuffer, CardError};

/// The dynamic shared memory a tiled affine map may take in a block, the default 48 KiB.
pub(crate) const AFFINE_SHARED: usize = 48 * 1024;

/// [agent-inferred, November 12; the triad record §4] The return of two blocks' tiling (`affine_two_tiled` in `kernels/field.cu`): a block passes
/// `256/rows` sites, holding `W` at the stride `cols + 1`, `W₂` at the stride `cols₂ + 1` and the bias in 32-bit words, each site's joint carrier bound
/// on 128 bits, then a pass's site rows of both blocks on 64 bits, where they fit a block's shared memory (the main line's `D = 64`, `f = 128`,
/// `J = 16`: 46,912 of 49,152 octets).
pub(crate) fn affine_two_tiling(rows: usize, cols: usize, cols2: usize) -> Option<(usize, usize)> {
    let per = (THREADS as usize).checked_div(rows).filter(|&p| p > 0)?;
    let shared = ((rows * (cols + 1) + rows * (cols2 + 1) + rows) * 4).div_ceil(16) * 16 + per * 16 + per * (cols + cols2) * 8;
    (shared <= AFFINE_SHARED).then_some((per, shared))
}

/// The widest span the contact's lanes carry (a lane an entry of the span).
pub(crate) const CONTACT_SPAN: u32 = 32;

/// The series row's carrier, in limbs of 64 bits: at least three (a face, a wide value and its sign, which the
/// declaration's bound less the host's multiplier always passes), at most twenty (`field_contact_l3` …
/// `field_contact_l20`, 1,280 bits).
pub(crate) const MIN_LIMBS: usize = 3;

pub(crate) const MAX_LIMBS: usize = 20;

/// The most modes a head's rows carry on the card (`MAXN` in `kernels/field.cu`).
pub(crate) const MAX_MODES: usize = 16;

/// Warps a contact or a reverse block carries (`CONTACT_ROWS`, `REV_ROWS` in `kernels/field.cu`).
pub(crate) const CONTACT_ROWS: u64 = 4;

pub(crate) const REV_ROWS: u64 = 4;

/// The most crowds a receiver hears, one lane each (`MAX_CROWD_SLOTS` in `kernels/field.cu`).
pub(crate) const MAX_CROWD_SLOTS: usize = 32;

/// The sites a thread of an encoding's covector segment takes (the segments' tile).
pub(crate) const OUTER_TILE: u64 = 64;

/// [realization; P61 item 4e; G191] The sites an outer sum's block walks (`OUTER_WALK` in `kernels/field.cu`, whose comment gives the reading).
pub(crate) const OUTER_WALK: u64 = 64;

/// [realization; P61 item 4f] The outer passes' slots for their largest words, zeroed again each time they are spent.
pub(crate) const OUTER_SLOTS: usize = 4096;

/// [definition; agent-inferred, November 1] **The crowds a receiver of a region of `sites` hears**
/// (the dispersing field's §14.10, the host's `crowd_ranges`): two an octave `level ≥ 2` with
/// `2^level < sites`, one on each side.
pub fn crowd_slots(sites: usize) -> usize {
    (2..usize::BITS).take_while(|&level| (1usize << level) < sites).count() * 2
}

/// [definition; agent-inferred, November 1] **The limbs a launch's rows need** (§14.11, §15.2: width is
/// dynamic, never arbitrary): a row's carrier is as wide as the exponents its rows hold, `62` bits of face,
/// `⌈log₂ reach⌉` of a crowd's count, the spread of whole bits `a − a₀` the widest
/// row of the launch holds, the bits of the terms a row sums, `64 + ⌈log₂ reach⌉` of a value summed over the
/// reach and the sign: [`Constitution::row_bits`] (its gain read from the largest temperature's octave the material
/// holds, [`Constitution::row_gain`], §15.10, §16.12) with its spread bound (`4n 2^c + 1 + ⌊log₂ reach⌋ + 2`) replaced by
/// the spread read. A spread
/// past that bound is refused (the bound is where a row ends), and so is a carrier past the twenty limbs the
/// card keeps.
///
/// [realization; agent-inferred, November 15] The host's row weighs a source by `2^62` ([`WEIGHT_BITS`]) and the card
/// by one, which leaves every quotient of the row the same (`kernels/field.cu`, beside `CONTACT_MIN_BLOCKS`), so the card's
/// carrier is the host's need less those bits, every term's total still within it. The refusals stay the host's: a
/// spread past the bound, or a host need past the twenty limbs, so the card refuses exactly where the host does.
pub fn row_limbs(field: &Constitution, spread: u64) -> Result<usize> {
    let d = &field.declaration;
    let bound = field.row_gain()? + (usize::BITS - 1 - d.reach.leading_zeros()) as u64 + 2;
    if spread > bound {
        return Err(TowerError::Refused("a contact row holds exponents past the declaration's bound (`row_bits`)"));
    }
    let need = field.row_bits()? as u64 - bound + spread;
    if need.div_ceil(64) as usize > MAX_LIMBS {
        return Err(TowerError::Refused("a contact row needs a carrier past the card's twenty limbs (1,280 bits)"));
    }
    Ok(((need - WEIGHT_BITS as u64).div_ceil(64) as usize).max(MIN_LIMBS))
}

pub(crate) struct Tick<'c> {
    pub(crate) read: Pooled<'c, i32>,
    pub(crate) scale: Pooled<'c, i128>,
    /// The word and the value, `[t][2·2M]`.
    pub(crate) qkv: Pooled<'c, i64>,
    pub(crate) qf: Pooled<'c, i64>,
    /// The unit words on 32 bits `[h][t][span]` (`field_unit` writes them beside `qf`).
    pub(crate) qf32: Pooled<'c, i32>,
    /// Every receiver's probe framed and at unit power by head (`[h][t][span]`, and on 32 bits) with its powers
    /// `[h][t]` (§16.19).
    pub(crate) pq: Pooled<'c, i64>,
    pub(crate) pq32: Pooled<'c, i32>,
    pub(crate) pscale: Pooled<'c, i128>,
    pub(crate) vf: Pooled<'c, i64>,
    /// The framed word's powers `[h][t]`, the ratios `field_unit` reads it as.
    pub(crate) qscale: Pooled<'c, i128>,
    /// The resonance classes `[h][t]`, each region's class offsets `[h][r][2·3^b + 1]` and members
    /// `[h][t]` (`field_classes`).
    pub(crate) cls: Pooled<'c, u32>,
    pub(crate) class_off: Pooled<'c, u32>,
    pub(crate) members: Pooled<'c, u32>,
    /// Each receiver's probed classes: their number `[h][t]`, the classes `[h][t][2^b − 1]`, and the
    /// receivers that probe each class, offsets `[h][r][3^b + 1]` and members `[h][t][2^b − 1]`.
    pub(crate) pn: Pooled<'c, u32>,
    pub(crate) pcls: Pooled<'c, u32>,
    pub(crate) poff: Pooled<'c, u32>,
    pub(crate) pmem: Pooled<'c, u32>,
    pub(crate) e: Pooled<'c, u64>,
    /// The pairs' locks at unit gain `S` (the temperatures' covector, §15.10), kept on a return.
    pub(crate) sb: Pooled<'c, i64>,
    /// The row's least whole bit `[h][t]` (`field_exposure`), each head's prefix sums of the definite
    /// sites' unit words and values `[h][row][span]` and their counts `[h][row]`, and each receiver's
    /// crowd shares `[h][t][slots]` (`row = site + region`, a region's `S + 1` rows).
    pub(crate) amin: Pooled<'c, i64>,
    pub(crate) sw: Pooled<'c, i128>,
    pub(crate) sv: Pooled<'c, i128>,
    pub(crate) sc: Pooled<'c, u64>,
    pub(crate) ce: Pooled<'c, u64>,
    pub(crate) y: Pooled<'c, i64>,
    pub(crate) read2: Pooled<'c, i32>,
    pub(crate) scale2: Pooled<'c, i128>,
    pub(crate) pa: Pooled<'c, i64>,
    /// [theory, November 11 17:25 and November 12 (G98)] The carry circles' charts' reads `q`, `ℓ` `[t][2C]`, their gate `γ` `[t][2C]`, the scan's operand
    /// `[t][2C]` and the coupled drive `κ b` `[t][2C]` (one slot each without them).
    pub(crate) pg: Pooled<'c, i64>,
    pub(crate) pgam: Pooled<'c, i64>,
    pub(crate) pqm: Pooled<'c, i64>,
    pub(crate) pkb: Pooled<'c, i64>,
    pub(crate) pb: Pooled<'c, i64>,
    pub(crate) pc: Pooled<'c, i64>,
    /// [theory, November 12; the triad record §3 and §4] The triads' chart read `abg` `[t][6J]`, their products `p` `[t][2J]` and `c^T` `[t][2J]`, kept
    /// for the reverse; none where the field has no triads, so a field without them takes nothing more.
    pub(crate) pabg: Option<Pooled<'c, i64>>,
    pub(crate) ptp: Option<Pooled<'c, i64>>,
    pub(crate) pct: Option<Pooled<'c, i64>>,
    /// The tick's carrier width: the binary length of its largest unit word.
    pub(crate) bits: Pooled<'c, u32>,
}

impl<'c> Resident<'c> {

    pub(crate) fn tick(&self, sites: usize, pairs: usize, regions: usize, field: &Constitution, stored: bool, returning: bool, dense: bool) -> Result<Tick<'c>> {
        let d = field.declaration;
        let rows = sites + regions;
        let slots = crowd_slots(d.reach);
        let (dw, m2, f, heads, span, lanes) = (d.width, 2 * d.complex(), d.contacts, d.heads, 2 * d.modes, d.lanes);
        let classes = d.classes();
        // A receiver's probed classes: its probe's own and the `2^b − 1` across its seams (§16.19).
        let probe_stride = 1usize << d.class_trits();
        let card = self.card;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let alloc32 = |len: usize| self.timed(Kind::Alloc, || self.take::<u32>(len.max(1))).map_err(device);
        // [theory, November 12; the triad record §4] A triads' carrier `[t][rows J]`, none where the field has no triads.
        let triads = d.triads;
        let triad = |rows: usize| if triads > 0 { alloc64(sites * rows * triads).map(Some) } else { Ok(None) };
        Ok(Tick {
            read: self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?,
            scale: self.timed(Kind::Alloc, || self.take::<i128>((sites * lanes).max(1))).map_err(device)?,
            qkv: alloc64(sites * 2 * m2)?,
            qf: alloc64(heads * sites * span)?,
            qf32: self.take::<i32>(heads * sites * span).map_err(device)?,
            pq: alloc64(heads * sites * span)?,
            pq32: self.take::<i32>(heads * sites * span).map_err(device)?,
            pscale: self.take::<i128>((heads * sites).max(1)).map_err(device)?,
            vf: alloc64(heads * sites * span)?,
            qscale: self.timed(Kind::Alloc, || self.take::<i128>((heads * sites).max(1))).map_err(device)?,
            cls: alloc32(heads * sites)?,
            class_off: alloc32(heads * regions * (2 * classes + 1))?,
            members: alloc32(heads * sites)?,
            pn: alloc32(heads * sites)?,
            pcls: alloc32(heads * sites * probe_stride)?,
            poff: alloc32(heads * regions * (classes + 1))?,
            pmem: alloc32(heads * sites * probe_stride)?,
            // The shares are zeroed where the echo reads another tick's (a pair absent from a row reads zero).
            // The pairs' scores, then their shares, a word a pair; zeroed where the echo reads another tick's (a
            // pair absent from a row reads zero), else only the support's entries are ever written and read.
            sb: self.take::<i64>(if returning { (heads * pairs).max(1) } else { 1 }).map_err(device)?,
            // [theory, November 13, P56 step 6] Taken without its zeroing where no dense reader runs (`dense`, at the call): every other word read is
            // written first in the same tick. The exposure (`field_exposure`) writes the score at every support entry `[i][j]` of every computed row of
            // every head; the contact (`contact_body`) reads it there and writes the share there; the rows, the skin's return and the rulers read only
            // those entries of computed rows, and the columns read them at the pairs whose covector `ds` they read beside, which is an unzeroed take
            // the rows write only at support entries. No reader meets an entry outside a computed row's support.
            e: if stored && dense { self.timed(Kind::Alloc, || self.take_zeroed::<u64>((heads * pairs).max(1))).map_err(device)? } else { self.timed(Kind::Alloc, || self.take::<u64>((heads * pairs).max(1))).map_err(device)? },
            amin: alloc64(heads * sites)?,
            sw: self.timed(Kind::Alloc, || self.take::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sv: self.timed(Kind::Alloc, || self.take::<i128>((heads * rows * span).max(1))).map_err(device)?,
            sc: self.timed(Kind::Alloc, || self.take::<u64>((heads * rows).max(1))).map_err(device)?,
            ce: self.timed(Kind::Alloc, || self.take::<u64>(if stored { (heads * sites * slots).max(1) } else { 1 })).map_err(device)?,
            y: alloc64(sites * m2)?,
            read2: self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?,
            scale2: self.timed(Kind::Alloc, || self.take::<i128>((sites * lanes).max(1))).map_err(device)?,
            pa: alloc64(sites * f)?,
            pg: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pgam: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pqm: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pkb: alloc64(if field.declaration.carry > 0 { sites * 2 * field.declaration.carry } else { 1 })?,
            pb: alloc64(sites * f)?,
            pc: alloc64(sites * f)?,
            pabg: triad(6)?,
            ptp: triad(2)?,
            pct: triad(2)?,
            bits: self.timed(Kind::Alloc, || self.take_zeroed::<u32>(4)).map_err(device)?,
        })
    }

    /// One tick of the constitution on the card over the staged sites of `words` (the host's `Constitution::tick`), its temporaries in
    /// `ticks[k]` (or the one shared tick where none is kept).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn tick_forward(&self, field: &Constitution, words: &mut Words, ticks: &[Tick<'c>], k: usize, kept: bool, stored: bool, keep_last: bool, logits: bool, returning: bool, pr: u64, sites: usize, pairs: usize, regions: usize) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m2, f, n, heads) = (d.width, 2 * d.complex(), d.contacts, d.modes, d.heads);
        let span = 2 * n;
        let buckets = 4 * 3 * d.classes() as u32;
        let tick = &ticks[if kept { k } else { 0 }];
        set_tick(words, tick, returning);
        self.chart(words, words.x, &tick.read, &tick.scale, false)?;
        for (part, weight, bias, wmax) in [(0usize, words.q, words.q_bias, words.rq), (1, words.v, words.v_bias, words.rv)] {
            let out = tick.qkv.device_ptr() + (part * m2 * 8) as u64;
            self.affine("field_affine_x32", words, weight, bias, wmax, m2, dw, tick.read.device_ptr(), dw, out, 2 * m2, 0, false)?;
        }
        // A value is linear in its site's moment (§15.1).
        self.launch("field_moment_add", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words)])?;
        card.zero_octets(&tick.bits, 0, 16).map_err(device)?;
        // Every receiver's probe (§16.19), before the classes: a receiver's probed classes are its probe's.
        self.affine("field_affine_x32", words, words.probe, words.probe_bias, words.rprobe, m2, dw, tick.read.device_ptr(), dw, pr, m2, 0, false)?;
        // Its probe reads its moment, as its value does (§16.20).
        let mut prp = pr;
        self.launch("field_moment_add_probe", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut prp)])?;
        self.launch_shared("field_classes", (heads * regions).clamp(1, 1 << 20) as u32, 32, buckets, &mut [arg(words)])?;
        self.launch("field_frame", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
        let mut qs = tick.qscale.device_ptr();
        self.launch("field_unit", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs)])?;
        self.launch("field_frame_probe", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words)])?;
        let mut ps = tick.pscale.device_ptr();
        self.launch("field_unit_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps)])?;
        // The definite sites' prefix sums (§14.10), read by the contact's crowds.
        self.launch("field_sums", ((heads * regions) as u64).clamp(1, 65_535) as u32, SUMS_THREADS, &mut [arg(words)])?;
        // The clock's skins, formed once for the exposure and the contact (the return forms them again for this tick's clock).
        self.skin_fill(field, words, sites)?;
        #[cfg(feature = "ruler-bits")]
        {
            let rows1 = sites + regions;
            for (arr, kind, count, at) in [(words.vf, 0, heads * sites * span, 13), (words.qf, 0, heads * sites * span, 14), (words.pq, 0, heads * sites * span, 15), (words.qf32, 1, heads * sites * span, 16), (words.pq32, 1, heads * sites * span, 17), (words.sc, 3, heads * rows1, 19), (words.sw, 2, heads * rows1 * span, 20), (words.sv, 2, heads * rows1 * span, 21)] {
                self.bits_words(arr, kind, count, at, k)?;
            }
            if words.skin != 0 {
                for h in (0..heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
                    for l in 0..n {
                        self.bits_pairs(words, h, 4, l as u32, words.skin, 5 + l, k, sites)?;
                    }
                }
            }
        }
        let mut store = u32::from(stored);
        if keep_last && k + 1 == d.ticks {
            // The last tick's rows are read whole: the entries outside its support read zero.
            card.zero_octets(&tick.e, 0, 8 * heads * pairs).map_err(device)?;
        }
        // [definition; agent-inferred, November 1] **The series row's carrier is as wide as the exponents
        // its rows hold** (§14.11, §15.2: width is dynamic, never arbitrary): the exposure reads each row's
        // least whole bit and the widest spread any row of the launch holds, and the contact is launched
        // with the limbs that spread needs, never past the declaration's bound (`row_bits`), where a row
        // is refused.
        let rows_per_block = CONTACT_ROWS;
        self.mark("tick_launch_pre");
        self.launch("field_exposure", Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words)])?;
        #[cfg(feature = "ruler-bits")]
        for h in 0..heads {
            // The score is a signed word (`scored`), read as one; the share after the contact is a 63-bit fraction, read unsigned.
            self.bits_pairs(words, h, 1, 0, words.e, 0, k, sites)?;
            if words.sb != 0 {
                self.bits_pairs(words, h, 1, 0, words.sb, 2, k, sites)?;
            }
        }
        let spread = self.timed(Kind::Copy, || card.fetch(&tick.bits)).map_err(device)?[1] as u64;
        if std::env::var_os("FIELD_SPREAD").is_some() {
            let need = field.row_bits().ok().zip(field.row_gain().ok()).map(|(bits, gain)| bits as i64 - (gain as i64 + (usize::BITS - 1 - d.reach.leading_zeros()) as i64 + 2) + spread as i64);
            eprintln!("FIELD_SPREAD tick={k} sites={sites} spread={spread} need_bits={} bound_limbs={}", need.map_or("-".to_string(), |n| n.to_string()), row_limbs(field, spread).map_or(0, |l| l));
        }
        self.mark("tick_exposure_wait");
        let limbs = row_limbs(field, spread)?;
        let contact: &'static str = ["field_contact_l3", "field_contact_l4", "field_contact_l5", "field_contact_l6", "field_contact_l7", "field_contact_l8", "field_contact_l9", "field_contact_l10", "field_contact_l11", "field_contact_l12", "field_contact_l13", "field_contact_l14", "field_contact_l15", "field_contact_l16", "field_contact_l17", "field_contact_l18", "field_contact_l19", "field_contact_l20"][limbs - MIN_LIMBS];
        self.launch(contact, Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words), arg(&mut store)])?;
        #[cfg(feature = "ruler-bits")]
        if store != 0 {
            for h in 0..heads {
                self.bits_pairs(words, h, 0, 0, words.e, 1, k, sites)?;
                self.bits_pairs(words, h, 5, 0, words.ce, 18, k, sites)?;
                if h < 4 {
                    self.bits_pairs(words, h, 6, (BITS_TICKS * BITS_BINS) as u32, words.e, 22 + 2 * h, k, sites)?;
                }
            }
        }
        // The echo's round trips of this tick against the last (§15.3).
        if logits && k > 0 {
            words.e_prev = ticks[k - 1].e.device_ptr();
            self.launch("field_echo_trips", Self::rows_grid((heads * sites) as u64, rows_per_block), (rows_per_block * 32) as u32, &mut [arg(words)])?;
        }
        self.affine("field_affine_x64", words, words.out, words.out_bias, words.rout, dw, m2, tick.y.device_ptr(), m2, 0, dw, words.x, false)?;
        self.chart(words, words.x, &tick.read2, &tick.scale2, false)?;
        self.affine("field_affine_x32", words, words.wa, words.a_bias, words.ra, f, dw, tick.read2.device_ptr(), dw, tick.pa.device_ptr(), f, 0, false)?;
        self.affine("field_affine_x32", words, words.wb, words.b_bias, words.rb, f, dw, tick.read2.device_ptr(), dw, tick.pb.device_ptr(), f, 0, false)?;
        // The plain contacts, the first `f/2 − C`: one thread a site and contact.
        let (plain, circles) = (d.carry_first(), d.carry);
        if plain > 0 {
            self.launch("field_pair", Self::cells((sites * plain) as u64), THREADS, &mut [arg(words)])?;
        }
        if circles > 0 {
            // [theory, November 11 17:25 and November 12 (G98)] The carry circles: their charts' reads `q`, `ℓ` (one affine with its bias), the gate's
            // two divisions and the drive's coupling through the leak off the chain on the pair's grid (one thread a site and circle, as
            // tower.field-scan-gate-once-a-site moved the root out), then the chain, one thread a (region, circle) in strand order.
            self.affine("field_affine_x32", words, words.wg, words.wgb, words.rg, 2 * circles, dw, tick.read2.device_ptr(), dw, tick.pg.device_ptr(), 2 * circles, 0, false)?;
            self.launch("field_pair_gamma", Self::cells((sites * circles) as u64), THREADS, &mut [arg(words)])?;
            self.launch("field_pair_scan", Self::cells((words.r as usize * circles) as u64), THREADS, &mut [arg(words)])?;
            // [realization; theory, November 16 05:40Z] The circles' faces `p = a Q(t∓1)` off the chain, from the operand the scan kept.
            self.launch("field_pair_scan_face", Self::cells((sites * circles) as u64), THREADS, &mut [arg(words)])?;
        }
        let triads = d.triads;
        if triads > 0 {
            // [definition; theory, November 12; the triad record §3 and §4] The triads, after the carry scan and before the return: their chart's read
            // `abg` (one affine with its bias over the pair chart, at the grains `a` and `b` are read at), then the products `p` and `c^T` a site and
            // triad on the pair's grid (zero at a region's two ends); then the return's two blocks, `W c` and `W_T c^T`, summed whole in one wide sum
            // with the bias before its one release and added into `x`, the joint carrier bound read over both blocks.
            self.affine("field_affine_x32", words, words.wt, words.wtb, words.rt, 6 * triads, dw, tick.read2.device_ptr(), dw, words.pabg, 6 * triads, 0, false)?;
            self.launch("field_triad", Self::cells((sites * triads) as u64), THREADS, &mut [arg(words)])?;
            self.affine_two(words, (words.w, words.w_bias, words.rw, dw, f, tick.pc.device_ptr(), f), (words.wtr, words.rwt, 2 * triads, words.pct, 2 * triads), words.x)?;
        } else {
            self.affine("field_affine_x64", words, words.w, words.w_bias, words.rw, dw, f, tick.pc.device_ptr(), f, 0, dw, words.x, false)?;
        }
        self.mark("tick_launch_post");
        Ok(())
    }

    pub(crate) fn chart(&self, words: &mut Words, x: u64, read: &CardBuffer<'c, i32>, scale: &CardBuffer<'c, i128>, only_unresolved: bool) -> Result<()> {
        let (mut x, mut rp, mut sp, mut u) = (x, read.device_ptr(), scale.device_ptr(), u32::from(only_unresolved));
        self.launch("field_chart", Self::warps(words.t as u64), THREADS, &mut [arg(words), arg(&mut x), arg(&mut rp), arg(&mut sp), arg(&mut u)])
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn affine(&self, entry: &'static str, words: &mut Words, weight: u64, bias: u64, wmax: u64, rows: usize, cols: usize, x: u64, x_stride: usize, out: u64, out_stride: usize, add: u64, only_unresolved: bool) -> Result<()> {
        let (mut weight, mut bias, mut wmax, mut rows32, mut cols32) = (weight, bias, wmax, rows as u32, cols as u32);
        let (mut x, mut xs, mut out, mut os, mut add, mut u) = (x, x_stride as u64, out, out_stride as u64, add, u32::from(only_unresolved));
        // [realization; P61 item 4] Every forward map in the tile form (`map_tile` in `kernels/field.cu`): a block a tile of 64 outputs by 64
        // sites, whatever the map's shape; the cell map and its tiling are retired with it.
        let x64 = entry.ends_with("x64");
        let launched = if x64 { "field_affine_tiled_x64" } else { "field_affine_tiled_x32" };
        let grid = (rows as u64).div_ceil(64).saturating_mul((words.t as u64).div_ceil(64)).clamp(1, 65_535) as u32;
        self.launch(launched, grid, THREADS, &mut [arg(words), arg(&mut weight), arg(&mut bias), arg(&mut wmax), arg(&mut rows32), arg(&mut cols32), arg(&mut x), arg(&mut xs), arg(&mut out), arg(&mut os), arg(&mut add), arg(&mut u)])?;
        self.map_record((launched, rows32, cols32, u != 0, add != 0), words, Some(cols), Some(wmax), None, &[(x, x64, xs as usize, cols)])
    }

    /// [definition; theory, November 12; the triad record §3 and §4] **The return of two blocks** (`field_affine_two_x64`; tiled,
    /// `field_affine_two_tiled_x64`, where both blocks' weights, the bias and a pass's site rows fit a block's shared memory, the same integers either
    /// way): `add[t][o] += release(Σ_i W[o][i] x_t[i] + Σ_j W₂[o][j] x₂_t[j] + bias[o] 2^24, 24)`, both blocks summed whole in one wide sum with the bias
    /// before the one release, the carrier bound read over both blocks together (the sum of each block's bound as [`Self::affine`] reads it) and refused
    /// at `2^126`. The first block is `(weight, bias, wmax, rows, cols, x, x_stride)` (the pair's return `W` over `c`), the second `(weight₂, wmax₂,
    /// cols₂, x₂, x₂_stride)` (the triads' `W_T` over `c^T`, no bias of its own), both on 64-bit faces.
    #[allow(clippy::type_complexity)]
    pub(crate) fn affine_two(&self, words: &mut Words, (weight, bias, wmax, rows, cols, x, x_stride): (u64, u64, u64, usize, usize, u64, usize), (weight2, wmax2, cols2, x2, x2_stride): (u64, u64, usize, u64, usize), add: u64) -> Result<()> {
        let (mut weight, mut bias, mut wmax, mut rows32, mut cols32, mut x, mut xs) = (weight, bias, wmax, rows as u32, cols as u32, x, x_stride as u64);
        let (mut weight2, mut wmax2, mut cols2_32, mut x2, mut x2s) = (weight2, wmax2, cols2 as u32, x2, x2_stride as u64);
        let (mut out, mut os, mut add) = (0u64, rows as u64, add);
        let tiling = affine_two_tiling(rows, cols, cols2);
        if std::env::var_os("FIELD_AFFINE_TRACE").is_some() {
            eprintln!("FIELD_AFFINE_TRACE entry=field_affine_two_x64 rows={rows} cols={cols} cols2={cols2} tiling={tiling:?}");
        }
        if let Some((per, shared)) = tiling {
            let grid = (words.t as u64).div_ceil(per as u64).clamp(1, 65_535) as u32;
            return self.launch_shared("field_affine_two_tiled_x64", grid, THREADS, shared as u32, &mut [arg(words), arg(&mut weight), arg(&mut bias), arg(&mut wmax), arg(&mut rows32), arg(&mut cols32), arg(&mut x), arg(&mut xs), arg(&mut weight2), arg(&mut wmax2), arg(&mut cols2_32), arg(&mut x2), arg(&mut x2s), arg(&mut out), arg(&mut os), arg(&mut add)]);
        }
        let cells = words.t as u64 * rows as u64;
        self.launch("field_affine_two_x64", Self::cells(cells), THREADS, &mut [arg(words), arg(&mut weight), arg(&mut bias), arg(&mut wmax), arg(&mut rows32), arg(&mut cols32), arg(&mut x), arg(&mut xs), arg(&mut weight2), arg(&mut wmax2), arg(&mut cols2_32), arg(&mut x2), arg(&mut x2s), arg(&mut out), arg(&mut os), arg(&mut add)])
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn transposed(&self, words: &mut Words, weight: u64, rows: usize, cols: usize, y: u64, y_stride: usize, out: u64, accumulate: bool, only_unresolved: bool) -> Result<()> {
        let (mut weight, mut rows32, mut cols32, mut y, mut ys, mut out, mut acc, mut u) = (weight, rows as u32, cols as u32, y, y_stride as u64, out, u32::from(accumulate), u32::from(only_unresolved));
        let grid = (cols as u64).div_ceil(64).saturating_mul((words.t as u64).div_ceil(64)).clamp(1, 65_535) as u32;
        self.launch("field_transposed", grid, THREADS, &mut [arg(words), arg(&mut weight), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut out), arg(&mut acc), arg(&mut u)])?;
        self.map_record(("field_transposed", rows32, cols32, u != 0, acc != 0), words, Some(rows), None, Some((weight, rows * cols)), &[(y, true, ys as usize, rows)])
    }

    /// A family's covector `g[at..] += Σ_t y_t ⊗ x_t` (or the bias's `Σ_t y_t` when `x` is zero), with
    /// the host's per-region refusal of its carrier when `x` is given.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn outer(&self, words: &mut Words, g: &CardBuffer<'c, i128>, at: u64, rows: usize, cols: usize, y: u64, y_stride: usize, x: u64, x_stride: usize, x64: bool, only_unresolved: bool) -> Result<()> {
        let (mut gp, mut at, mut rows32, mut cols32, mut y, mut ys, mut x, mut xs, mut u) = (g.device_ptr(), at, rows as u32, cols as u32, y, y_stride as u64, x, x_stride as u64, u32::from(only_unresolved));
        // [realization; P61 items 4e and 4f] The outer sum in the tile form, then (where `x` is given) the host's per-region refusal, which
        // first reads the outer pass's largest words from a slot of its own (`outer_slot`) and reads a region again only where they leave
        // its bound open. Without a slot the bound reads every region as before.
        let mut maxima = if x != 0 { self.outer_slot()? } else { 0 };
        let entry = if x64 { "field_outer_x64" } else { "field_outer_x32" };
        let (grid, mut walk) = self.outer_grid(rows, cols, x != 0, words.t as usize);
        self.launch(entry, grid, THREADS, &mut [arg(words), arg(&mut gp), arg(&mut at), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut x), arg(&mut xs), arg(&mut u), arg(&mut maxima), arg(&mut walk)])?;
        let ops: Vec<(u64, bool, usize, usize)> = if x != 0 { vec![(y, true, ys as usize, rows), (x, x64, xs as usize, cols)] } else { vec![(y, true, ys as usize, rows)] };
        self.map_record((entry, rows32, if x != 0 { cols32 } else { 0 }, u != 0, false), words, None, None, None, &ops)?;
        if x != 0 {
            let bound = if x64 { "field_outer_bound_x64" } else { "field_outer_bound_x32" };
            self.launch(bound, words.r, THREADS, &mut [arg(words), arg(&mut rows32), arg(&mut cols32), arg(&mut y), arg(&mut ys), arg(&mut x), arg(&mut xs), arg(&mut u), arg(&mut maxima)])?;
            self.map_record((bound, rows32, cols32, u != 0, false), words, None, None, None, &[])?;
        }
        Ok(())
    }

    /// [realization; November 15, the maps' second loop] The outer sum's grid and walk: a block a tile of 64 by 64 entries and a walk of
    /// sites, the walk the sites that give the tiles one wave of two blocks a multiprocessor (the kernel's launch bounds), a multiple of 32
    /// (`MAP_KC`) from 64 to 512 (`field_outer_x32`'s comment gives the bench's reading); with no `x`, the bias's entries by `THREADS` and a
    /// walk of `OUTER_WALK`. The walk changes no bit: the partials go in by an integer sum.
    pub(crate) fn outer_grid(&self, rows: usize, cols: usize, has_x: bool, sites: usize) -> (u32, u32) {
        if has_x {
            let tiles = (rows as u64).div_ceil(64).saturating_mul((cols as u64).div_ceil(64)).max(1);
            let wave = 2 * u64::from(self.card.census().multiprocessors.max(1));
            let walk = ((sites as u64).saturating_mul(tiles).div_ceil(wave)).div_ceil(32).saturating_mul(32).clamp(OUTER_WALK, 512);
            (tiles.saturating_mul((sites as u64).div_ceil(walk)).clamp(1, 65_535) as u32, walk as u32)
        } else {
            ((rows as u64).div_ceil(THREADS as u64).saturating_mul((sites as u64).div_ceil(OUTER_WALK)).clamp(1, 65_535) as u32, OUTER_WALK as u32)
        }
    }

    /// [realization; P61 item 4f] **An outer pass's slot for its two largest words**: two 64-bit words of a card buffer of `OUTER_SLOTS` slots,
    /// zeroed when it is first taken and again (in the stream's order, after every launch that read the slots before) each time its slots are
    /// spent, so every pass reads a slot zeroed for it alone. The device address of the slot.
    pub(crate) fn outer_slot(&self) -> Result<u64> {
        let mut held = self.outer_maxima.borrow_mut();
        if held.is_none() {
            let buffer = self.timed(Kind::Alloc, || self.take_zeroed::<u64>(2 * OUTER_SLOTS)).map_err(device)?;
            *held = Some((buffer, 0));
        }
        let (buffer, next) = held.as_mut().expect("the slots were just taken");
        if *next == OUTER_SLOTS {
            self.card.stream().memset_u32_async(buffer.device_ptr(), 0, 4 * OUTER_SLOTS).map_err(|e| device(e.into()))?;
            *next = 0;
        }
        let at = buffer.device_ptr() + 16 * *next as u64;
        *next += 1;
        Ok(at)
    }
}
