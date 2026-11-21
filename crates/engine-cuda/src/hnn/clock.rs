//! **Rings, clocks and paces, on the card.** The launches of the host's rings and of the open places' clocks
//! (`crates/engine/src/navigator.rs`, whose first lines state the equations, the kind and the Lean and atlas owners). THE_ENGINE §3 lists
//! each kernel beside the phase it serves, and the host is the reference these bits are read against (`athena parity`).

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

/// [theory, November 12, P50 step 1 and P51] The clock's skin store of a region of `sites` sites, `definite` of them definite
/// ([`Resident::skin_fill`]): 32 bits a paced head, support entry and mode over the row's support stride `K = NEAR_SLOTS + definite` (atlas
/// `tower.field-support-stride`: every row's support fits it), and a paced head, site, crowd slot and mode. Returns (the region's octets, octets a
/// reserved entry, octets a site's crowd edges, octets a site's near phases and skins).
pub fn skin_octets(d: &Declaration, sites: usize, definite: usize) -> (u64, u64, u64, u64) {
    let per = 4 * d.paced_heads() as u64 * d.modes as u64;
    let (entry, site) = (per, per * crowd_slots(d.reach) as u64);
    let stride = (2 * (NEAR - 1) + definite) as u64;
    // [theory, November 12, P50 step 2] A clock's near phases (two words) and skins (one), a moment mode and near offset of each site.
    let moment = if d.paced_heads() > 0 { 12 * (d.moment_modes() * CLOCK_NEAR) as u64 } else { 0 };
    (entry * sites as u64 * stride + (site + moment) * sites as u64, entry, site, moment)
}

/// The near offsets a moment mode reads about a site, `2(NEAR − 1)` (the clock's store, `near_slot`).
pub(crate) const CLOCK_NEAR: usize = 2 * (NEAR - 1);

/// A region's definite sites (the stage's `definite`: known and carrying no face, or locked).
pub(crate) fn definite_sites(region: &Region) -> usize {
    (0..region.classes.len()).filter(|&t| (!region.unresolved[t] && region.faces.get(t).and_then(Option::as_ref).is_none()) || region.locked.get(t).copied().unwrap_or(false)).count()
}

/// The fine sites a batch's words stage.
pub(crate) fn tb_fine_sites(words: &Words) -> usize {
    words.t as usize
}

/// Point the words at a tick's temporaries.
/// [definition; §16.44] A tick's own clocks on the card (the host's `TickClock`): its rates, clocks, variations, plainness
/// and frames, the moments read on them, and the blanks' rates with the face they were read from.
pub(crate) struct CardClock<'c> {
    pub(crate) kappa: Pooled<'c, i64>,
    pub(crate) tau: Pooled<'c, i64>,
    pub(crate) sigma: Pooled<'c, i64>,
    pub(crate) saddr: Pooled<'c, i64>,
    pub(crate) plain: Pooled<'c, u8>,
    pub(crate) pframe: Pooled<'c, i64>,
    pub(crate) moment: Pooled<'c, i64>,
    pub(crate) rates: Pooled<'c, i64>,
    pub(crate) masses: Pooled<'c, u64>,
    pub(crate) totals: Pooled<'c, i128>,
    /// The blanks' reads the return runs through: the chart and its scales, and the lift.
    pub(crate) fread: Pooled<'c, i32>,
    pub(crate) fscale: Pooled<'c, i128>,
    pub(crate) lift: Pooled<'c, i64>,
}

/// The words a tick reads its clocks through (§16.44): its own, or the pass's `base` (`kappa`, `tau`, `sigma`, `plain`,
/// `pframe`, `moment`), with no blank rates.
pub(crate) fn set_clock(w: &mut Words, clock: Option<&CardClock>, base: [u64; 7]) {
    match clock {
        Some(c) => {
            (w.kappa, w.tau, w.sigma, w.plain, w.pframe, w.moment) = (c.kappa.device_ptr(), c.tau.device_ptr(), c.sigma.device_ptr(), c.plain.device_ptr(), c.pframe.device_ptr(), c.moment.device_ptr());
            w.saddr = c.saddr.device_ptr();
            (w.blank_rate, w.blank_masses, w.blank_totals) = (c.rates.device_ptr(), c.masses.device_ptr(), c.totals.device_ptr());
        }
        None => {
            [w.kappa, w.tau, w.sigma, w.plain, w.pframe, w.moment, w.saddr] = base;
            (w.blank_rate, w.blank_masses, w.blank_totals) = (0, 0, 0);
        }
    }
}

pub(crate) fn set_tick(w: &mut Words, tick: &Tick, returning: bool) {
    w.fgate = tick.fgate.as_ref().map_or(0, |b| b.device_ptr());
    w.qkv = tick.qkv.device_ptr();
    w.qf = tick.qf.device_ptr();
    w.qf32 = tick.qf32.device_ptr();
    w.pq = tick.pq.device_ptr();
    w.pq32 = tick.pq32.device_ptr();
    w.pscale = tick.pscale.device_ptr();
    w.vf = tick.vf.device_ptr();
    w.cls = tick.cls.device_ptr();
    w.class_off = tick.class_off.device_ptr();
    w.members = tick.members.device_ptr();
    w.pn = tick.pn.device_ptr();
    w.pcls = tick.pcls.device_ptr();
    w.poff = tick.poff.device_ptr();
    w.pmem = tick.pmem.device_ptr();
    w.e = tick.e.device_ptr();
    w.sb = if returning { tick.sb.device_ptr() } else { 0 };
    w.amin = tick.amin.device_ptr();
    w.sw = tick.sw.device_ptr();
    w.sv = tick.sv.device_ptr();
    w.sc = tick.sc.device_ptr();
    w.ce = tick.ce.device_ptr();
    w.y = tick.y.device_ptr();
    w.pa = tick.pa.device_ptr();
    w.pg = tick.pg.device_ptr();
    w.pgam = tick.pgam.device_ptr();
    w.pqm = tick.pqm.device_ptr();
    w.pkb = tick.pkb.device_ptr();
    w.pb = tick.pb.device_ptr();
    w.pc = tick.pc.device_ptr();
    set_triads(w, tick);
    w.bits = tick.bits.device_ptr();
}

/// A held buffer's address, zero where none is held.
pub(crate) fn held_at(b: &Option<Pooled<'_, i64>>) -> u64 {
    b.as_ref().map_or(0, |b| b.device_ptr())
}

impl<'c> Resident<'c> {

    /// [definition; §16.44] **A blank's clock returns through its face** (the host's `Constitution::blank_return`): from each
    /// silent site's rates' covector `δκ` the face's logits' covector (held `2^30` finer), the encoding's bias and rows, the
    /// lift's covector (held `2^16` finer), the lift's bias and the read matrix, the chart's return and the lane adjoint, and
    /// the state's covector `dx` takes it.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn blank_back(&self, field: &Constitution, words: &mut Words, clock: &CardClock<'c>, dkappa: &CardBuffer<'c, i128>, g: &CardBuffer<'c, i128>, dx: &CardBuffer<'c, i64>, sites: usize) -> Result<()> {
        let d = field.declaration;
        let (dw, a) = (d.width, d.alphabet);
        let l = field.layout();
        let dz = self.timed(Kind::Alloc, || self.take::<i128>((sites * a).max(1))).map_err(device)?;
        // The faces were read at the sites a clock reads alone (`blank_clock`), and return there alone.
        let unresolved = words.unresolved;
        words.unresolved = words.blank_read;
        // [realization; November 16] The sites whose `δz` is nonzero in some class, marked (`live_at`, written at every site) and listed in
        // ascending order (`live`, its count `nlive`, by `field_blank_live_scan`): the outer sums walk the list and the lift's covector is zero
        // off it.
        let live_at = self.timed(Kind::Alloc, || self.take::<u8>(sites.max(1))).map_err(device)?;
        let live = self.timed(Kind::Alloc, || self.take::<u32>(sites.max(1))).map_err(device)?;
        let nlive = self.timed(Kind::Alloc, || self.take::<u32>(1)).map_err(device)?;
        let (mut dkp, mut dzp, mut lap) = (dkappa.device_ptr(), dz.device_ptr(), live_at.device_ptr());
        self.launch("field_blank_dz", (sites as u64).clamp(1, 65_535) as u32, BLANK_DZ_THREADS, &mut [arg(words), arg(&mut dkp), arg(&mut dzp), arg(&mut lap)])?;
        {
            let (mut lap, mut lp, mut nlp) = (live_at.device_ptr(), live.device_ptr(), nlive.device_ptr());
            self.launch("field_blank_live_scan", 1, BLANK_SCAN_THREADS, &mut [arg(words), arg(&mut lap), arg(&mut lp), arg(&mut nlp)])?;
        }
        // [measurement; theory, November 16] Which of the walked sites the blank's outer sums meet with a nonzero term: a reading of `δz`,
        // which moves nothing the field computes.
        if let Some(profile) = self.profile.as_ref().filter(|_| std::env::var_os("FIELD_BLANK_LIVE").is_some()) {
            let z = self.timed(Kind::Copy, || self.card.fetch_range(&dz, 0, sites * a)).map_err(device)?;
            let live_sites = z.chunks(a.max(1)).filter(|row| row.iter().any(|v| *v != 0)).count() as u128;
            let live = z.iter().filter(|v| **v != 0).count() as u128;
            let mut p = profile.borrow_mut();
            for (slot, v) in p.blank_live.iter_mut().zip([1, sites as u128, live_sites, (sites * a) as u128, live]) {
                *slot += v;
            }
        }
        // The outer sums' launches fill the card's resident threads for their entry once (its multiprocessors times the blocks of the entry
        // each holds, as the driver reads the entry's occupancy); each kernel reads the list's count and sizes its tiles to that.
        let multiprocessors = u64::from(self.card.census().multiprocessors.max(1));
        let resident = |entry: &str| -> Result<u64> {
            let blocks = self.module.function(entry).and_then(|f| f.active_blocks_per_multiprocessor(THREADS, 0)).map_err(|e| device(e.into()))?;
            Ok(multiprocessors * u64::from(blocks.max(1)) * u64::from(THREADS))
        };
        let mut want = resident("field_blank_bias_enc")?;
        {
            let (mut gp, mut enc, mut bias, mut dzp, mut yp, mut lp, mut nlp) = (g.device_ptr(), words.enc, words.read_bias, dz.device_ptr(), clock.lift.device_ptr(), live.device_ptr(), nlive.device_ptr());
            self.launch("field_blank_bias_enc", Self::cells(want), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut enc), arg(&mut bias), arg(&mut dzp), arg(&mut yp), arg(&mut lp), arg(&mut nlp), arg(&mut want)])?;
        }
        let dy = self.timed(Kind::Alloc, || self.take::<i64>((sites * dw).max(1))).map_err(device)?;
        {
            let (mut enc, mut dzp, mut dyp, mut lap) = (words.enc, dz.device_ptr(), dy.device_ptr(), live_at.device_ptr());
            self.launch("field_blank_dy", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut dzp), arg(&mut dyp), arg(&mut lap)])?;
        }
        {
            let (mut gp, mut read, mut bias, mut dyp, mut rp, mut lp, mut nlp) = (g.device_ptr(), words.read, l.lift_bias as u64, dy.device_ptr(), clock.fread.device_ptr(), live.device_ptr(), nlive.device_ptr());
            want = resident("field_blank_lift_read")?;
            self.launch("field_blank_lift_read", Self::cells(want), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut read), arg(&mut bias), arg(&mut dyp), arg(&mut rp), arg(&mut lp), arg(&mut nlp), arg(&mut want)])?;
        }
        // [realization; theory, November 13, P58 item 2] `dr` and `back` unzeroed. `field_transposed` (no accumulation) writes every column of a
        // site the clock read (`blank_read`, set above), and `dr`'s one reader, `field_ratio_adjoint` on the same sites, reads its covector only
        // there. `field_ratio_adjoint` with no base writes every word of `back`, zero at a site it skips and every lane's coordinates elsewhere,
        // before `field_blank_dx` reads it.
        let dr = self.timed(Kind::Alloc, || self.take::<i64>((sites * dw).max(1))).map_err(device)?;
        self.transposed(words, words.read, dw, dw, dy.device_ptr(), dw, dr.device_ptr(), false, true)?;
        let back = self.timed(Kind::Alloc, || self.take::<i64>((sites * dw).max(1))).map_err(device)?;
        self.ratio_adjoint(words, clock.fread.device_ptr(), clock.fscale.device_ptr(), dr.device_ptr(), 0, back.device_ptr(), true)?;
        let (mut bp, mut dxp) = (back.device_ptr(), dx.device_ptr());
        let done = self.launch("field_blank_dx", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut bp), arg(&mut dxp)]);
        words.unresolved = unresolved;
        done
    }

    /// [definition; §16.44] **The clocks a tick's blanks run at** (the host's `pass`): the face each unresolved site's state
    /// reads now (the chart, the lift, the encoding, at temperature one), each silent site's rate from its shares
    /// (`field_blank_rates`), and the clocks, frames and moments read again on those rates, into a tick's own buffers; the
    /// words are left pointing at them.
    pub(crate) fn blank_clock(&self, field: &Constitution, words: &mut Words, regions: usize, sites: usize) -> Result<CardClock<'c>> {
        let d = field.declaration;
        let (dw, a, n, m2, paced) = (d.width, d.alphabet, d.modes, 2 * d.complex(), d.paced_heads());
        // [realization; theory, November 13, P58 item 2] The blank's read, scale, lift and totals are taken without zeroing where no clock is read
        // at named sites: the face kernels write each at the sites the clock reads (`blank_read`) and every reader reads them only there:
        // `field_affine` and `field_ratio_adjoint` (blank_back) on the same sites, `field_blank_bias_enc` and `field_blank_lift_read` only where
        // the blank's face covector `dz` and its lift's `dy` are nonzero (written zero off those sites, by `field_blank_dz` and `field_blank_dy`),
        // `field_blank_rates` and `field_blank_dz` on the same sites, and `field_pace_c_back` where `blank_read[t]`. The clocks' reading at named
        // sites (`clock_sites`) fetches a silent site's face that the clock may not have read, so it keeps them zeroed.
        let zeroed = self.clock_sites.borrow().is_some();
        let fread = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i32>(sites * dw)) } else { self.timed(Kind::Alloc, || self.take::<i32>(sites * dw)) }.map_err(device)?;
        let fscale = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites * d.lanes)) } else { self.timed(Kind::Alloc, || self.take::<i128>(sites * d.lanes)) }.map_err(device)?;
        // [the unified-theory reading of November 6, 08:16] The faces are read only at the sites a clock reads (`blank_read`): the
        // face kernels read the open sites, so they are given those sites as the open ones, and the region's own are restored
        // before the clocks.
        let unresolved = words.unresolved;
        words.unresolved = words.blank_read;
        self.chart(words, words.x, &fread, &fscale, true)?;
        let lift = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i64>(sites * dw)) } else { self.timed(Kind::Alloc, || self.take::<i64>(sites * dw)) }.map_err(device)?;
        let lift_bias = field.layout().lift_bias as u64;
        self.affine("field_affine_x32", words, words.read, lift_bias, words.rread, dw, dw, fread.device_ptr(), dw, lift.device_ptr(), dw, 0, true)?;
        let z = self.timed(Kind::Alloc, || self.take::<i64>(sites * a)).map_err(device)?;
        {
            let (mut enc, mut cb, mut yp, mut zp) = (words.enc, words.read_bias, lift.device_ptr(), z.device_ptr());
            self.launch("field_tied_face_tiled", Self::map_grid(a, sites), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut zp)])?;
        }
        let masses = self.timed(Kind::Alloc, || self.take::<u64>(sites * a)).map_err(device)?;
        let totals = if zeroed { self.timed(Kind::Alloc, || self.take_zeroed::<i128>(sites)) } else { self.timed(Kind::Alloc, || self.take::<i128>(sites)) }.map_err(device)?;
        {
            let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
            self.launch("field_face", Self::warps(sites as u64), THREADS, &mut [arg(words), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        }
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let rates = alloc64(paced * sites)?;
        let clock = CardClock {
            kappa: alloc64(paced * sites)?,
            tau: alloc64(paced * sites)?,
            sigma: alloc64(paced * sites)?,
            saddr: alloc64(3 * paced * n * sites)?,
            plain: self.timed(Kind::Alloc, || self.take::<u8>((paced * regions).max(1))).map_err(device)?,
            pframe: alloc64(2 * paced * sites * n)?,
            moment: self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?,
            rates,
            masses,
            totals,
            fread,
            fscale,
            lift,
        };
        (words.blank_masses, words.blank_totals) = (clock.masses.device_ptr(), clock.totals.device_ptr());
        let mut rp = clock.rates.device_ptr();
        self.launch("field_blank_rates", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut rp)])?;
        words.unresolved = unresolved;
        set_clock(words, Some(&clock), [0; 7]);
        self.launch("field_paces", ((paced * regions) as u64).clamp(1, 65_535) as u32, PACE_SCAN_THREADS, &mut [arg(words)])?;
        self.launch("field_skin_addresses", Self::cells((paced * n * sites) as u64), THREADS, &mut [arg(words)])?;
        self.launch("field_pframes", Self::cells((paced * sites * n) as u64), THREADS, &mut [arg(words)])?;
        self.moments(field, words, regions, sites, false)?;
        Ok(clock)
    }

    /// [definition; theory, November 12, P50 step 1 (G116 a)] **The clock's skins, formed once** (`field_skin_fill`): after the clock is set, every
    /// support pair's and crowd edge's skin of the paced heads where their pace is not plain, read by the lock, the numerators, the rows, the columns
    /// and the skin's return. A debug build, and a test build whose fill is withheld, first writes `SKIN_UNFILLED` over the store, so a reader of a word no fill formed is refused
    /// (`REFUSED_UNFILLED`); a level with no store (no paced head, the packets' plain clocks) forms none.
    pub(crate) fn skin_fill(&self, field: &Constitution, words: &mut Words, sites: usize) -> Result<()> {
        let d = field.declaration;
        let paced = d.paced_heads();
        if paced == 0 || words.skin == 0 {
            return Ok(());
        }
        #[cfg(test)]
        let withheld = self.unfilled.get();
        #[cfg(not(test))]
        let withheld = false;
        // The planted word is written wherever the fill is withheld, whatever the build's profile: a release test build holds the control too.
        if cfg!(debug_assertions) || withheld {
            let n = d.modes;
            let pair_words = paced * words.skin_entries as usize * n;
            let stream = self.card.stream();
            stream.memset_u32_async(words.skin, u32::MAX, pair_words.max(1)).map_err(|e| device(e.into()))?;
        }
        if withheld {
            return Ok(());
        }
        let mut pc = paced as u32;
        self.launch("field_skin_fill", Self::rows_grid((paced * sites) as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut pc)])
    }

    /// [definition; theory, November 12, P50 step 2 (G116 b)] **The clock's phases and skins, formed once** (`field_clock_fill`): after a clock is set,
    /// every moment mode's near phases and skins at every site of a paced head, and its far skins into the crowd edges' store, read by the moments, the
    /// skinned prefixes, the moments' return and the clocks' covector, and by the contact's crowds. A debug build, and a test build whose fill is withheld, first writes `PHASE_UNFILLED` and
    /// `SKIN_UNFILLED` over the stores, so a reader of a word no fill formed is refused (`REFUSED_UNFILLED`).
    pub(crate) fn clock_fill(&self, field: &Constitution, words: &Words, sites: usize) -> Result<()> {
        let d = field.declaration;
        let tm = words.tm as usize;
        if tm == 0 || words.mphase == 0 || words.cskin == 0 {
            return Ok(());
        }
        #[cfg(test)]
        let withheld = self.unfilled.get();
        #[cfg(not(test))]
        let withheld = false;
        if cfg!(debug_assertions) || withheld {
            let stream = self.card.stream();
            let near = tm * sites * CLOCK_NEAR;
            stream.memset_u32_async(words.mphase, 0x8000_0000, 2 * near).map_err(|e| device(e.into()))?;
            stream.memset_u32_async(words.mskin, u32::MAX, near).map_err(|e| device(e.into()))?;
            stream.memset_u32_async(words.cskin, u32::MAX, (d.paced_heads() * sites * words.slots as usize * d.modes).max(1)).map_err(|e| device(e.into()))?;
        }
        if withheld {
            return Ok(());
        }
        let mut fw = *words;
        self.launch_grid("field_clock_fill", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut fw)])
    }
}
