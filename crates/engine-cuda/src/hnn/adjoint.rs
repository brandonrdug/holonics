//! The card realization's adjoint (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::hnn::field::*;
#[allow(unused_imports)]
use core::ffi::c_void;
#[allow(unused_imports)]
use std::time::Instant;
#[allow(unused_imports)]
use holonics_engine::field::{band_bits, landmarks_of, BlankClocks, CarryGates, Field, FieldDeclaration, FieldRead, FieldRealization, HeldRows, NearOffsets, RealizationCounters, RowCurrent, Region, Scale, TickRead, NEAR, SHARE_BITS, STATE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{level_cut, level_section, PACE_BITS};
#[allow(unused_imports)]
use holonics_engine::inherited::tower::{TowerError, TowerFace, MATERIAL_BITS};
#[allow(unused_imports)]
use crate::cuda::{Dim3, Module};
#[allow(unused_imports)]
use crate::hnn::card::{Card, CardBuffer, CardError};

/// A level's reverse buffers ([`CardField::back_buffers`]).
pub(crate) struct Back<'c> {
    pub(crate) dx: Pooled<'c, i64>,
    pub(crate) dr: Pooled<'c, i64>,
    pub(crate) dc: Pooled<'c, i64>,
    pub(crate) da: Pooled<'c, i64>,
    pub(crate) db: Pooled<'c, i64>,
    /// [theory, November 11 17:25] The carry circles' covector `[t][2C]` (one slot without them): the scan's reverse writes `δγ`, and the gate's
    /// reverse writes `δq`, `δℓ` over it in place, the circles' charts' row order.
    pub(crate) dg: Pooled<'c, i64>,
    /// [theory, November 12; the triad record §4] The triads' covectors (none without them): the products' `δc^T = W_Tᵀ δx` `[t][2J]`, and the legs'
    /// `δα`, `δβ`, `δγ` `[t][6J]` in the chart's row order.
    pub(crate) dct: Option<Pooled<'c, i64>>,
    pub(crate) dabg: Option<Pooled<'c, i64>>,
    pub(crate) ra: Pooled<'c, i64>,
    pub(crate) rb: Pooled<'c, i64>,
    pub(crate) dmid: Pooled<'c, i64>,
    pub(crate) dy: Pooled<'c, i64>,
    pub(crate) dyh: Pooled<'c, i64>,
    pub(crate) dq: Pooled<'c, i64>,
    pub(crate) dv: Pooled<'c, i64>,
    pub(crate) dp: Pooled<'c, i64>,
    pub(crate) ds: Pooled<'c, i64>,
    pub(crate) dpb: Pooled<'c, i128>,
    pub(crate) cv: Pooled<'c, i128>,
    pub(crate) cw: Pooled<'c, i128>,
    pub(crate) dm: Pooled<'c, i128>,
    pub(crate) gtau: Pooled<'c, i128>,
    pub(crate) gsig: Pooled<'c, i128>,
    pub(crate) cds: Pooled<'c, i64>,
    pub(crate) pr_back: Pooled<'c, i64>,
}

impl<'c> CardField<'c> {

    pub(crate) fn ratio_adjoint(&self, words: &mut Words, read: u64, scale: u64, cov: u64, base: u64, dst: u64, only_unresolved: bool) -> Result<()> {
        let (mut read, mut scale, mut cov, mut base, mut dst, mut u) = (read, scale, cov, base, dst, u32::from(only_unresolved));
        self.launch("field_ratio_adjoint", Self::warps(words.t as u64), THREADS, &mut [arg(words), arg(&mut read), arg(&mut scale), arg(&mut cov), arg(&mut base), arg(&mut dst), arg(&mut u)])
    }

    /// One tick's reverse on the card (the host's `Field::tick_return`): `b.dx`, the covector of the tick's output faces,
    /// carried back to the covector of its input faces, the level's material covector added into `g`.
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn tick_back(&self, field: &Field, words: &mut Words, tick: &Tick<'c>, at: usize, g: &CardBuffer<'c, i128>, b: &Back<'c>, dm: u64, sites: usize, readings: bool) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let regions = words.r as usize;
        let rows = sites + regions;
        let paced = d.paced_heads();
        let Back { dx, dr, dc, da, db, dg, dct, dabg, ra, rb, dmid, dy, dyh, dq, dv, dp, ds, cv, cw, pr_back, .. } = b;
        words.qf = tick.qf.device_ptr();
        words.qf32 = tick.qf32.device_ptr();
        words.pq = tick.pq.device_ptr();
        words.pq32 = tick.pq32.device_ptr();
        words.pscale = tick.pscale.device_ptr();
        words.vf = tick.vf.device_ptr();
        words.cls = tick.cls.device_ptr();
        words.class_off = tick.class_off.device_ptr();
        words.members = tick.members.device_ptr();
        words.pn = tick.pn.device_ptr();
        words.pcls = tick.pcls.device_ptr();
        words.poff = tick.poff.device_ptr();
        words.pmem = tick.pmem.device_ptr();
        words.e = tick.e.device_ptr();
        words.sb = tick.sb.device_ptr();
        words.qkv = tick.qkv.device_ptr();
        words.amin = tick.amin.device_ptr();
        words.sw = tick.sw.device_ptr();
        words.sv = tick.sv.device_ptr();
        words.sc = tick.sc.device_ptr();
        words.ce = tick.ce.device_ptr();
        words.pa = tick.pa.device_ptr();
        words.pg = tick.pg.device_ptr();
        words.pgam = tick.pgam.device_ptr();
        words.pqm = tick.pqm.device_ptr();
        words.pkb = tick.pkb.device_ptr();
        words.pb = tick.pb.device_ptr();
        words.pc = tick.pc.device_ptr();
        set_triads(words, tick);
        // The pair contact: x_out = x_mid + W_c c + b_c.
        self.outer(words, g, words.w_bias, dw, 0, dx.device_ptr(), dw, 0, 0, false, false)?;
        self.outer(words, g, words.w, dw, f, dx.device_ptr(), dw, tick.pc.device_ptr(), f, true, false)?;
        self.transposed(words, words.w, dw, f, dx.device_ptr(), dw, dc.device_ptr(), false, false)?;
        // [definition; theory, November 12; the triad record §4] The triads' reverse, by the product rule through the producing operands: `W_T`'s
        // covector `Σ_t δx_t c^T_tᵀ`, the products' covector `δc^T = W_Tᵀ δx` a site, then the legs' covectors `δα`, `δβ`, `δγ` (`field_triad_back`), each
        // slot written by the one place that read it. Their chart's outer sums and transposed read follow the plain contacts' and the circles' below.
        let triads = d.triads;
        let (dctp, dabgp) = (held_at(dct), held_at(dabg));
        if triads > 0 {
            self.outer(words, g, words.wtr, dw, 2 * triads, dx.device_ptr(), dw, words.pct, 2 * triads, true, false)?;
            self.transposed(words, words.wtr, dw, 2 * triads, dx.device_ptr(), dw, dctp, false, false)?;
            let (mut dctp, mut dabgp) = (dctp, dabgp);
            self.launch("field_triad_back", Self::cells((sites * triads) as u64), THREADS, &mut [arg(words), arg(&mut dctp), arg(&mut dabgp)])?;
        }
        let (mut dcp, mut dap, mut dbp) = (dc.device_ptr(), da.device_ptr(), db.device_ptr());
        let (plain, circles) = (d.carry_first(), d.carry);
        if plain > 0 {
            self.launch("field_pair_back", Self::cells((sites * plain) as u64), THREADS, &mut [arg(words), arg(&mut dcp), arg(&mut dap), arg(&mut dbp)])?;
        }
        if circles > 0 {
            // [theory, November 11 17:25 and November 12 (G98)] The circles' reverse: the same (region, circle) jobs in the opposite strand order, with the
            // forward's `γ`, coupled drive and `Q` operand, writing `δγ` and `u` a site and circle; then `δq`, `δℓ` and the drive's `δb = κ u` off the chain
            // on the pair's grid, the divisions out of the chain.
            let mut dgp = dg.device_ptr();
            self.launch("field_pair_scan_back", Self::cells((words.r as usize * circles) as u64), THREADS, &mut [arg(words), arg(&mut dcp), arg(&mut dap), arg(&mut dbp), arg(&mut dgp)])?;
            let (mut dgp, mut dbp) = (dg.device_ptr(), db.device_ptr());
            self.launch("field_pair_gate_back", Self::cells((sites * circles) as u64), THREADS, &mut [arg(words), arg(&mut dgp), arg(&mut dbp)])?;
        }
        self.outer(words, g, words.wa, f, dw, da.device_ptr(), f, tick.read2.device_ptr(), dw, false, false)?;
        self.outer(words, g, words.wb, f, dw, db.device_ptr(), f, tick.read2.device_ptr(), dw, false, false)?;
        self.outer(words, g, words.a_bias, f, 0, da.device_ptr(), f, 0, 0, false, false)?;
        self.outer(words, g, words.b_bias, f, 0, db.device_ptr(), f, 0, 0, false, false)?;
        if circles > 0 {
            self.outer(words, g, words.wg, 2 * circles, dw, dg.device_ptr(), 2 * circles, tick.read2.device_ptr(), dw, false, false)?;
            self.outer(words, g, words.wgb, 2 * circles, 0, dg.device_ptr(), 2 * circles, 0, 0, false, false)?;
        }
        if triads > 0 {
            // The triads' chart: `Σ_t δabg(t) r̂(t)ᵀ` into `A`, `B` and `G`, and `Σ_t δabg(t)` into their biases.
            self.outer(words, g, words.wt, 6 * triads, dw, dabgp, 6 * triads, tick.read2.device_ptr(), dw, false, false)?;
            self.outer(words, g, words.wtb, 6 * triads, 0, dabgp, 6 * triads, 0, 0, false, false)?;
        }
        self.transposed(words, words.wa, f, dw, da.device_ptr(), f, ra.device_ptr(), false, false)?;
        self.transposed(words, words.wb, f, dw, db.device_ptr(), f, rb.device_ptr(), false, false)?;
        if circles > 0 {
            self.transposed(words, words.wg, 2 * circles, dw, dg.device_ptr(), 2 * circles, rb.device_ptr(), true, false)?;
        }
        if triads > 0 {
            // The triads' chart reads the pair chart as `a`, `b` and the circles' do, so its transposed product joins the read's covector.
            self.transposed(words, words.wt, 6 * triads, dw, dabgp, 6 * triads, rb.device_ptr(), true, false)?;
        }
        let (mut rap, mut rbp, mut cells) = (ra.device_ptr(), rb.device_ptr(), (sites * dw) as u64);
        self.launch("field_add", Self::cells(cells), THREADS, &mut [arg(words), arg(&mut rap), arg(&mut rbp), arg(&mut cells)])?;
        self.ratio_adjoint(words, tick.read2.device_ptr(), tick.scale2.device_ptr(), rb.device_ptr(), dx.device_ptr(), dmid.device_ptr(), false)?;
        // The current: x_mid = x_in + O y + b_o.
        self.outer(words, g, words.out_bias, dw, 0, dmid.device_ptr(), dw, 0, 0, false, false)?;
        self.outer(words, g, words.out, dw, m2, dmid.device_ptr(), dw, tick.y.device_ptr(), m2, true, false)?;
        self.transposed(words, words.out, dw, m2, dmid.device_ptr(), dw, dy.device_ptr(), false, false)?;
        // The weights and the contact over each site's support, head by head: the rows' return
        // first, then the columns', which adds the word's second role into the same slots.
        let (mut dyp, mut dyhp) = (dy.device_ptr(), dyh.device_ptr());
        self.launch("field_current_back", Self::cells((heads * sites * n) as u64), THREADS, &mut [arg(words), arg(&mut dyp), arg(&mut dyhp)])?;
        // The current's covector of this tick, where the held rows' currents are read (§16.21).
        if let Some(cov) = self.row_cov.borrow_mut().as_mut().filter(|_| readings) {
            cov[at] = self.timed(Kind::Copy, || self.card.fetch_range(&dyh, 0, heads * sites * span)).map_err(device)?;
        }
        if paced > 0 {
            let (mut dyp, mut yp) = (dy.device_ptr(), tick.y.device_ptr());
            self.launch("field_pace_current_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dyp), arg(&mut yp)])?;
        }
        card.zero_octets(&dp, 0, 8 * sites * m2).map_err(device)?;
        // The tick's clock's phases and skins and its pairs' skins, formed again for its return (the forward's stores hold a later tick's): the crowd
        // edges and the moments' return read the clock's.
        self.clock_fill(field, words, sites)?;
        self.skin_fill(field, words, sites)?;
        if let Some(profile) = &self.profile {
            let mut p = profile.borrow_mut();
            if p.head_kinds.len() < heads {
                p.head_kinds = (0..heads).map(|h| if !d.carries_moment(h) { "still" } else if d.is_depth(h) { "depth" } else { "paced" }).collect();
            }
        }
        for h in 0..heads {
            self.head.set(Some(h as u32));
            // The crowds' difference arrays start empty a head (§14.10).
            card.zero_octets(&cv, 0, 16 * rows * span).map_err(device)?;
            card.zero_octets(&cw, 0, 16 * rows * span).map_err(device)?;
            let (mut hh, mut dyhp, mut dsp, mut dqp) = (h as u32, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr());
            // [measurement; theory, November 12, P53 item 1 (G120)] The ruler build alone: the rows' memory without their arithmetic, immediately
            // before the entry, its stores and atomics into scratch arrays of the layouts the entry writes, so the state's bytes are the law's.
            #[cfg(feature = "ruler-rows-reads")]
            {
                let pairs = words.pairs as usize;
                let scratch64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
                let scratch128 = |len: usize| self.timed(Kind::Alloc, || self.take::<i128>(len.max(1))).map_err(device);
                let (ds_s, dq_s, dp_s) = (scratch64(pairs)?, scratch64(sites * m2)?, scratch64(sites * m2)?);
                let (dpb_s, cds_s) = (scratch128(pairs)?, scratch64(heads * sites * words.slots as usize)?);
                let (cw_s, cv_s, gcov_s) = (scratch128(rows * span)?, scratch128(rows * span)?, scratch128(field.layout().len)?);
                let (mut dsp_s, mut dqp_s, mut dpp_s, mut dpbp_s) = (ds_s.device_ptr(), dq_s.device_ptr(), dp_s.device_ptr(), dpb_s.device_ptr());
                let (mut cdsp_s, mut cwp_s, mut cvp_s, mut gcp_s) = (cds_s.device_ptr(), cw_s.device_ptr(), cv_s.device_ptr(), gcov_s.device_ptr());
                self.launch(
                    "field_yard_rows",
                    Self::rows_grid(sites as u64, REV_ROWS),
                    (REV_ROWS * 32) as u32,
                    &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp_s), arg(&mut dqp_s), arg(&mut dpp_s), arg(&mut dpbp_s), arg(&mut cdsp_s), arg(&mut cwp_s), arg(&mut cvp_s), arg(&mut gcp_s)],
                )?;
            }
            self.launch("field_contact_rows", Self::rows_grid(sites as u64, REV_ROWS), (REV_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp)])?;
            #[cfg(feature = "ruler-bits")]
            {
                self.bits_pairs(words, h, 2, 0, ds.device_ptr(), 3, at, sites)?;
                self.bits_pairs(words, h, 3, 0, words.dpb, 4, at, sites)?;
            }
            if d.carries_moment(h) && !d.is_depth(h) {
                // The head's skins return to its variation (§16), from the pairs' and crowds' covectors just formed.
                let (mut hh, mut dyhp, mut dsp) = (h as u32, dyh.device_ptr(), ds.device_ptr());
                self.launch("field_pace_skin_back", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp)])?;
            }
            let (mut hh, mut dyhp, mut dsp, mut dqp, mut dvp) = (h as u32, dyh.device_ptr(), ds.device_ptr(), dq.device_ptr(), dv.device_ptr());
            self.launch("field_contact_columns", Self::rows_grid(sites as u64, CONTACT_ROWS), (CONTACT_ROWS * 32) as u32, &mut [arg(words), arg(&mut hh), arg(&mut dyhp), arg(&mut dsp), arg(&mut dqp), arg(&mut dvp)])?;
            let (mut hh, mut dqp, mut dvp) = (h as u32, dq.device_ptr(), dv.device_ptr());
            self.launch("field_spread", (regions as u32).clamp(1, 65_535), THREADS, &mut [arg(words), arg(&mut hh), arg(&mut dqp), arg(&mut dvp)])?;
        }
        self.head.set(None);
        let (mut qs, mut dqp) = (tick.qscale.device_ptr(), dq.device_ptr());
        self.launch("field_unit_back", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut qs), arg(&mut dqp)])?;
        // The probe's return through its own power, alike (§16.19).
        let (mut ps, mut dpp) = (tick.pscale.device_ptr(), dp.device_ptr());
        self.launch("field_unit_back_probe", Self::warps((heads * sites) as u64), THREADS, &mut [arg(words), arg(&mut ps), arg(&mut dpp)])?;
        for chart in [&dq, &dv, &dp] {
            let mut cp = chart.device_ptr();
            self.launch("field_unframe", Self::cells((sites * m) as u64), THREADS, &mut [arg(words), arg(&mut cp)])?;
        }
        if paced > 0 {
            // The frames' return to the clocks (§16): the unframed word and value of the tick, its probe read again.
            self.affine("field_affine_x32", words, words.probe, words.probe_bias, words.rprobe, m2, dw, tick.read.device_ptr(), dw, pr_back.device_ptr(), m2, 0, false)?;
            let mut prb = pr_back.device_ptr();
            self.launch("field_moment_add_probe", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut prb)])?;
            let (mut dqp, mut dvp, mut dpp, mut qkvp, mut prp) = (dq.device_ptr(), dv.device_ptr(), dp.device_ptr(), tick.qkv.device_ptr(), pr_back.device_ptr());
            self.launch("field_pace_frame_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dqp), arg(&mut dvp), arg(&mut dpp), arg(&mut qkvp), arg(&mut prp)])?;
        }
        // The values' and the probes' covectors, summed over the ticks, for the moments (§15.1, §16.20).
        for chart in [&dv, &dp] {
            let (mut cp, mut dmp) = (chart.device_ptr(), dm);
            self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp), arg(&mut dmp)])?;
        }
        card.zero_octets(&dr, 0, 8 * sites * dw).map_err(device)?;
        for (weight, bias, chart) in [(words.q, words.q_bias, &dq), (words.v, words.v_bias, &dv), (words.probe, words.probe_bias, &dp)] {
            self.outer(words, g, weight, m2, dw, chart.device_ptr(), m2, tick.read.device_ptr(), dw, false, false)?;
            self.outer(words, g, bias, m2, 0, chart.device_ptr(), m2, 0, 0, false, false)?;
            self.transposed(words, weight, m2, dw, chart.device_ptr(), m2, dr.device_ptr(), true, false)?;
        }
        self.ratio_adjoint(words, tick.read.device_ptr(), tick.scale.device_ptr(), dr.device_ptr(), dmid.device_ptr(), dx.device_ptr(), false)?;
        Ok(())
    }

    /// The reverse's per-site and per-pair buffers of one level, the words pointed at those the kernels read.
    pub(crate) fn back_buffers(&self, field: &Field, words: &mut Words, sites: usize, pairs: usize, early_clocks: Option<(Pooled<'c, i128>, Pooled<'c, i128>)>) -> Result<Back<'c>> {
        let d = field.declaration;
        let (dw, m, n, f, heads) = (d.width, d.complex(), d.modes, d.contacts, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let dx = alloc64(sites * dw)?;
        let dr = alloc64(sites * dw)?;
        let dc = alloc64(sites * f)?;
        let da = alloc64(sites * f)?;
        let db = alloc64(sites * f)?;
        let dg = alloc64(if d.carry > 0 { sites * 2 * d.carry } else { 1 })?;
        // [theory, November 12; the triad record §4] The triads' covectors, `δc^T` `[t][2J]` and `δabg` `[t][6J]`, none without triads.
        let triad = |rows: usize| if d.triads > 0 { alloc64(sites * rows * d.triads).map(Some) } else { Ok(None) };
        let (dct, dabg) = (triad(2)?, triad(6)?);
        let ra = alloc64(sites * dw)?;
        let rb = alloc64(sites * dw)?;
        let dmid = alloc64(sites * dw)?;
        let dy = alloc64(sites * m2)?;
        let dyh = alloc64(heads * sites * span)?;
        let dq = alloc64(sites * m2)?;
        let dv = alloc64(sites * m2)?;
        // The probe role, its own chart's covector (§16.19).
        let dp = alloc64(sites * m2)?;
        words.dp = dp.device_ptr();
        // The contact's covector a pair, `|δs| < 2^dsbits` with `dsbits ≤ 63` (refused past it).
        let ds = self.timed(Kind::Alloc, || self.take::<i64>(pairs.max(1))).map_err(device)?;
        // The pair covectors `⟨δỹ_i, D ṽ_j⟩` the rows compute once for both passes, on 128 bits.
        let dpb = self.timed(Kind::Alloc, || self.take::<i128>(pairs.max(1))).map_err(device)?;
        words.dpb = dpb.device_ptr();
        // The crowds' difference arrays over the places `[site + region][span]`, for the values and for
        // the word (§14.10).
        let regions = words.r as usize;
        let rows = sites + regions;
        let cv = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((rows * span).max(1))).map_err(device)?;
        let cw = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((rows * span).max(1))).map_err(device)?;
        words.cv = cv.device_ptr();
        words.cw = cw.device_ptr();
        // The values' covector at the moment modes, summed over the ticks (§15.1).
        let dm = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((sites * m2).max(1))).map_err(device)?;
        // The clocks' covectors `[p][t]` (§16), the crowds' contact covectors the skins' return reads, and the probe
        // chart's unframed read a tick (the frames' return turns it).
        let paced = d.paced_heads();
        // [realization; G144] Where the opening was compared, the base clock's two covectors were taken zeroed at the end of its forward and hold its
        // return; they are the pass's own.
        let (gtau, gsig) = match early_clocks {
            Some(clocks) => clocks,
            None => (self.timed(Kind::Alloc, || self.take_zeroed::<i128>((paced * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take_zeroed::<i128>((paced * sites).max(1))).map_err(device)?),
        };
        let cds = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((heads * sites * words.slots as usize).max(1))).map_err(device)?;
        let pr_back = alloc64(sites * m2)?;
        words.gtau = gtau.device_ptr();
        words.gsig = gsig.device_ptr();
        words.cds = cds.device_ptr();
        Ok(Back { dx, dr, dc, da, db, dg, dct, dabg, ra, rb, dmid, dy, dyh, dq, dv, dp, ds, dpb, cv, cw, dm, gtau, gsig, cds, pr_back })
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn reverse(&self, field: &Field, words: &mut Words, ticks: &[Tick<'c>], (clocks, base_clock): (&[Option<CardClock<'c>>], [u64; 7]), g: &CardBuffer<'c, i128>, fread: &CardBuffer<'c, i32>, fscale: &CardBuffer<'c, i128>, lift: &CardBuffer<'c, i64>, masses: &CardBuffer<'c, u64>, totals: &CardBuffer<'c, i128>, classes: &[u32], unresolved: &[u8], site_pos: &[u32], mix_off: &[u32], mix_class: &[u32], mix_share: &[u32], site_weight: &[(u64, u64)], ported: &(Vec<u32>, Vec<i64>), sites: usize, pairs: usize, mut tower: Option<(&mut TowerRun<'c>, &TowerBatch<'c>)>, early_clocks: Option<(Pooled<'c, i128>, Pooled<'c, i128>)>, loud: Option<(&CardBuffer<'c, i128>, &CardBuffer<'c, i64>, &CardBuffer<'c, i64>)>) -> Result<()> {
        let card = self.card;
        let d = field.declaration;
        let (dw, m, n, f, a, heads) = (d.width, d.complex(), d.modes, d.contacts, d.alphabet, d.heads);
        let (m2, span) = (2 * m, 2 * n);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let dz = alloc64(sites * a)?;
        let back = self.back_buffers(field, words, sites, pairs, early_clocks)?;
        let Back { dx, dr, dc, da, db, ra, rb, dmid, dy, dyh, dq, dv, dp, ds, cv, cw, dm, gtau, gsig, cds, pr_back, .. } = &back;
        let regions = words.r as usize;
        let rows = sites + regions;
        let paced = d.paced_heads();
        // The face.
        let (mut mp, mut tp, mut dzp) = (masses.device_ptr(), totals.device_ptr(), dz.device_ptr());
        self.launch("field_face_covector", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut mp), arg(&mut tp), arg(&mut dzp)])?;
        // The covector weighed as each region's state in the joint code (§16.23, the host's `returned_with`).
        if site_weight.iter().any(|&(m, k)| m != k) {
            let (wm, wk): (Vec<u64>, Vec<u64>) = site_weight.iter().copied().unzip();
            let wm_c = self.timed(Kind::Copy, || self.take_up(&wm)).map_err(device)?;
            let wk_c = self.timed(Kind::Copy, || self.take_up(&wk)).map_err(device)?;
            let (mut wmp, mut wkp) = (wm_c.device_ptr(), wk_c.device_ptr());
            self.launch("field_face_weigh", Self::cells((sites * a) as u64), THREADS, &mut [arg(words), arg(&mut wmp), arg(&mut wkp), arg(&mut dzp)])?;
        }
        // A port's places take their coupling's covector (§16.24), read on the host.
        if !ported.0.is_empty() {
            let at_c = self.timed(Kind::Copy, || self.take_up(&ported.0)).map_err(device)?;
            let rows_c = self.timed(Kind::Copy, || self.take_up(&ported.1)).map_err(device)?;
            let (mut atp, mut rp, mut count) = (at_c.device_ptr(), rows_c.device_ptr(), ported.0.len() as u64);
            self.launch("field_face_set", Self::cells(count * a as u64), THREADS, &mut [arg(words), arg(&mut atp), arg(&mut rp), arg(&mut count), arg(&mut dzp)])?;
        }
        self.outer(words, g, words.read_bias, a, 0, dz.device_ptr(), a, 0, 0, false, true)?;
        // [Brandon, November 15 02:06Z] Through a loud face's sharpness (the host's `Field::loud_return`): `δv = rel(β δz, 16)` takes `δz`'s place
        // in the encoding's and the lift's covectors, `κ` and `b` take theirs, and the radial part is the base the chart's adjoint adds to.
        let (sharp_dz, radial) = match loud {
            Some((beta, lambda, plain)) => {
                let dzv = alloc64(sites * a)?;
                let radial = alloc64(sites * dw)?;
                let (mut at, mut dzp, mut vp, mut bp, mut lp, mut sp, mut rp, mut gp, mut dvp, mut radp) = (field.layout().loud as u64, dz.device_ptr(), plain.device_ptr(), beta.device_ptr(), lambda.device_ptr(), fscale.device_ptr(), fread.device_ptr(), g.device_ptr(), dzv.device_ptr(), radial.device_ptr());
                self.launch("field_loud_back", Self::cells(sites as u64), THREADS, &mut [arg(words), arg(&mut at), arg(&mut dzp), arg(&mut vp), arg(&mut bp), arg(&mut lp), arg(&mut sp), arg(&mut rp), arg(&mut gp), arg(&mut dvp), arg(&mut radp)])?;
                (Some(dzv), Some(radial))
            }
            None => (None, None),
        };
        let dz_face = sharp_dz.as_ref().map_or(dz.device_ptr(), |b| b.device_ptr());
        // Through the encoding (§16.26, the host's `returned_with`): `δE(a)_i += Σ_t rel(δz_a y_i, 16)`, `δy = rel(Σ_a δz_a E(a), 16)`,
        // then the lift's own return.
        let dyl = alloc64(sites * dw)?;
        {
            let (mut gp, mut enc, mut dzp, mut yp, mut dyp) = (g.device_ptr(), words.enc, dz_face, lift.device_ptr(), dyl.device_ptr());
            let tiles = (sites as u64).div_ceil(64);
            self.launch("field_tied_back_e", Self::cells(a as u64 * dw as u64 * tiles), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut enc), arg(&mut dzp), arg(&mut yp)])?;
            let mut enc = words.enc;
            self.launch("field_tied_back_y", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut enc), arg(&mut dzp), arg(&mut dyp)])?;
        }
        let lift_bias = field.layout().lift_bias as u64;
        self.outer(words, g, lift_bias, dw, 0, dyl.device_ptr(), dw, 0, 0, false, true)?;
        self.outer(words, g, words.read, dw, dw, dyl.device_ptr(), dw, fread.device_ptr(), dw, false, true)?;
        self.transposed(words, words.read, dw, dw, dyl.device_ptr(), dw, dr.device_ptr(), false, true)?;
        self.ratio_adjoint(words, fread.device_ptr(), fscale.device_ptr(), dr.device_ptr(), radial.as_ref().map_or(0, |b| b.device_ptr()), dx.device_ptr(), true)?;
        // A tower's packets' reverse buffers, beside the fine field's.
        let cback = match (tower.as_mut(), field.scale.as_deref()) {
            (Some((tr, tb)), Some(s)) => Some(self.back_buffers(&s.coarse, &mut tr.cwords, tb.st.sites, tb.st.pairs, None)?),
            _ => None,
        };
        // [§16.44] One set of the clocks' and moments' covectors a clock: the pass's (the first tick and the opening), and
        // each tick's own where its blanks ran at the faces the tick before gave them.
        let own: Vec<Option<[Pooled<'c, i128>; 3]>> = clocks
            .iter()
            .map(|c| {
                c.as_ref()
                    .map(|_| -> Result<[Pooled<'c, i128>; 3]> {
                        let zeroed = |len: usize| self.timed(Kind::Alloc, || self.take_zeroed::<i128>(len.max(1))).map_err(device);
                        Ok([zeroed(sites * m2)?, zeroed(paced * sites)?, zeroed(paced * sites)?])
                    })
                    .transpose()
            })
            .collect::<Result<_>>()?;
        let covectors = |at: usize| -> [u64; 3] { own.get(at).and_then(Option::as_ref).map_or([dm.device_ptr(), gtau.device_ptr(), gsig.device_ptr()], |b| [b[0].device_ptr(), b[1].device_ptr(), b[2].device_ptr()]) };
        for (at, tick) in ticks.iter().enumerate().rev() {
            set_clock(words, clocks.get(at).and_then(Option::as_ref), base_clock);
            let [dmp, gtp, gsp] = covectors(at);
            (words.gtau, words.gsig) = (gtp, gsp);
            self.tick_back(field, words, tick, at, g, &back, dmp, sites, true)?;
            if let (Some((tr, tb)), Some(cb)) = (tower.as_mut(), cback.as_ref()) {
                if at == tr.split {
                    self.tower_back(field, words, tr, tb, &back, cb)?;
                }
            }
            // [§16.44] A tick's own clock was read off the state this tick began from: its moments and rates return now,
            // and each blank's clock returns through its face into that state's covector (the host's `clock_return`).
            if let Some(clock) = clocks.get(at).and_then(Option::as_ref) {
                self.moments_return_at(field, words, g, dmp, regions, sites)?;
                if paced > 0 {
                    // [realization; theory, November 13, P58 item 2] Unzeroed: `field_pace_kappa_back` writes every `(paced head, site)` word, each
                    // region's sites from its last to its first, before `field_pace_c_back` and `field_blank_dz` read them.
                    let dkappa = self.timed(Kind::Alloc, || self.take::<i128>((paced * sites).max(1))).map_err(device)?;
                    let (mut dkp, mut gp) = (dkappa.device_ptr(), g.device_ptr());
                    self.launch("field_pace_kappa_back", Self::cells((paced * regions) as u64), THREADS, &mut [arg(words), arg(&mut dkp)])?;
                    self.launch("field_pace_c_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dkp), arg(&mut gp)])?;
                    self.blank_back(field, words, clock, &dkappa, g, dx, sites)?;
                }
            }
        }
        set_clock(words, None, base_clock);
        (words.gtau, words.gsig) = (gtau.device_ptr(), gsig.device_ptr());
        // The moment's chart into the face (§16.22, the host's `returned_with`): `δC += Σ_t δx⁰_t s_tᵀ`, `δb += Σ_t δx⁰_t`,
        // and the moments' covector `δs_t += Cᵀ δx⁰_t` (formed in `dq`, free past the ticks) joined to the values' and probes'.
        let (mface, mface_bias, _) = moment_face(field);
        self.outer(words, g, mface_bias, dw, 0, dx.device_ptr(), dw, 0, 0, false, false)?;
        self.outer(words, g, mface, dw, m2, dx.device_ptr(), dw, words.moment, m2, true, false)?;
        self.transposed(words, mface, dw, m2, dx.device_ptr(), dw, dq.device_ptr(), false, false)?;
        let (mut cp, mut dmp) = (dq.device_ptr(), dm.device_ptr());
        self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp), arg(&mut dmp)])?;
        // The moments' return (§15.1): each moment mode's value covector, summed over the ticks that read one clock,
        // through the strands to the families on that clock (the host's `moments_return`); then the clocks return to
        // their paces (§16, §16.16): `δκ` by suffix sums, then `δc[u] += Σ_(u_t = u) δκ_t` on the class sheet, a blank's by
        // the shares of the face its clock read (§16.44); the opening takes nothing.
        {
            let [dmp, gtp, gsp] = [dm.device_ptr(), gtau.device_ptr(), gsig.device_ptr()];
            set_clock(words, None, base_clock);
            (words.gtau, words.gsig) = (gtp, gsp);
            self.moments_return_at(field, words, g, dmp, regions, sites)?;
            if paced > 0 {
                // [P58 item 2] Unzeroed, as each tick's: `field_pace_kappa_back` writes every word before `field_pace_c_back` reads it.
                let dkappa = self.timed(Kind::Alloc, || self.take::<i128>((paced * sites).max(1))).map_err(device)?;
                let (mut dkp, mut gp) = (dkappa.device_ptr(), g.device_ptr());
                self.launch("field_pace_kappa_back", Self::cells((paced * regions) as u64), THREADS, &mut [arg(words), arg(&mut dkp)])?;
                self.launch("field_pace_c_back", Self::cells((paced * sites) as u64), THREADS, &mut [arg(words), arg(&mut dkp), arg(&mut gp)])?;
            }
        }
        set_clock(words, None, base_clock);
        (words.gtau, words.gsig) = (gtau.device_ptr(), gsig.device_ptr());
        // The opening: each site's row of the encoding and its strand neighbours' rows of theirs (a
        // carried site's mixture by its shares), the entries partitioned by row once for each encoding
        // (a neighbour only within the site's region: the next site is the region's own when its place
        // is not the first). A plain row is a share of `2^16`.
        let terms = |s: usize, t: u32| -> Vec<(usize, u32, u32)> {
            let (from, to) = (mix_off[s] as usize, mix_off[s + 1] as usize);
            if from == to {
                return vec![(if unresolved[s] != 0 { a } else { classes[s] as usize }, t, 1 << STATE_BITS)];
            }
            (from..to).map(|k| (mix_class[k] as usize, t, mix_share[k])).collect()
        };
        let own: Vec<(usize, u32, u32)> = (0..sites).flat_map(|t| terms(t, t as u32)).collect();
        let before: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| site_pos[t] > 0).flat_map(|t| terms(t - 1, t as u32)).collect();
        let after: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| t + 1 < sites && site_pos[t + 1] > 0).flat_map(|t| terms(t + 1, t as u32)).collect();
        for (base, rows) in [(words.enc, own), (words.enc_before, before), (words.enc_after, after)] {
            let (rows_sites, rows_shares, segments) = encoding_partition(&rows, a + 1);
            let count = (segments.len() / 3) as u32;
            if count == 0 {
                continue;
            }
            let rows_sites_c = self.timed(Kind::Copy, || self.take_up(&rows_sites)).map_err(device)?;
            let rows_shares_c = self.timed(Kind::Copy, || self.take_up(&rows_shares)).map_err(device)?;
            let segments_c = self.timed(Kind::Copy, || self.take_up(&segments)).map_err(device)?;
            let (mut gp, mut dxp, mut rsp, mut rwp, mut sgp, mut count, mut base) = (g.device_ptr(), dx.device_ptr(), rows_sites_c.device_ptr(), rows_shares_c.device_ptr(), segments_c.device_ptr(), count, base);
            self.launch("field_encoding", Self::cells(count as u64 * dw as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut rsp), arg(&mut rwp), arg(&mut sgp), arg(&mut count), arg(&mut base)])?;
        }
        // [definition; agent-inferred, November 14, the ring record §4] **The mark's return** (the host's `Field::opening_return` at a marked site):
        // on a field's second read each silent site's rows above gave its open row `dx`; its mark adds `−release(α_b dx, 24)` there, each class's
        // `release(w_c release(α_b dx, 24), 16)` and the strength's `Σ_i dx_i Δ_i`, in every encoding its row enters (`field_mark_back`, then
        // `field_mark_rows` over the kept `release(α_b dx, 24)`).
        if words.mark_share != 0 {
            let marked: Vec<u32> = (0..sites).filter(|&s| unresolved[s] != 0 && mix_off[s] == mix_off[s + 1]).map(|s| s as u32).collect();
            if !marked.is_empty() {
                let count = marked.len();
                let marked_c = self.timed(Kind::Copy, || self.take_up(&marked)).map_err(device)?;
                // Unzeroed: `field_mark_back` writes every word `[b][k][i]` before `field_mark_rows` reads it.
                let adx = alloc64(3 * count * dw)?;
                let (mut gp, mut dxp, mut mp, mut cnt, mut ap) = (g.device_ptr(), dx.device_ptr(), marked_c.device_ptr(), count as u32, adx.device_ptr());
                self.launch("field_mark_back", Self::cells((count * dw) as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut dxp), arg(&mut mp), arg(&mut cnt), arg(&mut ap)])?;
                self.launch("field_mark_rows", Self::cells((3 * (a + 1) * dw * count.div_ceil(64)) as u64), THREADS, &mut [arg(words), arg(&mut gp), arg(&mut mp), arg(&mut cnt), arg(&mut ap)])?;
            }
        }
        Ok(())
    }
}
