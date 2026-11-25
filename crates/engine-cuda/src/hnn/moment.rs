//! **The source moment and the opening's cavity, on the card.** The launches of the host's moments and of the cavity opening
//! (`crates/engine/src/moment.rs` and `field/moment.rs`, whose first lines state the equations, the kind and the Lean and atlas
//! owners), with the moment kernels' words, one a mode. THE_ENGINE §3 lists each kernel beside the phase it serves, and the host is the
//! reference these bits are read against (`athena parity`).

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

/// The threads a moment scan's block carries (a power of two, `kernels/field_moment.cuh`).
pub(crate) const MOMENT_BLOCK: u32 = 256;

/// The moment's chart into the face (§16.22, [`holonics_engine::field::Loci::moment_face`]): its offset in
/// the material, its bias's, and its reach `max |C|` (the affine's carrier bound).
pub(crate) fn moment_face(field: &Constitution) -> (u64, u64, u64) {
    let (l, d) = (field.layout(), field.declaration);
    let len = d.width * 2 * d.complex();
    let reach = field.theta[l.moment_face..l.moment_face + len].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
    (l.moment_face as u64, l.moment_face_bias as u64, reach)
}

/// [the lead, November 25] The second fades' chart into the face (the host's `Loci::twin_face`): its offset in the material and its reach
/// `max |C′|`. No bias.
pub(crate) fn twin_face(field: &Constitution) -> (u64, u64) {
    let (l, d) = (field.layout(), field.declaration);
    let len = d.width * 2 * d.complex();
    let reach = field.theta[l.twin_face..l.twin_face + len].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
    (l.twin_face as u64, reach)
}

/// [realization; theory, November 13, P60 item 2] **The standing moments' operands, kept for the cavity's**: every moment mode's strands and their
/// exact prefixes, the forward's admission flags and the modes' words (`moments` with `keep`), which the cavity moments read at their standing
/// phases and the cavity's clock covector reads again.
pub(crate) struct MomentKeep<'c> {
    pub(crate) before: Pooled<'c, i64>,
    pub(crate) after: Pooled<'c, i64>,
    pub(crate) up: Pooled<'c, i128>,
    pub(crate) down: Pooled<'c, i128>,
    pub(crate) _ok: Pooled<'c, u8>,
    pub(crate) ws: Pooled<'c, u64>,
    pub(crate) cmap: Pooled<'c, u32>,
}

/// [realization; theory, November 13, P60 item 2] **The opening's comparison's forward on the card** (the host's `Constitution::cavity_forward` and
/// `Constitution::opening_read` at every compared place), kept for its return and its codes: the compared places (`mask`, the words' open-site mask while
/// the opening is read), the cavity moments `[t][2M]` and their two sides `[u][t]`, the cavity openings, their charts, lifts and faces.
pub(crate) struct Opening<'c> {
    /// The places the forward reads (held for its memory: the forward's kernels read it).
    pub(crate) _mask: Pooled<'c, u8>,
    /// [the lead, November 23] The places compared: the mask less the places read and not compared (`Resident::strand_skip`), whose
    /// faces the forward still reads (the level's news reads them) and whose covector and codes are none.
    pub(crate) compare: Pooled<'c, u8>,
    pub(crate) keep: Option<MomentKeep<'c>>,
    pub(crate) cmoment: Pooled<'c, i64>,
    pub(crate) sb: Pooled<'c, i64>,
    pub(crate) sa: Pooled<'c, i64>,
    pub(crate) read: Pooled<'c, i32>,
    pub(crate) scale: Pooled<'c, i128>,
    pub(crate) lift: Pooled<'c, i64>,
    pub(crate) masses: Pooled<'c, u64>,
    pub(crate) totals: Pooled<'c, i128>,
    /// [the lead, November 25] The cavity at the rings' second fades ([`SecondFade`]): their kept operands, cavity moments and two sides.
    pub(crate) second: Option<Box<StrandBase<'c>>>,
}

impl<'c> Resident<'c> {

    /// [the lead, November 25] **The second fades' words** ([`SecondFade`]): the words with the second decays, skin denominators and rates of
    /// fade, the covector's second fades and the base clock's second skin addresses, skins and moments in place of the first's; none where the
    /// field holds no second fade. Every other word (the clock, the phases, the strands' encodings, the covectors of the clock) is the words'.
    pub(crate) fn second_words(&self, words: &Words) -> Option<Words> {
        self.second_fade.get().map(|s| Words { decay: s.decay, skin_k: s.skin_k, skin_b: s.skin_b, gfade: s.gfade, saddr: s.saddr, mskin: s.mskin, cskin: s.cskin, moment: s.moment, ..*words })
    }

    /// [realization; theory, November 13, P60 item 2] **The opening's comparison's forward** (the host's `Constitution::cavity_forward` and
    /// `Constitution::opening_read`): the cavity moments from the standing moments' kept operands (`field_cavity_moment_all`), the cavity openings
    /// (`field_cavity_open`, then the moment's chart on the cavity moment), and at every compared place the lane chart, the opening's lift `R⁰ r̂ + b⁰`,
    /// the face through the encoding and its masses, by the field's own entries with the words' open-site mask set to the compared places. Every
    /// word a later kernel reads is written first: the cavity moment is zeroed (its still modes stay zero), the chart, the lift and the face are read
    /// at the compared places alone. Launches a batch: one, two and the moment's chart's, then the chart, the lift, `tied` and the face.
    /// [realization; theory, November 13, P60 item 2; cut out on November 18 for the strand's second stream] **The cavity moments' forward**
    /// (`field_cavity_moment_all`): the cavity moments `[t][2M]` (zeroed, their still modes stay zero) and their two sides `[u][t]`, from the
    /// standing moments' kept operands; zero moments where none were kept (a field with no moment mode).
    #[allow(clippy::type_complexity)]
    pub(crate) fn cavity_forward(&self, field: &Constitution, words: &Words, regions: usize, sites: usize, keep: Option<&MomentKeep<'c>>) -> Result<(Pooled<'c, i64>, Pooled<'c, i64>, Pooled<'c, i64>)> {
        let d = field.declaration;
        let (m2, tm) = (2 * d.complex(), d.moment_modes());
        let cmoment = self.timed(Kind::Alloc, || self.take_zeroed::<i64>((sites * m2).max(1))).map_err(device)?;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let (sb, sa) = (alloc64(tm * 2 * sites)?, alloc64(tm * 2 * sites)?);
        if let Some(k) = keep {
            let (mut wsp, mut cmp, mut fw) = (k.ws.device_ptr(), k.cmap.device_ptr(), *words);
            let (mut bp, mut ap, mut upp, mut dnp) = (k.before.device_ptr(), k.after.device_ptr(), k.up.device_ptr(), k.down.device_ptr());
            let (mut sbp, mut sap, mut cp) = (sb.device_ptr(), sa.device_ptr(), cmoment.device_ptr());
            let (mut stride, mut pre_stride) = ((2 * sites) as u64, (2 * (sites + regions)) as u64);
            self.launch_grid("field_cavity_moment_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut upp), arg(&mut dnp), arg(&mut sbp), arg(&mut sap), arg(&mut cp), arg(&mut stride), arg(&mut pre_stride)])?;
        }
        Ok((cmoment, sb, sa))
    }

    pub(crate) fn opening_forward(&self, field: &Constitution, words: &mut Words, regions: &[Region], st: &Staged<'c>, keep: Option<MomentKeep<'c>>, keep_second: Option<Option<MomentKeep<'c>>>) -> Result<Opening<'c>> {
        let d = field.declaration;
        let (dw, m2, a, sites, tm, lanes) = (d.width, 2 * d.complex(), d.alphabet, st.sites, d.moment_modes(), d.lanes);
        let _ = tm;
        let l = field.layout();
        // [the strand's two streams] In a passage read by two streams the compared places are the known stream's (`Resident::strand_heard`).
        let heard = self.strand_heard.borrow().clone();
        // [the lead, November 23] A place read and not compared (`Resident::strand_skip`) is read (its face is the level's news there) and is no
        // compared place of the opening: it leaves `compare`, which the covector and the codes read.
        let skip = self.strand_skip.borrow().clone();
        let mut mask = vec![0u8; sites.max(1)];
        let mut compare_mask = vec![0u8; sites.max(1)];
        for (r, region) in regions.iter().enumerate() {
            let first = st.region_off[r] as usize;
            let end = heard.get(r).map_or(region.port.map_or(region.classes.len(), |p| p.start), |&n| n as usize);
            mask[first..first + end].fill(1);
            compare_mask[first..first + end].fill(1);
            if let Some(k) = skip.get(r).filter(|_| heard.len() == regions.len()) {
                for (t, _) in k.iter().enumerate().filter(|&(t, &s)| s && t < end) {
                    compare_mask[first + t] = 0;
                }
            }
        }
        let mask = self.timed(Kind::Copy, || self.take_up(&mask)).map_err(device)?;
        let compare = self.timed(Kind::Copy, || self.take_up(&compare_mask)).map_err(device)?;
        let (cmoment, sb, sa) = self.cavity_forward(field, words, regions.len(), sites, keep.as_ref())?;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let cx = alloc64(sites * dw)?;
        let mut cxp = cx.device_ptr();
        self.launch("field_cavity_open", Self::cells((sites * dw) as u64), THREADS, &mut [arg(words), arg(&mut cxp)])?;
        let (mface, mface_bias, rmface) = moment_face(field);
        self.affine("field_affine_x64", words, mface, mface_bias, rmface, dw, m2, cmoment.device_ptr(), m2, 0, dw, cx.device_ptr(), false)?;
        // [the lead, November 25] The second fades' cavity moments and their chart on the cavity openings (the host's `cavity_forward_sided`).
        let second = match (self.second_words(words), keep_second) {
            (Some(w2), Some(keep2)) => {
                let (cm2, sb2, sa2) = self.cavity_forward(field, &w2, regions.len(), sites, keep2.as_ref())?;
                let (tface, rtface) = twin_face(field);
                self.affine("field_affine_x64", words, tface, u64::MAX, rtface, dw, m2, cm2.device_ptr(), m2, 0, dw, cx.device_ptr(), false)?;
                Some(Box::new(StrandBase { keep: keep2, cmoment: cm2, sb: sb2, sa: sa2, second: None }))
            }
            _ => None,
        };
        let mut cw = *words;
        cw.unresolved = mask.device_ptr();
        let read = self.timed(Kind::Alloc, || self.take::<i32>((sites * dw).max(1))).map_err(device)?;
        let scale = self.timed(Kind::Alloc, || self.take::<i128>((sites * lanes).max(1))).map_err(device)?;
        self.chart(&mut cw, cx.device_ptr(), &read, &scale, true)?;
        let reach = field.theta[l.opening..l.opening + dw * dw].iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0);
        let lift = alloc64(sites * dw)?;
        self.affine("field_affine_x32", &mut cw, l.opening as u64, l.opening_bias as u64, reach, dw, dw, read.device_ptr(), dw, lift.device_ptr(), dw, 0, true)?;
        let z = alloc64(sites * a)?;
        {
            let (mut enc, mut cb, mut yp, mut zp) = (cw.enc, cw.read_bias, lift.device_ptr(), z.device_ptr());
            self.launch("field_tied_face_tiled", Self::map_grid(a, sites), THREADS, &mut [arg(&mut cw), arg(&mut enc), arg(&mut cb), arg(&mut yp), arg(&mut zp)])?;
        }
        let masses = self.timed(Kind::Alloc, || self.take::<u64>((sites * a).max(1))).map_err(device)?;
        let totals = self.timed(Kind::Alloc, || self.take::<i128>(sites.max(1))).map_err(device)?;
        let (mut zp, mut mp, mut tp) = (z.device_ptr(), masses.device_ptr(), totals.device_ptr());
        self.launch("field_face", Self::warps(sites as u64), THREADS, &mut [arg(&mut cw), arg(&mut zp), arg(&mut mp), arg(&mut tp)])?;
        self.mark("opening_forward");
        Ok(Opening { _mask: mask, compare, keep, cmoment, sb, sa, read, scale, lift, masses, totals, second })
    }

    /// [realization; theory, November 13, P60 item 2] **The opening's comparison's return** (the host's `Constitution::opening_compare_return`): at every
    /// compared place the face covector at unit gain, through the class biases, the encoding (`tied`), the opening's lift and bias, the chart and its
    /// lanes, by the field's own entries under the compared places' mask; the cavity opening's covector into the unresolved row and the neighbours'
    /// strand rows (`field_encoding`), the moment's chart and bias, and the cavity moments' covector through their return and their clocks
    /// (`field_cavity_terms_all` and `field_cavity_scan_all`, `field_cavity_return_paced_all`, `field_cavity_pace_back_all`), added into `g` and into the pass's clock covectors
    /// the words name.
    #[allow(clippy::type_complexity)]
    pub(crate) fn opening_back(&self, field: &Constitution, words: &mut Words, op: &Opening<'c>, g: &CardBuffer<'c, i128>, (classes, unresolved, site_pos, mix_off, mix_class, mix_share): (&[u32], &[u8], &[u32], &[u32], &[u32], &[u32]), sites: usize) -> Result<()> {
        let d = field.declaration;
        let (dw, m2, a, tm) = (d.width, 2 * d.complex(), d.alphabet, d.moment_modes());
        let l = field.layout();
        let mut cw = *words;
        cw.unresolved = op.compare.device_ptr();
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let zeroed64 = |len: usize| self.timed(Kind::Alloc, || self.take_zeroed::<i64>(len.max(1))).map_err(device);
        // The face's covector at unit gain (no domain weighs it), written at every cell (zero past the compared places).
        let dz = alloc64(sites * a)?;
        let (mut mp, mut tp, mut dzp) = (op.masses.device_ptr(), op.totals.device_ptr(), dz.device_ptr());
        self.launch("field_face_covector", Self::cells((sites * a) as u64), THREADS, &mut [arg(&mut cw), arg(&mut mp), arg(&mut tp), arg(&mut dzp)])?;
        self.outer(&mut cw, g, words.read_bias, a, 0, dz.device_ptr(), a, 0, 0, false, true)?;
        let dy = alloc64(sites * dw)?;
        {
            let (mut gp, mut enc, mut dzp, mut yp, mut dyp) = (g.device_ptr(), cw.enc, dz.device_ptr(), op.lift.device_ptr(), dy.device_ptr());
            let tiles = (sites as u64).div_ceil(BLANK_TILE);
            self.launch("field_tied_back_e", Self::cells(a as u64 * dw as u64 * tiles), THREADS, &mut [arg(&mut cw), arg(&mut gp), arg(&mut enc), arg(&mut dzp), arg(&mut yp)])?;
            let mut enc = cw.enc;
            self.launch("field_tied_back_y_tiled", Self::map_grid(dw, sites), THREADS, &mut [arg(&mut cw), arg(&mut enc), arg(&mut dzp), arg(&mut dyp)])?;
        }
        self.outer_biased(&mut cw, g, l.opening as u64, l.opening_bias as u64, dw, dw, dy.device_ptr(), dw, op.read.device_ptr(), dw, false, true)?;
        let dr = alloc64(sites * dw)?;
        self.transposed(&mut cw, l.opening as u64, dw, dw, dy.device_ptr(), dw, dr.device_ptr(), false, true)?;
        let dx = zeroed64(sites * dw)?;
        self.ratio_adjoint(&mut cw, op.read.device_ptr(), op.scale.device_ptr(), dr.device_ptr(), 0, dx.device_ptr(), true)?;
        // The cavity opening's rows: the unresolved row for every compared place, its neighbours' rows of theirs (a carried neighbour's mixture by
        // its shares), the entries partitioned by row once for each encoding, as the reverse's opening.
        let mask = self.timed(Kind::Copy, || self.card.fetch_range(&op.compare, 0, sites)).map_err(device)?;
        let terms = |s: usize, t: u32| -> Vec<(usize, u32, u32)> {
            let (from, to) = (mix_off[s] as usize, mix_off[s + 1] as usize);
            if from == to {
                return vec![(if unresolved[s] != 0 { a } else { classes[s] as usize }, t, 1 << STATE_BITS)];
            }
            (from..to).map(|k| (mix_class[k] as usize, t, mix_share[k])).collect()
        };
        let compared = |t: usize| mask[t] != 0;
        let own: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| compared(t)).map(|t| (a, t as u32, 1 << STATE_BITS)).collect();
        let before: Vec<(usize, u32, u32)> = (0..sites).filter(|&t| compared(t) && site_pos[t] > 0).flat_map(|t| terms(t - 1, t as u32)).collect();
        // [the known stream] No after row was read (`FieldWords::before`), and none takes a covector.
        // [the record of the two streams §15] With the word the compared (known) places' retarded openings read the row of the second site before.
        let after: Vec<(usize, u32, u32)> = if words.before >= 3 {
            (0..sites).filter(|&t| compared(t) && site_pos[t] >= 2).flat_map(|t| terms(t - 2, t as u32)).collect()
        } else {
            (0..sites).filter(|&t| words.before == 0 && compared(t) && t + 1 < sites && site_pos[t + 1] > 0).flat_map(|t| terms(t + 1, t as u32)).collect()
        };
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
        // The moment's chart on the cavity moment: `δC += Σ_t δx_t s_tᵀ`, `δb += Σ_t δx_t`, `δs_t = Cᵀ δx_t` (zero past the compared places).
        let (mface, mface_bias, _) = moment_face(field);
        self.outer_biased(&mut cw, g, mface, mface_bias, dw, m2, dx.device_ptr(), dw, op.cmoment.device_ptr(), m2, true, true)?;
        let dq = zeroed64(sites * m2)?;
        self.transposed(&mut cw, mface, dw, m2, dx.device_ptr(), dw, dq.device_ptr(), false, true)?;
        let Some(k) = op.keep.as_ref().filter(|_| tm > 0) else {
            return Ok(());
        };
        let dm = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((sites * m2).max(1))).map_err(device)?;
        let (mut cp, mut dmp) = (dq.device_ptr(), dm.device_ptr());
        self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp), arg(&mut dmp)])?;
        self.cavity_back(field, words, k, &op.sb, &op.sa, &dm, g, sites)?;
        // [the lead, November 25] The second fades' chart on their cavity moments (the host's `opening_compare_return`): `δC′ += Σ_t δx_t s′_tᵀ`,
        // `δs′_t = C′ᵀ δx_t`, returned through the second cavity at the second skins into `g`, the clocks' covectors and the second fades.
        if let (Some(sc), Some(w2)) = (op.second.as_deref(), self.second_words(words)) {
            let (tface, _) = twin_face(field);
            self.outer_biased(&mut cw, g, tface, u64::MAX, dw, m2, dx.device_ptr(), dw, sc.cmoment.device_ptr(), m2, true, true)?;
            let dq2 = zeroed64(sites * m2)?;
            self.transposed(&mut cw, tface, dw, m2, dx.device_ptr(), dw, dq2.device_ptr(), false, true)?;
            let dm2 = self.timed(Kind::Alloc, || self.take_zeroed::<i128>((sites * m2).max(1))).map_err(device)?;
            let (mut cp, mut dmp) = (dq2.device_ptr(), dm2.device_ptr());
            self.launch("field_moment_accumulate", Self::cells((sites * m2) as u64), THREADS, &mut [arg(words), arg(&mut cp), arg(&mut dmp)])?;
            if let Some(k2) = sc.keep.as_ref() {
                self.cavity_back(field, &w2, k2, &sc.sb, &sc.sa, &dm2, g, sites)?;
            }
        }
        self.mark("opening_back");
        Ok(())
    }

    /// [realization; theory, November 13, P60 item 2; cut out on November 18 for the strand's second stream] **The cavity moments' return**
    /// (the host's `Constitution::cavity_moments_return`): from the cavity moments' covector `dm` (`[t][2M]`, 128 bits), each moment mode's
    /// covector, admitted by the return's certificate, its released prefix and the cavity's far prefixes, the return at every site into the
    /// strands' rows (`g`), then the clocks' covector (the words' `gtau`, `gsig`), on the forward's kept operands and the cavity moments'
    /// two sides.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn cavity_back(&self, field: &Constitution, words: &Words, k: &MomentKeep<'c>, sb: &CardBuffer<'c, i64>, sa: &CardBuffer<'c, i64>, dm: &CardBuffer<'c, i128>, g: &CardBuffer<'c, i128>, sites: usize) -> Result<()> {
        let d = field.declaration;
        let tm = d.moment_modes();
        if tm == 0 {
            return Ok(());
        }
        let l = field.layout();
        let regions = words.r as usize;
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let (strand, prefix) = ((2 * sites) as u64, (2 * (sites + regions)) as u64);
        let ds = alloc64(tm * 2 * sites)?;
        let q = self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?;
        let (d_before, d_after) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?);
        let ok = self.timed(Kind::Alloc, || self.take_up(&vec![0u8; (tm * regions).max(1)])).map_err(device)?;
        let (ws, cmap) = self.moment_modes(field, words, regions, sites, &ok)?;
        let (mut wsp, mut cmp, mut dmp) = (ws.device_ptr(), cmap.device_ptr(), dm.device_ptr());
        let (mut dsp, mut qp, mut dbp, mut dap, mut gp, mut none) = (ds.device_ptr(), q.device_ptr(), d_before.device_ptr(), d_after.device_ptr(), g.device_ptr(), 0u64);
        let (mut w2, mut base_b, mut base_a, mut tm32) = (*words, l.moment_before as u64, l.moment_after as u64, tm as u32);
        let (mut one32, mut stride, mut pre_stride) = (1u32, strand, prefix);
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        self.launch("field_moment_ds_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut dmp), arg(&mut cmp), arg(&mut tm32), arg(&mut dsp)])?;
        let mut fw = *words;
        self.launch_grid("field_moment_admit_paced_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut none), arg(&mut stride), arg(&mut one32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut qp), arg(&mut stride), arg(&mut pre_stride), arg(&mut one32)])?;
        let levels = (2u32..).take_while(|&lv| (1usize << lv) < d.reach).count() as u32;
        let sk_stride = (2 * levels as usize * 2 * (sites + regions)) as u64;
        // [realization; G143] The far prefixes are taken a moment mode at a time: one mode's prefixes (`sk_stride` words) serve every mode in turn,
        // each mode's terms, scan and return launched on its own words (`MomentWords` of 88 octets, its covector, prefix and return at its
        // offsets), so the return's scratch holds one mode's 1/tm of the prefixes every mode would hold at once. The same words and sums.
        let sk = self.timed(Kind::Alloc, || self.take::<i128>((sk_stride as usize).max(1))).map_err(device)?;
        let (mut skp, mut sk_stride_a, mut levels_a, mut one) = (sk.device_ptr(), sk_stride, levels, 1u32);
        for u in 0..tm as u64 {
            let (mut wsu, mut cmu, mut dsu, mut qu, mut dbu, mut dau) = (wsp + 88 * u, cmp + 4 * u, dsp + 8 * stride * u, qp + 16 * pre_stride * u, dbp + 16 * stride * u, dap + 16 * stride * u);
            if levels > 0 {
                // [realization; G141] The far prefixes' terms a thread each, then their scan a warp a row and region.
                self.launch("field_cavity_terms_all", Self::cells((2 * levels as usize * sites) as u64), THREADS, &mut [arg(&mut wsu), arg(&mut cmu), arg(&mut fw), arg(&mut dsu), arg(&mut skp), arg(&mut stride), arg(&mut sk_stride_a), arg(&mut levels_a), arg(&mut one)])?;
                self.launch("field_cavity_scan_all", Self::warps((2 * levels as usize * regions) as u64), THREADS, &mut [arg(&mut wsu), arg(&mut cmu), arg(&mut fw), arg(&mut skp), arg(&mut sk_stride_a), arg(&mut levels_a), arg(&mut one)])?;
            }
            self.launch_grid("field_cavity_return_paced_all", Dim3 { x: Self::cells(sites as u64), y: 1, z: 1 }, THREADS, 0, &mut [arg(&mut wsu), arg(&mut cmu), arg(&mut fw), arg(&mut dsu), arg(&mut qu), arg(&mut skp), arg(&mut dbu), arg(&mut dau), arg(&mut stride), arg(&mut pre_stride), arg(&mut sk_stride_a)])?;
        }
        self.launch("field_moment_strand_return_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut dbp), arg(&mut dap), arg(&mut gp)])?;
        let (mut bp, mut ap, mut upp, mut dnp) = (k.before.device_ptr(), k.after.device_ptr(), k.up.device_ptr(), k.down.device_ptr());
        let (mut sbp, mut sap) = (sb.device_ptr(), sa.device_ptr());
        self.launch_grid("field_cavity_pace_back_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut sbp), arg(&mut sap), arg(&mut dsp), arg(&mut dbp), arg(&mut dap), arg(&mut upp), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride)])?;
        let _ = &mut none;
        Ok(())
    }

    /// [definition; agent-inferred, November 1] **The site moments of a batch** (§15.1; the host's
    /// `Constitution::moments_of`, [`holonics_engine::field::moment`]), every moment mode (a turned head that
    /// is turned, each of its modes) in the same launches: the strands' encodings of each mode's ring
    /// slot gathered at every site (`field_moment_strands_all`), admitted by the l1 certificate, scanned to
    /// the prefix sums and read at every site (`kernels/field_moment.cuh` through its `_all` entries, a mode
    /// to a grid row), and placed at the unframed value's modes.
    pub(crate) fn moments(&self, field: &Constitution, words: &Words, regions: usize, sites: usize, keep: bool) -> Result<Option<MomentKeep<'c>>> {
        let d = field.declaration;
        let tm = d.moment_modes();
        if tm == 0 {
            return Ok(None);
        }
        let (n, l) = (d.modes, field.layout());
        let (strand, prefix) = ((2 * sites) as u64, (2 * (sites + regions)) as u64);
        let alloc64 = |len: usize| self.timed(Kind::Alloc, || self.take::<i64>(len.max(1))).map_err(device);
        let (before, after, s) = (alloc64(tm * 2 * sites)?, alloc64(tm * 2 * sites)?, alloc64(tm * 2 * sites)?);
        let (up, down) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?);
        let ok = self.timed(Kind::Alloc, || self.take_up(&vec![0u8; (tm * regions).max(1)])).map_err(device)?;
        let (ws, cmap) = self.moment_modes(field, words, regions, sites, &ok)?;
        let (mut wsp, mut cmp) = (ws.device_ptr(), cmap.device_ptr());
        let (mut bp, mut ap, mut sp, mut upp, mut dnp, mut none) = (before.device_ptr(), after.device_ptr(), s.device_ptr(), up.device_ptr(), down.device_ptr(), 0u64);
        let (mut w2, mut base_b, mut base_a, mut tm32) = (*words, l.moment_before as u64, l.moment_after as u64, tm as u32);
        let (mut zero32, mut stride, mut pre_stride) = (0u32, strand, prefix);
        // The clock's phases and skins, once, for its moments (the return forms them again for its own).
        self.clock_fill(field, words, sites)?;
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        let _ = n;
        self.launch("field_moment_strands_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut bp), arg(&mut ap)])?;
        // The paced kernels read a mode's region by the paced law where its pace is not plain, by the slot's own
        // elsewhere (the same bits there, §16).
        let mut fw = *words;
        self.launch_grid("field_moment_admit_paced_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut upp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut ap), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_paced_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut upp), arg(&mut dnp), arg(&mut sp), arg(&mut stride), arg(&mut pre_stride)])?;
        self.launch("field_moment_scatter_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut sp), arg(&mut cmp), arg(&mut tm32)])?;
        let _ = &mut none;
        // [P60 item 2] The strands, prefixes, admissions and modes' words kept where the opening is compared.
        Ok(keep.then_some(MomentKeep { before, after, up, down, _ok: ok, ws, cmap }))
    }

    /// The moment kernels' words for every moment mode, in the order of the moment index (`MomentWords` in
    /// `kernels/field_moment.cuh`, an array of them), each mode's ring slot's resident phasors and skin and
    /// its admission flags `ok[u][r]`; and the map from a moment mode to the unframed value's mode `h n + l`.
    pub(crate) fn moment_modes(&self, field: &Constitution, words: &Words, regions: usize, sites: usize, ok: &CardBuffer<'c, u8>) -> Result<(Pooled<'c, u64>, Pooled<'c, u32>)> {
        let d = field.declaration;
        let (mut packed, mut cmap) = (Vec::new(), Vec::new());
        for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
            for li in 0..d.modes {
                let slot = li * (d.frames - d.still) + h % d.frames - d.still;
                let offset: usize = field.rings()[..slot].iter().map(|(_, ring)| ring.len()).sum();
                let (period, ring) = &field.rings()[slot];
                let u = d.moment_index(h) + li;
                // `MomentWords` of `kernels/field_moment.cuh`, field for field (88 octets): `R, T` (two words of 32 bits), then
                // `region_off`, `site_region`, `site_pos`, `ring`, `n`, `ring_len`, `decay`, `dreach`, `ok`, `status`, 8 octets each.
                packed.extend([
                    regions as u64 | (sites as u64) << 32,
                    words.region_off,
                    words.site_region,
                    words.site_pos,
                    words.phasor + 16 * offset as u64,
                    *period as u64,
                    ring.len() as u64,
                    words.decay + 8 * (slot * d.reach) as u64,
                    d.reach as u64,
                    ok.device_ptr() + (u * regions) as u64,
                    words.status,
                ]);
                // A depth ring's mode carries no moment (its map's top bit, read by the moment kernels).
                cmap.push((h * d.modes + li) as u32 | if d.is_depth(h) { 1 << 31 } else { 0 });
            }
        }
        Ok((self.timed(Kind::Copy, || self.take_up(&packed)).map_err(device)?, self.timed(Kind::Copy, || self.take_up(&cmap)).map_err(device)?))
    }

    /// [definition; agent-inferred, November 1] **The moments' return** of the covector at `dm` (§16.44: one a clock; the host's `Constitution::moments_return`,
    /// the released law of §15.1): every moment mode's covector `dm` at its value (fit to 64 bits), admitted by
    /// the return's certificate, the prefix of the covector turned and released once a term, the return at
    /// every site, and the strands' encodings' rows (or a carried site's classes by their shares) added into
    /// `g`; all modes in the same launches.
    pub(crate) fn moments_return_at(&self, field: &Constitution, words: &Words, g: &CardBuffer<'c, i128>, dm: u64, regions: usize, sites: usize) -> Result<()> {
        let d = field.declaration;
        let tm = d.moment_modes();
        if tm == 0 {
            return Ok(());
        }
        let l = field.layout();
        let (strand, prefix) = ((2 * sites) as u64, (2 * (sites + regions)) as u64);
        let ds = self.timed(Kind::Alloc, || self.take::<i64>((tm * 2 * sites).max(1))).map_err(device)?;
        let q = self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?;
        let (d_before, d_after) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * sites).max(1))).map_err(device)?);
        let ok = self.timed(Kind::Alloc, || self.take_up(&vec![0u8; (tm * regions).max(1)])).map_err(device)?;
        let (ws, cmap) = self.moment_modes(field, words, regions, sites, &ok)?;
        let (mut wsp, mut cmp, mut dmp) = (ws.device_ptr(), cmap.device_ptr(), dm);
        let (mut dsp, mut qp, mut dbp, mut dap, mut gp, mut none) = (ds.device_ptr(), q.device_ptr(), d_before.device_ptr(), d_after.device_ptr(), g.device_ptr(), 0u64);
        let (mut w2, mut base_b, mut base_a, mut tm32) = (*words, l.moment_before as u64, l.moment_after as u64, tm as u32);
        let (mut one32, mut stride, mut pre_stride) = (1u32, strand, prefix);
        let grid = |x: usize| Dim3 { x: x.max(1) as u32, y: tm as u32, z: 1 };
        self.launch("field_moment_ds_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut dmp), arg(&mut cmp), arg(&mut tm32), arg(&mut dsp)])?;
        // The paced law where a mode's pace is not plain (§16): the admission with the faces' bound, the released
        // prefix of the turned covector, each receiver's far octave at its own skin (the skinned prefixes), the return.
        let mut fw = *words;
        self.launch_grid("field_moment_admit_paced_all", grid(regions), MOMENT_BLOCK, 3 * MOMENT_BLOCK * 16, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut none), arg(&mut stride), arg(&mut one32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut qp), arg(&mut stride), arg(&mut pre_stride), arg(&mut one32)])?;
        let levels = (2u32..).take_while(|&lv| (1usize << lv) < d.reach).count() as u32;
        let sk_stride = (2 * levels as usize * 2 * (sites + regions)) as u64;
        let sk = self.timed(Kind::Alloc, || self.take::<i128>((tm * sk_stride as usize).max(1))).map_err(device)?;
        let (mut skp, mut sk_stride_a, mut levels_a) = (sk.device_ptr(), sk_stride, levels);
        if levels > 0 {
            self.launch("field_moment_skinned_all", ((tm * regions * 2 * levels as usize) as u64).clamp(1, 65_535) as u32, PACE_SCAN_THREADS, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut skp), arg(&mut stride), arg(&mut sk_stride_a), arg(&mut levels_a), arg(&mut tm32)])?;
        }
        self.launch_grid("field_moment_return_paced_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut dsp), arg(&mut qp), arg(&mut skp), arg(&mut dbp), arg(&mut dap), arg(&mut stride), arg(&mut pre_stride), arg(&mut sk_stride_a)])?;
        self.launch("field_moment_strand_return_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut dbp), arg(&mut dap), arg(&mut gp)])?;
        // The moments' clock covector (§16, `moment::pace_return`): the strands and their paced prefixes read again.
        let (before, after) = (self.timed(Kind::Alloc, || self.take::<i64>((tm * 2 * sites).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i64>((tm * 2 * sites).max(1))).map_err(device)?);
        let (up, down) = (self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?, self.timed(Kind::Alloc, || self.take::<i128>((tm * 2 * (sites + regions)).max(1))).map_err(device)?);
        let (mut bp, mut ap, mut upp, mut dnp, mut zero32) = (before.device_ptr(), after.device_ptr(), up.device_ptr(), down.device_ptr(), 0u32);
        self.launch("field_moment_strands_all", Self::cells((sites * tm) as u64), THREADS, &mut [arg(&mut w2), arg(&mut base_b), arg(&mut base_a), arg(&mut tm32), arg(&mut bp), arg(&mut ap)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut upp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_prefix_paced_all", grid(regions), MOMENT_BLOCK, MOMENT_BLOCK * 32, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut ap), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride), arg(&mut zero32)])?;
        self.launch_grid("field_moment_pace_back_all", Dim3 { x: Self::cells(sites as u64), y: tm as u32, z: 1 }, THREADS, 0, &mut [arg(&mut wsp), arg(&mut cmp), arg(&mut fw), arg(&mut bp), arg(&mut ap), arg(&mut dsp), arg(&mut dbp), arg(&mut dap), arg(&mut upp), arg(&mut dnp), arg(&mut stride), arg(&mut pre_stride)])?;
        Ok(())
    }
}
