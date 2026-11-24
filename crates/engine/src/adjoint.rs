//! **The return through the producing operands.**
//!
//! the covector `p̂ − q` (weighed by a state's domain) returned through the `K` ticks, each carrier's operands held from the forward;
//! the logarithmic derivative `R⁻¹dR` of the comparison's ratio
//!
//! Kind: the forward's kinds, reversed. Kernels: `field_ratio_adjoint`, `field_current_back`, `field_pair_back`, `field_pair_scan_pre`, `field_pair_scan_back`,
//! `field_triad_back`, `field_unit_back*`, `field_tied_back_*`, `field_loud_back` and the moments' returns (`hnn/adjoint.rs`).
//! Lean: `HNN/SourceReceiverReturn`.
//! Atlas: `contact.triad-manley-rowe-gauge`, `tower.field-growth-by-lanes`, `tower.field-read-free-fall`.
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [§16.44] One clock's covectors in the reverse: `δτ`, `δσ` `[pace index][t]` and the moments' `[t][2M]`.
pub(crate) struct ClockReturn {
    pub(crate) gtau: Vec<Vec<i128>>,
    pub(crate) gsig: Vec<Vec<i128>>,
    pub(crate) dm: Vec<i128>,
}

impl ClockReturn {
    pub(crate) fn new(paced: usize, sites: usize, m2: usize) -> Self {
        Self { gtau: vec![vec![0i128; sites]; paced], gsig: vec![vec![0i128; sites]; paced], dm: vec![0i128; sites * m2] }
    }
}

impl Constitution {

    /// [definition; agent-inferred, November 5, §16.44] **A blank's clock returns through its face**: its rate
    /// `κ = 1 + Σ_a p_a c[a]` on each paced head moves with the face, so its covector `δκ` (the clocks' suffix sums at the
    /// blank) reaches the face's logits as `δz_b = Σ_h ln 2 · p_b (c_h[b] − Σ_a p_a c_h[a]) δκ_h` (the face's own Jacobian,
    /// `z` in bits), and then the readout's reverse at the state the face was read off: the encoding's bias and rows, the
    /// lift, the chart and the lane adjoint into that state's covector `dx`. Why: the code is read at the last tick and each
    /// blank's face sets a later tick's clocks, so the face is no operand there; without this return the covector missed how
    /// a blank's clock moves with its face (the unified-theory reading of November 5).
    pub(crate) fn blank_return(&self, read: &BlankRead, rates: &[(usize, i128)], reaches: &Reaches, g: &mut [i128], dx: &mut [i64]) -> Result<()> {
        let (d, l) = (&self.declaration, &self.layout);
        let (dw, a) = (d.width, d.alphabet);
        let (masses, total) = (&read.face.masses, read.face.total as i128);
        if total == 0 {
            return Ok(());
        }
        // The logits' covector held `LN2_FACE_BITS` finer than the face's (`δz 2^30`), each product released once from it.
        let mut dz = vec![0i128; a];
        for &(base, dk) in rates {
            let mean = div_nearest(masses.iter().enumerate().map(|(c, &m)| m as i128 * self.theta[base + c] as i128).sum(), total);
            for (b, slot) in dz.iter_mut().enumerate() {
                let u = div_nearest(masses[b] as i128 * (self.theta[base + b] as i128 - mean), total);
                let at = dk.checked_mul(u).and_then(|x| x.checked_mul(ln2_face())).ok_or(TowerError::Refused(PACE_RETURN))?;
                *slot += release(at, PACE_BITS);
            }
        }
        for (o, &dzo) in dz.iter().enumerate() {
            g[l.read_bias + o] += release(dzo, LN2_FACE_BITS);
        }
        // The lift's covector and everything after it held `BLANK_HELD` bits finer than the readout's (`δy 2^16`), so a
        // blank's small covector is not lost to the grain before it reaches the state; each entry released once from it.
        let mut dy = vec![0i64; dw];
        for (i, slot) in dy.iter_mut().enumerate() {
            let sum = dz.iter().enumerate().try_fold(0i128, |acc, (c, &dzc)| dzc.checked_mul(self.theta[l.enc + c * dw + i] as i128).and_then(|x| acc.checked_add(x))).ok_or(TowerError::Refused(PACE_RETURN))?;
            *slot = fit64(release(sum, STATE_BITS + LN2_FACE_BITS - BLANK_HELD))?;
        }
        for (c, &dzc) in dz.iter().enumerate() {
            for (i, &yi) in read.lift.iter().enumerate() {
                g[l.enc + c * dw + i] += release(dzc.checked_mul(yi as i128).ok_or(TowerError::Refused(PACE_RETURN))?, STATE_BITS + LN2_FACE_BITS);
            }
        }
        for (i, &dyi) in dy.iter().enumerate() {
            g[l.lift_bias + i] += release(dyi as i128, BLANK_HELD);
            for (j, &rj) in read.read.iter().enumerate() {
                g[l.read + i * dw + j] += release(dyi as i128 * rj as i128, BLANK_HELD);
            }
        }
        let mut dr = vec![0i64; dw];
        transposed(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &dy, MATERIAL_BITS, &mut dr)?;
        let back = lane_adjoint(&read.read, &read.scale, &dr)?;
        for (slot, &b) in dx.iter_mut().zip(&back) {
            *slot = fit64(*slot as i128 + release(b as i128, BLANK_HELD))?;
        }
        Ok(())
    }

    /// The exact reverse of [`Constitution::pass`] against each unresolved site's class: the code's own covector, added
    /// into `g` on each family's natural grain (a face family's `Σ δz` on `2^(−24)`, a material family's `Σ δz x` on
    /// `2^(−40)`), which the reverse's law tests read against the code's difference.
    pub(crate) fn returned(&self, region: &Region, pass: &Forward, g: &mut [i128]) -> Result<()> {
        // [definition; the lead, November 18] A passage read by two streams returns through the strand's own reverse; read once, its return
        // stands for both reads where the field reads twice (as a known stream's does, below).
        if let Some(strand) = pass.strand.as_deref() {
            for _ in 0..if self.declaration.mark { 2 } else { 1 } {
                self.strand_returned(region.classes, region.targets.unwrap_or(region.classes), strand, g)?;
            }
            return Ok(());
        }
        self.returned_with(region, pass, g, None, None, None, None, None, None, None)?;
        // [definition; agent-inferred, November 14, G180] Where the field reads twice both reads are compared: the first read's own return is
        // added beside the second's, and the consumer halves the section's sum once ([`Constitution::read_and_return`]), so the comparison is the two
        // reads' mean and at the founding (the reads equal) it is the one read's, bit for bit. Why: G180 read the first read, which no
        // comparison reached, drifting off its agreement with the passage (0.012 nats a place at one-place masks, 0.060 at whole masks) while
        // the field leaned on its marks; the field's own placement is kept its honest placement by the passage's comparison.
        if let Some(first) = pass.first.as_deref() {
            self.returned_with(region, first, g, None, None, None, None, None, None, None)?;
        } else if self.declaration.mark && region.before {
            // [definition; the lead, November 18; `agent-inferred`] A known stream is read once ([`Region::before`]). In a field that reads twice
            // its one read stands for both: its return enters the section's sum twice, so the mean the consumer takes is its own covector
            // at the weight every other region's has. (A ruler's forward at `3` or `4` returns once and is halved with the rest: a reading.)
            self.returned_with(region, pass, g, None, None, None, None, None, None, None)?;
        }
        Ok(())
    }

    /// [agent-inferred, November 3, §16.39] **One tick's return**: the covector `dx` of a tick's output faces carried back
    /// through its pair contact, its current and contact and its charts to the covector of its input faces, the material's
    /// covector added into `g`, the moments' into `dm` and the clocks' into `gtau` and `gsig` (with the contact covector's
    /// shares and the currents' covectors where read). A region's reverse reads its ticks through it in reverse order; a
    /// tower of scales reads each level's ticks through it.
    #[allow(clippy::too_many_arguments)]
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn tick_return(&self, cell: &TickCell, dx: &mut [i64], g: &mut [i128], paces: &Paces, definite: &[bool], dm: &mut [i128], gtau: &mut [Vec<i128>], gsig: &mut [Vec<i128>], mut shares: Option<&mut [u128]>, mut currents: Option<&mut Vec<Vec<i64>>>, mut reach: Option<&mut Vec<[ReachSums; 2]>>, closed_rows: Option<&[Vec<i128>]>) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n, f, heads, lanes) = (d.width, d.complex(), d.modes, d.contacts, d.heads, d.lanes);
        let m2 = 2 * m;
        let span = 2 * n;
        let sites = definite.len();
        // [the strand's two streams] Where the cell holds a strand's open places beside its known stream ([`ClassLists::twins_from`]), a
        // site's place is the known site's of its index, and a pair's distance is its places'.
        let heard = cell.classes.first().map_or(sites, |lists| lists.twins_from);
        let place = |t: usize| if t >= heard { t - heard } else { t };
        let pd = |h: usize, l: usize, i: usize, j: usize| self.pair_decay_placed(paces, h, l, i, j, place(i).abs_diff(place(j)));
        let l = &self.layout;
        let reaches = self.reaches();
        let ln2 = ln2_face();
        // The pair contact: x_out = x_mid + W_c c + b_c.
        let dxs: Vec<&[i64]> = dx.chunks_exact(dw).collect();
        for dxt in &dxs {
            for (i, &v) in dxt.iter().enumerate() {
                g[l.w_bias + i] += v as i128;
            }
        }
        let cs: Vec<&[i64]> = cell.c.chunks_exact(f).collect();
        outer_sum(&mut g[l.w..l.w + dw * f], f, &dxs, &cs)?;
        let mut da = vec![0i64; sites * f];
        let mut db = vec![0i64; sites * f];
        let mut dc = vec![0i64; sites * f];
        for t in 0..sites {
            transposed(&self.theta[l.w..l.w + dw * f], reaches.w, f, dxs[t], MATERIAL_BITS, &mut dc[t * f..(t + 1) * f])?;
        }
        // [definition; theory, November 12, the triad record §4] **The triads' reverse** ([`Declaration::triads`]): `W_T`'s covector the outer
        // sum over sites of `δx(t)` against `c^T(t)` (unreleased, as `W`'s); `δc^T(t) = W_Tᵀ δx(t)` released to the covector's grain; then the
        // products' covectors through their producing operands ([`triad_back`]), each slot one place's. Their charts' covectors follow below.
        let (triads, j2, j6) = (d.triads, 2 * d.triads, 6 * d.triads);
        let dabg = if triads > 0 {
            let cts: Vec<&[i64]> = cell.ct.chunks_exact(j2).collect();
            outer_sum(&mut g[l.w_triad..l.w_triad + dw * j2], j2, &dxs, &cts)?;
            let mut dct = vec![0i64; sites * j2];
            for t in 0..sites {
                transposed(&self.theta[l.w_triad..l.w_triad + dw * j2], reaches.w_triad, j2, dxs[t], MATERIAL_BITS, &mut dct[t * j2..(t + 1) * j2])?;
            }
            triad_back(triads, sites, &cell.abg, &cell.tp, &dct, d.crossing)?
        } else {
            Vec::new()
        };
        let half = f / 2;
        let (plain, circles) = (d.carry_first(), d.carry);
        let c2 = 2 * circles;
        let one_sided = cell.classes.first().is_some_and(|lists| lists.one_sided);
        let past = cell.classes.first().is_some_and(|lists| lists.past);
        // `δa_t = conj(b_s) δc_t`, `δb_s = conj(a_t) δc_t` for the complex product of site `t` and its strand mate `s` (§16.34); each site's `b`
        // is one mate's, so each `δb_s` is one term.
        for t in 0..sites {
            for e in 0..plain {
                // [the strand's known stream] Where every site hears only what stands before it, an odd contact met no mate.
                // [the strand's two streams] An open place's mate is the known site before its place, which is then two sites' mate: its
                // `δb` is the sum of both terms (each released as it stands alone).
                let mate = crate::contact::sided_mate(t, e, heard, one_sided, past);
                let Some(s) = mate else { continue };
                let (gr, gi) = (dc[t * f + e] as i128, dc[t * f + half + e] as i128);
                let (ar, ai) = (cell.a[t * f + e] as i128, cell.a[t * f + half + e] as i128);
                let (br, bi) = (cell.b[s * f + e] as i128, cell.b[s * f + half + e] as i128);
                da[t * f + e] = fit64(release(br * gr + bi * gi, FACE_BITS))?;
                da[t * f + half + e] = fit64(release(br * gi - bi * gr, FACE_BITS))?;
                db[s * f + e] = fit64(db[s * f + e] as i128 + release(ar * gr + ai * gi, FACE_BITS))?;
                db[s * f + half + e] = fit64(db[s * f + half + e] as i128 + release(ar * gi - ai * gr, FACE_BITS))?;
            }
        }
        // [definition; theory, November 11 17:25 and November 12 (G98)] **The carry circles' reverse**, with the producing operands (`a`, `b`,
        // `γ`, `q`, `ℓ` and `Q`'s operand `Qm(t) = Q(t ∓ 1)` of the forward), each circle in the opposite strand order, one release a step. With
        // `X(t)` the covector of `Qm(t)` and `u` the covector of `Q(t)` (`X(t ± 1)`, the next site of the reverse): `δa(t) = conj(Qm(t)) δp(t)`,
        // `δγ(t) = conj(Qm(t)) u` released at the face's grain, `X(t) = conj(a(t)) δp(t) + conj(γ(t)) u`; then off the chain the gate's and the
        // coupling's covectors `δq`, `δℓ` and the drive's `δb(t) = κ(t) u` ([`carry_gate_return`]).
        let mut dqh = vec![0i64; sites * c2];
        // [the lead, November 19] The pump chart's covector where the circles are pumped ([`Declaration::pump`]).
        let pumped = d.pump;
        let mut dph = vec![0i64; if pumped { sites * c2 } else { 0 }];
        // [the strand's known stream] A circle scanned from the right stood at rest there, and returns nothing.
        for k in (0..circles).filter(|&k| !one_sided || past || (plain + k) % 2 == 0) {
            let e = plain + k;
            let (mut xr, mut xi) = (0i128, 0i128);
            for step in 0..heard {
                // (a one-sided stream scans every circle from the left, so its reverse runs from the right)
                let t = if e % 2 == 0 || one_sided { heard - 1 - step } else { step };
                let (gr, gi) = (dc[t * f + e] as i128, dc[t * f + half + e] as i128);
                let (ar, ai) = (cell.a[t * f + e] as i128, cell.a[t * f + half + e] as i128);
                let (qr, qi) = (cell.qm[t * c2 + k] as i128, cell.qm[t * c2 + circles + k] as i128);
                let (yr, yi) = (cell.gam[t * c2 + k] as i128, cell.gam[t * c2 + circles + k] as i128);
                let (ur, ui) = (xr, xi);
                let du = (fit64(ur)?, fit64(ui)?);
                da[t * f + e] = fit64(release(qr * gr + qi * gi, FACE_BITS))?;
                da[t * f + half + e] = fit64(release(qr * gi - qi * gr, FACE_BITS))?;
                let dgamma = (fit64(release(qr * ur + qi * ui, FACE_BITS))?, fit64(release(qr * ui - qi * ur, FACE_BITS))?);
                // [the strand's two streams] The open place at this place read the same `Qm(t)`: its own `δa`, and its term of the
                // covector of `Qm(t)` beside the known site's, each released as it stands alone.
                let (mut tr, mut ti) = (0i128, 0i128);
                if heard + t < sites {
                    let o = heard + t;
                    let (ogr, ogi) = (dc[o * f + e] as i128, dc[o * f + half + e] as i128);
                    let (oar, oai) = (cell.a[o * f + e] as i128, cell.a[o * f + half + e] as i128);
                    da[o * f + e] = fit64(release(qr * ogr + qi * ogi, FACE_BITS))?;
                    da[o * f + half + e] = fit64(release(qr * ogi - qi * ogr, FACE_BITS))?;
                    (tr, ti) = (release(oar * ogr + oai * ogi, FACE_BITS), release(oar * ogi - oai * ogr, FACE_BITS));
                }
                // [the lead, November 19] The pump's reflection returns `η conj(u)` beside the turn's `conj(γ) u`, in the turn's one release
                // ([`Declaration::pump`]); zero where the circles are not pumped.
                let (er, ei) = if pumped { (cell.eta[t * c2 + k] as i128, cell.eta[t * c2 + circles + k] as i128) } else { (0, 0) };
                xr = i128::from(fit64(release(ar * gr + ai * gi, FACE_BITS) + tr + release(yr * ur + yi * ui + er * ur + ei * ui, GAMMA_BITS))?);
                xi = i128::from(fit64(release(ar * gi - ai * gr, FACE_BITS) + ti + release(yr * ui - yi * ur + ei * ur - er * ui, GAMMA_BITS))?);
                let drive = (cell.b[t * f + e], cell.b[t * f + half + e]);
                let (q, lk) = (cell.qh[t * c2 + k] as i128, cell.qh[t * c2 + circles + k] as i128);
                let gamma = (cell.gam[t * c2 + k], cell.gam[t * c2 + circles + k]);
                let ((dq, dl), (dbr, dbi)) = if pumped {
                    // `δη = u Qm`, released at the face's grain as `δγ` is.
                    let deta = (fit64(release(qr * ur - qi * ui, FACE_BITS))?, fit64(release(qr * ui + qi * ur, FACE_BITS))?);
                    let p = (cell.ph[t * c2 + k] as i128, cell.ph[t * c2 + circles + k] as i128);
                    let (dqdl, (dpr, dpi), dbs) = carry_gate_return_pumped(&self.exponential, gamma, dgamma, (er as i64, ei as i64), deta, drive, du, q, lk, p)?;
                    dph[t * c2 + k] = dpr;
                    dph[t * c2 + circles + k] = dpi;
                    (dqdl, dbs)
                } else {
                    carry_gate_return(&self.exponential, gamma, dgamma, drive, du, q, lk)?
                };
                db[t * f + e] = dbr;
                db[t * f + half + e] = dbi;
                dqh[t * c2 + k] = dq;
                dqh[t * c2 + circles + k] = dl;
            }
        }
        let das: Vec<&[i64]> = da.chunks_exact(f).collect();
        let dbs: Vec<&[i64]> = db.chunks_exact(f).collect();
        let r2s: Vec<&[i32]> = cell.read2.chunks_exact(dw).collect();
        outer_sum(&mut g[l.a..l.a + f * dw], dw, &das, &r2s)?;
        outer_sum(&mut g[l.b..l.b + f * dw], dw, &dbs, &r2s)?;
        if circles > 0 {
            // The carry circles' charts: `Σ_t δ(q, ℓ)(t) r̂(t)ᵀ` into `Q` and `L`, and `Σ_t δ(q, ℓ)(t)` into their biases.
            let dqhs: Vec<&[i64]> = dqh.chunks_exact(c2).collect();
            outer_sum(&mut g[l.carry..l.carry + c2 * dw], dw, &dqhs, &r2s)?;
            for row in &dqhs {
                for (j, &v) in row.iter().enumerate() {
                    g[l.carry_bias + j] += v as i128;
                }
            }
            if pumped {
                // [the lead, November 19] The pump's chart: `Σ_t δp(t) r̂(t)ᵀ` into `P`, and `Σ_t δp(t)` into its bias.
                let dphs: Vec<&[i64]> = dph.chunks_exact(c2).collect();
                outer_sum(&mut g[l.pump..l.pump + c2 * dw], dw, &dphs, &r2s)?;
                for row in &dphs {
                    for (j, &v) in row.iter().enumerate() {
                        g[l.pump_bias + j] += v as i128;
                    }
                }
            }
        }
        if triads > 0 {
            // [theory, November 12, the triad record §4] The triads' charts: `Σ_t δ(α, β, γ)(t) r̂(t)ᵀ` into `A`, `B` and `G`, and `Σ_t δ(α, β, γ)(t)`
            // into their biases.
            let dabgs: Vec<&[i64]> = dabg.chunks_exact(j6).collect();
            outer_sum(&mut g[l.triad..l.triad + j6 * dw], dw, &dabgs, &r2s)?;
            for row in &dabgs {
                for (j, &v) in row.iter().enumerate() {
                    g[l.triad_bias + j] += v as i128;
                }
            }
        }
        for t in 0..sites {
            for e in 0..f {
                g[l.a_bias + e] += das[t][e] as i128;
                g[l.b_bias + e] += dbs[t][e] as i128;
            }
        }
        let mut dmid = vec![0i64; sites * dw];
        let mut ra = vec![0i64; dw];
        let mut rb = vec![0i64; dw];
        let mut rg = vec![0i64; dw];
        let mut rt = vec![0i64; dw];
        for t in 0..sites {
            transposed(&self.theta[l.a..l.a + f * dw], reaches.a, dw, das[t], MATERIAL_BITS, &mut ra)?;
            transposed(&self.theta[l.b..l.b + f * dw], reaches.b, dw, dbs[t], MATERIAL_BITS, &mut rb)?;
            if circles > 0 {
                // The carry circles' charts read the pair chart as `a` and `b` do, so their transposed product joins the read's covector.
                transposed(&self.theta[l.carry..l.carry + c2 * dw], reaches.carry, dw, &dqh[t * c2..(t + 1) * c2], MATERIAL_BITS, &mut rg)?;
                if pumped {
                    // [the lead, November 19] So does the pump's chart, into the same slot (an accumulating transposed read, as the card's).
                    let mut rp = vec![0i64; dw];
                    transposed(&self.theta[l.pump..l.pump + c2 * dw], reaches.pump, dw, &dph[t * c2..(t + 1) * c2], MATERIAL_BITS, &mut rp)?;
                    for (slot, &v) in rg.iter_mut().zip(&rp) {
                        *slot += v;
                    }
                }
            }
            let mut dr: Vec<i64> = if circles > 0 { ra.iter().zip(&rb).zip(&rg).map(|((&p, &q), &r)| p + q + r).collect() } else { ra.iter().zip(&rb).map(|(&p, &q)| p + q).collect() };
            if triads > 0 {
                // [theory, November 12] The triads' charts read the pair chart as `a` and `b` do, so their transposed product joins the read's covector
                // beside the drives' and the circles'.
                transposed(&self.theta[l.triad..l.triad + j6 * dw], reaches.triad, dw, &dabg[t * j6..(t + 1) * j6], MATERIAL_BITS, &mut rt)?;
                for (slot, &v) in dr.iter_mut().zip(&rt) {
                    *slot += v;
                }
            }
            let back = lane_adjoint(r2s[t], &cell.scale2[t * lanes..(t + 1) * lanes], &dr)?;
            for i in 0..dw {
                dmid[t * dw + i] = fit64(dx[t * dw + i] as i128 + back[i] as i128)?;
            }
        }
        // The current: x_mid = x_in + O y + b_o.
        let dms: Vec<&[i64]> = dmid.chunks_exact(dw).collect();
        for dmt in &dms {
            for (i, &v) in dmt.iter().enumerate() {
                g[l.out_bias + i] += v as i128;
            }
        }
        let ys: Vec<&[i64]> = cell.y.chunks_exact(m2).collect();
        outer_sum(&mut g[l.out..l.out + dw * m2], m2, &dms, &ys)?;
        let mut dy = vec![0i64; sites * m2];
        for t in 0..sites {
            transposed(&self.theta[l.out..l.out + dw * m2], reaches.out, m2, dms[t], MATERIAL_BITS, &mut dy[t * m2..(t + 1) * m2])?;
        }
        // The weights and the contact over each site's support, head by head.
        let mut dq = vec![0i64; sites * m2];
        let mut dv = vec![0i64; sites * m2];
        let mut dp = vec![0i64; sites * m2];
        let mut dyh = vec![0i64; sites * span];
        // The current's covectors of this tick `[h][t][2n]`, where read ([`Constitution::row_currents`]).
        if let Some(c) = currents.as_deref_mut() {
            c.push(vec![0i64; heads * sites * span]);
        }
        // [the lead, November 21] Each row's friction covector at its receiver, `release(δψ_i, 16)` on the face family's `2^(−24)` (`[t][h]`), for
        // the friction's gate ([`Declaration::friction_gate`]).
        let mut dgate = vec![0i64; if d.friction_gate { sites * heads } else { 0 }];
        for h in 0..heads {
            // A paced head's current returns to the receiver's frame `y = conj(U) ỹ`, turned by `τ_i`:
            // `δτ_i −= b Re(conj(δy_i) i y_i)` (§16).
            if let Some(p) = paces.row[h] {
                for t in 0..sites {
                    for li in 0..n {
                        let c = h * n + li;
                        let a = (dy[t * m2 + c] as i128, dy[t * m2 + m + c] as i128);
                        let z = (cell.y[t * m2 + c] as i128, cell.y[t * m2 + m + c] as i128);
                        gtau[p][t] -= turned_back(self.turn_rate(self.slot(h, li)), a, z)?;
                    }
                }
            }
            // δỹ_i = U_i δy_i, the adjoint of the return to the receiver's frame.
            for t in 0..sites {
                for li in 0..n {
                    let c = h * n + li;
                    let (ur, ui) = self.frame_placed(paces, t, place(t), h, li);
                    let (ur, ui) = (ur as i128, ui as i128);
                    let (gr, gi) = (dy[t * m2 + c] as i128, dy[t * m2 + m + c] as i128);
                    dyh[t * span + li] = fit64(release(ur * gr - ui * gi, MOVE_BITS))?;
                    dyh[t * span + n + li] = fit64(release(ui * gr + ur * gi, MOVE_BITS))?;
                }
            }
            if let Some(c) = currents.as_deref_mut() {
                let last = c.last_mut().expect("pushed above");
                last[h * sites * span..(h + 1) * sites * span].copy_from_slice(&dyh);
            }
            let rows = &cell.rows[h * sites..(h + 1) * sites];
            let crowds = &cell.crowds[h * sites..(h + 1) * sites];
            let sums = &cell.sums[h];
            let vh = &cell.v[h * sites * span..(h + 1) * sites * span];
            let qh = &cell.q[h * sites * span..(h + 1) * sites * span];
            let ph = &cell.pq[h * sites * span..(h + 1) * sites * span];
            // A receiver's probe word (§16.19).
            let probe_of = |i: usize, r: usize| -> i64 { ph[i * span + r] };
            let back = CONTACT_BACK + self.decay(h, 0, 0).1;
            // [measurement; G157] A turned head's reach on its own clock: its founding covector by receiver row, where read.
            let mut reach_rows = [ReachSums::default(); 2];
            let reach_clock = reach.as_ref().and(paces.row[h]).filter(|_| d.carries_moment(h) && !d.is_depth(h)).map(|p| &paces.sigma[p]);
            // The values' return: `δṽ_jm = Σ_(i: j∈S_i) p_ij,m D_m(|i − j|) δỹ_im` with each term's
            // share `p` on `2^(−63)` (one integer sum, released once); a crowd's share is spread over
            // its members, `p_C/|C|` each, through a difference array over the places.
            let mut sv = vec![0i128; sites * span];
            let mut crowd_v = vec![0i128; (sites + 1) * span];
            for i in 0..sites {
                for src in &rows[i] {
                    let j = src.j as usize;
                    for r in 0..span {
                        sv[j * span + r] += src.p as i128 * decayed(pd(h, r % n, i, j), dyh[i * span + r]);
                    }
                }
                for c in &crowds[i] {
                    for r in 0..span {
                        let part = div_nearest(c.e as i128 * decayed(self.octave_decay(paces, h, r % n, i, c.level, c.lo > i), dyh[i * span + r]), c.count as i128);
                        crowd_v[c.lo * span + r] += part;
                        crowd_v[(c.hi + 1) * span + r] -= part;
                    }
                }
            }
            // A difference array's running prefix over the places (`[t][r]`).
            let prefixed = |diff: &[i128]| -> Vec<i128> {
                let mut out = diff[..sites * span].to_vec();
                for t in 1..sites {
                    for r in 0..span {
                        out[t * span + r] += out[(t - 1) * span + r];
                    }
                }
                out
            };
            let spread_v = prefixed(&crowd_v);
            for j in 0..sites {
                for r in 0..span {
                    // Held in the framed chart until the frame is undone below.
                    let c = h * n + r % n;
                    let slot = j * m2 + if r < n { c } else { m + c };
                    dv[slot] = fit64(release(sv[j * span + r], SHARE_BITS))?;
                    if definite[j] {
                        dv[slot] = fit64(dv[slot] as i128 + release(spread_v[j * span + r], SHARE_BITS))?;
                    }
                }
            }
            // `δz_k = ln 2 · p_k (δp_k − μ)`, `δp_k = ⟨δỹ_i, D ṽ_k⟩` on 2^(−40) (a crowd's value its decayed
            // mean), `μ = Σ_k p_k δp_k`; the falloff is the medium's constant and returns nothing. Then
            // `δs = 2^(−β) δz`.
            let mut ds: Vec<Vec<i128>> = Vec::with_capacity(sites);
            let mut dsc: Vec<Vec<i128>> = Vec::with_capacity(sites);
            for i in 0..sites {
                let (row, crowd) = (&rows[i], &crowds[i]);
                let dyi = &dyh[i * span..(i + 1) * span];
                let kind = usize::from(cell.classes[h].listens(i));
                let temper = self.temper(h, kind == 1)?;
                let mut dp: Vec<i128> = row
                    .iter()
                    .map(|src| {
                        let j = src.j as usize;
                        (0..n).map(|l| { let decay = pd(h, l, i, j); dyi[l] as i128 * decayed(decay, vh[j * span + l]) + dyi[n + l] as i128 * decayed(decay, vh[j * span + n + l]) }).sum()
                    })
                    .collect();
                // [definition; the lead, November 17] The closed face's covector on this row's shares, where the face read the row ([`crate::closed`]).
                if let Some(extra) = closed_rows.map(|c| &c[h * sites + i]).filter(|e| !e.is_empty()) {
                    for (slot, &v) in dp.iter_mut().zip(extra) {
                        *slot += v;
                    }
                }
                let dpc: Vec<i128> = crowd
                    .iter()
                    .map(|c| {
                        let pairs: i128 = (0..n).map(|l| { let decay = self.octave_decay(paces, h, l, i, c.level, c.lo > i); dyi[l] as i128 * decayed_wide(decay, sums.value(c.lo, c.hi, l)) + dyi[n + l] as i128 * decayed_wide(decay, sums.value(c.lo, c.hi, n + l)) }).sum();
                        div_nearest(pairs, c.count as i128)
                    })
                    .collect();
                let mean = release(row.iter().zip(&dp).map(|(src, &dpj)| src.p as i128 * dpj).sum::<i128>() + crowd.iter().zip(&dpc).map(|(c, &dpj)| c.e as i128 * dpj).sum::<i128>(), SHARE_BITS);
                let compare = |p: i128, dpk: i128| -> i128 { release(ln2 * release(p * (dpk - mean), SHARE_BITS), MOVE_BITS) };
                let mut out = Vec::with_capacity(row.len());
                let mut dt = 0i128;
                // [the lead, November 21] The friction's covector, `−Σ δz ⌊log₂ d⌋` (a crowd's `δz` times its level), on the face family's
                // `2^(−24)` from `δz` on `2^(−40)` ([`Declaration::friction`]).
                let mut dpsi = 0i128;
                let (mut row_w, mut row_u) = (0i128, 0i128);
                for (src, &dpj) in row.iter().zip(&dp) {
                    let dz = compare(src.p as i128, dpj);
                    dpsi -= dz * i128::from(octave(place(i).abs_diff(src.j as usize)));
                    if let Some(sigma) = reach_clock {
                        let (lw, lu) = reach_logs(sigma, i, src.j as usize);
                        (row_w, row_u) = (row_w - dz * i128::from(lw), row_u - dz * i128::from(lu));
                    }
                    dt += release(dz * src.s as i128, FACE_BITS);
                    let dsij = release(temper * dz, MATERIAL_BITS);
                    if dsij.unsigned_abs() >> d.contact_return_bits() != 0 {
                        return refuse("a contact's covector past its return's carrier");
                    }
                    out.push(dsij);
                }
                let mut outc = Vec::with_capacity(crowd.len());
                for (c, &dpj) in crowd.iter().zip(&dpc) {
                    let dz = compare(c.e as i128, dpj);
                    dpsi -= dz * i128::from(c.level);
                    if let Some(sigma) = reach_clock {
                        // A crowd takes the clock's term at the place its skin reads, `2^level` away, and no remainder.
                        let e = if c.lo > i { i + (1 << c.level) } else { i - (1 << c.level) };
                        row_w -= dz * i128::from(reach_logs(sigma, i, e).0);
                    }
                    dt += release(dz * c.s as i128, FACE_BITS);
                    let dsij = release(temper * dz, MATERIAL_BITS);
                    if dsij.unsigned_abs() >> d.contact_return_bits() != 0 {
                        return refuse("a contact's covector past its return's carrier");
                    }
                    outc.push(dsij);
                }
                // Into the temperature's own chart (§16.12), the row's.
                g[l.temper + 2 * h + kind] += temperature_chain(temper, dt)?;
                if d.friction {
                    g[l.friction + 2 * h + kind] += release(dpsi, FACE_BITS);
                }
                if d.friction_gate {
                    dgate[i * heads + h] = fit64(release(dpsi, FACE_BITS))?;
                }
                if let Some(sh) = shares.as_deref_mut() {
                    for (src, &v) in row.iter().zip(&out) {
                        sh[2 * h + usize::from(place(i).abs_diff(src.j as usize) >= NEAR)] += v.unsigned_abs();
                    }
                    sh[2 * h + 1] += outc.iter().map(|v| v.unsigned_abs()).sum::<u128>();
                }
                ds.push(out);
                dsc.push(outc);
                if reach_clock.is_some() {
                    let r = &mut reach_rows[usize::from(definite[i])];
                    r.rows += 1;
                    (r.w, r.w_abs, r.w_sq) = (r.w + row_w, r.w_abs + row_w.unsigned_abs(), r.w_sq + (row_w.unsigned_abs() >> 32).pow(2));
                    (r.u, r.u_abs, r.u_sq) = (r.u + row_u, r.u_abs + row_u.unsigned_abs(), r.u_sq + (row_u.unsigned_abs() >> 32).pow(2));
                }
            }
            if let Some(out) = reach.as_deref_mut() {
                out.push(reach_rows);
            }
            // A paced head's skins follow its turn (§16): each pair's and crowd's `D(σ_i − σ_j)` returns to the
            // two ends of its variation, `E = 2^40 ∂/∂D` from the value (`p Re(conj(δỹ_i) D ṽ_j)/D`) and the
            // lock (`δs (2 P 2^30 − 2 D Q)` over the lock's grains), then `δσ_i −= sgn b D E`, `δσ_j += sgn b D E`.
            if let Some(p) = paces.row[h].filter(|_| !d.is_depth(h)) {
                let sigma = &paces.sigma[p];
                for i in 0..sites {
                    for (k, src) in rows[i].iter().enumerate() {
                        let j = src.j as usize;
                        let sgn = (sigma[i] - sigma[j]).signum() as i128;
                        if sgn == 0 {
                            continue;
                        }
                        for l in 0..n {
                            let (dec, g_) = pd(h, l, i, j);
                            let inner = dyh[i * span + l] as i128 * vh[j * span + l] as i128 + dyh[i * span + n + l] as i128 * vh[j * span + n + l] as i128;
                            let value = release(src.p as i128 * inner, SHARE_BITS);
                            let (wr, wi, kr, ki) = (probe_of(i, l) as i128, probe_of(i, n + l) as i128, qh[j * span + l] as i128, qh[j * span + n + l] as i128);
                            let bracket = (2 * (wr * kr + wi * ki) << g_) - 2 * dec * (kr * kr + ki * ki);
                            let lock = release(ds[i][k].checked_mul(bracket).ok_or(TowerError::Refused(PACE_RETURN))?, LOCK_BACK_BITS + 2 * g_ - MOVE_BITS);
                            let at = skin_back(self.turn_rate(self.slot(h, l)), dec, value + lock)?;
                            gsig[p][i] -= sgn * at;
                            gsig[p][j] += sgn * at;
                        }
                    }
                    for (k, c) in crowds[i].iter().enumerate() {
                        let right = c.lo > i;
                        let e = if right { i + (1 << c.level) } else { i - (1 << c.level) };
                        let sgn = (sigma[i] - sigma[e]).signum() as i128;
                        if sgn == 0 {
                            continue;
                        }
                        let count = c.count as i128;
                        for l in 0..n {
                            let (dec, g_) = self.octave_decay(paces, h, l, i, c.level, right);
                            let (vr, vi) = (sums.value(c.lo, c.hi, l), sums.value(c.lo, c.hi, n + l));
                            let inner = dyh[i * span + l] as i128 * vr + dyh[i * span + n + l] as i128 * vi;
                            let value = div_nearest(release(c.e as i128 * inner, SHARE_BITS), count);
                            let (wr, wi) = (ph[i * span + l] as i128, ph[i * span + n + l] as i128);
                            let (mr, mi) = (sums.words[(c.hi + 1) * span + l] - sums.words[c.lo * span + l], sums.words[(c.hi + 1) * span + n + l] - sums.words[c.lo * span + n + l]);
                            let bracket = div_nearest((2 * count * (wr * mr + wi * mi) << g_) - 2 * dec * (mr * mr + mi * mi), count * count);
                            let lock = release(dsc[i][k].checked_mul(bracket).ok_or(TowerError::Refused(PACE_RETURN))?, LOCK_BACK_BITS + 2 * g_ - MOVE_BITS);
                            let at = skin_back(self.turn_rate(self.slot(h, l)), dec, value + lock)?;
                            gsig[p][i] -= sgn * at;
                            gsig[p][e] += sgn * at;
                        }
                    }
                }
            }
            // Each mode's lock ([`lock`]) returns to its two words: to the receiver's probe
            // `δp̃_i += Σ_(j∈S_i) δs_ij D(|i − j|) k̃_j`, to each source's key `δk̃_j += Σ_(i: j∈S_i) δs_ij (D p̃_i − D² k̃_j)`,
            // and a crowd's `δs_C D k̄/|C|` to its receiver's probe and `δs_C (D p̃_i/|C| − D² k̄/|C|²)` to each
            // member's key; each sum released to 2^(−24).
            let mut col = vec![0i128; sites * span];
            let mut crowd_w = vec![0i128; (sites + 1) * span];
            for i in 0..sites {
                for (k, src) in rows[i].iter().enumerate() {
                    let j = src.j as usize;
                    for r in 0..span {
                        let (dec, g) = pd(h, r % n, i, j);
                        // The key's bracket `D ŵ_i − D² ŵ_j` released by the skin's bits once (a
                        // declared crossing, as the probe's `D ŵ` is), so it stands on the probe's grain.
                        let bracket = release(((dec * probe_of(i, r) as i128) << g) - dec * dec * qh[j * span + r] as i128, g);
                        col[j * span + r] = col[j * span + r].checked_add(ds[i][k].checked_mul(bracket).ok_or(TowerError::Refused(KEY_RETURN))?).ok_or(TowerError::Refused(KEY_RETURN))?;
                    }
                }
                for (k, c) in crowds[i].iter().enumerate() {
                    for r in 0..span {
                        let (dec, g) = self.octave_decay(paces, h, r % n, i, c.level, c.lo > i);
                        let mean = sums.words[(c.hi + 1) * span + r] - sums.words[c.lo * span + r];
                        let bracket = release(((dec * ph[i * span + r] as i128 * c.count as i128) << g) - dec * dec * mean, g);
                        let part = div_nearest(dsc[i][k].checked_mul(bracket).ok_or(TowerError::Refused(KEY_RETURN))?, (c.count * c.count) as i128);
                        crowd_w[c.lo * span + r] += part;
                        crowd_w[(c.hi + 1) * span + r] -= part;
                    }
                }
            }
            let spread_w = prefixed(&crowd_w);
            for i in 0..sites {
                for r in 0..span {
                    let sq: i128 = rows[i].iter().enumerate().map(|(k, src)| ds[i][k] * pd(h, r % n, i, src.j as usize).0 * qh[src.j as usize * span + r] as i128).sum::<i128>()
                        + crowds[i].iter().enumerate().map(|(k, c)| div_nearest(dsc[i][k] * self.octave_decay(paces, h, r % n, i, c.level, c.lo > i).0 * (sums.words[(c.hi + 1) * span + r] - sums.words[c.lo * span + r]), c.count as i128)).sum::<i128>();
                    // Held in the framed chart until the frame is undone below.
                    let c = h * n + r % n;
                    let slot = if r < n { c } else { m + c };
                    dp[i * m2 + slot] = fit64(release(sq, back))?;
                    dq[i * m2 + slot] = fit64(release(col[i * span + r], back))?;
                    if definite[i] {
                        dq[i * m2 + slot] = fit64(dq[i * m2 + slot] as i128 + release(spread_w[i * span + r], back))?;
                    }
                }
            }
        }
        // The word's return through its ratio to its own power, head by head:
        // `δw̃ = (δŵ − ŵ ⟨ŵ, δŵ⟩/2n) / ‖w̃‖_rms` (`ratio_adjoint`), still in the framed chart.
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                let slot = |r: usize| t * m2 + if r < n { h * n + r } else { m + h * n + r - n };
                let unit: Vec<i32> = cell.q[at..at + span].iter().map(|&v| v as i32).collect();
                let cov: Vec<i64> = (0..span).map(|r| dq[slot(r)]).collect();
                let back = ratio_adjoint(&unit, cell.qscale[h * sites + t], &cov)?;
                for (r, b) in back.into_iter().enumerate() {
                    dq[slot(r)] = b;
                }
            }
        }
        // The probe's return through its own power, alike (§16.19).
        for h in 0..heads {
            for t in 0..sites {
                let at = (h * sites + t) * span;
                let slot = |r: usize| t * m2 + if r < n { h * n + r } else { m + h * n + r - n };
                let unit: Vec<i32> = cell.pq[at..at + span].iter().map(|&v| v as i32).collect();
                let cov: Vec<i64> = (0..span).map(|r| dp[slot(r)]).collect();
                if cov.iter().all(|&c| c == 0) {
                    continue;
                }
                let back = ratio_adjoint(&unit, cell.pscale[h * sites + t], &cov)?;
                for (r, b) in back.into_iter().enumerate() {
                    dp[slot(r)] = b;
                }
            }
        }
        // Undo the frame: δw = conj(U) δw̃, and so for the values.
        for t in 0..sites {
            for c in 0..m {
                let (ur, ui) = self.frame_placed(paces, t, place(t), c / n, c % n);
                let (ur, ui) = (ur as i128, ui as i128);
                for chart in [&mut dq, &mut dv, &mut dp] {
                    let (gr, gi) = (chart[t * m2 + c] as i128, chart[t * m2 + m + c] as i128);
                    chart[t * m2 + c] = fit64(release(ur * gr + ui * gi, MOVE_BITS))?;
                    chart[t * m2 + m + c] = fit64(release(ur * gi - ui * gr, MOVE_BITS))?;
                }
            }
        }
        // A paced head's frames turn its word, value and probe by `τ_t` (§16): `δτ_t += b Re(conj(δw) i w)` on
        // each, read in the unframed chart (the frame is a turn, so the pairing is the framed one's).
        for h in 0..heads {
            let Some(p) = paces.row[h] else { continue };
            for t in 0..sites {
                for li in 0..n {
                    let c = h * n + li;
                    let b = self.turn_rate(self.slot(h, li));
                    for (chart, word) in [(&dq, &cell.word), (&dv, &cell.vword), (&dp, &cell.probe)] {
                        let a = (chart[t * m2 + c] as i128, chart[t * m2 + m + c] as i128);
                        let z = (word[t * m2 + c] as i128, word[t * m2 + m + c] as i128);
                        gtau[p][t] += turned_back(b, a, z)?;
                    }
                }
            }
        }
        // The values' and the probes' covectors at the moment modes, summed over the ticks (§15.1, §16.20).
        for ((slot, &v), &p) in dm.iter_mut().zip(&dv).zip(&dp) {
            *slot += v as i128 + p as i128;
        }
        let reads: Vec<&[i32]> = cell.read.chunks_exact(dw).collect();
        let mut dr_all = vec![0i64; sites * dw];
        for (w, bias, reach_w, dfam) in [(l.q, l.q_bias, reaches.q, &dq), (l.v, l.v_bias, reaches.v, &dv), (l.probe, l.probe_bias, reaches.probe, &dp)] {
            let rows: Vec<&[i64]> = dfam.chunks_exact(m2).collect();
            outer_sum(&mut g[w..w + m2 * dw], dw, &rows, &reads)?;
            let mut back = vec![0i64; dw];
            for t in 0..sites {
                for (e, &v) in rows[t].iter().enumerate() {
                    g[bias + e] += v as i128;
                }
                transposed(&self.theta[w..w + m2 * dw], reach_w, dw, rows[t], MATERIAL_BITS, &mut back)?;
                for i in 0..dw {
                    dr_all[t * dw + i] = fit64(dr_all[t * dw + i] as i128 + back[i] as i128)?;
                }
            }
        }
        // [the lead, November 21] The friction's gate, a chart of the read with one output a head: `δa_h = Σ_t δψ_(t,h) r̂_t` on `2^(−40)`, and the
        // read takes `a_h δψ_(t,h)` back ([`Declaration::friction_gate`]).
        if d.friction_gate {
            let (at, len) = (l.friction_gate, heads * dw);
            let rows: Vec<&[i64]> = dgate.chunks_exact(heads).collect();
            outer_sum(&mut g[at..at + len], dw, &rows, &reads)?;
            let a = &self.theta[at..at + len];
            let amax = a.iter().map(|v| u64::from(v.unsigned_abs())).max().unwrap_or(0);
            let mut back = vec![0i64; dw];
            for t in 0..sites {
                transposed(a, amax, dw, rows[t], MATERIAL_BITS, &mut back)?;
                for i in 0..dw {
                    dr_all[t * dw + i] = fit64(dr_all[t * dw + i] as i128 + back[i] as i128)?;
                }
            }
        }
        for t in 0..sites {
            let back = lane_adjoint(reads[t], &cell.scale[t * lanes..(t + 1) * lanes], &dr_all[t * dw..(t + 1) * dw])?;
            for i in 0..dw {
                dx[t * dw + i] = fit64(dmid[t * dw + i] as i128 + back[i] as i128)?;
            }
        }
        Ok(())
    }

    /// [definition; the lead, November 18, the frontier record §6] **The strand's return**: the exact reverse of
    /// [`Constitution::strand_pass`] against the symbol at every place from the second, the code `Σ_(t≥1) −log₂ p̂_t(u_t)` of the passage
    /// in place order, its covector added into `g` on each family's natural grain. One return serves both streams:
    ///
    /// - each open place's face returns through the readout into its last state;
    /// - the ticks return in reverse through [`Constitution::tick_return`] over the joined sites, an open place's covectors on the keys,
    ///   values, strand contacts and circles it heard landing on the known sites it heard them from;
    /// - a tick's moments and clocks return as it ends: an open place's moment through the retarded moments' return on the clock it ran
    ///   on; its clock, one stride past the known site before it, to that site's clock and (from the second tick) to its stride, which it
    ///   read from its own face a tick earlier, so the stride's covector returns through that face into the state it was read off
    ///   ([`Constitution::blank_return`]) and into the paces' rows by the face's shares;
    /// - the known stream's moments and clocks, the same at every tick, return once at the end (no after row), its clocks to its strides
    ///   and their classes' paces; then the opening: the moment's chart, each known site's own row and the row of the site before it,
    ///   and each open place's unresolved row and the row of the site before it.
    ///
    /// Refused on a loud face and where the forward kept no ticks. A place is compared at weight one.
    /// [the lead, November 23] Each open place is compared with `targets` there ([`Region::targets`]); the known stream is `classes`.
    pub(crate) fn strand_returned(&self, classes: &[usize], targets: &[usize], pass: &StrandForward, g: &mut [i128]) -> Result<()> {
        self.strand_returned_with(classes, targets, pass, g, None)
    }

    /// [measurement; the lead, November 22] [`Constitution::strand_returned`] with the covector each tick's reverse receives (`λ^(k+1)` over
    /// the strand's `2n` sites, the known stream's then the open places', on the covector's grain), pushed in the reverse's order where
    /// `lambdas` is given: what a founding reads on the writer's own regime ([`Constitution::strand_tension`]). The return is the same.
    pub(crate) fn strand_returned_with(&self, classes: &[usize], targets: &[usize], pass: &StrandForward, g: &mut [i128], mut lambdas: Option<&mut Vec<Vec<i64>>>) -> Result<()> {
        let d = &self.declaration;
        if d.loud {
            return refuse("a strand's return on a loud face");
        }
        let (dw, m, lanes) = (d.width, d.complex(), d.lanes);
        let m2 = 2 * m;
        let n = pass.known;
        let sites = 2 * n;
        if pass.ticks.len() != d.ticks || pass.last.len() != sites * dw || classes.len() != n || targets.len() != n {
            return refuse("a strand's reverse reads a forward of the same passage that held every tick");
        }
        let l = &self.layout;
        let reaches = self.reaches();
        let known = vec![false; n];
        // (the known stream's region: sided, so the opening's comparison below is the retarded one; it leaves out the places read and not
        // compared, [`UNCOMPARED`])
        let skipped = targets.contains(&UNCOMPARED).then_some(targets);
        let region = Region { classes, unresolved: &known, faces: &[], locked: &[], echo: &[], domain: None, port: None, before: true, strand: false, past: false, second: pass.second, targets: skipped };
        let paces = self.paces(&region)?;
        let paced = paces.kappa.len();
        let definite: Vec<bool> = (0..sites).map(|t| t < n).collect();
        let width = d.alphabet + 1;
        let moment_modes: Vec<bool> = (0..m).map(|c| d.carries_moment(c / d.modes) && !d.is_depth(c / d.modes)).collect();
        // Each open place's face against its symbol, through the readout into its last state.
        let mut dx = vec![0i64; sites * dw];
        {
            let reads: Vec<BlankRead> = (1..n).map(|t| self.face_of(&pass.last[(n + t) * dw..(n + t + 1) * dw], &reaches)).collect::<Result<_>>()?;
            let mut ys: Vec<Vec<i64>> = Vec::with_capacity(reads.len());
            for (t, read) in (1..n).zip(&reads) {
                // A place read and not compared ([`UNCOMPARED`]) takes no covector: its face's covector is zero, so every term it adds is
                // (its row of the readout's outer sum stands beside the others', as the card's weight zero leaves it).
                let dz = if targets[t] == UNCOMPARED { vec![0i64; read.face.masses.len()] } else { covector(&read.face, targets[t]) };
                for (o, &dzo) in dz.iter().enumerate() {
                    g[l.read_bias + o] += dzo as i128;
                }
                let mut dy = vec![0i64; dw];
                for (i, slot) in dy.iter_mut().enumerate() {
                    let sum: i128 = dz.iter().enumerate().map(|(c, &dzc)| dzc as i128 * self.theta[l.enc + c * dw + i] as i128).sum();
                    *slot = fit64(release(sum, STATE_BITS))?;
                }
                for (c, &dzc) in dz.iter().enumerate() {
                    for (i, &yi) in read.lift.iter().enumerate() {
                        g[l.enc + c * dw + i] += release(dzc as i128 * yi as i128, STATE_BITS);
                    }
                }
                for (i, &dyi) in dy.iter().enumerate() {
                    g[l.lift_bias + i] += dyi as i128;
                }
                let mut dr = vec![0i64; dw];
                transposed(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &dy, MATERIAL_BITS, &mut dr)?;
                let back = lane_adjoint(&read.read, &read.scale[..lanes], &dr)?;
                dx[(n + t) * dw..(n + t + 1) * dw].copy_from_slice(&back);
                ys.push(dy);
            }
            let xs: Vec<&[i32]> = reads.iter().map(|r| r.read.as_slice()).collect();
            outer_sum(&mut g[l.read..l.read + dw * dw], dw, &ys, &xs)?;
        }
        // The known stream's own clocks and moments take every tick's covectors and return once, at the end.
        let mut whole = ClockReturn::new(paced, n, m2);
        // The open places' moments are read on one clock at every tick (the bare one), so their covectors are summed over the ticks and
        // return once, as the known stream's do.
        let mut open_dm = vec![0i128; n * m2];
        let mut ended: Option<ClockReturn> = None;
        for (k, cell) in pass.ticks.iter().enumerate().rev() {
            let mut r = ClockReturn::new(paced, sites, m2);
            if let Some(out) = lambdas.as_deref_mut() {
                out.push(dx.clone());
            }
            self.tick_return(cell, &mut dx, g, &pass.paces[k], &definite, &mut r.dm, &mut r.gtau, &mut r.gsig, None, None, None, None)?;
            // The level, where the strand heard it before this tick ([`Constitution::scale_return_before`]).
            if let (Some(s), Some(sp)) = (self.scale.as_deref().filter(|s| s.split == k), pass.tower.as_ref()) {
                self.scale_return_before(s, sp, &mut dx, g)?;
            }
            if k > 0 {
                self.strand_clock_return(pass, &r, &mut whole, &mut open_dm);
            } else {
                ended = Some(r);
            }
        }
        let mut r = ended.ok_or(TowerError::Refused("a strand's reverse with no tick"))?;
        // The moment's chart into the opening (§16.22), over the known sites and the open places alike, on the first tick's moments.
        {
            let (mf, mfb) = (l.moment_face, l.moment_face_bias);
            let dxs: Vec<&[i64]> = dx.chunks_exact(dw).collect();
            let ss: Vec<&[i64]> = pass.moments[0].chunks_exact(m2).collect();
            outer_sum(&mut g[mf..mf + dw * m2], m2, &dxs, &ss)?;
            let mut back = vec![0i64; m2];
            for t in 0..sites {
                for (o, &v) in dxs[t].iter().enumerate() {
                    g[mfb + o] += v as i128;
                }
                transposed(&self.theta[mf..mf + dw * m2], reaches.moment_face, m2, dxs[t], MATERIAL_BITS, &mut back)?;
                for (slot, &b) in r.dm[t * m2..(t + 1) * m2].iter_mut().zip(&back) {
                    *slot += b as i128;
                }
            }
        }
        self.strand_clock_return(pass, &r, &mut whole, &mut open_dm);
        // The open places' moments: the retarded cavity moments of the known stream on its cavity clocks ([`Constitution::cavity_moments_sided`]),
        // returned once to the strands' rows before each place and to the clocks.
        self.cavity_moments_return(&region, &paces, &open_dm, g, &mut whole.gtau, &mut whole.gsig, false)?;
        // [definition; the lead, November 18] Where the field compares its opening, the strand compares the retarded one at every place (the
        // opening an open place begins from, [`Constitution::opening_compare_return`] on the known stream's region); its clocks' covectors
        // join the known stream's, folded into the strides below.
        if d.opening {
            self.opening_compare_return(&region, &paces, 0..n, g, &mut whole.gtau, &mut whole.gsig)?;
        }
        // The known stream's moments (no after row) and its clocks, to its strides and their classes' paces.
        for (k, slot) in whole.dm.iter_mut().enumerate() {
            if !moment_modes[(k % m2) % m] {
                *slot = 0;
            }
        }
        self.moments_return_sided(&region, &paces, &whole.dm, g, &mut whole.gtau, &mut whole.gsig, false)?;
        for p in 0..paced {
            let base = l.pace + p * width;
            let (mut tail_tau, mut tail_sig) = (0i128, 0i128);
            for k in (1..n).rev() {
                tail_tau += whole.gtau[p][k];
                tail_sig += whole.gsig[p][k];
                let dk = tail_tau + paces.kappa[p][k].signum() as i128 * tail_sig;
                if dk != 0 {
                    g[base + self.row(&region, k)] += dk << STATE_BITS;
                }
            }
        }
        // The openings' rows.
        let unresolved = l.enc + d.alphabet * dw;
        for t in 0..n {
            let (dk, dopen) = (&dx[t * dw..(t + 1) * dw], &dx[(n + t) * dw..(n + t + 1) * dw]);
            self.opening_return(&region, l.enc, t, dk, g, None);
            for (i, &v) in dopen.iter().enumerate() {
                g[unresolved + i] += v as i128;
            }
            if t > 0 {
                self.opening_return(&region, l.before, t - 1, dk, g, None);
                self.opening_return(&region, l.before, t - 1, dopen, g, None);
            }
            // [the record of the two streams §15] The row of the second place before, where the openings took it.
            if pass.second && t >= 2 {
                self.opening_return(&region, l.after, t - 2, dk, g, None);
                self.opening_return(&region, l.after, t - 2, dopen, g, None);
            }
        }
        Ok(())
    }

    /// One tick's moments and clocks in the strand's return ([`Constitution::strand_returned`]): `r` holds a tick's covectors over the joined
    /// sites. The known sites' halves join `whole`; the open places' moments' covectors join `open_dm` (they return once, on the one clock
    /// every tick read them on); and each open place's clock, the clock of the known site before it and one bare stride, returns to that
    /// site.
    fn strand_clock_return(&self, pass: &StrandForward, r: &ClockReturn, whole: &mut ClockReturn, open_dm: &mut [i128]) {
        let m2 = 2 * self.declaration.complex();
        let n = pass.known;
        for (slot, &v) in whole.dm.iter_mut().zip(&r.dm[..n * m2]) {
            *slot += v;
        }
        for (slot, &v) in open_dm.iter_mut().zip(&r.dm[n * m2..]) {
            *slot += v;
        }
        for p in 0..whole.gtau.len() {
            for t in 0..n {
                whole.gtau[p][t] += r.gtau[p][t];
                whole.gsig[p][t] += r.gsig[p][t];
            }
            for t in 1..n {
                whole.gtau[p][t - 1] += r.gtau[p][n + t];
                whole.gsig[p][t - 1] += r.gsig[p][n + t];
            }
        }
    }

    /// [`Constitution::returned`], with the contact covector's magnitude by where its pairs lie added into `shares`
    /// (`[h][near, far]`, [`Constitution::covector_shares`]) where given.
    pub(crate) fn returned_with(&self, region: &Region, pass: &Forward, g: &mut [i128], mut shares: Option<&mut [u128]>, mut currents: Option<&mut Vec<Vec<i64>>>, mut junction: Option<&mut Vec<(usize, Vec<i64>)>>, mut reach: Option<&mut Vec<[ReachSums; 2]>>, mut lambdas: Option<&mut Vec<Vec<i64>>>, opening: Option<&mut Vec<i64>>, mut at_scale: Option<&mut Vec<i64>>) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, lanes) = (d.width, d.complex(), d.lanes);
        let m2 = 2 * m;
        let sites = region.classes.len();
        let l = &self.layout;
        let reaches = self.reaches();
        if pass.ticks.len() != d.ticks {
            return refuse("a reverse reads a forward that held every tick");
        }
        let definite: Vec<bool> = (0..sites).map(|t| Self::definite(region, t)).collect();
        // The clocks' covectors (§16, Law 1): `[pace index][t]`, `2^24 ∂/∂τ_t` and `2^24 ∂/∂σ_t` on `2^(−24)`, and the
        // moments' `[t][2M]`, one set a clock (§16.44): the pass's, which the first tick and the opening read, and each
        // tick's own where its blanks ran at the faces the tick before gave them.
        let paced = pass.paces.kappa.len();
        let clocks: Vec<Option<&TickClock>> = std::iter::once(None).chain(pass.ticks.iter().map(|c| c.clock.as_deref())).collect();
        let mut returns: Vec<Option<ClockReturn>> = clocks.iter().map(|_| None).collect();
        returns[0] = Some(ClockReturn::new(paced, sites, m2));
        // The face, its covector weighed as the region's state in the joint code (§16.23): `release(δz · m/K)` on the
        // covector's grain, to the nearest, half away from zero.
        let mut dx = vec![0i64; sites * dw];
        // [the lead, November 17] The closed face's covectors on the last tick's rows, `[h][t]` a value a source ([`crate::closed`]).
        let known = Self::known_classes(region, d.alphabet);
        let mut closed_rows: Vec<Vec<i128>> = vec![Vec::new(); if d.closed > 0 { d.heads * sites } else { 0 }];
        {
            let (wm, wk) = region.weight();
            // A port's places take their coupling's covector (§16.24), every other open site its own place's.
            let ported = match region.port {
                Some(port) => Some((port.start, self.port_of(pass, &port)?.0)),
                None => None,
            };
            let mut ys: Vec<Vec<i64>> = Vec::new();
            let mut radial: Vec<i64> = Vec::new();
            let mut xs: Vec<&[i32]> = Vec::new();
            for t in 0..sites {
                let Some(face) = &pass.faces[t] else { continue };
                if pass.skip.get(t).copied().unwrap_or(false) {
                    continue;
                }
                // [definition; the lead, November 17] Where the face is the closed face ([`crate::closed`]) the comparison returns through the mixture:
                // the field's own covector scaled by the field's responsibility for the written class, each head's odds covector into the odds'
                // rows (`δL_h += δz_h r̂ᵀ`, `δℓ_h += δz_h`) and through them into the chart's covector, and each head's covector on its last-tick
                // row's shares, which the last tick's reverse adds to the row's own.
                let mix = pass.mixes.get(t).and_then(Option::as_ref);
                let mut dr_closed: Vec<i64> = Vec::new();
                let dz = match &ported {
                    Some((start, rows)) if t >= *start => rows[t - start].clone(),
                    _ => {
                        let mut dz = covector(mix.and_then(|m| m.field.as_ref()).unwrap_or(face), region.classes[t]);
                        if wm != wk {
                            for v in dz.iter_mut() {
                                *v = fit64(div_nearest(*v as i128 * wm as i128, wk as i128))?;
                            }
                        }
                        if let Some(m) = mix {
                            let last = pass.ticks.last().ok_or(TowerError::Refused("a mixture's reverse reads the last tick's rows"))?;
                            let rows: Vec<&[Source]> = (0..d.heads).map(|h| last.rows[h * sites + t].as_slice()).collect();
                            if let Some((rho, dzo, extra)) = self.closed_back(m, face, &rows, &known, region.classes[t], wm, wk)? {
                                for v in dz.iter_mut() {
                                    *v = fit64(release(*v as i128 * rho, crate::closed::CLOSED_BITS))?;
                                }
                                let rt = &pass.read[t * dw..(t + 1) * dw];
                                for (h, &dzh) in dzo.iter().enumerate() {
                                    g[l.closed_odds_bias + h] += dzh as i128;
                                    for (i, &ri) in rt.iter().enumerate() {
                                        g[l.closed_odds + h * dw + i] += dzh as i128 * ri as i128;
                                    }
                                }
                                dr_closed = vec![0i64; dw];
                                let odds = &self.theta[l.closed_odds..l.closed_odds + d.heads * dw];
                                transposed(odds, crate::width::reach(odds), dw, &dzo, MATERIAL_BITS, &mut dr_closed)?;
                                for (h, e) in extra.into_iter().enumerate() {
                                    closed_rows[h * sites + t] = e;
                                }
                            }
                        }
                        dz
                    }
                };
                for (o, &dzo) in dz.iter().enumerate() {
                    g[l.read_bias + o] += dzo as i128;
                }
                let y = &pass.lift[t * dw..(t + 1) * dw];
                // [Brandon, November 15 02:06Z] Through a loud face's sharpness: `δv_a = release(β δz_a, 16)` takes `δz`'s place below, `δβ =
                // release(Σ_a δz_a v_a, 16)`, then `δκ_ℓ = release(δβ λ_ℓ, 16)`, `δb = δβ`, and `δλ_ℓ = release(δβ κ_ℓ, 16)` returned radially into the
                // state the face read ([`Constitution::loud_radial`]).
                let sharp = self.loud_beta(&pass.scale[t * lanes..(t + 1) * lanes])?;
                let dz = match &sharp {
                    None => dz,
                    Some((beta, lambda)) => {
                        let mut dbeta = 0i128;
                        for (c, &dzc) in dz.iter().enumerate() {
                            let row = &self.theta[l.enc + c * dw..l.enc + (c + 1) * dw];
                            let v = release(row.iter().zip(y).map(|(&e, &yi)| e as i128 * yi as i128).sum(), STATE_BITS) as i128;
                            dbeta += dzc as i128 * v;
                        }
                        let dbeta = release(dbeta, FACE_BITS) as i128;
                        self.loud_return(lambda, dbeta, &pass.read[t * dw..(t + 1) * dw], &pass.scale[t * lanes..(t + 1) * lanes], g, &mut radial)?;
                        dz.iter().map(|&d| fit64(release(*beta * d as i128, FACE_BITS) as i128)).collect::<Result<Vec<i64>>>()?
                    }
                };
                // Through the encoding (§16.26): `δE(a)_i += release(δz_a y_i, 16)` a term, `δy_i = release(Σ_a δz_a E(a)_i, 16)`.
                let mut dy = vec![0i64; dw];
                for (i, slot) in dy.iter_mut().enumerate() {
                    let sum: i128 = dz.iter().enumerate().map(|(c, &dzc)| dzc as i128 * self.theta[l.enc + c * dw + i] as i128).sum();
                    *slot = fit64(release(sum, STATE_BITS))?;
                }
                for (c, &dzc) in dz.iter().enumerate() {
                    for (i, &yi) in y.iter().enumerate() {
                        g[l.enc + c * dw + i] += release(dzc as i128 * yi as i128, STATE_BITS);
                    }
                }
                for (i, &dyi) in dy.iter().enumerate() {
                    g[l.lift_bias + i] += dyi as i128;
                }
                let rt = &pass.read[t * dw..(t + 1) * dw];
                let mut dr = vec![0i64; dw];
                transposed(&self.theta[l.read..l.read + dw * dw], reaches.read, dw, &dy, MATERIAL_BITS, &mut dr)?;
                for (slot, &v) in dr.iter_mut().zip(&dr_closed) {
                    *slot = fit64(*slot as i128 + v as i128)?;
                }
                let back = lane_adjoint(rt, &pass.scale[t * lanes..(t + 1) * lanes], &dr)?;
                dx[t * dw..(t + 1) * dw].copy_from_slice(&back);
                if sharp.is_some() {
                    for (slot, &v) in dx[t * dw..(t + 1) * dw].iter_mut().zip(&radial) {
                        *slot = fit64(*slot as i128 + v as i128)?;
                    }
                }
                ys.push(dy);
                xs.push(rt);
            }
            outer_sum(&mut g[l.read..l.read + dw * dw], dw, &ys, &xs)?;
        }
        // [definition; the formal thread, November 21] The lane leak's strengths, and its stores' covector from the forward alone: each lane's
        // successive chart moves over the region's sites and the pass's ticks, `−Σ_(t, k≥1) ⟨Δr̂_t^k, Δr̂_t^(k−1)⟩` released by the face's grain
        // (the last move read from the state the last tick left).
        let leak_deltas: Option<Vec<i64>> = d.lane_leak.then(|| self.theta[l.lane_leak..l.lane_leak + d.lanes].iter().map(|&v| crate::contact::lane_leak_delta(v)).collect());
        if d.lane_leak {
            let lw = dw / d.lanes;
            let mut charts: Vec<&[i32]> = pass.ticks.iter().map(|c| c.read.as_slice()).collect();
            let last = pass.ticks.last().ok_or(TowerError::Refused("a lane leak's return reads a pass with no tick"))?;
            let mut end = vec![0i32; sites * dw];
            let (mut r, mut sc) = (Vec::with_capacity(dw), Vec::with_capacity(d.lanes));
            for t in 0..sites {
                r.clear();
                sc.clear();
                lane_chart(&last.after[t * dw..(t + 1) * dw], d.lanes, &mut r, &mut sc)?;
                end[t * dw..(t + 1) * dw].copy_from_slice(&r);
            }
            charts.push(&end);
            let mut ip = vec![0i128; d.lanes];
            for k in 1..charts.len() - 1 {
                let (a, b, c) = (charts[k - 1], charts[k], charts[k + 1]);
                for (i, slot) in (0..sites * dw).map(|i| (i, (i % dw) / lw)) {
                    ip[slot] += (i128::from(b[i]) - i128::from(a[i])) * (i128::from(c[i]) - i128::from(b[i]));
                }
            }
            for (lane, &v) in ip.iter().enumerate() {
                g[l.lane_leak + lane] -= release(v, FACE_BITS);
            }
        }
        let mut opening_owed = vec![0i128; if leak_deltas.is_some() { dx.len() } else { 0 }];
        // [theory, November 13, the junction record §7] What a tick's return owes the state the tick before began from, `−Γ^(k+1) λ^(k+2)`.
        let mut owed: Option<Vec<i64>> = None;
        for (k, cell) in pass.ticks.iter().enumerate().rev() {
            let at = if cell.clock.is_some() { k + 1 } else { 0 };
            let r = returns[at].get_or_insert_with(|| ClockReturn::new(paced, sites, m2));
            // [measurement; §13.8] The covector this tick's reverse receives, `λ^(k+1)`, where read.
            if let Some(out) = lambdas.as_deref_mut() {
                out.push(dx.clone());
            }
            let leak_lambda: Option<Vec<i64>> = leak_deltas.as_ref().map(|_| dx.clone());
            let mut leak_lambda = leak_lambda;
            // The return after this tick: `dx` holds `λ^(k+1)` and becomes the output's `(1 + Γ) λ^(k+1)` ([`Constitution::junction_back`]).
            let joined = if cell.jg.is_empty() { None } else { Some(self.junction_back(cell, &mut dx)?) };
            self.tick_return(cell, &mut dx, g, pass.paces_at(cell), &definite, &mut r.dm, &mut r.gtau, &mut r.gsig, shares.as_deref_mut(), currents.as_deref_mut(), reach.as_deref_mut(), Some(closed_rows.as_slice()).filter(|c| !c.is_empty() && k + 1 == pass.ticks.len()))?;
            // Its chart's covector into the state this tick began from, then what the next tick's return owed that state; both before a level's
            // return, which reads the state as the tick began from it.
            let next_owed = match joined {
                Some((dl, back)) => {
                    self.junction_chart_back(cell, &dl, &reaches, &mut dx, g)?;
                    if let Some(out) = junction.as_deref_mut() {
                        out.push((k, dl));
                    }
                    Some(back)
                }
                None => None,
            };
            if let Some(o) = owed.take() {
                for (slot, &v) in dx.iter_mut().zip(&o) {
                    *slot = fit64(i128::from(*slot) + i128::from(v))?;
                }
            }
            owed = next_owed;
            // [definition; the formal thread, November 21] The lane leak's return into the state this tick began from, `−δ_ℓ λ^(k+1)`, and, the
            // opening held, `+δ_ℓ λ^(k+1)` into the opening (owed there once the ticks have returned; at the first tick the two cancel).
            if let (Some(deltas), Some(lam)) = (leak_deltas.as_deref(), leak_lambda.take()) {
                let lw = dw / deltas.len();
                for (i, (slot, &v)) in dx.iter_mut().zip(&lam).enumerate() {
                    let dl = deltas[(i % dw) / lw];
                    if dl != 0 {
                        let term = release(i128::from(dl) * i128::from(v), 30);
                        *slot = fit64(i128::from(*slot) - term)?;
                        opening_owed[i] += term;
                    }
                }
            }
            // [measurement] A forward that did not hear the level (a ruler's at `3` or `4`, a known stream's) returns nothing to it.
            if let Some(s) = self.scale.as_deref().filter(|s| s.split == k && self.levelled(region)) {
                let sp = pass.tower.as_ref().ok_or(TowerError::Refused("a tower's reverse reads a forward that held its scale"))?;
                // [measurement; the lead, November 17] The covector at the level's locus, of the state the prolongation wrote, where read.
                if let Some(out) = at_scale.as_deref_mut() {
                    *out = dx.clone();
                }
                self.scale_return(s, sp, &mut dx, g)?;
            }
            // [§16.44] A tick's own clock was read off the state this tick began from: its moments and rates return now,
            // and each blank's clock returns through its face into that state's covector.
            if let Some(c) = cell.clock.as_deref() {
                if let Some(mut r) = returns[at].take() {
                    self.clock_return(region, &c.paces, &c.blank, Some((&c.reads, &mut dx)), &mut r, g)?;
                }
            }
        }
        // [the formal thread, November 21] What the lane leak owes the opening it holds.
        if leak_deltas.is_some() {
            for (slot, &v) in dx.iter_mut().zip(&opening_owed) {
                *slot = fit64(i128::from(*slot) + v)?;
            }
        }
        // [measurement; November 13, the ring record's §4 first reading] The covector the opening receives, `λ⁰`, where read.
        if let Some(out) = opening {
            *out = dx.clone();
        }
        // The moment's chart into the face (§16.22): `δC += Σ_t δx⁰_t s_tᵀ`, `δb += Σ_t δx⁰_t`, and the moments'
        // covector `δs_t += Cᵀ δx⁰_t`, joined to the values' and the probes' before the strands' return.
        {
            let (mf, mfb) = (l.moment_face, l.moment_face_bias);
            let dxs: Vec<&[i64]> = dx.chunks_exact(dw).collect();
            let ss: Vec<&[i64]> = pass.moment.chunks_exact(m2).collect();
            outer_sum(&mut g[mf..mf + dw * m2], m2, &dxs, &ss)?;
            let mut back = vec![0i64; m2];
            let dm = &mut returns[0].as_mut().ok_or(TowerError::Refused("a reverse without the pass's clock"))?.dm;
            for t in 0..sites {
                for (o, &v) in dxs[t].iter().enumerate() {
                    g[mfb + o] += v as i128;
                }
                transposed(&self.theta[mf..mf + dw * m2], reaches.moment_face, m2, dxs[t], MATERIAL_BITS, &mut back)?;
                for (slot, &b) in dm[t * m2..(t + 1) * m2].iter_mut().zip(&back) {
                    *slot += b as i128;
                }
            }
        }
        // [theory, November 13, P60 item 1e] The opening's comparison at every place, where the field has the opening's lift: its covector joins the
        // last tick's in this one return, and its clocks' covectors join the pass's own before they fold into the strides.
        if d.opening {
            let r = returns[0].as_mut().ok_or(TowerError::Refused("a reverse without the pass's clock"))?;
            self.opening_compare_return(region, &pass.paces, 0..Self::opening_end(region), g, &mut r.gtau, &mut r.gsig)?;
        }
        // The pass's own clock (the first tick's and the opening's) returns last.
        if let Some(mut r) = returns[0].take() {
            self.clock_return(region, &pass.paces, &[], None, &mut r, g)?;
        }
        // The opening: each site's row of the encoding and its neighbours' rows of theirs (a carried
        // face's rows by their shares).
        for t in 0..sites {
            let dxt = &dx[t * dw..(t + 1) * dw];
            self.opening_return(region, l.enc, t, dxt, g, pass.marks.as_deref());
            if t > 0 {
                self.opening_return(region, l.before, t - 1, dxt, g, pass.marks.as_deref());
            }
            // [measurement] Under a ruler's `3` the opening read no row of the site after ([`Constitution::open_sided`]).
            if !self.sided(region) && t + 1 < sites {
                self.opening_return(region, l.after, t + 1, dxt, g, pass.marks.as_deref());
            }
            // [the record of the two streams §15] In a one-sided stream with the word, the opening read the row of the second site before.
            if self.second(region) && t >= 2 {
                self.opening_return(region, l.after, t - 2, dxt, g, pass.marks.as_deref());
            }
        }
        Ok(())
    }

    /// [§16, §16.44] **One clock's return**: the moments' covector at each moment mode through the strands, on the clock
    /// it was read on; then the clocks return to their paces: `τ_t = Σ_(0<k≤t) κ_k`, `σ_t = Σ_(0<k≤t) |κ_k|`, so `δκ_k =
    /// Σ_(t≥k) δτ_t + sgn(κ_k) Σ_(t≥k) δσ_t`; on the class sheet (§16.16) `κ_k = 1 + c[u_k]` gives `δc[u] += Σ_(k: u_k = u)
    /// δκ_k`, a carried face's classes by their shares, and a blank's by the shares of the face its clock read, on the
    /// material's covector grain (`2^(−24)` times the opening's `2^(−16)`, a whole class's share `2^16`); where the clock's
    /// blank reads are given, each blank's `δκ` also returns through its face into the state's covector
    /// ([`Constitution::blank_return`]). The opening takes nothing.
    #[allow(clippy::type_complexity)]
    pub(crate) fn clock_return(&self, region: &Region, paces: &Paces, blank: &[Option<Shares>], faces: Option<(&[Option<BlankRead>], &mut Vec<i64>)>, r: &mut ClockReturn, g: &mut [i128]) -> Result<()> {
        let d = &self.declaration;
        let (dw, m, n) = (d.width, d.complex(), d.modes);
        let m2 = 2 * m;
        let sites = region.classes.len();
        let paced = paces.kappa.len();
        let moment_modes: Vec<bool> = (0..m).map(|c| d.carries_moment(c / n) && !d.is_depth(c / n)).collect();
        for (k, slot) in r.dm.iter_mut().enumerate() {
            if !moment_modes[(k % m2) % m] {
                *slot = 0;
            }
        }
        self.moments_return(region, paces, &r.dm, g, &mut r.gtau, &mut r.gsig)?;
        if paced == 0 {
            return Ok(());
        }
        let l = &self.layout;
        let width = d.alphabet + 1;
        // Each blank's rates' covectors `(base, δκ)` a paced head, for its face's return.
        let mut rates: Vec<Vec<(usize, i128)>> = vec![Vec::new(); if faces.is_some() { sites } else { 0 }];
        let stretch = if self.per_blank_clock { sites } else { Self::silent_stretch(region) };
        for p in 0..paced {
            let base = l.pace + p * width;
            let head = (0..d.heads).find(|&h| paces.row[h] == Some(p)).ok_or(TowerError::Refused("a paced head with no row"))?;
            let (mut tail_tau, mut tail_sig) = (0i128, 0i128);
            let mut dks = vec![0i128; sites];
            for k in (1..sites).rev() {
                tail_tau += r.gtau[p][k];
                tail_sig += r.gsig[p][k];
                dks[k] = tail_tau + paces.kappa[p][k].signum() as i128 * tail_sig;
            }
            // [§16.47] The silent stretch past the last arrival runs at its first place's rate, so their covectors return there.
            if stretch < sites && !self.bare_stretch {
                let folded: i128 = dks[stretch + 1..].iter().sum();
                dks[stretch] += folded;
                for slot in &mut dks[stretch + 1..] {
                    *slot = 0;
                }
            }
            for k in (0..sites).rev() {
                let dk = dks[k];
                if dk == 0 {
                    continue;
                }
                let face = if Self::silent(region, k) { blank.get(k).and_then(Option::as_ref).filter(|_| !self.declaration.is_depth(head)) } else { Self::carried(region, k) };
                match face {
                    None if Self::silent(region, k) => {}
                    None => g[base + self.row(region, k)] += dk << STATE_BITS,
                    Some(face) => {
                        for &(c, w) in face {
                            g[base + c as usize] += dk * w as i128;
                        }
                        if Self::silent(region, k) && !rates.is_empty() {
                            rates[k].push((base, dk));
                        }
                    }
                }
            }
        }
        if let Some((reads, dx)) = faces {
            let reaches = self.reaches();
            for (t, rt) in rates.iter().enumerate().filter(|(_, rt)| !rt.is_empty()) {
                if let Some(Some(read)) = reads.get(t) {
                    self.blank_return(read, rt, &reaches, g, &mut dx[t * dw..(t + 1) * dw])?;
                }
            }
        }
        Ok(())
    }

    /// Each region's faces and the covector over the regions, summed in any order to the same bits.
    pub fn read_and_return(&self, regions: &[Region]) -> Result<(Vec<Vec<Option<TowerFace>>>, Vec<i128>)> {
        let len = self.material_len();
        let (mut faces, g) = regions
            .par_iter()
            .enumerate()
            .try_fold(
                || (Vec::new(), vec![0i128; len]),
                |(mut faces, mut g), (n, region)| -> Result<_> {
                    let pass = self.pass(region, true)?;
                    self.returned(region, &pass, &mut g)?;
                    faces.push((n, pass.faces));
                    Ok((faces, g))
                },
            )
            .try_reduce(
                || (Vec::new(), vec![0i128; len]),
                |(mut fa, mut ga), (fb, gb)| {
                    fa.extend(fb);
                    for (x, y) in ga.iter_mut().zip(gb) {
                        *x += y;
                    }
                    Ok((fa, ga))
                },
            )?;
        faces.sort_by_key(|(n, _)| *n);
        Ok((faces.into_iter().map(|(_, f)| f).collect(), self.both_reads_mean(g)))
    }
}

/// The adjoint of [`lane_chart`] at one site: each lane's covector through its own chart ([`ratio_adjoint`]).
pub(crate) fn lane_adjoint(read: &[i32], scales: &[i128], cov: &[i64]) -> Result<Vec<i64>> {
    let w = read.len() / scales.len();
    let mut out = Vec::with_capacity(read.len());
    for (k, &s) in scales.iter().enumerate() {
        out.extend(ratio_adjoint(&read[k * w..(k + 1) * w], s, &cov[k * w..(k + 1) * w])?);
    }
    Ok(out)
}

// The items this object owns that stood in the October tower until C5 (#603), each as it stood.

/// The covector a face returns when it is compared with `target`: `dz_c = p̂(c) − [c = target]` on
/// `2^(−24)`, the cross-entropy logit gradient `p − q` at the face's grain representative. The
/// reverse scan and the tension reading ([`Tower::read_tension`]) read this one law.
pub fn covector(face: &TowerFace, target: usize) -> Vec<i64> {
    (0..face.masses.len())
        .map(|c| {
            let p = ((face.masses[c] << COVECTOR_BITS) + face.total / 2) / face.total;
            p as i64 - if c == target { 1i64 << COVECTOR_BITS } else { 0 }
        })
        .collect()
}

/// `out[o] = release(Σ_i w[o·cols + i] x[i] + bias[o] · 2^bias_shift, shift)`, in `i64` where the
/// terms' bound allows and in `i128` otherwise; `x` a face carried in `i32` or `i64`.
pub fn affine<V: Copy + Into<i64>>(w: &[i32], wmax: u64, cols: usize, x: &[V], bias: Option<&[i32]>, bias_shift: u32, shift: u32, out: &mut [i64]) -> Result<()> {
    let xmax = x.iter().map(|&v| v.into().unsigned_abs()).max().unwrap_or(0);
    let terms = (wmax as u128) * (xmax as u128) * (cols as u128 + 1);
    if terms >= 1u128 << 126 {
        return refuse("an affine sum outgrew its 128-bit carrier");
    }
    let narrow = terms < (1u128 << 62);
    for (o, slot) in out.iter_mut().enumerate() {
        let row = &w[o * cols..(o + 1) * cols];
        let mut sum: i128 = if narrow {
            row.iter().zip(x).map(|(a, &b)| *a as i64 * b.into()).sum::<i64>() as i128
        } else {
            row.iter().zip(x).map(|(a, &b)| *a as i128 * b.into() as i128).sum::<i128>()
        };
        if let Some(b) = bias {
            sum += (b[o] as i128) << bias_shift;
        }
        *slot = fit64(release(sum, shift))?;
    }
    Ok(())
}

/// `out[i] = release(Σ_o w[o·cols + i] y[o], shift)`: the transposed read, `y` a covector (carried
/// in `i64`: the reverse scan accumulates a slow mode's covector over the section).
pub fn transposed(w: &[i32], wmax: u64, cols: usize, y: &[i64], shift: u32, out: &mut [i64]) -> Result<()> {
    let ymax = reach64(y);
    let rows = y.len();
    let narrow = (wmax as u128) * (ymax as u128) * (rows as u128 + 1) < (1u128 << 62);
    if narrow {
        let mut acc = vec![0i64; cols];
        for (o, &yo) in y.iter().enumerate() {
            if yo == 0 {
                continue;
            }
            let row = &w[o * cols..(o + 1) * cols];
            for (a, &wv) in acc.iter_mut().zip(row) {
                *a += wv as i64 * yo;
            }
        }
        for (slot, a) in out.iter_mut().zip(acc) {
            *slot = fit64(release(a as i128, shift))?;
        }
    } else {
        let mut acc = vec![0i128; cols];
        for (o, &yo) in y.iter().enumerate() {
            let row = &w[o * cols..(o + 1) * cols];
            for (a, &wv) in acc.iter_mut().zip(row) {
                *a += wv as i128 * yo as i128;
            }
        }
        for (slot, a) in out.iter_mut().zip(acc) {
            *slot = fit64(release(a, shift))?;
        }
    }
    Ok(())
}

/// `g[o·cols + i] += Σ_t y_t[o] x_t[i]`: a section's outer products of covectors with faces, at
/// their summed grain. Integer addition is associative, so summing over the section's cells before
/// the sum reaches the gradient gives the bits one product a cell gives; the sum runs in `i64` where
/// the terms' bound `Σ_t max|y_t| max|x_t|` allows it, in `i128` below `2^126`, and is refused past
/// it. A face `x` is carried in `i32` or `i64`.
pub fn outer_sum<Y: AsRef<[i64]>, X: AsRef<[V]>, V: Copy + Into<i64>>(g: &mut [i128], cols: usize, ys: &[Y], xs: &[X]) -> Result<()> {
    let mut bound = 0u128;
    for (y, x) in ys.iter().zip(xs) {
        let xmax = x.as_ref().iter().map(|&v| v.into().unsigned_abs()).max().unwrap_or(0);
        bound = bound.checked_add(reach64(y.as_ref()) as u128 * xmax as u128).filter(|&b| b < 1u128 << 126).ok_or(TowerError::Refused("an outer sum outgrew its 128-bit carrier"))?;
    }
    for (o, row) in g.chunks_exact_mut(cols).enumerate() {
        if bound < (1u128 << 62) {
            let mut acc = vec![0i64; cols];
            for (y, x) in ys.iter().zip(xs) {
                let yo = y.as_ref()[o];
                if yo != 0 {
                    for (a, &xv) in acc.iter_mut().zip(x.as_ref()) {
                        *a += yo * xv.into();
                    }
                }
            }
            for (slot, a) in row.iter_mut().zip(acc) {
                *slot += a as i128;
            }
        } else {
            for (y, x) in ys.iter().zip(xs) {
                let yo = y.as_ref()[o] as i128;
                if yo != 0 {
                    for (slot, &xv) in row.iter_mut().zip(x.as_ref()) {
                        *slot += yo * xv.into() as i128;
                    }
                }
            }
        }
    }
    Ok(())
}
