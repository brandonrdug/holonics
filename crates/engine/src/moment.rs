//! The engine's moment (C5 of #603: cut from `field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use crate::inherited::tower::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits_weighed, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, weighed_code, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
#[allow(unused_imports)]
use crate::inherited::keyed_modes::{ln2_face, log2_face, Exponential};
#[allow(unused_imports)]
use rayon::prelude::*;

impl Field {

    /// [measurement] A region's opening faces `x⁰` (`[t][D]` on `2^(−16)`), a reading for the receipts.
    pub fn opening(&self, region: &Region) -> Result<Vec<i64>> {
        self.admit_region(region)?;
        let paces = self.paces(region)?;
        let moment = self.moments_of(region, &paces)?;
        self.open(region, &moment, None)
    }

    /// [measurement; theory, November 13, P55 part B; the design record of November 13, §4.4] **A place's face at the region's opening**, before
    /// any tick: the opening `x⁰_t` (its row, its neighbours' rows and its moment from the region's other places, as `open` forms it) read through
    /// the readout at temperature one (`face_of`: the chart, the lift, the encoding). With `t` the region's one open, silent place this is its
    /// cavity opening by the built law. A reading: no state changes.
    pub fn opening_face(&self, region: &Region, t: usize) -> Result<TowerFace> {
        self.admit_region(region)?;
        let d = &self.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let sites = region.classes.len();
        if t >= sites {
            return Err(TowerError::Refused("an opening's place outside its region"));
        }
        let paces = self.paces(region)?;
        let moment = self.moments_of(region, &paces)?;
        let l = &self.layout;
        let mut xt = vec![0i64; dw];
        self.opening_term(region, l.enc, t, &mut xt, None);
        if t > 0 {
            self.opening_term(region, l.before, t - 1, &mut xt, None);
        }
        if t + 1 < sites {
            self.opening_term(region, l.after, t + 1, &mut xt, None);
        }
        let reach_c = reach(&self.theta[l.moment_face..l.moment_face + dw * m2]);
        let mut term = vec![0i64; dw];
        affine(&self.theta[l.moment_face..l.moment_face + dw * m2], reach_c, m2, &moment[t * m2..(t + 1) * m2], Some(&self.theta[l.moment_face_bias..l.moment_face_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut term)?;
        for (slot, &v) in xt.iter_mut().zip(&term) {
            *slot = fit64(*slot as i128 + v as i128)?;
        }
        self.readout_face(&xt, &self.reaches())
    }

    /// [measurement; theory, November 13, P55 part B] The same face from the whole opening (`open` over every place), the check of `opening_face`.
    pub fn opening_face_whole(&self, region: &Region, t: usize) -> Result<TowerFace> {
        let x = self.opening(region)?;
        let dw = self.declaration.width;
        self.readout_face(&x[t * dw..(t + 1) * dw], &self.reaches())
    }

    /// Site `s`'s opening term in the encoding at `base`: its row, or the superposition of its
    /// carried face's rows, `release(Σ_a w_a E(a), 16)`, added into `x`.
    pub(crate) fn opening_term(&self, region: &Region, base: usize, s: usize, x: &mut [i64], marks: Option<&[Option<Shares>]>) {
        let dw = self.declaration.width;
        match Self::carried(region, s) {
            None => {
                let start = base + self.row(region, s) * dw;
                for (slot, &e) in x.iter_mut().zip(&self.theta[start..start + dw]) {
                    *slot += e as i64;
                }
                // [the ring record §4; G176] A silent site's mark at its strength: the law's (the second read's marks at `α_b`), or the ruler's.
                if let Some((alpha, face)) = self.marked(region, base, s, marks) {
                    for (i, slot) in x.iter_mut().enumerate() {
                        let sum: i128 = face.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize * dw + i] as i128).sum();
                        let delta = release(sum, STATE_BITS) as i128 - self.theta[start + i] as i128;
                        *slot += release(alpha * delta, MATERIAL_BITS) as i64;
                    }
                }
            }
            Some(face) => {
                for (i, slot) in x.iter_mut().enumerate() {
                    let sum: i128 = face.iter().map(|&(c, w)| w as i128 * self.theta[base + c as usize * dw + i] as i128).sum();
                    *slot += release(sum, STATE_BITS) as i64;
                }
            }
        }
    }

    /// The opening term's return: `dx` into site `s`'s row, or each carried class's row by its
    /// share, `release(w_a dx, 16)` a term.
    pub(crate) fn opening_return(&self, region: &Region, base: usize, s: usize, dx: &[i64], g: &mut [i128], marks: Option<&[Option<Shares>]>) {
        let dw = self.declaration.width;
        match Self::carried(region, s) {
            None => {
                let start = base + self.row(region, s) * dw;
                // [the ring record §4] A marked site: `x = E(∗) + release(α Δ, 24)`, so `E(∗)` takes `dx − release(α dx, 24)`, each class's row
                // `release(w_c release(α dx, 24), 16)`, and the strength `Σ_i dx_i Δ_i` (the outer sum's grain). The ruler's mark returns nothing.
                match self.law_mark(region, base, s, marks) {
                    Some((alpha, face)) => {
                        let at = self.layout.mark + self.mark_base(base);
                        for i in 0..dw {
                            let a_dx = release(alpha * dx[i] as i128, MATERIAL_BITS);
                            g[start + i] += dx[i] as i128 - a_dx;
                            let mut sum = 0i128;
                            for &(c, w) in face {
                                g[base + c as usize * dw + i] += release(w as i128 * a_dx, STATE_BITS);
                                sum += w as i128 * self.theta[base + c as usize * dw + i] as i128;
                            }
                            g[at] += dx[i] as i128 * (release(sum, STATE_BITS) as i128 - self.theta[start + i] as i128);
                        }
                    }
                    None => {
                        for i in 0..dw {
                            g[start + i] += dx[i] as i128;
                        }
                    }
                }
            }
            Some(face) => {
                for &(c, w) in face {
                    for i in 0..dw {
                        g[base + c as usize * dw + i] += release(w as i128 * dx[i] as i128, STATE_BITS);
                    }
                }
            }
        }
    }

    /// [definition; agent-inferred, November 1] **Each site's moments** (§15.1, [`moment::moments`]),
    /// `[t][2M]` on `2^(−16)`, nonzero only at the modes that carry one: mode `l` of a turned head reads
    /// the strands' moment encodings `E⁺`, `E⁻` (a site's class row or its carried mixture; nothing from a silent
    /// open site, §16.28) on its own ring and skin.
    pub(crate) fn moments_of(&self, region: &Region, paces: &Paces) -> Result<Vec<i64>> {
        let d = &self.declaration;
        let (m, n, sites, tm) = (d.complex(), d.modes, region.classes.len(), d.moment_modes());
        let mut out = vec![0i64; sites * 2 * m];
        if tm == 0 {
            return Ok(out);
        }
        let l = &self.layout;
        let rows = |base: usize| -> Vec<Vec<i64>> { (0..sites).map(|t| self.strand_row(region, base, 2 * tm, t)).collect() };
        let (eb, ea) = (rows(l.moment_before), rows(l.moment_after));
        for h in (0..d.heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
            for li in 0..n {
                let idx = d.moment_index(h) + li;
                let slot = self.slot(h, li);
                let (period, ring) = &self.rings[slot];
                let pick = |e: &[Vec<i64>]| -> Vec<(i64, i64)> { e.iter().map(|r| (r[idx], r[tm + idx])).collect() };
                let (turn, skin) = (|r: i128| self.turn(slot, r), |s: i128| self.skin(slot, s));
                let pace = self.pace_of(paces, h, &turn, &skin);
                let s = moment::moments(&pick(&eb), &pick(&ea), ring, *period, &self.decays[slot], pace.as_ref())?;
                for (t, &(re, im)) in s.iter().enumerate() {
                    out[t * 2 * m + h * n + li] = re;
                    out[t * 2 * m + m + h * n + li] = im;
                }
            }
        }
        Ok(out)
    }

    /// [definition; theory, November 13, the design record of that day §4.4a] **Each place's cavity moment** `[t][2M]` on `2^(−16)`
    /// ([`moment::cavity_moments`]): the moment the region's other places bring to `t` at their standing phases, `t`'s own terms absent and its
    /// own stride bare (`κ_t = 1`, the rate of a silent place, §16.28), from the region's standing sums: the strands' rows as the region holds
    /// them, and on a paced head `t`'s cavity clock `τ_(t−1) + 1`, `σ_(t−1) + 1` (zero at the region's first place, whose clock is zero either way).
    pub(crate) fn cavity_moments_of(&self, region: &Region, paces: &Paces) -> Result<Vec<i64>> {
        let d = &self.declaration;
        let (m, n, sites, tm) = (d.complex(), d.modes, region.classes.len(), d.moment_modes());
        let mut out = vec![0i64; sites * 2 * m];
        if tm == 0 {
            return Ok(out);
        }
        let l = &self.layout;
        let rows = |base: usize| -> Vec<Vec<i64>> { (0..sites).map(|t| self.strand_row(region, base, 2 * tm, t)).collect() };
        let (eb, ea) = (rows(l.moment_before), rows(l.moment_after));
        for h in (0..d.heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
            let (tau_c, sigma_c) = Self::cavity_clocks(paces, h, sites);
            for li in 0..n {
                let idx = d.moment_index(h) + li;
                let slot = self.slot(h, li);
                let (period, ring) = &self.rings[slot];
                let pick = |e: &[Vec<i64>]| -> Vec<(i64, i64)> { e.iter().map(|r| (r[idx], r[tm + idx])).collect() };
                let (turn, skin) = (|r: i128| self.turn(slot, r), |s: i128| self.skin(slot, s));
                let pace = self.pace_of(paces, h, &turn, &skin);
                let s = moment::cavity_moments(&pick(&eb), &pick(&ea), ring, *period, &self.decays[slot], pace.as_ref(), &tau_c, &sigma_c)?;
                for (t, &(re, im)) in s.iter().enumerate() {
                    out[t * 2 * m + h * n + li] = re;
                    out[t * 2 * m + m + h * n + li] = im;
                }
            }
        }
        Ok(out)
    }

    /// [definition; theory, November 13, the design record of that day §4.4a] **A paced head's cavity clocks** `(τ_c, σ_c)` over a region: at each
    /// place the clocks it would hold silent, `τ_(t−1) + 1` and `σ_(t−1) + 1` (zero at the region's first place, whose clock is zero either way);
    /// empty where the head reads no pace.
    pub(crate) fn cavity_clocks(paces: &Paces, h: usize, sites: usize) -> (Vec<i64>, Vec<i64>) {
        let one = 1i64 << PACE_BITS;
        let cavity = |clock: &[i64]| -> Vec<i64> { (0..sites).map(|t| if t == 0 { 0 } else { clock[t - 1] + one }).collect() };
        match paces.row.get(h).copied().flatten() {
            Some(p) => (cavity(&paces.tau[p]), cavity(&paces.sigma[p])),
            None => (Vec::new(), Vec::new()),
        }
    }

    /// [definition; theory, November 13, the design record of that day §4.4 and §4.4a] **Each place's cavity opening** `[t][D]` on the opening's
    /// grain: `x^cav_t = E(∗) + E₋(u_(t−1)) + E₊(u_(t+1)) + release(C s^cav_t + b_s, 24)`, the unresolved row in place of the place's own, its two
    /// neighbours' strand rows as the region holds them (a carried neighbour by its mixture), and the moment's chart on the cavity moment
    /// ([`Field::cavity_moments_of`]). At an open, silent place it is the built opening. Formed from the region's sums once, never by rebuilding
    /// the region once a place. A reading and the opening's comparison's operand: no state changes.
    pub fn cavity_openings(&self, region: &Region) -> Result<Vec<i64>> {
        self.admit_region(region)?;
        let paces = self.paces(region)?;
        Ok(self.cavity_forward(region, &paces)?.0)
    }

    /// The cavity openings ([`Field::cavity_openings`]) and the cavity moments they read, on the region's clocks `paces`.
    pub(crate) fn cavity_forward(&self, region: &Region, paces: &Paces) -> Result<(Vec<i64>, Vec<i64>)> {
        let d = &self.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let sites = region.classes.len();
        let moment = self.cavity_moments_of(region, paces)?;
        let l = &self.layout;
        let reach_c = reach(&self.theta[l.moment_face..l.moment_face + dw * m2]);
        let unresolved = l.enc + d.alphabet * dw;
        let mut x = vec![0i64; sites * dw];
        let mut term = vec![0i64; dw];
        for (t, xt) in x.chunks_exact_mut(dw).enumerate() {
            for (slot, &e) in xt.iter_mut().zip(&self.theta[unresolved..unresolved + dw]) {
                *slot += e as i64;
            }
            if t > 0 {
                self.opening_term(region, l.before, t - 1, xt, None);
            }
            if t + 1 < sites {
                self.opening_term(region, l.after, t + 1, xt, None);
            }
            affine(&self.theta[l.moment_face..l.moment_face + dw * m2], reach_c, m2, &moment[t * m2..(t + 1) * m2], Some(&self.theta[l.moment_face_bias..l.moment_face_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut term)?;
            for (slot, &v) in xt.iter_mut().zip(&term) {
                *slot = fit64(*slot as i128 + v as i128)?;
            }
        }
        Ok((x, moment))
    }

    /// [definition; theory, November 13, P60 item 1d] **The places the opening compares**: every place of the region before its port (a port's places
    /// take their coupling's comparison at the last tick, which names no class; `agent-inferred`), written or open.
    pub(crate) fn opening_end(region: &Region) -> usize {
        region.port.map_or(region.classes.len(), |p| p.start)
    }

    /// [definition; theory, November 13, P60 item 1d] **The opening's read of a cavity opening** `x` (`D` words): the lane chart `r̂`, the opening's
    /// lift `y⁰ = R⁰ r̂ + b⁰` (its own block, founded at zero), the face through the encoding (`tied`) at temperature one: the forms [`Field::face_of`]
    /// uses with the opening's block in place of the read block. `reach_o` is the opening block's reach.
    pub(crate) fn opening_read(&self, x: &[i64], reach_o: u64) -> Result<BlankRead> {
        let (d, l) = (&self.declaration, &self.layout);
        let dw = d.width;
        let (mut r, mut s) = (Vec::with_capacity(dw), Vec::with_capacity(d.lanes));
        lane_chart(x, d.lanes, &mut r, &mut s)?;
        let mut y = vec![0i64; dw];
        affine(&self.theta[l.opening..l.opening + dw * dw], reach_o, dw, &r, Some(&self.theta[l.opening_bias..l.opening_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut y)?;
        let mut z = vec![0i64; d.alphabet];
        self.tied(&y, &mut z)?;
        Ok(BlankRead { read: r, scale: s, lift: y, face: self.tempered(&z, 1) })
    }

    /// [measurement; theory, November 13, G150's premise] **Each turned head's clock over a region**: its variation `σ_h(t)` on the pace grain
    /// (`2^(−24)`), the clock its skins read, one row a paced head in the order of [`FieldDeclaration::paced_heads`]. A reading: no state changes.
    pub fn head_variations(&self, region: &Region) -> Result<Vec<Vec<i64>>> {
        self.admit_region(region)?;
        Ok(self.paces(region)?.sigma)
    }

    /// [measurement; theory, November 13, P60 items 1d and 7] **The opening's faces at every place** of a region: each place's cavity opening read
    /// through the opening's lift ([`Field::opening_read`]), written or open. Refused on a field without the opening's block. A reading: no state
    /// changes; in a release it is read and compared with nothing.
    pub fn opening_faces(&self, region: &Region) -> Result<Vec<TowerFace>> {
        if !self.declaration.opening {
            return refuse("an opening's faces on a field without the opening's lift");
        }
        let dw = self.declaration.width;
        let (x, _) = {
            self.admit_region(region)?;
            let paces = self.paces(region)?;
            self.cavity_forward(region, &paces)?
        };
        let l = &self.layout;
        let reach_o = reach(&self.theta[l.opening..l.opening + dw * dw]);
        x.chunks_exact(dw).map(|xt| Ok(self.opening_read(xt, reach_o)?.face)).collect()
    }

    /// [definition; theory, November 13, P60 item 1d] **The opening's code at every compared place** ([`Field::opening_end`]): `−log₂ p̂⁰_t(u_t)` on
    /// `2^(−20)` bits, the class the passage holds at the place (at a masked place the class the last tick is compared with), `None` past the
    /// region's port. Empty on a field without the opening's block.
    pub fn opening_codes(&self, region: &Region) -> Result<Vec<Option<i64>>> {
        if !self.declaration.opening {
            return Ok(Vec::new());
        }
        let end = Self::opening_end(region);
        Ok(self.opening_faces(region)?.iter().enumerate().map(|(t, f)| (t < end).then(|| f.code(region.classes[t]))).collect())
    }

    /// [definition; theory, November 13, P60 item 1e] **The opening's comparison returned through the operands that produced it**: at every compared
    /// place, the covector face minus the class's indicator at unit gain (`covector`, no domain weight) through the encoding's bias and rows
    /// (`tied`), the opening's lift and bias, the chart and its lanes; then the cavity opening's covector into the unresolved row, the two
    /// neighbours' strand rows, the moment's chart and bias, and through the chart into the cavity moments' covector, which returns to the other
    /// places' moment terms ([`Field::cavity_moments_return`]) and their clocks (added into `gtau`, `gsig`, the region's own clock's covectors,
    /// folded into the strides with the pass's own). No place's own row, own moment term or own stride is an operand of its comparison, so none is
    /// returned to.
    ///
    /// `places` are the places compared, `0..opening_end` in the law (a test reads one place's return alone).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn opening_compare_return(&self, region: &Region, paces: &Paces, places: std::ops::Range<usize>, g: &mut [i128], gtau: &mut [Vec<i128>], gsig: &mut [Vec<i128>]) -> Result<()> {
        let d = &self.declaration;
        let (dw, m2, a, lanes) = (d.width, 2 * d.complex(), d.alphabet, d.lanes);
        let sites = region.classes.len();
        if places.end > Self::opening_end(region) {
            return refuse("an opening compared past its region's compared places");
        }
        let l = &self.layout;
        let reaches = self.reaches();
        let reach_o = reach(&self.theta[l.opening..l.opening + dw * dw]);
        let (x, moment) = self.cavity_forward(region, paces)?;
        let mut dx = vec![0i64; sites * dw];
        let (mut ys, mut rs): (Vec<Vec<i64>>, Vec<Vec<i32>>) = (Vec::new(), Vec::new());
        for t in places.clone() {
            let read = self.opening_read(&x[t * dw..(t + 1) * dw], reach_o)?;
            let dz = covector(&read.face, region.classes[t]);
            for (o, &dzo) in dz.iter().enumerate() {
                g[l.read_bias + o] += dzo as i128;
            }
            // Through the encoding: `δE(c)_i += release(δz_c y⁰_i, 16)`, `δy⁰_i = release(Σ_c δz_c E(c)_i, 16)`.
            let mut dy = vec![0i64; dw];
            for (i, slot) in dy.iter_mut().enumerate() {
                let sum: i128 = dz.iter().enumerate().map(|(c, &dzc)| dzc as i128 * self.theta[l.enc + c * dw + i] as i128).sum();
                *slot = fit64(release(sum, STATE_BITS))?;
            }
            for (c, &dzc) in dz.iter().enumerate().take(a) {
                for (i, &yi) in read.lift.iter().enumerate() {
                    g[l.enc + c * dw + i] += release(dzc as i128 * yi as i128, STATE_BITS);
                }
            }
            for (i, &dyi) in dy.iter().enumerate() {
                g[l.opening_bias + i] += dyi as i128;
            }
            let mut dr = vec![0i64; dw];
            transposed(&self.theta[l.opening..l.opening + dw * dw], reach_o, dw, &dy, MATERIAL_BITS, &mut dr)?;
            let back = lane_adjoint(&read.read, &read.scale[..lanes], &dr)?;
            dx[t * dw..(t + 1) * dw].copy_from_slice(&back);
            ys.push(dy);
            rs.push(read.read);
        }
        let xs: Vec<&[i32]> = rs.iter().map(Vec::as_slice).collect();
        outer_sum(&mut g[l.opening..l.opening + dw * dw], dw, &ys, &xs)?;
        // The cavity opening's covector: the unresolved row, the neighbours' strand rows, and the moment's chart on the cavity moment.
        let unresolved = l.enc + a * dw;
        let (mf, mfb) = (l.moment_face, l.moment_face_bias);
        let dxs: Vec<&[i64]> = dx.chunks_exact(dw).collect();
        let ss: Vec<&[i64]> = moment.chunks_exact(m2).collect();
        outer_sum(&mut g[mf..mf + dw * m2], m2, &dxs[places.clone()], &ss[places.clone()])?;
        let mut dm = vec![0i128; sites * m2];
        let mut back = vec![0i64; m2];
        for t in places {
            let dxt = dxs[t];
            for (i, &v) in dxt.iter().enumerate() {
                g[unresolved + i] += v as i128;
                g[mfb + i] += v as i128;
            }
            if t > 0 {
                self.opening_return(region, l.before, t - 1, dxt, g, None);
            }
            if t + 1 < sites {
                self.opening_return(region, l.after, t + 1, dxt, g, None);
            }
            transposed(&self.theta[mf..mf + dw * m2], reaches.moment_face, m2, dxt, MATERIAL_BITS, &mut back)?;
            for (slot, &b) in dm[t * m2..(t + 1) * m2].iter_mut().zip(&back) {
                *slot += b as i128;
            }
        }
        self.cavity_moments_return(region, paces, &dm, g, gtau, gsig)
    }

    /// [definition; theory, November 13, P60 item 1e] **The cavity moments' return** ([`moment::cavity_moments_return`]): the cavity moments'
    /// covector `dm` (`[t][2M]` on `2^(−24)`) back to the strands' moment encodings of the places that brought each term, and on a paced head to
    /// their clocks ([`moment::cavity_pace_return`]), added into `gtau`, `gsig`.
    pub(crate) fn cavity_moments_return(&self, region: &Region, paces: &Paces, dm: &[i128], g: &mut [i128], gtau: &mut [Vec<i128>], gsig: &mut [Vec<i128>]) -> Result<()> {
        let d = &self.declaration;
        let (m, n, sites, tm) = (d.complex(), d.modes, region.classes.len(), d.moment_modes());
        if tm == 0 {
            return Ok(());
        }
        let l = &self.layout;
        let rows = |base: usize| -> Vec<Vec<i64>> { (0..sites).map(|t| self.strand_row(region, base, 2 * tm, t)).collect() };
        let (eb, ea) = (rows(l.moment_before), rows(l.moment_after));
        let (mut db, mut da) = (vec![vec![0i128; 2 * tm]; sites], vec![vec![0i128; 2 * tm]; sites]);
        let side = |v: Vec<(i128, i128)>| -> Result<Vec<(i64, i64)>> { v.into_iter().map(|(re, im)| Ok((fit64(release(re, moment::COEFFICIENT_BITS))?, fit64(release(im, moment::COEFFICIENT_BITS))?))).collect() };
        for h in (0..d.heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
            let (tau_c, sigma_c) = Self::cavity_clocks(paces, h, sites);
            for li in 0..n {
                let idx = d.moment_index(h) + li;
                let slot = self.slot(h, li);
                let (period, ring) = &self.rings[slot];
                let ds: Vec<(i64, i64)> = (0..sites).map(|t| Ok((fit64(dm[t * 2 * m + h * n + li])?, fit64(dm[t * 2 * m + m + h * n + li])?))).collect::<Result<_>>()?;
                let (turn, skin) = (|r: i128| self.turn(slot, r), |s: i128| self.skin(slot, s));
                let pace = self.pace_of(paces, h, &turn, &skin);
                let (back_b, back_a) = moment::cavity_moments_return(&ds, ring, *period, &self.decays[slot], pace.as_ref(), &tau_c, &sigma_c)?;
                if let Some(p) = paces.row[h] {
                    let full = moment::Pace { tau: &paces.tau[p], sigma: &paces.sigma[p], turn: &turn, skin: &skin };
                    let pick = |e: &[Vec<i64>]| -> Vec<(i64, i64)> { e.iter().map(|r| (r[idx], r[tm + idx])).collect() };
                    let (before, after) = (pick(&eb), pick(&ea));
                    let parts = moment::cavity_moment_parts_exact(&before, &after, ring, *period, &self.decays[slot], pace.as_ref(), &tau_c, &sigma_c)?;
                    let (sb, sa): (Vec<_>, Vec<_>) = parts.into_iter().unzip();
                    let (sb, sa) = (side(sb)?, side(sa)?);
                    let (dt, dsg) = moment::cavity_pace_return(&before, &after, &sb, &sa, &ds, &back_b, &back_a, ring, *period, &self.decays[slot], &full, &tau_c, &sigma_c, self.turn_rate(slot))?;
                    for t in 0..sites {
                        gtau[p][t] += dt[t];
                        gsig[p][t] += dsg[t];
                    }
                }
                for t in 0..sites {
                    (db[t][idx], db[t][tm + idx]) = back_b[t];
                    (da[t][idx], da[t][tm + idx]) = back_a[t];
                }
            }
        }
        for t in 0..sites {
            self.strand_return(region, l.moment_before, 2 * tm, t, &db[t], g);
            self.strand_return(region, l.moment_after, 2 * tm, t, &da[t], g);
        }
        Ok(())
    }

    /// [measurement; theory, November 13, §4.4a's check] **The cavity openings against the region masked at each place**: for each place `t`, the
    /// built opening of the region with `t` unresolved and silent (`opening`), and the largest difference by word between it and `t`'s cavity
    /// opening ([`Field::cavity_openings`]), in units of the opening's last place, over every place, with the place it stood at. A reading.
    pub fn cavity_check(&self, region: &Region) -> Result<(u64, usize, usize)> {
        let dw = self.declaration.width;
        let cav = self.cavity_openings(region)?;
        let (mut worst, mut at, mut differ) = (0u64, 0usize, 0usize);
        for t in 0..region.classes.len() {
            let mut unresolved = region.unresolved.to_vec();
            unresolved[t] = true;
            let faces: Vec<Option<Shares>> = (0..region.classes.len()).map(|k| if k == t { None } else { region.faces.get(k).cloned().flatten() }).collect();
            let masked = Region { unresolved: &unresolved, faces: if region.faces.is_empty() { &[] } else { &faces }, ..*region };
            let x = self.opening(&masked)?;
            for (a, b) in x[t * dw..(t + 1) * dw].iter().zip(&cav[t * dw..(t + 1) * dw]) {
                let gap = a.abs_diff(*b);
                differ += usize::from(gap != 0);
                if gap > worst {
                    (worst, at) = (gap, t);
                }
            }
        }
        Ok((worst, at, differ))
    }

    /// The moments' return (§15.1, [`moment::moments_return`]): each moment mode's value covector summed
    /// over the ticks, `dm` (`[t][2M]` on `2^(−24)`), back to the strands' encodings.
    pub(crate) fn moments_return(&self, region: &Region, paces: &Paces, dm: &[i128], g: &mut [i128], gtau: &mut [Vec<i128>], gsig: &mut [Vec<i128>]) -> Result<()> {
        let d = &self.declaration;
        let (m, n, sites, tm) = (d.complex(), d.modes, region.classes.len(), d.moment_modes());
        if tm == 0 {
            return Ok(());
        }
        let l = &self.layout;
        let rows = |base: usize| -> Vec<Vec<i64>> { (0..sites).map(|t| self.strand_row(region, base, 2 * tm, t)).collect() };
        let (eb, ea) = (rows(l.moment_before), rows(l.moment_after));
        let (mut db, mut da) = (vec![vec![0i128; 2 * tm]; sites], vec![vec![0i128; 2 * tm]; sites]);
        for h in (0..d.heads).filter(|&h| d.carries_moment(h) && !d.is_depth(h)) {
            for li in 0..n {
                let idx = d.moment_index(h) + li;
                let slot = self.slot(h, li);
                let (period, ring) = &self.rings[slot];
                let ds: Vec<(i64, i64)> = (0..sites).map(|t| Ok((fit64(dm[t * 2 * m + h * n + li])?, fit64(dm[t * 2 * m + m + h * n + li])?))).collect::<Result<_>>()?;
                let (turn, skin) = (|r: i128| self.turn(slot, r), |s: i128| self.skin(slot, s));
                let pace = self.pace_of(paces, h, &turn, &skin);
                let (back_b, back_a) = moment::moments_return(&ds, ring, *period, &self.decays[slot], pace.as_ref())?;
                // A paced head's moments turn and decay by its clock (§16): their covector returns to it.
                if let Some(p) = paces.row[h] {
                    let full = moment::Pace { tau: &paces.tau[p], sigma: &paces.sigma[p], turn: &turn, skin: &skin };
                    let pick = |e: &[Vec<i64>]| -> Vec<(i64, i64)> { e.iter().map(|r| (r[idx], r[tm + idx])).collect() };
                    let (before, after) = (pick(&eb), pick(&ea));
                    let s = moment::moments(&before, &after, ring, *period, &self.decays[slot], pace.as_ref())?;
                    let (dt, dsg) = moment::pace_return(&before, &after, &s, &ds, &back_b, &back_a, ring, *period, &self.decays[slot], &full, self.turn_rate(slot))?;
                    for t in 0..sites {
                        gtau[p][t] += dt[t];
                        gsig[p][t] += dsg[t];
                    }
                }
                for t in 0..sites {
                    (db[t][idx], db[t][tm + idx]) = back_b[t];
                    (da[t][idx], da[t][tm + idx]) = back_a[t];
                }
            }
        }
        for t in 0..sites {
            self.strand_return(region, l.moment_before, 2 * tm, t, &db[t], g);
            self.strand_return(region, l.moment_after, 2 * tm, t, &da[t], g);
        }
        Ok(())
    }

    /// The region's opening faces `x⁰`: each site's row of the encoding with its strand
    /// neighbours' rows of their own encodings and its moment read through its chart,
    /// `x⁰_t = E(u_t) + E₋(u_(t−1)) + E₊(u_(t+1)) + release(C s_t + b, 24)` (§16.22; a region's first site has no
    /// site before it, its last none after), `moment` the region's moments `[t][2M]` ([`Field::moments_of`]).
    pub(crate) fn open(&self, region: &Region, moment: &[i64], marks: Option<&[Option<Shares>]>) -> Result<Vec<i64>> {
        let d = &self.declaration;
        let (dw, m2) = (d.width, 2 * d.complex());
        let sites = region.classes.len();
        let l = &self.layout;
        let reach_c = reach(&self.theta[l.moment_face..l.moment_face + dw * m2]);
        let mut x = vec![0i64; sites * dw];
        let mut term = vec![0i64; dw];
        for (t, xt) in x.chunks_exact_mut(dw).enumerate() {
            self.opening_term(region, l.enc, t, xt, marks);
            if t > 0 {
                self.opening_term(region, l.before, t - 1, xt, marks);
            }
            if t + 1 < sites {
                self.opening_term(region, l.after, t + 1, xt, marks);
            }
            affine(&self.theta[l.moment_face..l.moment_face + dw * m2], reach_c, m2, &moment[t * m2..(t + 1) * m2], Some(&self.theta[l.moment_face_bias..l.moment_face_bias + dw]), MATERIAL_BITS, MATERIAL_BITS, &mut term)?;
            for (slot, &v) in xt.iter_mut().zip(&term) {
                *slot = fit64(*slot as i128 + v as i128)?;
            }
        }
        Ok(x)
    }
}
