//! [definition; theory, November 13, the design record of that day §4.2 to §4.9 (`agent-inferred`)] **The level above**: level 0 is
//! the field on the places; level 1 is a field of its own on **epochs**, each led by a **site**, a landmark of the news below it. After
//! the fine field's first `split` ticks each epoch is opened on its places' reads charted by the **news phase**, the level's field runs its
//! own ticks on **its own clock**, the news between its sites, each place receives its epoch back through the same chart, and the fine
//! field's remaining ticks and its face follow:
//!
//! ```text
//! news      c_t        the opening's code: a written place's class at its cavity face, elsewhere the face's expected code
//! section   σ          the flat face's code over the alphabet: the news of one place nothing predicts
//! sites     ρ_t ≥ σ    ρ_t = min(S_t − S_u at the last u < t with c_u ≥ c_t, S_u − S_t at the first u > t with c_u > c_t), S the news's sum
//! phase     φ_t = (S_t − S_(a_j))/σ       from the anchor a_j of t's epoch (its site, or the region's first place before the first site)
//! chart     h(φ) = (1, cos 2πφ, sin 2πφ, cos 4πφ, sin 4πφ, cos 6πφ, …)   `harmonics` of them, each the field's turn at a declared width
//! restrict  x¹_j = A [m_0(j), …, m_(H−1)(j)] + b_A,   m_k(j) = release(Σ_(t∈e_j) h_k(φ_t) r̂(x_t), 30)
//! clock     τ¹_j = (S_(a_j) − S_(a_0))/σ,  κ¹_j = τ¹_j − τ¹_(j−1)        every turned head of the level on that one clock
//! prolong   x_t += release(Σ_k h_k(φ_t) v_k(j), 30),   v(j) = B r̂(x¹_j) + b_B        founded with B = 0, b_B = 0
//! ```
//!
//! An epoch is definite where every one of its places is, and keyed where any is. The cut, the phases and the clock are data: a carry
//! has no first-order return, so nothing returns to the news. The material is the fine field's, the level's field's and the glue (`A`,
//! `b_A`, `B`, `b_B`), in that order, one covector over all three ([`Field::material_len`], [`Field::families_all`]). Founded as a
//! growth in scale ([`Field::scaled_up`]): `B` and `b_B` open at zero, so the level reads every face of the field it was founded on.
//! With equal news a section a place and six harmonics, the chart is the discrete Fourier chart of six places: the packets of November
//! 3 (retired with this law) are its plain case.

use super::*;

/// The level's field above a field ([`Field::scaled_up`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scale {
    /// The harmonics of the news phase the glue charts (`h_0 = 1`, then a cosine and a sine a whole turn, the last a cosine where
    /// the count is even).
    pub harmonics: usize,
    /// The fine ticks read before the restriction, `0 < split < K`.
    pub split: usize,
    /// The level's field.
    pub coarse: Field,
    /// `A` (`D₁ × H D₀`, an epoch's harmonics of its places' reads) and `b_A` (`D₁`), then `B` (`H D₀ × D₁`) and `b_B` (`H D₀`, a bias
    /// a harmonic); matrices on `2^(−24)`, biases on the faces' `2^(−16)`.
    pub glue: Vec<i32>,
}

impl Scale {
    /// The glue's offsets of `A`, `b_A`, `B` and `b_B`, and its length, over a fine field of `fine_width` (a realization's
    /// read of [`Scale::glue`]).
    pub fn glue_offsets(&self, fine_width: usize) -> (usize, usize, usize, usize, usize) {
        glue_layout(self.harmonics, fine_width, self.coarse.declaration.width)
    }
}

/// The glue's offsets: `A`, `b_A`, `B`, `b_B` and the length.
pub(super) fn glue_len(harmonics: usize, fine: usize, coarse: usize) -> (usize, usize, usize, usize, usize) {
    glue_layout(harmonics, fine, coarse)
}

fn glue_layout(harmonics: usize, fine: usize, coarse: usize) -> (usize, usize, usize, usize, usize) {
    let a = 0;
    let ab = a + harmonics * coarse * fine;
    let b = ab + coarse;
    let bb = b + harmonics * fine * coarse;
    (a, ab, b, bb, bb + harmonics * fine)
}

/// [definition; theory, November 13, the design record §4.9 (`agent-inferred`)] **The level's field's declaration** over a field's `d`:
/// the fine field's with an alphabet of two (a level names no symbol), no triads, no carry circles, no opening of its own, and the ticks
/// the fine field has after its split (`d.ticks / 2` of them, the split [`level_split`]). Its reach is the fine field's: a region's
/// epochs are at most its places.
pub fn level_declaration(d: &FieldDeclaration) -> FieldDeclaration {
    FieldDeclaration { alphabet: 2, triads: 0, carry: 0, opening: false, ticks: d.ticks - level_split(d), ..*d }
}

/// The fine ticks before a level's restriction: half the fine field's, at least one.
pub fn level_split(d: &FieldDeclaration) -> usize {
    (d.ticks / 2).max(1)
}

/// The harmonics a level founded now charts (the design record §4.9: the packets' six, the discrete Fourier chart of six equal places
/// in real form; how many an epoch's interior needs is read on a state once epochs are cut).
pub const LEVEL_HARMONICS: usize = 6;

/// [definition; theory, November 13, the design record §4.6 and §4.9] **The level's section**: the flat face's code over `alphabet`
/// classes, on the code's grain (`2^(−20)` bits), the news of one place nothing predicts, so that under a flat face every place carries a
/// section and is a site (the founding is the identity).
pub fn level_section(alphabet: usize) -> i64 {
    face_code(1, alphabet.max(2) as u128)
}

/// [definition; theory, November 13, the record of the landmarks §5] **Each place's isolation** `ρ_t` over a region's news `c`: the
/// news to the nearest greater place on either side (`u ≻ t` where `c_u > c_t`, or `c_u = c_t` and `u < t`), `None` where no greater place
/// stands on either side. Two nearest-greater reads, one each way, on integer sums.
pub fn level_isolation(news: &[i64]) -> Vec<Option<i128>> {
    let n = news.len();
    let mut sum = vec![0i128; n + 1];
    for (t, &c) in news.iter().enumerate() {
        sum[t + 1] = sum[t] + c as i128;
    }
    // `S_t` is `sum[t + 1]`: the news up to and with place `t`.
    let s = |t: usize| sum[t + 1];
    let mut left: Vec<Option<usize>> = vec![None; n];
    let mut stack: Vec<usize> = Vec::new();
    for t in 0..n {
        // The last earlier place with news at least `c_t`.
        while let Some(&u) = stack.last() {
            if news[u] >= news[t] {
                break;
            }
            stack.pop();
        }
        left[t] = stack.last().copied();
        stack.push(t);
    }
    let mut right: Vec<Option<usize>> = vec![None; n];
    stack.clear();
    for t in (0..n).rev() {
        // The first later place with news greater than `c_t`.
        while let Some(&u) = stack.last() {
            if news[u] > news[t] {
                break;
            }
            stack.pop();
        }
        right[t] = stack.last().copied();
        stack.push(t);
    }
    (0..n)
        .map(|t| {
            let l = left[t].map(|u| s(t) - s(u));
            let r = right[t].map(|u| s(u) - s(t));
            match (l, r) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            }
        })
        .collect()
}

/// [definition; theory, November 13, the design record §4.2 and §4.9] **The anchors of a region's epochs**: its sites (`ρ_t ≥ σ`, a
/// place with no greater place on either side among them), each leading its epoch, after the region's first place where that is no site
/// (the leading epoch). Increasing, the first `0`; empty for an empty region.
pub fn level_anchors(news: &[i64], section: i64) -> Vec<usize> {
    if news.is_empty() {
        return Vec::new();
    }
    let rho = level_isolation(news);
    let mut out = vec![0usize];
    out.extend((1..news.len()).filter(|&t| rho[t].is_none_or(|r| r >= section as i128)));
    out
}

/// A region's cut for the level: its epochs' anchors, each place's epoch, each place's harmonics `[t][H]` on `2^(−30)` and the level's
/// clock on its epochs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LevelCut {
    pub anchors: Vec<usize>,
    pub epoch: Vec<usize>,
    pub harmonics: Vec<i64>,
    /// `τ¹_j` on `2^(−24)`: the news from the first epoch's anchor to epoch `j`'s, in sections.
    pub tau: Vec<i64>,
}

/// [definition; theory, November 13, the design record §4.5 and §4.9] **A region's cut** from its news: the anchors, each place's phase
/// `φ_t = (S_t − S_(a_j))/σ` on the pace grain (`2^(−24)`) and its `harmonics` on the turn's grain (`2^(−30)`, the field's turn on a ring
/// of one turn at `k φ_t`), and the level's clock `τ¹_j = (S_(a_j) − S_(a_0))/σ` on the pace grain, each a nearest quotient of the news's
/// integer sums by the section (released there, at the pace grain).
pub fn level_cut(news: &[i64], section: i64, harmonics: usize, pi: i128) -> Result<LevelCut> {
    if section <= 0 || harmonics == 0 {
        return refuse("a level's cut needs a positive section and a harmonic");
    }
    let anchors = level_anchors(news, section);
    let n = news.len();
    let mut sum = vec![0i128; n + 1];
    for (t, &c) in news.iter().enumerate() {
        if c < 0 {
            return refuse("a level's news below zero");
        }
        sum[t + 1] = sum[t] + c as i128;
    }
    let pace = |news: i128| div_nearest(news << PACE_BITS, section as i128);
    let mut epoch = vec![0usize; n];
    for (j, &a) in anchors.iter().enumerate() {
        let end = anchors.get(j + 1).copied().unwrap_or(n);
        epoch[a..end].fill(j);
    }
    let one = 1i64 << MOVE_BITS;
    let mut out = vec![0i64; n * harmonics];
    for t in 0..n {
        let phi = pace(sum[t + 1] - sum[anchors[epoch[t]] + 1]);
        let h = &mut out[t * harmonics..(t + 1) * harmonics];
        h[0] = one;
        for (i, slot) in h.iter_mut().enumerate().skip(1) {
            let k = i.div_ceil(2) as i128;
            let (re, im) = turn_phasor(k * phi, 1, pi);
            *slot = if i % 2 == 1 { re } else { im };
        }
    }
    let base = anchors.first().map_or(0, |&a| sum[a + 1]);
    let tau = anchors.iter().map(|&a| fit64(pace(sum[a + 1] - base))).collect::<Result<_>>()?;
    Ok(LevelCut { anchors, epoch, harmonics: out, tau })
}

/// What a level's forward keeps for its reverse.
#[derive(Clone, Debug, Default)]
pub(super) struct ScalePass {
    /// Each fine place's read at the split `[t][D₀]`, with its scale.
    read: Vec<i32>,
    scale: Vec<i128>,
    /// The region's cut, and each epoch's restricted harmonics `[j][H D₀]`.
    cut: LevelCut,
    restricted: Vec<i64>,
    /// The level's ticks, its read after the last `[j][D₁]` with its scale, and which epochs are definite.
    ticks: Vec<TickCell>,
    coarse_read: Vec<i32>,
    coarse_scale: Vec<i128>,
    definite: Vec<bool>,
    paces: Paces,
}

impl ScalePass {
    /// The level's ticks kept for the reverse.
    #[cfg(test)]
    pub(super) fn ticks(&self) -> &[TickCell] {
        &self.ticks
    }

    /// The region's cut the level read.
    #[cfg(test)]
    pub(super) fn cut(&self) -> &LevelCut {
        &self.cut
    }
}

/// [definition; theory, November 13, the design record §4.3 and §4.9] **The level's clock** on a region's epochs for every turned head:
/// `τ¹` the news between the anchors in sections, `κ¹_j = τ¹_j − τ¹_(j−1)` (the first epoch's rate one), its variation the same (the
/// rates are not negative), plain where every rate is one exactly.
fn level_paces(d: &FieldDeclaration, cut: &LevelCut) -> Result<Paces> {
    let one = 1i64 << PACE_BITS;
    let kappa: Vec<i64> = (0..cut.tau.len()).map(|j| if j == 0 { one } else { cut.tau[j] - cut.tau[j - 1] }).collect();
    let plain = kappa.iter().all(|&k| k == one);
    let mut out = Paces { row: vec![None; d.heads], ..Default::default() };
    for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
        out.row[h] = Some(out.kappa.len());
        out.kappa.push(kappa.clone());
        out.tau.push(cut.tau.clone());
        out.sigma.push(cut.tau.clone());
        out.plain.push(plain);
    }
    Ok(out)
}

/// `out[j][k D₀ + c] += Σ_(t∈e_j) h_k(φ_t) rows[t][c]`, released by 30 once an entry (the chart's sums over an epoch's places).
fn charted<V: Copy + Into<i64>>(cut: &LevelCut, h: usize, rows: &[V], width: usize) -> Result<Vec<i64>> {
    let epochs = cut.anchors.len();
    let mut acc = vec![0i128; epochs * h * width];
    for (t, &j) in cut.epoch.iter().enumerate() {
        let ht = &cut.harmonics[t * h..(t + 1) * h];
        let row = &rows[t * width..(t + 1) * width];
        let slot = &mut acc[j * h * width..(j + 1) * h * width];
        for (k, &hk) in ht.iter().enumerate() {
            for (c, &v) in row.iter().enumerate() {
                slot[k * width + c] += hk as i128 * v.into() as i128;
            }
        }
    }
    acc.into_iter().map(|v| fit64(release(v, MOVE_BITS))).collect()
}

/// Place `t`'s row from its epoch's harmonic blocks `v` (`[H][width]`): `release(Σ_k h_k(φ_t) v_k, 30)`.
fn uncharted(ht: &[i64], v: &[i64], width: usize, out: &mut [i64]) -> Result<()> {
    for (c, slot) in out.iter_mut().enumerate() {
        let sum: i128 = ht.iter().enumerate().map(|(k, &hk)| hk as i128 * v[k * width + c] as i128).sum();
        *slot = fit64(release(sum, MOVE_BITS))?;
    }
    Ok(())
}

impl Field {
    /// The material's length: the field's, and with a level the level's field's and the glue's.
    pub fn material_len(&self) -> usize {
        self.theta.len() + self.scale.as_ref().map_or(0, |s| s.coarse.theta.len() + s.glue.len())
    }

    /// Every family of the material, `(start, len, grain)` over [`Field::material_len`].
    pub fn families_all(&self) -> Vec<(usize, usize, u32)> {
        let mut out = self.layout.families.clone();
        if let Some(s) = &self.scale {
            let base = self.theta.len();
            out.extend(s.coarse.layout.families.iter().map(|&(start, len, grain)| (base + start, len, grain)));
            let at = base + s.coarse.theta.len();
            let (d0, d1) = (self.declaration.width, s.coarse.declaration.width);
            let (a, ab, b, bb, _) = glue_layout(s.harmonics, d0, d1);
            out.extend([(at + a, ab - a, MATERIAL_BITS), (at + ab, d1, FACE_BITS), (at + b, bb - b, MATERIAL_BITS), (at + bb, s.harmonics * d0, FACE_BITS)]);
        }
        out
    }

    /// The material entry `i` of [`Field::material_len`].
    pub fn material(&self) -> impl Iterator<Item = &i32> {
        let (coarse, glue): (&[i32], &[i32]) = match self.scale.as_deref() {
            Some(s) => (&s.coarse.theta[..], &s.glue[..]),
            None => (&[], &[]),
        };
        self.theta.iter().chain(coarse.iter()).chain(glue.iter())
    }

    /// The material entry `i` of [`Field::material_len`], mutable.
    pub fn material_mut(&mut self) -> impl Iterator<Item = &mut i32> {
        let (coarse, glue): (&mut [i32], &mut [i32]) = match self.scale.as_deref_mut() {
            Some(s) => (&mut s.coarse.theta[..], &mut s.glue[..]),
            None => (&mut [], &mut []),
        };
        self.theta.iter_mut().chain(coarse.iter_mut()).chain(glue.iter_mut())
    }

    /// [definition; theory, November 13, the design record §4.4 and §4.9] **The news of every place** of a region, on the code's grain: at
    /// a written place (definite) the code of its class at its opening face, elsewhere the face's expected code `Σ_a p̃_t(a) code_t(a)`
    /// (a nearest quotient of the masses' sum by the total). An open place's class is its comparison's target and is never read here.
    /// Refused on a field without the opening's block.
    pub fn level_news(&self, region: &Region) -> Result<Vec<i64>> {
        let faces = self.opening_faces(region)?;
        faces
            .iter()
            .enumerate()
            .map(|(t, f)| {
                if Self::definite(region, t) {
                    return Ok(f.code(region.classes[t]));
                }
                let sum: i128 = f.masses.iter().map(|&m| m as i128 * face_code(m, f.total) as i128).sum();
                fit64(div_nearest(sum, f.total as i128))
            })
            .collect()
    }

    /// [definition; theory, November 13, the design record §4.9] **Growth in scale**: this field with a level of `harmonics` after `split`
    /// of its ticks, the level's field founded on its own `declaration` from the key stream at `offset`, the restriction's `A` drawn after
    /// it on `±√(3/(H D₀))`, and `b_A`, `B`, `b_B` at zero, so every face reads as before. The level reads the opening's news, so the field
    /// carries the opening's block. Returns the tower and the key bytes read through.
    pub fn scaled_up(&self, harmonics: usize, split: usize, declaration: FieldDeclaration, keys: &[u8], offset: usize) -> Result<(Self, usize)> {
        if self.scale.is_some() || harmonics == 0 || split == 0 || split >= self.declaration.ticks || !self.declaration.opening || declaration.opening {
            return refuse("a level needs a field with the opening's block and without a level, a harmonic, and a split inside the ticks; the level's own field has no opening");
        }
        let coarse = Field::found(declaration, keys.get(offset..).ok_or(TowerError::Refused("a key file shorter than a level's founding"))?)?;
        let mut at = offset + 4 * declaration.founding_draws();
        let (d0, d1) = (self.declaration.width, declaration.width);
        let (a, ab, _, _, len) = glue_layout(harmonics, d0, d1);
        let mut glue = vec![0i32; len];
        let ((three, _), (_, pd)) = (chart_scale(d0), chart_scale(harmonics * d0));
        for v in &mut glue[a..ab] {
            let word = keys.get(at..at + 4).ok_or(TowerError::Refused("a key file shorter than a level's founding"))?;
            at += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            *v = fit32((k * ((three << MATERIAL_BITS) / pd) as i128) >> 31, "a founded value outgrew its 32-bit carrier")?;
        }
        let mut out = self.clone();
        out.scale = Some(Box::new(Scale { harmonics, split, coarse, glue }));
        Ok((out, at))
    }

    /// The level's forward at the split: the region's cut from its `news`, `x` restricted to the epochs by the news phase, the level's
    /// ticks on its own clock, and the prolongation added back into `x`.
    pub(super) fn scale_forward(&self, s: &Scale, x: &mut [i64], news: &[i64], definite: &[bool], keyed: &[bool], keep: bool) -> Result<ScalePass> {
        let (d0, d1, h) = (self.declaration.width, s.coarse.declaration.width, s.harmonics);
        let sites = definite.len();
        let cut = level_cut(news, level_section(self.declaration.alphabet), h, self.pi)?;
        let epochs = cut.anchors.len();
        let (a, ab, b, bb, _) = glue_layout(h, d0, d1);
        let g = &s.glue;
        let mut out = ScalePass::default();
        for xt in x.chunks_exact(d0) {
            lane_chart(xt, self.declaration.lanes, &mut out.read, &mut out.scale)?;
        }
        // The restriction: each epoch's harmonics of its places' reads, through `A`.
        out.restricted = charted(&cut, h, &out.read, d0)?;
        let reach_a = reach(&g[a..ab]);
        let mut x1 = vec![0i64; epochs * d1];
        for j in 0..epochs {
            affine(&g[a..ab], reach_a, h * d0, &out.restricted[j * h * d0..(j + 1) * h * d0], Some(&g[ab..ab + d1]), MATERIAL_BITS, MATERIAL_BITS, &mut x1[j * d1..(j + 1) * d1])?;
        }
        // The level's field, on its own clock.
        let span = |j: usize| cut.anchors[j]..cut.anchors.get(j + 1).copied().unwrap_or(sites);
        out.definite = (0..epochs).map(|j| span(j).all(|t| definite[t])).collect();
        let keyed1: Vec<bool> = (0..epochs).map(|j| span(j).any(|t| keyed[t])).collect();
        out.paces = level_paces(&s.coarse.declaration, &cut)?;
        let moment = vec![0i64; epochs * 2 * s.coarse.declaration.complex()];
        let reaches = s.coarse.reaches();
        for _ in 0..s.coarse.declaration.ticks {
            let mut cell = TickCell::default();
            s.coarse.tick(&mut x1, &out.definite, &keyed1, &out.paces, &moment, &reaches, None, &mut cell)?;
            if keep {
                out.ticks.push(cell);
            }
        }
        for xj in x1.chunks_exact(d1) {
            lane_chart(xj, s.coarse.declaration.lanes, &mut out.coarse_read, &mut out.coarse_scale)?;
        }
        // The prolongation: each epoch's harmonic blocks, each place reading them at its own phase.
        let reach_b = reach(&g[b..bb]);
        let mut v = vec![0i64; h * d0];
        let mut row = vec![0i64; d0];
        for j in 0..epochs {
            affine(&g[b..bb], reach_b, d1, &out.coarse_read[j * d1..(j + 1) * d1], Some(&g[bb..bb + h * d0]), MATERIAL_BITS, MATERIAL_BITS, &mut v)?;
            for t in span(j) {
                uncharted(&cut.harmonics[t * h..(t + 1) * h], &v, d0, &mut row)?;
                for (xv, &r) in x[t * d0..(t + 1) * d0].iter_mut().zip(&row) {
                    *xv = fit64(*xv as i128 + r as i128)?;
                }
            }
        }
        out.cut = cut;
        Ok(out)
    }

    /// The level's reverse at the split: `dx`, the covector of the faces after the prolongation, is carried through the prolongation,
    /// the level's ticks and the restriction into the covector of the faces before it; the level's field's covector and the glue's are
    /// added into `g` at their places in the material ([`Field::families_all`]). The cut is data and takes nothing.
    pub(super) fn scale_return(&self, s: &Scale, pass: &ScalePass, dx: &mut [i64], g: &mut [i128]) -> Result<()> {
        let (d0, d1, h) = (self.declaration.width, s.coarse.declaration.width, s.harmonics);
        let cut = &pass.cut;
        let epochs = pass.definite.len();
        let (a, ab, b, bb, _) = glue_layout(h, d0, d1);
        let len0 = self.theta.len();
        let len1 = s.coarse.theta.len();
        let (_, rest) = g.split_at_mut(len0);
        let (gc, gg) = rest.split_at_mut(len1);
        let gl = &s.glue;
        // The prolongation: `δv_k(j) = release(Σ_(t∈e_j) h_k(φ_t) δx_t, 30)`, then `δb_B += Σ_j δv(j)`, `δB += δv(j) r̂¹_jᵀ` and
        // `δr̂¹_j = Bᵀ δv(j)`.
        let dv = charted(cut, h, dx, d0)?;
        let douts: Vec<&[i64]> = dv.chunks_exact(h * d0).collect();
        for dout in &douts {
            for (i, &v) in dout.iter().enumerate() {
                gg[bb + i] += v as i128;
            }
        }
        let reads1: Vec<&[i32]> = (0..epochs).map(|j| &pass.coarse_read[j * d1..(j + 1) * d1]).collect();
        outer_sum(&mut gg[b..bb], d1, &douts, &reads1)?;
        let reach_b = reach(&gl[b..bb]);
        let mut dx1 = vec![0i64; epochs * d1];
        let mut dr1 = vec![0i64; d1];
        let l1 = s.coarse.declaration.lanes;
        for (j, dout) in douts.iter().enumerate() {
            transposed(&gl[b..bb], reach_b, d1, dout, MATERIAL_BITS, &mut dr1)?;
            let back = lane_adjoint(&pass.coarse_read[j * d1..(j + 1) * d1], &pass.coarse_scale[j * l1..(j + 1) * l1], &dr1)?;
            dx1[j * d1..(j + 1) * d1].copy_from_slice(&back);
        }
        // The level's ticks, in reverse; its clock is data and carries no covector, nor its absent moments.
        let paced = pass.paces.kappa.len();
        let (mut gtau, mut gsig) = (vec![vec![0i128; epochs]; paced], vec![vec![0i128; epochs]; paced]);
        let mut dm = vec![0i128; epochs * 2 * s.coarse.declaration.complex()];
        for cell in pass.ticks.iter().rev() {
            s.coarse.tick_return(cell, &mut dx1, gc, &pass.paces, &pass.definite, &mut dm, &mut gtau, &mut gsig, None, None)?;
        }
        // The restriction: `δb_A += Σ_j δx¹_j`, `δA += δx¹_j m(j)ᵀ` and `δm(j) = Aᵀ δx¹_j`, each place's part
        // `release(Σ_k h_k(φ_t) δm_k(j), 30)` through its read's adjoint into `δx_t`.
        for j in 0..epochs {
            for (i, &v) in dx1[j * d1..(j + 1) * d1].iter().enumerate() {
                gg[ab + i] += v as i128;
            }
        }
        let ds: Vec<&[i64]> = dx1.chunks_exact(d1).collect();
        let ms: Vec<&[i64]> = pass.restricted.chunks_exact(h * d0).collect();
        outer_sum(&mut gg[a..ab], h * d0, &ds, &ms)?;
        let reach_a = reach(&gl[a..ab]);
        let mut dm_k = vec![0i64; h * d0];
        let mut dr = vec![0i64; d0];
        let l0 = self.declaration.lanes;
        for j in 0..epochs {
            transposed(&gl[a..ab], reach_a, h * d0, ds[j], MATERIAL_BITS, &mut dm_k)?;
            let end = cut.anchors.get(j + 1).copied().unwrap_or(cut.epoch.len());
            for t in cut.anchors[j]..end {
                uncharted(&cut.harmonics[t * h..(t + 1) * h], &dm_k, d0, &mut dr)?;
                let back = lane_adjoint(&pass.read[t * d0..(t + 1) * d0], &pass.scale[t * l0..(t + 1) * l0], &dr)?;
                for (slot, &v) in dx[t * d0..(t + 1) * d0].iter_mut().zip(&back) {
                    *slot = fit64(*slot as i128 + v as i128)?;
                }
            }
        }
        Ok(())
    }
}
