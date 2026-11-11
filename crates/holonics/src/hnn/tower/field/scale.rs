//! [definition; agent-inferred, November 3] **The tower of scales** (the record
//! `2026-11-03_THE_FIELD_BECOMES_A_TOWER_OF_SCALES_A_PACKET_IS_THE_RETENTION_QUOTIENT_OF_ITS_INTERIOR`, D1): level 0 is the
//! field on the bytes; level 1 is a field of its own on packets of `P` sites. After the fine field's first `split` ticks
//! each packet is opened on the restriction of its sites, the packets' field runs its own ticks, each site receives its
//! packet back through the prolongation, and the fine field's remaining ticks and its face follow:
//!
//! ```text
//! restrict s_j = A [r̂(x_(Pj)), …, r̂(x_(Pj+P−1))] + b_A            one chart of the packet's reads in place order
//! level 1  x¹_j ← s_j, then the packets' field's own ticks        plain clocks on the packet strand, no moments
//! prolong  [x_(Pj)…x_(Pj+P−1)] += B r̂(x¹_j) + b_B                one chart back, each place its own rows and bias
//! ```
//!
//! A packet is definite where every one of its sites is, and keyed where any is; a packet past its region's last site reads
//! zero there and writes nothing there. The material is the fine field's, the
//! packets' field's and the glue (`A`, `b_A`, `B`, `b_B`), in that order, one covector over all three
//! ([`Field::material_len`], [`Field::families_all`]). Founded as a growth in scale ([`Field::scaled_up`]): `B` and `b_B`
//! open at zero, so the tower reads every face of the field it was founded on exactly.

use super::*;

/// The packets' level of a field ([`Field::scaled_up`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scale {
    /// The sites a packet holds.
    pub period: usize,
    /// The fine ticks read before the restriction, `0 < split < K`.
    pub split: usize,
    /// The packets' field.
    pub coarse: Field,
    /// `A` (`D₁ × P D₀`, a packet's reads in place order) and `b_A` (`D₁`), then `B` (`P D₀ × D₁`) and `b_B` (`P D₀`, a bias
    /// each place); matrices on `2^(−24)`, biases on the faces' `2^(−16)`.
    pub glue: Vec<i32>,
}

impl Scale {
    /// The glue's offsets of `A`, `b_A`, `B` and `b_B`, and its length, over a fine field of `fine_width` (a realization's
    /// read of [`Scale::glue`]).
    pub fn glue_offsets(&self, fine_width: usize) -> (usize, usize, usize, usize, usize) {
        glue_layout(self.period, fine_width, self.coarse.declaration.width)
    }
}

/// The glue's offsets: `A`, `b_A`, `B`, `b_B` and the length.
pub(super) fn glue_len(period: usize, fine: usize, coarse: usize) -> (usize, usize, usize, usize, usize) {
    glue_layout(period, fine, coarse)
}

fn glue_layout(period: usize, fine: usize, coarse: usize) -> (usize, usize, usize, usize, usize) {
    let a = 0;
    let ab = a + period * coarse * fine;
    let b = ab + coarse;
    let bb = b + period * fine * coarse;
    (a, ab, b, bb, bb + period * fine)
}

/// Packet `j`'s rows of `rows` (`[t][width]`) in place order, `period` of them, zero past `sites`.
fn padded<V: Copy + Default>(rows: &[V], j: usize, period: usize, width: usize, sites: usize) -> Vec<V> {
    let mut out = vec![V::default(); period * width];
    for t in period * j..(period * (j + 1)).min(sites) {
        let k = t - period * j;
        out[k * width..(k + 1) * width].copy_from_slice(&rows[t * width..(t + 1) * width]);
    }
    out
}

/// What a tower's forward keeps for its reverse.
#[derive(Clone, Debug, Default)]
pub(super) struct ScalePass {
    /// Each fine site's read at the split `[t][D₀]`, with its scale.
    read: Vec<i32>,
    scale: Vec<i128>,
    /// The packets' ticks, their read after the last `[j][D₁]` with its scale, and which packets are definite.
    ticks: Vec<TickCell>,
    coarse_read: Vec<i32>,
    coarse_scale: Vec<i128>,
    definite: Vec<bool>,
    paces: Paces,
}

impl ScalePass {
    /// The packets' ticks kept for the reverse.
    pub(super) fn ticks(&self) -> &[TickCell] {
        &self.ticks
    }
}

/// Plain clocks on `sites` places for every turned head (`κ = 1`, the clock the place).
fn plain_paces(d: &FieldDeclaration, sites: usize) -> Result<Paces> {
    let one = 1i128 << PACE_BITS;
    let mut out = Paces { row: vec![None; d.heads], ..Default::default() };
    for h in (0..d.heads).filter(|&h| d.carries_moment(h)) {
        out.row[h] = Some(out.kappa.len());
        out.kappa.push(vec![fit64(one)?; sites]);
        let clock: Vec<i64> = (0..sites).map(|t| fit64(t as i128 * one)).collect::<Result<_>>()?;
        out.tau.push(clock.clone());
        out.sigma.push(clock);
        out.plain.push(true);
    }
    Ok(out)
}

impl Field {
    /// The material's length: the field's, and with a scale the packets' field's and the glue's.
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
            let (a, ab, b, bb, _) = glue_layout(s.period, d0, d1);
            out.extend([(at + a, ab - a, MATERIAL_BITS), (at + ab, d1, FACE_BITS), (at + b, bb - b, MATERIAL_BITS), (at + bb, s.period * d0, FACE_BITS)]);
        }
        out
    }

    /// The material entry `i` of [`Field::material_len`], mutable.
    pub fn material_mut(&mut self) -> impl Iterator<Item = &mut i32> {
        let (coarse, glue): (&mut [i32], &mut [i32]) = match self.scale.as_deref_mut() {
            Some(s) => (&mut s.coarse.theta[..], &mut s.glue[..]),
            None => (&mut [], &mut []),
        };
        self.theta.iter_mut().chain(coarse.iter_mut()).chain(glue.iter_mut())
    }

    /// [definition; agent-inferred, November 3] **Growth in scale**: this field with a packets' level of `period` sites
    /// after `split` of its ticks, the packets' field founded on its own `declaration` from the key stream at `offset`, the
    /// restriction's `A` drawn after it on `±√(3/(P D₀))`, and `b_A`, `B`, `b_B` at zero, so every face reads as before.
    /// Returns the tower and the key bytes read through.
    pub fn scaled_up(&self, period: usize, split: usize, declaration: FieldDeclaration, keys: &[u8], offset: usize) -> Result<(Self, usize)> {
        if self.scale.is_some() || period < 2 || split == 0 || split >= self.declaration.ticks || declaration.reach < self.declaration.reach.div_ceil(period) {
            return refuse("a scale needs a field without one, a period of two or more, a split inside the ticks and a reach over the packets");
        }
        let coarse = Field::found(declaration, keys.get(offset..).ok_or(TowerError::Refused("a key file shorter than a scale's founding"))?)?;
        let mut at = offset + 4 * declaration.founding_draws();
        let (d0, d1) = (self.declaration.width, declaration.width);
        let (a, ab, _, _, len) = glue_layout(period, d0, d1);
        let mut glue = vec![0i32; len];
        let ((three, _), (_, pd)) = (chart_scale(d0), chart_scale(period * d0));
        for v in &mut glue[a..ab] {
            let word = keys.get(at..at + 4).ok_or(TowerError::Refused("a key file shorter than a scale's founding"))?;
            at += 4;
            let k = i32::from_be_bytes([word[0], word[1], word[2], word[3]]) as i128;
            *v = fit32((k * ((three << MATERIAL_BITS) / pd) as i128) >> 31, "a founded value outgrew its 32-bit carrier")?;
        }
        let mut out = self.clone();
        out.scale = Some(Box::new(Scale { period, split, coarse, glue }));
        Ok((out, at))
    }

    /// The tower's forward at the split: `x` restricted to the packets, the packets' ticks, and the prolongation added
    /// back into `x`.
    pub(super) fn scale_forward(&self, s: &Scale, x: &mut [i64], definite: &[bool], keyed: &[bool], keep: bool) -> Result<ScalePass> {
        let (d0, d1, period) = (self.declaration.width, s.coarse.declaration.width, s.period);
        let sites = definite.len();
        let packets = sites.div_ceil(period);
        let (a, ab, b, bb, _) = glue_layout(period, d0, d1);
        let g = &s.glue;
        let mut out = ScalePass::default();
        for xt in x.chunks_exact(d0) {
            lane_chart(xt, self.declaration.lanes, &mut out.read, &mut out.scale)?;
        }
        // The restriction: one chart of each packet's reads in place order, zero past the region's last site.
        let reach_a = reach(&g[a..ab]);
        let mut x1 = vec![0i64; packets * d1];
        for j in 0..packets {
            let reads = padded(&out.read, j, period, d0, sites);
            affine(&g[a..ab], reach_a, period * d0, &reads, Some(&g[ab..ab + d1]), MATERIAL_BITS, MATERIAL_BITS, &mut x1[j * d1..(j + 1) * d1])?;
        }
        // The packets' field.
        out.definite = (0..packets).map(|j| (period * j..(period * (j + 1)).min(sites)).all(|t| definite[t])).collect();
        let keyed1: Vec<bool> = (0..packets).map(|j| (period * j..(period * (j + 1)).min(sites)).any(|t| keyed[t])).collect();
        out.paces = plain_paces(&s.coarse.declaration, packets)?;
        let moment = vec![0i64; packets * 2 * s.coarse.declaration.complex()];
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
        // The prolongation: one chart back, each place its own rows and bias.
        let reach_b = reach(&g[b..bb]);
        let mut back = vec![0i64; period * d0];
        for j in 0..packets {
            affine(&g[b..bb], reach_b, d1, &out.coarse_read[j * d1..(j + 1) * d1], Some(&g[bb..bb + period * d0]), MATERIAL_BITS, MATERIAL_BITS, &mut back)?;
            for t in period * j..(period * (j + 1)).min(sites) {
                let k = t - period * j;
                for (xv, &v) in x[t * d0..(t + 1) * d0].iter_mut().zip(&back[k * d0..(k + 1) * d0]) {
                    *xv = fit64(*xv as i128 + v as i128)?;
                }
            }
        }
        Ok(out)
    }

    /// The tower's reverse at the split: `dx`, the covector of the faces after the prolongation, is carried through the
    /// prolongation, the packets' ticks and the restriction into the covector of the faces before it; the packets'
    /// field's covector and the glue's are added into `g` at their places in the material ([`Field::families_all`]).
    pub(super) fn scale_return(&self, s: &Scale, pass: &ScalePass, dx: &mut [i64], g: &mut [i128]) -> Result<()> {
        let (d0, d1, period) = (self.declaration.width, s.coarse.declaration.width, s.period);
        let sites = pass.scale.len();
        let packets = pass.definite.len();
        let (a, ab, b, bb, _) = glue_layout(period, d0, d1);
        let len0 = self.theta.len();
        let len1 = s.coarse.theta.len();
        let (g0, rest) = g.split_at_mut(len0);
        let _ = g0;
        let (gc, gg) = rest.split_at_mut(len1);
        let gl = &s.glue;
        // The prolongation: `δb_B += Σ_j δx_j`, `δB += δx_j r̂¹_jᵀ` and `δr̂¹_j = Bᵀ δx_j` with `δx_j` the packet's places'
        // covectors in place order (zero past the region's last site).
        let reach_b = reach(&gl[b..bb]);
        let douts: Vec<Vec<i64>> = (0..packets).map(|j| padded(dx, j, period, d0, sites)).collect();
        for dout in &douts {
            for (i, &v) in dout.iter().enumerate() {
                gg[bb + i] += v as i128;
            }
        }
        let reads1: Vec<&[i32]> = (0..packets).map(|j| &pass.coarse_read[j * d1..(j + 1) * d1]).collect();
        outer_sum(&mut gg[b..bb], d1, &douts, &reads1)?;
        let mut dr1 = vec![0i64; packets * d1];
        for (j, dout) in douts.iter().enumerate() {
            transposed(&gl[b..bb], reach_b, d1, dout, MATERIAL_BITS, &mut dr1[j * d1..(j + 1) * d1])?;
        }
        let mut dx1 = vec![0i64; packets * d1];
        for j in 0..packets {
            let l1 = s.coarse.declaration.lanes;
            let back = lane_adjoint(&pass.coarse_read[j * d1..(j + 1) * d1], &pass.coarse_scale[j * l1..(j + 1) * l1], &dr1[j * d1..(j + 1) * d1])?;
            dx1[j * d1..(j + 1) * d1].copy_from_slice(&back);
        }
        // The packets' ticks, in reverse; their clocks are plain and carry no covector, nor their absent moments.
        let paced = pass.paces.kappa.len();
        let (mut gtau, mut gsig) = (vec![vec![0i128; packets]; paced], vec![vec![0i128; packets]; paced]);
        let mut dm = vec![0i128; packets * 2 * s.coarse.declaration.complex()];
        for cell in pass.ticks.iter().rev() {
            s.coarse.tick_return(cell, &mut dx1, &mut Vec::new(), gc, &pass.paces, &pass.definite, &mut dm, &mut gtau, &mut gsig, None, None)?;
        }
        // The restriction: `δb_A += Σ_j δs_j`, `δA += δs_j [r̂]_jᵀ` and `δ[r̂]_j = Aᵀ δs_j`, each place's part through its
        // read's adjoint into `δx_t`.
        let reach_a = reach(&gl[a..ab]);
        for j in 0..packets {
            for (i, &v) in dx1[j * d1..(j + 1) * d1].iter().enumerate() {
                gg[ab + i] += v as i128;
            }
        }
        let ds: Vec<&[i64]> = (0..packets).map(|j| &dx1[j * d1..(j + 1) * d1]).collect();
        let reads: Vec<Vec<i32>> = (0..packets).map(|j| padded(&pass.read, j, period, d0, sites)).collect();
        outer_sum(&mut gg[a..ab], period * d0, &ds, &reads)?;
        let mut dpad = vec![0i64; period * d0];
        for j in 0..packets {
            transposed(&gl[a..ab], reach_a, period * d0, ds[j], MATERIAL_BITS, &mut dpad)?;
            for t in period * j..(period * (j + 1)).min(sites) {
                let k = t - period * j;
                let l0 = self.declaration.lanes;
                let back = lane_adjoint(&pass.read[t * d0..(t + 1) * d0], &pass.scale[t * l0..(t + 1) * l0], &dpad[k * d0..(k + 1) * d0])?;
                for (slot, &v) in dx[t * d0..(t + 1) * d0].iter_mut().zip(&back) {
                    *slot = fit64(*slot as i128 + v as i128)?;
                }
            }
        }
        Ok(())
    }
}
