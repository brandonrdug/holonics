//! [definition; agent-inferred, October 25] **The ring founding**: a situated form pushed into a
//! ring that rides one placement mode's own moves, its push gated by a pair contact with the state,
//! and read where a received landmark marks.
//!
//! ```text
//! v_t = (aᵀŝ_t)(bᵀx̂_t)(gᵀx_t),   x = (ŝ, 2^16), x̂ = (E(u), 2^16)
//! r_t = λ_(m,t) r_(t−1) + β_(m,t) r̄_(t−1) + v_t
//! ```
//!
//! `ŝ` is one level's carried face before the move (as the situated pool's), `a` and `b` complex,
//! `g` real, and `λ_(m,t)`, `β_(m,t)` the placement mode `m`'s own move at the cell
//! ([`holonics::hnn::tower::InputCovector`]'s `moves`). The record
//! `2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK` ("The demand at
//! the modes", "The operation crosses the reader", "Plural ranks find the sum's operand") located why
//! the situated pool's lift at the cell where a class arrives cannot found a sum's units where the
//! second operand arrives: the readers at the result are short-lived turning modes, the node modes
//! that carry a value from the operand to the result alike for both lengths have no reader there,
//! and the demand reaching the operand is turned by the distance. The ring is the form placed in a
//! node mode's own moves, read through the input lift at every marked cell,
//! `x⁰_t += P(Re r_t, Im r_t)`.
//!
//! **The landmark** is received material: one byte per byte of the text, beside it, nonzero where
//! the reading looks. It says where to look, never what to find: no value of the text enters the
//! founding through it, and the founded form is read held out where the operand arrives, a cell the
//! landmark does not mark. A machine that knows more than whoever marked its text may mark it back;
//! the exchange is communication (the record's "a received landmark is communication").
//!
//! Each factor is founded in turn by the pool law: the leading generalized eigenvector of the demand
//! its ring meets at the marked cells against the ring's own loudness there, each centred within the
//! arriving class,
//!
//! ```text
//! s(θ) = (‖Σ_t Re(r_t) y_tᵀ‖²_(Y⁻¹) + ‖Σ_t Im(r_t) y_tᵀ‖²_(Y⁻¹)) / Σ_t |r_t|²
//! ```
//!
//! with `y_t` the covector the tower's reverse sends to the cell's input and `Y = Σ y yᵀ` over the
//! marked cells: twice the nats a marked cell saves, both faces of the ring counted together
//! (`found-tower-situated`'s circular share). Each rank starts from the unit pool and the unit gate
//! and founds `a`, `b`, `g` in turn, then `a` once more; its exact share is `tr(Y⁻¹RᵀG⁻¹R)` over every
//! founded rank's two channels, and the tension is deflated by them before the next rank.
//!
//! **The ring's carrier.** Each factor's value at a cell is released to below `2^40` at its bound
//! over the passage (`release`, from the factor and the largest magnitude each coordinate carries,
//! read once), so the three multiply inside 128 bits whatever widths the founding gives them; the
//! push is their product released to below `2^40` at its bound (`push_shift`); the ring is carried
//! in 128 bits by the mode's own law, `λ r + β r̄` released from the moves' grain, and read released
//! by the bits its memory can gain (`read_shift`, from the largest `|λ_m| + |β_m|` over the passage).
//! A mode whose moves can boost (`|λ| + |β| ≥ 1`) gives the ring no bound and is refused. The frozen
//! tower reads the passage once ([`survey`]); every pass carries the rings over that one reading.
//! The founding's directions are searched on released copies; every share is read exactly from the
//! moments of the carried ring.

use super::tower_situated::{div_round, lcm, permille};
use super::tower_train::{count, pair_hats, positive, release_big, solve_scaled, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::{ring_carry, RingFace, RingRank, Tower, TowerError, TowerLearner, FACE_BITS, MOVE_BITS};
use num_bigint::BigInt;
use num_traits::Zero;
use rayon::prelude::*;

/// The largest magnitude a ring read, a channel or a covector entry may have: each product is
/// below `2^80`, so the moment sums stay inside 128 bits over fewer than `2^32` cells.
const REACH: u32 = 40;

/// `x` released `bits` coarser, to the nearest numerator, half away from zero (the tower's law).
fn release(x: i128, bits: u32) -> i128 {
    if bits == 0 {
        return x;
    }
    let half = 1i128 << (bits - 1);
    if x >= 0 { (x + half) >> bits } else { -((-x + half) >> bits) }
}

/// The bits of `x`'s magnitude: `x < 2^bits(x)`.
fn bits(x: u128) -> u32 {
    128 - x.leading_zeros()
}

/// `⌈√x⌉`, by Newton's descent from a power of two above the root.
fn ceil_sqrt(x: u128) -> u128 {
    if x == 0 {
        return 0;
    }
    let mut r = 1u128 << bits(x).div_ceil(2);
    loop {
        let next = (r + x / r) / 2;
        if next >= r {
            break;
        }
        r = next;
    }
    if r * r < x { r + 1 } else { r }
}

/// The factor a step founds.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Factor {
    A,
    B,
    G,
}

/// A ring form ([`RingRank`], the library's owner): complex `a` over the carried face, complex `b`
/// over the arriving class's `x̂`, real `g` over `x = (ŝ, 2^16)`, each held as wide as its founded
/// direction needs inside the 64-bit word ([`leading_real`], [`pool_factor`]), with each factor's
/// release at its bound and the shifts its push and read are carried by.
type Ring = RingRank;

/// What the passage holds once, read in the scale pass: per coordinate of `x` the largest
/// magnitude over the counted cells, the largest covector entry, and the placement mode's largest
/// `|λ| + |β|` on the moves' grain.
struct Scale {
    x: Vec<u128>,
    y: u128,
    rho: u128,
}

/// One stream as the frozen tower reads it once, its opening section included: per cell the
/// arriving class, the placement mode's move `(Re λ, Im λ, Re β, Im β)`, the level's carried face
/// before the move, and at each counted marked cell, in order, the covector the reverse sends to the
/// cell's input.
struct Stream {
    open: usize,
    start: usize,
    classes: Vec<usize>,
    moves: Vec<[i64; 4]>,
    faces: Vec<i64>,
    covectors: Vec<i64>,
}

/// The founding's fixed reading: the tower, the text cut into streams, the landmark, the level and
/// the placement mode, the classes' `x̂` and the passage's scale.
struct Passage<'a> {
    tower: &'a Tower,
    text: Vec<usize>,
    marks: Vec<u8>,
    cuts: Vec<(usize, usize)>,
    section: usize,
    level: usize,
    mode: usize,
    hats: Vec<Vec<i64>>,
    dims: usize,
    width: usize,
    /// The classes that arrive at a counted cell, in class order (the pool's coordinates).
    present: Vec<usize>,
    /// The streams as [`survey`] read them.
    streams: Vec<Stream>,
}

/// One pass's moments over the marked cells: per class its count, `Σy`, `Σc` over the founded
/// ranks' channels and `Σφ` over the step's columns (both faces); and over every marked cell `Y`,
/// `ΣccᵀΣ`, `Σcyᵀ`, `Σ_f φ_fφ_fᵀ`, `Σ y φ_fᵀ` and `Σ c φ_fᵀ` per face `f`.
#[derive(Clone)]
struct PassMoments {
    k: usize,
    channels: usize,
    width: usize,
    n: Vec<i128>,
    sy: Vec<Vec<i128>>,
    sc: Vec<Vec<i128>>,
    sf: Vec<Vec<i128>>,
    yy: Vec<i128>,
    cc: Vec<i128>,
    cy: Vec<i128>,
    ff: Vec<i128>,
    fy: Vec<i128>,
    cf: Vec<i128>,
    cells: u64,
}

impl PassMoments {
    fn new(alphabet: usize, width: usize, channels: usize, k: usize) -> Self {
        Self {
            k,
            channels,
            width,
            n: vec![0; alphabet],
            sy: vec![Vec::new(); alphabet],
            sc: vec![Vec::new(); alphabet],
            sf: vec![Vec::new(); alphabet],
            yy: vec![0; width * width],
            cc: vec![0; channels * channels],
            cy: vec![0; channels * width],
            ff: vec![0; k * k],
            fy: vec![0; 2 * width * k],
            cf: vec![0; 2 * channels * k],
            cells: 0,
        }
    }

    /// One marked cell: the class, its covector, the founded ranks' channels and the step's
    /// columns `φ[f][j]` (each below `2^40`, checked by the caller).
    fn add(&mut self, u: usize, y: &[i64], c: &[i64], phi: &[Vec<i64>; 2]) {
        let (w, ch, k) = (self.width, self.channels, self.k);
        if self.sy[u].is_empty() {
            self.sy[u] = vec![0; w];
            self.sc[u] = vec![0; ch];
            self.sf[u] = vec![0; 2 * k];
        }
        self.n[u] += 1;
        for (s, &v) in self.sy[u].iter_mut().zip(y) {
            *s += v as i128;
        }
        for (s, &v) in self.sc[u].iter_mut().zip(c) {
            *s += v as i128;
        }
        for f in 0..2 {
            for (s, &v) in self.sf[u][f * k..(f + 1) * k].iter_mut().zip(&phi[f]) {
                *s += v as i128;
            }
        }
        for r in 0..w {
            let yr = y[r] as i128;
            if yr == 0 {
                continue;
            }
            for (s, &y2) in self.yy[r * w + r..(r + 1) * w].iter_mut().zip(&y[r..]) {
                *s += yr * y2 as i128;
            }
        }
        for i in 0..ch {
            let ci = c[i] as i128;
            for (s, &c2) in self.cc[i * ch + i..(i + 1) * ch].iter_mut().zip(&c[i..]) {
                *s += ci * c2 as i128;
            }
            for (s, &yr) in self.cy[i * w..(i + 1) * w].iter_mut().zip(y) {
                *s += ci * yr as i128;
            }
        }
        for f in 0..2 {
            let p = &phi[f];
            for i in 0..k {
                let pi = p[i] as i128;
                if pi == 0 {
                    continue;
                }
                for (s, &p2) in self.ff[i * k + i..(i + 1) * k].iter_mut().zip(&p[i..]) {
                    *s += pi * p2 as i128;
                }
            }
            for r in 0..w {
                let yr = y[r] as i128;
                if yr == 0 {
                    continue;
                }
                for (s, &pj) in self.fy[(f * w + r) * k..(f * w + r + 1) * k].iter_mut().zip(p) {
                    *s += yr * pj as i128;
                }
            }
            for i in 0..ch {
                let ci = c[i] as i128;
                for (s, &pj) in self.cf[(f * ch + i) * k..(f * ch + i + 1) * k].iter_mut().zip(p) {
                    *s += ci * pj as i128;
                }
            }
        }
        self.cells += 1;
    }

    fn merge(&mut self, other: PassMoments) {
        for u in 0..self.n.len() {
            if other.n[u] == 0 {
                continue;
            }
            if self.n[u] == 0 {
                self.sy[u] = other.sy[u].clone();
                self.sc[u] = other.sc[u].clone();
                self.sf[u] = other.sf[u].clone();
            } else {
                for (a, b) in self.sy[u].iter_mut().zip(&other.sy[u]).chain(self.sc[u].iter_mut().zip(&other.sc[u])).chain(self.sf[u].iter_mut().zip(&other.sf[u])) {
                    *a += b;
                }
            }
            self.n[u] += other.n[u];
        }
        for (a, b) in self.yy.iter_mut().zip(&other.yy).chain(self.cc.iter_mut().zip(&other.cc)).chain(self.cy.iter_mut().zip(&other.cy)) {
            *a += b;
        }
        for (a, b) in self.ff.iter_mut().zip(&other.ff).chain(self.fy.iter_mut().zip(&other.fy)).chain(self.cf.iter_mut().zip(&other.cf)) {
            *a += b;
        }
        self.cells += other.cells;
    }

    fn present(&self) -> Vec<usize> {
        (0..self.n.len()).filter(|&u| self.n[u] > 0).collect()
    }
}

/// A symmetric matrix whose upper triangle (row by row, `d × d` row-major) is filled.
fn symmetric(upper: &[i128], d: usize) -> Vec<Vec<BigInt>> {
    (0..d).map(|i| (0..d).map(|j| BigInt::from(upper[i.min(j) * d + i.max(j)])).collect()).collect()
}

/// The founded ranks' exact fit on a pass: with `L` the lcm of the marked classes' counts, the
/// centred Gram `G_L = L·Σccᵀ − Σ_u (L/n_u) Σc_u Σc_uᵀ` and cross `R_L` likewise, `D` and `D·P`
/// with `G_L P = R_L`, and the metric of the tension they leave, `L·D·Y − R_Lᵀ(D·P)`.
struct RankFit {
    det: BigInt,
    dp: Vec<Vec<BigInt>>,
    y: Vec<Vec<BigInt>>,
    y_scale: BigInt,
    share: BigInt,
    share_den: BigInt,
}

fn rank_fit(m: &PassMoments) -> Result<RankFit> {
    let (ch, w) = (m.channels, m.width);
    let present = m.present();
    let l = lcm(present.iter().map(|&u| m.n[u]));
    let scale: Vec<BigInt> = present.iter().map(|&u| &l / m.n[u]).collect();
    let yy = symmetric(&m.yy, w);
    let identity: Vec<Vec<BigInt>> = (0..w).map(|r| (0..w).map(|r2| BigInt::from((r == r2) as i64)).collect()).collect();
    if ch == 0 {
        return Ok(RankFit { det: BigInt::from(1), dp: Vec::new(), y: yy, y_scale: BigInt::from(1), share: BigInt::zero(), share_den: BigInt::from(1) });
    }
    let cc = symmetric(&m.cc, ch);
    let g: Vec<Vec<BigInt>> = (0..ch)
        .map(|i| (0..ch).map(|j| &l * &cc[i][j] - present.iter().zip(&scale).map(|(&u, s)| s * m.sc[u][i] * m.sc[u][j]).sum::<BigInt>()).collect())
        .collect();
    let r: Vec<Vec<BigInt>> = (0..ch)
        .map(|i| (0..w).map(|q| &l * m.cy[i * w + q] - present.iter().zip(&scale).map(|(&u, s)| s * m.sc[u][i] * m.sy[u][q]).sum::<BigInt>()).collect())
        .collect();
    let (det, dp) = solve_scaled(&g, &r, true)?;
    let ld = &l * &det;
    let y: Vec<Vec<BigInt>> = (0..w).map(|q| (0..w).map(|q2| &ld * &yy[q][q2] - (0..ch).map(|i| &r[i][q] * &dp[i][q2]).sum::<BigInt>()).collect()).collect();
    // The exact share of every founded channel: tr(Y⁻¹ RᵀG⁻¹R) = tr(Y⁻¹ R_Lᵀ (D·P)) / (L·D).
    let (dy, yinv) = solve_scaled(&yy, &identity, false)?;
    let share: BigInt = (0..w).into_par_iter().map(|q| (0..w).map(|q2| &yinv[q][q2] * (0..ch).map(|i| &r[i][q2] * &dp[i][q]).sum::<BigInt>()).sum::<BigInt>()).sum();
    let share_den = dy * &l * &det;
    Ok(RankFit { det, dp, y, y_scale: ld, share, share_den })
}

/// The step's demand and loudness on a pass, deflated by the founded ranks' channels: the two faces'
/// centred cross moments stacked, `[X₀; X₁]` (each `width × k`), and the centred Gram summed over
/// the faces, each class's part rounded by its count (directions only).
fn step_blocks(m: &PassMoments, fit: &RankFit) -> (Vec<Vec<BigInt>>, Vec<Vec<BigInt>>) {
    let (k, ch, w) = (m.k, m.channels, m.width);
    let present = m.present();
    let ns: Vec<BigInt> = present.iter().map(|&u| BigInt::from(m.n[u])).collect();
    let q: Vec<Vec<BigInt>> = (0..k)
        .into_par_iter()
        .map(|i| {
            (0..k)
                .map(|j| {
                    let total = BigInt::from(m.ff[i.min(j) * k + i.max(j)]);
                    let means: BigInt = present.iter().zip(&ns).map(|(&u, n)| div_round(&(0..2).map(|f| BigInt::from(m.sf[u][f * k + i]) * m.sf[u][f * k + j]).sum::<BigInt>(), n)).sum();
                    total - means
                })
                .collect()
        })
        .collect();
    let stacked: Vec<Vec<BigInt>> = (0..2 * w)
        .into_par_iter()
        .map(|row| {
            let (f, r) = (row / w, row % w);
            (0..k)
                .map(|j| {
                    let centred = |total: i128, left: &dyn Fn(usize) -> i128| -> BigInt { BigInt::from(total) - present.iter().zip(&ns).map(|(&u, n)| div_round(&(BigInt::from(left(u)) * m.sf[u][f * k + j]), n)).sum::<BigInt>() };
                    let x = centred(m.fy[(f * w + r) * k + j], &|u| m.sy[u][r]);
                    if ch == 0 {
                        return x;
                    }
                    // Less the founded channels' lift: Σ_i P_ir (centred Σ c_i φ_f).
                    let lift: BigInt = (0..ch).map(|i| &fit.dp[i][r] * centred(m.cf[(f * ch + i) * k + j], &|u| m.sc[u][i])).sum();
                    x - div_round(&lift, &fit.det)
                })
                .collect()
        })
        .collect();
    (stacked, q)
}

/// The pass: over the streams as the frozen tower read them once (each after the first opening one
/// section early, from rest, and counting none of that section's cells), it carries every founded
/// rank's ring and, when a step is given, the ring of each of its columns, and keeps the moments of
/// the marked cells.
fn pass(p: &Passage, ranks: &[Ring], step: Option<(Factor, &Ring)>) -> Result<PassMoments> {
    let (dims, width) = (p.dims, p.width);
    let k = match step.map(|s| s.0) {
        None => 0,
        Some(Factor::A) => 2 * dims,
        Some(Factor::B) => 2 * p.present.len(),
        Some(Factor::G) => dims + 1,
    };
    let channels = 2 * ranks.len();
    let alphabet = p.tower.declaration.alphabet;
    let read: Vec<PassMoments> = p
        .streams
        .par_iter()
        .map(|stream| -> std::result::Result<PassMoments, TowerError> {
            let mut moments = PassMoments::new(alphabet, width, channels, k);
            // Each founded rank's ring and each column's, as (re, im) on the ring's grain.
            let mut held: Vec<(i128, i128)> = vec![(0, 0); ranks.len()];
            let mut cols: [Vec<i128>; 2] = [vec![0; k], vec![0; k]];
            let mut marked = 0;
            for (at, &class) in stream.classes.iter().enumerate() {
                let i = stream.open + at;
                let s = &stream.faces[at * dims..(at + 1) * dims];
                let hat = &p.hats[class];
                let m = stream.moves[at].map(|x| x as i128);
                let mut c = Vec::with_capacity(channels);
                for (h, ring) in held.iter_mut().zip(ranks) {
                    let (alpha, gamma) = ring.state_factors(s);
                    let v = ring.push(alpha, ring.pool(hat), gamma)?;
                    let carried = ring_carry(m, *h);
                    *h = (carried.0 + v.0, carried.1 + v.1);
                    c.push(release(h.0, ring.read_shift));
                    c.push(release(h.1, ring.read_shift));
                }
                let mut phi: [Vec<i64>; 2] = [vec![0; k], vec![0; k]];
                if let Some((factor, ring)) = step {
                    let ((alpha, gamma), beta) = (ring.state_factors(s), ring.pool(hat));
                    // σ, the held factors' product, and the column coordinates z it multiplies.
                    let (sigma, z): ((i128, i128), Vec<i128>) = match factor {
                        Factor::A => (cmul(beta, (gamma, 0)), s.iter().map(|&v| v as i128).collect()),
                        Factor::B => (cmul(alpha, (gamma, 0)), p.present.iter().map(|&u| (u == class) as i128).collect()),
                        Factor::G => (cmul(alpha, beta), s.iter().map(|&v| v as i128).chain([1i128 << 16]).collect()),
                    };
                    let half = z.len();
                    for j in 0..k {
                        // A complex factor's real part, then its imaginary part (i σ z).
                        let (zj, turned) = if factor == Factor::G { (z[j], false) } else { (z[j % half], j >= half) };
                        let v = if turned { (-sigma.1 * zj, sigma.0 * zj) } else { (sigma.0 * zj, sigma.1 * zj) };
                        let carried = ring_carry(m, (cols[0][j], cols[1][j]));
                        cols[0][j] = carried.0 + release(v.0, ring.push_shift);
                        cols[1][j] = carried.1 + release(v.1, ring.push_shift);
                        phi[0][j] = narrow(release(cols[0][j], ring.read_shift))?;
                        phi[1][j] = narrow(release(cols[1][j], ring.read_shift))?;
                    }
                }
                if i < stream.start || p.marks[i] == 0 {
                    continue;
                }
                let c: Vec<i64> = c.into_iter().map(narrow).collect::<std::result::Result<_, _>>()?;
                moments.add(class, &stream.covectors[marked * width..(marked + 1) * width], &c, &phi);
                marked += 1;
            }
            Ok(moments)
        })
        .collect::<std::result::Result<_, TowerError>>()
        .map_err(|e| e.to_string())?;
    let mut merged = PassMoments::new(alphabet, width, channels, k);
    for m in read {
        merged.merge(m);
    }
    Ok(merged)
}

fn dot(a: &[i64], x: &[i64]) -> i128 {
    a.iter().zip(x).map(|(&p, &q)| p as i128 * q as i128).sum()
}

fn cmul(x: (i128, i128), y: (i128, i128)) -> (i128, i128) {
    (x.0 * y.0 - x.1 * y.1, x.0 * y.1 + x.1 * y.0)
}

/// A ring read or channel inside the moments' reach.
fn narrow(x: i128) -> std::result::Result<i64, TowerError> {
    if x.unsigned_abs() >= 1 << REACH {
        return Err(TowerError::Refused("a ring read past 2^40: its read shift did not hold the ring's memory"));
    }
    Ok(x as i64)
}

/// The classes' coupling moments over every counted cell: per arriving class its count, `Σŝŝᵀ`
/// (upper triangle) and `Σŝyᵀ`, and over every cell `Σyyᵀ` (upper triangle).
struct Coupling {
    n: Vec<i128>,
    ss: Vec<Vec<i128>>,
    sy: Vec<Vec<i128>>,
    yy: Vec<i128>,
}

impl Coupling {
    fn new(alphabet: usize, width: usize) -> Self {
        Self { n: vec![0; alphabet], ss: vec![Vec::new(); alphabet], sy: vec![Vec::new(); alphabet], yy: vec![0; width * width] }
    }

    fn add(&mut self, u: usize, s: &[i64], y: &[i64]) {
        let (d, w) = (s.len(), y.len());
        if self.ss[u].is_empty() {
            self.ss[u] = vec![0; d * d];
            self.sy[u] = vec![0; d * w];
        }
        self.n[u] += 1;
        for i in 0..d {
            let si = s[i] as i128;
            if si == 0 {
                continue;
            }
            for (slot, &sj) in self.ss[u][i * d + i..(i + 1) * d].iter_mut().zip(&s[i..]) {
                *slot += si * sj as i128;
            }
            for (slot, &yr) in self.sy[u][i * w..(i + 1) * w].iter_mut().zip(y) {
                *slot += si * yr as i128;
            }
        }
        for r in 0..w {
            let yr = y[r] as i128;
            for (slot, &y2) in self.yy[r * w + r..(r + 1) * w].iter_mut().zip(&y[r..]) {
                *slot += yr * y2 as i128;
            }
        }
    }

    fn merge(&mut self, other: Coupling) {
        for u in 0..self.n.len() {
            if other.n[u] == 0 {
                continue;
            }
            if self.n[u] == 0 {
                self.ss[u] = other.ss[u].clone();
                self.sy[u] = other.sy[u].clone();
            } else {
                for (a, b) in self.ss[u].iter_mut().zip(&other.ss[u]).chain(self.sy[u].iter_mut().zip(&other.sy[u])) {
                    *a += b;
                }
            }
            self.n[u] += other.n[u];
        }
        for (a, b) in self.yy.iter_mut().zip(&other.yy) {
            *a += b;
        }
    }
}

/// The survey pass, the frozen tower's one reading of the passage: every stream's cells
/// ([`Stream`]), the largest magnitude of each coordinate of `x = (ŝ, 2^16)` over every cell a ring
/// carries, the largest covector entry over the counted cells, the placement mode's largest
/// `|λ| + |β|` (each modulus rounded up) over every cell, and the classes' coupling moments over the
/// counted cells.
fn survey(p: &Passage) -> Result<(Scale, Coupling, Vec<Stream>)> {
    let dims = p.dims;
    let level_face = p.level * dims;
    let mv = (p.level * p.tower.declaration.modes + p.mode) * 4;
    let alphabet = p.tower.declaration.alphabet;
    let read: Vec<(Scale, Coupling, Stream)> = p
        .cuts
        .par_iter()
        .map(|&(start, end)| {
            let open = start.saturating_sub(p.section);
            let mut out = Scale { x: vec![0; dims + 1], y: 0, rho: 0 };
            out.x[dims] = 1 << 16;
            let mut coupling = Coupling::new(alphabet, p.width);
            let mut stream = Stream { open, start, classes: Vec::with_capacity(end - open), moves: Vec::with_capacity(end - open), faces: Vec::with_capacity((end - open) * dims), covectors: Vec::new() };
            let mut state = p.tower.rest();
            let mut at = open;
            p.tower
                .read_input_covectors(&mut state, &p.text[open..end], p.section, |cell| {
                    let i = at;
                    at += 1;
                    let m = &cell.moves[mv..mv + 4];
                    let sq = |a: i64, b: i64| (a.unsigned_abs() as u128).pow(2) + (b.unsigned_abs() as u128).pow(2);
                    out.rho = out.rho.max(ceil_sqrt(sq(m[0], m[1])) + ceil_sqrt(sq(m[2], m[3])));
                    let s = &cell.carried[level_face..level_face + dims];
                    if s.iter().any(|v| v.unsigned_abs() >= 1 << REACH) {
                        return Err(TowerError::Refused("a carried coordinate past 2^40: a ring's factor would leave its reach"));
                    }
                    for (slot, &v) in out.x.iter_mut().zip(s) {
                        *slot = (*slot).max(v.unsigned_abs() as u128);
                    }
                    stream.classes.push(cell.class);
                    stream.moves.push([m[0], m[1], m[2], m[3]]);
                    stream.faces.extend_from_slice(s);
                    if i < start {
                        return Ok(());
                    }
                    out.y = out.y.max(cell.covector.iter().map(|v| v.unsigned_abs() as u128).max().unwrap_or(0));
                    if cell.covector.iter().any(|v| v.unsigned_abs() >= 1 << REACH) {
                        return Err(TowerError::Refused("a covector entry past 2^40: the moments would leave 128 bits"));
                    }
                    coupling.add(cell.class, s, cell.covector);
                    if p.marks[i] != 0 {
                        stream.covectors.extend_from_slice(cell.covector);
                    }
                    Ok(())
                })
                .map_err(|e| e.to_string())?;
            Ok((out, coupling, stream))
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut out = Scale { x: vec![0; dims + 1], y: 0, rho: 0 };
    let mut coupling = Coupling::new(alphabet, p.width);
    let mut streams = Vec::with_capacity(read.len());
    for (s, c, stream) in read {
        for (a, b) in out.x.iter_mut().zip(&s.x) {
            *a = (*a).max(*b);
        }
        out.y = out.y.max(s.y);
        out.rho = out.rho.max(s.rho);
        coupling.merge(c);
        streams.push(stream);
    }
    if streams.iter().map(|s| s.covectors.len() / p.width).sum::<usize>() >= 1 << 32 {
        return Err("2^32 marked cells: the moments would leave 128 bits".into());
    }
    Ok((out, coupling, streams))
}

/// `A·B` for BigInt matrices.
fn product(a: &[Vec<BigInt>], b: &[Vec<BigInt>]) -> Vec<Vec<BigInt>> {
    let inner = b.len();
    a.par_iter().map(|row| (0..b[0].len()).map(|j| (0..inner).filter(|&k| !row[k].is_zero()).map(|k| &row[k] * &b[k][j]).sum()).collect()).collect()
}

/// A matrix released to below `2^60` at its largest entry (directions only).
fn released(m: &[Vec<BigInt>]) -> Vec<Vec<BigInt>> {
    let cols = m.first().map_or(0, Vec::len);
    release_big(&m.iter().flatten().cloned().collect::<Vec<_>>(), 60).chunks(cols.max(1)).map(|row| row.iter().map(|&x| BigInt::from(x)).collect()).collect()
}

/// [agent-inferred, October 25] **The pool starts: the classes' coupling through the tension.**
/// After the common read (`W̄ = S⁻¹Σ_u M_u`, `S = Σ_u S_u` the state's Gram and `M_u = Σ ŝyᵀ` over
/// class `u`'s arrivals), each class keeps the tension it moves beyond what the state says for every
/// class alike, `M̃_u = M_u − S_u W̄`; two classes couple by how alike those are in the state's and
/// the tension's metrics, `K_uv = tr(S⁻¹ M̃_u Y⁻¹ M̃_vᵀ)/√(n_u n_v)`. Its leading modes (`count`
/// of them, by power steps with each kept orthogonal to those before) are pools that each class
/// reads with its own sign: the unit start, every class alike, cancels them. The record
/// `…EVERY_LOOK_IS_READ_BY_ITS_LOCK` ("The pool founded blind") read K's third mode on the digits'
/// ring, located without any digit named. Each mode is returned as `b` over `x̂`, the
/// least-norm factor whose `bᵀx̂_u` is the mode's value at class `u` (the mode released to `2^15`).
fn coupling_starts(p: &Passage, c: &Coupling, count: usize) -> Result<Vec<[Vec<i64>; 2]>> {
    let (d, w) = (p.dims, p.width);
    let present: Vec<usize> = (0..c.n.len()).filter(|&u| c.n[u] > 0).collect();
    if count == 0 || present.len() < 2 {
        return Ok(Vec::new());
    }
    let sym = |upper: &[i128], k: usize| -> Vec<Vec<BigInt>> { (0..k).map(|i| (0..k).map(|j| BigInt::from(upper[i.min(j) * k + i.max(j)])).collect()).collect() };
    let full = |m: &[i128], cols: usize| -> Vec<Vec<BigInt>> { m.chunks(cols).map(|row| row.iter().map(|&x| BigInt::from(x)).collect()).collect() };
    let mut s_total = vec![vec![BigInt::zero(); d]; d];
    let mut m_total = vec![vec![BigInt::zero(); w]; d];
    let ss: Vec<Vec<Vec<BigInt>>> = present.iter().map(|&u| sym(&c.ss[u], d)).collect();
    let ms: Vec<Vec<Vec<BigInt>>> = present.iter().map(|&u| full(&c.sy[u], w)).collect();
    for (su, mu) in ss.iter().zip(&ms) {
        for i in 0..d {
            for j in 0..d {
                s_total[i][j] += &su[i][j];
            }
            for r in 0..w {
                m_total[i][r] += &mu[i][r];
            }
        }
    }
    // D·M̃_u = D·M_u − S_u (D·W̄), with D·W̄ from S (D·W̄) = D Σ M_u.
    let (det, dw) = solve_scaled(&s_total, &m_total, true)?;
    let tension: Vec<Vec<Vec<BigInt>>> = ss.iter().zip(&ms).map(|(su, mu)| {
        let common = product(su, &dw);
        (0..d).map(|i| (0..w).map(|r| &det * &mu[i][r] - &common[i][r]).collect()).collect()
    }).collect();
    let joint = released(&tension.iter().flatten().cloned().collect::<Vec<_>>());
    let tension: Vec<Vec<Vec<BigInt>>> = joint.chunks(d).map(|m| m.to_vec()).collect();
    let id = |k: usize| -> Vec<Vec<BigInt>> { (0..k).map(|i| (0..k).map(|j| BigInt::from((i == j) as i64)).collect()).collect() };
    let s_inv = released(&solve_scaled(&s_total, &id(d), false)?.1);
    let y_inv = released(&solve_scaled(&sym(&c.yy, w), &id(w), false)?.1);
    // T_v = S⁻¹ M̃_v Y⁻¹; C_uv = Σ M̃_u ∘ T_v.
    let carried: Vec<Vec<Vec<BigInt>>> = tension.iter().map(|m| product(&s_inv, &product(m, &y_inv))).collect();
    let k = present.len();
    let coupling: Vec<Vec<BigInt>> = (0..k)
        .map(|u| (0..k).map(|v| tension[u].iter().zip(&carried[v]).map(|(a, b)| a.iter().zip(b).map(|(x, y)| x * y).sum::<BigInt>()).sum::<BigInt>()).collect())
        .collect();
    let symmetric: Vec<Vec<BigInt>> = (0..k).map(|u| (0..k).map(|v| &coupling[u][v] + &coupling[v][u]).collect()).collect();
    // K_uv = C_uv/√(n_u n_v), on C released to below 2^60 and the root of n_u n_v 2^80 (directions only).
    let cr = released(&symmetric);
    let kk: Vec<Vec<BigInt>> = (0..k)
        .map(|u| (0..k).map(|v| div_round(&(&cr[u][v] << 50u32), &BigInt::from(ceil_sqrt(((c.n[present[u]] * c.n[present[v]]) as u128) << 80)))).collect())
        .collect();
    let kk: Vec<i64> = release_big(&kk.into_iter().flatten().collect::<Vec<_>>(), 30);
    let apply = |v: &[i64]| -> Vec<i128> { (0..k).map(|u| (0..k).map(|t| kk[u * k + t] as i128 * v[t] as i128).sum()).collect() };
    let inner = |a: &[i64], b: &[i64]| -> i128 { a.iter().zip(b).map(|(&x, &y)| x as i128 * y as i128).sum() };
    let mut modes: Vec<Vec<i64>> = Vec::new();
    while modes.len() < count.min(k) {
        let top = (0..k).max_by_key(|&u| kk[u * k + u]).unwrap_or(0);
        let mut v: Vec<i64> = (0..k).map(|u| (u == top) as i64).collect();
        let mut best: Option<(i128, i128, Vec<i64>)> = None;
        loop {
            for m in &modes {
                let (mm, mv) = (inner(m, m), inner(m, &v));
                let wide: Vec<BigInt> = v.iter().zip(m).map(|(&x, &y)| BigInt::from(mm) * x - BigInt::from(mv) * y).collect();
                v = release_big(&wide, 15);
            }
            let kv = apply(&v);
            let (num, den) = (v.iter().zip(&kv).map(|(&x, &y)| x as i128 * y).sum::<i128>(), inner(&v, &v));
            if den == 0 {
                break;
            }
            let gained = match &best {
                None => true,
                Some((bn, bd, _)) => (BigInt::from(num) * bd) << 15u32 > BigInt::from(*bn) * den * ((1i64 << 15) + 1),
            };
            if best.as_ref().is_none_or(|(bn, bd, _)| BigInt::from(num) * bd > BigInt::from(*bn) * den) {
                best = Some((num, den, v.clone()));
            }
            if !gained {
                break;
            }
            v = release_big(&kv.iter().map(|&x| BigInt::from(x)).collect::<Vec<_>>(), 15);
        }
        let (_, _, v) = best.ok_or("the coupling's power step found no mode")?;
        modes.push(v);
    }
    if present != p.present {
        return Err("the coupling's classes are not the passage's".into());
    }
    let zeros = vec![0; k];
    modes.iter().map(|m| pool_factor(p, [m, &zeros])).collect()
}

/// The pool `β` over the present classes as its factor over `x̂`: the least-norm `b` with
/// `bᵀx̂_u = β_u` for every present class, `b = Σ_u c_u x̂_u` with `(X̂X̂ᵀ)c = β`, real and imaginary
/// parts alike, released together only where they would leave the 64-bit word (a pool whose classes
/// differ widely keeps its quiet classes' values).
fn pool_factor(p: &Passage, beta: [&[i64]; 2]) -> Result<[Vec<i64>; 2]> {
    let k = p.present.len();
    let hats: Vec<&Vec<i64>> = p.present.iter().map(|&u| &p.hats[u]).collect();
    let gram: Vec<Vec<BigInt>> = (0..k).map(|u| (0..k).map(|v| BigInt::from(dot(hats[u], hats[v]))).collect()).collect();
    let rhs: Vec<Vec<BigInt>> = (0..k).map(|u| vec![BigInt::from(beta[0][u]), BigInt::from(beta[1][u])]).collect();
    let (_, coef) = solve_scaled(&gram, &rhs, true)?;
    let b: Vec<BigInt> = (0..2).flat_map(|f| (0..=p.width).map(move |r| (f, r))).map(|(f, r)| (0..k).map(|u| &coef[u][f] * hats[u][r]).sum()).collect();
    let released = release_big(&b, 62);
    Ok([released[..=p.width].to_vec(), released[p.width + 1..].to_vec()])
}

/// The bounds of a ring's factors over the passage: `|aᵀŝ|`, `|bᵀx̂|` (largest over the classes) and
/// `|gᵀx|`, each summing magnitudes.
fn bounds(p: &Passage, sc: &Scale, ring: &Ring) -> (u128, u128, u128) {
    let dims = p.dims;
    let alpha: u128 = (0..dims).map(|i| (ring.a[0][i].unsigned_abs() as u128 + ring.a[1][i].unsigned_abs() as u128) * sc.x[i]).sum();
    let beta: u128 = p.hats.iter().map(|h| dot(&ring.b[0], h).unsigned_abs() + dot(&ring.b[1], h).unsigned_abs()).max().unwrap_or(0);
    let gamma: u128 = (0..=dims).map(|i| ring.g[i].unsigned_abs() as u128 * sc.x[i]).sum();
    (alpha, beta, gamma)
}

/// The releases a ring with these factors is carried by: each factor's value released to below
/// `2^40` at its bound over the passage; its push, the product of the released values, released to
/// below `2^40` at the product's bound (for the step's columns, at the largest column's); and its
/// read released by the bits its memory can gain, `⌈log₂(1/(1 − ρ))⌉` with `ρ` the mode's largest
/// `|λ| + |β|`. Three released factors, or two and a carried coordinate (below `2^40` by
/// [`survey`]), multiply below `2^121`, so the push is formed exactly in 128 bits.
fn shifts(p: &Passage, sc: &Scale, ring: &Ring, step: Option<Factor>) -> Result<([u32; 3], u32, u32)> {
    let unit = 1u128 << MOVE_BITS;
    if sc.rho >= unit {
        return Err("the placement mode's moves can boost (|λ| + |β| ≥ 1): its ring has no bound".into());
    }
    let gain = bits(unit / (unit - sc.rho)) + 1;
    let (alpha, beta, gamma) = bounds(p, sc, ring);
    let release = [alpha, beta, gamma].map(|b| bits(b).saturating_sub(REACH));
    let held = |b: u128| bits(b).min(REACH);
    let largest_s = sc.x[..p.dims].iter().copied().max().unwrap_or(0);
    let bound_bits = match step {
        None => held(alpha) + held(beta) + held(gamma),
        Some(Factor::A) => held(beta) + held(gamma) + bits(largest_s),
        Some(Factor::B) => held(alpha) + held(gamma),
        Some(Factor::G) => held(alpha) + held(beta) + bits(sc.x.iter().copied().max().unwrap_or(0)),
    };
    Ok((release, bound_bits.saturating_sub(REACH), gain))
}

/// One step: the pass with the step's columns, and the leading canonical direction of its demand,
/// deflated by the founded ranks, against its loudness. Returns the founded parameters (as
/// [`leading_real`] gives them) and the step's circular share in thousandths (on released copies).
fn found_step(p: &Passage, sc: &Scale, ranks: &[Ring], ring: &Ring, factor: Factor) -> Result<(Vec<i64>, String, u64)> {
    let started = std::time::Instant::now();
    let (release, push_shift, read_shift) = shifts(p, sc, ring, Some(factor))?;
    let held = Ring { release, push_shift, read_shift, ..ring.clone() };
    let m = pass(p, ranks, Some((factor, &held)))?;
    let fit = rank_fit(&m)?;
    let (stacked, q) = step_blocks(&m, &fit);
    let w = p.width;
    // The deflated tension's metric, (L·D·Y')⁻¹ up to its scale, released: directions only.
    let identity: Vec<Vec<BigInt>> = (0..w).map(|r| (0..w).map(|r2| BigInt::from((r == r2) as i64)).collect()).collect();
    let (dy, yinv) = solve_scaled(&fit.y, &identity, false)?;
    let released = release_big(&yinv.iter().flatten().cloned().collect::<Vec<_>>(), 60);
    let mut metric = vec![vec![0i64; 2 * w]; 2 * w];
    for f in 0..2 {
        for r in 0..w {
            for r2 in 0..w {
                metric[f * w + r][f * w + r2] = released[r * w + r2];
            }
        }
    }
    let top = (0..w).max_by(|&x, &y| fit.y[x][x].cmp(&fit.y[y][y])).unwrap_or(0);
    let start: Vec<i64> = (0..2 * w).map(|r| (r == top) as i64).collect();
    let found = [leading_real(&stacked, &q, &metric, start)?];
    // The circular share on the released copies, ‖X θ‖²_(Y⁻¹) / θᵀQθ, in thousandths, read by the
    // metric's scale: the share is a ratio, so the released metric's scale is divided out by the
    // exact metric's diagonal read once.
    let theta = &found[0];
    let xt: Vec<BigInt> = stacked.iter().map(|row| row.iter().zip(theta).map(|(x, &t)| x * t).sum()).collect();
    let qt: BigInt = (0..m.k).map(|i| BigInt::from(theta[i]) * q[i].iter().zip(theta).map(|(x, &t)| x * t).sum::<BigInt>()).sum();
    let num: BigInt = (0..2).map(|f| (0..w).map(|r| &xt[f * w + r] * (0..w).map(|r2| &yinv[r][r2] * &xt[f * w + r2]).sum::<BigInt>()).sum::<BigInt>()).sum();
    // Y' = fit.y / (L·D): (Y')⁻¹ = L·D·fit.y⁻¹ = L·D·yinv/dy.
    let share = permille(&(num * &fit.y_scale), &(qt * dy));
    Ok((theta.clone(), share, started.elapsed().as_millis() as u64))
}

/// `Q⁻¹` on a released copy, rows on a common scale (directions only): Gauss–Jordan on
/// `[Q | 2^60 I]` in 128 bits with diagonal pivots (`Q` is a Gram released below `2^60`), each
/// changed row brought back below `2^62` at its largest entry, so a step is exact to `2^(−62)` of
/// its row; a pivot that is not positive (a direction no column reaches) is passed over and its row
/// of the inverse left zero. The identity stands at `Q`'s own width: on `[Q | I]` the first release
/// of a row moves its inverse half by `Q`'s width and keeps almost none of its digits (one block's
/// development read: the first step's share fell to 140 thousandths, against 528 with the exact
/// inverse).
fn inverse_released(q: &[i64], k: usize) -> Vec<Vec<BigInt>> {
    let fit = |row: &mut Vec<i128>| {
        let top = row.iter().map(|x| x.unsigned_abs()).max().unwrap_or(0);
        let excess = bits(top).saturating_sub(62);
        if excess > 0 {
            for x in row.iter_mut() {
                *x = release(*x, excess);
            }
        }
    };
    let mut rows: Vec<Vec<i128>> = (0..k).map(|i| (0..2 * k).map(|j| if j < k { q[i * k + j] as i128 } else { ((j - k == i) as i128) << 60 }).collect()).collect();
    let mut live = vec![false; k];
    for p in 0..k {
        let pivot = rows[p][p];
        if pivot <= 0 {
            continue;
        }
        live[p] = true;
        let prow = rows[p].clone();
        rows.par_iter_mut().enumerate().filter(|(i, row)| *i != p && row[p] != 0).for_each(|(_, row)| {
            let f = row[p];
            for (x, &y) in row.iter_mut().zip(&prow) {
                *x = pivot * *x - f * y;
            }
            row[p] = 0;
            fit(row);
        });
    }
    // Row i reads x_i = R_i / D_i: bring every row to the common scale 2^60 / max_i(|R_i|/D_i).
    let lift = (0..k).filter(|&i| live[i]).map(|i| bits(rows[i][k..].iter().map(|x| x.unsigned_abs()).max().unwrap_or(0)) as i64 - bits(rows[i][i] as u128) as i64).max().unwrap_or(0);
    let shift = (60 - lift).max(0) as u32;
    (0..k)
        .map(|i| {
            if !live[i] {
                return vec![BigInt::zero(); k];
            }
            let d = BigInt::from(rows[i][i]);
            rows[i][k..].iter().map(|&x| div_round(&(BigInt::from(x) << shift), &d)).collect()
        })
        .collect()
}

/// The leading generalized eigenvector of `(MᵀY⁻¹M, Q)` for a real factor, by the power step
/// `w = Q⁻¹Mᵀv`, `v ← Y⁻¹Mw` (found-tower-situated's `leading_canonical` with `M₁ = 0`). Each
/// coordinate is first scaled by the power of two `2^(e_j)` that brings `Q`'s diagonal to one
/// width (`Q′ = EQE`, `M′ = ME`, exact shifts: the quotient is unchanged and a quiet coordinate
/// keeps its digits through the release); `M′` and `Q′` are released to below `2^60`, `Q′⁻¹` is
/// [`inverse_released`]'s, each vector is released to `2^15` in the balanced coordinates (where a
/// released term is below `2^(−15)` of the largest by a loudness of one width), and the search stops when a step raises
/// `‖Mw‖²_(Y⁻¹)/(wᵀQw)` by less than `2^(−15)` of itself. Returns `w = E w′` exactly, released only
/// where it would leave the 64-bit word: released to `2^15` after `E`, a direction would lose the loud
/// coordinates, whose entries `E` leaves small.
fn leading_real(dm: &[Vec<BigInt>], dq: &[Vec<BigInt>], metric: &[Vec<i64>], mut v: Vec<i64>) -> Result<Vec<i64>> {
    let (rows, q) = (dm.len(), dq.len());
    let widest = (0..q).map(|j| dq[j][j].bits()).max().unwrap_or(0);
    let e: Vec<u64> = (0..q).map(|j| if dq[j][j].is_zero() { 0 } else { (widest - dq[j][j].bits()) / 2 }).collect();
    let scaled_m: Vec<BigInt> = dm.iter().flat_map(|row| row.iter().zip(&e).map(|(x, &ej)| x << ej)).collect();
    let scaled_q: Vec<BigInt> = (0..q).flat_map(|i| (0..q).map(move |j| (i, j))).map(|(i, j)| &dq[i][j] << (e[i] + e[j])).collect();
    let mt = release_big(&scaled_m, 60);
    let qt = release_big(&scaled_q, 60);
    let inverse = inverse_released(&qt, q);
    let mut best: Option<(BigInt, BigInt, Vec<i64>)> = None;
    loop {
        let g: Vec<i128> = (0..q).map(|j| (0..rows).map(|a| mt[a * q + j] as i128 * v[a] as i128).sum()).collect();
        let wide: Vec<BigInt> = inverse.par_iter().map(|row| row.iter().zip(&g).map(|(x, &y)| x * y).sum()).collect();
        let w = release_big(&wide, 15);
        let u: Vec<i128> = (0..rows).map(|a| (0..q).map(|j| mt[a * q + j] as i128 * w[j] as i128).sum()).collect();
        let mu: Vec<BigInt> = metric.iter().map(|row| row.iter().zip(&u).map(|(&x, &y)| BigInt::from(x) * y).sum()).collect();
        let num: BigInt = mu.iter().zip(&u).map(|(x, &y)| x * y).sum();
        let den: BigInt = (0..q).into_par_iter().map(|i| (0..q).map(|j| BigInt::from(qt[i * q + j] as i128 * w[i] as i128) * w[j]).sum::<BigInt>()).sum();
        v = release_big(&mu, 15);
        if den <= BigInt::zero() || w.iter().all(|&x| x == 0) {
            break;
        }
        let gained = match &best {
            None => true,
            Some((bn, bd, _)) => (&num * bd) << 15u32 > bn * &den * ((1i64 << 15) + 1),
        };
        if best.as_ref().is_none_or(|(bn, bd, _)| &num * bd > bn * &den) {
            best = Some((num, den, w));
        }
        if !gained {
            break;
        }
    }
    let w = best.ok_or("the power step found no direction")?.2;
    Ok(release_big(&w.iter().zip(&e).map(|(&x, &ej)| BigInt::from(x) << ej).collect::<Vec<_>>(), 62))
}

/// The unit ring: `a` zero, `b` and `g` their unit coordinates.
fn unit_ring(p: &Passage) -> Ring {
    let (dims, width) = (p.dims, p.width);
    Ring {
        a: [vec![0; dims], vec![0; dims]],
        b: [(0..=width).map(|j| (j == width) as i64).collect(), vec![0; width + 1]],
        g: (0..=dims).map(|j| (j == dims) as i64).collect(),
        release: [0; 3],
        push_shift: 0,
        read_shift: 0,
    }
}

fn join(v: &[i64]) -> String {
    v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")
}

/// `found-tower-ring STATE STATE_SHA TEXT TEXT_SHA MARKS MARKS_SHA STREAMS SECTION LEVEL MODE
/// RANKS STARTS ROUNDS OUT`: found `RANKS` ring forms riding mode `MODE` of level `LEVEL`, read at
/// the cells `MARKS` marks (one byte per byte of `TEXT`, nonzero where the reading looks). Each rank
/// is founded from the unit pool and from each of the classes' coupling's `STARTS` leading modes
/// ([`coupling_starts`]), each with the unit gate, in `ROUNDS` rounds of `a`, `b`, `g` and a closing
/// `a`, and keeps the start whose form gives the larger exact share of the founded ranks' channels
/// (found-tower-situated's law: search from more than one start, keep the larger). Each kept form
/// is written to `OUT` (create-new) as it is founded: a `FORM` line (`c = (aᵀŝ)(bᵀx̂)`, read by
/// `read-tower-situated`) and a `RING` line (its gate, mode and shifts). Each step prints its
/// circular share on released copies; each start and each rank the exact share of the ranks'
/// channels in thousandths (twice the nats a marked cell saves).
pub(super) fn found_tower_ring(args: &[String]) -> Result<()> {
    if args.len() != 15 {
        return Err("found-tower-ring STATE STATE_SHA TEXT TEXT_SHA MARKS MARKS_SHA STREAMS SECTION LEVEL MODE RANKS STARTS ROUNDS OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let marks = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let (streams, section) = (positive(&args[7])?, positive(&args[8])?);
    let (level, mode) = (count(&args[9])?, count(&args[10])?);
    let (ranks, starts, rounds) = (positive(&args[11])?, count(&args[12])?, count(&args[13])?);
    if level >= tower.declaration.levels || mode >= tower.declaration.modes {
        return Err("LEVEL or MODE names no level or mode of the tower".into());
    }
    if marks.len() != text.len() || text.is_empty() {
        return Err("MARKS holds one byte per byte of TEXT".into());
    }
    if std::path::Path::new(&args[14]).exists() {
        return Err("OUT exists: the forms are written create-new".into());
    }
    let chunk = text.len().div_ceil(streams);
    let cuts: Vec<(usize, usize)> = (0..streams).map(|s| (s * chunk, ((s + 1) * chunk).min(text.len()))).filter(|&(a, b)| a < b).collect();
    let (hats, _) = pair_hats(tower);
    let mut p = Passage {
        tower,
        text: text.iter().map(|&b| b as usize).collect(),
        marks,
        cuts,
        section,
        level,
        mode,
        hats,
        dims: 2 * tower.declaration.modes,
        width: tower.declaration.width,
        present: Vec::new(),
        streams: Vec::new(),
    };
    let (sc, coupling, streams) = survey(&p)?;
    p.present = (0..coupling.n.len()).filter(|&u| coupling.n[u] > 0).collect();
    p.streams = streams;
    println!(
        "RING_PASS cells={} marked={} streams={} section={section} level={level} mode={mode} rho_on_2^-30={} largest_state={} largest_covector={} read_ms={}",
        text.len(),
        p.marks.iter().filter(|&&m| m != 0).count(),
        p.cuts.len(),
        sc.rho,
        sc.x[..p.dims].iter().max().unwrap_or(&0),
        sc.y,
        started.elapsed().as_millis()
    );
    let pools = coupling_starts(&p, &coupling, starts)?;
    println!("RING_STARTS coupling_modes={} classes={} elapsed_ms={}", pools.len(), coupling.n.iter().filter(|&&n| n > 0).count(), started.elapsed().as_millis());
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(&args[14])?;
    std::io::Write::write_all(&mut file, format!("SITUATED level={level} dims={} width={} state_sha256={} text_sha256={} marks_sha256={} mode={mode}\n", p.dims, p.width, args[2], args[4], args[6]).as_bytes())?;
    let mut founded: Vec<Ring> = Vec::new();
    let order: Vec<Factor> = (0..rounds).flat_map(|_| [Factor::A, Factor::B, Factor::G]).chain([Factor::A]).collect();
    for rank in 0..ranks {
        let unit = unit_ring(&p);
        let candidates: Vec<(String, Ring)> = std::iter::once(("unit".to_string(), unit.clone()))
            .chain(pools.iter().enumerate().map(|(j, b)| (format!("coupling_mode_{}", j + 1), Ring { b: b.clone(), ..unit.clone() })))
            .collect();
        let mut kept: Option<(BigInt, BigInt, Ring, PassMoments)> = None;
        for (name, mut ring) in candidates {
            for (n, &factor) in order.iter().enumerate() {
                let (theta, share, ms) = found_step(&p, &sc, &founded, &ring, factor)?;
                match factor {
                    Factor::A => ring.a = [theta[..p.dims].to_vec(), theta[p.dims..].to_vec()],
                    Factor::B => ring.b = pool_factor(&p, [&theta[..p.present.len()], &theta[p.present.len()..]])?,
                    Factor::G => ring.g = theta,
                }
                println!("RING_STEP rank={rank} start={name} step={n} factor={factor:?} circular_permille={share} pass_ms={ms} elapsed_ms={}", started.elapsed().as_millis());
            }
            let (release, push_shift, read_shift) = shifts(&p, &sc, &ring, None)?;
            ring.release = release;
            ring.push_shift = push_shift;
            ring.read_shift = read_shift;
            let with: Vec<Ring> = founded.iter().cloned().chain([ring.clone()]).collect();
            let m = pass(&p, &with, None)?;
            let fit = rank_fit(&m)?;
            println!("RING_START rank={rank} start={name} exact_share_permille={} elapsed_ms={}", permille(&fit.share, &fit.share_den), started.elapsed().as_millis());
            if kept.as_ref().is_none_or(|(n, d, _, _)| &fit.share * d > n * &fit.share_den) {
                kept = Some((fit.share, fit.share_den, ring, m));
            }
        }
        let (share, share_den, ring, m) = kept.ok_or("no start was founded")?;
        let (push_shift, read_shift) = (ring.push_shift, ring.read_shift);
        // The form's release for read-tower-situated's instant reading: `(aᵀŝ)(bᵀx̂)` brought below 2^32.
        let (alpha, beta, _) = bounds(&p, &sc, &ring);
        let form_shift = (bits(alpha) + bits(beta)).saturating_sub(32);
        std::io::Write::write_all(&mut file, format!("FORM {rank} shift={form_shift} faces=re,im a={} ai={} b={} bi={}\n", join(&ring.a[0]), join(&ring.a[1]), join(&ring.b[0]), join(&ring.b[1])).as_bytes())?;
        std::io::Write::write_all(&mut file, format!("RING {rank} mode={mode} release={} push_shift={push_shift} read_shift={read_shift} g={}\n", join(&ring.release.map(i64::from)), join(&ring.g)).as_bytes())?;
        file.sync_data()?;
        founded.push(ring);
        println!(
            "RING_RANK rank={rank} channels={} marked_cells={} exact_share_permille={} push_shift={push_shift} read_shift={read_shift} elapsed_ms={}",
            2 * founded.len(),
            m.cells,
            permille(&share, &share_den),
            started.elapsed().as_millis()
        );
    }
    drop(file);
    let written = std::fs::read(&args[14])?;
    println!("RING_WRITTEN forms={} sha256={} elapsed_ms={}", founded.len(), sha256(&written)?, started.elapsed().as_millis());
    Ok(())
}

/// The value of a forms line's `key=…` word.
fn field<'a>(line: &'a str, key: &str) -> Result<&'a str> {
    line.split(' ').find_map(|w| w.strip_prefix(key).and_then(|r| r.strip_prefix('='))).ok_or_else(|| format!("a forms line lacks {key}=").into())
}

/// A forms line's comma-separated integers under `key`.
fn integers<T: std::str::FromStr>(line: &str, key: &str) -> Result<Vec<T>> {
    field(line, key)?.split(',').map(|v| v.parse::<T>().map_err(|_| format!("a forms line's {key} is not integers").into())).collect()
}

/// The ranks a founding wrote ([`found_tower_ring`]'s `SITUATED`, `FORM` and `RING` lines): the
/// tower they were founded on (its state's SHA-256), the level and mode they ride, and each rank.
fn read_forms(text: &str, dims: usize, width: usize) -> Result<(String, usize, usize, Vec<RingRank>)> {
    let lines: Vec<&str> = text.lines().collect();
    let head = lines.first().filter(|l| l.starts_with("SITUATED ")).ok_or("a ring's forms open with their SITUATED line")?;
    let (level, mode): (usize, usize) = (field(head, "level")?.parse()?, field(head, "mode")?.parse()?);
    if field(head, "dims")?.parse::<usize>()? != dims || field(head, "width")?.parse::<usize>()? != width {
        return Err("the forms were founded on a tower of another extent".into());
    }
    if lines.len() < 3 || lines.len() % 2 != 1 {
        return Err("a ring's forms hold a FORM and a RING line a rank".into());
    }
    let mut ranks = Vec::new();
    for (r, pair) in lines[1..].chunks(2).enumerate() {
        if !pair[0].starts_with(&format!("FORM {r} ")) || !pair[1].starts_with(&format!("RING {r} mode={mode} ")) {
            return Err(format!("rank {r}'s FORM and RING lines are not in order").into());
        }
        let release: Vec<u32> = integers(pair[1], "release")?;
        ranks.push(RingRank {
            a: [integers(pair[0], "a")?, integers(pair[0], "ai")?],
            b: [integers(pair[0], "b")?, integers(pair[0], "bi")?],
            g: integers(pair[1], "g")?,
            release: release.try_into().map_err(|_| "a ring's release is three shifts")?,
            push_shift: field(pair[1], "push_shift")?.parse()?,
            read_shift: field(pair[1], "read_shift")?.parse()?,
        });
    }
    Ok((field(head, "state_sha256")?.to_string(), level, mode, ranks))
}

/// [agent-inferred, October 25] `join-tower-ring STATE STATE_SHA FORMS FORMS_SHA OUT`: join the
/// ring ranks `FORMS` founded on the tower `STATE` (`found-tower-ring`'s output, refused when
/// founded on another tower) as the tower's resident ring face
/// ([`holonics::hnn::tower::RingFace`]), its readout at zero, and write the learner create-new to
/// `OUT`. Each rank's face is its read as a ratio to its own power, so nothing is fitted to a
/// passage; the joined tower codes every passage as the tower alone until its readout learns
/// (`a_ring_faced_tower_opens_on_itself`).
pub(super) fn join_tower_ring(args: &[String]) -> Result<()> {
    if args.len() != 6 {
        return Err("join-tower-ring STATE STATE_SHA FORMS FORMS_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let forms = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    if std::path::Path::new(&args[5]).exists() {
        return Err("OUT exists: the joined learner is written create-new".into());
    }
    let d = learner.tower.declaration.clone();
    let (founded_on, level, mode, ranks) = read_forms(std::str::from_utf8(&forms)?, 2 * d.modes, d.width)?;
    if founded_on != args[2] {
        return Err("the forms were founded on another tower: the moves they ride and the encoding their pools read are this one's only".into());
    }
    let n = ranks.len();
    let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| learner.tower.encoding(u).to_vec()).collect();
    let mut out = learner;
    out.join_ring_face(RingFace::new(&d, level, mode, ranks, opening).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    let written = out.to_text();
    std::io::Write::write_all(&mut std::fs::OpenOptions::new().write(true).create_new(true).open(&args[5])?, written.as_bytes())?;
    println!(
        "RING_JOIN level={level} mode={mode} ranks={n} material={} sha256={} elapsed_ms={}",
        out.tower.theta.len(),
        sha256(written.as_bytes())?,
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [agent-inferred, October 25] `read-tower-at STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA`: the
/// tower's own guess at the cells `CELLS` names (ascending cell indices, whitespace-separated; cell
/// `i` has heard `TEXT[..=i]` and codes `TEXT[i + 1]`), `TEXT` read as one passage from rest. Each
/// named cell prints `AT i next top code`: the class that arrives, the class the face gives the
/// largest mass (the smaller class on a tie) and the code of the arriving class on `2^(−20)` bits;
/// with a ring face joined, also `FORMS i next ρ…`, the ring's face as the readout reads it (the
/// probe's situated format). A reading beside the code: the tower is not moved.
pub(super) fn read_tower_at(args: &[String]) -> Result<()> {
    if args.len() != 7 {
        return Err("read-tower-at STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let named: Vec<usize> = std::str::from_utf8(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?.split_whitespace().map(|w| w.parse::<usize>()).collect::<std::result::Result<_, _>>()?;
    if named.windows(2).any(|w| w[0] >= w[1]) || named.last().is_some_and(|&i| i + 1 >= text.len()) {
        return Err("CELLS names ascending cells of TEXT, each coding a class that arrives".into());
    }
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let tower = &learner.tower;
    let mut at = named.iter().peekable();
    let (mut right, mut code) = (0usize, 0i64);
    let read_to = named.last().map_or(0, |&i| i + 2);
    tower
        .read_ring(&mut tower.rest(), &classes[..read_to], |i, face, ring| {
            if at.peek() != Some(&&i) {
                return Ok(());
            }
            at.next();
            let next = classes[i + 1];
            let top = (0..face.masses.len()).max_by_key(|&c| (face.masses[c], std::cmp::Reverse(c))).expect("a nonempty alphabet");
            let c = face.code(next);
            right += (top == next) as usize;
            code += c;
            println!("AT {i} {next} {top} {c}");
            if let Some((_, rho)) = ring {
                println!("FORMS {i} {next} {}", rho.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(" "));
            }
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    println!(
        "TOWER_AT cells={} top_is_next={right} code_on_2^-20={code} ring_ranks={} elapsed_ms={}",
        named.len(),
        tower.ring_face().map_or(0, |f| f.ranks()),
        started.elapsed().as_millis()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The released inverse of a Gram at the width the search gives it (below `2^60`) is `Q⁻¹` up to
    /// one scale: `Q X` is diagonal to `2^(−40)` of its diagonal, which stands equal on every row.
    /// On `[Q | I]` the first release would have moved the inverse half by `Q`'s width.
    #[test]
    fn the_released_inverse_keeps_the_inverse_at_the_grams_width() {
        let a: [[i64; 3]; 3] = [[5, 1, -2], [1, 4, 1], [-2, 1, 6]];
        let k = 3;
        let q: Vec<i64> = (0..k * k).map(|ij| a[ij / k][ij % k] << 57).collect();
        let x = inverse_released(&q, k);
        let qx: Vec<Vec<BigInt>> = (0..k).map(|i| (0..k).map(|j| (0..k).map(|t| BigInt::from(q[i * k + t]) * &x[t][j]).sum()).collect()).collect();
        for i in 0..k {
            assert!(qx[i][i] > BigInt::zero());
            for j in 0..k {
                let off = if i == j { (&qx[i][i] - &qx[0][0]) << 40u32 } else { &qx[i][j] << 40u32 };
                assert!(off.magnitude() < qx[0][0].magnitude(), "row {i}, column {j}");
            }
        }
    }

    /// A direction whose coordinates differ by 24 bits of loudness keeps both: `M = [2^29, 2^5]`,
    /// `Q = diag(2^58, 2^10)` lead to `w ∝ Q⁻¹Mᵀ = (1, 2^24)`, which released to `2^15` after the
    /// balancing would be `(0, 2^15)` and save half of what it does.
    #[test]
    fn the_founded_direction_keeps_its_loud_coordinates() {
        let dm = vec![vec![BigInt::from(1i64 << 29), BigInt::from(1i64 << 5)]];
        let dq = vec![vec![BigInt::from(1i64 << 58), BigInt::zero()], vec![BigInt::zero(), BigInt::from(1i64 << 10)]];
        let w = leading_real(&dm, &dq, &[vec![1]], vec![1]).unwrap();
        assert!(w[0] != 0 && w[1] != 0, "{w:?}");
        let ratio = BigInt::from(w[1]) / BigInt::from(w[0]);
        assert!((BigInt::from((1i64 << 24) - (1 << 10))..=BigInt::from((1i64 << 24) + (1 << 10))).contains(&ratio), "{w:?}");
    }
}
