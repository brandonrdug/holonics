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

use super::tower_situated::{div_round, gcd, lcm, permille};
use super::tower_train::{count, pair_hats, positive, release_big, solve_scaled, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::{hand_after, ring_carry, RingFace, RingRank, Tower, TowerError, TowerLearner, FACE_BITS, MOVE_BITS};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
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

/// The factor a step founds: the push's `a`, `b` or `g`.
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
    /// Per cell the slot of its pair `(seam, class)` in [`Passage::pairs`] (the seam the start `A`
    /// at the stream's opening cell, which a ring at rest meets).
    slots: Vec<usize>,
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
    /// Every pair `(seam, class)` a ring meets over the passage, ascending: the keys of a founded
    /// table of pair moves ([`RingFace::move_at`]).
    pairs: Vec<(usize, usize)>,
    /// The class whose arrival restarts the rings' hand, when the closure located one
    /// ([`RingFace::with_restarts`]).
    restart: Option<usize>,
}

/// A table of pair moves over [`Passage::pairs`], `[Re λ, Im λ, Re β, Im β]` on `2^(−30)`.
type Table = Vec<[i64; 4]>;

/// The move a ring makes at a stream's cell: the table's pair move, or the placement mode's move.
fn move_of(stream: &Stream, at: usize, table: Option<&Table>) -> [i128; 4] {
    match table {
        Some(t) => t[stream.slots[at]].map(i128::from),
        None => stream.moves[at].map(i128::from),
    }
}

/// `|λ| + |β|` rounded up on the moves' grain, each modulus rounded up.
fn move_reach(m: [i64; 4]) -> u128 {
    let sq = |a: i64, b: i64| (a.unsigned_abs() as u128).pow(2) + (b.unsigned_abs() as u128).pow(2);
    ceil_sqrt(sq(m[0], m[1])) + ceil_sqrt(sq(m[2], m[3]))
}

/// [agent-inferred, October 25] `|λ| + |β| < 1` decided exactly, the library's passivity law for a
/// ring's pair move: `B < U²` and `4U²B < (U² + B − L)²` with the right side positive (`U = 2^30`,
/// `L = |λ|²`, `B = |β|²`).
fn passive(m: [i64; 4]) -> bool {
    let u2 = BigInt::from(1u8) << (2 * MOVE_BITS);
    let sq = |a: i64, b: i64| BigInt::from(a) * a + BigInt::from(b) * b;
    let (l, b) = (sq(m[0], m[1]), sq(m[2], m[3]));
    if b >= u2 {
        return false;
    }
    let right = &u2 + &b - l;
    right > BigInt::zero() && u2 * b * 4 < &right * &right
}

/// The passage's scale with `rho` read from a table of pair moves when one is founded.
fn scale_with(sc: &Scale, table: Option<&Table>) -> Scale {
    let rho = table.map_or(sc.rho, |t| t.iter().map(|&m| move_reach(m)).max().unwrap_or(0));
    Scale { x: sc.x.clone(), y: sc.y, rho }
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
/// the marked cells. The rings share the moves, so one hand a stream ([`hand_after`]) reads them all
/// in their own hand, `(Re h, ±Im h)`, as the library reads a ring, and the passage's restarting
/// class re-bases them all into it ([`RingFace::with_restarts`]).
fn pass(p: &Passage, table: Option<&Table>, ranks: &[Ring], step: Option<(Factor, &Ring)>) -> Result<PassMoments> {
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
            let (mut marked, mut hand) = (0, false);
            for (at, &class) in stream.classes.iter().enumerate() {
                let i = stream.open + at;
                let s = &stream.faces[at * dims..(at + 1) * dims];
                let hat = &p.hats[class];
                let m = move_of(stream, at, table);
                hand = hand_after(m, hand);
                let own = if hand { -1 } else { 1 };
                let mut c = Vec::with_capacity(channels);
                for (h, ring) in held.iter_mut().zip(ranks) {
                    let (alpha, gamma) = ring.state_factors(s);
                    let v = ring.push(alpha, ring.pool(hat), gamma)?;
                    let carried = ring_carry(m, *h);
                    *h = (carried.0 + v.0, carried.1 + v.1);
                    c.push(release(h.0, ring.read_shift));
                    c.push(own * release(h.1, ring.read_shift));
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
                        phi[1][j] = narrow(own * release(cols[1][j], ring.read_shift))?;
                    }
                }
                if hand && p.restart == Some(class) {
                    held.iter_mut().for_each(|h| h.1 = -h.1);
                    cols[1].iter_mut().for_each(|y| *y = -*y);
                    hand = false;
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
            let mut stream = Stream { open, start, classes: Vec::with_capacity(end - open), moves: Vec::with_capacity(end - open), slots: Vec::new(), faces: Vec::with_capacity((end - open) * dims), covectors: Vec::new() };
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
/// [`leading_real`] gives them) and the step's circular share as an exact ratio (on released
/// copies).
fn found_step(p: &Passage, sc: &Scale, table: Option<&Table>, ranks: &[Ring], ring: &Ring, factor: Factor) -> Result<(Vec<i64>, (BigInt, BigInt), u64)> {
    let started = std::time::Instant::now();
    let (release, push_shift, read_shift) = shifts(p, &scale_with(sc, table), ring, Some(factor))?;
    let held = Ring { release, push_shift, read_shift, ..ring.clone() };
    let m = pass(p, table, ranks, Some((factor, &held)))?;
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
    Ok((theta.clone(), (num * &fit.y_scale, qt * dy), started.elapsed().as_millis() as u64))
}

/// [agent-inferred, October 25] **A round of the founding's alternation pays** when it moves the
/// form by more than the error the marked cells leave it: its saving reaches half a nat for each
/// free parameter it re-states. The share counts twice the nats a marked cell saves, so a round
/// gaining `Δ` saves `N Δ / 2` nats over the `N` marked cells; a step that refits one factor exactly
/// saves `½ δᵀHδ`, `δ` its move and `H` the code's curvature in that factor, and the factor's own
/// estimation error has `E[eᵀHe]` at least its count of free parameters, so a round saving less than
/// half that count moves the factors by less than one standard error each, a difference no
/// receiver of these cells resolves. `free` is the round's free parameters, each factor's entries
/// less its scale (a gauge: the ring is read as a ratio to its own power): `(2·dims − 1) +
/// (2·present − 1) + dims`. The first round always runs, and a round that loses share never pays.
/// A paying round gains at least `free/N` of share and the share is at most one, so at most
/// `(1 − share₀)·N/free` rounds pay. This replaces a one-bit rule, under which the unit start's
/// alternation ran 65 rounds and 257 s, still saving about two bits a round, in a slow tail that
/// moved the form inside its own error (`ring/found14.txt`), and before it an authored count of
/// three rounds. Returns the decision and the round's saving in thousandths of a nat, a reading.
fn round_pays(marked: usize, free: usize, last: Option<&(BigInt, BigInt)>, share: &(BigInt, BigInt)) -> (bool, String) {
    use holonics::ratio::Rat;
    let Some(last) = last else {
        return (true, "-".into());
    };
    if share.1.is_zero() || last.1.is_zero() {
        return (false, "0".into());
    }
    let gain = Rat::new(share.0.clone(), share.1.clone()) - Rat::new(last.0.clone(), last.1.clone());
    let saved = gain * Rat::new(BigInt::from(marked), BigInt::from(2));
    let millinats = (&saved * Rat::from_integer(BigInt::from(1000))).round().to_integer().to_string();
    (saved >= Rat::new(BigInt::from(free), BigInt::from(2)), millinats)
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

/// [agent-inferred, October 25] **The pairs a ring meets and the mode's moves at them.** Every
/// cell's pair `(seam, class)` over the passage (the seam the start `A` at a stream's opening cell,
/// as a stream read from rest meets it) is collected, ascending, and each stream's cells take their
/// slots. Each pair's move is the exact mean of the placement mode's moves at its cells (the mode's
/// own where they agree, since level 0's moves are keyed by the arriving class), rounded to the
/// moves' grain: the memory the closure's table keeps ([`closure_table`]). Returns the table and
/// the count of pairs whose cells the mode moved differently.
fn pair_table(p: &mut Passage) -> Result<(Table, usize)> {
    let alphabet = p.tower.declaration.alphabet;
    let seam = |stream: &Stream, at: usize| if at == 0 { alphabet } else { stream.classes[at - 1] };
    let mut pairs: Vec<(usize, usize)> = p.streams.iter().flat_map(|stream| (0..stream.classes.len()).map(move |at| (seam(stream, at), stream.classes[at]))).collect();
    pairs.sort_unstable();
    pairs.dedup();
    let mut sums: Vec<([i128; 4], i128, [i64; 4], bool)> = vec![([0; 4], 0, [0; 4], false); pairs.len()];
    for stream in p.streams.iter_mut() {
        stream.slots = (0..stream.classes.len()).map(|at| pairs.binary_search(&(seam(stream, at), stream.classes[at])).expect("a collected pair")).collect();
        for (at, &q) in stream.slots.iter().enumerate() {
            let m = stream.moves[at];
            let (sum, n, first, varies) = &mut sums[q];
            if *n == 0 {
                *first = m;
            }
            *varies |= *first != m;
            for (x, &v) in sum.iter_mut().zip(&m) {
                *x += v as i128;
            }
            *n += 1;
        }
    }
    let table: Table = sums.iter().map(|(sum, n, _, _)| sum.map(|x| div_round(&BigInt::from(x), &BigInt::from(*n)).try_into().expect("a mean move inside its moves"))).collect();
    if table.iter().any(|&m| !passive(m)) {
        return Err("a mode's mean move that boosts: its ring has no bound".into());
    }
    let varying = sums.iter().filter(|s| s.3).count();
    p.pairs = pairs;
    Ok((table, varying))
}

/// [agent-inferred, October 25] **The loop-closure rows of an origin** (the Bombe's menu). A ring
/// pushed at its origin's arrival and turned by pair moves `λ_q = ρ_q ω^(θ_q)` (`ω` a primitive
/// `n`-th root of unity) holds at a marked cell `t` the turn `N_t θ`, `N_t` the count of each pair
/// met since the origin's last arrival in the cell's stream (the pair ending at the origin is not
/// counted: its move restarts the ring). The ring names the class arriving after `t` when a key
/// `(θ, ψ)` closes every loop, `N_t θ ≡ ψ(C_t) (mod n)`.
///
/// [agent-inferred, October 25] With a reflector `r`, each pair ending at `r` reflects the ring,
/// `φ ↦ θ_q − φ` ([`closure_table`]), and the ring is read in its own hand `σ = ±1`, reversed by
/// each reflection since the origin's arrival ([`hand_after`]). Read in its hand, a turn and a
/// reflection alike add `σ_k θ_(q_k)`, `σ_k` the hand after cell `k`'s move (a reflection read in
/// the reversed hand: `−(θ − φ) = σφ + σ'θ`, `σ' = −σ`), so `N_t` counts each pair with the hand in
/// force where it is met. A restarting class `e` restores the hand after its own pair is counted
/// ([`RingFace::with_restarts`]), so the pairs after it count forward. No reflector or restart is
/// named to the closure: [`found_closure`] tries none and each class. Returns the rows
/// `(N_t, C_t)`, one per marked counted cell that an origin arrival precedes in its stream, each
/// count that cancels to zero left out, the count of reflections met after an origin, and whether
/// a restart met a reversed hand.
#[allow(clippy::type_complexity)]
fn closure_rows(p: &Passage, origin: usize, reflector: Option<usize>, restart: Option<usize>) -> (Vec<(Vec<(usize, i64)>, usize)>, usize, bool) {
    let read: Vec<(Vec<(Vec<(usize, i64)>, usize)>, usize, bool)> = p
        .streams
        .par_iter()
        .map(|stream| {
            let mut rows = Vec::new();
            let (mut count, mut hand, mut met, mut restored): (Option<std::collections::BTreeMap<usize, i64>>, i64, usize, bool) = (None, 1, 0, false);
            for (at, &class) in stream.classes.iter().enumerate() {
                let i = stream.open + at;
                if class == origin {
                    count = Some(Default::default());
                    hand = 1;
                } else if let Some(c) = count.as_mut() {
                    if Some(class) == reflector {
                        hand = -hand;
                        met += 1;
                    }
                    *c.entry(stream.slots[at]).or_insert(0) += hand;
                    if hand < 0 && Some(class) == restart {
                        hand = 1;
                        restored = true;
                    }
                }
                if i < stream.start || p.marks[i] == 0 || i + 1 >= p.text.len() {
                    continue;
                }
                if let Some(c) = &count {
                    rows.push((c.iter().filter(|&(_, &v)| v != 0).map(|(&q, &v)| (q, v)).collect(), p.text[i + 1]));
                }
            }
            (rows, met, restored)
        })
        .collect();
    let (met, restored) = (read.iter().map(|r| r.1).sum(), read.iter().any(|r| r.2));
    (read.into_iter().flat_map(|r| r.0).collect(), met, restored)
}

/// `a^e mod p` for `p < 2^31` (so a product of two residues stays in 64 bits).
fn pow_mod(a: u64, mut e: u64, p: u64) -> u64 {
    let (mut base, mut out) = (a % p, 1u64);
    while e > 0 {
        if e & 1 == 1 {
            out = out * base % p;
        }
        base = base * base % p;
        e >>= 1;
    }
    out
}

/// `a⁻¹ mod p` for a prime `p < 2^31` (Fermat).
fn inv_mod(a: u64, p: u64) -> u64 {
    pow_mod(a, p - 2, p)
}

/// `n < 2^31` is prime: Miller–Rabin on the bases 2, 7 and 61, exact below 4,759,123,141.
fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for q in [2u64, 3, 5, 7, 11, 13, 61] {
        if n % q == 0 {
            return n == q;
        }
    }
    let (mut d, mut r) = (n - 1, 0u32);
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    [2u64, 7, 61].iter().all(|&a| {
        let mut x = pow_mod(a, d, n);
        if x == 1 || x == n - 1 {
            return true;
        }
        (1..r).any(|_| {
            x = x * x % n;
            x == n - 1
        })
    })
}

/// The primes below `2^31`, descending: the moduli a closure system is read under.
fn wide_primes() -> impl Iterator<Item = u64> {
    (2..1u64 << 31).rev().filter(|&n| is_prime(n))
}

/// A row echelon modulo a prime: the pivot columns ascending, the reduced rows (each one at its
/// pivot and zero at every other pivot), and the row of the system each pivot came from.
pub(super) struct Echelon {
    pub(super) pivots: Vec<usize>,
    rows: Vec<Vec<u64>>,
    sources: Vec<usize>,
}

/// [agent-inferred, October 25] **The reduced row echelon of integer rows modulo a prime**
/// `p < 2^31`, built one row at a time against the basis so far, stopping when the rank reaches
/// `stop`. The basis is kept reduced (each row one at its pivot and zero at every other pivot), so an
/// arriving row is reduced by the basis rows at its own nonzero entries in the pivot columns alone:
/// a closure row counts the pairs of one loop, so it meets a few pivots where a basis kept only in
/// echelon form is met at nearly all of them once the row fills in. The reduced row is the one
/// vector of `row + span(basis)` that is zero at every pivot, so the pivots, the rows kept and the
/// echelon are those of reducing against the echelon basis in order (the form this replaced; on the
/// sums' and differences' units together one closure's echelons took about 18 core-seconds,
/// `ring/found34sd.txt`).
pub(super) fn echelon_mod(rows: &[Vec<i128>], p: u64, stop: usize) -> Echelon {
    let wide = p as i128;
    let mut basis: Vec<(usize, Vec<u64>)> = Vec::new();
    let mut sources = Vec::new();
    for (i, row) in rows.iter().enumerate() {
        if basis.len() == stop {
            break;
        }
        let mut r: Vec<u64> = row.iter().map(|&x| x.rem_euclid(wide) as u64).collect();
        let met: Vec<(usize, u64)> = basis.iter().enumerate().filter_map(|(k, (c, _))| (r[*c] != 0).then_some((k, r[*c]))).collect();
        for (k, f) in met {
            let g = p - f;
            for (x, &y) in r.iter_mut().zip(&basis[k].1) {
                *x = (*x + g * y) % p;
            }
        }
        let Some(c) = r.iter().position(|&x| x != 0) else { continue };
        let inv = inv_mod(r[c], p);
        r.iter_mut().for_each(|x| *x = *x * inv % p);
        for (_, b) in basis.iter_mut() {
            let f = b[c];
            if f != 0 {
                let g = p - f;
                for (x, &y) in b.iter_mut().zip(&r) {
                    *x = (*x + g * y) % p;
                }
            }
        }
        basis.push((c, r));
        sources.push(i);
    }
    let mut order: Vec<usize> = (0..basis.len()).collect();
    order.sort_by_key(|&k| basis[k].0);
    Echelon { pivots: order.iter().map(|&k| basis[k].0).collect(), sources: order.iter().map(|&k| sources[k]).collect(), rows: order.into_iter().map(|k| std::mem::take(&mut basis[k].1)).collect() }
}

/// `det M` and `det M · M⁻¹ V` modulo a prime `q < 2^31` by Gauss–Jordan elimination, `M` square
/// and `V` its right-hand columns (row by row); `None` where `q` divides `det M`.
fn cramer_mod(m: &[Vec<i128>], v: &[Vec<i128>], q: u64) -> Option<(u64, Vec<Vec<u64>>)> {
    let (n, k, wide) = (m.len(), v.first().map_or(0, Vec::len), q as i128);
    let mut a: Vec<Vec<u64>> = m.iter().zip(v).map(|(row, rhs)| row.iter().chain(rhs).map(|&x| x.rem_euclid(wide) as u64).collect()).collect();
    let mut det = 1u64;
    for c in 0..n {
        let i = (c..n).find(|&i| a[i][c] != 0)?;
        if i != c {
            a.swap(i, c);
            det = (q - det) % q;
        }
        det = det * a[c][c] % q;
        let inv = inv_mod(a[c][c], q);
        a[c].iter_mut().for_each(|x| *x = *x * inv % q);
        let pivot = a[c].clone();
        for (j, row) in a.iter_mut().enumerate() {
            let f = row[c];
            if j != c && f != 0 {
                let g = q - f;
                for (x, &y) in row.iter_mut().zip(&pivot) {
                    *x = (*x + g * y) % q;
                }
            }
        }
    }
    Some((det, a.iter().map(|row| row[n..n + k].iter().map(|&x| x * det % q).collect()).collect()))
}

/// [agent-inferred, October 25] **An exact nonzero maximal minor of a closure system, and its
/// rank over the rationals certified.** The rank modulo a prime below `2^31` ([`echelon_mod`])
/// is at most the rank over the rationals; its pivot rows `I` and columns `J` give a minor
/// `M = A[I, J]` nonzero modulo that prime, so nonzero. Every free column `f` gives the kernel
/// vector `k_J = det M · M⁻¹(−A[I, f])`, `k_f = det M` (Cramer: integers), read exactly by the
/// Chinese remainder theorem over primes whose product passes twice Hadamard's bound
/// `∏_(i∈I) ‖A[i, J ∪ F]‖`, which bounds every minor these are. When every row of the system
/// annihilates every such vector, the rank over the rationals is no more than the rank modulo the
/// prime, so equal to it; else a row the prime lost is independent, and the next prime is read.
/// Returns the rank, `det M` and the certified kernel over the rationals, one integer vector a free
/// column (`det M` there, `M⁻¹`'s solution at the pivots, scaled by `det M`). No elimination over the integers is made: its entries grew past
/// 128 bits in `ring/found19.txt` and past the founding's deadline in `BigInt` in
/// `ring/found20.txt`, while the minor's entries stay the rows' own.
pub(super) fn rational_rank(rows: &[Vec<i128>]) -> (usize, BigInt, Vec<Vec<BigInt>>) {
    let columns = rows.first().map_or(0, Vec::len);
    for p in wide_primes() {
        let e = echelon_mod(rows, p, columns);
        let (r, pivots) = (e.pivots.len(), &e.pivots);
        let free: Vec<usize> = (0..columns).filter(|c| pivots.binary_search(c).is_err()).collect();
        let m: Vec<Vec<i128>> = e.sources.iter().map(|&i| pivots.iter().map(|&c| rows[i][c]).collect()).collect();
        let v: Vec<Vec<i128>> = e.sources.iter().map(|&i| free.iter().map(|&f| -rows[i][f]).collect()).collect();
        // Hadamard: ∏ ‖A[i, J ∪ F]‖² over the pivot rows, as bits of the bound on a minor.
        let square: BigInt = e.sources.iter().map(|&i| BigInt::from(rows[i].iter().map(|&x| x * x).sum::<i128>().max(1))).product();
        let bound_bits = square.bits() / 2 + 2;
        let (mut modulus, mut det, mut y) = (BigInt::from(1), BigInt::zero(), vec![vec![BigInt::zero(); free.len()]; r]);
        for q in wide_primes().filter(|&q| q != p) {
            if modulus.bits() > bound_bits {
                break;
            }
            let Some((dq, yq)) = cramer_mod(&m, &v, q) else { continue };
            let bq = BigInt::from(q);
            let step = BigInt::from(inv_mod((&modulus % &bq).to_u64().expect("a residue below its prime"), q));
            let join = |x: &mut BigInt, value: u64| {
                let lift = ((BigInt::from(value) - &*x) % &bq + &bq) % &bq * &step % &bq;
                *x += &modulus * lift;
            };
            join(&mut det, dq);
            for (row, yrow) in y.iter_mut().zip(&yq) {
                for (x, &value) in row.iter_mut().zip(yrow) {
                    join(x, value);
                }
            }
            modulus *= bq;
        }
        let half = &modulus >> 1u32;
        let centre = |x: &mut BigInt| {
            if *x > half {
                *x -= &modulus;
            }
        };
        centre(&mut det);
        y.iter_mut().flatten().for_each(centre);
        let kernel: Vec<Vec<BigInt>> = free
            .iter()
            .enumerate()
            .map(|(t, &f)| {
                let mut k = vec![BigInt::zero(); columns];
                k[f] = det.clone();
                for (j, &c) in pivots.iter().enumerate() {
                    k[c] = y[j][t].clone();
                }
                k
            })
            .collect();
        let certified = rows.par_iter().all(|row| kernel.iter().all(|k| row.iter().zip(k).filter(|(a, _)| **a != 0).map(|(&a, x)| x * BigInt::from(a)).sum::<BigInt>().is_zero()));
        if certified {
            return (r, det, kernel);
        }
    }
    unreachable!("a prime past the bound reads the rank over the rationals")
}

/// [agent-inferred, October 25] **A key's readable moduli**: the prime factors of `x > 1` below
/// `2^(FACE_BITS + 3)`, ascending, each once (trial division). A key mod `n` places adjacent
/// residues `2π/n` apart on the ring's unit turn, a chord of `2π·2^FACE_BITS/n` grains of the face
/// the readout reads it on; a prime past `2π·2^FACE_BITS < 2^(FACE_BITS + 3)` turns the ring by less
/// than one grain a residue, which no reader of the face separates, so a larger factor is not
/// sought (and a pivot's cofactor past it needs no factoring).
pub(super) fn readable_primes(x: &BigInt) -> Vec<i128> {
    let bound = 1i128 << (FACE_BITS + 3);
    let mut out = Vec::new();
    let mut x = x.clone();
    let mut d = 2i128;
    while d < bound && BigInt::from(d) * d <= x {
        let dd = BigInt::from(d);
        if (&x % &dd).is_zero() {
            out.push(d);
            while (&x % &dd).is_zero() {
                x /= &dd;
            }
        }
        d += 1;
    }
    if let Some(v) = i128::try_from(&x).ok().filter(|&v| v > 1 && v < bound) {
        out.push(v);
    }
    out
}

/// What one origin's closure system admits, under its reflector: its sizes, its rank over the
/// rationals, the size of its certified minor and that minor's readable primes (the candidate
/// moduli), the primes at which its rank falls (each with the fall) and, when a key reads the
/// arriving classes injectively, the key.
struct Closure {
    origin: usize,
    reflector: Option<usize>,
    /// The reflections met after an origin, over the passage.
    reflections: usize,
    restart: Option<usize>,
    rows: usize,
    unique: usize,
    columns: usize,
    rank: usize,
    minor_bits: u64,
    candidates: Vec<i128>,
    torsion: Vec<(i128, usize)>,
    key: Option<Key>,
}

/// A closure's key: its modulus `n`, `θ` per pair slot and `ψ` per class, whether it closes the
/// loops over the integers (`exact`, a vector of the rational kernel) or modulo its torsion, and the
/// count of rows it fails (zero: a key is exact by construction, and the count is its receipt).
struct Key {
    modulus: i128,
    theta: Vec<(usize, i128)>,
    psi: Vec<(usize, i128)>,
    failures: usize,
    exact: bool,
}

impl Key {
    /// The order the keys are kept in: one that closes the loops over the integers before one that
    /// closes them modulo its torsion; of the exact, the smaller modulus (the same loops closed on
    /// wider turns); of the torsion keys, the larger (more of the closure's torsion carried).
    fn order(&self) -> (bool, i128) {
        (!self.exact, if self.exact { self.modulus } else { -self.modulus })
    }
}

/// [agent-inferred, October 25] **The key an origin's loops close on.** The rows ([`closure_rows`])
/// as an integer system `[N | −C]` over the pair slots they meet and the classes that arrive;
/// its rank over the rationals and a nonzero maximal minor ([`rational_rank`]). A prime `p` drops
/// the rank exactly when it divides every maximal minor (the product of the system's Smith
/// invariants), so the candidate moduli are the minor's readable primes ([`readable_primes`]); at
/// each the rank mod `p` is read against the rank over the rationals, a fall being torsion: a key
/// mod `p` that no rational key gives. At each torsion prime
/// the kernel mod `p` ([`echelon_mod`], one vector per free column) is read for the vector whose
/// `ψ` takes the most values (a ring's turn names a class only where `ψ` separates them); the
/// torsion primes' keys are joined by the Chinese remainder theorem over the subsets of primes in
/// descending product, and the first whose `ψ` is injective over the arriving classes is the key:
/// the whole torsion where it separates every class. No modulus is proposed: the moduli are the
/// closure's own torsion. The key once took the smallest separating modulus; at the sums' units
/// that kept 10 of the torsion `110 = 2·5·11` and dropped the eleven, which reads the alternating
/// digit sum and with the units fixes the sum modulo 110 (the newline closure record, §§2–3), so
/// the key now keeps every torsion prime the closure located [agent-inferred, October 25].
///
/// [agent-inferred, October 25] Before the torsion, the rational kernel is read: a kernel vector
/// (divided by its entries' divisor) whose `ψ` is injective closes every loop over the integers,
/// `N_t θ = ψ(C_t)`, so modulo any `n` past its `ψ`'s span; its key is taken modulo
/// `n = max ψ − min ψ + 1`, the least that keeps the classes apart, when that is readable (below
/// `2^(FACE_BITS + 3)`, [`readable_primes`]). An exact key is kept before a torsion key. Returns
/// `None` when the reflector never arrives after the origin (its rows are the reflector-free rows),
/// or the restart never meets a reversed hand (its rows are the reflection's alone).
fn closure_key(p: &Passage, origin: usize, reflector: Option<usize>, restart: Option<usize>) -> Result<Option<Closure>> {
    let (found, reflections, restored) = closure_rows(p, origin, reflector, restart);
    if (reflector.is_some() && reflections == 0) || (restart.is_some() && !restored) {
        return Ok(None);
    }
    let mut slots: Vec<usize> = found.iter().flat_map(|(n, _)| n.iter().map(|&(q, _)| q)).collect();
    slots.sort_unstable();
    slots.dedup();
    let mut classes: Vec<usize> = found.iter().map(|&(_, c)| c).collect();
    classes.sort_unstable();
    classes.dedup();
    let (s, columns) = (slots.len(), slots.len() + classes.len());
    let dense: Vec<Vec<i128>> = found
        .iter()
        .map(|(n, c)| {
            let mut row = vec![0i128; columns];
            for &(q, v) in n {
                row[slots.binary_search(&q).expect("a met slot")] = v as i128;
            }
            row[s + classes.binary_search(c).expect("an arriving class")] = -1;
            row
        })
        .collect();
    let mut unique = dense.clone();
    unique.sort_unstable();
    unique.dedup();
    let mut out = Closure { origin, reflector, reflections, restart, rows: found.len(), unique: unique.len(), columns, rank: 0, minor_bits: 0, candidates: Vec::new(), torsion: Vec::new(), key: None };
    if found.is_empty() {
        return Ok(Some(out));
    }
    let (rank, minor, kernel) = rational_rank(&unique);
    out.rank = rank;
    out.minor_bits = minor.bits();
    out.candidates = readable_primes(&minor.abs());
    // Per torsion prime, the kernel vector whose ψ takes the most values.
    let mut keys: Vec<(i128, Vec<i128>)> = Vec::new();
    for &q in &out.candidates {
        let e = echelon_mod(&unique, q as u64, rank);
        if e.pivots.len() == rank {
            continue;
        }
        out.torsion.push((q, rank - e.pivots.len()));
        let (pivots, m) = (e.pivots, e.rows);
        let best = (0..columns)
            .filter(|c| pivots.binary_search(c).is_err())
            .map(|f| {
                let mut x = vec![0i128; columns];
                x[f] = 1;
                for (row, &c) in m.iter().zip(&pivots) {
                    x[c] = (-(row[f] as i128)).rem_euclid(q);
                }
                x
            })
            .max_by_key(|x| {
                let mut psi = x[s..].to_vec();
                psi.sort_unstable();
                psi.dedup();
                psi.len()
            });
        if let Some(x) = best.filter(|x| x[s..].iter().any(|&v| v != x[s])) {
            keys.push((q, x));
        }
    }
    let fails = |x: &[i128], n: i128| dense.iter().filter(|row| row.iter().zip(x).map(|(&a, &b)| a * b).sum::<i128>().rem_euclid(n) != 0).count();
    let key_of = |x: &[i128], n: i128, exact: bool| Key {
        modulus: n,
        theta: slots.iter().zip(x).map(|(&q, &t)| (q, t)).collect(),
        psi: classes.iter().zip(&x[s..]).map(|(&c, &v)| (c, v)).collect(),
        failures: fails(x, n),
        exact,
    };
    // The rational kernel's vectors whose ψ is injective: the least readable span.
    let readable = BigInt::from(1i128 << (FACE_BITS + 3));
    let exact = kernel
        .iter()
        .filter_map(|k| {
            let divisor = k.iter().fold(BigInt::zero(), |g, x| gcd(&g, x));
            if divisor.is_zero() {
                return None;
            }
            let k: Vec<BigInt> = k.iter().map(|x| x / &divisor).collect();
            let mut psi = k[s..].to_vec();
            psi.sort_unstable();
            psi.dedup();
            let span = psi.last()? - psi.first()? + 1;
            (psi.len() == classes.len() && span < readable).then(|| {
                let n = i128::try_from(&span).expect("a readable span");
                let bn = BigInt::from(n);
                let x: Vec<i128> = k.iter().map(|v| i128::try_from(((v % &bn) + &bn) % &bn).expect("a residue below its modulus")).collect();
                (n, x)
            })
        })
        .min_by_key(|(n, _)| *n);
    if let Some((n, x)) = exact {
        out.key = Some(key_of(&x, n, true));
    }
    // The subsets of the torsion primes in descending product; the first injective joined key.
    let mut subsets: Vec<(i128, Vec<usize>)> = (1u32..1 << keys.len().min(16))
        .map(|bitset| {
            let members: Vec<usize> = (0..keys.len()).filter(|&j| bitset >> j & 1 == 1).collect();
            (members.iter().map(|&j| keys[j].0).product(), members)
        })
        .collect();
    subsets.sort_by(|x, y| y.cmp(x));
    for (n, members) in subsets {
        // CRT: x ≡ x_j (mod q_j) for each member.
        let mut joined = vec![0i128; columns];
        let mut modulus = 1i128;
        for &j in &members {
            let (q, x) = (&keys[j].0, &keys[j].1);
            let step = inv_mod((modulus % q) as u64, *q as u64) as i128;
            for (y, &v) in joined.iter_mut().zip(x) {
                // y + modulus · ((v − y) · modulus⁻¹ mod q)
                *y += modulus * ((v - *y).rem_euclid(*q) * step % q);
            }
            modulus *= q;
        }
        let mut psi = joined[s..].to_vec();
        psi.sort_unstable();
        psi.dedup();
        if psi.len() == classes.len() {
            if out.key.is_none() {
                out.key = Some(key_of(&joined, n, false));
            }
            break;
        }
    }
    Ok(Some(out))
}

/// [agent-inferred, October 25] **The unit turn `ω = e^(2πi/n)` on `2^(−62)`**, a face of its
/// constraint: `cos(2π/n)` is the second root below one of the Chebyshev polynomial `U_(n−1)`
/// (`U_(n−1)(cos θ) = sin(nθ)/sin θ`, simple roots at `cos(kπ/n)`), located exactly by sign on
/// `x = X/2^62` (`W_k = 2^(62k) U_k(x)`, `W_(k+1) = 2X W_k − 2^124 W_(k−1)`): scanned down from one
/// in steps of `2^(−2·bits(n)−2)`, below the roots' least spacing near one (`> 4/n²`), then halved to
/// adjacent grains; `sin = √(2^124 − cos²)`, rounded down.
fn unit_turn(n: i128) -> (i128, i128) {
    const D: u32 = 62;
    let one = 1i128 << D;
    match n {
        1 => return (one, 0),
        2 => return (-one, 0),
        _ => {}
    }
    let w = |x: i128| -> BigInt {
        let (x2, d2) = (BigInt::from(x) << 1u32, BigInt::from(1u8) << (2 * D));
        let (mut prev, mut cur) = (BigInt::from(1u8), x2.clone());
        for _ in 1..n - 1 {
            let next = &x2 * &cur - &d2 * &prev;
            prev = std::mem::replace(&mut cur, next);
        }
        cur
    };
    let sign = |x: i128| w(x).sign();
    let step = 1i128 << (D - 2 * bits(n as u128) - 2);
    let (mut x, mut last, mut crossed) = (one, sign(one), 0);
    let c = loop {
        let lower = x - step;
        let s = sign(lower);
        if s == num_bigint::Sign::NoSign {
            crossed += 1;
            if crossed == 2 {
                break lower;
            }
            last = if last == num_bigint::Sign::Plus { num_bigint::Sign::Minus } else { num_bigint::Sign::Plus };
        } else if s != last {
            crossed += 1;
            if crossed == 2 {
                let (mut lo, mut hi) = (lower, x);
                while hi - lo > 1 {
                    let mid = lo + (hi - lo) / 2;
                    if sign(mid) == s || sign(mid) == num_bigint::Sign::NoSign {
                        lo = mid;
                    } else {
                        hi = mid;
                    }
                }
                break lo;
            }
            last = s;
        }
        x = lower;
    };
    let s = (BigInt::from(one) * one - BigInt::from(c) * c).sqrt();
    (c, i128::try_from(s).expect("a sine on its grain"))
}

/// [agent-inferred, October 25] **The closure's table of pair moves**: each pair `q` turns the ring
/// by `ω^(θ_q)` at the placement mode's own memory, `λ_q = ρ_q ω^(θ_q)` with `ρ_q = |λ̄_q|` the
/// modulus of the mode's mean move at the pair ([`pair_table`]), each part rounded toward zero (so
/// `|λ_q| ≤ ρ_q < 1`) and no `β`; the pairs ending at the origin restart the ring (zero move). The
/// turns are `ω^k` by Gaussian products on `2^(−62)`. A pair ending at the reflector reflects the
/// ring, `λ = 0` and `β_q = ρ_q ω^(θ_q)`: `h ↦ β h̄`, the dyad of the newline closure record's §8
/// [agent-inferred, October 25].
fn closure_table(p: &Passage, mode: &Table, origin: usize, reflector: Option<usize>, n: i128, theta: &[(usize, i128)]) -> Result<Table> {
    let (c, s) = unit_turn(n);
    let mut powers = vec![(1i128 << 62, 0i128)];
    for _ in 1..n {
        let (a, b) = *powers.last().expect("a power");
        let re = BigInt::from(a) * c - BigInt::from(b) * s;
        let im = BigInt::from(a) * s + BigInt::from(b) * c;
        let half = BigInt::from(1u8) << 61u32;
        powers.push((i128::try_from((re + &half) >> 62u32)?, i128::try_from((im + &half) >> 62u32)?));
    }
    let mut table = Table::with_capacity(p.pairs.len());
    for (q, &(_, cur)) in p.pairs.iter().enumerate() {
        if cur == origin {
            table.push([0; 4]);
            continue;
        }
        let m = mode[q];
        let rho = i128::try_from((BigInt::from(m[0]) * m[0] + BigInt::from(m[1]) * m[1]).sqrt())?;
        let turn = theta.binary_search_by_key(&q, |&(slot, _)| slot).map_or(0, |j| theta[j].1.rem_euclid(n));
        let (re, im) = powers[turn as usize];
        let (re, im) = (rho * re / (1i128 << 62), rho * im / (1i128 << 62));
        let moved = if Some(cur) == reflector { [0, 0, re, im] } else { [re, im, 0, 0] }.map(|v| v as i64);
        if !passive(moved) {
            return Err("a closure move that boosts".into());
        }
        table.push(moved);
    }
    Ok(table)
}

/// [agent-inferred, October 25] **The pair moves founded by exact loop closure.** Every class that
/// arrives over the passage is tried as the origin, with no reflector, with each other class as
/// the reflector, and with each reflector and each third class as the hand's restart
/// ([`closure_rows`], [`closure_key`], in parallel); each that the reflector and the restart meet
/// prints a `RING_CLOSURE` line (its rows, unique rows, columns, rank over the rationals, its
/// certified minor's bits and readable primes, the primes where the rank falls, and its key). Of
/// those with a key, the one whose loops cover the most marked cells is kept (a key over fewer
/// loops separates fewer arrivals, and an origin seen before only a few marked cells closes them on
/// a small modulus trivially), then the better key ([`Key::order`]: exact before torsion, then
/// its modulus), then no reflector before one and no restart before one (each enters only where it
/// closes more), then the fewer reflections met (of two reflectors that close alike, a gauge, the
/// one that reverses fewer loops), then the classes. Its key prints as `RING_KEY` (the reflector,
/// the restart, the modulus, each class's residue, and the turns of the pairs it moves) and its
/// table ([`closure_table`]) is the ring's. Returns the origin, the modulus, the table and the
/// restart, or `None` when no origin's loops close on a key that separates the arriving classes.
/// The torsion key across origins once took the smaller modulus; it now takes the larger, as each
/// closure's own key does.
///
/// [agent-inferred, October 25] **A restart refines a reflection that closes.** A restart only
/// restores a hand a reflection reversed, so it is sought only beside a reflector whose closure
/// already keys: the origins and reflectors are solved first (15 + 210 closures on the arithmetic
/// block), then each keyed reflector with each third class as its restart. A restart that would
/// key a reflection which closes on nothing is not sought. All 2,955 closures at once on the sums'
/// and differences' units together ran at 1.4 a second and were stopped at 210
/// (`ring/found32sd.txt`), and solving the origins one row count at a time saved nothing, as nearly
/// every origin precedes every mark (`ring/found33sd.txt`).
#[allow(clippy::type_complexity)]
fn found_closure(p: &Passage, mode: &Table) -> Result<Option<(usize, i128, Table, Option<usize>)>> {
    let mut origins: Vec<usize> = p.streams.iter().flat_map(|s| s.classes.iter().copied()).collect();
    origins.sort_unstable();
    origins.dedup();
    let started = std::time::Instant::now();
    let show = |c: usize| if (33..127).contains(&c) { (c as u8 as char).to_string() } else { format!("#{c}") };
    let others = |not: &[usize]| origins.iter().copied().filter(|c| !not.contains(c)).collect::<Vec<_>>();
    let reflected = |r: Option<usize>| r.map_or("none".to_string(), show);
    let (mut closures, mut tried_count): (Vec<Closure>, usize) = (Vec::new(), 0);
    let mut tried: Vec<(usize, Option<usize>, Option<usize>)> = origins.iter().flat_map(|&o| std::iter::once((o, None, None)).chain(others(&[o]).into_iter().map(move |r| (o, Some(r), None)))).collect();
    while !tried.is_empty() {
        tried_count += tried.len();
        // Each line as its closure completes (a pivot past 64 bits by its width), one for each
        // tried closure, so the run's progress is read from its lines.
        let solved: Vec<Closure> = tried
            .par_iter()
            .map(|&(o, r, e)| {
                let c = closure_key(p, o, r, e).map_err(|e| e.to_string())?;
                match &c {
                    None => println!("RING_UNMET origin={} reflector={} restart={} elapsed_ms={}", show(o), reflected(r), reflected(e), started.elapsed().as_millis()),
                    Some(c) => println!(
                        "RING_CLOSURE origin={} reflector={} restart={} reflections={} rows={} unique={} columns={} rank={} minor_bits={} candidates={} torsion={} key_modulus={} exact={} elapsed_ms={}",
                        show(c.origin),
                        reflected(c.reflector),
                        reflected(c.restart),
                        c.reflections,
                        c.rows,
                        c.unique,
                        c.columns,
                        c.rank,
                        c.minor_bits,
                        c.candidates.iter().map(|d| d.to_string()).collect::<Vec<_>>().join(","),
                        c.torsion.iter().map(|(q, t)| format!("{q}:{t}")).collect::<Vec<_>>().join(","),
                        c.key.as_ref().map_or("none".to_string(), |k| k.modulus.to_string()),
                        c.key.as_ref().is_some_and(|k| k.exact),
                        started.elapsed().as_millis()
                    ),
                }
                Ok(c)
            })
            .collect::<std::result::Result<Vec<Option<Closure>>, String>>()?
            .into_iter()
            .flatten()
            .collect();
        // The restarts beside each reflection that keys, once.
        tried = solved
            .iter()
            .filter(|c| c.key.is_some() && c.restart.is_none())
            .filter_map(|c| c.reflector.map(|r| (c.origin, r)))
            .flat_map(|(o, r)| others(&[o, r]).into_iter().map(move |e| (o, Some(r), Some(e))))
            .collect();
        closures.extend(solved);
    }
    println!("RING_CLOSURES origins={} tried={tried_count} met={} keyed={} elapsed_ms={}", origins.len(), closures.len(), closures.iter().filter(|c| c.key.is_some()).count(), started.elapsed().as_millis());
    let Some(kept) = closures.iter().filter(|c| c.key.is_some()).min_by_key(|c| (std::cmp::Reverse(c.rows), c.key.as_ref().map(Key::order), c.reflector.is_some(), c.restart.is_some(), c.reflections, c.origin, c.reflector, c.restart)) else {
        return Ok(None);
    };
    let key = kept.key.as_ref().expect("a kept key");
    let n = key.modulus;
    let pairs: Vec<String> = key.theta.iter().filter(|(_, t)| t.rem_euclid(n) != 0).map(|&(q, t)| format!("{}{}:{}", show(p.pairs[q].0), show(p.pairs[q].1), t.rem_euclid(n))).collect();
    println!(
        "RING_KEY origin={} reflector={} restart={} modulus={n} exact={} failures={} residues={} turns={}",
        show(kept.origin),
        reflected(kept.reflector),
        reflected(kept.restart),
        key.exact,
        key.failures,
        key.psi.iter().map(|&(c, v)| format!("{}:{v}", show(c))).collect::<Vec<_>>().join(","),
        pairs.join(",")
    );
    Ok(Some((kept.origin, n, closure_table(p, mode, kept.origin, kept.reflector, n, &key.theta)?, kept.restart)))
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
/// RANKS STARTS OUT`: found `RANKS` ring forms riding mode `MODE` of level `LEVEL`, read at the
/// cells `MARKS` marks (one byte per byte of `TEXT`, nonzero where the reading looks). Each rank is
/// founded from the unit pool and from each of the classes' coupling's `STARTS` leading modes
/// ([`coupling_starts`]), each with the unit gate, in rounds of `a`, `b`, `g` to the alternation's
/// own fixed point and a closing `a` ([`round_pays`]: a round is followed by another while it moves
/// the form by more than the marked cells' own error, half a nat a free parameter; no round count
/// is chosen), and keeps the start whose
/// form gives the larger exact share of the founded ranks' channels
/// (found-tower-situated's law: search from more than one start, keep the larger). Each kept form
/// is written to `OUT` (create-new) as it is founded: a `FORM` line (`c = (aᵀŝ)(bᵀx̂)`, read by
/// `read-tower-situated`) and a `RING` line (its gate, mode and shifts). Each step prints its
/// circular share on released copies; each start and each rank the exact share of the ranks'
/// channels in thousandths (twice the nats a marked cell saves).
///
/// [agent-inferred, October 25] With `pair-moves`, the ring's move is founded first, keyed by the
/// pair of the seam and the arriving class ([`RingFace::move_at`]), by exact loop closure
/// ([`found_closure`]): the origin, the modulus and every pair's turn are the closure's own, exact,
/// so they add no free parameter; the ring is then founded under that table from every start and
/// from the origin start (the push at the origin's arrival alone). With `pair-moves-at KEY_MARKS
/// KEY_MARKS_SHA` the closure is solved at the cells `KEY_MARKS` marks and the ring founded at those
/// `MARKS` marks: a key closes on the classes that arrive where it is located (a result's units),
/// and what its torsion holds beyond them is read elsewhere (modulo `110` the whole result, read
/// where its first digit arrives), where no key closes. With `pair-moves-held TABLE
/// TABLE_SHA` the table is read instead (`prev cur Re λ Im λ Re β Im β` a line; a ceiling reading,
/// never a founding). The table is written as a `MOVES` line after its rank (one rank: the moves
/// are the face's).
///
/// The moves were first founded by local steps from the mode's moves and from rest (along the
/// leading canonical direction of their tangent columns, then along the share's covector with the
/// step's length by octaves): none left its start, since a move's effect on the share reaches the
/// cells only through every recurrence of its pair within the ring's memory (`ρ` near one), a far
/// key no local step sees (`ring/found18u.txt`, `ring/found18v.txt`). The closure reads the key
/// whole.
pub(super) fn found_tower_ring(args: &[String]) -> Result<()> {
    let held = args.len() == 17 && args[14] == "pair-moves-held";
    let keyed_at = args.len() == 17 && args[14] == "pair-moves-at";
    let moves = held || keyed_at || (args.len() == 15 && args[14] == "pair-moves");
    if args.len() != 14 && !moves {
        return Err("found-tower-ring STATE STATE_SHA TEXT TEXT_SHA MARKS MARKS_SHA STREAMS SECTION LEVEL MODE RANKS STARTS OUT [pair-moves | pair-moves-at KEY_MARKS KEY_MARKS_SHA | pair-moves-held TABLE TABLE_SHA]".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let marks = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let (streams, section) = (positive(&args[7])?, positive(&args[8])?);
    let (level, mode) = (count(&args[9])?, count(&args[10])?);
    let (ranks, starts) = (positive(&args[11])?, count(&args[12])?);
    if level >= tower.declaration.levels || mode >= tower.declaration.modes {
        return Err("LEVEL or MODE names no level or mode of the tower".into());
    }
    if marks.len() != text.len() || text.is_empty() {
        return Err("MARKS holds one byte per byte of TEXT".into());
    }
    let key_marks = if keyed_at { Some(pinned_read(&args[15], &args[16], READ_BUDGET as usize)?) } else { None };
    if key_marks.as_ref().is_some_and(|k| k.len() != text.len()) {
        return Err("KEY_MARKS holds one byte per byte of TEXT".into());
    }
    if std::path::Path::new(&args[13]).exists() {
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
        pairs: Vec::new(),
        restart: None,
    };
    let (sc, coupling, streams) = survey(&p)?;
    p.present = (0..coupling.n.len()).filter(|&u| coupling.n[u] > 0).collect();
    p.streams = streams;
    if moves && ranks != 1 {
        return Err("pair moves are the face's: found them with one rank".into());
    }
    let mut origin_start: Option<usize> = None;
    let mut key_modulus: Option<i128> = None;
    let opening_table: Option<Table> = if moves {
        let (mut table, varying) = pair_table(&mut p)?;
        if !held {
            // The closure reads the cells the key is located at; the founding, the cells it is read at.
            let own = key_marks.map(|k| std::mem::replace(&mut p.marks, k));
            let solved = found_closure(&p, &table);
            if let Some(own) = own {
                p.marks = own;
            }
            let (origin, n, closed, restart) = solved?.ok_or("no origin's loops close on a key that separates the arriving classes")?;
            origin_start = Some(origin);
            key_modulus = Some(n);
            table = closed;
            p.restart = restart;
        } else {
            // A held table (`prev cur Re λ Im λ Re β Im β` a line): its pairs the passage meets take its
            // moves, every other pair rests; nothing in it is founded.
            let text = String::from_utf8(pinned_read(&args[15], &args[16], READ_BUDGET as usize)?)?;
            table = vec![[0; 4]; p.pairs.len()];
            let mut met = 0usize;
            for line in text.lines().filter(|l| !l.is_empty()) {
                let v: Vec<i64> = line.split(' ').map(|x| x.parse::<i64>()).collect::<std::result::Result<_, _>>()?;
                if v.len() != 6 || v[0] < 0 || v[1] < 0 || !passive([v[2], v[3], v[4], v[5]]) {
                    return Err("a held move is prev cur and four integers, passive".into());
                }
                if let Ok(q) = p.pairs.binary_search(&(v[0] as usize, v[1] as usize)) {
                    table[q] = [v[2], v[3], v[4], v[5]];
                    met += 1;
                }
            }
            println!("RING_HELD_TABLE moves={} met={met}", text.lines().filter(|l| !l.is_empty()).count());
        }
        println!("RING_PAIRS pairs={} varying={varying} rho_on_2^-30={} elapsed_ms={}", p.pairs.len(), scale_with(&sc, Some(&table)).rho, started.elapsed().as_millis());
        Some(table)
    } else {
        None
    };
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
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(&args[13])?;
    std::io::Write::write_all(&mut file, format!("SITUATED level={level} dims={} width={} state_sha256={} text_sha256={} marks_sha256={} mode={mode}\n", p.dims, p.width, args[2], args[4], args[6]).as_bytes())?;
    let mut founded: Vec<Ring> = Vec::new();
    let marked = p.marks.iter().filter(|&&m| m != 0).count();
    let free = (2 * p.dims - 1) + (2 * p.present.len() - 1) + p.dims;
    for rank in 0..ranks {
        let unit = unit_ring(&p);
        // [agent-inferred, October 25] With the closure's moves, one start more: the push at the
        // origin's arrival alone, the ring the closure reads.
        let origin_pool: Option<[Vec<i64>; 2]> = match origin_start.and_then(|o| p.present.iter().position(|&u| u == o)) {
            Some(at) => {
                let re: Vec<i64> = (0..p.present.len()).map(|u| ((u == at) as i64) << 15).collect();
                Some(pool_factor(&p, [&re, &vec![0; p.present.len()]])?)
            }
            None => None,
        };
        let rings: Vec<(String, Ring)> = std::iter::once(("unit".to_string(), unit.clone()))
            .chain(pools.iter().enumerate().map(|(j, b)| (format!("coupling_mode_{}", j + 1), Ring { b: b.clone(), ..unit.clone() })))
            .chain(origin_pool.into_iter().map(|b| ("origin".to_string(), Ring { b, ..unit.clone() })))
            .collect();
        let tables: Vec<(&str, Option<Table>)> = match &opening_table {
            Some(t) => vec![(if held { "held" } else { "closure" }, Some(t.clone()))],
            None => vec![("", None)],
        };
        let candidates: Vec<(String, Ring, Option<Table>)> = rings
            .iter()
            .flat_map(|(name, ring)| tables.iter().map(move |(t, table)| (if t.is_empty() { name.clone() } else { format!("{name}/{t}") }, ring.clone(), table.clone())))
            .collect();
        let mut kept: Option<(BigInt, BigInt, Ring, PassMoments, Option<Table>)> = None;
        for (name, mut ring, table) in candidates {
            let (mut step, mut last): (usize, Option<(BigInt, BigInt)>) = (0, None);
            let found = |factor: Factor, ring: &mut Ring, step: &mut usize, table: Option<&Table>| -> Result<(BigInt, BigInt)> {
                let (theta, s, ms) = found_step(&p, &sc, table, &founded, ring, factor)?;
                match factor {
                    Factor::A => ring.a = [theta[..p.dims].to_vec(), theta[p.dims..].to_vec()],
                    Factor::B => ring.b = pool_factor(&p, [&theta[..p.present.len()], &theta[p.present.len()..]])?,
                    Factor::G => ring.g = theta,
                }
                println!("RING_STEP rank={rank} start={name} step={step} factor={factor:?} circular_permille={} pass_ms={ms} elapsed_ms={}", permille(&s.0, &s.1), started.elapsed().as_millis());
                *step += 1;
                Ok(s)
            };
            for round in 0usize.. {
                let mut share = (BigInt::zero(), BigInt::from(1));
                for factor in [Factor::A, Factor::B, Factor::G] {
                    share = found(factor, &mut ring, &mut step, table.as_ref())?;
                }
                let (pays, saved) = round_pays(marked, free, last.as_ref(), &share);
                println!("RING_ROUND rank={rank} start={name} round={round} circular_permille={} saved_millinats={saved} another={pays} elapsed_ms={}", permille(&share.0, &share.1), started.elapsed().as_millis());
                last = Some(share);
                if !pays {
                    break;
                }
            }
            // The closing `a`: the form the push reads, once more after the last round.
            found(Factor::A, &mut ring, &mut step, table.as_ref())?;
            let (release, push_shift, read_shift) = shifts(&p, &scale_with(&sc, table.as_ref()), &ring, None)?;
            ring.release = release;
            ring.push_shift = push_shift;
            ring.read_shift = read_shift;
            let with: Vec<Ring> = founded.iter().cloned().chain([ring.clone()]).collect();
            let m = pass(&p, table.as_ref(), &with, None)?;
            let fit = rank_fit(&m)?;
            println!("RING_START rank={rank} start={name} exact_share_permille={} elapsed_ms={}", permille(&fit.share, &fit.share_den), started.elapsed().as_millis());
            if kept.as_ref().is_none_or(|(n, d, _, _, _)| &fit.share * d > n * &fit.share_den) {
                kept = Some((fit.share, fit.share_den, ring, m, table));
            }
        }
        let (share, share_den, ring, m, table) = kept.ok_or("no start was founded")?;
        let (push_shift, read_shift) = (ring.push_shift, ring.read_shift);
        // The form's release for read-tower-situated's instant reading: `(aᵀŝ)(bᵀx̂)` brought below 2^32.
        let (alpha, beta, _) = bounds(&p, &sc, &ring);
        let form_shift = (bits(alpha) + bits(beta)).saturating_sub(32);
        std::io::Write::write_all(&mut file, format!("FORM {rank} shift={form_shift} faces=re,im a={} ai={} b={} bi={}\n", join(&ring.a[0]), join(&ring.a[1]), join(&ring.b[0]), join(&ring.b[1])).as_bytes())?;
        std::io::Write::write_all(&mut file, format!("RING {rank} mode={mode} release={} push_shift={push_shift} read_shift={read_shift} g={}\n", join(&ring.release.map(i64::from)), join(&ring.g)).as_bytes())?;
        if let Some(t) = &table {
            let entries: Vec<String> = p.pairs.iter().zip(t).map(|(&(prev, cur), m)| format!("{prev}:{cur}:{}:{}:{}:{}", m[0], m[1], m[2], m[3])).collect();
            let key = key_modulus.map_or(String::new(), |n| format!(" key_modulus={n}")) + &p.restart.map_or(String::new(), |e| format!(" restart={e}"));
            std::io::Write::write_all(&mut file, format!("MOVES {rank} n={}{key} moves={}\n", entries.len(), entries.join(",")).as_bytes())?;
        }
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
    let written = std::fs::read(&args[13])?;
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

/// An arriving class's row and the harmonic its channels read ([`found_ring_readout`]).
type BlockId = (usize, usize);

/// A ring's pair moves (`MOVES r n=N [key_modulus=n] [restart=e] moves=prev:cur:Re λ:Im λ:Re β:Im β,…`).
type PairMoves = Vec<(usize, usize, [i64; 4])>;

/// The ranks a founding wrote ([`found_tower_ring`]'s `SITUATED`, `FORM` and `RING` lines, and a
/// `MOVES` line after a rank founded with its pair moves): the tower they were founded on (its
/// state's SHA-256), the level and mode they ride, each rank, the pair moves and the modulus of
/// the key that closed them, when a closure founded them.
#[allow(clippy::type_complexity)]
fn read_forms(text: &str, dims: usize, width: usize) -> Result<(String, usize, usize, Vec<RingRank>, PairMoves, Option<usize>, Option<usize>)> {
    let mut lines: Vec<&str> = text.lines().collect();
    let mut pair_moves: PairMoves = Vec::new();
    let (mut key_modulus, mut restart): (Option<usize>, Option<usize>) = (None, None);
    if let Some(at) = lines.iter().position(|l| l.starts_with("MOVES ")) {
        let line = lines.remove(at);
        if at != 3 || lines.iter().any(|l| l.starts_with("MOVES ")) || !line.starts_with("MOVES 0 ") {
            return Err("a ring's pair moves follow its one rank".into());
        }
        let n: usize = field(line, "n")?.parse()?;
        if line.split(' ').any(|w| w.starts_with("key_modulus=")) {
            key_modulus = Some(field(line, "key_modulus")?.parse()?);
        }
        if line.split(' ').any(|w| w.starts_with("restart=")) {
            restart = Some(field(line, "restart")?.parse()?);
        }
        for entry in field(line, "moves")?.split(',') {
            let v: Vec<i64> = entry.split(':').map(|x| x.parse::<i64>()).collect::<std::result::Result<_, _>>()?;
            if v.len() != 6 || v[0] < 0 || v[1] < 0 {
                return Err("a pair move is prev:cur and four integers".into());
            }
            pair_moves.push((v[0] as usize, v[1] as usize, [v[2], v[3], v[4], v[5]]));
        }
        if pair_moves.len() != n {
            return Err("a MOVES line's count is not its moves'".into());
        }
    }
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
    Ok((field(head, "state_sha256")?.to_string(), level, mode, ranks, pair_moves, key_modulus, restart))
}

/// [agent-inferred, October 25] `join-tower-ring STATE STATE_SHA FORMS FORMS_SHA [FORMS FORMS_SHA
/// …] OUT`: join the ring ranks each `FORMS` founded on the tower `STATE` (`found-tower-ring`'s
/// output, refused when founded on another tower or on another level or mode than the first) as
/// the tower's resident ring face ([`holonics::hnn::tower::RingFace`]), its readout at zero, and
/// write the learner create-new to `OUT`. Each rank keeps the pair moves its own closure founded,
/// so rings closed on different keys ride side by side on the one mode. Each rank's face is its
/// read as a ratio to its own power, so nothing is fitted to a passage; the joined tower codes
/// every passage as the tower alone until its readout learns (`a_ring_faced_tower_opens_on_itself`).
/// A ring whose moves a closure of modulus `n` founded is read through `⌊n/2⌋` harmonics of its
/// turn ([`RingFace::with_harmonics`]): the key's characters, which place its residues apart; the
/// face reads every rank through the most any of its keys asks, or through `harmonics=H`, the
/// characters a founded turn resolves when its spread blurs the higher ones (declared by the run,
/// with its reading). With `readout=LEARNER,SHA` the readout of a ring-faced learner joined on the
/// same tower, whose ranks are the leading ranks here (the same forms, moves and harmonics), stands
/// in their channels: a ring joined beside one whose readout is already founded
/// (`found-ring-readout … held=R`).
pub(super) fn join_tower_ring(args: &[String]) -> Result<()> {
    let usage = "join-tower-ring STATE STATE_SHA FORMS FORMS_SHA [FORMS FORMS_SHA …] OUT [harmonics=H] [readout=LEARNER,SHA]";
    let at = args.iter().position(|a| a.starts_with("harmonics=") || a.starts_with("readout=")).unwrap_or(args.len());
    let (args, options) = args.split_at(at);
    if args.len() < 6 || args.len() % 2 != 0 {
        return Err(usage.into());
    }
    let (mut harmonics_set, mut readout_from): (Option<usize>, Option<(&str, &str)>) = (None, None);
    for o in options {
        if let Some(h) = o.strip_prefix("harmonics=") {
            harmonics_set = Some(h.parse()?);
        } else if let Some(r) = o.strip_prefix("readout=") {
            readout_from = Some(r.split_once(',').ok_or(usage)?);
        } else {
            return Err(usage.into());
        }
    }
    let started = std::time::Instant::now();
    let out_path = &args[args.len() - 1];
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    if std::path::Path::new(out_path).exists() {
        return Err("OUT exists: the joined learner is written create-new".into());
    }
    let d = learner.tower.declaration.clone();
    let mut placement: Option<(usize, usize)> = None;
    let (mut ranks, mut tables, mut keys, mut restarts) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for pair in args[3..args.len() - 1].chunks(2) {
        let forms = pinned_read(&pair[0], &pair[1], READ_BUDGET as usize)?;
        let (founded_on, level, mode, founded, pair_moves, key_modulus, restart) = read_forms(std::str::from_utf8(&forms)?, 2 * d.modes, d.width)?;
        if founded_on != args[2] {
            return Err("the forms were founded on another tower: the moves they ride and the encoding their pools read are this one's only".into());
        }
        if placement.is_some_and(|p| p != (level, mode)) {
            return Err("the rings ride one level's mode: forms founded on another placement".into());
        }
        placement = Some((level, mode));
        tables.extend(std::iter::repeat_n(pair_moves, founded.len()));
        restarts.extend(std::iter::repeat_n(restart, founded.len()));
        ranks.extend(founded);
        keys.push(key_modulus);
    }
    let (level, mode) = placement.ok_or("no forms")?;
    let n = ranks.len();
    let opening: Vec<i32> = (0..d.alphabet).flat_map(|u| learner.tower.encoding(u).to_vec()).collect();
    let mut out = learner;
    let moves: Vec<usize> = tables.iter().map(Vec::len).collect();
    let harmonics = harmonics_set.unwrap_or_else(|| keys.iter().map(|k| k.map_or(1, |n| (n / 2).max(1))).max().unwrap_or(1));
    let face = RingFace::new(&d, level, mode, ranks, opening, tables).and_then(|f| f.with_harmonics(harmonics)).and_then(|f| f.with_restarts(restarts)).map_err(|e| e.to_string())?;
    out.join_ring_face(face).map_err(|e| e.to_string())?;
    let mut carried = 0usize;
    if let Some((path, sha)) = readout_from {
        let source = TowerLearner::from_text(std::str::from_utf8(&pinned_read(path, sha, STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
        let (st, nt) = (&source.tower, &out.tower);
        let refused = "readout=: a learner whose ring face is this one's leading ranks, joined on the same tower";
        let (sf, nf) = (st.ring_face().ok_or(refused)?, nt.ring_face().ok_or(refused)?);
        let (sr, nr) = (st.ring_family().ok_or(refused)?, nt.ring_family().ok_or(refused)?);
        let (sfac, nfac) = (st.ring_factor_family().ok_or(refused)?, nt.ring_factor_family().ok_or(refused)?);
        let r0 = sf.ranks();
        let same = st.declaration == nt.declaration
            && sr.start == nr.start
            && st.theta[..sr.start] == nt.theta[..nr.start]
            && r0 < nf.ranks()
            && sf.placement() == nf.placement()
            && sf.harmonics() == nf.harmonics()
            && sf.pair_moves() == &nf.pair_moves()[..r0]
            && sf.restarts() == &nf.restarts()[..r0]
            && st.theta[sfac.clone()] == nt.theta[nfac.start..nfac.start + sfac.len()];
        if !same {
            return Err(refused.into());
        }
        let (ks, kn) = (sf.channels(d.width), nf.channels(d.width));
        let (cs, cn) = (ks / (d.width + 1), kn / (d.width + 1));
        let mut readout = vec![0i32; d.alphabet * kn];
        for u in 0..d.alphabet {
            for x in 0..=d.width {
                let from = sr.start + u * ks + x * cs;
                readout[u * kn + x * cn..u * kn + x * cn + cs].copy_from_slice(&st.theta[from..from + cs]);
            }
        }
        carried = r0;
        out.tower.open_ring_readout(&readout).map_err(|e| e.to_string())?;
    }
    let written = out.to_text();
    std::io::Write::write_all(&mut std::fs::OpenOptions::new().write(true).create_new(true).open(out_path)?, written.as_bytes())?;
    let join = |v: Vec<String>| v.join(",");
    println!(
        "RING_JOIN level={level} mode={mode} ranks={n} pair_moves={} key_moduli={} harmonics={harmonics} readout_carried_ranks={carried} material={} sha256={} elapsed_ms={}",
        join(moves.iter().map(usize::to_string).collect()),
        join(keys.iter().map(|k| k.map_or("none".to_string(), |n| n.to_string())).collect()),
        out.tower.theta.len(),
        sha256(written.as_bytes())?,
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [agent-inferred, October 25] `read-tower-at STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA
/// [split]`: the tower's own guess at the cells `CELLS` names (ascending cell indices,
/// whitespace-separated; cell `i` has heard `TEXT[..=i]` and codes `TEXT[i + 1]`), `TEXT` read as
/// one passage from rest. Each named cell prints `AT i next top code`: the class that arrives, the
/// class the face gives the largest mass (the smaller class on a tie) and the code of the arriving
/// class on `2^(−20)` bits; with a ring face joined, also `FORMS i next ρ…`, the ring's face as the
/// readout reads it (the probe's situated format). With `split` (a ring-faced tower), the guess is
/// split into the ring's part, `W φ` with `φ` the ring's pair read with the top face
/// ([`RingFace::pair_read`]), and the rest, the same tower with its ring's readout at zero read
/// again: each named cell prints `SPLIT i next top ring_top rest_top ring_rank rest_rank top_rank
/// ring_margin`, the ranks the arriving class's place below the classes each part (and the whole
/// face) puts above it, and the margin the ring's part gives the arriving class over the largest
/// other, on `2^(−16)` of a bit. A reading beside the code: the tower is not moved.
pub(super) fn read_tower_at(args: &[String]) -> Result<()> {
    let split = args.len() == 8 && args[7] == "split";
    if args.len() != 7 && !split {
        return Err("read-tower-at STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA [split]".into());
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
    let (a, w) = (tower.declaration.alphabet, tower.declaration.width);
    let readout: Option<(usize, &[i32])> = match (split, tower.ring_face(), tower.ring_family()) {
        (false, _, _) => None,
        (true, Some(face), Some(family)) => {
            let k = face.channels(w);
            Some((k, &tower.theta[family.start..family.start + a * k]))
        }
        _ => return Err("split needs a ring-faced tower".into()),
    };
    // Below the arriving class: how many classes a part puts above it.
    let rank = |values: &[i128], next: usize| values.iter().filter(|&&v| v > values[next]).count();
    let mut parts: Vec<(usize, usize, usize, usize, usize, usize, i128)> = Vec::new();
    tower
        .read_ring(&mut tower.rest(), &classes[..read_to], |i, top_face, face, ring| {
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
                if let Some((k, readout)) = readout {
                    let (phi, _, _) = RingFace::pair_read(top_face, rho)?;
                    let part: Vec<i128> = (0..a).map(|c| release(readout[c * k..(c + 1) * k].iter().zip(&phi).map(|(&x, &y)| x as i128 * y as i128).sum(), 24)).collect();
                    let ring_top = (0..a).max_by_key(|&c| (part[c], std::cmp::Reverse(c))).expect("a nonempty alphabet");
                    let other = (0..a).filter(|&c| c != next).map(|c| part[c]).max().unwrap_or(0);
                    let masses: Vec<i128> = face.masses.iter().map(|&m| m as i128).collect();
                    parts.push((i, next, top, ring_top, rank(&part, next), rank(&masses, next), part[next] - other));
                }
            }
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    if let Some((k, _)) = readout {
        // The rest: the same tower with its ring's readout at zero, read again.
        let mut rest = tower.clone();
        rest.open_ring_readout(&vec![0; a * k]).map_err(|e| e.to_string())?;
        let mut tops = Vec::with_capacity(parts.len());
        let mut at = named.iter().peekable();
        rest.read_ring(&mut rest.rest(), &classes[..read_to], |i, _, face, _| {
            if at.peek() != Some(&&i) {
                return Ok(());
            }
            at.next();
            let masses: Vec<i128> = face.masses.iter().map(|&m| m as i128).collect();
            let top = (0..a).max_by_key(|&c| (masses[c], std::cmp::Reverse(c))).expect("a nonempty alphabet");
            tops.push((top, rank(&masses, classes[i + 1])));
            Ok(())
        })
        .map_err(|e| e.to_string())?;
        let (mut ring_right, mut rest_right, mut ring_only, mut whole_only) = (0usize, 0usize, 0usize, 0usize);
        for (&(i, next, top, ring_top, ring_rank, top_rank, margin), &(rest_top, rest_rank)) in parts.iter().zip(&tops) {
            println!("SPLIT {i} {next} {top} {ring_top} {rest_top} {ring_rank} {rest_rank} {top_rank} {margin}");
            ring_right += (ring_top == next) as usize;
            rest_right += (rest_top == next) as usize;
            ring_only += (ring_top == next && top != next) as usize;
            whole_only += (ring_top != next && top == next) as usize;
        }
        println!("TOWER_SPLIT cells={} ring_top_is_next={ring_right} rest_top_is_next={rest_right} ring_not_whole={ring_only} whole_not_ring={whole_only}", parts.len());
    }
    println!(
        "TOWER_AT cells={} top_is_next={right} code_on_2^-20={code} ring_ranks={} elapsed_ms={}",
        named.len(),
        tower.ring_face().map_or(0, |f| f.ranks()),
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [agent-inferred, October 25] **The ring's readout founded on the passage it is joined on, to
/// its own precision** (`found-ring-readout`). The joined tower, its ring's readout at zero, reads
/// TEXT once from rest, and at every cell the ring's pair read with the top face,
/// `φ_t = x̂_t ⊗ ρ_t` ([`RingFace::pair_read`]), is kept beside the face's masses. The readout `W`
/// is then founded in rounds. A round starts from the readout `W` the last one left: each cell's
/// face is the tower's carried through the ring's part `o_t = W φ_t` (released as the tower's
/// step releases it, on `2^(−16)` of a bit), with `p_t` its masses as a ratio to their total and
/// `q_t` the arriving class. For each class `c` that arrives in the passage, the round's direction
/// for its row is the Newton step of the passage's code in that row, `H_c d_c = −m_c` with
/// `H_c = Σ_t p_tc (1 − p_tc) φ_t φ_tᵀ` (the code's curvature in the row) and
/// `m_c = Σ_t φ_t (p_tc − q_tc)` (its covector, `p` on `2^(−24)`), solved exactly on a copy
/// released to a common grain (directions only). The curvature only points the direction (the
/// exact code's line fixes the step and reads its saving), so its weight `p(1 − p)` is carried on
/// `2^(−12)`: a pair (cell, class) below `2^(−13)` adds no curvature, and the share of the whole
/// curvature so released is reported each round. On a passage of several media most pairs are of
/// classes a cell does not expect, and the curvature's cost is its live pairs' [agent-inferred,
/// October 25]. A ring read through its harmonics ([`RingFace::with_harmonics`])
/// takes the curvature within each harmonic's channels: the cross blocks between two harmonics of
/// a turn that runs over the circle average toward zero, as the classes' cross blocks through the
/// normalization are dropped, and a block-diagonal curvature is positive, so its step is a descent
/// direction whose scale the exact code's line then fixes [agent-inferred, October 25]; it is
/// `H` blocks of `k/H` channels in place of one of `k`. Each row's direction is on its own scale:
/// its Newton step, `d_c · 2^28 / ln 2` in readout units (the logit is `w·φ·2^(−40)` bits, the
/// code's curvature in it `ln 2 · p(1 − p)`, and the solve's curvature and covector are on `2^(−12)`
/// and `2^(−24)`; without that factor the step fell `2^28.5` short and the four-media founding
/// saved a third of a nat), unless that moves some cell's offset by more than one bit, and then scaled to
/// one bit, which keeps the code's curvature along the step within a factor four of the one solved
/// with (the log-sum's self-concordance; one scale for every row let a rare class's thin
/// curvature round every other row's direction to zero) [agent-inferred, October 25]. The rows'
/// steps are moved together by the scale under which the passage codes least: from the trusted
/// step, doubled while the code falls or halved until it falls, then narrowed by golden section
/// to `2^(−8)` of the bracket, each code read from the face's
/// masses carried through the offsets' exponential (a founding's reading at the masses' grain; the
/// joined tower's own read measures the result). A round is followed by another while it pays:
/// while its saving, read exactly at the readout it leaves, reaches half a nat for each free
/// parameter the readout re-states, `k (C − 1)` for `k` channels and `C` arriving classes (the
/// precision rule of [`round_pays`]; a class that never arrives keeps its row at zero, and the
/// first round always runs). This replaces one least-squares direction at `W = 0` (`Q D = −M`,
/// `Q = Σ φφᵀ`), whose best scale was eleven times its own, so the code's curvature along it was
/// a small share of `Q`'s, and which read 244 of the 358 held-out units the ring's own
/// training-text directions read (the tower record, "The founding stops at its own precision").
/// The ring's moments, its readout's and its factors', are then opened on the same passage,
/// partitioned as a training pass reads it (`STREAMS` streams of `SECTION` cells a section), at
/// its sections' own covector statistics ([`TowerLearner::open_moments`]): a founded family opened
/// with zero moments is undone by its first steps. The learner, its readout opened there
/// ([`Tower::open_ring_readout`]), is written to OUT (created, never overwritten).
/// With `held=R` the leading `R` ranks' readout stands as the tower holds it and only the later
/// ranks' channels are founded (a ring joined beside one already founded).
pub(super) fn found_ring_readout(args: &[String]) -> Result<()> {
    use holonics::hnn::keyed_modes::Exponential;
    use holonics::hnn::tower::TowerFace;
    use holonics::ratio::Rat;
    let held: usize = match args.get(8).map(|a| a.strip_prefix("held=")) {
        None => 0,
        Some(Some(h)) if args.len() == 9 => h.parse()?,
        _ => return Err("found-ring-readout STATE STATE_SHA TEXT TEXT_SHA STREAMS SECTION OUT [held=R]".into()),
    };
    if args.len() != 8 && args.len() != 9 {
        return Err("found-ring-readout STATE STATE_SHA TEXT TEXT_SHA STREAMS SECTION OUT [held=R]".into());
    }
    let started = std::time::Instant::now();
    let mut learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let (streams, section): (usize, usize) = (args[5].parse()?, args[6].parse()?);
    if streams == 0 || section == 0 || text.len() < streams * (section + 1) {
        return Err("the passage must hold one section a stream".into());
    }
    if std::path::Path::new(&args[7]).exists() {
        return Err("OUT exists: the founded learner is written create-new".into());
    }
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let tower = &learner.tower;
    let (a, w) = (tower.declaration.alphabet, tower.declaration.width);
    let face = tower.ring_face().ok_or("found-ring-readout needs a ring-faced tower")?;
    let k_all = face.channels(w);
    let (ring_cols, h2) = (2 * face.ranks() * face.harmonics(), 2 * face.harmonics());
    // [agent-inferred, October 25] With `held=R` the leading `R` ranks' readout is held as the
    // tower holds it (founded on this passage already, to its precision) and only the later
    // ranks' channels are founded, from the face the held part already moves: a coordinate step
    // on the blocks that are not yet founded. Founding the held rank again would move it little.
    // Holding it drops the curvature between the ranks' channels, as between two harmonics, so
    // each harmonic's block keeps one rank's width: with two ranks, a quarter of the curvature and
    // an eighth of the solves of founding both, when a ring joins one already founded.
    if held >= face.ranks() {
        return Err("held=R holds fewer ranks than the face has: one rank at least is founded".into());
    }
    let founded_ch: Vec<usize> = (0..k_all).filter(|&c| c % ring_cols >= held * h2).collect();
    let k = founded_ch.len();
    // The founded channels by the harmonic they read: column `j` of `ρ` (rank by rank `2H` parts)
    // reads harmonic `(j mod 2H) / 2`.
    let harmonic_blocks: Vec<Vec<usize>> = (0..face.harmonics()).map(|h| (0..k).filter(|&i| (founded_ch[i] % ring_cols) % h2 / 2 == h).collect()).collect();
    let family = tower.ring_family().ok_or("found-ring-readout needs a ring-faced tower")?;
    let holding: Vec<i32> = tower.theta[family.start..family.start + a * k_all].to_vec();
    if (0..a).any(|u| founded_ch.iter().any(|&c| holding[u * k_all + c] != 0)) {
        return Err("found-ring-readout founds the readout of a joined ring, at zero (a held rank's may stand)".into());
    }
    let cells = classes.len().saturating_sub(1);
    // Each cell keeps its pair read's two factors, the top face's ratio with its unit (`w + 1`) and
    // the ring's read (`ring_cols`), and its channels are their products, read where they are used:
    // `φ_t[x · ring_cols + j] = ⌊x̂_t[x] ρ_t[j]⌉ 2^(−FACE_BITS)`, [`RingFace::pair_read`]'s law, checked
    // against it at every cell as the passage is read. Kept whole, `φ` is `k` words a cell, and at a
    // key's every harmonic (`k = 65 · 2 · 55` at modulus 110) the passage's `φ` would outgrow the
    // host; its factors are `w + 1 + ring_cols` [agent-inferred, October 25].
    let xs = w + 1;
    let channel_of = |i: usize| (i / ring_cols, i % ring_cols);
    let (mut nexts, mut hats, mut rhos, mut masses) = (Vec::with_capacity(cells), Vec::with_capacity(cells * xs), Vec::with_capacity(cells * ring_cols), Vec::with_capacity(cells * a));
    let mut code_before = 0i64;
    tower
        .read_ring(&mut tower.rest(), &classes, |i, top, face, ring| {
            let (_, rho) = ring.ok_or(TowerError::Refused("a ring read at every cell of a ring-faced tower"))?;
            let (phi, hat, _) = RingFace::pair_read(top, rho)?;
            if phi.iter().any(|v| v.unsigned_abs() >= 1 << 21) {
                return Err(TowerError::Refused("a ring's pair read past 2^21 of its grain: the moments' reach is owed"));
            }
            let unit = 1i32 << FACE_BITS;
            let x_of = |x: usize| if x < hat.len() { hat[x] } else { unit };
            if hat.len() + 1 != xs || rho.len() != ring_cols || (0..k_all).any(|c| {
                let (x, j) = channel_of(c);
                release(x_of(x) as i128 * rho[j] as i128, FACE_BITS) != phi[c] as i128
            }) {
                return Err(TowerError::Refused("a pair read that its factors do not give"));
            }
            hats.extend(hat.iter().copied().chain(std::iter::once(unit)));
            rhos.extend_from_slice(rho);
            // A face's masses are on 2^(−62) below its largest, so each fits 64 bits.
            masses.extend(face.masses.iter().map(|&m| m as u64));
            nexts.push(classes[i + 1]);
            code_before += face.code(classes[i + 1]);
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    let read_ms = started.elapsed().as_millis();
    let n = nexts.len();
    // Cell `t`'s founded channel `c`.
    let phi_at = |t: usize, c: usize| -> i128 {
        let (x, j) = channel_of(founded_ch[c]);
        release(hats[t * xs + x] as i128 * rhos[t * ring_cols + j] as i128, FACE_BITS)
    };
    let mut arrives = vec![false; a];
    nexts.iter().for_each(|&c| arrives[c] = true);
    let reached: Vec<usize> = (0..a).filter(|&c| arrives[c]).collect();
    let r = reached.len();
    let free = k * (r - 1);
    let ln_two = holonics::ratio::algebraic::ln_enclosure(&Rat::from_integer(BigInt::from(2))).map_err(|e| format!("ln 2's enclosure: {e:?}"))?;
    let exponential = Exponential::new(16);
    // The face at cell t with the ring's part `o` (one offset an arriving class, on 2^(−16) of a
    // bit; every other class's part is zero).
    let face_of = |t: usize, o: &[i64]| -> TowerFace {
        let largest = o.iter().copied().max().unwrap_or(0);
        let top = if r < a { largest.max(0) } else { largest };
        let base = &masses[t * a..(t + 1) * a];
        let rest = exponential.below_one(-(top as i128));
        let mut ms: Vec<u128> = base.iter().map(|&mass| ((mass as u128 * rest) >> 62).max(1)).collect();
        for (j, &c) in reached.iter().enumerate() {
            ms[c] = ((base[c] as u128 * exponential.below_one((o[j] - top) as i128)) >> 62).max(1);
        }
        let total = ms.iter().sum();
        TowerFace { masses: ms, total }
    };
    // Each cell's ring part at the readout `wr` (the arriving classes' rows, `r · k`).
    let offsets = |wr: &[i64]| -> Vec<i64> {
        let mut out = vec![0i64; n * r];
        out.par_chunks_mut(r).enumerate().for_each_init(
            || vec![0i128; k],
            |phi, (t, o)| {
                for (c, v) in phi.iter_mut().enumerate() {
                    *v = phi_at(t, c);
                }
                for (j, slot) in o.iter_mut().enumerate() {
                    *slot = release(wr[j * k..(j + 1) * k].iter().zip(phi.iter()).map(|(&x, &y)| x as i128 * y).sum(), 24) as i64;
                }
            },
        );
        out
    };
    let code_at = |offs: &[i64]| -> i64 { (0..n).into_par_iter().map(|t| face_of(t, &offs[t * r..(t + 1) * r]).code(nexts[t])).sum() };
    let mut wr = vec![0i64; r * k];
    let mut offs = vec![0i64; n * r];
    let mut current = code_at(&offs);
    let at_zero = current;
    let (mut round, mut evaluations) = (0usize, 1usize);
    let mut kappas: Vec<i64> = Vec::new();
    // Half a nat a free parameter, on 2^(−20) of a nat.
    let half_free = Rat::from_integer(BigInt::from(free) << 19u32);
    loop {
        let round_started = std::time::Instant::now();
        // The masses as a ratio to their total, on 2^(−24), at every cell for every arriving class.
        let probs: Vec<i64> = (0..n)
            .into_par_iter()
            .flat_map_iter(|t| {
                let face = face_of(t, &offs[t * r..(t + 1) * r]);
                reached.iter().map(|&c| (((face.masses[c] << 24) + face.total / 2) / face.total) as i64).collect::<Vec<_>>()
            })
            .collect();
        // Each arriving class's curvature and covector, the curvature within each harmonic's
        // channels: |φ| < 2^21 and p(1 − p) ≤ 2^10 on its grain keep every term below 2^52, and the
        // sums inside 128 bits over fewer than 2^60 cells. First the pairs (cell, class) whose
        // curvature is live at its grain, and the curvature released below it (on 2^(−48)), read
        // before the curvature is accumulated, so a round's cost is known before it is spent.
        let tally = probs.par_iter().fold(|| [0u128; 3], |mut acc, &p| {
            let exact = (p as i128 * ((1i128 << 24) - p as i128)) as u128;
            let live = (exact + (1 << 35)) >> 36 != 0;
            acc[0] += u128::from(live);
            acc[1] += if live { 0 } else { exact };
            acc[2] += exact;
            acc
        }).reduce(|| [0u128; 3], |a, b| [a[0] + b[0], a[1] + b[1], a[2] + b[2]]);
        println!(
            "RING_READOUT_CURVATURE round={round} live_pairs={} pairs={} released_ppm={} elapsed_ms={}",
            tally[0],
            n * r,
            (tally[1] * 1_000_000 + tally[2] / 2) / tally[2].max(1),
            started.elapsed().as_millis()
        );
        let blocks: Vec<(BlockId, Vec<i128>, Vec<i128>)> = (0..r)
            .flat_map(|j| (0..harmonic_blocks.len()).map(move |b| (j, b)))
            .collect::<Vec<_>>()
            .into_par_iter()
            .map(|(j, b)| {
                let c = reached[j];
                let channels = &harmonic_blocks[b];
                let kb = channels.len();
                let (mut h, mut m) = (vec![0i128; kb * kb], vec![0i128; kb]);
                // [agent-inferred, October 25] A curvature term is below 2^52 (|φ| < 2^21 and the
                // curvature on its grain at most 2^10) and a covector term below 2^45 (|y| ≤ 2^24),
                // so 2^11 cells' terms sum inside 64 bits. The sums are carried 64 bits wide and
                // cross into 128 every 2^11 live cells: a carrier as wide as its terms need, and
                // the same integers, since the sum is exact in any grouping. At 128 bits throughout
                // the four media's curvature took 1,087 s a round.
                const CROSSING: usize = 1 << 11;
                let (mut h64, mut m64) = (vec![0i64; kb * kb], vec![0i64; kb]);
                let cross = |h: &mut [i128], m: &mut [i128], h64: &mut [i64], m64: &mut [i64]| {
                    for (wide, part) in h.iter_mut().zip(h64.iter_mut()).chain(m.iter_mut().zip(m64.iter_mut())) {
                        *wide += *part as i128;
                        *part = 0;
                    }
                };
                let mut x = vec![0i64; kb];
                let mut pending = 0usize;
                for t in 0..n {
                    let p = probs[t * r + j];
                    let y = p - if nexts[t] == c { 1 << 24 } else { 0 };
                    let curvature = ((p as i128 * ((1i128 << 24) - p as i128) + (1 << 35)) >> 36) as i64;
                    if y == 0 && curvature == 0 {
                        continue;
                    }
                    for (slot, &i) in x.iter_mut().zip(channels) {
                        *slot = phi_at(t, i) as i64;
                    }
                    for i in 0..kb {
                        let xi = x[i];
                        if xi == 0 {
                            continue;
                        }
                        m64[i] += xi * y;
                        if curvature != 0 {
                            let xc = xi * curvature;
                            for (slot, &xl) in h64[i * kb + i..(i + 1) * kb].iter_mut().zip(&x[i..]) {
                                *slot += xc * xl;
                            }
                        }
                    }
                    pending += 1;
                    if pending == CROSSING {
                        cross(&mut h, &mut m, &mut h64, &mut m64);
                        pending = 0;
                    }
                }
                cross(&mut h, &mut m, &mut h64, &mut m64);
                ((j, b), h, m)
            })
            .collect();
        // Each phase of the round is reported as it ends, so a long round is read as it runs.
        println!("RING_READOUT_PHASE round={round} phase=curvature blocks={} elapsed_ms={}", blocks.len(), started.elapsed().as_millis());
        // Each row's Newton direction in each harmonic on a copy released so its curvature's
        // largest entry is below 2^40, the covector by the same shift: `D · H⁻¹ m` and `D`.
        let solved: Vec<(BlockId, BigInt, Vec<BigInt>)> = blocks
            .par_iter()
            .map(|(id, h, m)| {
                let kb = m.len();
                let largest = h.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0);
                let shift = (128 - largest.leading_zeros()).saturating_sub(40);
                let hh: Vec<Vec<BigInt>> = (0..kb).map(|i| (0..kb).map(|l| BigInt::from(release(h[i.min(l) * kb + i.max(l)], shift))).collect()).collect();
                let rr: Vec<Vec<BigInt>> = m.iter().map(|&v| vec![BigInt::from(release(v, shift))]).collect();
                let (det, y) = solve_scaled(&hh, &rr, false).map_err(|e| e.to_string())?;
                Ok((*id, det, y.into_iter().map(|row| row.into_iter().next().unwrap_or_default()).collect()))
            })
            .collect::<std::result::Result<_, String>>()?;
        println!("RING_READOUT_PHASE round={round} phase=solve elapsed_ms={}", started.elapsed().as_millis());
        // What each harmonic's Newton step would save, summed over the rows: the quadratic model's
        // `½ gᵀ H⁻¹ g` of the code is `2^(−37) mᵀ H⁻¹ m` nats (`g = m 2^(−64)` bits a readout unit,
        // the code's curvature `ln 2 · H · 2^(−92)`), on its own block. A reading of where the
        // passage's code lies on the ring's harmonics, before the trust and the line; nothing
        // chooses by it [agent-inferred, October 25].
        let mut predicted = vec![BigInt::zero(); harmonic_blocks.len()];
        for ((id, _, m), (_, det, y)) in blocks.iter().zip(&solved) {
            if det.is_zero() {
                continue;
            }
            let num: BigInt = m.iter().zip(y).map(|(&mi, yi)| BigInt::from(mi) * yi).sum();
            let (num, den) = if det.is_negative() { (-num, -det.clone()) } else { (num, det.clone()) };
            predicted[id.1] += div_round(&(num * 1000), &(den << 37u32));
        }
        println!(
            "RING_READOUT_HARMONICS round={round} predicted_millinats={}",
            predicted.iter().enumerate().map(|(h, v)| format!("{}:{v}", h + 1)).collect::<Vec<_>>().join(",")
        );
        // Each row on its own scale [agent-inferred, October 25]. One lift for every row let the
        // widest row (a class rare in the passage, its curvature thin where its covector is not)
        // set the scale, and every other row's direction rounded to zero. Row `j`'s direction is
        // lifted so its widest entry is near 2^20, `D_j = 2^(ℓ_j) d_j`.
        let mut widest = vec![None::<i64>; r];
        for ((j, _), det, y) in &solved {
            if det.is_zero() || y.iter().all(|v| v.is_zero()) {
                continue;
            }
            let wide = y.iter().map(|v| v.bits()).max().unwrap_or(0) as i64 - det.bits() as i64;
            widest[*j] = Some(widest[*j].map_or(wide, |w: i64| w.max(wide)));
        }
        if widest.iter().all(Option::is_none) {
            if round == 0 {
                return Err("the passage's code has no direction in the ring's readout".into());
            }
            break;
        }
        // A lift is bounded by the widths the solve already holds (`|ℓ_j| ≤ 20 + bits(y) + bits(det)`),
        // and how far a row's step can lie from the others' grain is refused where it would leave its
        // carrier: the lifted entry's 64 bits and the scale's 128 below.
        let lifts: Vec<i64> = widest.iter().map(|w| w.map_or(0, |w| 20 - w)).collect();
        let mut lifted = vec![0i64; r * k];
        for ((j, b), det, y) in &solved {
            if det.is_zero() {
                continue;
            }
            let lift = lifts[*j];
            for (&i, v) in harmonic_blocks[*b].iter().zip(y) {
                let (num, den) = if lift >= 0 { (-(v << lift as u32), det.clone()) } else { (-v.clone(), det << (-lift) as u32) };
                let (num, den) = if den < BigInt::zero() { (-num, -den) } else { (num, den) };
                lifted[j * k + i] = i64::try_from(div_round(&num, &den)).map_err(|_| "a lifted direction entry outgrew 64 bits".to_string())?;
            }
        }
        // The trust of a step [agent-inferred, October 25]. The code's curvature at a cell is the
        // variance of the moved offsets under the face's shares, and a step that moves no offset
        // by more than `s` bits changes every share by a factor within `2^(±2s)`, so the curvature
        // anywhere along it stays within `4^s` of the one the direction was solved with (the
        // log-sum's self-concordance in its largest offset). Each row takes its Newton step unless
        // that moves some cell's offset by more than one bit; then its step is scaled to move that
        // offset by one bit.
        //
        // The Newton step's units. A cell's offset is `(w·φ)·2^(−24)` on `2^(−16)` of a bit, so its
        // logit is `w·φ·2^(−40)` bits; the code in bits has gradient `p − q` and curvature
        // `ln 2 · (diag p − p pᵀ)` in those logits. The solve used curvature on `2^(−12)` and the
        // covector on `2^(−24)`, so its solution `d_j = −H⁻¹m` (lifted above to `D_j = 2^(ℓ_j) d_j`) is
        // the Newton step on `2^(−28)·ln 2` of a readout unit: the step is `d_j · 2^28 / ln 2`. Row
        // `j`'s scale on its lifted direction is `ν_j = 2^(28 − ℓ_j) / ln 2`, or `2^16 / reach_j` when
        // `ν_j · reach_j` passes one bit, with `reach_j` the largest offset the lifted direction
        // moves (on `2^(−16)` of a bit). The scale is carried on `2^(−40)`.
        let unit_moved = offsets(&lifted);
        let reach: Vec<i128> = (0..r).into_par_iter().map(|j| (0..n).map(|t| (unit_moved[t * r + j] as i128).abs()).max().unwrap_or(0)).collect();
        let one_bit = Rat::from_integer(BigInt::from(1u64 << 16));
        let pow2 = |e: i64| -> Rat { if e >= 0 { Rat::from_integer(BigInt::one() << e as u32) } else { Rat::new(BigInt::one(), BigInt::one() << (-e) as u32) } };
        let mut scales = vec![0i128; r];
        let (mut capped, mut reach_bits) = (0usize, i64::MIN);
        for j in 0..r {
            if reach[j] == 0 {
                continue;
            }
            let newton = pow2(28 - lifts[j]) / ln_two.lower.clone();
            let newton_reach = &newton * Rat::from_integer(BigInt::from(reach[j]));
            // The Newton step's largest offset, in bits (to the nearest power of two below).
            let whole = newton_reach.to_integer();
            let bits = if whole.is_zero() { -(newton_reach.recip().to_integer().bits() as i64) - 16 } else { whole.bits() as i64 - 1 - 16 };
            reach_bits = reach_bits.max(bits);
            let scale = if newton_reach > one_bit {
                capped += 1;
                Rat::new(BigInt::from(1u64 << 16), BigInt::from(reach[j]))
            } else {
                newton
            };
            scales[j] = i128::try_from((scale * pow2(40)).round().to_integer()).map_err(|_| "a row's step scale outgrew 128 bits".to_string())?;
        }
        if reach_bits == i64::MIN {
            reach_bits = 0;
        }
        let rdiv = |x: i128| -> i128 { (x + (1i128 << 39)) >> 40 };
        let mut direction = vec![0i64; r * k];
        for (j, &s) in scales.iter().enumerate() {
            for i in 0..k {
                let x = (lifted[j * k + i] as i128).checked_mul(s).ok_or("a scaled direction entry outgrew 128 bits")?;
                direction[j * k + i] = i64::try_from(rdiv(x)).map_err(|_| "a scaled direction entry outgrew 64 bits".to_string())?;
            }
        }
        // Each cell's ring part moved by the trusted step, on 2^(−16) of a bit.
        let moved: Vec<i64> = unit_moved
            .par_iter()
            .enumerate()
            .map(|(i, &v)| (v as i128).checked_mul(scales[i % r]).and_then(|x| i64::try_from(rdiv(x)).ok()))
            .collect::<Option<_>>()
            .ok_or("a moved offset outgrew 64 bits")?;
        let code = |kappa: i64| -> i64 {
            (0..n)
                .into_par_iter()
                .map(|t| {
                    let o: Vec<i64> = (0..r).map(|j| offs[t * r + j] + release(kappa as i128 * moved[t * r + j] as i128, 16) as i64).collect();
                    face_of(t, &o).code(nexts[t])
                })
                .sum()
        };
        // The line from the trusted step (`kappa` on 2^(−16) of it): doubled while the code falls,
        // or halved until it falls.
        let (mut best, mut best_code) = (0i64, current);
        let trusted = code(1 << 16);
        evaluations += 1;
        if trusted < current {
            (best, best_code) = (1 << 16, trusted);
            let mut kappa = 1i64 << 17;
            loop {
                if kappa > 1 << 40 {
                    return Err("the passage's code fell along the trusted step past 2^24 of it".into());
                }
                let c = code(kappa);
                evaluations += 1;
                if c >= best_code {
                    break;
                }
                (best, best_code) = (kappa, c);
                kappa *= 2;
            }
        } else {
            let mut kappa = 1i64 << 15;
            while kappa >= 1 {
                let c = code(kappa);
                evaluations += 1;
                if c < best_code {
                    (best, best_code) = (kappa, c);
                    break;
                }
                kappa /= 2;
            }
        }
        if best == 0 {
            if round == 0 {
                return Err("the passage's code did not fall along the founded direction".into());
            }
            println!("RING_READOUT_ROUND round={round} kappa_on_2^-16=0 another=false round_ms={} elapsed_ms={}", round_started.elapsed().as_millis(), started.elapsed().as_millis());
            break;
        }
        // Golden section on [best/2, 2·best] to 2^(−8) of the bracket.
        let (mut lo, mut hi) = (best / 2, 2 * best);
        let width = (hi - lo) >> 8;
        let golden = |lo: i64, hi: i64| -> (i64, i64) {
            let span = (hi - lo) as i128;
            let cut = (span * 381966 + 500000) / 1000000; // 1 − 1/φ to 2^(−20)
            (lo + cut as i64, hi - cut as i64)
        };
        let (mut x1, mut x2) = golden(lo, hi);
        let (mut c1, mut c2) = (code(x1), code(x2));
        evaluations += 2;
        while hi - lo > width.max(1) && x1 < x2 {
            if c1 <= c2 {
                hi = x2;
                (x2, c2) = (x1, c1);
                x1 = golden(lo, hi).0;
                c1 = code(x1);
            } else {
                lo = x1;
                (x1, c1) = (x2, c2);
                x2 = golden(lo, hi).1;
                c2 = code(x2);
            }
            evaluations += 1;
        }
        for (x, c) in [(x1, c1), (x2, c2)] {
            if c < best_code {
                (best, best_code) = (x, c);
            }
        }
        // The readout the round leaves, and its code read exactly there.
        let moved_readout: Vec<i64> = wr.iter().zip(&direction).map(|(&v, &d)| v + release(best as i128 * d as i128, 16) as i64).collect();
        let moved_offsets = offsets(&moved_readout);
        let left = code_at(&moved_offsets);
        evaluations += 1;
        let saved = current - left;
        // The saving in nats on 2^(−20): the code's bits times ln 2's enclosure's lower end.
        let saved_nats = Rat::from_integer(BigInt::from(saved)) * ln_two.lower.clone();
        let millinats = (&saved_nats * Rat::new(BigInt::from(1000), BigInt::from(1u64 << 20))).round().to_integer().to_string();
        let pays = saved > 0 && saved_nats >= half_free;
        println!(
            "RING_READOUT_ROUND round={round} kappa_on_2^-16={best} capped_rows={capped} newton_reach_bits={reach_bits} code_on_2^-20={left} line_code={best_code} saved_millinats={millinats} another={pays} round_ms={} elapsed_ms={}",
            round_started.elapsed().as_millis(),
            started.elapsed().as_millis()
        );
        if saved <= 0 {
            if round == 0 {
                return Err("the founded readout, released, did not lower the passage's code".into());
            }
            break;
        }
        (wr, offs, current) = (moved_readout, moved_offsets, left);
        kappas.push(best);
        round += 1;
        if !pays {
            break;
        }
    }
    drop((masses, hats, rhos, offs));
    let mut readout = holding;
    for (j, &c) in reached.iter().enumerate() {
        for (i, &ch) in founded_ch.iter().enumerate() {
            readout[c * k_all + ch] = i32::try_from(wr[j * k + i]).map_err(|_| "a founded readout entry outgrew its 32-bit carrier".to_string())?;
        }
    }
    learner.tower.open_ring_readout(&readout).map_err(|e| e.to_string())?;
    // The moments on the training pass's partition: section k of stream s reads
    // `[s·chunk + k·section, s·chunk + (k + 1)·section]`.
    let moments_started = std::time::Instant::now();
    let chunk = classes.len() / streams;
    let sections: Vec<Vec<&[usize]>> = (0..(chunk - 1) / section)
        .map(|k| (0..streams).map(|s| &classes[s * chunk + k * section..s * chunk + (k + 1) * section + 1]).collect())
        .collect();
    let family = learner.tower.ring_family().ok_or("a ring-faced tower has a ring")?;
    let mut states: Vec<_> = (0..streams).map(|_| learner.tower.rest()).collect();
    let read_sections = learner.open_moments(family.clone(), &mut states, &sections).map_err(|e| e.to_string())?;
    let moments_ms = moments_started.elapsed().as_millis();
    let written = learner.to_text();
    std::io::Write::write_all(&mut std::fs::OpenOptions::new().write(true).create_new(true).open(&args[7])?, written.as_bytes())?;
    println!(
        "RING_READOUT cells={n} channels={k} held_ranks={held} arriving_classes={r} free={free} rounds={round} kappas_on_2^-16={} code_before_on_2^-20={code_before} code_at_zero={at_zero} code_founded={current} evaluations={evaluations} largest={} moment_sections={read_sections} moments_ms={moments_ms} sha256={} read_ms={read_ms} elapsed_ms={}",
        kappas.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(","),
        readout.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0),
        sha256(written.as_bytes())?,
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [agent-inferred, October 25] **One pass with a declared hold** (`pass-ring-held STATE
/// STATE_SHA TRAIN TRAIN_SHA STREAMS SECTION HOLD OUT`), a foil that separates which families'
/// steps carry the pass's change: the learner reads TRAIN once on the training pass's partition
/// (`STREAMS` streams of `SECTION` cells a section from rest, the streams carried), certifying
/// each section as a training pass does, with `HOLD` declaring what does not deposit:
/// `all-but-readouts` deposits only the tower's readout and bias and the ring's readout `W`;
/// `ring-readout` deposits everything but `W`; `ring-reads` holds the material the ring's push reads
/// ([`Tower::ring_read_families`]) and deposits the rest. The learner is written to OUT (created, never
/// overwritten); the code before and after each section are summed into the pass's receipt.
pub(super) fn pass_ring_held(args: &[String]) -> Result<()> {
    if args.len() != 9 {
        return Err("pass-ring-held STATE STATE_SHA TRAIN TRAIN_SHA STREAMS SECTION HOLD OUT".into());
    }
    let started = std::time::Instant::now();
    let mut learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let (streams, section): (usize, usize) = (args[5].parse()?, args[6].parse()?);
    if streams == 0 || section == 0 || text.len() < streams * (section + 1) {
        return Err("the passage must hold one section a stream".into());
    }
    if std::path::Path::new(&args[8]).exists() {
        return Err("OUT exists: the learner is written create-new".into());
    }
    let tower = &learner.tower;
    // A tower without a ring (the foil) holds everything but its own readout.
    let w = match (tower.ring_family(), tower.ring_factor_family()) {
        (Some(ring), Some(factors)) => Some(ring.start..factors.start),
        _ => None,
    };
    let readout = tower.readout_family();
    let len = tower.theta.len();
    learner.held = match args[7].as_str() {
        "all-but-readouts" => {
            let mut moving: Vec<std::ops::Range<usize>> = std::iter::once(readout).chain(w).collect();
            moving.sort_by_key(|r| r.start);
            let mut held = Vec::new();
            let mut at = 0;
            for m in moving {
                held.push(at..m.start);
                at = m.end;
            }
            held.push(at..len);
            held
        }
        "ring-readout" => vec![w.ok_or("ring-readout needs a ring-faced tower")?],
        "ring-reads" => {
            w.as_ref().ok_or("ring-reads needs a ring-faced tower")?;
            tower.ring_read_families()
        }
        _ => return Err("HOLD is all-but-readouts, ring-readout or ring-reads".into()),
    };
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let chunk = classes.len() / streams;
    let mut states: Vec<_> = (0..streams).map(|_| learner.tower.rest()).collect();
    let (mut before, mut after, mut deposits, mut cells) = (0i64, 0i64, 0usize, 0usize);
    let sections = (chunk - 1) / section;
    for k in 0..sections {
        let parts: Vec<&[usize]> = (0..streams).map(|s| &classes[s * chunk + k * section..s * chunk + (k + 1) * section + 1]).collect();
        let receipt = learner.section(&mut states, &parts).map_err(|e| e.to_string())?;
        before += receipt.code_before;
        after += receipt.code_after;
        deposits += receipt.deposited as usize;
        cells += receipt.cells;
    }
    learner.held = Vec::new();
    let written = learner.to_text();
    std::io::Write::write_all(&mut std::fs::OpenOptions::new().write(true).create_new(true).open(&args[8])?, written.as_bytes())?;
    println!(
        "RING_HELD_PASS hold={} sections={sections} deposits={deposits} cells={cells} code_before_on_2^-20={before} code_after_on_2^-20={after} sha256={} elapsed_ms={}",
        args[7],
        sha256(written.as_bytes())?,
        started.elapsed().as_millis()
    );
    Ok(())
}

/// [agent-inferred, October 25] **Every cell's reading** (an exterior read for choosing the ring's
/// readout law): the frozen tower reads TEXT from rest, and each cell's record goes to OUT (created,
/// never overwritten), little-endian: the class that arrives next (`u32`), the top face the readout
/// reads (`width` × `i32`, on `2^(−16)`), the ring's face `ρ` (`2R` × `i32`, zero without a ring)
/// and every class's share of the face's masses (`alphabet` × `u32`, on `2^(−32)`, floored).
/// Nothing in it enters the tower.
pub(super) fn read_tower_cells(args: &[String]) -> Result<()> {
    use std::io::Write;
    if args.len() != 6 {
        return Err("read-tower-cells STATE STATE_SHA TEXT TEXT_SHA OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let tower = &learner.tower;
    let (ranks, harmonics) = tower.ring_face().map_or((0, 0), |f| (f.ranks(), f.harmonics()));
    let file = std::fs::OpenOptions::new().write(true).create_new(true).open(&args[5])?;
    let mut out = std::io::BufWriter::new(file);
    let mut failed: Option<std::io::Error> = None;
    let mut cells = 0usize;
    tower
        .read_ring(&mut tower.rest(), &classes, |i, top, face, ring| {
            let mut record = Vec::with_capacity(4 * (1 + top.len() + 2 * ranks + face.masses.len()));
            record.extend((classes[i + 1] as u32).to_le_bytes());
            top.iter().for_each(|v| record.extend(v.to_le_bytes()));
            match ring {
                Some((_, rho)) => rho.iter().for_each(|v| record.extend(v.to_le_bytes())),
                None => (0..2 * ranks * harmonics).for_each(|_| record.extend(0i32.to_le_bytes())),
            }
            for &m in &face.masses {
                let share = ((m << 32) / face.total).min(u32::MAX as u128) as u32;
                record.extend(share.to_le_bytes());
            }
            if failed.is_none() {
                if let Err(e) = out.write_all(&record) {
                    failed = Some(e);
                }
            }
            cells += 1;
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    if let Some(e) = failed {
        return Err(e.into());
    }
    out.flush()?;
    println!("TOWER_CELLS cells={cells} width={} ring_channels={} alphabet={} elapsed_ms={}", tower.declaration.width, 2 * ranks, tower.declaration.alphabet, started.elapsed().as_millis());
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

    /// A closure system's torsion is the primes every maximal minor carries. The rows `(2, 0)`,
    /// `(0, 5)`, `(4, 10)`, `(2, 5)` have rank 2 over the rationals and maximal minors 10, 20, 10,
    /// −20, −10 and 0, whose divisor is `10 = 2·5`: the certified minor is at the first two rows, the
    /// rank falls modulo 2 and modulo 5 and holds modulo 3.
    #[test]
    fn the_closures_torsion_is_the_primes_its_minors_share() {
        let rows: Vec<Vec<i128>> = vec![vec![2, 0], vec![0, 5], vec![4, 10], vec![2, 5]];
        let (rank, det, kernel) = rational_rank(&rows);
        assert!(kernel.is_empty(), "a system of full column rank has no kernel");
        assert_eq!(rank, 2);
        assert_eq!(det.abs(), BigInt::from(10));
        assert_eq!(readable_primes(&det.abs()), vec![2, 5]);
        for p in [2u64, 5] {
            assert_eq!(echelon_mod(&rows, p, rank).pivots.len(), 1, "modulo {p}");
        }
        assert_eq!(echelon_mod(&rows, 3, rank).pivots.len(), 2);
        // A system with no torsion: a unit minor.
        let free: Vec<Vec<i128>> = vec![vec![1, 1], vec![1, 2], vec![2, 3]];
        let (rank, det, _) = rational_rank(&free);
        assert_eq!((rank, det), (2, BigInt::from(1)));
        // A system with a kernel: `(1, 1, −2)` closes both rows over the integers.
        let (rank, det, kernel) = rational_rank(&[vec![1i128, 1, -2], vec![2, 0, -2]]);
        assert_eq!(rank, 2);
        assert_eq!(kernel.len(), 1);
        let k = &kernel[0];
        assert!(!det.is_zero() && k.iter().all(|x| *x == k[0]), "{k:?}");
    }

    /// The echelon kept reduced as rows arrive is the echelon of reducing each row against the
    /// echelon basis in order and clearing the later pivots after: the same rows kept, pivots and
    /// reduced rows, on sparse rows of small counts as a closure's are, at every stop.
    #[test]
    fn the_reduced_echelon_is_the_echelon_reduced_after() {
        fn in_order(rows: &[Vec<i128>], p: u64, stop: usize) -> Echelon {
            let wide = p as i128;
            let mut basis: Vec<(usize, Vec<u64>)> = Vec::new();
            let mut sources = Vec::new();
            for (i, row) in rows.iter().enumerate() {
                if basis.len() == stop {
                    break;
                }
                let mut r: Vec<u64> = row.iter().map(|&x| x.rem_euclid(wide) as u64).collect();
                for (c, b) in &basis {
                    let f = r[*c];
                    if f != 0 {
                        for (x, &y) in r.iter_mut().zip(b) {
                            *x = (*x + (p - f) * y) % p;
                        }
                    }
                }
                let Some(c) = r.iter().position(|&x| x != 0) else { continue };
                let inv = inv_mod(r[c], p);
                r.iter_mut().for_each(|x| *x = *x * inv % p);
                basis.push((c, r));
                sources.push(i);
            }
            for k in (0..basis.len()).rev() {
                for j in k + 1..basis.len() {
                    let f = basis[k].1[basis[j].0];
                    if f != 0 {
                        let (head, tail) = basis.split_at_mut(j);
                        for (x, &y) in head[k].1.iter_mut().zip(&tail[0].1) {
                            *x = (*x + (p - f) * y) % p;
                        }
                    }
                }
            }
            let mut order: Vec<usize> = (0..basis.len()).collect();
            order.sort_by_key(|&k| basis[k].0);
            Echelon { pivots: order.iter().map(|&k| basis[k].0).collect(), sources: order.iter().map(|&k| sources[k]).collect(), rows: order.into_iter().map(|k| std::mem::take(&mut basis[k].1)).collect() }
        }
        // Sparse rows of small signed counts, some repeated and some dependent, from a fixed walk.
        let (n, columns) = (60, 23);
        let mut state = 0x9e37_79b9u64;
        let mut rows: Vec<Vec<i128>> = (0..n)
            .map(|_| {
                (0..columns)
                    .map(|_| {
                        state = state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
                        let v = (state >> 33) % 13;
                        if v < 9 { 0 } else { v as i128 - 11 }
                    })
                    .collect()
            })
            .collect();
        rows.push(rows[3].iter().zip(&rows[7]).map(|(a, b)| 2 * a - b).collect());
        rows.push(rows[5].clone());
        for p in [2u64, 3, 5, 7, 11, 2_147_483_647] {
            for stop in [1, 5, 12, columns] {
                let (a, b) = (echelon_mod(&rows, p, stop), in_order(&rows, p, stop));
                assert_eq!((&a.pivots, &a.sources, &a.rows), (&b.pivots, &b.sources, &b.rows), "modulo {p}, stop {stop}");
            }
        }
    }
}
