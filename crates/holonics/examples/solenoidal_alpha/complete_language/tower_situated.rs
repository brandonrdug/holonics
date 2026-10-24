//! The situated pool: the state a class meets, crossed with the class arriving, founded on the
//! covector the tower's later faces send back to the cell's input.
//!
//! [definition; agent-inferred, October 24] A situated form reads
//!
//! ```text
//! c = (aᵀŝ)(bᵀx̂),   ŝ = one level's carried modes before the move (carried_face),
//!                   x̂ = (E(u), 2^16) the arriving class's encoding with the unit
//! ```
//!
//! and its lift into the input, `x⁰ = E(u) + P c`, crosses a strand the state carries with the
//! class that arrives. A mode's own move crosses them only where the class turns the strand's
//! mode; the record `2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT…` ("The flux at the units")
//! finds the mixed terrain gathering its energy into modes every digit moves alike, so the second
//! operand's units arrive on a state that holds the first operand's (476 of 495) and leaves them
//! uncrossed (124 to 134).
//!
//! The founding reads, over the training text in the learner's streams and sections, the covector
//! `y` the tower's own reverse sends to each cell's input ([`Tower::read_input_covectors`]): the
//! tension of every later face in the section carried back to where the class arrived. It is kept
//! as moments, written once (`read-tower-situated-moments`), so a founding never reads the text
//! again. The class alone bridges its covector's class mean (the encoding's own covector), so the
//! forms are read centred within each arriving class.
//!
//! Each rank founds the form whose lift saves the most code, read to second order in the
//! covector's own metric (the effective tension's law, `contact.tension-founds-face`, read at the
//! input; the closure fold's `det S/det S₀ = Π(1−ρ²)`). With `H = Y/N`, `Y = Σ yyᵀ` the empirical
//! Fisher of the input (a log-loss's covector carries its own curvature: `E[yyᵀ]` is the Fisher),
//! forms `c` with within-class Gram `G` and cross moment `R = Σ c yᵀ` save at best
//! `ΔL = −½ tr(R H⁻¹ Rᵀ G⁻¹)` nats, so `s = −2ΔL/N = tr(Y⁻¹ Rᵀ G⁻¹ R)`, the sum of the squared
//! canonical correlations between the forms and the tension: twice the nats a cell saves, and the
//! share reported in thousandths. [agent-inferred, October 24] Fitting `−y` in the identity metric
//! instead (energy, Brier's metric) founded a first form on prose letters that removed 1‰ of the
//! training tension and none held out (the record's "The situated pool"): energy saturates where
//! code does not, so a cell whose class the tower cannot place (a sum's units, 3.49 bits) weighs no
//! more than a prose letter it nearly knows. The two factors alternate from `b` the unit, each the
//! leading canonical direction of its block ([`leading_canonical`]). Directions are searched on
//! released copies; every share is read exactly from the moments.

use super::tower_train::{count, pair_hats, positive, release_big, release_wide, solve_scaled, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::{carried_face, Tower, TowerError, TowerLearner};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use rayon::prelude::*;

/// The largest magnitude a carried coordinate or a covector entry may have for the moment sums to
/// stay inside 128 bits over fewer than `2^32` cells: each product is below `2^80`.
const MOMENT_REACH: i64 = 1 << 40;

/// One class's moments over the cells it arrives at: `n`, `Σŝ`, `Σy`, `Σŝŝᵀ` (upper triangle)
/// and `Σŝyᵀ`.
#[derive(Clone)]
struct ClassMoments {
    n: i128,
    s: Vec<i128>,
    y: Vec<i128>,
    q: Vec<i128>,
    m: Vec<i128>,
}

/// A text's moments: per arriving class, and `Y = Σyyᵀ` over every cell (upper triangle).
struct Moments {
    dims: usize,
    width: usize,
    classes: Vec<Option<ClassMoments>>,
    yy: Vec<i128>,
    cells: usize,
}

/// A `key=value` field of a head line.
fn head_field(line: &str, key: &str) -> Result<String> {
    line.split_whitespace().find_map(|f| f.strip_prefix(key).and_then(|f| f.strip_prefix('=')).map(str::to_string)).ok_or_else(|| format!("the head line has no {key}").into())
}

fn numbers(text: &str) -> Result<Vec<i128>> {
    text.split(',').filter(|x| !x.is_empty()).map(|x| Ok(x.parse::<i128>()?)).collect()
}

/// The upper triangle of a square `d × d` row-major matrix, row by row.
fn upper(full: &[i128], d: usize) -> Vec<i128> {
    (0..d).flat_map(|i| full[i * d + i..(i + 1) * d].iter().copied()).collect()
}

/// A square `d × d` matrix whose upper triangle is `values` (the lower left zero).
fn from_upper(values: &[i128], d: usize) -> Vec<i128> {
    let mut full = vec![0i128; d * d];
    let mut at = values.iter();
    for i in 0..d {
        for slot in &mut full[i * d + i..(i + 1) * d] {
            *slot = *at.next().expect("the upper triangle's length is checked by its reader");
        }
    }
    full
}

impl Moments {
    fn new(alphabet: usize, dims: usize, width: usize) -> Self {
        Self { dims, width, classes: vec![None; alphabet], yy: vec![0; width * width], cells: 0 }
    }

    fn add(&mut self, class: usize, s: &[i64], y: &[i64]) -> std::result::Result<(), &'static str> {
        let (d, w) = (self.dims, self.width);
        if s.iter().chain(y).any(|v| v.abs() >= MOMENT_REACH) || self.cells as u64 >= 1 << 32 {
            return Err("a carried coordinate or covector entry past 2^40, or 2^32 cells: the moments would leave 128 bits");
        }
        let c = self.classes[class].get_or_insert_with(|| ClassMoments { n: 0, s: vec![0; d], y: vec![0; w], q: vec![0; d * d], m: vec![0; d * w] });
        c.n += 1;
        for i in 0..d {
            let si = s[i] as i128;
            if si == 0 {
                continue;
            }
            c.s[i] += si;
            for (slot, &sj) in c.q[i * d + i..(i + 1) * d].iter_mut().zip(&s[i..]) {
                *slot += si * sj as i128;
            }
            for (slot, &yr) in c.m[i * w..(i + 1) * w].iter_mut().zip(y) {
                *slot += si * yr as i128;
            }
        }
        for r in 0..w {
            let yr = y[r] as i128;
            c.y[r] += yr;
            if yr == 0 {
                continue;
            }
            for (slot, &y2) in self.yy[r * w + r..(r + 1) * w].iter_mut().zip(&y[r..]) {
                *slot += yr * y2 as i128;
            }
        }
        self.cells += 1;
        Ok(())
    }

    fn merge(&mut self, other: Moments) {
        for (into, from) in self.classes.iter_mut().zip(other.classes) {
            match (into.as_mut(), from) {
                (_, None) => {}
                (None, Some(f)) => *into = Some(f),
                (Some(i), Some(f)) => {
                    i.n += f.n;
                    for (a, b) in i.s.iter_mut().zip(&f.s).chain(i.y.iter_mut().zip(&f.y)).chain(i.q.iter_mut().zip(&f.q)).chain(i.m.iter_mut().zip(&f.m)) {
                        *a += b;
                    }
                }
            }
        }
        for (a, b) in self.yy.iter_mut().zip(&other.yy) {
            *a += b;
        }
        self.cells += other.cells;
    }

    /// The moments as text: the head line, the `YY` line, then one `CLASS` line per arriving class.
    fn text(&self, head: &str) -> String {
        let join = |v: &[i128]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
        let mut out = format!("{head} dims={} width={} alphabet={} cells={}\nYY {}\n", self.dims, self.width, self.classes.len(), self.cells, join(&upper(&self.yy, self.width)));
        for (u, c) in self.classes.iter().enumerate() {
            let Some(c) = c else { continue };
            out.push_str(&format!("CLASS {u} n={} s={} y={} q={} m={}\n", c.n, join(&c.s), join(&c.y), join(&upper(&c.q, self.dims)), join(&c.m)));
        }
        out
    }

    /// The moments of a `read-tower-situated-moments` file, with its head line.
    fn parse(text: &str) -> Result<(String, Moments)> {
        let mut lines = text.lines();
        let head = lines.next().ok_or("an empty moments file")?.to_string();
        if !head.starts_with("SITUATED_MOMENTS ") {
            return Err("a moments file opens with its SITUATED_MOMENTS line".into());
        }
        let (d, w) = (count(&head_field(&head, "dims")?)?, count(&head_field(&head, "width")?)?);
        let mut moments = Moments::new(count(&head_field(&head, "alphabet")?)?, d, w);
        moments.cells = count(&head_field(&head, "cells")?)?;
        let yy = numbers(lines.next().and_then(|l| l.strip_prefix("YY ")).ok_or("a moments file's second line is its YY line")?)?;
        if yy.len() != w * (w + 1) / 2 {
            return Err("the YY line has the wrong length".into());
        }
        moments.yy = from_upper(&yy, w);
        let mut counted = 0i128;
        for line in lines {
            let mut parts = line.split_whitespace();
            if parts.next() != Some("CLASS") {
                return Err("a moments line is not a CLASS line".into());
            }
            let u = count(parts.next().ok_or("a CLASS line names no class")?)?;
            let mut take = |key: &str, len: usize| -> Result<Vec<i128>> {
                let values = numbers(parts.next().and_then(|p| p.strip_prefix(key)).ok_or("a CLASS line's fields are short or out of order")?)?;
                if values.len() != len {
                    return Err("a CLASS field has the wrong length".into());
                }
                Ok(values)
            };
            let n = take("n=", 1)?[0];
            let (s, y) = (take("s=", d)?, take("y=", w)?);
            let q = from_upper(&take("q=", d * (d + 1) / 2)?, d);
            let m = take("m=", d * w)?;
            if n <= 0 || u >= moments.classes.len() || moments.classes[u].is_some() {
                return Err("a CLASS line repeats a class, names none of the alphabet, or counts no cell".into());
            }
            counted += n;
            moments.classes[u] = Some(ClassMoments { n, s, y, q, m });
        }
        if counted != moments.cells as i128 {
            return Err("the classes' counts do not sum to the moments' cells".into());
        }
        Ok((head, moments))
    }
}

/// The frozen tower reads `text` in `streams` streams, in sections of `section` cells, and keeps the
/// moments of level `level`'s carried face against each cell's input covector.
///
/// [agent-inferred, October 24] Each stream after the first opens one section early, from rest, and
/// counts none of that section's cells. Each level's read is the face's ratio to its power
/// (`ratio_to_power`), whose adjoint divides by the power, so just after rest, where the modes hold
/// one or two pushes, the covector a cell's input receives carries the inverse of a near-zero power:
/// read from rest at a stream's cut, the first cells' covectors reach 10^8 times a typical cell's
/// energy (the record's "The situated pool"), and the moments of the whole text are those few
/// cells. The section read before a cut brings the stream to the loudness the text keeps, as the
/// learner's own streams are; the first stream opens at the text's own start.
fn read_moments(tower: &Tower, text: &[usize], streams: usize, section: usize, level: usize) -> Result<Moments> {
    let (w, alphabet) = (tower.declaration.width, tower.declaration.alphabet);
    let dims = 2 * tower.declaration.modes;
    let chunk = text.len().div_ceil(streams);
    let cuts: Vec<(usize, usize)> = (0..streams).map(|s| (s * chunk, ((s + 1) * chunk).min(text.len()))).filter(|&(a, b)| a < b).collect();
    let read: Vec<Moments> = cuts
        .par_iter()
        .map(|&(start, end)| {
            let open = start.saturating_sub(section);
            let mut moments = Moments::new(alphabet, dims, w);
            let mut state = tower.rest();
            let mut at = open;
            tower
                .read_input_covectors(&mut state, &text[open..end], section, |cell| {
                    at += 1;
                    if at <= start {
                        return Ok(());
                    }
                    moments.add(cell.class, &cell.carried[level * dims..(level + 1) * dims], cell.covector).map_err(TowerError::Refused)
                })
                .map_err(|e| e.to_string())?;
            Ok(moments)
        })
        .collect::<std::result::Result<_, String>>()?;
    let mut merged = Moments::new(alphabet, dims, w);
    for m in read {
        merged.merge(m);
    }
    Ok(merged)
}

/// `x / d` rounded to nearest, `d > 0`.
fn div_round(x: &BigInt, d: &BigInt) -> BigInt {
    let twice: BigInt = x * 2;
    let span: BigInt = d * 2;
    if x.is_negative() {
        let up: BigInt = (d - twice) / &span;
        -up
    } else {
        (twice + d) / &span
    }
}

/// The least common multiple of the class counts.
fn lcm(ns: impl Iterator<Item = i128>) -> BigInt {
    ns.fold(BigInt::from(1), |l, n| {
        let n = BigInt::from(n);
        let g = gcd(&l, &n);
        &l / g * n
    })
}

fn gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let (mut a, mut b) = (a.abs(), b.abs());
    while !b.is_zero() {
        let r = &a % &b;
        a = b;
        b = r;
    }
    a
}

/// One class's moments centred on its own mean and scaled by its count: `n Σŝŝᵀ − ΣŝΣŝᵀ` (full)
/// and `n Σŝyᵀ − ΣŝΣyᵀ`, whose quotients by `n` are the within-class moments.
struct Centred {
    class: usize,
    n: i128,
    q: Vec<i128>,
    m: Vec<i128>,
}

/// A moment set read for the founding: the centred classes, `L` the lcm of their counts with each
/// class's `L/n_u`, the tension's metric `Y = Σyyᵀ` with `D_Y` and `D_Y·Y⁻¹` (its adjugate up to
/// sign), `Y⁻¹` released to below `2^60` its largest entry for the direction search, and the
/// share of `tr Y` that the class means carry.
struct Read {
    dims: usize,
    width: usize,
    classes: Vec<Centred>,
    l: BigInt,
    scales: Vec<BigInt>,
    gram: Vec<Vec<BigInt>>,
    gram_det: BigInt,
    gram_inverse: Vec<Vec<BigInt>>,
    metric: Vec<Vec<i64>>,
    diagonal: Vec<i128>,
    means_permille: String,
    cells: usize,
}

fn centred(moments: &Moments) -> Result<Read> {
    let (d, w) = (moments.dims, moments.width);
    let present: Vec<(usize, &ClassMoments)> = moments.classes.iter().enumerate().filter_map(|(u, c)| c.as_ref().map(|c| (u, c))).collect();
    let classes: Vec<Centred> = present
        .par_iter()
        .map(|&(u, c)| {
            let mut q = vec![0i128; d * d];
            for i in 0..d {
                for j in i..d {
                    let v = c.n.checked_mul(c.q[i * d + j]).and_then(|x| c.s[i].checked_mul(c.s[j]).and_then(|y| x.checked_sub(y)));
                    let v = v.ok_or("a centred moment outgrew its 128-bit carrier")?;
                    q[i * d + j] = v;
                    q[j * d + i] = v;
                }
            }
            let mut m = vec![0i128; d * w];
            for i in 0..d {
                for r in 0..w {
                    m[i * w + r] = c.n.checked_mul(c.m[i * w + r]).and_then(|x| c.s[i].checked_mul(c.y[r]).and_then(|y| x.checked_sub(y))).ok_or("a centred moment outgrew its 128-bit carrier")?;
                }
            }
            Ok(Centred { class: u, n: c.n, q, m })
        })
        .collect::<std::result::Result<_, &str>>()?;
    let l = lcm(present.iter().map(|(_, c)| c.n));
    let scales: Vec<BigInt> = classes.iter().map(|c| &l / c.n).collect();
    let gram: Vec<Vec<BigInt>> = (0..w).map(|r| (0..w).map(|r2| BigInt::from(moments.yy[r.min(r2) * w + r.max(r2)])).collect()).collect();
    let identity: Vec<Vec<BigInt>> = (0..w).map(|r| (0..w).map(|r2| BigInt::from((r == r2) as i64)).collect()).collect();
    let (gram_det, gram_inverse) = solve_scaled(&gram, &identity, false)?;
    let flat: Vec<BigInt> = gram_inverse.iter().flatten().cloned().collect();
    let released = release_big(&flat, 60);
    let metric = released.chunks(w).map(<[i64]>::to_vec).collect();
    let diagonal = (0..w).map(|r| moments.yy[r * w + r]).collect();
    let trace: BigInt = (0..w).map(|r| BigInt::from(moments.yy[r * w + r])).sum();
    let means: BigInt = present.iter().map(|(_, c)| c.y.iter().map(|&x| BigInt::from(x) * x).sum::<BigInt>() * (&l / c.n)).sum();
    let means_permille = permille(&means, &(trace * &l));
    Ok(Read { dims: d, width: w, classes, l, scales, gram, gram_det, gram_inverse, metric, diagonal, means_permille, cells: moments.cells })
}

/// A founded form's factors: `a` over the carried face, `b` over the arriving class's `x̂`.
#[derive(Clone)]
struct Form {
    a: Vec<i64>,
    b: Vec<i64>,
}

/// One form read on a moment set, beside the forms founded before it: per class `β_u = bᵀx̂_u`,
/// `z_u = Q̃_u a`, `w_u = M̃_uᵀ a`, and `a_kᵀ z_u` for each earlier form `k` and itself (so the
/// forms' Gram is read without reading the moments again).
struct FormRead {
    beta: Vec<i128>,
    z: Vec<Vec<i128>>,
    w: Vec<Vec<BigInt>>,
    inner: Vec<Vec<BigInt>>,
}

fn form_read(read: &Read, hats: &[Vec<i64>], form: &Form, before: &[Form]) -> Result<FormRead> {
    let (d, width) = (form.a.len(), read.width);
    let beta = read.classes.iter().map(|c| hats[c.class].iter().zip(&form.b).map(|(&x, &b)| x as i128 * b as i128).sum()).collect();
    let per: Vec<(Vec<i128>, Vec<BigInt>, Vec<BigInt>)> = read
        .classes
        .par_iter()
        .map(|c| {
            let z: Vec<i128> = (0..d)
                .map(|i| c.q[i * d..(i + 1) * d].iter().zip(&form.a).try_fold(0i128, |acc, (&q, &a)| q.checked_mul(a as i128).and_then(|p| acc.checked_add(p))).ok_or("a form's moment outgrew its 128-bit carrier"))
                .collect::<std::result::Result<_, &str>>()?;
            let w: Vec<BigInt> = (0..width).map(|r| (0..d).map(|i| BigInt::from(c.m[i * width + r]) * form.a[i]).sum()).collect();
            let inner: Vec<BigInt> = before.iter().chain(std::iter::once(form)).map(|f| f.a.iter().zip(&z).map(|(&a, &zz)| BigInt::from(zz) * a).sum()).collect();
            Ok((z, w, inner))
        })
        .collect::<std::result::Result<_, &str>>()?;
    let (mut z, mut w, mut inner) = (Vec::new(), Vec::new(), Vec::new());
    for (a, b, c) in per {
        z.push(a);
        w.push(b);
        inner.push(c);
    }
    Ok(FormRead { beta, z, w, inner })
}

/// The exact moments of a set of forms on a moment set, scaled by `L`: the Gram
/// `G_jk = Σ_u β_ju β_ku a_jᵀQ̃_u a_k (L/n_u)` and the cross `R_jr = Σ_u β_ju (M̃_uᵀ a_j)_r (L/n_u)`.
fn joint(read: &Read, reads: &[&FormRead]) -> (Vec<Vec<BigInt>>, Vec<Vec<BigInt>>) {
    let k = reads.len();
    let classes = read.classes.len();
    let lower: Vec<Vec<BigInt>> = (0..k)
        .into_par_iter()
        .map(|j| (0..=j).map(|kk| (0..classes).map(|u| &reads[j].inner[u][kk] * reads[j].beta[u] * reads[kk].beta[u] * &read.scales[u]).sum()).collect())
        .collect();
    let g = (0..k).map(|j| (0..k).map(|kk| if kk <= j { lower[j][kk].clone() } else { lower[kk][j].clone() }).collect()).collect();
    let r = (0..k)
        .into_par_iter()
        .map(|j| (0..read.width).map(|rr| (0..classes).map(|u| &reads[j].w[u][rr] * reads[j].beta[u] * &read.scales[u]).sum()).collect())
        .collect();
    (g, r)
}

/// A training fit: `D` and `D·P` with `G P = R`, and the canonical share
/// `s = tr(Y⁻¹ Rᵀ P)` the forms carry, as a numerator and denominator.
struct Fit {
    det: BigInt,
    dp: Vec<Vec<BigInt>>,
    share: BigInt,
    denominator: BigInt,
}

/// `tr(A Bᵀ C)` for `A` square over the covector and `B`, `C` with one row per form.
fn trace_through(a: &[Vec<BigInt>], b: &[Vec<BigInt>], c: &[Vec<BigInt>]) -> BigInt {
    let w = a.len();
    let bc: Vec<Vec<BigInt>> = (0..w).into_par_iter().map(|r| (0..w).map(|r2| b.iter().zip(c).map(|(bj, cj)| &bj[r] * &cj[r2]).sum()).collect()).collect();
    (0..w).into_par_iter().map(|r| (0..w).map(|r2| &a[r][r2] * &bc[r2][r]).sum::<BigInt>()).sum()
}

fn fit(read: &Read, reads: &[&FormRead]) -> Result<Fit> {
    let (g, r) = joint(read, reads);
    let (det, dp) = solve_scaled(&g, &r, true)?;
    let share = trace_through(&read.gram_inverse, &r, &dp);
    let denominator = &read.gram_det * &read.l * &det;
    Ok(Fit { det, dp, share, denominator })
}

/// The canonical share a held-out moment set keeps under the training lift, read to second order:
/// with the natural lift `−N Y⁻¹ Pᵀ` founded on the training text,
/// `s_h = (2N/N_h) tr(Y⁻¹PᵀR_h) − (N/N_h)² tr(P Y⁻¹ Y_h Y⁻¹ Pᵀ G_h)`, as a numerator and
/// denominator (twice the nats a held-out cell saves).
fn held_share(held: &Read, reads: &[&FormRead], train: &Read, trained: &Fit) -> (BigInt, BigInt) {
    let (g, r) = joint(held, reads);
    let (n, nh) = (BigInt::from(train.cells), BigInt::from(held.cells));
    let (det, dy) = (&trained.det, &train.gram_det);
    let cross = trace_through(&train.gram_inverse, &trained.dp, &r);
    let w = train.width;
    // B = Y⁻¹ Pᵀ (scaled by D_Y·D), one row per covector coordinate.
    let b: Vec<Vec<BigInt>> = (0..w).into_par_iter().map(|row| (0..reads.len()).map(|j| (0..w).map(|r2| &train.gram_inverse[row][r2] * &trained.dp[j][r2]).sum()).collect()).collect();
    // Bᵀ Y_h B: k × k.
    let yb: Vec<Vec<BigInt>> = (0..w).into_par_iter().map(|row| (0..reads.len()).map(|j| (0..w).map(|r2| &held.gram[row][r2] * &b[r2][j]).sum()).collect()).collect();
    let k = reads.len();
    let middle: Vec<Vec<BigInt>> = (0..k).map(|j| (0..k).map(|kk| (0..w).map(|row| &b[row][j] * &yb[row][kk]).sum()).collect()).collect();
    let quad: BigInt = (0..k).map(|j| (0..k).map(|kk| &middle[j][kk] * &g[kk][j]).sum::<BigInt>()).sum();
    let numerator = &n * &nh * dy * det * cross * 2 - &n * &n * quad;
    (numerator, &nh * &nh * dy * dy * det * det * &held.l)
}

fn permille(num: &BigInt, den: &BigInt) -> String {
    if den.is_zero() {
        return "0".into();
    }
    let scaled = div_round(&(num * 1000), den);
    format!("{scaled}")
}

/// The leading canonical direction of a block against the tension's metric: the generalized
/// eigenvector of `(Mᵀ Y⁻¹ M, Q)` by the power step `w = Q⁻¹Mᵀv`, `v ← Y⁻¹Mw`, on `M` and `Q`
/// released to below `2^60` their largest entry and `Y⁻¹` released (only directions are read),
/// each vector released to `2^15`; it stops when a step raises `(Mw)ᵀY⁻¹(Mw)/(wᵀQw)` by less than
/// `2^(−15)` of itself. Returns the factor and the carried `v`.
fn leading_canonical(dm: &[Vec<BigInt>], dq: &[Vec<BigInt>], metric: &[Vec<i64>], mut v: Vec<i64>) -> Result<(Vec<i64>, Vec<i64>)> {
    let (rows, q) = (dm.len(), dq.len());
    let mt = release_big(&dm.iter().flatten().cloned().collect::<Vec<_>>(), 60);
    let qt = release_big(&dq.iter().flatten().cloned().collect::<Vec<_>>(), 60);
    let qbig: Vec<Vec<BigInt>> = (0..q).map(|i| (0..q).map(|j| BigInt::from(qt[i * q + j])).collect()).collect();
    let identity: Vec<Vec<BigInt>> = (0..q).map(|i| (0..q).map(|j| BigInt::from((i == j) as i64)).collect()).collect();
    let (_, inverse) = solve_scaled(&qbig, &identity, false)?;
    let mut best: Option<(BigInt, BigInt, Vec<i64>, Vec<i64>)> = None;
    loop {
        let g: Vec<i128> = (0..q).map(|j| (0..rows).map(|a| mt[a * q + j] as i128 * v[a] as i128).sum()).collect();
        let wide: Vec<BigInt> = (0..q).map(|i| inverse[i].iter().zip(&g).map(|(x, &y)| x * y).sum()).collect();
        let w = release_big(&wide, 15);
        let u: Vec<i128> = (0..rows).map(|a| (0..q).map(|j| mt[a * q + j] as i128 * w[j] as i128).sum()).collect();
        let mu: Vec<BigInt> = (0..rows).map(|a| (0..rows).map(|b| BigInt::from(metric[a][b]) * u[b]).sum()).collect();
        let num: BigInt = mu.iter().zip(&u).map(|(x, &y)| x * y).sum();
        let den: BigInt = (0..q).map(|i| (0..q).map(|j| BigInt::from(qt[i * q + j] as i128 * w[i] as i128) * w[j]).sum::<BigInt>()).sum();
        v = release_big(&mu, 15);
        if den <= BigInt::from(0) || w.iter().all(|&x| x == 0) {
            break;
        }
        let gained = match &best {
            None => true,
            Some((bn, bd, _, _)) => (&num * bd) << 15u32 > bn * &den * ((1i64 << 15) + 1),
        };
        if best.as_ref().is_none_or(|(bn, bd, _, _)| &num * bd > bn * &den) {
            best = Some((num, den, w, v.clone()));
        }
        if !gained {
            break;
        }
    }
    let (_, _, w, v) = best.ok_or("the power step found no direction")?;
    Ok((w, v))
}

/// The a-step: with `b` held, the leading canonical direction over the carried face of the
/// deflated centred moments `Q_b = Σ_u β_u² Q̃_u/n_u`, `M_b = Σ_u β_u M̃'_u/n_u` (each `β_u`
/// released to `2^15`; only directions are read here).
fn a_step(read: &Read, deflated: &[Vec<i128>], hats: &[Vec<i64>], b: &[i64], v: Vec<i64>) -> Result<(Vec<i64>, Vec<i64>)> {
    let (dims, width) = (read.dims, read.width);
    let betas: Vec<i128> = read.classes.iter().map(|c| hats[c.class].iter().zip(b).map(|(&x, &bb)| x as i128 * bb as i128).sum()).collect();
    let rel = release_wide(&betas, 15);
    let ns: Vec<BigInt> = read.classes.iter().map(|c| BigInt::from(c.n)).collect();
    let dq: Vec<Vec<BigInt>> = (0..dims)
        .into_par_iter()
        .map(|i| (0..dims).map(|j| (0..read.classes.len()).filter(|&u| rel[u] != 0).map(|u| div_round(&(BigInt::from(read.classes[u].q[i * dims + j]) * rel[u] * rel[u]), &ns[u])).sum()).collect())
        .collect();
    let dm: Vec<Vec<BigInt>> = (0..width)
        .into_par_iter()
        .map(|r| (0..dims).map(|i| (0..read.classes.len()).filter(|&u| rel[u] != 0).map(|u| div_round(&(BigInt::from(deflated[u][i * width + r]) * rel[u]), &ns[u])).sum()).collect())
        .collect();
    leading_canonical(&dm, &dq, &read.metric, v)
}

/// The b-step: with `a` held, the leading canonical direction over `x̂` of
/// `N = Σ_u x̂_u (M̃'_uᵀa)ᵀ/n_u` against `C = Σ_u (aᵀQ̃_u a/n_u) x̂_u x̂_uᵀ`.
fn b_step(read: &Read, deflated: &[Vec<i128>], hats: &[Vec<i64>], a: &[i64], v: Vec<i64>) -> Result<(Vec<i64>, Vec<i64>)> {
    let (dims, width, hat) = (read.dims, read.width, hats[0].len());
    let per: Vec<(BigInt, Vec<BigInt>)> = read
        .classes
        .par_iter()
        .zip(deflated)
        .map(|(c, m)| {
            let n = BigInt::from(c.n);
            let quad: BigInt = (0..dims).map(|i| BigInt::from(a[i]) * (0..dims).map(|j| BigInt::from(c.q[i * dims + j]) * a[j]).sum::<BigInt>()).sum();
            let lin: Vec<BigInt> = (0..width).map(|r| div_round(&(0..dims).map(|i| BigInt::from(m[i * width + r]) * a[i]).sum::<BigInt>(), &n)).collect();
            (div_round(&quad, &n), lin)
        })
        .collect();
    let dm: Vec<Vec<BigInt>> = (0..width).into_par_iter().map(|r| (0..hat).map(|j| read.classes.iter().zip(&per).map(|(c, (_, lin))| &lin[r] * hats[c.class][j]).sum()).collect()).collect();
    let dq: Vec<Vec<BigInt>> = (0..hat)
        .into_par_iter()
        .map(|i| (0..hat).map(|j| read.classes.iter().zip(&per).map(|(c, (quad, _))| quad * hats[c.class][i] * hats[c.class][j]).sum()).collect())
        .collect();
    leading_canonical(&dm, &dq, &read.metric, v)
}

/// The centred moments less the founded forms' lift, `M̃'_u = M̃_u − Σ_j β_ju z_uj P_jᵀ` with
/// `P = D·P/D`, rounded (directions only).
fn deflate(read: &Read, reads: &[FormRead], fitted: &Fit) -> Result<Vec<Vec<i128>>> {
    use num_traits::ToPrimitive;
    let (dims, width) = (read.dims, read.width);
    read.classes
        .par_iter()
        .enumerate()
        .map(|(u, c)| {
            let lifts: Vec<Vec<BigInt>> = reads.iter().zip(&fitted.dp).map(|(f, p)| p.iter().map(|x| x * f.beta[u]).collect()).collect();
            let mut out = vec![0i128; dims * width];
            for i in 0..dims {
                for r in 0..width {
                    let lift: BigInt = reads.iter().zip(&lifts).map(|(f, l)| &l[r] * f.z[u][i]).sum();
                    let v = div_round(&(BigInt::from(c.m[i * width + r]) * &fitted.det - lift), &fitted.det);
                    out[i * width + r] = v.to_i128().ok_or("a deflated moment outgrew its 128-bit carrier")?;
                }
            }
            Ok(out)
        })
        .collect::<std::result::Result<_, &str>>()
        .map_err(Into::into)
}

/// Per class, the part of the canonical share it carries,
/// `s_u = 2 tr(Y⁻¹ Pᵀ R_u) − tr(P Y⁻¹ Pᵀ G_u)` (the parts sum to `s`), as numerators over
/// `D² D_Y n_u`: `2D Σ_j β_ju (DP_j Y⁻¹ M̃_uᵀa_j) − Σ_jk β_ju β_ku (a_jᵀQ̃_u a_k)(DP_j Y⁻¹ DP_kᵀ)`
/// with `Y⁻¹` its scaled inverse.
fn share_per_class(read: &Read, reads: &[FormRead], fitted: &Fit) -> Vec<BigInt> {
    let (k, w) = (reads.len(), read.width);
    let pa: Vec<Vec<BigInt>> = (0..k).map(|j| (0..w).map(|r| (0..w).map(|r2| &read.gram_inverse[r][r2] * &fitted.dp[j][r2]).sum()).collect()).collect();
    let cross: Vec<Vec<BigInt>> = (0..k).map(|j| (0..k).map(|kk| fitted.dp[j].iter().zip(&pa[kk]).map(|(x, y)| x * y).sum()).collect()).collect();
    (0..read.classes.len())
        .into_par_iter()
        .map(|u| {
            let lin: BigInt = (0..k).map(|j| reads[j].w[u].iter().zip(&pa[j]).map(|(x, y)| x * y).sum::<BigInt>() * reads[j].beta[u]).sum();
            let quad: BigInt = (0..k)
                .map(|j| (0..k).map(|kk| if kk <= j { &reads[j].inner[u][kk] } else { &reads[kk].inner[u][j] } * reads[j].beta[u] * reads[kk].beta[u] * &cross[j][kk]).sum::<BigInt>())
                .sum();
            lin * &fitted.det * 2 - quad
        })
        .collect()
}

/// The checked head of a moments file read on this tower: its level.
fn moments_level(head: &str, tower: &Tower, state_sha: &str) -> Result<usize> {
    let level = count(&head_field(head, "level")?)?;
    if head_field(head, "state_sha256")? != state_sha {
        return Err("the moments were read on another tower state".into());
    }
    if level >= tower.declaration.levels || count(&head_field(head, "dims")?)? != 2 * tower.declaration.modes || count(&head_field(head, "width")?)? != tower.declaration.width {
        return Err("the moments were read on another tower's shape".into());
    }
    Ok(level)
}

/// `read-tower-situated-moments STATE STATE_SHA TEXT TEXT_SHA STREAMS SECTION LEVEL OUT`: the
/// frozen tower reads `TEXT` in `STREAMS` streams, each after the first opening one section early
/// ([`read_moments`]), in sections of `SECTION` cells as the learner reads it, and the moments of
/// level `LEVEL`'s carried face against each cell's input covector, per arriving class, are written
/// to `OUT` (create-new).
pub(super) fn read_tower_situated_moments(args: &[String]) -> Result<()> {
    if args.len() != 9 {
        return Err("read-tower-situated-moments STATE STATE_SHA TEXT TEXT_SHA STREAMS SECTION LEVEL OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let (streams, section) = (positive(&args[5])?, positive(&args[6])?);
    let level = count(&args[7])?;
    let tower = &learner.tower;
    if level >= tower.declaration.levels {
        return Err("LEVEL names no level of the tower".into());
    }
    if text.is_empty() {
        return Err("TEXT holds no class".into());
    }
    if std::path::Path::new(&args[8]).exists() {
        return Err("OUT exists: the moments are written create-new".into());
    }
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let moments = read_moments(tower, &classes, streams, section, level)?;
    let out = moments.text(&format!("SITUATED_MOMENTS level={level} streams={streams} section={section} state_sha256={} text_sha256={}", args[2], args[4]));
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(&args[8])?;
    std::io::Write::write_all(&mut file, out.as_bytes())?;
    println!(
        "SITUATED_MOMENTS cells={} classes={} read_ms={} sha256={}",
        moments.cells,
        moments.classes.iter().flatten().count(),
        started.elapsed().as_millis(),
        sha256(out.as_bytes())?
    );
    Ok(())
}

/// `found-tower-situated STATE STATE_SHA TRAIN_MOMENTS TRAIN_MOMENTS_SHA HELD_MOMENTS
/// HELD_MOMENTS_SHA FORMS OUT [FROM FROM_SHA]`: found situated forms from the training moments up
/// to `FORMS` in all, read each rank's canonical share on the training and held-out moments, and
/// write each form to `OUT` (create-new) as it is founded. `FROM`, a forms file founded on the same
/// moments, supplies the first forms: they are read again, copied to `OUT` and deflated, and the
/// founding continues from the next rank. Shares are in thousandths, rounded: the sum of the
/// squared canonical correlations, twice the nats a cell saves; `serves` names the classes carrying
/// most of the training share, each with its part.
pub(super) fn found_tower_situated(args: &[String]) -> Result<()> {
    if args.len() != 9 && args.len() != 11 {
        return Err("found-tower-situated STATE STATE_SHA TRAIN_MOMENTS TRAIN_MOMENTS_SHA HELD_MOMENTS HELD_MOMENTS_SHA FORMS OUT [FROM FROM_SHA]".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let (train_head, train_moments) = Moments::parse(std::str::from_utf8(&pinned_read(&args[3], &args[4], STATE_BUDGET)?)?)?;
    let (held_head, held_moments) = Moments::parse(std::str::from_utf8(&pinned_read(&args[5], &args[6], STATE_BUDGET)?)?)?;
    let ranks = positive(&args[7])?;
    let level = moments_level(&train_head, tower, &args[2])?;
    if moments_level(&held_head, tower, &args[2])? != level {
        return Err("the training and held-out moments were read on different levels".into());
    }
    if std::path::Path::new(&args[8]).exists() {
        return Err("OUT exists: the forms are written create-new".into());
    }
    let width = tower.declaration.width;
    let train_read = centred(&train_moments)?;
    let held_read = centred(&held_moments)?;
    drop((train_moments, held_moments));
    println!(
        "SITUATED_PASS train_cells={} held_out_cells={} train_classes={} held_out_classes={} dims={} width={width} class_means_permille_of_covector_energy={} held_out_class_means_permille={} read_ms={}",
        train_read.cells,
        held_read.cells,
        train_read.classes.len(),
        held_read.classes.len(),
        train_read.dims,
        train_read.means_permille,
        held_read.means_permille,
        started.elapsed().as_millis()
    );
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(&args[8])?;
    std::io::Write::write_all(&mut file, format!("SITUATED level={level} dims={} width={width} state_sha256={} moments_sha256={}\n", train_read.dims, args[2], args[4]).as_bytes())?;
    let (hats, _) = pair_hats(tower);
    let mut forms: Vec<Form> = Vec::new();
    let mut reads: Vec<FormRead> = Vec::new();
    let mut held_reads: Vec<FormRead> = Vec::new();
    let mut deflated: Vec<Vec<i128>> = train_read.classes.iter().map(|c| c.m.clone()).collect();
    // The forms a founding on these same moments already wrote, read again and deflated before the
    // next rank is searched: the search is the founding's cost, the reading of a known form is not.
    if args.len() == 11 {
        let text = String::from_utf8(pinned_read(&args[9], &args[10], READ_BUDGET as usize)?)?;
        let head = text.lines().next().unwrap_or_default();
        if head_field(head, "moments_sha256")? != args[4] || head_field(head, "state_sha256")? != args[2] {
            return Err("FROM was founded on other moments or another tower state".into());
        }
        let (from_level, known) = parse_forms(&text, tower)?;
        if from_level != level || known.len() > ranks {
            return Err("FROM was founded on another level, or holds more forms than FORMS".into());
        }
        for (form, shift) in known {
            reads.push(form_read(&train_read, &hats, &form, &forms)?);
            held_reads.push(form_read(&held_read, &hats, &form, &forms)?);
            let join = |v: &[i64]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
            std::io::Write::write_all(&mut file, format!("FORM {} shift={shift} a={} b={}\n", forms.len(), join(&form.a), join(&form.b)).as_bytes())?;
            forms.push(form);
        }
        file.sync_data()?;
        let trained = fit(&train_read, &reads.iter().collect::<Vec<_>>())?;
        let (hnum, hden) = held_share(&held_read, &held_reads.iter().collect::<Vec<_>>(), &train_read, &trained);
        println!(
            "SITUATED_FROM forms={} train_canonical_permille={} held_out_canonical_permille={} elapsed_ms={}",
            forms.len(),
            permille(&trained.share, &trained.denominator),
            permille(&hnum, &hden),
            started.elapsed().as_millis()
        );
        if forms.len() < ranks {
            deflated = deflate(&train_read, &reads, &trained)?;
        }
    }
    let unit: Vec<i64> = (0..=width).map(|j| (j == width) as i64).collect();
    // Each rank starts at the covector coordinate with the most tension, `b` the unit.
    let top = (0..width).max_by(|&x, &y| train_read.diagonal[x].cmp(&train_read.diagonal[y])).unwrap_or(0);
    for rank in forms.len() + 1..=ranks {
        let mut v: Vec<i64> = (0..width).map(|r| (r == top) as i64).collect();
        let mut b = unit.clone();
        let mut best: Option<(BigInt, BigInt, Form)> = None;
        let mut steps = 0;
        loop {
            steps += 1;
            let (a, v1) = a_step(&train_read, &deflated, &hats, &b, v)?;
            let (b1, v2) = b_step(&train_read, &deflated, &hats, &a, v1)?;
            v = v2;
            b = b1.clone();
            let candidate = Form { a, b: b1 };
            let own = form_read(&train_read, &hats, &candidate, &forms)?;
            let trial: Vec<&FormRead> = reads.iter().chain(std::iter::once(&own)).collect();
            let trial_fit = fit(&train_read, &trial)?;
            let (num, den) = (trial_fit.share, trial_fit.denominator);
            let gained = match &best {
                None => true,
                Some((bn, bd, _)) => (&num * bd) << 15u32 > bn * &den * ((1i64 << 15) + 1),
            };
            if best.as_ref().is_none_or(|(bn, bd, _)| &num * bd > bn * &den) {
                best = Some((num, den, candidate));
            }
            if !gained {
                break;
            }
        }
        let (_, _, form) = best.ok_or("the alternation founded no form")?;
        reads.push(form_read(&train_read, &hats, &form, &forms)?);
        held_reads.push(form_read(&held_read, &hats, &form, &forms)?);
        forms.push(form);
        let trained = fit(&train_read, &reads.iter().collect::<Vec<_>>())?;
        let (hnum, hden) = held_share(&held_read, &held_reads.iter().collect::<Vec<_>>(), &train_read, &trained);
        // The classes carrying most of the training share, each with its part of it.
        let per = share_per_class(&train_read, &reads, &trained);
        let mut served: Vec<(BigInt, usize)> = per.iter().zip(&train_read.classes).enumerate().map(|(u, (x, c))| (div_round(&(x * &train_read.l), &BigInt::from(c.n)), u)).collect();
        served.sort_by(|x, y| y.0.cmp(&x.0));
        let named: Vec<String> = served.iter().take(6).map(|(x, u)| format!("{}:{}", class_label(train_read.classes[*u].class), permille(x, &(&trained.det * &trained.share)))).collect();
        println!(
            "SITUATED_RANK rank={rank} steps={steps} train_canonical_permille={} held_out_canonical_permille={} serves={} elapsed_ms={}",
            permille(&trained.share, &trained.denominator),
            permille(&hnum, &hden),
            named.join(","),
            started.elapsed().as_millis()
        );
        // The form's release for a reading: its training values' within-class root mean square
        // brought to below 2^16.
        let last = reads.last().expect("a founded form");
        let j = reads.len() - 1;
        let total: BigInt = train_read.classes.iter().enumerate().map(|(u, c)| div_round(&(&last.inner[u][j] * last.beta[u] * last.beta[u]), &BigInt::from(c.n))).sum();
        let mean_square = total / BigInt::from(train_read.cells.max(1));
        let shift = mean_square.bits().div_ceil(2).saturating_sub(16);
        let join = |v: &[i64]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
        let form = forms.last().expect("a founded form");
        std::io::Write::write_all(&mut file, format!("FORM {j} shift={shift} a={} b={}\n", join(&form.a), join(&form.b)).as_bytes())?;
        file.sync_data()?;
        if rank < ranks {
            deflated = deflate(&train_read, &reads, &trained)?;
        }
    }
    drop(file);
    let written = std::fs::read(&args[8])?;
    println!("SITUATED_WRITTEN forms={} sha256={} elapsed_ms={}", forms.len(), sha256(&written)?, started.elapsed().as_millis());
    Ok(())
}

fn class_label(u: usize) -> String {
    match u as u8 {
        b'\n' => "\\n".into(),
        b' ' => "␠".into(),
        b',' => "comma".into(),
        c if c.is_ascii_graphic() => (c as char).to_string(),
        c => format!("0x{c:02x}"),
    }
}

/// The forms of a `found-tower-situated` file, checked against the tower they are read on.
fn parse_forms(text: &str, tower: &Tower) -> Result<(usize, Vec<(Form, u64)>)> {
    let mut lines = text.lines();
    let head = lines.next().ok_or("an empty forms file")?;
    let field = |line: &str, key: &str| -> Option<String> { line.split_whitespace().find_map(|f| f.strip_prefix(&format!("{key}=")).map(str::to_string)) };
    if !head.starts_with("SITUATED ") {
        return Err("a forms file opens with its SITUATED line".into());
    }
    let level = count(&field(head, "level").ok_or("no level")?)?;
    let (dims, width) = (count(&field(head, "dims").ok_or("no dims")?)?, count(&field(head, "width").ok_or("no width")?)?);
    if level >= tower.declaration.levels || dims != 2 * tower.declaration.modes || width != tower.declaration.width {
        return Err("the forms were founded on another tower's shape".into());
    }
    let parse = |s: String| -> Result<Vec<i64>> { s.split(',').map(|x| Ok(x.parse::<i64>()?)).collect() };
    let mut forms = Vec::new();
    for line in lines.filter(|l| l.starts_with("FORM ")) {
        let shift = field(line, "shift").ok_or("no shift")?.parse::<u64>()?;
        let (a, b) = (parse(field(line, "a").ok_or("no a")?)?, parse(field(line, "b").ok_or("no b")?)?);
        if a.len() != dims || b.len() != width + 1 {
            return Err("a form's factors have the wrong lengths".into());
        }
        forms.push((Form { a, b }, shift));
    }
    if forms.is_empty() {
        return Err("a forms file with no form".into());
    }
    Ok((level, forms))
}

/// [agent-inferred, October 24] `read-tower-situated STATE STATE_SHA FORMS FORMS_SHA TEXT TEXT_SHA
/// CELLS CELLS_SHA`: the frozen tower reads `TEXT` as one passage from rest, and at each named cell
/// the situated forms' values are printed, `FORMS i class v₁ … v_k`, each `c = (aᵀŝ)(bᵀx̂)` (the
/// state the cell's class meets on its level, the class's encoding with the unit) released by its
/// form's shift, rounded to nearest. A reading beside the code: the tower is not moved.
pub(super) fn read_tower_situated(args: &[String]) -> Result<()> {
    if args.len() != 9 {
        return Err("read-tower-situated STATE STATE_SHA FORMS FORMS_SHA TEXT TEXT_SHA CELLS CELLS_SHA".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let (level, forms) = parse_forms(std::str::from_utf8(&pinned_read(&args[3], &args[4], READ_BUDGET as usize)?)?, tower)?;
    let text = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let cells: Vec<usize> = std::str::from_utf8(&pinned_read(&args[7], &args[8], READ_BUDGET as usize)?)?.split_whitespace().map(count).collect::<Result<_>>()?;
    let Some(&last) = cells.last() else {
        return Err("CELLS names no cell".into());
    };
    if cells.windows(2).any(|w| w[0] >= w[1]) || last + 1 >= classes.len() {
        return Err("CELLS must ascend and code a class inside the passage".into());
    }
    let (hats, _) = pair_hats(tower);
    let mut state = tower.rest();
    let mut next = 0;
    tower
        .read_circuit(&mut state, &classes[..last + 2], |i, cell| {
            use std::fmt::Write as _;
            if cells.get(next) != Some(&i) {
                return Ok(());
            }
            next += 1;
            let before: Vec<(i64, i64)> = cell.levels[level].modes.iter().map(|m| m.before).collect();
            let face = carried_face(&[before])?;
            let mut line = format!("FORMS {i} {}", classes[i]);
            for (form, shift) in &forms {
                let alpha: i128 = form.a.iter().zip(&face).map(|(&a, &s)| a as i128 * s as i128).sum();
                let beta: i128 = form.b.iter().zip(&hats[classes[i]]).map(|(&b, &x)| b as i128 * x as i128).sum();
                let value = BigInt::from(alpha) * beta;
                let released = if *shift == 0 { value } else { div_round(&value, &(BigInt::from(1) << *shift)) };
                let _ = write!(line, " {released}");
            }
            println!("{line}");
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    Ok(())
}

/// [agent-inferred, October 24] `read-tower-input-covectors STATE STATE_SHA TEXT TEXT_SHA CELLS
/// CELLS_SHA SECTION`: the frozen tower reads `TEXT` as one passage from rest, in sections of
/// `SECTION` cells as the learner reads it, and at each named cell prints the covector its reverse
/// sends to the cell's input, `FORMS i class y₁ … y_w` (on the covector's `2^(−24)`): the tension
/// of the section's later faces carried back to where the class arrived. A reading beside the
/// code: whether a later face's error reaches an earlier cell at all.
pub(super) fn read_tower_input_covectors(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("read-tower-input-covectors STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA SECTION".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let cells: Vec<usize> = std::str::from_utf8(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?.split_whitespace().map(count).collect::<Result<_>>()?;
    let section = positive(&args[7])?;
    let Some(&last) = cells.last() else {
        return Err("CELLS names no cell".into());
    };
    if cells.windows(2).any(|w| w[0] >= w[1]) || last + 1 >= classes.len() {
        return Err("CELLS must ascend and code a class inside the passage".into());
    }
    let mut state = tower.rest();
    let (mut at, mut next) = (0usize, 0usize);
    tower
        .read_input_covectors(&mut state, &classes, section, |cell| {
            use std::fmt::Write as _;
            let i = at;
            at += 1;
            if cells.get(next) != Some(&i) {
                return Ok(());
            }
            next += 1;
            let mut line = format!("FORMS {i} {}", cell.class);
            for y in cell.covector {
                let _ = write!(line, " {y}");
            }
            println!("{line}");
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    if next != cells.len() {
        return Err("a named cell was not read".into());
    }
    Ok(())
}
