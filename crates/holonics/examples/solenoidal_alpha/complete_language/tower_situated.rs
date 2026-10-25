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
//! more than a prose letter it nearly knows. The two factors alternate, each the leading canonical
//! direction of its block ([`leading_canonical`]). Directions are searched on released copies;
//! every share is read exactly from the moments.
//!
//! [agent-inferred, October 24] The factors are complex, `a = a₀ + i a₁` and `b = b₀ + i b₁` over
//! the Gaussian integers, and both faces of `c` are channels: `Re c = β₀ a₀ᵀŝ − β₁ a₁ᵀŝ` and
//! `Im c = β₁ a₀ᵀŝ + β₀ a₁ᵀŝ`, `β_k = b_kᵀx̂`. A sum's units are a character product,
//! `e^(2πik c₀/10) = e^(2πik a₀/10) e^(2πik b₀/10)`, rank one over the complex numbers and rank two
//! over the reals, so a real form holds at most half of a crossing that turns (the record's "The
//! situated pool": sixteen real forms tie each operand where it arrives, 481 of 495, and read the
//! sum's units where the second operand arrives in 75). Each rank searches from the unit (`b` the
//! unit, which stays real) and from a ring ([`ring_seed`]) and founds the larger exact training
//! share; a form whose two faces are one reading keeps the larger.

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
pub(super) fn div_round(x: &BigInt, d: &BigInt) -> BigInt {
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
pub(super) fn lcm(ns: impl Iterator<Item = i128>) -> BigInt {
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

/// A founded form's factors, each complex: `a = a₀ + i a₁` over the carried face and
/// `b = b₀ + i b₁` over the arriving class's `x̂`, with the faces of `c = (aᵀŝ)(bᵀx̂)` it keeps,
/// `Re c` and `Im c`.
#[derive(Clone)]
struct Form {
    a: [Vec<i64>; 2],
    b: [Vec<i64>; 2],
    faces: [bool; 2],
}

impl Form {
    /// The real channels of the kept faces, each a sum of terms `±β_k a_tᵀŝ` on the form's own
    /// parts (`t`, `k`: 0 real, 1 imaginary; `β_k = b_kᵀx̂`), `Re c = β₀ a₀ᵀŝ − β₁ a₁ᵀŝ` and
    /// `Im c = β₁ a₀ᵀŝ + β₀ a₁ᵀŝ`. A term on a zero part is left out, and a face with no term.
    fn channels(&self) -> Vec<Vec<(usize, usize, bool)>> {
        self.terms().into_iter().zip(self.faces).filter(|(terms, kept)| *kept && !terms.is_empty()).map(|(terms, _)| terms).collect()
    }

    /// Each face's terms on the form's nonzero parts.
    fn terms(&self) -> [Vec<(usize, usize, bool)>; 2] {
        let live = |v: &Vec<i64>| v.iter().any(|&x| x != 0);
        let (a, b) = ([live(&self.a[0]), live(&self.a[1])], [live(&self.b[0]), live(&self.b[1])]);
        [vec![(0, 0, false), (1, 1, true)], vec![(0, 1, false), (1, 0, false)]].map(|terms| terms.into_iter().filter(|&(t, k, _)| a[t] && b[k]).collect())
    }

    /// The faces that have a term: a real form (`a₁ = b₁ = 0`) has only `Re c`.
    fn live_faces(&self) -> [bool; 2] {
        self.terms().map(|terms| !terms.is_empty())
    }

    fn line(&self, j: usize, shift: u64) -> String {
        let join = |v: &[i64]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
        let faces: Vec<&str> = ["re", "im"].into_iter().zip(self.faces).filter(|(_, kept)| *kept).map(|(name, _)| name).collect();
        format!("FORM {j} shift={shift} faces={} a={} ai={} b={} bi={}\n", faces.join(","), join(&self.a[0]), join(&self.a[1]), join(&self.b[0]), join(&self.b[1]))
    }
}

/// One factor `a_t` read on a moment set beside the factors read before it: per class
/// `z = Q̃_u a_t`, `w = M̃_uᵀ a_t`, and `a_sᵀ z` for each earlier factor `s` and itself (so the
/// channels' Gram is read without reading the moments again).
struct AtomRead {
    z: Vec<Vec<i128>>,
    w: Vec<Vec<BigInt>>,
    inner: Vec<Vec<BigInt>>,
}

fn atom_read(read: &Read, a: &[i64], earlier: &[&[i64]]) -> Result<AtomRead> {
    let (d, width) = (a.len(), read.width);
    let per: Vec<(Vec<i128>, Vec<BigInt>, Vec<BigInt>)> = read
        .classes
        .par_iter()
        .map(|c| {
            let z: Vec<i128> = (0..d)
                .map(|i| c.q[i * d..(i + 1) * d].iter().zip(a).try_fold(0i128, |acc, (&q, &x)| q.checked_mul(x as i128).and_then(|p| acc.checked_add(p))).ok_or("a form's moment outgrew its 128-bit carrier"))
                .collect::<std::result::Result<_, &str>>()?;
            let w: Vec<BigInt> = (0..width).map(|r| (0..d).map(|i| BigInt::from(c.m[i * width + r]) * a[i]).sum()).collect();
            let inner: Vec<BigInt> = earlier.iter().copied().chain(std::iter::once(a)).map(|s| s.iter().zip(&z).map(|(&x, &zz)| BigInt::from(zz) * x).sum()).collect();
            Ok((z, w, inner))
        })
        .collect::<std::result::Result<_, &str>>()?;
    let (mut z, mut w, mut inner) = (Vec::new(), Vec::new(), Vec::new());
    for (a, b, c) in per {
        z.push(a);
        w.push(b);
        inner.push(c);
    }
    Ok(AtomRead { z, w, inner })
}

/// The founded forms read on one moment set: per form its `β_k = b_kᵀx̂_u` per class and its two
/// factors' reads (form `f` owns the factors and `β`s `2f` and `2f + 1`), and the real channels of
/// every form's kept faces, each with its form and its terms `(factor, β, negated)`.
#[derive(Default)]
struct Reads {
    betas: Vec<Vec<i128>>,
    atoms: Vec<AtomRead>,
    channels: Vec<(usize, Vec<(usize, usize, bool)>)>,
}

impl Reads {
    /// Read one more form on `read`, beside the forms `before` it.
    fn push(&mut self, read: &Read, hats: &[Vec<i64>], form: &Form, before: &[Form]) -> Result<()> {
        let f = before.len();
        for b in &form.b {
            self.betas.push(read.classes.iter().map(|c| hats[c.class].iter().zip(b).map(|(&x, &bb)| x as i128 * bb as i128).sum()).collect());
        }
        let mut earlier: Vec<&[i64]> = before.iter().flat_map(|g| g.a.iter().map(Vec::as_slice)).collect();
        for a in &form.a {
            self.atoms.push(atom_read(read, a, &earlier)?);
            earlier.push(a);
        }
        for terms in form.channels() {
            self.channels.push((f, terms.into_iter().map(|(t, k, negated)| (2 * f + t, 2 * f + k, negated)).collect()));
        }
        Ok(())
    }

    /// Forget every form from the `forms`-th on.
    fn truncate(&mut self, forms: usize) {
        self.betas.truncate(2 * forms);
        self.atoms.truncate(2 * forms);
        self.channels.retain(|(f, _)| *f < forms);
    }

    fn inner(&self, u: usize, s: usize, t: usize) -> &BigInt {
        if s >= t {
            &self.atoms[s].inner[u][t]
        } else {
            &self.atoms[t].inner[u][s]
        }
    }

    fn coefficient(&self, u: usize, k: usize, negated: bool) -> i128 {
        if negated {
            -self.betas[k][u]
        } else {
            self.betas[k][u]
        }
    }

    /// Class `u`'s part of two channels' Gram, `Σ ±β ±β' a_sᵀQ̃_u a_t` over their terms.
    fn class_gram(&self, u: usize, j: usize, k: usize) -> BigInt {
        let mut acc = BigInt::zero();
        for &(s, ks, ns) in &self.channels[j].1 {
            for &(t, kt, nt) in &self.channels[k].1 {
                acc += self.inner(u, s, t) * self.coefficient(u, ks, ns) * self.coefficient(u, kt, nt);
            }
        }
        acc
    }

    /// Class `u`'s part of a channel's cross moment at covector coordinate `r`, `Σ ±β (M̃_uᵀa_t)_r`.
    fn class_cross(&self, u: usize, j: usize, r: usize) -> BigInt {
        self.channels[j].1.iter().map(|&(t, k, negated)| &self.atoms[t].w[u][r] * self.coefficient(u, k, negated)).sum()
    }
}

/// The exact moments of the channels on a moment set, scaled by `L`: the Gram
/// `G_jk = Σ_u class_gram(u, j, k) (L/n_u)` and the cross `R_jr = Σ_u class_cross(u, j, r) (L/n_u)`.
fn joint(read: &Read, reads: &Reads) -> (Vec<Vec<BigInt>>, Vec<Vec<BigInt>>) {
    let k = reads.channels.len();
    let classes = read.classes.len();
    let lower: Vec<Vec<BigInt>> = (0..k).into_par_iter().map(|j| (0..=j).map(|kk| (0..classes).map(|u| reads.class_gram(u, j, kk) * &read.scales[u]).sum()).collect()).collect();
    let g = (0..k).map(|j| (0..k).map(|kk| if kk <= j { lower[j][kk].clone() } else { lower[kk][j].clone() }).collect()).collect();
    let r = (0..k).into_par_iter().map(|j| (0..read.width).map(|rr| (0..classes).map(|u| reads.class_cross(u, j, rr) * &read.scales[u]).sum()).collect()).collect();
    (g, r)
}

/// A training fit: the channels' Gram `G`, `D` and `D·P` with `G P = R`, and the canonical share
/// `s = tr(Y⁻¹ Rᵀ P)` they carry, as a numerator and denominator.
struct Fit {
    g: Vec<Vec<BigInt>>,
    det: BigInt,
    dp: Vec<Vec<BigInt>>,
    share: BigInt,
    denominator: BigInt,
}

/// `tr(A Bᵀ C)` for `A` square over the covector and `B`, `C` with one row per channel.
fn trace_through(a: &[Vec<BigInt>], b: &[Vec<BigInt>], c: &[Vec<BigInt>]) -> BigInt {
    let w = a.len();
    let bc: Vec<Vec<BigInt>> = (0..w).into_par_iter().map(|r| (0..w).map(|r2| b.iter().zip(c).map(|(bj, cj)| &bj[r] * &cj[r2]).sum()).collect()).collect();
    (0..w).into_par_iter().map(|r| (0..w).map(|r2| &a[r][r2] * &bc[r2][r]).sum::<BigInt>()).sum()
}

fn fit(read: &Read, reads: &Reads) -> Result<Fit> {
    let (g, r) = joint(read, reads);
    let (det, dp) = solve_scaled(&g, &r, true)?;
    let share = trace_through(&read.gram_inverse, &r, &dp);
    let denominator = &read.gram_det * &read.l * &det;
    Ok(Fit { g, det, dp, share, denominator })
}

/// The canonical share a held-out moment set keeps under the training lift, read to second order:
/// with the natural lift `−N Y⁻¹ Pᵀ` founded on the training text,
/// `s_h = (2N/N_h) tr(Y⁻¹PᵀR_h) − (N/N_h)² tr(P Y⁻¹ Y_h Y⁻¹ Pᵀ G_h)`, as a numerator and
/// denominator (twice the nats a held-out cell saves).
fn held_share(held: &Read, held_reads: &Reads, train: &Read, trained: &Fit) -> (BigInt, BigInt) {
    let (g, r) = joint(held, held_reads);
    let (n, nh) = (BigInt::from(train.cells), BigInt::from(held.cells));
    let (det, dy) = (&trained.det, &train.gram_det);
    let cross = trace_through(&train.gram_inverse, &trained.dp, &r);
    let (w, k) = (train.width, trained.dp.len());
    // B = Y⁻¹ Pᵀ (scaled by D_Y·D), one row per covector coordinate.
    let b: Vec<Vec<BigInt>> = (0..w).into_par_iter().map(|row| (0..k).map(|j| (0..w).map(|r2| &train.gram_inverse[row][r2] * &trained.dp[j][r2]).sum()).collect()).collect();
    // Bᵀ Y_h B: k × k.
    let yb: Vec<Vec<BigInt>> = (0..w).into_par_iter().map(|row| (0..k).map(|j| (0..w).map(|r2| &held.gram[row][r2] * &b[r2][j]).sum()).collect()).collect();
    let middle: Vec<Vec<BigInt>> = (0..k).map(|j| (0..k).map(|kk| (0..w).map(|row| &b[row][j] * &yb[row][kk]).sum()).collect()).collect();
    let quad: BigInt = (0..k).map(|j| (0..k).map(|kk| &middle[j][kk] * &g[kk][j]).sum::<BigInt>()).sum();
    let numerator = &n * &nh * dy * det * cross * 2 - &n * &n * quad;
    (numerator, &nh * &nh * dy * dy * det * det * &held.l)
}

pub(super) fn permille(num: &BigInt, den: &BigInt) -> String {
    if den.is_zero() {
        return "0".into();
    }
    let scaled = div_round(&(num * 1000), den);
    format!("{scaled}")
}

/// The leading canonical direction of a complex block against the tension's metric: the
/// generalized eigenvector of `(𝕄ᴴ Y⁻¹ 𝕄, Q)`, `𝕄 = M₀ + i M₁` acting on a complex factor `w`
/// and `Q` real, by the power step `w = Q⁻¹𝕄ᴴv`, `v ← Y⁻¹𝕄w`, on `M₀`, `M₁` and `Q` released to
/// below `2^60` their largest entry and `Y⁻¹` released (only directions are read), each vector
/// released to `2^15` with its two parts together; it stops when a step raises
/// `‖𝕄w‖²_(Y⁻¹)/(wᴴQw)` by less than `2^(−15)` of itself. The numerator is the energy both faces
/// of `c` carry, `‖Σ Re(c) y‖² + ‖Σ Im(c) y‖²` in `Y⁻¹`, over `Σ|c|²`: a turn's two faces count
/// together. With `M₁ = 0` and `v` real the step stays real. Returns the factor and the carried
/// `v`, each as its real and imaginary parts.
fn leading_canonical(dm: [&[Vec<BigInt>]; 2], dq: &[Vec<BigInt>], metric: &[Vec<i64>], mut v: [Vec<i64>; 2]) -> Result<([Vec<i64>; 2], [Vec<i64>; 2])> {
    let (rows, q) = (dm[0].len(), dq.len());
    let mt = release_big(&dm[0].iter().chain(dm[1]).flatten().cloned().collect::<Vec<_>>(), 60);
    let (m0, m1) = mt.split_at(rows * q);
    let qt = release_big(&dq.iter().flatten().cloned().collect::<Vec<_>>(), 60);
    let qbig: Vec<Vec<BigInt>> = (0..q).map(|i| (0..q).map(|j| BigInt::from(qt[i * q + j])).collect()).collect();
    let identity: Vec<Vec<BigInt>> = (0..q).map(|i| (0..q).map(|j| BigInt::from((i == j) as i64)).collect()).collect();
    let (_, inverse) = solve_scaled(&qbig, &identity, false)?;
    let mut best: Option<(BigInt, BigInt, [Vec<i64>; 2], [Vec<i64>; 2])> = None;
    loop {
        // g = 𝕄ᴴ v: g₀ = M₀ᵀv₀ + M₁ᵀv₁, g₁ = M₀ᵀv₁ − M₁ᵀv₀.
        let g0: Vec<i128> = (0..q).map(|j| (0..rows).map(|a| m0[a * q + j] as i128 * v[0][a] as i128 + m1[a * q + j] as i128 * v[1][a] as i128).sum()).collect();
        let g1: Vec<i128> = (0..q).map(|j| (0..rows).map(|a| m0[a * q + j] as i128 * v[1][a] as i128 - m1[a * q + j] as i128 * v[0][a] as i128).sum()).collect();
        let mut wide: Vec<BigInt> = Vec::with_capacity(2 * q);
        for g in [&g0, &g1] {
            for row in &inverse {
                wide.push(row.iter().zip(g.iter()).map(|(x, &y)| x * y).sum());
            }
        }
        let released = release_big(&wide, 15);
        let w = [released[..q].to_vec(), released[q..].to_vec()];
        // u = 𝕄 w: u₀ = M₀w₀ − M₁w₁, u₁ = M₀w₁ + M₁w₀.
        let u0: Vec<i128> = (0..rows).map(|a| (0..q).map(|j| m0[a * q + j] as i128 * w[0][j] as i128 - m1[a * q + j] as i128 * w[1][j] as i128).sum()).collect();
        let u1: Vec<i128> = (0..rows).map(|a| (0..q).map(|j| m0[a * q + j] as i128 * w[1][j] as i128 + m1[a * q + j] as i128 * w[0][j] as i128).sum()).collect();
        let mut mu: Vec<BigInt> = Vec::with_capacity(2 * rows);
        for u in [&u0, &u1] {
            for row in metric {
                mu.push(row.iter().zip(u.iter()).map(|(&x, &y)| BigInt::from(x) * y).sum());
            }
        }
        let num: BigInt = mu.iter().zip(u0.iter().chain(&u1)).map(|(x, &y)| x * y).sum();
        let den: BigInt = w.iter().map(|wp| (0..q).map(|i| (0..q).map(|j| BigInt::from(qt[i * q + j] as i128 * wp[i] as i128) * wp[j]).sum::<BigInt>()).sum::<BigInt>()).sum();
        let carried = release_big(&mu, 15);
        v = [carried[..rows].to_vec(), carried[rows..].to_vec()];
        if den <= BigInt::from(0) || w.iter().flatten().all(|&x| x == 0) {
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
/// deflated centred moments `Q_b = Σ_u |β_u|² Q̃_u/n_u`, `𝕄_b = Σ_u β_u M̃'_u/n_u` (each `β_u`
/// complex, released with the others to `2^15`; only directions are read here).
fn a_step(read: &Read, deflated: &[Vec<i128>], hats: &[Vec<i64>], b: &[Vec<i64>; 2], v: [Vec<i64>; 2]) -> Result<([Vec<i64>; 2], [Vec<i64>; 2])> {
    let (dims, width, classes) = (read.dims, read.width, read.classes.len());
    let betas: Vec<i128> = b.iter().flat_map(|bk| read.classes.iter().map(move |c| hats[c.class].iter().zip(bk).map(|(&x, &bb)| x as i128 * bb as i128).sum::<i128>())).collect();
    let rel = release_wide(&betas, 15);
    let (r0, r1) = rel.split_at(classes);
    let ns: Vec<BigInt> = read.classes.iter().map(|c| BigInt::from(c.n)).collect();
    let dq: Vec<Vec<BigInt>> = (0..dims)
        .into_par_iter()
        .map(|i| {
            (0..dims)
                .map(|j| {
                    (0..classes)
                        .filter(|&u| r0[u] != 0 || r1[u] != 0)
                        .map(|u| div_round(&(BigInt::from(read.classes[u].q[i * dims + j]) * (r0[u] as i128 * r0[u] as i128 + r1[u] as i128 * r1[u] as i128)), &ns[u]))
                        .sum()
                })
                .collect()
        })
        .collect();
    let block = |rk: &[i64]| -> Vec<Vec<BigInt>> {
        (0..width)
            .into_par_iter()
            .map(|r| (0..dims).map(|i| (0..classes).filter(|&u| rk[u] != 0).map(|u| div_round(&(BigInt::from(deflated[u][i * width + r]) * rk[u]), &ns[u])).sum()).collect())
            .collect()
    };
    let (dm0, dm1) = (block(r0), block(r1));
    leading_canonical([&dm0, &dm1], &dq, &read.metric, v)
}

/// The b-step: with `a` held, the leading canonical direction over `x̂` of
/// `𝕄 = Σ_u x̂_u (M̃'_uᵀa)ᵀ/n_u` against `C = Σ_u (aᴴQ̃_u a/n_u) x̂_u x̂_uᵀ`.
fn b_step(read: &Read, deflated: &[Vec<i128>], hats: &[Vec<i64>], a: &[Vec<i64>; 2], v: [Vec<i64>; 2]) -> Result<([Vec<i64>; 2], [Vec<i64>; 2])> {
    let (dims, width, hat) = (read.dims, read.width, hats[0].len());
    let live = [a[0].iter().any(|&x| x != 0), a[1].iter().any(|&x| x != 0)];
    let per: Vec<(BigInt, [Vec<BigInt>; 2])> = read
        .classes
        .par_iter()
        .zip(deflated)
        .map(|(c, m)| {
            let n = BigInt::from(c.n);
            let mut quad = BigInt::zero();
            let mut lin: [Vec<BigInt>; 2] = [vec![BigInt::zero(); width], vec![BigInt::zero(); width]];
            for k in 0..2 {
                if !live[k] {
                    continue;
                }
                let ak = &a[k];
                quad += (0..dims).map(|i| BigInt::from(ak[i]) * (0..dims).map(|j| BigInt::from(c.q[i * dims + j]) * ak[j]).sum::<BigInt>()).sum::<BigInt>();
                lin[k] = (0..width).map(|r| div_round(&(0..dims).map(|i| BigInt::from(m[i * width + r]) * ak[i]).sum::<BigInt>(), &n)).collect();
            }
            (div_round(&quad, &n), lin)
        })
        .collect();
    let block = |k: usize| -> Vec<Vec<BigInt>> { (0..width).into_par_iter().map(|r| (0..hat).map(|j| read.classes.iter().zip(&per).map(|(c, (_, lin))| &lin[k][r] * hats[c.class][j]).sum()).collect()).collect() };
    let (dm0, dm1) = (block(0), block(1));
    let dq: Vec<Vec<BigInt>> = (0..hat)
        .into_par_iter()
        .map(|i| (0..hat).map(|j| read.classes.iter().zip(&per).map(|(c, (quad, _))| quad * hats[c.class][i] * hats[c.class][j]).sum()).collect())
        .collect();
    leading_canonical([&dm0, &dm1], &dq, &read.metric, v)
}

/// [agent-inferred, October 24] A rank's ring start: the two leading directions over the carried
/// face of the tension each class reads on it, summed over the classes without their phases,
/// `A = Σ_u M̃'_u Y⁻¹ M̃'_uᵀ/n_u³` against the pooled within-class Gram `Q₀ = Σ_u Q̃_u/n_u` (with
/// `β_u` free per class, a direction's share is at most `Σ_u aᵀC_uY⁻¹C_uᵀa / aᵀS_ua`, `C_u = M̃'_u/n_u`
/// and `S_u = Q̃_u/n_u` the class's centred moments; `A` pools it, each class's part over its count,
/// against the pooled Gram). A direction that each
/// class reads with its own sign or phase, as a strand turned by the arriving class is, counts in
/// full here; the unit start, every class alike, cancels it. The first is `a₀`; the second, kept
/// `Q₀`-orthogonal to it and brought to its length, `a₁`. Power steps as [`leading_canonical`]'s.
fn ring_seed(read: &Read, deflated: &[Vec<i128>]) -> Result<[Vec<i64>; 2]> {
    let (dims, width, classes) = (read.dims, read.width, read.classes.len());
    let ns: Vec<BigInt> = read.classes.iter().map(|c| BigInt::from(c.n)).collect();
    let pooled: Vec<BigInt> = (0..dims * dims).into_par_iter().map(|ij| (0..classes).map(|u| div_round(&BigInt::from(read.classes[u].q[ij]), &ns[u])).sum()).collect();
    let qt = release_big(&pooled, 60);
    let qbig: Vec<Vec<BigInt>> = (0..dims).map(|i| (0..dims).map(|j| BigInt::from(qt[i * dims + j])).collect()).collect();
    let identity: Vec<Vec<BigInt>> = (0..dims).map(|i| (0..dims).map(|j| BigInt::from((i == j) as i64)).collect()).collect();
    let (_, inverse) = solve_scaled(&qbig, &identity, false)?;
    let cubes: Vec<BigInt> = ns.iter().map(|n| n * n * n).collect();
    let q_inner = |x: &[i64], y: &[i64]| -> BigInt { (0..dims).map(|i| (0..dims).map(|j| BigInt::from(qt[i * dims + j] as i128 * x[i] as i128) * y[j]).sum::<BigInt>()).sum() };
    // A w and wᵀAw, each class's part rounded by its n_u³ (directions only).
    let apply = |w: &[i64]| -> (Vec<BigInt>, BigInt) {
        let parts: Vec<(Vec<BigInt>, BigInt)> = (0..classes)
            .into_par_iter()
            .map(|u| {
                let m = &deflated[u];
                let t: Vec<BigInt> = (0..width).map(|r| (0..dims).map(|i| BigInt::from(m[i * width + r]) * w[i]).sum()).collect();
                let t2: Vec<BigInt> = read.metric.iter().map(|row| row.iter().zip(&t).map(|(&x, y)| y * x).sum()).collect();
                let s: Vec<BigInt> = (0..dims).map(|i| div_round(&(0..width).map(|r| &t2[r] * m[i * width + r]).sum::<BigInt>(), &cubes[u])).collect();
                let quad = div_round(&t.iter().zip(&t2).map(|(x, y)| x * y).sum::<BigInt>(), &cubes[u]);
                (s, quad)
            })
            .collect();
        let mut g = vec![BigInt::zero(); dims];
        let mut quad = BigInt::zero();
        for (s, q) in parts {
            for (gi, si) in g.iter_mut().zip(s) {
                *gi += si;
            }
            quad += q;
        }
        (g, quad)
    };
    let mut found: Vec<Vec<i64>> = Vec::new();
    for _ in 0..2 {
        let start = (0..dims).max_by(|&x, &y| qt[x * dims + x].cmp(&qt[y * dims + y])).unwrap_or(0);
        let mut w: Vec<i64> = (0..dims).map(|i| (i == start) as i64).collect();
        let mut best: Option<(BigInt, BigInt, Vec<i64>)> = None;
        loop {
            if let Some(e) = found.first() {
                // Kept Q₀-orthogonal to the first direction.
                let (ee, ew) = (q_inner(e, e), q_inner(e, &w));
                let wide: Vec<BigInt> = w.iter().zip(e).map(|(&x, &y)| &ee * x - &ew * y).collect();
                w = release_big(&wide, 15);
            }
            let (g, num) = apply(&w);
            let den = q_inner(&w, &w);
            if den <= BigInt::from(0) {
                break;
            }
            let gained = match &best {
                None => true,
                Some((bn, bd, _)) => (&num * bd) << 15u32 > bn * &den * ((1i64 << 15) + 1),
            };
            if best.as_ref().is_none_or(|(bn, bd, _)| &num * bd > bn * &den) {
                best = Some((num, den, w.clone()));
            }
            if !gained {
                break;
            }
            let wide: Vec<BigInt> = inverse.iter().map(|row| row.iter().zip(&g).map(|(x, y)| x * y).sum()).collect();
            w = release_big(&wide, 15);
        }
        let (_, _, w) = best.ok_or("the ring start found no direction")?;
        found.push(w);
    }
    // The second brought to the first's length in Q₀: a₁ ← a₁ √(a₀ᵀQ₀a₀ / a₁ᵀQ₀a₁).
    let (first, second) = (q_inner(&found[0], &found[0]), q_inner(&found[1], &found[1]));
    let scale = if second.is_zero() { BigInt::zero() } else { ((first << 64u32) / second).sqrt() };
    let wide: Vec<BigInt> = found[0].iter().map(|&x| BigInt::from(x) << 32u32).chain(found[1].iter().map(|&x| &scale * x)).collect();
    let released = release_big(&wide, 15);
    Ok([released[..dims].to_vec(), released[dims..].to_vec()])
}

/// The centred moments less the founded channels' lift, `M̃'_u = M̃_u − Σ_t z_ut L_utᵀ` with each
/// factor's lift `L_ut = Σ_(j ∋ t) ±β P_j` and `P = D·P/D`, rounded (directions only).
fn deflate(read: &Read, reads: &Reads, fitted: &Fit) -> Result<Vec<Vec<i128>>> {
    use num_traits::ToPrimitive;
    let (dims, width, atoms) = (read.dims, read.width, reads.atoms.len());
    read.classes
        .par_iter()
        .enumerate()
        .map(|(u, c)| {
            let mut lifts: Vec<Vec<BigInt>> = vec![vec![BigInt::zero(); width]; atoms];
            for ((_, terms), p) in reads.channels.iter().zip(&fitted.dp) {
                for &(t, k, negated) in terms {
                    let coefficient = reads.coefficient(u, k, negated);
                    for (slot, x) in lifts[t].iter_mut().zip(p) {
                        *slot += x * coefficient;
                    }
                }
            }
            let mut out = vec![0i128; dims * width];
            for i in 0..dims {
                for r in 0..width {
                    let lift: BigInt = (0..atoms).map(|t| &lifts[t][r] * reads.atoms[t].z[u][i]).sum();
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
/// `D² D_Y n_u`, with `Y⁻¹` its scaled inverse.
fn share_per_class(read: &Read, reads: &Reads, fitted: &Fit) -> Vec<BigInt> {
    let (k, w) = (reads.channels.len(), read.width);
    let pa: Vec<Vec<BigInt>> = (0..k).map(|j| (0..w).map(|r| (0..w).map(|r2| &read.gram_inverse[r][r2] * &fitted.dp[j][r2]).sum()).collect()).collect();
    let cross: Vec<Vec<BigInt>> = (0..k).map(|j| (0..k).map(|kk| fitted.dp[j].iter().zip(&pa[kk]).map(|(x, y)| x * y).sum()).collect()).collect();
    (0..read.classes.len())
        .into_par_iter()
        .map(|u| {
            let lin: BigInt = (0..k).map(|j| (0..w).map(|r| reads.class_cross(u, j, r) * &pa[j][r]).sum::<BigInt>()).sum();
            let quad: BigInt = (0..k).map(|j| (0..k).map(|kk| reads.class_gram(u, j, kk) * &cross[j][kk]).sum::<BigInt>()).sum();
            lin * &fitted.det * 2 - quad
        })
        .collect()
}

/// One rank's search from a start: the unit (`b` the unit, every class alike) or a ring
/// ([`ring_seed`], whose `a` is held for a first b-step), alternating the two factors' steps until
/// a pair raises the training share by less than `2^(−15)` of itself. Returns the best exact
/// share, its form and the steps taken.
fn alternate(read: &Read, deflated: &[Vec<i128>], hats: &[Vec<i64>], reads: &mut Reads, forms: &[Form], ring: Option<[Vec<i64>; 2]>) -> Result<(BigInt, BigInt, Form, usize)> {
    let width = read.width;
    // The carried covector starts at the coordinate with the most tension.
    let top = (0..width).max_by(|&x, &y| read.diagonal[x].cmp(&read.diagonal[y])).unwrap_or(0);
    let mut v: [Vec<i64>; 2] = [(0..width).map(|r| (r == top) as i64).collect(), vec![0; width]];
    let mut b: [Vec<i64>; 2] = [(0..=width).map(|j| (j == width) as i64).collect(), vec![0; width + 1]];
    if let Some(a) = ring {
        let (b1, v1) = b_step(read, deflated, hats, &a, v)?;
        b = b1;
        v = v1;
    }
    let mut best: Option<(BigInt, BigInt, Form)> = None;
    let mut steps = 0;
    loop {
        steps += 1;
        let (a, v1) = a_step(read, deflated, hats, &b, v)?;
        let (b1, v2) = b_step(read, deflated, hats, &a, v1)?;
        v = v2;
        b = b1.clone();
        let candidate = Form { a, b: b1, faces: [true, true] };
        reads.push(read, hats, &candidate, forms)?;
        let trial = fit(read, reads);
        reads.truncate(forms.len());
        let trial = trial?;
        let (num, den) = (trial.share, trial.denominator);
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
    let (num, den, form) = best.ok_or("the alternation founded no form")?;
    Ok((num, den, form, steps))
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
/// HELD_MOMENTS_SHA FORMS OUT [FROM FROM_SHA]`: found complex situated forms from the training
/// moments up to `FORMS` in all, read each rank's canonical share on the training and held-out
/// moments, and write each form to `OUT` (create-new) as it is founded. `FROM`, a forms file
/// founded on the same moments, supplies the first forms: they are read again, copied to `OUT` and
/// deflated, and the founding continues from the next rank. Each rank searches from the unit and
/// from a ring ([`alternate`]) and founds the larger exact training share; `unit` and `ring` print
/// each start's. A form keeps both faces unless they are one reading (their squared correlation
/// within `2^(−15)` of one), when it keeps the larger. Shares are in thousandths, rounded: the sum
/// of the squared canonical correlations, twice the nats a cell saves; `serves` names the classes
/// carrying most of the training share, each with its part.
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
    let (mut reads, mut held_reads) = (Reads::default(), Reads::default());
    let mut deflated: Vec<Vec<i128>> = train_read.classes.iter().map(|c| c.m.clone()).collect();
    // The form's release for a reading: its training values' within-class root mean square,
    // `Σ|c|²` over the cells, brought to below 2^16.
    let shift_of = |fitted: &Fit, reads: &Reads, j: usize| -> u64 {
        let total: BigInt = reads.channels.iter().enumerate().filter(|(_, (f, _))| *f == j).map(|(c, _)| fitted.g[c][c].clone()).sum();
        let mean_square = total / (&train_read.l * BigInt::from(train_read.cells.max(1)));
        mean_square.bits().div_ceil(2).saturating_sub(16)
    };
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
            reads.push(&train_read, &hats, &form, &forms)?;
            held_reads.push(&held_read, &hats, &form, &forms)?;
            std::io::Write::write_all(&mut file, form.line(forms.len(), shift).as_bytes())?;
            forms.push(form);
        }
        file.sync_data()?;
        let trained = fit(&train_read, &reads)?;
        let (hnum, hden) = held_share(&held_read, &held_reads, &train_read, &trained);
        println!(
            "SITUATED_FROM forms={} channels={} train_canonical_permille={} held_out_canonical_permille={} elapsed_ms={}",
            forms.len(),
            reads.channels.len(),
            permille(&trained.share, &trained.denominator),
            permille(&hnum, &hden),
            started.elapsed().as_millis()
        );
        if forms.len() < ranks {
            deflated = deflate(&train_read, &reads, &trained)?;
        }
    }
    for rank in forms.len() + 1..=ranks {
        let (unit_num, unit_den, unit_form, unit_steps) = alternate(&train_read, &deflated, &hats, &mut reads, &forms, None)?;
        let ring = ring_seed(&train_read, &deflated)?;
        let (ring_num, ring_den, ring_form, ring_steps) = alternate(&train_read, &deflated, &hats, &mut reads, &forms, Some(ring))?;
        let (unit_share, ring_share) = (permille(&unit_num, &unit_den), permille(&ring_num, &ring_den));
        let (mut form, start, steps) = if ring_num * &unit_den > unit_num * &ring_den { (ring_form, "ring", ring_steps) } else { (unit_form, "unit", unit_steps) };
        form.faces = form.live_faces();
        // A form whose two faces are one reading keeps the larger.
        reads.push(&train_read, &hats, &form, &forms)?;
        let own = fit(&train_read, &reads);
        let mine: Vec<usize> = reads.channels.iter().enumerate().filter(|(_, (f, _))| *f == forms.len()).map(|(c, _)| c).collect();
        reads.truncate(forms.len());
        let own = own?;
        if let [re, im] = mine[..] {
            let (g00, g11, g01) = (&own.g[re][re], &own.g[im][im], &own.g[re][im]);
            if (g01 * g01) << 15u32 > g00 * g11 * ((1i64 << 15) - 1) {
                form.faces = if g00 >= g11 { [true, false] } else { [false, true] };
            }
        }
        reads.push(&train_read, &hats, &form, &forms)?;
        held_reads.push(&held_read, &hats, &form, &forms)?;
        forms.push(form);
        let trained = fit(&train_read, &reads)?;
        let (hnum, hden) = held_share(&held_read, &held_reads, &train_read, &trained);
        // The classes carrying most of the training share, each with its part of it.
        let per = share_per_class(&train_read, &reads, &trained);
        let mut served: Vec<(BigInt, usize)> = per.iter().zip(&train_read.classes).enumerate().map(|(u, (x, c))| (div_round(&(x * &train_read.l), &BigInt::from(c.n)), u)).collect();
        served.sort_by(|x, y| y.0.cmp(&x.0));
        let named: Vec<String> = served.iter().take(6).map(|(x, u)| format!("{}:{}", class_label(train_read.classes[*u].class), permille(x, &(&trained.det * &trained.share)))).collect();
        let j = forms.len() - 1;
        let form = &forms[j];
        let faces: Vec<&str> = ["re", "im"].into_iter().zip(form.faces).filter(|(_, kept)| *kept).map(|(name, _)| name).collect();
        println!(
            "SITUATED_RANK rank={rank} start={start} steps={steps} unit={unit_share} ring={ring_share} faces={} channels={} train_canonical_permille={} held_out_canonical_permille={} serves={} elapsed_ms={}",
            faces.join(","),
            reads.channels.len(),
            permille(&trained.share, &trained.denominator),
            permille(&hnum, &hden),
            named.join(","),
            started.elapsed().as_millis()
        );
        std::io::Write::write_all(&mut file, form.line(j, shift_of(&trained, &reads, j)).as_bytes())?;
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
        let kept = field(line, "faces").ok_or("no faces")?;
        let faces = [kept.split(',').any(|f| f == "re"), kept.split(',').any(|f| f == "im")];
        if kept.split(',').any(|f| f != "re" && f != "im") || faces == [false, false] {
            return Err("a form's faces are re, im or both".into());
        }
        let a = [parse(field(line, "a").ok_or("no a")?)?, parse(field(line, "ai").ok_or("no ai")?)?];
        let b = [parse(field(line, "b").ok_or("no b")?)?, parse(field(line, "bi").ok_or("no bi")?)?];
        if a.iter().any(|x| x.len() != dims) || b.iter().any(|x| x.len() != width + 1) {
            return Err("a form's factors have the wrong lengths".into());
        }
        forms.push((Form { a, b, faces }, shift));
    }
    if forms.is_empty() {
        return Err("a forms file with no form".into());
    }
    Ok((level, forms))
}

/// [agent-inferred, October 24] `read-tower-situated STATE STATE_SHA FORMS FORMS_SHA TEXT TEXT_SHA
/// CELLS CELLS_SHA`: the frozen tower reads `TEXT` as one passage from rest, and at each named cell
/// the situated forms' kept faces are printed, `FORMS i class v₁ … v_k`, each a face of
/// `c = (aᵀŝ)(bᵀx̂)` (the state the cell's class meets on its level, the class's encoding with the
/// unit), `Re c` before `Im c`, released by its form's shift, rounded to nearest. A reading beside
/// the code: the tower is not moved.
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
                let p: Vec<BigInt> = form.a.iter().map(|a| BigInt::from(a.iter().zip(&face).map(|(&x, &s)| x as i128 * s as i128).sum::<i128>())).collect();
                let beta: Vec<BigInt> = form.b.iter().map(|b| BigInt::from(b.iter().zip(&hats[classes[i]]).map(|(&x, &h)| x as i128 * h as i128).sum::<i128>())).collect();
                let values = [&p[0] * &beta[0] - &p[1] * &beta[1], &p[0] * &beta[1] + &p[1] * &beta[0]];
                for (value, _) in values.iter().zip(form.faces).filter(|(_, kept)| *kept) {
                    let released = if *shift == 0 { value.clone() } else { div_round(value, &(BigInt::from(1) << *shift)) };
                    let _ = write!(line, " {released}");
                }
            }
            println!("{line}");
            Ok(())
        })
        .map_err(|e| e.to_string())?;
    Ok(())
}

/// [agent-inferred, October 24] `read-tower-input-covectors STATE STATE_SHA TEXT TEXT_SHA CELLS
/// CELLS_SHA SECTION [LEVEL]`: the frozen tower reads `TEXT` as one passage from rest, in sections
/// of `SECTION` cells as the learner reads it, and at each named cell prints the covector its
/// reverse sends to the cell's input, `FORMS i class y₁ … y_w` (on the covector's `2^(−24)`): the
/// tension of the section's later faces carried back to where the class arrived. With `LEVEL` it
/// prints instead the covector of that level's modes after the cell's push, each mode's `(re, im)`
/// on the same grain: the tension a value placed in the mode there meets, carried back through the
/// mode's own moves. A reading beside the code: whether a later face's error reaches an earlier
/// cell at all, and through which mode.
pub(super) fn read_tower_input_covectors(args: &[String]) -> Result<()> {
    if args.len() != 8 && args.len() != 9 {
        return Err("read-tower-input-covectors STATE STATE_SHA TEXT TEXT_SHA CELLS CELLS_SHA SECTION [LEVEL]".into());
    }
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let tower = &learner.tower;
    let text = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let classes: Vec<usize> = text.iter().map(|&b| b as usize).collect();
    let cells: Vec<usize> = std::str::from_utf8(&pinned_read(&args[5], &args[6], READ_BUDGET as usize)?)?.split_whitespace().map(count).collect::<Result<_>>()?;
    let section = positive(&args[7])?;
    let level = args.get(8).map(|l| count(l)).transpose()?;
    if level.is_some_and(|l| l >= tower.declaration.levels) {
        return Err("LEVEL names no level of the tower".into());
    }
    let dims = 2 * tower.declaration.modes;
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
            let printed = level.map_or(cell.covector, |l| &cell.modes[l * dims..(l + 1) * dims]);
            for y in printed {
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
