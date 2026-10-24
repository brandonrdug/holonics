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
//! the tower's own reverse sends to each cell's input ([`Tower::read_input_covectors`]): the
//! tension of every later face in the section carried back to where the class arrived. The class
//! alone bridges its covector's class mean (the encoding's own covector), so each class's moments
//! are centred; each rank founds the form whose best lift removes most of what remains
//! (the effective tension's law, `contact.tension-founds-face`, read at the input), alternating the
//! two factors from `b` the unit as the pair founding does ([`leading_factor`]). Directions are
//! searched on released copies; every share reported is read exactly from the moments.

use super::tower_train::{count, leading_factor, pair_hats, positive, release_wide, solve_scaled, STATE_BUDGET};
use super::*;
use holonics::hnn::tower::{carried_face, Tower, TowerError, TowerLearner};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use rayon::prelude::*;

/// The largest magnitude a carried coordinate or a covector entry may have for the moment sums to
/// stay inside 128 bits over fewer than `2^32` cells: each product is below `2^80`.
const MOMENT_REACH: i64 = 1 << 40;

/// One class's moments over the cells it arrives at: `n`, `Σŝ`, `Σy`, `Σŝŝᵀ` (upper triangle
/// while reading) and `Σŝyᵀ`.
#[derive(Clone)]
struct ClassMoments {
    n: i128,
    s: Vec<i128>,
    y: Vec<i128>,
    q: Vec<i128>,
    m: Vec<i128>,
}

/// A text's moments: per arriving class, and `Σyyᵀ` over every cell (upper triangle).
struct Moments {
    dims: usize,
    width: usize,
    classes: Vec<Option<ClassMoments>>,
    yy: Vec<i128>,
    cells: usize,
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
}

/// The frozen tower reads `streams` (each from rest) in sections of `section` cells, and keeps the
/// moments of level `level`'s carried face against each cell's input covector.
fn read_moments(tower: &Tower, streams: &[Vec<usize>], section: usize, level: usize) -> Result<Moments> {
    let (w, alphabet) = (tower.declaration.width, tower.declaration.alphabet);
    let dims = 2 * tower.declaration.modes;
    let read: Vec<Moments> = streams
        .par_iter()
        .map(|classes| {
            let mut moments = Moments::new(alphabet, dims, w);
            let mut state = tower.rest();
            tower
                .read_input_covectors(&mut state, classes, section, |cell| {
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

/// A moment set read for the founding: the centred classes, `L` the lcm of their counts and
/// `L·tr T̃`, the within-class covector energy `Σ|y|² − Σ_u |Σ_u y|²/n_u` scaled by `L`, with each
/// covector coordinate's `L·T̃_rr`.
struct Read {
    dims: usize,
    width: usize,
    classes: Vec<Centred>,
    l: BigInt,
    scales: Vec<BigInt>,
    trace: BigInt,
    diagonal: Vec<BigInt>,
    raw: BigInt,
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
    let diagonal: Vec<BigInt> = (0..w)
        .map(|r| &l * moments.yy[r * w + r] - present.iter().map(|(_, c)| BigInt::from(c.y[r]) * c.y[r] * (&l / c.n)).sum::<BigInt>())
        .collect();
    let trace = diagonal.iter().sum();
    let raw = &l * (0..w).map(|r| BigInt::from(moments.yy[r * w + r])).sum::<BigInt>();
    let scales = classes.iter().map(|c| &l / c.n).collect();
    Ok(Read { dims: d, width: w, classes, l, scales, trace, diagonal, raw, cells: moments.cells })
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

/// A training fit: `D` and `D·P` with `G P = R`, `R`, and the share of the training text's
/// within-class covector energy the lift removes, `tr(RᵀP)/tr T̃`, as a numerator and denominator.
struct Fit {
    det: BigInt,
    dp: Vec<Vec<BigInt>>,
    r: Vec<Vec<BigInt>>,
    removed: BigInt,
    denominator: BigInt,
}

fn fit(read: &Read, reads: &[&FormRead]) -> Result<Fit> {
    let (g, r) = joint(read, reads);
    let (det, dp) = solve_scaled(&g, &r, true)?;
    let removed: BigInt = r.iter().zip(&dp).flat_map(|(rr, pp)| rr.iter().zip(pp).map(|(x, y)| x * y)).sum();
    let denominator = &det * &read.trace;
    Ok(Fit { det, dp, r, removed, denominator })
}

/// The share of a held-out moment set's within-class covector energy that the training lift
/// `P = D·P/D` removes, `(2 tr(RᵀP) − tr(PᵀGP))/tr T̃`, as a numerator and denominator.
fn held_removed(read: &Read, reads: &[&FormRead], trained: &Fit) -> (BigInt, BigInt) {
    let (g, r) = joint(read, reads);
    let (det, dp, k) = (&trained.det, &trained.dp, reads.len());
    let cross: BigInt = r.iter().zip(dp).flat_map(|(rr, pp)| rr.iter().zip(pp).map(|(x, y)| x * y)).sum();
    let quadratic: BigInt = (0..read.width).into_par_iter().map(|c| (0..k).map(|j| &dp[j][c] * (0..k).map(|kk| &g[j][kk] * &dp[kk][c]).sum::<BigInt>()).sum::<BigInt>()).sum();
    (cross * det * 2 - quadratic, det * det * &read.trace)
}

fn permille(num: &BigInt, den: &BigInt) -> String {
    if den.is_zero() {
        return "0".into();
    }
    let scaled = div_round(&(num * 1000), den);
    format!("{scaled}")
}

/// The a-step: with `b` held, the leading direction over the carried face of the deflated centred
/// moments `Q_b = Σ_u β_u² Q̃_u/n_u`, `M_b = Σ_u β_u M̃'_u/n_u` (each `β_u` released to `2^15`;
/// only directions are read here).
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
    let (a, v, _) = leading_factor(&dm, &dq, v)?;
    Ok((a, v))
}

/// The b-step: with `a` held, the leading direction over `x̂` of `N = Σ_u x̂_u (M̃'_uᵀa)ᵀ/n_u`
/// against `C = Σ_u (aᵀQ̃_u a/n_u) x̂_u x̂_uᵀ`.
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
    let (b, v, _) = leading_factor(&dm, &dq, v)?;
    Ok((b, v))
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

/// `found-tower-situated STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA STREAMS SECTION LEVEL FORMS
/// OUT`: found `FORMS` situated forms on level `LEVEL`'s carried face from the input covectors the
/// frozen tower's reverse sends over the training text (`STREAMS` streams from rest, sections of
/// `SECTION` cells, as the learner reads it), read each rank's share on the training and held-out
/// texts, and write the forms to `OUT` (create-new). Shares are in thousandths, rounded.
pub(super) fn found_tower_situated(args: &[String]) -> Result<()> {
    if args.len() != 12 {
        return Err("found-tower-situated STATE STATE_SHA TRAIN TRAIN_SHA DEV DEV_SHA STREAMS SECTION LEVEL FORMS OUT".into());
    }
    let started = std::time::Instant::now();
    let learner = TowerLearner::from_text(std::str::from_utf8(&pinned_read(&args[1], &args[2], STATE_BUDGET)?)?).map_err(|e| e.to_string())?;
    let train = pinned_read(&args[3], &args[4], READ_BUDGET as usize)?;
    let dev = pinned_read(&args[5], &args[6], READ_BUDGET as usize)?;
    let (streams, section) = (positive(&args[7])?, positive(&args[8])?);
    let level = count(&args[9])?;
    let ranks = positive(&args[10])?;
    let tower = &learner.tower;
    if level >= tower.declaration.levels {
        return Err("LEVEL names no level of the tower".into());
    }
    if std::path::Path::new(&args[11]).exists() {
        return Err("OUT exists: the forms are written create-new".into());
    }
    let width = tower.declaration.width;
    let cut = |text: &[u8]| -> Vec<Vec<usize>> {
        let chunk = text.len().div_ceil(streams);
        text.chunks(chunk).map(|s| s.iter().map(|&b| b as usize).collect()).collect()
    };
    let train_read = centred(&read_moments(tower, &cut(&train), section, level)?)?;
    let dev_read = centred(&read_moments(tower, &cut(&dev), section, level)?)?;
    println!(
        "SITUATED_PASS train_cells={} held_out_cells={} train_classes={} held_out_classes={} dims={} width={width} class_means_permille_of_covector_energy={} held_out_class_means_permille={} read_ms={}",
        train_read.cells,
        dev_read.cells,
        train_read.classes.len(),
        dev_read.classes.len(),
        train_read.dims,
        permille(&(&train_read.raw - &train_read.trace), &train_read.raw),
        permille(&(&dev_read.raw - &dev_read.trace), &dev_read.raw),
        started.elapsed().as_millis()
    );
    let (hats, _) = pair_hats(tower);
    let mut forms: Vec<Form> = Vec::new();
    let mut reads: Vec<FormRead> = Vec::new();
    let mut held_reads: Vec<FormRead> = Vec::new();
    let mut deflated: Vec<Vec<i128>> = train_read.classes.iter().map(|c| c.m.clone()).collect();
    let mut diagonal = train_read.diagonal.clone();
    let unit: Vec<i64> = (0..=width).map(|j| (j == width) as i64).collect();
    for rank in 1..=ranks {
        // Start at the covector coordinate with the most energy left, `b` the unit.
        let top = (0..width).max_by(|&x, &y| diagonal[x].cmp(&diagonal[y])).unwrap_or(0);
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
            let (num, den) = (trial_fit.removed, trial_fit.denominator);
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
        held_reads.push(form_read(&dev_read, &hats, &form, &forms)?);
        forms.push(form);
        let trained = fit(&train_read, &reads.iter().collect::<Vec<_>>())?;
        let (hnum, hden) = held_removed(&dev_read, &held_reads.iter().collect::<Vec<_>>(), &trained);
        // The classes the newest form weighs most, by β_u² n_u.
        let last = reads.last().expect("a founded form");
        let mut weighed: Vec<(BigInt, usize)> = train_read.classes.iter().zip(&last.beta).map(|(c, &bt)| (BigInt::from(bt) * bt * c.n, c.class)).collect();
        weighed.sort_by(|x, y| y.0.cmp(&x.0));
        let named: Vec<String> = weighed.iter().take(6).map(|(_, u)| class_label(*u)).collect();
        println!(
            "SITUATED_RANK rank={rank} steps={steps} train_removed_permille={} held_out_removed_permille={} weighs={} elapsed_ms={}",
            permille(&trained.removed, &trained.denominator),
            permille(&hnum, &hden),
            named.join(","),
            started.elapsed().as_millis()
        );
        if rank < ranks {
            deflated = deflate(&train_read, &reads, &trained)?;
            diagonal = (0..width).map(|r| &train_read.diagonal[r] * &trained.det - trained.r.iter().zip(&trained.dp).map(|(rr, pp)| &rr[r] * &pp[r]).sum::<BigInt>()).collect();
        }
    }
    // Each form's release for a reading: its training values' within-class root mean square
    // brought to below 2^16.
    let (g, _) = joint(&train_read, &reads.iter().collect::<Vec<_>>());
    let mut out = format!("SITUATED level={level} dims={} width={width} forms={} state_sha256={}\n", train_read.dims, forms.len(), args[2]);
    for (j, form) in forms.iter().enumerate() {
        let mean_square = &g[j][j] / (&train_read.l * BigInt::from(train_read.cells.max(1)));
        let shift = mean_square.bits().div_ceil(2).saturating_sub(16);
        let join = |v: &[i64]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
        out.push_str(&format!("FORM {j} shift={shift} a={} b={}\n", join(&form.a), join(&form.b)));
    }
    let mut file = std::fs::OpenOptions::new().write(true).create_new(true).open(&args[11])?;
    std::io::Write::write_all(&mut file, out.as_bytes())?;
    println!("SITUATED_WRITTEN forms={} sha256={} elapsed_ms={}", forms.len(), sha256(out.as_bytes())?, started.elapsed().as_millis());
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
