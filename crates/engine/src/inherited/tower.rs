//! The October tower's items the engine's law reads (`hnn/tower.rs` until C3): moved whole into the engine (C3 of the consolidation, #603), each item's
//! text as it stood but for its visibility; C5 cuts them by object (THE_CONSOLIDATION §5).

pub(crate) use super::keyed_modes::release;
use super::keyed_modes::log2_face;
use num_bigint::BigUint;
use rayon::prelude::*;

/// A face's grain, `2^(−16)`.
pub const FACE_BITS: u32 = 16;

/// The material's grain, `2^(−24)`.
pub const MATERIAL_BITS: u32 = 24;

/// The moves' grain, `2^(−30)`.
pub const MOVE_BITS: u32 = 30;

/// A covector's grain, `2^(−24)`.
pub const COVECTOR_BITS: u32 = 24;

/// The deposit's covector grain, `2^(−32)`, and its ε.
pub const STEP_BITS: u32 = 32;

/// A code reading's grain, `2^(−20)` bits.
pub const READ_BITS: u32 = 20;

/// The first moment's rate, `2^(−3)`, and the second's, `2^(−8)` (agent-inferred: the classical
/// 0.9 and 0.999 read as dyadic rates; the second at `2^(−8)` so a pass of a few hundred sections
/// renews it).
pub const FIRST_RATE: u32 = 3;

pub const SECOND_RATE: u32 = 8;

pub const UNIT_BITS: u32 = 62;

/// Refusals of the tower's law.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TowerError {
    #[error("tower refused: {0}")]
    Refused(&'static str),
    /// A declared realization of the section's pass refused (`realization`), with its reason.
    #[error("tower realization refused: {0}")]
    Realization(String),
}

pub type Result<T> = std::result::Result<T, TowerError>;

pub fn refuse<T>(why: &'static str) -> Result<T> {
    Err(TowerError::Refused(why))
}

pub fn fit32(x: i128, what: &'static str) -> Result<i32> {
    i32::try_from(x).map_err(|_| TowerError::Refused(what))
}

#[track_caller]
pub fn fit64(x: i128) -> Result<i64> {
    crate::inherited::census::reach_here(&x);
    i64::try_from(x).map_err(|_| TowerError::Refused("a released value outgrew its 64-bit carrier"))
}

/// One cell's face: each class's mass `2^(z_a − z_max)` on `2^(−62)`, and their sum.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TowerFace {
    pub masses: Vec<u128>,
    pub total: u128,
}

impl TowerFace {
    /// The class's code, `−log₂ p̂(a)`, on `2^(−20)` bits.
    pub fn code(&self, class: usize) -> i64 {
        face_code(self.masses[class], self.total)
    }

    /// The comparison's descent covector against `target`, `p̂ − [· = target]` on `2^(−24)`: the
    /// one law the reverse scan reads ([`covector`]), handed to an exterior reading.
    pub fn covector(&self, target: usize) -> Vec<i64> {
        covector(self, target)
    }

    /// The class's rank on the face: how many classes carry more mass than it (0 when none does).
    pub fn rank(&self, class: usize) -> usize {
        let m = self.masses[class];
        self.masses.iter().filter(|&&x| x > m).count()
    }
}

/// A class's code read off its mass and the face's total, `−log₂(mass/total)` on `2^(−20)` bits
/// ([`TowerFace::code`]). Its domain is a positive total and a mass no greater than it, which every
/// face the tower forms satisfies; a face a realization returns is admitted to it before it is read
/// ([`realization::PassRead::admitted`]).
pub fn face_code(mass: u128, total: u128) -> i64 {
    let p = (mass << UNIT_BITS) / total;
    -(log2_face(p.max(1), READ_BITS) as i64)
}

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

/// `max |w|` over a family.
pub fn reach(w: &[i32]) -> u64 {
    w.iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0)
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

/// `max |y|` over a covector.
pub fn reach64(y: &[i64]) -> u64 {
    y.iter().map(|v| v.unsigned_abs()).max().unwrap_or(0)
}

/// A fallible map of known length collected into one allocation: `collect::<Result<Vec<_>>>`
/// cannot read the length through its adapter and grows the vector by reallocation, which crosses
/// the allocator's lock between the parallel streams.
pub fn collect_exact<T>(items: impl ExactSizeIterator<Item = Result<T>>) -> Result<Vec<T>> {
    let mut out = Vec::with_capacity(items.len());
    for item in items {
        out.push(item?);
    }
    Ok(out)
}

impl Default for TowerFace {
    fn default() -> Self {
        Self { masses: Vec::new(), total: 1 }
    }
}

/// `x / k` to the nearest integer, half away from zero.
pub fn div_nearest(x: i128, k: i128) -> i128 {
    if x >= 0 { (x + k / 2) / k } else { -((-x + k / 2) / k) }
}

/// `e^(a + i b)` on `2^(−30)`, `a`, `b` on `2^(−30)`: the series summed until its term releases
/// to zero at the grain.
pub fn exp_series(a: i128, b: i128) -> (i128, i128) {
    let mut term = (1i128 << MOVE_BITS, 0i128);
    let mut sum = term;
    let mut k = 1i128;
    loop {
        let re = release(term.0 * a - term.1 * b, MOVE_BITS);
        let im = release(term.0 * b + term.1 * a, MOVE_BITS);
        term = (div_nearest(re, k), div_nearest(im, k));
        if term == (0, 0) {
            return sum;
        }
        sum = (sum.0 + term.0, sum.1 + term.1);
        k += 1;
    }
}

/// `π` on `2^(−bits)` by Machin's series `π = 16 atan(1/5) − 4 atan(1/239)`, each term an exact
/// quotient sixteen grains finer, released once: the half turn's navigator face.
pub fn half_turn(bits: u32) -> i128 {
    const GUARD: u32 = 16;
    let one = 1i128 << (bits + GUARD);
    let atan_inverse = |k: i128| -> i128 {
        let (mut power, mut sum, mut n) = (one / k, 0i128, 0i128);
        while power != 0 {
            let term = power / (2 * n + 1);
            sum += if n % 2 == 0 { term } else { -term };
            power /= k * k;
            n += 1;
        }
        sum
    };
    release(16 * atan_inverse(5) - 4 * atan_inverse(239), GUARD)
}

/// `r̂ = r / ‖r‖_rms` on `2^(−16)` and `‖r‖_rms` on `2^(−16)`, `r` on `2^(−16)`; a zero face reads
/// as zero.
pub fn ratio_to_power(r: &[i64]) -> Result<(Vec<i32>, i128)> {
    let power: i128 = r.iter().map(|&v| v as i128 * v as i128).sum();
    let scale = ((power / r.len() as i128) as u128).isqrt() as i128;
    if scale == 0 {
        return Ok((vec![0; r.len()], 0));
    }
    let read = collect_exact(r.iter().map(|&v| fit32(div_nearest((v as i128) << FACE_BITS, scale), "a read's ratio outgrew its 32-bit carrier")))?;
    Ok((read, scale))
}

/// The adjoint of [`ratio_to_power`]: `∂r = (∂r̂ − r̂ ⟨r̂, ∂r̂⟩/d) / ‖r‖_rms`, covectors on
/// `2^(−24)`.
pub fn ratio_adjoint(read: &[i32], scale: i128, cov: &[i64]) -> Result<Vec<i64>> {
    if scale == 0 {
        return Ok(vec![0; cov.len()]);
    }
    let dot: i128 = read.iter().zip(cov).map(|(&a, &b)| a as i128 * b as i128).sum(); // 2^(−40)
    let mean = div_nearest(dot, read.len() as i128);
    collect_exact(read.iter().zip(cov).map(|(&a, &b)| fit64(div_nearest((b as i128 - release(mean * a as i128, 2 * FACE_BITS)) << FACE_BITS, scale))))
}

/// The exact comparison of two sections' codes: does `new` code strictly fewer bits than `old`?
/// `Π p_new > Π p_old`, over the products of their faces' numerators and denominators.
///
/// [definition; agent-inferred, October 27] **The certificate decided by partition.** The products
/// are compared through their logarithms first: each numerator and denominator `v` is read on
/// `2^(−CERTIFICATE_DIGITS)` ([`log2_reading`]), whose reading lies within `CERTIFICATE_SLACK`
/// grains of `log₂ v`. When the two sides' summed readings differ by more than every reading's
/// slack together, the sign of the difference is the sign of `log₂ Π p_new − log₂ Π p_old`, and so
/// the answer of the exact comparison; only inside that band are the products formed
/// ([`fewer_bits_exact`]). The answer is always the exact comparison's: the readings partition the
/// sections into those they decide and those the products decide. The readings are an integer sum,
/// so any partition of the faces sums them to the same bits. Measured October 25, the products
/// took 0.5 s a section at 320 streams and bounded the card's pass. The readings hold for positive
/// values only: a zero mass or total (never a face's, whose masses are at least one; Epime's review
/// of October 27 named the witness `[(0, 3)]` against `[(0, 2)]`) is decided by the products.
pub fn fewer_bits(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    if old.iter().chain(new).any(|&(m, t)| m == 0 || t == 0) {
        return fewer_bits_exact(old, new);
    }
    let side = |faces: &[(u128, u128)]| -> i128 { faces.par_iter().map(|&(m, t)| log2_reading(m) - log2_reading(t)).sum() };
    let difference = side(new) - side(old);
    let slack = CERTIFICATE_SLACK * 2 * (old.len() + new.len()) as i128;
    if difference > slack {
        return checked(true, old, new);
    }
    if difference < -slack {
        return checked(false, old, new);
    }
    fewer_bits_exact(old, new)
}

/// [definition; agent-inferred, November 2, the field's §16.23] **The certificate on a weighed code**: does `new` code
/// strictly fewer bits than `old` when each region's code is weighed by its state's `m/K` (the order-averaged joint
/// code)? `spans` gives each region's open sites (its run of consecutive pairs) and its `(m, K)`. Where every weight is
/// one it is [`fewer_bits`], the products. Otherwise the products cannot be formed (a rational power of a product), so
/// it is decided by partition alone: each region's readings are summed exactly, the difference
/// `ΔW = Σ_r (m_r/K_r) Σ_(i∈r) (log₂ p_new − log₂ p_old)` and its slack `Σ_r (m_r/K_r) · CERTIFICATE_SLACK · 2 · 2|r|`
/// are exact rationals of the readings, and the sign of `ΔW` decides once it passes the slack. The readings are read
/// at `CERTIFICATE_DIGITS` and, where the slack holds the difference, again at [`WEIGHED_DIGITS`], the readings' own
/// floor (their mantissa is released at `2^(−62)`); a difference still inside the slack there is a tie at that floor,
/// and a tie codes no fewer bits.
pub fn fewer_bits_weighed(old: &[(u128, u128)], new: &[(u128, u128)], spans: &[(usize, u64, u64)]) -> bool {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    if spans.iter().all(|&(_, m, k)| m == k) {
        return fewer_bits(old, new);
    }
    if old.iter().chain(new).any(|&(m, t)| m == 0 || t == 0) {
        return false;
    }
    for digits in [CERTIFICATE_DIGITS, WEIGHED_DIGITS] {
        let (mut difference, mut slack) = (BigRational::from_integer(BigInt::from(0)), BigRational::from_integer(BigInt::from(0)));
        let mut at = 0usize;
        for &(count, m, k) in spans {
            let range = at..at + count;
            at += count;
            let side = |faces: &[(u128, u128)]| -> i128 { faces[range.clone()].par_iter().map(|&(mm, t)| log2_reading_at(mm, digits) - log2_reading_at(t, digits)).sum() };
            let w = BigRational::new(BigInt::from(m), BigInt::from(k));
            difference += &w * &BigRational::from_integer(BigInt::from(side(new) - side(old)));
            slack += &w * &BigRational::from_integer(BigInt::from(CERTIFICATE_SLACK * 2 * 2 * count as i128));
        }
        if difference > slack {
            return true;
        }
        if difference < -slack {
            return false;
        }
    }
    false
}

/// The weighed certificate's finer readings: the readings' own floor (a mantissa released at `2^(−62)` holds a
/// reading within one grain and `2^(−60)` of `log₂ v`, so three grains at `2^(−60)`).
pub const WEIGHED_DIGITS: u32 = 60;

/// [definition; agent-inferred, November 2, the field's §16.23] **A weighed code** on `2^(−20)` bits: each region's
/// code `Σ_(i∈r) −log₂ p_i` read at `m_r/K_r`, released once a region to the nearest (half away from zero), summed.
pub fn weighed_code(pairs: &[(u128, u128)], spans: &[(usize, u64, u64)]) -> i64 {
    let mut at = 0usize;
    let mut sum = 0i64;
    for &(count, m, k) in spans {
        let code: i64 = pairs[at..at + count].par_iter().map(|&(mm, t)| face_code(mm, t)).sum();
        at += count;
        sum += if m == k { code } else { div_nearest(code as i128 * m as i128, k as i128) as i64 };
    }
    sum
}

/// A decision the readings made. Built with the `certificate-check` feature, it is compared with the
/// products and a disagreement stops the run: the acceptance read that the partition decides as the
/// products do on every call of a whole pass. Without the feature it is the decision.
pub fn checked(decided: bool, old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    #[cfg(feature = "certificate-check")]
    assert_eq!(decided, fewer_bits_exact(old, new), "the certificate's readings decided against its products");
    let _ = (old, new);
    decided
}

/// The fractional digits of the certificate's logarithmic readings.
pub const CERTIFICATE_DIGITS: u32 = 32;

/// How far a reading may lie from `log₂ v`, in grains of `2^(−CERTIFICATE_DIGITS)`. With `μ` the
/// mantissa, `d_k` the digits and `ε_k ≥ 0` the logarithm each release at `2^(−62)` takes off
/// (`ε_k < 2^(−61)`, the mantissa staying in `[1, 2)`), the squarings unroll to
/// `log₂ μ = Σ_(k≤K) 2^(−k) d_k + 2^(−K) log₂ μ_K + Σ_(k≤K) 2^(−k) ε_k`, so a reading lies below
/// `log₂ v` by less than one grain and `2^(−60)` (the entry release included), never above it;
/// three grains hold that with room.
pub const CERTIFICATE_SLACK: i128 = 3;

/// `log₂ v` for `v ≥ 1` on `2^(−CERTIFICATE_DIGITS)`: the whole part from `v`'s width, then the
/// mantissa's binary digits by squaring (released at `2^(−62)`), halving it when it passes two.
/// A `v` wider than 63 bits enters through its leading 63 (a relative release below `2^(−62)`).
pub fn log2_reading(v: u128) -> i128 {
    log2_reading_at(v, CERTIFICATE_DIGITS)
}

/// `log₂ v` on `2^(−digits)`, `digits ≤ 60` ([`log2_reading`]).
pub fn log2_reading_at(v: u128, digits: u32) -> i128 {
    let v = v.max(1);
    let width = 128 - v.leading_zeros();
    let mut mantissa = if width > 63 { v >> (width - 63) } else { v << (63 - width) }; // in [2^62, 2^63)
    let mut fraction = 0i128;
    for _ in 0..digits {
        mantissa = (mantissa * mantissa) >> 62;
        fraction <<= 1;
        if mantissa >= 1u128 << 63 {
            fraction |= 1;
            mantissa >>= 1;
        }
    }
    ((width as i128 - 1) << digits) + fraction
}

/// The products themselves: `Π m_new · Π t_old > Π m_old · Π t_new`.
pub fn fewer_bits_exact(old: &[(u128, u128)], new: &[(u128, u128)]) -> bool {
    // The halves of a long product are formed together: an exact product is the same in any
    // grouping.
    fn product(v: &[u128]) -> BigUint {
        match v.len() {
            0 => BigUint::from(1u8),
            1 => BigUint::from(v[0]),
            n if n < 1 << 12 => product(&v[..n / 2]) * product(&v[n / 2..]),
            n => {
                let (a, b) = rayon::join(|| product(&v[..n / 2]), || product(&v[n / 2..]));
                a * b
            }
        }
    }
    let (om, ot): (Vec<u128>, Vec<u128>) = old.iter().cloned().unzip();
    let (nm, nt): (Vec<u128>, Vec<u128>) = new.iter().cloned().unzip();
    let ((pnm, pot), (pom, pnt)) = rayon::join(|| rayon::join(|| product(&nm), || product(&ot)), || rayon::join(|| product(&om), || product(&nt)));
    pnm * pot > pom * pnt
}

/// A covector entry on the deposit's grain `2^(−32)` from its family's natural grain: a material
/// family's `Σ δz x` on `2^(−40)` is released, a face family's `Σ δz` on `2^(−24)` raised. The moves
/// step through their chart ([`Tower::to_move_chart`]) and are not read here.
pub fn on_step_grain(grain: u32, v: i128) -> i128 {
    if grain == MATERIAL_BITS {
        release(v, COVECTOR_BITS + FACE_BITS - STEP_BITS)
    } else {
        v << (STEP_BITS - COVECTOR_BITS)
    }
}

/// The deposit's step for one entry: its first moment `m` (on `2^(−32)`) over the root of its
/// second `v`, at the rate `2^(−rate)`, on its family's own grain:
/// `((m ≪ grain) ≫ rate) / (⌊√v⌋ + 1)`. The tower's certificate halves it; the field deposits it
/// at this size (the step fluxes, Brandon, November 5).
pub fn deposit_step(m: i128, v: i128, grain: u32, rate: u32) -> i128 {
    deposit_over(m, deposit_root(v), grain, rate)
}

/// The deposit's divisor for a second moment `v`: `⌊√v⌋ + 1`.
pub fn deposit_root(v: i128) -> i128 {
    (v.max(0) as u128).isqrt() as i128 + 1
}

/// The deposit's step for a first moment `m` over its second moment's divisor `root`.
pub fn deposit_over(m: i128, root: i128, grain: u32, rate: u32) -> i128 {
    ((m << grain) >> rate) / root
}

/// A moment moved toward its input at the rate `2^(−rate)`: `m + release(g − m, rate)`, and at
/// least one grain when that release rounds to zero. Released to the nearest grain alone, a moment
/// within `2^(rate−1)` grains of its input never reaches it, so a contact that stops conducting
/// keeps its last moments (`|m| ≤ 3`, `v ≤ 127` grains) and the step `m/(√v + 2^(−32))` reads that
/// remainder as a covector of a quarter of the rate (measured October 23 on all 6,726 GSM8K
/// problems, the narrow tower: no weight stalled through pass 2; 980 had by pass 3 and 2,146 by
/// pass 4, the most of two contacts that had stopped conducting, each moving `2^(−9)` every section,
/// one from 0.64 at pass 2 to 15.9 at pass 5). A silent contact's drifted weights meet the residual
/// stream at full scale when it conducts again. Moved by a grain, the moment reaches its input.
pub fn toward(m: i128, g: i128, rate: u32) -> i128 {
    let step = release(g - m, rate);
    m + if step == 0 { (g - m).signum() } else { step }
}

/// `m / t` on `2^(−62)`, at least one grain; a total past `2^64` is re-based so the shift fits.
pub fn unit_of(m: u128, t: u128) -> u128 {
    let shift = (128 - t.leading_zeros()).saturating_sub(64);
    (((m >> shift) << UNIT_BITS) / (t >> shift).max(1)).clamp(1, 1u128 << UNIT_BITS)
}

/// `−log₂(m / t)` on `2^(−20)` bits, for any face's mass and total.
pub fn code_of(m: u128, t: u128) -> i64 {
    -(log2_face(unit_of(m, t), READ_BITS) as i64)
}
