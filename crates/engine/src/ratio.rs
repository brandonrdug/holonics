//! **The Ratio: the undivided pair and its one release.**
//!
//! step `(M, J) ← (γM + m, γJ + mc)`; compose `(γ₂,m₂,j₂)∘(γ₁,m₁,j₁) = (γ₂γ₁, γ₂m₁ + m₂, γ₂j₁ + j₂)`; release `y = J/M` once,
//! at the receiver; a row's exponential faces `2^z` on `2^(−62)`, its shares on `2^(−63)`
//!
//! Kind: the one move (THE_ENGINE §2): a sum at `γ = 1`, a chain at `γ ≠ 1`. Kernels: `field_exponential`, `field_series_check` (`hnn/contact.rs`).
//! Lean: `Computation/AttentionModeCompression` (`weighted_summary_associative`).
//! Atlas: `tower.field-one-region`.
//! Records: THE_CONSOLIDATION §2. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [definition; agent-inferred, November 1] **A contact row as a series** (the dispersing field's
/// §14.11; one row a head, §15.2): each term `2^z · μ` (its face and whole bits from [`Constitution::face`], `μ`
/// its multiplier on `2^(−62)`: `2^62` in the near field, a far source's weight, a crowd's count `· 2^62`
/// in the mass with `2^62` against its value sum) keeps its own exponent; the terms are summed whole,
/// shifted from the row's least exponent, in a carrier as wide as the row's own exponents need (never
/// past [`Declaration::row_bits`]); the current `ỹ = Σ e v / Σ e` is released once, to the nearest
/// numerator on the value's grain; and each term's share of the mass is formed once on `2^(−63)`. No
/// peak is subtracted and no term is released before the current: a source outscored by any number of
/// bits still enters the sums. Integer sums, so any order gives the same bits.
pub struct SeriesRow {
    pub(crate) span: usize,
    pub(crate) terms: Vec<(i64, u128, u128, u128, Vec<i128>)>,
}

impl SeriesRow {
    pub fn new(span: usize) -> Self {
        Self { span, terms: Vec::new() }
    }

    /// A term: its score's `(a, face)`, its mass multiplier, its value multiplier and its values.
    pub fn push(&mut self, (a, face): (i64, u128), mass: u128, value_mult: u128, value: &[i128]) {
        self.terms.push((a, face, mass, value_mult, value.to_vec()));
    }

    /// The released current (each value entry `div_nearest(Σ 2^(a − a₀) face μ_v v, Σ 2^(a − a₀) face
    /// μ)`) and each term's share `div_nearest(2^(a − a₀) face μ 2^63, Σ …)`.
    pub fn release(&self) -> (Vec<i128>, Vec<u64>) {
        use num_bigint::BigInt;
        // A receiver whose support holds no keyed source (§16.20) gathers nothing.
        if self.terms.is_empty() {
            return (vec![0; self.span], Vec::new());
        }
        let a0 = self.terms.iter().map(|t| t.0).min().unwrap_or(0);
        let mass_of = |t: &(i64, u128, u128, u128, Vec<i128>)| (BigInt::from(t.1) * BigInt::from(t.2)) << ((t.0 - a0) as usize);
        let mass: BigInt = self.terms.iter().map(mass_of).sum();
        let nearest = |x: BigInt| -> BigInt {
            let half: BigInt = &mass / 2;
            let negative = x < BigInt::from(0);
            let q: BigInt = (if negative { -x } else { x } + half) / &mass;
            if negative { -q } else { q }
        };
        let current = (0..self.span)
            .map(|r| {
                let sum: BigInt = self.terms.iter().map(|t| ((BigInt::from(t.1) * BigInt::from(t.3)) << ((t.0 - a0) as usize)) * BigInt::from(t.4[r])).sum();
                i128::try_from(nearest(sum)).unwrap_or(0)
            })
            .collect();
        let shares = self.terms.iter().map(|t| u64::try_from(nearest(mass_of(t) << SHARE_BITS as usize)).unwrap_or(u64::MAX)).collect();
        (current, shares)
    }
}

/// [definition; agent-inferred, November 1] **The definite words' and values' prefix sums** over a
/// region, one head (§14.10): `words[t]`, `values[t]` the sums of the definite sites' framed unit words
/// and framed values before place `t` (the span's entries), `counts[t]` their number, so a crowd's sums
/// are two reads.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Sums {
    pub words: Vec<i128>,
    pub values: Vec<i128>,
    pub counts: Vec<u64>,
    pub span: usize,
}

impl Sums {
    pub fn of(words: &[i64], values: &[i64], definite: &[bool], span: usize) -> Self {
        let sites = definite.len();
        let (mut w, mut v, mut c) = (vec![0i128; (sites + 1) * span], vec![0i128; (sites + 1) * span], vec![0u64; sites + 1]);
        for t in 0..sites {
            for r in 0..span {
                let on = i128::from(definite[t]);
                w[(t + 1) * span + r] = w[t * span + r] + on * words[t * span + r] as i128;
                v[(t + 1) * span + r] = v[t * span + r] + on * values[t * span + r] as i128;
            }
            c[t + 1] = c[t] + u64::from(definite[t]);
        }
        Self { words: w, values: v, counts: c, span }
    }

    pub(crate) fn count(&self, lo: usize, hi: usize) -> u64 {
        self.counts[hi + 1] - self.counts[lo]
    }

    pub(crate) fn words(&self, lo: usize, hi: usize) -> Vec<i128> {
        (0..self.span).map(|r| self.words[(hi + 1) * self.span + r] - self.words[lo * self.span + r]).collect()
    }

    pub(crate) fn value(&self, lo: usize, hi: usize, r: usize) -> i128 {
        self.values[(hi + 1) * self.span + r] - self.values[lo * self.span + r]
    }
}

/// `⌊log₂ d⌋` for `d ≥ 1`, the falloff's octave in bits (§2.3).
pub fn octave(d: usize) -> u32 {
    usize::BITS - 1 - d.leading_zeros()
}

// The items this object owns that stood in the October tower until C5 (#603), each as it stood.

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

/// `m / t` on `2^(−62)`, at least one grain; a total past `2^64` is re-based so the shift fits.
pub fn unit_of(m: u128, t: u128) -> u128 {
    let shift = (128 - t.leading_zeros()).saturating_sub(64);
    (((m >> shift) << UNIT_BITS) / (t >> shift).max(1)).clamp(1, 1u128 << UNIT_BITS)
}

/// `−log₂(m / t)` on `2^(−20)` bits, for any face's mass and total.
pub fn ratio_code(m: u128, t: u128) -> i64 {
    -(log2_face(unit_of(m, t), READ_BITS) as i64)
}

/// `x` released `bits` coarser, to the nearest numerator, half away from zero.
pub fn release(x: i128, bits: u32) -> i128 {
    if bits == 0 {
        return x;
    }
    let half = 1i128 << (bits - 1);
    if x >= 0 { (x + half) >> bits } else { -((-x + half) >> bits) }
}

/// [definition; agent-inferred] **The exponential's navigator face at `2^(−62)`**: `2^(2^(−i))`
/// for `i = 1..=X`, each the floor of the exact integer square root of its predecessor's square
/// re-based, from `2^1`. A value `2^(n + f)` with `f` on `2^(−X)` is `2^n` times the product of the
/// factors the binary digits of `f` select, each product released at `2^(−62)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exponential {
    roots: Vec<u128>,
    digits: u32,
}

/// The grain of `ln 2`'s face, `2^(−30)`.
pub const LN2_BITS: u32 = 30;

/// [definition; agent-inferred] **`ln 2` as its navigator's face** on `2^(−30)`: the series
/// `Σ_(k≥1) 1/(k 2^k)`, its terms to `k = 60` read at `2^(−60)` and the sum released to `2^(−30)`
/// (the tail past `k = 60` and the terms' floors stay below `2^(−50)`).
pub fn ln2_face() -> i128 {
    let sum: i128 = (1..=60).map(|k: i128| (1i128 << (60 - k)) / k).sum();
    release(sum, 60 - LN2_BITS)
}

/// [definition; agent-inferred] **`log₂ p` on `2^(−X)`** for `p` on `2^(−62)`, `0 < p ≤ 2^62`: the
/// inverse face of the `ln 2`/exponential navigator (`log₂` undoes [`Exponential`]). The whole part
/// comes from the numerator's width, then `X` binary digits of the mantissa's logarithm, each read
/// by squaring the mantissa (released at `2^(−62)`) and halving it when it passes two.
pub fn log2_face(p: u128, digits: u32) -> i128 {
    debug_assert!(p > 0 && p <= 1u128 << UNIT_BITS);
    let width = 128 - p.leading_zeros(); // p in [2^(width−1), 2^width)
    let whole = width as i128 - 1 - UNIT_BITS as i128; // ≤ 0
    let mut mantissa = p << (UNIT_BITS + 1 - width); // in [2^62, 2^63)
    let mut fraction = 0i128;
    for _ in 0..digits {
        mantissa = (mantissa * mantissa) >> UNIT_BITS;
        fraction <<= 1;
        if mantissa >= 2u128 << UNIT_BITS {
            fraction |= 1;
            mantissa >>= 1;
        }
    }
    (whole << digits) + fraction
}

impl Exponential {
    pub fn new(digits: u32) -> Self {
        let mut roots = Vec::with_capacity(digits as usize);
        let mut previous: u128 = 2u128 << UNIT_BITS;
        for _ in 0..digits {
            previous = (previous << UNIT_BITS).isqrt();
            roots.push(previous);
        }
        Self { roots, digits }
    }
    /// The navigator's resident face, `2^(2^(−i))` on `2^(−62)` for `i = 1..=X`.
    pub fn roots(&self) -> &[u128] {
        &self.roots
    }

    /// `2^(x / 2^X)` for `x ≤ 0` on `2^(−62)`, at least one grain (a class is never released to
    /// zero mass by its exponent).
    pub fn below_one(&self, x: i128) -> u128 {
        debug_assert!(x <= 0);
        let whole = (-x) >> self.digits; // floor of the magnitude's whole part
        let frac = (-x) & ((1i128 << self.digits) - 1);
        // 2^(−whole − frac) = 2^(−whole − 1) · 2^(1 − frac) when frac > 0.
        let (shift, rest) = if frac == 0 { (whole, 0i128) } else { (whole + 1, (1i128 << self.digits) - frac) };
        let mut value: u128 = 1u128 << UNIT_BITS;
        for i in 0..self.digits {
            if rest & (1i128 << (self.digits - 1 - i)) != 0 {
                value = (value * self.roots[i as usize]) >> UNIT_BITS;
            }
        }
        let shifted = if shift >= 128 { 0 } else { value >> shift };
        shifted.max(1)
    }
}

#[cfg(test)]
mod tests {
    use super::div_nearest;

    /// [measurement; theory, November 15] **The nearest quotient keeps its value under an even factor**: `⌊(|x| + ⌊m/2⌋)/m⌋`
    /// and `⌊(|x|K + ⌊mK/2⌋)/(mK)⌋` with `K` even differ only where `2|x| + m` is a multiple of `2m` with `m` odd, and an odd
    /// number never is. The card's series row weighs a source by one where the host weighs it by `2^62` and leans on this
    /// (`row_limbs`); read here over odd and even divisors, both signs and the multiplier itself.
    #[test]
    fn the_nearest_quotient_keeps_its_value_under_an_even_factor() {
        for m in 1i128..=97 {
            for x in -700i128..=700 {
                let q = div_nearest(x, m);
                for k in [1u32, 2, 3, 7, 62] {
                    assert_eq!(div_nearest(x << k, m << k), q, "x={x} m={m} k={k}");
                }
                assert_eq!(div_nearest(6 * x, 6 * m), q, "x={x} m={m} k=6");
            }
        }
    }
}
