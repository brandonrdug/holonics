//! **The overture's intake** (#146; records `2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE…` §§2
//! and 5): the exterior boundary where an inherited model's coefficients arrive, and the only place
//! they are ever floats.
//!
//! [definition] **A stored word decodes exactly to its dyadic ratio.** An IEEE-754 word of a format
//! with `p` stored significand bits and `e` exponent bits is read as three integer fields, and its
//! value is `± significand · 2^ulp`, with the hidden leading one restored on a normal word and the
//! exponent `ulp = max(E, 1) − bias − p`, `bias = 2^(e−1) − 1`. An all-ones exponent field is an
//! infinity or a NaN and is refused: nothing is invented for it. `bfloat16` is the format
//! `(p, e) = (7, 8)`, the upper half of a `binary32` word, so it decodes as that word does.
//! Lean owns the law (`HolonicsResearch/Foundation/ExteriorIntake`): [`FloatFormat::decode`] is
//! `decode`, its `Ok` arm `decode_exact_on_finite` and its refusal `decode_refuses_nonfinite`;
//! [`FloatFormat`] is `FloatFormat` and [`Dyadic`] the codeword's `value` in lowest terms.
//!
//! [definition; agent-inferred, October 30] **The file is exterior codec information.** A
//! `safetensors` file is an eight-byte little-endian header length, a JSON header naming each
//! tensor's dtype, shape and byte range, and the tensors' bytes. [`Safetensors::read`] admits the
//! three float formats a released model is stored in, checks that each tensor's range holds its
//! shape and that the ranges tile the data exactly, and keeps the names and shapes only as the
//! codec's account of where the coefficients came from: they are never native identities. The
//! header reader admits only what the format's header uses (objects, arrays, strings and
//! non-negative integers) and refuses the rest.
//!
//! The coefficients enter once, here, as the initial configuration of native navigators and the
//! opening constitution of native owners (the record's §3 table); the engine is never graded by
//! agreement with the source model, and the source model is never run.
use std::collections::BTreeMap;
use std::ops::Range;

use num_bigint::BigInt;
use num_traits::One;
use thiserror::Error;

use crate::hnn::keyed_modes::release;
use crate::hnn::tower::TowerError;
use crate::ratio::Rat;

/// An IEEE-754 binary interchange format, as its two field widths.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FloatFormat {
    /// Stored significand bits: 10, 7 and 23 for `binary16`, `bfloat16` and `binary32`.
    pub significand_bits: u32,
    /// Exponent field bits: 5, 8 and 8.
    pub exponent_bits: u32,
}

impl FloatFormat {
    pub const BINARY16: FloatFormat = FloatFormat { significand_bits: 10, exponent_bits: 5 };
    pub const BFLOAT16: FloatFormat = FloatFormat { significand_bits: 7, exponent_bits: 8 };
    pub const BINARY32: FloatFormat = FloatFormat { significand_bits: 23, exponent_bits: 8 };

    /// The stored word's width in bits.
    pub fn width(self) -> u32 {
        1 + self.exponent_bits + self.significand_bits
    }

    /// The exponent bias, `2^(e−1) − 1`.
    pub fn bias(self) -> i32 {
        (1i32 << (self.exponent_bits - 1)) - 1
    }

    /// The word's exact value, or the refusal of a nonfinite word. Bits above the format's width
    /// are refused as a malformed word, never masked.
    pub fn decode(self, word: u32) -> Result<Dyadic, IntakeRefusal> {
        let (p, e) = (self.significand_bits, self.exponent_bits);
        if self.width() < 32 && word >> self.width() != 0 {
            return Err(IntakeRefusal::WiderThanFormat { word, format: self });
        }
        let fraction = i64::from(word & ((1u32 << p) - 1));
        let raw = (word >> p) & ((1u32 << e) - 1);
        if raw == (1u32 << e) - 1 {
            return Err(IntakeRefusal::NonFinite { word, format: self });
        }
        let negative = word >> (p + e) & 1 == 1;
        let significand = if raw == 0 { fraction } else { (1i64 << p) + fraction };
        let ulp = raw.max(1) as i32 - self.bias() - p as i32;
        Ok(Dyadic::reduced(if negative { -significand } else { significand }, ulp))
    }
}

/// An exact dyadic ratio `numerator · 2^exponent` in lowest terms: the numerator odd, or zero with
/// exponent zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Dyadic {
    pub numerator: i64,
    pub exponent: i32,
}

impl Dyadic {
    /// `numerator · 2^exponent` with the numerator's factors of two moved into the exponent.
    pub fn reduced(numerator: i64, exponent: i32) -> Dyadic {
        if numerator == 0 {
            return Dyadic { numerator: 0, exponent: 0 };
        }
        let shift = numerator.trailing_zeros();
        Dyadic { numerator: numerator >> shift, exponent: exponent + shift as i32 }
    }

    /// The exact value as a ratio.
    pub fn value(self) -> Rat {
        let n = BigInt::from(self.numerator);
        let power = BigInt::one() << self.exponent.unsigned_abs();
        if self.exponent >= 0 { Rat::from_integer(n * power) } else { Rat::new(n, power) }
    }
}

/// A refusal at the intake. Every arm names what was refused; nothing is rounded, masked or
/// skipped in its place.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum IntakeRefusal {
    #[error("a nonfinite word {word:#x} of {format:?}: an infinity or a NaN has no value")]
    NonFinite { word: u32, format: FloatFormat },
    #[error("a word {word:#x} wider than {format:?}")]
    WiderThanFormat { word: u32, format: FloatFormat },
    #[error("the file ends before its header does")]
    Truncated,
    #[error("the header is malformed at its byte {at}")]
    MalformedHeader { at: usize },
    #[error("the header entry {name} is not a tensor: {what}")]
    MalformedEntry { name: String, what: &'static str },
    #[error("the tensor {name} is stored as {dtype}, which is not a float format the intake admits")]
    UnadmittedDtype { name: String, dtype: String },
    #[error("the tensor {name}'s byte range does not hold its shape")]
    Extent { name: String },
    #[error("the tensors' byte ranges do not tile the data exactly")]
    Tiling,
    #[error("the tensor {name} is named twice")]
    Duplicate { name: String },
    #[error("the tensor {name} is not in the file")]
    Absent { name: String },
    #[error("the tensor {name} does not have the block's declared shape")]
    BlockShape { name: String },
    #[error("the founding refused: {what}")]
    Founding { what: &'static str },
    #[error(transparent)]
    Tower(#[from] TowerError),
}

/// One tensor's account in the file: its name and shape as exterior codec information, its
/// format, and its byte range within the data.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TensorEntry {
    pub name: String,
    pub format: FloatFormat,
    pub shape: Vec<usize>,
    pub range: Range<usize>,
}

impl TensorEntry {
    /// The number of coefficients, the product of the shape (one for a scalar).
    pub fn count(&self) -> usize {
        self.shape.iter().product()
    }
}

/// A `safetensors` file read at the boundary: its tensors in the order of their byte ranges.
#[derive(Clone, Debug)]
pub struct Safetensors<'a> {
    data: &'a [u8],
    pub entries: Vec<TensorEntry>,
}

impl<'a> Safetensors<'a> {
    /// Reads the header and checks every tensor's range against its shape and the data's extent.
    pub fn read(bytes: &'a [u8]) -> Result<Safetensors<'a>, IntakeRefusal> {
        let length = bytes.get(..8).ok_or(IntakeRefusal::Truncated)?;
        let length = usize::try_from(u64::from_le_bytes(length.try_into().expect("eight bytes"))).map_err(|_| IntakeRefusal::Truncated)?;
        let end = length.checked_add(8).filter(|&end| end <= bytes.len()).ok_or(IntakeRefusal::Truncated)?;
        let (header, data) = (&bytes[8..end], &bytes[end..]);
        let Json::Object(fields) = Header { text: header, at: 0 }.document()? else {
            return Err(IntakeRefusal::MalformedHeader { at: 0 });
        };
        let mut entries = Vec::new();
        for (name, field) in fields {
            if name == "__metadata__" {
                continue;
            }
            entries.push(entry(name, field)?);
        }
        entries.sort_by_key(|t| (t.range.start, t.range.end));
        let mut next = 0;
        for t in &entries {
            if t.range.start != next {
                return Err(IntakeRefusal::Tiling);
            }
            next = t.range.end;
        }
        if next != data.len() {
            return Err(IntakeRefusal::Tiling);
        }
        Ok(Safetensors { data, entries })
    }

    /// The tensor's coefficients, each decoded exactly, in its stored (row-major) order.
    pub fn decoded(&self, entry: &TensorEntry) -> Result<Vec<Dyadic>, IntakeRefusal> {
        let bytes = (entry.format.width() / 8) as usize;
        self.data[entry.range.clone()]
            .chunks_exact(bytes)
            .map(|w| entry.format.decode(w.iter().rev().fold(0u32, |acc, &b| acc << 8 | u32::from(b))))
            .collect()
    }
}

/// [definition; agent-inferred, October 30] **What a founding released** (record
/// `2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE…` §6): every coefficient a founding wrote, released
/// onto its material grain to the nearest once its composition is formed; how many kept a remainder
/// below the grain beside their leading bits, how many released to zero, and the remainders' summed
/// magnitude on `2^(−REMAINDER_BITS)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Released {
    pub coefficients: usize,
    pub remaindered: usize,
    pub zeroed: usize,
    /// `Σ |remainder|` on `2^(−REMAINDER_BITS)`.
    pub remainder: u128,
}

/// The grain the remainders are summed on, below every remainder a founding leaves: a `bfloat16`
/// chart (places down to `−133`) composed with a gain and a `2^(−60)` face lands at or above
/// `2^(−119)` on the source's file, and a coarser place is refused, never rounded.
pub const REMAINDER_BITS: u32 = 128;

impl Released {
    /// `numerator · 2^exponent` released onto `2^(−bits)` to the nearest, half away from zero, its
    /// remainder counted: the numerator on the grain. Refused when it outgrows `i32`, or when the
    /// remainder lies below the receipt's grain.
    pub fn take(&mut self, numerator: i128, exponent: i32, bits: u32) -> Result<i32, IntakeRefusal> {
        let outgrown = IntakeRefusal::Founding { what: "a founded coefficient outgrew its 32-bit carrier" };
        self.coefficients += 1;
        let shift = exponent + bits as i32;
        let on = if shift >= 0 {
            if numerator != 0 && (shift > 31 || numerator.unsigned_abs() >> (31 - shift) != 0) {
                return Err(outgrown);
            }
            numerator << shift
        } else {
            let s = shift.unsigned_abs();
            let below = exponent + REMAINDER_BITS as i32;
            if s > 126 || below < 0 {
                return Err(IntakeRefusal::Founding { what: "a remainder below the receipt's grain" });
            }
            let q = release(numerator, s);
            let r = numerator - (q << s);
            if r != 0 {
                if q == 0 { self.zeroed += 1 } else { self.remaindered += 1 }
                self.remainder = self.remainder.checked_add(r.unsigned_abs() << below).ok_or(IntakeRefusal::Founding { what: "the remainders outgrew their receipt" })?;
            }
            q
        };
        i32::try_from(on).map_err(|_| outgrown)
    }

    /// Two receipts as one.
    pub fn joined(self, other: Released) -> Option<Released> {
        Some(Released {
            coefficients: self.coefficients + other.coefficients,
            remaindered: self.remaindered + other.remaindered,
            zeroed: self.zeroed + other.zeroed,
            remainder: self.remainder.checked_add(other.remainder)?,
        })
    }
}

/// [definition; agent-inferred, October 30] **The shape a source declares for its attention
/// blocks**, pinned at intake from its configuration: the residual width, the query heads and the
/// key/value heads they share (each key/value head serves `heads/kv_heads` query heads in order),
/// each head's dimension `d`, and the rotary base `θ`: pair `m` of a head, its coordinates `m` and
/// `m + d/2`, turns `θ^(−2m/d)` radians a place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AttentionShape {
    pub width: usize,
    pub heads: usize,
    pub kv_heads: usize,
    pub head_dim: usize,
    pub theta: u64,
}

/// [definition; agent-inferred, October 30] **An attention block as its source stores it**: the
/// input norm's gain `g` (`width`), the projections `Q` (`heads·d × width`), `K` and `V`
/// (`kv_heads·d × width`) and `O` (`width × heads·d`), row-major, every coefficient exact. The
/// names they were stored under stay with the file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttentionBlock {
    pub shape: AttentionShape,
    pub gain: Vec<Dyadic>,
    pub query: Vec<Dyadic>,
    pub key: Vec<Dyadic>,
    pub value: Vec<Dyadic>,
    pub output: Vec<Dyadic>,
}

/// The source's attention computed at the boundary ([`AttentionBlock::reference`]), on
/// `2^(−REFERENCE_BITS)`: each site's heads (`d` coordinates a head) and the output projection's
/// read of them (`width`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttentionReference {
    pub heads: Vec<Vec<Vec<i128>>>,
    pub output: Vec<Vec<i128>>,
}

/// The reference's grain: twenty-four bits finer than the native face's `2^(−16)`.
pub const REFERENCE_BITS: u32 = 40;

impl AttentionBlock {
    /// The block read from its five tensors (gain, query, key, value, output), each checked against
    /// the declared shape.
    pub fn read(file: &Safetensors, names: [&str; 5], shape: AttentionShape) -> Result<Self, IntakeRefusal> {
        let AttentionShape { width: w, heads: h, kv_heads: hk, head_dim: d, theta } = shape;
        if w == 0 || hk == 0 || d == 0 || d % 2 != 0 || h % hk != 0 || h == 0 || theta < 2 {
            return Err(IntakeRefusal::Founding { what: "an attention shape of nonempty heads, an even head dimension, query heads a multiple of key/value heads and a rotary base above one" });
        }
        let shapes = [vec![w], vec![h * d, w], vec![hk * d, w], vec![hk * d, w], vec![w, h * d]];
        let mut parts = Vec::with_capacity(5);
        for (name, expected) in names.iter().zip(shapes) {
            let entry = file.entries.iter().find(|e| e.name == *name).ok_or_else(|| IntakeRefusal::Absent { name: (*name).to_string() })?;
            if entry.shape != expected {
                return Err(IntakeRefusal::BlockShape { name: (*name).to_string() });
            }
            parts.push(file.decoded(entry)?);
        }
        let [gain, query, key, value, output] = <[Vec<Dyadic>; 5]>::try_from(parts).map_err(|_| IntakeRefusal::Founding { what: "five parts" })?;
        Ok(Self { shape, gain, query, key, value, output })
    }

    /// [definition; agent-inferred, October 30] **The source's attention, computed once at the
    /// boundary** (record §6), the extraction check's reference and never a forward the engine runs.
    /// For inputs `n_t` of unit power on `2^(−input_bits)` (the source's norm `n/√(mean n² + ε)` is
    /// then `n/√(1 + ε)`; the reference omits `ε`, whose share is `ε/2` relative): `q = Q (g ⊙ n)`,
    /// `k` and `v` likewise (a grouped head's shared), each pair `(m, m + d/2)` of `q` and `k` turned
    /// by `e^(i t ω_m)` at place `t`, and each head
    /// `o_i = Σ_(j≤i) e^(s_ij − max_j s_ij) v_j / Σ_(j≤i) e^(s_ij − max_j s_ij)`,
    /// `s_ij = q'_i · k'_j / √d`; then the block's read `O [o_0; …]`. The projections and the read
    /// are exact sums released once onto `2^(−40)`; `ω_m` ([`rotary_rate`]), the turn and the
    /// exponential are faces on `2^(−40)`, each series summed until its term releases to zero, and
    /// every other product is released onto `2^(−40)`. `√d` must be an integer.
    pub fn reference(&self, inputs: &[Vec<i64>], input_bits: u32) -> Result<AttentionReference, IntakeRefusal> {
        const R: u32 = REFERENCE_BITS;
        let refused = |what| IntakeRefusal::Founding { what };
        let AttentionShape { width: w, heads: h, kv_heads: hk, head_dim: d, theta } = self.shape;
        let root = d.isqrt();
        if root * root != d {
            return Err(refused("a head dimension whose square root is not an integer"));
        }
        let unit = (w as i128) << (2 * input_bits);
        if inputs.iter().any(|n| n.len() != w || n.iter().map(|&v| v as i128 * v as i128).sum::<i128>() != unit) {
            return Err(refused("a reference input that is not of the block's width and unit power"));
        }
        // g ⊙ n exact, each coordinate a numerator on 2^(gain exponent − input_bits).
        let scaled: Vec<Vec<(i128, i32)>> = inputs.iter().map(|n| n.iter().zip(&self.gain).map(|(&v, g)| (g.numerator as i128 * v as i128, g.exponent - input_bits as i32)).collect()).collect();
        // A row of a projection against an exact vector: the exact sum on 2^(−80), released onto 2^(−40).
        let project = |rows: &[Dyadic], row: usize, x: &[(i128, i32)]| -> Result<i128, IntakeRefusal> {
            let mut sum = 0i128;
            for (c, &(xv, xe)) in rows[row * w..(row + 1) * w].iter().zip(x) {
                let place = c.exponent + xe + 2 * R as i32;
                if place < 0 || place > 100 {
                    return Err(refused("a reference product outside its carrier"));
                }
                let term = (c.numerator as i128).checked_mul(xv).and_then(|v| v.checked_mul(1i128 << place)).ok_or(refused("a reference product outgrew its carrier"))?;
                sum = sum.checked_add(term).ok_or(refused("a reference sum outgrew its carrier"))?;
            }
            Ok(release(sum, R))
        };
        let mul = |a: i128, b: i128| -> Result<i128, IntakeRefusal> { a.checked_mul(b).map(|v| release(v, R)).ok_or(refused("a reference product outgrew its carrier")) };
        let rates: Vec<(i128, i128)> = (0..d / 2).map(|m| cis(rotary_rate(theta, m, d, R), R)).collect::<Result<_, _>>()?;
        let group = h / hk;
        let mut heads = vec![vec![vec![0i128; d]; h]; inputs.len()];
        for head in 0..h {
            let kv = head / group;
            let (mut qs, mut ks, mut vs) = (Vec::new(), Vec::new(), Vec::new());
            for (t, x) in scaled.iter().enumerate() {
                let (mut q, mut k, mut v) = (vec![0i128; d], vec![0i128; d], vec![0i128; d]);
                for r in 0..d {
                    q[r] = project(&self.query, head * d + r, x)?;
                    k[r] = project(&self.key, kv * d + r, x)?;
                    v[r] = project(&self.value, kv * d + r, x)?;
                }
                // e^(i t ω_m), the place's turn, as the t-th power of the rate's turn.
                for (m, &(c1, s1)) in rates.iter().enumerate() {
                    let (mut c, mut s) = (1i128 << R, 0i128);
                    for _ in 0..t {
                        (c, s) = (mul(c, c1)? - mul(s, s1)?, mul(c, s1)? + mul(s, c1)?);
                    }
                    for z in [&mut q, &mut k] {
                        let (a, b) = (z[m], z[m + d / 2]);
                        (z[m], z[m + d / 2]) = (mul(a, c)? - mul(b, s)?, mul(b, c)? + mul(a, s)?);
                    }
                }
                qs.push(q);
                ks.push(k);
                vs.push(v);
            }
            for i in 0..inputs.len() {
                let scores: Vec<i128> = (0..=i).map(|j| Ok(div_nearest(qs[i].iter().zip(&ks[j]).map(|(&a, &b)| mul(a, b)).sum::<Result<i128, _>>()?, root as i128))).collect::<Result<_, IntakeRefusal>>()?;
                let peak = *scores.iter().max().expect("a site reads itself");
                let weights: Vec<i128> = scores.iter().map(|&s| exp_below(peak - s, R)).collect::<Result<_, _>>()?;
                let mass: i128 = weights.iter().sum();
                for r in 0..d {
                    let carried = weights.iter().zip(&vs).map(|(&e, v)| e.checked_mul(v[r]).ok_or(refused("a reference product outgrew its carrier"))).sum::<Result<i128, _>>()?;
                    heads[i][head][r] = div_nearest(carried, mass);
                }
            }
        }
        // The read O [o_0; …; o_(H−1)], exact on 2^(−80) and released onto 2^(−40).
        let cols = h * d;
        let mut output = vec![vec![0i128; w]; inputs.len()];
        for (i, out) in output.iter_mut().enumerate() {
            let joined: Vec<(i128, i32)> = heads[i].iter().flatten().map(|&v| (v, -(R as i32))).collect();
            for (o, slot) in out.iter_mut().enumerate() {
                let mut sum = 0i128;
                for (c, &(xv, xe)) in self.output[o * cols..(o + 1) * cols].iter().zip(&joined) {
                    let place = c.exponent + xe + 2 * R as i32;
                    if !(0..=100).contains(&place) {
                        return Err(refused("a reference product outside its carrier"));
                    }
                    let term = (c.numerator as i128).checked_mul(xv).and_then(|v| v.checked_mul(1i128 << place)).ok_or(refused("a reference product outgrew its carrier"))?;
                    sum = sum.checked_add(term).ok_or(refused("a reference sum outgrew its carrier"))?;
                }
                *slot = release(sum, R);
            }
        }
        Ok(AttentionReference { heads, output })
    }
}

/// `x / k` to the nearest integer, half away from zero.
pub fn div_nearest(x: i128, k: i128) -> i128 {
    if x >= 0 { (x + k / 2) / k } else { -((-x + k / 2) / k) }
}

/// [definition; agent-inferred, October 30] **A rotary rate as its navigator's face**: `ω = θ^(−2m/d)`
/// on `2^(−bits)`, read by its constraint in integers. The largest numerator `N` with
/// `N^d θ^(2m) ≤ 2^(bits·d)` is found by halving, then `N + 1` is taken when `(2N + 1)^d θ^(2m)` is
/// at most `2^((bits + 1)·d)` (the face to the nearest).
pub fn rotary_rate(theta: u64, m: usize, d: usize, bits: u32) -> i128 {
    let base = BigInt::from(theta).pow(2 * m as u32);
    let fits = |n: i128, extra: u32| BigInt::from(n).pow(d as u32) * &base <= BigInt::one() << ((bits + extra) as usize * d);
    let (mut low, mut high) = (0i128, 1i128 << bits);
    // `low` fits; past `high` nothing does (ω ≤ 1).
    while low < high {
        let mid = low + (high - low + 1) / 2;
        if fits(mid, 0) { low = mid } else { high = mid - 1 }
    }
    if fits(2 * low + 1, 1) { low + 1 } else { low }
}

/// `e^(iφ)` on `2^(−bits)` for `|φ| ≤ 1` on `2^(−bits)`: the series summed until its term releases
/// to zero.
pub fn cis(phi: i128, bits: u32) -> Result<(i128, i128), IntakeRefusal> {
    if phi.unsigned_abs() > 1u128 << bits {
        return Err(IntakeRefusal::Founding { what: "a turn's series read past one radian" });
    }
    let (mut term, mut sum) = ((1i128 << bits, 0i128), (1i128 << bits, 0i128));
    let mut k = 1i128;
    loop {
        // term · iφ / k
        term = (div_nearest(release(-term.1 * phi, bits), k), div_nearest(release(term.0 * phi, bits), k));
        if term == (0, 0) {
            return Ok(sum);
        }
        sum = (sum.0 + term.0, sum.1 + term.1);
        k += 1;
    }
}

/// `e^(−y)` on `2^(−bits)` for `y ≥ 0` on `2^(−bits)`: `y` halved `s` times to at most one,
/// `e^(−y/2^s)` by its series summed until a term releases to zero, then squared `s` times, each
/// square released to the grain. A `y` of `bits` or more weighs below `2^(−bits−1)` and reads zero.
fn exp_below(y: i128, bits: u32) -> Result<i128, IntakeRefusal> {
    if y < 0 {
        return Err(IntakeRefusal::Founding { what: "an exponential below the peak read above it" });
    }
    if y >= (bits as i128) << bits {
        return Ok(0);
    }
    let halvings = (128 - y.leading_zeros()).saturating_sub(bits);
    let z = release(y, halvings);
    let (mut term, mut sum, mut k) = (1i128 << bits, 1i128 << bits, 1i128);
    loop {
        term = div_nearest(release(-term * z, bits), k);
        if term == 0 {
            break;
        }
        sum += term;
        k += 1;
    }
    for _ in 0..halvings {
        sum = release(sum * sum, bits);
    }
    Ok(sum)
}

/// `log₂ e = 1/ln 2` on `2^(−60)`: `ln 2 = Σ_(k≥1) 1/(k 2^k)` with its terms to `k = 64` on
/// `2^(−64)` (the tail and the terms' floors below `2^(−57)`), inverted once.
pub fn log2_e_face() -> i128 {
    let ln2: i128 = (1..=64).map(|k: i128| (1i128 << (64 - k)) / k).sum();
    div_nearest(1i128 << 124, ln2)
}

/// One header entry checked as a tensor.
fn entry(name: String, field: Json) -> Result<TensorEntry, IntakeRefusal> {
    let malformed = |what| IntakeRefusal::MalformedEntry { name: name.clone(), what };
    let Json::Object(mut fields) = field else { return Err(malformed("not an object")) };
    let Some(Json::String(dtype)) = fields.remove("dtype") else { return Err(malformed("no dtype")) };
    let format = match dtype.as_str() {
        "F16" => FloatFormat::BINARY16,
        "BF16" => FloatFormat::BFLOAT16,
        "F32" => FloatFormat::BINARY32,
        _ => return Err(IntakeRefusal::UnadmittedDtype { name, dtype }),
    };
    let integers = |value: Option<Json>, what| -> Result<Vec<usize>, IntakeRefusal> {
        let Some(Json::Array(items)) = value else { return Err(malformed(what)) };
        items.into_iter().map(|v| if let Json::Integer(n) = v { usize::try_from(n).map_err(|_| malformed(what)) } else { Err(malformed(what)) }).collect()
    };
    let shape = integers(fields.remove("shape"), "no shape of integers")?;
    let offsets = integers(fields.remove("data_offsets"), "no data offsets of integers")?;
    let [start, end] = offsets[..] else { return Err(malformed("data offsets are not a pair")) };
    let held = shape.iter().try_fold(1usize, |n, &d| n.checked_mul(d)).and_then(|n| n.checked_mul((format.width() / 8) as usize));
    if start > end || held != Some(end - start) {
        return Err(IntakeRefusal::Extent { name });
    }
    Ok(TensorEntry { name, format, shape, range: start..end })
}

/// The header values the format uses.
enum Json {
    Object(BTreeMap<String, Json>),
    Array(Vec<Json>),
    String(String),
    Integer(u64),
}

/// The header's reader: a cursor over its bytes.
struct Header<'a> {
    text: &'a [u8],
    at: usize,
}

impl Header<'_> {
    fn refuse<T>(&self) -> Result<T, IntakeRefusal> {
        Err(IntakeRefusal::MalformedHeader { at: self.at })
    }

    /// The one value the header is, with only padding (the format pads with spaces) after it.
    fn document(mut self) -> Result<Json, IntakeRefusal> {
        let value = self.value()?;
        self.space();
        if self.at != self.text.len() {
            return self.refuse();
        }
        Ok(value)
    }

    fn space(&mut self) {
        while matches!(self.text.get(self.at), Some(b' ' | b'\t' | b'\n' | b'\r')) {
            self.at += 1;
        }
    }

    fn take(&mut self, byte: u8) -> Result<(), IntakeRefusal> {
        self.space();
        if self.text.get(self.at) != Some(&byte) {
            return self.refuse();
        }
        self.at += 1;
        Ok(())
    }

    fn value(&mut self) -> Result<Json, IntakeRefusal> {
        self.space();
        match self.text.get(self.at) {
            Some(b'{') => {
                self.at += 1;
                let mut fields = BTreeMap::new();
                self.space();
                if self.text.get(self.at) == Some(&b'}') {
                    self.at += 1;
                    return Ok(Json::Object(fields));
                }
                loop {
                    self.space();
                    let key = self.string()?;
                    self.take(b':')?;
                    let value = self.value()?;
                    if fields.insert(key.clone(), value).is_some() {
                        return Err(IntakeRefusal::Duplicate { name: key });
                    }
                    self.space();
                    match self.text.get(self.at) {
                        Some(b',') => self.at += 1,
                        Some(b'}') => {
                            self.at += 1;
                            return Ok(Json::Object(fields));
                        }
                        _ => return self.refuse(),
                    }
                }
            }
            Some(b'[') => {
                self.at += 1;
                let mut items = Vec::new();
                self.space();
                if self.text.get(self.at) == Some(&b']') {
                    self.at += 1;
                    return Ok(Json::Array(items));
                }
                loop {
                    items.push(self.value()?);
                    self.space();
                    match self.text.get(self.at) {
                        Some(b',') => self.at += 1,
                        Some(b']') => {
                            self.at += 1;
                            return Ok(Json::Array(items));
                        }
                        _ => return self.refuse(),
                    }
                }
            }
            Some(b'"') => Ok(Json::String(self.string()?)),
            Some(b'0'..=b'9') => {
                let from = self.at;
                while matches!(self.text.get(self.at), Some(b'0'..=b'9')) {
                    self.at += 1;
                }
                let digits = &self.text[from..self.at];
                if (digits.len() > 1 && digits[0] == b'0') || matches!(self.text.get(self.at), Some(b'.' | b'e' | b'E')) {
                    return self.refuse();
                }
                digits.iter().try_fold(0u64, |n, &d| n.checked_mul(10)?.checked_add(u64::from(d - b'0'))).map(Json::Integer).ok_or(IntakeRefusal::MalformedHeader { at: from })
            }
            _ => self.refuse(),
        }
    }

    fn string(&mut self) -> Result<String, IntakeRefusal> {
        if self.text.get(self.at) != Some(&b'"') {
            return self.refuse();
        }
        self.at += 1;
        let mut out = Vec::new();
        loop {
            let Some(&b) = self.text.get(self.at) else { return self.refuse() };
            self.at += 1;
            match b {
                b'"' => return String::from_utf8(out).or_else(|_| self.refuse()),
                b'\\' => {
                    let Some(&escape) = self.text.get(self.at) else { return self.refuse() };
                    self.at += 1;
                    let unit = match escape {
                        b'"' | b'\\' | b'/' => escape,
                        b'b' => 8,
                        b'f' => 12,
                        b'n' => b'\n',
                        b'r' => b'\r',
                        b't' => b'\t',
                        b'u' => {
                            let high = self.hex()?;
                            let code = if (0xD800..0xDC00).contains(&high) {
                                self.take(b'\\')?;
                                if self.text.get(self.at) != Some(&b'u') {
                                    return self.refuse();
                                }
                                self.at += 1;
                                let low = self.hex()?;
                                if !(0xDC00..0xE000).contains(&low) {
                                    return self.refuse();
                                }
                                0x10000 + ((high - 0xD800) << 10) + (low - 0xDC00)
                            } else {
                                high
                            };
                            let Some(c) = char::from_u32(code) else { return self.refuse() };
                            out.extend_from_slice(c.encode_utf8(&mut [0; 4]).as_bytes());
                            continue;
                        }
                        _ => return self.refuse(),
                    };
                    out.push(unit);
                }
                0..=0x1f => return self.refuse(),
                _ => out.push(b),
            }
        }
    }

    fn hex(&mut self) -> Result<u32, IntakeRefusal> {
        let digits = self.text.get(self.at..self.at + 4).ok_or(IntakeRefusal::MalformedHeader { at: self.at })?;
        let code = std::str::from_utf8(digits).ok().and_then(|d| u32::from_str_radix(d, 16).ok()).ok_or(IntakeRefusal::MalformedHeader { at: self.at })?;
        self.at += 4;
        Ok(code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The Lean `Codeword.value`, computed independently over big ratios from the three fields.
    fn lean_value(format: FloatFormat, word: u32) -> Rat {
        let (p, e) = (format.significand_bits, format.exponent_bits);
        let fraction = BigInt::from(word & ((1 << p) - 1));
        let raw = (word >> p) & ((1 << e) - 1);
        let significand = if raw == 0 { fraction } else { (BigInt::one() << p) + fraction };
        let ulp = i64::from(if raw == 0 { 1 } else { raw }) - i64::from(format.bias()) - i64::from(p);
        let sign = if word >> (p + e) & 1 == 1 { -Rat::one() } else { Rat::one() };
        let power = Rat::from_integer(BigInt::one() << ulp.unsigned_abs());
        sign * Rat::from_integer(significand) * if ulp >= 0 { power } else { power.recip() }
    }

    /// The exact encoder of a value onto a format's grid, where the value is on it: the inverse
    /// the refinement statements read.
    fn encode(format: FloatFormat, d: Dyadic) -> Option<u32> {
        let (p, e) = (format.significand_bits, format.exponent_bits);
        let sign = u32::from(d.numerator < 0) << (p + e);
        if d.numerator == 0 {
            return Some(0);
        }
        let magnitude = d.numerator.unsigned_abs();
        // The leading one's place, as an exponent of the value.
        let top = 63 - magnitude.leading_zeros() as i32 + d.exponent;
        let min_normal = 1 - format.bias();
        let (raw, ulp) = if top >= min_normal { (top + format.bias(), top - p as i32) } else { (0, min_normal - p as i32) };
        if raw >= (1 << e) - 1 || d.exponent < ulp {
            return None;
        }
        let significand = magnitude << (d.exponent - ulp) as u32;
        let fraction = if raw == 0 { significand } else { significand - (1 << p) };
        (fraction < 1 << p).then(|| sign | (raw as u32) << p | fraction as u32)
    }

    /// Every `bfloat16` and `binary16` word decodes to Lean's value or is refused exactly when its
    /// exponent field is all ones; each decoded value is in lowest terms and is carried exactly by
    /// `binary32` (`binary32_strictly_refines_binary16`, and `bfloat16` as `binary32`'s upper half).
    #[test]
    fn every_half_width_word_decodes_to_its_own_value() {
        for format in [FloatFormat::BFLOAT16, FloatFormat::BINARY16] {
            let mut refused = 0;
            for word in 0..1u32 << 16 {
                match format.decode(word) {
                    Ok(d) => {
                        assert_eq!(d.value(), lean_value(format, word), "{format:?} {word:#x}");
                        assert!(d.numerator % 2 != 0 || d == Dyadic { numerator: 0, exponent: 0 });
                        let wide = encode(FloatFormat::BINARY32, d).expect("binary32 carries every narrower value");
                        assert_eq!(FloatFormat::BINARY32.decode(wide), Ok(d));
                        let back = if d.numerator == 0 { 0 } else { word };
                        assert_eq!(encode(format, d), Some(back), "the round trip, up to the sign of zero");
                        if format == FloatFormat::BFLOAT16 {
                            assert_eq!(FloatFormat::BINARY32.decode(word << 16), Ok(d), "bfloat16 is binary32's upper half");
                        }
                    }
                    Err(IntakeRefusal::NonFinite { .. }) => refused += 1,
                    Err(other) => panic!("{other:?}"),
                }
            }
            assert_eq!(refused, 2 << format.significand_bits, "{format:?}: the all-ones exponent field, both signs");
        }
        // binary16 holds 1 + 2^(−10), which bfloat16 does not, and bfloat16 holds 2^100, which
        // binary16 does not: neither half-width format refines the other.
        assert!(encode(FloatFormat::BFLOAT16, Dyadic::reduced(1025, -10)).is_none());
        assert!(encode(FloatFormat::BINARY16, Dyadic::reduced(1, 100)).is_none());
    }

    /// The boundary words of `binary32`: zeros, the smallest and largest subnormal, the smallest
    /// normal, one, the largest finite, and the refused infinity and NaN; and a word wider than its
    /// format is refused, never masked.
    #[test]
    fn the_boundary_words_decode_exactly() {
        let f = FloatFormat::BINARY32;
        let at = |w: u32| f.decode(w).map(|d| (d.numerator, d.exponent));
        assert_eq!(at(0x0000_0000), Ok((0, 0)));
        assert_eq!(at(0x8000_0000), Ok((0, 0)));
        assert_eq!(at(0x0000_0001), Ok((1, -149)));
        assert_eq!(at(0x007f_ffff), Ok(((1 << 23) - 1, -149)));
        assert_eq!(at(0x0080_0000), Ok((1, -126)));
        assert_eq!(at(0x3f80_0000), Ok((1, 0)));
        assert_eq!(at(0xc000_0000), Ok((-1, 1)));
        assert_eq!(at(0x7f7f_ffff), Ok(((1 << 24) - 1, 104)));
        assert!(matches!(f.decode(0x7f80_0000), Err(IntakeRefusal::NonFinite { .. })));
        assert!(matches!(f.decode(0xffc0_0001), Err(IntakeRefusal::NonFinite { .. })));
        assert!(matches!(FloatFormat::BFLOAT16.decode(0x1_3f80), Err(IntakeRefusal::WiderThanFormat { .. })));
    }

    /// A file of the format's own shape: the header's length, its JSON padded with spaces, and the
    /// tensors' bytes little-endian.
    fn file(header: &str, data: &[u8]) -> Vec<u8> {
        let mut header = header.as_bytes().to_vec();
        header.resize(header.len().next_multiple_of(8), b' ');
        let mut out = (header.len() as u64).to_le_bytes().to_vec();
        out.extend(header);
        out.extend(data);
        out
    }

    /// A two-tensor file reads, its metadata passes untouched, and each tensor decodes to its
    /// words' values in stored order; each malformed file is refused by name.
    #[test]
    fn a_file_reads_its_tensors_and_refuses_what_it_does_not_hold() {
        // bf16 [1, −2, 0.5, 3] as a 2×2 matrix, then f32 [0.25].
        let data: Vec<u8> = [0x3f80u16, 0xc000, 0x3f00, 0x4040].iter().flat_map(|w| w.to_le_bytes()).chain(0x3e80_0000u32.to_le_bytes()).collect();
        let header = r#"{"__metadata__":{"format":"pt"},"w.bias":{"dtype":"F32","shape":[1],"data_offsets":[8,12]},"w":{"dtype":"BF16","shape":[2,2],"data_offsets":[0,8]}}"#;
        let bytes = file(header, &data);
        let read = Safetensors::read(&bytes).expect("read");
        assert_eq!(read.entries.iter().map(|t| (t.name.as_str(), t.count())).collect::<Vec<_>>(), [("w", 4), ("w.bias", 1)]);
        let values: Vec<Rat> = read.decoded(&read.entries[0]).expect("w").into_iter().map(Dyadic::value).collect();
        let r = |n: i64, d: i64| Rat::new(n.into(), d.into());
        assert_eq!(values, [r(1, 1), r(-2, 1), r(1, 2), r(3, 1)]);
        assert_eq!(read.decoded(&read.entries[1]).expect("bias"), [Dyadic { numerator: 1, exponent: -2 }]);

        let refused = |header: &str, data: &[u8]| Safetensors::read(&file(header, data)).err();
        assert_eq!(refused(r#"{"w":{"dtype":"BF16","shape":[2,2],"data_offsets":[0,8]}}"#, &data), Some(IntakeRefusal::Tiling), "four bytes held by no tensor");
        assert_eq!(refused(r#"{"w":{"dtype":"BF16","shape":[3],"data_offsets":[0,8]}}"#, &data[..8]), Some(IntakeRefusal::Extent { name: "w".into() }));
        assert_eq!(refused(r#"{"w":{"dtype":"I32","shape":[2],"data_offsets":[0,8]}}"#, &data[..8]), Some(IntakeRefusal::UnadmittedDtype { name: "w".into(), dtype: "I32".into() }));
        assert_eq!(
            refused(r#"{"a":{"dtype":"BF16","shape":[4],"data_offsets":[0,8]},"b":{"dtype":"BF16","shape":[2],"data_offsets":[4,8]}}"#, &data[..8]),
            Some(IntakeRefusal::Tiling),
            "overlapping ranges"
        );
        assert_eq!(refused(r#"{"w":{"dtype":"BF16","shape":[2],"data_offsets":[0,4]},"w":{"dtype":"BF16","shape":[2],"data_offsets":[4,8]}}"#, &data[..8]), Some(IntakeRefusal::Duplicate { name: "w".into() }));
        assert!(matches!(refused(r#"{"w":{"dtype":"BF16","shape":[2.0],"data_offsets":[0,4]}}"#, &data[..4]), Some(IntakeRefusal::MalformedHeader { .. })));
        assert_eq!(Safetensors::read(&bytes[..12]).err(), Some(IntakeRefusal::Truncated));
        // A tensor holding a NaN is read, and its decoding is refused at the word.
        let nan = file(r#"{"w":{"dtype":"BF16","shape":[1],"data_offsets":[0,2]}}"#, &0x7fc0u16.to_le_bytes());
        let read = Safetensors::read(&nan).expect("read");
        assert!(matches!(read.decoded(&read.entries[0]), Err(IntakeRefusal::NonFinite { .. })));
    }
}
