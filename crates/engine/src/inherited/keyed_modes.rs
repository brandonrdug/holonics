//! The keyed modes' exponential and logarithm faces (`hnn/keyed_modes.rs` until C3): moved whole into the engine (C3 of the consolidation, #603), each item's
//! text as it stood but for its visibility; C5 cuts them by object (THE_CONSOLIDATION §5).


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

pub const UNIT_BITS: u32 = 62;

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
