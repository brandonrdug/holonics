//! **The Mersenne ring `ℤ/(2^61 − 1)`: exact accumulation without division.**
//!
//! [definition] A 128-bit product folds back by shift-and-mask, because `2^61 ≡ 1`. Addition in
//! the ring is associative and commutative, which is the property an accumulating scatter needs
//! and floating-point addition lacks; Lean `Foundation/SectionLayout` states its laws over any
//! `CommSemiring`, and `ZMod (2^61 − 1)` is one. The device realization compiles the same
//! [`add`], [`mul`] and [`reduce`], so host/device agreement is a property of one piece of code.

/// The exact modulus: the Mersenne prime `2^61 - 1`.
pub(crate) const MODULUS: u64 = (1u64 << 61) - 1;

/// Fold **any** 128-bit word back into `[0, MODULUS)`.
///
/// `2^61 ≡ 1 (mod 2^61 - 1)`, so `x ≡ (x & (2^61 - 1)) + (x >> 61)` for every `x`, and the fold may
/// be iterated.  Both folds are performed **in `u128`**, which is what makes the total domain a
/// theorem rather than a precondition:
///
/// * `product < 2^128`, so `product >> 61 < 2^67` — the shifted half does **not** fit `u64` in
///   general, and narrowing it before the fold is exactly the truncation this reduction must not
///   commit.  `product & MODULUS < 2^61`, so
///   `once = (product & MODULUS) + (product >> 61) < 2^61 + 2^67 < 2^68`.
/// * `once < 2^68`, so `once >> 61 < 2^7` and `once & MODULUS < 2^61`, so
///   `twice = (once & MODULUS) + (once >> 61) < 2^61 + 2^7`.  That is below `2^64`, so the narrowing
///   to `u64` here is exact, and it is below `2 · MODULUS`, so one conditional subtraction lands in
///   `[0, MODULUS)`.
///
/// No division, no wrapping, and no operand precondition: the widest intermediate is `2^68`, held
/// in the 128-bit word the product already occupies.
#[inline(always)]
pub(crate) const fn reduce(product: u128) -> u64 {
    let once = (product & (MODULUS as u128)) + (product >> 61);
    let twice = ((once & (MODULUS as u128)) + (once >> 61)) as u64;
    if twice >= MODULUS {
        twice - MODULUS
    } else {
        twice
    }
}

/// The canonical residue of an arbitrary 64-bit word.
#[inline(always)]
pub(crate) const fn canonical(value: u64) -> u64 {
    reduce(value as u128)
}

/// Exact addition in `Z/(2^61 - 1)`, **total over every pair of `u64` words**.  Associative and
/// commutative, which is what makes the accumulating scatter order-independent.
///
/// The sum is formed in `u128` — `a + b < 2^65` — so no `u64` overflow is reachable and no
/// canonicality precondition is carried.  `reduce` then lands it in `[0, MODULUS)`.
#[inline(always)]
pub(crate) const fn add(a: u64, b: u64) -> u64 {
    reduce((a as u128) + (b as u128))
}

/// Exact multiplication in `Z/(2^61 - 1)`, **total over every pair of `u64` words**: the product of
/// two arbitrary 64-bit words is below `2^128`, which is [`reduce`]'s proved domain.
#[inline(always)]
pub(crate) const fn mul(a: u64, b: u64) -> u64 {
    reduce((a as u128) * (b as u128))
}

/// Whether a word is already the canonical residue of its own class, i.e. lies in `[0, MODULUS)`.
///
/// The arithmetic above no longer needs this — it is total — but the staging boundary does: a
/// declared coefficient outside `[0, MODULUS)` is a malformed declaration, and the host refuses it
/// there rather than reducing it silently.
#[inline(always)]
pub(crate) const fn is_canonical(value: u64) -> bool {
    value < MODULUS
}

#[cfg(test)]
mod tests;
