//! The landmark context's wide product (`compression/landmark/context.rs` until C3): moved whole into the engine (C3 of the consolidation, #603), each item's
//! text as it stood but for its visibility; C5 cuts them by object (THE_CONSOLIDATION §5).

/// `(hi, lo)` with `a b = hi 2^128 + lo`, every operation within `u128` (Lean
/// `Compression/Landmark/Context/BinaryLog.wideMul_eq`).
pub fn wide_mul(a: u128, b: u128) -> (u128, u128) {
    let mask = u128::from(u64::MAX);
    let (a1, a0, b1, b0) = (a >> 64, a & mask, b >> 64, b & mask);
    let (p00, p01, p10, p11) = (a0 * b0, a0 * b1, a1 * b0, a1 * b1);
    let middle = (p00 >> 64) + (p01 & mask) + (p10 & mask);
    (
        p11 + (p01 >> 64) + (p10 >> 64) + (middle >> 64),
        (p00 & mask) | (middle << 64),
    )
}
