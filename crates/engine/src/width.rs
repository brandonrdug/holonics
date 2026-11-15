//! **Precision: the declared grains every term is released to.**
//!
//! faces, charts and currents on `2^(−16)`; material on `2^(−24)`; frames and skins on `2^(−30)`; covectors on `2^(−24)`, the
//! contact's on `2^(−40)`; a product's remainder below its grain released to the nearest numerator
//!
//! Kind: the grains every phase releases to; no index of its own. Kernels: every kernel's `release` and `fit` (`kernels/field.cu`).
//! Lean: none (the precision law is stated in CLAUDE.md).
//! Records: `2026-11-01_THE_PROBLEM_IS_ONE_FIELD…`. The derivations' history is in the records; the items below keep their reasons.

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use rayon::prelude::*;

/// [agent-inferred, November 1] **A term's share of its row's mass** on `2^(−63)` (§14.11): formed
/// once, by one division of the exact series, for the return; the declared crossing into the step,
/// whose own release is to the material's grain.
pub const SHARE_BITS: u32 = 63;

/// A key's return past its 128-bit carrier, refused on the host and the card alike.
pub(crate) const KEY_RETURN: &str = "a contact's key return past its 128-bit carrier";

/// The contact covector's grain, `2^(−40)` (`δz` and `δs`).
pub(crate) const CONTACT_BITS: u32 = 40;

/// A face carried as a site's state, each class's share on `2^(−16)` ([`shares`]); its opening
/// `Σ_a w_a E(a)` releases the shares' grain to the encoding's own.
pub const STATE_BITS: u32 = 16;

// The items this object owns that stood in the October tower until C5 (#603), each as it stood.

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
    crate::census::reach_here(&x);
    i64::try_from(x).map_err(|_| TowerError::Refused("a released value outgrew its 64-bit carrier"))
}

/// `max |w|` over a family.
pub fn reach(w: &[i32]) -> u64 {
    w.iter().map(|v| v.unsigned_abs() as u64).max().unwrap_or(0)
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
