//! Exact receiver shadow of one raw material passage at the CUDA membrane.
//!
//! The shadow is invariant under a bijection of the passage's octet surfaces. At each situated
//! octet the card returns the distance to the immediately prior occurrence of the same surface,
//! or zero when the surface has not occurred. The ordered distance field is a causal equality
//! geometry: it preserves recurrence and chronology without carrying the source octets. The
//! fixed-width words below are a profile summary only; exact attachment uses the complete returned
//! field and never this hash.

pub const ENTRY_SYMBOL: &str = "material_shadow_read";
pub const LAYOUT_VERSION: u32 = 1;

pub const STATUS_UNWRITTEN: u32 = 0;
pub const STATUS_COMPLETE: u32 = 1;
pub const STATUS_INVALID: u32 = 2;

/// `(material_offset, material_extent, shadow_offset)`.
pub const INPUT_OFFSET: usize = 0;
pub const INPUT_EXTENT: usize = 1;
pub const INPUT_SHADOW_OFFSET: usize = 2;
pub const INPUT_WORDS: usize = 3;

pub const OUTPUT_STATUS: usize = 0;
pub const OUTPUT_VERSION: usize = 1;
pub const OUTPUT_SUMMARY_AT: usize = 2;

/// `(extent, distinct, recurrent, adjacent_equal, forward_hash_lo, forward_hash_hi,
/// reverse_hash_lo, reverse_hash_hi)`.
pub const SUMMARY_WORDS: usize = 8;
pub const OUTPUT_WORDS: usize = OUTPUT_SUMMARY_AT + SUMMARY_WORDS;

pub const FNV_OFFSET: u64 = 0xcbf29ce484222325;
pub const FNV_PRIME: u64 = 0x100000001b3;

#[inline]
pub const fn hash_step(state: u64, word: u32) -> u64 {
    (state ^ word as u64).wrapping_mul(FNV_PRIME)
}
