//! Record: research/records/2026-08-12_THE_RECURRENT_LAW_CROSSES_THE_CORPUS_DEPARTURE_THE_UNSEEN_SECTION_RIDES_ITS_DEPOSIT.md
//! Exact bi-affine transformation-law founding and evaluation at the CUDA membrane.
//!
//! A founding row is one complete rectangular intervention face
//! `(x0, x1, y0, y1, f00, f10, f01, f11)`. The card returns its Newton-form law
//! `(x0, y0, dx, dy, c0, cx, cy, cxy)`, where
//!
//! `f(x0 + u dx, y0 + v dy) = c0 + u cx + v cy + uv cxy`.
//!
//! Every signed integer is carried as two little-endian `u32` words. Overflow, a zero lattice
//! step, or a query outside the founded lattice is a typed refusal; no float or rounding exists.

pub const FOUND_ENTRY_SYMBOL: &str = "recurrent_law_found";
pub const EVALUATE_ENTRY_SYMBOL: &str = "recurrent_law_evaluate";
pub const FOLD_ENTRY_SYMBOL: &str = "recurrent_law_fold";
pub const LAYOUT_VERSION: u32 = 1;

pub const STATUS_UNWRITTEN: u32 = 0;
pub const STATUS_COMPLETE: u32 = 1;
pub const STATUS_INVALID: u32 = 2;
pub const STATUS_OVERFLOW: u32 = 3;
pub const STATUS_OUTSIDE_LATTICE: u32 = 4;

pub const I64_WORDS: usize = 2;
pub const FOUND_VALUES: usize = 8;
pub const FOUND_INPUT_WORDS: usize = FOUND_VALUES * I64_WORDS;
pub const LAW_VALUES: usize = 8;
pub const LAW_WORDS: usize = LAW_VALUES * I64_WORDS;
pub const FOUND_OUTPUT_STATUS: usize = 0;
pub const FOUND_OUTPUT_VERSION: usize = 1;
pub const FOUND_OUTPUT_LAW_AT: usize = 2;
pub const FOUND_OUTPUT_WORDS: usize = FOUND_OUTPUT_LAW_AT + LAW_WORDS;

pub const EVALUATE_COORDINATES: usize = 2;
pub const EVALUATE_INPUT_WORDS: usize = LAW_WORDS + EVALUATE_COORDINATES * I64_WORDS;
pub const EVALUATE_OUTPUT_STATUS: usize = 0;
pub const EVALUATE_OUTPUT_VERSION: usize = 1;
pub const EVALUATE_OUTPUT_VALUE_AT: usize = 2;
pub const EVALUATE_OUTPUT_WORDS: usize = EVALUATE_OUTPUT_VALUE_AT + I64_WORDS;

/// One fold row carries a law, an initial standing, an offset/extent into the current sheet, and
/// an offset into the returned world-line sheet.
pub const FOLD_INPUT_LAW_AT: usize = 0;
pub const FOLD_INPUT_INITIAL_AT: usize = FOLD_INPUT_LAW_AT + LAW_WORDS;
pub const FOLD_INPUT_CURRENT_OFFSET: usize = FOLD_INPUT_INITIAL_AT + I64_WORDS;
pub const FOLD_INPUT_CURRENT_EXTENT: usize = FOLD_INPUT_CURRENT_OFFSET + 1;
pub const FOLD_INPUT_TRACE_OFFSET: usize = FOLD_INPUT_CURRENT_EXTENT + 1;
pub const FOLD_INPUT_WORDS: usize = FOLD_INPUT_TRACE_OFFSET + 1;

pub const FOLD_OUTPUT_STATUS: usize = 0;
pub const FOLD_OUTPUT_VERSION: usize = 1;
pub const FOLD_OUTPUT_TRACE_OFFSET: usize = 2;
pub const FOLD_OUTPUT_TRACE_EXTENT: usize = 3;
pub const FOLD_OUTPUT_VALUE_AT: usize = 4;
pub const FOLD_OUTPUT_WORDS: usize = FOLD_OUTPUT_VALUE_AT + I64_WORDS;

#[inline]
pub const fn encode_i64(value: i64) -> [u32; I64_WORDS] {
    [value as u32, ((value as u64) >> 32) as u32]
}

#[inline]
pub const fn decode_i64(words: &[u32], at: usize) -> Option<i64> {
    if at > words.len() || I64_WORDS > words.len() - at {
        return None;
    }
    Some((words[at] as u64 | ((words[at + 1] as u64) << 32)) as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn signed_wire_round_trips_exact_extrema() {
        for value in [i64::MIN, -1, 0, 1, i64::MAX] {
            let words = encode_i64(value);
            assert_eq!(decode_i64(&words, 0), Some(value));
        }
    }
}
