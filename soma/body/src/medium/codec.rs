//! Fixed boundary codecs for `RegionalForm`.
//!
//! SLEEP V2/V3 records retain the original seventeen-word form independently of the live
//! `FORM_WORDS` mouth. This codec is deliberately literal: a later active-layout change cannot
//! silently change the historical archive width or reinterpret its fields. The eleven-word codec
//! is the active shared mouth and the fixed SLEEP V4 boundary representation.

use super::RegionalForm;
use crate::num::{Cog, Rung};
use crate::seam::{row_fits, SliceWordSeam, WordSeam};

/// The complete historical V2/V3 `RegionalForm` row: two five-word Cogs, two three-word Rungs,
/// and one occupied word. This is a wire constant, never derived from the active `FORM_WORDS`.
pub const LEGACY_FORM_WORDS: usize = 17;

const SAME_MAG: usize = 0;
const SAME_RANK_MAG: usize = 1;
const SAME_RANK_RANK: usize = 2;
const SAME_RANK_NEG: usize = 3;
const SAME_TURN: usize = 4;
const OTHER_MAG: usize = 5;
const OTHER_RANK_MAG: usize = 6;
const OTHER_RANK_RANK: usize = 7;
const OTHER_RANK_NEG: usize = 8;
const OTHER_TURN: usize = 9;
const THIS_WAY_MAG: usize = 10;
const THIS_WAY_RANK: usize = 11;
const THIS_WAY_NEG: usize = 12;
const THAT_WAY_MAG: usize = 13;
const THAT_WAY_RANK: usize = 14;
const THAT_WAY_NEG: usize = 15;
const OCCUPIED: usize = 16;

/// A historical row is semantic input, not a permissive integer bag. Every rejection happens
/// before a partial form or partially written output row can escape.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LegacyFormError {
    ShortRow { expected: usize, actual: usize },
    WrongWidth { expected: usize, actual: usize },
    NonCanonicalBoolean { word: usize, value: u32 },
    RankOutOfRange { word: usize, value: u32 },
    TurnOutOfRange { word: usize, value: u32 },
    UnoccupiedNonzeroData,
    MalformedRow,
}

#[inline]
fn exact_width(len: usize) -> Result<(), LegacyFormError> {
    if len < LEGACY_FORM_WORDS {
        Err(LegacyFormError::ShortRow {
            expected: LEGACY_FORM_WORDS,
            actual: len,
        })
    } else if len > LEGACY_FORM_WORDS {
        Err(LegacyFormError::WrongWidth {
            expected: LEGACY_FORM_WORDS,
            actual: len,
        })
    } else {
        Ok(())
    }
}

#[inline]
fn checked_bool(row: &[u32], word: usize) -> Result<bool, LegacyFormError> {
    match row[word] {
        0 => Ok(false),
        1 => Ok(true),
        value => Err(LegacyFormError::NonCanonicalBoolean { word, value }),
    }
}

#[inline]
fn checked_rank(row: &[u32], word: usize) -> Result<i32, LegacyFormError> {
    let value = row[word];
    if value > i32::MAX as u32 {
        Err(LegacyFormError::RankOutOfRange { word, value })
    } else {
        Ok(value as i32)
    }
}

#[inline]
fn checked_turn(row: &[u32], word: usize) -> Result<u32, LegacyFormError> {
    let value = row[word];
    if value > 3 {
        Err(LegacyFormError::TurnOutOfRange { word, value })
    } else {
        Ok(value)
    }
}

#[inline]
fn checked_rung(
    row: &[u32],
    mag_word: usize,
    rank_word: usize,
    neg_word: usize,
) -> Result<Rung, LegacyFormError> {
    let mag = row[mag_word];
    let rank = checked_rank(row, rank_word)?;
    let neg = checked_bool(row, neg_word)?;
    Ok(Rung { mag, rank, neg })
}

impl RegionalForm {
    #[inline]
    fn legacy_data_is_nonzero(self) -> bool {
        self.same.mag != 0
            || self.same.rank.mag != 0
            || self.same.rank.rank != 0
            || self.same.rank.neg
            || self.same.turn != 0
            || self.other.mag != 0
            || self.other.rank.mag != 0
            || self.other.rank.rank != 0
            || self.other.rank.neg
            || self.other.turn != 0
            || self.this_way.mag != 0
            || self.this_way.rank != 0
            || self.this_way.neg
            || self.that_way.mag != 0
            || self.that_way.rank != 0
            || self.that_way.neg
    }

    #[inline]
    fn validate_legacy(self) -> Result<(), LegacyFormError> {
        for (word, rank) in [
            (SAME_RANK_RANK, self.same.rank.rank),
            (OTHER_RANK_RANK, self.other.rank.rank),
            (THIS_WAY_RANK, self.this_way.rank),
            (THAT_WAY_RANK, self.that_way.rank),
        ] {
            if rank < 0 {
                return Err(LegacyFormError::RankOutOfRange {
                    word,
                    value: rank as u32,
                });
            }
        }
        for (word, turn) in [(SAME_TURN, self.same.turn), (OTHER_TURN, self.other.turn)] {
            if turn > 3 {
                return Err(LegacyFormError::TurnOutOfRange { word, value: turn });
            }
        }
        if !self.occupied && self.legacy_data_is_nonzero() {
            return Err(LegacyFormError::UnoccupiedNonzeroData);
        }
        Ok(())
    }

    /// Encode exactly one historical seventeen-word semantic row. The destination must be exactly
    /// one row; malformed typed state and wrong widths leave it untouched.
    pub fn pack_legacy_checked(&self, row: &mut [u32]) -> Result<(), LegacyFormError> {
        exact_width(row.len())?;
        self.validate_legacy()?;

        let packed = [
            self.same.mag,
            self.same.rank.mag,
            self.same.rank.rank as u32,
            self.same.rank.neg as u32,
            self.same.turn,
            self.other.mag,
            self.other.rank.mag,
            self.other.rank.rank as u32,
            self.other.rank.neg as u32,
            self.other.turn,
            self.this_way.mag,
            self.this_way.rank as u32,
            self.this_way.neg as u32,
            self.that_way.mag,
            self.that_way.rank as u32,
            self.that_way.neg as u32,
            self.occupied as u32,
        ];
        row.copy_from_slice(&packed);
        Ok(())
    }

    /// Decode exactly one historical V2/V3 form row. Boolean and occupancy words are canonical
    /// `0|1`; ranks and turns stay in the lawful domain; an unoccupied row is all-zero. Occupied-zero
    /// remains distinct from UNBORN.
    pub fn unpack_legacy_checked(row: &[u32]) -> Result<RegionalForm, LegacyFormError> {
        exact_width(row.len())?;

        let occupied = checked_bool(row, OCCUPIED)?;
        if !occupied && row[..OCCUPIED].iter().any(|word| *word != 0) {
            return Err(LegacyFormError::UnoccupiedNonzeroData);
        }
        let same = Cog {
            mag: row[SAME_MAG],
            rank: checked_rung(row, SAME_RANK_MAG, SAME_RANK_RANK, SAME_RANK_NEG)?,
            turn: checked_turn(row, SAME_TURN)?,
        };
        let other = Cog {
            mag: row[OTHER_MAG],
            rank: checked_rung(row, OTHER_RANK_MAG, OTHER_RANK_RANK, OTHER_RANK_NEG)?,
            turn: checked_turn(row, OTHER_TURN)?,
        };
        let form = RegionalForm {
            same,
            other,
            this_way: checked_rung(row, THIS_WAY_MAG, THIS_WAY_RANK, THIS_WAY_NEG)?,
            that_way: checked_rung(row, THAT_WAY_MAG, THAT_WAY_RANK, THAT_WAY_NEG)?,
            occupied,
        };
        form.validate_legacy()?;

        let mut canonical = [0u32; LEGACY_FORM_WORDS];
        form.pack_legacy_checked(&mut canonical)?;
        if canonical.as_slice() != row {
            return Err(LegacyFormError::MalformedRow);
        }
        Ok(form)
    }
}

/// The first direct `RegionalForm` layout. Generic Cog/Rung, carrier, and K encodings remain whole;
/// this exact eleven-word row is both the active shared mouth and SLEEP V4's fixed form layout.
pub const COMPACT_FORM_LAYOUT_VERSION: u32 = 1;
pub const COMPACT_FORM_WORDS: usize = 11;
const COMPACT_FORM_DATA_WORDS: usize = 10;

const COMPACT_FORM_SAME_MAG_WORD: usize = 0;
const COMPACT_FORM_SAME_RANK_MAG_WORD: usize = 1;
const COMPACT_FORM_SAME_RANK_RANK_WORD: usize = 2;
const COMPACT_FORM_OTHER_MAG_WORD: usize = 3;
const COMPACT_FORM_OTHER_RANK_MAG_WORD: usize = 4;
const COMPACT_FORM_OTHER_RANK_RANK_WORD: usize = 5;
const COMPACT_FORM_THIS_WAY_MAG_WORD: usize = 6;
const COMPACT_FORM_THIS_WAY_RANK_WORD: usize = 7;
const COMPACT_FORM_THAT_WAY_MAG_WORD: usize = 8;
const COMPACT_FORM_THAT_WAY_RANK_WORD: usize = 9;
const COMPACT_FORM_FLAGS_WORD: usize = 10;

const COMPACT_FORM_SAME_TURN_SHIFT: u32 = 0;
const COMPACT_FORM_SAME_RANK_NEG_BIT: u32 = 1 << 2;
const COMPACT_FORM_OTHER_TURN_SHIFT: u32 = 3;
const COMPACT_FORM_OTHER_RANK_NEG_BIT: u32 = 1 << 5;
const COMPACT_FORM_THIS_WAY_NEG_BIT: u32 = 1 << 6;
const COMPACT_FORM_THAT_WAY_NEG_BIT: u32 = 1 << 7;
const COMPACT_FORM_OCCUPIED_BIT: u32 = 1 << 8;
const COMPACT_FORM_KNOWN_FLAGS: u32 = (1 << 9) - 1;
const COMPACT_FORM_RESERVED_FLAGS: u32 = !COMPACT_FORM_KNOWN_FLAGS;

const COMPACT_FORM_TURN_MASK: u32 = 3;

/// A compact boundary row is reject-not-clip. The error names the first malformed face without
/// reconstructing a partial form or silently narrowing a boundary value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompactFormError {
    ShortRow,
    ReservedFlags { flags: u32 },
    RankOutOfRange { word: usize, value: u32 },
    TurnOutOfRange { other: bool, turn: u32 },
    UnoccupiedNonzeroData,
}

impl RegionalForm {
    #[inline]
    fn compact_data_is_nonzero(self) -> bool {
        self.same.mag != 0
            || self.same.rank.mag != 0
            || self.same.rank.rank != 0
            || self.same.rank.neg
            || self.same.turn != 0
            || self.other.mag != 0
            || self.other.rank.mag != 0
            || self.other.rank.rank != 0
            || self.other.rank.neg
            || self.other.turn != 0
            || self.this_way.mag != 0
            || self.this_way.rank != 0
            || self.this_way.neg
            || self.that_way.mag != 0
            || self.that_way.rank != 0
            || self.that_way.neg
    }

    #[inline]
    fn validate_compact(self) -> Result<(), CompactFormError> {
        for (word, rank) in [
            (COMPACT_FORM_SAME_RANK_RANK_WORD, self.same.rank.rank),
            (COMPACT_FORM_OTHER_RANK_RANK_WORD, self.other.rank.rank),
            (COMPACT_FORM_THIS_WAY_RANK_WORD, self.this_way.rank),
            (COMPACT_FORM_THAT_WAY_RANK_WORD, self.that_way.rank),
        ] {
            if rank < 0 {
                return Err(CompactFormError::RankOutOfRange {
                    word,
                    value: rank as u32,
                });
            }
        }
        if self.same.turn > COMPACT_FORM_TURN_MASK {
            return Err(CompactFormError::TurnOutOfRange {
                other: false,
                turn: self.same.turn,
            });
        }
        if self.other.turn > COMPACT_FORM_TURN_MASK {
            return Err(CompactFormError::TurnOutOfRange {
                other: true,
                turn: self.other.turn,
            });
        }
        if !self.occupied && self.compact_data_is_nonzero() {
            return Err(CompactFormError::UnoccupiedNonzeroData);
        }
        Ok(())
    }

    #[inline]
    fn compact_flags(self) -> u32 {
        (self.same.turn << COMPACT_FORM_SAME_TURN_SHIFT)
            | (self.same.rank.neg as u32 * COMPACT_FORM_SAME_RANK_NEG_BIT)
            | (self.other.turn << COMPACT_FORM_OTHER_TURN_SHIFT)
            | (self.other.rank.neg as u32 * COMPACT_FORM_OTHER_RANK_NEG_BIT)
            | (self.this_way.neg as u32 * COMPACT_FORM_THIS_WAY_NEG_BIT)
            | (self.that_way.neg as u32 * COMPACT_FORM_THAT_WAY_NEG_BIT)
            | (self.occupied as u32 * COMPACT_FORM_OCCUPIED_BIT)
    }

    /// One active seam word. Device finishes call this scalar mouth directly, so it performs no
    /// fallible boundary work and never materializes an intermediate row.
    #[inline(always)]
    pub fn packed_word(&self, word: usize) -> u32 {
        match word {
            COMPACT_FORM_SAME_MAG_WORD => self.same.mag,
            COMPACT_FORM_SAME_RANK_MAG_WORD => self.same.rank.mag,
            COMPACT_FORM_SAME_RANK_RANK_WORD => self.same.rank.rank as u32,
            COMPACT_FORM_OTHER_MAG_WORD => self.other.mag,
            COMPACT_FORM_OTHER_RANK_MAG_WORD => self.other.rank.mag,
            COMPACT_FORM_OTHER_RANK_RANK_WORD => self.other.rank.rank as u32,
            COMPACT_FORM_THIS_WAY_MAG_WORD => self.this_way.mag,
            COMPACT_FORM_THIS_WAY_RANK_WORD => self.this_way.rank as u32,
            COMPACT_FORM_THAT_WAY_MAG_WORD => self.that_way.mag,
            COMPACT_FORM_THAT_WAY_RANK_WORD => self.that_way.rank as u32,
            COMPACT_FORM_FLAGS_WORD => self.compact_flags(),
            _ => 0,
        }
    }

    /// Pack the active canonical row. Engine-owned malformed state is an assertion failure;
    /// untrusted archive/device-return material enters through `unpack_compact_checked`.
    pub fn pack(&self, out: &mut [u32], at: usize) {
        if self.validate_compact().is_err() {
            panic!("malformed RegionalForm cannot enter the compact trusted seam");
        }
        assert!(
            row_fits(out, at, COMPACT_FORM_WORDS),
            "the compact RegionalForm output row is short"
        );
        let mut word = 0usize;
        while word < COMPACT_FORM_WORDS {
            out[at + word] = self.packed_word(word);
            word += 1;
        }
    }

    /// Read one trusted active row without a fallible boundary path.
    ///
    /// # Safety
    ///
    /// `at..at + COMPACT_FORM_WORDS` must be a live canonical row in `words`.
    #[inline(always)]
    pub unsafe fn unpack_unchecked_with<S: WordSeam>(words: &[u32], at: usize) -> RegionalForm {
        let flags = unsafe { S::read_u32_unchecked(words, at + COMPACT_FORM_FLAGS_WORD) };
        RegionalForm {
            same: Cog {
                mag: unsafe { S::read_u32_unchecked(words, at + COMPACT_FORM_SAME_MAG_WORD) },
                rank: Rung {
                    mag: unsafe {
                        S::read_u32_unchecked(words, at + COMPACT_FORM_SAME_RANK_MAG_WORD)
                    },
                    rank: unsafe {
                        S::read_u32_unchecked(words, at + COMPACT_FORM_SAME_RANK_RANK_WORD)
                    } as i32,
                    neg: flags & COMPACT_FORM_SAME_RANK_NEG_BIT != 0,
                },
                turn: (flags >> COMPACT_FORM_SAME_TURN_SHIFT) & COMPACT_FORM_TURN_MASK,
            },
            other: Cog {
                mag: unsafe { S::read_u32_unchecked(words, at + COMPACT_FORM_OTHER_MAG_WORD) },
                rank: Rung {
                    mag: unsafe {
                        S::read_u32_unchecked(words, at + COMPACT_FORM_OTHER_RANK_MAG_WORD)
                    },
                    rank: unsafe {
                        S::read_u32_unchecked(words, at + COMPACT_FORM_OTHER_RANK_RANK_WORD)
                    } as i32,
                    neg: flags & COMPACT_FORM_OTHER_RANK_NEG_BIT != 0,
                },
                turn: (flags >> COMPACT_FORM_OTHER_TURN_SHIFT) & COMPACT_FORM_TURN_MASK,
            },
            this_way: Rung {
                mag: unsafe { S::read_u32_unchecked(words, at + COMPACT_FORM_THIS_WAY_MAG_WORD) },
                rank: unsafe { S::read_u32_unchecked(words, at + COMPACT_FORM_THIS_WAY_RANK_WORD) }
                    as i32,
                neg: flags & COMPACT_FORM_THIS_WAY_NEG_BIT != 0,
            },
            that_way: Rung {
                mag: unsafe { S::read_u32_unchecked(words, at + COMPACT_FORM_THAT_WAY_MAG_WORD) },
                rank: unsafe { S::read_u32_unchecked(words, at + COMPACT_FORM_THAT_WAY_RANK_WORD) }
                    as i32,
                neg: flags & COMPACT_FORM_THAT_WAY_NEG_BIT != 0,
            },
            occupied: flags & COMPACT_FORM_OCCUPIED_BIT != 0,
        }
    }

    /// Read one complete active form through `S`. A short row is wholly UNBORN; a complete malformed
    /// row is an assertion failure rather than a clipped construction. Device hot paths whose
    /// canonicality and extent were already proved call `unpack_unchecked_with` explicitly.
    #[inline]
    pub fn unpack_with<S: WordSeam>(words: &[u32], at: usize) -> RegionalForm {
        if row_fits(words, at, COMPACT_FORM_WORDS) {
            RegionalForm::unpack_compact_trusted_with::<S>(words, at)
        } else {
            RegionalForm::UNBORN
        }
    }

    #[inline]
    pub fn unpack(words: &[u32], at: usize) -> RegionalForm {
        RegionalForm::unpack_with::<SliceWordSeam>(words, at)
    }

    /// Checked compact boundary decode through a declared substrate seam. A short or malformed row
    /// returns an error before any partial `RegionalForm` can escape.
    #[inline]
    pub fn unpack_compact_checked_with<S: WordSeam>(
        words: &[u32],
        at: usize,
    ) -> Result<RegionalForm, CompactFormError> {
        if !row_fits(words, at, COMPACT_FORM_WORDS) {
            return Err(CompactFormError::ShortRow);
        }
        let mut row = [0u32; COMPACT_FORM_WORDS];
        let mut word = 0usize;
        while word < COMPACT_FORM_WORDS {
            row[word] = unsafe { S::read_u32_unchecked(words, at + word) };
            word += 1;
        }

        let flags = row[COMPACT_FORM_FLAGS_WORD];
        let reserved = flags & COMPACT_FORM_RESERVED_FLAGS;
        if reserved != 0 {
            return Err(CompactFormError::ReservedFlags { flags: reserved });
        }
        for rank_word in [
            COMPACT_FORM_SAME_RANK_RANK_WORD,
            COMPACT_FORM_OTHER_RANK_RANK_WORD,
            COMPACT_FORM_THIS_WAY_RANK_WORD,
            COMPACT_FORM_THAT_WAY_RANK_WORD,
        ] {
            if row[rank_word] > i32::MAX as u32 {
                return Err(CompactFormError::RankOutOfRange {
                    word: rank_word,
                    value: row[rank_word],
                });
            }
        }

        let same_turn = (flags >> COMPACT_FORM_SAME_TURN_SHIFT) & COMPACT_FORM_TURN_MASK;
        let other_turn = (flags >> COMPACT_FORM_OTHER_TURN_SHIFT) & COMPACT_FORM_TURN_MASK;

        let occupied = flags & COMPACT_FORM_OCCUPIED_BIT != 0;
        let non_occupancy_flags = flags & (COMPACT_FORM_KNOWN_FLAGS ^ COMPACT_FORM_OCCUPIED_BIT);
        let mut nonzero_data = non_occupancy_flags != 0;
        let mut data_word = 0usize;
        while data_word < COMPACT_FORM_DATA_WORDS {
            nonzero_data |= row[data_word] != 0;
            data_word += 1;
        }
        if !occupied && nonzero_data {
            return Err(CompactFormError::UnoccupiedNonzeroData);
        }

        let form = RegionalForm {
            same: Cog {
                mag: row[COMPACT_FORM_SAME_MAG_WORD],
                rank: Rung {
                    mag: row[COMPACT_FORM_SAME_RANK_MAG_WORD],
                    rank: row[COMPACT_FORM_SAME_RANK_RANK_WORD] as i32,
                    neg: flags & COMPACT_FORM_SAME_RANK_NEG_BIT != 0,
                },
                turn: same_turn,
            },
            other: Cog {
                mag: row[COMPACT_FORM_OTHER_MAG_WORD],
                rank: Rung {
                    mag: row[COMPACT_FORM_OTHER_RANK_MAG_WORD],
                    rank: row[COMPACT_FORM_OTHER_RANK_RANK_WORD] as i32,
                    neg: flags & COMPACT_FORM_OTHER_RANK_NEG_BIT != 0,
                },
                turn: other_turn,
            },
            this_way: Rung {
                mag: row[COMPACT_FORM_THIS_WAY_MAG_WORD],
                rank: row[COMPACT_FORM_THIS_WAY_RANK_WORD] as i32,
                neg: flags & COMPACT_FORM_THIS_WAY_NEG_BIT != 0,
            },
            that_way: Rung {
                mag: row[COMPACT_FORM_THAT_WAY_MAG_WORD],
                rank: row[COMPACT_FORM_THAT_WAY_RANK_WORD] as i32,
                neg: flags & COMPACT_FORM_THAT_WAY_NEG_BIT != 0,
            },
            occupied,
        };
        form.validate_compact()?;
        Ok(form)
    }

    /// Ordinary-slice checked boundary mouth for compact archive/device-return records.
    #[inline]
    pub fn unpack_compact_checked(
        words: &[u32],
        at: usize,
    ) -> Result<RegionalForm, CompactFormError> {
        RegionalForm::unpack_compact_checked_with::<SliceWordSeam>(words, at)
    }

    /// Trusted internal compact read. The same reject-not-clip invariants remain assertions here;
    /// no trusted caller can turn malformed input into UNBORN or a clipped number.
    #[inline]
    pub fn unpack_compact_trusted_with<S: WordSeam>(words: &[u32], at: usize) -> RegionalForm {
        match RegionalForm::unpack_compact_checked_with::<S>(words, at) {
            Ok(form) => form,
            Err(_) => panic!("malformed compact RegionalForm at a trusted seam"),
        }
    }

    /// Ordinary-slice trusted internal compact read.
    #[inline]
    pub fn unpack_compact_trusted(words: &[u32], at: usize) -> RegionalForm {
        RegionalForm::unpack_compact_trusted_with::<SliceWordSeam>(words, at)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::medium::FORM_WORDS;
    use crate::num::{COG_WORDS, RUNG_WORDS};
    use crate::seam::WordSeam;

    fn maximal_form() -> RegionalForm {
        RegionalForm {
            same: Cog {
                mag: u32::MAX,
                rank: Rung {
                    mag: u32::MAX,
                    rank: i32::MAX,
                    neg: true,
                },
                turn: 3,
            },
            other: Cog {
                mag: u32::MAX,
                rank: Rung {
                    mag: u32::MAX,
                    rank: i32::MAX,
                    neg: true,
                },
                turn: 3,
            },
            this_way: Rung {
                mag: u32::MAX,
                rank: i32::MAX,
                neg: true,
            },
            that_way: Rung {
                mag: u32::MAX,
                rank: i32::MAX,
                neg: true,
            },
            occupied: true,
        }
    }

    #[test]
    fn historical_form_width_and_layout_are_literal_and_exact() {
        assert_eq!(LEGACY_FORM_WORDS, 17);
        assert_eq!(
            FORM_WORDS, COMPACT_FORM_WORDS,
            "the historical form remains fixed while the active mouth is direct"
        );
        let form = maximal_form();
        let mut row = [0u32; LEGACY_FORM_WORDS];
        form.pack_legacy_checked(&mut row).unwrap();
        assert_eq!(
            row,
            [
                u32::MAX,
                u32::MAX,
                i32::MAX as u32,
                1,
                3,
                u32::MAX,
                u32::MAX,
                i32::MAX as u32,
                1,
                3,
                u32::MAX,
                i32::MAX as u32,
                1,
                u32::MAX,
                i32::MAX as u32,
                1,
                1,
            ]
        );
        assert_eq!(RegionalForm::unpack_legacy_checked(&row), Ok(form));
    }

    #[test]
    fn historical_unborn_and_occupied_zero_remain_distinct() {
        let unborn = [0u32; LEGACY_FORM_WORDS];
        assert_eq!(
            RegionalForm::unpack_legacy_checked(&unborn),
            Ok(RegionalForm::UNBORN)
        );

        let occupied_zero = RegionalForm::UNBORN.occupy();
        let mut row = [0u32; LEGACY_FORM_WORDS];
        occupied_zero.pack_legacy_checked(&mut row).unwrap();
        assert!(row[..OCCUPIED].iter().all(|word| *word == 0));
        assert_eq!(row[OCCUPIED], 1);
        assert_eq!(RegionalForm::unpack_legacy_checked(&row), Ok(occupied_zero));
    }

    #[test]
    fn historical_zero_magnitudes_preserve_their_carried_grain_and_direction() {
        let form = RegionalForm {
            same: Cog {
                mag: 0,
                rank: Rung {
                    mag: 0,
                    rank: 7,
                    neg: true,
                },
                turn: 3,
            },
            other: Cog::ZERO,
            this_way: Rung {
                mag: 0,
                rank: 9,
                neg: true,
            },
            that_way: Rung::ZERO,
            occupied: true,
        };
        let mut row = [0u32; LEGACY_FORM_WORDS];
        form.pack_legacy_checked(&mut row).unwrap();
        assert_eq!(RegionalForm::unpack_legacy_checked(&row), Ok(form));
    }

    #[test]
    fn historical_rows_reject_short_and_wrong_width_without_writing() {
        let form = maximal_form();
        for len in 0..LEGACY_FORM_WORDS {
            assert_eq!(
                RegionalForm::unpack_legacy_checked(&[0u32; LEGACY_FORM_WORDS][..len]),
                Err(LegacyFormError::ShortRow {
                    expected: LEGACY_FORM_WORDS,
                    actual: len,
                })
            );
        }
        let long = [0u32; LEGACY_FORM_WORDS + 1];
        assert_eq!(
            RegionalForm::unpack_legacy_checked(&long),
            Err(LegacyFormError::WrongWidth {
                expected: LEGACY_FORM_WORDS,
                actual: LEGACY_FORM_WORDS + 1,
            })
        );

        let mut short = [0x5a5a_5a5au32; LEGACY_FORM_WORDS - 1];
        let before = short;
        assert!(form.pack_legacy_checked(&mut short).is_err());
        assert_eq!(short, before);
        let mut long = [0x5a5a_5a5au32; LEGACY_FORM_WORDS + 1];
        let before = long;
        assert!(form.pack_legacy_checked(&mut long).is_err());
        assert_eq!(long, before);
    }

    #[test]
    fn historical_boolean_and_occupancy_words_are_canonical() {
        for word in [
            SAME_RANK_NEG,
            OTHER_RANK_NEG,
            THIS_WAY_NEG,
            THAT_WAY_NEG,
            OCCUPIED,
        ] {
            let mut row = [0u32; LEGACY_FORM_WORDS];
            if word != OCCUPIED {
                row[OCCUPIED] = 1;
            }
            row[word] = 2;
            assert_eq!(
                RegionalForm::unpack_legacy_checked(&row),
                Err(LegacyFormError::NonCanonicalBoolean { word, value: 2 })
            );
        }
    }

    #[test]
    fn historical_ranks_and_turns_reject_malformed_rows() {
        for word in [
            SAME_RANK_RANK,
            OTHER_RANK_RANK,
            THIS_WAY_RANK,
            THAT_WAY_RANK,
        ] {
            let mut row = [0u32; LEGACY_FORM_WORDS];
            row[word] = i32::MAX as u32 + 1;
            row[OCCUPIED] = 1;
            assert_eq!(
                RegionalForm::unpack_legacy_checked(&row),
                Err(LegacyFormError::RankOutOfRange {
                    word,
                    value: i32::MAX as u32 + 1,
                })
            );
        }
        for word in [SAME_TURN, OTHER_TURN] {
            let mut row = [0u32; LEGACY_FORM_WORDS];
            row[word] = 4;
            row[OCCUPIED] = 1;
            assert_eq!(
                RegionalForm::unpack_legacy_checked(&row),
                Err(LegacyFormError::TurnOutOfRange { word, value: 4 })
            );
        }
    }

    #[test]
    fn historical_checked_pack_rejects_malformed_typed_forms_before_writing() {
        let assert_rejected = |form: RegionalForm, expected: LegacyFormError| {
            let mut row = [0x5a5a_5a5au32; LEGACY_FORM_WORDS];
            let before = row;
            assert_eq!(form.pack_legacy_checked(&mut row), Err(expected));
            assert_eq!(
                row, before,
                "validation precedes every historical-row store"
            );
        };

        let mut negative_rank = maximal_form();
        negative_rank.same.rank.rank = -1;
        assert_rejected(
            negative_rank,
            LegacyFormError::RankOutOfRange {
                word: SAME_RANK_RANK,
                value: u32::MAX,
            },
        );

        let mut bad_turn = maximal_form();
        bad_turn.other.turn = 4;
        assert_rejected(
            bad_turn,
            LegacyFormError::TurnOutOfRange {
                word: OTHER_TURN,
                value: 4,
            },
        );

        let mut false_occupancy = maximal_form();
        false_occupancy.occupied = false;
        assert_rejected(false_occupancy, LegacyFormError::UnoccupiedNonzeroData);
    }

    #[test]
    fn historical_unoccupied_nonzero_data_never_becomes_a_form() {
        for word in 0..OCCUPIED {
            let mut row = [0u32; LEGACY_FORM_WORDS];
            row[word] = 1;
            assert_eq!(
                RegionalForm::unpack_legacy_checked(&row),
                Err(LegacyFormError::UnoccupiedNonzeroData),
                "legacy word {word} cannot hide behind false occupancy",
            );
        }
    }

    struct MirrorWordSeam;

    unsafe impl WordSeam for MirrorWordSeam {
        unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32 {
            *words.get_unchecked(at)
        }

        unsafe fn store_u32_unchecked(_words: &mut [u32], _at: usize, _value: u32) {
            panic!("the form fixture never stores through its read face")
        }
    }

    struct TrapWordSeam;

    unsafe impl WordSeam for TrapWordSeam {
        unsafe fn read_u32_unchecked(_words: &[u32], _at: usize) -> u32 {
            panic!("a short form must not enter the seam")
        }

        unsafe fn store_u32_unchecked(_words: &mut [u32], _at: usize, _value: u32) {
            panic!("a short form must not enter the seam")
        }
    }

    fn maximal_compact_form() -> RegionalForm {
        RegionalForm {
            same: Cog {
                mag: u32::MAX,
                rank: Rung {
                    mag: u32::MAX,
                    rank: i32::MAX,
                    neg: true,
                },
                turn: 3,
            },
            other: Cog {
                mag: u32::MAX,
                rank: Rung {
                    mag: u32::MAX,
                    rank: i32::MAX,
                    neg: true,
                },
                turn: 3,
            },
            this_way: Rung {
                mag: u32::MAX,
                rank: i32::MAX,
                neg: true,
            },
            that_way: Rung {
                mag: u32::MAX,
                rank: i32::MAX,
                neg: true,
            },
            occupied: true,
        }
    }

    #[test]
    fn the_active_direct_form_has_the_exact_eleven_word_layout() {
        assert_eq!(COMPACT_FORM_LAYOUT_VERSION, 1);
        assert_eq!(COMPACT_FORM_WORDS, 11);
        assert_eq!(FORM_WORDS, 11, "the direct form is the active shared mouth");
        assert_eq!(COG_WORDS, 5, "the generic Cog wire remains whole");
        assert_eq!(RUNG_WORDS, 3, "the generic Rung wire remains whole");
        assert_eq!(crate::manifold::OWN_CELL_WORDS, 22);
        assert_eq!(crate::manifold::RADIATION_WORDS, 39);

        let form = maximal_compact_form();
        let mut row = [0x55aa55aau32; COMPACT_FORM_WORDS + 2];
        form.pack(&mut row, 1);
        assert_eq!(row[0], 0x55aa55aa);
        assert_eq!(row[COMPACT_FORM_WORDS + 1], 0x55aa55aa);
        assert_eq!(
            &row[1..1 + COMPACT_FORM_WORDS],
            &[
                u32::MAX,
                u32::MAX,
                i32::MAX as u32,
                u32::MAX,
                u32::MAX,
                i32::MAX as u32,
                u32::MAX,
                i32::MAX as u32,
                u32::MAX,
                i32::MAX as u32,
                COMPACT_FORM_KNOWN_FLAGS,
            ]
        );
        assert_eq!(RegionalForm::unpack_compact_checked(&row, 1), Ok(form));
        assert_eq!(
            RegionalForm::unpack_with::<MirrorWordSeam>(&row, 1),
            form,
            "the device-oriented active reader preserves every direct field",
        );
        assert_eq!(
            RegionalForm::unpack_compact_trusted_with::<MirrorWordSeam>(&row, 1),
            form
        );
    }

    #[test]
    fn compact_unborn_and_occupied_zero_are_distinct_canonical_rows() {
        let unborn = [0u32; COMPACT_FORM_WORDS];
        assert_eq!(
            RegionalForm::unpack_compact_checked(&unborn, 0),
            Ok(RegionalForm::UNBORN)
        );

        let occupied_zero = RegionalForm::UNBORN.occupy();
        let mut row = [0u32; COMPACT_FORM_WORDS];
        occupied_zero.pack(&mut row, 0);
        assert_eq!(row[COMPACT_FORM_FLAGS_WORD], COMPACT_FORM_OCCUPIED_BIT);
        assert!(row[..COMPACT_FORM_FLAGS_WORD].iter().all(|word| *word == 0));
        assert_eq!(
            RegionalForm::unpack_compact_checked(&row, 0),
            Ok(occupied_zero)
        );
        assert_ne!(occupied_zero, RegionalForm::UNBORN);

        // Zero magnitude does not universally erase grain: cancellation after a raised transport
        // lawfully retains the rank at which it occurred. Compact11 preserves that construction;
        // only the explicit all-zero occupied fixture above is flags-only.
        let raised = Cog::lit(7).turn_up(9).add(Cog::lit(-7).turn_up(9));
        assert_eq!(raised.mag, 0);
        assert_ne!(raised.rank, Rung::ZERO);
        let raised_zero =
            RegionalForm::from_components(raised, Cog::ZERO, Rung::ZERO, Rung::ZERO).occupy();
        let mut raised_row = [0u32; COMPACT_FORM_WORDS];
        raised_zero.pack(&mut raised_row, 0);
        assert_ne!(raised_row[COMPACT_FORM_SAME_RANK_MAG_WORD], 0);
        assert_eq!(
            RegionalForm::unpack_compact_checked(&raised_row, 0),
            Ok(raised_zero),
            "a zero magnitude keeps the grain at which its cancellation lived"
        );
    }

    #[test]
    fn every_compact_flag_pattern_is_either_exact_or_rejected_without_clipping() {
        let mut flags = 0u32;
        while flags <= COMPACT_FORM_KNOWN_FLAGS {
            let mut row = [0u32; COMPACT_FORM_WORDS];
            row[COMPACT_FORM_FLAGS_WORD] = flags;
            let decoded = RegionalForm::unpack_compact_checked(&row, 0);
            if flags == 0 {
                assert_eq!(decoded, Ok(RegionalForm::UNBORN));
            } else if flags & COMPACT_FORM_OCCUPIED_BIT != 0 {
                let form = decoded.expect("every occupied lower-nine-bit pattern is representable");
                let mut repacked = [0u32; COMPACT_FORM_WORDS];
                form.pack(&mut repacked, 0);
                assert_eq!(repacked, row, "flags {flags:#x} crossed without clipping");
            } else {
                assert_eq!(decoded, Err(CompactFormError::UnoccupiedNonzeroData));
            }
            flags += 1;
        }

        let mut bit = 9u32;
        while bit < 32 {
            let reserved = 1u32 << bit;
            let mut row = [0u32; COMPACT_FORM_WORDS];
            row[COMPACT_FORM_FLAGS_WORD] = COMPACT_FORM_OCCUPIED_BIT | reserved;
            assert_eq!(
                RegionalForm::unpack_compact_checked(&row, 0),
                Err(CompactFormError::ReservedFlags { flags: reserved })
            );
            bit += 1;
        }
    }

    #[test]
    fn compact_checked_decode_rejects_every_short_rank_and_unoccupied_data_face() {
        let full = [0u32; COMPACT_FORM_WORDS];
        let mut len = 0usize;
        while len < COMPACT_FORM_WORDS {
            assert_eq!(
                RegionalForm::unpack_compact_checked_with::<TrapWordSeam>(&full[..len], 0),
                Err(CompactFormError::ShortRow)
            );
            len += 1;
        }
        assert_eq!(
            RegionalForm::unpack_compact_checked(&full, usize::MAX),
            Err(CompactFormError::ShortRow)
        );

        for word in [
            COMPACT_FORM_SAME_RANK_RANK_WORD,
            COMPACT_FORM_OTHER_RANK_RANK_WORD,
            COMPACT_FORM_THIS_WAY_RANK_WORD,
            COMPACT_FORM_THAT_WAY_RANK_WORD,
        ] {
            for value in [i32::MAX as u32 + 1, u32::MAX] {
                let mut row = [0u32; COMPACT_FORM_WORDS];
                row[word] = value;
                row[COMPACT_FORM_FLAGS_WORD] = COMPACT_FORM_OCCUPIED_BIT;
                assert_eq!(
                    RegionalForm::unpack_compact_checked(&row, 0),
                    Err(CompactFormError::RankOutOfRange { word, value })
                );
            }
        }

        let mut word = 0usize;
        while word < COMPACT_FORM_DATA_WORDS {
            let mut row = [0u32; COMPACT_FORM_WORDS];
            row[word] = 1;
            assert_eq!(
                RegionalForm::unpack_compact_checked(&row, 0),
                Err(CompactFormError::UnoccupiedNonzeroData)
            );
            word += 1;
        }
    }

    #[test]
    #[should_panic(expected = "malformed compact RegionalForm at a trusted seam")]
    fn the_complete_active_reader_never_clips_a_malformed_row() {
        let mut row = [0u32; COMPACT_FORM_WORDS];
        row[COMPACT_FORM_FLAGS_WORD] = COMPACT_FORM_OCCUPIED_BIT | (1 << 31);
        let _ = RegionalForm::unpack(&row, 0);
    }

    #[test]
    fn compact_trusted_input_rejects_out_of_domain_turns_and_negative_ranks() {
        for (other, turn) in [
            (false, 4u32),
            (false, u32::MAX),
            (true, 4),
            (true, u32::MAX),
        ] {
            let mut form = RegionalForm::UNBORN.occupy();
            if other {
                form.other.turn = turn;
            } else {
                form.same.turn = turn;
            }
            assert_eq!(
                form.validate_compact(),
                Err(CompactFormError::TurnOutOfRange { other, turn })
            );
        }

        for word in [
            COMPACT_FORM_SAME_RANK_RANK_WORD,
            COMPACT_FORM_OTHER_RANK_RANK_WORD,
            COMPACT_FORM_THIS_WAY_RANK_WORD,
            COMPACT_FORM_THAT_WAY_RANK_WORD,
        ] {
            let mut form = RegionalForm::UNBORN.occupy();
            match word {
                COMPACT_FORM_SAME_RANK_RANK_WORD => form.same.rank.rank = -1,
                COMPACT_FORM_OTHER_RANK_RANK_WORD => form.other.rank.rank = -1,
                COMPACT_FORM_THIS_WAY_RANK_WORD => form.this_way.rank = -1,
                COMPACT_FORM_THAT_WAY_RANK_WORD => form.that_way.rank = -1,
                _ => unreachable!(),
            }
            assert_eq!(
                form.validate_compact(),
                Err(CompactFormError::RankOutOfRange {
                    word,
                    value: u32::MAX,
                })
            );
        }

        let mut malformed = RegionalForm::UNBORN.occupy();
        malformed.same.turn = 4;
        let mut canaries = [0x5a5a_5a5au32; COMPACT_FORM_WORDS + 2];
        let before = canaries;
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            malformed.pack(&mut canaries, 1);
        }));
        assert!(
            rejected.is_err(),
            "an out-of-domain turn cannot enter compact packing"
        );
        assert_eq!(canaries, before, "pack validates before its first store");

        malformed.same.turn = 0;
        malformed.this_way.rank = -1;
        let rejected = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            malformed.pack(&mut canaries, 1);
        }));
        assert!(
            rejected.is_err(),
            "a negative inner rank cannot enter compact packing"
        );
        assert_eq!(canaries, before, "rank rejection also precedes every store");
    }

    #[test]
    #[should_panic(expected = "malformed compact RegionalForm at a trusted seam")]
    fn compact_trusted_unpack_asserts_the_boundary_invariants() {
        let mut row = [0u32; COMPACT_FORM_WORDS];
        row[COMPACT_FORM_FLAGS_WORD] = 1 << 31;
        let _ = RegionalForm::unpack_compact_trusted(&row, 0);
    }
}
