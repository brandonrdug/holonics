//! Exact returned-contact grouping at the CUDA execution membrane.
//!
//! The semantic owner presents a sparse population of integer-addressed local movements.  CUDA
//! groups that population by target and, independently, returns one disposition per causing
//! occurrence.  Strings, passage objects, provenance maps, and morphology do not cross this ABI;
//! their owner retains the exact atlases behind the two ordinals.

pub const ENTRY_SYMBOL: &str = "returned_contact_group";
pub const LAYOUT_VERSION: u32 = 1;

pub const STATUS_INCOMPLETE: u32 = 0;
pub const STATUS_COMPLETE: u32 = 1;
pub const STATUS_INVALID: u32 = 2;
pub const OPEN_RELATION: u32 = u32::MAX;

// One control row.  Redundant offsets and widths are carried deliberately: both sides validate the
// exact dynamic layout before reading a variable-width target row.
pub const CONTROL_VERSION: usize = 0;
pub const CONTROL_EPOCH: usize = 1;
pub const CONTROL_TARGETS: usize = 2;
pub const CONTROL_OCCURRENCES: usize = 3;
pub const CONTROL_RELATIONS: usize = 4;
pub const CONTROL_OCCURRENCE_MASK_WORDS: usize = 5;
pub const CONTROL_RELATION_WORDS: usize = 6;
pub const CONTROL_RELATION_TOTAL_WORDS: usize = 7;
pub const CONTROL_TARGET_ROW_WORDS: usize = 8;
pub const CONTROL_TARGET_ROWS_AT: usize = 9;
pub const CONTROL_OCCURRENCE_ROW_WORDS: usize = 10;
pub const CONTROL_OCCURRENCE_ROWS_AT: usize = 11;
pub const CONTROL_OUTPUT_TOTAL_WORDS: usize = 12;
pub const CONTROL_TOTAL_WORDS: usize = 13;
pub const CONTROL_WORDS: usize = 14;

// One sparse local movement.  The two state words are canonical booleans and must differ.  Thus a
// row is either a withdrawal (1 -> 0) or a founding (0 -> 1), never a still comparison.
pub const RELATION_TARGET: usize = 0;
pub const RELATION_OCCURRENCE: usize = 1;
pub const RELATION_STOOD_BEFORE: usize = 2;
pub const RELATION_STANDS_AFTER: usize = 3;
pub const RELATION_WORDS: usize = 4;

// Returned header.  `INVALID_RELATION` is the first malformed input row found by the header lane;
// duplicate target/occurrence pairs are reported by the uniquely-owned target row instead.
pub const OUTPUT_STATUS: usize = 0;
pub const OUTPUT_VERSION: usize = 1;
pub const OUTPUT_EPOCH: usize = 2;
pub const OUTPUT_TARGETS: usize = 3;
pub const OUTPUT_OCCURRENCES: usize = 4;
pub const OUTPUT_RELATIONS: usize = 5;
pub const OUTPUT_OCCURRENCE_MASK_WORDS: usize = 6;
pub const OUTPUT_TARGET_ROW_WORDS: usize = 7;
pub const OUTPUT_TARGET_ROWS_AT: usize = 8;
pub const OUTPUT_OCCURRENCE_ROW_WORDS: usize = 9;
pub const OUTPUT_OCCURRENCE_ROWS_AT: usize = 10;
pub const OUTPUT_TOTAL_WORDS: usize = 11;
pub const OUTPUT_INVALID_RELATION: usize = 12;
pub const OUTPUT_HEADER_WORDS: usize = 13;

// One row per target, in target-ordinal order.  The two masks are disjoint because every admitted
// relation has exactly one live side.  Bits address occurrence ordinals directly.
pub const TARGET_STATUS: usize = 0;
pub const TARGET_EPOCH: usize = 1;
pub const TARGET_ORDINAL: usize = 2;
pub const TARGET_WITHDRAWN: usize = 3;
pub const TARGET_FOUNDED: usize = 4;
pub const TARGET_WITHDRAWN_MASK_AT: usize = 5;

// One row per occurrence, in occurrence-ordinal order.  This is the card's independent disposition
// of the occurrence over all targets; the host does not transpose the target masks to reconstruct it.
pub const OCCURRENCE_STATUS: usize = 0;
pub const OCCURRENCE_EPOCH: usize = 1;
pub const OCCURRENCE_ORDINAL: usize = 2;
pub const OCCURRENCE_WITHDRAWN_TARGETS: usize = 3;
pub const OCCURRENCE_FOUNDED_TARGETS: usize = 4;
pub const OCCURRENCE_ROW_WORDS: usize = 5;

#[inline]
pub const fn mask_words(population: usize) -> usize {
    population.div_ceil(u32::BITS as usize)
}

#[inline]
pub fn target_row_words(occurrences: usize) -> Option<usize> {
    mask_words(occurrences)
        .checked_mul(2)
        .and_then(|masks| TARGET_WITHDRAWN_MASK_AT.checked_add(masks))
}

#[inline]
pub fn target_founded_mask_at(occurrences: usize) -> Option<usize> {
    TARGET_WITHDRAWN_MASK_AT.checked_add(mask_words(occurrences))
}

#[inline]
pub fn output_words(targets: usize, occurrences: usize) -> Option<usize> {
    let target_words = targets.checked_mul(target_row_words(occurrences)?)?;
    let occurrence_words = occurrences.checked_mul(OCCURRENCE_ROW_WORDS)?;
    OUTPUT_HEADER_WORDS
        .checked_add(target_words)?
        .checked_add(occurrence_words)
}

#[inline]
pub fn occurrence_rows_at(targets: usize, occurrences: usize) -> Option<usize> {
    OUTPUT_HEADER_WORDS.checked_add(targets.checked_mul(target_row_words(occurrences)?)?)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReturnedContactRelation {
    words: [u32; RELATION_WORDS],
}

impl ReturnedContactRelation {
    pub const fn new(
        target: u32,
        occurrence: u32,
        stood_before: bool,
        stands_after: bool,
    ) -> Option<Self> {
        if stood_before == stands_after {
            return None;
        }
        Some(Self {
            words: [target, occurrence, stood_before as u32, stands_after as u32],
        })
    }

    pub const fn from_words(words: [u32; RELATION_WORDS]) -> Option<Self> {
        if words[RELATION_STOOD_BEFORE] > 1
            || words[RELATION_STANDS_AFTER] > 1
            || words[RELATION_STOOD_BEFORE] == words[RELATION_STANDS_AFTER]
        {
            return None;
        }
        Some(Self { words })
    }

    pub const fn words(self) -> [u32; RELATION_WORDS] {
        self.words
    }

    pub const fn target(self) -> u32 {
        self.words[RELATION_TARGET]
    }

    pub const fn occurrence(self) -> u32 {
        self.words[RELATION_OCCURRENCE]
    }

    pub const fn stood_before(self) -> bool {
        self.words[RELATION_STOOD_BEFORE] == 1
    }

    pub const fn stands_after(self) -> bool {
        self.words[RELATION_STANDS_AFTER] == 1
    }
}

/// Form the exact fixed control row for one launch.  Population extents are `u32` at the membrane;
/// larger material is an explicit obstruction rather than a clipped launch.
pub fn control(
    epoch: u32,
    targets: usize,
    occurrences: usize,
    relations: usize,
) -> Option<[u32; CONTROL_WORDS]> {
    if epoch == 0 {
        return None;
    }
    let mask_words = mask_words(occurrences);
    let target_row_words = target_row_words(occurrences)?;
    let relation_total_words = relations.checked_mul(RELATION_WORDS)?;
    let occurrence_rows_at = occurrence_rows_at(targets, occurrences)?;
    let output_total_words = output_words(targets, occurrences)?;
    Some([
        LAYOUT_VERSION,
        epoch,
        u32::try_from(targets).ok()?,
        u32::try_from(occurrences).ok()?,
        u32::try_from(relations).ok()?,
        u32::try_from(mask_words).ok()?,
        RELATION_WORDS as u32,
        u32::try_from(relation_total_words).ok()?,
        u32::try_from(target_row_words).ok()?,
        OUTPUT_HEADER_WORDS as u32,
        OCCURRENCE_ROW_WORDS as u32,
        u32::try_from(occurrence_rows_at).ok()?,
        u32::try_from(output_total_words).ok()?,
        CONTROL_WORDS as u32,
    ])
}

pub fn control_is_canonical(words: &[u32]) -> bool {
    if words.len() != CONTROL_WORDS {
        return false;
    }
    let Some(expected) = control(
        words[CONTROL_EPOCH],
        words[CONTROL_TARGETS] as usize,
        words[CONTROL_OCCURRENCES] as usize,
        words[CONTROL_RELATIONS] as usize,
    ) else {
        return false;
    };
    words == expected
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn relation_rows_are_exact_xor_movements() {
        for (before, after) in [(true, false), (false, true)] {
            let relation = ReturnedContactRelation::new(7, 11, before, after).unwrap();
            assert_eq!(
                ReturnedContactRelation::from_words(relation.words()),
                Some(relation)
            );
            assert_eq!(relation.target(), 7);
            assert_eq!(relation.occurrence(), 11);
            assert_eq!(relation.stood_before(), before);
            assert_eq!(relation.stands_after(), after);
        }
        assert!(ReturnedContactRelation::new(0, 0, false, false).is_none());
        assert!(ReturnedContactRelation::new(0, 0, true, true).is_none());
        assert!(ReturnedContactRelation::from_words([0, 0, 2, 0]).is_none());
    }

    #[test]
    fn dynamic_layout_is_exact_at_mask_boundaries() {
        assert_eq!(mask_words(0), 0);
        assert_eq!(mask_words(1), 1);
        assert_eq!(mask_words(32), 1);
        assert_eq!(mask_words(33), 2);
        assert_eq!(target_row_words(33), Some(9));
        assert_eq!(occurrence_rows_at(3, 33), Some(40));
        assert_eq!(output_words(3, 33), Some(205));

        let control_row = control(9, 3, 33, 7).unwrap();
        assert!(control_is_canonical(&control_row));
        assert_eq!(control_row[CONTROL_RELATION_TOTAL_WORDS], 28);
        assert_eq!(control_row[CONTROL_OUTPUT_TOTAL_WORDS], 205);

        let mut forged = control_row;
        forged[CONTROL_TARGET_ROW_WORDS] += 1;
        assert!(!control_is_canonical(&forged));
        assert!(control(0, 3, 33, 7).is_none());
    }
}
