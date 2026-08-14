//! Exact morphological-conduct attachment at the CUDA execution membrane.
//!
//! **The card decides membership; the host never computes the incidence.**  The semantic owner
//! ships two independently assembled key sheets — one row per deposit carrying that deposit's own
//! exact transport key, and one row per (candidate, candidate-key) pair carrying the key the
//! candidate could ride — and the card matches them.  One lane per candidate binary-searches the
//! canonically ordered deposit sheet for each of its keys and writes only the deposit ordinals it
//! found.  Nothing that resembles the answer crosses the membrane in the ingress direction.
//!
//! The first version of this layout carried a host-built `relation` sheet of
//! `[candidate, deposit, face]` triples, which is the join already performed: the card returned
//! the identity on it and the host re-verified.  That is an echo and not a carrier, and it is
//! withdrawn at `LAYOUT_VERSION = 2`.
//!
//! **Canonical order is a property of the atlas, not a precomputed answer.**  The deposit sheet is
//! the conduct morphology's own ordered relation and the key rows are each candidate's own ordered
//! key set; the card *refuses* either sheet if it is not strictly ascending, so the ordering it
//! relies on for the search is a validated input rather than an assumption.

pub const ENTRY_SYMBOL: &str = "morphological_conduct_group";
pub const LAYOUT_VERSION: u32 = 3;

pub const STATUS_INCOMPLETE: u32 = 0;
pub const STATUS_COMPLETE: u32 = 1;
pub const STATUS_INVALID: u32 = 2;
/// A key row ordinal reserved to mean "no key row was refused".
pub const OPEN_KEY_ROW: u32 = u32::MAX;
/// A candidate face reserved to mean "no face", and therefore refused as a face.
pub const OPEN_FACE: u32 = u32::MAX;
/// A match slot carrying no deposit.
pub const OPEN_DEPOSIT: u32 = u32::MAX;

pub const CONTROL_VERSION: usize = 0;
pub const CONTROL_EPOCH: usize = 1;
pub const CONTROL_CANDIDATES: usize = 2;
pub const CONTROL_DEPOSITS: usize = 3;
pub const CONTROL_KEY_ROWS: usize = 4;
/// Words in one exact transport key. Derived from the material by the semantic owner; a key of
/// zero words is not a key and is refused.
pub const CONTROL_KEY_WORDS: usize = 5;
/// The largest number of key rows any one candidate carries, which is what makes the returned row
/// width exact. It is read off the front, never authored.
pub const CONTROL_MAX_CANDIDATE_KEYS: usize = 6;
pub const CONTROL_CANDIDATE_WORDS: usize = 7;
pub const CONTROL_CANDIDATE_TOTAL_WORDS: usize = 8;
pub const CONTROL_DEPOSIT_ROW_WORDS: usize = 9;
pub const CONTROL_DEPOSIT_TOTAL_WORDS: usize = 10;
pub const CONTROL_KEY_ROW_WORDS: usize = 11;
pub const CONTROL_KEY_ROW_TOTAL_WORDS: usize = 12;
pub const CONTROL_OUTPUT_ROW_WORDS: usize = 13;
pub const CONTROL_OUTPUT_TOTAL_WORDS: usize = 14;
pub const CONTROL_TOTAL_WORDS: usize = 15;
pub const CONTROL_WORDS: usize = 16;

pub const CANDIDATE_FACE: usize = 0;
pub const CANDIDATE_WORDS: usize = 1;

pub const DEPOSIT_ACTIVE: usize = 0;
pub const DEPOSIT_KEY_AT: usize = 1;

pub const KEY_ROW_CANDIDATE: usize = 0;
pub const KEY_ROW_KEY_AT: usize = 1;

pub const OUTPUT_STATUS: usize = 0;
pub const OUTPUT_VERSION: usize = 1;
pub const OUTPUT_EPOCH: usize = 2;
pub const OUTPUT_CANDIDATES: usize = 3;
pub const OUTPUT_DEPOSITS: usize = 4;
pub const OUTPUT_KEY_ROWS: usize = 5;
pub const OUTPUT_ACTIVE_DEPOSITS: usize = 6;
pub const OUTPUT_MAX_CANDIDATE_KEYS: usize = 7;
pub const OUTPUT_CANDIDATE_ROW_WORDS: usize = 8;
pub const OUTPUT_CANDIDATE_ROWS_AT: usize = 9;
pub const OUTPUT_TOTAL_WORDS: usize = 10;
pub const OUTPUT_INVALID_KEY_ROW: usize = 11;
/// **Why the card declined, by name.**
///
/// The shape agreement the card performs before it starts is roughly twenty separate checks, and
/// it used to answer all of them with one status word. A host reading that could say only "the card
/// refused" — and worse, on the decline path the card never reaches the header fields, so a host
/// walking them reported the first unwritten word as the disagreement. These three words carry the
/// cause ordinal and, where the check is an equality of extents, the two extents that disagreed.
pub const OUTPUT_REFUSAL_CAUSE: usize = 12;
pub const OUTPUT_REFUSAL_DECLARED: usize = 13;
pub const OUTPUT_REFUSAL_FOUND: usize = 14;
pub const OUTPUT_HEADER_WORDS: usize = 15;

/// No shape refusal was recorded.
pub const REFUSAL_NONE: u32 = 0;
pub const REFUSAL_CONTROL_EXTENT: u32 = 1;
pub const REFUSAL_CONTROL_VERSION: u32 = 2;
pub const REFUSAL_CONTROL_EPOCH_ZERO: u32 = 3;
pub const REFUSAL_CONTROL_TOTAL_WORDS: u32 = 4;
pub const REFUSAL_KEY_WORDS_ZERO: u32 = 5;
pub const REFUSAL_MAX_CANDIDATE_KEYS: u32 = 6;
pub const REFUSAL_EXTENT_OVERFLOW: u32 = 7;
pub const REFUSAL_CONTROL_CANDIDATE_WORDS: u32 = 8;
pub const REFUSAL_CONTROL_CANDIDATE_TOTAL_WORDS: u32 = 9;
pub const REFUSAL_CONTROL_DEPOSIT_ROW_WORDS: u32 = 10;
pub const REFUSAL_CONTROL_DEPOSIT_TOTAL_WORDS: u32 = 11;
pub const REFUSAL_CONTROL_KEY_ROW_WORDS: u32 = 12;
pub const REFUSAL_CONTROL_KEY_ROW_TOTAL_WORDS: u32 = 13;
pub const REFUSAL_CONTROL_OUTPUT_ROW_WORDS: u32 = 14;
pub const REFUSAL_CONTROL_OUTPUT_TOTAL_WORDS: u32 = 15;
pub const REFUSAL_CANDIDATE_SHEET_EXTENT: u32 = 16;
pub const REFUSAL_DEPOSIT_SHEET_EXTENT: u32 = 17;
pub const REFUSAL_KEY_ROW_SHEET_EXTENT: u32 = 18;
pub const REFUSAL_OUTPUT_SHEET_EXTENT: u32 = 19;
pub const REFUSAL_DEPOSIT_ACTIVITY_WORD: u32 = 20;
pub const REFUSAL_DEPOSIT_SHEET_UNSORTED: u32 = 21;
pub const REFUSAL_CANDIDATE_FACE_OPEN: u32 = 22;
pub const REFUSAL_ACTIVE_DEPOSIT_OVERFLOW: u32 = 23;

/// The name of a refusal ordinal. One table, on the host side of the same wire the card writes.
pub const fn refusal_cause_name(cause: u32) -> &'static str {
    match cause {
        REFUSAL_NONE => "no shape refusal was recorded",
        REFUSAL_CONTROL_EXTENT => "the control block is not the declared word count",
        REFUSAL_CONTROL_VERSION => "the control block declares a different layout version",
        REFUSAL_CONTROL_EPOCH_ZERO => "the control block declares epoch zero",
        REFUSAL_CONTROL_TOTAL_WORDS => "the control block's own total-words word disagrees",
        REFUSAL_KEY_WORDS_ZERO => "the control block declares a key of zero words",
        REFUSAL_MAX_CANDIDATE_KEYS => {
            "the declared maximum candidate keys exceeds the key-row population"
        }
        REFUSAL_EXTENT_OVERFLOW => "a derived sheet extent overflowed",
        REFUSAL_CONTROL_CANDIDATE_WORDS => "the control block's candidate row width disagrees",
        REFUSAL_CONTROL_CANDIDATE_TOTAL_WORDS => {
            "the control block's candidate sheet extent disagrees"
        }
        REFUSAL_CONTROL_DEPOSIT_ROW_WORDS => "the control block's deposit row width disagrees",
        REFUSAL_CONTROL_DEPOSIT_TOTAL_WORDS => "the control block's deposit sheet extent disagrees",
        REFUSAL_CONTROL_KEY_ROW_WORDS => "the control block's key row width disagrees",
        REFUSAL_CONTROL_KEY_ROW_TOTAL_WORDS => "the control block's key sheet extent disagrees",
        REFUSAL_CONTROL_OUTPUT_ROW_WORDS => "the control block's output row width disagrees",
        REFUSAL_CONTROL_OUTPUT_TOTAL_WORDS => "the control block's output extent disagrees",
        REFUSAL_CANDIDATE_SHEET_EXTENT => {
            "the candidate sheet the card received is not the declared extent"
        }
        REFUSAL_DEPOSIT_SHEET_EXTENT => {
            "the deposit sheet the card received is not the declared extent"
        }
        REFUSAL_KEY_ROW_SHEET_EXTENT => {
            "the key sheet the card received is not the declared extent"
        }
        REFUSAL_OUTPUT_SHEET_EXTENT => {
            "the output sheet the card received is not the declared extent"
        }
        REFUSAL_DEPOSIT_ACTIVITY_WORD => {
            "a deposit carries an activity word that is neither zero nor one"
        }
        REFUSAL_DEPOSIT_SHEET_UNSORTED => "the deposit sheet is not strictly ascending by key",
        REFUSAL_CANDIDATE_FACE_OPEN => "a candidate carries the reserved open face",
        REFUSAL_ACTIVE_DEPOSIT_OVERFLOW => "the active deposit count overflowed",
        _ => "the card recorded a refusal ordinal this host does not name",
    }
}

pub const CANDIDATE_STATUS: usize = 0;
pub const CANDIDATE_EPOCH: usize = 1;
pub const CANDIDATE_ORDINAL: usize = 2;
pub const CANDIDATE_OUTPUT_FACE: usize = 3;
/// How many key rows the card itself saw for this candidate. The host knows what it shipped; this
/// is the card saying what it read, and the two are compared.
pub const CANDIDATE_KEY_ROWS: usize = 4;
pub const CANDIDATE_ACTIVE_DEPOSITS: usize = 5;
pub const CANDIDATE_MATCH_AT: usize = 6;

#[inline]
pub const fn deposit_row_words(key_words: usize) -> Option<usize> {
    if key_words == 0 {
        return None;
    }
    DEPOSIT_KEY_AT.checked_add(key_words)
}

#[inline]
pub const fn key_row_words(key_words: usize) -> Option<usize> {
    if key_words == 0 {
        return None;
    }
    KEY_ROW_KEY_AT.checked_add(key_words)
}

#[inline]
pub const fn candidate_row_words(max_candidate_keys: usize) -> Option<usize> {
    CANDIDATE_MATCH_AT.checked_add(max_candidate_keys)
}

#[inline]
pub const fn output_words(candidates: usize, max_candidate_keys: usize) -> Option<usize> {
    let Some(row) = candidate_row_words(max_candidate_keys) else {
        return None;
    };
    let Some(rows) = candidates.checked_mul(row) else {
        return None;
    };
    OUTPUT_HEADER_WORDS.checked_add(rows)
}

/// One candidate row. The face is the candidate's own receiver coordinate; it never enters the
/// transport key and never decides a match.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MorphologicalConductCandidate {
    words: [u32; CANDIDATE_WORDS],
}

impl MorphologicalConductCandidate {
    pub const fn new(face: u32) -> Option<Self> {
        if face == OPEN_FACE {
            return None;
        }
        Some(Self { words: [face] })
    }

    pub const fn from_words(words: [u32; CANDIDATE_WORDS]) -> Option<Self> {
        if words[CANDIDATE_FACE] == OPEN_FACE {
            return None;
        }
        Some(Self { words })
    }

    pub const fn words(self) -> [u32; CANDIDATE_WORDS] {
        self.words
    }

    pub const fn face(self) -> u32 {
        self.words[CANDIDATE_FACE]
    }
}

/// Exact lexicographic comparison of two keys of the declared width. This is the whole of what
/// decides a match, on either side of the membrane, and it is the same function on both.
#[inline]
pub fn key_precedes(left: &[u32], right: &[u32]) -> bool {
    let mut at = 0usize;
    while at < left.len() && at < right.len() {
        if left[at] != right[at] {
            return left[at] < right[at];
        }
        at += 1;
    }
    left.len() < right.len()
}

#[inline]
pub fn key_equals(left: &[u32], right: &[u32]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut at = 0usize;
    while at < left.len() {
        if left[at] != right[at] {
            return false;
        }
        at += 1;
    }
    true
}

pub fn control(
    epoch: u32,
    candidates: usize,
    deposits: usize,
    key_rows: usize,
    key_words: usize,
    max_candidate_keys: usize,
) -> Option<[u32; CONTROL_WORDS]> {
    if epoch == 0 || key_words == 0 || max_candidate_keys > key_rows {
        return None;
    }
    let candidate_total_words = candidates.checked_mul(CANDIDATE_WORDS)?;
    let deposit_row = deposit_row_words(key_words)?;
    let deposit_total_words = deposits.checked_mul(deposit_row)?;
    let key_row = key_row_words(key_words)?;
    let key_row_total_words = key_rows.checked_mul(key_row)?;
    let output_row_words = candidate_row_words(max_candidate_keys)?;
    let output_total_words = output_words(candidates, max_candidate_keys)?;
    Some([
        LAYOUT_VERSION,
        epoch,
        u32::try_from(candidates).ok()?,
        u32::try_from(deposits).ok()?,
        u32::try_from(key_rows).ok()?,
        u32::try_from(key_words).ok()?,
        u32::try_from(max_candidate_keys).ok()?,
        CANDIDATE_WORDS as u32,
        u32::try_from(candidate_total_words).ok()?,
        u32::try_from(deposit_row).ok()?,
        u32::try_from(deposit_total_words).ok()?,
        u32::try_from(key_row).ok()?,
        u32::try_from(key_row_total_words).ok()?,
        u32::try_from(output_row_words).ok()?,
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
        words[CONTROL_CANDIDATES] as usize,
        words[CONTROL_DEPOSITS] as usize,
        words[CONTROL_KEY_ROWS] as usize,
        words[CONTROL_KEY_WORDS] as usize,
        words[CONTROL_MAX_CANDIDATE_KEYS] as usize,
    ) else {
        return false;
    };
    words == expected
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn candidate_rows_preserve_typed_faces() {
        let candidate = MorphologicalConductCandidate::new(17).unwrap();
        assert_eq!(
            MorphologicalConductCandidate::from_words(candidate.words()),
            Some(candidate)
        );
        assert_eq!(candidate.face(), 17);
        assert!(MorphologicalConductCandidate::new(OPEN_FACE).is_none());
    }

    #[test]
    fn key_order_is_lexicographic_and_width_sensitive() {
        assert!(key_precedes(&[1, 2, 3], &[1, 2, 4]));
        assert!(!key_precedes(&[1, 2, 4], &[1, 2, 3]));
        assert!(!key_precedes(&[1, 2, 3], &[1, 2, 3]));
        assert!(key_precedes(&[1, 2], &[1, 2, 0]));
        assert!(key_equals(&[7, 8], &[7, 8]));
        assert!(!key_equals(&[7, 8], &[7, 8, 0]));
    }

    #[test]
    fn every_refusal_ordinal_is_named_and_the_unknown_one_says_so() {
        // A cause the host cannot name is worse than no cause, so the table is required to cover
        // every ordinal the card can write and to say plainly when it does not.
        for cause in REFUSAL_NONE..=REFUSAL_ACTIVE_DEPOSIT_OVERFLOW {
            let name = refusal_cause_name(cause);
            assert!(!name.is_empty());
            assert_ne!(
                name,
                refusal_cause_name(REFUSAL_ACTIVE_DEPOSIT_OVERFLOW + 1),
                "ordinal {cause} falls through to the unknown arm"
            );
        }
        assert_eq!(
            refusal_cause_name(u32::MAX),
            "the card recorded a refusal ordinal this host does not name"
        );
    }

    #[test]
    fn dynamic_layout_is_exact_at_declared_key_and_match_widths() {
        assert_eq!(deposit_row_words(0), None);
        assert_eq!(key_row_words(0), None);
        assert_eq!(deposit_row_words(11), Some(12));
        assert_eq!(key_row_words(11), Some(12));
        assert_eq!(candidate_row_words(0), Some(6));
        assert_eq!(candidate_row_words(3), Some(9));
        assert_eq!(output_words(4, 3), Some(51));

        let row = control(5, 4, 33, 7, 11, 3).unwrap();
        assert!(control_is_canonical(&row));
        assert_eq!(row[CONTROL_KEY_WORDS], 11);
        assert_eq!(row[CONTROL_DEPOSIT_ROW_WORDS], 12);
        assert_eq!(row[CONTROL_KEY_ROW_WORDS], 12);
        assert_eq!(row[CONTROL_OUTPUT_ROW_WORDS], 9);
        assert_eq!(row[CONTROL_OUTPUT_TOTAL_WORDS], 51);

        let mut forged = row;
        forged[CONTROL_OUTPUT_ROW_WORDS] += 1;
        assert!(!control_is_canonical(&forged));
        assert!(control(0, 1, 1, 1, 1, 1).is_none());
        // A key of zero words is not a key.
        assert!(control(1, 1, 1, 1, 0, 1).is_none());
        // No candidate can carry more keys than the whole front has key rows.
        assert!(control(1, 1, 1, 2, 4, 3).is_none());
    }
}
