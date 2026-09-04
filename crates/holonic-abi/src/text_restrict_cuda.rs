//! Exact resident text-section restriction at the CUDA membrane.
//!
//! The cpu text owner supplies one bounded aperture plus interned feature and transport
//! coordinates. The resident card follows its append-only incidence links, returns only the
//! caused section handles which fit that aperture, and restricts those handles exactly. No
//! question/proof role, semantic rank, dominance population, or cpu-selected section list exists
//! in this ABI.

pub const SELECT_ENTRY_SYMBOL: &str = "text_incidence_select";
pub const RESTRICT_ENTRY_SYMBOL: &str = "text_section_restrict";
pub const LAYOUT_VERSION: u32 = 8;
pub const OPEN_LINK: u32 = u32::MAX;

// One bounded receiver-local physical restriction request.
pub const VERSION: usize = 0;
pub const EPOCH: usize = 1;
pub const APERTURE: usize = 2;
pub const LEADER_FEATURES: usize = 3;
pub const QUERY_TRANSPORTS: usize = 4;
pub const FEATURE_MASK_WORDS: usize = 5;
pub const TRANSPORT_MASK_WORDS: usize = 6;
pub const LEADER_FEATURES_AT: usize = 7;
pub const QUERY_TRANSPORTS_AT: usize = 8;
pub const FEATURE_CURSORS_AT: usize = 9;
pub const TOTAL_WORDS: usize = 10;
pub const HEADER_WORDS: usize = 11;

// One bounded returned restriction body. The two-word header reports exact population testimony;
// every following row starts with the caused resident section handle and then its exact masks.
pub const RETURN_COMPLETE_POPULATION: usize = 0;
pub const RETURN_HANDLE_POPULATION: usize = 1;
pub const RETURN_HEADER_WORDS: usize = 2;
pub const RETURN_SECTION_HANDLE: usize = 0;
pub const RETURN_MASK_AT: usize = 1;

// One resident section row. Offsets address the retained feature/token bodies directly.
pub const SECTION_FEATURE_AT: usize = 0;
pub const SECTION_FEATURES: usize = 1;
pub const SECTION_TOKEN_AT: usize = 2;
pub const SECTION_TOKENS: usize = 3;
pub const SECTION_ROW_WORDS: usize = 4;

// One node in the append-only resident feature-to-section incidence population.
pub const FEATURE_NODE_SECTION: usize = 0;
pub const FEATURE_NODE_NEXT: usize = 1;
pub const FEATURE_NODE_WORDS: usize = 2;

pub const TRANSPORT_WORDS: usize = 2;

#[inline]
pub const fn mask_words(population: usize) -> usize {
    population.div_ceil(u32::BITS as usize)
}
