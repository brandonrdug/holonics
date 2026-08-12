//! Exact word membrane for resident morphological conditioning.
//!
//! The exterior chart supplies dense material symbols and caused source labels.  The card returns
//! the generalized suffix-automaton incidence (including source-tree spans) and the
//! boundary-anchored question-prefix incidence.  No host-built state, transition, suffix link,
//! prefix node, or active-prefix answer crosses into the card.

pub const SUFFIX_ENTRY_SYMBOL: &str = "morphological_suffix_condition";
pub const PREFIX_ENTRY_SYMBOL: &str = "morphological_prefix_condition";
pub const LAYOUT_VERSION: u32 = 1;

pub const STATUS_INCOMPLETE: u32 = 0;
pub const STATUS_COMPLETE: u32 = 1;
pub const STATUS_INVALID: u32 = 2;
pub const OPEN: u32 = u32::MAX;

// Suffix control.
pub const SUFFIX_CONTROL_VERSION: usize = 0;
pub const SUFFIX_CONTROL_INPUTS: usize = 1;
pub const SUFFIX_CONTROL_MATERIAL_SYMBOLS: usize = 2;
pub const SUFFIX_CONTROL_STATE_CAPACITY: usize = 3;
pub const SUFFIX_CONTROL_TRANSITION_CAPACITY: usize = 4;
pub const SUFFIX_CONTROL_OCCURRENCE_CAPACITY: usize = 5;
pub const SUFFIX_CONTROL_SCRATCH_WORDS: usize = 6;
pub const SUFFIX_CONTROL_WORDS: usize = 7;

// One input row: dense symbol, direct source (OPEN for a path boundary), material bit.
pub const SUFFIX_INPUT_SYMBOL: usize = 0;
pub const SUFFIX_INPUT_SOURCE: usize = 1;
pub const SUFFIX_INPUT_MATERIAL: usize = 2;
pub const SUFFIX_INPUT_WORDS: usize = 3;

// One returned state.  All lengths are bounded by the u32 input extent at this membrane.
pub const SUFFIX_STATE_MAXIMUM_LENGTH: usize = 0;
pub const SUFFIX_STATE_SUFFIX: usize = 1;
pub const SUFFIX_STATE_MULTIPLICITY_LO: usize = 2;
pub const SUFFIX_STATE_MULTIPLICITY_HI: usize = 3;
pub const SUFFIX_STATE_TRANSITION_HEAD: usize = 4;
pub const SUFFIX_STATE_DIRECT_SOURCE: usize = 5;
pub const SUFFIX_STATE_SPAN_START: usize = 6;
pub const SUFFIX_STATE_SPAN_LEN: usize = 7;
pub const SUFFIX_STATE_WORDS: usize = 8;

// Mutable transition incidence.  `next` is only the resident adjacency chart; state/symbol/target
// are the semantic edge returned to the host.
pub const SUFFIX_TRANSITION_STATE: usize = 0;
pub const SUFFIX_TRANSITION_SYMBOL: usize = 1;
pub const SUFFIX_TRANSITION_TARGET: usize = 2;
pub const SUFFIX_TRANSITION_NEXT: usize = 3;
pub const SUFFIX_TRANSITION_WORDS: usize = 4;

pub const SUFFIX_OUTPUT_STATUS: usize = 0;
pub const SUFFIX_OUTPUT_VERSION: usize = 1;
pub const SUFFIX_OUTPUT_STATE_COUNT: usize = 2;
pub const SUFFIX_OUTPUT_TRANSITION_COUNT: usize = 3;
pub const SUFFIX_OUTPUT_OCCURRENCE_COUNT: usize = 4;
pub const SUFFIX_OUTPUT_MATERIAL_TRANSITIONS: usize = 5;
pub const SUFFIX_OUTPUT_EXTENSIONS: usize = 6;
pub const SUFFIX_OUTPUT_CLONES: usize = 7;
pub const SUFFIX_OUTPUT_SUFFIX_CROSSES_LO: usize = 8;
pub const SUFFIX_OUTPUT_SUFFIX_CROSSES_HI: usize = 9;
pub const SUFFIX_OUTPUT_TRANSITION_READS_LO: usize = 10;
pub const SUFFIX_OUTPUT_TRANSITION_READS_HI: usize = 11;
pub const SUFFIX_OUTPUT_WORDS: usize = 12;

// Prefix control and path rows.  The token stream contains the complete question clause,
// including its terminal question mark; each proper prefix crossing carries its next token.
pub const PREFIX_CONTROL_VERSION: usize = 0;
pub const PREFIX_CONTROL_PATHS: usize = 1;
pub const PREFIX_CONTROL_TOKENS: usize = 2;
pub const PREFIX_CONTROL_NODE_CAPACITY: usize = 3;
pub const PREFIX_CONTROL_SUPPORT_CAPACITY: usize = 4;
pub const PREFIX_CONTROL_WORDS: usize = 5;

pub const PREFIX_PATH_START: usize = 0;
pub const PREFIX_PATH_LEN: usize = 1;
pub const PREFIX_PATH_SOURCE: usize = 2;
pub const PREFIX_PATH_WORDS: usize = 3;

pub const PREFIX_NODE_PARENT: usize = 0;
pub const PREFIX_NODE_TOKEN: usize = 1;
pub const PREFIX_NODE_FIRST_CHILD: usize = 2;
pub const PREFIX_NODE_NEXT_SIBLING: usize = 3;
pub const PREFIX_NODE_OCCURRENCES: usize = 4;
pub const PREFIX_NODE_FIRST_CONTINUATION: usize = 5;
pub const PREFIX_NODE_DIVERGENT: usize = 6;
pub const PREFIX_NODE_ACTIVE: usize = 7;
pub const PREFIX_NODE_WORDS: usize = 8;

pub const PREFIX_SUPPORT_NODE: usize = 0;
pub const PREFIX_SUPPORT_SOURCE: usize = 1;
pub const PREFIX_SUPPORT_WORDS: usize = 2;

pub const PREFIX_OUTPUT_STATUS: usize = 0;
pub const PREFIX_OUTPUT_VERSION: usize = 1;
pub const PREFIX_OUTPUT_NODE_COUNT: usize = 2;
pub const PREFIX_OUTPUT_SUPPORT_COUNT: usize = 3;
pub const PREFIX_OUTPUT_CROSSINGS_LO: usize = 4;
pub const PREFIX_OUTPUT_CROSSINGS_HI: usize = 5;
pub const PREFIX_OUTPUT_LEGACY_CLONES_LO: usize = 6;
pub const PREFIX_OUTPUT_LEGACY_CLONES_HI: usize = 7;
pub const PREFIX_OUTPUT_RETURNED_TOKENS_LO: usize = 8;
pub const PREFIX_OUTPUT_RETURNED_TOKENS_HI: usize = 9;
pub const PREFIX_OUTPUT_EDGE_READS_LO: usize = 10;
pub const PREFIX_OUTPUT_EDGE_READS_HI: usize = 11;
pub const PREFIX_OUTPUT_WORDS: usize = 12;
