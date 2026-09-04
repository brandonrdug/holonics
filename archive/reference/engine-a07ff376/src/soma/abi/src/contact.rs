//! Transient cooperative REGISTER-contact sheet.

use body::manifold::{FACE_WORDS, NODE_WORDS};
use body::num::COG_WORDS;

/// One transient cooperative REGISTER-contact sheet per mounted lineage.
pub const COMMAND: usize = 0;
pub const LIVE: usize = 1;
pub const HEAD: usize = 2;
pub const REGISTER_LO: usize = 3;
pub const REGISTER_HI: usize = 4;
pub const NODE: usize = 5;
pub const FRAME: usize = NODE + NODE_WORDS;
pub const FLY: usize = FRAME + 2 * COG_WORDS;
pub const FLY_LIVE: usize = FLY + FACE_WORDS;
pub const OUTPUT: usize = FLY_LIVE + 1;

pub const OUTPUT_LIVE: usize = 0;
pub const OUTPUT_SAME: usize = 1;
pub const OUTPUT_OTHER: usize = OUTPUT_SAME + COG_WORDS;
pub const OUTPUT_WORDS: usize = 1 + 2 * COG_WORDS;

pub const RECEIPT: usize = OUTPUT + body::register::REGISTER as usize * OUTPUT_WORDS;
pub const SURFACE_WORDS: usize = RECEIPT + body::register::REGISTER as usize;

pub const COMMAND_FORM: u32 = 1;
pub const COMMAND_STOP: u32 = 2;
