//! **Text repair by local keys glued on overlaps** (the
//! [record](../../records/2026-10-05_TEXT_REPAIR_BY_LOCAL_KEYS_GLUED_ON_OVERLAPS.md); #73, #148,
//! #63). [historical; retired October 5 with THE_MACHINE guard 9 at the field's entries] The mode
//! read 48-byte passages of a cut's development range on the byte chart's `2⁸` ports and located local
//! keys over them: the codec's grain, which guard 9 refuses. Its source is at
//! [`f91666c0`](https://github.com/brandonrdug/holonics/blob/f91666c0/research/notebook/hnn_design/hnn_text_repair.rs).
//!
//! ```sh
//! cargo run --release -p holonics --example hnn_prediction -- executed text-repair <cut> <out dir> <pin> <dev|run>
//! ```
//!
//! [definition; agent-inferred, October 5; THE_MACHINE guards 9, 21 and 22] The mode still takes its
//! committed pin and reads the cut only through `exterior::read_cut`, and its result is guard 9's
//! refusal: a byte passage enters the field only as `hnn::encoding::Encoded`, built from a founded
//! encoding (`Encoded::through` over a located chart), and no encoding of the cut's bytes is founded.

use super::*;

/// **The mode's result: the refusal** (module header).
pub(super) fn run(cut: &str) {
    let exterior::Cut { population, .. } = exterior::read_cut(cut);
    println!(
        "executed text-repair: the cut's {population} bytes; refused: {} (THE_MACHINE guard 9: a byte \
         passage enters the field only through a founded encoding, and no encoding of bytes is founded)",
        holonics::hnn::EncodingError::Unencoded
    );
}
