//! **The section chart: a curated stream's parts opened by their section letters** (campaign 5's
//! curated source under HNN_FORMULA's source contract, items 1–3; #73, #148).
//!
//! [definition; agent-inferred] **The chart** ([`SectionChart`]): a stream whose cells are the
//! exterior chart's `B` cells (the UTF-8 bytes of a part, `B = 256`) followed by the **section
//! letters**, one per `(kind, channel)`, coded `B + C·k + c` for kind `k < K` and channel `c < C`
//! (the curated source's `open`, `switch`, `turn`, `part` on the human, agent and tool ports:
//! `|A| = 256 + 12`). A part opens with its one letter, so the channel a cell lies on is never
//! supplied: it is read from the coded past, at the part's section.
//!
//! [definition] **Retired September 30** with the byte-tree text line (THE_REBUILD U6's order,
//! C.5; history at `f5fd8f3b`): the typed address the receiving tree read over the chart
//! (`Sections`, each tick's letter bundled with its part's slots, the channel alone or with the
//! kind, read once at the section letter; `SectionSlots::Cells`, the whole-stream control). The
//! chart stays: the exterior reads the curated cuts on it (the notebook's `exterior.rs`).
//!
//! [definition] The computational object is the helical pair interaction, read here as a curated
//! passage's chart. Of the winding guide's six general objects this owner touches **faces and
//! placement** (the ports: a section letter's channel) and the **tower thread** (sections restrict
//! the passage: a part is the span between two letters); the helix, pair, cell holonomy and tube
//! stay attached through the owners that read the chart.

use super::{ContextError, shape};

/// [definition] **A section letter's reading**: the kind of section it opens and its channel.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Section {
    pub kind: usize,
    pub channel: usize,
}

/// [definition; agent-inferred] **The section chart** (module header): `bytes` exterior cells, then
/// `kinds · channels` section letters `bytes + channels · kind + channel`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SectionChart {
    bytes: usize,
    channels: usize,
    kinds: usize,
}

impl SectionChart {
    /// **Declare the chart**, refused at fewer than two exterior cells, two channels (a channel slot
    /// of one letter carries nothing) or one kind, and past 31 bits.
    pub fn new(bytes: usize, channels: usize, kinds: usize) -> Result<Self, ContextError> {
        if bytes < 2 || channels < 2 || kinds < 1 {
            return Err(shape(
                "a section chart of at least two cells, two channels and one kind",
                2,
                bytes.min(channels).min(kinds),
            ));
        }
        let letters = channels
            .checked_mul(kinds)
            .and_then(|letters| letters.checked_add(bytes))
            .filter(|&alphabet| alphabet < u32::MAX as usize / 2);
        if letters.is_none() {
            return Err(shape(
                "a section chart within 31 bits",
                u32::MAX as usize / 2,
                usize::MAX,
            ));
        }
        Ok(Self {
            bytes,
            channels,
            kinds,
        })
    }

    /// The curated source's chart: the 256 bytes, the human, agent and tool channels and the kinds
    /// `open`, `switch`, `turn`, `part` (`|A| = 268`).
    pub fn curated() -> Self {
        Self {
            bytes: 256,
            channels: 3,
            kinds: 4,
        }
    }

    /// The exterior cells.
    pub fn bytes(&self) -> usize {
        self.bytes
    }

    /// The channels (ports).
    pub fn channels(&self) -> usize {
        self.channels
    }

    /// The section kinds.
    pub fn kinds(&self) -> usize {
        self.kinds
    }

    /// `|A| = bytes + channels · kinds`.
    pub fn alphabet(&self) -> usize {
        self.bytes + self.channels * self.kinds
    }

    /// The section letters, `channels · kinds`.
    pub fn letters(&self) -> usize {
        self.channels * self.kinds
    }

    /// **A cell's section**, or none for an exterior cell (and for a cell outside the chart).
    pub fn section(&self, cell: usize) -> Option<Section> {
        (self.bytes..self.alphabet())
            .contains(&cell)
            .then(|| Section {
                kind: (cell - self.bytes) / self.channels,
                channel: (cell - self.bytes) % self.channels,
            })
    }

    /// **The letter of a section**, `bytes + channels · kind + channel`; refused outside the chart.
    pub fn letter(&self, section: Section) -> Result<usize, ContextError> {
        if section.kind >= self.kinds || section.channel >= self.channels {
            return Err(shape(
                "a section within the declared kinds and channels",
                self.letters(),
                self.channels * section.kind + section.channel,
            ));
        }
        Ok(self.bytes + self.channels * section.kind + section.channel)
    }
}
