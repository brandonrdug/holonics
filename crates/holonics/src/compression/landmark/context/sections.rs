//! **The section chart and the typed address it reads: a channel slot read once at its section**
//! (campaign 5's curated source under HNN_FORMULA's source contract, items 1–3; #73, #148).
//!
//! [definition; agent-inferred] **The chart** ([`SectionChart`]): a stream whose cells are the
//! exterior chart's `B` cells (the UTF-8 bytes of a part, `B = 256`) followed by the **section
//! letters**, one per `(kind, channel)`, coded `B + C·k + c` for kind `k < K` and channel `c < C`
//! (the curated source's `open`, `switch`, `turn`, `part` on the human, agent and tool ports:
//! `|A| = 256 + 12`). A part opens with its one letter, so the channel a cell lies on is never
//! supplied: it is read from the coded past, at the part's section.
//!
//! [definition; agent-inferred] **The typed address** ([`Sections`]): each tick's letter is its cell
//! bundled with the declared slots of the part it lies in (a section letter's own part: the one it
//! opens), `Bundle { cell, features }` over the family [`SectionSlots::family`] declares: the
//! channel alone (`[C]`), or the channel and the kind (`[C, K]`, the typed reader of September 27).
//! The slot is read **once**, at the section letter, and carried by every bundle of its part; the
//! address of cell `j` is the preceding `D` bundles, newest first (`letter_address`), so it is causal.
//! The reader refuses a cell outside the chart and a byte before any section letter (a cut opens at
//! a letter: the codec's pin), before anything moves.
//!
//! [definition] The computational object is the helical pair interaction, read here as the receiving
//! tree's address over a curated passage. Of the winding guide's six general objects this owner
//! touches **faces and placement** (the ports: a cell's channel placed on its bundle) and the **tower
//! thread** (sections restrict the passage: a part is the span between two letters); the helix, pair,
//! cell holonomy and tube stay attached through the tree's owner.

use super::{Bundle, ContextError, Letter, LetterFamily, shape};

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

/// [definition; agent-inferred] **The slots a typed address carries** (module header): the
/// channel alone, or the channel and the kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SectionSlots {
    Channel,
    ChannelKind,
}

impl SectionSlots {
    /// **The declared letter family** of the slots over a chart: `[C]` or `[C, K]`. Refused where a
    /// slot would hold one letter (a chart of one kind carries no kind slot).
    pub fn family(self, chart: &SectionChart) -> Result<LetterFamily, ContextError> {
        match self {
            SectionSlots::Channel => LetterFamily::new(vec![chart.channels as u64]),
            SectionSlots::ChannelKind => {
                LetterFamily::new(vec![chart.channels as u64, chart.kinds as u64])
            }
        }
    }

    /// The slots' values of a section.
    fn values(self, section: Section) -> Vec<u64> {
        match self {
            SectionSlots::Channel => vec![section.channel as u64],
            SectionSlots::ChannelKind => vec![section.channel as u64, section.kind as u64],
        }
    }
}

/// [definition; agent-inferred] **The typed address's reader** (module header): the chart, the
/// declared slots and their family, and the open section, read once at its letter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sections {
    chart: SectionChart,
    slots: SectionSlots,
    family: LetterFamily,
    open: Option<Section>,
}

impl Sections {
    /// The reader over a chart with the declared slots, no section open yet.
    pub fn new(chart: SectionChart, slots: SectionSlots) -> Result<Self, ContextError> {
        Ok(Self {
            family: slots.family(&chart)?,
            chart,
            slots,
            open: None,
        })
    }

    /// The chart.
    pub fn chart(&self) -> &SectionChart {
        &self.chart
    }

    /// The declared slots.
    pub fn slots(&self) -> SectionSlots {
        self.slots
    }

    /// The slots' letter family (the tree's declared family).
    pub fn family(&self) -> &LetterFamily {
        &self.family
    }

    /// The open section: the part the next byte lies in.
    pub fn open(&self) -> Option<Section> {
        self.open
    }

    /// Restore the contemporary open part from a durable standing. The section is checked against
    /// this reader's immutable chart before the state changes.
    pub(crate) fn restore_open(&mut self, open: Option<Section>) -> Result<(), ContextError> {
        if let Some(section) = open {
            self.chart.letter(section)?;
        }
        self.open = open;
        Ok(())
    }

    /// **The letter a cell would read**, nothing moved: the cell bundled with its part's slots
    /// (a section letter's own). Refused outside the chart and at a byte before any section.
    pub fn letter_of(&self, cell: usize) -> Result<Letter, ContextError> {
        let alphabet = self.chart.alphabet();
        if cell >= alphabet {
            return Err(ContextError::CellOutside {
                code: cell,
                alphabet,
            });
        }
        let section = self
            .chart
            .section(cell)
            .or(self.open)
            .ok_or_else(|| shape("a section letter before the first byte", 1, 0))?;
        Ok(Letter::Bundle(Bundle {
            cell,
            features: self.family.encode(&self.slots.values(section))?,
        }))
    }

    /// **Read one tick** (module header): its letter ([`Self::letter_of`]), and a section letter
    /// opens its part. Refused, with nothing moved, where `letter_of` refuses.
    pub fn read(&mut self, cell: usize) -> Result<Letter, ContextError> {
        let letter = self.letter_of(cell)?;
        if let Some(section) = self.chart.section(cell) {
            self.open = Some(section);
        }
        Ok(letter)
    }
}
