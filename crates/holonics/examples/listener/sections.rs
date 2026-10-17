//! **The section boundary of the one continuing listener**: the exterior
//! contract between the dataset readers and the driver, the octet chart into the receiver's
//! classes, and the framed reader.
//!
//! Every item of every dataset is one [`Section`]: source passages through boundary charts, then one
//! declared target span. Dataset, split and role are exterior codec information and
//! never reach the field.
//!
//! [definition; agent-inferred, October 16] **The octet chart.** An octet `b` enters as two cells,
//! `b = 16q + r`, quotient `q = ⌊b/16⌋` then remainder `r = b mod 16`, as the MNIST digit chart places an
//! intensity. Each cell's class is `16·place + digit` over [`PLACES`] places: with two places the
//! receiver's 32 classes carry the digit's place in its octet (the quotient digit `0..16`, the remainder digit
//! `16..32`); with one place the 16 classes leave it to the receiver's context. The end letter
//! ([`end_cells`]) is written by the driver after every passage and every target, never by a reader.
//! - Why the class carries the place: a chart that packs one exterior symbol into `P` cells owes
//!   the receiver its place, a clock of period `P`. Under one place the receiver's tree is
//!   addressed by the last cells' classes alone, and no ring of the field's odd periods resolves a
//!   cell's parity (an odometer phase read at grain `g` gives blocks of the period, not residues),
//!   so a release slips the octet boundary: the first four-section release slipped it 22 times.
//!   MNIST's serial chart already carries its coordinate; this is the same law for the octet.
//!   Measured against one place on the same field in condition B (October 16): GSM8K learning
//!   section 0 codes `[664,665]` bits against `[674,675]`, section 1 `[558,559]` against
//!   `[582,583]`, and development section 1, read frozen (no deposit) after one learned section `[762,763]` against
//!   `[800,801]`, at about three times the cost per cell (32 classes, located `n* = 23803`
//!   against `5100`).
//! - Why base-16 digits and not the 256 octets plus an end letter of the initial design: the
//!   observation's pairing is a fixed-point-free involution over every boundary class
//!   (`PairedObservation::admit` refuses a pairing that leaves a class uncovered), so the class count
//!   is even, and `257` is refused by the pairing law itself. `256 + 2` would admit, but each
//!   comparison would then score 258 classes against 32.
//! - Why the end letter is two quotient-place zero cells: a general octet codec owes an end that no
//!   octet can write. With the place in the class, a quotient-place cell followed by another is no
//!   octet, so `(0, 0)` closes a passage while `0x00`, MNIST's background, stays the octet
//!   `(0, 16)`, and nothing is refused. Under one place the end letter falls back to the octet
//!   `0x00`'s cells: no GSM8K train octet is `0x00` (counted over the whole train file), a text
//!   passage or target that carries one is refused by name ([`SectionError::EndLetterInPassage`]),
//!   and a raster's extent is its declared `width · height`. The end letter is coded and released
//!   as the other cells are.
//! - What stays one class across modalities: MNIST's label `7` as its numeral octet `0x37` and the
//!   `7` of a GSM8K answer are the same cells. That is a fact of the receiver, not transfer;
//!   transfer is only what a sibling difference measures (stage B).
//! - A release is read back by [`pieces_of`]: every cell that does not begin an octet at its place
//!   is kept and shown as a slip, never dropped.
//!
//! **The framed file** (`HLSN1`, read by [`read_frames`]): the six bytes `HLSN1\n`, then per section
//! a big-endian `u32` passage count; per passage a kind byte (`0` octets, `1` raster, `2` PCM) and its
//! payload (octets: `u32` length and the bytes; raster: `u16` width, `u16` height and the row-major
//! intensities; PCM: `u32` rate, `u32` count and the big-endian `i16` samples); then the target's
//! `u32` length and its octets. A release section carries an empty target.

use std::fmt;

/// One item: source passages through their boundary charts, then one target span.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Section {
    pub passages: Vec<Passage>,
    /// Octets only. The driver appends the receiver's end letter; readers never write it.
    pub target: Vec<u8>,
}

/// One source passage, as its dataset gives it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Passage {
    /// Text: a GSM8K question, the complete original octets, annotations included.
    Octets(Vec<u8>),
    /// MNIST: row-major intensities, exactly as the file gives them.
    Raster {
        width: u16,
        height: u16,
        intensities: Vec<u8>,
    },
    /// LibriSpeech: integer PCM at its rate, the amplitude `s·2^(−15)`.
    Pcm { rate: u32, samples: Vec<i16> },
}

/// The base-16 digits of an octet's two cells.
pub const DIGITS: usize = 16;
/// The places of a digit in its octet that its class carries: `2` bears the place (the class is
/// `16·place + digit`), `1` leaves it to the receiver's context.
pub const PLACES: usize = 2;
/// The receiver's classes: each digit at each place its class bears.
pub const CLASSES: usize = DIGITS * PLACES;
/// The first class of the remainder digit's place.
const REMAINDER: usize = DIGITS * (PLACES - 1);
/// The octet whose cells are the end letter under one place.
pub const END: u8 = 0x00;

/// A refusal at the section boundary.
#[derive(Debug, PartialEq, Eq)]
pub enum SectionError {
    /// The framed file does not begin with `HLSN1\n`.
    Magic,
    /// The file ended inside a field.
    Truncated { at: usize, wanted: &'static str },
    /// A passage kind byte that names no passage.
    Kind { at: usize, kind: u8 },
    /// A raster whose intensities are not `width · height`.
    Raster {
        width: u16,
        height: u16,
        found: usize,
    },
    /// A passage or target carries the end letter's octet.
    EndLetterInPassage { section: usize, at: usize },
    /// PCM enters through the matched wave port, whose join into the source moments is owed (L4).
    PcmUnjoined { section: usize },
}

impl fmt::Display for SectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

impl std::error::Error for SectionError {}

/// The two cells of one octet, the quotient digit first.
pub fn cells_of(octet: u8) -> [usize; 2] {
    [
        usize::from(octet >> 4),
        REMAINDER + usize::from(octet & 0x0f),
    ]
}

/// The octet of two cells, the quotient digit first.
pub fn octet_of(quotient: usize, remainder: usize) -> Option<u8> {
    (quotient < DIGITS && (REMAINDER..REMAINDER + DIGITS).contains(&remainder))
        .then(|| ((quotient << 4) | (remainder - REMAINDER)) as u8)
}

/// The end letter's two cells. With the place in the class they are two quotient-place zero digits,
/// a pair no octet writes, so every octet, `0x00` included, stays an octet. With one place they are
/// the octet [`END`]'s cells, and a text passage or a target that carries it is refused.
pub fn end_cells() -> [usize; 2] {
    if PLACES > 1 { [0, 0] } else { cells_of(END) }
}

/// One piece of a released cell run read back on the octet chart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Piece {
    /// A quotient-place cell followed by a remainder-place cell.
    Octet(u8),
    /// The end letter.
    End,
    /// A cell that does not begin an octet at its place: a remainder digit where a quotient one was owed,
    /// or a quotient digit followed by another quotient digit. It is shown, never dropped.
    Slip(usize),
}

/// Reads a released cell run back on the octet chart, pairing a quotient-place cell with the remainder-place
/// cell after it and keeping every other cell as a [`Piece::Slip`]. Under one place every class
/// fits either place, so the run pairs by position and only an odd last cell slips.
pub fn pieces_of(cells: &[usize]) -> Vec<Piece> {
    let mut pieces = Vec::with_capacity(cells.len() / 2 + 1);
    let mut at = 0;
    while at < cells.len() {
        if cells[at..].starts_with(&end_cells()) {
            pieces.push(Piece::End);
            at += 2;
            continue;
        }
        match cells.get(at + 1).and_then(|&low| octet_of(cells[at], low)) {
            Some(octet) => {
                pieces.push(Piece::Octet(octet));
                at += 2;
            }
            None => {
                pieces.push(Piece::Slip(cells[at]));
                at += 1;
            }
        }
    }
    pieces
}

/// Whether a released run has just closed with the end letter. With the place in the class the
/// two cells close it wherever they fall; with one place the octet boundary is the run's parity.
pub fn closes(cells: &[usize]) -> bool {
    cells.ends_with(&end_cells()) && (PLACES > 1 || cells.len() % 2 == 0)
}

/// The cells of an octet run followed by the end letter.
pub fn closed_cells(octets: &[u8]) -> Vec<usize> {
    let mut cells = Vec::with_capacity(2 * octets.len() + 2);
    for &octet in octets {
        cells.extend(cells_of(octet));
    }
    cells.extend(end_cells());
    cells
}

impl Section {
    /// The source cells: every passage on the octet chart, each closed by the end letter. A raster
    /// enters as its intensities, row-major, on the same chart; PCM is refused until its join lands.
    pub fn source_cells(&self, section: usize) -> Result<Vec<usize>, SectionError> {
        let mut cells = Vec::new();
        for passage in &self.passages {
            let octets = match passage {
                Passage::Octets(octets) => octets,
                Passage::Raster { intensities, .. } => intensities,
                Passage::Pcm { .. } => return Err(SectionError::PcmUnjoined { section }),
            };
            if let Some(at) = octets.iter().position(|&octet| PLACES == 1 && octet == END) {
                if matches!(passage, Passage::Octets(_)) {
                    return Err(SectionError::EndLetterInPassage { section, at });
                }
            }
            cells.extend(closed_cells(octets));
        }
        Ok(cells)
    }

    /// The target cells, closed by the end letter; none for a release section.
    pub fn target_cells(&self, section: usize) -> Result<Vec<usize>, SectionError> {
        if self.target.is_empty() {
            return Ok(Vec::new());
        }
        if let Some(at) = self
            .target
            .iter()
            .position(|&octet| PLACES == 1 && octet == END)
        {
            return Err(SectionError::EndLetterInPassage { section, at });
        }
        Ok(closed_cells(&self.target))
    }
}

struct Reader<'b> {
    bytes: &'b [u8],
    at: usize,
}

impl<'b> Reader<'b> {
    fn take(&mut self, n: usize, wanted: &'static str) -> Result<&'b [u8], SectionError> {
        let end = self
            .at
            .checked_add(n)
            .filter(|&end| end <= self.bytes.len())
            .ok_or(SectionError::Truncated {
                at: self.at,
                wanted,
            })?;
        let part = &self.bytes[self.at..end];
        self.at = end;
        Ok(part)
    }

    fn u16(&mut self, wanted: &'static str) -> Result<u16, SectionError> {
        let b = self.take(2, wanted)?;
        Ok(u16::from_be_bytes([b[0], b[1]]))
    }

    fn u32(&mut self, wanted: &'static str) -> Result<u32, SectionError> {
        let b = self.take(4, wanted)?;
        Ok(u32::from_be_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn octets(&mut self, wanted: &'static str) -> Result<Vec<u8>, SectionError> {
        let n = self.u32(wanted)? as usize;
        Ok(self.take(n, wanted)?.to_vec())
    }
}

/// Read every section of a framed `HLSN1` file.
pub fn read_frames(bytes: &[u8]) -> Result<Vec<Section>, SectionError> {
    let mut reader = Reader { bytes, at: 0 };
    if reader.take(6, "magic").map_err(|_| SectionError::Magic)? != b"HLSN1\n" {
        return Err(SectionError::Magic);
    }
    let mut sections = Vec::new();
    while reader.at < bytes.len() {
        let count = reader.u32("passage count")?;
        let mut passages = Vec::new();
        for _ in 0..count {
            let at = reader.at;
            let kind = reader.take(1, "passage kind")?[0];
            passages.push(match kind {
                0 => Passage::Octets(reader.octets("octets")?),
                1 => {
                    let width = reader.u16("raster width")?;
                    let height = reader.u16("raster height")?;
                    let n = usize::from(width) * usize::from(height);
                    let intensities = reader.take(n, "intensities")?.to_vec();
                    if intensities.len() != n {
                        return Err(SectionError::Raster {
                            width,
                            height,
                            found: intensities.len(),
                        });
                    }
                    Passage::Raster {
                        width,
                        height,
                        intensities,
                    }
                }
                2 => {
                    let rate = reader.u32("pcm rate")?;
                    let n = reader.u32("pcm count")? as usize;
                    let samples = reader
                        .take(2 * n, "pcm samples")?
                        .chunks_exact(2)
                        .map(|b| i16::from_be_bytes([b[0], b[1]]))
                        .collect();
                    Passage::Pcm { rate, samples }
                }
                kind => return Err(SectionError::Kind { at, kind }),
            });
        }
        let target = reader.octets("target")?;
        sections.push(Section { passages, target });
    }
    Ok(sections)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_corrupt_passage_count_returns_truncated_without_reserving_it() {
        let mut bytes = b"HLSN1\n".to_vec();
        bytes.extend(u32::MAX.to_be_bytes());
        assert_eq!(
            read_frames(&bytes),
            Err(SectionError::Truncated {
                at: 10,
                wanted: "passage kind"
            })
        );
    }

    /// `pieces_of(closed_cells(b)) = b ⟨end⟩` for every octet run, `0x00` included under two places.
    #[test]
    fn the_chart_reads_back_every_octet_and_its_end() {
        let octets: Vec<u8> = (0..=255u8)
            .filter(|&octet| PLACES > 1 || octet != END)
            .collect();
        let mut expected: Vec<Piece> = octets.iter().map(|&octet| Piece::Octet(octet)).collect();
        expected.push(Piece::End);
        let cells = closed_cells(&octets);
        assert_eq!(pieces_of(&cells), expected);
        assert!(closes(&cells));
    }

    /// A cell out of its place is kept as a slip, and the octets on either side still read.
    #[test]
    fn a_cell_out_of_place_is_shown_as_a_slip() {
        let mut cells = cells_of(b'A').to_vec();
        cells.push(cells_of(b'B')[1]);
        cells.extend(cells_of(b'C'));
        let read = pieces_of(&cells);
        if PLACES > 1 {
            assert_eq!(
                read,
                vec![
                    Piece::Octet(b'A'),
                    Piece::Slip(cells[2]),
                    Piece::Octet(b'C')
                ]
            );
        } else {
            assert_eq!(read.len(), 3);
            assert_eq!(read[0], Piece::Octet(b'A'));
        }
    }
}
