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

#[path = "sections/sha256.rs"]
mod sha256;
pub(crate) use sha256::{Sha256, sha256};

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

/// Exterior chart identity, used only for receiving/reporting a section on its own scale.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ChartKind {
    Octets,
    Raster,
    Pcm,
}

impl ChartKind {
    pub fn byte(self) -> u8 {
        match self {
            Self::Octets => 0,
            Self::Raster => 1,
            Self::Pcm => 2,
        }
    }
}

/// Compact canonical chart identity. Hashes are exterior checks, not learner operands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChartSummary {
    pub kind: ChartKind,
    pub chart_octets: usize,
    pub chart_sha256: String,
    pub fibre_bytes: u128,
    pub fibre_sha256: String,
}

impl fmt::Display for ChartSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "kind={:?} chart_octets={} chart_sha256={} fibre_bytes={} fibre_sha256={} canonical_format=listener-fibre-v1",
            self.kind, self.chart_octets, self.chart_sha256, self.fibre_bytes, self.fibre_sha256
        )
    }
}

/// The frame and the intensity remainders, in the stroke's pixel order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StrokeFibre {
    pub width: u16,
    pub height: u16,
    /// Includes the initial pen-up jump from the origin.
    pub jumps: usize,
    pub remainders: Vec<u8>,
}

/// Exact residuals of the samples from the signed peak of one half-cycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HalfCycleFibre {
    pub peak_remainder: u16,
    /// `sample = signed_peak + samples_from_peak[i]`, including the peak itself.
    pub samples_from_peak: Vec<i32>,
}

/// The recording's frame and every run's exact reconstruction fibre.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PcmFibre {
    pub rate: u32,
    pub runs: Vec<HalfCycleFibre>,
}

/// Boundary reconstruction information, never learner material or a pending-comparison archive.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChartFibre {
    Octets,
    Stroke(StrokeFibre),
    HalfCycles(PcmFibre),
}

/// A passage's chart octets beside their exact frame/fibre. `decode(encode(p)) = p`.
///
/// [agent-inferred, REQ-20261018-064] The eighth-turn convention is clockwise in a raster's
/// row-down frame: east, southeast, south, southwest, west, northwest, north, northeast.
/// End letters belong to passage framing, not this chart: at a PCM sign-change cut,
/// `chart(a ++ b).octets = chart(a).octets ++ chart(b).octets`. Each separately framed passage
/// still receives its own end letter through [`Self::cells`]. The native matched-wave join
/// (L4) remains owed; these are lossless exterior codecs, not that physical port.
/// The computational object remains the helical pair interaction. This boundary touches faces
/// and placement, and the tube's cross-section charts; helix/carry, pair, cell holonomy and the
/// compatible tower thread stay attached through the continuing listener's existing owners.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassageChart {
    pub kind: ChartKind,
    pub octets: Vec<u8>,
    pub fibre: ChartFibre,
}

impl PassageChart {
    /// Canonical v1 fibre bytes: domain `holonics.listener.fibre.v1\0`, then kind byte.
    /// Octets have no payload. Raster carries width/height (u16 BE), jump/remainder counts
    /// (u64 BE), then the u8 remainders. PCM carries rate (u32 BE), run count (u64 BE), then
    /// each peak remainder (u16 BE), sample count (u64 BE), and sample residuals (i32 BE).
    /// Lengths refer to the full canonical bytes, including the domain and kind.
    pub fn write_canonical_fibre(&self, mut write: impl FnMut(&[u8])) {
        write(b"holonics.listener.fibre.v1\0");
        write(&[self.kind.byte()]);
        match &self.fibre {
            ChartFibre::Octets => {}
            ChartFibre::Stroke(fibre) => {
                write(&fibre.width.to_be_bytes());
                write(&fibre.height.to_be_bytes());
                write(&(fibre.jumps as u64).to_be_bytes());
                write(&(fibre.remainders.len() as u64).to_be_bytes());
                write(&fibre.remainders);
            }
            ChartFibre::HalfCycles(fibre) => {
                write(&fibre.rate.to_be_bytes());
                write(&(fibre.runs.len() as u64).to_be_bytes());
                for run in &fibre.runs {
                    write(&run.peak_remainder.to_be_bytes());
                    write(&(run.samples_from_peak.len() as u64).to_be_bytes());
                    for sample in &run.samples_from_peak {
                        write(&sample.to_be_bytes());
                    }
                }
            }
        }
    }

    pub fn summary(&self) -> ChartSummary {
        let mut digest = Sha256::new();
        self.write_canonical_fibre(|bytes| digest.update(bytes));
        let fibre_bytes = digest.bytes;
        ChartSummary {
            kind: self.kind,
            chart_octets: self.octets.len(),
            chart_sha256: sha256(&self.octets),
            fibre_bytes,
            fibre_sha256: digest.finish(),
        }
    }

    /// The chart's cells with exactly one passage end letter.
    pub fn cells(&self) -> Vec<usize> {
        closed_cells(&self.octets)
    }

    /// Reconstruct the complete passage and refuse a malformed or noncanonical chart/fibre.
    pub fn decode(&self) -> Result<Passage, SectionError> {
        let passage = match (&self.kind, &self.fibre) {
            (ChartKind::Octets, ChartFibre::Octets) => Passage::Octets(self.octets.clone()),
            (ChartKind::Raster, ChartFibre::Stroke(fibre)) => decode_stroke(&self.octets, fibre)?,
            (ChartKind::Pcm, ChartFibre::HalfCycles(fibre)) => {
                decode_half_cycles(&self.octets, fibre)?
            }
            _ => {
                return Err(SectionError::Chart {
                    at: 0,
                    reason: "chart kind and fibre differ",
                });
            }
        };
        if passage.encode_chart()? != *self {
            return Err(SectionError::Chart {
                at: 0,
                reason: "noncanonical chart or fibre",
            });
        }
        Ok(passage)
    }
}

impl Passage {
    pub fn chart_kind(&self) -> ChartKind {
        match self {
            Self::Octets(_) => ChartKind::Octets,
            Self::Raster { .. } => ChartKind::Raster,
            Self::Pcm { .. } => ChartKind::Pcm,
        }
    }

    /// Lossless boundary encoding. Width/height and sample clock remain in the exact fibre.
    pub fn encode_chart(&self) -> Result<PassageChart, SectionError> {
        match self {
            Self::Octets(octets) => Ok(PassageChart {
                kind: ChartKind::Octets,
                octets: octets.clone(),
                fibre: ChartFibre::Octets,
            }),
            Self::Raster {
                width,
                height,
                intensities,
            } => encode_stroke(*width, *height, intensities),
            Self::Pcm { rate, samples } => Ok(encode_half_cycles(*rate, samples)),
        }
    }
}

const DIRECTIONS: [(i32, i32); 8] = [
    (0, 1),
    (1, 1),
    (1, 0),
    (1, -1),
    (0, -1),
    (-1, -1),
    (-1, 0),
    (-1, 1),
];
const TURNS: [usize; 8] = [0, 1, 7, 2, 6, 3, 5, 4];

fn encode_stroke(
    width: u16,
    height: u16,
    intensities: &[u8],
) -> Result<PassageChart, SectionError> {
    let count = usize::from(width) * usize::from(height);
    if intensities.len() != count {
        return Err(SectionError::Raster {
            width,
            height,
            found: intensities.len(),
        });
    }
    let mut visited = vec![false; count];
    let mut octets = Vec::new();
    let mut remainders = Vec::new();
    let (mut row, mut col, mut heading, mut next, mut jumps) = (0i32, 0i32, 0usize, 0usize, 0usize);
    let mut pen_down = false;
    loop {
        let neighbour = pen_down
            .then(|| {
                TURNS.iter().find_map(|&turn| {
                    let direction = (heading + turn) % 8;
                    let (dr, dc) = DIRECTIONS[direction];
                    let (r, c) = (row + dr, col + dc);
                    if r < 0 || c < 0 || r >= i32::from(height) || c >= i32::from(width) {
                        return None;
                    }
                    let index = r as usize * usize::from(width) + c as usize;
                    (!visited[index] && intensities[index] != 0)
                        .then_some((index, r, c, turn, direction))
                })
            })
            .flatten();
        let (index, r, c, turn, direction) = if let Some(found) = neighbour {
            found
        } else {
            while next < count && (visited[next] || intensities[next] == 0) {
                next += 1;
            }
            if next == count {
                break;
            }
            let (r, c) = (
                (next / usize::from(width)) as i32,
                (next % usize::from(width)) as i32,
            );
            (next, r, c, 8, 0)
        };
        let value = intensities[index];
        let octave = value.ilog2() as u8;
        octets.push(((turn as u8) << 4) | octave);
        if turn == 8 {
            let (dr, dc) = (r - row, c - col);
            let dr = i8::try_from(dr).map_err(|_| SectionError::StrokeOffset {
                row: r - row,
                column: c - col,
            })?;
            let dc = i8::try_from(dc).map_err(|_| SectionError::StrokeOffset {
                row: r - row,
                column: c - col,
            })?;
            octets.extend([dr.to_be_bytes()[0], dc.to_be_bytes()[0]]);
            jumps += 1;
        }
        remainders.push(value - (1u8 << octave));
        visited[index] = true;
        (row, col, heading, pen_down) = (r, c, direction, true);
    }
    Ok(PassageChart {
        kind: ChartKind::Raster,
        octets,
        fibre: ChartFibre::Stroke(StrokeFibre {
            width,
            height,
            jumps,
            remainders,
        }),
    })
}

fn decode_stroke(octets: &[u8], fibre: &StrokeFibre) -> Result<Passage, SectionError> {
    let count = usize::from(fibre.width) * usize::from(fibre.height);
    let mut intensities = vec![0u8; count];
    let (mut row, mut col, mut heading, mut at, mut pixel) = (0i32, 0i32, 0usize, 0usize, 0usize);
    while at < octets.len() {
        let start = at;
        let (turn, octave) = (usize::from(octets[at] >> 4), octets[at] & 15);
        at += 1;
        if turn > 8 || octave > 7 || (pixel == 0 && turn != 8) {
            return Err(SectionError::Chart {
                at: start,
                reason: "invalid stroke pixel",
            });
        }
        if turn == 8 {
            let offsets = octets.get(at..at + 2).ok_or(SectionError::Chart {
                at,
                reason: "truncated stroke jump",
            })?;
            row += i32::from(i8::from_be_bytes([offsets[0]]));
            col += i32::from(i8::from_be_bytes([offsets[1]]));
            heading = 0;
            at += 2;
        } else {
            heading = (heading + turn) % 8;
            row += DIRECTIONS[heading].0;
            col += DIRECTIONS[heading].1;
        }
        if row < 0 || col < 0 || row >= i32::from(fibre.height) || col >= i32::from(fibre.width) {
            return Err(SectionError::Chart {
                at: start,
                reason: "stroke pixel outside frame",
            });
        }
        let index = row as usize * usize::from(fibre.width) + col as usize;
        let remainder = *fibre.remainders.get(pixel).ok_or(SectionError::Chart {
            at: start,
            reason: "missing intensity fibre",
        })?;
        if intensities[index] != 0 || u16::from(remainder) >= (1u16 << octave) {
            return Err(SectionError::Chart {
                at: start,
                reason: "revisited pixel or invalid intensity fibre",
            });
        }
        intensities[index] = (1u8 << octave) + remainder;
        pixel += 1;
    }
    if pixel != fibre.remainders.len() {
        return Err(SectionError::Chart {
            at,
            reason: "excess intensity fibre",
        });
    }
    Ok(Passage::Raster {
        width: fibre.width,
        height: fibre.height,
        intensities,
    })
}

fn sample_sign(sample: i16) -> u8 {
    if sample > 0 {
        0
    } else if sample < 0 {
        1
    } else {
        2
    }
}

fn encode_half_cycles(rate: u32, samples: &[i16]) -> PassageChart {
    let mut octets = Vec::new();
    let mut runs = Vec::new();
    let mut at = 0;
    while at < samples.len() {
        let sign = sample_sign(samples[at]);
        let mut end = at + 1;
        while end < samples.len()
            && (sample_sign(samples[end]) == sign || (sign != 2 && samples[end] == 0))
        {
            end += 1;
        }
        let peak = samples[at..end]
            .iter()
            .map(|&sample| i32::from(sample).unsigned_abs())
            .max()
            .unwrap_or(0);
        let octave = if peak == 0 { 0 } else { peak.ilog2() as u8 };
        let peak_remainder = if peak == 0 {
            0
        } else {
            (peak - (1u32 << octave)) as u16
        };
        let signed_peak = if sign == 1 {
            -(peak as i32)
        } else {
            peak as i32
        };
        let length = end - at;
        octets.extend(std::iter::repeat_n(255, length / 255));
        octets.push((length % 255) as u8);
        octets.push((sign << 4) | octave);
        runs.push(HalfCycleFibre {
            peak_remainder,
            samples_from_peak: samples[at..end]
                .iter()
                .map(|&sample| i32::from(sample) - signed_peak)
                .collect(),
        });
        at = end;
    }
    PassageChart {
        kind: ChartKind::Pcm,
        octets,
        fibre: ChartFibre::HalfCycles(PcmFibre { rate, runs }),
    }
}

fn decode_half_cycles(octets: &[u8], fibre: &PcmFibre) -> Result<Passage, SectionError> {
    let mut samples = Vec::new();
    let (mut at, mut run_index) = (0usize, 0usize);
    while at < octets.len() {
        let start = at;
        let mut length = 0usize;
        loop {
            let part = *octets.get(at).ok_or(SectionError::Chart {
                at,
                reason: "unterminated PCM length",
            })?;
            at += 1;
            length = length
                .checked_add(usize::from(part))
                .ok_or(SectionError::Chart {
                    at,
                    reason: "PCM length overflow",
                })?;
            if part != 255 {
                break;
            }
        }
        let tag = *octets.get(at).ok_or(SectionError::Chart {
            at,
            reason: "missing PCM peak",
        })?;
        at += 1;
        let (sign, octave) = (tag >> 4, tag & 15);
        let run = fibre.runs.get(run_index).ok_or(SectionError::Chart {
            at: start,
            reason: "missing PCM fibre",
        })?;
        if length == 0
            || length != run.samples_from_peak.len()
            || sign > 2
            || (sign == 2 && (octave != 0 || run.peak_remainder != 0))
            || u32::from(run.peak_remainder) >= (1u32 << octave)
        {
            return Err(SectionError::Chart {
                at: start,
                reason: "invalid PCM run or peak fibre",
            });
        }
        let magnitude = if sign == 2 {
            0
        } else {
            (1i32 << octave) + i32::from(run.peak_remainder)
        };
        let peak = if sign == 1 { -magnitude } else { magnitude };
        for &offset in &run.samples_from_peak {
            let sample = peak
                .checked_add(offset)
                .and_then(|sample| i16::try_from(sample).ok())
                .ok_or(SectionError::Chart {
                    at: start,
                    reason: "PCM sample outside i16",
                })?;
            samples.push(sample);
        }
        run_index += 1;
    }
    if run_index != fibre.runs.len() {
        return Err(SectionError::Chart {
            at,
            reason: "excess PCM fibre",
        });
    }
    Ok(Passage::Pcm {
        rate: fibre.rate,
        samples,
    })
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
    /// A declared wire extent does not fit the host's checked address space.
    Extent { at: usize, wanted: &'static str },
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
    /// A signed octet cannot carry this pen-up displacement.
    StrokeOffset { row: i32, column: i32 },
    /// A malformed boundary chart or reconstruction fibre.
    Chart { at: usize, reason: &'static str },
    /// No source passage identifies this section's release chart.
    EmptyPassages,
    /// One release has no single chart when its source passages differ.
    MixedCharts { first: ChartKind, found: ChartKind },
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
    /// A release's exterior chart is defined by homogeneous, nonempty source passages, never by
    /// the target's bytes. Empty or mixed sections have no such chart and are refused.
    pub fn chart_kind(&self) -> Result<ChartKind, SectionError> {
        let first = self
            .passages
            .first()
            .ok_or(SectionError::EmptyPassages)?
            .chart_kind();
        for passage in &self.passages[1..] {
            let found = passage.chart_kind();
            if first != found {
                return Err(SectionError::MixedCharts { first, found });
            }
        }
        Ok(first)
    }

    /// Every passage enters through its own lossless chart, each closed by one end letter.
    /// The raw passage and exact fibre stay exterior; no fibre is silently discarded by the codec.
    pub fn source_cells(&self, section: usize) -> Result<Vec<usize>, SectionError> {
        let mut cells = Vec::new();
        for passage in &self.passages {
            let chart = passage.encode_chart()?;
            if let Some(at) = chart
                .octets
                .iter()
                .position(|&octet| PLACES == 1 && octet == END)
            {
                if matches!(passage, Passage::Octets(_)) {
                    return Err(SectionError::EndLetterInPassage { section, at });
                }
            }
            cells.extend(chart.cells());
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
        let n = usize::try_from(self.u32(wanted)?).map_err(|_| SectionError::Extent {
            at: self.at,
            wanted,
        })?;
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
                    let n = usize::from(width).checked_mul(usize::from(height)).ok_or(
                        SectionError::Extent {
                            at: reader.at,
                            wanted: "raster intensities",
                        },
                    )?;
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
                    let n = usize::try_from(reader.u32("pcm count")?).map_err(|_| {
                        SectionError::Extent {
                            at: reader.at,
                            wanted: "pcm count",
                        }
                    })?;
                    let byte_count = n.checked_mul(2).ok_or(SectionError::Extent {
                        at: reader.at,
                        wanted: "pcm samples",
                    })?;
                    let samples = reader
                        .take(byte_count, "pcm samples")?
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
    fn canonical_fibre_bytes_match_the_python_golden_schema() {
        fn hex(text: &str) -> Vec<u8> {
            let text: String = text.chars().filter(|c| !c.is_whitespace()).collect();
            (0..text.len())
                .step_by(2)
                .map(|i| u8::from_str_radix(&text[i..i + 2], 16).unwrap())
                .collect()
        }
        let cases = [
            (Passage::Octets(b"abc".to_vec()), "00"),
            (
                raster(1, 1, vec![3]),
                "01 0001 0001 0000000000000001 0000000000000001 01",
            ),
            (
                pcm(vec![-32768, 0]),
                "02 00003e80 0000000000000001 0000 0000000000000002 00000000 00008000",
            ),
        ];
        for (passage, payload) in cases {
            let chart = passage.encode_chart().unwrap();
            let mut canonical: Vec<u8> = Vec::new();
            chart.write_canonical_fibre(|bytes| canonical.extend(bytes));
            let mut expected = b"holonics.listener.fibre.v1\0".to_vec();
            expected.extend(hex(payload));
            assert_eq!(canonical, expected);
            let summary = chart.summary();
            assert_eq!(summary.fibre_bytes, expected.len() as u128);
            assert_eq!(summary.fibre_sha256, sha256(&expected));
        }
        let summary = Passage::Octets(b"abc".to_vec())
            .encode_chart()
            .unwrap()
            .summary();
        assert_eq!(
            summary.chart_sha256,
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert!(!summary.to_string().contains("samples_from_peak"));
        assert!(!summary.to_string().contains("remainders="));
    }

    fn round_trip(passage: Passage) -> PassageChart {
        let chart = passage.encode_chart().unwrap();
        assert_eq!(chart.decode().unwrap(), passage);
        let expected: Vec<_> = chart
            .octets
            .iter()
            .copied()
            .map(Piece::Octet)
            .chain([Piece::End])
            .collect();
        assert_eq!(pieces_of(&chart.cells()), expected);
        chart
    }

    fn raster(width: u16, height: u16, intensities: Vec<u8>) -> Passage {
        Passage::Raster {
            width,
            height,
            intensities,
        }
    }

    fn pcm(samples: Vec<i16>) -> Passage {
        Passage::Pcm {
            rate: 16000,
            samples,
        }
    }

    #[test]
    fn stroke_round_trips_empty_single_and_full_frames_with_the_first_jump() {
        for passage in [
            raster(0, 0, vec![]),
            raster(0, 2, vec![]),
            raster(3, 2, vec![0; 6]),
        ] {
            let chart = round_trip(passage);
            assert!(chart.octets.is_empty());
            assert_eq!(chart.cells(), end_cells());
        }
        let single = round_trip(raster(3, 2, vec![0, 0, 0, 0, 255, 0]));
        assert_eq!(single.octets, [0x87, 1, 1]);
        assert_eq!(
            single.fibre,
            ChartFibre::Stroke(StrokeFibre {
                width: 3,
                height: 2,
                jumps: 1,
                remainders: vec![127]
            })
        );
        let full = round_trip(raster(3, 3, vec![255; 9]));
        let ChartFibre::Stroke(fibre) = &full.fibre else {
            panic!("stroke fibre");
        };
        assert_eq!(fibre.jumps, 1);
        assert_eq!(fibre.remainders.len(), 9);
        assert_eq!(full.cells().len(), 2 * 9 + 4 * fibre.jumps + 2);
    }

    #[test]
    fn stroke_jumps_upward_and_keeps_every_intensity_remainder() {
        let mut intensities = vec![0; 15];
        for (index, value) in [(0, 1), (6, 2), (12, 3), (4, 4)] {
            intensities[index] = value;
        }
        let chart = round_trip(raster(5, 3, intensities));
        assert_eq!(chart.octets, [0x80, 0, 0, 0x11, 0x01, 0x82, 254, 2]);
        assert_eq!(
            chart.fibre,
            ChartFibre::Stroke(StrokeFibre {
                width: 5,
                height: 3,
                jumps: 2,
                remainders: vec![0, 0, 1, 0]
            })
        );
        for value in 1..=255 {
            round_trip(raster(1, 1, vec![value]));
        }
    }

    #[test]
    fn stroke_refuses_shape_mismatch_and_signed_jump_overflow() {
        assert_eq!(
            raster(2, 2, vec![1]).encode_chart(),
            Err(SectionError::Raster {
                width: 2,
                height: 2,
                found: 1
            })
        );
        let mut valid = vec![0; 128];
        valid[127] = 1;
        assert_eq!(round_trip(raster(128, 1, valid)).octets, [0x80, 0, 127]);
        let mut invalid = vec![0; 129];
        invalid[128] = 1;
        assert_eq!(
            raster(129, 1, invalid).encode_chart(),
            Err(SectionError::StrokeOffset {
                row: 0,
                column: 128
            })
        );
        // The first component walks downward; its next component is above its final pixel.
        for height in [129u16, 130] {
            let mut intensities = vec![0; usize::from(height) * 3];
            for row in 0..usize::from(height) {
                intensities[row * 3] = 1;
            }
            intensities[2] = 1;
            let passage = raster(3, height, intensities);
            if height == 129 {
                assert!(round_trip(passage).octets.ends_with(&[0x80, 128, 2]));
            } else {
                assert_eq!(
                    passage.encode_chart(),
                    Err(SectionError::StrokeOffset {
                        row: -129,
                        column: 2
                    })
                );
            }
        }
    }

    #[test]
    fn stroke_decode_refuses_malformed_coordinates_moves_and_fibres() {
        let original = round_trip(raster(1, 1, vec![3]));
        for octets in [
            vec![0x01],
            vec![0x80, 0],
            vec![0x80, 0, 1],
            vec![0x88, 0, 0],
            vec![0x90],
        ] {
            let mut bad = original.clone();
            bad.octets = octets;
            assert!(bad.decode().is_err());
        }
        for remainders in [vec![], vec![2], vec![1, 0]] {
            let mut bad = original.clone();
            let ChartFibre::Stroke(fibre) = &mut bad.fibre else {
                unreachable!()
            };
            fibre.remainders = remainders;
            assert!(bad.decode().is_err());
        }
        let mut bad = original;
        let ChartFibre::Stroke(fibre) = &mut bad.fibre else {
            unreachable!()
        };
        fibre.jumps = 0;
        assert!(bad.decode().is_err());
    }

    #[test]
    fn pcm_round_trips_zeros_sign_changes_one_sample_and_the_i16_minimum() {
        for samples in [
            vec![],
            vec![0],
            vec![0; 12],
            vec![1],
            vec![-32768],
            vec![0, 0, 3, 0, 2, -4, 0, -1, 5, 0],
        ] {
            round_trip(pcm(samples));
        }
        let chart = round_trip(pcm(vec![-32768]));
        assert_eq!(chart.octets, [1, 0x1f]);
        assert_eq!(
            chart.fibre,
            ChartFibre::HalfCycles(PcmFibre {
                rate: 16000,
                runs: vec![HalfCycleFibre {
                    peak_remainder: 0,
                    samples_from_peak: vec![0]
                }]
            })
        );
        let chart = round_trip(pcm(vec![0, 0, 3, 0, 2, -4, 0, -1, 5, 0]));
        assert_eq!(chart.octets, [2, 0x20, 3, 0x01, 3, 0x12, 2, 0x02]);
    }

    #[test]
    fn pcm_length_carries_always_end_with_a_remainder_including_zero() {
        for length in [254, 255, 256, 510] {
            let chart = round_trip(pcm(vec![7; length]));
            let mut expected = vec![255; length / 255];
            expected.extend([(length % 255) as u8, 2]);
            assert_eq!(chart.octets, expected);
        }
    }

    #[test]
    fn pcm_sign_change_composes_raw_octets_and_keeps_passage_framing_separate() {
        let a = pcm(vec![0, 2, 0, -3, 0]);
        let b = pcm(vec![4, 0, -5]);
        let whole = round_trip(pcm(vec![0, 2, 0, -3, 0, 4, 0, -5]));
        let (a_chart, b_chart) = (a.encode_chart().unwrap(), b.encode_chart().unwrap());
        assert_eq!(
            whole.octets,
            [a_chart.octets.clone(), b_chart.octets.clone()].concat()
        );
        let separate = Section {
            passages: vec![a, b],
            target: vec![],
        }
        .source_cells(0)
        .unwrap();
        assert_eq!(separate, [a_chart.cells(), b_chart.cells()].concat());
        assert_eq!(separate.len(), whole.cells().len() + end_cells().len());
    }

    #[test]
    fn pcm_decode_refuses_bad_carries_peak_tags_samples_and_fibres() {
        let original = round_trip(pcm(vec![3]));
        for octets in [
            vec![255],
            vec![1],
            vec![0, 0],
            vec![1, 0x30],
            vec![1, 0x21],
            vec![2, 0],
        ] {
            let mut bad = original.clone();
            bad.octets = octets;
            assert!(bad.decode().is_err());
        }
        for (peak_remainder, samples_from_peak) in [
            (2, vec![0]),
            (1, vec![]),
            (1, vec![i32::MAX]),
            (1, vec![-6]),
        ] {
            let mut bad = original.clone();
            let ChartFibre::HalfCycles(fibre) = &mut bad.fibre else {
                unreachable!()
            };
            fibre.runs[0] = HalfCycleFibre {
                peak_remainder,
                samples_from_peak,
            };
            assert!(bad.decode().is_err());
        }
    }

    #[test]
    fn source_cells_use_the_actual_chart_and_targets_remain_octets() {
        for passage in [
            Passage::Octets(vec![b'A']),
            raster(2, 1, vec![0, 3]),
            pcm(vec![2, -3]),
        ] {
            let chart = passage.encode_chart().unwrap();
            let section = Section {
                passages: vec![passage],
                target: vec![b'7'],
            };
            assert_eq!(section.chart_kind().unwrap(), chart.kind);
            assert_eq!(section.source_cells(0).unwrap(), chart.cells());
            assert_eq!(section.target_cells(0).unwrap(), closed_cells(b"7"));
        }
    }

    #[test]
    fn release_chart_requires_nonempty_homogeneous_passages_and_ignores_targets() {
        assert_eq!(
            Section {
                passages: vec![],
                target: vec![b'7']
            }
            .chart_kind(),
            Err(SectionError::EmptyPassages)
        );
        assert_eq!(
            Section {
                passages: vec![pcm(vec![]), pcm(vec![1])],
                target: vec![b'7']
            }
            .chart_kind(),
            Ok(ChartKind::Pcm)
        );
        assert_eq!(
            Section {
                passages: vec![Passage::Octets(vec![]), pcm(vec![])],
                target: vec![]
            }
            .chart_kind(),
            Err(SectionError::MixedCharts {
                first: ChartKind::Octets,
                found: ChartKind::Pcm
            })
        );
    }

    #[test]
    fn raw_hlsn_frames_preserve_raster_and_pcm_reconstruction_information() {
        let mut bytes = b"HLSN1\n".to_vec();
        bytes.extend(2u32.to_be_bytes());
        bytes.push(1);
        bytes.extend(2u16.to_be_bytes());
        bytes.extend(1u16.to_be_bytes());
        bytes.extend([0, 255]);
        bytes.push(2);
        bytes.extend(16000u32.to_be_bytes());
        bytes.extend(3u32.to_be_bytes());
        for sample in [0i16, -32768, 32767] {
            bytes.extend(sample.to_be_bytes());
        }
        bytes.extend(1u32.to_be_bytes());
        bytes.push(b'7');
        let decoded = read_frames(&bytes).unwrap();
        assert_eq!(
            decoded,
            [Section {
                passages: vec![raster(2, 1, vec![0, 255]), pcm(vec![0, -32768, 32767])],
                target: vec![b'7']
            }]
        );
        for passage in &decoded[0].passages {
            round_trip(passage.clone());
        }
    }

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
