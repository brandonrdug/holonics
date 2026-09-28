//! Canonical codecs for `BoundaryEgg` and its part-clock/hazard owners.
//!
//! The egg payload stores current nested tree standing, bounded letter address, exact passage
//! accumulators, and readout accumulators. Hazard fine counts are authoritative; pooled counts are
//! reconstructed through the encoded partition. No passage cells or deposit order are retained.

use super::{
    BYTE_VALUES, BoundaryEgg, BoundaryReadout, Hazard, HazardCell, HazardComparison,
    HazardPartition, HazardRest, PartClock, PartPort,
};
use crate::compression::landmark::context::{
    ContextError, LandmarkDeclaration, Landmarks, Letter, LetterFamily, PassageCode, Section,
    SectionChart, SectionSlots, Sections,
};
use crate::receiver::population::{Family, families::TreeFamilyCheckpointError};
use std::collections::BTreeMap;
use thiserror::Error;

const CLOCK_MAGIC: &[u8; 8] = b"HPCLK\0\0\x01";
const HAZARD_MAGIC: &[u8; 8] = b"HHAZ\0\0\0\x01";
const EGG_MAGIC: &[u8; 8] = b"HBEGG\0\0\x01";

/// Typed refusal while encoding or restoring a part-clock or hazard standing.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum BoundaryPortCheckpointError {
    #[error("unsupported boundary-port checkpoint version")]
    Version,
    #[error("boundary-port checkpoint is truncated at byte {offset}")]
    Truncated { offset: usize },
    #[error("boundary-port checkpoint has trailing bytes at byte {offset}")]
    Trailing { offset: usize },
    #[error("malformed boundary-port checkpoint at byte {offset}: {reason}")]
    Malformed { offset: usize, reason: &'static str },
    #[error("boundary-port checkpoint declaration does not match")]
    Declaration,
    #[error("boundary-port checkpoint state is inconsistent")]
    Inconsistent,
    #[error(transparent)]
    TreeFamily(#[from] TreeFamilyCheckpointError),
    #[error(transparent)]
    Landmark(#[from] crate::compression::landmark::context::StandingCodecError),
    #[error(transparent)]
    Passage(#[from] crate::compression::landmark::context::PassageCodecError),
    #[error(transparent)]
    Context(#[from] ContextError),
}

struct Writer(Vec<u8>);

impl Writer {
    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }
    fn u32(&mut self, value: u32) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }
    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }
    fn len(&mut self, value: usize) {
        self.u64(u64::try_from(value).expect("wire length fits u64"));
    }
    fn chart(&mut self, chart: SectionChart) {
        self.len(chart.bytes());
        self.len(chart.channels());
        self.len(chart.kinds());
    }
    fn rest(&mut self, rest: HazardRest) {
        match rest {
            HazardRest::Sentence { kind, phase, carry } => {
                self.u8(0);
                self.len(kind);
                self.u32(phase);
                self.u32(carry);
            }
            HazardRest::Other { class } => {
                self.u8(1);
                self.len(class);
            }
        }
    }
    fn blob(&mut self, bytes: &[u8]) {
        self.len(bytes.len());
        self.0.extend_from_slice(bytes);
    }
    fn string(&mut self, value: &str) {
        self.blob(value.as_bytes());
    }
    fn passage(&mut self, passage: &PassageCode) {
        self.blob(&passage.encode_checkpoint());
    }
    fn passages(&mut self, passages: &[PassageCode]) {
        self.len(passages.len());
        for passage in passages {
            self.passage(passage);
        }
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn fail<T>(&self, reason: &'static str) -> Result<T, BoundaryPortCheckpointError> {
        Err(BoundaryPortCheckpointError::Malformed {
            offset: self.at,
            reason,
        })
    }
    fn take<const N: usize>(&mut self) -> Result<[u8; N], BoundaryPortCheckpointError> {
        let end = self
            .at
            .checked_add(N)
            .ok_or(BoundaryPortCheckpointError::Malformed {
                offset: self.at,
                reason: "length overflow",
            })?;
        let Some(bytes) = self.bytes.get(self.at..end) else {
            return Err(BoundaryPortCheckpointError::Truncated { offset: self.at });
        };
        self.at = end;
        Ok(bytes.try_into().expect("fixed-size slice"))
    }
    fn u8(&mut self) -> Result<u8, BoundaryPortCheckpointError> {
        Ok(self.take::<1>()?[0])
    }
    fn u32(&mut self) -> Result<u32, BoundaryPortCheckpointError> {
        Ok(u32::from_le_bytes(self.take()?))
    }
    fn u64(&mut self) -> Result<u64, BoundaryPortCheckpointError> {
        Ok(u64::from_le_bytes(self.take()?))
    }
    fn usize_value(&mut self) -> Result<usize, BoundaryPortCheckpointError> {
        usize::try_from(self.u64()?).map_err(|_| BoundaryPortCheckpointError::Malformed {
            offset: self.at,
            reason: "value does not fit this host",
        })
    }
    fn len(&mut self, minimum_item_bytes: usize) -> Result<usize, BoundaryPortCheckpointError> {
        let value =
            usize::try_from(self.u64()?).map_err(|_| BoundaryPortCheckpointError::Malformed {
                offset: self.at,
                reason: "length does not fit this host",
            })?;
        if value > self.bytes.len().saturating_sub(self.at) / minimum_item_bytes.max(1) {
            return self.fail("length exceeds remaining input");
        }
        Ok(value)
    }
    fn blob(&mut self) -> Result<&'a [u8], BoundaryPortCheckpointError> {
        let length = self.len(0)?;
        let end = self
            .at
            .checked_add(length)
            .ok_or(BoundaryPortCheckpointError::Malformed {
                offset: self.at,
                reason: "blob length overflow",
            })?;
        let Some(bytes) = self.bytes.get(self.at..end) else {
            return Err(BoundaryPortCheckpointError::Truncated { offset: self.at });
        };
        self.at = end;
        Ok(bytes)
    }
    fn string(&mut self) -> Result<String, BoundaryPortCheckpointError> {
        String::from_utf8(self.blob()?.to_vec()).map_err(|_| {
            BoundaryPortCheckpointError::Malformed {
                offset: self.at,
                reason: "string is not UTF-8",
            }
        })
    }
    fn passage(&mut self) -> Result<PassageCode, BoundaryPortCheckpointError> {
        Ok(PassageCode::decode_checkpoint(self.blob()?)?)
    }
    fn passages(
        &mut self,
        expected: usize,
    ) -> Result<Vec<PassageCode>, BoundaryPortCheckpointError> {
        let count = self.len(8)?;
        if count != expected {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        (0..count).map(|_| self.passage()).collect()
    }
    fn chart(&mut self, chart: SectionChart) -> Result<(), BoundaryPortCheckpointError> {
        let actual = [
            self.usize_value()?,
            self.usize_value()?,
            self.usize_value()?,
        ];
        let expected = [chart.bytes(), chart.channels(), chart.kinds()];
        if actual != expected {
            return Err(BoundaryPortCheckpointError::Declaration);
        }
        Ok(())
    }
    fn rest(&mut self) -> Result<HazardRest, BoundaryPortCheckpointError> {
        match self.u8()? {
            0 => Ok(HazardRest::Sentence {
                kind: self.usize_value()?,
                phase: self.u32()?,
                carry: self.u32()?,
            }),
            1 => Ok(HazardRest::Other {
                class: self.usize_value()?,
            }),
            _ => self.fail("unknown hazard-rest tag"),
        }
    }
}

impl PartClock {
    /// Encode the clock's current port and pinned chart, without retaining received cells.
    pub fn encode_checkpoint(&self) -> Vec<u8> {
        let mut writer = Writer(CLOCK_MAGIC.to_vec());
        writer.chart(self.chart);
        match self.port.section {
            None => writer.u8(0),
            Some(section) => {
                writer.u8(1);
                writer.len(section.kind);
                writer.len(section.channel);
            }
        }
        writer.u64(self.port.phase);
        writer.u64(self.port.carry);
        match self.port.byte {
            None => writer.u8(0),
            Some(byte) => {
                writer.u8(1);
                writer.u8(byte);
            }
        }
        writer.0
    }

    /// Restore a clock's port against the caller's immutable section chart.
    pub fn decode_checkpoint(
        chart: SectionChart,
        bytes: &[u8],
    ) -> Result<Self, BoundaryPortCheckpointError> {
        if bytes.len() < CLOCK_MAGIC.len() || &bytes[..CLOCK_MAGIC.len()] != CLOCK_MAGIC {
            return Err(BoundaryPortCheckpointError::Version);
        }
        let mut reader = Reader {
            bytes,
            at: CLOCK_MAGIC.len(),
        };
        reader.chart(chart)?;
        let section = match reader.u8()? {
            0 => None,
            1 => {
                let section = Section {
                    kind: reader.usize_value()?,
                    channel: reader.usize_value()?,
                };
                if section.kind >= chart.kinds() || section.channel >= chart.channels() {
                    return reader.fail("section lies outside its chart");
                }
                Some(section)
            }
            _ => return reader.fail("unknown section tag"),
        };
        let phase = reader.u64()?;
        let carry = reader.u64()?;
        let byte = match reader.u8()? {
            0 => None,
            1 => Some(reader.u8()?),
            _ => return reader.fail("unknown last-byte tag"),
        };
        if reader.at != bytes.len() {
            return Err(BoundaryPortCheckpointError::Trailing { offset: reader.at });
        }
        let empty = section.is_none() && phase == 0 && carry == 0 && byte.is_none();
        let open = section.is_some()
            && carry <= phase
            && ((phase == 0 && byte.is_none() && carry == 0) || (phase > 0 && byte.is_some()));
        if !(empty || open) {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        let clock = Self {
            chart,
            port: PartPort {
                section,
                phase,
                carry,
                byte,
            },
        };
        if clock.encode_checkpoint() != bytes {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        Ok(clock)
    }
}

impl Hazard {
    /// Encode the hazard partition and fine-cell counts. Pooled counts are a derived projection.
    pub fn encode_checkpoint(&self, chart: SectionChart) -> Vec<u8> {
        let mut writer = Writer(HAZARD_MAGIC.to_vec());
        writer.chart(chart);
        writer.len(self.partition.classes.len());
        for &class in &self.partition.classes {
            writer.len(class);
        }
        writer.len(self.partition.shares.len());
        for (rest, map) in &self.partition.shares {
            writer.rest(*rest);
            writer.len(map.len());
            for &channel in map {
                writer.len(channel);
            }
        }
        writer.len(self.fine.len());
        for (cell, counts) in &self.fine {
            writer.len(cell.channel);
            writer.rest(cell.rest);
            writer.u64(counts[0]);
            writer.u64(counts[1]);
        }
        writer.u64(self.deposits);
        writer.0
    }

    /// Restore exact fine counts, validating the partition and rebuilding pooled counts.
    pub fn decode_checkpoint(
        chart: SectionChart,
        bytes: &[u8],
    ) -> Result<Self, BoundaryPortCheckpointError> {
        if bytes.len() < HAZARD_MAGIC.len() || &bytes[..HAZARD_MAGIC.len()] != HAZARD_MAGIC {
            return Err(BoundaryPortCheckpointError::Version);
        }
        let mut reader = Reader {
            bytes,
            at: HAZARD_MAGIC.len(),
        };
        reader.chart(chart)?;
        let class_count = reader.len(8)?;
        if class_count != BYTE_VALUES {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        let mut classes = Vec::with_capacity(class_count);
        for _ in 0..class_count {
            classes.push(reader.usize_value()?);
        }
        let share_count = reader.len(9)?;
        let mut shares = BTreeMap::new();
        for _ in 0..share_count {
            let rest = reader.rest()?;
            if let HazardRest::Sentence { kind, .. } = rest {
                if kind >= chart.kinds() {
                    return reader.fail("sentence kind lies outside its chart");
                }
            }
            let len = reader.len(8)?;
            if len != chart.channels() {
                return reader.fail("shared channel map has the wrong size");
            }
            let mut map = Vec::with_capacity(len);
            for _ in 0..len {
                let channel = reader.usize_value()?;
                if channel >= chart.channels() {
                    return reader.fail("shared channel lies outside its chart");
                }
                map.push(channel);
            }
            if shares.insert(rest, map).is_some() {
                return reader.fail("duplicate shared hazard rest");
            }
        }
        let partition = HazardPartition::learned(classes, shares)
            .map_err(|_| BoundaryPortCheckpointError::Inconsistent)?;
        let fine_count = reader.len(24)?;
        let mut fine = BTreeMap::new();
        let mut total = 0u64;
        for _ in 0..fine_count {
            let channel = reader.usize_value()?;
            if channel >= chart.channels() {
                return reader.fail("hazard channel lies outside its chart");
            }
            let rest = reader.rest()?;
            match rest {
                HazardRest::Sentence { kind, .. } if kind >= chart.kinds() => {
                    return reader.fail("sentence kind lies outside its chart");
                }
                HazardRest::Other { class } if class >= BYTE_VALUES => {
                    return reader.fail("byte class lies outside its declared values");
                }
                _ => {}
            }
            let counts = [reader.u64()?, reader.u64()?];
            if counts == [0, 0] {
                return reader.fail("stored fine cell has no deposits");
            }
            total = total
                .checked_add(counts[0])
                .and_then(|n| n.checked_add(counts[1]))
                .ok_or(BoundaryPortCheckpointError::Inconsistent)?;
            if fine.insert(HazardCell { channel, rest }, counts).is_some() {
                return reader.fail("duplicate fine hazard cell");
            }
        }
        let deposits = reader.u64()?;
        if reader.at != bytes.len() {
            return Err(BoundaryPortCheckpointError::Trailing { offset: reader.at });
        }
        if total != deposits {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        let mut counts = BTreeMap::new();
        for (cell, pair) in &fine {
            let merged = counts.entry(partition.coarse(cell)).or_insert([0u64; 2]);
            merged[0] = merged[0]
                .checked_add(pair[0])
                .ok_or(BoundaryPortCheckpointError::Inconsistent)?;
            merged[1] = merged[1]
                .checked_add(pair[1])
                .ok_or(BoundaryPortCheckpointError::Inconsistent)?;
        }
        let hazard = Self {
            partition,
            fine,
            counts,
            deposits,
        };
        if hazard.encode_checkpoint(chart) != bytes {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        Ok(hazard)
    }
}

fn write_letters(writer: &mut Writer, letters: &[Letter]) {
    writer.len(letters.len());
    for letter in letters {
        match letter {
            Letter::Boundary => writer.u8(0),
            Letter::Cell(cell) => {
                writer.u8(1);
                writer.len(*cell);
            }
            Letter::Bundle(bundle) => {
                writer.u8(2);
                writer.len(bundle.cell);
                writer.u32(bundle.features);
            }
        }
    }
}

fn read_letters(reader: &mut Reader<'_>) -> Result<Vec<Letter>, BoundaryPortCheckpointError> {
    let count = reader.len(1)?;
    (0..count)
        .map(|_| match reader.u8()? {
            0 => Ok(Letter::Boundary),
            1 => Ok(Letter::Cell(reader.usize_value()?)),
            2 => Ok(Letter::Bundle(
                crate::compression::landmark::context::Bundle {
                    cell: reader.usize_value()?,
                    features: reader.u32()?,
                },
            )),
            _ => reader.fail("unknown letter tag"),
        })
        .collect()
}

fn write_counts(writer: &mut Writer, values: &[u64]) {
    writer.len(values.len());
    for value in values {
        writer.u64(*value);
    }
}

fn read_counts(
    reader: &mut Reader<'_>,
    expected: usize,
) -> Result<Vec<u64>, BoundaryPortCheckpointError> {
    let count = reader.len(8)?;
    if count != expected {
        return Err(BoundaryPortCheckpointError::Inconsistent);
    }
    (0..count).map(|_| reader.u64()).collect()
}

fn encode_readout(writer: &mut Writer, readout: &BoundaryReadout) {
    write_counts(writer, &readout.bytes);
    write_counts(writer, &readout.closes);
    writer.passages(&readout.hazard_bytes);
    writer.passages(&readout.hazard_closes);
    writer.passages(&readout.within_bytes);
    writer.passage(&readout.letters);
    writer.passages(&readout.root_bytes);
    writer.passages(&readout.root_closes);
    writer.passage(&readout.tree_letters);
    writer.len(readout.hazard_cells);
    writer.len(readout.comparisons.len());
    for comparison in &readout.comparisons {
        writer.string(&comparison.label);
        writer.passages(&comparison.bytes);
        writer.passages(&comparison.closes);
        writer.len(comparison.cells);
    }
}

fn decode_readout(
    reader: &mut Reader<'_>,
    channels: usize,
    expected_comparisons: &[String],
) -> Result<BoundaryReadout, BoundaryPortCheckpointError> {
    let bytes = read_counts(reader, channels)?;
    let closes = read_counts(reader, channels)?;
    let hazard_bytes = reader.passages(channels)?;
    let hazard_closes = reader.passages(channels)?;
    let within_bytes = reader.passages(channels)?;
    let letters = reader.passage()?;
    let root_bytes = reader.passages(channels)?;
    let root_closes = reader.passages(channels)?;
    let tree_letters = reader.passage()?;
    let hazard_cells = reader.usize_value()?;
    let comparison_count = reader.len(1)?;
    if comparison_count != expected_comparisons.len() {
        return Err(BoundaryPortCheckpointError::Declaration);
    }
    let mut comparisons = Vec::with_capacity(comparison_count);
    for expected_label in expected_comparisons {
        let label = reader.string()?;
        if &label != expected_label {
            return Err(BoundaryPortCheckpointError::Declaration);
        }
        comparisons.push(HazardComparison {
            label,
            bytes: reader.passages(channels)?,
            closes: reader.passages(channels)?,
            cells: reader.usize_value()?,
        });
    }
    Ok(BoundaryReadout {
        bytes,
        closes,
        hazard_bytes,
        hazard_closes,
        within_bytes,
        letters,
        root_bytes,
        root_closes,
        tree_letters,
        hazard_cells,
        comparisons,
    })
}

fn inferred_sections(
    declaration: &LandmarkDeclaration,
    chart: SectionChart,
) -> Result<Option<(SectionChart, SectionSlots)>, BoundaryPortCheckpointError> {
    if declaration.family.is_empty() {
        return Ok(None);
    }
    for slots in [SectionSlots::Channel, SectionSlots::ChannelKind] {
        if Sections::new(chart, slots)
            .is_ok_and(|sections| declaration.family == *sections.family())
        {
            return Ok(Some((chart, slots)));
        }
    }
    Err(BoundaryPortCheckpointError::Declaration)
}

fn tree_open_section(bytes: &[u8]) -> Result<Option<Section>, BoundaryPortCheckpointError> {
    const TREE_MAGIC: &[u8; 8] = b"HTREE\0\0\x01";
    if bytes.len() < TREE_MAGIC.len() || &bytes[..TREE_MAGIC.len()] != TREE_MAGIC {
        return Err(BoundaryPortCheckpointError::Inconsistent);
    }
    let mut reader = Reader {
        bytes,
        at: TREE_MAGIC.len(),
    };
    let _description = reader.u64()?;
    let _standing = reader.blob()?;
    let sections_tag = reader.u8()?;
    match sections_tag {
        0 => {
            if reader.u8()? != 0 {
                return Err(BoundaryPortCheckpointError::Inconsistent);
            }
            Ok(None)
        }
        1 => {
            let _chart = [
                reader.usize_value()?,
                reader.usize_value()?,
                reader.usize_value()?,
            ];
            match reader.u8()? {
                0 | 1 => {}
                _ => return reader.fail("unknown tree section-slot tag"),
            }
            match reader.u8()? {
                0 => Ok(None),
                1 => Ok(Some(Section {
                    kind: reader.usize_value()?,
                    channel: reader.usize_value()?,
                })),
                _ => reader.fail("unknown tree open-section tag"),
            }
        }
        _ => reader.fail("unknown tree section-declaration tag"),
    }
}

impl BoundaryEgg {
    /// Encode the full contemporary egg standing in canonical versioned form.
    ///
    /// The receiving byte tree and letter tree are stored as their own native standing codecs;
    /// the bounded letter address and readout accumulators are direct current state, not a replay
    /// archive. Restoration requires an unread egg constructed from the same immutable declaration.
    pub fn encode_checkpoint(&self) -> Vec<u8> {
        let mut writer = Writer(EGG_MAGIC.to_vec());
        writer.string(&self.label);
        writer.u64(self.description);
        writer.chart(self.chart);
        writer.blob(&self.bytes.encode_checkpoint());
        writer.blob(&self.clock.encode_checkpoint());
        writer.blob(&self.hazard.encode_checkpoint(self.chart));
        writer.len(self.comparisons.len());
        for (hazard, reading) in self.comparisons.iter().zip(&self.readout.comparisons) {
            writer.string(&reading.label);
            writer.blob(&hazard.encode_checkpoint(self.chart));
        }
        writer.blob(&self.letters.tree.encode_standing());
        writer.u64(self.letters.lengths);
        writer.len(self.letters.family.sizes().len());
        for &size in self.letters.family.sizes() {
            writer.u64(size);
        }
        match self.letters.pending {
            None => writer.u8(0),
            Some(letter) => {
                writer.u8(1);
                writer.len(letter);
            }
        }
        writer.u64(self.letters.received);
        let past: Vec<Letter> = self.letters.past.iter().copied().collect();
        write_letters(&mut writer, &past);
        writer.passage(&self.passage);
        encode_readout(&mut writer, &self.readout);
        writer.0
    }

    /// Restore a complete egg from current state bytes against a fresh pinned declaration.
    pub fn decode_checkpoint(
        mut declaration: Self,
        bytes: &[u8],
    ) -> Result<Self, BoundaryPortCheckpointError> {
        if bytes.len() < EGG_MAGIC.len() || &bytes[..EGG_MAGIC.len()] != EGG_MAGIC {
            return Err(BoundaryPortCheckpointError::Version);
        }
        if declaration.bytes.tree().passed() != 0
            || declaration.letters.received != 0
            || declaration.passage.factors() != 0
            || declaration.hazard.deposits != 0
            || declaration
                .comparisons
                .iter()
                .any(|hazard| hazard.deposits != 0)
        {
            return Err(BoundaryPortCheckpointError::Declaration);
        }
        let expected_labels: Vec<String> = declaration
            .readout
            .comparisons
            .iter()
            .map(|comparison| comparison.label.clone())
            .collect();
        let mut reader = Reader {
            bytes,
            at: EGG_MAGIC.len(),
        };
        if reader.string()? != declaration.label || reader.u64()? != declaration.description {
            return Err(BoundaryPortCheckpointError::Declaration);
        }
        reader.chart(declaration.chart)?;
        let byte_checkpoint = reader.blob()?;
        let byte_declaration = declaration.bytes.tree().declaration().clone();
        let byte_sections = inferred_sections(&byte_declaration, declaration.chart)?;
        let byte_open = tree_open_section(byte_checkpoint)?;
        declaration.bytes = crate::receiver::population::TreeFamily::decode_checkpoint(
            byte_declaration,
            declaration.bytes.description(),
            byte_sections,
            byte_checkpoint,
        )?;
        declaration.clock = PartClock::decode_checkpoint(declaration.chart, reader.blob()?)?;
        if byte_sections.is_some() && byte_open != declaration.clock.port.section {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        let expected_hazard_partition = declaration.hazard.partition().clone();
        declaration.hazard = Hazard::decode_checkpoint(declaration.chart, reader.blob()?)?;
        if declaration.hazard.partition() != &expected_hazard_partition {
            return Err(BoundaryPortCheckpointError::Declaration);
        }
        let comparison_count = reader.len(1)?;
        if comparison_count != declaration.comparisons.len() {
            return Err(BoundaryPortCheckpointError::Declaration);
        }
        for index in 0..comparison_count {
            let label = reader.string()?;
            if label != expected_labels[index] {
                return Err(BoundaryPortCheckpointError::Declaration);
            }
            let hazard = Hazard::decode_checkpoint(declaration.chart, reader.blob()?)?;
            if hazard.partition() != declaration.comparisons[index].partition() {
                return Err(BoundaryPortCheckpointError::Declaration);
            }
            declaration.comparisons[index] = hazard;
        }
        let letter_standing = reader.blob()?;
        let lengths = reader.u64()?;
        let family_len = reader.len(8)?;
        let mut sizes = Vec::with_capacity(family_len);
        for _ in 0..family_len {
            sizes.push(reader.u64()?);
        }
        if lengths != declaration.letters.lengths
            || LetterFamily::new(sizes)? != declaration.letters.family
        {
            return Err(BoundaryPortCheckpointError::Declaration);
        }
        let letter_declaration = declaration.letters.tree.declaration().clone();
        let letter_standing = Landmarks::decode_standing(letter_declaration, letter_standing)?;
        let pending = match reader.u8()? {
            0 => None,
            1 => Some(reader.usize_value()?),
            _ => return reader.fail("unknown pending-letter tag"),
        };
        let received = reader.u64()?;
        let past = read_letters(&mut reader)?;
        let passage = reader.passage()?;
        let readout = decode_readout(&mut reader, declaration.chart.channels(), &expected_labels)?;
        if reader.at != bytes.len() {
            return Err(BoundaryPortCheckpointError::Trailing { offset: reader.at });
        }
        declaration.letters.tree = letter_standing;
        declaration.letters.pending = pending;
        declaration.letters.received = received;
        declaration.letters.past = past.into();
        declaration.passage = passage;
        declaration.readout = readout;
        validate_egg_state(&declaration)?;
        if declaration.encode_checkpoint() != bytes {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        Ok(declaration)
    }
}

fn validate_egg_state(egg: &BoundaryEgg) -> Result<(), BoundaryPortCheckpointError> {
    let channel_count = egg.chart.channels();
    let readout = &egg.readout;
    let letters = &egg.letters;
    let total_bytes = readout
        .bytes
        .iter()
        .try_fold(0u64, |sum, &value| sum.checked_add(value));
    let total_closes = readout
        .closes
        .iter()
        .try_fold(0u64, |sum, &value| sum.checked_add(value));
    let expected_past = letters
        .received
        .saturating_sub(1)
        .min(letters.tree.declaration().depth as u64);
    let expected_passed = total_bytes
        .and_then(|count| count.checked_add(letters.received))
        .ok_or(BoundaryPortCheckpointError::Inconsistent)?;
    let expected_hazard_deposits = expected_passed.saturating_sub(1);
    let latest_letter_matches = match (egg.clock.port.section, letters.pending) {
        (None, None) => letters.received == 0,
        (Some(section), Some(pending)) => egg
            .chart
            .letter(section)
            .ok()
            .is_some_and(|cell| cell - egg.chart.bytes() == pending),
        _ => false,
    };
    if readout.bytes.len() != channel_count
        || readout.closes.len() != channel_count
        || readout.hazard_bytes.len() != channel_count
        || readout.hazard_closes.len() != channel_count
        || readout.within_bytes.len() != channel_count
        || readout.root_bytes.len() != channel_count
        || readout.root_closes.len() != channel_count
        || total_closes != Some(letters.received.saturating_sub(1))
        || egg.bytes.tree().passed() != expected_passed
        || egg.passage.factors() != expected_passed
        || letters.tree.passed() != letters.received
        || letters.received > letters.tree.declaration().population
        || letters.past.len() as u64 != expected_past
        || letters.pending.is_some() != (letters.received > 0)
        || !latest_letter_matches
        || letters
            .pending
            .is_some_and(|pending| pending >= egg.chart.letters())
        || letters.past.iter().any(|letter| match letter {
            Letter::Bundle(bundle) => {
                bundle.cell >= egg.chart.letters()
                    || u64::from(bundle.features) >= letters.family.codes()
            }
            _ => true,
        })
        || readout.hazard_cells != egg.hazard.cells()
        || egg.hazard.deposits != expected_hazard_deposits
        || readout.comparisons.len() != egg.comparisons.len()
        || readout.letters.factors() != letters.received
        || readout.tree_letters.factors() != letters.received
    {
        return Err(BoundaryPortCheckpointError::Inconsistent);
    }
    if let Some(section) = egg.clock.port.section {
        if section.channel >= channel_count
            || section.kind >= egg.chart.kinds()
            || egg.clock.port.phase > readout.bytes[section.channel]
        {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
    } else if letters.received != 0 {
        return Err(BoundaryPortCheckpointError::Inconsistent);
    }
    for channel in 0..channel_count {
        for (code, expected) in [
            (&readout.hazard_bytes[channel], readout.bytes[channel]),
            (&readout.within_bytes[channel], readout.bytes[channel]),
            (&readout.root_bytes[channel], readout.bytes[channel]),
            (&readout.hazard_closes[channel], readout.closes[channel]),
            (&readout.root_closes[channel], readout.closes[channel]),
        ] {
            if code.factors() != expected {
                return Err(BoundaryPortCheckpointError::Inconsistent);
            }
        }
    }
    for (reading, hazard) in readout.comparisons.iter().zip(&egg.comparisons) {
        if reading.cells != hazard.cells()
            || hazard.deposits != expected_hazard_deposits
            || reading.bytes.len() != channel_count
            || reading.closes.len() != channel_count
        {
            return Err(BoundaryPortCheckpointError::Inconsistent);
        }
        for channel in 0..channel_count {
            if reading.bytes[channel].factors() != readout.bytes[channel]
                || reading.closes[channel].factors() != readout.closes[channel]
            {
                return Err(BoundaryPortCheckpointError::Inconsistent);
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::{Capacity, StopPrior};
    use crate::receiver::population::{Family, Readout, TreeFamily};

    fn section(chart: SectionChart) -> usize {
        chart
            .letter(Section {
                kind: 1,
                channel: 0,
            })
            .unwrap()
    }

    fn egg() -> BoundaryEgg {
        let chart = SectionChart::curated();
        let slots = SectionSlots::ChannelKind;
        let sections = Sections::new(chart, slots).unwrap();
        let population = 256;
        let byte_declaration = LandmarkDeclaration {
            alphabet: chart.alphabet(),
            depth: 3,
            forced: 0,
            population,
            grain: 16,
            family: sections.family().clone(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        };
        let bytes = TreeFamily::sectioned(byte_declaration, 71, sections).unwrap();
        let letter_declaration = LandmarkDeclaration {
            alphabet: chart.letters(),
            depth: 2,
            forced: 0,
            population,
            grain: 16,
            family: BoundaryEgg::letter_family(population).unwrap(),
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        };
        BoundaryEgg::new(
            "checkpoint fixture".to_string(),
            73,
            bytes,
            chart,
            letter_declaration,
        )
        .unwrap()
        .compared_with("fine control".to_string(), HazardPartition::finest())
        .unwrap()
    }

    #[test]
    fn clock_checkpoint_restores_port_and_next_advance() {
        let chart = SectionChart::curated();
        let mut current = PartClock::new(chart);
        current.advance(section(chart));
        for &byte in b"A sentence. More" {
            current.advance(usize::from(byte));
        }
        let bytes = current.encode_checkpoint();
        let mut restored = PartClock::decode_checkpoint(chart, &bytes).unwrap();
        assert_eq!(restored, current);
        assert_eq!(restored.encode_checkpoint(), bytes);
        let next = usize::from(b'.');
        restored.advance(next);
        current.advance(next);
        assert_eq!(restored, current);
    }

    #[test]
    fn hazard_checkpoint_rebuilds_projection_and_same_next_face() {
        let chart = SectionChart::curated();
        let mut clock = PartClock::new(chart);
        clock.advance(section(chart));
        let mut hazard = Hazard::new();
        hazard.deposit(&clock.port(), false);
        clock.advance(usize::from(b'.'));
        hazard.deposit(&clock.port(), true);
        let bytes = hazard.encode_checkpoint(chart);
        let mut restored = Hazard::decode_checkpoint(chart, &bytes).unwrap();
        assert_eq!(restored, hazard);
        let port = clock.port();
        assert_eq!(restored.face(&port), hazard.face(&port));
        restored.deposit(&port, false);
        hazard.deposit(&port, false);
        assert_eq!(restored, hazard);
    }

    #[test]
    fn hazard_checkpoint_keeps_a_learned_partition_and_its_shared_counts() {
        let chart = SectionChart::curated();
        let mut classes = vec![10_000; BYTE_VALUES];
        classes[0] = 10_000;
        let mut shares = BTreeMap::new();
        shares.insert(HazardRest::Other { class: 10_000 }, vec![0, 0, 2]);
        let partition = HazardPartition::learned(classes, shares).unwrap();
        let mut clock = PartClock::new(chart);
        clock.advance(section(chart));
        let mut hazard = Hazard::with_partition(partition);
        hazard.deposit(&clock.port(), false);
        clock.advance(usize::from(b'a'));
        hazard.deposit(&clock.port(), true);

        let bytes = hazard.encode_checkpoint(chart);
        let restored = Hazard::decode_checkpoint(chart, &bytes).unwrap();
        assert_eq!(restored, hazard);
        assert_eq!(restored.counts(), hazard.counts());
        assert_eq!(restored.encode_checkpoint(chart), bytes);
    }

    #[test]
    fn clock_and_hazard_checkpoints_refuse_malformed_state() {
        let chart = SectionChart::curated();
        let clock = PartClock::new(chart).encode_checkpoint();
        assert!(PartClock::decode_checkpoint(chart, &clock[..clock.len() - 1]).is_err());
        assert!(
            PartClock::decode_checkpoint(SectionChart::new(256, 2, 4).unwrap(), &clock).is_err()
        );
        let hazard = Hazard::new().encode_checkpoint(chart);
        assert!(Hazard::decode_checkpoint(chart, &hazard[..hazard.len() - 1]).is_err());
        let mut corrupt = hazard;
        corrupt[0] ^= 0xff;
        assert_eq!(
            Hazard::decode_checkpoint(chart, &corrupt),
            Err(BoundaryPortCheckpointError::Version)
        );
    }

    #[test]
    fn boundary_egg_checkpoint_restores_faces_readout_and_identical_continuation() {
        let chart = SectionChart::curated();
        let mut current = egg();
        let mut cells = vec![section(chart)];
        cells.extend(b"A sentence.".iter().map(|&byte| usize::from(byte)));
        cells.push(
            chart
                .letter(Section {
                    kind: 2,
                    channel: 1,
                })
                .unwrap(),
        );
        cells.extend(b"Ok.".iter().map(|&byte| usize::from(byte)));
        cells.push(
            chart
                .letter(Section {
                    kind: 3,
                    channel: 0,
                })
                .unwrap(),
        );
        for cell in cells {
            let face = current.face().unwrap();
            assert_eq!(current.receive(cell).unwrap(), face[cell]);
        }

        let bytes = current.encode_checkpoint();
        let mut restored = BoundaryEgg::decode_checkpoint(egg(), &bytes).unwrap();
        assert_eq!(restored.encode_checkpoint(), bytes);
        assert_eq!(restored.face().unwrap(), current.face().unwrap());
        assert_eq!(restored.likelihood(), current.likelihood());
        assert_eq!(restored.stages(), current.stages());
        match (restored.readout(), current.readout()) {
            (Readout::Boundary(restored), Readout::Boundary(current)) => {
                assert_eq!(restored, current);
            }
            _ => panic!("boundary eggs expose their staged readout"),
        }

        let next = usize::from(b' ');
        assert_eq!(
            restored.receive(next).unwrap(),
            current.receive(next).unwrap()
        );
        assert_eq!(restored.face().unwrap(), current.face().unwrap());
        assert_eq!(restored.stages(), current.stages());
        assert_eq!(restored.encode_checkpoint(), current.encode_checkpoint());
    }

    #[test]
    fn boundary_egg_checkpoint_refuses_malformed_and_unpinned_declarations() {
        let chart = SectionChart::curated();
        let mut current = egg();
        for cell in [section(chart), usize::from(b'a')] {
            current.receive(cell).unwrap();
        }
        let bytes = current.encode_checkpoint();
        assert!(BoundaryEgg::decode_checkpoint(egg(), &bytes[..bytes.len() - 1]).is_err());
        let mut wrong_version = bytes.clone();
        wrong_version[7] = 2;
        assert!(matches!(
            BoundaryEgg::decode_checkpoint(egg(), &wrong_version),
            Err(BoundaryPortCheckpointError::Version)
        ));
        let mut other = egg();
        other.label = "different declaration".to_string();
        assert!(matches!(
            BoundaryEgg::decode_checkpoint(other, &bytes),
            Err(BoundaryPortCheckpointError::Declaration)
        ));
    }
}
