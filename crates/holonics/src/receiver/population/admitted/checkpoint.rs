//! Canonical checkpoint codecs for the copy-stage and incidence-code constituents of
//! [`super::AdmittedEgg`]. These codecs persist only their sufficient counts and current
//! accumulated readouts; they do not retain passage occurrences.

use super::{
    AdmittedEgg, CopyCell, CopyLaw, CopyStage, Family, OpenPart, PointerCode, PointerReadout,
    Relation, RelationKind, Span, StageReadout,
};
use crate::compression::landmark::context::spans::{SpanReadingSnapshot, SpanReadingSnapshotError};
use crate::compression::landmark::context::{PassageCode, PassageCodecError, SpanReading};
use crate::receiver::population::boundary::BoundaryPortCheckpointError;
use std::collections::BTreeMap;
use thiserror::Error;

const STAGE_MAGIC: &[u8; 8] = b"HACPY\0\0\x01";
const POINTER_MAGIC: &[u8; 8] = b"HAPTR\0\0\x01";
const EGG_MAGIC: &[u8; 8] = b"HAEGG\0\0\x01";

/// A typed refusal to encode or restore an admitted-stage standing component.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AdmittedStageCheckpointError {
    #[error("unsupported admitted-stage checkpoint version")]
    Version,
    #[error("admitted-stage checkpoint is truncated at byte {offset}")]
    Truncated { offset: usize },
    #[error("admitted-stage checkpoint has trailing bytes at byte {offset}")]
    Trailing { offset: usize },
    #[error("malformed admitted-stage checkpoint at byte {offset}: {reason}")]
    Malformed { offset: usize, reason: &'static str },
    #[error("admitted-stage checkpoint declaration does not match")]
    Declaration,
    #[error("admitted-stage checkpoint state is inconsistent")]
    Inconsistent,
    #[error(transparent)]
    Passage(#[from] PassageCodecError),
    #[error(transparent)]
    Boundary(#[from] BoundaryPortCheckpointError),
    #[error(transparent)]
    SpanReading(#[from] SpanReadingSnapshotError),
}

struct Writer(Vec<u8>);

impl Writer {
    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }
    fn u32(&mut self, value: u32) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }
    fn i32(&mut self, value: i32) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }
    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_le_bytes());
    }
    fn len(&mut self, value: usize) {
        self.u64(u64::try_from(value).expect("checkpoint length fits u64"));
    }
    fn kind(&mut self, kind: RelationKind) {
        self.u8(match kind {
            RelationKind::Request => 0,
            RelationKind::LaterHuman => 1,
        });
    }
    fn law(&mut self, law: CopyLaw) {
        self.u64(law.least);
        self.u32(law.lengths);
        self.u32(law.odds);
    }
    fn cell(&mut self, cell: CopyCell) {
        self.u32(cell.length);
        self.i32(cell.odds);
    }
    fn pair(&mut self, pair: [u64; 2]) {
        self.u64(pair[0]);
        self.u64(pair[1]);
    }
    fn passage(&mut self, code: &PassageCode) {
        let encoded = code.encode_checkpoint();
        self.len(encoded.len());
        self.0.extend_from_slice(&encoded);
    }
    fn blob(&mut self, bytes: &[u8]) {
        self.len(bytes.len());
        self.0.extend_from_slice(bytes);
    }
    fn string(&mut self, value: &str) {
        self.blob(value.as_bytes());
    }
    fn chart(&mut self, chart: crate::compression::landmark::context::SectionChart) {
        self.len(chart.bytes());
        self.len(chart.channels());
        self.len(chart.kinds());
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn malformed<T>(&self, reason: &'static str) -> Result<T, AdmittedStageCheckpointError> {
        Err(AdmittedStageCheckpointError::Malformed {
            offset: self.at,
            reason,
        })
    }
    fn take<const N: usize>(&mut self) -> Result<[u8; N], AdmittedStageCheckpointError> {
        let end = self
            .at
            .checked_add(N)
            .ok_or(AdmittedStageCheckpointError::Malformed {
                offset: self.at,
                reason: "length overflow",
            })?;
        let Some(bytes) = self.bytes.get(self.at..end) else {
            return Err(AdmittedStageCheckpointError::Truncated { offset: self.at });
        };
        self.at = end;
        Ok(bytes.try_into().expect("fixed-size slice"))
    }
    fn u8(&mut self) -> Result<u8, AdmittedStageCheckpointError> {
        Ok(self.take::<1>()?[0])
    }
    fn u32(&mut self) -> Result<u32, AdmittedStageCheckpointError> {
        Ok(u32::from_le_bytes(self.take()?))
    }
    fn i32(&mut self) -> Result<i32, AdmittedStageCheckpointError> {
        Ok(i32::from_le_bytes(self.take()?))
    }
    fn u64(&mut self) -> Result<u64, AdmittedStageCheckpointError> {
        Ok(u64::from_le_bytes(self.take()?))
    }
    fn usize_value(&mut self) -> Result<usize, AdmittedStageCheckpointError> {
        let at = self.at;
        usize::try_from(self.u64()?).map_err(|_| AdmittedStageCheckpointError::Malformed {
            offset: at,
            reason: "value does not fit this host",
        })
    }
    fn len(&mut self, minimum_item_bytes: usize) -> Result<usize, AdmittedStageCheckpointError> {
        let at = self.at;
        let value =
            usize::try_from(self.u64()?).map_err(|_| AdmittedStageCheckpointError::Malformed {
                offset: at,
                reason: "length does not fit this host",
            })?;
        if value > self.bytes.len().saturating_sub(self.at) / minimum_item_bytes.max(1) {
            return self.malformed("length exceeds remaining input");
        }
        Ok(value)
    }
    fn blob(&mut self) -> Result<&[u8], AdmittedStageCheckpointError> {
        let length = self.len(1)?;
        let end = self
            .at
            .checked_add(length)
            .ok_or(AdmittedStageCheckpointError::Malformed {
                offset: self.at,
                reason: "blob length overflow",
            })?;
        let Some(value) = self.bytes.get(self.at..end) else {
            return Err(AdmittedStageCheckpointError::Truncated { offset: self.at });
        };
        self.at = end;
        Ok(value)
    }
    fn string(&mut self) -> Result<String, AdmittedStageCheckpointError> {
        String::from_utf8(self.blob()?.to_vec()).map_err(|_| {
            AdmittedStageCheckpointError::Malformed {
                offset: self.at,
                reason: "declaration label is not UTF-8",
            }
        })
    }
    fn kind(&mut self) -> Result<RelationKind, AdmittedStageCheckpointError> {
        match self.u8()? {
            0 => Ok(RelationKind::Request),
            1 => Ok(RelationKind::LaterHuman),
            _ => self.malformed("unknown relation-kind tag"),
        }
    }
    fn law(&mut self) -> Result<CopyLaw, AdmittedStageCheckpointError> {
        let least = self.u64()?;
        let lengths = self.u32()?;
        let odds = self.u32()?;
        CopyLaw::new(least, lengths, odds).map_err(|_| AdmittedStageCheckpointError::Inconsistent)
    }
    fn cell(&mut self) -> Result<CopyCell, AdmittedStageCheckpointError> {
        Ok(CopyCell {
            length: self.u32()?,
            odds: self.i32()?,
        })
    }
    fn pair(&mut self) -> Result<[u64; 2], AdmittedStageCheckpointError> {
        Ok([self.u64()?, self.u64()?])
    }
    fn passage(&mut self) -> Result<PassageCode, AdmittedStageCheckpointError> {
        let length = self.len(1)?;
        let end = self
            .at
            .checked_add(length)
            .ok_or(AdmittedStageCheckpointError::Malformed {
                offset: self.at,
                reason: "passage-code length overflow",
            })?;
        let Some(bytes) = self.bytes.get(self.at..end) else {
            return Err(AdmittedStageCheckpointError::Truncated { offset: self.at });
        };
        let value = PassageCode::decode_checkpoint(bytes)?;
        self.at = end;
        Ok(value)
    }
    fn finish(self) -> Result<(), AdmittedStageCheckpointError> {
        if self.at == self.bytes.len() {
            Ok(())
        } else {
            Err(AdmittedStageCheckpointError::Trailing { offset: self.at })
        }
    }
}

fn read_header<'a>(
    bytes: &'a [u8],
    magic: &[u8; 8],
) -> Result<Reader<'a>, AdmittedStageCheckpointError> {
    if bytes.len() < magic.len() || &bytes[..magic.len()] != magic {
        return Err(AdmittedStageCheckpointError::Version);
    }
    Ok(Reader {
        bytes,
        at: magic.len(),
    })
}

fn total_pairs<I>(pairs: I) -> Option<u64>
where
    I: IntoIterator<Item = [u64; 2]>,
{
    pairs
        .into_iter()
        .try_fold(0u64, |sum, [a, b]| sum.checked_add(a)?.checked_add(b))
}

impl CopyStage {
    /// Encode this stage's contemporary readout and per-cell `[miss, copy]` counts.
    pub fn encode_checkpoint(&self) -> Vec<u8> {
        let mut out = Writer(STAGE_MAGIC.to_vec());
        out.kind(self.readout.kind);
        out.law(self.readout.law);
        out.u64(self.readout.ticks[0]);
        out.u64(self.readout.ticks[1]);
        out.u64(self.readout.copies);
        for code in &self.readout.staged {
            out.passage(code);
        }
        for code in &self.readout.inner {
            out.passage(code);
        }
        out.passage(&self.readout.stage);
        out.passage(&self.readout.conditioned);
        out.len(self.readout.cells);
        out.len(self.counts.len());
        for (cell, counts) in &self.counts {
            out.cell(*cell);
            out.pair(*counts);
        }
        out.0
    }

    /// Restore a stage only under its caller-pinned kind and law.
    pub fn decode_checkpoint(
        kind: RelationKind,
        law: CopyLaw,
        bytes: &[u8],
    ) -> Result<Self, AdmittedStageCheckpointError> {
        let mut input = read_header(bytes, STAGE_MAGIC)?;
        if input.kind()? != kind || input.law()? != law {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        let ticks = [input.u64()?, input.u64()?];
        let copies = input.u64()?;
        let staged = [input.passage()?, input.passage()?];
        let inner = [input.passage()?, input.passage()?];
        let stage = input.passage()?;
        let conditioned = input.passage()?;
        let cells = input.usize_value()?;
        let count = input.len(24)?;
        let mut counts = BTreeMap::new();
        let mut previous = None;
        for _ in 0..count {
            let cell = input.cell()?;
            if previous.is_some_and(|old| old >= cell) {
                return input.malformed("copy cells are duplicated or not canonical");
            }
            let pair = input.pair()?;
            if pair == [0, 0] || cell.length >= law.lengths || law.odds == 0 && cell.odds != 0 {
                return input.malformed("copy count cell lies outside its declared partition");
            }
            if law.odds > 0 {
                let bound = i64::from(law.odds);
                if i64::from(cell.odds) < -bound || i64::from(cell.odds) >= bound {
                    return input.malformed("copy odds class lies outside its declared partition");
                }
            }
            previous = Some(cell);
            counts.insert(cell, pair);
        }
        input.finish()?;
        let total = total_pairs(counts.values().copied())
            .ok_or(AdmittedStageCheckpointError::Inconsistent)?;
        let ticks_total = ticks[0]
            .checked_add(ticks[1])
            .ok_or(AdmittedStageCheckpointError::Inconsistent)?;
        let copies_total = counts
            .values()
            .try_fold(0u64, |sum, pair| sum.checked_add(pair[1]));
        if cells != counts.len()
            || total != ticks_total
            || copies_total != Some(copies)
            || copies > ticks_total
        {
            return Err(AdmittedStageCheckpointError::Inconsistent);
        }
        Ok(Self {
            readout: StageReadout {
                kind,
                law,
                ticks,
                copies,
                staged,
                inner,
                stage,
                conditioned,
                cells,
            },
            counts,
        })
    }
}

impl PointerCode {
    pub(super) fn encode_checkpoint(&self) -> Vec<u8> {
        let mut out = Writer(POINTER_MAGIC.to_vec());
        out.kind(self.readout.kind);
        out.u64(self.readout.parts);
        out.u64(self.readout.held);
        out.passage(&self.readout.code);
        out.len(self.held.len());
        for (&(section_kind, previous), counts) in &self.held {
            out.len(section_kind);
            out.u8(u8::from(previous));
            out.pair(*counts);
        }
        out.len(self.same.len());
        for (&section_kind, counts) in &self.same {
            out.len(section_kind);
            out.pair(*counts);
        }
        out.len(self.levels.len());
        for counts in &self.levels {
            out.pair(*counts);
        }
        match self.previous {
            None => out.u8(0),
            Some(target) => {
                out.u8(1);
                out.u64(target);
            }
        }
        out.0
    }

    pub(super) fn decode_checkpoint(
        kind: RelationKind,
        section_kinds: usize,
        bytes: &[u8],
    ) -> Result<Self, AdmittedStageCheckpointError> {
        let mut input = read_header(bytes, POINTER_MAGIC)?;
        if input.kind()? != kind {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        let parts = input.u64()?;
        let held_count = input.u64()?;
        let code = input.passage()?;
        let held_len = input.len(25)?;
        let mut held = BTreeMap::new();
        let mut previous_key = None;
        for _ in 0..held_len {
            let section_kind = input.usize_value()?;
            if section_kind >= section_kinds {
                return input.malformed("held-count section kind lies outside its declaration");
            }
            let previous = match input.u8()? {
                0 => false,
                1 => true,
                _ => return input.malformed("invalid previous-held tag"),
            };
            let key = (section_kind, previous);
            if previous_key.is_some_and(|old| old >= key) {
                return input.malformed("held-count keys are duplicated or not canonical");
            }
            let pair = input.pair()?;
            if pair == [0, 0] {
                return input.malformed("empty held-count entry");
            }
            previous_key = Some(key);
            held.insert(key, pair);
        }
        let same_len = input.len(24)?;
        let mut same = BTreeMap::new();
        let mut previous_kind = None;
        for _ in 0..same_len {
            let section_kind = input.usize_value()?;
            if section_kind >= section_kinds {
                return input.malformed("same-target section kind lies outside its declaration");
            }
            if previous_kind.is_some_and(|old| old >= section_kind) {
                return input.malformed("same-target keys are duplicated or not canonical");
            }
            let pair = input.pair()?;
            if pair == [0, 0] {
                return input.malformed("empty same-target entry");
            }
            previous_kind = Some(section_kind);
            same.insert(section_kind, pair);
        }
        let levels_len = input.len(16)?;
        let mut levels = Vec::with_capacity(levels_len);
        for _ in 0..levels_len {
            let pair = input.pair()?;
            if pair == [0, 0] {
                return input.malformed("empty rank-level entry");
            }
            levels.push(pair);
        }
        let previous = match input.u8()? {
            0 => None,
            1 => Some(input.u64()?),
            _ => return input.malformed("invalid previous-target tag"),
        };
        input.finish()?;
        let all_parts = total_pairs(held.values().copied())
            .ok_or(AdmittedStageCheckpointError::Inconsistent)?;
        let held_parts = held
            .values()
            .try_fold(0u64, |sum, pair| sum.checked_add(pair[1]));
        let same_parts = total_pairs(same.values().copied())
            .ok_or(AdmittedStageCheckpointError::Inconsistent)?;
        if all_parts != parts
            || held_parts != Some(held_count)
            || held_count > parts
            || same_parts > held_count
            || previous.is_some() != (held_count > 0)
        {
            return Err(AdmittedStageCheckpointError::Inconsistent);
        }
        Ok(Self {
            readout: PointerReadout {
                kind,
                parts,
                held: held_count,
                code,
            },
            held,
            same,
            levels,
            previous,
        })
    }
}

impl AdmittedEgg {
    /// Encode this egg's current future-sufficient outer standing and its complete inner egg.
    /// Copy laws and the caller's base incidence remain pinned declarations. Newly committed
    /// future relations are part of current incidence state; spans retain only live target cells,
    /// while the open reading address keeps only the suffix needed by that fixed target span.
    pub fn encode_checkpoint(&self) -> Result<Vec<u8>, AdmittedStageCheckpointError> {
        let mut out = Writer(EGG_MAGIC.to_vec());
        out.string(&self.label);
        out.u64(self.description);
        out.chart(self.chart);
        out.len(self.relations.len());
        for relation in &self.relations {
            out.u64(relation.letter);
            out.kind(relation.kind);
            out.u64(relation.target);
        }
        out.law(self.stage.readout.law);
        out.len(self.receipts.len());
        for receipt in &self.receipts {
            out.kind(receipt.readout.kind);
            out.law(receipt.readout.law);
        }

        out.blob(&self.inner.encode_checkpoint());
        out.len(self.next);
        out.blob(&self.stage.encode_checkpoint());
        out.len(self.receipts.len());
        for receipt in &self.receipts {
            out.blob(&receipt.encode_checkpoint());
        }
        out.len(self.pointers.len());
        for pointer in &self.pointers {
            out.blob(&pointer.encode_checkpoint());
        }
        out.len(self.spans.len());
        for (&letter, span) in &self.spans {
            out.u64(letter);
            out.len(span.channel);
            out.u64(span.ordinal);
            out.u64(span.remaining);
            out.len(span.cells.len());
            for &cell in &span.cells {
                out.len(cell);
            }
        }
        match &self.open {
            None => out.u8(0),
            Some(open) => {
                out.u8(1);
                out.u64(open.letter);
                match open.relation {
                    None => out.u8(0),
                    Some((kind, target)) => {
                        out.u8(1);
                        out.kind(kind);
                        out.u64(target);
                        let span = self
                            .spans
                            .get(&target)
                            .ok_or(AdmittedStageCheckpointError::Inconsistent)?;
                        let snapshot = open.reading.snapshot(&span.cells)?;
                        out.len(snapshot.received);
                        out.len(snapshot.suffix.len());
                        for cell in snapshot.suffix {
                            out.len(cell);
                        }
                        match snapshot.at {
                            None => out.u8(0),
                            Some((j, length)) => {
                                out.u8(1);
                                out.len(j);
                                out.u64(length);
                            }
                        }
                    }
                }
            }
        }
        out.len(self.parts.len());
        for &parts in &self.parts {
            out.u64(parts);
        }
        out.u64(self.tick);
        out.passage(&self.passage);
        out.len(self.held);
        out.len(self.widest);
        Ok(out.0)
    }

    /// Restore from current state bytes against a fresh, caller-pinned declaration.
    pub fn decode_checkpoint(
        mut declaration: Self,
        bytes: &[u8],
    ) -> Result<Self, AdmittedStageCheckpointError> {
        if bytes.len() < EGG_MAGIC.len() || &bytes[..EGG_MAGIC.len()] != EGG_MAGIC {
            return Err(AdmittedStageCheckpointError::Version);
        }
        if !fresh(&declaration) {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        let mut input = Reader {
            bytes,
            at: EGG_MAGIC.len(),
        };
        if input.string()? != declaration.label || input.u64()? != declaration.description {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        let chart = [
            input.usize_value()?,
            input.usize_value()?,
            input.usize_value()?,
        ];
        if chart
            != [
                declaration.chart.bytes(),
                declaration.chart.channels(),
                declaration.chart.kinds(),
            ]
        {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        let relation_count = input.len(17)?;
        if relation_count < declaration.relations.len() {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        let mut relations = Vec::with_capacity(relation_count);
        let mut previous_relation = None;
        for _ in 0..relation_count {
            let actual = Relation {
                letter: input.u64()?,
                kind: input.kind()?,
                target: input.u64()?,
            };
            if actual.target >= actual.letter
                || previous_relation.is_some_and(|old: Relation| old.letter >= actual.letter)
            {
                return input.malformed("relations are invalid or not in canonical letter order");
            }
            previous_relation = Some(actual);
            relations.push(actual);
        }
        let mut base = declaration.relations.iter().peekable();
        for relation in &relations {
            if base.peek().is_some_and(|expected| **expected == *relation) {
                base.next();
            }
        }
        if base.next().is_some() {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        if input.law()? != declaration.stage.readout.law {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        let receipt_declarations = input.len(9)?;
        if receipt_declarations != declaration.receipts.len() {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        for expected in &declaration.receipts {
            if input.kind()? != expected.readout.kind || input.law()? != expected.readout.law {
                return Err(AdmittedStageCheckpointError::Declaration);
            }
        }

        let inner_bytes = input.blob()?.to_vec();
        declaration.inner = crate::receiver::population::boundary::BoundaryEgg::decode_checkpoint(
            declaration.inner.clone(),
            &inner_bytes,
        )?;
        let next = input.usize_value()?;
        if next > declaration.relations.len() {
            return input.malformed("next relation lies outside the declared incidence");
        }
        declaration.stage = CopyStage::decode_checkpoint(
            RelationKind::Request,
            declaration.stage.readout.law,
            input.blob()?,
        )?;
        let receipts = input.len(8)?;
        if receipts != declaration.receipts.len() {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        for expected in &mut declaration.receipts {
            *expected = CopyStage::decode_checkpoint(
                expected.readout.kind,
                expected.readout.law,
                input.blob()?,
            )?;
        }
        let pointers = input.len(8)?;
        if pointers != RelationKind::ALL.len() || declaration.pointers.len() != pointers {
            return Err(AdmittedStageCheckpointError::Declaration);
        }
        for (pointer, &kind) in declaration.pointers.iter_mut().zip(&RelationKind::ALL) {
            *pointer =
                PointerCode::decode_checkpoint(kind, declaration.chart.kinds(), input.blob()?)?;
        }
        let span_count = input.len(40)?;
        let mut spans = BTreeMap::new();
        let mut previous_letter = None;
        let mut held = 0usize;
        for _ in 0..span_count {
            let letter = input.u64()?;
            if previous_letter.is_some_and(|old| old >= letter) {
                return input.malformed("span keys are duplicated or not canonical");
            }
            let channel = input.usize_value()?;
            let ordinal = input.u64()?;
            let remaining = input.u64()?;
            let cell_count = input.len(8)?;
            if channel >= declaration.chart.channels() || remaining == 0 {
                return input.malformed("span port or live-reader count is invalid");
            }
            let mut cells = Vec::with_capacity(cell_count);
            for _ in 0..cell_count {
                let cell = input.usize_value()?;
                if cell >= declaration.alphabet() {
                    return input.malformed("retained target cell lies outside the alphabet");
                }
                cells.push(cell);
            }
            held = held
                .checked_add(cell_count)
                .ok_or(AdmittedStageCheckpointError::Inconsistent)?;
            previous_letter = Some(letter);
            spans.insert(
                letter,
                Span {
                    channel,
                    ordinal,
                    cells,
                    remaining,
                },
            );
        }
        let open = match input.u8()? {
            0 => None,
            1 => {
                let letter = input.u64()?;
                let relation = match input.u8()? {
                    0 => None,
                    1 => {
                        let kind = input.kind()?;
                        let target = input.u64()?;
                        let span = spans
                            .get(&target)
                            .ok_or(AdmittedStageCheckpointError::Inconsistent)?;
                        let received = input.usize_value()?;
                        let suffix_len = input.len(8)?;
                        let mut suffix = Vec::with_capacity(suffix_len);
                        for _ in 0..suffix_len {
                            let cell = input.usize_value()?;
                            if cell >= declaration.alphabet() {
                                return input
                                    .malformed("open reading cell lies outside the alphabet");
                            }
                            suffix.push(cell);
                        }
                        let at = match input.u8()? {
                            0 => None,
                            1 => Some((input.usize_value()?, input.u64()?)),
                            _ => return input.malformed("unknown open-address tag"),
                        };
                        let reading = SpanReading::restore(
                            SpanReadingSnapshot {
                                received,
                                suffix,
                                at,
                            },
                            &span.cells,
                        )?;
                        Some((kind, target, reading))
                    }
                    _ => return input.malformed("unknown open-relation tag"),
                };
                let (relation, reading) = relation
                    .map_or((None, SpanReading::new()), |(kind, target, reading)| {
                        (Some((kind, target)), reading)
                    });
                Some(OpenPart {
                    letter,
                    relation,
                    reading,
                })
            }
            _ => return input.malformed("unknown open-part tag"),
        };
        let part_count = input.len(8)?;
        if part_count != declaration.chart.channels() {
            return Err(AdmittedStageCheckpointError::Inconsistent);
        }
        let mut parts = Vec::with_capacity(part_count);
        for _ in 0..part_count {
            parts.push(input.u64()?);
        }
        let tick = input.u64()?;
        let passage = input.passage()?;
        let encoded_held = input.usize_value()?;
        let widest = input.usize_value()?;
        input.finish()?;
        declaration.passage = passage.clone();

        let mut targets = BTreeMap::new();
        declaration.relations = relations;
        for relation in &declaration.relations {
            *targets.entry(relation.target).or_insert(0u64) += 1;
        }
        validate_outer(
            &declaration,
            next,
            &spans,
            open.as_ref(),
            &parts,
            tick,
            held,
            encoded_held,
            widest,
            &targets,
        )?;
        declaration.next = next;
        declaration.spans = spans;
        declaration.targets = targets;
        declaration.open = open;
        declaration.parts = parts;
        declaration.tick = tick;
        declaration.passage = passage;
        declaration.held = held;
        declaration.widest = widest;
        Ok(declaration)
    }
}

fn fresh(egg: &AdmittedEgg) -> bool {
    egg.next == 0
        && egg.stage.readout.ticks == [0; 2]
        && egg.stage.readout.copies == 0
        && egg.stage.counts.is_empty()
        && egg.receipts.iter().all(|stage| {
            stage.readout.ticks == [0; 2] && stage.readout.copies == 0 && stage.counts.is_empty()
        })
        && egg.pointers.iter().all(|pointer| {
            pointer.readout.parts == 0
                && pointer.readout.held == 0
                && pointer.readout.code.factors() == 0
                && pointer.held.is_empty()
                && pointer.same.is_empty()
                && pointer.levels.is_empty()
                && pointer.previous.is_none()
        })
        && egg.spans.is_empty()
        && egg.open.is_none()
        && egg.parts.iter().all(|&count| count == 0)
        && egg.tick == 0
        && egg.passage.factors() == 0
        && egg.held == 0
        && egg.widest == 0
}

fn validate_outer(
    egg: &AdmittedEgg,
    next: usize,
    spans: &BTreeMap<u64, Span>,
    open: Option<&OpenPart>,
    parts: &[u64],
    tick: u64,
    held: usize,
    encoded_held: usize,
    widest: usize,
    targets: &BTreeMap<u64, u64>,
) -> Result<(), AdmittedStageCheckpointError> {
    let inconsistent = || AdmittedStageCheckpointError::Inconsistent;
    let part_total = parts
        .iter()
        .try_fold(0u64, |sum, &count| sum.checked_add(count))
        .ok_or_else(inconsistent)?;
    if next > egg.relations.len()
        || parts.len() != egg.chart.channels()
        || part_total > tick
        || !matches!(
            egg.inner.likelihood(),
            super::Likelihood::Enclosed(code) if code.factors() == tick
        )
        || egg.passage.factors() != tick
        || held != encoded_held
        || egg.pointers[RelationKind::Request.index()].readout.parts != parts[super::AGENT]
        || egg.pointers[RelationKind::LaterHuman.index()].readout.parts != parts[super::HUMAN]
    {
        return Err(inconsistent());
    }
    let mut held_cells = 0usize;
    for (&letter, span) in spans {
        let expected_remaining = egg.relations[next..]
            .iter()
            .filter(|relation| relation.target == letter)
            .count() as u64
            + if open.is_some_and(|open| open.relation.is_some_and(|(_, target)| target == letter))
            {
                1
            } else {
                0
            };
        if expected_remaining == 0
            || span.remaining != expected_remaining
            || span.ordinal >= parts[span.channel]
            || targets.get(&letter).copied().unwrap_or(0) < expected_remaining
        {
            return Err(inconsistent());
        }
        let expected_channel = egg
            .relations
            .iter()
            .filter(|relation| relation.target == letter)
            .map(|relation| relation.kind.channels().1)
            .next();
        if expected_channel != Some(span.channel) {
            return Err(inconsistent());
        }
        held_cells = held_cells
            .checked_add(span.cells.len())
            .ok_or_else(inconsistent)?;
    }
    if held_cells != held {
        return Err(inconsistent());
    }
    let section = egg.inner.clock().port().section;
    match (open, section) {
        (None, None) if tick == 0 => {}
        (Some(open), Some(section)) => {
            if open.letter >= tick
                || section.channel >= egg.chart.channels()
                || section.kind >= egg.chart.kinds()
            {
                return Err(inconsistent());
            }
            if let Some((kind, target)) = open.relation {
                let Some(relation) = next
                    .checked_sub(1)
                    .and_then(|index| egg.relations.get(index))
                else {
                    return Err(inconsistent());
                };
                let Some(span) = spans.get(&target) else {
                    return Err(inconsistent());
                };
                let (reader, target_channel) = kind.channels();
                if *relation
                    != (Relation {
                        letter: open.letter,
                        kind,
                        target,
                    })
                    || reader != section.channel
                    || target_channel != span.channel
                    || u64::try_from(open.reading.cells()).ok()
                        != Some(egg.inner.clock().port().phase)
                {
                    return Err(inconsistent());
                }
            }
            if held
                .checked_add(open.reading.cells())
                .ok_or_else(inconsistent)?
                > widest
            {
                return Err(inconsistent());
            }
        }
        _ => return Err(inconsistent()),
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::{
        Capacity, LandmarkDeclaration, SectionSlots, Sections, StopPrior,
    };
    use crate::receiver::population::TreeFamily;

    const POPULATION: u64 = 1 << 10;
    const GRAIN: u64 = 16;

    fn chart() -> crate::compression::landmark::context::SectionChart {
        crate::compression::landmark::context::SectionChart::curated()
    }

    fn letter(kind: usize, channel: usize) -> usize {
        chart()
            .letter(crate::compression::landmark::context::Section { kind, channel })
            .expect("a section letter")
    }

    fn inner() -> crate::receiver::population::BoundaryEgg {
        let chart = chart();
        let sections = Sections::new(chart.clone(), SectionSlots::Channel).unwrap();
        let bytes = TreeFamily::sectioned(
            LandmarkDeclaration {
                alphabet: chart.alphabet(),
                depth: 3,
                forced: 0,
                population: POPULATION,
                grain: GRAIN,
                family: sections.family().clone(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
            1,
            sections,
        )
        .unwrap();
        crate::receiver::population::BoundaryEgg::new(
            "boundary egg".into(),
            1,
            bytes,
            chart.clone(),
            LandmarkDeclaration {
                alphabet: chart.letters(),
                depth: 2,
                forced: 0,
                population: POPULATION,
                grain: GRAIN,
                family: crate::receiver::population::BoundaryEgg::letter_family(POPULATION)
                    .unwrap(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
        )
        .unwrap()
    }

    fn egg() -> AdmittedEgg {
        AdmittedEgg::new(
            "admitted receivers".into(),
            1,
            inner(),
            chart(),
            vec![Relation {
                letter: 4,
                kind: RelationKind::Request,
                target: 0,
            }],
            CopyLaw::new(1, 3, 2).unwrap(),
        )
        .unwrap()
    }

    fn receive(egg: &mut AdmittedEgg, cells: &[usize]) {
        for &cell in cells {
            egg.receive(cell).unwrap();
        }
    }

    #[test]
    fn copy_stage_restores_face_counts_and_accumulators_for_next_read() {
        let law = CopyLaw::new(2, 5, 4).unwrap();
        let mut stage = CopyStage::new(RelationKind::Request, law);
        for (length, next, cell) in [(2, 12, 12), (3, 14, 2), (7, 90, 90)] {
            let q = crate::ratio::Rat::new(1.into(), 256.into());
            stage
                .read(
                    crate::compression::landmark::context::Located { length, next },
                    &q,
                    &q,
                    cell,
                    false,
                )
                .unwrap();
        }
        let bytes = stage.encode_checkpoint();
        let mut restored =
            CopyStage::decode_checkpoint(RelationKind::Request, law, &bytes).unwrap();
        assert_eq!(restored, stage);
        assert_eq!(restored.encode_checkpoint(), bytes);
        let q = crate::ratio::Rat::new(1.into(), 256.into());
        let at = crate::compression::landmark::context::Located {
            length: 4,
            next: 31,
        };
        assert_eq!(
            stage.read(at, &q, &q, 31, true).unwrap(),
            restored.read(at, &q, &q, 31, true).unwrap()
        );
        assert_eq!(restored.encode_checkpoint(), stage.encode_checkpoint());
    }

    #[test]
    fn copy_stage_rejects_declaration_and_malformed_bytes() {
        let law = CopyLaw::new(2, 5, 4).unwrap();
        let stage = CopyStage::new(RelationKind::Request, law);
        let bytes = stage.encode_checkpoint();
        assert!(matches!(
            CopyStage::decode_checkpoint(RelationKind::LaterHuman, law, &bytes),
            Err(AdmittedStageCheckpointError::Declaration)
        ));
        assert!(matches!(
            CopyStage::decode_checkpoint(RelationKind::Request, law, &bytes[..bytes.len() - 1]),
            Err(AdmittedStageCheckpointError::Truncated { .. })
        ));
        let mut trailing = bytes;
        trailing.push(0);
        assert!(matches!(
            CopyStage::decode_checkpoint(RelationKind::Request, law, &trailing),
            Err(AdmittedStageCheckpointError::Trailing { .. })
        ));
    }

    #[test]
    fn pointer_code_restores_exact_online_state_and_next_pointer() {
        let mut pointer = PointerCode::new(RelationKind::Request);
        pointer.read(1, None).unwrap();
        pointer.read(1, Some((4, 0, 1))).unwrap();
        pointer.read(1, Some((4, 1, 2))).unwrap();
        pointer.read(2, Some((7, 0, 3))).unwrap();
        let bytes = pointer.encode_checkpoint();
        let mut restored =
            PointerCode::decode_checkpoint(RelationKind::Request, 4, &bytes).unwrap();
        assert_eq!(restored, pointer);
        assert_eq!(restored.encode_checkpoint(), bytes);
        pointer.read(2, Some((9, 3, 4))).unwrap();
        restored.read(2, Some((9, 3, 4))).unwrap();
        assert_eq!(restored, pointer);
        assert_eq!(restored.encode_checkpoint(), pointer.encode_checkpoint());
    }

    #[test]
    fn pointer_code_rejects_bad_tags_and_noncanonical_counts() {
        let pointer = PointerCode::new(RelationKind::LaterHuman);
        let bytes = pointer.encode_checkpoint();
        assert!(matches!(
            PointerCode::decode_checkpoint(RelationKind::Request, 4, &bytes),
            Err(AdmittedStageCheckpointError::Declaration)
        ));
        assert!(matches!(
            PointerCode::decode_checkpoint(RelationKind::LaterHuman, 4, &bytes[..bytes.len() - 1]),
            Err(AdmittedStageCheckpointError::Truncated { .. })
        ));
    }

    #[test]
    fn admitted_egg_restores_open_request_address_and_next_receive() {
        let mut original = egg();
        receive(
            &mut original,
            &[
                letter(0, 0),
                usize::from(b'a'),
                usize::from(b'b'),
                usize::from(b'c'),
                letter(2, 1),
                usize::from(b'a'),
            ],
        );
        let bytes = original.encode_checkpoint().unwrap();
        let mut restored = AdmittedEgg::decode_checkpoint(egg(), &bytes)
            .unwrap_or_else(|error| panic!("decode error: {error:?}"));
        assert_eq!(restored.encode_checkpoint().unwrap(), bytes);
        assert_eq!(restored.face().unwrap(), original.face().unwrap());
        for cell in [usize::from(b'b'), usize::from(b'c'), letter(3, 0)] {
            assert_eq!(
                restored.receive(cell).unwrap(),
                original.receive(cell).unwrap()
            );
            assert_eq!(restored.face().unwrap(), original.face().unwrap());
            assert_eq!(
                restored.encode_checkpoint().unwrap(),
                original.encode_checkpoint().unwrap()
            );
        }
    }

    #[test]
    fn admitted_egg_checkpoint_rejects_wrong_manifest_and_truncation() {
        let mut original = egg();
        receive(&mut original, &[letter(0, 0), usize::from(b'a')]);
        let bytes = original.encode_checkpoint().unwrap();
        let wrong = AdmittedEgg::new(
            "different".into(),
            1,
            inner(),
            chart(),
            vec![Relation {
                letter: 4,
                kind: RelationKind::Request,
                target: 0,
            }],
            CopyLaw::new(1, 3, 2).unwrap(),
        )
        .unwrap();
        assert!(matches!(
            AdmittedEgg::decode_checkpoint(wrong, &bytes),
            Err(AdmittedStageCheckpointError::Declaration)
        ));
        assert!(matches!(
            AdmittedEgg::decode_checkpoint(egg(), &bytes[..bytes.len() - 1]),
            Err(AdmittedStageCheckpointError::Truncated { .. })
        ));
    }

    #[test]
    fn admitted_egg_restores_a_committed_future_relation_from_its_pinned_base() {
        let mut original = egg();
        let planned = Relation {
            letter: 2,
            kind: RelationKind::LaterHuman,
            target: 1,
        };
        original.validate_planned_relation(planned).unwrap();
        original.commit_planned_relation(planned);
        let bytes = original.encode_checkpoint().unwrap();
        let restored = AdmittedEgg::decode_checkpoint(egg(), &bytes).unwrap();
        assert_eq!(restored.relations, original.relations);
        assert_eq!(restored.targets, original.targets);
        assert_eq!(restored.encode_checkpoint().unwrap(), bytes);
    }
}
