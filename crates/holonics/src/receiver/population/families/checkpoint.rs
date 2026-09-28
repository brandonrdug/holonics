//! Canonical durable standing of a receiving tree family.
//!
//! The payload contains contemporary landmark state, the bounded causal address, the current
//! section reader state, and the passage-code accumulator. It never stores or replays the source
//! passage. The immutable tree declaration, family description, and optional section declaration
//! are supplied again at restoration and bound to the payload.

use super::TreeFamily;
use crate::compression::landmark::context::{
    ContextError, LandmarkDeclaration, Landmarks, Letter, PassageCode, PassageCodecError, Section,
    SectionChart, SectionSlots, Sections, StandingCodecError,
};
use thiserror::Error;

const MAGIC: &[u8; 8] = b"HTREE\0\0\x01";

/// A refusal to encode or restore a tree family's contemporary standing.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum TreeFamilyCheckpointError {
    #[error("unsupported tree-family checkpoint version")]
    Version,
    #[error("tree-family checkpoint is truncated at byte {offset}")]
    Truncated { offset: usize },
    #[error("tree-family checkpoint has trailing bytes at byte {offset}")]
    Trailing { offset: usize },
    #[error("malformed tree-family checkpoint at byte {offset}: {reason}")]
    Malformed { offset: usize, reason: &'static str },
    #[error("tree-family checkpoint does not match its declaration")]
    Declaration,
    #[error("tree-family checkpoint state is inconsistent")]
    Inconsistent,
    #[error(transparent)]
    Standing(#[from] StandingCodecError),
    #[error(transparent)]
    Passage(#[from] PassageCodecError),
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

    fn section_declaration(&mut self, sections: Option<&Sections>) {
        let Some(sections) = sections else {
            self.u8(0);
            return;
        };
        self.u8(1);
        self.len(sections.chart().bytes());
        self.len(sections.chart().channels());
        self.len(sections.chart().kinds());
        self.u8(match sections.slots() {
            SectionSlots::Channel => 0,
            SectionSlots::ChannelKind => 1,
        });
    }

    fn open(&mut self, open: Option<Section>) {
        match open {
            None => self.u8(0),
            Some(section) => {
                self.u8(1);
                self.len(section.kind);
                self.len(section.channel);
            }
        }
    }

    fn letter(&mut self, letter: Letter) {
        match letter {
            Letter::Boundary => self.u8(0),
            Letter::Cell(cell) => {
                self.u8(1);
                self.len(cell);
            }
            Letter::Bundle(bundle) => {
                self.u8(2);
                self.len(bundle.cell);
                self.u32(bundle.features);
            }
        }
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn malformed<T>(&self, reason: &'static str) -> Result<T, TreeFamilyCheckpointError> {
        Err(TreeFamilyCheckpointError::Malformed {
            offset: self.at,
            reason,
        })
    }

    fn take<const N: usize>(&mut self) -> Result<[u8; N], TreeFamilyCheckpointError> {
        let end = self
            .at
            .checked_add(N)
            .ok_or(TreeFamilyCheckpointError::Malformed {
                offset: self.at,
                reason: "length overflow",
            })?;
        let Some(slice) = self.bytes.get(self.at..end) else {
            return Err(TreeFamilyCheckpointError::Truncated { offset: self.at });
        };
        self.at = end;
        Ok(slice.try_into().expect("fixed-size slice"))
    }

    fn u8(&mut self) -> Result<u8, TreeFamilyCheckpointError> {
        Ok(self.take::<1>()?[0])
    }

    fn u32(&mut self) -> Result<u32, TreeFamilyCheckpointError> {
        Ok(u32::from_le_bytes(self.take()?))
    }

    fn u64(&mut self) -> Result<u64, TreeFamilyCheckpointError> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    fn usize_value(&mut self) -> Result<usize, TreeFamilyCheckpointError> {
        let at = self.at;
        usize::try_from(self.u64()?).map_err(|_| TreeFamilyCheckpointError::Malformed {
            offset: at,
            reason: "value does not fit this host",
        })
    }

    fn len(&mut self, minimum_item_bytes: usize) -> Result<usize, TreeFamilyCheckpointError> {
        let value = self.usize_value()?;
        if value > self.bytes.len().saturating_sub(self.at) / minimum_item_bytes.max(1) {
            return self.malformed("length exceeds remaining input");
        }
        Ok(value)
    }

    fn section_declaration(
        &mut self,
    ) -> Result<Option<(SectionChart, SectionSlots)>, TreeFamilyCheckpointError> {
        match self.u8()? {
            0 => Ok(None),
            1 => {
                let bytes = self.usize_value()?;
                let channels = self.usize_value()?;
                let kinds = self.usize_value()?;
                let slots = match self.u8()? {
                    0 => SectionSlots::Channel,
                    1 => SectionSlots::ChannelKind,
                    _ => return self.malformed("invalid section-slot tag"),
                };
                Ok(Some((SectionChart::new(bytes, channels, kinds)?, slots)))
            }
            _ => self.malformed("invalid section-declaration tag"),
        }
    }

    fn open(&mut self) -> Result<Option<Section>, TreeFamilyCheckpointError> {
        match self.u8()? {
            0 => Ok(None),
            1 => Ok(Some(Section {
                kind: self.usize_value()?,
                channel: self.usize_value()?,
            })),
            _ => self.malformed("invalid open-section tag"),
        }
    }

    fn letter(&mut self) -> Result<Letter, TreeFamilyCheckpointError> {
        match self.u8()? {
            0 => Ok(Letter::Boundary),
            1 => Ok(Letter::Cell(self.usize_value()?)),
            2 => Ok(Letter::Bundle(
                crate::compression::landmark::context::Bundle {
                    cell: self.usize_value()?,
                    features: self.u32()?,
                },
            )),
            _ => self.malformed("invalid address-letter tag"),
        }
    }
}

fn descriptor_matches(
    declaration: &LandmarkDeclaration,
    section_declaration: Option<(SectionChart, SectionSlots)>,
) -> bool {
    match section_declaration {
        None => declaration.family.is_empty(),
        Some((chart, slots)) => {
            declaration.alphabet == chart.alphabet()
                && Sections::new(chart, slots)
                    .is_ok_and(|sections| declaration.family == *sections.family())
        }
    }
}

impl TreeFamily {
    /// Encode the contemporary tree-family standing in canonical little-endian form.
    pub fn encode_checkpoint(&self) -> Vec<u8> {
        let mut writer = Writer(MAGIC.to_vec());
        writer.u64(self.description);
        let standing = self.tree.encode_standing();
        writer.len(standing.len());
        writer.0.extend_from_slice(&standing);
        writer.section_declaration(self.sections.as_ref());
        writer.open(self.sections.as_ref().and_then(Sections::open));
        writer.len(self.past.len());
        for &letter in &self.past {
            writer.letter(letter);
        }
        let passage = self.passage.encode_checkpoint();
        writer.len(passage.len());
        writer.0.extend_from_slice(&passage);
        writer.u64(self.received);
        writer.0
    }

    /// Restore directly from the durable standing, requiring the immutable tree and section
    /// declarations and description. `sections` supplies only chart and slot declarations; its
    /// incoming open section is deliberately ignored and restored from the payload.
    pub fn decode_checkpoint(
        declaration: LandmarkDeclaration,
        description: u64,
        sections: Option<(SectionChart, SectionSlots)>,
        bytes: &[u8],
    ) -> Result<Self, TreeFamilyCheckpointError> {
        if bytes.len() < MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
            return Err(TreeFamilyCheckpointError::Version);
        }
        if !descriptor_matches(&declaration, sections) {
            return Err(TreeFamilyCheckpointError::Declaration);
        }
        let mut reader = Reader {
            bytes,
            at: MAGIC.len(),
        };
        if reader.u64()? != description {
            return Err(TreeFamilyCheckpointError::Declaration);
        }
        let standing_len = reader.len(1)?;
        let standing_end =
            reader
                .at
                .checked_add(standing_len)
                .ok_or(TreeFamilyCheckpointError::Malformed {
                    offset: reader.at,
                    reason: "standing length overflow",
                })?;
        let standing = reader
            .bytes
            .get(reader.at..standing_end)
            .ok_or(TreeFamilyCheckpointError::Truncated { offset: reader.at })?;
        reader.at = standing_end;

        let wire_sections = reader.section_declaration()?;
        if wire_sections != sections {
            return Err(TreeFamilyCheckpointError::Declaration);
        }
        let open = reader.open()?;
        let past_len = reader.len(1)?;
        let mut past = Vec::with_capacity(past_len);
        for _ in 0..past_len {
            past.push(reader.letter()?);
        }
        let passage_len = reader.len(1)?;
        let passage_end =
            reader
                .at
                .checked_add(passage_len)
                .ok_or(TreeFamilyCheckpointError::Malformed {
                    offset: reader.at,
                    reason: "passage-code length overflow",
                })?;
        let passage_bytes = reader
            .bytes
            .get(reader.at..passage_end)
            .ok_or(TreeFamilyCheckpointError::Truncated { offset: reader.at })?;
        reader.at = passage_end;
        let received = reader.u64()?;
        if reader.at != bytes.len() {
            return Err(TreeFamilyCheckpointError::Trailing { offset: reader.at });
        }

        let tree = Landmarks::decode_standing(declaration.clone(), standing)?;
        let section_reader = match sections {
            None => {
                if open.is_some() || past.iter().any(|letter| !matches!(letter, Letter::Cell(_))) {
                    return Err(TreeFamilyCheckpointError::Inconsistent);
                }
                None
            }
            Some((chart, slots)) => {
                let mut section_reader = Sections::new(chart, slots)?;
                section_reader.restore_open(open)?;
                if past
                    .iter()
                    .any(|letter| !matches!(letter, Letter::Bundle(_)))
                {
                    return Err(TreeFamilyCheckpointError::Inconsistent);
                }
                Some(section_reader)
            }
        };
        let expected_past = usize::try_from(received)
            .map_or(declaration.depth, |count| count.min(declaration.depth));
        if received != tree.passed()
            || received > declaration.population
            || past.len() != expected_past
        {
            return Err(TreeFamilyCheckpointError::Inconsistent);
        }
        for letter in &past {
            match (letter, section_reader.as_ref()) {
                (Letter::Cell(cell), None) if *cell < declaration.alphabet => {}
                (Letter::Bundle(bundle), Some(sections)) => {
                    if bundle.cell >= declaration.alphabet
                        || u64::from(bundle.features) >= sections.family().codes()
                    {
                        return Err(TreeFamilyCheckpointError::Inconsistent);
                    }
                    if let Some(section) = sections.chart().section(bundle.cell) {
                        let mut probe = Sections::new(*sections.chart(), sections.slots())?;
                        probe.restore_open(Some(section))?;
                        if probe.letter_of(bundle.cell)? != *letter {
                            return Err(TreeFamilyCheckpointError::Inconsistent);
                        }
                    }
                }
                _ => return Err(TreeFamilyCheckpointError::Inconsistent),
            }
        }
        if received == 0 && open.is_some() {
            return Err(TreeFamilyCheckpointError::Inconsistent);
        }
        let passage = PassageCode::decode_checkpoint(passage_bytes)?;
        let mut fresh = match sections {
            None => TreeFamily::new(declaration, description)
                .map_err(|_| TreeFamilyCheckpointError::Declaration)?,
            Some((chart, slots)) => {
                TreeFamily::sectioned(declaration, description, Sections::new(chart, slots)?)
                    .map_err(|_| TreeFamilyCheckpointError::Declaration)?
            }
        };
        fresh.tree = tree;
        fresh.sections = section_reader;
        fresh.past = past.into();
        fresh.passage = passage;
        fresh.received = received;
        if fresh.encode_checkpoint() != bytes {
            return Err(TreeFamilyCheckpointError::Inconsistent);
        }
        Ok(fresh)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::{Capacity, StopPrior};
    use crate::receiver::population::{Family, Readout};

    const DESCRIPTION: u64 = 3;

    fn tree_declaration(
        alphabet: usize,
        family: crate::compression::landmark::context::LetterFamily,
    ) -> LandmarkDeclaration {
        LandmarkDeclaration {
            alphabet,
            depth: 3,
            forced: 0,
            population: 256,
            grain: 16,
            family,
            prior: StopPrior::half(),
            capacity: Capacity::Unbounded,
        }
    }

    fn assert_same_readings(left: &TreeFamily, right: &TreeFamily) {
        assert_eq!(left.face().unwrap(), right.face().unwrap());
        assert_eq!(left.likelihood(), right.likelihood());
        match (left.readout(), right.readout()) {
            (Readout::Standing(a), Readout::Standing(b)) => assert_eq!(a, b),
            _ => panic!("tree families expose landmark standing readouts"),
        }
    }

    fn continuation(
        family: &TreeFamily,
        declaration: LandmarkDeclaration,
        sections: Option<(SectionChart, SectionSlots)>,
        next: usize,
    ) {
        let bytes = family.encode_checkpoint();
        let mut restored =
            TreeFamily::decode_checkpoint(declaration, DESCRIPTION, sections, &bytes).unwrap();
        assert_eq!(restored.encode_checkpoint(), bytes);
        assert_same_readings(family, &restored);
        let mut expected = family.clone();
        assert_eq!(
            expected.receive(next).unwrap(),
            restored.receive(next).unwrap()
        );
        assert_same_readings(&expected, &restored);
        assert_eq!(restored.encode_checkpoint(), expected.encode_checkpoint());
    }

    #[test]
    fn cell_tree_checkpoint_restores_standing_and_identical_next_receive() {
        let declaration = tree_declaration(4, Default::default());
        let mut family = TreeFamily::new(declaration.clone(), DESCRIPTION).unwrap();
        family.receive(1).unwrap();
        family.receive(3).unwrap();
        continuation(&family, declaration, None, 0);
    }

    #[test]
    fn sectioned_tree_checkpoint_restores_open_part_and_identical_continuation() {
        let chart = SectionChart::curated();
        let slots = SectionSlots::ChannelKind;
        let sections = Sections::new(chart, slots).unwrap();
        let declaration = tree_declaration(chart.alphabet(), sections.family().clone());
        let mut family = TreeFamily::sectioned(declaration.clone(), DESCRIPTION, sections).unwrap();
        let section = chart
            .letter(Section {
                kind: 2,
                channel: 1,
            })
            .unwrap();
        family.receive(section).unwrap();
        family.receive(usize::from(b'h')).unwrap();
        family.receive(usize::from(b'i')).unwrap();
        continuation(
            &family,
            declaration,
            Some((chart, slots)),
            usize::from(b'!'),
        );
    }

    #[test]
    fn tree_family_checkpoint_refuses_truncation_and_declaration_mismatch() {
        let declaration = tree_declaration(2, Default::default());
        let family = TreeFamily::new(declaration.clone(), DESCRIPTION).unwrap();
        let bytes = family.encode_checkpoint();
        assert!(matches!(
            TreeFamily::decode_checkpoint(
                declaration.clone(),
                DESCRIPTION,
                None,
                &bytes[..bytes.len() - 1]
            ),
            Err(TreeFamilyCheckpointError::Truncated { .. })
        ));
        let standing_len = u64::from_le_bytes(bytes[16..24].try_into().unwrap()) as usize;
        let section_tag = 24 + standing_len;
        let mut malformed = bytes.clone();
        malformed[section_tag] = 3;
        assert!(matches!(
            TreeFamily::decode_checkpoint(declaration.clone(), DESCRIPTION, None, &malformed),
            Err(TreeFamilyCheckpointError::Malformed { .. })
        ));
        assert!(matches!(
            TreeFamily::decode_checkpoint(declaration.clone(), DESCRIPTION + 1, None, &bytes),
            Err(TreeFamilyCheckpointError::Declaration)
        ));
        let incompatible = tree_declaration(4, Default::default());
        assert!(TreeFamily::decode_checkpoint(incompatible, DESCRIPTION, None, &bytes).is_err());
    }
}
