//! Canonical checkpoint for a declared population with tagged tree and admitted members.
//!
//! The immutable manifest supplies each tree's complete declaration, description, mass and
//! optional section chart. Admitted members supply a fresh pinned egg. The payload retains only
//! current member weights/likelihood owners and the population's cells and open section. Founding,
//! unsupported tags and evolved member state are refused until their owners have codecs.

use num_bigint::{BigInt, Sign};
use num_traits::Zero;
use std::io::{self, Write};
use thiserror::Error;

use super::{AdmittedEgg, Family, Population, PopulationError, TreeFamily};
use crate::compression::landmark::context::{
    ContextError, LandmarkDeclaration, SectionChart, SectionSlots, Sections,
};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;

const MAGIC: &[u8; 8] = b"HPOP\0\0\0\x01";

/// Exterior declaration needed to restore one tree member. Member order is significant.
#[derive(Clone, Debug)]
pub struct TreeMemberManifest {
    pub declaration: LandmarkDeclaration,
    pub description: u64,
    pub mass: Rat,
    pub sections: Option<(SectionChart, SectionSlots)>,
}

/// A caller-supplied fresh declaration for the outer request/response receiver.
#[derive(Clone)]
pub struct AdmittedMemberManifest {
    pub fresh: AdmittedEgg,
    pub description: u64,
    pub mass: Rat,
}

/// Explicit, ordered member tags accepted by the native population codec.
#[derive(Clone)]
pub enum PopulationMemberManifest {
    Tree(TreeMemberManifest),
    Admitted(AdmittedMemberManifest),
}

impl TreeMemberManifest {
    fn family(&self) -> Result<TreeFamily, PopulationCheckpointError> {
        match &self.sections {
            None => Ok(TreeFamily::new(self.declaration.clone(), self.description)?),
            Some((chart, slots)) => Ok(TreeFamily::sectioned(
                self.declaration.clone(),
                self.description,
                Sections::new(chart.clone(), *slots)?,
            )?),
        }
    }
}

impl PopulationMemberManifest {
    fn mass(&self) -> &Rat {
        match self {
            Self::Tree(tree) => &tree.mass,
            Self::Admitted(admitted) => &admitted.mass,
        }
    }
    fn description(&self) -> u64 {
        match self {
            Self::Tree(tree) => tree.description,
            Self::Admitted(admitted) => admitted.description,
        }
    }
}

#[derive(Debug, Error)]
pub enum PopulationCheckpointError {
    #[error("unsupported population checkpoint version")]
    Version,
    #[error("population checkpoint is truncated at byte {0}")]
    Truncated(usize),
    #[error("population checkpoint has trailing bytes at byte {0}")]
    Trailing(usize),
    #[error("malformed population checkpoint at byte {offset}: {reason}")]
    Malformed { offset: usize, reason: &'static str },
    #[error("population checkpoint does not match the supplied member manifest")]
    Manifest,
    #[error("population has founding or member state outside the supported tagged codec")]
    UnsupportedState,
    #[error("population family has no checkpoint codec for its declared tag")]
    UnsupportedFamily,
    #[error("checkpoint length does not fit the canonical wire integer")]
    LengthOverflow,
    #[error("writing population checkpoint failed: {0}")]
    Io(#[from] io::Error),
    #[error(transparent)]
    Population(#[from] PopulationError),
    #[error(transparent)]
    Context(#[from] ContextError),
    #[error(transparent)]
    Tree(#[from] super::families::TreeFamilyCheckpointError),
    #[error(transparent)]
    Admitted(#[from] super::admitted::AdmittedStageCheckpointError),
}

struct Writer<'a, W: Write> {
    output: &'a mut W,
}

impl<W: Write> Writer<'_, W> {
    fn raw(&mut self, bytes: &[u8]) -> Result<(), PopulationCheckpointError> {
        self.output.write_all(bytes)?;
        Ok(())
    }
    fn u8(&mut self, x: u8) -> Result<(), PopulationCheckpointError> {
        self.raw(&[x])
    }
    fn u64(&mut self, x: u64) -> Result<(), PopulationCheckpointError> {
        self.raw(&x.to_le_bytes())
    }
    fn usize(&mut self, x: usize) -> Result<(), PopulationCheckpointError> {
        self.u64(u64::try_from(x).map_err(|_| PopulationCheckpointError::LengthOverflow)?)
    }
    fn bytes(&mut self, x: &[u8]) -> Result<(), PopulationCheckpointError> {
        self.usize(x.len())?;
        self.raw(x)
    }
    fn integer(&mut self, x: &BigInt) -> Result<(), PopulationCheckpointError> {
        let (sign, magnitude) = x.to_bytes_le();
        self.u8(match sign {
            Sign::NoSign => 0,
            Sign::Plus => 1,
            Sign::Minus => 2,
        })?;
        self.bytes(&magnitude)
    }
    fn rat(&mut self, x: &Rat) -> Result<(), PopulationCheckpointError> {
        self.integer(x.numer())?;
        self.integer(x.denom())
    }
    fn interval(&mut self, x: &ExactInterval) -> Result<(), PopulationCheckpointError> {
        self.rat(&x.lower)?;
        self.rat(&x.upper)
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn malformed<T>(&self, reason: &'static str) -> Result<T, PopulationCheckpointError> {
        Err(PopulationCheckpointError::Malformed {
            offset: self.at,
            reason,
        })
    }
    fn take<const N: usize>(&mut self) -> Result<[u8; N], PopulationCheckpointError> {
        let end = self
            .at
            .checked_add(N)
            .ok_or(PopulationCheckpointError::Malformed {
                offset: self.at,
                reason: "length overflow",
            })?;
        let Some(slice) = self.bytes.get(self.at..end) else {
            return Err(PopulationCheckpointError::Truncated(self.at));
        };
        self.at = end;
        Ok(slice.try_into().expect("fixed-size slice"))
    }
    fn u8(&mut self) -> Result<u8, PopulationCheckpointError> {
        Ok(self.take::<1>()?[0])
    }
    fn u64(&mut self) -> Result<u64, PopulationCheckpointError> {
        Ok(u64::from_le_bytes(self.take()?))
    }
    fn usize(&mut self) -> Result<usize, PopulationCheckpointError> {
        let at = self.at;
        usize::try_from(self.u64()?).map_err(|_| PopulationCheckpointError::Malformed {
            offset: at,
            reason: "integer does not fit host",
        })
    }
    fn bytes(&mut self) -> Result<&[u8], PopulationCheckpointError> {
        let len = self.usize()?;
        let end = self
            .at
            .checked_add(len)
            .ok_or(PopulationCheckpointError::Malformed {
                offset: self.at,
                reason: "byte length overflow",
            })?;
        let Some(slice) = self.bytes.get(self.at..end) else {
            return Err(PopulationCheckpointError::Truncated(self.at));
        };
        self.at = end;
        Ok(slice)
    }
    fn integer(&mut self) -> Result<BigInt, PopulationCheckpointError> {
        let at = self.at;
        let sign = match self.u8()? {
            0 => Sign::NoSign,
            1 => Sign::Plus,
            2 => Sign::Minus,
            _ => return self.malformed("invalid integer sign"),
        };
        let magnitude = self.bytes()?;
        if magnitude.last() == Some(&0) || (magnitude.is_empty() != (sign == Sign::NoSign)) {
            return Err(PopulationCheckpointError::Malformed {
                offset: at,
                reason: "noncanonical integer",
            });
        }
        Ok(BigInt::from_bytes_le(sign, magnitude))
    }
    fn rat(&mut self) -> Result<Rat, PopulationCheckpointError> {
        let numerator = self.integer()?;
        let denominator = self.integer()?;
        if denominator <= BigInt::zero() {
            return self.malformed("nonpositive rational denominator");
        }
        let value = Rat::new(numerator.clone(), denominator.clone());
        if value.numer() != &numerator || value.denom() != &denominator {
            return self.malformed("noncanonical rational");
        }
        Ok(value)
    }
    fn interval(&mut self) -> Result<ExactInterval, PopulationCheckpointError> {
        let lower = self.rat()?;
        let upper = self.rat()?;
        ExactInterval::new(lower, upper).map_err(|_| PopulationCheckpointError::Malformed {
            offset: self.at,
            reason: "reversed interval",
        })
    }
}

impl Population {
    /// Encode only a non-founding population whose ordered members match this explicit tree manifest.
    /// `D(E(Θ))` reconstructs every tree directly from its own checkpoint, without source replay.
    pub fn encode_tree_checkpoint(
        &self,
        manifest: &[TreeMemberManifest],
    ) -> Result<Vec<u8>, PopulationCheckpointError> {
        let tagged: Vec<_> = manifest
            .iter()
            .cloned()
            .map(PopulationMemberManifest::Tree)
            .collect();
        self.encode_checkpoint(&tagged)
    }

    /// Encode a population whose ordered member tags match this pinned manifest.
    pub fn encode_checkpoint(
        &self,
        manifest: &[PopulationMemberManifest],
    ) -> Result<Vec<u8>, PopulationCheckpointError> {
        let mut bytes = Vec::new();
        self.write_checkpoint(manifest, &mut bytes)?;
        Ok(bytes)
    }

    /// Stream the canonical tagged population standing to `output`.
    ///
    /// The writer holds only the outer fixed fields and one owner's checkpoint bytes at a time;
    /// it does not accumulate the population payload. A validation or I/O refusal can leave a
    /// prefix in `output`, so callers needing atomicity must write to a staged destination.
    pub fn write_checkpoint<W: Write>(
        &self,
        manifest: &[PopulationMemberManifest],
        output: &mut W,
    ) -> Result<(), PopulationCheckpointError> {
        if self.founding.is_some()
            || self.members.len() != manifest.len()
            || self.mass != self.founded
        {
            return Err(PopulationCheckpointError::UnsupportedState);
        }
        let mut out = Writer { output };
        out.raw(MAGIC)?;
        out.usize(self.alphabet)?;
        out.usize(self.cells)?;
        out.rat(&self.mass)?;
        out.rat(&self.founded)?;
        match &self.section {
            Some(section) => {
                out.u8(1)?;
                out.interval(section)?;
            }
            None => out.u8(0)?,
        }
        out.usize(self.members.len())?;
        for (member, declared) in self.members.iter().zip(manifest) {
            let (tag, checkpoint) = match declared {
                PopulationMemberManifest::Tree(tree) => {
                    let expected = tree.family()?;
                    if member.family.declaration() != expected.declaration()
                        || member.family.tree_received_cells() != u64::try_from(self.cells).ok()
                    {
                        return Err(PopulationCheckpointError::Manifest);
                    }
                    (
                        1,
                        member
                            .family
                            .tree_checkpoint()
                            .ok_or(PopulationCheckpointError::UnsupportedFamily)?,
                    )
                }
                PopulationMemberManifest::Admitted(admitted) => {
                    if member.family.declaration() != admitted.fresh.declaration()
                        || member.family.alphabet() != admitted.fresh.alphabet()
                        || member.family.admitted_received_cells() != u64::try_from(self.cells).ok()
                    {
                        return Err(PopulationCheckpointError::Manifest);
                    }
                    let bytes = member
                        .family
                        .admitted_checkpoint()
                        .ok_or(PopulationCheckpointError::UnsupportedFamily)?
                        .map_err(PopulationCheckpointError::Admitted)?;
                    (2, bytes)
                }
            };
            if member.family.declaration().kind
                != match declared {
                    PopulationMemberManifest::Tree(_) => "receiving tree",
                    PopulationMemberManifest::Admitted(_) => "admitted receivers",
                }
                || member.family.description() != declared.description()
                || member.mass != *declared.mass()
                || member.prior != &member.mass / &self.mass
                || member.born != 0
                || member.inherited.is_some()
                || member.died.is_some()
                || member.reseeded
                || member.origin.is_some()
            {
                return Err(PopulationCheckpointError::UnsupportedState);
            }
            out.u8(tag)?;
            out.rat(&member.mass)?;
            out.rat(&member.prior)?;
            out.bytes(&checkpoint)?;
        }
        Ok(())
    }

    /// Restore a tree-only population from its exact current state and supplied immutable manifest.
    pub fn decode_tree_checkpoint(
        manifest: &[TreeMemberManifest],
        bytes: &[u8],
    ) -> Result<Self, PopulationCheckpointError> {
        let tagged: Vec<_> = manifest
            .iter()
            .cloned()
            .map(PopulationMemberManifest::Tree)
            .collect();
        Self::decode_checkpoint(&tagged, bytes)
    }

    /// Restore a tagged population using fresh, pinned owner declarations supplied by the caller.
    pub fn decode_checkpoint(
        manifest: &[PopulationMemberManifest],
        bytes: &[u8],
    ) -> Result<Self, PopulationCheckpointError> {
        if bytes.len() < MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
            return Err(PopulationCheckpointError::Version);
        }
        let mut input = Reader {
            bytes,
            at: MAGIC.len(),
        };
        let alphabet = input.usize()?;
        let cells = input.usize()?;
        let mass = input.rat()?;
        let founded = input.rat()?;
        if mass <= Rat::zero() {
            return Err(PopulationCheckpointError::Manifest);
        }
        let section = match input.u8()? {
            0 => None,
            1 => Some(input.interval()?),
            _ => return input.malformed("invalid section tag"),
        };
        let count = input.usize()?;
        if count != manifest.len() {
            return Err(PopulationCheckpointError::Manifest);
        }
        let mut families: Vec<Box<dyn Family>> = Vec::with_capacity(count);
        let mut masses = Vec::with_capacity(count);
        for declared in manifest {
            let tag = input.u8()?;
            let expected_tag = match declared {
                PopulationMemberManifest::Tree(_) => 1,
                PopulationMemberManifest::Admitted(_) => 2,
            };
            if tag != expected_tag {
                return Err(PopulationCheckpointError::Manifest);
            }
            let member_mass = input.rat()?;
            let prior = input.rat()?;
            if member_mass != *declared.mass() || prior != &member_mass / &mass {
                return Err(PopulationCheckpointError::Manifest);
            }
            let state = input.bytes()?;
            let family: Box<dyn Family> = match declared {
                PopulationMemberManifest::Tree(tree) => {
                    if tree.declaration.alphabet != alphabet {
                        return Err(PopulationCheckpointError::Manifest);
                    }
                    let expected = tree.family()?;
                    let restored = TreeFamily::decode_checkpoint(
                        tree.declaration.clone(),
                        tree.description,
                        tree.sections.clone(),
                        state,
                    )?;
                    if restored.declaration() != expected.declaration()
                        || restored.alphabet() != alphabet
                        || restored.tree_received_cells() != u64::try_from(cells).ok()
                    {
                        return Err(PopulationCheckpointError::Manifest);
                    }
                    Box::new(restored)
                }
                PopulationMemberManifest::Admitted(admitted) => {
                    if admitted.fresh.alphabet() != alphabet {
                        return Err(PopulationCheckpointError::Manifest);
                    }
                    let restored = AdmittedEgg::decode_checkpoint(admitted.fresh.clone(), state)?;
                    if restored.declaration() != admitted.fresh.declaration()
                        || restored.description() != admitted.description
                        || restored.alphabet() != alphabet
                        || restored.admitted_received_cells() != u64::try_from(cells).ok()
                    {
                        return Err(PopulationCheckpointError::Manifest);
                    }
                    Box::new(restored)
                }
            };
            families.push(family);
            masses.push(member_mass);
        }
        if input.at != bytes.len() {
            return Err(PopulationCheckpointError::Trailing(input.at));
        }
        if founded != mass {
            return Err(PopulationCheckpointError::UnsupportedState);
        }
        let mut population = Population::with_masses(families, masses)?;
        if population.alphabet != alphabet {
            return Err(PopulationCheckpointError::Manifest);
        }
        population.cells = cells;
        population.founded = founded;
        population.section = section;
        Ok(population)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compression::landmark::context::{
        Capacity, LandmarkDeclaration, LetterFamily, Section, SectionChart, SectionSlots, Sections,
        StopPrior,
    };
    use crate::receiver::population::{BoundaryEgg, CopyLaw, Relation};
    use num_bigint::BigInt;

    fn member(depth: usize, description: u64, mass: i64) -> TreeMemberManifest {
        TreeMemberManifest {
            declaration: LandmarkDeclaration {
                alphabet: 4,
                depth,
                forced: 1,
                population: 32,
                grain: 1,
                family: LetterFamily::cells(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
            description,
            mass: Rat::new(BigInt::from(mass), BigInt::from(8)),
            sections: None,
        }
    }

    fn admitted() -> AdmittedEgg {
        let chart = SectionChart::curated();
        let sections = Sections::new(chart.clone(), SectionSlots::Channel).unwrap();
        let bytes = TreeFamily::sectioned(
            LandmarkDeclaration {
                alphabet: chart.alphabet(),
                depth: 2,
                forced: 0,
                population: 32,
                grain: 1,
                family: sections.family().clone(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
            1,
            sections,
        )
        .unwrap();
        let inner = BoundaryEgg::new(
            "boundary".into(),
            1,
            bytes,
            chart.clone(),
            LandmarkDeclaration {
                alphabet: chart.letters(),
                depth: 2,
                forced: 0,
                population: 32,
                grain: 1,
                family: BoundaryEgg::letter_family(32).unwrap(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
        )
        .unwrap();
        AdmittedEgg::new(
            "admitted".into(),
            1,
            inner,
            chart,
            vec![Relation {
                letter: 4,
                kind: crate::receiver::population::RelationKind::Request,
                target: 0,
            }],
            CopyLaw::new(1, 2, 1).unwrap(),
        )
        .unwrap()
    }

    #[test]
    fn tree_population_checkpoint_preserves_next_face_receive_and_canonical_bytes() {
        let manifest = vec![member(2, 2, 2), member(3, 2, 2)];
        let mut original = Population::with_masses(
            manifest
                .iter()
                .map(|m| {
                    Box::new(TreeFamily::new(m.declaration.clone(), m.description).unwrap())
                        as Box<dyn Family>
                })
                .collect(),
            manifest.iter().map(|m| m.mass.clone()).collect(),
        )
        .unwrap();
        for cell in [1, 3, 0, 1, 1] {
            original.receive(cell).unwrap();
        }
        let encoded = original.encode_tree_checkpoint(&manifest).unwrap();
        let mut restored = Population::decode_tree_checkpoint(&manifest, &encoded).unwrap();
        assert_eq!(restored.encode_tree_checkpoint(&manifest).unwrap(), encoded);
        assert_eq!(restored.face().unwrap(), original.face().unwrap());
        for cell in [2, 1, 3] {
            assert_eq!(
                restored.receive(cell).unwrap(),
                original.receive(cell).unwrap()
            );
            assert_eq!(
                restored.encode_tree_checkpoint(&manifest).unwrap(),
                original.encode_tree_checkpoint(&manifest).unwrap()
            );
        }
    }

    #[test]
    fn tree_population_checkpoint_binds_manifest_and_rejects_malformed_bytes() {
        let manifest = vec![member(2, 2, 2)];
        let p = Population::with_masses(
            vec![Box::new(
                TreeFamily::new(manifest[0].declaration.clone(), 2).unwrap(),
            )],
            vec![manifest[0].mass.clone()],
        )
        .unwrap();
        let encoded = p.encode_tree_checkpoint(&manifest).unwrap();
        let mut wrong = manifest.clone();
        wrong[0].description += 1;
        assert!(Population::decode_tree_checkpoint(&wrong, &encoded).is_err());
        assert!(
            Population::decode_tree_checkpoint(&manifest, &encoded[..encoded.len() - 1]).is_err()
        );
        let mut trailing = encoded;
        trailing.push(0);
        assert!(Population::decode_tree_checkpoint(&manifest, &trailing).is_err());
    }

    #[test]
    fn mixed_tree_and_admitted_population_has_the_same_continuation_square() {
        let chart = SectionChart::curated();
        let tree = TreeMemberManifest {
            declaration: LandmarkDeclaration {
                alphabet: chart.alphabet(),
                depth: 3,
                forced: 0,
                population: 32,
                grain: 1,
                family: LetterFamily::cells(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
            description: 1,
            mass: Rat::new(BigInt::from(1), BigInt::from(4)),
            sections: None,
        };
        let admitted_manifest = AdmittedMemberManifest {
            fresh: admitted(),
            description: 1,
            mass: Rat::new(BigInt::from(1), BigInt::from(4)),
        };
        let manifest = vec![
            PopulationMemberManifest::Tree(tree.clone()),
            PopulationMemberManifest::Admitted(admitted_manifest.clone()),
        ];
        let mut original = Population::with_masses(
            vec![
                Box::new(TreeFamily::new(tree.declaration.clone(), tree.description).unwrap()),
                Box::new(admitted()),
            ],
            vec![tree.mass.clone(), admitted_manifest.mass.clone()],
        )
        .unwrap();
        let opening = chart
            .letter(Section {
                kind: 0,
                channel: 0,
            })
            .unwrap();
        let response = chart
            .letter(Section {
                kind: 2,
                channel: 1,
            })
            .unwrap();
        for cell in [
            opening,
            usize::from(b'a'),
            usize::from(b'b'),
            usize::from(b'c'),
            response,
            usize::from(b'a'),
        ] {
            original.receive(cell).unwrap();
        }
        let encoded = original.encode_checkpoint(&manifest).unwrap();
        let mut streamed = Vec::new();
        original.write_checkpoint(&manifest, &mut streamed).unwrap();
        assert_eq!(streamed, encoded);
        let mut restored = Population::decode_checkpoint(&manifest, &streamed).unwrap();
        assert_eq!(restored.face().unwrap(), original.face().unwrap());
        assert_eq!(restored.encode_checkpoint(&manifest).unwrap(), encoded);
        for cell in [usize::from(b'b'), usize::from(b'c')] {
            assert_eq!(
                restored.receive(cell).unwrap(),
                original.receive(cell).unwrap()
            );
            assert_eq!(restored.face().unwrap(), original.face().unwrap());
            assert_eq!(
                restored.encode_checkpoint(&manifest).unwrap(),
                original.encode_checkpoint(&manifest).unwrap()
            );
        }
    }

    #[test]
    fn mixed_population_refuses_unknown_tag_and_wrong_member_manifest() {
        let chart = SectionChart::curated();
        let tree = TreeMemberManifest {
            declaration: LandmarkDeclaration {
                alphabet: chart.alphabet(),
                depth: 2,
                forced: 0,
                population: 32,
                grain: 1,
                family: LetterFamily::cells(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
            description: 1,
            mass: Rat::new(BigInt::from(1), BigInt::from(4)),
            sections: None,
        };
        let admitted_manifest = AdmittedMemberManifest {
            fresh: admitted(),
            description: 1,
            mass: Rat::new(BigInt::from(1), BigInt::from(4)),
        };
        let manifest = vec![
            PopulationMemberManifest::Tree(tree.clone()),
            PopulationMemberManifest::Admitted(admitted_manifest.clone()),
        ];
        let population = Population::with_masses(
            vec![
                Box::new(TreeFamily::new(tree.declaration.clone(), 1).unwrap()),
                Box::new(admitted()),
            ],
            vec![tree.mass.clone(), admitted_manifest.mass.clone()],
        )
        .unwrap();
        let bytes = population.encode_checkpoint(&manifest).unwrap();
        let mut reader = Reader {
            bytes: &bytes,
            at: MAGIC.len(),
        };
        let _alphabet = reader.usize().unwrap();
        let _cells = reader.usize().unwrap();
        let _mass = reader.rat().unwrap();
        let _founded = reader.rat().unwrap();
        let _section = reader.u8().unwrap();
        let _count = reader.usize().unwrap();
        let _tag = reader.u8().unwrap();
        let _member_mass = reader.rat().unwrap();
        let _prior = reader.rat().unwrap();
        let _tree = reader.bytes().unwrap();
        let tag_offset = reader.at;
        let mut unknown_tag = bytes.clone();
        unknown_tag[tag_offset] = 255;
        assert!(Population::decode_checkpoint(&manifest, &unknown_tag).is_err());
        let wrong_order = vec![
            PopulationMemberManifest::Admitted(admitted_manifest),
            PopulationMemberManifest::Tree(tree),
        ];
        assert!(Population::decode_checkpoint(&wrong_order, &bytes).is_err());
        let mut wrong_description = manifest.clone();
        if let PopulationMemberManifest::Admitted(admitted) = &mut wrong_description[1] {
            admitted.description += 1;
        }
        assert!(Population::decode_checkpoint(&wrong_description, &bytes).is_err());
    }

    #[test]
    fn population_checkpoint_reports_sink_failure() {
        struct RefusingWriter;
        impl Write for RefusingWriter {
            fn write(&mut self, _bytes: &[u8]) -> io::Result<usize> {
                Err(io::Error::other("fixture sink refusal"))
            }
            fn flush(&mut self) -> io::Result<()> {
                Ok(())
            }
        }

        let manifest = vec![member(2, 2, 2)];
        let population = Population::with_masses(
            vec![Box::new(
                TreeFamily::new(manifest[0].declaration.clone(), manifest[0].description).unwrap(),
            )],
            vec![manifest[0].mass.clone()],
        )
        .unwrap();
        let tagged: Vec<_> = manifest
            .into_iter()
            .map(PopulationMemberManifest::Tree)
            .collect();
        assert!(matches!(
            population.write_checkpoint(&tagged, &mut RefusingWriter),
            Err(PopulationCheckpointError::Io(_))
        ));
    }
}
