//! Condensation and seal: SKE4's owner, at the role grain.
//!
//! The excited resident realization is admitted as a `SoulkillerDismantlingInput`: the apparatus
//! (the source-neutral operator ecology and the cold witness that locates its coefficients) with
//! the declared family's exposures as the card returned them (faces, exact digests) and the cones
//! the family's declared withdrawals founded (`operative_roles.rs`: every contraction population
//! a role, a query population a role per head, ordered by the excitation and bisected jointly
//! over the exposures of a class and of the family).  What crosses `soulkiller::dismantle` is one
//! return of three lanes.  The productive lane is the cone-restricted ecology: the operator
//! graph, one class ecology per signature class (its signature, its retained occurrences as the
//! preimage fibre, its founded cone, its receiver-indexed response, and its remainder), and the
//! exact dyadic cross-sections restricted to the extent of the family: every contraction
//! population keeps the rows in the union of the class cones, a population read by a lookup keeps
//! the rows the family addressed, and every population that is not a site (gains, scalars) is
//! carried whole.  No source name, offset, executor, or the resident realization itself is in
//! that lane.  The cold witness carries the source ordinals and offsets and the excitation and
//! intervention testimony.  The insufficiency is the complement of the extent per population and
//! the declared boundary of the family: an occurrence or history outside it returns this lane,
//! never a face.
//!
//! The remainder is exhibited, never a number (`canon/TABLET_THE_COMPRESSION.md`, `H.0420`,
//! `H.0480`): the collapsed pairs between the class body and the full operator over the declared
//! exposures, each with the shortest declared history that separates it under the full
//! operator, and the enclosure the terminal reactions propagate to every coordinate of the face
//! when the receiver reads it unsealed.  The return states its species by that remainder: a
//! rebase when nothing is collapsed and the propagated remainder is every coordinate a point, a
//! condensation when nothing is collapsed and the propagated remainder is exhibited as its
//! certificate, a compression otherwise, with the collapsed population as the remainder.
//!
//! A class ecology is a lens and shortcut, graded as a lift (`FaithfulLocalSectionLift`): its
//! quotient is the stored presentation, every declared generator word and receiver history
//! descends exactly when its face under the lens equals the full operator's, and a receiver
//! outside the family obstructs descent (the insufficiency lane).  It is not the compression;
//! the compression law applies to the composed variant (SKE5).
//!
//! Formal owners composed: `HolonicExcitationFoundedQuotient.ExcitationFoundedReturn`,
//! `IsConeUnder`/`FoundedCone`, `DeclaredFamily.extent`/`insufficiency`,
//! `HolonicIntelligenceLifecycle.DismantlingReturn`,
//! `NativeMorphologyVariant.FaithfulLocalSectionLift.preimageFibre`.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs::File,
    io::{BufReader, BufWriter, Read, Write},
    os::unix::fs::FileExt,
    path::Path,
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::soulkiller::{SoulkillerDismantlingInput, SoulkillerDismantlingReturn};

use super::{
    NativeCoefficientIntake, NativeExposure, NativeExposureFace, NativeFullOperatorColdWitness,
    NativeFullOperatorDismantlingReturn, NativeFullOperatorEcology, NativeIdentificationError,
    NativeOperationPrimitive, NativeOperatorResidenceError, NativeSignature,
    NativeSignatureQuotient, NativeSiteBitmask,
};

pub const NATIVE_CONE_RESTRICTED_ECOLOGY_SCHEMA: &str =
    "holonic-engine.native-cone-restricted-ecology.v1";
pub const NATIVE_FAMILY_INSUFFICIENCY_SCHEMA: &str = "holonic-engine.native-family-insufficiency.v1";
const REST_MAGIC: &[u8; 32] = b"HOLONIC-CONE-RESTRICTED-ECOLOGY\n";

/// How one coefficient population is restricted in the productive lane.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeRestriction {
    /// A contraction population: rows in the extent of the family's cones, and, when a lookup
    /// also reads it, the rows the family addressed.
    Sites,
    /// A population read only by lookups: the rows the family addressed.
    Addressed,
    /// Not a site: carried whole.
    Whole,
}

/// One exact dyadic cross-section restricted to its retained rows.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeRestrictedCrossSection {
    pub population: u32,
    pub restriction: NativeRestriction,
    pub rows: usize,
    pub dim: usize,
    /// Ascending row ordinals retained; `words` holds `retained_rows.len() * dim` codewords.
    pub retained_rows: Vec<u32>,
    #[serde(skip)]
    pub words: Vec<u16>,
}

/// One retained occurrence of a class: the preimage fibre.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeRetainedOccurrence {
    pub occurrence: usize,
    pub addresses: Vec<u32>,
}

/// The class's receiver-indexed response: its face at one declared exposure.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeReceiverResponse {
    pub exposure: NativeExposure,
    pub face: u32,
    pub exact_digest: String,
}

/// One collapsed pair: two occurrences of the family the class body identifies at some declared
/// exposure where the full operator separates them, with the shortest declared history that
/// separates them under the full operator.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeCollapsedPair {
    pub left: usize,
    pub right: usize,
    pub exposure: NativeExposure,
    pub lens_face: u32,
    pub full_faces: (u32, u32),
    pub separating_word: Vec<u32>,
}

/// The enclosure the terminal reactions propagate to the face's coordinates under one exposure,
/// read at the receiver unsealed: how many coordinates are not points and the widest, with the
/// per-coordinate widths carried beside the receipt as octets.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeTerminalRemainder {
    pub exposure: NativeExposure,
    pub occurrence: usize,
    pub coordinates: usize,
    pub nonpoint_coordinates: usize,
    pub widest_grains: u64,
    pub grain: u32,
    /// Histogram of widths in grains: (width, coordinates with it), ascending.
    pub widths: Vec<(u64, usize)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeRemainderSpecies {
    /// Nothing collapsed, every coordinate of the face a point under every exposure.
    Rebase,
    /// Nothing collapsed; the propagated remainder is the certificate.
    Condensation,
    /// Pairs collapsed: the class body is a quotient with that population as its remainder.
    Compression,
}

/// The remainder of one class body against the full operator, exhibited.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeClassRemainder {
    /// The faces the class body returned for every occurrence of the family at every declared
    /// exposure, beside the full operator's.
    pub lens_faces: Vec<(usize, NativeExposure, u32, u32)>,
    pub collapsed: Vec<NativeCollapsedPair>,
    /// Member exposures whose face under the lens differed from the full operator's: the class
    /// body's own descent failures (the lift obligation refused for that word).
    pub member_faces_changed: Vec<(usize, NativeExposure, u32, u32)>,
    pub propagated: Vec<NativeTerminalRemainder>,
    pub species: NativeRemainderSpecies,
}

impl NativeClassRemainder {
    /// The species by the remainder alone.
    pub fn species_of(collapsed: &[NativeCollapsedPair], propagated: &[NativeTerminalRemainder]) -> NativeRemainderSpecies {
        if !collapsed.is_empty() {
            NativeRemainderSpecies::Compression
        } else if propagated.iter().all(|remainder| remainder.nonpoint_coordinates == 0) {
            NativeRemainderSpecies::Rebase
        } else {
            NativeRemainderSpecies::Condensation
        }
    }

    /// The collapsed pairs between lens faces and full faces over the declared exposures: for
    /// every exposure, every pair of occurrences with equal lens faces and different full faces.
    /// The separating word is the shortest declared history at which the full faces differ.
    pub fn collapsed_pairs(
        lens_faces: &[(usize, NativeExposure, u32, u32)],
    ) -> Vec<NativeCollapsedPair> {
        let mut exposures: Vec<&NativeExposure> = lens_faces.iter().map(|(_, e, _, _)| e).collect();
        exposures.sort();
        exposures.dedup();
        let full_face = |occurrence: usize, exposure: &NativeExposure| -> Option<u32> {
            lens_faces
                .iter()
                .find(|(o, e, _, _)| *o == occurrence && e == exposure)
                .map(|(_, _, _, full)| *full)
        };
        let mut collapsed = Vec::new();
        for exposure in &exposures {
            let at: Vec<&(usize, NativeExposure, u32, u32)> =
                lens_faces.iter().filter(|(_, e, _, _)| e == *exposure).collect();
            for (i, left) in at.iter().enumerate() {
                for right in &at[i + 1..] {
                    if left.2 == right.2 && left.3 != right.3 {
                        let separating_word = exposures
                            .iter()
                            .filter(|candidate| {
                                match (full_face(left.0, candidate), full_face(right.0, candidate)) {
                                    (Some(a), Some(b)) => a != b,
                                    _ => false,
                                }
                            })
                            .map(|candidate| candidate.history.clone())
                            .min_by_key(Vec::len)
                            .unwrap_or_default();
                        collapsed.push(NativeCollapsedPair {
                            left: left.0,
                            right: right.0,
                            exposure: (*exposure).clone(),
                            lens_face: left.2,
                            full_faces: (left.3, right.3),
                            separating_word,
                        });
                    }
                }
            }
        }
        collapsed
    }
}

/// One class ecology: the recurring structure the family revealed, restricted to its cone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeClassEcology {
    pub ordinal: usize,
    pub signature: NativeSignature,
    pub fibre: Vec<NativeRetainedOccurrence>,
    pub cone: BTreeMap<u32, NativeSiteBitmask>,
    pub cone_population: usize,
    pub response: Vec<NativeReceiverResponse>,
    pub remainder: NativeClassRemainder,
}

/// The productive lane: the cone-restricted ecology of the declared family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeConeRestrictedEcology {
    pub schema: String,
    pub ecology: NativeFullOperatorEcology,
    pub histories: Vec<Vec<u32>>,
    pub classes: Vec<NativeClassEcology>,
    pub extent: BTreeMap<u32, NativeSiteBitmask>,
    pub sites: usize,
    pub extent_population: usize,
    pub cross_sections: Vec<NativeRestrictedCrossSection>,
}

/// The testimony of one exposure's excitation and intervention, carried in the cold witness.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeExposureTestimony {
    pub occurrence: usize,
    pub history: Vec<u32>,
    pub face: u32,
    pub exact_digest: String,
    pub cone_population: usize,
    pub complement_unchanged: bool,
    pub cone_changed: bool,
    pub probes: usize,
    pub monotone: bool,
}

/// The cold lane: where the coefficients came from, and what excited and intervened.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeExcitationColdWitness {
    pub source: NativeFullOperatorColdWitness,
    pub exposures: Vec<NativeExposureTestimony>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeInsufficiencyCause {
    OccurrenceOutsideFamily { addresses: Vec<u32> },
    HistoryUndeclared { history: Vec<u32> },
}

/// The insufficiency lane: what the family did not excite, and its declared boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeFamilyInsufficiency {
    pub schema: String,
    pub insufficiency: BTreeMap<u32, NativeSiteBitmask>,
    pub insufficiency_population: usize,
    pub declared_histories: Vec<Vec<u32>>,
    pub retained_occurrences: Vec<Vec<u32>>,
    pub cause: Option<NativeInsufficiencyCause>,
}

#[derive(Debug, thiserror::Error)]
pub enum NativeCondensationError {
    #[error("identification: {0}")]
    Identification(#[from] NativeIdentificationError),
    #[error("the family's fibre lacks occurrence {0}")]
    Fibre(usize),
    #[error("population {0} is not a matrix the cones can restrict")]
    Population(u32),
    #[error("source I/O: {0}")]
    Io(String),
    #[error("the rest is malformed: {0}")]
    Rest(String),
}

/// One class cone founded jointly over the class's exposures within the family cone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeFoundedClassCone {
    pub occurrences: Vec<usize>,
    pub cone: BTreeMap<u32, NativeSiteBitmask>,
}

/// The cones founded jointly by intervention: the family cone (the extent) and every class cone
/// within it.  Unions of single-exposure cones are not cones and do not enter here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeFoundedCones {
    pub extent: BTreeMap<u32, NativeSiteBitmask>,
    pub classes: Vec<NativeFoundedClassCone>,
}

/// The excited resident realization admitted for dismantling.
pub struct ResidentExcitationDismantling {
    pub realization: NativeFullOperatorDismantlingReturn,
    pub faces: Vec<NativeExposureFace>,
    pub fibre: Vec<NativeRetainedOccurrence>,
    pub histories: Vec<Vec<u32>>,
    pub testimony: Vec<NativeExposureTestimony>,
    pub founded: NativeFoundedCones,
    /// One remainder per founded class cone, in the order of `founded.classes`.
    pub remainders: Vec<NativeClassRemainder>,
}

impl SoulkillerDismantlingInput for ResidentExcitationDismantling {
    type Productive = NativeConeRestrictedEcology;
    type ColdWitness = NativeExcitationColdWitness;
    type Insufficiency = NativeFamilyInsufficiency;
    type Error = NativeCondensationError;

    fn dismantle(
        self,
    ) -> Result<
        SoulkillerDismantlingReturn<Self::Productive, Self::ColdWitness, Self::Insufficiency>,
        Self::Error,
    > {
        let quotient = NativeSignatureQuotient::found(&self.faces)?;
        let ecology = self.realization.native;
        let witness = self.realization.exterior;
        let addressed = |occurrences: &[usize]| -> BTreeSet<u32> {
            let mut rows = BTreeSet::new();
            for occurrence in occurrences {
                if let Some(retained) = self.fibre.iter().find(|r| r.occurrence == *occurrence) {
                    rows.extend(retained.addresses.iter().copied());
                }
            }
            for history in &self.histories {
                rows.extend(history.iter().copied());
            }
            rows
        };
        let mut classes = Vec::with_capacity(quotient.classes.len());
        for class in &quotient.classes {
            let fibre = class
                .occurrences
                .iter()
                .map(|occurrence| {
                    self.fibre
                        .iter()
                        .find(|r| r.occurrence == *occurrence)
                        .cloned()
                        .ok_or(NativeCondensationError::Fibre(*occurrence))
                })
                .collect::<Result<Vec<_>, _>>()?;
            let member = class.occurrences[0];
            let response = quotient
                .exposures
                .iter()
                .filter_map(|exposure| {
                    self.faces
                        .iter()
                        .find(|f| f.occurrence == member && &f.exposure == exposure)
                        .map(|f| NativeReceiverResponse {
                            exposure: exposure.clone(),
                            face: f.face,
                            exact_digest: f.exact_digest.clone(),
                        })
                })
                .collect();
            let (founded_at, founded) = self
                .founded
                .classes
                .iter()
                .enumerate()
                .find(|(_, c)| c.occurrences == class.occurrences)
                .ok_or_else(|| NativeCondensationError::Rest(format!("no founded cone for class {}", class.ordinal)))?;
            let remainder = self
                .remainders
                .get(founded_at)
                .cloned()
                .ok_or_else(|| NativeCondensationError::Rest(format!("no remainder for class {}", class.ordinal)))?;
            classes.push(NativeClassEcology {
                ordinal: class.ordinal,
                signature: class.signature.clone(),
                fibre,
                cone_population: founded.cone.values().map(NativeSiteBitmask::population).sum(),
                cone: founded.cone.clone(),
                response,
                remainder,
            });
        }
        let extent = self.founded.extent.clone();
        let extent_population: usize = extent.values().map(NativeSiteBitmask::population).sum();
        let all_occurrences: Vec<usize> = self.fibre.iter().map(|r| r.occurrence).collect();
        let family_rows = addressed(&all_occurrences);
        let restrictions = restrictions_of(&ecology);
        let source = File::open(Path::new(&witness.source_container))
            .map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        let mut cross_sections = Vec::with_capacity(ecology.coefficient_populations.len());
        for population in &ecology.coefficient_populations {
            let ordinal = population.ordinal.0;
            let restriction = restrictions
                .get(&ordinal)
                .copied()
                .unwrap_or(NativeRestriction::Whole);
            let (rows, dim) = match population.shape.as_slice() {
                [extent] => (1usize, *extent),
                [rows, dim] => (*rows, *dim),
                _ => return Err(NativeCondensationError::Population(ordinal)),
            };
            let retained_rows: Vec<u32> = match restriction {
                NativeRestriction::Whole => (0..rows as u32).collect(),
                NativeRestriction::Addressed => family_rows
                    .iter()
                    .copied()
                    .filter(|row| (*row as usize) < rows)
                    .collect(),
                NativeRestriction::Sites => {
                    let mut retained: BTreeSet<u32> = extent
                        .get(&ordinal)
                        .map(|mask| {
                            mask.to_sites()
                                .iter()
                                .enumerate()
                                .filter(|(_, site)| **site)
                                .map(|(row, _)| row as u32)
                                .collect()
                        })
                        .unwrap_or_default();
                    if lookup_reads(&ecology, population.ordinal) {
                        retained.extend(family_rows.iter().copied().filter(|row| (*row as usize) < rows));
                    }
                    retained.into_iter().collect()
                }
            };
            let cold = witness
                .populations
                .get(ordinal as usize)
                .ok_or(NativeCondensationError::Population(ordinal))?;
            let mut words = Vec::with_capacity(retained_rows.len() * dim);
            let mut buffer = vec![0u8; dim * 2];
            for row in &retained_rows {
                let at = witness.payload_base + cold.source_start + (*row as u64) * (dim as u64) * 2;
                source
                    .read_exact_at(&mut buffer, at)
                    .map_err(|error| NativeCondensationError::Io(error.to_string()))?;
                words.extend(buffer.chunks_exact(2).map(|pair| u16::from_le_bytes([pair[0], pair[1]])));
            }
            cross_sections.push(NativeRestrictedCrossSection {
                population: ordinal,
                restriction,
                rows,
                dim,
                retained_rows,
                words,
            });
        }
        let productive = NativeConeRestrictedEcology {
            schema: NATIVE_CONE_RESTRICTED_ECOLOGY_SCHEMA.to_owned(),
            ecology,
            histories: self.histories.clone(),
            classes,
            sites: quotient.sites,
            extent_population,
            extent: extent.clone(),
            cross_sections,
        };
        let insufficiency = NativeFamilyInsufficiency {
            schema: NATIVE_FAMILY_INSUFFICIENCY_SCHEMA.to_owned(),
            insufficiency: extent
                .iter()
                .map(|(population, mask)| {
                    let complement: Vec<bool> = mask.to_sites().iter().map(|site| !site).collect();
                    (*population, NativeSiteBitmask::from_sites(&complement))
                })
                .collect(),
            insufficiency_population: quotient.sites - extent_population,
            declared_histories: self.histories,
            retained_occurrences: self.fibre.iter().map(|r| r.addresses.clone()).collect(),
            cause: None,
        };
        Ok(SoulkillerDismantlingReturn {
            native: productive,
            exterior: NativeExcitationColdWitness {
                source: witness,
                exposures: self.testimony,
            },
            insufficiency,
        })
    }
}

/// Which populations are sites (contraction cross-sections) and which are only addressed.
fn restrictions_of(ecology: &NativeFullOperatorEcology) -> BTreeMap<u32, NativeRestriction> {
    let mut restrictions = BTreeMap::new();
    // The receiver's own population: the terminal contraction's, which the family's cones
    // never restrict (it is not a role), is carried whole.
    let terminal_start = ecology.operations.len().saturating_sub(5);
    let receiver: Option<u32> = ecology
        .operations
        .get(terminal_start)
        .filter(|operation| matches!(operation.primitive, NativeOperationPrimitive::Contract))
        .and_then(|operation| operation.coefficients.first().map(|p| p.0));
    if let Some(receiver) = receiver {
        restrictions.insert(receiver, NativeRestriction::Whole);
    }
    for operation in &ecology.operations {
        match operation.primitive {
            NativeOperationPrimitive::Contract => {
                if let Some(population) = operation.coefficients.first() {
                    if Some(population.0) != receiver {
                        restrictions.insert(population.0, NativeRestriction::Sites);
                    }
                }
            }
            NativeOperationPrimitive::Lookup { .. } => {
                if let Some(population) = operation.coefficients.first() {
                    restrictions
                        .entry(population.0)
                        .or_insert(NativeRestriction::Addressed);
                }
            }
            _ => {}
        }
    }
    restrictions
}

fn lookup_reads(ecology: &NativeFullOperatorEcology, population: super::NativeTensorOrdinal) -> bool {
    ecology.operations.iter().any(|operation| {
        matches!(operation.primitive, NativeOperationPrimitive::Lookup { .. })
            && operation.coefficients.first() == Some(&population)
    })
}

impl NativeConeRestrictedEcology {
    pub fn validate(&self) -> Result<(), NativeCondensationError> {
        if self.schema != NATIVE_CONE_RESTRICTED_ECOLOGY_SCHEMA {
            return Err(NativeCondensationError::Rest("schema".to_owned()));
        }
        self.ecology
            .validate()
            .map_err(|error| NativeCondensationError::Rest(error.to_string()))?;
        if self.cross_sections.len() != self.ecology.coefficient_populations.len() {
            return Err(NativeCondensationError::Rest("cross-section population".to_owned()));
        }
        for (at, section) in self.cross_sections.iter().enumerate() {
            let population = &self.ecology.coefficient_populations[at];
            let expected_rows = population.shape.first().copied().unwrap_or(0);
            let (rows, dim) = match population.shape.as_slice() {
                [extent] => (1usize, *extent),
                [rows, dim] => (*rows, *dim),
                _ => return Err(NativeCondensationError::Population(at as u32)),
            };
            if section.population != at as u32
                || section.rows != rows
                || section.dim != dim
                || section.words.len() != section.retained_rows.len() * dim
                || section.retained_rows.windows(2).any(|pair| pair[0] >= pair[1])
                || section.retained_rows.last().is_some_and(|row| *row as usize >= rows.max(expected_rows.min(rows)))
            {
                return Err(NativeCondensationError::Rest(format!("cross-section {at}")));
            }
        }
        Ok(())
    }

    /// The class an occurrence belongs to, by its retained addresses.
    pub fn class_of(&self, addresses: &[u32]) -> Option<&NativeClassEcology> {
        self.classes
            .iter()
            .find(|class| class.fibre.iter().any(|retained| retained.addresses == addresses))
    }

    /// Admit one exposure: an occurrence of the family under a declared history, or the
    /// insufficiency lane, never a face.
    pub fn admit(
        &self,
        addresses: &[u32],
        history: &[u32],
    ) -> Result<&NativeClassEcology, NativeFamilyInsufficiency> {
        let refuse = |cause: NativeInsufficiencyCause| NativeFamilyInsufficiency {
            schema: NATIVE_FAMILY_INSUFFICIENCY_SCHEMA.to_owned(),
            insufficiency: self
                .extent
                .iter()
                .map(|(population, mask)| {
                    let complement: Vec<bool> = mask.to_sites().iter().map(|site| !site).collect();
                    (*population, NativeSiteBitmask::from_sites(&complement))
                })
                .collect(),
            insufficiency_population: self.sites - self.extent_population,
            declared_histories: self.histories.clone(),
            retained_occurrences: self
                .classes
                .iter()
                .flat_map(|class| class.fibre.iter().map(|r| r.addresses.clone()))
                .collect(),
            cause: Some(cause),
        };
        let class = self.class_of(addresses).ok_or_else(|| {
            refuse(NativeInsufficiencyCause::OccurrenceOutsideFamily {
                addresses: addresses.to_vec(),
            })
        })?;
        if !self.histories.iter().any(|declared| declared == history) {
            return Err(refuse(NativeInsufficiencyCause::HistoryUndeclared {
                history: history.to_vec(),
            }));
        }
        Ok(class)
    }

    /// The rows a class keeps of one population: its cone (with the rows it addressed when a
    /// lookup reads the population), the rows it addressed, or the whole population.
    pub fn class_rows(&self, class: &NativeClassEcology, section: &NativeRestrictedCrossSection) -> BTreeSet<u32> {
        let addressed = || -> BTreeSet<u32> {
            let mut rows = BTreeSet::new();
            for retained in &class.fibre {
                rows.extend(retained.addresses.iter().copied());
            }
            for history in &self.histories {
                rows.extend(history.iter().copied());
            }
            rows.into_iter().filter(|row| (*row as usize) < section.rows).collect()
        };
        match section.restriction {
            NativeRestriction::Whole => section.retained_rows.iter().copied().collect(),
            NativeRestriction::Addressed => addressed(),
            NativeRestriction::Sites => {
                let mut rows: BTreeSet<u32> = class
                    .cone
                    .get(&section.population)
                    .map(|mask| {
                        mask.to_sites()
                            .iter()
                            .enumerate()
                            .filter(|(_, site)| **site)
                            .map(|(row, _)| row as u32)
                            .collect()
                    })
                    .unwrap_or_default();
                if lookup_reads(&self.ecology, super::NativeTensorOrdinal(section.population)) {
                    rows.extend(addressed());
                }
                rows
            }
        }
    }

    /// Write the rest: a header naming everything but the words, then the words of every
    /// cross-section in order.  Returns the SHA-256 of the octets written.
    pub fn write_rest(&self, path: &Path) -> Result<String, NativeCondensationError> {
        let file = File::create(path).map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        let mut out = BufWriter::new(file);
        let mut digest = Sha256::new();
        let header = serde_json::to_vec(self).map_err(|error| NativeCondensationError::Rest(error.to_string()))?;
        let mut write = |bytes: &[u8]| -> Result<(), NativeCondensationError> {
            digest.update(bytes);
            out.write_all(bytes).map_err(|error| NativeCondensationError::Io(error.to_string()))
        };
        write(REST_MAGIC)?;
        write(&(header.len() as u64).to_le_bytes())?;
        write(&header)?;
        for section in &self.cross_sections {
            let mut bytes = Vec::with_capacity(section.words.len() * 2);
            for word in &section.words {
                bytes.extend_from_slice(&word.to_le_bytes());
            }
            write(&bytes)?;
        }
        out.flush().map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        Ok(format!("{:x}", digest.finalize()))
    }

    /// Read a rest's header alone: everything but the words.  The cross-sections carry their
    /// retained row ordinals and no codewords; `validate` is not satisfied by a header.
    pub fn read_rest_header(path: &Path) -> Result<Self, NativeCondensationError> {
        let file = File::open(path).map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        let mut input = BufReader::with_capacity(1 << 24, file);
        Self::read_header(&mut input)
    }

    fn read_header(input: &mut BufReader<File>) -> Result<Self, NativeCondensationError> {
        let mut magic = [0u8; 32];
        input.read_exact(&mut magic).map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        if &magic != REST_MAGIC {
            return Err(NativeCondensationError::Rest("magic".to_owned()));
        }
        let mut length = [0u8; 8];
        input.read_exact(&mut length).map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        let mut header = vec![0u8; u64::from_le_bytes(length) as usize];
        input.read_exact(&mut header).map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        serde_json::from_slice(&header).map_err(|error| NativeCondensationError::Rest(error.to_string()))
    }

    /// Read a rest written by `write_rest`.
    pub fn read_rest(path: &Path) -> Result<Self, NativeCondensationError> {
        let file = File::open(path).map_err(|error| NativeCondensationError::Io(error.to_string()))?;
        let mut input = BufReader::with_capacity(1 << 24, file);
        let mut rest = Self::read_header(&mut input)?;
        for section in &mut rest.cross_sections {
            let count = section.retained_rows.len() * section.dim;
            let mut bytes = vec![0u8; count * 2];
            input.read_exact(&mut bytes).map_err(|error| NativeCondensationError::Io(error.to_string()))?;
            section.words = bytes.chunks_exact(2).map(|pair| u16::from_le_bytes([pair[0], pair[1]])).collect();
        }
        rest.validate()?;
        Ok(rest)
    }

    /// The octets one class's body needs, population by population: the coefficient intake of a
    /// restricted mount.
    pub fn intake(&self, class: Option<usize>) -> Result<NativeRestrictedIntake<'_>, NativeCondensationError> {
        let class = match class {
            Some(ordinal) => Some(
                self.classes
                    .iter()
                    .find(|c| c.ordinal == ordinal)
                    .ok_or_else(|| NativeCondensationError::Rest(format!("class {ordinal}")))?,
            ),
            None => None,
        };
        Ok(NativeRestrictedIntake { restricted: self, class })
    }
}

/// The intake of a restricted mount: every retained row's codewords, zero elsewhere.  With a
/// class, the rows are the class's; without, the extent's (the composed body).
pub struct NativeRestrictedIntake<'a> {
    restricted: &'a NativeConeRestrictedEcology,
    class: Option<&'a NativeClassEcology>,
}

impl NativeCoefficientIntake for NativeRestrictedIntake<'_> {
    fn populations(&self) -> usize {
        self.restricted.cross_sections.len()
    }

    fn population_octets(&self, ordinal: usize) -> Result<u64, NativeOperatorResidenceError> {
        let section = self
            .restricted
            .cross_sections
            .get(ordinal)
            .ok_or(NativeOperatorResidenceError::Witness)?;
        Ok((section.rows * section.dim * 2) as u64)
    }

    fn deliver(
        &mut self,
        ordinal: usize,
        sink: &mut dyn FnMut(usize, &[u8]) -> Result<(), NativeOperatorResidenceError>,
    ) -> Result<(), NativeOperatorResidenceError> {
        let section = self
            .restricted
            .cross_sections
            .get(ordinal)
            .ok_or(NativeOperatorResidenceError::Witness)?;
        let rows: BTreeSet<u32> = match self.class {
            Some(class) => self.restricted.class_rows(class, section),
            None => section.retained_rows.iter().copied().collect(),
        };
        let row_octets = section.dim * 2;
        const CHUNK_OCTETS: usize = 64 << 20;
        let mut chunk: Vec<u8> = Vec::with_capacity(CHUNK_OCTETS.min(section.rows * row_octets));
        let mut chunk_offset = 0usize;
        let mut position = 0usize;
        for row in 0..section.rows as u32 {
            if rows.contains(&row) {
                match section.retained_rows.binary_search(&row) {
                    Ok(index) => {
                        for word in &section.words[index * section.dim..(index + 1) * section.dim] {
                            chunk.extend_from_slice(&word.to_le_bytes());
                        }
                    }
                    Err(_) => return Err(NativeOperatorResidenceError::Witness),
                }
            } else {
                chunk.resize(chunk.len() + row_octets, 0);
            }
            position += row_octets;
            if chunk.len() >= CHUNK_OCTETS {
                sink(chunk_offset, &chunk)?;
                chunk_offset = position;
                chunk.clear();
            }
        }
        if !chunk.is_empty() {
            sink(chunk_offset, &chunk)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_restriction_of_every_population_follows_the_operations_that_read_it() {
        use super::super::{NativeCarrierAxis, NativeCarrierChart, NativeCarrierOrdinal, NativeCoefficientPopulation, NativeOperatorNode, NativeScaleConstraint, NativeTensorOrdinal};
        let population = |ordinal: u32, shape: Vec<usize>| NativeCoefficientPopulation {
            ordinal: NativeTensorOrdinal(ordinal),
            coefficient_population: shape.iter().product::<usize>() as u64,
            shape,
        };
        let ecology = NativeFullOperatorEcology {
            schema: super::super::NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA.to_owned(),
            shared_carrier_extent: 4,
            coefficient_populations: vec![population(0, vec![8, 4]), population(1, vec![8, 4]), population(2, vec![4])],
            carriers: vec![
                NativeCarrierChart { ordinal: NativeCarrierOrdinal(0), axes: vec![NativeCarrierAxis::Occurrence, NativeCarrierAxis::Fixed(4)] },
                NativeCarrierChart { ordinal: NativeCarrierOrdinal(1), axes: vec![NativeCarrierAxis::Occurrence, NativeCarrierAxis::Fixed(8)] },
            ],
            operations: vec![
                NativeOperatorNode { ordinal: 0, layer: None, primitive: NativeOperationPrimitive::Lookup { scale: NativeScaleConstraint::Rational { numerator: 1, denominator: 1 } }, inputs: vec![], output: NativeCarrierOrdinal(0), coefficients: vec![NativeTensorOrdinal(0)] },
                NativeOperatorNode { ordinal: 1, layer: None, primitive: NativeOperationPrimitive::Contract, inputs: vec![NativeCarrierOrdinal(0)], output: NativeCarrierOrdinal(1), coefficients: vec![NativeTensorOrdinal(1)] },
            ],
            layers: vec![],
            coefficient_obstructions: vec![],
        };
        let restrictions = restrictions_of(&ecology);
        assert_eq!(restrictions.get(&0), Some(&NativeRestriction::Addressed));
        assert_eq!(restrictions.get(&1), Some(&NativeRestriction::Sites));
        assert_eq!(restrictions.get(&2), None);
        assert!(lookup_reads(&ecology, NativeTensorOrdinal(0)));
        assert!(!lookup_reads(&ecology, NativeTensorOrdinal(1)));
    }

    #[test]
    fn a_restricted_intake_delivers_retained_rows_and_zeros_elsewhere() {
        let section = NativeRestrictedCrossSection {
            population: 0,
            restriction: NativeRestriction::Sites,
            rows: 4,
            dim: 2,
            retained_rows: vec![1, 3],
            words: vec![0x3f80, 0x4000, 0x4040, 0x4080],
        };
        let restricted = NativeConeRestrictedEcology {
            schema: NATIVE_CONE_RESTRICTED_ECOLOGY_SCHEMA.to_owned(),
            ecology: NativeFullOperatorEcology {
                schema: super::super::NATIVE_FULL_OPERATOR_ECOLOGY_SCHEMA.to_owned(),
                shared_carrier_extent: 1,
                coefficient_populations: vec![],
                carriers: vec![],
                operations: vec![],
                layers: vec![],
                coefficient_obstructions: vec![],
            },
            histories: vec![],
            classes: vec![],
            extent: BTreeMap::new(),
            sites: 4,
            extent_population: 2,
            cross_sections: vec![section],
        };
        let mut intake = restricted.intake(None).unwrap();
        assert_eq!(intake.population_octets(0).unwrap(), 16);
        let mut delivered: Vec<(usize, Vec<u8>)> = Vec::new();
        intake
            .deliver(0, &mut |offset, bytes| {
                delivered.push((offset, bytes.to_vec()));
                Ok(())
            })
            .unwrap();
        assert_eq!(delivered.len(), 1);
        assert_eq!(delivered[0].0, 0);
        assert_eq!(
            delivered[0].1,
            vec![0, 0, 0, 0, 0x80, 0x3f, 0x00, 0x40, 0, 0, 0, 0, 0x40, 0x40, 0x80, 0x40]
        );
    }
}
