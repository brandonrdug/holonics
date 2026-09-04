//! Identification: the signature quotient of a declared family, SKE3's owner.
//!
//! A declared family names occurrences, receivers, and ordered histories.  On the resident
//! operator the receiver is the selected face at the terminal position and a history is a fixed
//! generator word appended to the occurrence's addresses before the cycle; the signature of an
//! occurrence is its face at every declared exposure (receiver, history).  Two occurrences are
//! one class exactly when their signatures agree (`DeclaredFamily.Identified`); one separating
//! exposure reopens a proposed class (`separatingExposure_reopens`). Each exposure carries
//! supplied intervention masks; this quotient does not certify universal cone soundness.
//! A class's mask is the union of its members' masks over
//! every exposure, the extent of the family is the union of every cone (`DeclaredFamily.extent`),
//! and the insufficiency is its complement together with every exposure the family did not
//! declare (`DeclaredFamily.insufficiency`).  Nothing here selects an answer: the faces are the
//! operator's own.
//!
//! This owner is host arithmetic over faces and site bitmasks the card returned; it launches
//! nothing.

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

/// One declared exposure: the terminal face after one fixed generator word.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeExposure {
    pub receiver: String,
    pub history: Vec<u32>,
}

/// One occurrence's face at one exposure with its supplied intervention mask, per population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeExposureFace {
    pub occurrence: usize,
    pub exposure: NativeExposure,
    pub face: u32,
    pub exact_digest: String,
    /// Per population: its site count and its cone as a bitmask, most significant bit first.
    pub cones: BTreeMap<u32, NativeSiteBitmask>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeSiteBitmask {
    pub sites: usize,
    pub hex: String,
}

impl NativeSiteBitmask {
    pub fn from_sites(sites: &[bool]) -> Self {
        let mut hex = String::with_capacity(sites.len() / 4 + 1);
        for chunk in sites.chunks(4) {
            let mut nibble = 0u8;
            for (at, site) in chunk.iter().enumerate() {
                if *site {
                    nibble |= 1 << (3 - at);
                }
            }
            hex.push(char::from_digit(u32::from(nibble), 16).unwrap_or('0'));
        }
        Self {
            sites: sites.len(),
            hex,
        }
    }

    pub fn to_sites(&self) -> Vec<bool> {
        let mut sites = Vec::with_capacity(self.sites);
        for nibble in self.hex.chars().map(|c| c.to_digit(16).unwrap_or(0) as u8) {
            for at in 0..4 {
                if sites.len() < self.sites {
                    sites.push(nibble & (1 << (3 - at)) != 0);
                }
            }
        }
        sites.resize(self.sites, false);
        sites
    }

    pub fn population(&self) -> usize {
        self.to_sites().iter().filter(|site| **site).count()
    }

    /// The union of two bitmasks over the same sites.
    pub fn union(&self, other: &Self) -> Option<Self> {
        if self.sites != other.sites {
            return None;
        }
        let left = self.to_sites();
        let right = other.to_sites();
        let joined: Vec<bool> = left.iter().zip(&right).map(|(a, b)| *a || *b).collect();
        Some(Self::from_sites(&joined))
    }
}

/// The signature of one occurrence: its face at every declared exposure, in exposure order.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct NativeSignature {
    pub faces: Vec<(NativeExposure, u32)>,
}

/// One class of the signature quotient with the occurrences it retains and its cone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeSignatureClass {
    pub ordinal: usize,
    pub signature: NativeSignature,
    pub occurrences: Vec<usize>,
    /// Per population: the union of the members' cones over every exposure.
    pub cone: BTreeMap<u32, NativeSiteBitmask>,
    pub cone_population: usize,
}

/// A declared exposure that separates two occurrences a coarser exposure family identified.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeSeparation {
    pub left: usize,
    pub right: usize,
    pub exposure: NativeExposure,
    pub left_face: u32,
    pub right_face: u32,
}

/// The signature quotient of a declared family with its extent and insufficiency.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeSignatureQuotient {
    pub exposures: Vec<NativeExposure>,
    pub occurrences: usize,
    pub classes: Vec<NativeSignatureClass>,
    /// Per population: the union of every class's cone, the extent of the lift.
    pub extent: BTreeMap<u32, NativeSiteBitmask>,
    pub sites: usize,
    pub extent_population: usize,
    pub insufficiency_population: usize,
    /// The classes under the empty history alone and how the declared histories reopened them.
    pub classes_under_empty_history: usize,
    pub separations: Vec<NativeSeparation>,
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum NativeIdentificationError {
    #[error("occurrence {occurrence} lacks its face at a declared exposure")]
    ExposureMissing { occurrence: usize },
    #[error("occurrence {occurrence} has conflicting records at exposure {exposure:?}")]
    ExposureConflict {
        occurrence: usize,
        exposure: NativeExposure,
    },
    #[error("the cones of population {population} disagree in site count")]
    Sites { population: u32 },
    #[error("the family declares no exposure")]
    Empty,
}

impl NativeSignatureQuotient {
    /// Form the quotient from every (occurrence, exposure) face the card returned.  The
    /// exposures declared are exactly those present; every occurrence must carry every one.
    /// Repeated testimony is accepted only when its complete stored record agrees; the
    /// signature itself remains receiver-face equality, independent of testimony digests.
    pub fn found(faces: &[NativeExposureFace]) -> Result<Self, NativeIdentificationError> {
        let mut observations = BTreeMap::new();
        for face in faces {
            let key = (face.occurrence, face.exposure.clone());
            if let Some(previous) = observations.insert(key, face) {
                if previous != face {
                    return Err(NativeIdentificationError::ExposureConflict {
                        occurrence: face.occurrence,
                        exposure: face.exposure.clone(),
                    });
                }
            }
        }
        let mut exposures: Vec<NativeExposure> = faces.iter().map(|f| f.exposure.clone()).collect();
        exposures.sort();
        exposures.dedup();
        if exposures.is_empty() {
            return Err(NativeIdentificationError::Empty);
        }
        let mut occurrences: Vec<usize> = faces.iter().map(|f| f.occurrence).collect();
        occurrences.sort_unstable();
        occurrences.dedup();
        let face_of = |occurrence: usize, exposure: &NativeExposure| {
            observations.get(&(occurrence, exposure.clone())).copied()
        };
        let mut signatures: Vec<(usize, NativeSignature)> = Vec::new();
        for occurrence in &occurrences {
            let mut signature = Vec::with_capacity(exposures.len());
            for exposure in &exposures {
                let face = face_of(*occurrence, exposure).ok_or(
                    NativeIdentificationError::ExposureMissing {
                        occurrence: *occurrence,
                    },
                )?;
                signature.push((exposure.clone(), face.face));
            }
            signatures.push((*occurrence, NativeSignature { faces: signature }));
        }
        let mut classes: Vec<NativeSignatureClass> = Vec::new();
        for (occurrence, signature) in &signatures {
            match classes
                .iter_mut()
                .find(|class| &class.signature == signature)
            {
                Some(class) => class.occurrences.push(*occurrence),
                None => classes.push(NativeSignatureClass {
                    ordinal: classes.len(),
                    signature: signature.clone(),
                    occurrences: vec![*occurrence],
                    cone: BTreeMap::new(),
                    cone_population: 0,
                }),
            }
        }
        let mut extent: BTreeMap<u32, NativeSiteBitmask> = BTreeMap::new();
        let mut sites = 0usize;
        for class in &mut classes {
            let mut cone: BTreeMap<u32, NativeSiteBitmask> = BTreeMap::new();
            for occurrence in &class.occurrences {
                for exposure in &exposures {
                    let face = face_of(*occurrence, exposure).ok_or(
                        NativeIdentificationError::ExposureMissing {
                            occurrence: *occurrence,
                        },
                    )?;
                    for (population, mask) in &face.cones {
                        join(&mut cone, *population, mask)?;
                    }
                }
            }
            class.cone_population = cone.values().map(NativeSiteBitmask::population).sum();
            for (population, mask) in &cone {
                join(&mut extent, *population, mask)?;
            }
            class.cone = cone;
        }
        for mask in extent.values() {
            sites += mask.sites;
        }
        let extent_population: usize = extent.values().map(NativeSiteBitmask::population).sum();
        // The classes under the empty history alone, and every declared history that separates
        // two occurrences the empty history identified.
        let empty: Vec<&NativeExposure> =
            exposures.iter().filter(|e| e.history.is_empty()).collect();
        let mut coarse: Vec<Vec<usize>> = Vec::new();
        for (occurrence, signature) in &signatures {
            let key: Vec<u32> = signature
                .faces
                .iter()
                .filter(|(exposure, _)| empty.contains(&exposure))
                .map(|(_, face)| *face)
                .collect();
            let same = coarse.iter_mut().find(|members| {
                let first = members[0];
                let other: Vec<u32> = signatures
                    .iter()
                    .find(|(o, _)| *o == first)
                    .map(|(_, s)| {
                        s.faces
                            .iter()
                            .filter(|(exposure, _)| empty.contains(&exposure))
                            .map(|(_, face)| *face)
                            .collect()
                    })
                    .unwrap_or_default();
                other == key
            });
            match same {
                Some(members) => members.push(*occurrence),
                None => coarse.push(vec![*occurrence]),
            }
        }
        let mut separations = Vec::new();
        for members in &coarse {
            for (i, left) in members.iter().enumerate() {
                for right in &members[i + 1..] {
                    for exposure in &exposures {
                        if exposure.history.is_empty() {
                            continue;
                        }
                        let (Some(a), Some(b)) =
                            (face_of(*left, exposure), face_of(*right, exposure))
                        else {
                            continue;
                        };
                        if a.face != b.face {
                            separations.push(NativeSeparation {
                                left: *left,
                                right: *right,
                                exposure: exposure.clone(),
                                left_face: a.face,
                                right_face: b.face,
                            });
                        }
                    }
                }
            }
        }
        Ok(Self {
            exposures,
            occurrences: occurrences.len(),
            classes,
            extent,
            sites,
            extent_population,
            insufficiency_population: sites - extent_population,
            classes_under_empty_history: coarse.len(),
            separations,
        })
    }
}

fn join(
    into: &mut BTreeMap<u32, NativeSiteBitmask>,
    population: u32,
    mask: &NativeSiteBitmask,
) -> Result<(), NativeIdentificationError> {
    match into.get(&population) {
        Some(held) => {
            let joined = held
                .union(mask)
                .ok_or(NativeIdentificationError::Sites { population })?;
            into.insert(population, joined);
        }
        None => {
            into.insert(population, mask.clone());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn exposure(history: &[u32]) -> NativeExposure {
        NativeExposure {
            receiver: "terminal-face".to_owned(),
            history: history.to_vec(),
        }
    }

    fn face(occurrence: usize, history: &[u32], face: u32, cone: &[bool]) -> NativeExposureFace {
        NativeExposureFace {
            occurrence,
            exposure: exposure(history),
            face,
            exact_digest: String::new(),
            cones: BTreeMap::from([(0, NativeSiteBitmask::from_sites(cone))]),
        }
    }

    #[test]
    fn a_bitmask_round_trips_and_unions() {
        let sites = [true, false, false, true, true];
        let mask = NativeSiteBitmask::from_sites(&sites);
        assert_eq!(mask.hex, "98");
        assert_eq!(mask.to_sites(), sites);
        assert_eq!(mask.population(), 3);
        let other = NativeSiteBitmask::from_sites(&[false, true, false, false, true]);
        assert_eq!(
            mask.union(&other).unwrap().to_sites(),
            [true, true, false, true, true]
        );
        assert!(mask
            .union(&NativeSiteBitmask::from_sites(&[true]))
            .is_none());
    }

    #[test]
    fn equal_signatures_are_one_class_and_a_separating_history_reopens_it() {
        let faces = vec![
            face(0, &[], 7, &[true, false, false, false]),
            face(1, &[], 7, &[false, true, false, false]),
            face(2, &[], 9, &[false, false, true, false]),
            face(0, &[5], 5, &[false, false, false, true]),
            face(1, &[5], 6, &[false, false, false, false]),
            face(2, &[5], 3, &[false, false, false, false]),
        ];
        let quotient = NativeSignatureQuotient::found(&faces).unwrap();
        assert_eq!(quotient.occurrences, 3);
        assert_eq!(quotient.classes_under_empty_history, 2);
        assert_eq!(quotient.classes.len(), 3);
        assert_eq!(quotient.separations.len(), 1);
        assert_eq!(quotient.separations[0].left, 0);
        assert_eq!(quotient.separations[0].right, 1);
        assert_eq!(quotient.extent_population, 4);
        assert_eq!(quotient.insufficiency_population, 0);
        // Without the separating history the two are one class with the union cone.
        let coarse: Vec<NativeExposureFace> = faces
            .into_iter()
            .filter(|f| f.exposure.history.is_empty())
            .collect();
        let quotient = NativeSignatureQuotient::found(&coarse).unwrap();
        assert_eq!(quotient.classes.len(), 2);
        assert_eq!(quotient.classes[0].occurrences, vec![0, 1]);
        assert_eq!(quotient.classes[0].cone_population, 2);
        assert_eq!(quotient.insufficiency_population, 1);
    }

    #[test]
    fn a_missing_exposure_refuses() {
        let faces = vec![
            face(0, &[], 7, &[true]),
            face(1, &[], 7, &[true]),
            face(0, &[1], 2, &[true]),
        ];
        assert_eq!(
            NativeSignatureQuotient::found(&faces),
            Err(NativeIdentificationError::ExposureMissing { occurrence: 1 })
        );
    }

    #[test]
    fn conflicting_duplicate_exposure_refuses_in_either_order() {
        let first = face(0, &[], 7, &[true, false]);
        let conflicts = [
            face(0, &[], 9, &[true, false]),
            face(0, &[], 7, &[false, true]),
            NativeExposureFace {
                exact_digest: "different testimony".into(),
                ..first.clone()
            },
        ];
        for conflict in conflicts {
            for records in [[first.clone(), conflict.clone()], [conflict, first.clone()]] {
                assert_eq!(
                    NativeSignatureQuotient::found(&records),
                    Err(NativeIdentificationError::ExposureConflict {
                        occurrence: 0,
                        exposure: exposure(&[]),
                    })
                );
            }
        }
    }

    #[test]
    fn identical_duplicate_testimony_preserves_the_quotient() {
        let record = face(0, &[], 7, &[true, false]);
        let other = face(1, &[], 9, &[false, true]);
        assert_eq!(
            NativeSignatureQuotient::found(&[record.clone(), other.clone(), record.clone()]),
            NativeSignatureQuotient::found(&[other, record]),
        );
    }
}
