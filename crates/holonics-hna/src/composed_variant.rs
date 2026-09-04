//! The composed Athena variant: Eros composes the class ecologies of a Soulkiller return into
//! one body, and the compression law is stated over that body.
//!
//! Eros is an interpretation, not a module (`docs/canon/05_ONTOLOGY.md`): the operational pattern in
//! which differences meet, constrain one another, found new local relations, and return
//! consequences.  Here that pattern is the act of composition: the classes a family's
//! excitation founded (`NativeConeRestrictedEcology`, the productive lane) are taken together as
//! one variant whose body is the union of their cones, and the family's declared exposures are
//! driven through that one body.  The composition itself is exterior arithmetic over the return;
//! the body is mounted from the rest alone and the recurrence runs on it unchanged.
//!
//! What the compression law owes on the composed variant (`docs/canon/TABLET_THE_COMPRESSION.md`,
//! `H.0420`, `H.0410`) and what this owner returns:
//!
//! - the **species by remainder**: the collapsed pairs between the composed body and the full
//!   operator over the declared family, with their separating words; none collapsed and every
//!   family face reproduced states condensation with the propagated enclosure as certificate;
//! - the **declared decoder**: the executable that recovers the first chart's face from the second
//!   chart, named, with its measured cost; a rest without it is not a compression;
//! - the **invariance as a difference**, never a ratio: what the composed body returns beside
//!   what the full operator returns, per exposure and per face coordinate;
//! - the **consequence-preserving product** as the vector it is: native standing, executable
//!   decoder, retained fibres, semantic work, span, residency, transfer; no scalar summarizes it;
//! - **identification saturation** inside each observed enlargement: exact equality of its
//!   identified occurrence pairs, independently of changes in reachable receiver faces.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::native_ecology::holonic_intelligence::{
    NativeClassRemainder, NativeCollapsedPair, NativeConeRestrictedEcology, NativeExposure,
    NativeExposureFace, NativeRemainderSpecies, NativeSignatureQuotient, NativeTerminalRemainder,
};
use serde::{Deserialize, Serialize};

pub const COMPOSED_VARIANT_SCHEMA: &str = "athena-alpha.composed-variant.v2";
pub const COMPOSED_DEED_SCOPE: &str = "declared-family-deed-only";

/// The declared decoder: the executable that turns the rest into faces, named by its owners,
/// with the cost it was measured at.  The cost is reported as what was measured, not as a ratio
/// against anything.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredDecoder {
    pub mount: String,
    pub recurrence: String,
    pub receiver: String,
    pub mount_seconds_milli: u64,
    pub cycle_milliseconds: Vec<u128>,
    pub launches_per_cycle: Vec<u64>,
    pub passages_per_cycle: Vec<u64>,
}

/// One exposure of the family driven through the composed body beside the full operator.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComposedFace {
    pub occurrence: usize,
    pub exposure: NativeExposure,
    pub full_face: u32,
    pub composed_face: u32,
    pub equal: bool,
    /// Per-coordinate difference of enclosure widths at the face (composed minus full), as a
    /// histogram of (difference in grains, coordinates).
    pub width_difference: Vec<(i64, usize)>,
}

/// The consequence-preserving product, as a vector; nothing here is a summary of anything else.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProductVector {
    /// Native standing: the rest's octets and its retained rows by restriction.
    pub rest_octets: u64,
    pub retained_rows: BTreeMap<String, usize>,
    pub rest_sha256: String,
    /// The executable decoder and its cost.
    pub decoder: DeclaredDecoder,
    /// Retained fibres: every occurrence the classes retain, with its addresses.
    pub retained_fibres: Vec<(usize, Vec<u32>)>,
    /// Semantic work: operations per cycle and the census of one cycle on the composed body.
    pub operations_per_cycle: usize,
    pub deed_launches_per_cycle: u64,
    pub section_read_outs_per_cycle: u64,
    /// Span: the declared family the body was driven over.
    pub occurrences: usize,
    pub histories: usize,
    pub exposures: usize,
    /// Residency: resident octets of the composed body beside the full operator's resident
    /// octets as its own census read them, and beside the full coefficient octets.
    pub composed_resident_octets: u64,
    pub full_resident_octets: Option<u64>,
    pub full_coefficient_octets: u64,
    /// Transfer: ingress and egress octets per cycle on the composed body.
    pub ingress_octets_per_cycle: u64,
    pub egress_section_octets_per_cycle: u64,
}

/// What one enlargement of the declared exposures did to the family's structure, over its
/// fixed occurrences.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SaturationStep {
    /// The occurrences of the family (fixed under the enlargement).
    pub occurrence: usize,
    /// The exposure added at this step.
    pub exposure: NativeExposure,
    pub classes: usize,
    pub separations: usize,
    /// Generators: the exposures declared so far.
    pub generators: usize,
    /// Relations: the identified pairs under the declared exposures.
    pub relations: usize,
    /// Obstructions: refusals returned under the declared exposures.
    pub obstructions: usize,
    pub extent_roles: usize,
    pub insufficiency_roles: usize,
    pub reachable_faces: usize,
    pub added_classes: usize,
    pub added_separations: usize,
    pub removed_relations: usize,
    pub added_reachable_faces: usize,
    /// Exact equality of the identified-pair relations before and after this enlargement.
    /// The initial declaration has no preceding family and therefore returns `None`.
    pub identification_preserved: Option<bool>,
    /// Broader observed growth, including a newly reachable face even when no class reopens.
    pub observed_consequences_changed: bool,
}

/// Finite observed enlargements only; no claim about any unobserved future family.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SaturationReceipt {
    pub steps: Vec<SaturationStep>,
    pub trailing_identification_preserving_enlargements: usize,
    pub last_enlargement_identification_saturated: Option<bool>,
    pub trailing_enlargements_without_observed_consequence_change: usize,
    pub last_enlargement_added_no_observed_consequences: Option<bool>,
}

/// A correction projected from previously deposited observations, not a new card measurement.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiptDerivation {
    pub source_revision: String,
    pub method: String,
    pub new_gpu_run: bool,
}

/// The composed variant's return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComposedVariant {
    pub schema: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub derivation: Option<ReceiptDerivation>,
    pub classes: Vec<usize>,
    pub class_cone_roles: Vec<usize>,
    pub extent_roles: usize,
    pub roles: usize,
    pub faces: Vec<ComposedFace>,
    /// The family occurrence refused at admission, never driven: the insufficiency lane's cause.
    pub refused_outside_family: Option<String>,
    pub refused_undeclared_history: Option<String>,
    pub collapsed: Vec<NativeCollapsedPair>,
    /// Absent when a family face did not descend: no species is stated.
    pub species: Option<NativeRemainderSpecies>,
    pub propagated: Vec<NativeTerminalRemainder>,
    /// The per-coordinate residual of the composed body under each exposure, as octets beside
    /// the receipt.
    pub residual_files: Vec<String>,
    /// The grain the width differences are stated at.
    pub difference_grain: u32,
    pub product: ProductVector,
    pub saturation: SaturationReceipt,
    /// One continuing session: the generations the family's cycles ran through.
    pub session_generations: Vec<(u64, u64)>,
    /// The declared-family deed checks only; this is not the repository release-gate result.
    pub release: ReleaseReceipt,
}

/// Checks of the deposited SKE5 deed fields. Repository release gates are outside this scope.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReleaseReceipt {
    pub scope: String,
    pub one_session_over_the_family: bool,
    pub every_family_face_equal: bool,
    pub outside_occurrence_refused: bool,
    pub undeclared_history_refused: bool,
    pub species_stated: bool,
    pub remainder_exhibited: bool,
    pub decoder_declared: bool,
    pub product_vector_returned: bool,
    pub saturation_receipt_returned: bool,
    pub extent_is_union_of_class_cones: bool,
    pub passed: bool,
}

impl ComposedVariant {
    /// Re-read the deed's actual fields. File availability and the validated cone union are
    /// supplied by their owning apparatus checks; neither stands in for repository gates.
    pub fn assess_deed(
        &self,
        residual_files_present: bool,
        extent_is_union: bool,
    ) -> ReleaseReceipt {
        let cycles = self.faces.len();
        let keys: BTreeSet<_> = self
            .faces
            .iter()
            .map(|f| (f.occurrence, &f.exposure))
            .collect();
        let occurrences: BTreeSet<_> = self.faces.iter().map(|f| f.occurrence).collect();
        let exposures: BTreeSet<_> = self.faces.iter().map(|f| &f.exposure).collect();
        let family_complete = cycles > 0
            && keys.len() == cycles
            && occurrences.len().checked_mul(exposures.len()) == Some(cycles);
        let decoder = &self.product.decoder;
        let decoder_declared = family_complete
            && [&decoder.mount, &decoder.recurrence, &decoder.receiver]
                .iter()
                .all(|owner| !owner.trim().is_empty())
            && decoder.cycle_milliseconds.len() == cycles
            && decoder.launches_per_cycle.len() == cycles
            && decoder.passages_per_cycle.len() == cycles
            && decoder.launches_per_cycle.iter().all(|n| *n > 0)
            && decoder.passages_per_cycle.iter().all(|n| *n > 0);
        let retained: BTreeSet<_> = self.product.retained_fibres.iter().map(|f| f.0).collect();
        let product_vector_returned = family_complete
            && self.product.exposures == cycles
            && self.product.occurrences == occurrences.len()
            && self.product.histories == exposures.len()
            && self.product.rest_octets > 0
            && !self.product.retained_rows.is_empty()
            && self.product.retained_rows.values().all(|rows| *rows > 0)
            && retained == occurrences
            && retained.len() == self.product.retained_fibres.len()
            && self
                .product
                .retained_fibres
                .iter()
                .all(|(_, addresses)| !addresses.is_empty())
            && self.product.operations_per_cycle > 0
            && self.product.deed_launches_per_cycle > 0
            && self.product.section_read_outs_per_cycle > 0
            && self.product.composed_resident_octets > 0
            && self.product.full_coefficient_octets > 0
            && self
                .product
                .full_resident_octets
                .is_none_or(|octets| octets > 0)
            && self.product.ingress_octets_per_cycle > 0
            && self.product.egress_section_octets_per_cycle > 0;
        let one_session_over_the_family = family_complete
            && self.session_generations.len() == cycles
            && self
                .session_generations
                .first()
                .is_some_and(|(before, _)| *before == 0)
            && self.session_generations.iter().all(|(before, after)| {
                before.checked_add(self.product.operations_per_cycle as u64) == Some(*after)
            })
            && self
                .session_generations
                .windows(2)
                .all(|w| w[0].1 == w[1].0);
        let (collapsed, species) = species_over_family(&self.faces);
        let remainder_keys: BTreeSet<_> = self
            .propagated
            .iter()
            .map(|r| (r.occurrence, &r.exposure))
            .collect();
        let remainder_exhibited = residual_files_present
            && family_complete
            && self.residual_files.len() == cycles
            && self.residual_files.iter().collect::<BTreeSet<_>>().len() == cycles
            && self.propagated.len() == cycles
            && remainder_keys == keys
            && self.propagated.iter().all(|r| {
                r.coordinates > 0
                    && r.widths.iter().map(|(_, count)| count).sum::<usize>() == r.coordinates
            });
        let exposures_in_order: Vec<_> = self
            .saturation
            .steps
            .iter()
            .map(|s| s.exposure.clone())
            .collect();
        let observed: Vec<_> = self
            .faces
            .iter()
            .map(|f| NativeExposureFace {
                occurrence: f.occurrence,
                exposure: f.exposure.clone(),
                face: f.full_face,
                exact_digest: String::new(),
                cones: BTreeMap::new(),
            })
            .collect();
        let saturation_receipt_returned = saturation(
            &observed,
            &exposures_in_order,
            self.extent_roles,
            self.roles,
            usize::from(self.refused_outside_family.is_some())
                + usize::from(self.refused_undeclared_history.is_some()),
        )
        .is_ok_and(|receipt| receipt == self.saturation);
        let mut receipt = ReleaseReceipt {
            scope: COMPOSED_DEED_SCOPE.into(),
            one_session_over_the_family,
            every_family_face_equal: family_complete
                && self
                    .faces
                    .iter()
                    .all(|f| f.equal && f.full_face == f.composed_face),
            outside_occurrence_refused: self
                .refused_outside_family
                .as_ref()
                .is_some_and(|r| !r.is_empty()),
            undeclared_history_refused: self
                .refused_undeclared_history
                .as_ref()
                .is_some_and(|r| !r.is_empty()),
            species_stated: family_complete
                && species.is_some()
                && species == self.species
                && collapsed == self.collapsed,
            remainder_exhibited,
            decoder_declared,
            product_vector_returned,
            saturation_receipt_returned,
            extent_is_union_of_class_cones: extent_is_union && self.extent_roles <= self.roles,
            passed: false,
        };
        receipt.passed = receipt.one_session_over_the_family
            && receipt.every_family_face_equal
            && receipt.outside_occurrence_refused
            && receipt.undeclared_history_refused
            && receipt.species_stated
            && receipt.remainder_exhibited
            && receipt.decoder_declared
            && receipt.product_vector_returned
            && receipt.saturation_receipt_returned
            && receipt.extent_is_union_of_class_cones;
        receipt
    }
}

/// The histogram of per-coordinate width differences (composed minus full), in grains of the
/// finer of the two grains: each width is rebased to that grain before the subtraction, so two
/// readings at different grains are never subtracted as bare counts.
pub fn width_difference(
    full: &[u32],
    full_grain: u32,
    composed: &[u32],
    composed_grain: u32,
) -> (Vec<(i64, usize)>, u32) {
    let grain = full_grain.max(composed_grain);
    let scale = |width: u32, own: u32| -> i64 { i64::from(width) << (grain - own) };
    let mut histogram: BTreeMap<i64, usize> = BTreeMap::new();
    for (f, c) in full.iter().zip(composed) {
        *histogram
            .entry(scale(*c, composed_grain) - scale(*f, full_grain))
            .or_default() += 1;
    }
    (histogram.into_iter().collect(), grain)
}

/// The collapsed pairs of the composed body against the full operator over the family, and the
/// species they state on that domain; a face that does not descend refuses a species.
pub fn species_over_family(
    faces: &[ComposedFace],
) -> (Vec<NativeCollapsedPair>, Option<NativeRemainderSpecies>) {
    let domain: Vec<(usize, NativeExposure, u32, u32)> = faces
        .iter()
        .map(|f| {
            (
                f.occurrence,
                f.exposure.clone(),
                f.composed_face,
                f.full_face,
            )
        })
        .collect();
    let collapsed = NativeClassRemainder::collapsed_pairs(&domain);
    let failures = faces
        .iter()
        .filter(|f| f.full_face != f.composed_face)
        .count();
    let species = NativeClassRemainder::species_of(&collapsed, failures);
    (collapsed, species)
}

/// The formal `DeclaredFamily.Saturated` compares identified-pair relations over fixed
/// occurrences. New reachable faces and additional separating testimony are recorded separately.
/// The retained extent and refusals are testimony supplied for this family, not reconstructed
/// from the number of classes. Every declared prefix must expose the same occurrence population.
pub fn saturation(
    faces: &[NativeExposureFace],
    exposures_in_order: &[NativeExposure],
    extent_roles: usize,
    roles: usize,
    refusals: usize,
) -> Result<SaturationReceipt, String> {
    let occurrences: BTreeSet<usize> = faces.iter().map(|f| f.occurrence).collect();
    if occurrences.is_empty() || exposures_in_order.is_empty() || extent_roles > roles {
        return Err(
            "saturation needs a nonempty family, exposures, and an admitted role extent".into(),
        );
    }
    if exposures_in_order.iter().collect::<BTreeSet<_>>().len() != exposures_in_order.len() {
        return Err("the exposure enlargement contains a duplicate declaration".into());
    }
    let mut steps = Vec::with_capacity(exposures_in_order.len());
    let (mut classes, mut separations, mut relations, mut reachable) =
        (0usize, 0usize, 0usize, 0usize);
    let mut previous_pairs: Option<BTreeSet<(usize, usize)>> = None;
    for at in 0..exposures_in_order.len() {
        let declared = &exposures_in_order[..=at];
        let restricted: Vec<NativeExposureFace> = faces
            .iter()
            .filter(|f| declared.contains(&f.exposure))
            .cloned()
            .collect();
        let quotient = NativeSignatureQuotient::found(&restricted).map_err(|e| e.to_string())?;
        if quotient.occurrences != occurrences.len() || quotient.exposures.len() != declared.len() {
            return Err(
                "an enlargement changed the occurrence population or lacks an exposure".into(),
            );
        }
        let pairs: BTreeSet<(usize, usize)> = quotient
            .classes
            .iter()
            .flat_map(|class| {
                class.occurrences.iter().enumerate().flat_map(|(at, left)| {
                    class.occurrences[at + 1..]
                        .iter()
                        .map(move |right| (*left, *right))
                })
            })
            .collect();
        let relation_count = pairs.len();
        let reachable_faces: BTreeSet<u32> = restricted.iter().map(|f| f.face).collect();
        let step = SaturationStep {
            occurrence: occurrences.len(),
            exposure: declared[at].clone(),
            classes: quotient.classes.len(),
            separations: quotient.separations.len(),
            generators: declared.len(),
            relations: relation_count,
            obstructions: refusals,
            extent_roles,
            insufficiency_roles: roles - extent_roles,
            reachable_faces: reachable_faces.len(),
            added_classes: quotient.classes.len().saturating_sub(classes),
            added_separations: quotient.separations.len().saturating_sub(separations),
            removed_relations: relations.saturating_sub(relation_count),
            added_reachable_faces: reachable_faces.len().saturating_sub(reachable),
            identification_preserved: previous_pairs.as_ref().map(|previous| previous == &pairs),
            observed_consequences_changed: at == 0
                || quotient.classes.len() != classes
                || quotient.separations.len() != separations
                || relation_count != relations
                || reachable_faces.len() != reachable,
        };
        classes = quotient.classes.len();
        separations = quotient.separations.len();
        relations = relation_count;
        reachable = reachable_faces.len();
        previous_pairs = Some(pairs);
        steps.push(step);
    }
    Ok(SaturationReceipt {
        last_enlargement_identification_saturated: steps
            .last()
            .and_then(|s| s.identification_preserved),
        trailing_identification_preserving_enlargements: steps
            .iter()
            .rev()
            .take_while(|s| s.identification_preserved == Some(true))
            .count(),
        last_enlargement_added_no_observed_consequences: steps.last().and_then(|s| {
            s.identification_preserved
                .map(|_| !s.observed_consequences_changed)
        }),
        trailing_enlargements_without_observed_consequence_change: steps
            .iter()
            .rev()
            .take_while(|s| {
                s.identification_preserved.is_some() && !s.observed_consequences_changed
            })
            .count(),
        steps,
    })
}

/// The class cones of a return as role sets, by the occurrences each class retains: a role is
/// in a cone when every one of its sites is.
pub fn class_cone_roles(
    restricted: &NativeConeRestrictedEcology,
    roles: &[holonic_engine::native_ecology::holonic_intelligence::NativeRole],
) -> (Vec<usize>, BTreeMap<usize, BTreeSet<u32>>) {
    let mut by_occurrence = BTreeMap::new();
    let mut per_class = Vec::new();
    for class in &restricted.classes {
        let cone: BTreeSet<u32> = roles
            .iter()
            .filter(|role| {
                role.members.iter().all(|m| {
                    class
                        .cone
                        .get(&m.population)
                        .map(|mask| {
                            let sites = mask.to_sites();
                            (m.first..m.first + m.sites)
                                .all(|site| sites.get(site).copied().unwrap_or(false))
                        })
                        .unwrap_or(false)
                })
            })
            .map(|role| role.ordinal)
            .collect();
        per_class.push(cone.len());
        for retained in &class.fibre {
            by_occurrence.insert(retained.occurrence, cone.clone());
        }
    }
    (per_class, by_occurrence)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn face(occurrence: usize, history: &[u32], face: u32) -> NativeExposureFace {
        NativeExposureFace {
            occurrence,
            exposure: NativeExposure {
                receiver: "terminal-face".to_owned(),
                history: history.to_vec(),
            },
            face,
            exact_digest: String::new(),
            cones: BTreeMap::new(),
        }
    }

    #[test]
    fn a_width_difference_is_a_histogram_of_signed_grains_at_the_finer_grain() {
        let (histogram, grain) = width_difference(&[30, 60, 90], 47, &[30, 90, 60], 47);
        assert_eq!(grain, 47);
        assert_eq!(histogram, vec![(-30, 1), (0, 1), (30, 1)]);
        // A coarser reading is rebased before the subtraction: 2 grains at 2^-45 are 8 at 2^-47.
        let (histogram, grain) = width_difference(&[8], 47, &[2], 45);
        assert_eq!(grain, 47);
        assert_eq!(histogram, vec![(0, 1)]);
    }

    #[test]
    fn equal_faces_over_the_family_collapse_nothing_and_state_condensation() {
        let faces = vec![
            ComposedFace {
                occurrence: 0,
                exposure: NativeExposure {
                    receiver: "r".into(),
                    history: vec![],
                },
                full_face: 7,
                composed_face: 7,
                equal: true,
                width_difference: vec![],
            },
            ComposedFace {
                occurrence: 1,
                exposure: NativeExposure {
                    receiver: "r".into(),
                    history: vec![],
                },
                full_face: 9,
                composed_face: 9,
                equal: true,
                width_difference: vec![],
            },
        ];
        let propagated = vec![NativeTerminalRemainder {
            exposure: NativeExposure {
                receiver: "r".into(),
                history: vec![],
            },
            occurrence: 0,
            coordinates: 2,
            nonpoint_coordinates: 2,
            widest_grains: 3,
            grain: 47,
            widths: vec![(3, 2)],
        }];
        let (collapsed, species) = species_over_family(&faces);
        assert!(collapsed.is_empty());
        assert_eq!(species, Some(NativeRemainderSpecies::Condensation));
        let _ = propagated;
    }

    #[test]
    fn saturation_enlarges_the_declared_exposures_over_fixed_occurrences() {
        // Three occurrences; the empty history identifies 0 and 2; the second history separates
        // them; a third history adds nothing.
        let faces = vec![
            face(0, &[], 7),
            face(1, &[], 9),
            face(2, &[], 7),
            face(0, &[5], 5),
            face(1, &[5], 3),
            face(2, &[5], 6),
            face(0, &[8], 7),
            face(1, &[8], 9),
            face(2, &[8], 7),
        ];
        let exposures: Vec<NativeExposure> = [vec![], vec![5u32], vec![8u32]]
            .into_iter()
            .map(|history| NativeExposure {
                receiver: "terminal-face".to_owned(),
                history,
            })
            .collect();
        let receipt = saturation(&faces, &exposures, 3, 4, 0).unwrap();
        assert_eq!(receipt.steps.len(), 3);
        assert_eq!(receipt.steps[0].classes, 2);
        assert_eq!(receipt.steps[0].relations, 1);
        assert_eq!(receipt.steps[1].classes, 3);
        assert_eq!(receipt.steps[1].removed_relations, 1);
        assert_eq!(receipt.steps[0].identification_preserved, None);
        assert_eq!(receipt.steps[1].identification_preserved, Some(false));
        assert!(receipt.steps[1].observed_consequences_changed);
        assert!(!receipt.steps[2].observed_consequences_changed);
        assert_eq!(
            receipt.last_enlargement_identification_saturated,
            Some(true)
        );
        assert_eq!(
            receipt.last_enlargement_added_no_observed_consequences,
            Some(true)
        );
        assert_eq!(receipt.trailing_identification_preserving_enlargements, 1);
        assert_eq!(receipt.steps[2].extent_roles, 3);
    }

    #[test]
    fn a_singleton_new_face_preserves_identification_but_adds_a_consequence() {
        let faces = vec![face(0, &[], 7), face(0, &[1], 9)];
        let exposures: Vec<_> = faces.iter().map(|f| f.exposure.clone()).collect();
        let receipt = saturation(&faces, &exposures, 0, 0, 0).unwrap();
        assert_eq!(
            receipt.last_enlargement_identification_saturated,
            Some(true)
        );
        assert_eq!(
            receipt.last_enlargement_added_no_observed_consequences,
            Some(false)
        );
        assert_eq!(receipt.steps[1].added_reachable_faces, 1);
        assert_eq!(receipt.steps[1].removed_relations, 0);
    }

    #[test]
    fn saturation_refuses_a_changing_occurrence_population_or_repeated_exposure() {
        let faces = vec![face(0, &[], 7), face(0, &[1], 9), face(1, &[1], 8)];
        let exposures = vec![faces[0].exposure.clone(), faces[1].exposure.clone()];
        assert!(saturation(&faces, &exposures, 0, 0, 0).is_err());
        assert!(saturation(
            &faces[..1],
            &[exposures[0].clone(), exposures[0].clone()],
            0,
            0,
            0
        )
        .is_err());
    }

    fn recorded_deed() -> ComposedVariant {
        serde_json::from_str(include_str!(
            "../../../research/records/2026-09-03_SKE5_receipts/ske5_composed_variant.json"
        ))
        .unwrap()
    }

    #[test]
    fn deposited_deed_validates_without_inventing_its_missing_baseline() {
        let variant = recorded_deed();
        let receipt = variant.assess_deed(true, true);
        assert_eq!(receipt.scope, COMPOSED_DEED_SCOPE);
        assert!(receipt.passed);
        assert_eq!(variant.product.full_resident_octets, None);
        assert_eq!(
            variant.saturation.last_enlargement_identification_saturated,
            Some(true)
        );
        assert_eq!(
            variant
                .saturation
                .last_enlargement_added_no_observed_consequences,
            Some(false)
        );
    }

    #[test]
    fn missing_decoder_or_product_or_false_session_cannot_pass_the_deed() {
        let original = recorded_deed();
        let mut variant = original.clone();
        variant.product.decoder.recurrence.clear();
        assert!(!variant.assess_deed(true, true).passed);
        variant = original.clone();
        variant.product.exposures += 1;
        assert!(!variant.assess_deed(true, true).passed);
        variant = original.clone();
        variant.session_generations[1].0 = 0;
        assert!(!variant.assess_deed(true, true).passed);
        variant = original.clone();
        variant.faces[0].composed_face += 1; // Its stale `equal` flag remains true.
        assert!(!variant.assess_deed(true, true).passed);
        variant = original;
        variant.saturation.last_enlargement_identification_saturated = Some(false);
        assert!(!variant.assess_deed(true, true).passed);
    }
}
