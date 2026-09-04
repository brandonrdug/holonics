//! The composed Athena variant: Eros composes the class ecologies of a Soulkiller return into
//! one body, and the compression law is stated over that body.
//!
//! Eros is an interpretation, not a module (`canon/05_ONTOLOGY.md`): the operational pattern in
//! which differences meet, constrain one another, found new local relations, and return
//! consequences.  Here that pattern is the act of composition: the classes a family's
//! excitation founded (`NativeConeRestrictedEcology`, the productive lane) are taken together as
//! one variant whose body is the union of their cones, and the family's declared exposures are
//! driven through that one body.  The composition itself is exterior arithmetic over the return;
//! the body is mounted from the rest alone and the recurrence runs on it unchanged.
//!
//! What the compression law owes on the composed variant (`canon/TABLET_THE_COMPRESSION.md`,
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
//! - **saturation** under the growing family, structurally: what each added exposure adds in
//!   classes, separations, extent, insufficiency, and reachable faces, and whether the last
//!   lawful crossings added nothing.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::native_ecology::holonic_intelligence::{
    NativeClassRemainder, NativeCollapsedPair, NativeConeRestrictedEcology, NativeExposure,
    NativeExposureFace, NativeRemainderSpecies, NativeSignatureQuotient, NativeTerminalRemainder,
};
use serde::{Deserialize, Serialize};

pub const COMPOSED_VARIANT_SCHEMA: &str = "athena-alpha.composed-variant.v1";

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
    pub added_anything: bool,
}

/// Saturation under the growing family, structurally: the steps, and how many of the last
/// crossings added nothing.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SaturationReceipt {
    pub steps: Vec<SaturationStep>,
    pub trailing_crossings_that_added_nothing: usize,
    /// Saturation is stated only when the last crossing added nothing; it is never inferred from
    /// exhaustion of the declared family.
    pub last_crossing_added_nothing: bool,
}

/// The composed variant's return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComposedVariant {
    pub schema: String,
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
    /// The release receiver: every pass condition of the blueprint, read on the card.
    pub release: ReleaseReceipt,
}

/// The release receiver for SKE5: each condition the blueprint's pass names, as read.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReleaseReceipt {
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

/// The histogram of per-coordinate width differences (composed minus full), in grains of the
/// finer of the two grains: each width is rebased to that grain before the subtraction, so two
/// readings at different grains are never subtracted as bare counts.
pub fn width_difference(full: &[u32], full_grain: u32, composed: &[u32], composed_grain: u32) -> (Vec<(i64, usize)>, u32) {
    let grain = full_grain.max(composed_grain);
    let scale = |width: u32, own: u32| -> i64 { i64::from(width) << (grain - own) };
    let mut histogram: BTreeMap<i64, usize> = BTreeMap::new();
    for (f, c) in full.iter().zip(composed) {
        *histogram.entry(scale(*c, composed_grain) - scale(*f, full_grain)).or_default() += 1;
    }
    (histogram.into_iter().collect(), grain)
}

/// The collapsed pairs of the composed body against the full operator over the family, and the
/// species they state on that domain; a face that does not descend refuses a species.
pub fn species_over_family(faces: &[ComposedFace]) -> (Vec<NativeCollapsedPair>, Option<NativeRemainderSpecies>) {
    let domain: Vec<(usize, NativeExposure, u32, u32)> = faces
        .iter()
        .map(|f| (f.occurrence, f.exposure.clone(), f.composed_face, f.full_face))
        .collect();
    let collapsed = NativeClassRemainder::collapsed_pairs(&domain);
    let failures = faces.iter().filter(|f| !f.equal).count();
    let species = NativeClassRemainder::species_of(&collapsed, failures);
    (collapsed, species)
}

/// Saturation as the formal `Saturated` reads it: the occurrences stay fixed and the declared
/// exposures (receiver and history) are enlarged one at a time in declared order; after each
/// enlargement the signature quotient, its separations, the generators (the histories
/// declared), the relations (the pairs identified), the separators (the histories that reopened
/// an identification), the obstructions (refusals), and the reachable consequences (the
/// distinct faces) are read again.  The extent is that of the classes, which the enlargement
/// can only separate, never merge.
pub fn saturation(
    faces: &[NativeExposureFace],
    exposures_in_order: &[NativeExposure],
    class_cone_roles_by_occurrence: &BTreeMap<usize, BTreeSet<u32>>,
    roles: usize,
    refusals: usize,
) -> Result<SaturationReceipt, String> {
    let occurrences: BTreeSet<usize> = faces.iter().map(|f| f.occurrence).collect();
    let mut steps = Vec::with_capacity(exposures_in_order.len());
    let (mut classes, mut separations, mut relations, mut reachable) = (0usize, 0usize, 0usize, 0usize);
    let extent_roles: BTreeSet<u32> = class_cone_roles_by_occurrence.values().flatten().copied().collect();
    for at in 0..exposures_in_order.len() {
        let declared = &exposures_in_order[..=at];
        let restricted: Vec<NativeExposureFace> = faces.iter().filter(|f| declared.contains(&f.exposure)).cloned().collect();
        let quotient = NativeSignatureQuotient::found(&restricted).map_err(|e| e.to_string())?;
        let relation_count: usize = quotient.classes.iter().map(|c| c.occurrences.len() * c.occurrences.len().saturating_sub(1) / 2).sum();
        let reachable_faces: BTreeSet<u32> = restricted.iter().map(|f| f.face).collect();
        let step = SaturationStep {
            occurrence: occurrences.len(),
            exposure: declared[at].clone(),
            classes: quotient.classes.len(),
            separations: quotient.separations.len(),
            generators: declared.len(),
            relations: relation_count,
            obstructions: refusals,
            extent_roles: extent_roles.len(),
            insufficiency_roles: roles.saturating_sub(extent_roles.len()),
            reachable_faces: reachable_faces.len(),
            added_classes: quotient.classes.len().saturating_sub(classes),
            added_separations: quotient.separations.len().saturating_sub(separations),
            removed_relations: relations.saturating_sub(relation_count),
            added_reachable_faces: reachable_faces.len().saturating_sub(reachable),
            added_anything: at == 0
                || quotient.classes.len() != classes
                || quotient.separations.len() != separations
                || relation_count != relations
                || reachable_faces.len() != reachable,
        };
        classes = quotient.classes.len();
        separations = quotient.separations.len();
        relations = relation_count;
        reachable = reachable_faces.len();
        steps.push(step);
    }
    let trailing = steps.iter().rev().take_while(|s| !s.added_anything).count();
    Ok(SaturationReceipt {
        last_crossing_added_nothing: steps.last().is_some_and(|s| !s.added_anything),
        trailing_crossings_that_added_nothing: trailing,
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
                            (m.first..m.first + m.sites).all(|site| sites.get(site).copied().unwrap_or(false))
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
            ComposedFace { occurrence: 0, exposure: NativeExposure { receiver: "r".into(), history: vec![] }, full_face: 7, composed_face: 7, equal: true, width_difference: vec![] },
            ComposedFace { occurrence: 1, exposure: NativeExposure { receiver: "r".into(), history: vec![] }, full_face: 9, composed_face: 9, equal: true, width_difference: vec![] },
        ];
        let propagated = vec![NativeTerminalRemainder {
            exposure: NativeExposure { receiver: "r".into(), history: vec![] },
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
            face(0, &[], 7), face(1, &[], 9), face(2, &[], 7),
            face(0, &[5], 5), face(1, &[5], 3), face(2, &[5], 6),
            face(0, &[8], 7), face(1, &[8], 9), face(2, &[8], 7),
        ];
        let exposures: Vec<NativeExposure> = [vec![], vec![5u32], vec![8u32]]
            .into_iter()
            .map(|history| NativeExposure { receiver: "terminal-face".to_owned(), history })
            .collect();
        let cones = BTreeMap::from([(0usize, BTreeSet::from([0u32, 1])), (1, BTreeSet::from([1, 2])), (2, BTreeSet::from([0, 1]))]);
        let receipt = saturation(&faces, &exposures, &cones, 4, 0).unwrap();
        assert_eq!(receipt.steps.len(), 3);
        assert_eq!(receipt.steps[0].classes, 2);
        assert_eq!(receipt.steps[0].relations, 1);
        assert_eq!(receipt.steps[1].classes, 3);
        assert_eq!(receipt.steps[1].removed_relations, 1);
        assert!(receipt.steps[1].added_anything);
        assert!(!receipt.steps[2].added_anything);
        assert!(receipt.last_crossing_added_nothing);
        assert_eq!(receipt.trailing_crossings_that_added_nothing, 1);
        assert_eq!(receipt.steps[2].extent_roles, 3);
    }
}
