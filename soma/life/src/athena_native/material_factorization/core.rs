//! One cross-codec material aperture into the situated Athena ecology.
//!
//! Exterior presentations never choose a native factor.  A caused world return supplies an exact
//! finite incidence population; this owner recognizes only the incidence law, constructs the
//! common mathematical consequence, and rebases that section through the rank already owned by
//! the L2 body.  Unresolved returns retain every candidate and their shortest separating
//! intervention.

use std::{
    cell::RefCell,
    collections::{BTreeMap, BTreeSet},
};

use serde::Serialize;
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::mathematical_particle::{
    NativeConstraintCell, NativeExactConsequenceFace, NativeGeometryCell, NativeGeometryVertex,
    NativeMathematicalComplex, NativeOperationCell,
};
use crate::mathematical_source::{
    HierarchicalOpticalPassage, NativeHierarchicalOpticalConsequence,
};

use crate::athena_native::{LaboratoryCultivatedAthenaRest, SituatedCultivatedAthenaRest};

pub const MATERIAL_NATIVE_FACTORIZATION_SCHEMA: &str = "soma-life.material-native-factorization.v1";
pub const MATERIAL_RECEIVER_INSUFFICIENCY_SCHEMA: &str =
    "soma-life.material-receiver-insufficiency.v1";
pub const MATERIAL_AFFINE_TRANSPORT_SCHEMA: &str = "soma-life.material-affine-transport.v1";

/// Exterior delivery testimony.  `delivery_faces` may be removed, reordered, or renamed without
/// changing any native operation coordinate or factor support.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AddressedMaterialOccurrence {
    pub occurrence: String,
    pub payload_sha256: String,
    pub payload_octets: u64,
    pub predecessor_occurrence: Option<String>,
    pub delivery_faces: Vec<String>,
    pub open_exterior: Vec<String>,
}

impl AddressedMaterialOccurrence {
    pub fn found(
        occurrence: impl Into<String>,
        payload: &[u8],
        predecessor_occurrence: Option<String>,
        delivery_faces: Vec<String>,
        open_exterior: Vec<String>,
    ) -> Result<Self, MaterialFactorizationError> {
        let occurrence = Self {
            occurrence: occurrence.into(),
            payload_sha256: hex_sha256(payload),
            payload_octets: u64::try_from(payload.len())
                .map_err(|_| MaterialFactorizationError::Extent)?,
            predecessor_occurrence,
            delivery_faces,
            open_exterior,
        };
        occurrence.validate()?;
        Ok(occurrence)
    }

    pub fn without_delivery_faces(&self) -> Self {
        let mut occurrence = self.clone();
        occurrence.delivery_faces.clear();
        occurrence
    }

    pub fn with_reordered_delivery_faces(&self) -> Self {
        let mut occurrence = self.clone();
        occurrence.delivery_faces.reverse();
        occurrence
    }

    fn validate(&self) -> Result<(), MaterialFactorizationError> {
        if self.occurrence.is_empty()
            || !is_sha256(&self.payload_sha256)
            || self.payload_octets == 0
            || self
                .predecessor_occurrence
                .as_ref()
                .is_some_and(String::is_empty)
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(MaterialFactorizationError::MaterialOccurrence);
        }
        Ok(())
    }
}

/// One returned result cell and its complete input incidence.  A disjoint-union cell touches
/// exactly one input member.  An independent-product cell touches one member on each axis.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CausalResultCell {
    pub occurrence: String,
    pub left_member: Option<String>,
    pub right_member: Option<String>,
}

/// Exterior apparatus testimony can certify that a compiler, kernel, sensor, or other world body
/// returned.  Its name and verdict are not inputs to the incidence classification.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ExteriorWorldReturnTestimony {
    pub occurrence: String,
    pub apparatus_face: String,
    pub accepted: bool,
    pub returned_payload_sha256: String,
    pub returned_payload_octets: u64,
    pub open_exterior: Vec<String>,
}

impl ExteriorWorldReturnTestimony {
    pub fn found(
        occurrence: impl Into<String>,
        apparatus_face: impl Into<String>,
        accepted: bool,
        returned_payload: &[u8],
        open_exterior: Vec<String>,
    ) -> Result<Self, MaterialFactorizationError> {
        let testimony = Self {
            occurrence: occurrence.into(),
            apparatus_face: apparatus_face.into(),
            accepted,
            returned_payload_sha256: hex_sha256(returned_payload),
            returned_payload_octets: u64::try_from(returned_payload.len())
                .map_err(|_| MaterialFactorizationError::Extent)?,
            open_exterior,
        };
        testimony.validate()?;
        Ok(testimony)
    }

    fn validate(&self) -> Result<(), MaterialFactorizationError> {
        if self.occurrence.is_empty()
            || self.apparatus_face.is_empty()
            || !is_sha256(&self.returned_payload_sha256)
            || self.returned_payload_octets == 0
            || self.open_exterior.iter().any(String::is_empty)
        {
            return Err(MaterialFactorizationError::WorldReturn);
        }
        Ok(())
    }
}

/// The law is inferred from complete cell incidence; the caller never supplies this enum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum CausalPopulationLaw {
    DisjointUnion,
    IndependentProduct,
}

/// A caused operation return.  Input names and apparatus survive as lineage while validation
/// derives the operation law solely from the returned incidence population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CausalOperationWorldReturn {
    pub occurrence: String,
    pub predecessor_material_occurrence: String,
    pub left_input: Vec<String>,
    pub right_input: Vec<String>,
    pub result_cells: Vec<CausalResultCell>,
    pub apparatus: ExteriorWorldReturnTestimony,
    pub open_exterior: Vec<String>,
}

impl CausalOperationWorldReturn {
    pub fn found(
        occurrence: impl Into<String>,
        predecessor_material_occurrence: impl Into<String>,
        left_input: Vec<String>,
        right_input: Vec<String>,
        result_cells: Vec<CausalResultCell>,
        apparatus: ExteriorWorldReturnTestimony,
        open_exterior: Vec<String>,
    ) -> Result<Self, MaterialFactorizationError> {
        let returned = Self {
            occurrence: occurrence.into(),
            predecessor_material_occurrence: predecessor_material_occurrence.into(),
            left_input,
            right_input,
            result_cells,
            apparatus,
            open_exterior,
        };
        returned.validate()?;
        Ok(returned)
    }

    pub fn law(&self) -> Result<CausalPopulationLaw, MaterialFactorizationError> {
        derive_population_law(&self.left_input, &self.right_input, &self.result_cells)
    }

    pub fn invariant(&self) -> Result<CausalOperationInvariant, MaterialFactorizationError> {
        self.validate()?;
        let law = self.law()?;
        let left_population = exact_i64(self.left_input.len())?;
        let right_population = exact_i64(self.right_input.len())?;
        let returned_population = exact_i64(self.result_cells.len())?;
        let left_extension_returned_population = match law {
            CausalPopulationLaw::DisjointUnion => returned_population
                .checked_add(1)
                .ok_or(MaterialFactorizationError::Extent)?,
            CausalPopulationLaw::IndependentProduct => right_population
                .checked_mul(
                    left_population
                        .checked_add(1)
                        .ok_or(MaterialFactorizationError::Extent)?,
                )
                .ok_or(MaterialFactorizationError::Extent)?,
        };
        let right_extension_returned_population = match law {
            CausalPopulationLaw::DisjointUnion => returned_population
                .checked_add(1)
                .ok_or(MaterialFactorizationError::Extent)?,
            CausalPopulationLaw::IndependentProduct => left_population
                .checked_mul(
                    right_population
                        .checked_add(1)
                        .ok_or(MaterialFactorizationError::Extent)?,
                )
                .ok_or(MaterialFactorizationError::Extent)?,
        };
        Ok(CausalOperationInvariant {
            law,
            left_population,
            right_population,
            returned_population,
            left_extension_returned_population,
            right_extension_returned_population,
            incidence_degree: match law {
                CausalPopulationLaw::DisjointUnion => 1,
                CausalPopulationLaw::IndependentProduct => 2,
            },
        })
    }

    fn validate(&self) -> Result<(), MaterialFactorizationError> {
        self.apparatus.validate()?;
        if self.occurrence.is_empty()
            || self.predecessor_material_occurrence.is_empty()
            || self.occurrence == self.predecessor_material_occurrence
            || self.left_input.is_empty()
            || self.right_input.is_empty()
            || self.result_cells.is_empty()
            || self.open_exterior.iter().any(String::is_empty)
            || !unique_nonempty(self.left_input.iter().map(String::as_str))
            || !unique_nonempty(self.right_input.iter().map(String::as_str))
            || !unique_nonempty(
                self.result_cells
                    .iter()
                    .map(|cell| cell.occurrence.as_str()),
            )
            || self
                .left_input
                .iter()
                .any(|left| self.right_input.contains(left))
        {
            return Err(MaterialFactorizationError::WorldReturn);
        }
        self.law().map(|_| ())
    }
}

/// Source-neutral causal signature.  The two one-member extensions are successor histories, not
/// scalar scores; they separate operations which happen to share one returned cardinality.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CausalOperationInvariant {
    pub law: CausalPopulationLaw,
    pub left_population: i64,
    pub right_population: i64,
    pub returned_population: i64,
    pub left_extension_returned_population: i64,
    pub right_extension_returned_population: i64,
    pub incidence_degree: u32,
}

impl CausalOperationInvariant {
    /// One receiver section over the standing four-cycle chart.  Its extent is derived from the
    /// four causal quantities named here and is checked against the body's actual rank.
    pub fn relation_current_section(&self) -> Result<Vec<i64>, MaterialFactorizationError> {
        let returned_change = self
            .right_extension_returned_population
            .checked_sub(self.returned_population)
            .ok_or(MaterialFactorizationError::Extent)?;
        Ok(vec![
            self.left_population,
            self.right_population,
            self.returned_population,
            returned_change,
        ])
    }

    pub fn identity_sha256(&self) -> Result<String, MaterialFactorizationError> {
        digest_json(self)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialReceiverChartAxis {
    pub coordinate: u32,
    pub situated_thread: String,
}

/// Explicit basis testimony.  Both matrices are retained and both identity composites are
/// checked; the chart does not turn the four directions into semantic classes.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialReceiverChart {
    pub axes: Vec<MaterialReceiverChartAxis>,
    pub forward: Vec<Vec<i64>>,
    pub inverse: Vec<Vec<i64>>,
    pub forward_then_inverse_is_identity: bool,
    pub inverse_then_forward_is_identity: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct SituatedMaterialFactorSupport {
    pub coordinate: u32,
    pub situated_thread: String,
    pub coefficient: i64,
    pub incident_symmetric_families: Vec<String>,
    pub exact_reconstruction_fibres: Vec<String>,
}

/// Exact testimony that one later situated section crossed one cultivated affine cell by linear
/// extension. The singular rested owner retains the barycentric population and the
/// landmark-to-four-fibre correspondence needed to reconstruct every local term.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialAffineCellTransportReceipt {
    pub cell_address: String,
    pub transported_field_identity_sha256: String,
    pub landmark_population: usize,
    pub local_fibre_term_population: usize,
    pub barycentric_total_mass: u64,
    pub augmentation_reconstructs_entering_section: bool,
}

/// Exterior testimony for the singular card-owned word which conducts coupled current,
/// participant incidence, and the complete affine field before any leaf returns to the CPU path.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialIntegratedResidentApparatusReceipt {
    pub schema: String,
    pub device: String,
    pub context_identity: usize,
    pub one_underlying_context: bool,
    pub launches: u64,
    pub synchronizations: u64,
    pub successor_host_ingress_octets: u64,
    pub successor_host_egress_octets: u64,
    pub intermediate_host_egress_octets: u64,
    pub resident_invariant_octets: u64,
    pub invariant_transport_reuploaded: bool,
    pub cpu_semantic_replay_after_device: bool,
}

/// The complete, unselected barycentric field over a cultivated laboratory base.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialAffineTransportReceipt {
    pub schema: String,
    pub standing_rest_identity_sha256: String,
    pub entering_section: Vec<i64>,
    pub addressed_landmark_population: usize,
    pub addressed_cell_population: usize,
    pub local_fibre_term_population: usize,
    pub cell_sections: Vec<MaterialAffineCellTransportReceipt>,
    pub every_cell_augments_to_entering_section: bool,
    pub complete_cell_reconstruction_fibre: Vec<String>,
    /// Exterior apparatus testimony populated only after the complete field has crossed the
    /// resident card. It is excluded from native field identity.
    pub resident_apparatus:
        Option<holonic_engine::cuda_refine::ResidentAffineBarycentricTransportReturn>,
    /// The composed apparatus boundary. It is excluded from native field identity.
    pub integrated_resident_apparatus: Option<MaterialIntegratedResidentApparatusReceipt>,
    pub identity_sha256: String,
}

impl MaterialAffineTransportReceipt {
    pub(crate) fn found(
        standing_rest_identity_sha256: String,
        entering_section: Vec<i64>,
        addressed_landmark_population: usize,
        cell_sections: Vec<MaterialAffineCellTransportReceipt>,
    ) -> Result<Self, MaterialFactorizationError> {
        if !is_sha256(&standing_rest_identity_sha256)
            || entering_section.is_empty()
            || addressed_landmark_population == 0
            || cell_sections.is_empty()
            || cell_sections.iter().any(|cell| {
                cell.cell_address.is_empty()
                    || !is_sha256(&cell.transported_field_identity_sha256)
                    || cell.landmark_population == 0
                    || cell.local_fibre_term_population == 0
                    || cell.barycentric_total_mass == 0
                    || !cell.augmentation_reconstructs_entering_section
            })
        {
            return Err(MaterialFactorizationError::AffineTransport);
        }
        let local_fibre_term_population = cell_sections
            .iter()
            .try_fold(0usize, |sum, cell| {
                sum.checked_add(cell.local_fibre_term_population)
            })
            .ok_or(MaterialFactorizationError::Extent)?;
        let complete_cell_reconstruction_fibre = cell_sections
            .iter()
            .map(|cell| cell.cell_address.clone())
            .collect::<Vec<_>>();
        if complete_cell_reconstruction_fibre
            .iter()
            .collect::<BTreeSet<_>>()
            .len()
            != complete_cell_reconstruction_fibre.len()
        {
            return Err(MaterialFactorizationError::AffineTransport);
        }
        let every_cell_augments_to_entering_section = cell_sections
            .iter()
            .all(|cell| cell.augmentation_reconstructs_entering_section);
        let identity_sha256 = digest_json(&(
            MATERIAL_AFFINE_TRANSPORT_SCHEMA,
            &standing_rest_identity_sha256,
            &entering_section,
            addressed_landmark_population,
            &cell_sections,
            &complete_cell_reconstruction_fibre,
        ))?;
        Ok(Self {
            schema: MATERIAL_AFFINE_TRANSPORT_SCHEMA.to_owned(),
            standing_rest_identity_sha256,
            entering_section,
            addressed_landmark_population,
            addressed_cell_population: cell_sections.len(),
            local_fibre_term_population,
            cell_sections,
            every_cell_augments_to_entering_section,
            complete_cell_reconstruction_fibre,
            resident_apparatus: None,
            integrated_resident_apparatus: None,
            identity_sha256,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialShortestSeparator {
    pub receiver: String,
    pub history: String,
    pub left_returned_population: i64,
    pub right_returned_population: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialCandidateSection {
    pub world_return_occurrence: String,
    pub native_operation_identity_sha256: String,
    pub invariant: CausalOperationInvariant,
    pub relation_current_section: Vec<i64>,
}

/// The complete successful cross-codec factorization.  The mathematical complex retains the
/// occurrence-bearing realization; `native_operation_identity_sha256` is its receiver quotient
/// and deliberately excludes payload bytes, material kind, codec, filename, and apparatus name.
#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialNativeFactorization {
    pub schema: String,
    pub occurrence: String,
    pub material_occurrence: String,
    pub world_return_occurrences: Vec<String>,
    pub predecessor_rest_identity_sha256: String,
    pub native_operation_identity_sha256: String,
    pub invariant: CausalOperationInvariant,
    pub relation_current_section: Vec<i64>,
    pub mathematical_complex: NativeMathematicalComplex,
    pub receiver_chart: MaterialReceiverChart,
    pub factor_support: Vec<SituatedMaterialFactorSupport>,
    pub complete_symmetric_family_support: Vec<String>,
    /// Absent only on a standing which owns no cultivated affine base.
    pub cultivated_affine_transport: Option<MaterialAffineTransportReceipt>,
    pub reconstruction_fibre: Vec<String>,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialReceiverInsufficiency {
    pub schema: String,
    pub at_material_occurrence: String,
    pub predecessor_rest_identity_sha256: String,
    pub candidate_sections: Vec<MaterialCandidateSection>,
    pub reconstruction_fibre: Vec<String>,
    pub shortest_separator: MaterialShortestSeparator,
    pub open_exterior: Vec<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum MaterialFactorizationReturn {
    Supported(MaterialNativeFactorization),
    Insufficient(MaterialReceiverInsufficiency),
}

/// Exact incidence binding between one later world return and every hierarchical optical
/// constraint section whose ordered addressed members it realizes.  Relation-glyph strings and
/// object-class faces are deliberately absent: they remain exterior testimony in the borrowed
/// optical passage and never select this binding.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct HierarchicalOpticalConstraintBinding {
    pub world_return_occurrence: String,
    pub equation_address: String,
    pub relation_glyph_address: String,
    pub constraint_form_sha256: String,
}

/// A validated, source-neutral view of hierarchical optical geometry at the material aperture.
///
/// The view borrows the complete passage rather than cloning a second optical ecology.  Therefore
/// every scale, holon, alternative cover, glyph reconstruction fibre and open identity remains
/// reachable while the material candidate family is factored.  Candidate bindings are derived
/// only from equality of the ordered before/after address populations.
#[derive(Debug)]
pub struct HierarchicalOpticalMaterialCandidates<'optical> {
    material: &'optical AddressedMaterialOccurrence,
    passage: &'optical HierarchicalOpticalPassage,
    returned: &'optical [CausalOperationWorldReturn],
    bindings: Vec<HierarchicalOpticalConstraintBinding>,
}

impl<'optical> HierarchicalOpticalMaterialCandidates<'optical> {
    pub fn found(
        material: &'optical AddressedMaterialOccurrence,
        passage: &'optical HierarchicalOpticalPassage,
        returned: &'optical [CausalOperationWorldReturn],
    ) -> Result<Self, MaterialFactorizationError> {
        material.validate()?;
        passage
            .validate()
            .map_err(|error| MaterialFactorizationError::Optical(error.to_string()))?;
        if material.payload_sha256 != passage.predecessor_source_sha256 || returned.is_empty() {
            return Err(MaterialFactorizationError::OpticalLineage);
        }

        let mut bindings = Vec::new();
        for world in returned {
            world.validate()?;
            if world.predecessor_material_occurrence != material.occurrence {
                return Err(MaterialFactorizationError::Lineage);
            }
            let before = world.left_input.iter().collect::<BTreeSet<_>>();
            let after = world.right_input.iter().collect::<BTreeSet<_>>();
            let mut matched = 0usize;
            for section in &passage.native_consequence.equation_constraint_sections {
                let section_before = section
                    .before_member_addresses
                    .iter()
                    .collect::<BTreeSet<_>>();
                let section_after = section
                    .after_member_addresses
                    .iter()
                    .collect::<BTreeSet<_>>();
                if before == section_before && after == section_after {
                    matched = matched
                        .checked_add(1)
                        .ok_or(MaterialFactorizationError::Extent)?;
                    bindings.push(HierarchicalOpticalConstraintBinding {
                        world_return_occurrence: world.occurrence.clone(),
                        equation_address: section.equation_address.clone(),
                        relation_glyph_address: section.relation_glyph_address.clone(),
                        constraint_form_sha256: section.constraint_form_sha256.clone(),
                    });
                }
            }
            if matched == 0 {
                return Err(MaterialFactorizationError::OpticalCandidateLineage {
                    world_return_occurrence: world.occurrence.clone(),
                });
            }
        }
        bindings.sort_by(|left, right| {
            (
                &left.world_return_occurrence,
                &left.equation_address,
                &left.relation_glyph_address,
                &left.constraint_form_sha256,
            )
                .cmp(&(
                    &right.world_return_occurrence,
                    &right.equation_address,
                    &right.relation_glyph_address,
                    &right.constraint_form_sha256,
                ))
        });
        Ok(Self {
            material,
            passage,
            returned,
            bindings,
        })
    }

    pub fn material(&self) -> &AddressedMaterialOccurrence {
        self.material
    }

    pub fn passage(&self) -> &HierarchicalOpticalPassage {
        self.passage
    }

    pub fn native_consequence(&self) -> &NativeHierarchicalOpticalConsequence {
        &self.passage.native_consequence
    }

    pub fn world_returns(&self) -> &[CausalOperationWorldReturn] {
        self.returned
    }

    pub fn bindings(&self) -> &[HierarchicalOpticalConstraintBinding] {
        &self.bindings
    }

    fn every_candidate_has_one_constraint_section(&self) -> bool {
        self.returned.iter().all(|world| {
            self.bindings
                .iter()
                .filter(|binding| binding.world_return_occurrence == world.occurrence)
                .count()
                == 1
        })
    }
}

/// The hierarchical optical return retains its complete borrowed optical body beside the existing
/// material factorization return.  `Insufficient` is returned both for plural operation sections
/// and for a world return that still matches plural optical constraint occurrences; neither face
/// is guessed closed from an inherited glyph string.
#[derive(Debug)]
pub enum HierarchicalOpticalMaterialReturn<'optical> {
    Supported {
        passage: &'optical HierarchicalOpticalPassage,
        bindings: Vec<HierarchicalOpticalConstraintBinding>,
        factorization: MaterialNativeFactorization,
    },
    Insufficient {
        passage: &'optical HierarchicalOpticalPassage,
        bindings: Vec<HierarchicalOpticalConstraintBinding>,
        material_return: MaterialFactorizationReturn,
        open_identity: Vec<String>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct MaterialNaturalityReceipt {
    pub left_material_occurrence: String,
    pub right_material_occurrence: String,
    pub receiver: String,
    pub native_operation_equal: bool,
    pub relation_current_equal: bool,
    pub situated_support_equal: bool,
    pub affine_transport_equal: bool,
    pub square_commutes: bool,
    pub shortest_separator: Option<MaterialShortestSeparator>,
}

/// The source-neutral interface required by the material aperture.  L2 and its L5 type-state
/// successor expose the same four-cycle receiver chart; returned morphology changes incident
/// constitutive support without being miscounted as a fifth winding coordinate.
pub trait MaterialFactorizationStanding {
    fn validate_material_standing(&self) -> Result<(), String>;
    fn material_standing_identity(&self) -> &str;
    fn material_standing_branches(&self) -> &[crate::athena_native::SituatedCultivationBranch];
    fn material_standing_ecology(&self)
        -> &holonic_engine::native_spool::NativeSituatedSpoolBundle;
    fn material_standing_realization(
        &self,
    ) -> &crate::athena_native::ReceiverHistoryRealizationPassage;

    fn material_affine_transport(
        &self,
        _entering_section: &[i64],
    ) -> Result<Option<MaterialAffineTransportReceipt>, String> {
        Ok(None)
    }
}

impl MaterialFactorizationStanding for SituatedCultivatedAthenaRest {
    fn validate_material_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn material_standing_identity(&self) -> &str {
        self.identity()
    }

    fn material_standing_branches(&self) -> &[crate::athena_native::SituatedCultivationBranch] {
        self.branches()
    }

    fn material_standing_ecology(
        &self,
    ) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.ecology()
    }

    fn material_standing_realization(
        &self,
    ) -> &crate::athena_native::ReceiverHistoryRealizationPassage {
        self.realization()
    }
}

impl MaterialFactorizationStanding for LaboratoryCultivatedAthenaRest {
    fn validate_material_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }

    fn material_standing_identity(&self) -> &str {
        self.identity()
    }

    fn material_standing_branches(&self) -> &[crate::athena_native::SituatedCultivationBranch] {
        self.branches()
    }

    fn material_standing_ecology(
        &self,
    ) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.ecology()
    }

    fn material_standing_realization(
        &self,
    ) -> &crate::athena_native::ReceiverHistoryRealizationPassage {
        self.realization()
    }
}

pub struct MaterialFactorizationAperture<'a, Standing: MaterialFactorizationStanding> {
    rest: &'a Standing,
    chart: MaterialReceiverChart,
    /// Exact native transport is a function of the rested body and entered section, not of the
    /// exterior codec face which presented that section.  Keep one witness per distinct section
    /// for the lifetime of this aperture so cross-codec comparisons do not reconstruct the same
    /// complete affine field serially.  Material occurrence lineage remains in each returned
    /// factorization and is never used as a native transport key.
    shared_affine_transports: RefCell<BTreeMap<Vec<i64>, Option<MaterialAffineTransportReceipt>>>,
}

impl<'a, Standing: MaterialFactorizationStanding> MaterialFactorizationAperture<'a, Standing> {
    pub fn found(rest: &'a Standing) -> Result<Self, MaterialFactorizationError> {
        rest.validate_material_standing()
            .map_err(MaterialFactorizationError::Rest)?;
        let axes = rest
            .material_standing_branches()
            .iter()
            .enumerate()
            .map(|(coordinate, branch)| {
                Ok(MaterialReceiverChartAxis {
                    coordinate: u32::try_from(coordinate)
                        .map_err(|_| MaterialFactorizationError::Extent)?,
                    situated_thread: branch.thread_address.clone(),
                })
            })
            .collect::<Result<Vec<_>, MaterialFactorizationError>>()?;
        if axes.is_empty() {
            return Err(MaterialFactorizationError::Chart);
        }
        let forward = identity_matrix(axes.len());
        let inverse = identity_matrix(axes.len());
        let chart = MaterialReceiverChart {
            axes,
            forward: forward.clone(),
            inverse: inverse.clone(),
            forward_then_inverse_is_identity: multiply(&forward, &inverse)? == forward,
            inverse_then_forward_is_identity: multiply(&inverse, &forward)? == inverse,
        };
        if !chart.forward_then_inverse_is_identity || !chart.inverse_then_forward_is_identity {
            return Err(MaterialFactorizationError::Chart);
        }
        Ok(Self {
            rest,
            chart,
            shared_affine_transports: RefCell::new(BTreeMap::new()),
        })
    }

    pub fn factor(
        &self,
        material: &AddressedMaterialOccurrence,
        returned: &CausalOperationWorldReturn,
    ) -> Result<MaterialNativeFactorization, MaterialFactorizationError> {
        material.validate()?;
        returned.validate()?;
        if returned.predecessor_material_occurrence != material.occurrence {
            return Err(MaterialFactorizationError::Lineage);
        }
        self.factor_one(material, returned, vec![returned.occurrence.clone()])
    }

    pub fn factor_candidates(
        &self,
        material: &AddressedMaterialOccurrence,
        returned: &[CausalOperationWorldReturn],
    ) -> Result<MaterialFactorizationReturn, MaterialFactorizationError> {
        material.validate()?;
        if returned.is_empty() {
            return Err(MaterialFactorizationError::WorldReturn);
        }
        let mut candidates = Vec::with_capacity(returned.len());
        for world in returned {
            world.validate()?;
            if world.predecessor_material_occurrence != material.occurrence {
                return Err(MaterialFactorizationError::Lineage);
            }
            let invariant = world.invariant()?;
            candidates.push(MaterialCandidateSection {
                world_return_occurrence: world.occurrence.clone(),
                native_operation_identity_sha256: invariant.identity_sha256()?,
                relation_current_section: invariant.relation_current_section()?,
                invariant,
            });
        }
        candidates.sort_by(|left, right| {
            left.native_operation_identity_sha256
                .cmp(&right.native_operation_identity_sha256)
                .then(
                    left.world_return_occurrence
                        .cmp(&right.world_return_occurrence),
                )
        });
        let identities = candidates
            .iter()
            .map(|candidate| candidate.native_operation_identity_sha256.as_str())
            .collect::<BTreeSet<_>>();
        let fibre = candidates
            .iter()
            .map(|candidate| candidate.world_return_occurrence.clone())
            .collect::<Vec<_>>();
        if identities.len() == 1 {
            return self
                .factor_one(material, &returned[0], fibre)
                .map(MaterialFactorizationReturn::Supported);
        }
        let separator = shortest_separator(&candidates[0].invariant, &candidates[1].invariant)
            .ok_or(MaterialFactorizationError::UnseparatedAmbiguity)?;
        Ok(MaterialFactorizationReturn::Insufficient(
            MaterialReceiverInsufficiency {
                schema: MATERIAL_RECEIVER_INSUFFICIENCY_SCHEMA.to_owned(),
                at_material_occurrence: material.occurrence.clone(),
                predecessor_rest_identity_sha256: self.rest.material_standing_identity().to_owned(),
                candidate_sections: candidates,
                reconstruction_fibre: fibre,
                shortest_separator: separator,
                open_exterior: vec![
                    "the exterior occurrence admits plural operation-current sections".to_owned(),
                    "a later receiver or world return must separate the retained fibre".to_owned(),
                ],
            },
        ))
    }

    /// Factor one validated hierarchical optical candidate family without consulting glyph text,
    /// choosing an alternative cover, or dropping the passage's reconstruction fibres.
    pub fn factor_hierarchical_optical_candidates<'optical>(
        &self,
        candidates: &HierarchicalOpticalMaterialCandidates<'optical>,
    ) -> Result<HierarchicalOpticalMaterialReturn<'optical>, MaterialFactorizationError> {
        let material_return = self.factor_candidates(candidates.material, candidates.returned)?;
        if candidates.every_candidate_has_one_constraint_section()
            && matches!(&material_return, MaterialFactorizationReturn::Supported(_))
        {
            let MaterialFactorizationReturn::Supported(factorization) = material_return else {
                unreachable!("the supported material return was checked above")
            };
            return Ok(HierarchicalOpticalMaterialReturn::Supported {
                passage: candidates.passage,
                bindings: candidates.bindings.clone(),
                factorization,
            });
        }

        let mut open_identity = candidates.passage.native_consequence.open_exterior.clone();
        if !candidates.every_candidate_has_one_constraint_section() {
            open_identity.push(
                "plural addressed optical constraint occurrences retain the same candidate current"
                    .to_owned(),
            );
        }
        if matches!(
            &material_return,
            MaterialFactorizationReturn::Insufficient(_)
        ) {
            open_identity.push(
                "plural operation-current identities await a separating receiver history"
                    .to_owned(),
            );
        }
        open_identity.sort();
        open_identity.dedup();
        Ok(HierarchicalOpticalMaterialReturn::Insufficient {
            passage: candidates.passage,
            bindings: candidates.bindings.clone(),
            material_return,
            open_identity,
        })
    }

    fn factor_one(
        &self,
        material: &AddressedMaterialOccurrence,
        returned: &CausalOperationWorldReturn,
        reconstruction_fibre: Vec<String>,
    ) -> Result<MaterialNativeFactorization, MaterialFactorizationError> {
        let invariant = returned.invariant()?;
        let relation_current_section = invariant.relation_current_section()?;
        if relation_current_section.len() != self.chart.axes.len() {
            return Err(MaterialFactorizationError::Rank {
                section: relation_current_section.len(),
                body: self.chart.axes.len(),
            });
        }
        let native_operation_identity_sha256 = invariant.identity_sha256()?;
        let shared_transport = {
            self.shared_affine_transports
                .borrow()
                .get(&relation_current_section)
                .cloned()
        };
        let cultivated_affine_transport = if let Some(transport) = shared_transport {
            transport
        } else {
            let transport = self
                .rest
                .material_affine_transport(&relation_current_section)
                .map_err(MaterialFactorizationError::Rest)?;
            self.shared_affine_transports
                .borrow_mut()
                .insert(relation_current_section.clone(), transport.clone());
            transport
        };
        let mathematical_complex = mathematical_complex(
            material,
            returned,
            &invariant,
            &relation_current_section,
            &native_operation_identity_sha256,
        )?;
        let mixed = self
            .rest
            .material_standing_ecology()
            .mixed_constitutive_families();
        let fibres = self
            .rest
            .material_standing_ecology()
            .exact_reconstruction_fibres();
        let factor_support = self
            .chart
            .axes
            .iter()
            .zip(&relation_current_section)
            .filter(|(_, coefficient)| **coefficient != 0)
            .map(|(axis, coefficient)| SituatedMaterialFactorSupport {
                coordinate: axis.coordinate,
                situated_thread: axis.situated_thread.clone(),
                coefficient: *coefficient,
                incident_symmetric_families: mixed
                    .iter()
                    .filter(|family| {
                        family.left_thread == axis.situated_thread
                            || family.right_thread == axis.situated_thread
                    })
                    .map(|family| family.address.clone())
                    .collect(),
                exact_reconstruction_fibres: fibres
                    .iter()
                    .filter(|fibre| fibre.thread == axis.situated_thread)
                    .map(|fibre| fibre.address.clone())
                    .collect(),
            })
            .collect::<Vec<_>>();
        if factor_support.is_empty()
            || factor_support.iter().any(|support| {
                support.incident_symmetric_families.is_empty()
                    || support.exact_reconstruction_fibres.is_empty()
            })
        {
            return Err(MaterialFactorizationError::Support);
        }
        let mut complete_symmetric_family_support = mixed
            .iter()
            .filter(|family| {
                factor_support.iter().any(|support| {
                    family.left_thread == support.situated_thread
                        || family.right_thread == support.situated_thread
                })
            })
            .map(|family| family.address.clone())
            .collect::<Vec<_>>();
        complete_symmetric_family_support.sort();
        complete_symmetric_family_support.dedup();
        let occurrence = format!(
            "material-native-factorization/{}",
            digest_json(&(
                &material.occurrence,
                &returned.occurrence,
                self.rest.material_standing_identity(),
                &native_operation_identity_sha256,
                &factor_support,
            ))?
        );
        let mut open_exterior = material.open_exterior.clone();
        open_exterior.extend(returned.open_exterior.iter().cloned());
        open_exterior.extend(returned.apparatus.open_exterior.iter().cloned());
        open_exterior.sort();
        open_exterior.dedup();
        Ok(MaterialNativeFactorization {
            schema: MATERIAL_NATIVE_FACTORIZATION_SCHEMA.to_owned(),
            occurrence,
            material_occurrence: material.occurrence.clone(),
            world_return_occurrences: reconstruction_fibre.clone(),
            predecessor_rest_identity_sha256: self.rest.material_standing_identity().to_owned(),
            native_operation_identity_sha256,
            invariant,
            relation_current_section,
            mathematical_complex,
            receiver_chart: self.chart.clone(),
            factor_support,
            complete_symmetric_family_support,
            cultivated_affine_transport,
            reconstruction_fibre,
            open_exterior,
        })
    }
}

pub fn compare_material_factorizations(
    left: &MaterialNativeFactorization,
    right: &MaterialNativeFactorization,
    receiver: impl Into<String>,
) -> MaterialNaturalityReceipt {
    let native_operation_equal =
        left.native_operation_identity_sha256 == right.native_operation_identity_sha256;
    let relation_current_equal = left.relation_current_section == right.relation_current_section;
    let situated_support_equal = left
        .factor_support
        .iter()
        .map(|support| (&support.situated_thread, support.coefficient))
        .eq(right
            .factor_support
            .iter()
            .map(|support| (&support.situated_thread, support.coefficient)));
    let affine_transport_equal = left
        .cultivated_affine_transport
        .as_ref()
        .map(|transport| &transport.identity_sha256)
        == right
            .cultivated_affine_transport
            .as_ref()
            .map(|transport| &transport.identity_sha256);
    MaterialNaturalityReceipt {
        left_material_occurrence: left.material_occurrence.clone(),
        right_material_occurrence: right.material_occurrence.clone(),
        receiver: receiver.into(),
        native_operation_equal,
        relation_current_equal,
        situated_support_equal,
        affine_transport_equal,
        square_commutes: native_operation_equal
            && relation_current_equal
            && situated_support_equal
            && affine_transport_equal,
        shortest_separator: (!native_operation_equal)
            .then(|| shortest_separator(&left.invariant, &right.invariant))
            .flatten(),
    }
}

fn mathematical_complex(
    material: &AddressedMaterialOccurrence,
    returned: &CausalOperationWorldReturn,
    invariant: &CausalOperationInvariant,
    section: &[i64],
    identity: &str,
) -> Result<NativeMathematicalComplex, MaterialFactorizationError> {
    let carrier = format!("native-operation/{identity}");
    let entered_section = vec![
        invariant.left_population,
        invariant.right_population,
        invariant.returned_population,
        0,
    ];
    let exact_difference = section
        .iter()
        .zip(&entered_section)
        .map(|(right, left)| right - left)
        .collect::<Vec<_>>();
    let orientation = vec![1, 1, -1, 0];
    let transport_incidence = vec![1, 1, 1, 1];
    let vertices = entered_section
        .iter()
        .zip(section)
        .enumerate()
        .map(|(coordinate, (entered, returned))| {
            Ok(NativeGeometryVertex {
                coordinate: u32::try_from(coordinate)
                    .map_err(|_| MaterialFactorizationError::Extent)?,
                entered: *entered,
                returned: *returned,
            })
        })
        .collect::<Result<Vec<_>, MaterialFactorizationError>>()?;
    Ok(NativeMathematicalComplex {
        operation_cells: vec![NativeOperationCell {
            occurrence: format!("{}/operation", returned.occurrence),
            carrier_chart_occurrence: carrier.clone(),
            generator_relation_occurrence: format!(
                "{carrier}/incidence-degree/{}",
                invariant.incidence_degree
            ),
            source_boundary: material.occurrence.clone(),
            target_boundary: returned.occurrence.clone(),
            entered_section,
            returned_section: section.to_vec(),
            exact_difference,
            ordered_transport_word: vec![invariant.incidence_degree],
        }],
        constraint_cells: vec![NativeConstraintCell {
            occurrence: format!("{}/constraint", returned.occurrence),
            carrier_chart_occurrence: carrier.clone(),
            orientation: orientation.clone(),
            exact_residual: 0,
            held: true,
        }],
        geometry_cells: vec![NativeGeometryCell {
            occurrence: format!("{}/geometry", returned.occurrence),
            carrier_chart_occurrence: carrier.clone(),
            vertices,
            constraint_incidence: orientation,
            transport_incidence,
        }],
        exact_consequence_faces: vec![NativeExactConsequenceFace {
            carrier_chart_occurrence: carrier,
            returned_section: section.to_vec(),
            exact_residual: 0,
            selected_route: invariant.incidence_degree,
            fixed_section: true,
        }],
    })
}

fn derive_population_law(
    left: &[String],
    right: &[String],
    result: &[CausalResultCell],
) -> Result<CausalPopulationLaw, MaterialFactorizationError> {
    let left_set = left.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let right_set = right.iter().map(String::as_str).collect::<BTreeSet<_>>();
    if result.iter().any(|cell| {
        cell.left_member
            .as_deref()
            .is_some_and(|member| !left_set.contains(member))
            || cell
                .right_member
                .as_deref()
                .is_some_and(|member| !right_set.contains(member))
    }) {
        return Err(MaterialFactorizationError::OperationGeometry);
    }

    let union = result
        .iter()
        .all(|cell| cell.left_member.is_some() ^ cell.right_member.is_some())
        && result.len() == left.len().saturating_add(right.len())
        && result
            .iter()
            .filter_map(|cell| cell.left_member.as_deref())
            .collect::<BTreeSet<_>>()
            == left_set
        && result
            .iter()
            .filter_map(|cell| cell.right_member.as_deref())
            .collect::<BTreeSet<_>>()
            == right_set;

    let actual_pairs = result
        .iter()
        .filter_map(|cell| Some((cell.left_member.as_deref()?, cell.right_member.as_deref()?)))
        .collect::<BTreeSet<_>>();
    let expected_pairs = left
        .iter()
        .flat_map(|left| {
            right
                .iter()
                .map(move |right| (left.as_str(), right.as_str()))
        })
        .collect::<BTreeSet<_>>();
    let product = result
        .iter()
        .all(|cell| cell.left_member.is_some() && cell.right_member.is_some())
        && actual_pairs == expected_pairs
        && result.len() == expected_pairs.len();

    match (union, product) {
        (true, false) => Ok(CausalPopulationLaw::DisjointUnion),
        (false, true) => Ok(CausalPopulationLaw::IndependentProduct),
        _ => Err(MaterialFactorizationError::OperationGeometry),
    }
}

fn shortest_separator(
    left: &CausalOperationInvariant,
    right: &CausalOperationInvariant,
) -> Option<MaterialShortestSeparator> {
    if left.left_extension_returned_population != right.left_extension_returned_population {
        return Some(MaterialShortestSeparator {
            receiver: "exact-returned-population".to_owned(),
            history: "adjoin-one-member-to-left-input".to_owned(),
            left_returned_population: left.left_extension_returned_population,
            right_returned_population: right.left_extension_returned_population,
        });
    }
    (left.right_extension_returned_population != right.right_extension_returned_population).then(
        || MaterialShortestSeparator {
            receiver: "exact-returned-population".to_owned(),
            history: "adjoin-one-member-to-right-input".to_owned(),
            left_returned_population: left.right_extension_returned_population,
            right_returned_population: right.right_extension_returned_population,
        },
    )
}

fn identity_matrix(rank: usize) -> Vec<Vec<i64>> {
    (0..rank)
        .map(|row| (0..rank).map(|column| i64::from(row == column)).collect())
        .collect()
}

fn multiply(
    left: &[Vec<i64>],
    right: &[Vec<i64>],
) -> Result<Vec<Vec<i64>>, MaterialFactorizationError> {
    let rank = left.len();
    if rank == 0
        || right.len() != rank
        || left.iter().any(|row| row.len() != rank)
        || right.iter().any(|row| row.len() != rank)
    {
        return Err(MaterialFactorizationError::Chart);
    }
    let mut product = vec![vec![0i64; rank]; rank];
    for row in 0..rank {
        for column in 0..rank {
            for inner in 0..rank {
                product[row][column] = product[row][column]
                    .checked_add(
                        left[row][inner]
                            .checked_mul(right[inner][column])
                            .ok_or(MaterialFactorizationError::Extent)?,
                    )
                    .ok_or(MaterialFactorizationError::Extent)?;
            }
        }
    }
    Ok(product)
}

fn exact_i64(value: usize) -> Result<i64, MaterialFactorizationError> {
    i64::try_from(value).map_err(|_| MaterialFactorizationError::Extent)
}

fn unique_nonempty<'a>(mut values: impl Iterator<Item = &'a str>) -> bool {
    let mut seen = BTreeSet::new();
    values.all(|value| !value.is_empty() && seen.insert(value))
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn digest_json(value: &impl Serialize) -> Result<String, MaterialFactorizationError> {
    serde_json::to_vec(value)
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|error| MaterialFactorizationError::Wire(error.to_string()))
}

use holonic_engine::is_sha256_digest as is_sha256;

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MaterialFactorizationError {
    #[error("the addressed material occurrence is malformed")]
    MaterialOccurrence,
    #[error("the exterior world return is malformed")]
    WorldReturn,
    #[error("the world return does not descend from the addressed material occurrence")]
    Lineage,
    #[error(
        "the returned incidence is neither a complete disjoint union nor an independent product"
    )]
    OperationGeometry,
    #[error("the situated Athena rest refused the aperture: {0}")]
    Rest(String),
    #[error("the material receiver chart is malformed")]
    Chart,
    #[error("the material section has rank {section}, but the situated body has rank {body}")]
    Rank { section: usize, body: usize },
    #[error("the material section has no exact situated support")]
    Support,
    #[error("the cultivated affine transport field is malformed")]
    AffineTransport,
    #[error("plural material candidates have no admitted separating receiver history")]
    UnseparatedAmbiguity,
    #[error("a finite material extent overflowed its exact carrier")]
    Extent,
    #[error("the material factorization wire refused: {0}")]
    Wire(String),
    #[error("the hierarchical optical passage refused: {0}")]
    Optical(String),
    #[error("the addressed material does not carry the hierarchical optical predecessor")]
    OpticalLineage,
    #[error(
        "world return {world_return_occurrence} does not realize an addressed optical constraint section"
    )]
    OpticalCandidateLineage { world_return_occurrence: String },
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;
