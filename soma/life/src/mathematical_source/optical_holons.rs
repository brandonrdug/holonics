//! Hierarchical optical holons grown from the raw [`super::OpticalPassage`] incidence.
//!
//! This is an owner-local extension of optical recovery, not an OCR subsystem. Components,
//! inherited glyph faces, decorated symbols, terms, assemblies, relation-lines, blocks and the
//! page coexist as addressed occurrences. Larger grains retain their complete constituent fibre;
//! object names are later receiver faces and never route the geometry.

mod growth;

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::{OpticalBounds, SourceLayoutError};

pub use growth::grow_optical_holons;

pub const OPTICAL_HOLON_SCHEMA: &str = "soma-life.hierarchical-optical-holons.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum OpticalHolonGrain {
    Component,
    GlyphOrSubfigure,
    DecoratedSymbol,
    Term,
    Assembly,
    RelationOrEquation,
    LabelledOrDiagramBlock,
    Page,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum OpticalHolonIncidenceKind {
    Contains,
    SuperscriptAttachment,
    SubscriptAttachment,
    FractionNumerator,
    FractionDenominator,
    RadicalEnclosure,
    DelimiterAttachment,
    BaselineAlignment,
    ReadingTransport,
    MatrixRow,
    MatrixColumn,
    AlignmentRegion,
    DiagramIncidence,
    TermContact,
    LineContact,
    RepeatedFormKinship,
}

impl OpticalHolonIncidenceKind {
    pub(crate) const fn bit(self) -> Option<u16> {
        match self {
            Self::Contains | Self::RepeatedFormKinship => None,
            Self::BaselineAlignment => Some(1 << 1),
            Self::ReadingTransport => Some(1 << 2),
            Self::SuperscriptAttachment => Some(1 << 3),
            Self::SubscriptAttachment => Some(1 << 4),
            Self::FractionNumerator => Some(1 << 5),
            Self::FractionDenominator => Some(1 << 6),
            Self::RadicalEnclosure => Some(1 << 7),
            Self::DelimiterAttachment => Some(1 << 8),
            Self::MatrixRow => Some(1 << 9),
            Self::MatrixColumn => Some(1 << 10),
            Self::AlignmentRegion => Some(1 << 11),
            Self::DiagramIncidence => Some(1 << 12),
            Self::TermContact => Some(1 << 13),
            Self::LineContact => Some(1 << 14),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalFormMember {
    pub child_form_sha256: String,
    pub relative_bounds: OpticalBounds,
    pub inherited_face: Option<String>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalHolon {
    pub address_sha256: String,
    pub form_sha256: String,
    pub grain: OpticalHolonGrain,
    pub bounds: OpticalBounds,
    pub constituents: Vec<String>,
    pub glyph_ordinals: Vec<u32>,
    pub component_ordinals: Vec<u32>,
    pub inherited_face: Option<String>,
    pub form_members: Vec<OpticalFormMember>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalHolonIncidence {
    pub from_address: String,
    pub to_address: String,
    pub kind: OpticalHolonIncidenceKind,
    pub device_contact_class: Option<u8>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalLocalRelation {
    pub from_atom_address: String,
    pub to_atom_address: String,
    pub kind: OpticalHolonIncidenceKind,
    pub device_contact_class: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalAlternativeCover {
    pub subject_address: String,
    pub alternative_parent_addresses: Vec<String>,
    pub separating_relation_kinds: Vec<OpticalHolonIncidenceKind>,
    pub complete_within_resident_relation_word: bool,
    pub richer_receiver_reopens: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum OpticalObjectClass {
    RawComponent,
    Glyph,
    UnresolvedSubfigure,
    DecoratedSymbol,
    ProseTerm,
    MathematicalTerm,
    FractionAssembly,
    RadicalOrDelimiterAssembly,
    DiagramAssembly,
    TextLine,
    Equation,
    ProseBlock,
    LabelledMathematicalBlock,
    DiagramBlock,
    Page,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OpticalObjectClassFace {
    pub holon_address: String,
    pub classes: Vec<OpticalObjectClass>,
    pub inherited_face: Option<String>,
    pub classification_routes_geometry: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RepeatedOpticalFormFibre {
    pub form_sha256: String,
    pub occurrence_addresses: Vec<String>,
    pub parent_context_addresses: Vec<Vec<String>>,
    pub occurrences_remain_distinct: bool,
    pub context_covers_distinct: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EquationGlyphFibre {
    pub equation_address: String,
    pub glyph_holon_addresses: Vec<String>,
    pub glyph_ordinals: Vec<u32>,
    pub complete_constituent_reconstruction: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeEquationConstraintSection {
    pub equation_address: String,
    pub relation_glyph_address: String,
    pub relation_glyph_ordinals: Vec<u32>,
    pub inherited_relation_face: String,
    pub before_member_addresses: Vec<String>,
    pub after_member_addresses: Vec<String>,
    pub crossing_member_addresses: Vec<String>,
    pub complete_glyph_holon_addresses: Vec<String>,
    pub constraint_form_sha256: String,
    pub exact_ordered_constraint_geometry: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeHierarchicalOpticalConsequence {
    pub term_addresses: Vec<String>,
    pub assembly_addresses: Vec<String>,
    pub equation_addresses: Vec<String>,
    pub block_addresses: Vec<String>,
    pub equation_glyph_fibres: Vec<EquationGlyphFibre>,
    pub equation_constraint_sections: Vec<NativeEquationConstraintSection>,
    pub higher_equation_objects_change_native_consequence: bool,
    pub glyph_fibres_retained: bool,
    pub open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactOpticalScale {
    pub lower_median_height: u64,
    pub upper_median_height: u64,
    pub lower_median_width: u64,
    pub upper_median_width: u64,
    pub lower_median_nearest_gap: u64,
    pub upper_median_nearest_gap: u64,
    pub term_gap: u64,
    pub line_gap: u64,
    pub authored_capacity_constant: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactOpticalIncidenceReceipt {
    pub atom_population: u64,
    pub complete_pair_population: u64,
    pub complete_relation_words_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeviceOpticalHolonReceipt {
    pub device_name: String,
    pub launches: u64,
    pub synchronizations: u64,
    pub host_ingress_octets: u64,
    pub host_egress_octets: u64,
    pub resident_octets: u64,
    pub cpu_semantic_fallback: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
pub enum OpticalHolonIntervention {
    None,
    Crop { bounds: OpticalBounds },
    Translate { horizontal: i64, vertical: i64 },
    WithoutInheritedGlyph { glyph_ordinal: u32 },
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HierarchicalOpticalPassage {
    pub schema: String,
    pub truth_status: String,
    pub predecessor_occurrence: String,
    pub predecessor_source_sha256: String,
    pub occurrence: String,
    pub width: u32,
    pub height: u32,
    pub intervention: OpticalHolonIntervention,
    pub scale: ExactOpticalScale,
    pub holons: Vec<OpticalHolon>,
    pub incidences: Vec<OpticalHolonIncidence>,
    pub local_relations: Vec<OpticalLocalRelation>,
    pub alternative_covers: Vec<OpticalAlternativeCover>,
    pub classifications: Vec<OpticalObjectClassFace>,
    pub repeated_forms: Vec<RepeatedOpticalFormFibre>,
    pub native_consequence: NativeHierarchicalOpticalConsequence,
    pub relation_receipt: ExactOpticalIncidenceReceipt,
    pub productive_transcript_present: bool,
    pub productive_text_layer_present: bool,
    pub productive_anchor_labels_present: bool,
}

impl HierarchicalOpticalPassage {
    pub fn read(bytes: &[u8]) -> Result<Self, SourceLayoutError> {
        let passage: Self = serde_json::from_slice(bytes)
            .map_err(|error| SourceLayoutError::OpticalHolon(error.to_string()))?;
        passage.validate()?;
        Ok(passage)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, SourceLayoutError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| SourceLayoutError::OpticalHolon(error.to_string()))
    }

    pub fn validate(&self) -> Result<(), SourceLayoutError> {
        if self.schema != OPTICAL_HOLON_SCHEMA
            || self.truth_status != "implemented-exact"
            || self.predecessor_occurrence.is_empty()
            || self.occurrence.is_empty()
            || self.width == 0
            || self.height == 0
            || self.holons.is_empty()
            || self.productive_transcript_present
            || self.productive_text_layer_present
            || self.productive_anchor_labels_present
            || self.scale.authored_capacity_constant
            || self.scale.term_gap > self.scale.line_gap
            || self.scale.lower_median_height > self.scale.upper_median_height
            || self.scale.lower_median_width > self.scale.upper_median_width
            || self.scale.lower_median_nearest_gap > self.scale.upper_median_nearest_gap
            || self.relation_receipt.complete_pair_population
                != self
                    .relation_receipt
                    .atom_population
                    .saturating_mul(self.relation_receipt.atom_population.saturating_sub(1))
                    / 2
        {
            return Err(SourceLayoutError::OpticalHolon(
                "the hierarchical optical boundary does not reconstruct".to_owned(),
            ));
        }
        require_digest(&self.predecessor_source_sha256)?;
        require_digest(&self.relation_receipt.complete_relation_words_sha256)?;

        let mut known = BTreeMap::<String, &OpticalHolon>::new();
        for holon in &self.holons {
            require_digest(&holon.address_sha256)?;
            require_digest(&holon.form_sha256)?;
            let obstruction = if holon.bounds.left > holon.bounds.right
                || holon.bounds.top > holon.bounds.bottom
            {
                Some("its bounds are not oriented")
            } else if holon.form_sha256
                != form_digest(
                    holon.grain,
                    &holon.form_members,
                    holon.inherited_face.as_deref(),
                )?
            {
                Some("its form receipt does not reconstruct")
            } else if holon.address_sha256
                != holon_address(
                    &self.occurrence,
                    holon.grain,
                    holon.bounds,
                    &holon.constituents,
                    &holon.form_sha256,
                )?
            {
                Some("its occurrence address does not reconstruct")
            } else if holon
                .constituents
                .iter()
                .any(|constituent| !known.contains_key(constituent))
            {
                Some("one constituent has not yet entered the incidence")
            } else if known.insert(holon.address_sha256.clone(), holon).is_some() {
                Some("the same occurrence was inserted twice")
            } else {
                None
            };
            if let Some(obstruction) = obstruction {
                return Err(SourceLayoutError::OpticalHolon(format!(
                    "optical {:?} holon {} does not reconstruct: {obstruction}",
                    holon.grain, holon.address_sha256,
                )));
            }
        }
        let addresses = known.keys().cloned().collect::<BTreeSet<_>>();
        if self.incidences.iter().any(|incidence| {
            !addresses.contains(&incidence.from_address)
                || !addresses.contains(&incidence.to_address)
                || incidence.from_address == incidence.to_address
        }) || self.local_relations.iter().any(|relation| {
            !addresses.contains(&relation.from_atom_address)
                || !addresses.contains(&relation.to_atom_address)
                || relation.device_contact_class > 2
        }) {
            return Err(SourceLayoutError::OpticalHolon(
                "an optical incidence leaves the addressed body".to_owned(),
            ));
        }
        for holon in self
            .holons
            .iter()
            .filter(|holon| !holon.constituents.is_empty())
        {
            for child in &holon.constituents {
                if !self.incidences.iter().any(|incidence| {
                    incidence.from_address == *child
                        && incidence.to_address == holon.address_sha256
                        && incidence.kind == OpticalHolonIncidenceKind::Contains
                }) {
                    return Err(SourceLayoutError::OpticalHolon(format!(
                        "{} does not retain constituent {}",
                        holon.address_sha256, child
                    )));
                }
            }
        }
        if self.native_consequence.equation_glyph_fibres.len()
            != self.native_consequence.equation_addresses.len()
            || self
                .native_consequence
                .higher_equation_objects_change_native_consequence
                != !self.native_consequence.equation_addresses.is_empty()
            || self
                .native_consequence
                .equation_glyph_fibres
                .iter()
                .any(|fibre| {
                    !addresses.contains(&fibre.equation_address)
                        || fibre.glyph_holon_addresses.is_empty()
                        || !fibre.complete_constituent_reconstruction
                        || fibre
                            .glyph_holon_addresses
                            .iter()
                            .any(|address| !addresses.contains(address))
                })
            || !self.native_consequence.glyph_fibres_retained
            || self.repeated_forms.iter().any(|fibre| {
                fibre.occurrence_addresses.len() < 2
                    || !fibre.occurrences_remain_distinct
                    || fibre.parent_context_addresses.len() != fibre.occurrence_addresses.len()
            })
        {
            return Err(SourceLayoutError::OpticalHolon(
                "the higher equation consequence or repeated-form control is absent".to_owned(),
            ));
        }
        let equation_addresses = self
            .native_consequence
            .equation_addresses
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        if !equation_addresses.is_empty()
            && self
                .native_consequence
                .equation_constraint_sections
                .is_empty()
        {
            return Err(SourceLayoutError::OpticalHolon(format!(
                "the native equation constraint section population is empty for {} equation faces",
                equation_addresses.len()
            )));
        }
        for equation in &equation_addresses {
            if !self
                .native_consequence
                .equation_constraint_sections
                .iter()
                .any(|section| section.equation_address == *equation)
            {
                return Err(SourceLayoutError::OpticalHolon(format!(
                    "equation {equation} has no native ordered constraint section"
                )));
            }
        }
        for section in &self.native_consequence.equation_constraint_sections {
            let obstruction = if !equation_addresses.contains(&section.equation_address) {
                Some("its parent is not an equation")
            } else if !addresses.contains(&section.relation_glyph_address) {
                Some("its relation glyph is outside the incidence")
            } else if section.relation_glyph_ordinals.is_empty() {
                Some("its relation glyph has no inherited lineage")
            } else if section.inherited_relation_face.is_empty() {
                Some("its relation receiver face is empty")
            } else if section.before_member_addresses.is_empty() {
                Some("its before section is empty")
            } else if section.after_member_addresses.is_empty() {
                Some("its after section is empty")
            } else if section.complete_glyph_holon_addresses.is_empty() {
                Some("its complete glyph fibre is empty")
            } else if !section.exact_ordered_constraint_geometry {
                Some("its ordered geometry is not exact")
            } else if require_digest(&section.constraint_form_sha256).is_err() {
                Some("its form identity is not a digest")
            } else if section
                .before_member_addresses
                .iter()
                .chain(&section.after_member_addresses)
                .chain(&section.crossing_member_addresses)
                .chain(&section.complete_glyph_holon_addresses)
                .any(|address| !addresses.contains(address))
            {
                Some("one of its members leaves the incidence")
            } else {
                None
            };
            if let Some(obstruction) = obstruction {
                return Err(SourceLayoutError::OpticalHolon(format!(
                    "native equation constraint {} -> {} does not reconstruct: {obstruction}",
                    section.equation_address, section.relation_glyph_address,
                )));
            }
        }
        Ok(())
    }
}

pub(crate) fn form_digest(
    grain: OpticalHolonGrain,
    members: &[OpticalFormMember],
    inherited_face: Option<&str>,
) -> Result<String, SourceLayoutError> {
    digest_json(&("optical-form-v1", grain, members, inherited_face))
}

pub(crate) fn holon_address(
    occurrence: &str,
    grain: OpticalHolonGrain,
    bounds: OpticalBounds,
    constituents: &[String],
    form_sha256: &str,
) -> Result<String, SourceLayoutError> {
    digest_json(&(
        "optical-holon-occurrence-v1",
        occurrence,
        grain,
        bounds,
        constituents,
        form_sha256,
    ))
}

pub(crate) fn digest_json(value: &impl Serialize) -> Result<String, SourceLayoutError> {
    serde_json::to_vec(value)
        .map(|bytes| {
            Sha256::digest(bytes)
                .iter()
                .map(|octet| format!("{octet:02x}"))
                .collect()
        })
        .map_err(|error| SourceLayoutError::OpticalHolon(error.to_string()))
}

fn require_digest(value: &str) -> Result<(), SourceLayoutError> {
    if value.len() != 64 || !value.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(SourceLayoutError::OpticalHolon(
            "an optical identity is not SHA-256".to_owned(),
        ));
    }
    Ok(())
}
