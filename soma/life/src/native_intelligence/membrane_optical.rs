//! Exact optical receiver chart over native Athena membrane radiation.
//!
//! The productive object is an addressed cell complex, not a raster or an image template. Native
//! outward ports found its lattice incidence and iterated adjacency covers; later exact current
//! occupies those cells. A cold RGB/PNG receiver may project the complete field while retaining
//! every quotient/remainder and every omitted address. The rendered surface is therefore a world
//! consequence which may return through the standing optical transducer, never the origin of the
//! productive field.

mod hierarchical_formation;

pub use hierarchical_formation::{
    NativeHierarchicalOpticalFormation, NativeHierarchicalOpticalFormationSection,
    NativeHierarchicalOpticalProjection,
};

use std::{collections::BTreeMap, io::Cursor};

use holonic_engine::ExactComplexWaveCurrent;
use image::{DynamicImage, ImageFormat, Rgb, RgbImage};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use thiserror::Error;

use super::membrane_cultivation::MembraneDifferenceStanding;
use super::{
    AcousticProductRest, AcousticRelationalCellWithdrawal, GranularMembraneStanding,
    LaboratoryCellAffineSection, LaboratoryFactorCycleCorrespondence, MembraneStanding,
    NativeAcousticRadiationInput, NativeGranularPotential, ReceiverHistoryRealizationPassage,
    SituatedCultivationBranch, SituatedDifferenceSection,
};

pub const NATIVE_OPTICAL_PRODUCTION_MORPHOLOGY_SCHEMA: &str =
    "soma-life.native-optical-production-morphology.v1";
const NATIVE_OPTICAL_FIELD_SCHEMA: &str = "soma-life.native-optical-potential-field.v1";
const NATIVE_OPTICAL_RASTER_SCHEMA: &str = "soma-life.native-optical-raster-projection.v1";
const OPTICAL_PRODUCT_REST_SCHEMA: &str = "soma-life.optical-product-rest.v1";
const WITHDRAWN_OPTICAL_PRODUCTION_SCHEMA: &str =
    "soma-life.withdrawn-native-optical-production.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalCellBounds {
    pub left: u32,
    pub top: u32,
    pub right: u32,
    pub bottom: u32,
}

impl NativeOpticalCellBounds {
    fn contains(self, x: u32, y: u32) -> bool {
        self.left <= x && x < self.right && self.top <= y && y < self.bottom
    }
}

/// Reusable source-neutral incidence. No current, pixel, color, source image, or label is rested.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalProductionMorphology {
    pub schema: String,
    pub founding_rest_identity_sha256: String,
    pub founding_radiation_identity_sha256: String,
    pub ordered_ports: Vec<(u32, u32)>,
    pub founding_causal_order_population: u32,
    pub lattice_width: u32,
    pub lattice_height_per_order: u32,
    pub scale_spans: Vec<u32>,
    pub source_current_retained: bool,
    pub source_image_retained: bool,
    pub pixel_template_retained: bool,
    pub label_route_retained: bool,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalCell {
    pub address_sha256: String,
    pub causal_order: u64,
    pub port: u32,
    pub universal_port: u32,
    pub x: u32,
    pub y: u32,
    pub current: ExactComplexWaveCurrent,
    pub lies_in_outward_radical: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalScaleCover {
    pub address_sha256: String,
    pub span: u32,
    pub translated: bool,
    pub bounds: NativeOpticalCellBounds,
    pub member_addresses: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalAlternativeCover {
    pub subject_address_sha256: String,
    pub parent_cover_addresses_sha256: Vec<String>,
    pub parent_spans: Vec<u32>,
    pub complete_native_membership_fibre_retained: bool,
    pub richer_receiver_reopens: bool,
}

/// Complete exact multi-scale optical field before any raster receiver acts.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalPotentialField {
    pub schema: String,
    pub morphology_identity_sha256: String,
    pub radiation_identity_sha256: String,
    pub width_cells: u32,
    pub height_cells: u32,
    pub cells: Vec<NativeOpticalCell>,
    pub scale_covers: Vec<NativeOpticalScaleCover>,
    pub alternative_covers: Vec<NativeOpticalAlternativeCover>,
    pub source_image_accessible: bool,
    pub pixel_template_applied: bool,
    pub label_route_applied: bool,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case", tag = "kind", deny_unknown_fields)]
pub enum NativeOpticalReceiverIntervention {
    None,
    Crop { bounds: NativeOpticalCellBounds },
    Scale { factor: u32 },
    ColorChart { channel_order: [u8; 3] },
    Occlude { cover_address_sha256: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalChannelQuotient {
    pub cell_address_sha256: String,
    pub channel: u8,
    pub exact_integer: BigInt,
    pub divisor: BigInt,
    pub quotient: BigInt,
    pub remainder: BigInt,
    pub rendered_sample: u8,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalRasterProjection {
    pub schema: String,
    pub field_identity_sha256: String,
    pub intervention: NativeOpticalReceiverIntervention,
    pub width: u32,
    pub height: u32,
    pub rendered_cell_addresses: Vec<String>,
    pub omitted_cell_addresses: Vec<String>,
    pub channel_quotients: Vec<NativeOpticalChannelQuotient>,
    pub png_sha256: String,
    pub complete_field_reconstruction_fibre_retained: bool,
    pub cold_renderer_only: bool,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalCultivationReceipt {
    pub predecessor_rest_identity_sha256: String,
    pub successor_rest_identity_sha256: String,
    pub morphology_identity_sha256: String,
    pub founding_radiation_identity_sha256: String,
    pub port_population: usize,
    pub causal_order_population: u32,
    pub scale_spans: Vec<u32>,
    pub source_current_retained_in_morphology: bool,
    pub source_image_retained_in_morphology: bool,
    pub pixel_template_retained: bool,
    pub label_route_retained: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalStandingMutation {
    pub operation: String,
    pub predecessor_rest_identity_sha256: String,
    pub successor_rest_identity_sha256: String,
    pub morphology_identity_sha256: String,
}

/// Receipt for moving an already source-neutral optical morphology onto a compatible continuing
/// Athena body. Source raster, label, and founding current remain absent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeOpticalOrganCompositionReceipt {
    pub inherited_rest_identity_sha256: String,
    pub inherited_predecessor_identity_sha256: String,
    pub morphology_identity_sha256: String,
    pub receiving_body_identity_sha256: String,
    pub composed_rest_identity_sha256: String,
    pub source_occurrence_consulted: bool,
    pub source_image_retained_in_morphology: bool,
    pub pixel_template_retained: bool,
    pub label_route_retained: bool,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WithdrawnNativeOpticalProduction {
    schema: String,
    original_rest_identity_sha256: String,
    predecessor_body_identity_sha256: String,
    morphology: NativeOpticalProductionMorphology,
    identity_sha256: String,
}

/// One move-owned Athena body carrying its acoustic and optical boundary morphologies.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OpticalProductRest {
    schema: String,
    body: AcousticProductRest,
    production: NativeOpticalProductionMorphology,
    identity_sha256: String,
}

/// Exact inverse for one affine-cell ablation conducted through the complete optical/acoustic
/// product body.
#[derive(Debug, PartialEq, Eq)]
pub struct OpticalRelationalCellWithdrawal {
    original_rest_identity_sha256: String,
    body: AcousticRelationalCellWithdrawal,
}

impl NativeOpticalProductionMorphology {
    fn found(input: &NativeAcousticRadiationInput) -> Result<Self, NativeOpticalError> {
        input
            .validate()
            .map_err(|error| NativeOpticalError::Radiation(error.to_string()))?;
        let first = input
            .orders
            .first()
            .ok_or(NativeOpticalError::MalformedMorphology)?;
        let ordered_ports = first
            .outward_port_returns
            .iter()
            .enumerate()
            .map(|(at, returned)| {
                if usize::try_from(returned.port).ok() != Some(at) {
                    Err(NativeOpticalError::MalformedMorphology)
                } else {
                    Ok((returned.port, returned.universal_port))
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        let order_population =
            u32::try_from(input.orders.len()).map_err(|_| NativeOpticalError::Extent)?;
        let port_population =
            u32::try_from(ordered_ports.len()).map_err(|_| NativeOpticalError::Extent)?;
        let lattice_width = ceil_sqrt(port_population).ok_or(NativeOpticalError::Extent)?;
        let lattice_height_per_order =
            ceil_div(port_population, lattice_width).ok_or(NativeOpticalError::Extent)?;
        let height = lattice_height_per_order
            .checked_mul(order_population)
            .ok_or(NativeOpticalError::Extent)?;
        let scale_spans = dyadic_spans(lattice_width.max(height))?;
        let mut morphology = Self {
            schema: NATIVE_OPTICAL_PRODUCTION_MORPHOLOGY_SCHEMA.to_owned(),
            founding_rest_identity_sha256: input.rested_identity_sha256.clone(),
            founding_radiation_identity_sha256: input.identity_sha256.clone(),
            ordered_ports,
            founding_causal_order_population: order_population,
            lattice_width,
            lattice_height_per_order,
            scale_spans,
            source_current_retained: false,
            source_image_retained: false,
            pixel_template_retained: false,
            label_route_retained: false,
            identity_sha256: String::new(),
        };
        morphology.identity_sha256 = morphology.rederived_identity()?;
        morphology.validate()?;
        Ok(morphology)
    }

    pub fn validate(&self) -> Result<(), NativeOpticalError> {
        let port_population =
            u32::try_from(self.ordered_ports.len()).map_err(|_| NativeOpticalError::Extent)?;
        let expected_width = ceil_sqrt(port_population).ok_or(NativeOpticalError::Extent)?;
        let expected_height =
            ceil_div(port_population, expected_width).ok_or(NativeOpticalError::Extent)?;
        let total_height = expected_height
            .checked_mul(self.founding_causal_order_population)
            .ok_or(NativeOpticalError::Extent)?;
        if self.schema != NATIVE_OPTICAL_PRODUCTION_MORPHOLOGY_SCHEMA
            || !is_digest(&self.founding_rest_identity_sha256)
            || !is_digest(&self.founding_radiation_identity_sha256)
            || self.ordered_ports.is_empty()
            || self.founding_causal_order_population == 0
            || self.lattice_width != expected_width
            || self.lattice_height_per_order != expected_height
            || self.scale_spans != dyadic_spans(expected_width.max(total_height))?
            || self.source_current_retained
            || self.source_image_retained
            || self.pixel_template_retained
            || self.label_route_retained
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeOpticalError::MalformedMorphology);
        }
        let mut ports = self.ordered_ports.clone();
        ports.sort_unstable();
        ports.dedup();
        if ports.len() != self.ordered_ports.len() {
            return Err(NativeOpticalError::MalformedMorphology);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeOpticalError> {
        digest(&(
            &self.schema,
            &self.founding_rest_identity_sha256,
            &self.founding_radiation_identity_sha256,
            &self.ordered_ports,
            self.founding_causal_order_population,
            self.lattice_width,
            self.lattice_height_per_order,
            &self.scale_spans,
            self.source_current_retained,
            self.source_image_retained,
            self.pixel_template_retained,
            self.label_route_retained,
        ))
    }

    fn form_field(
        &self,
        input: &NativeAcousticRadiationInput,
    ) -> Result<NativeOpticalPotentialField, NativeOpticalError> {
        self.validate()?;
        input
            .validate()
            .map_err(|error| NativeOpticalError::Radiation(error.to_string()))?;
        // The founding body/order population is retained as exact lineage testimony. It cannot
        // prevent a later cultivated body from using the same source-neutral port incidence.
        // Causal depth and the dyadic cover tower are derived anew from the emitted section.
        if input.outward_port_population != self.ordered_ports.len() {
            return Err(NativeOpticalError::Lineage);
        }
        let current_order_population =
            u32::try_from(input.orders.len()).map_err(|_| NativeOpticalError::Extent)?;
        let height_cells = self
            .lattice_height_per_order
            .checked_mul(current_order_population)
            .ok_or(NativeOpticalError::Extent)?;
        let mut cells = Vec::with_capacity(
            input
                .orders
                .len()
                .checked_mul(self.ordered_ports.len())
                .ok_or(NativeOpticalError::Extent)?,
        );
        for (order_at, order) in input.orders.iter().enumerate() {
            for (port_at, returned) in order.outward_port_returns.iter().enumerate() {
                if self.ordered_ports.get(port_at)
                    != Some(&(returned.port, returned.universal_port))
                {
                    return Err(NativeOpticalError::Lineage);
                }
                let x = u32::try_from(port_at).map_err(|_| NativeOpticalError::Extent)?
                    % self.lattice_width;
                let y = u32::try_from(order_at)
                    .map_err(|_| NativeOpticalError::Extent)?
                    .checked_mul(self.lattice_height_per_order)
                    .and_then(|base| {
                        base.checked_add(u32::try_from(port_at).ok()? / self.lattice_width)
                    })
                    .ok_or(NativeOpticalError::Extent)?;
                let address_sha256 = digest(&(
                    &self.identity_sha256,
                    &input.identity_sha256,
                    order.causal_order,
                    returned.port,
                    returned.universal_port,
                    x,
                    y,
                ))?;
                cells.push(NativeOpticalCell {
                    address_sha256,
                    causal_order: order.causal_order,
                    port: returned.port,
                    universal_port: returned.universal_port,
                    x,
                    y,
                    current: returned.returned_response.clone(),
                    lies_in_outward_radical: returned.lies_in_outward_radical,
                });
            }
        }
        let scale_spans = dyadic_spans(self.lattice_width.max(height_cells))?;
        let scale_covers = found_scale_covers(
            &self.identity_sha256,
            &input.identity_sha256,
            self.lattice_width,
            height_cells,
            &scale_spans,
            &cells,
        )?;
        let mut parents = BTreeMap::<String, Vec<(String, u32)>>::new();
        for cover in &scale_covers {
            for member in &cover.member_addresses {
                parents
                    .entry(member.clone())
                    .or_default()
                    .push((cover.address_sha256.clone(), cover.span));
            }
        }
        let alternative_covers = cells
            .iter()
            .map(|cell| {
                let fibre = parents.remove(&cell.address_sha256).unwrap_or_default();
                NativeOpticalAlternativeCover {
                    subject_address_sha256: cell.address_sha256.clone(),
                    parent_cover_addresses_sha256: fibre
                        .iter()
                        .map(|(address, _)| address.clone())
                        .collect(),
                    parent_spans: fibre.iter().map(|(_, span)| *span).collect(),
                    complete_native_membership_fibre_retained: true,
                    richer_receiver_reopens: fibre.len() > self.scale_spans.len(),
                }
            })
            .collect::<Vec<_>>();
        let mut field = NativeOpticalPotentialField {
            schema: NATIVE_OPTICAL_FIELD_SCHEMA.to_owned(),
            morphology_identity_sha256: self.identity_sha256.clone(),
            radiation_identity_sha256: input.identity_sha256.clone(),
            width_cells: self.lattice_width,
            height_cells,
            cells,
            scale_covers,
            alternative_covers,
            source_image_accessible: false,
            pixel_template_applied: false,
            label_route_applied: false,
            identity_sha256: String::new(),
        };
        field.identity_sha256 = field.rederived_identity()?;
        if field.validate().is_err() {
            eprintln!(
                "native optical field refusal: orders={} width={} height={} cells={} covers={} alternatives={} empty-parent-fibres={} out-of-bounds={}",
                input.orders.len(),
                field.width_cells,
                field.height_cells,
                field.cells.len(),
                field.scale_covers.len(),
                field.alternative_covers.len(),
                field
                    .alternative_covers
                    .iter()
                    .filter(|cover| cover.parent_cover_addresses_sha256.is_empty())
                    .count(),
                field
                    .cells
                    .iter()
                    .filter(|cell| cell.x >= field.width_cells || cell.y >= field.height_cells)
                    .count(),
            );
        }
        field.validate()?;
        Ok(field)
    }
}

impl NativeOpticalPotentialField {
    pub fn validate(&self) -> Result<(), NativeOpticalError> {
        if self.schema != NATIVE_OPTICAL_FIELD_SCHEMA
            || !is_digest(&self.morphology_identity_sha256)
            || !is_digest(&self.radiation_identity_sha256)
            || self.width_cells == 0
            || self.height_cells == 0
            || self.cells.is_empty()
            || self.scale_covers.is_empty()
            || self.alternative_covers.len() != self.cells.len()
            || self.source_image_accessible
            || self.pixel_template_applied
            || self.label_route_applied
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeOpticalError::MalformedField);
        }
        let cell_addresses = self
            .cells
            .iter()
            .map(|cell| cell.address_sha256.as_str())
            .collect::<std::collections::BTreeSet<_>>();
        if cell_addresses.len() != self.cells.len()
            || self.cells.iter().any(|cell| {
                cell.x >= self.width_cells
                    || cell.y >= self.height_cells
                    || !is_digest(&cell.address_sha256)
            })
            || self.scale_covers.iter().any(|cover| {
                !is_digest(&cover.address_sha256)
                    || cover.member_addresses.is_empty()
                    || cover
                        .member_addresses
                        .iter()
                        .any(|address| !cell_addresses.contains(address.as_str()))
            })
            || self.alternative_covers.iter().any(|cover| {
                !cell_addresses.contains(cover.subject_address_sha256.as_str())
                    || cover.parent_cover_addresses_sha256.is_empty()
                    || cover.parent_cover_addresses_sha256.len() != cover.parent_spans.len()
                    || !cover.complete_native_membership_fibre_retained
            })
        {
            return Err(NativeOpticalError::MalformedField);
        }
        Ok(())
    }

    /// Compose this exact radiation field with an admitted hierarchical optical potential.
    /// The hierarchy remains the spatial/scale owner; the radiation supplies transported current.
    /// No rectangular port index, OCR string, label, or source pixel selects a native section.
    pub fn form_hierarchical(
        &self,
        hierarchy: &crate::mathematical_source::HierarchicalOpticalPassage,
    ) -> Result<NativeHierarchicalOpticalFormation, NativeOpticalError> {
        NativeHierarchicalOpticalFormation::found(self, hierarchy)
    }

    pub fn derived_crop(&self) -> Result<NativeOpticalReceiverIntervention, NativeOpticalError> {
        self.validate()?;
        let cover = self
            .scale_covers
            .iter()
            .filter(|cover| {
                cover.member_addresses.len() > 1 && cover.member_addresses.len() < self.cells.len()
            })
            .max_by_key(|cover| (cover.span, cover.member_addresses.len()))
            .ok_or(NativeOpticalError::Intervention)?;
        Ok(NativeOpticalReceiverIntervention::Crop {
            bounds: cover.bounds,
        })
    }

    pub fn derived_scale(&self) -> Result<NativeOpticalReceiverIntervention, NativeOpticalError> {
        self.validate()?;
        let factor = u32::try_from(
            self.cells
                .iter()
                .map(|cell| cell.causal_order)
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
        )
        .map_err(|_| NativeOpticalError::Extent)?;
        if factor < 2 {
            return Err(NativeOpticalError::Intervention);
        }
        Ok(NativeOpticalReceiverIntervention::Scale { factor })
    }

    pub fn derived_color_chart(
        &self,
    ) -> Result<NativeOpticalReceiverIntervention, NativeOpticalError> {
        self.validate()?;
        let first = self
            .cells
            .iter()
            .find(|cell| !cell.current.is_zero())
            .ok_or(NativeOpticalError::Intervention)?;
        let channel_order =
            if first.current.real.is_negative() == first.current.imaginary.is_negative() {
                [1, 2, 0]
            } else {
                [2, 0, 1]
            };
        Ok(NativeOpticalReceiverIntervention::ColorChart { channel_order })
    }

    pub fn derived_occlusion(
        &self,
    ) -> Result<NativeOpticalReceiverIntervention, NativeOpticalError> {
        self.validate()?;
        let cover = self
            .scale_covers
            .iter()
            .filter(|cover| {
                cover.member_addresses.len() > 1 && cover.member_addresses.len() < self.cells.len()
            })
            .min_by_key(|cover| (cover.span, cover.member_addresses.len()))
            .ok_or(NativeOpticalError::Intervention)?;
        Ok(NativeOpticalReceiverIntervention::Occlude {
            cover_address_sha256: cover.address_sha256.clone(),
        })
    }

    pub fn render_png(
        &self,
        intervention: NativeOpticalReceiverIntervention,
    ) -> Result<(Vec<u8>, NativeOpticalRasterProjection), NativeOpticalError> {
        self.validate()?;
        let base_span = u32::try_from(
            self.scale_covers
                .iter()
                .map(|cover| cover.span)
                .collect::<std::collections::BTreeSet<_>>()
                .len(),
        )
        .map_err(|_| NativeOpticalError::Extent)?
        .checked_add(1)
        .ok_or(NativeOpticalError::Extent)?;
        let (crop, scale, channel_order, occluded) = match &intervention {
            NativeOpticalReceiverIntervention::None => (None, 1, [0, 1, 2], None),
            NativeOpticalReceiverIntervention::Crop { bounds } => {
                (Some(*bounds), 1, [0, 1, 2], None)
            }
            NativeOpticalReceiverIntervention::Scale { factor } if *factor > 0 => {
                (None, *factor, [0, 1, 2], None)
            }
            NativeOpticalReceiverIntervention::ColorChart { channel_order }
                if is_channel_permutation(*channel_order) =>
            {
                (None, 1, *channel_order, None)
            }
            NativeOpticalReceiverIntervention::Occlude {
                cover_address_sha256,
            } => {
                let cover = self
                    .scale_covers
                    .iter()
                    .find(|cover| &cover.address_sha256 == cover_address_sha256)
                    .ok_or(NativeOpticalError::Intervention)?;
                (None, 1, [0, 1, 2], Some(cover.member_addresses.as_slice()))
            }
            _ => return Err(NativeOpticalError::Intervention),
        };
        let selected = self
            .cells
            .iter()
            .filter(|cell| crop.is_none_or(|bounds| bounds.contains(cell.x, cell.y)))
            .collect::<Vec<_>>();
        if selected.is_empty() {
            return Err(NativeOpticalError::Intervention);
        }
        let min_x = selected
            .iter()
            .map(|cell| cell.x)
            .min()
            .ok_or(NativeOpticalError::Intervention)?;
        let min_y = selected
            .iter()
            .map(|cell| cell.y)
            .min()
            .ok_or(NativeOpticalError::Intervention)?;
        let max_x = selected
            .iter()
            .map(|cell| cell.x)
            .max()
            .ok_or(NativeOpticalError::Intervention)?;
        let max_y = selected
            .iter()
            .map(|cell| cell.y)
            .max()
            .ok_or(NativeOpticalError::Intervention)?;
        let step = base_span
            .checked_add(1)
            .and_then(|value| value.checked_mul(scale))
            .ok_or(NativeOpticalError::Extent)?;
        let grain = base_span
            .checked_mul(scale)
            .ok_or(NativeOpticalError::Extent)?;
        let width = max_x
            .checked_sub(min_x)
            .and_then(|value| value.checked_add(1))
            .and_then(|value| value.checked_mul(step))
            .and_then(|value| value.checked_add(1))
            .ok_or(NativeOpticalError::Extent)?;
        let height = max_y
            .checked_sub(min_y)
            .and_then(|value| value.checked_add(1))
            .and_then(|value| value.checked_mul(step))
            .and_then(|value| value.checked_add(1))
            .ok_or(NativeOpticalError::Extent)?;
        let mut image = RgbImage::from_pixel(width, height, Rgb([0, 0, 0]));
        let divisor = BigInt::from(u8::MAX);
        let mut rendered = Vec::new();
        let mut omitted = Vec::new();
        let mut quotients = Vec::new();
        for cell in selected {
            if occluded.is_some_and(|addresses| addresses.contains(&cell.address_sha256))
                || cell.current.is_zero()
            {
                omitted.push(cell.address_sha256.clone());
                continue;
            }
            let exact = exact_color_coordinates(&cell.current);
            let mut samples = [0_u8; 3];
            for channel in 0..3 {
                let value = &exact[channel_order[channel] as usize];
                let magnitude = value.abs();
                let quotient = &magnitude / &divisor;
                let remainder = &magnitude % &divisor;
                let rendered_sample = remainder
                    .to_u8()
                    .ok_or(NativeOpticalError::Extent)?
                    .saturating_add(1);
                samples[channel] = rendered_sample;
                quotients.push(NativeOpticalChannelQuotient {
                    cell_address_sha256: cell.address_sha256.clone(),
                    channel: u8::try_from(channel).map_err(|_| NativeOpticalError::Extent)?,
                    exact_integer: value.clone(),
                    divisor: divisor.clone(),
                    quotient,
                    remainder,
                    rendered_sample,
                });
            }
            let left = cell
                .x
                .checked_sub(min_x)
                .and_then(|value| value.checked_mul(step))
                .and_then(|value| value.checked_add(1))
                .ok_or(NativeOpticalError::Extent)?;
            let top = cell
                .y
                .checked_sub(min_y)
                .and_then(|value| value.checked_mul(step))
                .and_then(|value| value.checked_add(1))
                .ok_or(NativeOpticalError::Extent)?;
            for y in top..top.checked_add(grain).ok_or(NativeOpticalError::Extent)? {
                for x in left..left.checked_add(grain).ok_or(NativeOpticalError::Extent)? {
                    image.put_pixel(x, y, Rgb(samples));
                }
            }
            rendered.push(cell.address_sha256.clone());
        }
        if rendered.is_empty() {
            return Err(NativeOpticalError::Intervention);
        }
        let mut png = Cursor::new(Vec::new());
        DynamicImage::ImageRgb8(image)
            .write_to(&mut png, ImageFormat::Png)
            .map_err(|error| NativeOpticalError::Raster(error.to_string()))?;
        let png = png.into_inner();
        let png_sha256 = hex_sha256(&png);
        let mut projection = NativeOpticalRasterProjection {
            schema: NATIVE_OPTICAL_RASTER_SCHEMA.to_owned(),
            field_identity_sha256: self.identity_sha256.clone(),
            intervention,
            width,
            height,
            rendered_cell_addresses: rendered,
            omitted_cell_addresses: omitted,
            channel_quotients: quotients,
            png_sha256,
            complete_field_reconstruction_fibre_retained: true,
            cold_renderer_only: true,
            identity_sha256: String::new(),
        };
        projection.identity_sha256 = digest(&(
            &projection.schema,
            &projection.field_identity_sha256,
            &projection.intervention,
            projection.width,
            projection.height,
            &projection.rendered_cell_addresses,
            &projection.omitted_cell_addresses,
            &projection.channel_quotients,
            &projection.png_sha256,
            projection.complete_field_reconstruction_fibre_retained,
            projection.cold_renderer_only,
        ))?;
        Ok((png, projection))
    }

    fn rederived_identity(&self) -> Result<String, NativeOpticalError> {
        digest(&(
            &self.schema,
            &self.morphology_identity_sha256,
            &self.radiation_identity_sha256,
            self.width_cells,
            self.height_cells,
            &self.cells,
            &self.scale_covers,
            &self.alternative_covers,
            self.source_image_accessible,
            self.pixel_template_applied,
            self.label_route_applied,
        ))
    }
}

impl OpticalProductRest {
    pub fn cultivate(
        body: AcousticProductRest,
        founding: &NativeAcousticRadiationInput,
    ) -> Result<(Self, NativeOpticalCultivationReceipt), NativeOpticalError> {
        body.validate()
            .map_err(|error| NativeOpticalError::Standing(error.to_string()))?;
        if body.production().founding_radiation_identity_sha256 != founding.identity_sha256 {
            return Err(NativeOpticalError::Lineage);
        }
        let production = NativeOpticalProductionMorphology::found(founding)?;
        let predecessor_rest_identity_sha256 = body.identity().to_owned();
        let mut rest = Self {
            schema: OPTICAL_PRODUCT_REST_SCHEMA.to_owned(),
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        let receipt = NativeOpticalCultivationReceipt {
            predecessor_rest_identity_sha256,
            successor_rest_identity_sha256: rest.identity_sha256.clone(),
            morphology_identity_sha256: rest.production.identity_sha256.clone(),
            founding_radiation_identity_sha256: founding.identity_sha256.clone(),
            port_population: rest.production.ordered_ports.len(),
            causal_order_population: rest.production.founding_causal_order_population,
            scale_spans: rest.production.scale_spans.clone(),
            source_current_retained_in_morphology: false,
            source_image_retained_in_morphology: false,
            pixel_template_retained: false,
            label_route_retained: false,
        };
        Ok((rest, receipt))
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeOpticalError> {
        let rest: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeOpticalError::Wire(error.to_string()))?;
        rest.validate()?;
        Ok(rest)
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeOpticalError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeOpticalError::Wire(error.to_string()))
    }

    pub fn identity(&self) -> &str {
        &self.identity_sha256
    }
    pub fn body(&self) -> &AcousticProductRest {
        &self.body
    }
    pub fn production(&self) -> &NativeOpticalProductionMorphology {
        &self.production
    }

    pub fn withdraw_relational_cell(
        self,
        cell_address: &str,
    ) -> Result<(Self, OpticalRelationalCellWithdrawal), NativeOpticalError> {
        self.validate()?;
        let Self {
            schema,
            body,
            production,
            identity_sha256,
        } = self;
        let (body, withdrawal) = body
            .withdraw_relational_cell(cell_address)
            .map_err(|error| NativeOpticalError::Standing(error.to_string()))?;
        let mut rest = Self {
            schema,
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        Ok((
            rest,
            OpticalRelationalCellWithdrawal {
                original_rest_identity_sha256: identity_sha256,
                body: withdrawal,
            },
        ))
    }

    pub fn restore_relational_cell(
        self,
        withdrawal: OpticalRelationalCellWithdrawal,
    ) -> Result<Self, NativeOpticalError> {
        self.validate()?;
        let Self {
            schema,
            body,
            production,
            identity_sha256: _,
        } = self;
        let body = body
            .restore_relational_cell(withdrawal.body)
            .map_err(|error| NativeOpticalError::Standing(error.to_string()))?;
        let mut rest = Self {
            schema,
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        if rest.identity_sha256 != withdrawal.original_rest_identity_sha256 {
            return Err(NativeOpticalError::Lineage);
        }
        rest.validate()?;
        Ok(rest)
    }

    pub fn radiate(
        &self,
        input: &NativeAcousticRadiationInput,
    ) -> Result<NativeOpticalPotentialField, NativeOpticalError> {
        self.validate()?;
        self.production.form_field(input)
    }

    pub fn withdraw_production(
        self,
    ) -> Result<
        (
            AcousticProductRest,
            WithdrawnNativeOpticalProduction,
            NativeOpticalStandingMutation,
        ),
        NativeOpticalError,
    > {
        self.validate()?;
        let original_rest_identity_sha256 = self.identity_sha256;
        let predecessor_body_identity_sha256 = self.body.identity().to_owned();
        let morphology_identity_sha256 = self.production.identity_sha256.clone();
        let mut withdrawn = WithdrawnNativeOpticalProduction {
            schema: WITHDRAWN_OPTICAL_PRODUCTION_SCHEMA.to_owned(),
            original_rest_identity_sha256: original_rest_identity_sha256.clone(),
            predecessor_body_identity_sha256: predecessor_body_identity_sha256.clone(),
            morphology: self.production,
            identity_sha256: String::new(),
        };
        withdrawn.identity_sha256 = withdrawn.rederived_identity()?;
        let mutation = NativeOpticalStandingMutation {
            operation: "withdraw-native-optical-production".to_owned(),
            predecessor_rest_identity_sha256: original_rest_identity_sha256,
            successor_rest_identity_sha256: predecessor_body_identity_sha256,
            morphology_identity_sha256,
        };
        Ok((self.body, withdrawn, mutation))
    }

    pub fn restore_production(
        body: AcousticProductRest,
        withdrawn: WithdrawnNativeOpticalProduction,
    ) -> Result<(Self, NativeOpticalStandingMutation), NativeOpticalError> {
        withdrawn.validate()?;
        if body.identity() != withdrawn.predecessor_body_identity_sha256 {
            return Err(NativeOpticalError::Lineage);
        }
        let predecessor_rest_identity_sha256 = body.identity().to_owned();
        let morphology_identity_sha256 = withdrawn.morphology.identity_sha256.clone();
        let expected = withdrawn.original_rest_identity_sha256;
        let mut rest = Self {
            schema: OPTICAL_PRODUCT_REST_SCHEMA.to_owned(),
            body,
            production: withdrawn.morphology,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        if rest.identity_sha256 != expected {
            return Err(NativeOpticalError::Lineage);
        }
        rest.validate()?;
        let mutation = NativeOpticalStandingMutation {
            operation: "restore-native-optical-production".to_owned(),
            predecessor_rest_identity_sha256,
            successor_rest_identity_sha256: rest.identity_sha256.clone(),
            morphology_identity_sha256,
        };
        Ok((rest, mutation))
    }

    /// Compose an inherited source-neutral morphology over another compatible acoustic
    /// continuation body. Exact port compatibility is checked when later current radiates.
    pub fn compose_source_neutral_production(
        body: AcousticProductRest,
        withdrawn: WithdrawnNativeOpticalProduction,
    ) -> Result<(Self, NativeOpticalOrganCompositionReceipt), NativeOpticalError> {
        body.validate()
            .map_err(|error| NativeOpticalError::Standing(error.to_string()))?;
        withdrawn.validate()?;
        let inherited_rest_identity_sha256 = withdrawn.original_rest_identity_sha256.clone();
        let inherited_predecessor_identity_sha256 =
            withdrawn.predecessor_body_identity_sha256.clone();
        let morphology_identity_sha256 = withdrawn.morphology.identity_sha256.clone();
        let receiving_body_identity_sha256 = body.identity().to_owned();
        let mut rest = Self {
            schema: OPTICAL_PRODUCT_REST_SCHEMA.to_owned(),
            body,
            production: withdrawn.morphology,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest.rederived_identity()?;
        rest.validate()?;
        let receipt = NativeOpticalOrganCompositionReceipt {
            inherited_rest_identity_sha256,
            inherited_predecessor_identity_sha256,
            morphology_identity_sha256,
            receiving_body_identity_sha256,
            composed_rest_identity_sha256: rest.identity_sha256.clone(),
            source_occurrence_consulted: false,
            source_image_retained_in_morphology: false,
            pixel_template_retained: false,
            label_route_retained: false,
        };
        Ok((rest, receipt))
    }

    pub fn validate(&self) -> Result<(), NativeOpticalError> {
        self.body
            .validate()
            .map_err(|error| NativeOpticalError::Standing(error.to_string()))?;
        self.production.validate()?;
        if self.schema != OPTICAL_PRODUCT_REST_SCHEMA
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeOpticalError::Lineage);
        }
        Ok(())
    }

    fn rederived_identity(&self) -> Result<String, NativeOpticalError> {
        digest(&(
            &self.schema,
            self.body.identity(),
            &self.production.identity_sha256,
        ))
    }
}

impl WithdrawnNativeOpticalProduction {
    fn validate(&self) -> Result<(), NativeOpticalError> {
        self.morphology.validate()?;
        if self.schema != WITHDRAWN_OPTICAL_PRODUCTION_SCHEMA
            || !is_digest(&self.original_rest_identity_sha256)
            || !is_digest(&self.predecessor_body_identity_sha256)
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeOpticalError::Lineage);
        }
        Ok(())
    }
    fn rederived_identity(&self) -> Result<String, NativeOpticalError> {
        digest(&(
            &self.schema,
            &self.original_rest_identity_sha256,
            &self.predecessor_body_identity_sha256,
            &self.morphology,
        ))
    }
}

impl MembraneStanding for OpticalProductRest {
    fn validate_membrane_standing(&self) -> Result<(), String> {
        self.validate().map_err(|error| error.to_string())
    }
    fn membrane_identity(&self) -> &str {
        &self.identity_sha256
    }
    fn membrane_ecology(&self) -> &holonic_engine::native_spool::NativeSituatedSpoolBundle {
        self.body.membrane_ecology()
    }
    fn membrane_realization(&self) -> &ReceiverHistoryRealizationPassage {
        self.body.membrane_realization()
    }
    fn membrane_branches(&self) -> &[SituatedCultivationBranch] {
        self.body.membrane_branches()
    }
    fn membrane_correspondences(&self) -> &[LaboratoryFactorCycleCorrespondence] {
        self.body.membrane_correspondences()
    }
    fn membrane_affine_cells(&self) -> &[LaboratoryCellAffineSection] {
        self.body.membrane_affine_cells()
    }
}

impl GranularMembraneStanding for OpticalProductRest {
    fn membrane_granular_potential(&self) -> &NativeGranularPotential {
        self.body.membrane_granular_potential()
    }
}

impl MembraneDifferenceStanding for OpticalProductRest {
    type Successor = Self;
    fn deposit_membrane_difference(
        self,
        difference: SituatedDifferenceSection,
    ) -> Result<Self::Successor, String> {
        let production = self.production;
        let body = self.body.deposit_membrane_difference(difference)?;
        let mut rest = Self {
            schema: OPTICAL_PRODUCT_REST_SCHEMA.to_owned(),
            body,
            production,
            identity_sha256: String::new(),
        };
        rest.identity_sha256 = rest
            .rederived_identity()
            .map_err(|error| error.to_string())?;
        rest.validate().map_err(|error| error.to_string())?;
        Ok(rest)
    }
}

fn found_scale_covers(
    morphology: &str,
    radiation: &str,
    width: u32,
    height: u32,
    spans: &[u32],
    cells: &[NativeOpticalCell],
) -> Result<Vec<NativeOpticalScaleCover>, NativeOpticalError> {
    let mut covers = Vec::new();
    for &span in spans {
        let shifts = if span == 1 {
            vec![(0, 0, false)]
        } else {
            vec![(0, 0, false), (span / 2, span / 2, true)]
        };
        for (shift_x, shift_y, translated) in shifts {
            let mut top = shift_y;
            while top < height {
                let mut left = shift_x;
                while left < width {
                    let bounds = NativeOpticalCellBounds {
                        left,
                        top,
                        right: left.saturating_add(span).min(width),
                        bottom: top.saturating_add(span).min(height),
                    };
                    let member_addresses = cells
                        .iter()
                        .filter(|cell| bounds.contains(cell.x, cell.y))
                        .map(|cell| cell.address_sha256.clone())
                        .collect::<Vec<_>>();
                    if !member_addresses.is_empty() {
                        covers.push(NativeOpticalScaleCover {
                            address_sha256: digest(&(
                                morphology,
                                radiation,
                                span,
                                translated,
                                bounds,
                                &member_addresses,
                            ))?,
                            span,
                            translated,
                            bounds,
                            member_addresses,
                        });
                    }
                    left = left.checked_add(span).ok_or(NativeOpticalError::Extent)?;
                }
                top = top.checked_add(span).ok_or(NativeOpticalError::Extent)?;
            }
        }
    }
    Ok(covers)
}

fn exact_color_coordinates(current: &ExactComplexWaveCurrent) -> [BigInt; 3] {
    let denominator = lcm_positive(current.real.denom(), current.imaginary.denom());
    let real = current.real.numer() * (&denominator / current.real.denom());
    let imaginary = current.imaginary.numer() * (&denominator / current.imaginary.denom());
    [real.clone(), imaginary.clone(), real + imaginary]
}

fn ceil_sqrt(value: u32) -> Option<u32> {
    if value == 0 {
        return None;
    }
    let mut root = 1_u32;
    while root.checked_mul(root)? < value {
        root = root.checked_add(1)?;
    }
    Some(root)
}

fn ceil_div(left: u32, right: u32) -> Option<u32> {
    if right == 0 {
        return None;
    }
    left.checked_add(right.checked_sub(1)?)?.checked_div(right)
}

fn dyadic_spans(extent: u32) -> Result<Vec<u32>, NativeOpticalError> {
    if extent == 0 {
        return Err(NativeOpticalError::Extent);
    }
    let mut spans = vec![1_u32];
    while *spans.last().ok_or(NativeOpticalError::Extent)? < extent {
        let prior = *spans.last().ok_or(NativeOpticalError::Extent)?;
        spans.push(prior.checked_mul(2).ok_or(NativeOpticalError::Extent)?);
    }
    Ok(spans)
}

fn is_channel_permutation(order: [u8; 3]) -> bool {
    let mut order = order;
    order.sort_unstable();
    order == [0, 1, 2]
}

fn lcm_positive(left: &BigInt, right: &BigInt) -> BigInt {
    (left / gcd_positive(left.clone(), right.clone())) * right
}

fn gcd_positive(mut left: BigInt, mut right: BigInt) -> BigInt {
    left = left.abs();
    right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

use holonic_engine::is_sha256_digest as is_digest;

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn digest(value: &impl Serialize) -> Result<String, NativeOpticalError> {
    serde_json::to_vec(value)
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|error| NativeOpticalError::Wire(error.to_string()))
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeOpticalError {
    #[error("the native radiation input refused: {0}")]
    Radiation(String),
    #[error("the native optical production morphology is malformed")]
    MalformedMorphology,
    #[error("the exact native optical field is malformed")]
    MalformedField,
    #[error("the native optical boundary lineage does not join")]
    Lineage,
    #[error("the native optical receiver intervention is empty or malformed")]
    Intervention,
    #[error("the native optical carrier exceeded its finite apparatus chart")]
    Extent,
    #[error("the native optical raster receiver refused: {0}")]
    Raster(String),
    #[error("the rested Athena body refused: {0}")]
    Standing(String),
    #[error("the native optical wire refused: {0}")]
    Wire(String),
}

#[cfg(test)]
mod tests {
    use super::{ceil_sqrt, dyadic_spans, is_channel_permutation};

    #[test]
    fn lattice_extent_and_scale_population_are_derived() {
        assert_eq!(ceil_sqrt(180), Some(14));
        assert_eq!(dyadic_spans(26).unwrap(), vec![1, 2, 4, 8, 16, 32]);
    }

    #[test]
    fn color_chart_requires_an_exact_permutation() {
        assert!(is_channel_permutation([2, 0, 1]));
        assert!(!is_channel_permutation([0, 0, 1]));
    }
}
