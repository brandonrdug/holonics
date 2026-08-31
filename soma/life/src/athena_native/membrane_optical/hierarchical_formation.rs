//! Hierarchical optical formation from one exact Athena radiation field.
//!
//! The admitted optical hierarchy owns space, scale, incidence, ambiguity, and reconstruction.
//! The radiation field contributes current through a derived chart. A PNG is only a later cold
//! receiver over this composed potential complex.

use std::{collections::BTreeMap, io::Cursor};

use holonic_engine::ExactComplexWaveCurrent;
use image::{DynamicImage, ImageFormat, ImageReader, Rgb, RgbImage};
use num_bigint::BigInt;
use num_traits::{ToPrimitive, Zero};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::mathematical_source::{HierarchicalOpticalPassage, OpticalBounds, OpticalHolonGrain};

use super::{NativeOpticalError, NativeOpticalPotentialField};

pub const NATIVE_HIERARCHICAL_OPTICAL_FORMATION_SCHEMA: &str =
    "soma-life.native-hierarchical-optical-formation.v1";
pub const NATIVE_HIERARCHICAL_OPTICAL_PROJECTION_SCHEMA: &str =
    "soma-life.native-hierarchical-optical-projection.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeHierarchicalOpticalFormationSection {
    pub holon_address_sha256: String,
    pub grain: OpticalHolonGrain,
    pub original_bounds: OpticalBounds,
    pub transported_bounds: OpticalBounds,
    pub field_cell_address_sha256: String,
    pub field_cover_addresses_sha256: Vec<String>,
    pub source_alternative_parent_addresses_sha256: Vec<String>,
    pub current: ExactComplexWaveCurrent,
    pub complete_source_holon_fibre_retained: bool,
    pub complete_field_cover_fibre_retained: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeHierarchicalOpticalFormation {
    pub schema: String,
    pub field_identity_sha256: String,
    pub source_hierarchy_identity_sha256: String,
    pub source_incidence_identity_sha256: String,
    pub width: u32,
    pub height: u32,
    pub source_holon_population: usize,
    pub source_incidence_population: usize,
    pub source_alternative_cover_population: usize,
    pub source_repeated_form_population: usize,
    pub sections: Vec<NativeHierarchicalOpticalFormationSection>,
    pub source_transcript_used: bool,
    pub source_object_class_routed_transport: bool,
    pub rectangular_port_lattice_used_as_optical_space: bool,
    pub complete_source_hierarchy_fibre_retained: bool,
    pub identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NativeHierarchicalOpticalProjection {
    pub schema: String,
    pub formation_identity_sha256: String,
    pub source_raster_sha256: String,
    pub width: u32,
    pub height: u32,
    pub rendered_holon_addresses_sha256: Vec<String>,
    pub png_sha256: String,
    pub complete_formation_fibre_retained: bool,
    pub cold_renderer_only: bool,
    pub identity_sha256: String,
}

impl NativeHierarchicalOpticalFormation {
    pub(super) fn found(
        field: &NativeOpticalPotentialField,
        hierarchy: &HierarchicalOpticalPassage,
    ) -> Result<Self, NativeOpticalError> {
        field.validate()?;
        hierarchy
            .validate()
            .map_err(|error| NativeOpticalError::Standing(error.to_string()))?;
        let hierarchy_bytes = hierarchy
            .canonical_bytes()
            .map_err(|error| NativeOpticalError::Standing(error.to_string()))?;
        let source_hierarchy_identity_sha256 = hex_sha256(&hierarchy_bytes);
        let alternative_parents = hierarchy
            .alternative_covers
            .iter()
            .map(|cover| {
                (
                    cover.subject_address.as_str(),
                    cover.alternative_parent_addresses.clone(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let aperture = derived_displacement_aperture(hierarchy)?;
        let mut sections = Vec::with_capacity(hierarchy.holons.len());
        for holon in &hierarchy.holons {
            let centre_x = holon.bounds.left.saturating_add(holon.bounds.right) / 2;
            let centre_y = holon.bounds.top.saturating_add(holon.bounds.bottom) / 2;
            let field_x = rebase_coordinate(centre_x, hierarchy.width, field.width_cells)?;
            let field_y = rebase_coordinate(centre_y, hierarchy.height, field.height_cells)?;
            let cell = field
                .cells
                .iter()
                .find(|cell| cell.x == field_x && cell.y == field_y)
                .or_else(|| nearest_cell(field, field_x, field_y))
                .ok_or(NativeOpticalError::MalformedField)?;
            let field_cover_addresses_sha256 = field
                .scale_covers
                .iter()
                .filter(|cover| cover.member_addresses.contains(&cell.address_sha256))
                .map(|cover| cover.address_sha256.clone())
                .collect::<Vec<_>>();
            if field_cover_addresses_sha256.is_empty() {
                return Err(NativeOpticalError::MalformedField);
            }
            let horizontal = situated_step(&cell.current.real, aperture)?;
            let vertical = situated_step(&cell.current.imaginary, aperture)?;
            let transported_bounds = transport_bounds(
                holon.bounds,
                horizontal,
                vertical,
                hierarchy.width,
                hierarchy.height,
            );
            sections.push(NativeHierarchicalOpticalFormationSection {
                holon_address_sha256: holon.address_sha256.clone(),
                grain: holon.grain,
                original_bounds: holon.bounds,
                transported_bounds,
                field_cell_address_sha256: cell.address_sha256.clone(),
                field_cover_addresses_sha256,
                source_alternative_parent_addresses_sha256: alternative_parents
                    .get(holon.address_sha256.as_str())
                    .cloned()
                    .unwrap_or_default(),
                current: cell.current.clone(),
                complete_source_holon_fibre_retained: true,
                complete_field_cover_fibre_retained: true,
            });
        }
        let mut formation = Self {
            schema: NATIVE_HIERARCHICAL_OPTICAL_FORMATION_SCHEMA.to_owned(),
            field_identity_sha256: field.identity_sha256.clone(),
            source_hierarchy_identity_sha256,
            source_incidence_identity_sha256: hierarchy
                .relation_receipt
                .complete_relation_words_sha256
                .clone(),
            width: hierarchy.width,
            height: hierarchy.height,
            source_holon_population: hierarchy.holons.len(),
            source_incidence_population: hierarchy.incidences.len(),
            source_alternative_cover_population: hierarchy.alternative_covers.len(),
            source_repeated_form_population: hierarchy.repeated_forms.len(),
            sections,
            source_transcript_used: false,
            source_object_class_routed_transport: false,
            rectangular_port_lattice_used_as_optical_space: false,
            complete_source_hierarchy_fibre_retained: true,
            identity_sha256: String::new(),
        };
        formation.identity_sha256 = formation.rederived_identity()?;
        formation.validate()?;
        Ok(formation)
    }

    pub fn validate(&self) -> Result<(), NativeOpticalError> {
        if self.schema != NATIVE_HIERARCHICAL_OPTICAL_FORMATION_SCHEMA
            || !is_digest(&self.field_identity_sha256)
            || !is_digest(&self.source_hierarchy_identity_sha256)
            || !is_digest(&self.source_incidence_identity_sha256)
            || self.width == 0
            || self.height == 0
            || self.sections.is_empty()
            || self.sections.len() != self.source_holon_population
            || self.source_incidence_population == 0
            || self.source_transcript_used
            || self.source_object_class_routed_transport
            || self.rectangular_port_lattice_used_as_optical_space
            || !self.complete_source_hierarchy_fibre_retained
            || self.sections.iter().any(|section| {
                !is_digest(&section.holon_address_sha256)
                    || !is_digest(&section.field_cell_address_sha256)
                    || section.field_cover_addresses_sha256.is_empty()
                    || section
                        .field_cover_addresses_sha256
                        .iter()
                        .any(|address| !is_digest(address))
                    || !section.complete_source_holon_fibre_retained
                    || !section.complete_field_cover_fibre_retained
            })
            || self.identity_sha256 != self.rederived_identity()?
        {
            return Err(NativeOpticalError::MalformedField);
        }
        Ok(())
    }

    pub fn render_png(
        &self,
        encoded_source_raster: &[u8],
    ) -> Result<(Vec<u8>, NativeHierarchicalOpticalProjection), NativeOpticalError> {
        self.validate()?;
        let source = ImageReader::new(Cursor::new(encoded_source_raster))
            .with_guessed_format()
            .map_err(|error| NativeOpticalError::Raster(error.to_string()))?
            .decode()
            .map_err(|error| NativeOpticalError::Raster(error.to_string()))?
            .to_rgb8();
        if source.width() != self.width || source.height() != self.height {
            return Err(NativeOpticalError::Lineage);
        }
        let background = *source.get_pixel(0, 0);
        let mut image = RgbImage::from_pixel(self.width, self.height, background);
        let mut rendered_holon_addresses_sha256 = Vec::new();
        // The supplied finest connected optical occurrences reconstruct the cold surface. Higher
        // grains remain in the native formation and constrain their currents/covers, but drawing
        // their hulls as solid rectangles would join unrelated components and destroy the very
        // optical incidence the return receiver must recover.
        for section in self
            .sections
            .iter()
            .filter(|section| section.grain == OpticalHolonGrain::Component)
        {
            let color = section_color(section)?;
            transport_component_pixels(
                &source,
                &mut image,
                section.original_bounds,
                section.transported_bounds,
                background,
                color,
            );
            rendered_holon_addresses_sha256.push(section.holon_address_sha256.clone());
        }
        if rendered_holon_addresses_sha256.is_empty() {
            return Err(NativeOpticalError::MalformedField);
        }
        let mut png = Cursor::new(Vec::new());
        DynamicImage::ImageRgb8(image)
            .write_to(&mut png, ImageFormat::Png)
            .map_err(|error| NativeOpticalError::Raster(error.to_string()))?;
        let png = png.into_inner();
        let mut projection = NativeHierarchicalOpticalProjection {
            schema: NATIVE_HIERARCHICAL_OPTICAL_PROJECTION_SCHEMA.to_owned(),
            formation_identity_sha256: self.identity_sha256.clone(),
            source_raster_sha256: hex_sha256(encoded_source_raster),
            width: self.width,
            height: self.height,
            rendered_holon_addresses_sha256,
            png_sha256: hex_sha256(&png),
            complete_formation_fibre_retained: true,
            cold_renderer_only: true,
            identity_sha256: String::new(),
        };
        projection.identity_sha256 = digest(&(
            &projection.schema,
            &projection.formation_identity_sha256,
            &projection.source_raster_sha256,
            projection.width,
            projection.height,
            &projection.rendered_holon_addresses_sha256,
            &projection.png_sha256,
        ))?;
        Ok((png, projection))
    }

    fn rederived_identity(&self) -> Result<String, NativeOpticalError> {
        digest(&(
            &self.schema,
            &self.field_identity_sha256,
            &self.source_hierarchy_identity_sha256,
            &self.source_incidence_identity_sha256,
            self.width,
            self.height,
            self.source_holon_population,
            self.source_incidence_population,
            self.source_alternative_cover_population,
            self.source_repeated_form_population,
            &self.sections,
            self.source_transcript_used,
            self.source_object_class_routed_transport,
            self.rectangular_port_lattice_used_as_optical_space,
            self.complete_source_hierarchy_fibre_retained,
        ))
    }
}

fn derived_displacement_aperture(
    hierarchy: &HierarchicalOpticalPassage,
) -> Result<i64, NativeOpticalError> {
    let grain = hierarchy
        .scale
        .lower_median_width
        .min(hierarchy.scale.lower_median_height)
        .max(1);
    i64::try_from(grain).map_err(|_| NativeOpticalError::Extent)
}

fn rebase_coordinate(
    source: i64,
    source_extent: u32,
    target_extent: u32,
) -> Result<u32, NativeOpticalError> {
    if source_extent == 0 || target_extent == 0 {
        return Err(NativeOpticalError::Extent);
    }
    let source = source.max(0) as u128;
    let target = source
        .saturating_mul(u128::from(target_extent))
        .checked_div(u128::from(source_extent))
        .ok_or(NativeOpticalError::Extent)?
        .min(u128::from(target_extent - 1));
    u32::try_from(target).map_err(|_| NativeOpticalError::Extent)
}

fn nearest_cell(
    field: &NativeOpticalPotentialField,
    x: u32,
    y: u32,
) -> Option<&super::NativeOpticalCell> {
    field.cells.iter().min_by_key(|cell| {
        u64::from(cell.x.abs_diff(x)).saturating_add(u64::from(cell.y.abs_diff(y)))
    })
}

fn situated_step(
    value: &num_rational::BigRational,
    aperture: i64,
) -> Result<i64, NativeOpticalError> {
    if aperture <= 0 || value.is_zero() {
        return Ok(0);
    }
    let integer = value.numer() / value.denom();
    let span = BigInt::from(aperture)
        .checked_mul(&BigInt::from(2u8))
        .and_then(|value| value.checked_add(&BigInt::from(1u8)))
        .ok_or(NativeOpticalError::Extent)?;
    let residue = ((integer % &span) + &span) % &span;
    residue
        .to_i64()
        .and_then(|coordinate| coordinate.checked_sub(aperture))
        .ok_or(NativeOpticalError::Extent)
}

fn transport_bounds(
    bounds: OpticalBounds,
    horizontal: i64,
    vertical: i64,
    width: u32,
    height: u32,
) -> OpticalBounds {
    let max_x = i64::from(width);
    let max_y = i64::from(height);
    let left = bounds
        .left
        .saturating_add(horizontal)
        .clamp(0, max_x.saturating_sub(1));
    let top = bounds
        .top
        .saturating_add(vertical)
        .clamp(0, max_y.saturating_sub(1));
    let right = bounds
        .right
        .saturating_add(horizontal)
        .clamp(left.saturating_add(1), max_x);
    let bottom = bounds
        .bottom
        .saturating_add(vertical)
        .clamp(top.saturating_add(1), max_y);
    OpticalBounds {
        left,
        top,
        right,
        bottom,
    }
}

fn section_color(
    section: &NativeHierarchicalOpticalFormationSection,
) -> Result<Rgb<u8>, NativeOpticalError> {
    let real = signed_channel(&section.current.real)?;
    let imaginary = signed_channel(&section.current.imaginary)?;
    let coupled = signed_channel(&(&section.current.real + &section.current.imaginary))?;
    let grain_shift = match section.grain {
        OpticalHolonGrain::Component => 0,
        OpticalHolonGrain::GlyphOrSubfigure => 1,
        OpticalHolonGrain::DecoratedSymbol => 2,
        OpticalHolonGrain::Term => 3,
        OpticalHolonGrain::Assembly => 4,
        OpticalHolonGrain::RelationOrEquation => 5,
        OpticalHolonGrain::LabelledOrDiagramBlock => 6,
        OpticalHolonGrain::Page => 7,
    };
    Ok(Rgb([
        real.rotate_left(grain_shift),
        imaginary.rotate_left(grain_shift),
        coupled.rotate_left(grain_shift),
    ]))
}

fn signed_channel(value: &num_rational::BigRational) -> Result<u8, NativeOpticalError> {
    let denominator = BigInt::from(u8::MAX);
    let integer = value.numer() / value.denom();
    let residue = ((integer % &denominator) + &denominator) % &denominator;
    residue
        .to_u8()
        .map(|sample| sample.saturating_add(1))
        .ok_or(NativeOpticalError::Extent)
}

fn transport_component_pixels(
    source: &RgbImage,
    target: &mut RgbImage,
    original: OpticalBounds,
    transported: OpticalBounds,
    background: Rgb<u8>,
    current_color: Rgb<u8>,
) {
    let horizontal = transported.left.saturating_sub(original.left);
    let vertical = transported.top.saturating_sub(original.top);
    let left = original.left.max(0) as u32;
    let top = original.top.max(0) as u32;
    let right = u32::try_from(original.right)
        .unwrap_or(source.width())
        .min(source.width());
    let bottom = u32::try_from(original.bottom)
        .unwrap_or(source.height())
        .min(source.height());
    for y in top..bottom {
        for x in left..right {
            let pixel = *source.get_pixel(x, y);
            if pixel == background {
                continue;
            }
            let target_x = i64::from(x).saturating_add(horizontal);
            let target_y = i64::from(y).saturating_add(vertical);
            let (Ok(target_x), Ok(target_y)) = (u32::try_from(target_x), u32::try_from(target_y))
            else {
                continue;
            };
            if target_x >= target.width() || target_y >= target.height() {
                continue;
            }
            let mut transported_pixel = pixel;
            blend(&mut transported_pixel, current_color);
            *target.get_pixel_mut(target_x, target_y) = transported_pixel;
        }
    }
}

fn blend(pixel: &mut Rgb<u8>, color: Rgb<u8>) {
    for channel in 0..3 {
        pixel[channel] = ((u16::from(pixel[channel]) + u16::from(color[channel])) / 2) as u8;
    }
}

use holonic_engine::is_sha256_digest as is_digest;

fn digest(value: &impl Serialize) -> Result<String, NativeOpticalError> {
    serde_json::to_vec(value)
        .map(|bytes| hex_sha256(&bytes))
        .map_err(|error| NativeOpticalError::Wire(error.to_string()))
}

fn hex_sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
