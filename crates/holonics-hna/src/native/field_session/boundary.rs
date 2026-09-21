//! Exterior codec boundary for the incident-field session.
//!
//! This adapter owns only the presentation chart and its seeded boundary maps.
//! Generation and receiving remain resident operations on the field body; symbol
//! ordinals are used to address rows and never become local field coordinates.

use super::super::section_input::SymbolCurrentChart;
use super::NativeSessionError;
use holonic_engine::{
    native_ecology::constitutive_fibre::{
        BoundaryMaterialMaps, BoundaryMaterialSeed, NativeNormalPrior,
        ResidentNormalEnclosureSection,
    },
    resident_section::{ResidentGrain, ResidentSurface},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryMaterialSpec {
    pub local_complex: usize,
    pub output_aperture: usize,
    pub grain: ResidentGrain,
    pub material_seed: BoundaryMaterialSeed,
}

/// A source-qualified boundary chart.  The native field width is supplied by
/// `local_complex`; the codec length only sizes the exterior maps and rows.
pub struct BoundaryMaterial<'c> {
    _surface: &'c ResidentSurface<'c>,
    chart: SymbolCurrentChart,
    spec: BoundaryMaterialSpec,
    maps: BoundaryMaterialMaps,
}

impl<'c> BoundaryMaterial<'c> {
    pub fn found(
        surface: &'c ResidentSurface<'c>,
        chart: SymbolCurrentChart,
        local_complex: usize,
        output_aperture: usize,
        grain: ResidentGrain,
        material_seed: BoundaryMaterialSeed,
    ) -> Result<Self, NativeSessionError> {
        if output_aperture == 0 || grain.0 != material_seed.fractional_bits {
            return Err(NativeSessionError::Application(
                "invalid boundary material extent".into(),
            ));
        }
        let maps = material_seed
            .initial_maps(chart.alphabet().len(), local_complex)
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        maps.validate_bootstrap()
            .map_err(|e| NativeSessionError::Application(e.to_string()))?;
        Ok(Self {
            _surface: surface,
            chart,
            spec: BoundaryMaterialSpec {
                local_complex,
                output_aperture,
                grain,
                material_seed,
            },
            maps,
        })
    }

    pub fn spec(&self) -> &BoundaryMaterialSpec {
        &self.spec
    }
    pub fn chart(&self) -> &SymbolCurrentChart {
        &self.chart
    }
    pub fn maps(&self) -> &BoundaryMaterialMaps {
        &self.maps
    }

    /// Normal-law prior for R_text, retaining the homogeneous bias as its final
    /// source feature.
    pub fn text_prior(&self) -> Result<NativeNormalPrior, NativeSessionError> {
        NativeNormalPrior::from_coefficients(self.maps.decoder.clone())
            .map_err(|e| NativeSessionError::Application(e.to_string()))
    }

    /// Append the homogeneous receiver coordinate to a generated resident
    /// boundary section without reading its rows to the host.
    pub fn support_from_boundary(
        &self,
        boundary: &ResidentNormalEnclosureSection<'c>,
    ) -> Result<ResidentNormalEnclosureSection<'c>, NativeSessionError> {
        if boundary.rows() != self.spec.output_aperture
            || boundary.components() != 2 * self.spec.local_complex
            || boundary.grain() != self.spec.grain
        {
            return Err(NativeSessionError::Application(
                "boundary/support chart mismatch".into(),
            ));
        }
        boundary
            .pack_components(self.spec.output_aperture)
            .and_then(|packed| packed.append_homogeneous())
            .map_err(|e| NativeSessionError::Application(e.to_string()))
    }
}
