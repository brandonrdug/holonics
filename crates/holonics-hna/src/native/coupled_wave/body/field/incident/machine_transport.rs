//! Resident fixed-generator transport for the incident field.
//!
//! The machine source is the six-real-coordinate complex3 chart stored in a width-12
//! realification.  Forward maps decode that chart, apply the resident affine geometry operation,
//! and realify value currents where the receiving value chart requires width 12.  Reverse maps
//! pull back each producing branch through its own affine/realification owner and only then sum
//! full source-row covectors.  Query geometry, neighbor geometry, and transported values remain
//! separate operands throughout.
//!
//! This module deliberately owns no machine declaration, grouping, parent lifetime, phase/clock
//! contract, or dynamic geometry derivative.  Callers prepare and retain coefficient sections;
//! these wrappers only enact the supplied resident maps.

use super::*;
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeAffineGeometry, NativeEnclosurePropagation, NativePairParticipation, NativeRealification,
    ResidentNormalEnclosureSection,
};
use holonic_engine::resident_section::{Dyadic, SeriesAperture};
use std::rc::Rc;

type Section<'c> = ResidentNormalEnclosureSection<'c>;
type SectionRc<'c> = Rc<Section<'c>>;

const MACHINE_REALIFIED_COMPONENTS: usize = 12;
const MACHINE_COMPLEX3_COMPONENTS: usize = 6;

fn machine_error(error: impl ToString) -> NativeSessionError {
    invalid(error)
}

/// A supplied affine value map from the full source field to one group's source rows.
///
/// Forward values retain all six complex3 coordinates after the affine action and are then
/// realified to the native width-12 value chart.  Pullback returns a full source-row width-12
/// covector, including repeated-source joins owned by `NativeAffineGeometry`.
pub struct MachineValueTransport<'c> {
    decoded: NativeRealification<'c>,
    affine: NativeAffineGeometry<'c>,
    realified: NativeRealification<'c>,
}

impl<'c> MachineValueTransport<'c> {
    /// Build one resident value transport. `source` has width 12 and `coefficients` has one
    /// affine row for every requested source index. The exact affine declarations are already
    /// represented by the mounted coefficient section owned by the caller.
    pub fn new(
        source: SectionRc<'c>,
        source_indices: &[usize],
        coefficients: SectionRc<'c>,
    ) -> Result<Self, NativeSessionError> {
        Self::new_with_enclosure(
            source,
            source_indices,
            coefficients,
            NativeEnclosurePropagation::ComponentIntervals,
        )
    }
    pub fn new_with_enclosure(
        source: SectionRc<'c>,
        source_indices: &[usize],
        coefficients: SectionRc<'c>,
        enclosure: NativeEnclosurePropagation,
    ) -> Result<Self, NativeSessionError> {
        if source.components() != MACHINE_REALIFIED_COMPONENTS {
            return Err(machine_error("machine value source must have width 12"));
        }
        let decoded = source
            .clone()
            .decode_realification()
            .map_err(machine_error)?;
        if decoded.output().components() != MACHINE_COMPLEX3_COMPONENTS {
            return Err(machine_error("machine value decode must have width 6"));
        }
        let affine = decoded
            .output_handle()
            .affine_geometry_with_enclosure(source_indices, coefficients, false, enclosure.clone())
            .map_err(machine_error)?;
        let realified = affine.output_handle().realify().map_err(machine_error)?;
        Ok(Self {
            decoded,
            affine,
            realified,
        })
    }

    /// The resident width-12 value rows for this group's producing sources.
    pub fn output(&self) -> &Section<'c> {
        self.realified.output()
    }

    /// Pull a group's width-12 value covector back to the full source field.
    pub fn pull_back(&self, gy: &Section<'c>) -> Result<Section<'c>, NativeSessionError> {
        if gy.components() != MACHINE_REALIFIED_COMPONENTS {
            return Err(machine_error("machine value covector must have width 12"));
        }
        let realified = self.realified.pull_back(gy).map_err(machine_error)?;
        let affine = self
            .affine
            .pull_back(realified.source())
            .map_err(machine_error)?;
        let decoded = self
            .decoded
            .pull_back(affine.source())
            .map_err(machine_error)?;
        Ok(decoded.into_source())
    }
}

/// A fixed-generator participation chart with independent query geometry, neighbor geometry,
/// and value-current maps.
pub struct MachineParticipation<'c> {
    decoded: NativeRealification<'c>,
    query_geometry: NativeAffineGeometry<'c>,
    neighbor_geometry: NativeAffineGeometry<'c>,
    value_geometry: NativeAffineGeometry<'c>,
    value_realified: NativeRealification<'c>,
    participation: NativePairParticipation<'c>,
}

impl<'c> MachineParticipation<'c> {
    /// Build one group's score/value participation.
    ///
    /// `receiver_indices` and `query_coefficients` have one row per receiver.  The flattened
    /// `source_indices` and `neighbor_coefficients` have one row per admitted neighbor, in
    /// receiver-major order.  Values use an independent affine map section and retain width 12;
    /// score geometry uses the projected real face of each affine map.
    pub fn new(
        source: SectionRc<'c>,
        receiver_indices: &[usize],
        source_indices: &[usize],
        query_coefficients: SectionRc<'c>,
        neighbor_coefficients: SectionRc<'c>,
        value_coefficients: SectionRc<'c>,
        beta: Dyadic,
        terms: SeriesAperture,
    ) -> Result<Self, NativeSessionError> {
        Self::new_with_enclosure(
            source,
            receiver_indices,
            source_indices,
            query_coefficients,
            neighbor_coefficients,
            value_coefficients,
            beta,
            terms,
            NativeEnclosurePropagation::ComponentIntervals,
        )
    }
    pub fn new_with_enclosure(
        source: SectionRc<'c>,
        receiver_indices: &[usize],
        source_indices: &[usize],
        query_coefficients: SectionRc<'c>,
        neighbor_coefficients: SectionRc<'c>,
        value_coefficients: SectionRc<'c>,
        beta: Dyadic,
        terms: SeriesAperture,
        enclosure: NativeEnclosurePropagation,
    ) -> Result<Self, NativeSessionError> {
        if source.components() != MACHINE_REALIFIED_COMPONENTS {
            return Err(machine_error(
                "machine participation source must have width 12",
            ));
        }
        if receiver_indices.is_empty()
            || source_indices.is_empty()
            || source_indices.len() % receiver_indices.len() != 0
        {
            return Err(machine_error("machine participation row grouping"));
        }
        let neighbors_per_row = source_indices.len() / receiver_indices.len();
        let decoded = source
            .clone()
            .decode_realification()
            .map_err(machine_error)?;
        if decoded.output().components() != MACHINE_COMPLEX3_COMPONENTS {
            return Err(machine_error(
                "machine participation decode must have width 6",
            ));
        }
        let query_geometry = decoded
            .output_handle()
            .affine_geometry_with_enclosure(
                receiver_indices,
                query_coefficients,
                true,
                enclosure.clone(),
            )
            .map_err(machine_error)?;
        let neighbor_geometry = decoded
            .output_handle()
            .affine_geometry_with_enclosure(
                source_indices,
                neighbor_coefficients,
                true,
                enclosure.clone(),
            )
            .map_err(machine_error)?;
        let value_geometry = decoded
            .output_handle()
            .affine_geometry_with_enclosure(
                source_indices,
                value_coefficients,
                false,
                enclosure.clone(),
            )
            .map_err(machine_error)?;
        let value_realified = value_geometry
            .output_handle()
            .realify()
            .map_err(machine_error)?;
        let participation = query_geometry
            .output_handle()
            .pair_quadrance_participation_with_enclosure(
                neighbor_geometry.output_handle(),
                value_realified.output_handle(),
                neighbors_per_row,
                beta,
                terms,
                enclosure,
            )
            .map_err(machine_error)?;
        Ok(Self {
            decoded,
            query_geometry,
            neighbor_geometry,
            value_geometry,
            value_realified,
            participation,
        })
    }

    pub fn output(&self) -> &Section<'c> {
        self.participation.output()
    }

    #[cfg(test)]
    pub fn values(&self) -> &Section<'c> {
        self.participation.values()
    }

    /// Pull back the complete score-geometry and value return to the original width-12 source.
    /// The query, neighbor, and value branches are individually transposed before their full
    /// source-row sections are joined.
    pub fn pull_back(&self, gy: &Section<'c>) -> Result<Section<'c>, NativeSessionError> {
        if gy.rows() != self.output().rows() || gy.components() != self.output().components() {
            return Err(machine_error("machine participation covector shape"));
        }
        let (query, neighbors, values) = self
            .participation
            .pull_back(gy, None)
            .map_err(machine_error)?
            .into_parts();
        let query = self
            .query_geometry
            .pull_back(&query)
            .map_err(machine_error)?
            .into_source();
        let neighbors = self
            .neighbor_geometry
            .pull_back(&neighbors)
            .map_err(machine_error)?
            .into_source();
        let values = self
            .value_realified
            .pull_back(&values)
            .map_err(machine_error)?
            .into_source();
        let values = self
            .value_geometry
            .pull_back(&values)
            .map_err(machine_error)?
            .into_source();
        let joined = query.sum_same_shape(&neighbors).map_err(machine_error)?;
        let joined = joined.sum_same_shape(&values).map_err(machine_error)?;
        let source = self.decoded.pull_back(&joined).map_err(machine_error)?;
        Ok(source.into_source())
    }
}
