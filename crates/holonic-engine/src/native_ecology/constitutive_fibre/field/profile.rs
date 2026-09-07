//! Borrowed structural profile for the complete constitutive field.
//!
//! This is a receiver over the field owner, not a second ecology and not a basis export.  It
//! reports the complete source and receiving chart extents, the owned material and chronology,
//! and the source/frame fibres already retained by the continuing field.  Apparatus readings are
//! kept in their own census facet; they do not become intrinsic dimensions.

use super::*;
use crate::native_ecology::holonic_intelligence::{
    DimensionFace, DimensionObstruction, IntrinsicHolonDimensions, ReconstructionExtent,
};

/// The exact chart extents of one complete field relation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeConstitutiveFieldExtents {
    /// Two complex source branches per node, represented as real coordinates.
    pub source_extent: usize,
    /// One complex receiving current per node, represented as real coordinates.
    pub target_extent: usize,
    /// The complete paired relation width, including both sides.
    pub relation_extent: usize,
}

/// A borrowed profile of the continuing complete field. All source, frame, material and
/// predecessor data remain owned by `NativeConstitutiveField`; observing this value cannot issue
/// a receiving handle or copy the resident paired basis.
#[derive(Debug)]
pub struct NativeConstitutiveFieldProfile<'a> {
    pub extents: NativeConstitutiveFieldExtents,
    pub dimensions: IntrinsicHolonDimensions,
    pub material: &'a [NativeJunctionSeed],
    pub current_frame: &'a NativeCurrentFrame,
    pub lineages: Vec<&'a NativeFieldLineage>,
    pub source_frames: Vec<&'a NativeCurrentFrame>,
    pub predecessor_states: Vec<Option<usize>>,
    pub recharts: &'a [NativeRechartReceipt],
    pub incidence_changes: &'a [NativeIncidenceChange],
    pub pending_lineage: Option<&'a NativeFieldLineage>,
    pub transfer_census: TransferCensus,
    /// The complete historical source sections remain in the field owner and can be requested
    /// with `inspect_source`; this extent records that reconstruction fibre without materializing
    /// any section or resident relation basis here.
    pub reconstruction_extent: usize,
    pub open_obligations: Vec<crate::native_ecology::holonic_intelligence::OpenObligation<'static>>,
}

impl NativeConstitutiveField<'_> {
    /// Read the field's intrinsic structural profile without a full-basis readback.
    pub fn intrinsic_profile(&self) -> NativeConstitutiveFieldProfile<'_> {
        let nodes = self.nodes();
        let source_extent = nodes.checked_mul(4).expect("validated field source extent");
        let target_extent = nodes.checked_mul(2).expect("validated field target extent");
        let relation_extent = source_extent
            .checked_add(target_extent)
            .expect("validated field relation extent");
        let lineages = (0..self.occurrence_count())
            .filter_map(|occurrence| self.lineage(occurrence))
            .collect::<Vec<_>>();
        let source_frames = (0..self.occurrence_count())
            .filter_map(|occurrence| self.source_frame(occurrence))
            .collect::<Vec<_>>();
        let predecessor_states = lineages
            .iter()
            .map(|lineage| lineage.predecessor_state)
            .collect::<Vec<_>>();
        NativeConstitutiveFieldProfile {
            extents: NativeConstitutiveFieldExtents {
                source_extent,
                target_extent,
                relation_extent,
            },
            dimensions: field_dimensions(nodes, source_extent, target_extent, lineages.len()),
            material: self.material(),
            current_frame: self.current_frame(),
            lineages,
            source_frames,
            predecessor_states,
            recharts: self.recharts(),
            incidence_changes: self.incidence_changes(),
            pending_lineage: self.pending_lineage(),
            transfer_census: self.census(),
            reconstruction_extent: self.occurrence_count(),
            open_obligations: vec![
                crate::native_ecology::holonic_intelligence::OpenObligation {
                    scope: crate::native_ecology::holonic_intelligence::OpenScope::Thread,
                    testimony: "scale chart is outside the native constitutive field profile",
                },
                crate::native_ecology::holonic_intelligence::OpenObligation {
                    scope: crate::native_ecology::holonic_intelligence::OpenScope::Thread,
                    testimony: "apparatus work is reported by TransferCensus, not intrinsic field dimensions",
                },
            ],
        }
    }
}

fn field_dimensions(
    _nodes: usize,
    _source_extent: usize,
    _target_extent: usize,
    reconstruction_extent: usize,
) -> IntrinsicHolonDimensions {
    IntrinsicHolonDimensions {
        // The field exposes complete chart extents above, but does not yet found the native
        // incidence/carrier/generator facets needed to assign these dimensions.
        topological_degree: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        incidence_rank: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        incidence_nullity: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        cycle_rank: DimensionFace::Open(DimensionObstruction::NotExposedByConstitutiveFieldProfile),
        carrier_rank: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        exterior_degree: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        representation_rank: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        generator_extent: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        receiver_extent: DimensionFace::Open(
            DimensionObstruction::NotExposedByConstitutiveFieldProfile,
        ),
        reconstruction_extent: DimensionFace::Exact(ReconstructionExtent(reconstruction_extent)),
        scale_extent: DimensionFace::Open(DimensionObstruction::ScaleChartOutsideNativeThread),
        apparatus_work: DimensionFace::Open(DimensionObstruction::ApparatusWorkOutsideNativeRest),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_dimensions_keep_chart_extents_separate_from_unfounded_ranks() {
        let dimensions = field_dimensions(2, 8, 4, 3);
        assert!(matches!(
            dimensions.carrier_rank,
            DimensionFace::Open(DimensionObstruction::NotExposedByConstitutiveFieldProfile)
        ));
        assert!(matches!(
            dimensions.generator_extent,
            DimensionFace::Open(DimensionObstruction::NotExposedByConstitutiveFieldProfile)
        ));
        assert!(matches!(
            dimensions.receiver_extent,
            DimensionFace::Open(DimensionObstruction::NotExposedByConstitutiveFieldProfile)
        ));
        assert_eq!(
            dimensions.reconstruction_extent,
            DimensionFace::Exact(ReconstructionExtent(3))
        );
    }
}
