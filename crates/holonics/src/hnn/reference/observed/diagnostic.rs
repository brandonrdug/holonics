//! A detached receiving-map intervention at an actual kept native read.
//! No source, clock, tree, population, current, chart, carry or constitution is changed.

use super::*;
use crate::compression::landmark::context::LandmarkFace;
use crate::hnn::constitution::ReceivingLayout;
use crate::hnn::receiving::cells::ScoredFaceReading;
use crate::hnn::receiving::cells::diagnostic::{ReadoutMapDiagnostic, compare_readout_maps_at};
use crate::hnn::receiving::ReceivingCarrier;

/// Exterior provenance and both operative R reads from one pending aperture-one word. The
/// control is a readout substitution on fixed features, never a replacement live constitution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingReadoutDiagnostic {
    pub pending: PendingId,
    pub material_commit: u64,
    pub source_cells: u64,
    pub anchor: Vec<BigInt>,
    pub phases: ReceivingPhases,
    pub tree: LandmarkFace,
    pub scored_face: ScoredFaceReading,
    pub native_map: ExactRatMatrix,
    pub control_map: ExactRatMatrix,
    pub readout: ReadoutMapDiagnostic,
}

impl Reference {
    /// Compare the native and a declared control R on the *same actual kept-word feature*.
    /// This aperture-one Physical/Anchor diagnostic freezes the tree and the population before
    /// any target/release reception. Other layouts and a missing/stale kept read refuse. The
    /// caller may use the founding R as its control; E and all retained moments remain native.
    pub fn diagnose_pending_readout(
        &self,
        resident: &Resident,
        pending: &PendingId,
        control_map: &ExactRatMatrix,
        bits: u32,
    ) -> Result<PendingReadoutDiagnostic, HnnError> {
        resident.admit_exact_current()?;
        let slot = resident.pending.get(pending).ok_or(HnnError::UnknownHandle {
            handle: Handle::Pending(*pending),
        })?;
        let phases = slot.ratio.phases();
        let ring = phases.ring();
        let theta = &resident.constitution;
        if phases.aperture() != 1
            || theta.receiving_layout(ring) != Some(ReceivingLayout::Single)
            || ConstitutionRead::receiving_carrier(theta, ring) != ReceivingCarrier::Anchor
        {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control requires one physical anchor read",
            });
        }
        let kept = slot.kept.as_ref().ok_or(HnnError::Unadmitted {
            reason: "a pending readout control requires its actual kept native word",
        })?;
        if kept.commit != theta.commit() || slot.ratio.commit() != theta.commit() {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control refuses a changed producing constitution",
            });
        }
        let features = resident.receiving_inputs(pending, phases)?.ok_or(HnnError::Unadmitted {
            reason: "a pending readout control has no producing receiving feature",
        })?;
        let [feature] = features.as_slice() else {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control preserves one complete producing feature",
            });
        };
        let native_read = phases.read(&resident.field, theta, feature)?;
        if kept.faces.logits.as_slice() != [native_read.logits.clone()]
            || kept.faces.faces.as_slice() != [crate::hnn::ratio::Face::of_read(&native_read, phases.grain())?]
        {
            return Err(HnnError::Unadmitted {
                reason: "a pending readout control reconstructs its exact kept native read",
            });
        }
        // No known response target enters this address. This is the actual query's first face.
        let against = slot.ratio.against(theta, &kept.faces, &[])?;
        let tree = against.trees.first().ok_or(HnnError::Unadmitted {
            reason: "a pending readout control keeps its producing tree face",
        })?;
        let population = ConstitutionRead::population(theta, ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        let scored_face = ScoredFaceReading {
            population: population.clone(),
            tree_probabilities: tree.probabilities.clone(),
            combined: against.faces.faces[0].clone(),
        };
        let native_map = ConstitutionRead::receiving_map(theta, ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?;
        let readout = compare_readout_maps_at(
            &scored_face, tree, feature, native_map, &native_read.logits, control_map, bits,
        )?;
        Ok(PendingReadoutDiagnostic {
            pending: *pending,
            material_commit: theta.commit(),
            source_cells: slot.ratio.moment().cells(),
            anchor: slot.ratio.anchor().to_vec(),
            phases: phases.clone(),
            tree: tree.clone(),
            scored_face,
            native_map: native_map.clone(),
            control_map: control_map.clone(),
            readout,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::tests::support::{contact, encoded, small_field_of};
    use crate::ratio::exponentiated::READING_BITS;

    #[test]
    fn pending_readout_control_consumes_the_actual_kept_word_without_teaching() {
        let base = small_field_of(
            &[5, 2, 3], vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)], 2, 4,
        );
        let mut declaration = base.declaration().clone();
        declaration.receivers[0].aperture = 1;
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let material = Constitution::initial(&field, 1 << 40).unwrap();
        let phases = field.receivers().first().unwrap();
        let map = material.receiving_law(phases.ring).unwrap().map().clone();
        let reference = Reference::new(16, 1 << 40);
        let mut resident = reference.mount_with(&field, &Current::at_rest(&field), material).unwrap();
        let (moment, _) = reference.ingest(&mut resident, None, &encoded(&field, &[0, 1, 2])).unwrap();
        let phases = resident.admitted[0].clone();
        let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
        // A live kept comparison is intentionally not checkpointable. Compare the complete
        // actual resident, including its kept word, without crossing that checkpoint guard.
        let before = format!("{resident:?}");
        let diagnostic = reference.diagnose_pending_readout(&resident, &pending, &map, READING_BITS).unwrap();
        assert_eq!(diagnostic.readout.native, diagnostic.readout.control);
        assert_eq!(diagnostic.readout.native_wave_logits,
            resident.pending[&pending].kept.as_ref().unwrap().faces.logits[0]);
        assert_eq!(diagnostic.source_cells, 3);
        assert_eq!(format!("{resident:?}"), before);
        assert!(resident.holds_kept_read(&pending));
        let malformed = ExactRatMatrix::new(vec![vec![integer(0)]]).unwrap();
        assert!(reference.diagnose_pending_readout(&resident, &pending, &malformed, READING_BITS).is_err());
        assert_eq!(format!("{resident:?}"), before);
        resident.pending.get_mut(&pending).unwrap().kept.as_mut().unwrap().faces.logits[0][0] += integer(1);
        let corrupt = format!("{resident:?}");
        assert!(reference.diagnose_pending_readout(&resident, &pending, &map, READING_BITS).is_err());
        assert_eq!(format!("{resident:?}"), corrupt);
    }
}
