//! Addressed occurrence binding recovered from the standing membrane ecology.

use super::super::InteriorContactConsequence;
use super::*;
use holonic_engine::receiver_exact_compression::ReceiverId;

impl<Standing: AthenaMembraneStanding> AthenaCausalMembrane<Standing> {
    pub fn founded_interior_contact(
        &self,
        left_cell: &str,
        right_cell: &str,
    ) -> Result<InteriorContactConsequence, MembraneInteriorError> {
        let interior = self
            .interior
            .as_ref()
            .ok_or(MembraneInteriorError::InteriorAbsent)?;
        interior.contact(&self.rest, left_cell, right_cell)
    }

    /// Found one addressed membrane contact from the standing ecology itself. The caller names a
    /// native address and dependent receiver, but cannot supply or alter its current, incidence,
    /// response, chronology, or reconstruction fibre.
    pub fn bind_occurrence(
        &self,
        exterior: ExteriorOccurrenceFibre,
        exterior_boundary: BoundaryId,
        native_address: &NativeSectionAddress,
        receiver: ReceiverId,
        chart: ExactMembraneChartPassage,
        open_exterior: Vec<String>,
    ) -> Result<AthenaMembraneOccurrence, NativeMembraneBindingInsufficiency> {
        let native = match derive_native_section(&self.rest, native_address, receiver) {
            Ok(native) => native,
            Err(defect) => {
                return Err(NativeMembraneBindingInsufficiency {
                    defect,
                    exterior,
                    chart,
                });
            }
        };
        let exterior_port = OccurrencePort::output(exterior.address().event_projection, 0);
        Ok(AthenaMembraneOccurrence {
            exterior,
            exterior_boundary,
            exterior_port,
            rested_identity_sha256: self.rest.membrane_identity().to_owned(),
            native,
            chart,
            open_exterior,
        })
    }
}

fn derive_native_section(
    rest: &impl AthenaMembraneStanding,
    address: &NativeSectionAddress,
    receiver: ReceiverId,
) -> Result<NativeConductedSection, NativeMembraneDefect> {
    if !rest.membrane_realization().sections.contains(address) {
        return Err(NativeMembraneDefect::NativeSectionOutsideEcology);
    }
    let admitted = native_contact_view(rest, address)
        .ok_or(NativeMembraneDefect::NativeSectionOutsideEcology)?;
    let occurrence = admitted.occurrence;
    let spool = admitted.spool;
    let thread = admitted.thread;
    if !spool.receiver_family.contains(&receiver) {
        return Err(NativeMembraneDefect::ReceiverOutsideEcology);
    }
    let constitutive_response = thread
        .constitutive_responses
        .iter()
        .find(|response| {
            response.native == occurrence.emitting_native && response.receiver == receiver
        })
        .cloned()
        .ok_or(NativeMembraneDefect::ReceiverOutsideEcology)?;
    let observation = thread
        .receiver_consequences
        .iter()
        .find(|consequence| {
            consequence.native == occurrence.emitting_native && consequence.receiver == receiver
        })
        .map(|consequence| consequence.observation)
        .ok_or(NativeMembraneDefect::ReceiverOutsideEcology)?;
    let mut mutual_constitutive_responses = spool
        .mutual_constitutive_responses
        .iter()
        .filter(|response| {
            response.left_occurrence == occurrence.occurrence
                || response.right_occurrence == occurrence.occurrence
        })
        .cloned()
        .collect::<Vec<_>>();
    mutual_constitutive_responses
        .sort_by_key(|response| (response.left_occurrence, response.right_occurrence));
    let mut successor_sections = rest
        .membrane_realization()
        .sections
        .iter()
        .filter_map(|candidate_address| {
            let candidate = native_contact_view(rest, candidate_address)?;
            (candidate.occurrence.predecessor == Some(occurrence.occurrence))
                .then_some(candidate_address.clone())
        })
        .collect::<Vec<_>>();
    successor_sections.sort();
    let mut open_exterior = thread.open_exterior.clone();
    open_exterior.extend(rest.membrane_realization().open_exterior.iter().cloned());
    open_exterior.sort();
    open_exterior.dedup();
    Ok(NativeConductedSection {
        address: address.clone(),
        predecessor: occurrence.predecessor,
        entering_boundary: thread.entering_boundary,
        emitting_boundary: thread.emitting_boundary,
        entering_port: occurrence.entering_port,
        emitting_port: occurrence.emitting_port,
        entering_native: occurrence.entering_native,
        emitting_native: occurrence.emitting_native,
        incidence: admitted.incidence.clone(),
        entering_section: admitted.entering_parametron.section.clone(),
        entering_current: admitted.entering_parametron.current.clone(),
        emitting_section: admitted.emitting_parametron.section.clone(),
        emitting_current: admitted.emitting_parametron.current.clone(),
        relative_phase: admitted.emitting_parametron.relative_phase.clone(),
        hand: admitted.emitting_parametron.hand,
        constitutive_response,
        mutual_constitutive_responses,
        ordered_word: admitted.thread.chronology.clone(),
        receiver,
        observation,
        reconstruction_fibre: admitted.reconstruction_fibre.occurrences.clone(),
        successor_sections,
        open_exterior,
    })
}
