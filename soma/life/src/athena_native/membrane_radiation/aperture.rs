//! Owner-local radiation seam: aperture and sections.

use super::super::{
    AffineLaboratoryCultivatedAthenaRest, AthenaMembraneCrossingReceipt,
    ReturnedAffineLaboratoryAthenaRest,
};
use super::*;
use crate::relational_language::{
    realize_relational_clauses, relational_question_phase_words, relational_question_regions,
};
use holonic_engine::cuda_refine::ResidentMembraneInteriorReturn;
use std::collections::BTreeSet;
impl NativeRadiationAperture {
    /// Radiate from the sole resident factored image. Boundary restrictions become addressed
    /// receiver complexes, their contraction and the complete phase chain remain on the card,
    /// and only the returned image address plus terminal boundary testimony cross back.
    pub fn found(rest: &ReturnedAffineLaboratoryAthenaRest) -> Result<Self, NativeRadiationError> {
        rest.validate()
            .map_err(|error| NativeRadiationError::Standing(error.to_string()))?;
        let potential = rest.relational_potential();
        let seeds = potential
            .addressed_participant_subject_faces()
            .map_err(|error| NativeRadiationError::Standing(error.to_string()))?;
        let (closure, _) = potential
            .participant_closure(&seeds)
            .map_err(|error| NativeRadiationError::Standing(error.to_string()))?;
        let relational_cell_indices = potential
            .cells
            .iter()
            .enumerate()
            .filter_map(|(at, cell)| {
                (closure.contains(&cell.subject) || closure.contains(&cell.object)).then_some(at)
            })
            .collect::<Vec<_>>();
        if relational_cell_indices.is_empty() {
            return Err(NativeRadiationError::Aperture(
                "the addressed receiver port has no incident relational 2-cell".to_owned(),
            ));
        }
        let relational_cell_addresses = relational_cell_indices
            .iter()
            .map(|at| potential.cells[*at].address.clone())
            .collect::<Vec<_>>();
        let relational_cell_boundaries = relational_cell_indices
            .iter()
            .map(|at| {
                let cell = &potential.cells[*at];
                let mut boundary = vec![cell.subject, cell.relation, cell.object];
                boundary.extend(cell.modality);
                boundary.sort_unstable();
                boundary.dedup();
                boundary
            })
            .collect::<Vec<_>>();
        let (left_contact_cell, right_contact_cell) = first_founded_contact(rest)?;
        let receiver_port_faces = closure.into_iter().collect::<Vec<_>>();
        let participant_receiver_charts =
            derive_participant_receiver_charts(rest.relational_codec(), potential, &seeds)?;
        let relation_receiver_charts =
            derive_relation_receiver_charts(rest.relational_codec(), potential)?;
        let identity_sha256 = digest(&(
            NATIVE_RADIATION_SCHEMA,
            rest.identity(),
            &receiver_port_faces,
            &participant_receiver_charts,
            &relation_receiver_charts,
            &relational_cell_indices,
            &relational_cell_addresses,
            &relational_cell_boundaries,
            &left_contact_cell,
            &right_contact_cell,
        ))?;
        Ok(Self {
            schema: NATIVE_RADIATION_SCHEMA.to_owned(),
            rested_identity_sha256: rest.identity().to_owned(),
            receiver_port_faces,
            participant_receiver_charts,
            relation_receiver_charts,
            relational_cell_indices,
            relational_cell_addresses,
            relational_cell_boundaries,
            left_contact_cell,
            right_contact_cell,
            target_query_was_visible_when_frozen: false,
            deed_or_semantic_mode_supplied: false,
            identity_sha256,
        })
    }

    pub fn found_predecessor(
        rest: &AffineLaboratoryCultivatedAthenaRest,
    ) -> Result<Self, NativeRadiationError> {
        rest.validate()
            .map_err(|error| NativeRadiationError::Standing(error.to_string()))?;
        found_aperture(
            rest.identity(),
            rest.relational_potential(),
            rest.relational_codec(),
            rest.affine_cells(),
        )
    }
}

/// The notation-free exterior quantity chart shared by every membrane mouth.  This calculation
/// sees only caused octet incidence and order.  It deliberately precedes and does not invoke the
/// optional relational receiver codec used by [`ExteriorActionCurrent`].
pub(super) fn exterior_boundary_current(
    payload: &[u8],
) -> Result<(ExactComplexWaveCurrent, ExactComplexWaveCurrent), NativeRadiationError> {
    if payload.is_empty() {
        return Err(NativeRadiationError::Exterior);
    }
    let population = u64::try_from(payload.len()).map_err(|_| NativeRadiationError::Extent)?;
    let mass = payload
        .iter()
        .fold(BigInt::from(0), |sum, octet| sum + BigInt::from(*octet));
    let oriented_change = payload.windows(2).fold(BigInt::from(0), |sum, pair| {
        sum + BigInt::from(pair[1]) - BigInt::from(pair[0])
    });
    let magnitude = Rat::new(mass.clone(), BigInt::from(population));
    let mut action = BigInt::from(0);
    let mut prior = 0i64;
    for (at, octet) in payload.iter().copied().enumerate() {
        let position = i64::try_from(at)
            .map_err(|_| NativeRadiationError::Extent)?
            .checked_add(1)
            .ok_or(NativeRadiationError::Extent)?;
        let difference = i64::from(octet) - prior;
        prior = i64::from(octet);
        action += BigInt::from(position) * BigInt::from(difference);
    }
    let action_square = &action * &action;
    let phase_denominator = BigInt::from(1) + &action_square;
    let phase = ExactComplexWaveCurrent::new(
        Rat::new(BigInt::from(1) - action_square, phase_denominator.clone()),
        Rat::new(BigInt::from(2) * action.clone(), phase_denominator),
    );
    let current = phase.scaled(&magnitude);
    let section = ExactComplexWaveCurrent::new(
        Rat::from_integer(mass),
        Rat::from_integer(action + oriented_change),
    );
    Ok((section, current))
}

impl ExteriorActionCurrent {
    pub fn transduce(
        occurrence: impl Into<String>,
        payload: &[u8],
    ) -> Result<Self, NativeRadiationError> {
        let occurrence = occurrence.into();
        if occurrence.is_empty() || payload.is_empty() {
            return Err(NativeRadiationError::Exterior);
        }
        let population = u64::try_from(payload.len()).map_err(|_| NativeRadiationError::Extent)?;
        let (section, current) = exterior_boundary_current(payload)?;
        let surface = std::str::from_utf8(payload).ok();
        let mut receiver_regions = surface
            .map(relational_question_regions)
            .unwrap_or_default()
            .into_iter()
            .map(|region| region.into_iter().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        receiver_regions.sort();
        receiver_regions.dedup();
        let relation_phase_words = surface
            .map(relational_question_phase_words)
            .unwrap_or_default();
        let causal_relation_phase_octets = relation_phase_words
            .iter()
            .map(|phase| phase.as_bytes().to_vec())
            .collect();
        Ok(Self {
            occurrence: occurrence.clone(),
            caused_octet_population: population,
            section,
            current,
            source_sha256: hex_sha256(payload),
            source_components: vec![ExteriorSourceComponent {
                occurrence: occurrence.clone(),
                caused_octet_population: population,
                source_sha256: hex_sha256(payload),
            }],
            causal_octets: payload.to_vec(),
            causal_relation_phase_octets,
            receiver_regions,
            relation_phase_words,
            boundary_codec_applied: surface.is_some(),
            native_tokenization_performed: false,
            semantic_classification_performed: false,
        })
    }

    /// Compose an earlier returned exterior occurrence with this later receiver-bearing current.
    /// The exact length-prefixed payload preserves both source fibres and their order.  Receiver
    /// coordinates remain those of the later occurrence; the earlier surface changes the physical
    /// action current but cannot silently widen or replace the declared receiver aperture.
    pub fn after_returned(
        self,
        predecessor_occurrence: impl Into<String>,
        predecessor_payload: &[u8],
    ) -> Result<Self, NativeRadiationError> {
        let predecessor = Self::transduce(predecessor_occurrence, predecessor_payload)?;
        let predecessor_extent = u64::try_from(predecessor.causal_octets.len())
            .map_err(|_| NativeRadiationError::Extent)?;
        let successor_extent =
            u64::try_from(self.causal_octets.len()).map_err(|_| NativeRadiationError::Extent)?;
        let mut payload = Vec::with_capacity(
            16usize
                .checked_add(predecessor.causal_octets.len())
                .and_then(|extent| extent.checked_add(self.causal_octets.len()))
                .ok_or(NativeRadiationError::Extent)?,
        );
        payload.extend_from_slice(&predecessor_extent.to_be_bytes());
        payload.extend_from_slice(&predecessor.causal_octets);
        payload.extend_from_slice(&successor_extent.to_be_bytes());
        payload.extend_from_slice(&self.causal_octets);
        let mut composed = Self::transduce(self.occurrence.clone(), &payload)?;
        composed.receiver_regions = self.receiver_regions;
        composed.relation_phase_words = predecessor
            .relation_phase_words
            .into_iter()
            .chain(self.relation_phase_words)
            .collect();
        composed.relation_phase_words.sort();
        composed.relation_phase_words.dedup();
        composed.causal_relation_phase_octets = predecessor
            .causal_relation_phase_octets
            .into_iter()
            .chain(self.causal_relation_phase_octets)
            .collect();
        composed.source_components = predecessor
            .source_components
            .into_iter()
            .chain(self.source_components)
            .collect();
        composed.boundary_codec_applied =
            predecessor.boundary_codec_applied && self.boundary_codec_applied;
        Ok(composed)
    }

    pub fn exact_source_payload(&self) -> &[u8] {
        &self.causal_octets
    }
}

impl NativeRadiationSection {
    pub fn found(
        rest: &impl super::super::AthenaMembraneStanding,
        aperture: &NativeRadiationAperture,
        exterior: &ExteriorActionCurrent,
        crossing: &AthenaMembraneCrossingReceipt,
        resident: ResidentMembraneInteriorReturn,
    ) -> Result<Self, NativeRadiationError> {
        Self::found_from_returned(rest, aperture, exterior, crossing, resident, None)
    }

    pub fn found_after_returned(
        rest: &impl super::super::AthenaMembraneStanding,
        aperture: &NativeRadiationAperture,
        exterior: &ExteriorActionCurrent,
        crossing: &AthenaMembraneCrossingReceipt,
        resident: ResidentMembraneInteriorReturn,
        predecessor: &NativeRadiationSection,
    ) -> Result<Self, NativeRadiationError> {
        if predecessor.rested_identity_sha256 != aperture.rested_identity_sha256
            || predecessor.aperture_identity_sha256 != aperture.identity_sha256
            || predecessor.emitted_relational_cell_addresses.is_empty()
        {
            return Err(NativeRadiationError::RadiationDetail(
                "the proposed refinement predecessor escaped the rested aperture".to_owned(),
            ));
        }
        Self::found_from_returned(
            rest,
            aperture,
            exterior,
            crossing,
            resident,
            Some(predecessor),
        )
    }

    fn found_from_returned(
        rest: &impl super::super::AthenaMembraneStanding,
        aperture: &NativeRadiationAperture,
        exterior: &ExteriorActionCurrent,
        crossing: &AthenaMembraneCrossingReceipt,
        resident: ResidentMembraneInteriorReturn,
        predecessor: Option<&NativeRadiationSection>,
    ) -> Result<Self, NativeRadiationError> {
        if aperture.schema != NATIVE_RADIATION_SCHEMA
            || crossing.rested_identity_sha256 != aperture.rested_identity_sha256
            || crossing.exterior_occurrence != exterior.occurrence
            || resident.injected_boundary_current != exterior.current
            || resident.returned_radiation != resident.native_radiation.multiply(&exterior.current)
            || !resident.boundary_injection_depended_on_native_radiation
            || resident.invariant_transport_reuploaded
            || resident.cpu_semantic_replay_after_device
            || resident.cell_selected_or_ranked
        {
            return Err(NativeRadiationError::Radiation);
        }
        let (
            receiver_chart,
            relation_receiver_chart_identities_sha256,
            unresolved_relation_phase_words,
            relational_cell_radiation,
            emitted_relational_cell_addresses,
            retained_relational_cell_fibre,
        ) = emitted_relational_front(rest, aperture, exterior, &resident, predecessor)?;
        let predecessor_radiation_identity_sha256 =
            predecessor.map(|section| section.identity_sha256.clone());
        let carried_relational_cell_addresses = predecessor
            .map(|section| section.emitted_relational_cell_addresses.clone())
            .unwrap_or_default();
        let relational_cell_radiation_identity_sha256 = digest(&relational_cell_radiation)?;
        let relational_cell_radiation_population = u32::try_from(relational_cell_radiation.len())
            .map_err(|_| NativeRadiationError::Extent)?;
        let mut section = Self {
            schema: NATIVE_RADIATION_SCHEMA.to_owned(),
            aperture_identity_sha256: aperture.identity_sha256.clone(),
            rested_identity_sha256: aperture.rested_identity_sha256.clone(),
            exterior_occurrence: exterior.occurrence.clone(),
            exterior_source_sha256: exterior.source_sha256.clone(),
            predecessor_radiation_identity_sha256,
            carried_relational_cell_addresses,
            native_ordered_word: crossing.native_ordered_word.clone(),
            family_overlaps: resident.family_overlaps,
            native_radiation: resident.native_radiation,
            injected_boundary_current: resident.injected_boundary_current,
            returned_radiation: resident.returned_radiation,
            participant_receiver_chart_identity_sha256: receiver_chart.identity_sha256.clone(),
            participant_alias: receiver_chart.participant_alias,
            relation_receiver_chart_identities_sha256,
            unresolved_relation_phase_words,
            relational_cell_radiation_identity_sha256,
            relational_cell_radiation_population,
            relational_cell_radiation,
            emitted_relational_cell_addresses,
            retained_relational_cell_fibre,
            renderer_has_not_run: true,
            identity_sha256: String::new(),
        };
        let lineage_identity_sha256 = digest(&(
            &section.schema,
            &section.aperture_identity_sha256,
            &section.rested_identity_sha256,
            &section.exterior_occurrence,
            &section.exterior_source_sha256,
            &section.predecessor_radiation_identity_sha256,
            &section.carried_relational_cell_addresses,
            &section.native_ordered_word,
        ))?;
        section.identity_sha256 = digest(&(
            lineage_identity_sha256,
            &section.family_overlaps,
            &section.native_radiation,
            &section.injected_boundary_current,
            &section.returned_radiation,
            &section.participant_receiver_chart_identity_sha256,
            &section.participant_alias,
            &section.relation_receiver_chart_identities_sha256,
            &section.unresolved_relation_phase_words,
            &section.relational_cell_radiation_identity_sha256,
            &section.relational_cell_radiation_population,
            &section.emitted_relational_cell_addresses,
            &section.retained_relational_cell_fibre,
        ))?;
        Ok(section)
    }

    /// Project the already-returned native section through the cold relational codec.  Every
    /// cell in the predeclared fibre is rendered exactly once; no search, score, candidate rank,
    /// stored sentence, or expected surface is available here.
    pub fn render(
        mut self,
        rest: &ReturnedAffineLaboratoryAthenaRest,
        aperture: &NativeRadiationAperture,
    ) -> Result<ExteriorRadiationSurface, NativeRadiationError> {
        if rest.identity() != self.rested_identity_sha256
            || aperture.identity_sha256 != self.aperture_identity_sha256
            || !self
                .emitted_relational_cell_addresses
                .iter()
                .all(|address| aperture.relational_cell_addresses.contains(address))
            || self
                .retained_relational_cell_fibre
                .iter()
                .any(|address| self.emitted_relational_cell_addresses.contains(address))
        {
            return Err(NativeRadiationError::Aperture(
                "the renderer was offered a different rested receiver fibre".to_owned(),
            ));
        }
        let potential = rest.relational_potential();
        let codec = rest.relational_codec();
        let emitted = self
            .emitted_relational_cell_addresses
            .iter()
            .collect::<BTreeSet<_>>();
        let mut clauses = aperture
            .relational_cell_indices
            .iter()
            .filter(|at| emitted.contains(&potential.cells[**at].address))
            .map(|at| {
                codec
                    .clause(
                        potential,
                        &potential.cells[*at],
                        Some(self.participant_alias),
                    )
                    .map_err(|error| NativeRadiationError::Render(error.to_string()))
            })
            .collect::<Result<Vec<_>, _>>()?;
        clauses.sort_by_key(|clause| (clause.source_order, clause.identity.clone()));
        let realized = realize_relational_clauses(&clauses, &[], false)
            .map_err(|error| NativeRadiationError::Render(format!("{error:?}")))?;
        let text = realized.text;
        self.renderer_has_not_run = false;
        Ok(ExteriorRadiationSurface {
            radiation_identity_sha256: self.identity_sha256.clone(),
            exterior_occurrence: self.exterior_occurrence,
            text_sha256: hex_sha256(text.as_bytes()),
            text,
            rendered_cell_addresses: self.emitted_relational_cell_addresses,
            candidate_search_performed: false,
            stored_sentence_selected: false,
            expected_answer_consulted: false,
        })
    }
}
