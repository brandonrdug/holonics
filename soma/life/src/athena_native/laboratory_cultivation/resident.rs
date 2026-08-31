impl ResidentAffineLaboratoryAthena {
    pub fn emanate_participant(
        &mut self,
        ingress: LaboratoryParticipantIngress,
    ) -> Result<LaboratoryParticipantEmanation, LaboratoryCultivationError> {
        let deed = match ingress.deed {
            EmanationDeed::Describe => 0,
            EmanationDeed::Identify => 1,
            EmanationDeed::Infer => 2,
            _ => {
                return Err(LaboratoryCultivationError::Correspondence(
                    "this receiver admits describe, identify, and infer deeds".to_owned(),
                ));
            }
        };
        let apparatus = self
            .resident
            .conduct_participant(deed)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        project_participant_emanation(
            &self.identity_sha256,
            &self.potential,
            &self.codec,
            &self.affine_cells,
            &self.participant_faces,
            ingress,
            apparatus,
        )
    }

    /// Return the coupled L2 current under the identity of the one mounted affine body. The
    /// participant and material fields remain resident beside that current; no predecessor body
    /// is reopened or copied.
    pub fn conduct_material(
        &mut self,
        factorization: &mut MaterialNativeFactorization,
    ) -> Result<SituatedCultivatedConductReturn, LaboratoryCultivationError> {
        if factorization.predecessor_rest_identity_sha256 != self.identity_sha256 {
            return Err(LaboratoryCultivationError::Correspondence(
                "the material section addresses a different cultivated affine rest".to_owned(),
            ));
        }
        let transport = factorization
            .cultivated_affine_transport
            .as_mut()
            .ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(
                    "the cultivated material section has no affine transport field".to_owned(),
                )
            })?;
        if transport.standing_rest_identity_sha256 != self.identity_sha256
            || transport.resident_apparatus.is_some()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the affine transport testimony is stale or already conducted".to_owned(),
            ));
        }
        let integrated = self
            .resident
            .conduct(
                &vec![true; self.factors.len()],
                &transport.entering_section,
                0,
            )
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        if !integrated.one_underlying_context
            || integrated.launches != 3
            || integrated.synchronizations != 1
            || integrated.intermediate_host_egress_octets != 0
            || integrated.coupled.synchronizations != 0
            || integrated.affine.synchronizations != 0
            || integrated.participant.synchronizations != 0
            || integrated.invariant_transport_reuploaded
            || integrated.cpu_semantic_replay_after_device
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the three resident fronts did not return as one card-owned word".to_owned(),
            ));
        }
        let integrated_resident_apparatus = MaterialIntegratedResidentApparatusReceipt {
            schema: "soma-life.material-integrated-resident-apparatus.v1".to_owned(),
            device: integrated.coupled.device.clone(),
            context_identity: integrated.context_identity,
            one_underlying_context: integrated.one_underlying_context,
            launches: integrated.launches,
            synchronizations: integrated.synchronizations,
            successor_host_ingress_octets: integrated.successor_host_ingress_octets,
            successor_host_egress_octets: integrated.successor_host_egress_octets,
            intermediate_host_egress_octets: integrated.intermediate_host_egress_octets,
            resident_invariant_octets: integrated.resident_invariant_octets,
            invariant_transport_reuploaded: integrated.invariant_transport_reuploaded,
            cpu_semantic_replay_after_device: integrated.cpu_semantic_replay_after_device,
        };
        let affine_return = integrated.affine;
        if affine_return.addressed_cell_population != transport.addressed_cell_population
            || affine_return.local_fibre_term_population != transport.local_fibre_term_population
            || affine_return.exact_reconstruction_cell_population
                != transport.addressed_cell_population
            || affine_return.invariant_transport_reuploaded
            || affine_return.cpu_semantic_replay_after_device
            || affine_return.cell_selected_or_ranked
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the resident affine field diverged from its exact cold reconstruction".to_owned(),
            ));
        }
        transport.resident_apparatus = Some(affine_return);
        transport.integrated_resident_apparatus = Some(integrated_resident_apparatus);
        if integrated.coupled.sections != self.expected
            || integrated.coupled.sections.len() != self.factors.len()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the integrated resident word diverged from the one affine Athena body".to_owned(),
            ));
        }
        let factors = self
            .factors
            .iter()
            .zip(&integrated.coupled.sections)
            .map(|((address, incident_threads), current)| {
                super::SituatedCultivatedConductedFactor {
                    address: address.clone(),
                    incident_threads: incident_threads.clone(),
                    current: current.clone(),
                }
            })
            .collect();
        Ok(SituatedCultivatedConductReturn {
            rest_identity_sha256: self.identity_sha256.clone(),
            factors,
            apparatus: integrated.coupled,
        })
    }

    pub fn into_rest(
        self,
    ) -> Result<AffineLaboratoryCultivatedAthenaRest, LaboratoryCultivationError> {
        let rest = AffineLaboratoryCultivatedAthenaRest {
            schema: self.schema,
            predecessor_rest_identity_sha256: self.predecessor_rest_identity_sha256,
            body: self.body,
            potential: self.potential,
            codec: self.codec,
            correspondences: self.correspondences,
            affine_cells: self.affine_cells,
            identity_sha256: self.identity_sha256,
        };
        rest.validate()?;
        Ok(rest)
    }
}

/// Project one already returned resident participant section through the cold relational codec.
///
/// This is shared by the original affine mount and the complete optical/acoustic product mount.
/// It never conducts a second body and never selects native cells from the exterior proper name.
pub(super) fn project_participant_emanation(
    rest_identity_sha256: &str,
    potential: &NativeRelationalPotentialComplex,
    codec: &NativeRelationalCodec,
    affine_cells: &[LaboratoryCellAffineSection],
    participant_faces: &BTreeSet<u32>,
    ingress: LaboratoryParticipantIngress,
    apparatus: ResidentParticipantCausalFrontReturn,
) -> Result<LaboratoryParticipantEmanation, LaboratoryCultivationError> {
    if apparatus.selected_population == 0
        || apparatus.selected.len() != potential.cells.len()
        || affine_cells.len() != potential.cells.len()
    {
        return Err(LaboratoryCultivationError::Correspondence(
            "the participant causal front returned no complete native section".to_owned(),
        ));
    }
    let mut selected = apparatus
        .selected
        .iter()
        .enumerate()
        .filter_map(|(at, selected)| (*selected != 0).then_some(at))
        .collect::<Vec<_>>();
    selected.sort_by_key(|at| {
        (
            potential.cells[*at].last_delivery_order().unwrap_or(0),
            potential.cells[*at].address.clone(),
        )
    });
    let perspective_surface =
        if ingress.perspective.speaker.as_deref() == Some(&ingress.participant.identity) {
            "I".to_owned()
        } else if ingress.perspective.addressee.as_deref() == Some(&ingress.participant.identity) {
            "you".to_owned()
        } else {
            ingress.participant.proper_name.clone()
        };
    let mut clauses = Vec::<RelationalClause>::with_capacity(selected.len());
    let mut selected_cell_addresses = Vec::with_capacity(selected.len());
    let mut selected_affine_sections = Vec::with_capacity(selected.len());
    for at in &selected {
        let cell = &potential.cells[*at];
        let mut clause = codec
            .clause(potential, cell, None)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        clause.subject = exterior_entity(&perspective_surface);
        clauses.push(clause);
        selected_cell_addresses.push(cell.address.clone());
        selected_affine_sections.push(affine_cells[*at].clone());
    }
    let realization = realize_relational_clauses(&clauses, &[], false)
        .map_err(|error| LaboratoryCultivationError::Relational(format!("{error:?}")))?;
    let selected_set = selected.iter().copied().collect::<BTreeSet<_>>();
    let hidden_participant_cell_fibre = potential
        .cells
        .iter()
        .enumerate()
        .filter(|(at, cell)| {
            participant_faces.contains(&cell.subject) && !selected_set.contains(at)
        })
        .map(|(_, cell)| cell.address.clone())
        .collect::<Vec<_>>();
    let native_successor_identity_sha256 = digest_json(&(
        "soma-life.affine-laboratory-participant-successor.v1",
        rest_identity_sha256,
        apparatus.deed,
        &selected_cell_addresses,
        &selected_affine_sections,
    ))?;
    let text_sha256 = render_hex(&Sha256::digest(realization.text.as_bytes()));
    Ok(LaboratoryParticipantEmanation {
        ingress_occurrence: ingress.occurrence,
        rest_identity_sha256: rest_identity_sha256.to_owned(),
        deed: ingress.deed,
        perspective_surface,
        native_successor_identity_sha256,
        selected_cell_addresses,
        selected_affine_sections,
        hidden_participant_cell_fibre,
        text: realization.text,
        text_sha256,
        apparatus,
    })
}

/// Render an already returned native participant-cell section through one exterior perspective.
///
/// The caller supplies addresses which have already been selected by native incidence.  This
/// helper performs no contact, search, ranking, or semantic selection; it only reconstructs the
/// corresponding cold clauses in their admitted causal order.
pub(super) fn render_returned_participant_cells(
    potential: &NativeRelationalPotentialComplex,
    codec: &NativeRelationalCodec,
    cell_addresses: &[String],
    perspective_surface: &str,
) -> Result<String, LaboratoryCultivationError> {
    if cell_addresses.is_empty() {
        return Err(LaboratoryCultivationError::Correspondence(
            "the returned participant section is empty".to_owned(),
        ));
    }
    let requested = cell_addresses
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if requested.len() != cell_addresses.len() {
        return Err(LaboratoryCultivationError::Correspondence(
            "the returned participant section repeats a native cell".to_owned(),
        ));
    }
    let mut selected = potential
        .cells
        .iter()
        .filter(|cell| requested.contains(cell.address.as_str()))
        .collect::<Vec<_>>();
    if selected.len() != requested.len() {
        return Err(LaboratoryCultivationError::Correspondence(
            "the returned participant section names a cell outside the cultivated body".to_owned(),
        ));
    }
    selected.sort_by_key(|cell| {
        (
            cell.last_delivery_order().unwrap_or(0),
            cell.address.clone(),
        )
    });
    let mut clauses = Vec::<RelationalClause>::with_capacity(selected.len());
    for cell in selected {
        let mut clause = codec
            .clause(potential, cell, None)
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        clause.subject = exterior_entity(perspective_surface);
        clauses.push(clause);
    }
    realize_relational_clauses(&clauses, &[], false)
        .map(|realization| realization.text)
        .map_err(|error| LaboratoryCultivationError::Relational(format!("{error:?}")))
}

/// Reconstruct an already returned native cell section without replacing its cultivated subject
/// face.  Native incidence has selected the section before this cold projection; this helper does
/// not inspect the entering material, rank cells, or introduce an exterior semantic address.
pub(super) fn render_returned_cells(
    potential: &NativeRelationalPotentialComplex,
    codec: &NativeRelationalCodec,
    cell_addresses: &[String],
) -> Result<String, LaboratoryCultivationError> {
    if cell_addresses.is_empty() {
        return Err(LaboratoryCultivationError::Correspondence(
            "the returned native section is empty".to_owned(),
        ));
    }
    let requested = cell_addresses
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    if requested.len() != cell_addresses.len() {
        return Err(LaboratoryCultivationError::Correspondence(
            "the returned native section repeats a cell".to_owned(),
        ));
    }
    let mut selected = potential
        .cells
        .iter()
        .filter(|cell| requested.contains(cell.address.as_str()))
        .collect::<Vec<_>>();
    if selected.len() != requested.len() {
        return Err(LaboratoryCultivationError::Correspondence(
            "the returned native section names a cell outside the cultivated body".to_owned(),
        ));
    }
    selected.sort_by_key(|cell| {
        (
            cell.last_delivery_order().unwrap_or(0),
            cell.address.clone(),
        )
    });
    let clauses = selected
        .into_iter()
        .map(|cell| {
            codec
                .clause(potential, cell, None)
                .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))
        })
        .collect::<Result<Vec<_>, _>>()?;
    realize_relational_clauses(&clauses, &[], false)
        .map(|realization| realization.text)
        .map_err(|error| LaboratoryCultivationError::Relational(format!("{error:?}")))
}

impl ResidentRecurrentAffineLaboratoryAthena {
    /// Conduct one factorized material section while the complete recurrent affine body and every
    /// returned deposit remain resident in the same integrated card context.
    pub fn conduct_material(
        &mut self,
        factorization: &mut MaterialNativeFactorization,
    ) -> Result<SituatedCultivatedConductReturn, LaboratoryCultivationError> {
        let identity = self.rest.identity();
        if factorization.predecessor_rest_identity_sha256 != identity {
            return Err(LaboratoryCultivationError::Correspondence(
                "the material section addresses a different recurrent affine rest".to_owned(),
            ));
        }
        let transport = factorization
            .cultivated_affine_transport
            .as_mut()
            .ok_or_else(|| {
                LaboratoryCultivationError::Correspondence(
                    "the recurrent material section has no affine transport field".to_owned(),
                )
            })?;
        if transport.standing_rest_identity_sha256 != identity
            || transport.resident_apparatus.is_some()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the recurrent affine transport testimony is stale or already conducted".to_owned(),
            ));
        }
        let integrated = self
            .resident
            .conduct(
                &vec![true; self.factors.len()],
                &transport.entering_section,
                0,
            )
            .map_err(|error| LaboratoryCultivationError::Relational(error.to_string()))?;
        if !integrated.one_underlying_context
            || integrated.launches != 3
            || integrated.synchronizations != 1
            || integrated.intermediate_host_egress_octets != 0
            || integrated.coupled.synchronizations != 0
            || integrated.affine.synchronizations != 0
            || integrated.participant.synchronizations != 0
            || integrated.invariant_transport_reuploaded
            || integrated.cpu_semantic_replay_after_device
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the recurrent fronts did not return as one card-owned word".to_owned(),
            ));
        }
        let integrated_resident_apparatus = MaterialIntegratedResidentApparatusReceipt {
            schema: "soma-life.material-integrated-resident-apparatus.v1".to_owned(),
            device: integrated.coupled.device.clone(),
            context_identity: integrated.context_identity,
            one_underlying_context: integrated.one_underlying_context,
            launches: integrated.launches,
            synchronizations: integrated.synchronizations,
            successor_host_ingress_octets: integrated.successor_host_ingress_octets,
            successor_host_egress_octets: integrated.successor_host_egress_octets,
            intermediate_host_egress_octets: integrated.intermediate_host_egress_octets,
            resident_invariant_octets: integrated.resident_invariant_octets,
            invariant_transport_reuploaded: integrated.invariant_transport_reuploaded,
            cpu_semantic_replay_after_device: integrated.cpu_semantic_replay_after_device,
        };
        let affine_return = integrated.affine;
        if affine_return.addressed_cell_population != transport.addressed_cell_population
            || affine_return.local_fibre_term_population != transport.local_fibre_term_population
            || affine_return.exact_reconstruction_cell_population
                != transport.addressed_cell_population
            || affine_return.invariant_transport_reuploaded
            || affine_return.cpu_semantic_replay_after_device
            || affine_return.cell_selected_or_ranked
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the recurrent resident affine field diverged from its cold reconstruction"
                    .to_owned(),
            ));
        }
        transport.resident_apparatus = Some(affine_return);
        transport.integrated_resident_apparatus = Some(integrated_resident_apparatus);
        if integrated.coupled.sections != self.expected
            || integrated.coupled.sections.len() != self.factors.len()
        {
            return Err(LaboratoryCultivationError::Correspondence(
                "the integrated recurrent word diverged from the one Athena body".to_owned(),
            ));
        }
        let factors = self
            .factors
            .iter()
            .zip(&integrated.coupled.sections)
            .map(|((address, incident_threads), current)| {
                super::SituatedCultivatedConductedFactor {
                    address: address.clone(),
                    incident_threads: incident_threads.clone(),
                    current: current.clone(),
                }
            })
            .collect();
        Ok(SituatedCultivatedConductReturn {
            rest_identity_sha256: identity.to_owned(),
            factors,
            apparatus: integrated.coupled,
        })
    }

    pub fn into_rest(self) -> RecurrentReturnedAffineLaboratoryAthenaRest {
        self.rest
    }
}
