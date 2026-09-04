use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::native_spool::NativeAddressedSection;

use super::super::{
    MaterialFactorizationStanding, MaterialNativeFactorization, NativeConductedSection,
    NativeSectionAddress, SituatedCultivatedConductReturn,
};
use super::{
    digest_json, hex_sha256, AddressedEmanationIngress, EmanationCondensationReceipt,
    EmanationError, NativePotentialCell, NativePotentialCellBody, NativePotentialCellKind,
    NativePotentialContact, NativePotentialContactKind, NativeProsePotentialComplex,
};

pub(super) fn native_potential<Standing: MaterialFactorizationStanding>(
    rest: &Standing,
    factorization: &MaterialNativeFactorization,
    resident_return: &SituatedCultivatedConductReturn,
    ingress: &AddressedEmanationIngress,
) -> Result<NativeProsePotentialComplex, EmanationError> {
    let currents = resident_return
        .factors
        .iter()
        .map(|factor| (factor.address.as_str(), factor.current.clone()))
        .collect::<BTreeMap<_, _>>();
    let mut cells = Vec::new();
    for operation in &factorization.mathematical_complex.operation_cells {
        cells.push(NativePotentialCell {
            address: operation.occurrence.clone(),
            body: NativePotentialCellBody::Operation {
                invariant: factorization.invariant.clone(),
                entered_section: operation.entered_section.clone(),
                returned_section: operation.returned_section.clone(),
                exact_difference: operation.exact_difference.clone(),
            },
        });
    }
    for constraint in &factorization.mathematical_complex.constraint_cells {
        cells.push(NativePotentialCell {
            address: constraint.occurrence.clone(),
            body: NativePotentialCellBody::Constraint {
                orientation: constraint.orientation.clone(),
                exact_residual: constraint.exact_residual,
                held: constraint.held,
            },
        });
    }
    for geometry in &factorization.mathematical_complex.geometry_cells {
        cells.push(NativePotentialCell {
            address: geometry.occurrence.clone(),
            body: NativePotentialCellBody::Geometry {
                vertices: geometry
                    .vertices
                    .iter()
                    .map(|vertex| (vertex.coordinate, vertex.entered, vertex.returned))
                    .collect(),
                constraint_incidence: geometry.constraint_incidence.clone(),
                transport_incidence: geometry.transport_incidence.clone(),
            },
        });
    }
    for (at, consequence) in factorization
        .mathematical_complex
        .exact_consequence_faces
        .iter()
        .enumerate()
    {
        cells.push(NativePotentialCell {
            address: format!(
                "{}/exact-consequence/{at}",
                consequence.carrier_chart_occurrence
            ),
            body: NativePotentialCellBody::ExactConsequence {
                returned_section: consequence.returned_section.clone(),
                exact_residual: consequence.exact_residual,
                fixed_section: consequence.fixed_section,
            },
        });
    }
    let mut native_sections = Vec::new();
    for support in &factorization.factor_support {
        let current = currents
            .get(support.situated_thread.as_str())
            .cloned()
            .ok_or_else(|| {
                EmanationError::Resident(format!(
                    "missing primary current {}",
                    support.situated_thread
                ))
            })?;
        let section = owned_section(rest, &support.situated_thread)?;
        cells.push(NativePotentialCell {
            address: format!("situated-factor/{}", support.situated_thread),
            body: NativePotentialCellBody::SituatedFactor {
                coordinate: support.coordinate,
                coefficient: support.coefficient,
                current,
                incident_symmetric_population: support.incident_symmetric_families.len(),
            },
        });
        native_sections.push(section);
    }
    for family in &factorization.complete_symmetric_family_support {
        let current = currents.get(family.as_str()).cloned().ok_or_else(|| {
            EmanationError::Resident(format!("missing symmetric current {family}"))
        })?;
        cells.push(NativePotentialCell {
            address: format!("symmetric-interaction/{family}"),
            body: NativePotentialCellBody::SymmetricInteraction { current },
        });
    }
    if let Some(transport) = &factorization.cultivated_affine_transport {
        cells.push(NativePotentialCell {
            address: format!("cultivated-affine-transport/{}", transport.identity_sha256),
            body: NativePotentialCellBody::CultivatedAffineTransport {
                transport_identity_sha256: transport.identity_sha256.clone(),
                entering_section: transport.entering_section.clone(),
                addressed_landmark_population: transport.addressed_landmark_population,
                addressed_cell_population: transport.addressed_cell_population,
                local_fibre_term_population: transport.local_fibre_term_population,
                every_cell_augments_to_entering_section: transport
                    .every_cell_augments_to_entering_section,
            },
        });
    }
    for participant in &ingress.participants {
        cells.push(NativePotentialCell {
            address: format!("participant/{}", participant.identity),
            body: NativePotentialCellBody::Participant {
                participant_identity: participant.identity.clone(),
            },
        });
    }
    for modifier in &ingress.modifiers {
        cells.push(NativePotentialCell {
            address: format!("modifier/{}", hex_sha256(modifier.as_bytes())),
            body: NativePotentialCellBody::Modifier {
                addressed_disturbance: modifier.clone(),
            },
        });
    }
    let mut predecessor = ingress.predecessor_occurrence.clone();
    for successor in &ingress.chronology {
        cells.push(NativePotentialCell {
            address: format!("chronology/{successor}"),
            body: NativePotentialCellBody::Chronology {
                predecessor: predecessor.clone(),
                successor: successor.clone(),
            },
        });
        predecessor = Some(successor.clone());
    }
    for ambiguity in &ingress.open_ambiguity {
        cells.push(NativePotentialCell {
            address: format!("open-ambiguity/{}", hex_sha256(ambiguity.as_bytes())),
            body: NativePotentialCellBody::OpenAmbiguity {
                retained_fibre: ambiguity.clone(),
            },
        });
    }
    if cells.is_empty() || native_sections.is_empty() {
        return Err(EmanationError::Potential);
    }
    let operation_roots = cells
        .iter()
        .filter(|cell| cell.body.kind() == NativePotentialCellKind::Operation)
        .map(|cell| cell.address.clone())
        .collect::<Vec<_>>();
    let root = operation_roots
        .first()
        .ok_or(EmanationError::Potential)?
        .clone();
    let mut contacts = Vec::new();
    for cell in &cells {
        if cell.address == root {
            continue;
        }
        let kind = match cell.body.kind() {
            NativePotentialCellKind::Constraint => NativePotentialContactKind::Constrains,
            NativePotentialCellKind::Geometry | NativePotentialCellKind::ExactConsequence => {
                NativePotentialContactKind::Realizes
            }
            NativePotentialCellKind::SituatedFactor => NativePotentialContactKind::Supports,
            NativePotentialCellKind::SymmetricInteraction => NativePotentialContactKind::Couples,
            NativePotentialCellKind::CultivatedAffineTransport => {
                NativePotentialContactKind::Couples
            }
            NativePotentialCellKind::Participant => NativePotentialContactKind::Presents,
            NativePotentialCellKind::Modifier => NativePotentialContactKind::Presents,
            NativePotentialCellKind::Chronology => NativePotentialContactKind::Precedes,
            NativePotentialCellKind::OpenAmbiguity => NativePotentialContactKind::LeavesOpen,
            NativePotentialCellKind::Operation => NativePotentialContactKind::Supports,
        };
        contacts.push(NativePotentialContact {
            from: cell.address.clone(),
            to: root.clone(),
            kind,
        });
    }
    contacts.sort();
    let occurrence = format!(
        "native-prose-potential/{}/{}",
        ingress.occurrence, factorization.native_operation_identity_sha256
    );
    let mut complete_reconstruction_fibre = factorization.reconstruction_fibre.clone();
    complete_reconstruction_fibre.extend(native_sections.iter().flat_map(|section| {
        section
            .reconstruction_fibre
            .iter()
            .map(|event| format!("event/{}", event.0))
    }));
    complete_reconstruction_fibre.sort();
    complete_reconstruction_fibre.dedup();
    let mut open_exterior = ingress.open_exterior.clone();
    open_exterior.extend(factorization.open_exterior.iter().cloned());
    open_exterior.sort();
    open_exterior.dedup();
    let identity_sha256 = digest_json(&(
        super::NATIVE_PROSE_POTENTIAL_SCHEMA,
        &occurrence,
        rest.material_standing_identity(),
        &factorization.material_occurrence,
        &factorization.native_operation_identity_sha256,
        &cells,
        &contacts,
        &native_sections,
        &complete_reconstruction_fibre,
        &open_exterior,
    ))?;
    Ok(NativeProsePotentialComplex {
        schema: super::NATIVE_PROSE_POTENTIAL_SCHEMA.to_owned(),
        occurrence,
        predecessor_rest_identity_sha256: rest.material_standing_identity().to_owned(),
        material_occurrence: factorization.material_occurrence.clone(),
        native_operation_identity_sha256: factorization.native_operation_identity_sha256.clone(),
        cells,
        contacts,
        native_sections,
        complete_reconstruction_fibre,
        open_exterior,
        identity_sha256,
    })
}

fn owned_section<Standing: MaterialFactorizationStanding>(
    rest: &Standing,
    thread_address: &str,
) -> Result<NativeConductedSection, EmanationError> {
    let native = rest.material_standing_ecology().native();
    let (spool_address, thread) = native
        .spools
        .iter()
        .find_map(|spool| {
            spool
                .threads
                .iter()
                .find(|thread| thread.address == thread_address)
                .map(|thread| (spool.address.clone(), thread))
        })
        .ok_or_else(|| EmanationError::NativeSection(thread_address.to_owned()))?;
    let occurrence = thread
        .occurrences
        .first()
        .ok_or_else(|| EmanationError::NativeSection(thread_address.to_owned()))?;
    let section = native
        .addressed_section(&spool_address, thread_address, occurrence.occurrence)
        .map_err(|error| EmanationError::NativeSection(error.to_string()))?;
    section_to_owned(rest, section)
}

fn section_to_owned<Standing: MaterialFactorizationStanding>(
    rest: &Standing,
    section: NativeAddressedSection<'_>,
) -> Result<NativeConductedSection, EmanationError> {
    let occurrence = section.occurrence();
    let thread = section.thread();
    let constitutive_response = thread
        .constitutive_responses
        .iter()
        .find(|response| response.native == occurrence.emitting_native)
        .cloned()
        .ok_or_else(|| EmanationError::NativeSection(thread.address.clone()))?;
    let consequence = thread
        .receiver_consequences
        .iter()
        .find(|consequence| {
            consequence.native == occurrence.emitting_native
                && consequence.receiver == constitutive_response.receiver
        })
        .copied()
        .ok_or_else(|| EmanationError::NativeSection(thread.address.clone()))?;
    let mut successors = rest
        .material_standing_realization()
        .sections
        .iter()
        .filter_map(|address| {
            let successor = rest
                .material_standing_ecology()
                .native()
                .spools
                .iter()
                .find(|spool| spool.address == address.spool)?
                .threads
                .iter()
                .find(|thread| thread.address == address.thread)?
                .occurrences
                .iter()
                .find(|candidate| candidate.occurrence == address.occurrence)?;
            (successor.predecessor == Some(occurrence.occurrence)).then_some(address.clone())
        })
        .collect::<Vec<_>>();
    successors.sort();
    let mutual_constitutive_responses = section
        .spool()
        .mutual_constitutive_responses
        .iter()
        .filter(|response| {
            response.left_occurrence == occurrence.occurrence
                || response.right_occurrence == occurrence.occurrence
        })
        .cloned()
        .collect();
    Ok(NativeConductedSection {
        address: NativeSectionAddress {
            spool: section.spool().address.clone(),
            thread: thread.address.clone(),
            occurrence: occurrence.occurrence,
        },
        predecessor: occurrence.predecessor,
        entering_boundary: thread.entering_boundary,
        emitting_boundary: thread.emitting_boundary,
        entering_port: occurrence.entering_port,
        emitting_port: occurrence.emitting_port,
        entering_native: occurrence.entering_native,
        emitting_native: occurrence.emitting_native,
        incidence: section.incidence().clone(),
        entering_section: section.entering_parametron().section.clone(),
        entering_current: section.entering_parametron().current.clone(),
        emitting_section: section.emitting_parametron().section.clone(),
        emitting_current: section.emitting_parametron().current.clone(),
        relative_phase: section.emitting_parametron().relative_phase.clone(),
        hand: section.emitting_parametron().hand,
        constitutive_response,
        mutual_constitutive_responses,
        ordered_word: section.ordered_generator_word().to_vec(),
        receiver: consequence.receiver,
        observation: consequence.observation,
        reconstruction_fibre: section.reconstruction_fibre().occurrences.clone(),
        successor_sections: successors,
        open_exterior: thread.open_exterior.clone(),
    })
}

pub(super) fn condensation(
    potential: &NativeProsePotentialComplex,
    requested: BTreeSet<NativePotentialCellKind>,
) -> Result<EmanationCondensationReceipt, EmanationError> {
    if requested.is_empty() {
        return Err(EmanationError::Condensation);
    }
    let present = potential
        .cells
        .iter()
        .map(|cell| cell.body.kind())
        .collect::<BTreeSet<_>>();
    if !requested.is_subset(&present) {
        return Err(EmanationError::Condensation);
    }
    let mut closure = requested.clone();
    if closure.contains(&NativePotentialCellKind::ExactConsequence)
        || closure.contains(&NativePotentialCellKind::Geometry)
        || closure.contains(&NativePotentialCellKind::Constraint)
        || closure.contains(&NativePotentialCellKind::SituatedFactor)
        || closure.contains(&NativePotentialCellKind::SymmetricInteraction)
        || closure.contains(&NativePotentialCellKind::CultivatedAffineTransport)
    {
        closure.insert(NativePotentialCellKind::Operation);
    }
    if closure.contains(&NativePotentialCellKind::ExactConsequence)
        || closure.contains(&NativePotentialCellKind::Geometry)
    {
        closure.insert(NativePotentialCellKind::Constraint);
    }
    closure.insert(NativePotentialCellKind::Participant);
    let visible_cells = potential
        .cells
        .iter()
        .filter(|cell| closure.contains(&cell.body.kind()))
        .map(|cell| cell.address.clone())
        .collect::<BTreeSet<_>>();
    let retained_hidden_fibre = potential
        .cells
        .iter()
        .filter(|cell| !visible_cells.contains(&cell.address))
        .map(|cell| cell.address.clone())
        .collect::<BTreeSet<_>>();
    Ok(EmanationCondensationReceipt {
        requested_future_receiver_family: requested,
        dependency_closed_family: closure,
        visible_cells,
        retained_hidden_fibre,
    })
}
