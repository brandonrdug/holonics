use std::collections::{BTreeMap, BTreeSet};

use super::super::{CausalOperationInvariant, CausalPopulationLaw};
use super::{
    AddressedEmanationIngress, EmanationDeed, EmanationError, EmanationMorphology, EmanationVoice,
    NativePotentialCell, NativePotentialCellBody, NativePotentialCellKind,
    NativeProsePotentialComplex, population_surface,
};
use crate::relational_language::{
    RelationalClause, RelationalClauseVoice, RelationalEntity, RelationalRealization,
    realize_relational_clauses,
};

fn operation_surface(invariant: &CausalOperationInvariant) -> String {
    format!(
        "a {} of populations {} and {} returning {} and separating at {} under one left extension",
        law_surface(invariant.law),
        invariant.left_population,
        invariant.right_population,
        invariant.returned_population,
        invariant.left_extension_returned_population,
    )
}

fn section_surface(section: &[i64]) -> String {
    format!(
        "[{}]",
        section
            .iter()
            .map(i64::to_string)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

pub(super) fn exterior_clauses(
    potential: &NativeProsePotentialComplex,
    invariant: &CausalOperationInvariant,
    ingress: &AddressedEmanationIngress,
    morphology: &EmanationMorphology,
) -> Result<Vec<RelationalClause>, EmanationError> {
    let subject = ingress
        .participants
        .iter()
        .find(|participant| participant.identity == ingress.subject_participant)
        .ok_or(EmanationError::Perspective)?;
    let face = morphology.perspective.face(subject);
    let subject_entity = RelationalEntity {
        surface: vec![face.exterior_surface],
        identity: BTreeSet::from([subject.identity.clone(), subject.occurrence.clone()]),
    };
    let mut by_kind = BTreeMap::<NativePotentialCellKind, Vec<&NativePotentialCell>>::new();
    for cell in &potential.cells {
        if morphology
            .condensation
            .visible_cells
            .contains(&cell.address)
        {
            by_kind.entry(cell.body.kind()).or_default().push(cell);
        }
    }
    let operation_surface = operation_surface(invariant);
    let (root_relation, root_object) = match ingress.deed {
        EmanationDeed::Describe => ("present", operation_surface.clone()),
        EmanationDeed::Identify => (
            "identify",
            format!(
                "the addressed {} operation section",
                law_surface(invariant.law)
            ),
        ),
        EmanationDeed::Infer => (
            "infer",
            format!(
                "a returned population of {} after the next left extension",
                invariant.left_extension_returned_population
            ),
        ),
        EmanationDeed::Explain => (
            "connect",
            format!(
                "{} through complete incidence and returned difference",
                operation_surface
            ),
        ),
        EmanationDeed::Rewrite => ("restate", operation_surface.clone()),
        EmanationDeed::Derive => (
            "derive",
            format!(
                "{} from populations {} and {} with successor return {}",
                invariant.returned_population,
                invariant.left_population,
                invariant.right_population,
                invariant.left_extension_returned_population
            ),
        ),
    };
    let mut clauses = vec![clause(
        format!("{}/receiver/{:?}", potential.occurrence, ingress.deed),
        potential.occurrence.clone(),
        subject_entity,
        root_relation,
        Some("can"),
        entity(
            root_object,
            [potential.native_operation_identity_sha256.clone()],
        ),
    )];

    for kind in &morphology.kind_order {
        let Some(cells) = by_kind.get(kind) else {
            continue;
        };
        match kind {
            NativePotentialCellKind::Operation | NativePotentialCellKind::Participant => {}
            NativePotentialCellKind::Modifier => {
                clauses.push(clause(
                    format!("{}/modifier-population", potential.occurrence),
                    potential.occurrence.clone(),
                    entity(
                        "The complete ingress",
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                    "retain",
                    None,
                    entity(
                        format!("{} addressed modifiers", cells.len()),
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                ));
            }
            NativePotentialCellKind::Constraint => {
                for cell in cells {
                    let NativePotentialCellBody::Constraint {
                        exact_residual,
                        held,
                        ..
                    } = &cell.body
                    else {
                        continue;
                    };
                    clauses.push(clause(
                        cell.address.clone(),
                        potential.occurrence.clone(),
                        entity("The exact constraint", [cell.address.clone()]),
                        if *held { "hold" } else { "remain" },
                        None,
                        entity(
                            format!("with returned residual {exact_residual}"),
                            [cell.address.clone()],
                        ),
                    ));
                }
            }
            NativePotentialCellKind::Geometry => {
                for cell in cells {
                    let NativePotentialCellBody::Geometry { vertices, .. } = &cell.body else {
                        continue;
                    };
                    clauses.push(clause(
                        cell.address.clone(),
                        potential.occurrence.clone(),
                        entity("The native geometry", [cell.address.clone()]),
                        "carry",
                        None,
                        entity(
                            format!("{} addressed vertices", vertices.len()),
                            [cell.address.clone()],
                        ),
                    ));
                }
            }
            NativePotentialCellKind::ExactConsequence => {
                for cell in cells {
                    let NativePotentialCellBody::ExactConsequence {
                        returned_section,
                        exact_residual,
                        ..
                    } = &cell.body
                    else {
                        continue;
                    };
                    clauses.push(clause(
                        cell.address.clone(),
                        potential.occurrence.clone(),
                        entity("The exact consequence", [cell.address.clone()]),
                        "return",
                        None,
                        entity(
                            format!(
                                "section {} with residual {exact_residual}",
                                section_surface(returned_section)
                            ),
                            [cell.address.clone()],
                        ),
                    ));
                }
            }
            NativePotentialCellKind::SituatedFactor => {
                for cell in cells {
                    let NativePotentialCellBody::SituatedFactor {
                        coordinate,
                        coefficient,
                        incident_symmetric_population,
                        ..
                    } = &cell.body
                    else {
                        continue;
                    };
                    clauses.push(clause(
                        cell.address.clone(),
                        potential.occurrence.clone(),
                        entity(format!("Situated direction {coordinate}"), [cell.address.clone()]),
                        "carry",
                        None,
                        entity(format!("coefficient {coefficient} through {incident_symmetric_population} coupled families"), [cell.address.clone()]),
                    ));
                }
            }
            NativePotentialCellKind::SymmetricInteraction => {
                clauses.push(clause(
                    format!("{}/symmetric-population", potential.occurrence),
                    potential.occurrence.clone(),
                    entity(
                        "The constitutive body",
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                    "retain",
                    None,
                    entity(
                        format!("{} symmetric interaction currents", cells.len()),
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                ));
            }
            NativePotentialCellKind::CultivatedAffineTransport => {
                for cell in cells {
                    let NativePotentialCellBody::CultivatedAffineTransport {
                        entering_section,
                        addressed_landmark_population,
                        addressed_cell_population,
                        local_fibre_term_population,
                        every_cell_augments_to_entering_section,
                        ..
                    } = &cell.body
                    else {
                        continue;
                    };
                    clauses.push(clause(
                        cell.address.clone(),
                        potential.occurrence.clone(),
                        entity("The cultivated affine laboratory", [cell.address.clone()]),
                        "transport",
                        None,
                        entity(
                            format!(
                                "section {} through {} addressed cells over {} landmarks with {} retained local fibre terms; affine augmentation {} the entering section",
                                section_surface(entering_section),
                                addressed_cell_population,
                                addressed_landmark_population,
                                local_fibre_term_population,
                                if *every_cell_augments_to_entering_section {
                                    "reconstructs"
                                } else {
                                    "does not reconstruct"
                                }
                            ),
                            [cell.address.clone()],
                        ),
                    ));
                }
            }
            NativePotentialCellKind::Chronology => {
                clauses.push(clause(
                    format!("{}/chronology-population", potential.occurrence),
                    potential.occurrence.clone(),
                    entity(
                        "The addressed chronology",
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                    "retain",
                    None,
                    entity(
                        format!("{} ordered occurrences", cells.len()),
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                ));
            }
            NativePotentialCellKind::OpenAmbiguity => {
                clauses.push(clause(
                    format!("{}/ambiguity-population", potential.occurrence),
                    potential.occurrence.clone(),
                    entity(
                        "The open boundary",
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                    "retain",
                    None,
                    entity(
                        population_surface(cells.len(), "unresolved reconstruction fibre"),
                        cells.iter().map(|cell| cell.address.clone()),
                    ),
                ));
            }
        }
    }
    if clauses.is_empty() {
        return Err(EmanationError::Surface(
            "the receiver aperture hid every consequence".to_owned(),
        ));
    }
    Ok(clauses)
}

fn clause(
    identity: String,
    passage: String,
    subject: RelationalEntity,
    relation: &str,
    modality: Option<&str>,
    object: RelationalEntity,
) -> RelationalClause {
    RelationalClause {
        identity: identity.clone(),
        passage,
        source: identity,
        receiver: 0,
        source_order: 0,
        source_order_declared: true,
        source_local_step: 0,
        subject,
        relation: relation.to_owned(),
        modality: modality.map(str::to_owned),
        object,
        witnessed_voice: RelationalClauseVoice::Active,
        witnessed_surface: String::new(),
    }
}

fn entity(
    surface: impl Into<String>,
    identity: impl IntoIterator<Item = String>,
) -> RelationalEntity {
    RelationalEntity {
        surface: surface
            .into()
            .split_whitespace()
            .map(str::to_owned)
            .collect(),
        identity: identity.into_iter().collect(),
    }
}

fn law_surface(law: CausalPopulationLaw) -> &'static str {
    match law {
        CausalPopulationLaw::DisjointUnion => "disjoint union",
        CausalPopulationLaw::IndependentProduct => "independent product",
    }
}

pub(super) fn realize_surface(
    clauses: &[RelationalClause],
    voice: EmanationVoice,
) -> Result<RelationalRealization, EmanationError> {
    match voice {
        EmanationVoice::Active => realize_relational_clauses(clauses, &[], false)
            .map_err(|error| EmanationError::Surface(format!("{error:?}"))),
        EmanationVoice::Passive => {
            let (principal, consequences) = clauses.split_first().ok_or_else(|| {
                EmanationError::Surface("the native successor has no principal relation".to_owned())
            })?;
            let principal = realize_relational_clauses(std::slice::from_ref(principal), &[], true)
                .map_err(|error| EmanationError::Surface(format!("{error:?}")))?;
            let consequences = realize_relational_clauses(consequences, &[], false)
                .map_err(|error| EmanationError::Surface(format!("{error:?}")))?;
            let text = if consequences.text.is_empty() {
                principal.text.clone()
            } else {
                format!("{} {}", principal.text, consequences.text)
            };
            let mut realized_clauses = principal.clauses;
            realized_clauses.extend(consequences.clauses);
            Ok(RelationalRealization {
                text,
                clauses: realized_clauses,
                voice_dual: true,
                inherited_contiguous: false,
            })
        }
        EmanationVoice::Copular => {
            let mut realized = realize_relational_clauses(clauses, &[], false)
                .map_err(|error| EmanationError::Surface(format!("{error:?}")))?;
            realized.text = format!("The returned perspective is this: {}", realized.text);
            Ok(realized)
        }
    }
}
