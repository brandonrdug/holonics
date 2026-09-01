//! Cold one-way intake for the source-bearing relational predecessor.
//!
//! This module is the only owner of the rejected developmental chart.  Its parser consumes the
//! predecessor and emits sealed source-neutral morphology plus the exterior realization chart.
//! No type in this module is reachable from hot conduct.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use serde::Deserialize;

use super::source_neutral_relational::{
    canonicalize_partition, cell_address, face_address, invalid_support, key, partition,
    realization_sites_match_relational, relational_boundary_positions, same_partition,
    SourceNeutralExteriorRealizationMorphology, SourceNeutralExteriorRealizationSite,
    SourceNeutralExteriorRealizationTransition, SourceNeutralPhasePopulation,
    SourceNeutralRelationalCell, SourceNeutralRelationalError, SourceNeutralRelationalFace,
    SourceNeutralRelationalMorphology, SOURCE_NEUTRAL_EXTERIOR_REALIZATION_MORPHOLOGY_SCHEMA,
    SOURCE_NEUTRAL_RELATIONAL_MORPHOLOGY_SCHEMA,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
enum ColdPhase {
    Ingress,
    Emanation,
    Return,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ColdFaceOccurrence {
    factor: u32,
    phase: ColdPhase,
    #[serde(rename = "role")]
    _role: serde_json::Value,
    #[serde(rename = "source_occurrence_identity_sha256")]
    _source_occurrence: String,
    #[serde(rename = "first_delivery_order")]
    _first_delivery_order: u64,
    #[serde(rename = "last_delivery_order")]
    _last_delivery_order: u64,
    occurrence_population: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ColdFace {
    #[serde(rename = "address")]
    _address: String,
    #[serde(rename = "kind")]
    _kind: serde_json::Value,
    #[serde(rename = "founding_delivery_order")]
    _founding_delivery_order: u64,
    #[serde(rename = "founding_clause_order")]
    _founding_clause_order: u64,
    occurrences: Vec<ColdFaceOccurrence>,
    factor_support: Vec<u32>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ColdCellOccurrence {
    factor: u32,
    phase: ColdPhase,
    #[serde(rename = "source_occurrence_identity_sha256")]
    _source_occurrence: String,
    #[serde(rename = "first_delivery_order")]
    _first_delivery_order: u64,
    #[serde(rename = "last_delivery_order")]
    _last_delivery_order: u64,
    occurrence_population: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ColdCell {
    #[serde(rename = "address")]
    _address: String,
    subject: u32,
    relation: u32,
    modality: Option<u32>,
    object: u32,
    #[serde(rename = "copular")]
    _copular: bool,
    occurrences: Vec<ColdCellOccurrence>,
    factor_support: Vec<u32>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ColdPotential {
    #[serde(rename = "schema")]
    _schema: String,
    factor_addresses: Vec<String>,
    factor_adjacency: Vec<(u32, u32)>,
    faces: Vec<ColdFace>,
    cells: Vec<ColdCell>,
    obstructed_delivery_population: u64,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ColdBoundaryFace {
    #[serde(rename = "key")]
    _key: serde_json::Value,
    surface_variants: Vec<Vec<String>>,
    native_face: u32,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ColdCodec {
    #[serde(rename = "schema")]
    _schema: String,
    faces: Vec<ColdBoundaryFace>,
}

pub(super) fn read_developmental_predecessor(
    value: serde_json::Value,
    codec: serde_json::Value,
) -> Result<
    (
        SourceNeutralRelationalMorphology,
        SourceNeutralExteriorRealizationMorphology,
        u64,
    ),
    SourceNeutralRelationalError,
> {
    let potential: ColdPotential =
        serde_json::from_value(value).map_err(|_| SourceNeutralRelationalError::Developmental)?;
    let codec: ColdCodec =
        serde_json::from_value(codec).map_err(|_| SourceNeutralRelationalError::Developmental)?;
    let factor_population = u32::try_from(potential.factor_addresses.len())
        .map_err(|_| SourceNeutralRelationalError::Extent)?;
    if factor_population == 0
        || potential.faces.is_empty()
        || potential.cells.is_empty()
        || potential
            .factor_adjacency
            .windows(2)
            .any(|pair| pair[0] >= pair[1])
        || potential
            .factor_adjacency
            .iter()
            .any(|(left, right)| left >= right || *right >= factor_population)
    {
        return Err(SourceNeutralRelationalError::Developmental);
    }
    let face_population = potential.faces.len();
    if potential.cells.iter().any(|cell| {
        [cell.subject, cell.relation, cell.object]
            .into_iter()
            .any(|face| face as usize >= face_population)
            || cell
                .modality
                .is_some_and(|face| face as usize >= face_population)
    }) {
        return Err(SourceNeutralRelationalError::Developmental);
    }

    let face_phase = potential
        .faces
        .iter()
        .map(|face| {
            aggregate_phase(
                face.occurrences.iter().map(|occurrence| {
                    (
                        occurrence.factor,
                        occurrence.phase,
                        occurrence.occurrence_population,
                    )
                }),
                factor_population,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    let cell_phase = potential
        .cells
        .iter()
        .map(|cell| {
            aggregate_phase(
                cell.occurrences.iter().map(|occurrence| {
                    (
                        occurrence.factor,
                        occurrence.phase,
                        occurrence.occurrence_population,
                    )
                }),
                factor_population,
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    validate_supports(
        potential
            .faces
            .iter()
            .map(|face| face.factor_support.as_slice()),
        factor_population,
    )?;
    validate_supports(
        potential
            .cells
            .iter()
            .map(|cell| cell.factor_support.as_slice()),
        factor_population,
    )?;

    let mut face_classes = partition(
        potential
            .faces
            .iter()
            .zip(&face_phase)
            .map(|(face, phase)| key(&(face.factor_support.as_slice(), phase)))
            .collect::<Result<Vec<_>, _>>()?,
    )?;
    let mut cell_classes = partition(
        potential
            .cells
            .iter()
            .zip(&cell_phase)
            .map(|(cell, phase)| {
                key(&(
                    cell.factor_support.as_slice(),
                    phase,
                    cell.modality.is_some(),
                ))
            })
            .collect::<Result<Vec<_>, _>>()?,
    )?;
    let mut refinement_order = 0_u64;
    loop {
        let mut incident = vec![Vec::<(u8, u32)>::new(); face_population];
        for (cell_at, cell) in potential.cells.iter().enumerate() {
            let class = cell_classes[cell_at];
            incident[cell.subject as usize].push((0, class));
            incident[cell.relation as usize].push((1, class));
            if let Some(modality) = cell.modality {
                incident[modality as usize].push((2, class));
            }
            incident[cell.object as usize].push((3, class));
        }
        incident.iter_mut().for_each(|edges| edges.sort_unstable());
        let next_faces = partition(
            potential
                .faces
                .iter()
                .zip(&face_phase)
                .zip(&incident)
                .zip(&face_classes)
                .map(|(((face, phase), edges), prior)| {
                    key(&(*prior, face.factor_support.as_slice(), phase, edges))
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let next_cells = partition(
            potential
                .cells
                .iter()
                .zip(&cell_phase)
                .zip(&cell_classes)
                .map(|((cell, phase), prior)| {
                    let boundary = oriented_boundary(cell, &next_faces);
                    key(&(*prior, cell.factor_support.as_slice(), phase, boundary))
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        refinement_order = refinement_order
            .checked_add(1)
            .ok_or(SourceNeutralRelationalError::Extent)?;
        if same_partition(&face_classes, &next_faces) && same_partition(&cell_classes, &next_cells)
        {
            face_classes = canonicalize_partition(next_faces)?;
            cell_classes = canonicalize_partition(next_cells)?;
            break;
        }
        face_classes = next_faces;
        cell_classes = next_cells;
    }

    let faces = quotient_faces(
        &potential.faces,
        &face_phase,
        &potential.cells,
        &face_classes,
        &cell_classes,
    )?;
    let cells = quotient_cells(&potential.cells, &cell_phase, &face_classes, &cell_classes)?;
    let mut morphology = SourceNeutralRelationalMorphology {
        schema: SOURCE_NEUTRAL_RELATIONAL_MORPHOLOGY_SCHEMA.to_owned(),
        factor_population,
        factor_adjacency: potential.factor_adjacency,
        faces,
        cells,
        obstructed_delivery_population: potential.obstructed_delivery_population,
        identity_sha256: String::new(),
    };
    morphology.identity_sha256 = morphology.rederived_identity();
    morphology.validate()?;
    let realization = found_realization(
        codec,
        &potential.faces,
        &face_classes,
        &morphology,
        factor_population,
    )?;
    realization.validate(factor_population as usize)?;
    Ok((morphology, realization, refinement_order))
}

fn found_realization(
    codec: ColdCodec,
    faces: &[ColdFace],
    face_classes: &[u32],
    relational: &SourceNeutralRelationalMorphology,
    factor_population: u32,
) -> Result<SourceNeutralExteriorRealizationMorphology, SourceNeutralRelationalError> {
    relational.validate()?;
    if factor_population == 0
        || relational.face_population() == 0
        || relational.cell_population() == 0
        || faces.is_empty()
        || face_classes.len() != faces.len()
        || face_classes
            .iter()
            .any(|face| *face as usize >= relational.face_population())
        || codec.faces.is_empty()
    {
        return Err(SourceNeutralRelationalError::Developmental);
    }
    let face_root_states = (0..relational.face_population())
        .map(|face| u32::try_from(face).map_err(|_| SourceNeutralRelationalError::Extent))
        .collect::<Result<Vec<_>, _>>()?;
    let mut realization_state_population =
        u32::try_from(face_root_states.len()).map_err(|_| SourceNeutralRelationalError::Extent)?;
    let mut path_edges = HashMap::<(u32, u32, u16, u16), Option<u32>>::new();
    let mut transition_population = HashMap::<(u32, u32, u16, u16, Option<u32>), u64>::new();
    let mut developmental_transition_population = 0_u64;
    for face in codec.faces {
        let site = *face_classes
            .get(face.native_face as usize)
            .ok_or(SourceNeutralRelationalError::Developmental)?;
        let support = faces
            .get(face.native_face as usize)
            .map(|face| face.factor_support.as_slice())
            .ok_or(SourceNeutralRelationalError::Developmental)?;
        if invalid_support(support, factor_population) {
            return Err(SourceNeutralRelationalError::Developmental);
        }
        for variant in face.surface_variants {
            if variant.is_empty() || variant.iter().any(String::is_empty) {
                return Err(SourceNeutralRelationalError::Developmental);
            }
            let mut surface = Vec::new();
            for (at, part) in variant.iter().enumerate() {
                if at != 0 {
                    surface.push(b' ');
                }
                surface.extend_from_slice(part.as_bytes());
            }
            if surface.is_empty() {
                return Err(SourceNeutralRelationalError::Developmental);
            }
            let mut ports = Vec::with_capacity(surface.len().saturating_add(2));
            ports.push(0_u16);
            ports.extend(surface.into_iter().map(|octet| u16::from(octet) + 1));
            ports.push(257_u16);
            let mut state = *face_root_states
                .get(site as usize)
                .ok_or(SourceNeutralRelationalError::Developmental)?;
            for pair in ports.windows(2) {
                developmental_transition_population = developmental_transition_population
                    .checked_add(1)
                    .ok_or(SourceNeutralRelationalError::Extent)?;
                let edge = (site, state, pair[0], pair[1]);
                let target_state = if pair[1] == 257 {
                    None
                } else if let Some(target) = path_edges.get(&edge).copied() {
                    target
                } else {
                    let target = realization_state_population;
                    realization_state_population = realization_state_population
                        .checked_add(1)
                        .ok_or(SourceNeutralRelationalError::Extent)?;
                    path_edges.insert(edge, Some(target));
                    Some(target)
                };
                path_edges.entry(edge).or_insert(target_state);
                let entry = transition_population
                    .entry((site, state, pair[0], pair[1], target_state))
                    .or_default();
                *entry = entry
                    .checked_add(1)
                    .ok_or(SourceNeutralRelationalError::Extent)?;
                if let Some(target) = target_state {
                    state = target;
                }
            }
        }
    }
    if developmental_transition_population == 0 || transition_population.is_empty() {
        return Err(SourceNeutralRelationalError::Developmental);
    }
    let mut transitions = transition_population
        .into_iter()
        .map(
            |((face, state, source, target, target_state), occurrence_population)| {
                SourceNeutralExteriorRealizationTransition {
                    face,
                    state,
                    source,
                    target,
                    target_state,
                    occurrence_population,
                }
            },
        )
        .collect::<Vec<_>>();
    transitions.sort_unstable_by_key(|transition| {
        (
            transition.source,
            transition.state,
            transition.face,
            transition.target,
        )
    });
    let sites = founded_realization_sites(relational)?;
    let mut morphology = SourceNeutralExteriorRealizationMorphology {
        schema: SOURCE_NEUTRAL_EXTERIOR_REALIZATION_MORPHOLOGY_SCHEMA.to_owned(),
        relational_identity_sha256: relational.identity().to_owned(),
        face_population: u32::try_from(relational.face_population())
            .map_err(|_| SourceNeutralRelationalError::Extent)?,
        cell_population: u32::try_from(relational.cell_population())
            .map_err(|_| SourceNeutralRelationalError::Extent)?,
        sites,
        factor_population,
        face_root_states,
        realization_state_population,
        transitions,
        developmental_transition_population,
        identity_sha256: String::new(),
    };
    morphology.identity_sha256 = morphology.rederived_identity();
    morphology.validate(factor_population as usize)?;
    if morphology.relational_identity_sha256 != relational.identity()
        || !realization_sites_match_relational(&morphology.sites, relational)?
    {
        return Err(SourceNeutralRelationalError::Quotient);
    }
    Ok(morphology)
}

fn aggregate_phase(
    occurrences: impl IntoIterator<Item = (u32, ColdPhase, u64)>,
    factor_population: u32,
) -> Result<Vec<SourceNeutralPhasePopulation>, SourceNeutralRelationalError> {
    let mut aggregate = BTreeMap::<(u32, u8), u64>::new();
    for (factor, phase, population) in occurrences {
        if factor >= factor_population || population == 0 {
            return Err(SourceNeutralRelationalError::Developmental);
        }
        let entry = aggregate.entry((factor, phase_id(phase))).or_default();
        *entry = entry
            .checked_add(population)
            .ok_or(SourceNeutralRelationalError::Extent)?;
    }
    if aggregate.is_empty() {
        return Err(SourceNeutralRelationalError::Developmental);
    }
    Ok(aggregate
        .into_iter()
        .map(
            |((factor, phase), occurrence_population)| SourceNeutralPhasePopulation {
                factor,
                phase,
                occurrence_population,
            },
        )
        .collect())
}

fn phase_id(phase: ColdPhase) -> u8 {
    match phase {
        ColdPhase::Ingress => 0,
        ColdPhase::Emanation => 1,
        ColdPhase::Return => 2,
    }
}

fn validate_supports<'a>(
    supports: impl IntoIterator<Item = &'a [u32]>,
    factor_population: u32,
) -> Result<(), SourceNeutralRelationalError> {
    if supports
        .into_iter()
        .any(|support| invalid_support(support, factor_population))
    {
        Err(SourceNeutralRelationalError::Developmental)
    } else {
        Ok(())
    }
}

fn oriented_boundary(cell: &ColdCell, face_classes: &[u32]) -> Vec<u32> {
    let mut boundary = vec![
        face_classes[cell.subject as usize],
        face_classes[cell.relation as usize],
    ];
    if let Some(modality) = cell.modality {
        boundary.push(face_classes[modality as usize]);
    }
    boundary.push(face_classes[cell.object as usize]);
    boundary
}

fn quotient_faces(
    developmental: &[ColdFace],
    phase: &[Vec<SourceNeutralPhasePopulation>],
    cells: &[ColdCell],
    face_classes: &[u32],
    cell_classes: &[u32],
) -> Result<Vec<SourceNeutralRelationalFace>, SourceNeutralRelationalError> {
    let class_population = face_classes.iter().copied().max().unwrap_or(0) as usize + 1;
    let mut members = vec![Vec::<usize>::new(); class_population];
    for (face, class) in face_classes.iter().copied().enumerate() {
        members[class as usize].push(face);
    }
    let mut incident = vec![Vec::<(u32, u8)>::new(); developmental.len()];
    for (cell_at, cell) in cells.iter().enumerate() {
        let class = cell_classes[cell_at];
        incident[cell.subject as usize].push((class, 0));
        incident[cell.relation as usize].push((class, 1));
        if let Some(modality) = cell.modality {
            incident[modality as usize].push((class, 2));
        }
        incident[cell.object as usize].push((class, 3));
    }
    members
        .into_iter()
        .enumerate()
        .map(|(class, members)| {
            let mut support = BTreeSet::new();
            let mut populations = BTreeMap::<(u32, u8), u64>::new();
            let mut incidences = BTreeMap::<(u32, u8), u64>::new();
            for member in &members {
                support.extend(developmental[*member].factor_support.iter().copied());
                for current in &phase[*member] {
                    let entry = populations
                        .entry((current.factor, current.phase))
                        .or_default();
                    *entry = entry
                        .checked_add(current.occurrence_population)
                        .ok_or(SourceNeutralRelationalError::Extent)?;
                }
                for incidence in &incident[*member] {
                    let entry = incidences.entry(*incidence).or_default();
                    *entry = entry
                        .checked_add(1)
                        .ok_or(SourceNeutralRelationalError::Extent)?;
                }
            }
            let mut face = SourceNeutralRelationalFace {
                address: String::new(),
                factor_support: support.into_iter().collect(),
                phase_population: populations
                    .into_iter()
                    .map(
                        |((factor, phase), occurrence_population)| SourceNeutralPhasePopulation {
                            factor,
                            phase,
                            occurrence_population,
                        },
                    )
                    .collect(),
                cell_incidence: incidences
                    .into_iter()
                    .map(|((cell, boundary_position), incidence_population)| {
                        super::source_neutral_relational::SourceNeutralRelationalIncidence {
                            cell,
                            boundary_position,
                            incidence_population,
                        }
                    })
                    .collect(),
            };
            face.address = face_address(class as u32, &face);
            Ok(face)
        })
        .collect()
}

fn quotient_cells(
    developmental: &[ColdCell],
    phase: &[Vec<SourceNeutralPhasePopulation>],
    face_classes: &[u32],
    cell_classes: &[u32],
) -> Result<Vec<SourceNeutralRelationalCell>, SourceNeutralRelationalError> {
    let class_population = cell_classes.iter().copied().max().unwrap_or(0) as usize + 1;
    let mut members = vec![Vec::<usize>::new(); class_population];
    for (cell, class) in cell_classes.iter().copied().enumerate() {
        members[class as usize].push(cell);
    }
    members
        .into_iter()
        .enumerate()
        .map(|(class, members)| {
            let first = *members
                .first()
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            let boundary = oriented_boundary(&developmental[first], face_classes);
            let mut support = BTreeSet::new();
            let mut populations = BTreeMap::<(u32, u8), u64>::new();
            for member in &members {
                if oriented_boundary(&developmental[*member], face_classes) != boundary {
                    return Err(SourceNeutralRelationalError::Quotient);
                }
                support.extend(developmental[*member].factor_support.iter().copied());
                for current in &phase[*member] {
                    let entry = populations
                        .entry((current.factor, current.phase))
                        .or_default();
                    *entry = entry
                        .checked_add(current.occurrence_population)
                        .ok_or(SourceNeutralRelationalError::Extent)?;
                }
            }
            let mut cell = SourceNeutralRelationalCell {
                address: String::new(),
                oriented_boundary: boundary,
                factor_support: support.into_iter().collect(),
                phase_population: populations
                    .into_iter()
                    .map(
                        |((factor, phase), occurrence_population)| SourceNeutralPhasePopulation {
                            factor,
                            phase,
                            occurrence_population,
                        },
                    )
                    .collect(),
            };
            cell.address = cell_address(class as u32, &cell);
            Ok(cell)
        })
        .collect()
}

fn founded_realization_sites(
    relational: &SourceNeutralRelationalMorphology,
) -> Result<Vec<SourceNeutralExteriorRealizationSite>, SourceNeutralRelationalError> {
    let mut raw = Vec::<(u32, u32, u8, u64)>::new();
    for (cell_at, cell) in relational.cells.iter().enumerate() {
        let cell_at = u32::try_from(cell_at).map_err(|_| SourceNeutralRelationalError::Extent)?;
        let positions = relational_boundary_positions(cell.oriented_boundary.len())?;
        for (position, face_at) in cell.oriented_boundary.iter().copied().enumerate() {
            let boundary_position = positions[position];
            let face = relational
                .faces
                .get(face_at as usize)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            let incidence_population = face
                .cell_incidence
                .iter()
                .find(|incidence| {
                    incidence.cell == cell_at && incidence.boundary_position == boundary_position
                })
                .map(|incidence| incidence.incidence_population)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            raw.push((face_at, cell_at, boundary_position, incidence_population));
        }
    }
    raw.sort_unstable();
    if raw.is_empty() || raw.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(SourceNeutralRelationalError::Quotient);
    }
    let addresses = raw
        .iter()
        .enumerate()
        .map(|(site, (_, cell, position, _))| {
            Ok((
                (*cell, *position),
                u32::try_from(site).map_err(|_| SourceNeutralRelationalError::Extent)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, SourceNeutralRelationalError>>()?;
    raw.into_iter()
        .map(|(face, cell, boundary_position, incidence_population)| {
            let boundary = relational
                .cells
                .get(cell as usize)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            let positions = relational_boundary_positions(boundary.oriented_boundary.len())?;
            let at = positions
                .iter()
                .position(|position| *position == boundary_position)
                .ok_or(SourceNeutralRelationalError::Quotient)?;
            let successor_site = positions
                .get(at + 1)
                .map(|next_position| {
                    addresses
                        .get(&(cell, *next_position))
                        .copied()
                        .ok_or(SourceNeutralRelationalError::Quotient)
                })
                .transpose()?;
            Ok(SourceNeutralExteriorRealizationSite {
                face,
                cell,
                boundary_position,
                incidence_population,
                successor_site,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bounded_fixture() -> (serde_json::Value, serde_json::Value) {
        let face_occurrence = serde_json::json!({
            "factor": 0,
            "phase": "ingress",
            "role": {},
            "source_occurrence_identity_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
            "first_delivery_order": 0,
            "last_delivery_order": 0,
            "occurrence_population": 1
        });
        let cell_occurrence = serde_json::json!({
            "factor": 0,
            "phase": "ingress",
            "source_occurrence_identity_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
            "first_delivery_order": 0,
            "last_delivery_order": 0,
            "occurrence_population": 1
        });
        let potential = serde_json::json!({
            "schema": "fixture",
            "factor_addresses": ["factor-0"],
            "factor_adjacency": [],
            "faces": [{
                "address": "face-0",
                "kind": {},
                "founding_delivery_order": 0,
                "founding_clause_order": 0,
                "occurrences": [face_occurrence],
                "factor_support": [0]
            }],
            "cells": [{
                "address": "cell-0",
                "subject": 0,
                "relation": 0,
                "modality": null,
                "object": 0,
                "copular": false,
                "occurrences": [cell_occurrence],
                "factor_support": [0]
            }],
            "obstructed_delivery_population": 0
        });
        let codec = serde_json::json!({
            "schema": "fixture",
            "faces": [{
                "key": {},
                "surface_variants": [["x"]],
                "native_face": 0
            }]
        });
        (potential, codec)
    }

    #[test]
    fn hot_relational_owner_has_no_cold_source_fields() {
        let hot = include_str!("source_neutral_relational.rs");
        assert!(!hot.contains("surface_variants"));
        assert!(!hot.contains("source_occurrence_identity_sha256"));
    }

    #[test]
    fn cold_intake_is_repeatable_on_bounded_fixture() {
        let (potential, codec) = bounded_fixture();
        let first = read_developmental_predecessor(potential.clone(), codec.clone()).unwrap();
        let second = read_developmental_predecessor(potential, codec).unwrap();
        assert_eq!(first.0.identity(), second.0.identity());
        assert_eq!(first.1.identity(), second.1.identity());
        assert_eq!(first.2, second.2);
        assert_eq!(first.0, second.0);
        assert_eq!(first.1, second.1);
    }
}
