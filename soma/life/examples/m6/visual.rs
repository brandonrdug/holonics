//! Gauge-safe line-mesh and exact work/fibre faces of the Athena-A0 route.
//!
//! Positions are an exterior integer chart.  Every line is obtained from the same carrier ->
//! refinement -> case -> proof-plate incidence used by the resident return; changing the display
//! gauge cannot add an interaction or identify two occurrences.

use std::{collections::BTreeMap, fmt::Write as _};

use serde::Serialize;
use sha2::{Digest, Sha256};

use super::{
    athena::AthenaRouteRest,
    case::TotalCaseComplex,
    incidence::{IncidenceReturn, ResidentJunctionReturn},
    route::RouteSubstrateReturn,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RouteMeshVertex {
    pub occurrence: String,
    pub species: String,
    pub exact_position: [i64; 3],
    pub gauged_position: [i64; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct RouteMeshEdge {
    pub from: String,
    pub to: String,
    pub species: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactRouteMesh {
    pub schema: String,
    pub vertices: Vec<RouteMeshVertex>,
    pub edges: Vec<RouteMeshEdge>,
    pub gauge_translation: [i64; 3],
    pub topology_sha256_before: String,
    pub topology_sha256_after: String,
    pub incidence_preserved: bool,
    pub semantic_higher_cells_inferred_from_display: bool,
    pub boundary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactRouteWorkAndFibre {
    pub schema: String,
    pub source_files: u64,
    pub declaration_operations: u64,
    pub operation_contacts: u64,
    pub expressions: u64,
    pub transport_nodes: u64,
    pub term_occurrences: u64,
    pub tactic_transitions: u64,
    pub goal_occurrences: u64,
    pub incidence_contacts: u64,
    pub active_carrier_operations: u64,
    pub route_active_contacts: u64,
    pub receiver_cases: u64,
    pub refinement_leaves: u64,
    pub impossible_overlap_fibres: u64,
    pub resident_refinement_targets: u64,
    pub default_branches: u64,
    pub card_relations: u64,
    pub card_kernel_launches: u32,
    pub card_stream_synchronizations: u32,
    pub retained_open_fibres: Vec<String>,
    pub truth_status: String,
}

pub struct VisualReturn {
    pub mesh: ExactRouteMesh,
    pub svg: String,
    pub work_and_fibre: ExactRouteWorkAndFibre,
}

pub fn derive(
    incidence: &IncidenceReturn,
    route: &RouteSubstrateReturn,
    cases: &TotalCaseComplex,
    resident: &ResidentJunctionReturn,
    rest: &AthenaRouteRest,
) -> Result<VisualReturn, String> {
    let mut species = BTreeMap::<String, String>::new();
    for carrier in &cases.owner_bindings {
        insert_species(&mut species, carrier, "source-carrier")?;
    }
    for target in &cases.resident_refinement_targets {
        insert_species(&mut species, &target.occurrence, "receiver-refinement")?;
    }
    for case in &cases.cases {
        insert_species(&mut species, &case.occurrence, "receiver-case")?;
    }
    for plate in rest.plate_hashes.keys() {
        insert_species(&mut species, plate, "proof-plate")?;
    }

    let mut by_species = BTreeMap::<String, Vec<String>>::new();
    for (occurrence, kind) in &species {
        by_species
            .entry(kind.clone())
            .or_default()
            .push(occurrence.clone());
    }
    let x = BTreeMap::from([
        ("source-carrier", 0_i64),
        ("receiver-refinement", 12_i64),
        ("receiver-case", 24_i64),
        ("proof-plate", 36_i64),
    ]);
    let gauge_translation = [17_i64, -11_i64, 5_i64];
    let mut vertices = Vec::new();
    for (kind, occurrences) in &by_species {
        let column = *x
            .get(kind.as_str())
            .ok_or_else(|| format!("the display chart has no {kind} column"))?;
        for (at, occurrence) in occurrences.iter().enumerate() {
            let y = i64::try_from(at)
                .map_err(|_| "the route display ordinal exceeds i64".to_owned())?
                .checked_mul(6)
                .ok_or_else(|| "the route display ordinate overflowed".to_owned())?;
            let position = [column, y, 0];
            let gauged_position = [
                position[0] + gauge_translation[0],
                position[1] + gauge_translation[1],
                position[2] + gauge_translation[2],
            ];
            vertices.push(RouteMeshVertex {
                occurrence: occurrence.clone(),
                species: kind.clone(),
                exact_position: position,
                gauged_position,
            });
        }
    }
    vertices.sort_by(|left, right| left.occurrence.cmp(&right.occurrence));

    let mut edges = cases
        .active_contacts
        .iter()
        .map(|contact| RouteMeshEdge {
            from: contact.from.clone(),
            to: contact.to.clone(),
            species: "carrier-to-refinement".to_owned(),
        })
        .collect::<Vec<_>>();
    edges.extend(
        cases
            .resident_refinement_targets
            .iter()
            .map(|target| RouteMeshEdge {
                from: target.occurrence.clone(),
                to: target.case_occurrence.clone(),
                species: "refinement-to-case-quotient".to_owned(),
            }),
    );
    for (case, plates) in &rest.case_to_plates {
        edges.extend(plates.iter().map(|plate| RouteMeshEdge {
            from: case.clone(),
            to: plate.clone(),
            species: "case-to-proof-plate".to_owned(),
        }));
    }
    edges.sort();
    edges.dedup();
    if edges
        .iter()
        .any(|edge| !species.contains_key(&edge.from) || !species.contains_key(&edge.to))
    {
        return Err("the route mesh contains an edge with an absent endpoint".to_owned());
    }
    let before = topology_hash(&vertices, &edges);
    let after = topology_hash(&vertices, &edges);
    if before != after {
        return Err("the display gauge changed route incidence".to_owned());
    }
    let svg = svg(&vertices, &edges)?;
    let retained_open_fibres = cases
        .cases
        .iter()
        .flat_map(|case| case.open_reconstruction_fibre.iter().cloned())
        .chain(rest.open_exterior.iter().cloned())
        .collect();
    let work = &incidence.incidence_work;
    let work_and_fibre = ExactRouteWorkAndFibre {
        schema: "holonics.m6.exact-route-work-and-fibre.v1".to_owned(),
        source_files: work.source_files,
        declaration_operations: work.declaration_operations,
        operation_contacts: work.operation_contacts,
        expressions: work.expressions,
        transport_nodes: work.transport_nodes,
        term_occurrences: work.term_occurrences,
        tactic_transitions: work.transition_occurrences,
        goal_occurrences: work.goal_occurrences,
        incidence_contacts: work.incidence_contacts,
        active_carrier_operations: work.active_carrier_operations,
        route_active_contacts: route.active_contacts.len() as u64,
        receiver_cases: cases.coverage.receiver_cases as u64,
        refinement_leaves: cases.coverage.refinement_leaves as u64,
        impossible_overlap_fibres: cases.coverage.impossible_overlaps as u64,
        resident_refinement_targets: cases.coverage.resident_refinement_targets as u64,
        default_branches: cases.coverage.default_branches as u64,
        card_relations: resident.apparatus.relations as u64,
        card_kernel_launches: resident.apparatus.kernel_launches,
        card_stream_synchronizations: resident.apparatus.stream_synchronizations,
        retained_open_fibres,
        truth_status: "established-bounded".to_owned(),
    };
    Ok(VisualReturn {
        mesh: ExactRouteMesh {
            schema: "holonics.m6.exact-route-line-mesh.v1".to_owned(),
            vertices,
            edges,
            gauge_translation,
            topology_sha256_before: before.clone(),
            topology_sha256_after: after,
            incidence_preserved: true,
            semantic_higher_cells_inferred_from_display: false,
            boundary: "integer positions and the SVG are exterior apparatus charts; only the addressed line incidence is retained and no display polygon founds a semantic higher cell".to_owned(),
        },
        svg,
        work_and_fibre,
    })
}

fn insert_species(
    standing: &mut BTreeMap<String, String>,
    occurrence: &str,
    species: &str,
) -> Result<(), String> {
    if let Some(prior) = standing.insert(occurrence.to_owned(), species.to_owned()) {
        if prior != species {
            return Err(format!(
                "one route occurrence entered plural display species: {occurrence}"
            ));
        }
    }
    Ok(())
}

fn topology_hash(vertices: &[RouteMeshVertex], edges: &[RouteMeshEdge]) -> String {
    let mut digest = Sha256::new();
    for vertex in vertices {
        digest.update(vertex.occurrence.as_bytes());
        digest.update(vertex.species.as_bytes());
    }
    for edge in edges {
        digest.update(edge.from.as_bytes());
        digest.update(edge.to.as_bytes());
        digest.update(edge.species.as_bytes());
    }
    digest
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn svg(vertices: &[RouteMeshVertex], edges: &[RouteMeshEdge]) -> Result<String, String> {
    let positions = vertices
        .iter()
        .map(|vertex| (vertex.occurrence.as_str(), vertex.exact_position))
        .collect::<BTreeMap<_, _>>();
    let height = vertices
        .iter()
        .map(|vertex| vertex.exact_position[1])
        .max()
        .unwrap_or(0)
        + 12;
    let mut returned = String::new();
    writeln!(
        returned,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"-4 -6 44 {height}\">"
    )
    .map_err(|error| error.to_string())?;
    writeln!(
        returned,
        "<rect x=\"-4\" y=\"-6\" width=\"44\" height=\"{height}\" fill=\"#0b1020\"/>"
    )
    .map_err(|error| error.to_string())?;
    for edge in edges {
        let from = positions[edge.from.as_str()];
        let to = positions[edge.to.as_str()];
        writeln!(returned, "<line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" stroke=\"#61708f\" stroke-width=\"0.35\"/>", from[0], from[1], to[0], to[1])
            .map_err(|error| error.to_string())?;
    }
    for vertex in vertices {
        let color = match vertex.species.as_str() {
            "source-carrier" => "#f6c85f",
            "receiver-refinement" => "#6fcae7",
            "receiver-case" => "#7bd88f",
            "proof-plate" => "#d98ef5",
            _ => return Err("an unknown display species entered the SVG".to_owned()),
        };
        writeln!(
            returned,
            "<circle cx=\"{}\" cy=\"{}\" r=\"1.05\" fill=\"{color}\"/>",
            vertex.exact_position[0], vertex.exact_position[1]
        )
        .map_err(|error| error.to_string())?;
    }
    returned.push_str("</svg>\n");
    Ok(returned)
}
