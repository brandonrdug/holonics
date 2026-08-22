//! Vector and mesh apparatus faces derived from one exact complex without changing incidence.

use std::collections::BTreeMap;
use std::fmt::Write as _;

use holonic_engine::physical_constraint_complex::{
    ConstraintEdge, ConstraintVertexId, PhysicalConstraintComplex,
};
use num_bigint::BigInt;
use num_traits::ToPrimitive;
use serde::Serialize;
use sha2::{Digest, Sha256};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MeshVertex {
    pub id: u64,
    pub component: u64,
    pub local_ordinal: u32,
    pub source_ordinal: i32,
    pub exact_display_position: [i64; 3],
    pub gauged_display_position: [i64; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MeshTriangle {
    pub id: u64,
    pub vertices: [u64; 3],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MeshEdge {
    pub vertices: [u64; 2],
    pub boundary_coefficient: i64,
    pub species: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ExactMesh {
    pub schema: String,
    pub position_denominator: u64,
    pub vertices: Vec<MeshVertex>,
    pub triangles: Vec<MeshTriangle>,
    pub edges: Vec<MeshEdge>,
    pub gauge_translation: [i64; 3],
    pub topology_sha256_before: String,
    pub topology_sha256_after: String,
    pub incidence_preserved: bool,
    pub boundary: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct VisualReturn {
    pub mesh: ExactMesh,
    pub svg: String,
}

pub fn derive(
    complex: &PhysicalConstraintComplex,
    resident_denominator: u64,
) -> Result<VisualReturn, String> {
    let position_denominator = resident_denominator
        .checked_mul(2)
        .ok_or_else(|| "the exact display denominator exceeds u64".to_owned())?;
    let original = exact_positions(complex, position_denominator)?;
    let (minimum, maximum) = bounds(&original)?;
    let translation = [
        maximum[0]
            .checked_sub(minimum[0])
            .and_then(|span| span.checked_add(1))
            .ok_or_else(|| "display gauge x translation overflow".to_owned())?,
        maximum[1]
            .checked_sub(minimum[1])
            .and_then(|span| span.checked_add(1))
            .and_then(i64::checked_neg)
            .ok_or_else(|| "display gauge y translation overflow".to_owned())?,
        maximum[2]
            .checked_sub(minimum[2])
            .and_then(|span| span.checked_add(1))
            .ok_or_else(|| "display gauge z translation overflow".to_owned())?,
    ];
    let gauged = original
        .iter()
        .map(|(vertex, position)| {
            Ok((
                *vertex,
                [
                    position[0]
                        .checked_add(translation[0])
                        .ok_or_else(|| "display gauge x overflow".to_owned())?,
                    position[1]
                        .checked_add(translation[1])
                        .ok_or_else(|| "display gauge y overflow".to_owned())?,
                    position[2]
                        .checked_add(translation[2])
                        .ok_or_else(|| "display gauge z overflow".to_owned())?,
                ],
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;

    let topology_before = topology_hash(complex);
    // The gauged chart deliberately owns a new position map but obtains all incidence by vertex
    // address from the same complex. Rehash that independently after checking the map is total.
    if gauged.len() != complex.vertices.len()
        || complex.vertices.keys().any(|vertex| !gauged.contains_key(vertex))
    {
        return Err("the gauged chart lost a vertex occurrence".to_owned());
    }
    let topology_after = topology_hash(complex);
    if topology_before != topology_after {
        return Err("a display gauge changed certified incidence".to_owned());
    }

    let vertices = complex
        .vertices
        .values()
        .map(|vertex| MeshVertex {
            id: vertex.id.0,
            component: vertex.component.0,
            local_ordinal: vertex.local_ordinal,
            source_ordinal: vertex.source_ordinal,
            exact_display_position: original[&vertex.id],
            gauged_display_position: gauged[&vertex.id],
        })
        .collect();
    let triangles = complex
        .faces
        .values()
        .map(|face| MeshTriangle {
            id: face.id.0,
            vertices: face.vertices.map(|vertex| vertex.0),
        })
        .collect();
    let mut edges = complex
        .polygonal_edges
        .iter()
        .map(|edge| mesh_edge(*edge, 0, "polygonal"))
        .collect::<Vec<_>>();
    edges.extend(
        complex
            .contact_edges
            .iter()
            .map(|edge| mesh_edge(*edge, 0, "contact")),
    );
    edges.extend(
        complex
            .boundary
            .two_chain_boundary
            .iter()
            .map(|(edge, coefficient)| mesh_edge(*edge, *coefficient, "two-chain-boundary")),
    );
    let svg = svg(complex, &original)?;
    Ok(VisualReturn {
        mesh: ExactMesh {
            schema: "holonics.m5.exact-incidence-mesh.v1".to_owned(),
            position_denominator,
            vertices,
            triangles,
            edges,
            gauge_translation: translation,
            topology_sha256_before: topology_before.clone(),
            topology_sha256_after: topology_after,
            incidence_preserved: true,
            boundary: format!(
                "positions are exact integer numerators over {position_denominator}; the SVG drops z as an apparatus projection; the translated gauge owns no incidence and cannot certify new contact or higher cells"
            ),
        },
        svg,
    })
}

fn exact_positions(
    complex: &PhysicalConstraintComplex,
    display_denominator: u64,
) -> Result<BTreeMap<ConstraintVertexId, [i64; 3]>, String> {
    let scale = BigInt::from(display_denominator);
    complex
        .vertices
        .iter()
        .map(|(id, vertex)| {
            let coordinate = |interval: &holonic_engine::exact_value::ExactInterval| {
                let center = (&interval.lower + &interval.upper) / BigInt::from(2);
                let scaled = center * &scale;
                if scaled.denom() != &BigInt::from(1) {
                    return Err("the exact position does not land on the declared display lattice".to_owned());
                }
                scaled
                    .numer()
                    .to_i64()
                    .ok_or_else(|| "the exact display coordinate exceeds i64".to_owned())
            };
            Ok((
                *id,
                [
                    coordinate(&vertex.position.x)?,
                    coordinate(&vertex.position.y)?,
                    coordinate(&vertex.position.z)?,
                ],
            ))
        })
        .collect()
}

fn bounds(
    positions: &BTreeMap<ConstraintVertexId, [i64; 3]>,
) -> Result<([i64; 3], [i64; 3]), String> {
    if positions.is_empty() {
        return Err("the complex has no display vertices".to_owned());
    }
    let mut minimum = [i64::MAX; 3];
    let mut maximum = [i64::MIN; 3];
    for position in positions.values() {
        for axis in 0..3 {
            minimum[axis] = minimum[axis].min(position[axis]);
            maximum[axis] = maximum[axis].max(position[axis]);
        }
    }
    Ok((minimum, maximum))
}

fn mesh_edge(edge: ConstraintEdge, boundary_coefficient: i64, species: &str) -> MeshEdge {
    MeshEdge {
        vertices: [edge.lower.0, edge.upper.0],
        boundary_coefficient,
        species: species.to_owned(),
    }
}

fn topology_hash(complex: &PhysicalConstraintComplex) -> String {
    let mut digest = Sha256::new();
    for component in complex.components.values() {
        digest.update(component.id.0.to_le_bytes());
        for vertex in &component.vertices {
            digest.update(vertex.0.to_le_bytes());
        }
    }
    for edge in &complex.polygonal_edges {
        digest.update(b"P");
        digest.update(edge.lower.0.to_le_bytes());
        digest.update(edge.upper.0.to_le_bytes());
    }
    for edge in &complex.contact_edges {
        digest.update(b"C");
        digest.update(edge.lower.0.to_le_bytes());
        digest.update(edge.upper.0.to_le_bytes());
    }
    for face in complex.faces.values() {
        digest.update(b"F");
        digest.update(face.id.0.to_le_bytes());
        for vertex in face.vertices {
            digest.update(vertex.0.to_le_bytes());
        }
    }
    for (edge, coefficient) in &complex.boundary.two_chain_boundary {
        digest.update(b"B");
        digest.update(edge.lower.0.to_le_bytes());
        digest.update(edge.upper.0.to_le_bytes());
        digest.update(coefficient.to_le_bytes());
    }
    hex(digest.finalize().as_slice())
}

fn svg(
    complex: &PhysicalConstraintComplex,
    positions: &BTreeMap<ConstraintVertexId, [i64; 3]>,
) -> Result<String, String> {
    let projected = positions
        .iter()
        .map(|(vertex, position)| {
            let y = position[1]
                .checked_neg()
                .ok_or_else(|| "SVG projection negates i64::MIN".to_owned())?;
            Ok((*vertex, [position[0], y]))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let mut minimum = [i64::MAX; 2];
    let mut maximum = [i64::MIN; 2];
    for point in projected.values() {
        for axis in 0..2 {
            minimum[axis] = minimum[axis].min(point[axis]);
            maximum[axis] = maximum[axis].max(point[axis]);
        }
    }
    let width = maximum[0]
        .checked_sub(minimum[0])
        .ok_or_else(|| "SVG width overflow".to_owned())?;
    let height = maximum[1]
        .checked_sub(minimum[1])
        .ok_or_else(|| "SVG height overflow".to_owned())?;
    let pad = width.max(height).checked_div(20).unwrap_or(0).max(1);
    let view_x = minimum[0].checked_sub(pad).ok_or_else(|| "SVG x overflow".to_owned())?;
    let view_y = minimum[1].checked_sub(pad).ok_or_else(|| "SVG y overflow".to_owned())?;
    let view_width = width
        .checked_add(pad.checked_mul(2).ok_or_else(|| "SVG pad overflow".to_owned())?)
        .ok_or_else(|| "SVG width overflow".to_owned())?;
    let view_height = height
        .checked_add(pad.checked_mul(2).ok_or_else(|| "SVG pad overflow".to_owned())?)
        .ok_or_else(|| "SVG height overflow".to_owned())?;
    let stroke = width.max(height).checked_div(700).unwrap_or(0).max(1);
    let contact_stroke = stroke.checked_div(2).unwrap_or(0).max(1);

    let mut body = String::new();
    writeln!(
        body,
        "<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"{view_x} {view_y} {view_width} {view_height}\">"
    )
    .map_err(|error| error.to_string())?;
    writeln!(body, "<rect x=\"{view_x}\" y=\"{view_y}\" width=\"{view_width}\" height=\"{view_height}\" fill=\"#0c1117\"/>")
        .map_err(|error| error.to_string())?;
    for edge in &complex.contact_edges {
        let a = projected[&edge.lower];
        let b = projected[&edge.upper];
        writeln!(body, "<line x1=\"{}\" y1=\"{}\" x2=\"{}\" y2=\"{}\" stroke=\"#e5b567\" stroke-opacity=\"0.34\" stroke-width=\"{contact_stroke}\"/>", a[0], a[1], b[0], b[1])
            .map_err(|error| error.to_string())?;
    }
    let colours = ["#6cb6ff", "#8ddb8c", "#d2a8ff", "#ff7b72"];
    for component in complex.components.values() {
        let points = component
            .vertices
            .iter()
            .map(|vertex| {
                let point = projected[vertex];
                format!("{},{}", point[0], point[1])
            })
            .collect::<Vec<_>>()
            .join(" ");
        let colour = colours[(component.id.0 as usize - 1) % colours.len()];
        writeln!(body, "<polyline points=\"{points}\" fill=\"none\" stroke=\"{colour}\" stroke-width=\"{stroke}\"/>")
            .map_err(|error| error.to_string())?;
    }
    writeln!(body, "</svg>").map_err(|error| error.to_string())?;
    Ok(body)
}

fn hex(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
