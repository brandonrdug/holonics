use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use relational_geometry::{
    ConstraintKind, Construction, DiagramNodeKind, ExactPolynomial, Geometry, Rat, RatVec3,
    Receiver, ReceiverId, ReceiverOrientation, ReceiverTopology, SourceEndpoint,
    analyze_receiver_topology, format_rat, integer, rat,
};

struct TetrahedralState {
    construction: Construction,
    vertices: [RatVec3; 4],
}

const EDGE_VERTICES: [(usize, usize, &str); 6] = [
    (0, 1, "AB"),
    (0, 2, "AC"),
    (0, 3, "AD"),
    (1, 2, "BC"),
    (1, 3, "BD"),
    (2, 3, "CD"),
];

fn build_state(d_height: Rat) -> TetrahedralState {
    let vertices = [
        RatVec3::from_i64(0, 0, 0),
        RatVec3::from_i64(4, 0, 0),
        RatVec3::from_i64(0, 4, 0),
        RatVec3::new(integer(1), integer(1), d_height),
    ];
    let (mut construction, frame) = Construction::new("tetrahedral incidence");
    let mut edge_entities = Vec::new();
    for (left, right, name) in EDGE_VERTICES {
        let entity = construction
            .add_entity(
                format!("edge {name}"),
                frame,
                Geometry::Thread {
                    vertices: vec![vertices[left].clone(), vertices[right].clone()],
                    closed: false,
                },
            )
            .expect("the one source frame exists");
        edge_entities.push(entity);
    }

    for abstract_vertex in 0..4 {
        let members = EDGE_VERTICES
            .iter()
            .enumerate()
            .filter_map(|(edge_index, (left, right, _))| {
                if *left == abstract_vertex {
                    Some(SourceEndpoint {
                        entity: edge_entities[edge_index],
                        vertex: 0,
                    })
                } else if *right == abstract_vertex {
                    Some(SourceEndpoint {
                        entity: edge_entities[edge_index],
                        vertex: 1,
                    })
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        for pair in members.windows(2) {
            construction.add_constraint(
                format!(
                    "vertex {} retains one source incidence",
                    ["A", "B", "C", "D"][abstract_vertex]
                ),
                ConstraintKind::SharedVertex {
                    left: pair[0].entity,
                    right: pair[1].entity,
                    left_vertex: pair[0].vertex,
                    right_vertex: pair[1].vertex,
                },
            );
        }
    }
    TetrahedralState {
        construction,
        vertices,
    }
}

fn receiver_family() -> [Receiver; 2] {
    let frame = relational_geometry::FrameId(1);
    let direct = Receiver::new(
        ReceiverId(1),
        "direct incidence face",
        frame,
        relational_geometry::ProjectionLaw::Orthographic,
    );
    let mut precessed = Receiver::new(
        ReceiverId(2),
        "precessed crossing face",
        frame,
        relational_geometry::ProjectionLaw::Orthographic,
    );
    precessed.orientation =
        ReceiverOrientation::from_cayley_xyz(rat(-1, 2), rat(-1, 2), Rat::zero());
    [direct, precessed]
}

fn volume_witness(vertices: &[RatVec3; 4]) -> Rat {
    let ab = vertices[1].subtract(&vertices[0]);
    let ac = vertices[2].subtract(&vertices[0]);
    let ad = vertices[3].subtract(&vertices[0]);
    ab.cross(&ac).dot(&ad)
}

fn edge_metric(vertices: &[RatVec3; 4]) -> Vec<(&'static str, Rat)> {
    EDGE_VERTICES
        .iter()
        .map(|(left, right, name)| {
            (
                *name,
                vertices[*right].subtract(&vertices[*left]).norm_squared(),
            )
        })
        .collect()
}

fn format_polynomial(polynomial: &ExactPolynomial) -> String {
    let mut terms = Vec::new();
    for (degree, coefficient) in polynomial.coefficients.iter().enumerate().rev() {
        if coefficient.is_zero() {
            continue;
        }
        let magnitude = coefficient.abs();
        let body = match degree {
            0 => magnitude.to_string(),
            1 if magnitude == BigInt::from(1) => "u".to_owned(),
            1 => format!("{magnitude}u"),
            _ if magnitude == BigInt::from(1) => format!("u^{degree}"),
            _ => format!("{magnitude}u^{degree}"),
        };
        if terms.is_empty() {
            terms.push(if coefficient.is_negative() {
                format!("-{body}")
            } else {
                body
            });
        } else if coefficient.is_negative() {
            terms.push(format!("- {body}"));
        } else {
            terms.push(format!("+ {body}"));
        }
    }
    if terms.is_empty() {
        "0".to_owned()
    } else {
        terms.join(" ")
    }
}

fn format_primitive_cycles(topology: &ReceiverTopology) -> String {
    topology
        .face_dual_ihara
        .primitive_oriented_cycles
        .iter()
        .enumerate()
        .filter(|(_, count)| !count.is_zero())
        .map(|(index, count)| format!("l{}={count}", index + 1))
        .collect::<Vec<_>>()
        .join(", ")
}

fn print_topology(label: &str, topology: &ReceiverTopology) {
    println!("{label}");
    println!(
        "  source V/E = {}/{} · diagram V/E/F = {}/{}/{} · apparent crossings = {}",
        topology.source_graph.vertex_count,
        topology.source_graph.edges.len(),
        topology.nodes.len(),
        topology.edges.len(),
        topology.faces.len(),
        topology.apparent_crossing_count()
    );
    for node in &topology.nodes {
        if let DiagramNodeKind::ApparentCrossing {
            first,
            second,
            over,
            orientation,
            first_source_parameter,
            second_source_parameter,
        } = &node.kind
        {
            println!(
                "  crossing ({},{})@{} x ({},{})@{} at ({},{}) · over ({},{}) · orientation {}",
                first.entity.0,
                first.segment,
                format_rat(first_source_parameter),
                second.entity.0,
                second.segment,
                format_rat(second_source_parameter),
                format_rat(&node.point.x),
                format_rat(&node.point.y),
                over.entity.0,
                over.segment,
                orientation
            );
        }
    }
    for face in &topology.faces {
        let boundary = face
            .boundary
            .iter()
            .map(|dart| {
                let edge = &topology.edges[dart.edge.0 as usize - 1];
                format!(
                    "({}:{}@{}{})",
                    edge.source.entity.0,
                    edge.source.segment,
                    edge.id.0,
                    if dart.forward { "+" } else { "-" }
                )
            })
            .collect::<Vec<_>>()
            .join(" ");
        println!(
            "  face {} · {} · signed 2-area {} · {}",
            face.id.0,
            if face.bounded { "bounded" } else { "outer" },
            format_rat(&face.signed_double_area),
            boundary
        );
    }
    println!(
        "  source Z^-1 = {}",
        format_polynomial(&topology.source_ihara.reciprocal)
    );
    println!(
        "  receiver-dual Z^-1 = {}",
        format_polynomial(&topology.face_dual_ihara.reciprocal)
    );
    println!(
        "  receiver-dual primitive loops: {}",
        format_primitive_cycles(topology)
    );
    println!();
}

fn main() {
    let before = build_state(integer(1));
    let after = build_state(rat(1, 4));
    let [direct, precessed] = receiver_family();
    let direct_before = analyze_receiver_topology(&before.construction, &direct, 8)
        .expect("direct face is regular");
    let precessed_before = analyze_receiver_topology(&before.construction, &precessed, 8)
        .expect("precessed face is regular");
    let precessed_after = analyze_receiver_topology(&after.construction, &precessed, 8)
        .expect("emanated face is regular");

    println!("RECEIVER TOPOLOGY ATLAS 01");
    println!("one source incidence · receiver precession · one source emanation");
    println!();
    println!(
        "SOURCE GEOMETRY · volume witness {} -> {}",
        format_rat(&volume_witness(&before.vertices)),
        format_rat(&volume_witness(&after.vertices))
    );
    let before_metric = edge_metric(&before.vertices);
    let after_metric = edge_metric(&after.vertices);
    for ((name, before), (_, after)) in before_metric.iter().zip(after_metric.iter()) {
        println!(
            "  {name} squared length {} -> {}{}",
            format_rat(before),
            format_rat(after),
            if before == after {
                " · retained"
            } else {
                " · changed"
            }
        );
    }
    println!();

    print_topology("CUT A · before source · direct receiver", &direct_before);
    print_topology(
        "CUT B · same before source · precessed receiver",
        &precessed_before,
    );
    print_topology(
        "CUT C · emanated source · same precessed receiver",
        &precessed_after,
    );

    println!("RELATIONAL COMPARISON");
    println!(
        "  source incidence zeta A=B=C: {}",
        direct_before.source_ihara == precessed_before.source_ihara
            && precessed_before.source_ihara == precessed_after.source_ihara
    );
    println!(
        "  raw receiver-dual zeta A=B: {}",
        direct_before.face_dual_ihara == precessed_before.face_dual_ihara
    );
    println!(
        "  raw receiver-dual zeta A=C: {}",
        direct_before.face_dual_ihara == precessed_after.face_dual_ihara
    );
    println!(
        "  raw receiver-dual zeta B=C: {}",
        precessed_before.face_dual_ihara == precessed_after.face_dual_ihara
    );
}
