//! Assert Ihara's theorem against the signature the receiver topology already
//! returns, and read the source graph and the face-dual graph as two frames.
//!
//! `IharaSignature` carries `det(I - uB)` on the spectral side and the
//! primitive closed-geodesic counts on the string side. Ihara's theorem says
//! the two determine each other:
//!
//! ```text
//!   Z(u)^-1  =  det(I - uB)  =  prod over primitive closed geodesics [P] (1 - u^len(P))
//! ```
//!
//! Nothing asserted it. This driver expands the Euler product truncated to the
//! caller-declared horizon, compares it coefficient by coefficient against the
//! determinant, states how many coefficients the horizon determines and how
//! many it withholds, and then breaks the comparison on purpose so the
//! agreement is evidence rather than an accident of shape.

use num_bigint::BigInt;
use num_traits::{Signed, Zero};

use relational_geometry::{
    ConstraintKind, Construction, ExactMultiGraph, ExactPolynomial, GraphEdge, IharaCrossCheck,
    Rat, RatVec3, Receiver, ReceiverId, ReceiverOrientation, ReceiverTopology,
    TwoFrameIharaReading, analyze_receiver_topology, cross_check_ihara,
    cross_check_ihara_perturbed, diagram_graph, ihara_signature, integer, rat,
};

fn format_window(window: &[BigInt]) -> String {
    let mut terms = Vec::new();
    for (degree, coefficient) in window.iter().enumerate().rev() {
        if coefficient.is_zero() {
            continue;
        }
        let magnitude = coefficient.abs();
        let unit = magnitude == BigInt::from(1);
        let body = match degree {
            0 => magnitude.to_string(),
            1 if unit => "u".to_owned(),
            1 => format!("{magnitude}u"),
            _ if unit => format!("u^{degree}"),
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

fn format_polynomial(polynomial: &ExactPolynomial) -> String {
    format_window(&polynomial.coefficients)
}

fn format_cycles(counts: &[BigInt]) -> String {
    let named = counts
        .iter()
        .enumerate()
        .filter(|(_, count)| !count.is_zero())
        .map(|(index, count)| format!("N_{}={count}", index + 1))
        .collect::<Vec<_>>();
    if named.is_empty() {
        "none inside the horizon".to_owned()
    } else {
        named.join("  ")
    }
}

fn print_cross_check(indent: &str, check: &IharaCrossCheck) {
    println!(
        "{indent}horizon {} · determinant degree {} · compared {} coefficients · withheld {}",
        check.horizon,
        check.reciprocal_degree,
        check.compared_coefficients,
        check.withheld_coefficients
    );
    println!(
        "{indent}det(I - uB)        [0..={}] = {}",
        check.horizon,
        format_window(&check.reciprocal_window)
    );
    println!(
        "{indent}prod (1 - u^l)^N_l [0..={}] = {}",
        check.horizon,
        format_window(&check.euler_product_window)
    );
    match check.first_disagreement {
        None => println!("{indent}IDENTITY HOLDS on every compared coefficient",),
        Some(degree) => println!(
            "{indent}DISAGREES first at degree {degree}: determinant {} · product {}",
            check.reciprocal_window[degree], check.euler_product_window[degree]
        ),
    }
}

fn declared_graph(
    name: &str,
    vertex_count: usize,
    pairs: &[(usize, usize)],
) -> (String, ExactMultiGraph) {
    (
        name.to_owned(),
        ExactMultiGraph {
            vertex_count,
            edges: pairs
                .iter()
                .enumerate()
                .map(|(index, (left, right))| GraphEdge {
                    left: *left,
                    right: *right,
                    source: format!("{left}-{right}#{index}"),
                })
                .collect(),
        },
    )
}

fn complete_graph(name: &str, vertex_count: usize) -> (String, ExactMultiGraph) {
    let mut pairs = Vec::new();
    for left in 0..vertex_count {
        for right in (left + 1)..vertex_count {
            pairs.push((left, right));
        }
    }
    declared_graph(name, vertex_count, &pairs)
}

fn cycle_graph(name: &str, vertex_count: usize) -> (String, ExactMultiGraph) {
    let pairs = (0..vertex_count)
        .map(|left| (left, (left + 1) % vertex_count))
        .collect::<Vec<_>>();
    declared_graph(name, vertex_count, &pairs)
}

fn complete_bipartite(
    name: &str,
    left_count: usize,
    right_count: usize,
) -> (String, ExactMultiGraph) {
    let mut pairs = Vec::new();
    for left in 0..left_count {
        for right in 0..right_count {
            pairs.push((left, left_count + right));
        }
    }
    declared_graph(name, left_count + right_count, &pairs)
}

fn petersen() -> (String, ExactMultiGraph) {
    let mut pairs = Vec::new();
    for index in 0..5 {
        pairs.push((index, (index + 1) % 5));
        pairs.push((index, 5 + index));
        pairs.push((5 + index, 5 + (index + 2) % 5));
    }
    declared_graph("Petersen", 10, &pairs)
}

/// The two-vertex multigraph with `edge_count` parallel edges. This is the
/// planar face-dual of the cycle on `edge_count` vertices, and it is here so
/// the declared family contains the dual of one of its own members.
fn dipole(name: &str, edge_count: usize) -> (String, ExactMultiGraph) {
    let pairs = (0..edge_count)
        .map(|_| (0usize, 1usize))
        .collect::<Vec<_>>();
    declared_graph(name, 2, &pairs)
}

fn declared_family() -> Vec<(String, ExactMultiGraph)> {
    vec![
        cycle_graph("C4 · the four-cycle", 4),
        dipole("B4 · four parallel edges", 4),
        cycle_graph("C5 · the five-cycle", 5),
        complete_graph("K4", 4),
        complete_bipartite("K3,3", 3, 3),
        complete_graph("K5", 5),
        petersen(),
        // A pendant vertex is on no closed geodesic. It is here to decide
        // whether the determinant's degree is 2|E| or 2|E| of the two-core,
        // rather than to let the family agree by carrying only 2-regular-or-
        // better material.
        declared_graph(
            "triangle with a pendant edge",
            4,
            &[(0, 1), (1, 2), (2, 0), (0, 3)],
        ),
        declared_graph(
            "two triangles joined by a path",
            7,
            &[
                (0, 1),
                (1, 2),
                (2, 0),
                (2, 3),
                (3, 4),
                (4, 5),
                (5, 6),
                (6, 4),
            ],
        ),
    ]
}

fn section_the_identity() {
    println!("== 1 · THE IDENTITY, AT A HORIZON THAT WITHHOLDS NOTHING ==");
    println!();
    println!("The horizon is declared as 2|E|, which BOUNDS the degree of det(I - uB).");
    println!("Every coefficient the determinant carries is therefore compared. The bound");
    println!("is not always attained, and the triangle-with-a-pendant-edge member is here");
    println!("to say so: a pendant vertex lies on no closed geodesic, the leading");
    println!("coefficient prod(deg - 1) vanishes, and the degree is 2|E| of the two-core.");
    println!();
    for (name, graph) in declared_family() {
        let horizon = 2 * graph.edges.len();
        let signature = match ihara_signature(&graph, horizon) {
            Ok(signature) => signature,
            Err(error) => {
                println!("{name}: refused · {error}");
                println!();
                continue;
            }
        };
        let check = cross_check_ihara(&signature);
        println!(
            "{name} · V={} E={} · cycle rank {} · 2|E| = {} · det degree = {}{}",
            graph.vertex_count,
            graph.edges.len(),
            graph.edges.len() + 1 - graph.vertex_count,
            horizon,
            check.reciprocal_degree,
            if check.reciprocal_degree == horizon {
                ""
            } else {
                "  <- BELOW 2|E|"
            }
        );
        println!(
            "  primitive oriented closed geodesics: {}",
            format_cycles(&signature.primitive_oriented_cycles)
        );
        print_cross_check("  ", &check);
        println!();
    }
}

fn section_the_third_route() {
    println!("== 1b · A THIRD ROUTE, OUTSIDE THIS BODY ==");
    println!();
    println!("Two routes inside one body agreeing with each other is weaker evidence than");
    println!("either agreeing with a source neither produced. Terras gives the Ihara zeta");
    println!("of K4 in factored form; the factors are multiplied out here and compared.");
    println!();
    let factored = ExactPolynomial::from_coefficients(vec![
        BigInt::from(1),
        BigInt::from(0),
        BigInt::from(-1),
    ])
    .pow(2)
    .multiply(&ExactPolynomial::from_coefficients(vec![
        BigInt::from(1),
        BigInt::from(-1),
    ]))
    .multiply(&ExactPolynomial::from_coefficients(vec![
        BigInt::from(1),
        BigInt::from(-2),
    ]))
    .multiply(
        &ExactPolynomial::from_coefficients(vec![
            BigInt::from(1),
            BigInt::from(1),
            BigInt::from(2),
        ])
        .pow(3),
    );
    let (_, graph) = complete_graph("K4", 4);
    let signature = ihara_signature(&graph, 12).expect("K4 is inside the cut");
    println!(
        "  (1-u^2)^2 (1-u)(1-2u)(1+u+2u^2)^3 = {}",
        format_polynomial(&factored)
    );
    println!(
        "  det(I - uB)                        = {}",
        format_polynomial(&signature.reciprocal)
    );
    println!(
        "  prod (1 - u^l)^N_l                 = {}",
        format_window(&cross_check_ihara(&signature).euler_product_window)
    );
    println!(
        "  three routes agree: {}",
        factored == signature.reciprocal && cross_check_ihara(&signature).agrees()
    );
    println!();
}

fn section_the_horizon() {
    println!("== 2 · WHAT THE HORIZON DETERMINES ==");
    println!();
    println!("K4 again, with the caller-declared horizon swept from 1 upward.");
    println!("prod_{{l>H}} (1 - u^l)^N_l is 1 + O(u^(H+1)), so the truncated product");
    println!("is congruent to the determinant modulo u^(H+1) and says nothing above.");
    println!();
    let (_, graph) = complete_graph("K4", 4);
    for horizon in 1..=14usize {
        let signature = ihara_signature(&graph, horizon).expect("K4 is inside the cut");
        let check = cross_check_ihara(&signature);
        println!(
            "  H={horizon:<3} compared {:<3} withheld {:<3} agrees {:<5} product[0..=H] = {}",
            check.compared_coefficients,
            check.withheld_coefficients,
            check.agrees(),
            format_window(&check.euler_product_window)
        );
    }
    println!();
    println!("  Above the horizon the truncated product is simply wrong, which is why");
    println!("  those coefficients are withheld rather than compared. At H=3 the product");
    println!("  over the eight primitive triangles alone is:");
    let signature = ihara_signature(&graph, 3).expect("K4 is inside the cut");
    let full = ihara_signature(&graph, 12).expect("K4 is inside the cut");
    println!(
        "    (1 - u^3)^8                 = {}",
        format_window(&relational_geometry::ihara_euler_product_window(
            &signature.primitive_oriented_cycles
        ))
    );
    println!(
        "    det(I - uB)                 = {}",
        format_polynomial(&full.reciprocal)
    );
    println!("  agreeing on degrees 0..=3 and diverging at degree 4, as declared.");
    println!();
}

fn section_the_falsifier() {
    println!("== 3 · THE FALSIFIER ==");
    println!();
    println!("A comparison that could not fail carries no evidence. Perturbing one");
    println!("primitive-cycle count by one multiplies the product by (1 - u^l)^delta,");
    println!("and since the product's constant coefficient is one, the coefficient at");
    println!("degree l moves by exactly -delta. The break is therefore predicted, and");
    println!("its position identifies the perturbed length.");
    println!();
    let (_, graph) = complete_graph("K4", 4);
    let signature = ihara_signature(&graph, 12).expect("K4 is inside the cut");
    let clean = cross_check_ihara(&signature);
    println!(
        "  unperturbed: first disagreement {:?}",
        clean.first_disagreement
    );
    println!();
    for length in 1..=12usize {
        let mut cells = Vec::new();
        for delta in [1i64, -1] {
            let broken = cross_check_ihara_perturbed(&signature, &[(length, delta)]);
            let moved = &broken.euler_product_window[length] - &clean.euler_product_window[length];
            cells.push(format!(
                "N_{length}{:+} -> first disagreement {:?}, coefficient moved by {moved}",
                delta, broken.first_disagreement
            ));
        }
        println!("  {}", cells.join("   |   "));
    }
    println!();
    let broken = cross_check_ihara_perturbed(&signature, &[(3, 1)]);
    println!("  One break printed in full, N_3 = 8 -> 9:");
    print_cross_check("    ", &broken);
    println!();
    let outside = cross_check_ihara_perturbed(
        &ihara_signature(&graph, 5).expect("K4 is inside the cut"),
        &[(9, 1)],
    );
    println!(
        "  Negative control · perturbing N_9 at horizon 5 is outside the compared window: agrees {}",
        outside.agrees()
    );
    println!();
}

fn print_frame(reading: &TwoFrameIharaReading) {
    for frame in [&reading.source, &reading.face_dual] {
        println!(
            "  {} · V={} E={} · cycle rank {} · det degree {}",
            frame.frame,
            frame.vertex_count,
            frame.edge_count,
            frame.cycle_rank,
            frame.reciprocal_degree
        );
        println!("    Z^-1 = {}", format_polynomial(&frame.reciprocal));
        println!(
            "    geodesics: {}",
            format_cycles(&frame.primitive_oriented_cycles)
        );
        print_cross_check("    ", &frame.cross_check);
    }
    println!(
        "  apparent crossings {} · diagram V={} E={} cycle rank {} · source graph is the diagram graph: {}",
        reading.apparent_crossings,
        reading.diagram_vertex_count,
        reading.diagram_edge_count,
        reading.diagram_cycle_rank,
        reading.source_graph_is_diagram_graph
    );
    println!(
        "  INVARIANT · cycle rank(diagram) + cycle rank(face dual) = {} + {} = {} · equals |E| = {}",
        reading.diagram_cycle_rank,
        reading.face_dual.cycle_rank,
        reading.dual_cycle_rank_sum,
        reading.dual_cycle_rank_sum_is_edge_count
    );
    println!(
        "  INVARIANT · the identity holds in both frames: {} and {}",
        reading.source.cross_check.agrees(),
        reading.face_dual.cross_check.agrees()
    );
    println!(
        "  MOVES · det degrees agree: {} · reciprocals first differ at degree {:?} · geodesic counts first differ at length {:?}",
        reading.reciprocal_degrees_agree,
        reading.first_reciprocal_difference,
        reading.first_cycle_count_difference
    );
    println!();
}

fn square_construction() -> (Construction, Receiver) {
    let (mut construction, frame) = Construction::new("square");
    construction
        .add_entity(
            "closed square",
            frame,
            relational_geometry::Geometry::Thread {
                vertices: vec![
                    RatVec3::from_i64(-1, -1, 0),
                    RatVec3::from_i64(1, -1, 0),
                    RatVec3::from_i64(1, 1, 0),
                    RatVec3::from_i64(-1, 1, 0),
                ],
                closed: true,
            },
        )
        .expect("the one source frame exists");
    let receiver = Receiver::new(
        ReceiverId(1),
        "square receiver",
        frame,
        relational_geometry::ProjectionLaw::Orthographic,
    );
    (construction, receiver)
}

fn bowtie_construction() -> (Construction, Receiver) {
    let (mut construction, frame) = Construction::new("apparent crossing");
    construction
        .add_entity(
            "self-crossing closed thread",
            frame,
            relational_geometry::Geometry::Thread {
                vertices: vec![
                    RatVec3::from_i64(0, 0, 0),
                    RatVec3::from_i64(2, 2, 0),
                    RatVec3::from_i64(2, 0, 1),
                    RatVec3::from_i64(0, 2, 1),
                ],
                closed: true,
            },
        )
        .expect("the one source frame exists");
    let receiver = Receiver::new(
        ReceiverId(1),
        "crossing receiver",
        frame,
        relational_geometry::ProjectionLaw::Orthographic,
    );
    (construction, receiver)
}

const TETRAHEDRON_EDGES: [(usize, usize, &str); 6] = [
    (0, 1, "AB"),
    (0, 2, "AC"),
    (0, 3, "AD"),
    (1, 2, "BC"),
    (1, 3, "BD"),
    (2, 3, "CD"),
];

fn tetrahedron_construction() -> Construction {
    let vertices = [
        RatVec3::from_i64(0, 0, 0),
        RatVec3::from_i64(4, 0, 0),
        RatVec3::from_i64(0, 4, 0),
        RatVec3::new(integer(1), integer(1), integer(1)),
    ];
    let (mut construction, frame) = Construction::new("tetrahedral incidence");
    let mut edge_entities = Vec::new();
    for (left, right, name) in TETRAHEDRON_EDGES {
        let entity = construction
            .add_entity(
                format!("edge {name}"),
                frame,
                relational_geometry::Geometry::Thread {
                    vertices: vec![vertices[left].clone(), vertices[right].clone()],
                    closed: false,
                },
            )
            .expect("the one source frame exists");
        edge_entities.push(entity);
    }
    for abstract_vertex in 0..4 {
        let members = TETRAHEDRON_EDGES
            .iter()
            .enumerate()
            .filter_map(|(edge_index, (left, right, _))| {
                if *left == abstract_vertex {
                    Some(relational_geometry::SourceEndpoint {
                        entity: edge_entities[edge_index],
                        vertex: 0,
                    })
                } else if *right == abstract_vertex {
                    Some(relational_geometry::SourceEndpoint {
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
                format!("vertex {abstract_vertex} retains one source incidence"),
                ConstraintKind::SharedVertex {
                    left: pair[0].entity,
                    right: pair[1].entity,
                    left_vertex: pair[0].vertex,
                    right_vertex: pair[1].vertex,
                },
            );
        }
    }
    construction
}

fn section_two_frames() {
    println!("== 4 · TWO FRAMES ON ONE CONSTRUCTION ==");
    println!();
    println!("analyze_receiver_topology computes an Ihara signature for the source");
    println!("graph and one for the face-dual graph, and nothing compared them.");
    println!("The face dual is dual to the DIAGRAM graph, which is the source graph");
    println!("only when the receiver reports no apparent crossing.");
    println!();

    let (construction, receiver) = square_construction();
    let topology = analyze_receiver_topology(&construction, &receiver, 12).expect("regular face");
    println!("-- the closed square, orthographic · C4 against its planar dual --");
    print_frame(&topology.two_frame_ihara_reading());

    let (construction, receiver) = bowtie_construction();
    let topology = analyze_receiver_topology(&construction, &receiver, 12).expect("regular face");
    println!("-- a self-crossing closed thread · one apparent crossing --");
    print_frame(&topology.two_frame_ihara_reading());
    let diagram = diagram_graph(&topology);
    let diagram_signature = ihara_signature(&diagram, 12).expect("the diagram is inside the cut");
    println!(
        "  the frame the face dual IS dual to · diagram V={} E={} · det degree {} · identity holds {}",
        diagram.vertex_count,
        diagram.edges.len(),
        diagram_signature.reciprocal.coefficients.len() - 1,
        cross_check_ihara(&diagram_signature).agrees()
    );
    println!(
        "    diagram Z^-1 = {}",
        format_polynomial(&diagram_signature.reciprocal)
    );
    println!();

    let construction = tetrahedron_construction();
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

    for receiver in [&direct, &precessed] {
        match analyze_receiver_topology(&construction, receiver, 12) {
            Ok(topology) => {
                println!("-- the tetrahedron under the {} --", receiver.name);
                print_frame(&topology.two_frame_ihara_reading());
                report_orbit(&topology);
            }
            Err(error) => println!(
                "-- the tetrahedron under the {} · refused: {error} --\n",
                receiver.name
            ),
        }
    }
}

/// A gauge whose group acts trivially on the declared material is not a gauge.
/// K4 is self-dual in the plane, so the source/face-dual pair is exactly such a
/// degenerate orbit and must be named rather than read as agreement.
fn report_orbit(topology: &ReceiverTopology) {
    let reading = topology.two_frame_ihara_reading();
    match reading.first_reciprocal_difference {
        None => println!(
            "  ORBIT IS TRIVIAL on this material: the two frames return the same reciprocal.\n  \
             Agreement here is not evidence of anything the two frames share, because they are\n  \
             the same graph up to isomorphism. Read the orbit before reading the agreement.\n"
        ),
        Some(degree) => println!(
            "  ORBIT IS NON-TRIVIAL: the two frames' reciprocals first separate at degree {degree}.\n"
        ),
    }
}

fn main() {
    println!("IHARA TWO-ROUTE CROSS-CHECK");
    println!("det(I - uB) against prod over primitive closed geodesics (1 - u^len)");
    println!("the spectral side against the geodesic side, exact over BigInt");
    println!();
    section_the_identity();
    section_the_third_route();
    section_the_horizon();
    section_the_falsifier();
    section_two_frames();
    println!("== WHAT IS NOT CLAIMED ==");
    println!();
    println!("Ihara's theorem is standard; nothing here proves it. What is returned is");
    println!("that this body's determinant route and this body's geodesic route agree");
    println!("on every coefficient the declared horizon determines, on the family above,");
    println!("and that the agreement breaks under a one-unit perturbation of any single");
    println!("primitive-cycle count inside the window. No spectral gap, no Ramanujan");
    println!("claim, and no root isolation is performed here.");
}
