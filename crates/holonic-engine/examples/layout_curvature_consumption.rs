//! LAYOUT -> CURVATURE, closed. Loop (b) of `blueprint/THE_ASSEMBLY.md:122`.
//!
//! `local_star` computes a disclination charge at every vertex and then clones
//! its `geometry_responses` verbatim (`local_star.rs:2301`), so the population
//! that produced the curvature never receives it. `holonic_engine::curvature_bridge`
//! is the adapter between that population and `discrete_curvature`'s update law.
//! Until this driver existed the module had **one** inbound edge in the whole
//! tree — its `pub mod` line — and the loop was entered nowhere.
//!
//! This driver enters at the response population and returns the artifact: the
//! aperture in both coordination frames, the projection population, the
//! revision population per step, the deficit population per step, and every
//! refusal as the population it is. Counts appear only as labels on populations
//! that are printed in full.
//!
//! Every falsifier the design names for loop (b) is asserted here, so a wrong
//! bridge makes this driver exit nonzero rather than print a nice table:
//!
//! - a nonzero deficit MUST move;
//! - a flat layout MUST stay exactly fixed;
//! - *"the flow drives every deficit to zero"* is FALSE, shown twice — the
//!   `+12 / -12` involution that never reaches zero, and a bipartite aperture
//!   fixed at nonzero deficits whose TOTAL is exactly zero, which is precisely
//!   the reading that would make a total-grading run announce convergence;
//! - grade the deficit, not the combinatorial charge — the charge is printed
//!   beside the deficit at every step and is asserted constant.
//!
//! Run: `cargo run -p holonic-engine --example layout_curvature_consumption`

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::curvature_bridge::{
    declare_aperture, read, revise, revise_partially, step, step_partially, ApertureRefusal,
    CurvatureBridgeError,
};
use holonic_engine::{
    CpuExecutor, Edge, EventId, HingeId, HingeTrajectory, HingeTransportNetwork, HingeUnitSystem,
    HingeWorldLaw, LocalStarLaw, LocalStarMaterial, LocalStarStanding, QuadraticHingeAction,
    SimplicialComplex, VertexId,
};
use num_traits::Zero;
use relational_geometry::{integer, rat, Rat, RatVec3};

// ---------------------------------------------------------------------------
// Exact display. Nothing here rounds, and no value is ordered by magnitude.
// ---------------------------------------------------------------------------

fn show(value: &Rat) -> String {
    if value.is_integer() {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn show_vector(value: &RatVec3) -> String {
    format!("({}, {}, {})", show(&value.x), show(&value.y), show(&value.z))
}

struct Names {
    vertices: BTreeMap<VertexId, String>,
    hinges: BTreeMap<HingeId, String>,
}

impl Names {
    fn of(standing: &LocalStarStanding) -> Self {
        let vertices = standing
            .kinematic
            .complex
            .vertices
            .values()
            .map(|vertex| (vertex.id, vertex.name.clone()))
            .collect::<BTreeMap<_, _>>();
        let hinges = standing
            .kinematic
            .complex
            .hinges
            .values()
            .map(|hinge| {
                (
                    hinge.id,
                    format!(
                        "{}-{}",
                        vertices[&hinge.edge.lower], vertices[&hinge.edge.upper]
                    ),
                )
            })
            .collect();
        Self { vertices, hinges }
    }

    fn vertex(&self, vertex: VertexId) -> &str {
        self.vertices
            .get(&vertex)
            .map_or("?", |name| name.as_str())
    }

    fn hinge(&self, hinge: HingeId) -> &str {
        self.hinges.get(&hinge).map_or("?", |name| name.as_str())
    }
}

// ---------------------------------------------------------------------------
// Material. The driver builds its own standings from the public law, so the
// populations below are not a test fixture read back to itself.
// ---------------------------------------------------------------------------

fn units() -> HingeUnitSystem {
    HingeUnitSystem {
        coordinate: "turn".to_owned(),
        event_step: "event".to_owned(),
        action: "action".to_owned(),
        momentum: "action/turn".to_owned(),
        impulse: "action/turn".to_owned(),
    }
}

/// A nonzero vector orthogonal to `edge_vector`.
fn off_edge(edge_vector: &RatVec3) -> RatVec3 {
    for aux in [
        RatVec3::from_i64(1, 0, 0),
        RatVec3::from_i64(0, 1, 0),
        RatVec3::from_i64(0, 0, 1),
    ] {
        let candidate = edge_vector.cross(&aux);
        if !candidate.norm_squared().is_zero() {
            return candidate;
        }
    }
    panic!("a nonzero edge vector has a nonzero orthogonal complement")
}

/// A response projecting to exactly `target` along `edge_vector` and **not**
/// parallel to it. The orthogonal summand dots to zero against the edge, so it
/// is invisible to the projection and visible to the lift: a lift that
/// reconstructed the response from the edge would be caught by it.
fn response_projecting_to(edge_vector: &RatVec3, target: &Rat) -> RatVec3 {
    edge_vector
        .scale(&(target / edge_vector.norm_squared()))
        .add(&off_edge(edge_vector).scale(&rat(1, 7)))
}

fn standing_from(
    complex: SimplicialComplex,
    positions: BTreeMap<VertexId, RatVec3>,
    response: impl Fn(Edge, &RatVec3) -> RatVec3,
) -> LocalStarStanding {
    let kinematic =
        HingeWorldLaw::new(complex, HingeTransportNetwork::default(), Vec::new()).unwrap();
    let hinges = kinematic.complex.hinges.keys().copied().collect::<Vec<_>>();
    let parameters = hinges
        .iter()
        .map(|hinge| (*hinge, integer(0)))
        .collect::<BTreeMap<_, _>>();
    let kinematic_standing = kinematic.initial_standing(parameters).unwrap();
    let materials = hinges
        .iter()
        .map(|hinge| {
            let edge = kinematic.complex.hinges[hinge].edge;
            let edge_vector = positions[&edge.upper].subtract(&positions[&edge.lower]);
            (
                *hinge,
                LocalStarMaterial {
                    action: QuadraticHingeAction::new(integer(2), integer(1), units()).unwrap(),
                    stress_response: rat(1, 4),
                    geometry_response: response(edge, &edge_vector),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let law = LocalStarLaw::new(kinematic, materials, Vec::new(), CpuExecutor::serial()).unwrap();
    let trajectories = hinges
        .iter()
        .map(|hinge| {
            (
                *hinge,
                HingeTrajectory {
                    previous: integer(0),
                    current: integer(0),
                },
            )
        })
        .collect();
    law.initial_standing(kinematic_standing, trajectories, positions, Vec::new())
        .expect("the driver's own material is a well formed standing")
}

fn octahedron(target: impl Fn(Edge) -> Rat) -> LocalStarStanding {
    let founding = EventId(1);
    let mut complex = SimplicialComplex::default();
    let a = complex.found_vertex("a", founding);
    let b = complex.found_vertex("b", founding);
    let c = complex.found_vertex("c", founding);
    let d = complex.found_vertex("d", founding);
    let e = complex.found_vertex("e", founding);
    let f = complex.found_vertex("f", founding);
    for (name, vertices) in [
        ("eab", [e, a, b]),
        ("ebc", [e, b, c]),
        ("ecd", [e, c, d]),
        ("eda", [e, d, a]),
        ("fba", [f, b, a]),
        ("fcb", [f, c, b]),
        ("fdc", [f, d, c]),
        ("fad", [f, a, d]),
    ] {
        complex.found_face(name, founding, vertices).unwrap();
    }
    let positions = BTreeMap::from([
        (a, RatVec3::from_i64(-3, -2, 6)),
        (b, RatVec3::from_i64(3, -2, 6)),
        (c, RatVec3::from_i64(0, 3, 7)),
        (d, RatVec3::from_i64(0, -3, 7)),
        (e, RatVec3::from_i64(0, 0, 11)),
        (f, RatVec3::from_i64(0, 0, 3)),
    ]);
    for edge in face_edges(&complex) {
        complex
            .found_hinge("octahedral hinge", founding, edge)
            .unwrap();
    }
    standing_from(complex, positions, |edge, vector| {
        response_projecting_to(vector, &target(edge))
    })
}

fn bipyramid(target: impl Fn(bool) -> Rat) -> LocalStarStanding {
    let founding = EventId(1);
    let mut complex = SimplicialComplex::default();
    let north = complex.found_vertex("north", founding);
    let south = complex.found_vertex("south", founding);
    let equator = (0..5)
        .map(|i| complex.found_vertex(format!("ring-{i}"), founding))
        .collect::<Vec<_>>();
    for i in 0..5 {
        let p = equator[i];
        let q = equator[(i + 1) % 5];
        complex
            .found_face(format!("north-{i}"), founding, [north, p, q])
            .unwrap();
        complex
            .found_face(format!("south-{i}"), founding, [south, q, p])
            .unwrap();
    }
    let ring = [
        RatVec3::from_i64(4, 0, 0),
        RatVec3::from_i64(1, 3, 0),
        RatVec3::from_i64(-3, 2, 0),
        RatVec3::from_i64(-2, -3, 0),
        RatVec3::from_i64(2, -4, 0),
    ];
    let mut positions = BTreeMap::from([
        (north, RatVec3::from_i64(0, 0, 5)),
        (south, RatVec3::from_i64(0, 0, -3)),
    ]);
    for (index, vertex) in equator.iter().enumerate() {
        positions.insert(*vertex, ring[index].clone());
    }
    for edge in face_edges(&complex) {
        complex
            .found_hinge("bipyramid hinge", founding, edge)
            .unwrap();
    }
    let apexes = [north, south];
    standing_from(complex, positions, |edge, vector| {
        let at_apex = apexes.contains(&edge.lower) || apexes.contains(&edge.upper);
        response_projecting_to(vector, &target(at_apex))
    })
}

/// Two octahedra sharing exactly one vertex, plus one vertex in no face. The
/// pinch is `Singular`, the free vertex is `Isolated`, and the eight vertices
/// adjacent to the pinch each leak one hinge out of the aperture.
fn pinched_octahedra() -> LocalStarStanding {
    let founding = EventId(1);
    let mut complex = SimplicialComplex::default();
    let a = complex.found_vertex("a", founding);
    let b = complex.found_vertex("b", founding);
    let c = complex.found_vertex("c", founding);
    let d = complex.found_vertex("d", founding);
    let e = complex.found_vertex("e", founding);
    let f = complex.found_vertex("f", founding);
    let g = complex.found_vertex("g", founding);
    let h = complex.found_vertex("h", founding);
    let i = complex.found_vertex("i", founding);
    let j = complex.found_vertex("j", founding);
    let k = complex.found_vertex("k", founding);
    let free = complex.found_vertex("free", founding);
    for (name, vertices) in [
        ("eab", [e, a, b]),
        ("ebc", [e, b, c]),
        ("ecd", [e, c, d]),
        ("eda", [e, d, a]),
        ("fba", [f, b, a]),
        ("fcb", [f, c, b]),
        ("fdc", [f, d, c]),
        ("fad", [f, a, d]),
        ("kgh", [k, g, h]),
        ("khi", [k, h, i]),
        ("kij", [k, i, j]),
        ("kjg", [k, j, g]),
        ("fhg", [f, h, g]),
        ("fih", [f, i, h]),
        ("fji", [f, j, i]),
        ("fgj", [f, g, j]),
    ] {
        complex.found_face(name, founding, vertices).unwrap();
    }
    let positions = BTreeMap::from([
        (a, RatVec3::from_i64(-3, -2, 6)),
        (b, RatVec3::from_i64(3, -2, 6)),
        (c, RatVec3::from_i64(0, 3, 7)),
        (d, RatVec3::from_i64(0, -3, 7)),
        (e, RatVec3::from_i64(0, 0, 11)),
        (f, RatVec3::from_i64(0, 0, 3)),
        (g, RatVec3::from_i64(-3, -2, -4)),
        (h, RatVec3::from_i64(3, -2, -4)),
        (i, RatVec3::from_i64(0, 3, -5)),
        (j, RatVec3::from_i64(0, -3, -5)),
        (k, RatVec3::from_i64(0, 0, -9)),
        (free, RatVec3::from_i64(20, 20, 20)),
    ]);
    for edge in face_edges(&complex) {
        complex.found_hinge("pinched hinge", founding, edge).unwrap();
    }
    standing_from(complex, positions, |_, vector| {
        response_projecting_to(vector, &integer(1))
    })
}

fn face_edges(complex: &SimplicialComplex) -> Vec<Edge> {
    complex
        .faces
        .values()
        .flat_map(|face| face.boundary().map(|(edge, _)| edge))
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn vertex_id(standing: &LocalStarStanding, name: &str) -> VertexId {
    standing
        .kinematic
        .complex
        .vertices
        .values()
        .find(|vertex| vertex.name == name)
        .expect("the driver names its vertices")
        .id
}

/// Narrow a founded standing's hinge population in place. `HingeWorldStanding`
/// documents its complex as contemporary incidence that later topology deeds
/// replace (`simplicial.rs:826-828`); `initial_standing` cannot produce a
/// narrowed one because `face_fields` demands a hinge on every face edge.
fn retire_hinges(standing: &mut LocalStarStanding, keep: impl Fn(Edge) -> bool) {
    standing
        .kinematic
        .complex
        .hinges
        .retain(|_, hinge| keep(hinge.edge));
}

// ---------------------------------------------------------------------------
// The artifact. Every section prints the population it computed.
// ---------------------------------------------------------------------------

fn print_aperture(standing: &LocalStarStanding) {
    let names = Names::of(standing);
    let aperture = declare_aperture(standing).expect("the aperture is declared");
    println!("  conducted vertices, in BOTH coordination frames:");
    println!(
        "    {:<8} {:>10} {:>10} {:>10} {:>10}  frames",
        "vertex", "face |lk|", "face chg", "hinges", "hinge chg"
    );
    for carried in aperture.conducted.values() {
        println!(
            "    {:<8} {:>10} {:>10} {:>10} {:>10}  {}",
            names.vertex(carried.vertex),
            carried.link_coordination,
            carried.link_charge,
            carried.incident_hinges,
            carried.hinge_charge,
            if carried.frames_agree() {
                "agree"
            } else {
                "DISAGREE"
            }
        );
    }
    if aperture.refused.is_empty() {
        println!("  refused vertices: none");
    } else {
        println!("  refused vertices, with the typed reason:");
        for (vertex, refusal) in &aperture.refused {
            let reason = match refusal {
                ApertureRefusal::BoundaryPath { coordination } => {
                    format!("BoundaryPath, link {coordination}")
                }
                ApertureRefusal::SingularLink { coordination } => {
                    format!("SingularLink, link {coordination}")
                }
                ApertureRefusal::IsolatedLink => "IsolatedLink".to_owned(),
                ApertureRefusal::InteriorCycleWithoutHinges => {
                    "InteriorCycleWithoutHinges".to_owned()
                }
            };
            println!("    {:<8} {reason}", names.vertex(*vertex));
        }
    }
    if aperture.refused_hinges.is_empty() {
        println!("  refused hinges: none");
    } else {
        println!("  refused hinges, with the endpoint that put each out:");
        for refused in aperture.refused_hinges.values() {
            println!(
                "    {:<10} exterior endpoint {}",
                names.hinge(refused.hinge),
                names.vertex(refused.exterior)
            );
        }
    }
}

fn print_projections(standing: &LocalStarStanding) {
    let names = Names::of(standing);
    let reading = read(standing).expect("the standing conducts");
    println!("  the projection population — the WHOLE record travels, not the scalar:");
    println!(
        "    {:<10} {:>22} {:>18} {:>10} {:>14}",
        "hinge", "response", "edge vector", "along edge", "refused |r|^2"
    );
    for projection in reading.projections.values() {
        println!(
            "    {:<10} {:>22} {:>18} {:>10} {:>14}",
            names.hinge(projection.hinge),
            show_vector(&projection.response_direction),
            show_vector(&projection.edge_vector),
            show(&projection.along_edge),
            show(&projection.direction_blind_norm_squared)
        );
    }
}

fn print_deficits(standing: &LocalStarStanding, label: &str) -> BTreeMap<VertexId, Rat> {
    let names = Names::of(standing);
    let reading = read(standing).expect("the standing conducts");
    let deficits = reading.deficits();
    let charges = reading.combinatorial_charges();
    print!("  {label}: deficit / combinatorial charge per vertex —");
    for (vertex, deficit) in &deficits {
        print!(
            " {}: {} / {}",
            names.vertex(*vertex),
            show(deficit),
            charges[vertex]
        );
    }
    println!();
    deficits
}

fn print_revisions(standing: &LocalStarStanding) {
    let names = Names::of(standing);
    let applied = step(standing).expect("the standing conducts");
    println!("  the revision population — every hinge's lift, whole:");
    println!(
        "    {:<10} {:>22} {:>22} {:>8} {:>8} {:>8}",
        "hinge", "before", "after", "s_before", "s_after", "factor"
    );
    for revision in applied.revisions.values() {
        println!(
            "    {:<10} {:>22} {:>22} {:>8} {:>8} {:>8}",
            names.hinge(revision.hinge),
            show_vector(&revision.before),
            show_vector(&revision.after),
            show(&revision.along_edge_before),
            show(&revision.along_edge_after),
            show(&revision.magnitude_factor)
        );
    }
}

// ---------------------------------------------------------------------------

fn a_charged_layout_moves() {
    println!("== a charged closed layout moves, and the charge does not ==");
    let mut standing = octahedron(|_| integer(1));
    print_aperture(&standing);
    print_projections(&standing);
    print_revisions(&standing);

    let founding_charges = read(&standing)
        .expect("the octahedron conducts")
        .combinatorial_charges();
    let mut seen = vec![print_deficits(&standing, "founding")];
    let mut totals = vec![read(&standing).expect("conducts").total_deficit()];
    for index in 0..4 {
        let applied = revise(&mut standing).expect("the octahedron conducts");
        assert!(applied.flow.moved, "a charged layout that does not move");
        let reading = read(&standing).expect("the octahedron conducts");
        assert_eq!(
            reading.combinatorial_charges(),
            founding_charges,
            "the combinatorial charge moved while the complex stood still"
        );
        seen.push(print_deficits(&standing, &format!("after step {}", index + 1)));
        totals.push(reading.total_deficit());
    }
    print!("  the total deficit across the run —");
    for total in &totals {
        print!(" {}", show(total));
    }
    println!();
    assert!(
        totals.iter().all(|total| !total.is_zero()),
        "the flow never drives this total to zero; a run that reports it has \
         mis-graded"
    );
    assert!(
        seen.iter().collect::<BTreeSet<_>>().len() >= 2,
        "the deficit population must actually vary"
    );
    println!();
}

fn a_flat_layout_stays_exactly_fixed() {
    println!("== a flat layout is left EXACTLY fixed ==");
    // Apex hinges project to 6/5, ring hinges to 9/5: two link sizes and two
    // response values, so flatness here is a property of the layout and not of
    // uniformity. This fixture could have moved.
    let mut standing = bipyramid(|at_apex| if at_apex { rat(6, 5) } else { rat(9, 5) });
    let founding = standing.geometry_responses.clone();
    print_aperture(&standing);
    print_deficits(&standing, "founding");
    let reading = read(&standing).expect("the bipyramid conducts");
    assert!(reading.is_flat());
    let projected = reading
        .projections
        .values()
        .map(|projection| projection.along_edge.clone())
        .collect::<BTreeSet<_>>();
    assert!(
        projected.len() > 1,
        "a fixture with one response value cannot show flat is not uniform"
    );

    for _ in 0..10 {
        let applied = revise(&mut standing).expect("the bipyramid conducts");
        assert!(
            !applied.flow.moved,
            "a bridge that moves a flat layout is introducing curvature"
        );
    }
    assert_eq!(
        standing.geometry_responses, founding,
        "ten revisions of a flat layout must leave the population identical"
    );
    println!("  ten revisions later the response population is identical, hinge for hinge");
    println!();
}

fn the_flow_does_not_drive_the_deficit_to_zero() {
    println!("== \"the flow drives every deficit to zero\" is FALSE, twice ==");

    // Once: the involution. Sixteen steps, never zero.
    let mut standing = octahedron(|_| integer(1));
    let mut totals = Vec::new();
    for _ in 0..16 {
        let applied = revise(&mut standing).expect("the octahedron conducts");
        assert_eq!(
            applied.flow.total_deficit_after,
            -applied.flow.total_deficit_before.clone(),
            "one step negates the total exactly"
        );
        totals.push(applied.flow.total_deficit_after.clone());
    }
    print!("  sixteen steps of the octahedral total —");
    for total in &totals {
        print!(" {}", show(total));
    }
    println!();
    assert!(totals.iter().all(|total| !total.is_zero()));

    // Twice: a bipartite aperture with unequal parts, FIXED at nonzero
    // deficits. Retiring the four equatorial hinges leaves K(2,4); at uniform
    // response 9/4 nothing moves, ever.
    let mut narrowed = octahedron(|_| rat(9, 4));
    let apexes = [vertex_id(&narrowed, "e"), vertex_id(&narrowed, "f")];
    retire_hinges(&mut narrowed, |edge| {
        apexes.contains(&edge.lower) || apexes.contains(&edge.upper)
    });
    let names = Names::of(&narrowed);
    let reading = read(&narrowed).expect("the narrowed octahedron conducts");
    print!("  the K(2,4) aperture's deficit population —");
    for (vertex, deficit) in reading.deficits() {
        print!(" {}: {}", names.vertex(vertex), show(&deficit));
    }
    println!();
    print!("  its forced component scale —");
    for (component, scale) in reading.configuration.forced_component_scale() {
        print!(" [{}]: {}", names.vertex(component), show(&scale));
    }
    println!();
    println!(
        "  its TOTAL deficit is {} while not one vertex is flat: a run grading \
         the total announces convergence here",
        show(&reading.total_deficit())
    );
    assert!(reading.total_deficit().is_zero());
    assert!(!reading.is_flat());
    assert!(reading
        .deficits()
        .values()
        .all(|deficit| !deficit.is_zero()));
    for _ in 0..8 {
        let applied = revise(&mut narrowed).expect("the narrowed octahedron conducts");
        assert!(
            !applied.flow.moved,
            "an unbalanced bipartite aperture is FIXED at a nonzero deficit"
        );
        assert!(applied
            .flow
            .deficits_after
            .values()
            .all(|deficit| !deficit.is_zero()));
    }
    println!("  eight further steps move nothing and flatten nothing");
    println!();
}

fn the_two_coordination_frames_can_disagree() {
    println!("== two frames, and the material on which they disagree ==");
    let mut standing = octahedron(|_| integer(1));
    let apexes = [vertex_id(&standing, "e"), vertex_id(&standing, "f")];
    retire_hinges(&mut standing, |edge| {
        apexes.contains(&edge.lower) || apexes.contains(&edge.upper)
    });
    print_aperture(&standing);
    let names = Names::of(&standing);
    let reading = read(&standing).expect("the narrowed octahedron conducts");
    let disagreements = reading.frame_disagreements();
    print!("  the disagreement POPULATION —");
    for carried in disagreements.values() {
        print!(
            " {}: face {} vs hinge {};",
            names.vertex(carried.vertex),
            carried.link_charge,
            carried.hinge_charge
        );
    }
    println!();
    assert_eq!(
        disagreements.len(),
        4,
        "the four equatorial vertices read differently in the two frames"
    );
    assert!(
        disagreements.len() < reading.aperture.conducted.len(),
        "the two apexes must still agree, or the fixture proves nothing about \
         which vertices disagree"
    );
    for carried in disagreements.values() {
        assert_eq!(carried.link_coordination, 4);
        assert_eq!(carried.incident_hinges, 2);
    }
    println!();
}

fn every_refusal_is_a_population() {
    println!("== every refusal is a keyed population, never a bool or a count ==");
    let standing = pinched_octahedra();
    let names = Names::of(&standing);
    print_aperture(&standing);
    match read(&standing) {
        Err(CurvatureBridgeError::AperturePorous { leaks }) => {
            println!("  the reading refuses with the WHOLE leak population:");
            for leak in leaks.values() {
                println!(
                    "    {:<8} {} hinges in the complex, {} inside the aperture",
                    names.vertex(leak.vertex),
                    leak.incident_in_complex,
                    leak.incident_in_aperture
                );
            }
            assert_eq!(
                leaks.len(),
                8,
                "eight vertices leak; a refusal naming one of them has dropped \
                 a population it had already computed"
            );
        }
        other => panic!("expected a porosity refusal, got {other:?}"),
    }
    println!();
}

fn the_third_arm_deposits_what_it_cannot_lift() {
    println!("== the third arm: lift what is defined, DEPOSIT what is not ==");
    // Reproduce the defect in `local_star`'s own octahedral fixture: a response
    // orthogonal to its own edge, spending exactly nothing along it. Two of
    // them, so a refusal that returns the first is visibly short.
    let mut standing = octahedron(|_| integer(1));
    let (a, b) = (vertex_id(&standing, "a"), vertex_id(&standing, "b"));
    let (c, d) = (vertex_id(&standing, "c"), vertex_id(&standing, "d"));
    let mut turned = Vec::new();
    for edge in [Edge::new(a, b).unwrap(), Edge::new(c, d).unwrap()] {
        let hinge = standing
            .kinematic
            .complex
            .hinges
            .values()
            .find(|hinge| hinge.edge == edge)
            .expect("every octahedral edge carries a hinge")
            .id;
        let edge_vector = standing.spatial.edges[&edge].vector.clone();
        let sideways = edge_vector.cross(&RatVec3::from_i64(1, 1, 1));
        assert!(sideways.dot(&edge_vector).is_zero());
        standing.geometry_responses.insert(hinge, sideways);
        turned.push(hinge);
    }
    let names = Names::of(&standing);

    // Arm one: refuse whole, with the population.
    match step(&standing) {
        Err(CurvatureBridgeError::ResponsesOrthogonalToTheirOwnEdges { refused }) => {
            println!("  the whole arm refuses, carrying EVERY unliftable hinge:");
            for record in refused.values() {
                println!(
                    "    {:<10} response {} . edge {} = 0, requested {}",
                    names.hinge(record.hinge),
                    show_vector(&record.response_direction),
                    show_vector(&record.edge_vector),
                    show(&record.requested)
                );
            }
            assert_eq!(refused.len(), 2, "both unliftable hinges must be carried");
        }
        other => panic!("expected an orthogonality refusal, got {other:?}"),
    }

    // Arm two: fall open. That wiring reads `match step(..) { Ok(s) => write
    // s, Err(_) => keep the clone }`, so its successor population IS the clone.
    // Measured here rather than assumed.
    let fallen_open = match step(&standing) {
        Ok(applied) => applied.revised_geometry_responses,
        Err(_) => standing.geometry_responses.clone(),
    };
    assert_eq!(
        fallen_open, standing.geometry_responses,
        "falling open on the refusal is a no-op wearing a wiring's name"
    );
    println!("  falling open on that refusal changes nothing at all — measured, not assumed");

    // Arm three: apply the lift where it is defined, deposit the rest.
    let before = read(&standing).expect("the reading succeeds");
    let mut moved = standing.clone();
    let applied = revise_partially(&mut moved).expect("the partial arm conducts");
    assert!(!applied.is_whole());
    println!(
        "  the partial arm lifted {} hinges and deposited {}:",
        applied.revisions.len(),
        applied.unlifted.len()
    );
    for record in applied.unlifted.values() {
        println!(
            "    deposited {:<10} response {} spends nothing along {}",
            names.hinge(record.hinge),
            show_vector(&record.response_direction),
            show_vector(&record.edge_vector)
        );
    }
    for revision in applied.revisions.values() {
        println!(
            "    lifted    {:<10} {} -> {}   ({} -> {})",
            names.hinge(revision.hinge),
            show_vector(&revision.before),
            show_vector(&revision.after),
            show(&revision.along_edge_before),
            show(&revision.along_edge_after)
        );
    }

    let after = read(&moved).expect("the moved standing conducts");
    assert_ne!(
        after.deficits(),
        before.deficits(),
        "the partial arm must actually move the deficit; a green run that moved \
         nothing is the fall-open arm wearing a third name"
    );

    // The exact price, per vertex: the successor differs from the carrier's own
    // successor by exactly the increment the unlifted hinges never received.
    let mut owed: BTreeMap<VertexId, Rat> = BTreeMap::new();
    for (hinge, record) in &applied.unlifted {
        let increment = &applied.flow.revisions[hinge];
        for endpoint in [record.edge.lower, record.edge.upper] {
            *owed.entry(endpoint).or_insert_with(Rat::zero) += increment;
        }
    }
    print!("  the price of the arm, per vertex —");
    for (vertex, expected) in &applied.flow.deficits_after {
        let owed_here = owed.get(vertex).cloned().unwrap_or_else(Rat::zero);
        assert_eq!(
            after.deficits()[vertex],
            expected + &owed_here,
            "the discrepancy at a vertex is not the retained increment"
        );
        print!(" {}: {}", names.vertex(*vertex), show(&owed_here));
    }
    println!();
    assert!(
        owed.values().any(|value| !value.is_zero()),
        "a price of zero everywhere would make the assertion above vacuous"
    );

    // And the partial step is reproducible without mutating: `step_partially`
    // returns the same successor population that `revise_partially` wrote.
    let dry = step_partially(&standing).expect("the partial arm conducts");
    assert_eq!(dry.revised_geometry_responses, moved.geometry_responses);
    println!();
}

fn main() {
    println!("LAYOUT -> CURVATURE. The signal is the revision population, entering");
    println!("at `LocalStarStanding::geometry_responses`. Grade the deficit, not the");
    println!("combinatorial charge.\n");
    a_charged_layout_moves();
    a_flat_layout_stays_exactly_fixed();
    the_flow_does_not_drive_the_deficit_to_zero();
    the_two_coordination_frames_can_disagree();
    every_refusal_is_a_population();
    the_third_arm_deposits_what_it_cannot_lift();
    println!("every falsifier this driver asserts held; the populations above are the return");
}
