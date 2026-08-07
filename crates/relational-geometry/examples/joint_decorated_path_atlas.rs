use num_traits::Zero;

use relational_geometry::{
    ConstraintKind, Construction, CrossingRole, DecoratedPrimitiveTrace, EntityId, ExactTurn,
    Geometry, JointDecoratedPathOperator, Rat, RatVec3, Receiver, ReceiverClosedTrace, ReceiverId,
    ReceiverOrientation, SourceDartAddress, SourceEndpoint, SourceSegmentAddress,
    build_joint_decorated_path_operator, format_rat, integer, rat,
};

struct TetrahedralState {
    construction: Construction,
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
        edge_entities.push(
            construction
                .add_entity(
                    format!("edge {name}"),
                    frame,
                    Geometry::Thread {
                        vertices: vec![vertices[left].clone(), vertices[right].clone()],
                        closed: false,
                    },
                )
                .expect("the source frame exists"),
        );
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
                "one source incidence",
                ConstraintKind::SharedVertex {
                    left: pair[0].entity,
                    right: pair[1].entity,
                    left_vertex: pair[0].vertex,
                    right_vertex: pair[1].vertex,
                },
            );
        }
    }
    TetrahedralState { construction }
}

fn receivers() -> [Receiver; 2] {
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

fn edge_label(construction: &Construction, entity: EntityId) -> &str {
    construction.entities[&entity]
        .name
        .strip_prefix("edge ")
        .expect("the bounded world names each edge")
}

fn format_source_word(construction: &Construction, word: &[SourceDartAddress]) -> String {
    word.iter()
        .map(|dart| {
            format!(
                "{}{}",
                edge_label(construction, dart.segment.entity),
                if dart.forward { "+" } else { "-" }
            )
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn format_rat_word(values: &[Rat]) -> String {
    format!(
        "[{}]",
        values.iter().map(format_rat).collect::<Vec<_>>().join(",")
    )
}

fn format_interval_word(values: &[Vec<Rat>]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(|intervals| format_rat_word(intervals))
            .collect::<Vec<_>>()
            .join(";")
    )
}

fn format_turn_word(values: &[ExactTurn]) -> String {
    format!(
        "[{}]",
        values
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn format_crossings(construction: &Construction, trace: &ReceiverClosedTrace) -> String {
    let rows = trace
        .crossing_word
        .iter()
        .enumerate()
        .flat_map(|(dart, marks)| {
            marks.iter().map(move |mark| {
                format!(
                    "d{}@{}:{}:{}:{}",
                    dart + 1,
                    format_rat(&mark.source_parameter),
                    edge_label(construction, mark.other_branch.entity),
                    match mark.role {
                        CrossingRole::Over => "over",
                        CrossingRole::Under => "under",
                    },
                    mark.crossing_orientation
                )
            })
        })
        .collect::<Vec<_>>();
    if rows.is_empty() {
        "[]".to_owned()
    } else {
        format!("[{}]", rows.join(","))
    }
}

fn print_receiver_trace(construction: &Construction, label: &str, trace: &ReceiverClosedTrace) {
    println!(
        "    {label} · {} · chords {} · intervals {}",
        trace.receiver_name,
        format_rat_word(&trace.projected_chord_word),
        format_interval_word(&trace.interval_chord_word)
    );
    println!(
        "      crossings {} · local turns {} · closed return {}",
        format_crossings(construction, trace),
        format_turn_word(&trace.local_turn_word),
        trace.closed_return
    );
}

fn is_crossing_quadrilateral(trace: &DecoratedPrimitiveTrace) -> bool {
    let entities = trace
        .source_word
        .iter()
        .map(|dart| dart.segment.entity.0)
        .collect::<Vec<_>>();
    trace.source_word.len() == 4
        && entities.contains(&2)
        && entities.contains(&3)
        && entities.contains(&4)
        && entities.contains(&5)
}

fn print_joint_refinement(
    construction: &Construction,
    before: &JointDecoratedPathOperator,
    after: &JointDecoratedPathOperator,
) {
    println!("JOINT RECEIVER REFINEMENT");
    for before_dart in before.darts.iter().filter(|dart| dart.address.forward) {
        let after_dart = after
            .darts
            .iter()
            .find(|candidate| candidate.address == before_dart.address)
            .expect("source incidence persists");
        let before_crossings = before_dart
            .receiver_faces
            .iter()
            .map(|face| face.crossings.len())
            .sum::<usize>();
        let after_crossings = after_dart
            .receiver_faces
            .iter()
            .map(|face| face.crossings.len())
            .sum::<usize>();
        if before_dart.ordered_source_cuts == after_dart.ordered_source_cuts
            && before_crossings == 0
            && after_crossings == 0
        {
            continue;
        }
        println!(
            "  {} · joint cuts {} -> {}",
            edge_label(construction, before_dart.address.segment.entity),
            format_rat_word(&before_dart.ordered_source_cuts),
            format_rat_word(&after_dart.ordered_source_cuts)
        );
        for (before_face, after_face) in before_dart
            .receiver_faces
            .iter()
            .zip(&after_dart.receiver_faces)
        {
            println!(
                "    {} · visible marks {} -> {} · interval metrics {} -> {}",
                before_face.receiver_name,
                before_face.crossings.len(),
                after_face.crossings.len(),
                format_rat_word(
                    &before_face
                        .intervals
                        .iter()
                        .map(|row| row.gauge_chord_squared.clone())
                        .collect::<Vec<_>>()
                ),
                format_rat_word(
                    &after_face
                        .intervals
                        .iter()
                        .map(|row| row.gauge_chord_squared.clone())
                        .collect::<Vec<_>>()
                )
            );
        }
    }
    println!();
}

fn main() {
    let before = build_state(integer(1));
    let after = build_state(rat(1, 4));
    let receiver_family = receivers();
    let before_operator =
        build_joint_decorated_path_operator(&before.construction, &receiver_family, 4)
            .expect("the before cut is regular");
    let after_operator =
        build_joint_decorated_path_operator(&after.construction, &receiver_family, 4)
            .expect("the emanated cut is regular");

    println!("JOINT DECORATED PATH ATLAS 01");
    println!("one lawful source incidence · two co-present receiver faces · one source emanation");
    println!();
    println!("CARRIER");
    println!(
        "  schema {} · source segments {} · oriented darts {} · lawful nonbacktracking transitions {}",
        before_operator.schema,
        before_operator.source_segments.len(),
        before_operator.darts.len(),
        before_operator.transitions.len()
    );
    println!(
        "  primitive source words through length four {} -> {}",
        before_operator.primitive_traces.len(),
        after_operator.primitive_traces.len()
    );
    println!(
        "  source word population exact: {}",
        before_operator
            .primitive_traces
            .iter()
            .map(|trace| &trace.source_word)
            .eq(after_operator
                .primitive_traces
                .iter()
                .map(|trace| &trace.source_word))
    );
    println!();

    print_joint_refinement(&before.construction, &before_operator, &after_operator);

    let ac = SourceSegmentAddress {
        entity: EntityId(2),
        segment: 0,
    };
    let bd = SourceSegmentAddress {
        entity: EntityId(5),
        segment: 0,
    };
    let false_crossing_switch = before_operator.transitions.iter().any(|transition| {
        let incoming = before_operator.dart(transition.incoming).address.segment;
        let outgoing = before_operator.dart(transition.outgoing).address.segment;
        (incoming == ac && outgoing == bd) || (incoming == bd && outgoing == ac)
    });
    println!("SOURCE-LAWFULNESS");
    println!(
        "  precessed AC x BD is visible, but a transition AC <-> BD at that crossing exists: {false_crossing_switch}"
    );
    println!("  every transition remains pinned to one declared source vertex.");
    println!();

    println!("COMPLETE PRIMITIVE SOURCE WORDS");
    for (index, (before_trace, after_trace)) in before_operator
        .primitive_traces
        .iter()
        .zip(&after_operator.primitive_traces)
        .enumerate()
    {
        println!(
            "  P{:02} {} · source metric {} -> {}{}",
            index + 1,
            format_source_word(&before.construction, &before_trace.source_word),
            format_rat_word(&before_trace.source_chord_word),
            format_rat_word(&after_trace.source_chord_word),
            if before_trace.source_chord_word == after_trace.source_chord_word {
                " · retained"
            } else {
                " · changed"
            }
        );
    }
    println!();

    println!("CROSSING-BEARING LAWFUL LOOPS");
    for (before_trace, after_trace) in before_operator
        .primitive_traces
        .iter()
        .zip(&after_operator.primitive_traces)
        .filter(|(trace, _)| is_crossing_quadrilateral(trace))
    {
        println!(
            "  {}",
            format_source_word(&before.construction, &before_trace.source_word)
        );
        println!(
            "    source metric {} -> {}",
            format_rat_word(&before_trace.source_chord_word),
            format_rat_word(&after_trace.source_chord_word)
        );
        for receiver_index in 0..before_trace.receiver_traces.len() {
            print_receiver_trace(
                &before.construction,
                "before",
                &before_trace.receiver_traces[receiver_index],
            );
            print_receiver_trace(
                &after.construction,
                "after ",
                &after_trace.receiver_traces[receiver_index],
            );
        }
    }
    println!();

    let all_returns_closed = before_operator
        .primitive_traces
        .iter()
        .chain(&after_operator.primitive_traces)
        .flat_map(|trace| &trace.receiver_traces)
        .all(|trace| trace.closed_return == ExactTurn::one());
    let any_crossing_departed = before_operator
        .darts
        .iter()
        .flat_map(|dart| &dart.receiver_faces)
        .any(|face| !face.crossings.is_empty())
        && after_operator
            .darts
            .iter()
            .flat_map(|dart| &dart.receiver_faces)
            .all(|face| face.crossings.is_empty());
    let any_interval_is_nonzero = before_operator
        .darts
        .iter()
        .flat_map(|dart| &dart.receiver_faces)
        .flat_map(|face| &face.intervals)
        .any(|interval| !interval.gauge_chord_squared.is_zero());
    println!("EXACT CONSEQUENCE");
    println!("  all local turn products close as (1,0): {all_returns_closed}");
    println!("  the receiver crossing departs after source emanation: {any_crossing_departed}");
    println!(
        "  the shared refinement carries nonzero exact interval geometry: {any_interval_is_nonzero}"
    );
    println!(
        "  neither the invariant return nor the source word alone identifies the contemporary cut; the ordered decorations do."
    );
}
