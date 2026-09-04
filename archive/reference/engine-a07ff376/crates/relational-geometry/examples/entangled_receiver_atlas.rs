use std::collections::BTreeMap;

use relational_geometry::{
    ConstraintKind, Construction, EntityId, Geometry, GrainedReceiver, MarkedOccurrence,
    OccurrenceId, ProjectionLaw, Rat, RatVec3, Receiver, ReceiverGauge, ReceiverGrain, ReceiverId,
    ReceiverOrientation, SwingCell, analyze_receiver_atlas, compare_receiver_atlases, format_rat,
    integer, rat, triangle_face_signature,
};

struct State {
    construction: Construction,
    occurrences: Vec<MarkedOccurrence>,
    first_triangle: EntityId,
    second_triangle: EntityId,
}

fn point_on_source(parameter: &Rat) -> RatVec3 {
    RatVec3::new(
        parameter.clone(),
        parameter / integer(2) + rat(1, 10),
        parameter / integer(3) + rat(1, 5),
    )
}

fn build_state(witness_parameter: Rat) -> State {
    let (mut construction, frame) = Construction::new("one causal source");
    let parameters = [
        rat(-3, 4),
        rat(-1, 4),
        Rat::from_integer(0.into()),
        witness_parameter,
        rat(3, 4),
    ];
    let names = ["A", "B", "C", "D", "E"];
    let mut occurrences = parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            MarkedOccurrence::new(
                OccurrenceId(index as u64 + 1),
                names[index],
                frame,
                point_on_source(parameter),
            )
        })
        .collect::<Vec<_>>();
    let pivot = MarkedOccurrence::new(
        OccurrenceId(6),
        "Q",
        frame,
        RatVec3::new(rat(1, 10), rat(9, 10), rat(-1, 5)),
    );
    occurrences.push(pivot.clone());

    let source = construction
        .add_entity(
            "ordered source thread",
            frame,
            Geometry::Thread {
                vertices: occurrences[0..5]
                    .iter()
                    .map(|occurrence| occurrence.point.clone())
                    .collect(),
                closed: false,
            },
        )
        .expect("source frame exists");
    let return_thread = construction
        .add_entity(
            "transverse return thread",
            frame,
            Geometry::Thread {
                vertices: vec![
                    RatVec3::new(rat(-4, 5), rat(4, 5), rat(3, 5)),
                    RatVec3::new(rat(4, 5), rat(-3, 5), rat(-2, 5)),
                ],
                closed: false,
            },
        )
        .expect("source frame exists");
    let first_triangle = construction
        .add_entity(
            "first pivot face",
            frame,
            Geometry::Triangle {
                vertices: [
                    occurrences[0].point.clone(),
                    occurrences[2].point.clone(),
                    pivot.point.clone(),
                ],
            },
        )
        .expect("source frame exists");
    let second_triangle = construction
        .add_entity(
            "emanating pivot face",
            frame,
            Geometry::Triangle {
                vertices: [
                    occurrences[2].point.clone(),
                    occurrences[3].point.clone(),
                    pivot.point,
                ],
            },
        )
        .expect("source frame exists");
    construction.add_constraint(
        "source and return are co-present currents",
        ConstraintKind::Declared {
            expression: format!(
                "thread {} and thread {} participate in one contemporary cut",
                source.0, return_thread.0
            ),
        },
    );
    construction.add_constraint(
        "pivot faces share C",
        ConstraintKind::SharedVertex {
            left: first_triangle,
            right: second_triangle,
            left_vertex: 1,
            right_vertex: 0,
        },
    );
    construction.add_constraint(
        "pivot faces share Q",
        ConstraintKind::SharedVertex {
            left: first_triangle,
            right: second_triangle,
            left_vertex: 2,
            right_vertex: 2,
        },
    );

    State {
        construction,
        occurrences,
        first_triangle,
        second_triangle,
    }
}

fn receiver_family() -> Vec<GrainedReceiver> {
    let frame = relational_geometry::FrameId(1);
    let mut coarse = Receiver::new(
        ReceiverId(1),
        "coarse square carrier",
        frame,
        ProjectionLaw::Orthographic,
    );
    coarse.gauge = ReceiverGauge {
        anchor: RatVec3::zero(),
        reference: RatVec3::from_i64(1, 0, 0),
    };

    let mut portrait = Receiver::new(
        ReceiverId(2),
        "portrait perspective intermediary",
        frame,
        ProjectionLaw::PerspectiveRay {
            focal_distance: integer(6),
        },
    );
    portrait.orientation = ReceiverOrientation::from_cayley_xyz(rat(1, 5), rat(-1, 4), rat(1, 3));
    portrait.gauge = ReceiverGauge {
        anchor: RatVec3::new(rat(1, 5), rat(-1, 7), rat(1, 6)),
        reference: RatVec3::from_i64(0, 1, 1),
    };

    let mut wide = Receiver::new(
        ReceiverId(3),
        "wide stereographic witness",
        frame,
        ProjectionLaw::StereographicNorth,
    );
    wide.orientation = ReceiverOrientation::from_cayley_xyz(rat(-1, 6), rat(1, 5), rat(-1, 4));
    wide.gauge = ReceiverGauge {
        anchor: RatVec3::new(rat(-1, 6), rat(1, 8), rat(1, 5)),
        reference: RatVec3::from_i64(1, 1, 0),
    };

    let mut oblique = Receiver::new(
        ReceiverId(4),
        "oblique return carrier",
        frame,
        ProjectionLaw::Orthographic,
    );
    oblique.orientation = ReceiverOrientation::from_cayley_xyz(rat(1, 7), rat(-1, 2), rat(-1, 3));
    oblique.gauge = ReceiverGauge {
        anchor: RatVec3::new(rat(1, 9), rat(1, 9), rat(-1, 9)),
        reference: RatVec3::from_i64(1, -1, 1),
    };

    vec![
        GrainedReceiver {
            receiver: coarse,
            grain: ReceiverGrain::new(3, 3),
        },
        GrainedReceiver {
            receiver: portrait,
            grain: ReceiverGrain::new(73, 127),
        },
        GrainedReceiver {
            receiver: wide,
            grain: ReceiverGrain::new(23, 7),
        },
        GrainedReceiver {
            receiver: oblique,
            grain: ReceiverGrain::new(17, 9),
        },
    ]
}

fn swing_cells() -> Vec<SwingCell> {
    vec![
        SwingCell {
            id: 1,
            name: "(A,B,C) pivots D".to_owned(),
            pivot: [OccurrenceId(1), OccurrenceId(2), OccurrenceId(3)],
            witness: OccurrenceId(4),
        },
        SwingCell {
            id: 2,
            name: "(B,C,D) pivots E".to_owned(),
            pivot: [OccurrenceId(2), OccurrenceId(3), OccurrenceId(4)],
            witness: OccurrenceId(5),
        },
    ]
}

fn format_cells(cells: &[relational_geometry::PixelCell]) -> String {
    if cells.is_empty() {
        return "outside".to_owned();
    }
    cells
        .iter()
        .map(|cell| format!("({}, {})", cell.column, cell.row))
        .collect::<Vec<_>>()
        .join("|")
}

fn format_ratios(values: &[Rat; 3]) -> String {
    values
        .iter()
        .map(format_rat)
        .collect::<Vec<_>>()
        .join(" : ")
}

fn main() {
    let receivers = receiver_family();
    let cells = swing_cells();
    let before_state = build_state(rat(1, 4));
    let after_state = build_state(rat(1, 3));
    let before = analyze_receiver_atlas(
        &before_state.construction,
        &receivers,
        &before_state.occurrences,
        &cells,
    )
    .expect("the initial receiver atlas is exact");
    let after = analyze_receiver_atlas(
        &after_state.construction,
        &receivers,
        &after_state.occurrences,
        &cells,
    )
    .expect("the emanated receiver atlas is exact");
    let emanation =
        compare_receiver_atlases(&before, &after).expect("the two cuts retain one identity family");

    println!("ENTANGLED RECEIVER ATLAS 01");
    println!("one source cut; four independently grained receiver faces");
    println!();

    for face in &before.faces {
        println!(
            "RECEIVER {} · {} · grain {}x{} · aspect {}",
            face.receiver.0,
            face.receiver_name,
            face.grain.width,
            face.grain.height,
            format_rat(&face.grain.aspect_ratio())
        );
        for occurrence in &face.occurrences {
            let point = occurrence
                .projected
                .rational
                .as_ref()
                .expect("bounded analysis uses rational projections");
            let cells = occurrence
                .aperture
                .as_ref()
                .map(|address| format_cells(&address.cells))
                .unwrap_or_else(|| "unavailable".to_owned());
            println!(
                "  {} -> ({}, {}) · aperture {}",
                occurrence.name,
                format_rat(&point.x),
                format_rat(&point.y),
                cells
            );
        }
        for crossing in &face.crossings.crossings {
            println!(
                "  crossing e{}:{} x e{}:{} at ({}, {}) · over e{} · orientation {}",
                crossing.first_entity.0,
                crossing.first_segment,
                crossing.second_entity.0,
                crossing.second_segment,
                format_rat(&crossing.point.x),
                format_rat(&crossing.point.y),
                crossing.over_entity.0,
                crossing.orientation_sign
            );
        }
        for discriminant in &face.crossings.discriminants {
            println!(
                "  discriminant e{}:{} x e{}:{} · {:?}",
                discriminant.first_entity.0,
                discriminant.first_segment,
                discriminant.second_entity.0,
                discriminant.second_segment,
                discriminant.kind
            );
        }
        let first_signature = triangle_face_signature(
            &before_state.construction,
            before_state.first_triangle,
            &receivers
                .iter()
                .find(|candidate| candidate.receiver.id == face.receiver)
                .expect("receiver remains in family")
                .receiver,
        )
        .expect("first face is a triangle");
        let second_signature = triangle_face_signature(
            &before_state.construction,
            before_state.second_triangle,
            &receivers
                .iter()
                .find(|candidate| candidate.receiver.id == face.receiver)
                .expect("receiver remains in family")
                .receiver,
        )
        .expect("second face is a triangle");
        println!(
            "  triangle A-C-Q ratios {} · parity {}",
            format_ratios(&first_signature.side_ratios),
            first_signature.parity
        );
        println!(
            "  triangle C-D-Q ratios {} · parity {}",
            format_ratios(&second_signature.side_ratios),
            second_signature.parity
        );
        println!();
    }

    println!("SHARED FOUR-MEMBER SWINGS");
    for swing in &before.swings {
        let values = swing
            .receiver_values
            .iter()
            .map(|(receiver, value)| format!("r{}={}", receiver.0, format_rat(value)))
            .collect::<Vec<_>>()
            .join(", ");
        println!(
            "  {} · {} · invariant {} · {}",
            swing.cell,
            swing.name,
            swing
                .invariant
                .as_ref()
                .map(format_rat)
                .unwrap_or_else(|| "OPEN".to_owned()),
            values
        );
    }
    println!();

    println!("VARIABLE-GRAIN RELATIONS");
    for comparison in &before.grain_comparisons {
        if !comparison.indistinguishable_at.is_empty() && !comparison.distinguished_at.is_empty() {
            println!(
                "  {:?}<->{:?} · same at {:?} · separated at {:?}",
                comparison.first,
                comparison.second,
                comparison.indistinguishable_at,
                comparison.distinguished_at
            );
        }
    }
    println!();

    println!("ONE SOURCE EMANATION · D: 1/4 -> 1/3");
    for occurrence in &emanation.occurrences {
        if !occurrence.changed_faces.is_empty() {
            println!(
                "  {:?} · exact face changed at {:?} · grain-visible {:?} · grain-dark {:?}",
                occurrence.occurrence,
                occurrence.changed_faces,
                occurrence.grain_visible_at,
                occurrence.grain_dark_at
            );
        }
    }
    for swing in &emanation.swings {
        if !swing.changed_at.is_empty() {
            println!(
                "  swing {} · {} -> {} · changed at {:?}",
                swing.cell,
                swing
                    .before
                    .as_ref()
                    .map(format_rat)
                    .unwrap_or_else(|| "OPEN".to_owned()),
                swing
                    .after
                    .as_ref()
                    .map(format_rat)
                    .unwrap_or_else(|| "OPEN".to_owned()),
                swing.changed_at
            );
        }
    }
    println!();

    println!("SECOND TRIANGLE AFTER EMANATION");
    let receiver_rows = receivers
        .iter()
        .map(|receiver| (receiver.receiver.id, &receiver.receiver))
        .collect::<BTreeMap<_, _>>();
    for face in &after.faces {
        let signature = triangle_face_signature(
            &after_state.construction,
            after_state.second_triangle,
            receiver_rows[&face.receiver],
        )
        .expect("emanating face remains a triangle");
        println!(
            "  r{} · ratios {} · parity {}",
            face.receiver.0,
            format_ratios(&signature.side_ratios),
            signature.parity
        );
    }
}
