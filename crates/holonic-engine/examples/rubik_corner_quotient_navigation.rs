//! Exact quotient navigation induced by genuine Rubik's Cube face turns.
//!
//! Each marked corner is a signed coordinate vertex of the cube. A face quarter-turn is derived
//! geometrically by rotating the four vertices on that face; the six resulting 4-cycles generate
//! the full S8 corner-permutation projection. Corner orientation and edge coordinates are
//! intentionally omitted, so the returned distance is an exact quotient lower bound for a full
//! cube state in the quarter-turn metric, not a full-cube God's Algorithm solution.

use holonic_engine::{
    group_navigation::{ExactGroupNavigation, NavigationMove},
    structure_group::{GroupElement, StructureGroup},
};
use serde_json::json;
use std::time::Instant;

type Vertex = (i8, i8, i8);
type Sticker = (Vertex, Vertex);

const VERTICES: [Vertex; 8] = [
    (1, 1, 1),
    (1, 1, -1),
    (1, -1, 1),
    (1, -1, -1),
    (-1, 1, 1),
    (-1, 1, -1),
    (-1, -1, 1),
    (-1, -1, -1),
];

fn rotate(axis: usize, direction: i8, vertex: Vertex) -> Vertex {
    let (x, y, z) = vertex;
    match (axis, direction) {
        (0, 1) => (x, -z, y),
        (0, -1) => (x, z, -y),
        (1, 1) => (z, y, -x),
        (1, -1) => (-z, y, x),
        (2, 1) => (-y, x, z),
        (2, -1) => (y, -x, z),
        _ => unreachable!("only signed coordinate quarter-turns are admitted"),
    }
}

fn face_turn(axis: usize, face_sign: i8) -> GroupElement {
    let images = VERTICES
        .iter()
        .map(|vertex| {
            let coordinate = [vertex.0, vertex.1, vertex.2][axis];
            let image = if coordinate == face_sign {
                rotate(axis, face_sign, *vertex)
            } else {
                *vertex
            };
            VERTICES
                .iter()
                .position(|candidate| *candidate == image)
                .unwrap() as u8
        })
        .collect();
    GroupElement::Permutation(images)
}

fn sticker_slots() -> Vec<Sticker> {
    let mut slots = Vec::with_capacity(54);
    for axis in 0..3 {
        let free = (0..3)
            .filter(|coordinate| *coordinate != axis)
            .collect::<Vec<_>>();
        for face_sign in [-1, 1] {
            for first in -1..=1 {
                for second in -1..=1 {
                    let mut position = [0i8; 3];
                    let mut normal = [0i8; 3];
                    position[axis] = face_sign;
                    normal[axis] = face_sign;
                    position[free[0]] = first;
                    position[free[1]] = second;
                    slots.push((
                        (position[0], position[1], position[2]),
                        (normal[0], normal[1], normal[2]),
                    ));
                }
            }
        }
    }
    slots
}

fn sticker_turn(axis: usize, face_sign: i8) -> GroupElement {
    let slots = sticker_slots();
    let images = slots
        .iter()
        .map(|(position, normal)| {
            let (next_position, next_normal) = if position.0 == face_sign && axis == 0
                || position.1 == face_sign && axis == 1
                || position.2 == face_sign && axis == 2
            {
                (
                    rotate(axis, face_sign, *position),
                    rotate(axis, face_sign, *normal),
                )
            } else {
                (*position, *normal)
            };
            slots
                .iter()
                .position(|candidate| *candidate == (next_position, next_normal))
                .unwrap() as u8
        })
        .collect();
    GroupElement::Permutation(images)
}

fn element_wire(element: &GroupElement) -> serde_json::Value {
    match element {
        GroupElement::Permutation(images) => json!({"kind":"permutation", "images":images}),
        GroupElement::Quaternion(values) => json!({"kind":"quaternion", "values":values}),
    }
}

fn corner_projection(full: &GroupElement) -> GroupElement {
    let GroupElement::Permutation(images) = full else {
        panic!("facelet permutation required")
    };
    let slots = sticker_slots();
    GroupElement::Permutation(
        VERTICES
            .iter()
            .map(|vertex| {
                let positions = slots
                    .iter()
                    .enumerate()
                    .filter(|(_, (position, _))| position == vertex)
                    .map(|(index, _)| slots[usize::from(images[index])].0)
                    .collect::<Vec<_>>();
                assert_eq!(positions.len(), 3);
                assert!(positions.iter().all(|position| *position == positions[0]));
                VERTICES
                    .iter()
                    .position(|position| *position == positions[0])
                    .unwrap() as u8
            })
            .collect(),
    )
}

fn full_word(full_named: &[(&str, GroupElement)], labels: &[String]) -> GroupElement {
    labels
        .iter()
        .fold(full_named[0].1.identity_like().unwrap(), |state, label| {
            let base = &full_named
                .iter()
                .find(|(name, _)| *name == label.trim_end_matches('\''))
                .unwrap()
                .1;
            let movement = if label.ends_with('\'') {
                base.inverse().unwrap()
            } else {
                base.clone()
            };
            state.then(&movement).unwrap()
        })
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let total_start = Instant::now();
    let named = [
        ("R", face_turn(0, 1)),
        ("L", face_turn(0, -1)),
        ("U", face_turn(1, 1)),
        ("D", face_turn(1, -1)),
        ("F", face_turn(2, 1)),
        ("B", face_turn(2, -1)),
    ];
    let closure_start = Instant::now();
    let group = StructureGroup::close(named.iter().map(|(_, element)| element.clone()), 40_320)?;
    let closure_ns = closure_start.elapsed().as_nanos();
    assert_eq!(
        group.order(),
        40_320,
        "the six geometric face turns generate S8"
    );
    let target = group.identity().clone();
    let navigation_start = Instant::now();
    let navigation = ExactGroupNavigation::new(
        group.clone(),
        target.clone(),
        named
            .iter()
            .map(|(label, element)| NavigationMove::new(*label, element.clone(), 1).unwrap()),
    )?;
    let navigation_ns = navigation_start.elapsed().as_nanos();
    // Check the local certificate independently of Dijkstra's relaxation order. These are the
    // edge/goal/descent hypotheses of Foundation.TransportWord.descendingWord_is_optimal.
    let mut certified_edges = 0usize;
    for state in group.elements() {
        let distance = navigation.distance(state)?;
        assert_eq!(distance == 0, state == &target);
        if distance > 0 {
            assert!(!navigation.minimizing_fibre(state)?.is_empty());
        }
        for (_, generator) in &named {
            for movement in [generator.clone(), generator.inverse().unwrap()] {
                let next = state.then(&movement).unwrap();
                assert!(distance <= 1 + navigation.distance(&next)?);
                certified_edges += 1;
            }
        }
    }
    let query_start = Instant::now();

    let source = named[2]
        .1
        .then(&named[0].1)
        .ok_or("face-turn composition left S8")?;
    let solution = navigation.solve(source.clone())?;
    assert_eq!(
        solution.steps.iter().map(|step| step.cost).sum::<u32>(),
        solution.distance
    );
    let policy = navigation.minimizing_fibre(&source)?;
    let query_ns = query_start.elapsed().as_nanos();
    let policy_rows = policy
        .iter()
        .map(|step| {
            let next = source.then(&step.element).expect("policy move composes");
            json!({"move":step.label,"cost":step.cost,"next":element_wire(&next)})
        })
        .collect::<Vec<_>>();

    // Lift the same U R scramble to all 54 facelets. The quotient distance is a lower bound for
    // this full state, and the returned inverse word is a known full-state solution. Equality
    // therefore certifies this particular scramble as QTM-optimal without solving all cube states.
    let full_named = [
        ("R", sticker_turn(0, 1)),
        ("L", sticker_turn(0, -1)),
        ("U", sticker_turn(1, 1)),
        ("D", sticker_turn(1, -1)),
        ("F", sticker_turn(2, 1)),
        ("B", sticker_turn(2, -1)),
    ];
    for ((_, corner), (_, full)) in named.iter().zip(&full_named) {
        assert_eq!(corner_projection(full), *corner);
        let squared = corner.then(corner).unwrap();
        assert!(squared.then(&squared).unwrap().is_identity());
    }
    let full_source = full_named[2]
        .1
        .then(&full_named[0].1)
        .ok_or("sticker scramble left its carrier")?;
    let full_solution = solution
        .steps
        .iter()
        .try_fold(full_source.clone(), |state, step| {
            let label = step.label.trim_end_matches('\'');
            let base = full_named
                .iter()
                .find(|(name, _)| *name == label)
                .map(|(_, element)| element.clone())
                .ok_or("policy named an unknown face")?;
            let move_element = if step.label.ends_with('\'') {
                base.inverse().ok_or("face inverse failed")?
            } else {
                base
            };
            state
                .then(&move_element)
                .ok_or("full sticker policy left its carrier")
        })?;
    assert!(
        full_solution.is_identity(),
        "the quotient policy must solve the selected full sticker scramble"
    );

    // Construct a full-state representative of a maximally distant corner fibre. Its returned
    // quotient-optimal word defines a lift whose inverse has that corner source. The matched
    // lower/upper bounds prove optimality of this full 54-sticker representative, not of every
    // possible state in its orientation/edge fibre.
    let farthest = group
        .elements()
        .max_by_key(|state| navigation.distance(state).unwrap())
        .unwrap()
        .clone();
    let far_solution = navigation.solve(farthest.clone())?;
    let far_labels = far_solution
        .steps
        .iter()
        .map(|step| step.label.clone())
        .collect::<Vec<_>>();
    let far_word = full_word(&full_named, &far_labels);
    let far_full_source = far_word.inverse().unwrap();
    assert_eq!(corner_projection(&far_full_source), farthest);
    assert!(far_full_source.then(&far_word).unwrap().is_identity());
    assert_eq!(far_solution.distance as usize, far_labels.len());
    let total_ns = total_start.elapsed().as_nanos();

    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "schema": "holonics.exact-group-navigation.v2",
            "scope": "genuine Rubik face-turn S8 corner-permutation quotient",
            "target": element_wire(&target),
            "group_order": group.order(),
            "generators": named.iter().map(|(label, element)| json!({"label":label,"permutation":element_wire(element)})).collect::<Vec<_>>(),
            "generator_metric": {"quarter_turn_cost": 1, "inverse_moves": true},
            "orientation_convention": "base labels are positive quarter turns about outward face normals; apostrophe reverses that declared turn",
            "preprocessing": {"states":navigation.states(),"edges_examined":navigation.edges_examined(),"quotient_diameter":navigation.diameter()},
            "local_optimality_certificate": {"goal_zero_iff":true,"all_nonzero_states_have_descending_move":true,"unit_edges_checked":certified_edges},
            "timing_nanoseconds": {"group_closure":closure_ns,"distance_policy_and_counts":navigation_ns,"selected_query_and_policy":query_ns,"construction_and_checks_before_serialization":total_ns},
            "source": element_wire(&source),
            "distance": solution.distance,
            "optimal_word": solution.steps.iter().map(|step| step.label.clone()).collect::<Vec<_>>(),
            "minimizing_policy_fibre": policy_rows,
            "shortest_word_fibre_size": solution.minimizing_fibre_size.to_string(),
            "full_cube_certificate": {
                "sticker_count": sticker_slots().len(),
                "scramble_word": ["U", "R"],
                "inverse_word": solution.steps.iter().map(|step| step.label.clone()).collect::<Vec<_>>(),
                "inverse_solves_all_stickers": full_solution.is_identity(),
                "quotient_lower_bound": solution.distance,
                "known_full_solution_cost": solution.steps.iter().map(|step| step.cost).sum::<u32>(),
                "optimal_for_this_scramble": solution.distance == solution.steps.iter().map(|step| step.cost).sum::<u32>(),
                "scope": "one admitted full-cube scramble; arbitrary full states still require an orientation/edge lift",
            },
            "farthest_representative_certificate": {
                "corner_source": element_wire(&farthest),
                "full_sticker_source": element_wire(&far_full_source),
                "optimal_word": far_labels,
                "quotient_lower_bound": far_solution.distance,
                "full_solution_cost": far_solution.steps.len(),
                "all_54_stickers_solved": true,
                "scope": "constructively lifted full-state representative attaining the quotient diameter; other states in the fibre retain their additional problem",
            },
            "optimality": "exact weighted Cayley distance in the declared corner-permutation quotient",
            "full_cube_lift": "for any full-cube state with this corner permutation, quotient distance is a QTM lower bound; equality requires an orientation/edge lift ending at the target",
            "omitted_coordinates": ["corner orientation", "edge permutation", "edge orientation", "full 3x3 centre frame"],
        }))?
    );
    Ok(())
}
