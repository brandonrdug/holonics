//! Exact prediction from an unresolved parameter fiber, followed by
//! production-derived model enrichment and an unseen-interval grade.
//!
//! The opaque world membrane owns only caused responses. It never passes its
//! capacities, pair couplings, reactions, or a successor model into
//! production. `GenerativeTransportLaw` diagnoses the failed passive grammar,
//! selects the distinguishing observations, closes its own exact family, and
//! predicts a complete operator at an interval not used for fitting.

use std::error::Error;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use holonic_engine::{
    CausalWorld, EventId, GeneratedTransportSpecies, GenerativeTransportCertificate,
    GenerativeTransportEvent, GenerativeTransportLaw, GenerativeTransportPhase,
    GenerativeTransportStanding, GenerativeTransportWork, ParameterizedTransportQuery,
    TransportExtensionNeed, TransportLineageId,
};
use num_traits::{Signed, Zero};
use relational_geometry::{Rat, format_rat, integer};

const EXTENT: usize = 4;

#[derive(Clone, Debug)]
struct HiddenEdge {
    left: usize,
    right: usize,
    symmetric: Rat,
    skew: Rat,
}

#[derive(Clone, Debug)]
struct OpaqueTransportWorld {
    capacities: Vec<Rat>,
    edges: Vec<HiddenEdge>,
    reactions: Vec<Rat>,
}

impl OpaqueTransportWorld {
    fn fixture() -> Self {
        Self {
            capacities: vec![integer(2), integer(3), integer(1), integer(2)],
            edges: vec![
                HiddenEdge {
                    left: 0,
                    right: 1,
                    symmetric: integer(2),
                    skew: integer(1),
                },
                HiddenEdge {
                    left: 0,
                    right: 2,
                    symmetric: integer(0),
                    skew: integer(-1),
                },
                HiddenEdge {
                    left: 0,
                    right: 3,
                    symmetric: integer(1),
                    skew: integer(0),
                },
                HiddenEdge {
                    left: 1,
                    right: 2,
                    symmetric: integer(1),
                    skew: integer(1),
                },
                HiddenEdge {
                    left: 1,
                    right: 3,
                    symmetric: integer(0),
                    skew: integer(0),
                },
                HiddenEdge {
                    left: 2,
                    right: 3,
                    symmetric: integer(3),
                    skew: integer(0),
                },
            ],
            reactions: vec![integer(1), integer(0), integer(2), integer(0)],
        }
    }

    #[inline(never)]
    fn receive(&self, query: &ParameterizedTransportQuery) -> Rat {
        let standing = self
            .capacities
            .iter()
            .zip(&query.receiver)
            .zip(&query.imposed_potential)
            .fold(integer(0), |sum, ((capacity, receiver), potential)| {
                sum + capacity * receiver * potential
            });
        let transported = self.edges.iter().fold(integer(0), |sum, edge| {
            sum + &edge.symmetric
                * (&query.receiver[edge.left] - &query.receiver[edge.right])
                * (&query.imposed_potential[edge.left] - &query.imposed_potential[edge.right])
                + &edge.skew
                    * (&query.receiver[edge.left] * &query.imposed_potential[edge.right]
                        - &query.receiver[edge.right] * &query.imposed_potential[edge.left])
        });
        let reacted = self
            .reactions
            .iter()
            .zip(&query.receiver)
            .zip(&query.imposed_potential)
            .fold(integer(0), |sum, ((reaction, receiver), potential)| {
                sum + reaction * receiver * potential
            });
        standing + &query.interval * (transported + reacted)
    }

    fn complete_operator(&self, interval: &Rat) -> Result<Vec<Rat>, Box<dyn Error>> {
        (0..EXTENT)
            .flat_map(|row| {
                (0..EXTENT).map(move |column| {
                    let query = basis_query(interval.clone(), row, column)?;
                    Ok(self.receive(&query))
                })
            })
            .collect()
    }

    fn operator_matrix(&self, interval: &Rat) -> Result<Vec<Vec<Rat>>, Box<dyn Error>> {
        Ok(self
            .complete_operator(interval)?
            .chunks_exact(EXTENT)
            .map(<[Rat]>::to_vec)
            .collect())
    }
}

fn basis_query(
    interval: Rat,
    row: usize,
    column: usize,
) -> Result<ParameterizedTransportQuery, Box<dyn Error>> {
    let mut potential = vec![integer(0); EXTENT];
    let mut receiver = vec![integer(0); EXTENT];
    potential[column] = integer(1);
    receiver[row] = integer(1);
    Ok(ParameterizedTransportQuery::new(
        interval, potential, receiver,
    )?)
}

fn basis_coordinate(query: &ParameterizedTransportQuery) -> Option<(usize, usize)> {
    let row = query
        .receiver
        .iter()
        .enumerate()
        .filter(|(_, value)| !value.is_zero())
        .collect::<Vec<_>>();
    let column = query
        .imposed_potential
        .iter()
        .enumerate()
        .filter(|(_, value)| !value.is_zero())
        .collect::<Vec<_>>();
    match (row.as_slice(), column.as_slice()) {
        ([(row, row_value)], [(column, column_value)])
            if *row_value == &integer(1) && *column_value == &integer(1) =>
        {
            Some((*row, *column))
        }
        _ => None,
    }
}

fn add_work(
    total: &mut GenerativeTransportWork,
    received: &GenerativeTransportWork,
) -> Result<(), Box<dyn Error>> {
    total.exact_row_eliminations = total
        .exact_row_eliminations
        .checked_add(received.exact_row_eliminations)
        .ok_or("row-elimination work overflow")?;
    total.inspected_operator_coordinates = total
        .inspected_operator_coordinates
        .checked_add(received.inspected_operator_coordinates)
        .ok_or("coordinate-inspection work overflow")?;
    Ok(())
}

fn apply_operator(operator: &[Vec<Rat>], vector: &[Rat]) -> Result<Vec<Rat>, Box<dyn Error>> {
    if operator.len() != vector.len() || operator.iter().any(|row| row.len() != vector.len()) {
        return Err("held-out operator and vector dimensions disagree".into());
    }
    Ok(operator
        .iter()
        .map(|row| {
            row.iter()
                .zip(vector)
                .fold(integer(0), |sum, (coefficient, value)| {
                    sum + coefficient * value
                })
        })
        .collect())
}

/// An outer ordinal inspection projection. Its positions, bends, colors, and
/// chronology strip are presentation only; exact model values remain in text
/// and `data-*` attributes.
fn write_svg(
    certificate: &GenerativeTransportCertificate,
    affine_dimensions: &[usize],
) -> Result<PathBuf, Box<dyn Error>> {
    let positions = [(120_i64, 135_i64), (355, 80), (610, 155), (375, 325)];
    let mut svg = String::new();
    writeln!(
        svg,
        r#"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 760 560" data-schema="holonic-engine.generative-transport-svg.v1">"#
    )?;
    writeln!(
        svg,
        "  <metadata>Exact generated transport model in a non-intrinsic ordinal inspection projection. Geometry and color do not define the physical law.</metadata>"
    )?;
    writeln!(
        svg,
        r##"  <defs><marker id="skew-arrow" markerWidth="8" markerHeight="8" refX="7" refY="4" orient="auto"><path d="M0,0 L8,4 L0,8 Z" fill="#a13d2d"/></marker></defs>"##
    )?;
    writeln!(
        svg,
        r##"  <rect width="760" height="560" fill="#f7f3e8"/>"##
    )?;
    writeln!(
        svg,
        r##"  <text x="28" y="34" font-family="monospace" font-size="18" fill="#172a2a">generated exact transport: M + τ(S + K + R)</text>"##
    )?;

    for (ordinal, edge) in certificate.model.edges.iter().enumerate() {
        if edge.symmetric_coupling.is_zero() && edge.skew_coupling.is_zero() {
            continue;
        }
        let left = usize::try_from(edge.edge.left)?;
        let right = usize::try_from(edge.edge.right)?;
        let (x1, y1) = positions[left];
        let (x2, y2) = positions[right];
        let midpoint_x = (x1 + x2) / 2;
        let midpoint_y = (y1 + y2) / 2;
        let symmetric = format_rat(&edge.symmetric_coupling);
        let skew = format_rat(&edge.skew_coupling);
        if !edge.symmetric_coupling.is_zero() {
            let stroke = if edge.symmetric_coupling.is_positive() {
                "#174f52"
            } else {
                "#7a355f"
            };
            writeln!(
                svg,
                r##"  <line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="{stroke}" stroke-width="4" data-edge="{left}-{right}" data-symmetric="{symmetric}"/>"##
            )?;
        }
        if !edge.skew_coupling.is_zero() {
            let bend = if ordinal % 2 == 0 { 34_i64 } else { -34_i64 };
            let control_x = midpoint_x + bend;
            let control_y = midpoint_y - bend;
            writeln!(
                svg,
                r##"  <path d="M{x1},{y1} Q{control_x},{control_y} {x2},{y2}" fill="none" stroke="#a13d2d" stroke-width="3" marker-end="url(#skew-arrow)" data-edge="{left}-{right}" data-skew="{skew}"/>"##
            )?;
        }
        writeln!(
            svg,
            r##"  <rect x="{}" y="{}" width="112" height="24" rx="4" fill="#f7f3e8" opacity="0.9"/>"##,
            midpoint_x - 56,
            midpoint_y - 17
        )?;
        writeln!(
            svg,
            r##"  <text x="{midpoint_x}" y="{midpoint_y}" text-anchor="middle" font-family="monospace" font-size="13" fill="#172a2a">S={symmetric} K={skew}</text>"##
        )?;
    }

    for (node, ((x, y), (capacity, reaction))) in positions
        .iter()
        .copied()
        .zip(
            certificate
                .model
                .capacities
                .iter()
                .zip(&certificate.model.reactions),
        )
        .enumerate()
    {
        let capacity = format_rat(capacity);
        let reaction = format_rat(reaction);
        writeln!(
            svg,
            r##"  <circle cx="{x}" cy="{y}" r="41" fill="#f7f3e8" stroke="#172a2a" stroke-width="4" data-node="{node}" data-capacity="{capacity}" data-reaction="{reaction}"/>"##
        )?;
        writeln!(
            svg,
            r##"  <text x="{x}" y="{}" text-anchor="middle" font-family="monospace" font-size="18" fill="#172a2a">n{node}</text>"##,
            y - 5
        )?;
        writeln!(
            svg,
            r##"  <text x="{x}" y="{}" text-anchor="middle" font-family="monospace" font-size="13" fill="#172a2a">M={capacity} R={reaction}</text>"##,
            y + 17
        )?;
    }

    writeln!(
        svg,
        r##"  <line x1="60" y1="455" x2="700" y2="455" stroke="#172a2a" stroke-width="2"/>"##
    )?;
    writeln!(
        svg,
        r##"  <text x="60" y="420" font-family="monospace" font-size="14" fill="#172a2a">τ=1 obstruction leaves dim {}</text>"##,
        affine_dimensions[0]
    )?;
    for (ordinal, dimension) in affine_dimensions.iter().copied().skip(1).enumerate() {
        let x = 205_i64 + 85 * i64::try_from(ordinal)?;
        writeln!(
            svg,
            r##"  <circle cx="{x}" cy="455" r="8" fill="#174f52" data-discrimination-return="{}" data-affine-dimension="{dimension}"/>"##,
            ordinal + 1
        )?;
        writeln!(
            svg,
            r##"  <text x="{x}" y="486" text-anchor="middle" font-family="monospace" font-size="13" fill="#172a2a">τ=2 dim {dimension}</text>"##
        )?;
    }
    writeln!(
        svg,
        r##"  <circle cx="660" cy="455" r="10" fill="#a13d2d" data-prediction-grade="exact"/>"##
    )?;
    writeln!(
        svg,
        r##"  <text x="660" y="486" text-anchor="middle" font-family="monospace" font-size="13" fill="#172a2a">τ=3 grade</text>"##
    )?;
    writeln!(
        svg,
        r##"  <text x="60" y="532" font-family="monospace" font-size="13" fill="#4b5656">ordinal projection only; exact values are carried by the model and receiver testimony</text>"##
    )?;
    writeln!(svg, "</svg>")?;

    let directory = PathBuf::from("target/holonic-engine");
    fs::create_dir_all(&directory)?;
    let path = directory.join("generative_transport_prediction.svg");
    fs::write(&path, svg)?;
    Ok(path)
}

fn main() -> Result<(), Box<dyn Error>> {
    let hidden = OpaqueTransportWorld::fixture();
    let initial_interval = integer(1);
    let law = GenerativeTransportLaw::new(u32::try_from(EXTENT)?, initial_interval.clone())?;
    let standing =
        GenerativeTransportStanding::new(u32::try_from(EXTENT)?, initial_interval.clone())?;
    let mut world = CausalWorld::new(law, standing);
    let receiver = TransportLineageId(41);
    let mut event = 10_000_u64;
    let mut work = GenerativeTransportWork::default();

    let receipt = world.receive(&GenerativeTransportEvent::ReturnCompleteOperator {
        event: EventId(event),
        receiver,
        interval: initial_interval,
        responses: hidden.complete_operator(&integer(1))?,
    })?;
    event += 1;
    add_work(&mut work, &receipt.radiation[0].work)?;
    if world.standing().phase != GenerativeTransportPhase::ResolvingExtension {
        return Err("the hidden world unexpectedly inhabited the passive base grammar".into());
    }
    let obstruction = world
        .standing()
        .obstruction()
        .ok_or("the failed base grammar did not remain as an obstruction")?
        .clone();
    let initial_affine_dimension = world
        .standing()
        .family()
        .ok_or("the obstruction did not cause a parameter family")?
        .affine_dimension();
    let mut affine_dimensions = vec![initial_affine_dimension];

    let prediction_interval = world.standing().prediction_interval.clone();
    let determined_query = basis_query(prediction_interval.clone(), 0, 1)?;
    let determined_before_closure = world.standing().predict(&determined_query)?;
    let returned_determined_before_closure = hidden.receive(&determined_query);
    if determined_before_closure.determined_value() != Some(&returned_determined_before_closure) {
        return Err("a determined pre-closure prediction disagreed with the opaque world".into());
    }
    let open_query = basis_query(prediction_interval.clone(), 0, 0)?;
    let open_before_closure = world.standing().predict(&open_query)?;
    if open_before_closure.is_determined() || open_before_closure.unresolved_variables.is_empty() {
        return Err("the capacity/reaction ambiguity was hidden rather than retained".into());
    }

    let mut selected_coordinates = Vec::new();
    while let Some(query) = world.standing().next_query().cloned() {
        selected_coordinates.push(
            basis_coordinate(&query)
                .ok_or("production selected a non-basis discrimination query unexpectedly")?,
        );
        let response = hidden.receive(&query);
        let receipt = world.receive(&GenerativeTransportEvent::ReturnObservation {
            event: EventId(event),
            receiver,
            query,
            response,
        })?;
        event += 1;
        add_work(&mut work, &receipt.radiation[0].work)?;
        affine_dimensions.push(
            world
                .standing()
                .family()
                .ok_or("parameter family disappeared before prediction grade")?
                .affine_dimension(),
        );
    }
    if selected_coordinates != vec![(0, 0), (1, 1), (2, 2), (3, 3)]
        || affine_dimensions != vec![4, 3, 2, 1, 0]
    {
        return Err("production did not isolate exactly the four open diagonal directions".into());
    }

    let aggregate_query = ParameterizedTransportQuery::new(
        prediction_interval.clone(),
        vec![integer(2), integer(-1), integer(0), integer(3)],
        vec![integer(1), integer(0), integer(2), integer(-1)],
    )?;
    let aggregate_before_grade = world.standing().predict(&aggregate_query)?;
    let returned_aggregate_before_grade = hidden.receive(&aggregate_query);
    if aggregate_before_grade.determined_value() != Some(&returned_aggregate_before_grade) {
        return Err("the generated pre-grade aggregate prediction disagreed".into());
    }

    let receipt = world.receive(&GenerativeTransportEvent::ReturnCompleteOperator {
        event: EventId(event),
        receiver,
        interval: prediction_interval.clone(),
        responses: hidden.complete_operator(&prediction_interval)?,
    })?;
    add_work(&mut work, &receipt.radiation[0].work)?;
    world.standing().validate()?;
    let certificate = world
        .standing()
        .certificate()
        .ok_or("the unseen complete operator did not certify")?;

    let held_out_interval = integer(5);
    let held_out_query = ParameterizedTransportQuery::new(
        held_out_interval.clone(),
        vec![integer(-2), integer(1), integer(3), integer(0)],
        vec![integer(0), integer(2), integer(-1), integer(1)],
    )?;
    let predicted_held_out = certificate.model.clamped_response(&held_out_query)?;
    let returned_held_out = hidden.receive(&held_out_query);
    if predicted_held_out != returned_held_out {
        return Err("the τ=5 held-out aggregate prediction disagreed".into());
    }
    let generated_operator = certificate.model.event_operator(&held_out_interval)?;
    let hidden_operator = hidden.operator_matrix(&held_out_interval)?;
    if generated_operator != hidden_operator {
        return Err("the generated τ=5 operator disagreed with the opaque world".into());
    }
    let right_hand = vec![integer(5), integer(-1), integer(2), integer(0)];
    let propagation = certificate
        .model
        .propagate(held_out_interval, right_hand.clone())?;
    if apply_operator(&hidden_operator, &propagation.potential)? != right_hand {
        return Err("the generated propagation failed in the opaque τ=5 operator".into());
    }

    let svg_path = write_svg(certificate, &affine_dimensions)?;
    let generated_edges = certificate
        .model
        .edges
        .iter()
        .filter(|edge| !edge.symmetric_coupling.is_zero() || !edge.skew_coupling.is_zero())
        .map(|edge| {
            (
                edge.edge,
                format_rat(&edge.symmetric_coupling),
                format_rat(&edge.skew_coupling),
            )
        })
        .collect::<Vec<_>>();
    let needs = obstruction
        .extension_needs
        .iter()
        .copied()
        .collect::<Vec<TransportExtensionNeed>>();
    let species = certificate
        .model
        .species
        .iter()
        .copied()
        .collect::<Vec<GeneratedTransportSpecies>>();

    println!("schema\tholonic-engine.generative-transport-instrument.v1");
    println!("initial_interval\t1");
    println!("initial_obstruction_needs\t{needs:?}");
    println!("initial_affine_dimension\t{initial_affine_dimension}");
    println!(
        "preclosure_determined_coordinate\t(0,1)={}",
        format_rat(&returned_determined_before_closure)
    );
    println!(
        "preclosure_open_coordinate\t(0,0) free={:?}",
        open_before_closure.unresolved_variables
    );
    println!("production_selected_queries\t{selected_coordinates:?}");
    println!("affine_dimensions\t{affine_dimensions:?}");
    println!("generated_species\t{species:?}");
    println!(
        "generated_capacities\t{:?}",
        certificate
            .model
            .capacities
            .iter()
            .map(format_rat)
            .collect::<Vec<_>>()
    );
    println!(
        "generated_reactions\t{:?}",
        certificate
            .model
            .reactions
            .iter()
            .map(format_rat)
            .collect::<Vec<_>>()
    );
    println!("generated_edges\t{generated_edges:?}");
    println!(
        "pregrade_aggregate_prediction\t{}",
        format_rat(&returned_aggregate_before_grade)
    );
    println!("unseen_prediction_interval\t3");
    println!("unseen_complete_operator_exact\ttrue");
    println!(
        "held_out_tau5_aggregate\t{}",
        format_rat(&predicted_held_out)
    );
    println!(
        "held_out_tau5_potential\t{:?}",
        propagation
            .potential
            .iter()
            .map(format_rat)
            .collect::<Vec<_>>()
    );
    println!(
        "held_out_tau5_net_exchange\t{}",
        format_rat(&propagation.net_exchange)
    );
    println!("exact_row_eliminations\t{}", work.exact_row_eliminations);
    println!(
        "inspected_operator_coordinates\t{}",
        work.inspected_operator_coordinates
    );
    println!("standing_exactly_validated\ttrue");
    println!("svg_receiver_projection\t{}", svg_path.display());
    Ok(())
}
