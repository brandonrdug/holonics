//! Reconstruction of an opaque passive transport ecology from exact aggregate
//! lineage and production-owned receiver experiments.
//!
//! The hidden graph is available only to the world membrane. The production
//! `InverseTransportLaw` receives clamped-potential responses, retains an
//! affine version fiber over every potential edge, requests its own missing
//! edge sections, and accepts the topology only after a complete operator
//! basis return.

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;

use holonic_engine::{
    CausalWorld, CurrentBranchId, CurrentNodeId, DiffusionBranch, DiffusionComplex, DiffusionEvent,
    DiffusionNode, ExactDiffusionLaw, InverseTransportCertificate, InverseTransportEvent,
    InverseTransportLaw, InverseTransportStanding, InverseTransportWork, PotentialTransportEdge,
    TransportLineageId, TransportQuery,
};
use relational_geometry::{Rat, format_rat, integer};

const EXTENT: usize = 6;

#[derive(Clone, Debug)]
struct ReconstructionReceipt {
    standing: InverseTransportStanding,
    imported_landmarks: u64,
    returned_queries: u64,
    complete_returns: u64,
    affine_dimensions: Vec<usize>,
    work: InverseTransportWork,
}

fn hidden_edge_material() -> Vec<(u32, u32, i64)> {
    vec![
        (0, 1, 2),
        (0, 2, 1),
        (1, 2, 3),
        (1, 4, 1),
        (2, 3, 1),
        (3, 4, 2),
        (3, 5, 1),
        (4, 5, 4),
    ]
}

fn hidden_complex() -> DiffusionComplex {
    let nodes = (0..EXTENT)
        .map(|ordinal| DiffusionNode {
            node: CurrentNodeId(u64::try_from(ordinal).unwrap() + 1),
            capacity: integer(1),
        })
        .collect::<Vec<_>>();
    let branches = hidden_edge_material()
        .into_iter()
        .enumerate()
        .map(|(ordinal, (left, right, conductance))| DiffusionBranch {
            branch: CurrentBranchId(u64::try_from(ordinal).unwrap() + 1),
            source: CurrentNodeId(u64::from(left) + 1),
            target: CurrentNodeId(u64::from(right) + 1),
            conductance: integer(conductance),
        })
        .collect::<Vec<_>>();
    DiffusionComplex::new(nodes, branches).expect("hidden ecology is exact and passive")
}

/// The opaque clamped-potential membrane. Production never receives the
/// branches used to evaluate this response.
#[inline(never)]
fn opaque_transport_response(
    complex: &DiffusionComplex,
    interval: &Rat,
    query: &TransportQuery,
) -> Rat {
    let baseline = query
        .receiver
        .iter()
        .zip(&query.imposed_potential)
        .fold(Rat::from_integer(0.into()), |sum, (receiver, potential)| {
            sum + receiver * potential
        });
    complex.branches().values().fold(baseline, |sum, branch| {
        let left = usize::try_from(branch.source.0 - 1).expect("hidden node ordinal");
        let right = usize::try_from(branch.target.0 - 1).expect("hidden node ordinal");
        sum + interval
            * &branch.conductance
            * (&query.receiver[left] - &query.receiver[right])
            * (&query.imposed_potential[left] - &query.imposed_potential[right])
    })
}

fn complete_operator(complex: &DiffusionComplex, interval: &Rat) -> Vec<Rat> {
    (0..EXTENT)
        .flat_map(|row| {
            (0..EXTENT).map(move |column| {
                let mut potential = vec![integer(0); EXTENT];
                let mut receiver = vec![integer(0); EXTENT];
                potential[column] = integer(1);
                receiver[row] = integer(1);
                opaque_transport_response(
                    complex,
                    interval,
                    &TransportQuery::new(potential, receiver).expect("basis query"),
                )
            })
        })
        .collect()
}

fn cut_query(members: &[usize]) -> TransportQuery {
    let mut section = vec![integer(0); EXTENT];
    for member in members {
        section[*member] = integer(1);
    }
    TransportQuery::new(section.clone(), section).expect("cut is a nonempty receiver section")
}

fn inherited_cut_landmarks() -> Vec<TransportQuery> {
    vec![
        cut_query(&[0]),
        cut_query(&[1]),
        cut_query(&[2]),
        cut_query(&[0, 1]),
        cut_query(&[0, 2]),
    ]
}

fn add_work(
    total: &mut InverseTransportWork,
    received: &InverseTransportWork,
) -> Result<(), Box<dyn Error>> {
    total.exact_row_eliminations = total
        .exact_row_eliminations
        .checked_add(received.exact_row_eliminations)
        .ok_or("row-elimination work overflow")?;
    total.inspected_edge_coordinates = total
        .inspected_edge_coordinates
        .checked_add(received.inspected_edge_coordinates)
        .ok_or("edge-inspection work overflow")?;
    Ok(())
}

fn reconstruct(
    complex: &DiffusionComplex,
    with_lineage: bool,
    event_base: u64,
) -> Result<ReconstructionReceipt, Box<dyn Error>> {
    let interval = integer(1);
    let law = InverseTransportLaw::new(u32::try_from(EXTENT)?, interval.clone())?;
    let standing = InverseTransportStanding::new(u32::try_from(EXTENT)?, interval.clone())?;
    let mut world = CausalWorld::new(law, standing);
    let mut event = event_base;
    let mut imported_landmarks = 0_u64;
    let mut returned_queries = 0_u64;
    let mut complete_returns = 0_u64;
    let mut affine_dimensions = vec![world.standing().version_fiber().affine_dimension()];
    let mut work = InverseTransportWork::default();

    if with_lineage {
        for (ordinal, query) in inherited_cut_landmarks().into_iter().enumerate() {
            let response = opaque_transport_response(complex, &interval, &query);
            let receipt = world.receive(&InverseTransportEvent::InheritLandmark {
                event: holonic_engine::EventId(event),
                lineage: TransportLineageId(700 + u64::try_from(ordinal)?),
                query,
                response,
            })?;
            event += 1;
            imported_landmarks += 1;
            add_work(&mut work, &receipt.radiation[0].work)?;
            affine_dimensions.push(world.standing().version_fiber().affine_dimension());
        }
    }

    while let Some(query) = world.standing().next_query().cloned() {
        let response = opaque_transport_response(complex, &interval, &query);
        let receipt = world.receive(&InverseTransportEvent::ReturnObservation {
            event: holonic_engine::EventId(event),
            receiver: TransportLineageId(1),
            query,
            response,
        })?;
        event += 1;
        returned_queries += 1;
        add_work(&mut work, &receipt.radiation[0].work)?;
        affine_dimensions.push(world.standing().version_fiber().affine_dimension());
    }

    if world.standing().verification_required() {
        let receipt = world.receive(&InverseTransportEvent::ReturnCompleteOperator {
            event: holonic_engine::EventId(event),
            receiver: TransportLineageId(1),
            responses: complete_operator(complex, &interval),
        })?;
        complete_returns += 1;
        add_work(&mut work, &receipt.radiation[0].work)?;
    }
    world.standing().validate()?;
    Ok(ReconstructionReceipt {
        standing: world.standing().clone(),
        imported_landmarks,
        returned_queries,
        complete_returns,
        affine_dimensions,
        work,
    })
}

fn structural_certificate_equal(
    left: &InverseTransportCertificate,
    right: &InverseTransportCertificate,
) -> bool {
    left.extent == right.extent
        && left.interval == right.interval
        && left.edge_order == right.edge_order
        && left.edge_conductances == right.edge_conductances
        && left.laplacian == right.laplacian
        && left.event_operator == right.event_operator
        && left.transfer_operator == right.transfer_operator
        && left.inverse_residual == right.inverse_residual
        && left.diffusion_complex == right.diffusion_complex
        && left.connected_components == right.connected_components
        && left.cycle_rank == right.cycle_rank
        && left.affine_rank == right.affine_rank
}

fn grade_forward_transport(
    hidden: &DiffusionComplex,
    certificate: &InverseTransportCertificate,
) -> Result<(Vec<Rat>, Rat), Box<dyn Error>> {
    let source = vec![
        integer(3),
        integer(0),
        integer(0),
        integer(0),
        integer(0),
        integer(0),
    ];
    let inferred = certificate.propagate_from_zero(source.clone())?;

    let law = ExactDiffusionLaw::new(hidden.clone())?;
    let initial = law.initial_standing(
        hidden
            .nodes()
            .keys()
            .copied()
            .map(|node| {
                (
                    node,
                    if node == CurrentNodeId(1) {
                        integer(3)
                    } else {
                        integer(0)
                    },
                )
            })
            .collect::<BTreeMap<_, _>>(),
    )?;
    let (hidden_after, receipt) = law.enact(
        &initial,
        &DiffusionEvent {
            interval: integer(1),
            source: BTreeMap::new(),
        },
    )?;
    let hidden_values = hidden
        .nodes()
        .keys()
        .map(|node| hidden_after.content[node].clone())
        .collect::<Vec<_>>();
    if inferred.content_after != hidden_values {
        return Err("reconstructed topology failed the held-out forward event".into());
    }
    Ok((hidden_values, receipt.energy_departed))
}

/// This is an outer ordinal projection for inspection only. The SVG does not
/// claim that graph topology selected an intrinsic Euclidean embedding.
fn write_svg(certificate: &InverseTransportCertificate) -> Result<PathBuf, Box<dyn Error>> {
    let positions = (0..EXTENT)
        .map(|ordinal| {
            let parameter = i64::try_from(ordinal)?;
            Ok((70_i64 + 95 * parameter, 60_i64 + 11 * parameter * parameter))
        })
        .collect::<Result<Vec<_>, std::num::TryFromIntError>>()?;
    let mut svg = String::new();
    writeln!(
        svg,
        r#"<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 640 420" data-schema="holonic-engine.inverse-transport-svg.v1">"#
    )?;
    writeln!(
        svg,
        r#"  <metadata>Exact ordinal moment-curve receiver projection; topology and conductances are exact, embedding is not intrinsic.</metadata>"#
    )?;
    writeln!(
        svg,
        r##"  <rect width="640" height="420" fill="#faf8f2"/>"##
    )?;
    for edge in certificate
        .edge_conductances
        .iter()
        .filter(|edge| edge.conductance > integer(0))
    {
        let left = usize::try_from(edge.edge.left)?;
        let right = usize::try_from(edge.edge.right)?;
        let (x1, y1) = positions[left];
        let (x2, y2) = positions[right];
        let label_x = (x1 + x2) / 2;
        let label_y = (y1 + y2) / 2;
        let conductance = format_rat(&edge.conductance);
        writeln!(
            svg,
            r##"  <line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="#173a3a" stroke-width="4" data-left="{left}" data-right="{right}" data-conductance="{conductance}"/>"##
        )?;
        writeln!(
            svg,
            r##"  <text x="{label_x}" y="{label_y}" font-family="monospace" font-size="16" fill="#173a3a">c={conductance}</text>"##
        )?;
    }
    for (ordinal, (x, y)) in positions.iter().copied().enumerate() {
        writeln!(
            svg,
            r##"  <circle cx="{x}" cy="{y}" r="30" fill="#faf8f2" stroke="#111" stroke-width="3" data-node="{ordinal}"/>"##
        )?;
        writeln!(
            svg,
            r##"  <text x="{x}" y="{}" text-anchor="middle" font-family="monospace" font-size="20" fill="#111">{ordinal}</text>"##,
            y + 7
        )?;
    }
    writeln!(svg, "</svg>")?;

    let directory = PathBuf::from("target/holonic-engine");
    fs::create_dir_all(&directory)?;
    let path = directory.join("inverse_transport_reconstruction.svg");
    fs::write(&path, svg)?;
    Ok(path)
}

fn main() -> Result<(), Box<dyn Error>> {
    let hidden = hidden_complex();
    let cold = reconstruct(&hidden, false, 1_000)?;
    let inherited = reconstruct(&hidden, true, 1_000_000)?;
    let cold_certificate = cold
        .standing
        .certificate()
        .ok_or("cold reconstruction did not certify")?;
    let inherited_certificate = inherited
        .standing
        .certificate()
        .ok_or("lineage-rich reconstruction did not certify")?;
    if !structural_certificate_equal(cold_certificate, inherited_certificate) {
        return Err("cold and lineage-rich reconstructions differ structurally".into());
    }
    if inherited
        .returned_queries
        .checked_add(inherited.imported_landmarks)
        != Some(cold.returned_queries)
    {
        return Err("lineage did not replace an equal rank of receiver queries".into());
    }

    let held_out = TransportQuery::new(
        vec![
            integer(2),
            integer(-1),
            integer(0),
            integer(3),
            integer(0),
            integer(1),
        ],
        vec![
            integer(1),
            integer(0),
            integer(1),
            integer(0),
            integer(1),
            integer(0),
        ],
    )?;
    let predicted_held_out = inherited_certificate.clamped_response(&held_out)?;
    let returned_held_out = opaque_transport_response(&hidden, &integer(1), &held_out);
    if predicted_held_out != returned_held_out {
        return Err("held-out aggregate receiver response disagreed".into());
    }

    let (forward_content, energy_departed) =
        grade_forward_transport(&hidden, inherited_certificate)?;
    let svg_path = write_svg(inherited_certificate)?;
    let positive_edges = inherited_certificate
        .edge_conductances
        .iter()
        .filter(|edge| edge.conductance > integer(0))
        .map(|edge| -> (PotentialTransportEdge, String) {
            (edge.edge, format_rat(&edge.conductance))
        })
        .collect::<Vec<_>>();

    println!("schema\tholonic-engine.inverse-transport-instrument.v1");
    println!(
        "potential_edge_factors\t{}",
        cold_certificate.edge_order.len()
    );
    println!("cold_imported_landmarks\t{}", cold.imported_landmarks);
    println!("cold_returned_queries\t{}", cold.returned_queries);
    println!(
        "lineage_imported_cut_landmarks\t{}",
        inherited.imported_landmarks
    );
    println!("lineage_returned_queries\t{}", inherited.returned_queries);
    println!("cold_complete_returns\t{}", cold.complete_returns);
    println!("lineage_complete_returns\t{}", inherited.complete_returns);
    println!(
        "complete_operator_basis_entries\t{}",
        inherited_certificate.event_operator.len() * inherited_certificate.event_operator.len()
    );
    println!("cold_affine_dimensions\t{:?}", cold.affine_dimensions);
    println!(
        "lineage_affine_dimensions\t{:?}",
        inherited.affine_dimensions
    );
    println!(
        "cold_exact_row_eliminations\t{}",
        cold.work.exact_row_eliminations
    );
    println!(
        "lineage_exact_row_eliminations\t{}",
        inherited.work.exact_row_eliminations
    );
    println!(
        "cold_inspected_edge_coordinates\t{}",
        cold.work.inspected_edge_coordinates
    );
    println!(
        "lineage_inspected_edge_coordinates\t{}",
        inherited.work.inspected_edge_coordinates
    );
    println!("reconstructed_positive_edges\t{positive_edges:?}");
    println!(
        "connected_components\t{}",
        inherited_certificate.connected_components
    );
    println!("cycle_rank\t{}", inherited_certificate.cycle_rank);
    println!(
        "held_out_aggregate_response\t{}",
        format_rat(&predicted_held_out)
    );
    println!(
        "held_out_forward_content\t{:?}",
        forward_content.iter().map(format_rat).collect::<Vec<_>>()
    );
    println!("held_out_energy_departed\t{}", format_rat(&energy_departed));
    println!("standing_exactly_validated\ttrue");
    println!("svg_receiver_projection\t{}", svg_path.display());
    Ok(())
}
