use std::{
    env,
    error::Error,
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use holonic_engine::{
    CausalWorld, EventId, ExactRaster, ExactRgb, HolonicCellAddress, HolonicCellWitness,
    HolonicOverlapCell, HolonicQuotient, ImageExtent, RayFamily, ReceiverGraphAtlas,
    ReceiverGraphCell, ReceiverGraphDeed, ReceiverGraphRadiation, ReceiverGraphRequest,
    ReceiverGraphSection, ReceiverHolonicComplexEvent, ReceiverHolonicComplexLaw,
    ReceiverPhaseSectionOccurrence,
};
use relational_geometry::{RatVec3, ReceiverId};

const DEFAULT_INPUT: &str =
    "target/holonic-engine/deterministic-image-completion-full-mask64/00_truth.png";
const DEFAULT_OUTPUT: &str = "target/holonic-engine/receiver-graph-analysis";
const ANALYSIS_RECEIVER: ReceiverId = ReceiverId(7_001);

#[derive(Debug)]
struct Arguments {
    input: PathBuf,
    output: PathBuf,
}

fn main() -> Result<(), Box<dyn Error>> {
    let arguments = parse_arguments()?;
    fs::create_dir_all(&arguments.output)?;
    let raster = load_raster(&arguments.input)?;

    let law = ReceiverHolonicComplexLaw::default();
    let mut world = CausalWorld::new(law.clone(), law.initial_standing());
    let construction_started = Instant::now();
    world.receive(&ReceiverHolonicComplexEvent {
        event: EventId(1),
        chronology: 1,
        sections: vec![ReceiverPhaseSectionOccurrence::whole(
            None,
            1,
            ReceiverId(1),
            receiver_rays(),
            &raster,
        )],
    })?;
    let construction_milliseconds = construction_started.elapsed().as_millis();
    let standing = world.standing();
    standing.validate()?;

    let quotient = standing
        .quotients
        .values()
        .max_by_key(|quotient| {
            (
                quotient.source_closed_hull.len(),
                std::cmp::Reverse(quotient.id),
            )
        })
        .cloned()
        .ok_or("the received ecology contains no cross-grain quotient")?;

    let mount_started = Instant::now();
    let mut graph = ReceiverGraphAtlas::mount(standing)?;
    let mount_milliseconds = mount_started.elapsed().as_millis();
    let query_started = Instant::now();
    let mut radiations = Vec::new();
    let mut sections = Vec::new();

    receive(
        &mut graph,
        &mut radiations,
        &mut sections,
        1_001,
        1,
        ReceiverGraphDeed::Found {
            focus: quotient.target,
            upper_horizon: 0,
        },
    )?;
    receive(
        &mut graph,
        &mut radiations,
        &mut sections,
        1_002,
        2,
        ReceiverGraphDeed::Refine {
            quotient: quotient.id,
            upper_horizon: 0,
        },
    )?;
    receive(
        &mut graph,
        &mut radiations,
        &mut sections,
        1_003,
        3,
        ReceiverGraphDeed::Dilate { upper_horizon: 1 },
    )?;
    receive(
        &mut graph,
        &mut radiations,
        &mut sections,
        1_004,
        4,
        ReceiverGraphDeed::Retain,
    )?;

    let source_apex = quotient.source_apex;
    let incident_lower = *graph
        .source()
        .cell(source_apex)?
        .boundary
        .support()
        .iter()
        .next()
        .ok_or("the selected quotient apex has no lower incidence")?;
    let incident_lower = HolonicCellAddress {
        grain: source_apex.grain,
        cell: incident_lower,
    };
    receive(
        &mut graph,
        &mut radiations,
        &mut sections,
        1_005,
        5,
        ReceiverGraphDeed::Traverse {
            path: vec![source_apex, incident_lower],
            upper_horizon: 1,
        },
    )?;
    receive(
        &mut graph,
        &mut radiations,
        &mut sections,
        1_006,
        6,
        ReceiverGraphDeed::Traverse {
            path: vec![incident_lower, source_apex],
            upper_horizon: 1,
        },
    )?;
    receive(
        &mut graph,
        &mut radiations,
        &mut sections,
        1_007,
        7,
        ReceiverGraphDeed::Coarsen {
            quotient: quotient.id,
            upper_horizon: 0,
        },
    )?;
    let query_microseconds = query_started.elapsed().as_micros();
    graph.validate()?;

    let encoded = ron::ser::to_string(&graph)?;
    let remounted: ReceiverGraphAtlas = ron::from_str(&encoded)?;
    remounted.validate()?;
    if remounted != graph {
        return Err("receiver graph atlas changed across exact rest/remount".into());
    }

    let maximal = sections
        .iter()
        .max_by_key(|section| section.cells.len())
        .ok_or("the receiver emitted no graph section")?;
    fs::write(
        arguments.output.join("receiver_sections.ron"),
        ron::ser::to_string(&sections)?,
    )?;
    write_summary(
        &arguments.output.join("summary.tsv"),
        &arguments.input,
        &raster,
        standing,
        &quotient,
        construction_milliseconds,
        mount_milliseconds,
        query_microseconds,
        radiations.len(),
        &encoded,
        maximal,
    )?;
    write_transitions(
        &arguments.output.join("transitions.tsv"),
        &radiations,
        &sections,
    )?;
    write_cells(&arguments.output.join("maximal_section_cells.tsv"), maximal)?;
    write_overlaps(
        &arguments.output.join("maximal_section_overlaps.tsv"),
        &maximal.overlaps,
    )?;

    println!(
        "input\t{}\nextent\t{}x{}\nsource_cells\t{}\nquotient\t{}\n\
         quotient_source_fiber\t{}\nreceiver_transitions\t{}\nmaximum_received_cells\t{}\n\
         construction_milliseconds\t{}\nmount_milliseconds\t{}\nquery_microseconds\t{}\n\
         exact_rest_remount\ttrue\noutput\t{}",
        arguments.input.display(),
        raster.extent.width,
        raster.extent.height,
        standing
            .grains
            .values()
            .map(|grain| grain.incidence.cells().len())
            .sum::<usize>(),
        quotient.id.0,
        quotient.source_closed_hull.len(),
        radiations.len(),
        maximal.cells.len(),
        construction_milliseconds,
        mount_milliseconds,
        query_microseconds,
        arguments.output.display(),
    );
    Ok(())
}

fn receive(
    graph: &mut ReceiverGraphAtlas,
    radiations: &mut Vec<ReceiverGraphRadiation>,
    sections: &mut Vec<ReceiverGraphSection>,
    event: u64,
    chronology: u64,
    deed: ReceiverGraphDeed,
) -> Result<(), Box<dyn Error>> {
    let radiation = graph.receive(&ReceiverGraphRequest {
        event: EventId(event),
        chronology,
        receiver: ANALYSIS_RECEIVER,
        deed,
    })?;
    radiations.push(radiation);
    sections.push(
        graph
            .section(ANALYSIS_RECEIVER)
            .cloned()
            .ok_or("receiver graph section disappeared after its event")?,
    );
    Ok(())
}

fn parse_arguments() -> Result<Arguments, Box<dyn Error>> {
    let mut arguments = Arguments {
        input: PathBuf::from(DEFAULT_INPUT),
        output: PathBuf::from(DEFAULT_OUTPUT),
    };
    let mut supplied = env::args().skip(1);
    while let Some(argument) = supplied.next() {
        match argument.as_str() {
            "--input" => {
                arguments.input = PathBuf::from(supplied.next().ok_or("--input requires a path")?);
            }
            "--output" => {
                arguments.output =
                    PathBuf::from(supplied.next().ok_or("--output requires a path")?);
            }
            "--help" | "-h" => {
                println!("receiver_graph_analysis [--input FILE] [--output DIRECTORY]");
                std::process::exit(0);
            }
            unknown => return Err(format!("unknown argument {unknown}").into()),
        }
    }
    Ok(arguments)
}

fn load_raster(path: &Path) -> Result<ExactRaster, Box<dyn Error>> {
    let image = image::open(path)?.to_rgb8();
    let extent = ImageExtent {
        width: image.width(),
        height: image.height(),
    };
    let samples = image
        .pixels()
        .map(|pixel| ExactRgb {
            red: pixel[0],
            green: pixel[1],
            blue: pixel[2],
        })
        .collect();
    Ok(ExactRaster::new(extent, samples)?)
}

fn receiver_rays() -> RayFamily {
    RayFamily::Central {
        center: RatVec3::zero(),
        forward: RatVec3::from_i64(0, 0, 1),
        horizontal: RatVec3::from_i64(1, 0, 0),
        vertical: RatVec3::from_i64(0, 1, 0),
    }
}

#[allow(clippy::too_many_arguments)]
fn write_summary(
    path: &Path,
    input: &Path,
    raster: &ExactRaster,
    standing: &holonic_engine::ReceiverHolonicComplexStanding,
    quotient: &HolonicQuotient,
    construction_milliseconds: u128,
    mount_milliseconds: u128,
    query_microseconds: u128,
    receiver_transitions: usize,
    encoded_graph: &str,
    maximal: &ReceiverGraphSection,
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from("property\tvalue\n");
    writeln!(output, "schema\tholonic-engine.receiver-graph-analysis.v1")?;
    writeln!(output, "input\t{}", input.display())?;
    writeln!(
        output,
        "extent\t{}x{}",
        raster.extent.width, raster.extent.height
    )?;
    writeln!(output, "phase_germs\t{}", standing.phase_atlas.germs.len())?;
    writeln!(
        output,
        "phase_connections\t{}",
        standing.phase_atlas.connections.len()
    )?;
    writeln!(
        output,
        "phase_cycles\t{}",
        standing.phase_atlas.cycles.len()
    )?;
    writeln!(
        output,
        "source_cells\t{}",
        standing
            .grains
            .values()
            .map(|grain| grain.incidence.cells().len())
            .sum::<usize>()
    )?;
    writeln!(output, "source_quotients\t{}", standing.quotients.len())?;
    writeln!(output, "source_overlaps\t{}", standing.overlaps.len())?;
    writeln!(output, "selected_quotient\t{}", quotient.id.0)?;
    writeln!(
        output,
        "selected_quotient_source_fiber\t{}",
        quotient.source_closed_hull.len()
    )?;
    writeln!(output, "receiver_transitions\t{receiver_transitions}")?;
    writeln!(output, "maximum_received_cells\t{}", maximal.cells.len())?;
    writeln!(
        output,
        "maximum_received_dimension\t{}",
        maximal
            .analysis
            .dimension
            .map_or_else(|| "none".to_owned(), |dimension| dimension.to_string())
    )?;
    writeln!(
        output,
        "maximum_received_f_vector\t{}",
        encode_f_vector(&maximal.analysis.f_vector)
    )?;
    writeln!(
        output,
        "maximum_received_euler_characteristic\t{}",
        maximal.analysis.euler_characteristic
    )?;
    writeln!(
        output,
        "maximum_received_graph_cycle_rank\t{}",
        maximal
            .analysis
            .graph_cycle_rank
            .as_ref()
            .map_or_else(|| "not-graph-like".to_owned(), ToString::to_string)
    )?;
    writeln!(
        output,
        "maximum_received_open_upper_frontier\t{}",
        maximal.analysis.open_upper_frontier
    )?;
    writeln!(
        output,
        "construction_milliseconds\t{construction_milliseconds}"
    )?;
    writeln!(output, "source_mount_milliseconds\t{mount_milliseconds}")?;
    writeln!(
        output,
        "seven_receiver_events_microseconds\t{query_microseconds}"
    )?;
    writeln!(output, "exact_rest_remount\ttrue")?;
    writeln!(output, "serialized_atlas_bytes\t{}", encoded_graph.len())?;
    writeln!(output, "terminal_layout_invoked\tfalse")?;
    fs::write(path, output)?;
    Ok(())
}

fn write_transitions(
    path: &Path,
    radiations: &[ReceiverGraphRadiation],
    sections: &[ReceiverGraphSection],
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from(
        "event\tchronology\tchange\tfocus_grain\tfocus_cell\thorizon\tcells\tf_vector\t\
         euler\tcomponents\tgraph_cycle_rank\tquotient_points\tsource_fiber_population\t\
         maximum_source_fiber\toverlaps\topen_upper_frontier\tadded\tremoved\tretained\t\
         reused_cells\tmaterialized_cells\tcoboundary_lookups\tcoboundary_terms\tclosure_cells\n",
    );
    for (radiation, section) in radiations.iter().zip(sections) {
        let transition = &radiation.transition;
        let analysis = &radiation.analysis;
        writeln!(
            output,
            "{}\t{}\t{:?}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            transition.event.0,
            transition.chronology,
            transition.change,
            transition.to.focus.grain.0,
            transition.to.focus.cell.0,
            transition.to.upper_horizon,
            section.cells.len(),
            encode_f_vector(&analysis.f_vector),
            analysis.euler_characteristic,
            analysis.connected_components,
            analysis
                .graph_cycle_rank
                .as_ref()
                .map_or_else(|| "not-graph-like".to_owned(), ToString::to_string),
            analysis.quotient_points,
            analysis.source_fiber_population,
            analysis.maximum_source_fiber,
            analysis.actual_overlaps,
            analysis.open_upper_frontier,
            transition.delta.added.len(),
            transition.delta.removed.len(),
            transition.delta.retained.len(),
            radiation.query_work.reused_cells,
            radiation.query_work.materialized_cells,
            radiation.query_work.coboundary_lookups,
            radiation.query_work.coboundary_terms,
            radiation.query_work.closure_cells,
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_cells(path: &Path, section: &ReceiverGraphSection) -> Result<(), Box<dyn Error>> {
    let mut output = String::from(
        "grain\tcell\tgrade\tname\tsource_events\tboundary\tcoboundary\twitness\t\
         source_fiber\n",
    );
    for cell in section.cells.values() {
        writeln!(
            output,
            "{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            cell.address.grain.0,
            cell.address.cell.0,
            cell.body.grade,
            cell.body.name.replace(['\t', '\n'], " "),
            encode_events(&cell.body.source_events),
            encode_chain(&cell.body.boundary),
            encode_chain(&cell.coboundary),
            witness_name(cell),
            encode_addresses(&cell.source_fiber),
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn write_overlaps(
    path: &Path,
    overlaps: &std::collections::BTreeMap<holonic_engine::HolonicOverlapId, HolonicOverlapCell>,
) -> Result<(), Box<dyn Error>> {
    let mut output = String::from("overlap\tevent\toccurrence\tmembers\n");
    for overlap in overlaps.values() {
        writeln!(
            output,
            "{}\t{}\t{}:{}\t{}",
            overlap.id.0,
            overlap.caused_by.0,
            overlap.occurrence.grain.0,
            overlap.occurrence.cell.0,
            encode_addresses(overlap.members.iter()),
        )?;
    }
    fs::write(path, output)?;
    Ok(())
}

fn witness_name(cell: &ReceiverGraphCell) -> String {
    match &cell.witness {
        holonic_engine::ReceiverGraphSourceWitness::Algebraic => "algebraic".to_owned(),
        holonic_engine::ReceiverGraphSourceWitness::Holonic(witness) => match witness {
            HolonicCellWitness::PhaseGerm { germ, .. } => format!("phase-germ:{}", germ.0),
            HolonicCellWitness::PhaseTransport { connection } => {
                format!("phase-transport:{}", connection.0)
            }
            HolonicCellWitness::PhaseClosure { cycle } => {
                format!("phase-closure:{}", cycle.0)
            }
            HolonicCellWitness::QuotientedComplex { quotient } => {
                format!("quotiented-complex:{}", quotient.0)
            }
        },
    }
}

fn encode_f_vector(values: &std::collections::BTreeMap<u32, num_bigint::BigUint>) -> String {
    values
        .iter()
        .map(|(grade, population)| format!("{grade}:{population}"))
        .collect::<Vec<_>>()
        .join(",")
}

fn encode_events(events: &std::collections::BTreeSet<EventId>) -> String {
    events
        .iter()
        .map(|event| event.0.to_string())
        .collect::<Vec<_>>()
        .join(",")
}

fn encode_chain(chain: &holonic_engine::CausalChain) -> String {
    chain
        .coefficients()
        .iter()
        .map(|(cell, coefficient)| format!("{}:{}", cell.0, coefficient.difference()))
        .collect::<Vec<_>>()
        .join(",")
}

fn encode_addresses<'a>(addresses: impl IntoIterator<Item = &'a HolonicCellAddress>) -> String {
    addresses
        .into_iter()
        .map(|address| format!("{}:{}", address.grain.0, address.cell.0))
        .collect::<Vec<_>>()
        .join(",")
}
