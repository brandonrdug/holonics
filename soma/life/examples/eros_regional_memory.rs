use std::io::Write;
use std::path::PathBuf;

use body::channel::WindingQuantum;
use body::incidence::IncidenceHand;
use body::manifold::FeltDeed;
use body::num::Cog;
use serde::Serialize;
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveBoundaryTransition, LiveConstituent, LiveCurrentError,
    LiveCurrentMachine, LiveMemory, RegionalRelationArc, RegionalRelationCell, SparseStandingError,
    SparseStandingSurface,
};

#[derive(Serialize)]
struct CogRead {
    mag: u32,
    rank_mag: u32,
    rank_rank: i32,
    rank_negative: bool,
    turn: u32,
}

#[derive(Serialize)]
struct PinRead {
    ordinal: usize,
    exposed: bool,
    meeting_reach: CogRead,
    meeting_aim: CogRead,
    meeting_cross: CogRead,
    held_aim: CogRead,
    held_cross: CogRead,
    position: Option<[CogRead; 2]>,
    chi: Option<[CogRead; 2]>,
    winding: &'static str,
    deed: &'static str,
}

#[derive(Serialize)]
struct TransportTermRead {
    boundary: usize,
    path: usize,
    term: usize,
    axes: Vec<u32>,
    coefficient: CogRead,
}

#[derive(Serialize)]
struct ConstituentRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    paths: usize,
    folded_paths: usize,
    transport_terms: usize,
    exposed_pins: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
    pin_geometry: Vec<PinRead>,
    transport: Vec<TransportTermRead>,
}

#[derive(Serialize)]
struct MachineRead {
    standing_rank: u64,
    standing_cells: usize,
    standing_constituents: usize,
    constituent_cells: usize,
    constituent_incidences: usize,
    constituent_pins: usize,
    constituent_paths: usize,
    constituent_transport_terms: usize,
    live_lineages: usize,
    carrier_words: usize,
    overflow_nodes: usize,
}

#[derive(Serialize)]
struct Foils {
    same_collapsed_place_did_not_create_correspondence: bool,
    nonidentical_faces_with_one_completed_well_rebased: bool,
    reversing_only_the_recurrent_hand_founded_an_axis: bool,
    arc_storage_order_was_gauge: bool,
    overlapping_predecessor_use_refused_atomically: bool,
    rest_remount_was_exact: bool,
    consumed_ride_seam_departed_into_transport: bool,
    prior_constituent_departed_as_a_separate_factor: bool,
    later_identical_probe_changed_at_the_regional_grain: bool,
    ordinary_current_radiation_remained_exact: bool,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    aperture: &'static str,
    seed: ConstituentRead,
    bridge_without_prior: ConstituentRead,
    bridge_with_prior: ConstituentRead,
    bridge_with_reversed_hand: ConstituentRead,
    probe_without_seed: ConstituentRead,
    probe_with_seed: ConstituentRead,
    final_taught_machine: MachineRead,
    final_control_machine: MachineRead,
    foils: Foils,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros regional memory: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(
        arguments
            .next()
            .ok_or_else(|| "usage: eros_regional_memory <new-report.json>".to_owned())?,
    );
    if arguments.next().is_some() {
        return Err("usage: eros_regional_memory <new-report.json>".to_owned());
    }
    let report = run_host()?;
    let mut bytes = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("report does not encode: {error}"))?;
    bytes.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&output)
        .map_err(|error| format!("{} opens as a new report: {error}", output.display()))?;
    file.write_all(&bytes)
        .map_err(|error| format!("{} writes completely: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output.display()))?;
    eprintln!(
        "eros regional memory: {} · {} bytes · {}",
        report.status,
        bytes.len(),
        output.display()
    );
    Ok(())
}

fn run_host() -> Result<Report, String> {
    let (base, lineages) = primed_machine()?;
    let rest = base.rest_image().map_err(debug)?;
    let mut taught = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let mut control = LiveCurrentMachine::from_rest_image(rest).map_err(debug)?;
    let arcs = triangle_arcs(lineages, IncidenceHand::Against);
    let regional = [RegionalRelationCell::new(lineages[2], &arcs)];

    let seed_currents = currents(lineages, [17, 29, 43]);
    let seed_radiation = taught
        .receive(ContemporaryEvent::with_regional(
            &seed_currents,
            &[],
            &regional,
        ))
        .map_err(debug)?;
    let seed_control = control
        .receive(ContemporaryEvent::unrelated(&seed_currents))
        .map_err(debug)?;
    let seed = seed_radiation.regional()[0].constituent();
    let same_seed_currents = seed_radiation.currents() == seed_control.currents();
    let seed_rest = taught.rest_image().map_err(debug)?;
    let mut reversed = LiveCurrentMachine::from_rest_image(seed_rest.clone()).map_err(debug)?;
    let mut permuted = LiveCurrentMachine::from_rest_image(seed_rest.clone()).map_err(debug)?;
    let mut overlapping = LiveCurrentMachine::from_rest_image(seed_rest).map_err(debug)?;

    let bridge_currents = currents(lineages, [17, 29, 71]);
    let bridge_taught_radiation = taught
        .receive(ContemporaryEvent::with_regional(
            &bridge_currents,
            &[],
            &regional,
        ))
        .map_err(debug)?;
    let bridge_control_radiation = control
        .receive(ContemporaryEvent::with_regional(
            &bridge_currents,
            &[],
            &regional,
        ))
        .map_err(debug)?;
    let bridge_taught = bridge_taught_radiation.regional()[0].constituent();
    let bridge_control = bridge_control_radiation.regional()[0].constituent();

    let reversed_arcs = [
        RegionalRelationArc::new(
            lineages[0],
            CurrentBoundaryPort::Cell,
            lineages[1],
            CurrentBoundaryPort::Cell,
            InterfaceCapability::new(0x4d45_4d4f_5259, 0),
            0,
            0,
            IncidenceHand::With,
        ),
        arcs[1].clone(),
        arcs[2].clone(),
    ];
    let reversed_regional = [RegionalRelationCell::new(lineages[2], &reversed_arcs)];
    let reversed_radiation = reversed
        .receive(ContemporaryEvent::with_regional(
            &bridge_currents,
            &[],
            &reversed_regional,
        ))
        .map_err(debug)?;
    let bridge_reversed = reversed_radiation.regional()[0].constituent();

    let permuted_arcs = [arcs[2].clone(), arcs[0].clone(), arcs[1].clone()];
    let permuted_regional = [RegionalRelationCell::new(lineages[2], &permuted_arcs)];
    permuted
        .receive(ContemporaryEvent::with_regional(
            &bridge_currents,
            &[],
            &permuted_regional,
        ))
        .map_err(debug)?;
    let order_gauge =
        taught.rest_image().map_err(debug)? == permuted.rest_image().map_err(debug)?;

    let overlap_before = overlapping.rest_image().map_err(debug)?;
    let overlap_refused = matches!(
        overlapping.receive(ContemporaryEvent::with_regional(
            &bridge_currents,
            &[],
            &[regional[0], regional[0]],
        )),
        Err(LiveCurrentError::Standing(SparseStandingError::Topology))
    ) && overlapping.rest_image().map_err(debug)? == overlap_before;

    let bridge_rest = taught.rest_image().map_err(debug)?;
    let mut remounted = LiveCurrentMachine::from_rest_image(bridge_rest.clone()).map_err(debug)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == bridge_rest;
    let probe_currents = currents(lineages, [29, 71, 97]);
    let probe_taught_radiation = remounted
        .receive(ContemporaryEvent::with_regional(
            &probe_currents,
            &[],
            &regional,
        ))
        .map_err(debug)?;
    let probe_control_radiation = control
        .receive(ContemporaryEvent::with_regional(
            &probe_currents,
            &[],
            &regional,
        ))
        .map_err(debug)?;
    let probe_taught = probe_taught_radiation.regional()[0].constituent();
    let probe_control = probe_control_radiation.regional()[0].constituent();

    let same_place = seed.pins()[1..]
        .iter()
        .all(|pin| pin.transport_position() == seed.pins()[0].transport_position());
    let distinct_wells = seed.pins()[1..]
        .iter()
        .all(|pin| pin.meeting().arrow.reach != seed.pins()[0].meeting().arrow.reach);
    let nonidentical_rebase = bridge_control.pins()[0].meeting().arrow.reach
        == seed.pins()[0].meeting().arrow.reach
        && bridge_control.pins()[0].transport_position() != seed.pins()[0].transport_position()
        && bridge_taught.grain() == 3;
    let orientation_founded = bridge_reversed.axis_count() > bridge_taught.axis_count()
        && bridge_reversed.pins().iter().any(|pin| {
            pin.formed().is_some_and(|formed| {
                matches!(formed.deed(), FeltDeed::FoundThis | FeltDeed::FoundThat)
            })
        });
    let seam_folded = bridge_taught.boundaries().last().is_some_and(|boundary| {
        boundary.paths()[0].interior_folded()
            && boundary.paths()[0].steps().is_empty()
            && !boundary.paths()[0].transport().terms().is_empty()
    });
    let predecessor_departed = taught.standing().constituents().len() == 1
        && remounted.standing().constituents().len() == 1;
    let later_probe_changed = probe_taught.grain() == 4
        && probe_control.grain() == 3
        && remounted.rest_image().map_err(debug)? != control.rest_image().map_err(debug)?;
    let ordinary_current_exact = same_seed_currents
        && bridge_taught_radiation.currents() == bridge_control_radiation.currents()
        && probe_taught_radiation.currents() == probe_control_radiation.currents();
    let foils = Foils {
        same_collapsed_place_did_not_create_correspondence: same_place
            && distinct_wells
            && bridge_taught.exposed().len() == 4,
        nonidentical_faces_with_one_completed_well_rebased: nonidentical_rebase,
        reversing_only_the_recurrent_hand_founded_an_axis: orientation_founded,
        arc_storage_order_was_gauge: order_gauge,
        overlapping_predecessor_use_refused_atomically: overlap_refused,
        rest_remount_was_exact: rest_exact,
        consumed_ride_seam_departed_into_transport: seam_folded,
        prior_constituent_departed_as_a_separate_factor: predecessor_departed,
        later_identical_probe_changed_at_the_regional_grain: later_probe_changed,
        ordinary_current_radiation_remained_exact: ordinary_current_exact,
    };
    let accepted = foils.same_collapsed_place_did_not_create_correspondence
        && foils.nonidentical_faces_with_one_completed_well_rebased
        && foils.reversing_only_the_recurrent_hand_founded_an_axis
        && foils.arc_storage_order_was_gauge
        && foils.overlapping_predecessor_use_refused_atomically
        && foils.rest_remount_was_exact
        && foils.consumed_ride_seam_departed_into_transport
        && foils.prior_constituent_departed_as_a_separate_factor
        && foils.later_identical_probe_changed_at_the_regional_grain
        && foils.ordinary_current_radiation_remained_exact;
    if !accepted {
        return Err("the fixed regional-memory contrasts did not all close".to_owned());
    }

    Ok(Report {
        schema: "eros.regional-memory.observer.v1",
        status: "accepted",
        aperture: "exact completed meeting reach + unordered boundary-cell grain; full rotor rebase + temporal hand decides the seam",
        seed: constituent_read(seed),
        bridge_without_prior: constituent_read(bridge_control),
        bridge_with_prior: constituent_read(bridge_taught),
        bridge_with_reversed_hand: constituent_read(bridge_reversed),
        probe_without_seed: constituent_read(probe_control),
        probe_with_seed: constituent_read(probe_taught),
        final_taught_machine: machine_read(&remounted),
        final_control_machine: machine_read(&control),
        foils,
    })
}

fn primed_machine() -> Result<(LiveCurrentMachine, [CurrentLineage; 3]), String> {
    let first = relation(13)?;
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let lineages = [
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
    ];
    for value in [13, 29, 17, 31, -63_245, 47, 71, -89] {
        let event = currents(lineages, [value; 3]);
        machine
            .receive(ContemporaryEvent::unrelated(&event))
            .map_err(debug)?;
    }
    Ok((machine, lineages))
}

fn currents(lineages: [CurrentLineage; 3], values: [i64; 3]) -> [CurrentEvent<'static>; 3] {
    [
        CurrentEvent::continuing(lineages[0], relation(values[0]).unwrap(), action()),
        CurrentEvent::continuing(lineages[1], relation(values[1]).unwrap(), action()),
        CurrentEvent::continuing(lineages[2], relation(values[2]).unwrap(), action()),
    ]
}

fn triangle_arcs(
    lineages: [CurrentLineage; 3],
    first_hand: IncidenceHand,
) -> [RegionalRelationArc; 3] {
    [
        RegionalRelationArc::new(
            lineages[0],
            CurrentBoundaryPort::Cell,
            lineages[1],
            CurrentBoundaryPort::Cell,
            InterfaceCapability::new(0x4d45_4d4f_5259, 0),
            0,
            0,
            first_hand,
        ),
        RegionalRelationArc::new(
            lineages[1],
            CurrentBoundaryPort::Cell,
            lineages[2],
            CurrentBoundaryPort::Cell,
            InterfaceCapability::new(0x4d45_4d4f_5259, 1),
            1,
            0,
            IncidenceHand::Against,
        ),
        RegionalRelationArc::new(
            lineages[2],
            CurrentBoundaryPort::Cell,
            lineages[0],
            CurrentBoundaryPort::Cell,
            InterfaceCapability::new(0x4d45_4d4f_5259, 2),
            2,
            0,
            IncidenceHand::Against,
        ),
    ]
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value)).ok_or_else(|| "zero relation is not a live cell".to_owned())
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn constituent_read(constituent: &LiveConstituent) -> ConstituentRead {
    let mut open_boundaries = 0usize;
    let mut ride_boundaries = 0usize;
    let mut found_boundaries = 0usize;
    let mut paths = 0usize;
    let mut folded_paths = 0usize;
    let mut transport_terms = 0usize;
    let mut transport = Vec::new();
    for (boundary_at, boundary) in constituent.boundaries().iter().enumerate() {
        match constituent.boundary_transition(boundary_at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => {}
        }
        paths += boundary.paths().len();
        for (path_at, path) in boundary.paths().iter().enumerate() {
            folded_paths += usize::from(path.interior_folded());
            transport_terms += path.transport().terms().len();
            for (term_at, term) in path.transport().terms().iter().enumerate() {
                transport.push(TransportTermRead {
                    boundary: boundary_at,
                    path: path_at,
                    term: term_at,
                    axes: term
                        .blade()
                        .axes()
                        .iter()
                        .map(|axis| axis.local())
                        .collect(),
                    coefficient: cog_read(term.coefficient()),
                });
            }
        }
    }
    let pin_geometry = constituent
        .pins()
        .iter()
        .enumerate()
        .map(|(ordinal, pin)| {
            let formed = pin.formed();
            PinRead {
                ordinal,
                exposed: constituent
                    .exposed()
                    .binary_search(&(ordinal as u32))
                    .is_ok(),
                meeting_reach: cog_read(pin.meeting().arrow.reach),
                meeting_aim: cog_read(pin.meeting().arrow.aim),
                meeting_cross: cog_read(pin.meeting().arrow.cross),
                held_aim: cog_read(pin.held().arrow.aim),
                held_cross: cog_read(pin.held().arrow.cross),
                position: formed
                    .map(|formed| [cog_read(formed.position().0), cog_read(formed.position().1)]),
                chi: formed
                    .map(|formed| [cog_read(formed.chi().same), cog_read(formed.chi().other)]),
                winding: winding(formed.map(Formed::winding)),
                deed: deed(formed.map(Formed::deed)),
            }
        })
        .collect();
    ConstituentRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        boundaries: constituent.boundaries().len(),
        paths,
        folded_paths,
        transport_terms,
        exposed_pins: constituent.exposed().len(),
        open_boundaries,
        ride_boundaries,
        found_boundaries,
        pin_geometry,
        transport,
    }
}

type Formed = soma_membrane::FormedPin;

fn machine_read(machine: &LiveCurrentMachine) -> MachineRead {
    let LiveMemory {
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        carrier_words,
        overflow_nodes,
    } = machine.memory();
    MachineRead {
        standing_rank: machine.standing().rank(),
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        carrier_words,
        overflow_nodes,
    }
}

fn cog_read(cog: Cog) -> CogRead {
    CogRead {
        mag: cog.mag,
        rank_mag: cog.rank.mag,
        rank_rank: cog.rank.rank,
        rank_negative: cog.rank.neg,
        turn: cog.turn,
    }
}

fn winding(winding: Option<WindingQuantum>) -> &'static str {
    match winding {
        None => "OPEN",
        Some(WindingQuantum::None) => "NONE",
        Some(WindingQuantum::ThisWay) => "THIS_WAY",
        Some(WindingQuantum::ThatWay) => "THAT_WAY",
    }
}

fn deed(deed: Option<FeltDeed>) -> &'static str {
    match deed {
        None => "OPEN",
        Some(FeltDeed::Ride) => "RIDE",
        Some(FeltDeed::FoundThis) => "FOUND_THIS",
        Some(FeltDeed::FoundThat) => "FOUND_THAT",
        Some(FeltDeed::Dark) => "DARK",
    }
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
