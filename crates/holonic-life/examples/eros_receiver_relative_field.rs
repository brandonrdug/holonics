use std::io::Write;
use std::path::PathBuf;

use body::incidence::IncidenceHand;
use body::manifold::FeltDeed;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, ContemporaryRadiation, CurrentBoundaryPort, CurrentEvent, CurrentGeometry,
    CurrentLineage, InterfaceCapability, LiveBoundaryTransition, LiveConstituent,
    LiveCurrentMachine, LiveCurrentRestImage, LiveMemory, ParallelCpuLiveCurrentExecutor,
    RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `.local/artifacts/eros_receiver_relative_field/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_receiver_relative_field";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";

const FIELD: InterfaceCapability = InterfaceCapability::new(0x4649_454c_44, 1);
const FOREIGN: InterfaceCapability = InterfaceCapability::new(0x4649_454c_44, 2);
const PRIMING: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];
const EVENT_FACES: [i64; 4] = [17, 29, 43, 71];

#[derive(Clone, Copy)]
enum BranchKind {
    Dyad,
    EligibleTriad,
    IneligibleTriad,
    PermutedTriad,
}

#[derive(Serialize)]
struct ConstituentRead {
    sha256: String,
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    paths: usize,
    exposed_pins: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
    pin_states: Vec<PinRead>,
    native_word_count: usize,
}

#[derive(Serialize)]
struct PinRead {
    ordinal: usize,
    exposed: bool,
    capability: Option<[u64; 2]>,
    deed: &'static str,
}

#[derive(Serialize)]
struct MachineRead {
    rest_sha256: String,
    standing_rank: u64,
    scalar_cells: usize,
    standing_constituents: Vec<ConstituentRead>,
    live_lineages: usize,
    carrier_words: usize,
}

#[derive(Serialize)]
struct BranchRead {
    role: &'static str,
    regional_members: usize,
    regional_successors: Vec<ConstituentRead>,
    machine: MachineRead,
}

#[derive(Serialize)]
struct Acceptance {
    common_predecessor_had_no_cellular_field: bool,
    dyad_closed_as_one_component: bool,
    eligible_third_changed_the_dyadic_successor: bool,
    eligible_population_closed_as_one_component: bool,
    ineligible_third_left_the_dyadic_component_exact: bool,
    ineligible_third_remained_a_separate_component: bool,
    omitting_the_third_restored_the_dyad_exactly: bool,
    regional_storage_order_was_gauge: bool,
    one_and_eight_cpu_cores_were_exact: bool,
    ordinary_current_radiation_was_exact_across_every_branch: bool,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    boundary: &'static str,
    source_population: SourcePopulation,
    predecessor: MachineRead,
    dyad: BranchRead,
    eligible_triad: BranchRead,
    ineligible_triad: BranchRead,
    permuted_triad: BranchRead,
    restored_dyad: BranchRead,
    unique_native_bodies: Vec<NativeBodyRead>,
    acceptance: Acceptance,
    conclusion: &'static str,
}

#[derive(Serialize)]
struct NativeBodyRead {
    sha256: String,
    native_words: Vec<u32>,
}

#[derive(Serialize)]
struct SourcePopulation {
    event_faces: [i64; 4],
    eligible_capability: [u64; 2],
    ineligible_capability: [u64; 2],
    dyad_germs: [[usize; 2]; 2],
    third_germ: [usize; 2],
    relation_law: &'static str,
}

struct Outcome {
    radiation: ContemporaryRadiation,
    machine: LiveCurrentMachine,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros receiver-relative field: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(
        arguments
            .next()
            .ok_or_else(|| "usage: eros_receiver_relative_field <new-report.json>".to_owned())?,
    );
    if arguments.next().is_some() {
        return Err("usage: eros_receiver_relative_field <new-report.json>".to_owned());
    }

    let report = run_cpu()?;
    let mut encoded = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("the exact report encodes: {error}"))?;
    encoded.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&output)
        .map_err(|error| format!("{} opens once: {error}", output.display()))?;
    file.write_all(&encoded)
        .map_err(|error| format!("{} writes completely: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output.display()))?;
    eprintln!(
        "eros receiver-relative field: {} · {} bytes · {}",
        report.status,
        encoded.len(),
        output.display()
    );
    Ok(())
}

fn run_cpu() -> Result<Report, String> {
    let (base, lineages) = primed_machine()?;
    let predecessor_image = base.rest_image().map_err(debug)?;
    let predecessor = machine_read(&base)?;

    let dyad = enact(&predecessor_image, lineages, BranchKind::Dyad, 1)?;
    let eligible_one = enact(&predecessor_image, lineages, BranchKind::EligibleTriad, 1)?;
    let eligible_many = enact(&predecessor_image, lineages, BranchKind::EligibleTriad, 8)?;
    let ineligible = enact(&predecessor_image, lineages, BranchKind::IneligibleTriad, 1)?;
    let permuted = enact(&predecessor_image, lineages, BranchKind::PermutedTriad, 8)?;
    let restored = enact(&predecessor_image, lineages, BranchKind::Dyad, 8)?;

    let dyad_body = dyad.radiation.regional()[0].constituent();
    let eligible_body = eligible_one.radiation.regional()[0].constituent();
    let ineligible_dyad = ineligible.radiation.regional()[0].constituent();
    let ineligible_third = ineligible.radiation.regional()[2].constituent();
    let acceptance = Acceptance {
        common_predecessor_had_no_cellular_field: base.standing().constituents().is_empty(),
        dyad_closed_as_one_component: dyad.radiation.regional().len() == 2
            && dyad.radiation.regional()[1].constituent() == dyad_body
            && dyad.machine.standing().constituents().len() == 1,
        eligible_third_changed_the_dyadic_successor: eligible_body != dyad_body,
        eligible_population_closed_as_one_component: eligible_one.radiation.regional().len() == 3
            && eligible_one
                .radiation
                .regional()
                .iter()
                .all(|region| region.constituent() == eligible_body)
            && eligible_one.machine.standing().constituents().len() == 1,
        ineligible_third_left_the_dyadic_component_exact: ineligible_dyad == dyad_body
            && ineligible.radiation.regional()[1].constituent() == dyad_body,
        ineligible_third_remained_a_separate_component: ineligible_third != dyad_body
            && ineligible.machine.standing().constituents().len() == 2,
        omitting_the_third_restored_the_dyad_exactly: restored.radiation == dyad.radiation
            && restored.machine.rest_image().map_err(debug)?
                == dyad.machine.rest_image().map_err(debug)?,
        regional_storage_order_was_gauge: permuted.machine.rest_image().map_err(debug)?
            == eligible_one.machine.rest_image().map_err(debug)?,
        one_and_eight_cpu_cores_were_exact: eligible_many.radiation == eligible_one.radiation
            && eligible_many.machine.rest_image().map_err(debug)?
                == eligible_one.machine.rest_image().map_err(debug)?,
        ordinary_current_radiation_was_exact_across_every_branch: [
            &eligible_one,
            &eligible_many,
            &ineligible,
            &permuted,
            &restored,
        ]
        .iter()
        .all(|outcome| outcome.radiation.currents() == dyad.radiation.currents()),
    };
    let accepted = acceptance.common_predecessor_had_no_cellular_field
        && acceptance.dyad_closed_as_one_component
        && acceptance.eligible_third_changed_the_dyadic_successor
        && acceptance.eligible_population_closed_as_one_component
        && acceptance.ineligible_third_left_the_dyadic_component_exact
        && acceptance.ineligible_third_remained_a_separate_component
        && acceptance.omitting_the_third_restored_the_dyad_exactly
        && acceptance.regional_storage_order_was_gauge
        && acceptance.one_and_eight_cpu_cores_were_exact
        && acceptance.ordinary_current_radiation_was_exact_across_every_branch;
    if !accepted {
        return Err("the fixed population-relative contrasts did not all close".to_owned());
    }

    Ok(Report {
        schema: "eros.receiver-relative-field.observer.v1",
        status: "accepted",
        question: "does the complete eligible population reform one regional successor without storing prior winner edges?",
        theory_to_structure: "each source-declared regional germ emits an exposed interface arm; the one contemporary closure joins exactly capability-compatible arms against one immutable predecessor and commits each connected component once",
        boundary: "this measures Soma's exact topological population closure; it does not install or reproduce a transformer's numerical projection, normalization, or value-transport law",
        source_population: SourcePopulation {
            event_faces: EVENT_FACES,
            eligible_capability: [FIELD.namespace(), FIELD.local()],
            ineligible_capability: [FOREIGN.namespace(), FOREIGN.local()],
            dyad_germs: [[0, 1], [1, 2]],
            third_germ: [2, 3],
            relation_law: "equal source capability admits a co-present seam; unequal capability forbids it even when every current face is otherwise identical",
        },
        predecessor,
        dyad: branch_read("eligible dyad", &dyad)?,
        eligible_triad: branch_read("eligible third present", &eligible_one)?,
        ineligible_triad: branch_read("ineligible third present", &ineligible)?,
        permuted_triad: branch_read("same eligible population, reversed storage", &permuted)?,
        restored_dyad: branch_read("third absent from the event cut", &restored)?,
        unique_native_bodies: vec![
            native_body_read(dyad_body)?,
            native_body_read(eligible_body)?,
            native_body_read(ineligible_third)?,
        ],
        acceptance,
        conclusion: "the context is the population: adding one eligible germ changes the jointly emitted component, an ineligible germ remains separate without perturbing the dyad, and removing it restores the exact dyadic field; no finished relation is carried between branches",
    })
}

fn enact(
    predecessor: &LiveCurrentRestImage,
    lineages: [CurrentLineage; 4],
    kind: BranchKind,
    threads: usize,
) -> Result<Outcome, String> {
    let mut machine = LiveCurrentMachine::from_rest_image(predecessor.clone()).map_err(debug)?;
    let currents = event_currents(lineages)?;
    let first = [arc(0, 1, lineages, FIELD, IncidenceHand::Against)];
    let second = [arc(1, 2, lineages, FIELD, IncidenceHand::With)];
    let third_capability = match kind {
        BranchKind::IneligibleTriad => FOREIGN,
        _ => FIELD,
    };
    let third = [arc(
        2,
        3,
        lineages,
        third_capability,
        IncidenceHand::Against,
    )];
    let cells = [
        RegionalRelationCell::new(lineages[1], &first),
        RegionalRelationCell::new(lineages[2], &second),
        RegionalRelationCell::new(lineages[3], &third),
    ];
    let mut executor = ParallelCpuLiveCurrentExecutor::new(threads);
    let radiation = match kind {
        BranchKind::Dyad => machine.receive_with(
            ContemporaryEvent::with_regional(&currents, &[], &cells[..2]),
            &mut executor,
        ),
        BranchKind::PermutedTriad => {
            let permuted = [cells[2], cells[1], cells[0]];
            machine.receive_with(
                ContemporaryEvent::with_regional(&currents, &[], &permuted),
                &mut executor,
            )
        }
        BranchKind::EligibleTriad | BranchKind::IneligibleTriad => machine.receive_with(
            ContemporaryEvent::with_regional(&currents, &[], &cells),
            &mut executor,
        ),
    }
    .map_err(debug)?;
    Ok(Outcome { radiation, machine })
}

fn primed_machine() -> Result<(LiveCurrentMachine, [CurrentLineage; 4]), String> {
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
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
    ];
    for value in PRIMING {
        let currents = [
            CurrentEvent::continuing(lineages[0], relation(value)?, action()),
            CurrentEvent::continuing(lineages[1], relation(value)?, action()),
            CurrentEvent::continuing(lineages[2], relation(value)?, action()),
            CurrentEvent::continuing(lineages[3], relation(value)?, action()),
        ];
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
    }
    Ok((machine, lineages))
}

fn event_currents(lineages: [CurrentLineage; 4]) -> Result<[CurrentEvent<'static>; 4], String> {
    Ok([
        CurrentEvent::continuing(lineages[0], relation(EVENT_FACES[0])?, action()),
        CurrentEvent::continuing(lineages[1], relation(EVENT_FACES[1])?, action()),
        CurrentEvent::continuing(lineages[2], relation(EVENT_FACES[2])?, action()),
        CurrentEvent::continuing(lineages[3], relation(EVENT_FACES[3])?, action()),
    ])
}

fn arc(
    from: usize,
    to: usize,
    lineages: [CurrentLineage; 4],
    capability: InterfaceCapability,
    hand: IncidenceHand,
) -> RegionalRelationArc {
    RegionalRelationArc::new(
        lineages[from],
        CurrentBoundaryPort::Cell,
        lineages[to],
        CurrentBoundaryPort::Cell,
        capability,
        0,
        0,
        hand,
    )
}

fn branch_read(role: &'static str, outcome: &Outcome) -> Result<BranchRead, String> {
    Ok(BranchRead {
        role,
        regional_members: outcome.radiation.regional().len(),
        regional_successors: outcome
            .radiation
            .regional()
            .iter()
            .map(|region| constituent_read(region.constituent()))
            .collect::<Result<_, _>>()?,
        machine: machine_read(&outcome.machine)?,
    })
}

fn machine_read(machine: &LiveCurrentMachine) -> Result<MachineRead, String> {
    let rest = machine.rest_image().map_err(debug)?;
    let bytes = rest.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched and
    // still reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead
    // of being hashed and dropped. The address is the content, so this helper -- called at many
    // rests -- deposits every distinct form it sealed instead of overwriting all but the last, and
    // the file name it returns carries the same hash the receipt does.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &bytes)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let LiveMemory {
        live_lineages,
        carrier_words,
        ..
    } = machine.memory();
    Ok(MachineRead {
        rest_sha256: hex_digest(&bytes),
        standing_rank: machine.standing().rank(),
        scalar_cells: machine.standing().cells().len(),
        standing_constituents: machine
            .standing()
            .constituents()
            .iter()
            .map(constituent_read)
            .collect::<Result<_, _>>()?,
        live_lineages,
        carrier_words,
    })
}

fn constituent_read(body: &LiveConstituent) -> Result<ConstituentRead, String> {
    let native_words = body.native_words().map_err(debug)?;
    let mut native_bytes = Vec::with_capacity(native_words.len() * 4);
    for word in &native_words {
        native_bytes.extend_from_slice(&word.to_le_bytes());
    }
    let mut open_boundaries = 0;
    let mut ride_boundaries = 0;
    let mut found_boundaries = 0;
    for at in 0..body.boundaries().len() {
        match body.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => return Err("a constituent boundary lost its transition".to_owned()),
        }
    }
    let pin_states = body
        .pins()
        .iter()
        .enumerate()
        .map(|(ordinal, pin)| PinRead {
            ordinal,
            exposed: body.exposed().binary_search(&(ordinal as u32)).is_ok(),
            capability: pin
                .interface()
                .map(|capability| [capability.namespace(), capability.local()]),
            deed: match pin.formed().map(|formed| formed.deed()) {
                None => "OPEN",
                Some(FeltDeed::Ride) => "RIDE",
                Some(FeltDeed::FoundThis) => "FOUND_THIS",
                Some(FeltDeed::FoundThat) => "FOUND_THAT",
                Some(FeltDeed::Dark) => "DARK",
            },
        })
        .collect();
    Ok(ConstituentRead {
        sha256: hex_digest(&native_bytes),
        grain: body.grain(),
        axes: body.axis_count(),
        cells: body.cells().len(),
        incidences: body.incidences().len(),
        pins: body.pins().len(),
        boundaries: body.boundaries().len(),
        paths: body
            .boundaries()
            .iter()
            .map(|boundary| boundary.paths().len())
            .sum(),
        exposed_pins: body.exposed().len(),
        open_boundaries,
        ride_boundaries,
        found_boundaries,
        pin_states,
        native_word_count: native_words.len(),
    })
}

fn native_body_read(body: &LiveConstituent) -> Result<NativeBodyRead, String> {
    let native_words = body.native_words().map_err(debug)?;
    let mut native_bytes = Vec::with_capacity(native_words.len() * 4);
    for word in &native_words {
        native_bytes.extend_from_slice(&word.to_le_bytes());
    }
    Ok(NativeBodyRead {
        sha256: hex_digest(&native_bytes),
        native_words,
    })
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value)).ok_or_else(|| "zero is not a live relation".to_owned())
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn hex_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
