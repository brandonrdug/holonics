use std::io::Write;
use std::path::PathBuf;

use body::channel::WindingQuantum;
use body::incidence::{
    DiscreteEventGerm, EventCell, EventCellId, EventComplex, EventPort, EventPortKind,
    IncidenceHand, IncidenceKind, OrientedIncidence,
};
use body::manifold::FeltDeed;
use body::num::Cog;
use life::current_world::{
    present_native_event_with, present_native_event_with_regional, NativeEventCurrent,
    NativeRegionalArc, NativeRegionalRelation, NativeRelationOrgan, NativeRelationOrganImage,
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;
use soma_membrane::{
    ContemporaryRadiation, CurrentBoundaryPort, CurrentExecutionRequest, DirectedExecutionRequest,
    ExecutedContemporaryEvent, HostLiveCurrentExecutor, InterfaceCapability,
    LiveBoundaryTransition, LiveConstituent, LiveCurrentError, LiveCurrentExecutor,
    LiveCurrentMachine, LiveCurrentRestImage, LiveMemory, RegionalExecutionRequest,
    SparseStandingSurface,
};
use life::form_mouth::deposit_form_or_message;

/// This driver's name at the plate mouth: `output/eros_euclidean_worldline/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_euclidean_worldline";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
/// The `ERST` half of the world checkpoint, deposited apart from the concatenation the driver hashes.
const CHECKPOINT_MACHINE_FORM: &str = "checkpoint-machine";
/// The relation-organ half of the same checkpoint. Its codec is real; no held plate schema reads it.
const CHECKPOINT_TRAJECTORY_FORM: &str = "checkpoint-trajectory";
const TRAINING_FORWARD: [Pair; 2] = [Pair::new(84, 30), Pair::new(55, 34)];
const HELD_OUT: Pair = Pair::new(391, 299);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct Pair {
    a: u64,
    b: u64,
}

impl Pair {
    const fn new(a: u64, b: u64) -> Self {
        Self { a, b }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct Division {
    before: Pair,
    quotient: u64,
    remainder: u64,
    after: Pair,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct EuclideanTrace {
    input: Pair,
    states: Vec<Pair>,
    divisions: Vec<Division>,
}

impl EuclideanTrace {
    fn new(input: Pair) -> Result<Self, String> {
        if input.a == 0 || input.b == 0 {
            return Err(
                "the bounded Euclidean source begins with two positive integers".to_owned(),
            );
        }
        let mut state = input;
        let mut states = vec![state];
        let mut divisions = Vec::new();
        while state.b != 0 {
            let quotient = state.a / state.b;
            let remainder = state.a % state.b;
            let after = Pair::new(state.b, remainder);
            divisions.push(Division {
                before: state,
                quotient,
                remainder,
                after,
            });
            states.push(after);
            state = after;
        }
        Ok(Self {
            input,
            states,
            divisions,
        })
    }

    fn gcd(&self) -> u64 {
        self.states
            .last()
            .expect("one Euclidean trace has its initial state")
            .a
    }
}

#[derive(Clone, Copy)]
struct StageCells {
    a: EventCellId,
    b: EventCellId,
    pair: EventCellId,
}

struct EuclideanChart {
    cells: Vec<EventCell>,
    incidences: Vec<OrientedIncidence>,
    ports: Vec<EventPort>,
    roles: Vec<String>,
}

impl EuclideanChart {
    fn new(trace: &EuclideanTrace) -> Result<Self, String> {
        let mut cells = Vec::new();
        let mut incidences = Vec::new();
        let mut ports = Vec::new();
        let mut roles = Vec::new();
        let mut stages = Vec::new();

        for (stage_at, state) in trace.states.iter().copied().enumerate() {
            let stage = u32::try_from(stage_at)
                .map_err(|_| "Euclidean stage extent exceeded u32".to_owned())?;
            let a = next_id(cells.len())?;
            cells.push(EventCell::new(a, stage, 0, exact_cog(state.a)?));
            roles.push(format!("state[{stage}].a={}", state.a));
            let b = next_id(cells.len())?;
            cells.push(EventCell::new(b, stage, 0, exact_cog(state.b)?));
            roles.push(format!("state[{stage}].b={}", state.b));
            let pair = next_id(cells.len())?;
            let quotient = trace
                .divisions
                .get(stage_at)
                .map_or(0, |division| division.quotient);
            cells.push(EventCell::new(pair, stage, 1, exact_cog(quotient)?));
            roles.push(if quotient == 0 {
                format!("state[{stage}].terminal-pair")
            } else {
                format!("state[{stage}].pair-with-q={quotient}")
            });
            incidences.push(OrientedIncidence::boundary(
                a,
                pair,
                IncidenceHand::Against,
                0,
            ));
            incidences.push(OrientedIncidence::boundary(b, pair, IncidenceHand::With, 1));
            stages.push(StageCells { a, b, pair });
        }

        for pair in stages.windows(2) {
            let before = pair[0];
            let after = pair[1];
            // `a' = b` is the carried side. `b' = a mod b` depends on both prior sides. The
            // whole oriented pair carries the exact quotient on its outgoing one-cell.
            incidences.push(OrientedIncidence::dependency(
                before.b,
                after.a,
                IncidenceHand::With,
                0,
            ));
            incidences.push(OrientedIncidence::dependency(
                before.a,
                after.b,
                IncidenceHand::Against,
                0,
            ));
            incidences.push(OrientedIncidence::dependency(
                before.b,
                after.b,
                IncidenceHand::With,
                1,
            ));
            incidences.push(OrientedIncidence::dependency(
                before.pair,
                after.pair,
                IncidenceHand::With,
                2,
            ));
        }
        incidences.sort_unstable_by_key(|incidence| (incidence.to().ordinal(), incidence.slot()));

        let first = stages
            .first()
            .ok_or_else(|| "one Euclidean chart needs an ingress state".to_owned())?;
        let last = stages
            .last()
            .ok_or_else(|| "one Euclidean chart needs an exposed state".to_owned())?;
        ports.push(EventPort::ingress(first.pair, IncidenceHand::With, 0));
        ports.push(EventPort::exposed(last.pair, IncidenceHand::With, 0));
        ports.sort_unstable_by_key(|port| {
            (
                match port.kind() {
                    EventPortKind::Ingress => 0u8,
                    EventPortKind::Exposed => 1u8,
                },
                port.slot(),
            )
        });
        let complex = EventComplex::new(&cells, &incidences, &ports).map_err(debug)?;
        DiscreteEventGerm::new(complex).map_err(debug)?;
        Ok(Self {
            cells,
            incidences,
            ports,
            roles,
        })
    }

    fn complex(&self) -> EventComplex<'_> {
        EventComplex::new(&self.cells, &self.incidences, &self.ports)
            .expect("an immutable Euclidean chart retains its validated event law")
    }

    fn read(&self, trace: &EuclideanTrace) -> TraceRead {
        let germ = DiscreteEventGerm::new(self.complex())
            .expect("an immutable Euclidean chart retains its discrete germ");
        let cells = self
            .cells
            .iter()
            .zip(&self.roles)
            .map(|(cell, role)| {
                let forward = germ.forward_multiplicity(cell.id()).unwrap_or(0);
                let inverse = germ.inverse_multiplicity(cell.id()).unwrap_or(0);
                CellRead {
                    id: cell.id().ordinal(),
                    dependency_rank: cell.dependency_rank(),
                    dimension: cell.dimension(),
                    grain: cell.grain(),
                    role: role.clone(),
                    relation: cog_read(cell.relation()),
                    forward_multiplicity: forward,
                    inverse_multiplicity: inverse,
                    critical: (cell.dependency_rank() < germ.image_rank() && forward != 1)
                        || (cell.dependency_rank() > germ.domain_rank() && inverse != 1),
                    terminal_residual: cell.dependency_rank() < germ.image_rank() && forward == 0,
                }
            })
            .collect();
        let incidences = self
            .incidences
            .iter()
            .copied()
            .map(|incidence| IncidenceRead {
                from: incidence.from().ordinal(),
                to: incidence.to().ordinal(),
                kind: match incidence.kind() {
                    IncidenceKind::Boundary => "BOUNDARY",
                    IncidenceKind::Dependency => "DEPENDENCY",
                    IncidenceKind::RewriteInterface => "REWRITE_INTERFACE",
                },
                hand: hand_name(incidence.hand()),
                slot: incidence.slot(),
            })
            .collect();
        TraceRead {
            input: trace.input,
            states: trace.states.clone(),
            divisions: trace.divisions.clone(),
            gcd: trace.gcd(),
            domain_rank: germ.domain_rank(),
            image_rank: germ.image_rank(),
            internal_ranks: germ.rank_count(),
            dependencies: germ.dependency_count(),
            cells,
            incidences,
        }
    }
}

#[derive(Clone)]
struct WorldCheckpoint {
    machine: LiveCurrentRestImage,
    trajectory: NativeRelationOrganImage,
}

struct EuclideanWorld {
    machine: LiveCurrentMachine,
    trajectory: NativeRelationOrgan,
}

impl EuclideanWorld {
    fn new() -> Result<Self, String> {
        Ok(Self {
            machine: LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?),
            trajectory: NativeRelationOrgan::new(),
        })
    }

    fn from_checkpoint(checkpoint: &WorldCheckpoint) -> Result<Self, String> {
        let machine =
            LiveCurrentMachine::from_rest_image(checkpoint.machine.clone()).map_err(debug)?;
        let trajectory =
            NativeRelationOrgan::recover(checkpoint.trajectory, &machine).map_err(debug)?;
        Ok(Self {
            machine,
            trajectory,
        })
    }

    fn checkpoint(&self) -> Result<WorldCheckpoint, String> {
        Ok(WorldCheckpoint {
            machine: self.machine.rest_image().map_err(debug)?,
            trajectory: self.trajectory.checkpoint(),
        })
    }

    fn present_with(
        &mut self,
        chart: &EuclideanChart,
        hand: IncidenceHand,
        regional: bool,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, String> {
        let mut currents = [NativeEventCurrent::continuing_complex(
            &mut self.trajectory,
            chart.complex(),
            action(),
        )];
        if regional {
            let arcs = [NativeRegionalArc::new(
                0,
                CurrentBoundaryPort::Ingress(0),
                0,
                CurrentBoundaryPort::Exposed(0),
                InterfaceCapability::new(0x4555_434c_4944, 0),
                0,
                0,
                hand,
            )];
            let regions = [NativeRegionalRelation::new(0, &arcs)];
            present_native_event_with_regional(
                &mut self.machine,
                executor,
                &mut currents,
                &[],
                &regions,
            )
            .map_err(debug)
        } else {
            present_native_event_with(&mut self.machine, executor, &mut currents, &[])
                .map_err(debug)
        }
    }
}

#[derive(Default)]
struct WitnessHost {
    host: HostLiveCurrentExecutor,
    touched: Vec<Vec<usize>>,
}

impl LiveCurrentExecutor for WitnessHost {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        let executed =
            self.host
                .enact(physical_revision, standing, currents, relations, regional)?;
        self.touched = executed
            .regional()
            .iter()
            .map(|relation| relation.touched().to_vec())
            .collect();
        Ok(executed)
    }

    fn settle_physical_successor(
        &mut self,
        physical_revision: u64,
        successor: &SparseStandingSurface,
    ) -> Result<(), LiveCurrentError> {
        self.host
            .settle_physical_successor(physical_revision, successor)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct CogRead {
    mag: u32,
    rank_mag: u32,
    rank_rank: i32,
    rank_negative: bool,
    turn: u32,
}

#[derive(Clone, Debug, Serialize)]
struct CellRead {
    id: u64,
    dependency_rank: u32,
    dimension: u32,
    grain: u32,
    role: String,
    relation: CogRead,
    forward_multiplicity: u64,
    inverse_multiplicity: u64,
    critical: bool,
    terminal_residual: bool,
}

#[derive(Clone, Debug, Serialize)]
struct IncidenceRead {
    from: u64,
    to: u64,
    kind: &'static str,
    hand: &'static str,
    slot: u32,
}

#[derive(Clone, Debug, Serialize)]
struct TraceRead {
    input: Pair,
    states: Vec<Pair>,
    divisions: Vec<Division>,
    gcd: u64,
    domain_rank: u32,
    image_rank: u32,
    internal_ranks: u64,
    dependencies: u64,
    cells: Vec<CellRead>,
    incidences: Vec<IncidenceRead>,
}

#[derive(Clone, Debug, Serialize)]
struct PathStepRead {
    incidence: u32,
    support_axis: u32,
    winding: &'static str,
}

#[derive(Clone, Debug, Serialize)]
struct TransportTermRead {
    axes: Vec<u32>,
    coefficient: CogRead,
}

#[derive(Clone, Debug, Serialize)]
struct PathRead {
    interior_folded: bool,
    steps: Vec<PathStepRead>,
    transport: Vec<TransportTermRead>,
}

#[derive(Clone, Debug, Serialize)]
struct BoundaryRead {
    hand: &'static str,
    transition: &'static str,
    paths: Vec<PathRead>,
}

#[derive(Clone, Debug, Serialize)]
struct PinRead {
    ordinal: usize,
    exposed: bool,
    open: bool,
    meeting_reach: CogRead,
    meeting_aim: CogRead,
    meeting_cross: CogRead,
    held_aim: CogRead,
    held_cross: CogRead,
    deed: &'static str,
    winding: &'static str,
    position: Option<[CogRead; 2]>,
    chi: Option<[CogRead; 2]>,
}

#[derive(Clone, Debug, Serialize)]
struct ConstituentRead {
    native_sha256: String,
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: Vec<PinRead>,
    exposed_pins: usize,
    boundaries: Vec<BoundaryRead>,
}

#[derive(Clone, Copy, Debug, Serialize)]
struct MemoryRead {
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

#[derive(Clone, Debug, Serialize)]
struct PassageRead {
    input: Pair,
    hand: &'static str,
    touched_predecessors: Vec<usize>,
    touched_predecessor_sha256: Vec<String>,
    standing_before: MemoryRead,
    standing_after: MemoryRead,
    standing_before_sha256: String,
    standing_after_sha256: String,
    current_folds: u64,
    formed_event_incidences: u64,
    regional: Option<ConstituentRead>,
}

#[derive(Clone, Debug, Serialize)]
struct TrainingRead {
    forward_order: [Pair; 2],
    reversed_order: [Pair; 2],
    traces: Vec<TraceRead>,
    forward_passages: Vec<PassageRead>,
    reverse_order_passages: Vec<PassageRead>,
    no_region_received_same_worldlines: bool,
    ordinary_current_radiation_exact_against_no_region: bool,
    forward_rest_sha256: String,
    reverse_order_rest_sha256: String,
    no_region_rest_sha256: String,
    order_changed_rest: bool,
}

#[derive(Clone, Debug, Serialize)]
struct HeldOutRead {
    trace: TraceRead,
    gcd_face: u64,
    reduced_ratio_face: [u64; 2],
    trained_forward: PassageRead,
    trained_reverse_order: PassageRead,
    no_region_history: PassageRead,
    reversed_hand: PassageRead,
    forward_current_radiation_equals_no_region: bool,
    forward_region_equals_no_region: bool,
    forward_region_equals_reverse_order: bool,
    reversing_only_hand_changed_region: bool,
    all_worlds_enacted_the_complete_trace: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    event_grain: &'static str,
    learning_read: &'static str,
    training: TrainingRead,
    held_out: HeldOutRead,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros Euclidean worldline: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(
        arguments
            .next()
            .ok_or_else(|| "usage: eros_euclidean_worldline <new-report.json>".to_owned())?,
    );
    if arguments.next().is_some() {
        return Err("usage: eros_euclidean_worldline <new-report.json>".to_owned());
    }

    let training_traces = [
        EuclideanTrace::new(TRAINING_FORWARD[0])?,
        EuclideanTrace::new(TRAINING_FORWARD[1])?,
    ];
    if training_traces[0].divisions.len() == training_traces[1].divisions.len() {
        return Err(
            "the corrected fixture must not align its training paths by stage count".to_owned(),
        );
    }
    let training_charts = [
        EuclideanChart::new(&training_traces[0])?,
        EuclideanChart::new(&training_traces[1])?,
    ];
    let held_trace = EuclideanTrace::new(HELD_OUT)?;
    let held_chart = EuclideanChart::new(&held_trace)?;

    let mut forward = EuclideanWorld::new()?;
    let mut reverse_order = EuclideanWorld::new()?;
    let mut no_region = EuclideanWorld::new()?;
    let mut forward_passages = Vec::new();
    let mut reverse_order_passages = Vec::new();
    let mut ordinary_exact = true;

    for at in 0..training_traces.len() {
        let (passage, radiation) = present_read(
            &mut forward,
            &training_traces[at],
            &training_charts[at],
            IncidenceHand::Against,
            true,
        )?;
        let mut control_host = HostLiveCurrentExecutor;
        let control = no_region.present_with(
            &training_charts[at],
            IncidenceHand::Against,
            false,
            &mut control_host,
        )?;
        ordinary_exact &= radiation.currents() == control.currents();
        forward_passages.push(passage);
    }
    for at in [1usize, 0usize] {
        reverse_order_passages.push(
            present_read(
                &mut reverse_order,
                &training_traces[at],
                &training_charts[at],
                IncidenceHand::Against,
                true,
            )?
            .0,
        );
    }

    let forward_checkpoint = forward.checkpoint()?;
    let reverse_checkpoint = reverse_order.checkpoint()?;
    let control_checkpoint = no_region.checkpoint()?;
    let forward_rest = rest_sha256(&forward_checkpoint.machine)?;
    let reverse_rest = rest_sha256(&reverse_checkpoint.machine)?;
    let control_rest = rest_sha256(&control_checkpoint.machine)?;
    for checkpoint in [
        &forward_checkpoint,
        &reverse_checkpoint,
        &control_checkpoint,
    ] {
        let remounted = EuclideanWorld::from_checkpoint(checkpoint)?;
        if checkpoint_bytes(&remounted.checkpoint()?)? != checkpoint_bytes(checkpoint)? {
            return Err("one Euclidean rest/remount changed the exact live body".to_owned());
        }
    }

    let mut forward_probe = EuclideanWorld::from_checkpoint(&forward_checkpoint)?;
    let mut reverse_probe = EuclideanWorld::from_checkpoint(&reverse_checkpoint)?;
    let mut control_probe = EuclideanWorld::from_checkpoint(&control_checkpoint)?;
    let mut hand_probe = EuclideanWorld::from_checkpoint(&forward_checkpoint)?;
    let (forward_read, forward_radiation) = present_read(
        &mut forward_probe,
        &held_trace,
        &held_chart,
        IncidenceHand::Against,
        true,
    )?;
    let (reverse_read, reverse_radiation) = present_read(
        &mut reverse_probe,
        &held_trace,
        &held_chart,
        IncidenceHand::Against,
        true,
    )?;
    let (control_read, control_radiation) = present_read(
        &mut control_probe,
        &held_trace,
        &held_chart,
        IncidenceHand::Against,
        true,
    )?;
    let (hand_read, hand_radiation) = present_read(
        &mut hand_probe,
        &held_trace,
        &held_chart,
        IncidenceHand::With,
        true,
    )?;

    let gcd = held_trace.gcd();
    let reduced = [HELD_OUT.a / gcd, HELD_OUT.b / gcd];
    let held_out = HeldOutRead {
        trace: held_chart.read(&held_trace),
        gcd_face: gcd,
        reduced_ratio_face: reduced,
        forward_current_radiation_equals_no_region: forward_radiation.currents()
            == control_radiation.currents(),
        forward_region_equals_no_region: forward_radiation.regional()
            == control_radiation.regional(),
        forward_region_equals_reverse_order: forward_radiation.regional()
            == reverse_radiation.regional(),
        reversing_only_hand_changed_region: forward_radiation.regional()
            != hand_radiation.regional(),
        all_worlds_enacted_the_complete_trace: [
            &forward_radiation,
            &reverse_radiation,
            &control_radiation,
            &hand_radiation,
        ]
        .iter()
        .all(|radiation| {
            radiation.currents().len() == 1
                && radiation.currents()[0].consequence().cells == held_chart.cells.len() as u64
                && radiation.currents()[0].consequence().incidences
                    == held_chart.incidences.len() as u64
        }),
        trained_forward: forward_read,
        trained_reverse_order: reverse_read,
        no_region_history: control_read,
        reversed_hand: hand_read,
    };
    let training = TrainingRead {
        forward_order: TRAINING_FORWARD,
        reversed_order: [TRAINING_FORWARD[1], TRAINING_FORWARD[0]],
        traces: training_charts
            .iter()
            .zip(&training_traces)
            .map(|(chart, trace)| chart.read(trace))
            .collect(),
        forward_passages,
        reverse_order_passages,
        no_region_received_same_worldlines: true,
        ordinary_current_radiation_exact_against_no_region: ordinary_exact,
        forward_rest_sha256: forward_rest.clone(),
        reverse_order_rest_sha256: reverse_rest.clone(),
        no_region_rest_sha256: control_rest,
        order_changed_rest: forward_rest != reverse_rest,
    };
    let report = Report {
        schema: "eros.euclidean-worldline.observer.v1",
        status: "observed",
        event_grain: "one complete variable-length Euclidean trace is one external event; its actual states are ordered internal stages and b=0 is its exposed boundary",
        learning_read: "the world always enacts the exact trace; learning is read only from prior Standing participating in and changing the complete later regional path",
        training,
        held_out,
    };

    let mut bytes = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("Euclidean report does not encode: {error}"))?;
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
        "eros Euclidean worldline: observed · {} bytes · {}",
        bytes.len(),
        output.display()
    );
    Ok(())
}

fn present_read(
    world: &mut EuclideanWorld,
    trace: &EuclideanTrace,
    chart: &EuclideanChart,
    hand: IncidenceHand,
    regional: bool,
) -> Result<(PassageRead, ContemporaryRadiation), String> {
    let before_memory = memory_read(world.machine.memory());
    let before_rest = world.machine.rest_image().map_err(debug)?;
    let before_hashes = standing_hashes(world.machine.standing())?;
    let mut witness = WitnessHost::default();
    let radiation = world.present_with(chart, hand, regional, &mut witness)?;
    let touched = witness.touched.first().cloned().unwrap_or_default();
    let touched_hashes = touched
        .iter()
        .map(|at| {
            before_hashes
                .get(*at)
                .cloned()
                .ok_or_else(|| "a touched predecessor is absent from Standing-before".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    let regional_read = radiation
        .regional()
        .first()
        .map(|relation| constituent_read(relation.constituent()))
        .transpose()?;
    let current = radiation
        .currents()
        .first()
        .ok_or_else(|| "one Euclidean event returned no current radiation".to_owned())?;
    let after_rest = world.machine.rest_image().map_err(debug)?;
    Ok((
        PassageRead {
            input: trace.input,
            hand: hand_name(hand),
            touched_predecessors: touched,
            touched_predecessor_sha256: touched_hashes,
            standing_before: before_memory,
            standing_after: memory_read(world.machine.memory()),
            standing_before_sha256: rest_sha256(&before_rest)?,
            standing_after_sha256: rest_sha256(&after_rest)?,
            current_folds: current.consequence().folds,
            formed_event_incidences: current.consequence().formed_incidences,
            regional: regional_read,
        },
        radiation,
    ))
}

fn constituent_read(constituent: &LiveConstituent) -> Result<ConstituentRead, String> {
    let mut boundaries = Vec::new();
    for (at, boundary) in constituent.boundaries().iter().enumerate() {
        let transition = match constituent.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => "OPEN",
            Some(LiveBoundaryTransition::Ride) => "RIDE",
            Some(LiveBoundaryTransition::Found) => "FOUND",
            None => "ABSENT",
        };
        let mut paths = Vec::new();
        for path in boundary.paths() {
            paths.push(PathRead {
                interior_folded: path.interior_folded(),
                steps: path
                    .steps()
                    .iter()
                    .copied()
                    .map(|step| PathStepRead {
                        incidence: step.incidence(),
                        support_axis: step.support().local(),
                        winding: winding_name(step.winding()),
                    })
                    .collect(),
                transport: path
                    .transport()
                    .terms()
                    .iter()
                    .map(|term| TransportTermRead {
                        axes: term
                            .blade()
                            .axes()
                            .iter()
                            .map(|axis| axis.local())
                            .collect(),
                        coefficient: cog_read(term.coefficient()),
                    })
                    .collect(),
            });
        }
        boundaries.push(BoundaryRead {
            hand: hand_name(boundary.hand()),
            transition,
            paths,
        });
    }
    let pins = constituent
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
                open: formed.is_none(),
                meeting_reach: cog_read(pin.meeting().arrow.reach),
                meeting_aim: cog_read(pin.meeting().arrow.aim),
                meeting_cross: cog_read(pin.meeting().arrow.cross),
                held_aim: cog_read(pin.held().arrow.aim),
                held_cross: cog_read(pin.held().arrow.cross),
                deed: formed.map_or("OPEN", |formed| deed_name(formed.deed())),
                winding: formed.map_or("OPEN", |formed| winding_name(formed.winding())),
                position: formed
                    .map(|formed| [cog_read(formed.position().0), cog_read(formed.position().1)]),
                chi: formed
                    .map(|formed| [cog_read(formed.chi().same), cog_read(formed.chi().other)]),
            }
        })
        .collect();
    let words = constituent.native_words().map_err(debug)?;
    Ok(ConstituentRead {
        native_sha256: words_sha256(&words),
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins,
        exposed_pins: constituent.exposed().len(),
        boundaries,
    })
}

fn standing_hashes(standing: &SparseStandingSurface) -> Result<Vec<String>, String> {
    standing
        .constituents()
        .iter()
        .map(|constituent| {
            constituent
                .native_words()
                .map(|words| words_sha256(&words))
                .map_err(debug)
        })
        .collect()
}

fn memory_read(memory: LiveMemory) -> MemoryRead {
    MemoryRead {
        standing_cells: memory.standing_cells,
        standing_constituents: memory.standing_constituents,
        constituent_cells: memory.constituent_cells,
        constituent_incidences: memory.constituent_incidences,
        constituent_pins: memory.constituent_pins,
        constituent_paths: memory.constituent_paths,
        constituent_transport_terms: memory.constituent_transport_terms,
        live_lineages: memory.live_lineages,
        carrier_words: memory.carrier_words,
        overflow_nodes: memory.overflow_nodes,
    }
}

fn next_id(extent: usize) -> Result<EventCellId, String> {
    Ok(EventCellId::new(u64::try_from(extent).map_err(|_| {
        "Euclidean cell extent exceeded u64".to_owned()
    })?))
}

fn exact_cog(value: u64) -> Result<Cog, String> {
    i64::try_from(value)
        .map(Cog::lit)
        .map_err(|_| "the bounded Euclidean value exceeded i64".to_owned())
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving Euclidean action")
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

fn hand_name(hand: IncidenceHand) -> &'static str {
    match hand {
        IncidenceHand::Against => "AGAINST",
        IncidenceHand::With => "WITH",
    }
}

fn winding_name(winding: WindingQuantum) -> &'static str {
    match winding {
        WindingQuantum::None => "NONE",
        WindingQuantum::ThisWay => "THIS_WAY",
        WindingQuantum::ThatWay => "THAT_WAY",
    }
}

fn deed_name(deed: FeltDeed) -> &'static str {
    match deed {
        FeltDeed::Ride => "RIDE",
        FeltDeed::FoundThis => "FOUND_THIS",
        FeltDeed::FoundThat => "FOUND_THAT",
        FeltDeed::Dark => "DARK",
    }
}

fn checkpoint_bytes(checkpoint: &WorldCheckpoint) -> Result<Vec<u8>, String> {
    let machine = checkpoint.machine.encode_native_bytes().map_err(debug)?;
    let trajectory = checkpoint.trajectory.encode_native_bytes();
    // The checkpoint the driver hashes is the two wires concatenated, which is a form of no schema
    // any reader holds. Its two constituents are each a form of their own codec, so they are
    // deposited apart: the machine half is `ERST` and has a mouth today; the organ half is the
    // relation-organ wire and has none, which is a fact about the reader's held set rather than
    // about these octets, and the falsifier reports it rather than the concatenation hiding it.
    let deposited = deposit_form_or_message(FORM_DRIVER, CHECKPOINT_MACHINE_FORM, &machine)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let deposited = deposit_form_or_message(FORM_DRIVER, CHECKPOINT_TRAJECTORY_FORM, &trajectory)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let mut bytes = machine;
    bytes.extend_from_slice(&trajectory);
    Ok(bytes)
}

fn rest_sha256(rest: &LiveCurrentRestImage) -> Result<String, String> {
    let octets = rest.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched and
    // still reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead
    // of being hashed and dropped. The address is the content, so this helper -- called at many
    // rests -- deposits every distinct form it sealed instead of overwriting all but the last, and
    // the file name it returns carries the same hash the receipt does.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    Ok(sha256(&octets))
}

fn words_sha256(words: &[u32]) -> String {
    let mut hash = Sha256::new();
    for word in words {
        hash.update(word.to_le_bytes());
    }
    encode_digest(hash.finalize())
}

fn sha256(bytes: &[u8]) -> String {
    encode_digest(Sha256::digest(bytes))
}

fn encode_digest(digest: impl IntoIterator<Item = u8>) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
