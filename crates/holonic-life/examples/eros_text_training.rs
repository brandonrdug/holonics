use std::collections::BTreeSet;
use std::io::Write;
use std::path::PathBuf;

use body::channel::WindingQuantum;
use body::incidence::IncidenceHand;
use body::manifold::{DirectedEventContact, Face, FeltDeed};
use body::num::Cog;
use life::current_world::{
    present_native_event_with_regional, NativeEventCurrent, NativePathChart, NativeRegionalArc,
    NativeRegionalRelation, NativeRelationOrgan, NativeRelationOrganImage,
};
use life::form_mouth::deposit_form_or_message;
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryRadiation, CpuLiveCurrentExecutor, CurrentBoundaryPort, CurrentExecutionRequest,
    DirectedExecutionRequest, ExecutedContemporaryEvent, InterfaceCapability,
    LiveBoundaryTransition, LiveConstituent, LiveCurrentError, LiveCurrentExecutor,
    LiveCurrentMachine, LiveCurrentRestImage, LiveMemory, RegionalExecutionRequest,
    SparseStandingSurface,
};

/// This driver's name at the plate mouth: `.local/artifacts/eros_text_training/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_text_training";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
const TRAINING_LINES: [&str; 4] = [
    "one red sheep runs.",
    "two red sheep walk.",
    "one blue deer runs.",
    "two blue deer walk.",
];

const PASSES: u32 = 3;

#[derive(Clone, Copy)]
struct ProbeSpec {
    prefix: &'static str,
    actual: u8,
}

const PROBES: [ProbeSpec; 4] = [
    ProbeSpec {
        prefix: "one red deer ",
        actual: b'r',
    },
    ProbeSpec {
        prefix: "two red deer ",
        actual: b'w',
    },
    ProbeSpec {
        prefix: "one blue sheep ",
        actual: b'r',
    },
    ProbeSpec {
        prefix: "two blue sheep ",
        actual: b'w',
    },
];

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct CogRead {
    mag: u32,
    rank_mag: u32,
    rank_rank: i32,
    rank_negative: bool,
    turn: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct FaceRead {
    reach: CogRead,
    aim: CogRead,
    cross: CogRead,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct EmissionRead {
    position: [CogRead; 2],
    chi: [CogRead; 2],
    winding: &'static str,
    deed: &'static str,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ContactRead {
    meeting: FaceRead,
    held: FaceRead,
    held_live: bool,
    emission: Option<EmissionRead>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct PinRead {
    ordinal: u32,
    meeting: FaceRead,
    held: FaceRead,
    held_live: bool,
    emission: Option<EmissionRead>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct RegionalShape {
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
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct RegionalRead {
    shape: RegionalShape,
    native_words: usize,
    native_sha256: String,
    exposed: Vec<PinRead>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct StandingConstituentRead {
    ordinal: usize,
    shape: RegionalShape,
    native_words: usize,
    native_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct StandingRead {
    constituents: Vec<StandingConstituentRead>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct CandidateSignature {
    touched_factors: usize,
    standing_constituents_after: usize,
    arc_deed: &'static str,
    regional: RegionalShape,
}

#[derive(Clone, Debug, Serialize)]
struct CandidateRead {
    octet: u8,
    display: String,
    actual: bool,
    touched: Vec<usize>,
    standing_constituents_before: usize,
    standing_constituents_after: usize,
    contact: ContactRead,
    regional: RegionalRead,
    signature: CandidateSignature,
    successor_rest: SealedRest,
}

#[derive(Clone, Debug, Serialize)]
struct ProbeRead {
    prefix: &'static str,
    actual: u8,
    actual_display: String,
    rival: u8,
    contextual_events: u64,
    contextual_rest: SealedRest,
    contextual_memory: MemoryRead,
    contextual_standing: StandingRead,
    touching_candidates: Vec<u8>,
    actual_is_only_touching_candidate: bool,
    actual_touches: bool,
    rival_touches: bool,
    actual_and_rival_signatures_differ: bool,
    candidates: Vec<CandidateRead>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct ProbeSummary {
    probes: usize,
    actual_is_only_touching_candidate: usize,
    actual_and_rival_both_touch: usize,
    actual_does_not_touch: usize,
    actual_and_rival_signatures_differ: usize,
}

#[derive(Clone, Debug, Serialize)]
struct CheckpointRead {
    pass: u32,
    direction: &'static str,
    training_events: u64,
    rest: SealedRest,
    memory: MemoryRead,
    standing: StandingRead,
    probe_summary: ProbeSummary,
    probes: Vec<ProbeRead>,
}

#[derive(Clone, Debug, Serialize)]
struct TrainingPassRead {
    pass: u32,
    direction: &'static str,
    events: u64,
    new_constituent_events: u64,
    touched_events: u64,
    touched_factors: u64,
    maximum_emitted_grain: u32,
    before: MemoryRead,
    after: MemoryRead,
}

#[derive(Clone, Debug, Serialize)]
struct PassageRead {
    pass: u32,
    forward_training: Option<TrainingPassRead>,
    reversed_training: Option<TrainingPassRead>,
    forward: CheckpointRead,
    reversed: CheckpointRead,
    checkpoint_rests_equal: bool,
}

#[derive(Clone, Debug, Serialize)]
struct FixtureRead {
    training_lines: [&'static str; 4],
    passes: u32,
    candidate_octets: Vec<u8>,
    candidate_displays: Vec<String>,
    held_out_prefixes: Vec<&'static str>,
    held_out_actual_octets: Vec<u8>,
    reversed_lines_retain_exact_octet_inventory: bool,
    held_out_combinations_absent_from_training: bool,
    every_terminal_local_context_observed_with_r_and_w: bool,
}

#[derive(Clone, Debug, Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    event_grain: &'static str,
    candidate_aperture: &'static str,
    fixture: FixtureRead,
    passages: Vec<PassageRead>,
}

#[derive(Clone)]
struct TextCheckpoint {
    machine: LiveCurrentRestImage,
    context: NativeRelationOrganImage,
    arrival: NativeRelationOrganImage,
    training_events: u64,
}

struct TextWorld {
    machine: LiveCurrentMachine,
    context: NativeRelationOrgan,
    arrival: NativeRelationOrgan,
    training_events: u64,
}

impl TextWorld {
    fn new() -> Result<Self, String> {
        Ok(Self {
            machine: LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?),
            context: NativeRelationOrgan::new(),
            arrival: NativeRelationOrgan::new(),
            training_events: 0,
        })
    }

    fn from_checkpoint(checkpoint: &TextCheckpoint) -> Result<Self, String> {
        let machine =
            LiveCurrentMachine::from_rest_image(checkpoint.machine.clone()).map_err(debug)?;
        let context = NativeRelationOrgan::recover(checkpoint.context, &machine).map_err(debug)?;
        let arrival = NativeRelationOrgan::recover(checkpoint.arrival, &machine).map_err(debug)?;
        Ok(Self {
            machine,
            context,
            arrival,
            training_events: checkpoint.training_events,
        })
    }

    fn checkpoint(&self) -> Result<TextCheckpoint, String> {
        Ok(TextCheckpoint {
            machine: self.machine.rest_image().map_err(debug)?,
            context: self.context.checkpoint(),
            arrival: self.arrival.checkpoint(),
            training_events: self.training_events,
        })
    }

    fn present_window_with(
        &mut self,
        window: [u8; 3],
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ContemporaryRadiation, String> {
        let context = [octet(window[0])?, octet(window[1])?];
        let context_chart = NativePathChart::new(&context).map_err(debug)?;
        let arrival = [octet(window[2])?];
        let arcs = [NativeRegionalArc::new(
            0,
            CurrentBoundaryPort::Exposed(0),
            1,
            CurrentBoundaryPort::Cell,
            InterfaceCapability::new(0x5445_5854, 0),
            0,
            0,
            IncidenceHand::Against,
        )];
        let regional = [NativeRegionalRelation::new(1, &arcs)];
        let mut currents = [
            NativeEventCurrent::continuing_complex(
                &mut self.context,
                context_chart.complex(),
                action(),
            ),
            NativeEventCurrent::continuing(&mut self.arrival, &arrival, action()),
        ];
        let radiation = present_native_event_with_regional(
            &mut self.machine,
            executor,
            &mut currents,
            &[],
            &regional,
        )
        .map_err(debug)?;
        self.training_events = self
            .training_events
            .checked_add(1)
            .ok_or_else(|| "text event extent exceeded u64".to_owned())?;
        Ok(radiation)
    }

    fn present_line(&mut self, line: &[u8]) -> Result<u64, String> {
        let mut events = 0u64;
        let mut cpu = CpuLiveCurrentExecutor;
        for (at, window) in line.windows(3).enumerate() {
            self.present_window_with([window[0], window[1], window[2]], &mut cpu)
                .map_err(|error| {
                    format!(
                        "prefix window {at} [{} {} {}]: {error}",
                        display(window[0]),
                        display(window[1]),
                        display(window[2])
                    )
                })?;
            events += 1;
        }
        Ok(events)
    }
}

#[derive(Default)]
struct WitnessCpu {
    cpu: CpuLiveCurrentExecutor,
    touched: Vec<Vec<usize>>,
}

impl WitnessCpu {
    fn one_touched(&self) -> Result<Vec<usize>, String> {
        match self.touched.as_slice() {
            [one] => Ok(one.clone()),
            _ => Err(format!(
                "one text region produced {} touched populations",
                self.touched.len()
            )),
        }
    }
}

impl LiveCurrentExecutor for WitnessCpu {
    fn enact(
        &mut self,
        physical_revision: u64,
        standing: &SparseStandingSurface,
        currents: &[CurrentExecutionRequest<'_>],
        relations: &[DirectedExecutionRequest],
        regional: &[RegionalExecutionRequest<'_>],
    ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
        let executed =
            self.cpu
                .enact(physical_revision, standing, currents, relations, regional)?;
        self.touched.clear();
        self.touched
            .try_reserve_exact(executed.regional().len())
            .map_err(|_| LiveCurrentError::ResourceReservation)?;
        for region in executed.regional() {
            self.touched.push(region.touched().to_vec());
        }
        Ok(executed)
    }

    fn settle_physical_successor(
        &mut self,
        physical_revision: u64,
        successor: &SparseStandingSurface,
    ) -> Result<(), LiveCurrentError> {
        self.cpu
            .settle_physical_successor(physical_revision, successor)
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros text training: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let output = PathBuf::from(
        arguments
            .next()
            .ok_or_else(|| "usage: eros_text_training <new-report.json>".to_owned())?,
    );
    if arguments.next().is_some() {
        return Err("usage: eros_text_training <new-report.json>".to_owned());
    }

    let candidates = candidate_octets();
    validate_fixture(&candidates)?;

    let mut forward = TextWorld::new()?;
    let mut reversed = TextWorld::new()?;
    let empty = forward.checkpoint()?;
    let mut passages = Vec::new();
    passages.push(passage_read(0, None, None, &empty, &empty, &candidates)?);

    for pass in 1..=PASSES {
        let forward_training = train_pass(&mut forward, pass, false)?;
        let reversed_training = train_pass(&mut reversed, pass, true)?;
        let forward_checkpoint = forward.checkpoint()?;
        let reversed_checkpoint = reversed.checkpoint()?;
        passages.push(passage_read(
            pass,
            Some(forward_training),
            Some(reversed_training),
            &forward_checkpoint,
            &reversed_checkpoint,
            &candidates,
        )?);
    }

    let report = Report {
        schema: "eros.text-training.observer.v1",
        status: "observed",
        event_grain: "two raw octets form one ordered NativePathChart edge; the actual next octet cones that edge through one regional arm",
        candidate_aperture: "every distinct nonzero training octet, each on an exact sibling remount after the same held-out prefix",
        fixture: fixture_read(&candidates),
        passages,
    };
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
        "eros text training: observed · {} bytes · {}",
        bytes.len(),
        output.display()
    );
    Ok(())
}

fn passage_read(
    pass: u32,
    forward_training: Option<TrainingPassRead>,
    reversed_training: Option<TrainingPassRead>,
    forward: &TextCheckpoint,
    reversed: &TextCheckpoint,
    candidates: &[u8],
) -> Result<PassageRead, String> {
    let forward_read = checkpoint_read(pass, "forward", forward, candidates)?;
    let reversed_read = checkpoint_read(pass, "reversed", reversed, candidates)?;
    Ok(PassageRead {
        pass,
        forward_training,
        reversed_training,
        checkpoint_rests_equal: forward_read.rest.sha256 == reversed_read.rest.sha256,
        forward: forward_read,
        reversed: reversed_read,
    })
}

fn train_pass(world: &mut TextWorld, pass: u32, reverse: bool) -> Result<TrainingPassRead, String> {
    let direction = if reverse { "reversed" } else { "forward" };
    let before = memory_read(world.machine.memory());
    let mut events = 0u64;
    let mut new_constituent_events = 0u64;
    let mut touched_events = 0u64;
    let mut touched_factors = 0u64;
    let mut maximum_emitted_grain = 0u32;
    for line in TRAINING_LINES {
        let material: Vec<u8> = if reverse {
            line.bytes().rev().collect()
        } else {
            line.as_bytes().to_vec()
        };
        for (at, window) in material.windows(3).enumerate() {
            let mut witness = WitnessCpu::default();
            let radiation = world
                .present_window_with([window[0], window[1], window[2]], &mut witness)
                .map_err(|error| {
                    format!(
                        "{direction} pass {pass} line {line:?} window {at} [{} {} {}]: {error}",
                        display(window[0]),
                        display(window[1]),
                        display(window[2])
                    )
                })?;
            let touched = witness.one_touched()?;
            if touched.is_empty() {
                new_constituent_events += 1;
            } else {
                touched_events += 1;
                touched_factors = touched_factors
                    .checked_add(touched.len() as u64)
                    .ok_or_else(|| "touched-factor extent exceeded u64".to_owned())?;
            }
            let region = radiation
                .regional()
                .first()
                .ok_or_else(|| "one training window returned no regional relation".to_owned())?;
            maximum_emitted_grain = maximum_emitted_grain.max(region.constituent().grain());
            events += 1;
        }
    }
    Ok(TrainingPassRead {
        pass,
        direction,
        events,
        new_constituent_events,
        touched_events,
        touched_factors,
        maximum_emitted_grain,
        before,
        after: memory_read(world.machine.memory()),
    })
}

fn checkpoint_read(
    pass: u32,
    direction: &'static str,
    checkpoint: &TextCheckpoint,
    candidates: &[u8],
) -> Result<CheckpointRead, String> {
    let machine = LiveCurrentMachine::from_rest_image(checkpoint.machine.clone()).map_err(debug)?;
    let mut probes = Vec::new();
    for probe in PROBES {
        probes.push(probe_read(checkpoint, probe, candidates)?);
    }
    let probe_summary = ProbeSummary {
        probes: probes.len(),
        actual_is_only_touching_candidate: probes
            .iter()
            .filter(|probe| probe.actual_is_only_touching_candidate)
            .count(),
        actual_and_rival_both_touch: probes
            .iter()
            .filter(|probe| probe.actual_touches && probe.rival_touches)
            .count(),
        actual_does_not_touch: probes.iter().filter(|probe| !probe.actual_touches).count(),
        actual_and_rival_signatures_differ: probes
            .iter()
            .filter(|probe| probe.actual_and_rival_signatures_differ)
            .count(),
    };
    Ok(CheckpointRead {
        pass,
        direction,
        training_events: checkpoint.training_events,
        rest: seal_rest(&checkpoint.machine)?,
        memory: memory_read(machine.memory()),
        standing: standing_read(machine.standing())?,
        probe_summary,
        probes,
    })
}

fn probe_read(
    checkpoint: &TextCheckpoint,
    probe: ProbeSpec,
    candidates: &[u8],
) -> Result<ProbeRead, String> {
    let mut contextual = TextWorld::from_checkpoint(checkpoint)?;
    let contextual_events = contextual.present_line(probe.prefix.as_bytes())?;
    let contextual_checkpoint = contextual.checkpoint()?;
    let contextual_memory = memory_read(contextual.machine.memory());
    let contextual_standing = standing_read(contextual.machine.standing())?;
    let contextual_rest = seal_rest(&contextual_checkpoint.machine)?;
    let context = probe
        .prefix
        .as_bytes()
        .get(probe.prefix.len().saturating_sub(2)..)
        .ok_or_else(|| "a held-out prefix needs two context octets".to_owned())?;

    let mut rows = Vec::new();
    for candidate in candidates.iter().copied() {
        let mut world = TextWorld::from_checkpoint(&contextual_checkpoint)?;
        let before = world.machine.memory().standing_constituents;
        let mut witness = WitnessCpu::default();
        let radiation = world
            .present_window_with([context[0], context[1], candidate], &mut witness)
            .map_err(|error| {
                format!(
                    "candidate {} after prefix {:?}: {error}",
                    display(candidate),
                    probe.prefix
                )
            })?;
        let touched = witness.one_touched()?;
        let returned = radiation
            .regional()
            .first()
            .ok_or_else(|| "one candidate returned no regional relation".to_owned())?;
        let arc = returned
            .arcs()
            .first()
            .ok_or_else(|| "one candidate returned no regional arc".to_owned())?;
        let regional = regional_read(returned.constituent())?;
        let after = world.machine.memory().standing_constituents;
        let arc_deed = arc
            .contact()
            .emission
            .map_or("OPEN", |emission| deed_name(emission.deed));
        let signature = CandidateSignature {
            touched_factors: touched.len(),
            standing_constituents_after: after,
            arc_deed,
            regional: regional.shape.clone(),
        };
        rows.push(CandidateRead {
            octet: candidate,
            display: display(candidate),
            actual: candidate == probe.actual,
            touched,
            standing_constituents_before: before,
            standing_constituents_after: after,
            contact: contact_read(arc.contact()),
            regional,
            signature,
            successor_rest: seal_rest(&world.machine.rest_image().map_err(debug)?)?,
        });
    }

    let rival = if probe.actual == b'r' { b'w' } else { b'r' };
    let actual_row = rows
        .iter()
        .find(|row| row.octet == probe.actual)
        .ok_or_else(|| "the actual octet is absent from the candidate aperture".to_owned())?;
    let rival_row = rows
        .iter()
        .find(|row| row.octet == rival)
        .ok_or_else(|| "the grammatical rival is absent from the candidate aperture".to_owned())?;
    let touching_candidates: Vec<u8> = rows
        .iter()
        .filter(|row| !row.touched.is_empty())
        .map(|row| row.octet)
        .collect();
    Ok(ProbeRead {
        prefix: probe.prefix,
        actual: probe.actual,
        actual_display: display(probe.actual),
        rival,
        contextual_events,
        contextual_rest,
        contextual_memory,
        contextual_standing,
        actual_is_only_touching_candidate: touching_candidates == [probe.actual],
        actual_touches: !actual_row.touched.is_empty(),
        rival_touches: !rival_row.touched.is_empty(),
        actual_and_rival_signatures_differ: actual_row.signature != rival_row.signature,
        touching_candidates,
        candidates: rows,
    })
}

fn regional_read(constituent: &LiveConstituent) -> Result<RegionalRead, String> {
    let shape = regional_shape(constituent);
    let words = constituent.native_words().map_err(debug)?;
    let mut exposed = Vec::new();
    for ordinal in constituent.exposed().iter().copied() {
        let pin = constituent
            .pins()
            .get(ordinal as usize)
            .ok_or_else(|| "an exposed pin ordinal is absent".to_owned())?;
        exposed.push(PinRead {
            ordinal,
            meeting: face_read(pin.meeting()),
            held: face_read(pin.held()),
            held_live: pin.held_live(),
            emission: pin.formed().map(|formed| EmissionRead {
                position: [cog_read(formed.position().0), cog_read(formed.position().1)],
                chi: [cog_read(formed.chi().same), cog_read(formed.chi().other)],
                winding: winding_name(formed.winding()),
                deed: deed_name(formed.deed()),
            }),
        });
    }
    Ok(RegionalRead {
        shape,
        native_words: words.len(),
        native_sha256: words_sha256(&words),
        exposed,
    })
}

fn standing_read(standing: &SparseStandingSurface) -> Result<StandingRead, String> {
    let mut constituents = Vec::new();
    for (ordinal, constituent) in standing.constituents().iter().enumerate() {
        let words = constituent.native_words().map_err(debug)?;
        constituents.push(StandingConstituentRead {
            ordinal,
            shape: regional_shape(constituent),
            native_words: words.len(),
            native_sha256: words_sha256(&words),
        });
    }
    Ok(StandingRead { constituents })
}

fn regional_shape(constituent: &LiveConstituent) -> RegionalShape {
    let mut paths = 0usize;
    let mut folded_paths = 0usize;
    let mut transport_terms = 0usize;
    let mut open_boundaries = 0usize;
    let mut ride_boundaries = 0usize;
    let mut found_boundaries = 0usize;
    for (at, boundary) in constituent.boundaries().iter().enumerate() {
        match constituent.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => {}
        }
        paths += boundary.paths().len();
        for path in boundary.paths() {
            folded_paths += usize::from(path.interior_folded());
            transport_terms += path.transport().terms().len();
        }
    }
    RegionalShape {
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
    }
}

fn contact_read(contact: DirectedEventContact) -> ContactRead {
    ContactRead {
        meeting: face_read(contact.meeting),
        held: face_read(contact.receiver.held),
        held_live: contact.receiver.held_live,
        emission: contact.emission.map(|emission| EmissionRead {
            position: [cog_read(emission.position.0), cog_read(emission.position.1)],
            chi: [
                cog_read(emission.term.chi.same),
                cog_read(emission.term.chi.other),
            ],
            winding: winding_name(emission.term.winding),
            deed: deed_name(emission.deed),
        }),
    }
}

fn face_read(face: Face) -> FaceRead {
    FaceRead {
        reach: cog_read(face.arrow.reach),
        aim: cog_read(face.arrow.aim),
        cross: cog_read(face.arrow.cross),
    }
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

fn fixture_read(candidates: &[u8]) -> FixtureRead {
    FixtureRead {
        training_lines: TRAINING_LINES,
        passes: PASSES,
        candidate_octets: candidates.to_vec(),
        candidate_displays: candidates.iter().copied().map(display).collect(),
        held_out_prefixes: PROBES.iter().map(|probe| probe.prefix).collect(),
        held_out_actual_octets: PROBES.iter().map(|probe| probe.actual).collect(),
        reversed_lines_retain_exact_octet_inventory: reversed_inventory_exact(),
        held_out_combinations_absent_from_training: PROBES.iter().all(|probe| {
            !TRAINING_LINES
                .iter()
                .any(|line| line.contains(probe.prefix))
        }),
        every_terminal_local_context_observed_with_r_and_w: PROBES.iter().all(|probe| {
            let bytes = probe.prefix.as_bytes();
            let context = &bytes[bytes.len() - 2..];
            contains_window([context[0], context[1], b'r'])
                && contains_window([context[0], context[1], b'w'])
        }),
    }
}

fn validate_fixture(candidates: &[u8]) -> Result<(), String> {
    let fixture = fixture_read(candidates);
    if !fixture.reversed_lines_retain_exact_octet_inventory
        || !fixture.held_out_combinations_absent_from_training
        || !fixture.every_terminal_local_context_observed_with_r_and_w
        || PROBES
            .iter()
            .any(|probe| candidates.binary_search(&probe.actual).is_err())
    {
        return Err("the declared text fixture does not satisfy its fixed controls".to_owned());
    }
    Ok(())
}

fn candidate_octets() -> Vec<u8> {
    TRAINING_LINES
        .iter()
        .flat_map(|line| line.bytes())
        .filter(|octet| *octet != 0)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn contains_window(window: [u8; 3]) -> bool {
    TRAINING_LINES.iter().any(|line| {
        line.as_bytes()
            .windows(3)
            .any(|candidate| candidate == window)
    })
}

fn reversed_inventory_exact() -> bool {
    TRAINING_LINES.iter().all(|line| {
        let mut forward = line.as_bytes().to_vec();
        let mut reverse: Vec<u8> = line.bytes().rev().collect();
        forward.sort_unstable();
        reverse.sort_unstable();
        forward == reverse
    })
}

fn octet(value: u8) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value as i64))
        .ok_or_else(|| "a zero octet cannot enter this nonzero ASCII fixture".to_owned())
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving text-world action")
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

fn deed_name(deed: FeltDeed) -> &'static str {
    match deed {
        FeltDeed::Ride => "RIDE",
        FeltDeed::FoundThis => "FOUND_THIS",
        FeltDeed::FoundThat => "FOUND_THAT",
        FeltDeed::Dark => "DARK",
    }
}

fn winding_name(winding: WindingQuantum) -> &'static str {
    match winding {
        WindingQuantum::None => "NONE",
        WindingQuantum::ThisWay => "THIS_WAY",
        WindingQuantum::ThatWay => "THAT_WAY",
    }
}

fn display(octet: u8) -> String {
    octet.escape_ascii().map(char::from).collect()
}

/// One rest, sealed: the hash this driver has always reported, and the address of the artifact it
/// is a hash OF. Reporting only the hash is what lost 510 of this driver's 511 returned rests.
#[derive(Clone, Debug, Serialize)]
struct SealedRest {
    sha256: String,
    form: String,
}

/// Seal one rest at the plate mouth and return both halves of its receipt.
///
/// THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash is untouched and still
/// reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead of being
/// hashed and dropped.
///
/// This helper is called once per checkpoint, once per probe, and **once per candidate inside the
/// probe loop** -- 511 distinct rests in a full run. Under a fixed `machine-rest.form` the first
/// 510 were overwritten and the survivor carried nothing saying which rest it was, so the receipt
/// held 511 hashes and the disk held one nameless artifact. The mouth now addresses a form by its
/// content, and the address travels back into the receipt beside the hash rather than being
/// dropped at the call site.
fn seal_rest(rest: &LiveCurrentRestImage) -> Result<SealedRest, String> {
    let octets = rest.encode_native_bytes().map_err(debug)?;
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &octets)?;
    // The hash reported here is the mouth's content address, not a second digest computed beside
    // it. That is the whole point of addressing a form by its content: the receipt's hash and the
    // artifact's file name are one string rather than two that could drift. The independent frame
    // on it is a different process -- `holon-plate deposit` recomputes `form_sha256` from the file
    // and prints it, so a wrong address here is visible outside this crate.
    Ok(SealedRest {
        sha256: deposited.address,
        form: deposited.path.display().to_string(),
    })
}

fn words_sha256(words: &[u32]) -> String {
    let mut hash = Sha256::new();
    for word in words {
        hash.update(word.to_le_bytes());
    }
    encode_digest(hash.finalize())
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
