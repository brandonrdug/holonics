use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::Instant;

use body::channel::WindingQuantum;
use body::incidence::IncidenceHand;
use body::manifold::{Face, FeltDeed};
use body::num::{Cog, Rung};
use life::current_world::{
    present_native_event_with_regional, NativeEventCurrent, NativeRegionalArc,
    NativeRegionalRelation, NativeRelationOrgan,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    CurrentBoundaryPort, InterfaceCapability, LiveBoundaryTransition, LiveConstituent,
    LiveCurrentMachine, LiveCurrentRestImage, LiveIncidenceKind, LiveMemory,
    ParallelHostLiveCurrentExecutor, SparseStandingSurface,
};

const SOURCE_SCHEMA: &str = "eros.cohered-corpus.source.v1";
const REPORT_SCHEMA: &str = "eros.cohered-corpus.report.v1";
const OBSERVATION_ID: &str = "eros-cohered-corpus-01";
const PREFLIGHT_LINES: usize = 32;
const ADJACENCY_NAMESPACE: u64 = 0x4552_4f53_544f_4b41;
const MAX_ACCEPTED_PROJECTED_MICROS: u128 = 3_600_000_000;
const MAX_ACCEPTED_RSS_KIB: u64 = 8 * 1024 * 1024;

#[derive(Clone, Debug, Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    event_law: serde_json::Value,
    corpora: SourceCorpora,
    tokenizer: serde_json::Value,
    training_lines: Vec<SourceLine>,
    probes: Vec<SourceProbe>,
    controls: Vec<String>,
    stopping_condition: String,
}

#[derive(Clone, Debug, Deserialize)]
struct SourceCorpora {
    training: CorpusCut,
    validation: CorpusCut,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
struct CorpusCut {
    path: String,
    sha256: String,
    token_limit: usize,
    complete_lines: usize,
    token_occurrences: usize,
}

#[derive(Clone, Debug, Deserialize)]
struct SourceLine {
    line_ordinal: u32,
    text: String,
    text_sha256: String,
    token_ids: Vec<u32>,
}

#[derive(Clone, Debug, Deserialize)]
struct SourceProbe {
    species: String,
    validation: SourceLine,
    target_index: usize,
    prefix_token_ids: Vec<u32>,
    actual_token_id: u32,
    actual_piece: String,
    sibling_token_id: u32,
    sibling_piece: String,
    actual_candidate_token_ids: Vec<u32>,
    sibling_candidate_token_ids: Vec<u32>,
    selection_evidence: serde_json::Value,
}

#[derive(Clone, Copy)]
enum Direction {
    Chronological,
    ReversedWithinUtterance,
}

impl Direction {
    const fn name(self) -> &'static str {
        match self {
            Self::Chronological => "chronological",
            Self::ReversedWithinUtterance => "reversed_within_utterance",
        }
    }
}

#[derive(Clone, Default)]
struct AncestryState {
    counts: BTreeMap<Vec<u32>, usize>,
    sources: BTreeMap<Vec<u32>, BTreeSet<u32>>,
}

impl AncestryState {
    fn transition(
        &self,
        after_keys: &[Vec<u32>],
        replacement_key: &[u32],
        source_line: Option<u32>,
    ) -> Result<(Self, Vec<TouchedFactorRead>), String> {
        let mut retained = count_keys(after_keys);
        let replacement_count = retained.get_mut(replacement_key).ok_or_else(|| {
            "the returned regional constituent is absent from Standing-after".to_owned()
        })?;
        if *replacement_count == 0 {
            return Err("the replacement constituent has zero Standing multiplicity".to_owned());
        }
        *replacement_count -= 1;
        if *replacement_count == 0 {
            retained.remove(replacement_key);
        }

        for (key, count) in &retained {
            let before = self.counts.get(key).copied().unwrap_or(0);
            if *count > before {
                return Err(
                    "Standing-after contains a non-replacement constituent absent before"
                        .to_owned(),
                );
            }
        }

        let mut touched = Vec::new();
        let mut inherited_sources = BTreeSet::new();
        for (key, before) in &self.counts {
            let remains = retained.get(key).copied().unwrap_or(0);
            if remains > *before {
                return Err("retained multiplicity exceeds Standing-before".to_owned());
            }
            let removed = before - remains;
            if removed == 0 {
                continue;
            }
            let sources = self.sources.get(key).cloned().unwrap_or_default();
            inherited_sources.extend(sources.iter().copied());
            touched.push(TouchedFactorRead {
                native_sha256: words_sha256(key),
                instances: removed,
                training_source_lines: sources.into_iter().collect(),
            });
        }

        if let Some(line) = source_line {
            inherited_sources.insert(line);
        }
        let after_counts = count_keys(after_keys);
        let mut after_sources = BTreeMap::new();
        for key in after_counts.keys() {
            let mut sources = self.sources.get(key).cloned().unwrap_or_default();
            if key.as_slice() == replacement_key {
                sources.extend(inherited_sources.iter().copied());
            }
            after_sources.insert(key.clone(), sources);
        }
        let next = Self {
            counts: after_counts,
            sources: after_sources,
        };
        Ok((next, touched))
    }

    fn sources_for_key(&self, key: &[u32]) -> Vec<u32> {
        self.sources
            .get(key)
            .map(|sources| sources.iter().copied().collect())
            .unwrap_or_default()
    }
}

struct CorpusWorld {
    machine: LiveCurrentMachine,
    ancestry: AncestryState,
    executor: ParallelHostLiveCurrentExecutor,
}

impl CorpusWorld {
    fn new(executor_threads: usize) -> Result<Self, String> {
        Ok(Self {
            machine: LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?),
            ancestry: AncestryState::default(),
            executor: ParallelHostLiveCurrentExecutor::new(executor_threads),
        })
    }

    fn from_checkpoint(
        rest: LiveCurrentRestImage,
        ancestry: AncestryState,
        executor_threads: usize,
    ) -> Result<Self, String> {
        Ok(Self {
            machine: LiveCurrentMachine::from_rest_image(rest).map_err(debug)?,
            ancestry,
            executor: ParallelHostLiveCurrentExecutor::new(executor_threads),
        })
    }

    fn present_tokens(
        &mut self,
        token_ids: &[u32],
        source_line: Option<u32>,
    ) -> Result<EventOutcome, String> {
        if token_ids.is_empty() {
            return Err("an utterance event cannot be empty".to_owned());
        }
        let before = memory_read(self.machine.memory());
        let atoms = token_ids
            .iter()
            .copied()
            .map(token_atom)
            .collect::<Result<Vec<_>, _>>()?;
        let mut organs = (0..atoms.len())
            .map(|_| NativeRelationOrgan::new())
            .collect::<Vec<_>>();
        let mut currents = organs
            .iter_mut()
            .zip(atoms.iter().copied())
            .map(|(organ, atom)| NativeEventCurrent::ending(organ, atom, action()))
            .collect::<Vec<_>>();
        let arcs = token_ids
            .windows(2)
            .enumerate()
            .map(|(at, pair)| {
                Ok(NativeRegionalArc::new(
                    at,
                    CurrentBoundaryPort::Cell,
                    at + 1,
                    CurrentBoundaryPort::Cell,
                    InterfaceCapability::new(
                        ADJACENCY_NAMESPACE,
                        pair_capability(pair[0], pair[1]),
                    ),
                    u32::try_from(at)
                        .map_err(|_| "one utterance has too many adjacency slots".to_owned())?,
                    0,
                    IncidenceHand::Against,
                ))
            })
            .collect::<Result<Vec<_>, String>>()?;
        let regions = if arcs.is_empty() {
            Vec::new()
        } else {
            vec![NativeRegionalRelation::new(currents.len() - 1, &arcs)]
        };
        let started = Instant::now();
        let radiation = present_native_event_with_regional(
            &mut self.machine,
            &mut self.executor,
            &mut currents,
            &[],
            &regions,
        )
        .map_err(debug)?;
        let wall_micros = started.elapsed().as_micros();
        if self.machine.memory().live_lineages != 0 {
            return Err("ended utterance occurrences remained live after commit".to_owned());
        }

        let (replacement, touched) = match radiation.regional() {
            [] => {
                if token_ids.len() != 1 {
                    return Err("a plural utterance returned no regional constituent".to_owned());
                }
                (None, Vec::new())
            }
            [region] => {
                let replacement = region.constituent().clone();
                let words = replacement.native_words().map_err(debug)?;
                let after_keys = standing_keys(&self.machine)?;
                let (ancestry, touched) =
                    self.ancestry.transition(&after_keys, &words, source_line)?;
                self.ancestry = ancestry;
                (Some(replacement), touched)
            }
            many => {
                return Err(format!(
                    "one utterance returned {} regional constituents",
                    many.len()
                ))
            }
        };
        Ok(EventOutcome {
            before,
            after: memory_read(self.machine.memory()),
            wall_micros,
            touched,
            replacement,
        })
    }
}

struct EventOutcome {
    before: MemoryRead,
    after: MemoryRead,
    wall_micros: u128,
    touched: Vec<TouchedFactorRead>,
    replacement: Option<LiveConstituent>,
}

struct TrainedBody {
    rest: LiveCurrentRestImage,
    ancestry: AncestryState,
    read: TrainingRead,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    mode: &'static str,
    source: SourceRead,
    execution: ExecutionRead,
    preflight_projection: Option<ProjectionRead>,
    training: Vec<TrainingRead>,
    probes: Vec<BodyProbeRead>,
}

#[derive(Serialize)]
struct SourceRead {
    source_path: String,
    source_sha256: String,
    event_law: serde_json::Value,
    corpora: SourceCorporaRead,
    tokenizer: serde_json::Value,
    controls: Vec<String>,
    stopping_condition: String,
}

#[derive(Serialize)]
struct SourceCorporaRead {
    training: CorpusCut,
    validation: CorpusCut,
}

#[derive(Serialize)]
struct ExecutionRead {
    logical_cpu_parallelism: usize,
    concurrent_training_bodies: usize,
    host_threads_per_training_body: usize,
    concurrent_probe_bodies: usize,
    host_threads_per_probe_body: usize,
    source_training_lines: usize,
    received_training_lines: usize,
    received_training_token_occurrences_per_body: usize,
    wall_micros: u128,
    process_peak_rss_kib: Option<u64>,
}

#[derive(Serialize)]
struct ProjectionRead {
    preflight_lines_per_body: usize,
    preflight_token_occurrences_per_body: usize,
    projected_full_wall_micros: u128,
    projected_full_wall_ratio: String,
    measured_peak_rss_kib: Option<u64>,
    projected_report_floor_bytes: u128,
    projected_under_one_hour: bool,
    measured_under_eight_gib: bool,
    resource_boundary_accepts_scientific_run: bool,
}

#[derive(Serialize)]
struct TrainingRead {
    direction: &'static str,
    events: usize,
    token_occurrences: usize,
    adjacency_arcs: usize,
    new_constituent_events: usize,
    recurrent_events: usize,
    touched_factor_geometries: usize,
    touched_factor_instances: usize,
    maximum_replacement_grain: u32,
    elapsed_micros: u128,
    peak_rss_kib: Option<u64>,
    before: MemoryRead,
    after: MemoryRead,
    rest_sha256: String,
    first_utterances: Vec<TrainingEventRead>,
    standing_ancestry: Vec<StandingAncestryRead>,
}

#[derive(Serialize)]
struct TrainingEventRead {
    event_ordinal: usize,
    source_line_ordinal: u32,
    source_text: String,
    source_text_sha256: String,
    token_ids: Vec<u32>,
    wall_micros: u128,
    before: MemoryRead,
    after: MemoryRead,
    touched: Vec<TouchedFactorRead>,
    lower_constituent_instances_departed: usize,
    replacement: Option<ConstituentRead>,
}

#[derive(Clone, Serialize)]
struct TouchedFactorRead {
    native_sha256: String,
    instances: usize,
    training_source_lines: Vec<u32>,
}

#[derive(Serialize)]
struct StandingAncestryRead {
    ordinal: usize,
    native_sha256: String,
    equal_geometry_instances: usize,
    training_source_lines: Vec<u32>,
    shape: ConstituentShape,
}

#[derive(Serialize)]
struct BodyProbeRead {
    body: &'static str,
    checkpoint_rest_sha256: String,
    checkpoint_memory: MemoryRead,
    probes: Vec<ProbeRead>,
}

#[derive(Serialize)]
struct ProbeRead {
    species: String,
    validation_line_ordinal: u32,
    validation_text: String,
    target_index: usize,
    prefix_token_ids: Vec<u32>,
    actual_token_id: u32,
    actual_piece: String,
    sibling_token_id: u32,
    sibling_piece: String,
    selection_evidence: serde_json::Value,
    actual: CandidateRead,
    sibling: CandidateRead,
    same_touched_training_sources: bool,
    same_replacement: bool,
    same_successor: bool,
}

#[derive(Serialize)]
struct CandidateRead {
    role: &'static str,
    token_ids: Vec<u32>,
    wall_micros: u128,
    before: MemoryRead,
    after: MemoryRead,
    touched: Vec<TouchedFactorRead>,
    imported_training_source_lines: Vec<u32>,
    lower_constituent_instances_departed: usize,
    replacement: ConstituentRead,
    successor_rest_sha256: String,
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
struct ConstituentShape {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    paths: usize,
    path_steps: usize,
    folded_paths: usize,
    transport_terms: usize,
    exposed_pins: usize,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
}

#[derive(Serialize)]
struct ConstituentRead {
    native_sha256: String,
    native_words: Vec<u32>,
    shape: ConstituentShape,
    cells: Vec<CellRead>,
    incidences: Vec<IncidenceRead>,
    pins: Vec<PinRead>,
    boundaries: Vec<BoundaryRead>,
    exposed_pin_ordinals: Vec<u32>,
}

#[derive(Serialize)]
struct CellRead {
    dependency_rank: u32,
    dimension: u32,
    grain: u32,
}

#[derive(Serialize)]
struct IncidenceRead {
    from: u32,
    to: u32,
    kind: &'static str,
    hand: &'static str,
    pin: u32,
}

#[derive(Serialize)]
struct PinRead {
    meeting: FaceRead,
    held: FaceRead,
    held_live: bool,
    interface: Option<InterfaceRead>,
    projected_residual: Option<ChiRead>,
    formed: Option<FormedRead>,
}

#[derive(Serialize)]
struct InterfaceRead {
    namespace: u64,
    local: u64,
    ordered_token_pair: Option<[u32; 2]>,
}

#[derive(Serialize)]
struct FormedRead {
    position: [CogRead; 2],
    chi: ChiRead,
    winding: &'static str,
    deed: &'static str,
}

#[derive(Serialize)]
struct BoundaryRead {
    hand: &'static str,
    transition: &'static str,
    paths: Vec<PathRead>,
}

#[derive(Serialize)]
struct PathRead {
    steps: Vec<PathStepRead>,
    transport: Vec<TransportTermRead>,
    this_way: RungRead,
    that_way: RungRead,
    interior_folded: bool,
}

#[derive(Serialize)]
struct PathStepRead {
    incidence: u32,
    support_axis: u32,
    winding: &'static str,
}

#[derive(Serialize)]
struct TransportTermRead {
    blade_axes: Vec<u32>,
    coefficient: CogRead,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct RungRead {
    mag: u32,
    rank: i32,
    negative: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct CogRead {
    mag: u32,
    rank: RungRead,
    turn: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct FaceRead {
    reach: CogRead,
    aim: CogRead,
    cross: CogRead,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct ChiRead {
    other: CogRead,
    same: CogRead,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros cohered corpus: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let output_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let preflight = match arguments.next() {
        None => false,
        Some(argument) if argument == "--preflight" => true,
        Some(_) => return Err(usage()),
    };
    if arguments.next().is_some() {
        return Err(usage());
    }

    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads: {error}", source_path.display()))?;
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} decodes: {error}", source_path.display()))?;
    validate_source(&source)?;

    let available = std::thread::available_parallelism()
        .map(|extent| extent.get())
        .unwrap_or(1);
    let training_threads = (available / 2).max(1);
    let probe_threads = (available / 3).max(1);
    let received_lines = if preflight {
        PREFLIGHT_LINES.min(source.training_lines.len())
    } else {
        source.training_lines.len()
    };
    let selected_lines = source.training_lines[..received_lines].to_vec();
    let received_occurrences = selected_lines
        .iter()
        .map(|line| line.token_ids.len())
        .sum::<usize>();
    let run_started = Instant::now();

    let forward_lines = selected_lines.clone();
    let reverse_lines = selected_lines;
    let (forward, reversed) = std::thread::scope(|scope| {
        let forward = scope
            .spawn(move || train_body(forward_lines, Direction::Chronological, training_threads));
        let reversed = scope.spawn(move || {
            train_body(
                reverse_lines,
                Direction::ReversedWithinUtterance,
                training_threads,
            )
        });
        let forward = forward
            .join()
            .map_err(|_| "the chronological training worker panicked".to_owned())??;
        let reversed = reversed
            .join()
            .map_err(|_| "the reversed training worker panicked".to_owned())??;
        Ok::<_, String>((forward, reversed))
    })?;

    let (probes, projection) = if preflight {
        (
            Vec::new(),
            Some(projection_read(
                &source,
                received_lines,
                received_occurrences,
                &forward.read,
                &reversed.read,
            )),
        )
    } else {
        let virgin = CorpusWorld::new(probe_threads)?;
        let virgin_rest = virgin.machine.rest_image().map_err(debug)?;
        let virgin_ancestry = virgin.ancestry;
        let source_probes = source.probes.clone();
        let forward_rest = forward.rest.clone();
        let forward_ancestry = forward.ancestry.clone();
        let reversed_rest = reversed.rest.clone();
        let reversed_ancestry = reversed.ancestry.clone();
        let forward_probes = source_probes.clone();
        let reversed_probes = source_probes.clone();
        let virgin_probes = source_probes;
        let probes = std::thread::scope(|scope| {
            let chronological = scope.spawn(move || {
                run_body_probes(
                    "chronological",
                    forward_rest,
                    forward_ancestry,
                    forward_probes,
                    probe_threads,
                )
            });
            let reversed = scope.spawn(move || {
                run_body_probes(
                    "reversed_within_utterance",
                    reversed_rest,
                    reversed_ancestry,
                    reversed_probes,
                    probe_threads,
                )
            });
            let virgin = scope.spawn(move || {
                run_body_probes(
                    "virgin",
                    virgin_rest,
                    virgin_ancestry,
                    virgin_probes,
                    probe_threads,
                )
            });
            Ok::<_, String>(vec![
                chronological
                    .join()
                    .map_err(|_| "the chronological probe worker panicked".to_owned())??,
                reversed
                    .join()
                    .map_err(|_| "the reversed probe worker panicked".to_owned())??,
                virgin
                    .join()
                    .map_err(|_| "the virgin probe worker panicked".to_owned())??,
            ])
        })?;
        (probes, None)
    };

    let wall_micros = run_started.elapsed().as_micros();
    let report = Report {
        schema: REPORT_SCHEMA,
        status: if preflight {
            "mechanical_preflight"
        } else {
            "observed"
        },
        mode: if preflight { "preflight" } else { "scientific" },
        source: SourceRead {
            source_path: source_path.display().to_string(),
            source_sha256: sha256(&source_bytes),
            event_law: source.event_law,
            corpora: SourceCorporaRead {
                training: source.corpora.training,
                validation: source.corpora.validation,
            },
            tokenizer: source.tokenizer,
            controls: source.controls,
            stopping_condition: source.stopping_condition,
        },
        execution: ExecutionRead {
            logical_cpu_parallelism: available,
            concurrent_training_bodies: 2,
            host_threads_per_training_body: training_threads,
            concurrent_probe_bodies: if preflight { 0 } else { 3 },
            host_threads_per_probe_body: probe_threads,
            source_training_lines: source.training_lines.len(),
            received_training_lines: received_lines,
            received_training_token_occurrences_per_body: received_occurrences,
            wall_micros,
            process_peak_rss_kib: process_peak_rss_kib(),
        },
        preflight_projection: projection,
        training: vec![forward.read, reversed.read],
        probes,
    };
    write_new_json(&output_path, &report)?;
    eprintln!(
        "eros cohered corpus: {} · {} lines/body · {} µs · {}",
        report.status,
        received_lines,
        wall_micros,
        output_path.display()
    );
    Ok(())
}

fn train_body(
    lines: Vec<SourceLine>,
    direction: Direction,
    executor_threads: usize,
) -> Result<TrainedBody, String> {
    let mut world = CorpusWorld::new(executor_threads)?;
    let before = memory_read(world.machine.memory());
    let started = Instant::now();
    let mut peak_rss_kib = process_peak_rss_kib();
    let mut events = 0usize;
    let mut token_occurrences = 0usize;
    let mut adjacency_arcs = 0usize;
    let mut new_constituent_events = 0usize;
    let mut recurrent_events = 0usize;
    let mut touched_factor_geometries = 0usize;
    let mut touched_factor_instances = 0usize;
    let mut maximum_replacement_grain = 0u32;
    let mut first_utterances = Vec::new();

    for (event_at, line) in lines.iter().enumerate() {
        let mut token_ids = line.token_ids.clone();
        if matches!(direction, Direction::ReversedWithinUtterance) {
            token_ids.reverse();
        }
        let outcome = world
            .present_tokens(&token_ids, Some(line.line_ordinal))
            .map_err(|error| {
                format!(
                    "{} event {} source line {}: {error}",
                    direction.name(),
                    event_at + 1,
                    line.line_ordinal
                )
            })?;
        let departed = outcome
            .touched
            .iter()
            .map(|factor| factor.instances)
            .sum::<usize>();
        if outcome.touched.is_empty() {
            new_constituent_events += usize::from(outcome.replacement.is_some());
        } else {
            recurrent_events += 1;
        }
        touched_factor_geometries += outcome.touched.len();
        touched_factor_instances += departed;
        if let Some(replacement) = &outcome.replacement {
            maximum_replacement_grain = maximum_replacement_grain.max(replacement.grain());
        }
        events += 1;
        token_occurrences += token_ids.len();
        adjacency_arcs += token_ids.len().saturating_sub(1);
        peak_rss_kib = maximum_option(peak_rss_kib, process_peak_rss_kib());

        if event_at < PREFLIGHT_LINES {
            first_utterances.push(TrainingEventRead {
                event_ordinal: event_at + 1,
                source_line_ordinal: line.line_ordinal,
                source_text: line.text.clone(),
                source_text_sha256: line.text_sha256.clone(),
                token_ids,
                wall_micros: outcome.wall_micros,
                before: outcome.before,
                after: outcome.after,
                touched: outcome.touched,
                lower_constituent_instances_departed: departed,
                replacement: outcome
                    .replacement
                    .as_ref()
                    .map(constituent_read)
                    .transpose()?,
            });
        }
    }
    let rest = world.machine.rest_image().map_err(debug)?;
    let standing_ancestry = standing_ancestry_read(&world.machine, &world.ancestry)?;
    let read = TrainingRead {
        direction: direction.name(),
        events,
        token_occurrences,
        adjacency_arcs,
        new_constituent_events,
        recurrent_events,
        touched_factor_geometries,
        touched_factor_instances,
        maximum_replacement_grain,
        elapsed_micros: started.elapsed().as_micros(),
        peak_rss_kib,
        before,
        after: memory_read(world.machine.memory()),
        rest_sha256: rest_sha256(&rest)?,
        first_utterances,
        standing_ancestry,
    };
    Ok(TrainedBody {
        rest,
        ancestry: world.ancestry,
        read,
    })
}

fn run_body_probes(
    body: &'static str,
    rest: LiveCurrentRestImage,
    ancestry: AncestryState,
    probes: Vec<SourceProbe>,
    executor_threads: usize,
) -> Result<BodyProbeRead, String> {
    let checkpoint_machine = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let checkpoint_memory = memory_read(checkpoint_machine.memory());
    let checkpoint_rest_sha256 = rest_sha256(&rest)?;
    let mut reads = Vec::new();
    for probe in probes {
        let actual = candidate_read(
            "actual",
            rest.clone(),
            ancestry.clone(),
            probe.actual_candidate_token_ids.clone(),
            executor_threads,
        )?;
        let sibling = candidate_read(
            "sibling",
            rest.clone(),
            ancestry.clone(),
            probe.sibling_candidate_token_ids.clone(),
            executor_threads,
        )?;
        let actual_sources = actual.imported_training_source_lines.clone();
        let sibling_sources = sibling.imported_training_source_lines.clone();
        reads.push(ProbeRead {
            species: probe.species,
            validation_line_ordinal: probe.validation.line_ordinal,
            validation_text: probe.validation.text,
            target_index: probe.target_index,
            prefix_token_ids: probe.prefix_token_ids,
            actual_token_id: probe.actual_token_id,
            actual_piece: probe.actual_piece,
            sibling_token_id: probe.sibling_token_id,
            sibling_piece: probe.sibling_piece,
            selection_evidence: probe.selection_evidence,
            same_touched_training_sources: actual_sources == sibling_sources,
            same_replacement: actual.replacement.native_words == sibling.replacement.native_words,
            same_successor: actual.successor_rest_sha256 == sibling.successor_rest_sha256,
            actual,
            sibling,
        });
    }
    Ok(BodyProbeRead {
        body,
        checkpoint_rest_sha256,
        checkpoint_memory,
        probes: reads,
    })
}

fn candidate_read(
    role: &'static str,
    rest: LiveCurrentRestImage,
    ancestry: AncestryState,
    token_ids: Vec<u32>,
    executor_threads: usize,
) -> Result<CandidateRead, String> {
    let mut world = CorpusWorld::from_checkpoint(rest, ancestry, executor_threads)?;
    let outcome = world.present_tokens(&token_ids, None)?;
    let replacement = outcome
        .replacement
        .as_ref()
        .ok_or_else(|| "a probe candidate did not return one regional constituent".to_owned())?;
    let mut imported_training_source_lines = BTreeSet::new();
    for factor in &outcome.touched {
        imported_training_source_lines.extend(factor.training_source_lines.iter().copied());
    }
    let departed = outcome.touched.iter().map(|factor| factor.instances).sum();
    Ok(CandidateRead {
        role,
        token_ids,
        wall_micros: outcome.wall_micros,
        before: outcome.before,
        after: outcome.after,
        touched: outcome.touched,
        imported_training_source_lines: imported_training_source_lines.into_iter().collect(),
        lower_constituent_instances_departed: departed,
        replacement: constituent_read(replacement)?,
        successor_rest_sha256: rest_sha256(&world.machine.rest_image().map_err(debug)?)?,
    })
}

fn projection_read(
    source: &Source,
    received_lines: usize,
    received_occurrences: usize,
    forward: &TrainingRead,
    reversed: &TrainingRead,
) -> ProjectionRead {
    let measured_wall = forward.elapsed_micros.max(reversed.elapsed_micros);
    let projected_full_wall_micros = if received_occurrences == 0 {
        u128::MAX
    } else {
        measured_wall
            .saturating_mul(source.corpora.training.token_occurrences as u128)
            .div_ceil(received_occurrences as u128)
    };
    let measured_peak_rss_kib = maximum_option(forward.peak_rss_kib, reversed.peak_rss_kib);
    let projected_report_floor_bytes = (forward
        .after
        .constituent_paths
        .saturating_add(reversed.after.constituent_paths)
        as u128)
        .saturating_mul(source.corpora.training.complete_lines as u128)
        .div_ceil(received_lines.max(1) as u128)
        .saturating_mul(32);
    let projected_under_one_hour = projected_full_wall_micros <= MAX_ACCEPTED_PROJECTED_MICROS;
    let measured_under_eight_gib =
        measured_peak_rss_kib.is_some_and(|rss| rss <= MAX_ACCEPTED_RSS_KIB);
    ProjectionRead {
        preflight_lines_per_body: received_lines,
        preflight_token_occurrences_per_body: received_occurrences,
        projected_full_wall_micros,
        projected_full_wall_ratio: format!(
            "{} / {}",
            measured_wall.saturating_mul(source.corpora.training.token_occurrences as u128),
            received_occurrences
        ),
        measured_peak_rss_kib,
        projected_report_floor_bytes,
        projected_under_one_hour,
        measured_under_eight_gib,
        resource_boundary_accepts_scientific_run: projected_under_one_hour
            && measured_under_eight_gib,
    }
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA
        || source.observation_id != OBSERVATION_ID
        || source.training_lines.len() != source.corpora.training.complete_lines
        || source
            .training_lines
            .iter()
            .map(|line| line.token_ids.len())
            .sum::<usize>()
            != source.corpora.training.token_occurrences
        || source.probes.len() != 16
        || source.controls != ["chronological", "reversed_within_utterance", "virgin"]
        || source
            .training_lines
            .windows(2)
            .any(|pair| pair[0].line_ordinal >= pair[1].line_ordinal)
        || source
            .training_lines
            .iter()
            .any(|line| line.token_ids.is_empty())
    {
        return Err("the frozen corpus source violates its declared extent or order".to_owned());
    }
    let species = source
        .probes
        .iter()
        .fold(BTreeMap::<&str, usize>::new(), |mut counts, probe| {
            *counts.entry(probe.species.as_str()).or_default() += 1;
            counts
        });
    for expected in [
        "exact_recurrence",
        "single_slot_recombination",
        "same_segment_changed_field",
        "unseen_adjacent_pair",
    ] {
        if species.get(expected).copied() != Some(4) {
            return Err(format!(
                "probe species {expected} does not have extent four"
            ));
        }
    }
    for probe in &source.probes {
        if probe.prefix_token_ids.is_empty()
            || probe.actual_candidate_token_ids
                != [probe.prefix_token_ids.as_slice(), &[probe.actual_token_id]].concat()
            || probe.sibling_candidate_token_ids
                != [probe.prefix_token_ids.as_slice(), &[probe.sibling_token_id]].concat()
            || probe.actual_token_id == probe.sibling_token_id
        {
            return Err("one frozen probe has a degenerate candidate boundary".to_owned());
        }
    }
    Ok(())
}

fn standing_ancestry_read(
    machine: &LiveCurrentMachine,
    ancestry: &AncestryState,
) -> Result<Vec<StandingAncestryRead>, String> {
    let keys = standing_keys(machine)?;
    let counts = count_keys(&keys);
    let mut reads = Vec::new();
    for (ordinal, (constituent, key)) in machine
        .standing()
        .constituents()
        .iter()
        .zip(keys)
        .enumerate()
    {
        reads.push(StandingAncestryRead {
            ordinal,
            native_sha256: words_sha256(&key),
            equal_geometry_instances: counts.get(&key).copied().unwrap_or(0),
            training_source_lines: ancestry.sources_for_key(&key),
            shape: constituent_shape(constituent),
        });
    }
    Ok(reads)
}

fn standing_keys(machine: &LiveCurrentMachine) -> Result<Vec<Vec<u32>>, String> {
    machine
        .standing()
        .constituents()
        .iter()
        .map(|constituent| constituent.native_words().map_err(debug))
        .collect()
}

fn count_keys(keys: &[Vec<u32>]) -> BTreeMap<Vec<u32>, usize> {
    let mut counts = BTreeMap::new();
    for key in keys {
        *counts.entry(key.clone()).or_default() += 1;
    }
    counts
}

fn constituent_read(constituent: &LiveConstituent) -> Result<ConstituentRead, String> {
    let native_words = constituent.native_words().map_err(debug)?;
    let cells = constituent
        .cells()
        .iter()
        .copied()
        .map(|cell| CellRead {
            dependency_rank: cell.dependency_rank(),
            dimension: cell.dimension(),
            grain: cell.grain(),
        })
        .collect();
    let incidences = constituent
        .incidences()
        .iter()
        .copied()
        .map(|incidence| IncidenceRead {
            from: incidence.from(),
            to: incidence.to(),
            kind: incidence_kind_name(incidence.kind()),
            hand: hand_name(incidence.hand()),
            pin: incidence.pin(),
        })
        .collect();
    let pins = constituent
        .pins()
        .iter()
        .map(|pin| {
            let interface = pin.interface().map(|interface| InterfaceRead {
                namespace: interface.namespace(),
                local: interface.local(),
                ordered_token_pair: (interface.namespace() == ADJACENCY_NAMESPACE)
                    .then_some([(interface.local() >> 32) as u32, interface.local() as u32]),
            });
            PinRead {
                meeting: face_read(pin.meeting()),
                held: face_read(pin.held()),
                held_live: pin.held_live(),
                interface,
                projected_residual: pin.comparison().chi().map(chi_read),
                formed: pin.formed().map(|formed| FormedRead {
                    position: [cog_read(formed.position().0), cog_read(formed.position().1)],
                    chi: chi_read(formed.chi()),
                    winding: winding_name(formed.winding()),
                    deed: deed_name(formed.deed()),
                }),
            }
        })
        .collect();
    let mut boundaries = Vec::new();
    for (at, boundary) in constituent.boundaries().iter().enumerate() {
        let transition = constituent
            .boundary_transition(at)
            .ok_or_else(|| "one constituent boundary has no transition".to_owned())?;
        let paths = boundary
            .paths()
            .iter()
            .map(|path| PathRead {
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
                        blade_axes: term
                            .blade()
                            .axes()
                            .iter()
                            .map(|axis| axis.local())
                            .collect(),
                        coefficient: cog_read(term.coefficient()),
                    })
                    .collect(),
                this_way: rung_read(path.this_way()),
                that_way: rung_read(path.that_way()),
                interior_folded: path.interior_folded(),
            })
            .collect();
        boundaries.push(BoundaryRead {
            hand: hand_name(boundary.hand()),
            transition: transition_name(transition),
            paths,
        });
    }
    Ok(ConstituentRead {
        native_sha256: words_sha256(&native_words),
        native_words,
        shape: constituent_shape(constituent),
        cells,
        incidences,
        pins,
        boundaries,
        exposed_pin_ordinals: constituent.exposed().to_vec(),
    })
}

fn constituent_shape(constituent: &LiveConstituent) -> ConstituentShape {
    let mut paths = 0usize;
    let mut path_steps = 0usize;
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
            path_steps += path.steps().len();
            folded_paths += usize::from(path.interior_folded());
            transport_terms += path.transport().terms().len();
        }
    }
    ConstituentShape {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        boundaries: constituent.boundaries().len(),
        paths,
        path_steps,
        folded_paths,
        transport_terms,
        exposed_pins: constituent.exposed().len(),
        open_boundaries,
        ride_boundaries,
        found_boundaries,
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

fn token_atom(token_id: u32) -> Result<RelationAtom, String> {
    let address = u64::from(token_id)
        .checked_add(1)
        .and_then(|value| i64::try_from(value).ok())
        .ok_or_else(|| "one tokenizer address does not fit the relation chart".to_owned())?;
    RelationAtom::new(Cog::lit(address))
        .ok_or_else(|| "the shifted tokenizer address became zero".to_owned())
}

fn pair_capability(left: u32, right: u32) -> u64 {
    (u64::from(left) << 32) | u64::from(right)
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving corpus-world action")
}

fn face_read(face: Face) -> FaceRead {
    FaceRead {
        reach: cog_read(face.arrow.reach),
        aim: cog_read(face.arrow.aim),
        cross: cog_read(face.arrow.cross),
    }
}

fn chi_read(chi: body::soul::Chi) -> ChiRead {
    ChiRead {
        other: cog_read(chi.other),
        same: cog_read(chi.same),
    }
}

fn cog_read(cog: Cog) -> CogRead {
    CogRead {
        mag: cog.mag,
        rank: rung_read(cog.rank),
        turn: cog.turn,
    }
}

fn rung_read(rung: Rung) -> RungRead {
    RungRead {
        mag: rung.mag,
        rank: rung.rank,
        negative: rung.neg,
    }
}

fn hand_name(hand: IncidenceHand) -> &'static str {
    match hand {
        IncidenceHand::Against => "AGAINST",
        IncidenceHand::With => "WITH",
    }
}

fn incidence_kind_name(kind: LiveIncidenceKind) -> &'static str {
    match kind {
        LiveIncidenceKind::Boundary => "BOUNDARY",
        LiveIncidenceKind::Dependency => "DEPENDENCY",
        LiveIncidenceKind::Transport => "TRANSPORT",
        LiveIncidenceKind::RewriteInterface => "REWRITE_INTERFACE",
    }
}

fn transition_name(transition: LiveBoundaryTransition) -> &'static str {
    match transition {
        LiveBoundaryTransition::Open => "OPEN",
        LiveBoundaryTransition::Ride => "RIDE",
        LiveBoundaryTransition::Found => "FOUND",
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

fn rest_sha256(rest: &LiveCurrentRestImage) -> Result<String, String> {
    Ok(sha256(&rest.encode_native_bytes().map_err(debug)?))
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

fn process_peak_rss_kib() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    status.lines().find_map(|line| {
        let value = line.strip_prefix("VmHWM:")?.trim();
        value.strip_suffix("kB")?.trim().parse::<u64>().ok()
    })
}

fn maximum_option(left: Option<u64>, right: Option<u64>) -> Option<u64> {
    match (left, right) {
        (Some(left), Some(right)) => Some(left.max(right)),
        (Some(value), None) | (None, Some(value)) => Some(value),
        (None, None) => None,
    }
}

fn write_new_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value)
        .map_err(|error| format!("report does not encode: {error}"))?;
    bytes.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(path)
        .map_err(|error| format!("{} opens as a new report: {error}", path.display()))?;
    file.write_all(&bytes)
        .map_err(|error| format!("{} writes completely: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", path.display()))
}

fn usage() -> String {
    "usage: eros_cohered_corpus <SOURCE.json> <new-REPORT.json> [--preflight]".to_owned()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
