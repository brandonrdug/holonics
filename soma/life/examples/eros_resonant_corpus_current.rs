//! Full-corpus capacitive conditioning over the production live-current Swing.
//!
//! Each source line is one informant hyperedge over its actual ordered adjacent-token sections.
//! No line-to-line edge, association table, nearest-neighbor query, or scalar score is supplied.
//! The complete offline corpus enters as one co-present configuration, so file enumeration is
//! administrative gauge while each line's own morphology remains ordered.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt::Write as FmtWrite,
    fs::File,
    io::{BufWriter, Write},
    path::{Path, PathBuf},
    time::Instant,
};

use body::num::Cog;
use life::resonance_ecology::{
    ResonanceConstituentRead, ResonanceEcology, ResonanceEcologyRestImage, ResonanceGerm,
    ResonanceOccurrence,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    LiveBoundaryTransition, LiveCurrentMachine, LiveMemory, ParallelHostLiveCurrentExecutor,
    ReceiverFiberIdentity, SparseStandingSurface,
};

const REPORT_SCHEMA: &str = "eros.resonant-corpus-current.report.v1";
const INFORMANT_SCHEMA: u64 = 0x4552_4f53_4c49_4e45;
const DYAD_SCHEMA: u64 = 0x4552_4f53_4459_4144;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    training_lines: Vec<SourceLine>,
}

#[derive(Deserialize)]
struct SourceLine {
    line_ordinal: u32,
    text: String,
    token_ids: Vec<u32>,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    source_schema: String,
    source_observation_id: String,
    source_sha256: String,
    source_lines_available: usize,
    source_lines_received: usize,
    token_occurrences: usize,
    adjacent_sections: usize,
    distinct_germs: usize,
    recurrent_germs: usize,
    configuration_wall_millis: u128,
    reverse_configuration_wall_millis: u128,
    delivery_permutation_exact: bool,
    receptor_population: usize,
    rest_bytes: usize,
    rest_sha256: String,
    remount_exact: bool,
    machine: MemoryRead,
    support: SupportRead,
    training_radiation: TrainingRadiationRead,
    probe: ProbeRead,
    complete_recurrence: CompleteRecurrenceRead,
    phase_obstruction: PhaseObstructionRead,
    resonant_component_tsv: String,
}

#[derive(Clone, Copy, Serialize)]
struct MemoryRead {
    standing_cells: usize,
    standing_constituents: usize,
    constituent_cells: usize,
    constituent_incidences: usize,
    constituent_pins: usize,
    constituent_paths: usize,
    constituent_transport_terms: usize,
}

#[derive(Default, Serialize)]
struct SupportRead {
    active_factors: usize,
    dag_nodes: usize,
    cause_edges: usize,
    direct_boundary_entries: usize,
    resolved_active_boundary_entries: usize,
    largest_factor_population: usize,
    largest_node_population: usize,
}

#[derive(Serialize)]
struct TrainingRadiationRead {
    regional_population: usize,
    regions_touching_prior_standing: usize,
    maximum_front_depth: u32,
}

#[derive(Serialize)]
struct ProbeRead {
    seed_left: u32,
    seed_right: u32,
    seed_line_ordinal: u32,
    seed_line_text: String,
    direct_informants: usize,
    returned_informants: usize,
    indirectly_recruited_informants: usize,
    unreached_informants: usize,
    returned_germs: usize,
    touched_standing_constituents: usize,
    front_depth: u32,
    open_pins: usize,
    riding_pins: usize,
    transitions: TransitionRead,
    constituent_sha256: String,
    bounded_oracle_component_exact: bool,
    causal_degree_histogram: BTreeMap<usize, usize>,
    maximum_causal_degree: usize,
}

#[derive(Serialize)]
struct CompleteRecurrenceRead {
    line_ordinal: u32,
    returned_informants: usize,
    returned_germs: usize,
    touched_standing_constituents: usize,
    front_depth: u32,
    open_pins: usize,
    riding_pins: usize,
    transitions: TransitionRead,
}

#[derive(Serialize)]
struct PhaseObstructionRead {
    open_returned: bool,
    open_pins: usize,
    riding_pins: usize,
    touched_standing_constituents: usize,
    front_depth: u32,
    transitions: TransitionRead,
    constituent_sha256: String,
    differs_from_probe: bool,
}

#[derive(Default, Serialize)]
struct TransitionRead {
    open: usize,
    ride: usize,
    found: usize,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros resonant corpus current: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let report_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let source_event_limit = arguments
        .next()
        .map(|value| {
            value
                .to_string_lossy()
                .parse::<usize>()
                .map_err(|_| usage())
        })
        .transpose()?;
    if arguments.next().is_some() || source_event_limit.is_some_and(|limit| limit == 0) {
        return Err(usage());
    }

    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads: {error}", source_path.display()))?;
    let source_sha256 = sha256(&source_bytes);
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} decodes: {error}", source_path.display()))?;
    let source_lines_available = source.training_lines.len();
    let source_lines_received = source_event_limit
        .unwrap_or(source_lines_available)
        .min(source_lines_available);
    if source_lines_received == 0 {
        return Err("the source has no training lines".to_owned());
    }
    let lines = &source.training_lines[..source_lines_received];

    let mut token_occurrences = 0usize;
    let mut adjacent_sections = 0usize;
    let mut germ_lines = BTreeMap::<(u32, u32), BTreeSet<usize>>::new();
    let mut line_germs = Vec::new();
    let mut informant_lines = BTreeMap::<ReceiverFiberIdentity, usize>::new();
    let mut occurrences = Vec::new();
    for (line_at, line) in lines.iter().enumerate() {
        if line.token_ids.len() < 2 {
            continue;
        }
        token_occurrences = token_occurrences
            .checked_add(line.token_ids.len())
            .ok_or_else(|| "token occurrence census overflowed".to_owned())?;
        adjacent_sections = adjacent_sections
            .checked_add(line.token_ids.len() - 1)
            .ok_or_else(|| "adjacent section census overflowed".to_owned())?;

        let informant = informant_fiber(line)?;
        if informant_lines.insert(informant.clone(), line_at).is_some() {
            return Err(format!(
                "line {} duplicates a complete source informant identity",
                line.line_ordinal
            ));
        }
        let mut seen = BTreeSet::new();
        let mut germs = Vec::new();
        for pair in line.token_ids.windows(2) {
            let dyad = (pair[0], pair[1]);
            germ_lines.entry(dyad).or_default().insert(line_at);
            if seen.insert(dyad) {
                germs.push(germ(dyad, false)?);
            }
        }
        line_germs.push(seen);
        occurrences.push(
            ResonanceOccurrence::informant(
                informant,
                u64::from(line.line_ordinal)
                    .checked_mul(2)
                    .ok_or_else(|| "source chronology overflowed".to_owned())?,
                germs,
            )
            .map_err(debug)?,
        );
    }
    if occurrences.len() != lines.len() {
        return Err(
            "this instrument requires every selected source line to contain a causal dyad"
                .to_owned(),
        );
    }

    let threads = std::thread::available_parallelism()
        .map(|extent| extent.get())
        .unwrap_or(1);
    let mut executor = ParallelHostLiveCurrentExecutor::new(threads);
    let mut ecology = ResonanceEcology::new(LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(8).map_err(debug)?,
    ));
    let started = Instant::now();
    let training = ecology
        .receive_configuration_with(&occurrences, action()?, &mut executor)
        .map_err(debug)?;
    let configuration_wall_millis = started.elapsed().as_millis();
    let training_radiation = TrainingRadiationRead {
        regional_population: training.regional().len(),
        regions_touching_prior_standing: training
            .regional()
            .iter()
            .filter(|regional| regional.touched_constituents() > 0)
            .count(),
        maximum_front_depth: training
            .regional()
            .iter()
            .map(|regional| regional.front_depth())
            .max()
            .unwrap_or(0),
    };
    let rest = ecology.rest_image().map_err(debug)?;
    let rest_bytes = rest.encode_native_bytes().map_err(debug)?;
    let rest_sha256 = sha256(&rest_bytes);
    let decoded_rest = ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).map_err(debug)?;
    let remounted = ResonanceEcology::from_rest_image(decoded_rest).map_err(debug)?;
    let remount_exact = remounted
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?
        == rest_bytes;

    let mut reverse_executor = ParallelHostLiveCurrentExecutor::new(threads);
    let mut reverse = ResonanceEcology::new(LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(8).map_err(debug)?,
    ));
    let reversed = occurrences.iter().rev().cloned().collect::<Vec<_>>();
    let reverse_started = Instant::now();
    reverse
        .receive_configuration_with(&reversed, action()?, &mut reverse_executor)
        .map_err(debug)?;
    let reverse_configuration_wall_millis = reverse_started.elapsed().as_millis();
    let delivery_permutation_exact = reverse.machine().standing() == ecology.machine().standing()
        && reverse.rest_image().map_err(debug)? == rest;

    let seed = select_seed(lines, &germ_lines)?;
    let direct_informants = germ_lines
        .get(&seed)
        .map(BTreeSet::len)
        .ok_or_else(|| "selected seed departed from the source chart".to_owned())?;
    let seed_owner = germ_lines
        .get(&seed)
        .and_then(|owners| owners.iter().next().copied())
        .ok_or_else(|| "selected seed has no source informant".to_owned())?;
    let mut probing = ResonanceEcology::from_rest_image(
        ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).map_err(debug)?,
    )
    .map_err(debug)?;
    let probe_return = probing
        .receive(
            &ResonanceOccurrence::probe(u64::MAX - 2, vec![germ(seed, false)?]).map_err(debug)?,
            action()?,
        )
        .map_err(debug)?;
    let probe_read = probe_return.read();
    let returned_lines = returned_line_indices(probe_read, &informant_lines)?;
    let causal_degrees = causal_degrees(seed, &line_germs, &germ_lines)?;
    let bounded_oracle_component_exact =
        causal_degrees.keys().copied().collect::<BTreeSet<_>>() == returned_lines;
    let mut causal_degree_histogram = BTreeMap::new();
    for degree in causal_degrees.values() {
        *causal_degree_histogram.entry(*degree).or_insert(0usize) += 1;
    }
    let maximum_causal_degree = causal_degrees.values().copied().max().unwrap_or(0);
    let indirectly_recruited_informants = returned_lines.len().saturating_sub(direct_informants);
    let probe_constituent_sha256 = constituent_sha256(probe_return.regional().constituent())?;
    let probe = ProbeRead {
        seed_left: seed.0,
        seed_right: seed.1,
        seed_line_ordinal: lines[seed_owner].line_ordinal,
        seed_line_text: lines[seed_owner].text.clone(),
        direct_informants,
        returned_informants: returned_lines.len(),
        indirectly_recruited_informants,
        unreached_informants: lines.len().saturating_sub(returned_lines.len()),
        returned_germs: probe_read.germs().len(),
        touched_standing_constituents: probe_return.regional().touched_constituents(),
        front_depth: probe_return.regional().front_depth(),
        open_pins: probe_read.open_pins(),
        riding_pins: probe_read.riding_pins(),
        transitions: transition_read(probe_return.regional().support_transitions()),
        constituent_sha256: probe_constituent_sha256.clone(),
        bounded_oracle_component_exact,
        causal_degree_histogram,
        maximum_causal_degree,
    };

    let mut recurring = ResonanceEcology::from_rest_image(
        ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).map_err(debug)?,
    )
    .map_err(debug)?;
    let recurrence_occurrence =
        occurrence_from_line(&lines[seed_owner], u64::MAX - 4).map_err(debug)?;
    let recurrence_return = recurring
        .receive(&recurrence_occurrence, action()?)
        .map_err(debug)?;
    let recurrence_read = recurrence_return.read();
    let complete_recurrence = CompleteRecurrenceRead {
        line_ordinal: lines[seed_owner].line_ordinal,
        returned_informants: recurrence_read.informants().len(),
        returned_germs: recurrence_read.germs().len(),
        touched_standing_constituents: recurrence_return.regional().touched_constituents(),
        front_depth: recurrence_return.regional().front_depth(),
        open_pins: recurrence_read.open_pins(),
        riding_pins: recurrence_read.riding_pins(),
        transitions: transition_read(recurrence_return.regional().support_transitions()),
    };

    let mut obstructed = ResonanceEcology::from_rest_image(
        ResonanceEcologyRestImage::from_native_bytes(&rest_bytes).map_err(debug)?,
    )
    .map_err(debug)?;
    let obstruction_return = obstructed
        .receive(
            &ResonanceOccurrence::probe(u64::MAX - 2, vec![germ(seed, true)?]).map_err(debug)?,
            action()?,
        )
        .map_err(debug)?;
    let obstruction_read = obstruction_return.read();
    let obstruction_constituent_sha256 =
        constituent_sha256(obstruction_return.regional().constituent())?;
    let phase_obstruction = PhaseObstructionRead {
        open_returned: obstruction_return
            .regional()
            .support_transitions()
            .iter()
            .flatten()
            .any(|transition| *transition == LiveBoundaryTransition::Open),
        open_pins: obstruction_read.open_pins(),
        riding_pins: obstruction_read.riding_pins(),
        touched_standing_constituents: obstruction_return.regional().touched_constituents(),
        front_depth: obstruction_return.regional().front_depth(),
        transitions: transition_read(obstruction_return.regional().support_transitions()),
        differs_from_probe: obstruction_constituent_sha256 != probe_constituent_sha256,
        constituent_sha256: obstruction_constituent_sha256,
    };

    let report_parent = report_path
        .parent()
        .ok_or_else(|| format!("{} has no parent", report_path.display()))?;
    std::fs::create_dir_all(report_parent)
        .map_err(|error| format!("{} creates: {error}", report_parent.display()))?;
    let component_path = report_parent.join("RESONANT_COMPONENT.tsv");
    write_component(&component_path, lines, &returned_lines, &causal_degrees)?;

    let report = Report {
        schema: REPORT_SCHEMA,
        status: if source_lines_received == source_lines_available {
            "full-corpus-observed"
        } else {
            "bounded-physical-preflight"
        },
        source_schema: source.schema,
        source_observation_id: source.observation_id,
        source_sha256,
        source_lines_available,
        source_lines_received,
        token_occurrences,
        adjacent_sections,
        distinct_germs: germ_lines.len(),
        recurrent_germs: germ_lines.values().filter(|lines| lines.len() > 1).count(),
        configuration_wall_millis,
        reverse_configuration_wall_millis,
        delivery_permutation_exact,
        receptor_population: rest.receptor_count(),
        rest_bytes: rest_bytes.len(),
        rest_sha256,
        remount_exact,
        machine: memory(ecology.machine().memory()),
        support: support_read(ecology.machine())?,
        training_radiation,
        probe,
        complete_recurrence,
        phase_obstruction,
        resonant_component_tsv: component_path.display().to_string(),
    };
    write_json(&report_path, &report)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&report).map_err(|error| error.to_string())?
    );
    Ok(())
}

fn informant_fiber(line: &SourceLine) -> Result<ReceiverFiberIdentity, String> {
    let count = u64::try_from(line.token_ids.len())
        .map_err(|_| "line token extent does not fit the exact carrier".to_owned())?;
    let mut words = Vec::with_capacity(4 + line.token_ids.len());
    words.extend([line.line_ordinal, 0, count as u32, (count >> 32) as u32]);
    words.extend_from_slice(&line.token_ids);
    Ok(ReceiverFiberIdentity::new(INFORMANT_SCHEMA, words))
}

fn occurrence_from_line(
    line: &SourceLine,
    source_order: u64,
) -> Result<ResonanceOccurrence, String> {
    let mut seen = BTreeSet::new();
    let germs = line
        .token_ids
        .windows(2)
        .filter_map(|pair| {
            let dyad = (pair[0], pair[1]);
            seen.insert(dyad).then_some(dyad)
        })
        .map(|dyad| germ(dyad, false))
        .collect::<Result<Vec<_>, _>>()?;
    ResonanceOccurrence::informant(informant_fiber(line)?, source_order, germs).map_err(debug)
}

fn germ(dyad: (u32, u32), obstructed: bool) -> Result<ResonanceGerm, String> {
    let material = i64::from(dyad.1)
        .checked_add(1)
        .ok_or_else(|| "token material overflowed".to_owned())?;
    let material = if obstructed {
        material
            .checked_add(1)
            .ok_or_else(|| "obstructed token material overflowed".to_owned())?
    } else {
        material
    };
    let phase = RelationAtom::new(Cog::lit(material))
        .ok_or_else(|| "zero token material cannot enter the current".to_owned())?;
    Ok(ResonanceGerm::new(
        ReceiverFiberIdentity::new(DYAD_SCHEMA, [dyad.0, dyad.1]),
        phase,
    ))
}

fn select_seed(
    lines: &[SourceLine],
    germ_lines: &BTreeMap<(u32, u32), BTreeSet<usize>>,
) -> Result<(u32, u32), String> {
    for (line_at, line) in lines.iter().enumerate() {
        let dyads = line
            .token_ids
            .windows(2)
            .map(|pair| (pair[0], pair[1]))
            .collect::<BTreeSet<_>>();
        let has_recurring_bridge = dyads
            .iter()
            .any(|dyad| germ_lines.get(dyad).is_some_and(|owners| owners.len() > 1));
        if !has_recurring_bridge {
            continue;
        }
        if let Some(seed) = dyads.into_iter().find(|dyad| {
            germ_lines
                .get(dyad)
                .is_some_and(|owners| owners.len() == 1 && owners.contains(&line_at))
        }) {
            return Ok(seed);
        }
    }
    germ_lines
        .iter()
        .find_map(|(dyad, owners)| (owners.len() == 1).then_some(*dyad))
        .ok_or_else(|| "the selected corpus has no receiver-local unique germ".to_owned())
}

fn returned_line_indices(
    read: &ResonanceConstituentRead,
    informant_lines: &BTreeMap<ReceiverFiberIdentity, usize>,
) -> Result<BTreeSet<usize>, String> {
    read.informants()
        .iter()
        .map(|identity| {
            informant_lines
                .get(identity)
                .copied()
                .ok_or_else(|| "returned an informant outside the supplied corpus".to_owned())
        })
        .collect()
}

fn causal_degrees(
    seed: (u32, u32),
    line_germs: &[BTreeSet<(u32, u32)>],
    germ_lines: &BTreeMap<(u32, u32), BTreeSet<usize>>,
) -> Result<BTreeMap<usize, usize>, String> {
    let mut degrees = BTreeMap::new();
    let mut queue = VecDeque::new();
    for line in germ_lines
        .get(&seed)
        .ok_or_else(|| "the seed is absent from the source incidence".to_owned())?
    {
        degrees.insert(*line, 0usize);
        queue.push_back(*line);
    }
    while let Some(line_at) = queue.pop_front() {
        let next_degree = degrees[&line_at]
            .checked_add(1)
            .ok_or_else(|| "causal degree overflowed".to_owned())?;
        for germ in line_germs
            .get(line_at)
            .ok_or_else(|| "line-germ incidence is incomplete".to_owned())?
        {
            for reached in germ_lines
                .get(germ)
                .ok_or_else(|| "germ-line incidence is incomplete".to_owned())?
            {
                if let std::collections::btree_map::Entry::Vacant(entry) = degrees.entry(*reached) {
                    entry.insert(next_degree);
                    queue.push_back(*reached);
                }
            }
        }
    }
    Ok(degrees)
}

fn support_read(machine: &LiveCurrentMachine) -> Result<SupportRead, String> {
    let mut read = SupportRead::default();
    for constituent in machine.standing().constituents() {
        let support = constituent.support_family();
        read.active_factors = read
            .active_factors
            .checked_add(support.factor_count())
            .ok_or_else(|| "support factor census overflowed".to_owned())?;
        read.dag_nodes = read
            .dag_nodes
            .checked_add(support.node_count())
            .ok_or_else(|| "support node census overflowed".to_owned())?;
        read.cause_edges = read
            .cause_edges
            .checked_add(support.cause_edges())
            .ok_or_else(|| "support cause census overflowed".to_owned())?;
        read.direct_boundary_entries = read
            .direct_boundary_entries
            .checked_add(support.direct_boundary_entries())
            .ok_or_else(|| "support boundary census overflowed".to_owned())?;
        read.resolved_active_boundary_entries = read
            .resolved_active_boundary_entries
            .checked_add(support.resolved_active_boundary_entries().map_err(debug)?)
            .ok_or_else(|| "resolved support census overflowed".to_owned())?;
        read.largest_factor_population = read.largest_factor_population.max(support.factor_count());
        read.largest_node_population = read.largest_node_population.max(support.node_count());
    }
    Ok(read)
}

fn memory(memory: LiveMemory) -> MemoryRead {
    MemoryRead {
        standing_cells: memory.standing_cells,
        standing_constituents: memory.standing_constituents,
        constituent_cells: memory.constituent_cells,
        constituent_incidences: memory.constituent_incidences,
        constituent_pins: memory.constituent_pins,
        constituent_paths: memory.constituent_paths,
        constituent_transport_terms: memory.constituent_transport_terms,
    }
}

fn transition_read(transitions: &[Vec<LiveBoundaryTransition>]) -> TransitionRead {
    let mut read = TransitionRead::default();
    for transition in transitions.iter().flatten() {
        match transition {
            LiveBoundaryTransition::Open => read.open += 1,
            LiveBoundaryTransition::Ride => read.ride += 1,
            LiveBoundaryTransition::Found => read.found += 1,
        }
    }
    read
}

fn constituent_sha256(constituent: &soma_membrane::LiveConstituent) -> Result<String, String> {
    let mut digest = Sha256::new();
    for word in constituent.native_words().map_err(debug)? {
        digest.update(word.to_le_bytes());
    }
    Ok(hex_digest(digest.finalize().as_slice()))
}

fn write_component(
    path: &Path,
    lines: &[SourceLine],
    returned: &BTreeSet<usize>,
    degrees: &BTreeMap<usize, usize>,
) -> Result<(), String> {
    let file =
        File::create(path).map_err(|error| format!("{} creates: {error}", path.display()))?;
    let mut writer = BufWriter::new(file);
    writeln!(writer, "causal_degree\tline_ordinal\ttext")
        .map_err(|error| format!("{} writes: {error}", path.display()))?;
    for line_at in returned {
        let line = lines
            .get(*line_at)
            .ok_or_else(|| "returned line address exceeds the source".to_owned())?;
        let degree = degrees
            .get(line_at)
            .ok_or_else(|| "returned line is absent from the bounded oracle".to_owned())?;
        writeln!(
            writer,
            "{}\t{}\t{}",
            degree,
            line.line_ordinal,
            line.text.replace('\t', " ")
        )
        .map_err(|error| format!("{} writes: {error}", path.display()))?;
    }
    writer
        .flush()
        .map_err(|error| format!("{} flushes: {error}", path.display()))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    std::fs::write(path, bytes).map_err(|error| format!("{} writes: {error}", path.display()))
}

fn action() -> Result<ActionCurrent, String> {
    ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current refuses".to_owned())
}

fn sha256(bytes: &[u8]) -> String {
    hex_digest(Sha256::digest(bytes).as_slice())
}

fn hex_digest(bytes: &[u8]) -> String {
    bytes
        .iter()
        .fold(String::with_capacity(64), |mut digest, byte| {
            write!(&mut digest, "{byte:02x}").expect("a String write cannot fail");
            digest
        })
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

fn usage() -> String {
    "usage: eros_resonant_corpus_current <SOURCE.json> <REPORT.json> [source-line-limit]".to_owned()
}
