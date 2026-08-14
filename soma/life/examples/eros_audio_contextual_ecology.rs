#[allow(dead_code)]
#[path = "audio_inscription/exact_pcm.rs"]
mod exact_pcm;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use body::incidence::IncidenceHand;
use body::manifold::FeltDeed;
use body::num::Cog;
use exact_pcm::{ExactPathChart, PcmWave};
use life::current_world::{
    present_native_event_with_regional, NativeEventCurrent, NativeRegionalArc,
    NativeRegionalRelation, NativeRelationOrgan,
};
use life::form_mouth::deposit_form_or_message;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;
use soma_membrane::{
    CurrentBoundaryPort, InterfaceCapability, LiveBoundaryTransition, LiveConstituent,
    LiveCurrentMachine, LiveMemory, ParallelHostLiveCurrentExecutor, RegionalArcRadiation,
    RegionalSupportSection, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_audio_contextual_ecology/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_audio_contextual_ecology";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";

const SOURCE_SCHEMA: &str = "eros.audio-contextual-ecology.source.v1";
const REPORT_SCHEMA: &str = "eros.audio-contextual-ecology.report.v1";
const OBSERVATION_ID: &str = "eros-audio-contextual-ecology-01";
const HOST_THREADS: usize = 8;
const EVENT_LIMIT: Duration = Duration::from_secs(30);
const RUN_LIMIT: Duration = Duration::from_secs(180);

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    question: String,
    fixed_law: Value,
    instrument: Value,
    components: Vec<SourceComponent>,
    training: Vec<SourceTraining>,
    probes: Vec<SourceProbe>,
    stopping_condition: String,
}

#[derive(Deserialize)]
struct SourceComponent {
    id: String,
    text: String,
    voice: String,
    path: PathBuf,
    sha256: String,
    sample_rate: u32,
    samples: usize,
    blocks: Vec<SourceBlock>,
}

#[derive(Clone, Copy, Deserialize)]
struct SourceBlock {
    ordinal: usize,
    start: usize,
    end: usize,
    sum: i64,
}

#[derive(Deserialize)]
struct SourceTraining {
    id: String,
    components: Vec<SourceSpan>,
    path: PathBuf,
    sha256: String,
    samples: usize,
    sample_rate: u32,
    inherited: SourceInherited,
}

#[derive(Deserialize)]
struct SourceSpan {
    role: usize,
    component: String,
    start: usize,
    end: usize,
}

#[derive(Deserialize)]
struct SourceInherited {
    token_ids: Vec<u32>,
    token_pieces: Vec<String>,
    text: String,
    valid_feature_frames: usize,
    valid_encoder_frames: usize,
    attention: SourceAttention,
}

#[derive(Deserialize)]
struct SourceAttention {
    layer: usize,
    layers: usize,
    heads: usize,
    tokens: usize,
    frames: usize,
    dtype: String,
    rows: Vec<SourceAttentionRow>,
    frame_map: Vec<SourceFrameMap>,
}

#[derive(Deserialize)]
struct SourceAttentionRow {
    token_ordinal: usize,
    head: usize,
    words: Vec<u32>,
}

#[derive(Clone, Deserialize)]
struct SourceFrameMap {
    frame: usize,
    role: usize,
    component: String,
    component_block: usize,
}

#[derive(Deserialize)]
struct SourceProbe {
    id: String,
    core: Vec<String>,
    extras: Vec<String>,
    expected_ecology: Option<String>,
    assembled_components: Vec<SourceSpan>,
    path: PathBuf,
    sha256: String,
    samples: usize,
    sample_rate: u32,
    always_parent_control: SourceParentControl,
}

#[derive(Deserialize, Serialize)]
struct SourceParentControl {
    token_ids: Vec<u32>,
    token_pieces: Vec<String>,
    text: String,
    valid_feature_frames: usize,
    valid_encoder_frames: usize,
}

struct ValidatedComponent<'a> {
    source: &'a SourceComponent,
    samples: Vec<i16>,
}

struct ValidatedSource<'a> {
    components: BTreeMap<&'a str, ValidatedComponent<'a>>,
    source_bytes: usize,
    retained_attention_words: usize,
    retained_token_words: usize,
}

struct EventBundle {
    charts: Vec<ExactPathChart>,
    arcs: Vec<NativeRegionalArc>,
    section_slots: Vec<Vec<u32>>,
    receiver: usize,
    semantic_words: usize,
}

#[derive(Clone)]
struct EcologyInterfaces {
    tokens: BTreeSet<InterfaceCapability>,
    attention: BTreeSet<InterfaceCapability>,
    gate: InterfaceCapability,
}

impl EcologyInterfaces {
    fn complete_in(&self, constituent: &LiveConstituent) -> bool {
        let exposed = exposed_interfaces(constituent);
        self.tokens.is_subset(&exposed) && self.attention.is_subset(&exposed)
    }

    fn read(&self, constituent: &LiveConstituent) -> EcologyRead {
        let exposed = exposed_interfaces(constituent);
        let token_words = self.tokens.intersection(&exposed).count();
        let attention_words = self.attention.intersection(&exposed).count();
        let gate = interface_transition_read(constituent, self.gate.clone());
        EcologyRead {
            token_words,
            token_words_expected: self.tokens.len(),
            attention_words,
            attention_words_expected: self.attention.len(),
            data_complete: token_words == self.tokens.len()
                && attention_words == self.attention.len(),
            gate_open: gate.open,
            gate_ride: gate.ride,
            gate_found: gate.found,
            conducted: gate.ride + gate.found > 0,
        }
    }
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
struct ShapeRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    paths: usize,
    exposed_pins: usize,
    support_sections: usize,
    support_extents: Vec<usize>,
    open_boundaries: usize,
    ride_boundaries: usize,
    found_boundaries: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
struct ContactRead {
    open: usize,
    ride: usize,
    found_this: usize,
    found_that: usize,
    dark: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct InterfaceTransitionRead {
    open: usize,
    ride: usize,
    found: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct EventRead {
    id: String,
    role: String,
    currents: usize,
    arcs: usize,
    support_sections: usize,
    semantic_words: usize,
    contacts: ContactRead,
    before: MemoryRead,
    after: MemoryRead,
    emitted: ShapeRead,
    elapsed_microseconds: u128,
}

struct EventOutcome {
    read: EventRead,
    constituent: LiveConstituent,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
struct EcologyRead {
    token_words: usize,
    token_words_expected: usize,
    attention_words: usize,
    attention_words_expected: usize,
    data_complete: bool,
    gate_open: usize,
    gate_ride: usize,
    gate_found: usize,
    conducted: bool,
}

#[derive(Serialize)]
struct TrainingRead {
    id: String,
    text: String,
    token_ids: Vec<u32>,
    retained_layer: usize,
    retained_heads: usize,
    retained_tokens: usize,
    retained_frames: usize,
    acoustic: EventRead,
    returned_consequence: EventRead,
    predecessor_departed: bool,
    complete_ecology_exposed: bool,
}

#[derive(Serialize)]
struct ProbeRead {
    id: String,
    expected_ecology: Option<String>,
    observed_conducted_ecologies: Vec<String>,
    ecology_reads: BTreeMap<String, EcologyRead>,
    always_parent_control: SourceParentControl,
    event: EventRead,
}

struct RunBudget {
    started: Instant,
}

impl RunBudget {
    fn new() -> Self {
        Self {
            started: Instant::now(),
        }
    }

    fn require_open(&self) -> Result<(), String> {
        if self.started.elapsed() > RUN_LIMIT {
            Err("the bounded audio ecology run exceeded three minutes".to_owned())
        } else {
            Ok(())
        }
    }
}

fn main() {
    if let Err(error) = run_main() {
        eprintln!("eros audio contextual ecology: {error}");
        std::process::exit(1);
    }
}

fn run_main() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let output_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads completely: {error}", source_path.display()))?;
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} decodes: {error}", source_path.display()))?;
    let report = run(&source, source_bytes.len())?;
    write_new_json(&output_path, &report)?;
    eprintln!(
        "eros audio contextual ecology: accepted · {} bytes · {}",
        source_bytes.len(),
        output_path.display()
    );
    Ok(())
}

fn usage() -> String {
    "usage: eros_audio_contextual_ecology <SOURCE.json> <new-report.json>".to_owned()
}

fn run(source: &Source, source_bytes: usize) -> Result<Value, String> {
    let budget = RunBudget::new();
    let validated = validate_source(source, source_bytes)?;
    let ecology_interfaces = source
        .training
        .iter()
        .map(|training| {
            Ok((
                training.id.clone(),
                ecology_interfaces(training, &validated)?,
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;

    let mut machine =
        LiveCurrentMachine::new(SparseStandingSurface::empty_rank(10).map_err(debug)?);
    let mut training_reads = Vec::new();
    for training in &source.training {
        budget.require_open()?;
        let before_acoustic = machine.memory().standing_constituents;
        let acoustic_bundle = acoustic_bundle(
            training
                .components
                .iter()
                .map(|span| span.component.as_str())
                .collect::<Vec<_>>()
                .as_slice(),
            "acoustic",
            &validated,
            &[],
        )?;
        let acoustic = execute(
            &budget,
            &mut machine,
            &format!("{}-acoustic", training.id),
            "open-acoustic-support",
            acoustic_bundle,
        )?;
        if machine.memory().standing_constituents != before_acoustic + 1 {
            return Err(format!(
                "{} acoustic seed did not stand as one new OPEN support body",
                training.id
            ));
        }

        let before_return = machine.memory().standing_constituents;
        let consequence_bundle = consequence_bundle(training, &validated)?;
        let returned = execute(
            &budget,
            &mut machine,
            &format!("{}-return", training.id),
            "whisper-return-and-contextual-successor",
            consequence_bundle,
        )?;
        let interfaces = ecology_interfaces
            .get(&training.id)
            .ok_or_else(|| format!("{} has no expected ecology interface set", training.id))?;
        let complete = interfaces.complete_in(&returned.constituent);
        let predecessor_departed = machine.memory().standing_constituents <= before_return
            && machine
                .standing()
                .constituents()
                .iter()
                .any(|constituent| constituent == &returned.constituent)
            && machine
                .standing()
                .constituents()
                .iter()
                .all(|constituent| constituent != &acoustic.constituent);
        if !complete || !predecessor_departed {
            return Err(format!(
                "{} consequence did not replace its acoustic predecessor with one complete ecology",
                training.id
            ));
        }
        training_reads.push(TrainingRead {
            id: training.id.clone(),
            text: training.inherited.text.clone(),
            token_ids: training.inherited.token_ids.clone(),
            retained_layer: training.inherited.attention.layer,
            retained_heads: training.inherited.attention.heads,
            retained_tokens: training.inherited.attention.tokens,
            retained_frames: training.inherited.attention.frames,
            acoustic: acoustic.read,
            returned_consequence: returned.read,
            predecessor_departed,
            complete_ecology_exposed: complete,
        });
    }

    if machine.memory().standing_constituents != 1 || machine.memory().live_lineages != 0 {
        return Err(
            "the cultivated world did not rest as one integrated, departed contextual ecology"
                .to_owned(),
        );
    }
    let rest = machine.rest_image().map_err(debug)?;
    let rest_octets = rest.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. This site reported only the
    // octet COUNT and dropped the octets; the count in the report is unchanged and the octets now
    // reach `holon-plate deposit --from ERST:`.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let remounted = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == rest
        && remounted.standing() == machine.standing();
    if !rest_exact {
        return Err("the contextual ecology changed across exact rest/remount".to_owned());
    }
    machine = remounted;

    let mut probes = Vec::new();
    for probe in &source.probes {
        budget.require_open()?;
        let mut branch = LiveCurrentMachine::from_rest_image(machine.rest_image().map_err(debug)?)
            .map_err(debug)?;
        let bundle = acoustic_bundle(
            probe
                .core
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>()
                .as_slice(),
            "ecology",
            &validated,
            probe
                .extras
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>()
                .as_slice(),
        )?;
        let outcome = execute(
            &budget,
            &mut branch,
            &probe.id,
            "source-absent-audio-probe",
            bundle,
        )?;
        let ecology_reads = ecology_interfaces
            .iter()
            .map(|(id, interfaces)| (id.clone(), interfaces.read(&outcome.constituent)))
            .collect::<BTreeMap<_, _>>();
        let observed_conducted_ecologies = ecology_reads
            .iter()
            .filter_map(|(id, read)| read.conducted.then_some(id.clone()))
            .collect::<Vec<_>>();
        probes.push(ProbeRead {
            id: probe.id.clone(),
            expected_ecology: probe.expected_ecology.clone(),
            observed_conducted_ecologies,
            ecology_reads,
            always_parent_control: SourceParentControl {
                token_ids: probe.always_parent_control.token_ids.clone(),
                token_pieces: probe.always_parent_control.token_pieces.clone(),
                text: probe.always_parent_control.text.clone(),
                valid_feature_frames: probe.always_parent_control.valid_feature_frames,
                valid_encoder_frames: probe.always_parent_control.valid_encoder_frames,
            },
            event: outcome.read,
        });
    }

    let quantity = source
        .training
        .iter()
        .find(|training| training.id == "quantity")
        .ok_or_else(|| "the fixed quantity training row is absent".to_owned())?;
    let quantity_core = quantity
        .components
        .iter()
        .map(|span| span.component.as_str())
        .collect::<Vec<_>>();
    let mut no_return_machine =
        LiveCurrentMachine::new(SparseStandingSurface::empty_rank(10).map_err(debug)?);
    let no_return_seed = execute(
        &budget,
        &mut no_return_machine,
        "no-return-seed",
        "acoustic-only-no-return",
        acoustic_bundle(&quantity_core, "acoustic", &validated, &[])?,
    )?;
    let no_return_probe = execute(
        &budget,
        &mut no_return_machine,
        "no-return-probe",
        "later-acoustic-without-parent-return",
        acoustic_bundle(&quantity_core, "acoustic", &validated, &["prefix"])?,
    )?;
    let no_return_ecology = ecology_interfaces
        .get("quantity")
        .ok_or_else(|| "the quantity ecology interface set is absent".to_owned())?
        .read(&no_return_probe.constituent);

    let mut empty_machine =
        LiveCurrentMachine::new(SparseStandingSurface::empty_rank(10).map_err(debug)?);
    let empty_probe = execute(
        &budget,
        &mut empty_machine,
        "empty-standing-probe",
        "audio-probe-without-standing-ecology",
        acoustic_bundle(&quantity_core, "ecology", &validated, &["prefix"])?,
    )?;
    let empty_ecology = ecology_interfaces
        .get("quantity")
        .ok_or_else(|| "the quantity ecology interface set is absent".to_owned())?
        .read(&empty_probe.constituent);

    let local_probes_exact = probes.iter().all(|probe| match &probe.expected_ecology {
        Some(expected) => probe.observed_conducted_ecologies == [expected.clone()],
        None => probe.observed_conducted_ecologies.is_empty(),
    });
    let no_return_exact = !no_return_ecology.data_complete
        && no_return_ecology.token_words == 0
        && no_return_ecology.attention_words == 0
        && !no_return_ecology.conducted;
    let empty_exact = !empty_ecology.data_complete
        && empty_ecology.token_words == 0
        && empty_ecology.attention_words == 0
        && !empty_ecology.conducted;
    let predecessor_departure_exact = training_reads.iter().all(|read| read.predecessor_departed);
    let complete_returns_exact = training_reads
        .iter()
        .all(|read| read.complete_ecology_exposed);
    let acceptance = json!({
        "fixed_source_validated": true,
        "all_three_whisper_context_faces_were_distinct_and_complete": complete_returns_exact,
        "each_return_replaced_its_open_acoustic_predecessor": predecessor_departure_exact,
        "derived_ecology_survived_exact_rest_remount": rest_exact,
        "each_local_nonidentity_probe_conducted_exactly_one_contextual_gate": local_probes_exact,
        "changed_context_conducted_no_trained_gate":
            probe_named(&probes, "changed_context")?.observed_conducted_ecologies.is_empty(),
        "reversed_chronology_conducted_no_trained_gate":
            probe_named(&probes, "reversed_chronology")?.observed_conducted_ecologies.is_empty(),
        "held_speaker_conducted_no_trained_gate":
            probe_named(&probes, "held_speaker")?.observed_conducted_ecologies.is_empty(),
        "no_return_foil_carried_no_inherited_face": no_return_exact,
        "empty_standing_foil_carried_no_inherited_face": empty_exact,
        "source_lineages_departed": machine.memory().live_lineages == 0,
        "no_floating_point_causal_values_entered_soma": true,
    });
    if acceptance
        .as_object()
        .ok_or_else(|| "acceptance is not a JSON object".to_owned())?
        .values()
        .any(|value| value != &json!(true))
    {
        return Err(format!(
            "the bounded audio ecology acceptance did not close: {}",
            serde_json::to_string_pretty(&acceptance).map_err(debug)?
        ));
    }

    Ok(json!({
        "schema": REPORT_SCHEMA,
        "observation_id": OBSERVATION_ID,
        "status": "accepted",
        "question": source.question,
        "theory_to_structure": "Each integer component contributes an exact ordered pressure-block chart. The complete phrase is one support section; its repeated pivot is therefore insufficient without both contextual cofaces. Whisper returns every token and every final-layer cross-attention codeword in the unpadded cut. That later event closes the acoustic aperture and emits the complete contextual ecology as its outgoing factor. Source-absent probes then address only the exact local acoustic support.",
        "source": {
            "schema": source.schema,
            "observation_id": source.observation_id,
            "bytes": validated.source_bytes,
            "components": source.components.len(),
            "training_phrases": source.training.len(),
            "probes": source.probes.len(),
            "retained_token_words": validated.retained_token_words,
            "retained_attention_words": validated.retained_attention_words,
            "fixed_law": source.fixed_law,
        },
        "physical_preflight": {
            "inherited_instrument": source.instrument,
            "host_executor": "ParallelHostLiveCurrentExecutor",
            "host_threads": HOST_THREADS,
            "available_parallelism": std::thread::available_parallelism().map_or(1, usize::from),
            "run_limit_seconds": RUN_LIMIT.as_secs(),
            "event_limit_seconds": EVENT_LIMIT.as_secs(),
        },
        "training": training_reads,
        "rest": {
            "exact": rest_exact,
            "bytes": rest_octets.len(),
            "machine": memory_read(machine.memory()),
        },
        "probes": probes,
        "controls": {
            "no_return": {
                "seed": no_return_seed.read,
                "probe": no_return_probe.read,
                "quantity_ecology": no_return_ecology,
            },
            "empty_standing": {
                "probe": empty_probe.read,
                "quantity_ecology": empty_ecology,
            },
        },
        "acceptance": acceptance,
        "stopping_condition": source.stopping_condition,
        "conclusion": "The identical acoustic pivot did not determine one inscription. Three complete surrounding pressure chronologies joined through that shared pivot into one inherited token-attention ecology. After the parent returns, a larger but locally identical audio event carries that integrated ecology while exactly one context gate RIDEs; the other two gates remain OPEN. Sharing only partial context, reversing component roles, or changing the pivot voice conducts no trained gate. This closes contextual local recurrence and returned reconditioning at the fixed support boundary. It does not yet transport a nonidentical pronunciation into that support.",
    }))
}

fn validate_source<'a>(
    source: &'a Source,
    source_bytes: usize,
) -> Result<ValidatedSource<'a>, String> {
    if source.schema != SOURCE_SCHEMA || source.observation_id != OBSERVATION_ID {
        return Err("the contextual audio source identity changed".to_owned());
    }
    if source.training.len() != 3 || source.probes.len() != 6 {
        return Err("the fixed audio population changed".to_owned());
    }
    let mut components = BTreeMap::new();
    for component in &source.components {
        if component.sample_rate != 16_000
            || component.blocks.is_empty()
            || component.text.trim().is_empty()
            || component.voice.trim().is_empty()
            || components.contains_key(component.id.as_str())
        {
            return Err(format!("component {} changed its fixed cut", component.id));
        }
        let bytes = std::fs::read(&component.path)
            .map_err(|error| format!("{} reads completely: {error}", component.path.display()))?;
        if sha256(&bytes) != component.sha256 {
            return Err(format!("component {} changed its PCM hash", component.id));
        }
        let wave = PcmWave::read(&component.path)?;
        if wave.sample_rate != component.sample_rate || wave.samples.len() != component.samples {
            return Err(format!("component {} changed its PCM extent", component.id));
        }
        let mut cursor = 0usize;
        for (ordinal, block) in component.blocks.iter().enumerate() {
            if block.ordinal != ordinal
                || block.start != cursor
                || block.end <= block.start
                || block.end > wave.samples.len()
                || block.end - block.start > 320
                || wave.samples[block.start..block.end]
                    .iter()
                    .map(|sample| i64::from(*sample))
                    .sum::<i64>()
                    != block.sum
            {
                return Err(format!(
                    "component {} block {} changed",
                    component.id, ordinal
                ));
            }
            cursor = block.end;
        }
        if cursor != wave.samples.len() {
            return Err(format!(
                "component {} blocks do not cover its exact extent",
                component.id
            ));
        }
        components.insert(
            component.id.as_str(),
            ValidatedComponent {
                source: component,
                samples: wave.samples,
            },
        );
    }

    let mut retained_attention_words = 0usize;
    let mut retained_token_words = 0usize;
    for training in &source.training {
        validate_assembled(
            &training.path,
            &training.sha256,
            training.sample_rate,
            training.samples,
            &training.components,
            &components,
        )?;
        let inherited = &training.inherited;
        let attention = &inherited.attention;
        if inherited.token_ids.is_empty()
            || inherited.token_ids.len() != inherited.token_pieces.len()
            || inherited.valid_feature_frames == 0
            || (inherited.valid_feature_frames + 1) / 2 != inherited.valid_encoder_frames
            || inherited.valid_encoder_frames != attention.frames
            || attention.tokens != inherited.token_ids.len()
            || attention.dtype != "ieee754-binary32-raw-u32"
            || attention.layers == 0
            || attention.layer + 1 != attention.layers
            || attention.rows.len() != attention.heads * attention.tokens
            || attention.frame_map.len() != attention.frames
        {
            return Err(format!(
                "{} changed its complete inherited tensor cut",
                training.id
            ));
        }
        let mut rows = BTreeSet::new();
        for row in &attention.rows {
            if row.token_ordinal >= attention.tokens
                || row.head >= attention.heads
                || row.words.len() != attention.frames
                || !rows.insert((row.token_ordinal, row.head))
            {
                return Err(format!("{} carries an invalid attention row", training.id));
            }
            retained_attention_words = retained_attention_words
                .checked_add(row.words.len())
                .ok_or_else(|| "attention word extent overflowed".to_owned())?;
        }
        for (frame, mapping) in attention.frame_map.iter().enumerate() {
            let component = components.get(mapping.component.as_str()).ok_or_else(|| {
                format!(
                    "{} frame {} names absent component {}",
                    training.id, frame, mapping.component
                )
            })?;
            if mapping.frame != frame
                || mapping.role >= training.components.len()
                || mapping.component_block >= component.source.blocks.len()
            {
                return Err(format!(
                    "{} frame {} changed its component-local address",
                    training.id, frame
                ));
            }
        }
        retained_token_words = retained_token_words
            .checked_add(inherited.token_ids.len())
            .ok_or_else(|| "token word extent overflowed".to_owned())?;
    }
    for probe in &source.probes {
        validate_assembled(
            &probe.path,
            &probe.sha256,
            probe.sample_rate,
            probe.samples,
            &probe.assembled_components,
            &components,
        )?;
        for component in probe.core.iter().chain(&probe.extras) {
            if !components.contains_key(component.as_str()) {
                return Err(format!(
                    "probe {} names absent component {}",
                    probe.id, component
                ));
            }
        }
    }
    Ok(ValidatedSource {
        components,
        source_bytes,
        retained_attention_words,
        retained_token_words,
    })
}

fn validate_assembled(
    path: &Path,
    expected_sha256: &str,
    sample_rate: u32,
    samples: usize,
    spans: &[SourceSpan],
    components: &BTreeMap<&str, ValidatedComponent<'_>>,
) -> Result<(), String> {
    let bytes =
        std::fs::read(path).map_err(|error| format!("{} reads: {error}", path.display()))?;
    if sha256(&bytes) != expected_sha256 {
        return Err(format!("{} changed its PCM hash", path.display()));
    }
    let wave = PcmWave::read(path)?;
    if wave.sample_rate != sample_rate || wave.samples.len() != samples || spans.is_empty() {
        return Err(format!("{} changed its assembled extent", path.display()));
    }
    let mut expected = Vec::new();
    let mut cursor = 0usize;
    for (role, span) in spans.iter().enumerate() {
        let component = components.get(span.component.as_str()).ok_or_else(|| {
            format!(
                "{} names absent component {}",
                path.display(),
                span.component
            )
        })?;
        if span.role != role || span.start != cursor || span.end != cursor + component.samples.len()
        {
            return Err(format!(
                "{} changed its component chronology",
                path.display()
            ));
        }
        expected.extend_from_slice(&component.samples);
        cursor = span.end;
    }
    if expected != wave.samples {
        return Err(format!(
            "{} does not equal its exact component chronology",
            path.display()
        ));
    }
    Ok(())
}

fn acoustic_bundle(
    core: &[&str],
    phase: &str,
    source: &ValidatedSource<'_>,
    extras: &[&str],
) -> Result<EventBundle, String> {
    let mut charts = Vec::new();
    let mut arcs = Vec::new();
    let mut section_slots = Vec::new();
    let mut core_slots = Vec::new();
    for (role, id) in core.iter().enumerate() {
        append_component(
            &mut charts,
            &mut arcs,
            &mut core_slots,
            source,
            id,
            role,
            phase,
        )?;
    }
    let gate_slot = next_slot(&arcs)?;
    arcs.push(NativeRegionalArc::new(
        0,
        CurrentBoundaryPort::Exposed(0),
        1,
        CurrentBoundaryPort::Exposed(0),
        context_gate_interface(phase, core, source)?,
        gate_slot,
        0,
        IncidenceHand::Against,
    ));
    core_slots.push(gate_slot);
    section_slots.push(core_slots);
    for (extra, id) in extras.iter().enumerate() {
        let mut slots = Vec::new();
        append_component(
            &mut charts,
            &mut arcs,
            &mut slots,
            source,
            id,
            100 + extra,
            "probe-extra",
        )?;
        section_slots.push(slots);
    }
    Ok(EventBundle {
        semantic_words: arcs.len(),
        charts,
        arcs,
        section_slots,
        receiver: 0,
    })
}

fn consequence_bundle(
    training: &SourceTraining,
    source: &ValidatedSource<'_>,
) -> Result<EventBundle, String> {
    let mut charts = Vec::new();
    let mut arcs = Vec::new();
    let mut incoming = Vec::new();
    let mut outgoing_support = Vec::new();
    for span in &training.components {
        let component = source
            .components
            .get(span.component.as_str())
            .ok_or_else(|| format!("{} component is absent", span.component))?;
        let values = cumulative_block_sums(component.source)?;
        let ordinals = (0..=component.source.blocks.len())
            .map(|value| i64::try_from(value).map_err(debug))
            .collect::<Result<Vec<_>, _>>()?;
        let left = charts.len();
        charts.push(ExactPathChart::new(&values)?);
        let right = charts.len();
        charts.push(ExactPathChart::new(&ordinals)?);
        for block in &component.source.blocks {
            let slot = next_slot(&arcs)?;
            arcs.push(component_arc(
                left,
                right,
                block,
                component.source,
                span.role,
                "acoustic",
                slot,
                IncidenceHand::Against,
            )?);
            incoming.push(slot);
            let slot = next_slot(&arcs)?;
            arcs.push(component_arc(
                left,
                right,
                block,
                component.source,
                span.role,
                "ecology",
                slot,
                IncidenceHand::Against,
            )?);
            outgoing_support.push(slot);
        }
    }
    let core = training
        .components
        .iter()
        .map(|span| span.component.as_str())
        .collect::<Vec<_>>();
    let slot = next_slot(&arcs)?;
    arcs.push(NativeRegionalArc::new(
        0,
        CurrentBoundaryPort::Exposed(0),
        1,
        CurrentBoundaryPort::Exposed(0),
        context_gate_interface("acoustic", &core, source)?,
        slot,
        0,
        IncidenceHand::Against,
    ));
    incoming.push(slot);
    let slot = next_slot(&arcs)?;
    arcs.push(NativeRegionalArc::new(
        0,
        CurrentBoundaryPort::Exposed(0),
        1,
        CurrentBoundaryPort::Exposed(0),
        context_gate_interface("ecology", &core, source)?,
        slot,
        0,
        IncidenceHand::Against,
    ));
    outgoing_support.push(slot);

    let mut sections = vec![incoming, outgoing_support.clone()];
    let token_values = std::iter::once(0i64)
        .chain(training.inherited.token_ids.iter().copied().map(i64::from))
        .collect::<Vec<_>>();
    let token_coordinates = (0..token_values.len())
        .map(|value| i64::try_from(value).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let token_left = charts.len();
    charts.push(ExactPathChart::new(&token_values)?);
    let token_right = charts.len();
    charts.push(ExactPathChart::new(&token_coordinates)?);
    let mut token_slots = Vec::new();
    for (ordinal, token) in training.inherited.token_ids.iter().copied().enumerate() {
        let slot = next_slot(&arcs)?;
        arcs.push(NativeRegionalArc::new(
            token_left,
            CurrentBoundaryPort::Exposed(u32::try_from(ordinal).map_err(debug)?),
            token_right,
            CurrentBoundaryPort::Exposed(u32::try_from(ordinal).map_err(debug)?),
            token_interface(&training.id, ordinal, token),
            slot,
            0,
            IncidenceHand::Against,
        ));
        token_slots.push(slot);
    }
    sections.push(token_slots);

    for row in &training.inherited.attention.rows {
        let values = std::iter::once(0i64)
            .chain(row.words.iter().copied().map(i64::from))
            .collect::<Vec<_>>();
        let coordinates = (0..values.len())
            .map(|value| i64::try_from(value).map_err(debug))
            .collect::<Result<Vec<_>, _>>()?;
        let left = charts.len();
        charts.push(ExactPathChart::new(&values)?);
        let right = charts.len();
        charts.push(ExactPathChart::new(&coordinates)?);
        let mut row_slots = Vec::new();
        for (frame, word) in row.words.iter().copied().enumerate() {
            let mapping = training
                .inherited
                .attention
                .frame_map
                .get(frame)
                .ok_or_else(|| format!("{} frame {} is absent", training.id, frame))?;
            let component = source
                .components
                .get(mapping.component.as_str())
                .ok_or_else(|| format!("{} frame component is absent", mapping.component))?;
            let slot = next_slot(&arcs)?;
            arcs.push(NativeRegionalArc::new(
                left,
                CurrentBoundaryPort::Exposed(u32::try_from(frame).map_err(debug)?),
                right,
                CurrentBoundaryPort::Exposed(u32::try_from(frame).map_err(debug)?),
                attention_interface(
                    &training.id,
                    row.token_ordinal,
                    row.head,
                    mapping,
                    &component.source.sha256,
                    word,
                ),
                slot,
                0,
                IncidenceHand::Against,
            ));
            row_slots.push(slot);
        }
        sections.push(row_slots);
    }
    Ok(EventBundle {
        semantic_words: training.inherited.token_ids.len()
            + training
                .inherited
                .attention
                .rows
                .iter()
                .map(|row| row.words.len())
                .sum::<usize>(),
        charts,
        arcs,
        section_slots: sections,
        receiver: 0,
    })
}

fn append_component(
    charts: &mut Vec<ExactPathChart>,
    arcs: &mut Vec<NativeRegionalArc>,
    slots: &mut Vec<u32>,
    source: &ValidatedSource<'_>,
    id: &str,
    role: usize,
    phase: &str,
) -> Result<(), String> {
    let component = source
        .components
        .get(id)
        .ok_or_else(|| format!("component {id} is absent"))?;
    let values = cumulative_block_sums(component.source)?;
    let ordinals = (0..=component.source.blocks.len())
        .map(|value| i64::try_from(value).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let left = charts.len();
    charts.push(ExactPathChart::new(&values)?);
    let right = charts.len();
    charts.push(ExactPathChart::new(&ordinals)?);
    for block in &component.source.blocks {
        let slot = next_slot(arcs)?;
        arcs.push(component_arc(
            left,
            right,
            block,
            component.source,
            role,
            phase,
            slot,
            IncidenceHand::Against,
        )?);
        slots.push(slot);
    }
    Ok(())
}

fn cumulative_block_sums(component: &SourceComponent) -> Result<Vec<i64>, String> {
    let mut values = Vec::with_capacity(component.blocks.len() + 1);
    values.push(0);
    for block in &component.blocks {
        let next = values
            .last()
            .copied()
            .unwrap_or(0i64)
            .checked_add(block.sum)
            .ok_or_else(|| format!("component {} cumulative sum overflowed", component.id))?;
        values.push(next);
    }
    Ok(values)
}

fn component_arc(
    left: usize,
    right: usize,
    block: &SourceBlock,
    component: &SourceComponent,
    role: usize,
    phase: &str,
    slot: u32,
    hand: IncidenceHand,
) -> Result<NativeRegionalArc, String> {
    let port = u32::try_from(block.ordinal).map_err(debug)?;
    Ok(NativeRegionalArc::new(
        left,
        CurrentBoundaryPort::Exposed(port),
        right,
        CurrentBoundaryPort::Exposed(port),
        component_interface(phase, role, component, block),
        slot,
        0,
        hand,
    ))
}

fn component_interface(
    phase: &str,
    role: usize,
    component: &SourceComponent,
    block: &SourceBlock,
) -> InterfaceCapability {
    InterfaceCapability::new(
        namespace(&[
            b"eros-audio-context-support-v1",
            phase.as_bytes(),
            &role.to_le_bytes(),
            component.sha256.as_bytes(),
            &block.ordinal.to_le_bytes(),
        ]),
        u64::from_le_bytes(block.sum.to_le_bytes()),
    )
}

fn context_gate_interface(
    phase: &str,
    core: &[&str],
    source: &ValidatedSource<'_>,
) -> Result<InterfaceCapability, String> {
    let mut ordered = Vec::new();
    for (role, id) in core.iter().enumerate() {
        let component = source
            .components
            .get(id)
            .ok_or_else(|| format!("component {id} is absent"))?;
        ordered.extend_from_slice(&role.to_le_bytes());
        ordered.extend_from_slice(&(component.source.sha256.len() as u64).to_le_bytes());
        ordered.extend_from_slice(component.source.sha256.as_bytes());
    }
    Ok(InterfaceCapability::new(
        namespace(&[
            b"eros-audio-context-conductance-v1",
            phase.as_bytes(),
            &ordered,
        ]),
        u64::try_from(core.len()).map_err(debug)?,
    ))
}

fn token_interface(phrase: &str, ordinal: usize, token: u32) -> InterfaceCapability {
    InterfaceCapability::new(
        namespace(&[
            b"eros-audio-context-token-v1",
            phrase.as_bytes(),
            &ordinal.to_le_bytes(),
        ]),
        u64::from(token),
    )
}

fn attention_interface(
    phrase: &str,
    token: usize,
    head: usize,
    mapping: &SourceFrameMap,
    component_sha256: &str,
    word: u32,
) -> InterfaceCapability {
    InterfaceCapability::new(
        namespace(&[
            b"eros-audio-context-attention-v1",
            phrase.as_bytes(),
            &token.to_le_bytes(),
            &head.to_le_bytes(),
            &mapping.frame.to_le_bytes(),
            &mapping.role.to_le_bytes(),
            component_sha256.as_bytes(),
            &mapping.component_block.to_le_bytes(),
        ]),
        u64::from(word),
    )
}

fn ecology_interfaces(
    training: &SourceTraining,
    source: &ValidatedSource<'_>,
) -> Result<EcologyInterfaces, String> {
    let tokens = training
        .inherited
        .token_ids
        .iter()
        .copied()
        .enumerate()
        .map(|(ordinal, token)| token_interface(&training.id, ordinal, token))
        .collect();
    let mut attention = BTreeSet::new();
    for row in &training.inherited.attention.rows {
        for (frame, word) in row.words.iter().copied().enumerate() {
            let mapping = training
                .inherited
                .attention
                .frame_map
                .get(frame)
                .ok_or_else(|| format!("{} frame {} is absent", training.id, frame))?;
            let component = source
                .components
                .get(mapping.component.as_str())
                .ok_or_else(|| format!("component {} is absent", mapping.component))?;
            attention.insert(attention_interface(
                &training.id,
                row.token_ordinal,
                row.head,
                mapping,
                &component.source.sha256,
                word,
            ));
        }
    }
    let core = training
        .components
        .iter()
        .map(|span| span.component.as_str())
        .collect::<Vec<_>>();
    Ok(EcologyInterfaces {
        tokens,
        attention,
        gate: context_gate_interface("ecology", &core, source)?,
    })
}

fn execute(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    id: &str,
    role: &str,
    bundle: EventBundle,
) -> Result<EventOutcome, String> {
    budget.require_open()?;
    if bundle.charts.is_empty()
        || bundle.arcs.is_empty()
        || bundle.section_slots.is_empty()
        || bundle.receiver >= bundle.charts.len()
    {
        return Err(format!(
            "event {id} has an empty or invalid regional bundle"
        ));
    }
    let mut organs = (0..bundle.charts.len())
        .map(|_| NativeRelationOrgan::new())
        .collect::<Vec<_>>();
    let mut currents = organs
        .iter_mut()
        .zip(&bundle.charts)
        .map(|(organ, chart)| NativeEventCurrent::ending_complex(organ, chart.complex(), action()))
        .collect::<Vec<_>>();
    let sections = bundle
        .section_slots
        .iter()
        .map(|slots| RegionalSupportSection::new(slots))
        .collect::<Vec<_>>();
    let regional = [NativeRegionalRelation::with_support_sections(
        bundle.receiver,
        &bundle.arcs,
        &sections,
    )];
    let before = memory_read(machine.memory());
    let mut executor = ParallelHostLiveCurrentExecutor::new(HOST_THREADS);
    let started = Instant::now();
    let radiation =
        present_native_event_with_regional(machine, &mut executor, &mut currents, &[], &regional)
            .map_err(debug)?;
    let elapsed = started.elapsed();
    if elapsed > EVENT_LIMIT {
        return Err(format!(
            "event {id} exceeded {} seconds",
            EVENT_LIMIT.as_secs()
        ));
    }
    budget.require_open()?;
    let relation = radiation
        .regional()
        .first()
        .ok_or_else(|| format!("event {id} returned no regional relation"))?;
    let constituent = relation.constituent().clone();
    let read = EventRead {
        id: id.to_owned(),
        role: role.to_owned(),
        currents: bundle.charts.len(),
        arcs: bundle.arcs.len(),
        support_sections: bundle.section_slots.len(),
        semantic_words: bundle.semantic_words,
        contacts: contact_read(relation.arcs()),
        before,
        after: memory_read(machine.memory()),
        emitted: shape_read(&constituent),
        elapsed_microseconds: elapsed.as_micros(),
    };
    Ok(EventOutcome { read, constituent })
}

fn exposed_interfaces(constituent: &LiveConstituent) -> BTreeSet<InterfaceCapability> {
    constituent
        .exposed()
        .iter()
        .filter_map(|pin| {
            constituent
                .pins()
                .get(*pin as usize)
                .and_then(|pin| pin.interface())
        })
        .collect()
}

fn interface_transition_read(
    constituent: &LiveConstituent,
    interface: InterfaceCapability,
) -> InterfaceTransitionRead {
    let mut read = InterfaceTransitionRead::default();
    for (boundary_at, boundary) in constituent.boundaries().iter().enumerate() {
        let carries = boundary.paths().iter().any(|path| {
            path.steps().iter().any(|step| {
                constituent
                    .incidences()
                    .get(step.incidence() as usize)
                    .and_then(|incidence| constituent.pins().get(incidence.pin() as usize))
                    .and_then(|pin| pin.interface())
                    == Some(interface.clone())
            })
        });
        if !carries {
            continue;
        }
        match constituent.boundary_transition(boundary_at) {
            Some(LiveBoundaryTransition::Open) => read.open += 1,
            Some(LiveBoundaryTransition::Ride) => read.ride += 1,
            Some(LiveBoundaryTransition::Found) => read.found += 1,
            None => {}
        }
    }
    read
}

fn next_slot(arcs: &[NativeRegionalArc]) -> Result<u32, String> {
    u32::try_from(arcs.len()).map_err(debug)
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving audio ecology action")
}

fn contact_read(arcs: &[RegionalArcRadiation]) -> ContactRead {
    let mut read = ContactRead::default();
    for arc in arcs {
        match arc.contact().emission.map(|emission| emission.deed) {
            None => read.open += 1,
            Some(FeltDeed::Ride) => read.ride += 1,
            Some(FeltDeed::FoundThis) => read.found_this += 1,
            Some(FeltDeed::FoundThat) => read.found_that += 1,
            Some(FeltDeed::Dark) => read.dark += 1,
        }
    }
    read
}

fn shape_read(constituent: &LiveConstituent) -> ShapeRead {
    let mut paths = 0usize;
    let mut open_boundaries = 0usize;
    let mut ride_boundaries = 0usize;
    let mut found_boundaries = 0usize;
    for (at, boundary) in constituent.boundaries().iter().enumerate() {
        paths += boundary.paths().len();
        match constituent.boundary_transition(at) {
            Some(LiveBoundaryTransition::Open) => open_boundaries += 1,
            Some(LiveBoundaryTransition::Ride) => ride_boundaries += 1,
            Some(LiveBoundaryTransition::Found) => found_boundaries += 1,
            None => {}
        }
    }
    let mut support_extents = constituent
        .support_sections()
        .iter()
        .map(|section| section.boundaries().len())
        .collect::<Vec<_>>();
    support_extents.sort_unstable();
    ShapeRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        boundaries: constituent.boundaries().len(),
        paths,
        exposed_pins: constituent.exposed().len(),
        support_sections: constituent.support_sections().len(),
        support_extents,
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

fn probe_named<'a>(probes: &'a [ProbeRead], id: &str) -> Result<&'a ProbeRead, String> {
    probes
        .iter()
        .find(|probe| probe.id == id)
        .ok_or_else(|| format!("probe {id} is absent"))
}

fn namespace(parts: &[&[u8]]) -> u64 {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    u64::from_le_bytes(digest.finalize()[..8].try_into().expect("eight bytes"))
}

fn sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn write_new_json(path: &Path, value: &Value) -> Result<(), String> {
    let mut bytes =
        serde_json::to_vec_pretty(value).map_err(|error| format!("report encodes: {error}"))?;
    bytes.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("{} opens as a new report: {error}", path.display()))?;
    file.write_all(&bytes)
        .map_err(|error| format!("{} writes completely: {error}", path.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", path.display()))
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}
