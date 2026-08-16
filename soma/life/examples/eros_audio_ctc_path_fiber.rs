#[allow(dead_code)]
#[path = "audio_inscription/exact_pcm.rs"]
mod exact_pcm;

use std::cmp::Ordering;
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
use num_bigint::BigUint;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;
use soma_membrane::{
    CurrentBoundaryPort, InterfaceCapability, LiveBoundaryTransition, LiveConstituent,
    LiveCurrentMachine, LiveMemory, ParallelCpuLiveCurrentExecutor, RegionalArcRadiation,
    RegionalSupportSection, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_audio_ctc_path_fiber/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_audio_ctc_path_fiber";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";

const SOURCE_SCHEMA: &str = "eros.audio-ctc-path-fiber.source.v1";
const REPORT_SCHEMA: &str = "eros.audio-ctc-path-fiber.report.v1";
const OBSERVATION_ID: &str = "eros-audio-ctc-path-fiber-01";
const CPU_THREADS: usize = 8;
const CPU_WORKER_STACK_BYTES: usize = 32 * 1024 * 1024;
const EVENT_LIMIT: Duration = Duration::from_secs(30);
const RUN_LIMIT: Duration = Duration::from_secs(180);
const PCM_BLOCK: usize = 320;

// These are direct world vocabulary coordinates. They are deliberately fixed integers rather
// than hashes of files, recordings, speakers, phrases, or contexts.
const NS_OCCURRENCE_LINK: u64 = 0x4552_4f53_0000_0001;
const NS_OCCURRENCE_DATA_BASE: u64 = 0x4552_4f53_0000_0100;
const NS_EXPRESSION_COMMAND: u64 = 0x4552_4f53_0000_0201;
const NS_EXPRESSION_SYMBOL: u64 = 0x4552_4f53_0000_0202;
const NS_CONTEXT_IDENTITY: u64 = 0x4552_4f53_0000_0301;
const NS_CONTEXT_ATOM: u64 = 0x4552_4f53_0000_0302;
const NS_CROSS_FACE: u64 = 0x4552_4f53_0000_0401;
const NS_CONSEQUENCE: u64 = 0x4552_4f53_0000_0501;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    question: String,
    selection_law: String,
    numerical_law: String,
    instrument: Value,
    sample_rate: u32,
    blank_token_id: u32,
    vocabulary: Vec<SourceVocabulary>,
    commands: Vec<SourceCommand>,
    contexts: Vec<SourceContext>,
    untrained_context: SourceBareContext,
    occurrences: Vec<SourceOccurrence>,
    causal_digest_policy: String,
    stopping_condition: String,
}

#[derive(Deserialize)]
struct SourceVocabulary {
    id: u32,
    token: String,
}

#[derive(Deserialize)]
struct SourceCommand {
    id: u32,
    text: String,
    token_ids: Vec<u32>,
}

#[derive(Clone, Deserialize)]
struct SourceBareContext {
    id: u32,
    name: String,
    atoms: Vec<u32>,
}

#[derive(Clone, Deserialize)]
struct SourceContext {
    id: u32,
    name: String,
    atoms: Vec<u32>,
    consequence: SourceConsequence,
}

#[derive(Clone, Deserialize)]
struct SourceConsequence {
    id: u32,
    name: String,
}

#[derive(Deserialize)]
struct SourceOccurrence {
    ordinal: u32,
    role: String,
    context_id: Option<u32>,
    partition: String,
    observer_label: String,
    relative_path: String,
    speaker: String,
    path: PathBuf,
    sha256: String,
    sample_rate: u32,
    samples: usize,
    pcm_min: i16,
    pcm_max: i16,
    field: SourceField,
    fibers: Vec<SourceFiber>,
    fiber_order: Vec<String>,
    unique_winner: bool,
    derived_expression: Option<String>,
    observer_greedy_text: String,
    observer_greedy_ids: Vec<u32>,
}

#[derive(Deserialize)]
struct SourceField {
    frames: usize,
    alphabet: usize,
    dtype: String,
    probability_words: Vec<u32>,
    frame_sums: Vec<DyadicWire>,
}

#[derive(Deserialize)]
struct SourceFiber {
    command_id: u32,
    text: String,
    measure: DyadicWire,
    nonzero_forward_states: usize,
}

#[derive(Clone, Deserialize)]
struct DyadicWire {
    numerator_hex: String,
    denominator_exponent: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Dyadic {
    numerator: BigUint,
    denominator_exponent: u32,
}

impl Dyadic {
    fn zero() -> Self {
        Self {
            numerator: BigUint::from(0u8),
            denominator_exponent: 0,
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator == BigUint::from(0u8)
    }

    fn normalized(mut self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        while self.denominator_exponent > 0 && !self.numerator.bit(0) {
            self.numerator >>= 1usize;
            self.denominator_exponent -= 1;
        }
        self
    }

    fn add(&self, other: &Self) -> Self {
        let exponent = self.denominator_exponent.max(other.denominator_exponent);
        let left = &self.numerator
            << usize::try_from(exponent - self.denominator_exponent)
                .expect("a u32 exponent delta fits usize");
        let right = &other.numerator
            << usize::try_from(exponent - other.denominator_exponent)
                .expect("a u32 exponent delta fits usize");
        Self {
            numerator: left + right,
            denominator_exponent: exponent,
        }
        .normalized()
    }

    fn multiply(&self, other: &Self) -> Result<Self, String> {
        Ok(Self {
            numerator: &self.numerator * &other.numerator,
            denominator_exponent: self
                .denominator_exponent
                .checked_add(other.denominator_exponent)
                .ok_or_else(|| "one exact dyadic exponent overflowed u32".to_owned())?,
        }
        .normalized())
    }

    fn compare(&self, other: &Self) -> Ordering {
        let exponent = self.denominator_exponent.max(other.denominator_exponent);
        let left = &self.numerator
            << usize::try_from(exponent - self.denominator_exponent)
                .expect("a u32 exponent delta fits usize");
        let right = &other.numerator
            << usize::try_from(exponent - other.denominator_exponent)
                .expect("a u32 exponent delta fits usize");
        left.cmp(&right)
    }

    fn from_wire(wire: &DyadicWire) -> Result<Self, String> {
        let numerator =
            BigUint::parse_bytes(wire.numerator_hex.as_bytes(), 16).ok_or_else(|| {
                format!(
                    "{} is not an exact hexadecimal numerator",
                    wire.numerator_hex
                )
            })?;
        let value = Self {
            numerator,
            denominator_exponent: wire.denominator_exponent,
        };
        let normalized = value.clone().normalized();
        if value != normalized {
            return Err("a source dyadic was not canonically normalized".to_owned());
        }
        Ok(value)
    }

    fn digits_le(&self) -> Vec<u32> {
        self.numerator.to_u32_digits()
    }
}

#[derive(Clone)]
struct RecomputedFiber {
    command_id: u32,
    text: String,
    measure: Dyadic,
    nonzero_forward_states: usize,
}

struct ValidatedOccurrence<'a> {
    source: &'a SourceOccurrence,
    wave: PcmWave,
    derived_command_id: u32,
    derived_expression: String,
    order: Vec<String>,
    fibers: Vec<RecomputedFiber>,
    data_words: Vec<u32>,
}

struct ValidatedSource<'a> {
    occurrences: Vec<ValidatedOccurrence<'a>>,
    command_by_text: BTreeMap<&'a str, &'a SourceCommand>,
    context_by_id: BTreeMap<u32, &'a SourceContext>,
    source_bytes: usize,
}

struct EventBundle {
    charts: Vec<ExactPathChart>,
    arcs: Vec<NativeRegionalArc>,
    section_slots: Vec<Vec<u32>>,
    receiver: usize,
    data_words: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
struct InterfaceTransitionRead {
    open: usize,
    ride: usize,
    found: usize,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize)]
struct ContactRead {
    open: usize,
    ride: usize,
    found_this: usize,
    found_that: usize,
    dark: usize,
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct EventRead {
    id: String,
    role: String,
    currents: usize,
    arcs: usize,
    support_sections: usize,
    data_words: usize,
    contacts: ContactRead,
    before: MemoryRead,
    after: MemoryRead,
    emitted: ShapeRead,
    elapsed_microseconds: u128,
}

struct EventOutcome {
    read: EventRead,
    constituent: LiveConstituent,
    prior: Vec<LiveConstituent>,
}

#[derive(Serialize)]
struct FiberSummary {
    occurrence: u32,
    role: String,
    partition: String,
    speaker: String,
    relative_path: String,
    frames: usize,
    alphabet: usize,
    probability_words: usize,
    pcm_blocks: usize,
    derived_expression: String,
    unique_winner: bool,
    top_five: Vec<String>,
    observer_greedy_text: String,
    greedy_agrees_with_complete_fiber: bool,
    exact_measure_numerator_bits: Vec<usize>,
    exact_forward_states: Vec<usize>,
}

#[derive(Serialize)]
struct CultivationRead {
    occurrence: u32,
    context: String,
    field: EventRead,
    returned_expression: EventRead,
    occurrence_link_face: InterfaceTransitionRead,
    expression_face: InterfaceTransitionRead,
    cross_face: InterfaceTransitionRead,
    predecessor_departed: bool,
    retained_occurrence_words: usize,
}

#[derive(Serialize)]
struct ExpressionProbeRead {
    id: String,
    occurrence: u32,
    derived_expression: String,
    event: EventRead,
    expression_face: InterfaceTransitionRead,
    retained_cultivation_words: BTreeMap<u32, usize>,
    retained_probe_words: usize,
}

#[derive(Serialize)]
struct ProbeRead {
    id: String,
    occurrence: u32,
    derived_expression: String,
    context: String,
    expected_consequence: Option<String>,
    event: EventRead,
    selected_cross_face: InterfaceTransitionRead,
    all_trained_cross_faces: BTreeMap<String, InterfaceTransitionRead>,
    retained_cultivation_words: BTreeMap<u32, usize>,
    retained_probe_words: usize,
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
            Err("the bounded CTC path-fiber run exceeded three minutes".to_owned())
        } else {
            Ok(())
        }
    }
}

fn main() {
    if let Err(error) = run_main() {
        eprintln!("eros audio CTC path fiber: {error}");
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
    let report = run(&source, source_bytes.len(), sha256(&source_bytes))?;
    write_new_json(&output_path, &report)?;
    eprintln!(
        "eros audio CTC path fiber: accepted · {} bytes · {}",
        source_bytes.len(),
        output_path.display()
    );
    Ok(())
}

fn usage() -> String {
    "usage: eros_audio_ctc_path_fiber <SOURCE.json> <new-report.json>".to_owned()
}

fn run(source: &Source, source_bytes: usize, source_sha256: String) -> Result<Value, String> {
    let budget = RunBudget::new();
    let validated = validate_source(source, source_bytes)?;
    let mut executor =
        ParallelCpuLiveCurrentExecutor::with_worker_stack(CPU_THREADS, CPU_WORKER_STACK_BYTES);
    let mut machine =
        LiveCurrentMachine::new(SparseStandingSurface::empty_rank(10).map_err(debug)?);

    let fiber_summaries = validated
        .occurrences
        .iter()
        .map(fiber_summary)
        .collect::<Vec<_>>();

    let mut cultivation = Vec::new();
    for occurrence in validated.occurrences.iter().take(2) {
        budget.require_open()?;
        let field = execute(
            &budget,
            &mut executor,
            &mut machine,
            &format!("occurrence-{}-field", occurrence.source.ordinal),
            "complete-acoustic-field-open",
            field_bundle(occurrence)?,
        )?;
        if field.prior.len() + 1 != machine.memory().standing_constituents
            || field.read.emitted.open_boundaries == 0
        {
            return Err(format!(
                "occurrence {} did not stand as one OPEN acoustic field",
                occurrence.source.ordinal
            ));
        }

        let context_id = occurrence.source.context_id.ok_or_else(|| {
            format!(
                "cultivation occurrence {} has no returned context",
                occurrence.source.ordinal
            )
        })?;
        let context = validated
            .context_by_id
            .get(&context_id)
            .copied()
            .ok_or_else(|| format!("context {context_id} is absent"))?;
        let declared = validated
            .command_by_text
            .get(occurrence.source.observer_label.as_str())
            .copied()
            .ok_or_else(|| {
                format!(
                    "declared expression {} is absent",
                    occurrence.source.observer_label
                )
            })?;
        let returned = execute(
            &budget,
            &mut executor,
            &mut machine,
            &format!("occurrence-{}-return", occurrence.source.ordinal),
            "world-label-expression-and-context-return",
            return_bundle(occurrence.source.ordinal, declared, context)?,
        )?;
        let link_face = interface_transition_read(
            &returned.constituent,
            occurrence_link_interface(occurrence.source.ordinal),
        );
        let expression_face = interface_transition_read(
            &returned.constituent,
            expression_command_interface(occurrence.source.ordinal, declared.id),
        );
        let cross_face = interface_transition_read(
            &returned.constituent,
            cross_face_interface(context.id, declared.id),
        );
        let predecessor_departed = returned
            .prior
            .iter()
            .any(|prior| prior == &field.constituent)
            && machine
                .standing()
                .constituents()
                .iter()
                .all(|body| body != &field.constituent);
        let retained_occurrence_words = count_namespace(
            &returned.constituent,
            occurrence_data_namespace(occurrence.source.ordinal)?,
        );
        if !predecessor_departed || retained_occurrence_words != occurrence.data_words.len() {
            return Err(format!(
                "occurrence {} return mismatch: link_face={link_face:?} predecessor_departed={} retained_words={}/{} standing={}",
                occurrence.source.ordinal,
                predecessor_departed,
                retained_occurrence_words,
                occurrence.data_words.len(),
                machine.memory().standing_constituents,
            ));
        }
        cultivation.push(CultivationRead {
            occurrence: occurrence.source.ordinal,
            context: context.name.clone(),
            field: field.read,
            returned_expression: returned.read,
            occurrence_link_face: link_face,
            expression_face,
            cross_face,
            predecessor_departed,
            retained_occurrence_words,
        });
    }

    if machine.memory().standing_constituents != 1 || machine.memory().live_lineages != 0 {
        return Err(
            "the two returned pronunciations did not rest as one integrated expression ecology"
                .to_owned(),
        );
    }
    let cultivated = machine
        .standing()
        .constituents()
        .first()
        .cloned()
        .ok_or_else(|| "the cultivated expression body is absent".to_owned())?;
    for occurrence in validated.occurrences.iter().take(2) {
        if count_namespace(
            &cultivated,
            occurrence_data_namespace(occurrence.source.ordinal)?,
        ) != occurrence.data_words.len()
        {
            return Err(format!(
                "cultivation occurrence {} departed from the integrated body",
                occurrence.source.ordinal
            ));
        }
    }

    let rest = machine.rest_image().map_err(debug)?;
    let rest_octets = rest.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. This site reported only the
    // octet COUNT and dropped the octets; the count below is unchanged and the octets now reach
    // `holon-plate deposit --from ERST:`.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let rest_bytes = rest_octets.len();
    let remounted = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == rest
        && remounted.standing() == machine.standing();
    if !rest_exact {
        return Err("the cultivated path-fiber ecology changed across rest/remount".to_owned());
    }
    machine = remounted;

    let held_positive = validated
        .occurrences
        .get(2)
        .ok_or_else(|| "the held positive occurrence is absent".to_owned())?;
    let held_foil = validated
        .occurrences
        .get(3)
        .ok_or_else(|| "the held foil occurrence is absent".to_owned())?;
    let expression_probe = probe_expression(
        &budget,
        &mut executor,
        &machine,
        held_positive,
        &validated,
        "held-right-expression-only",
    )?;
    let mut probes = Vec::new();
    for context in &source.contexts {
        probes.push(probe(
            &budget,
            &mut executor,
            &machine,
            held_positive,
            ProbeContext::Trained(context),
            false,
            &validated,
            &format!("held-right-{}", context.name),
        )?);
    }
    probes.push(probe(
        &budget,
        &mut executor,
        &machine,
        held_positive,
        ProbeContext::Untrained(&source.untrained_context),
        false,
        &validated,
        "held-right-copy",
    )?);
    probes.push(probe(
        &budget,
        &mut executor,
        &machine,
        held_positive,
        ProbeContext::Untrained(&source.untrained_context),
        true,
        &validated,
        "held-right-expression-plus-copy",
    )?);
    for context in &source.contexts {
        probes.push(probe(
            &budget,
            &mut executor,
            &machine,
            held_foil,
            ProbeContext::Trained(context),
            false,
            &validated,
            &format!("held-left-{}", context.name),
        )?);
    }

    let mut empty = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(10).map_err(debug)?);
    let empty_context = source
        .contexts
        .first()
        .ok_or_else(|| "the first trained context is absent".to_owned())?;
    let empty_probe = probe_on(
        &budget,
        &mut executor,
        &mut empty,
        held_positive,
        ProbeContext::Trained(empty_context),
        false,
        &validated,
        "held-right-empty-standing",
    )?;

    let right_command = held_positive.derived_command_id;
    let left_command = held_foil.derived_command_id;
    let right_probes = probes
        .iter()
        .filter(|probe| probe.derived_expression == held_positive.derived_expression)
        .collect::<Vec<_>>();
    let left_probes = probes
        .iter()
        .filter(|probe| probe.derived_expression == held_foil.derived_expression)
        .collect::<Vec<_>>();
    let trained_positive_exact = right_probes
        .iter()
        .filter(|probe| probe.expected_consequence.is_some())
        .all(|probe| {
            probe
                .retained_cultivation_words
                .values()
                .all(|count| *count > 0)
        });
    let untrained_positive = probe_named(&probes, "held-right-copy")?;
    let untrained_context_only_exact = untrained_positive
        .retained_cultivation_words
        .values()
        .all(|count| *count == 0);
    let expression_plus_untrained = probe_named(&probes, "held-right-expression-plus-copy")?;
    let untrained_exact = expression_plus_untrained
        .retained_cultivation_words
        .values()
        .all(|count| *count > 0)
        && expression_plus_untrained.selected_cross_face.ride == 0
        && expression_plus_untrained.selected_cross_face.found == 0;
    let foil_exact = left_probes.iter().all(|probe| {
        probe
            .retained_cultivation_words
            .values()
            .all(|count| *count == 0)
    });
    let empty_exact = empty_probe
        .retained_cultivation_words
        .values()
        .all(|count| *count == 0);
    let expression_only_exact = expression_probe
        .retained_cultivation_words
        .values()
        .all(|count| *count > 0);
    let contextual_sections_select_exactly_one = right_probes
        .iter()
        .filter(|probe| probe.expected_consequence.is_some())
        .all(|probe| {
            probe
                .retained_cultivation_words
                .values()
                .all(|count| *count > 0)
        })
        && untrained_context_only_exact
        && expression_plus_untrained.selected_cross_face.ride == 0
        && expression_plus_untrained.selected_cross_face.found == 0;
    let distinct_pronunciations = validated.occurrences[0].wave.samples
        != validated.occurrences[1].wave.samples
        && validated.occurrences[0].source.speaker != validated.occurrences[1].source.speaker
        && validated.occurrences[0].data_words != validated.occurrences[1].data_words;
    let greedy_collapse_insufficient = validated.occurrences.iter().any(|occurrence| {
        occurrence.source.observer_greedy_text.to_lowercase() != occurrence.derived_expression
    });
    let acceptance = json!({
        "complete_source_and_all_35_fibers_recomputed_exactly": true,
        "two_distinct_cultivation_pronunciations_returned_one_expression": distinct_pronunciations,
        "second_return_joined_the_first_expression_without_requiring_an_exact_waveform": true,
        "both_complete_occurrence_fields_survived_in_one_body": true,
        "cultivated_body_rested_and_remounted_exactly": rest_exact,
        "held_right_expression_only_recruited_the_cultivated_body": expression_only_exact,
        "held_right_addressed_the_expression_in_each_trained_context": trained_positive_exact,
        "complete_context_sections_selected_only_trained_cross_faces": contextual_sections_select_exactly_one,
        "untrained_context_preserved_expression_contact_without_inventing_consequence": untrained_exact,
        "held_left_shared_context_but_did_not_recruit_right_expression": foil_exact,
        "empty_standing_supplied_no_inherited_expression": empty_exact,
        "complete_fiber_succeeded_where_greedy_collapse_did_not": greedy_collapse_insufficient,
        "no_digest_or_floating_point_value_entered_a_causal_interface": true,
        "source_lineages_departed": machine.memory().live_lineages == 0,
    });
    if acceptance
        .as_object()
        .ok_or_else(|| "acceptance is not an object".to_owned())?
        .values()
        .any(|value| value != &json!(true))
    {
        return Err(format!(
            "the bounded CTC path-fiber acceptance did not close: {}",
            serde_json::to_string_pretty(&acceptance).map_err(debug)?
        ));
    }

    Ok(json!({
        "schema": REPORT_SCHEMA,
        "observation_id": OBSERVATION_ID,
        "status": "accepted",
        "question": source.question,
        "theory_to_structure": "A recording is one complete ordered frame-by-symbol field, not a filename or transcript identity. The inherited binary32 codewords are decoded as exact dyadics and the complete CTC forward sum yields one ordered family of expression-path fibers. During cultivation only, the world later returns its declared expression across the occurrence link. Each return consumes the prior expression phase and emanates the next direct symbol-path phase; this preserves causal recurrence without pretending two moments are one interface. Context and expression meet at a direct cross-face coordinate. A held field receives no label or transcript: its exact fiber winner supplies the expression coordinate, and support-cover closure decides whether the expression or complete contextual face can recruit standing terrain.",
        "source": {
            "schema": source.schema,
            "observation_id": source.observation_id,
            "bytes": validated.source_bytes,
            "sha256_provenance_only": source_sha256,
            "selection_law": source.selection_law,
            "numerical_law": source.numerical_law,
            "causal_digest_policy": source.causal_digest_policy,
            "vocabulary_symbols": source.vocabulary.len(),
            "commands": source.commands.len(),
            "contexts": source.contexts.len(),
            "occurrences": source.occurrences.len(),
        },
        "physical_preflight": {
            "inherited_instrument": source.instrument,
            "cpu_executor": "ParallelCpuLiveCurrentExecutor",
            "cpu_threads": CPU_THREADS,
            "cpu_worker_stack_bytes": CPU_WORKER_STACK_BYTES,
            "available_parallelism": std::thread::available_parallelism().map_or(1, usize::from),
            "run_limit_seconds": RUN_LIMIT.as_secs(),
            "event_limit_seconds": EVENT_LIMIT.as_secs(),
        },
        "fiber_fields": fiber_summaries,
        "cultivation": cultivation,
        "rest": {
            "exact": rest_exact,
            "bytes": rest_bytes,
            "machine": memory_read(machine.memory()),
        },
        "expression_probe": expression_probe,
        "probes": probes,
        "empty_standing": empty_probe,
        "acceptance": acceptance,
        "stopping_condition": source.stopping_condition,
        "conclusion": format!(
            "The two cultivation recordings were different PCM worldlines from different speakers, yet their independently recomputed 35-way exact path fields both selected expression {} and cohered when the second return met the first return's expression phase. That event emanated a later recruitable symbol-path phase instead of retaining a spent seam. The unseen held recording selected the same expression without receiving a transcript; it recruited the cultivated field through that later phase and under each trained cross-face. COPY alone recruited nothing; when the expression phase was separately co-present, the expression recruited while COPY remained OPEN. The held {} foil recruited neither expression nor contextual ecology. The operative inherited object is therefore the complete path-fiber ordering plus returned phased topology, not greedy decoded text, an audio digest, or exact waveform identity. This closes a bounded inherited-pronunciation transport law; it does not claim that CTC itself was learned inside Soma.",
            command_text(source, right_command)?,
            command_text(source, left_command)?,
        ),
    }))
}

enum ProbeContext<'a> {
    Trained(&'a SourceContext),
    Untrained(&'a SourceBareContext),
}

impl ProbeContext<'_> {
    fn id(&self) -> u32 {
        match self {
            Self::Trained(context) => context.id,
            Self::Untrained(context) => context.id,
        }
    }

    fn name(&self) -> &str {
        match self {
            Self::Trained(context) => &context.name,
            Self::Untrained(context) => &context.name,
        }
    }

    fn atoms(&self) -> &[u32] {
        match self {
            Self::Trained(context) => &context.atoms,
            Self::Untrained(context) => &context.atoms,
        }
    }

    fn consequence(&self) -> Option<&SourceConsequence> {
        match self {
            Self::Trained(context) => Some(&context.consequence),
            Self::Untrained(_) => None,
        }
    }
}

fn probe(
    budget: &RunBudget,
    executor: &mut ParallelCpuLiveCurrentExecutor,
    cultivated: &LiveCurrentMachine,
    occurrence: &ValidatedOccurrence<'_>,
    context: ProbeContext<'_>,
    include_expression: bool,
    source: &ValidatedSource<'_>,
    id: &str,
) -> Result<ProbeRead, String> {
    let mut branch = LiveCurrentMachine::from_rest_image(cultivated.rest_image().map_err(debug)?)
        .map_err(debug)?;
    probe_on(
        budget,
        executor,
        &mut branch,
        occurrence,
        context,
        include_expression,
        source,
        id,
    )
}

fn probe_expression(
    budget: &RunBudget,
    executor: &mut ParallelCpuLiveCurrentExecutor,
    cultivated: &LiveCurrentMachine,
    occurrence: &ValidatedOccurrence<'_>,
    source: &ValidatedSource<'_>,
    id: &str,
) -> Result<ExpressionProbeRead, String> {
    let command = source
        .command_by_text
        .get(occurrence.derived_expression.as_str())
        .copied()
        .ok_or_else(|| {
            format!(
                "derived expression {} is absent",
                occurrence.derived_expression
            )
        })?;
    let mut branch = LiveCurrentMachine::from_rest_image(cultivated.rest_image().map_err(debug)?)
        .map_err(debug)?;
    let outcome = execute(
        budget,
        executor,
        &mut branch,
        id,
        "held-field-derived-expression-only",
        expression_probe_bundle(occurrence, command)?,
    )?;
    let retained_cultivation_words = source
        .occurrences
        .iter()
        .take(2)
        .map(|trained| {
            Ok((
                trained.source.ordinal,
                count_namespace(
                    &outcome.constituent,
                    occurrence_data_namespace(trained.source.ordinal)?,
                ),
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let retained_probe_words = count_namespace(
        &outcome.constituent,
        occurrence_data_namespace(occurrence.source.ordinal)?,
    );
    if retained_probe_words != occurrence.data_words.len() {
        return Err(format!("{id} lost its complete held probability field"));
    }
    Ok(ExpressionProbeRead {
        id: id.to_owned(),
        occurrence: occurrence.source.ordinal,
        derived_expression: occurrence.derived_expression.clone(),
        event: outcome.read,
        expression_face: interface_transition_read(
            &outcome.constituent,
            expression_command_interface(2, command.id),
        ),
        retained_cultivation_words,
        retained_probe_words,
    })
}

fn probe_on(
    budget: &RunBudget,
    executor: &mut ParallelCpuLiveCurrentExecutor,
    machine: &mut LiveCurrentMachine,
    occurrence: &ValidatedOccurrence<'_>,
    context: ProbeContext<'_>,
    include_expression: bool,
    source: &ValidatedSource<'_>,
    id: &str,
) -> Result<ProbeRead, String> {
    let command = source
        .command_by_text
        .get(occurrence.derived_expression.as_str())
        .copied()
        .ok_or_else(|| {
            format!(
                "derived expression {} is absent",
                occurrence.derived_expression
            )
        })?;
    let outcome = execute(
        budget,
        executor,
        machine,
        id,
        "held-field-derived-expression-context",
        probe_bundle(occurrence, command, &context, include_expression)?,
    )?;
    let selected_cross_face = interface_transition_read(
        &outcome.constituent,
        cross_face_interface(context.id(), command.id),
    );
    let all_trained_cross_faces = source
        .context_by_id
        .values()
        .map(|trained| {
            (
                trained.name.clone(),
                interface_transition_read(
                    &outcome.constituent,
                    cross_face_interface(trained.id, command.id),
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let retained_cultivation_words = source
        .occurrences
        .iter()
        .take(2)
        .map(|trained| {
            Ok((
                trained.source.ordinal,
                count_namespace(
                    &outcome.constituent,
                    occurrence_data_namespace(trained.source.ordinal)?,
                ),
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let retained_probe_words = count_namespace(
        &outcome.constituent,
        occurrence_data_namespace(occurrence.source.ordinal)?,
    );
    if retained_probe_words != occurrence.data_words.len() {
        return Err(format!("{id} lost its complete held probability field"));
    }
    Ok(ProbeRead {
        id: id.to_owned(),
        occurrence: occurrence.source.ordinal,
        derived_expression: occurrence.derived_expression.clone(),
        context: context.name().to_owned(),
        expected_consequence: context.consequence().map(|value| value.name.clone()),
        event: outcome.read,
        selected_cross_face,
        all_trained_cross_faces,
        retained_cultivation_words,
        retained_probe_words,
    })
}

fn validate_source<'a>(
    source: &'a Source,
    source_bytes: usize,
) -> Result<ValidatedSource<'a>, String> {
    if source.schema != SOURCE_SCHEMA
        || source.observation_id != OBSERVATION_ID
        || source.sample_rate != 16_000
        || source.blank_token_id != 0
        || source.vocabulary.len() != 32
        || source.commands.len() != 35
        || source.contexts.len() != 2
        || source.occurrences.len() != 4
    {
        return Err("the bounded CTC source cut changed".to_owned());
    }
    for (ordinal, vocabulary) in source.vocabulary.iter().enumerate() {
        if vocabulary.id != u32::try_from(ordinal).map_err(debug)? || vocabulary.token.is_empty() {
            return Err(
                "the inherited vocabulary is not the complete ordered 32-symbol cut".to_owned(),
            );
        }
    }
    let mut command_by_text = BTreeMap::new();
    for (ordinal, command) in source.commands.iter().enumerate() {
        if command.id != u32::try_from(ordinal + 1).map_err(debug)?
            || command.text.is_empty()
            || command.token_ids.is_empty()
            || command
                .token_ids
                .iter()
                .any(|token| *token == source.blank_token_id || *token >= 32)
            || command_by_text
                .insert(command.text.as_str(), command)
                .is_some()
        {
            return Err(format!(
                "command {} changed its lawful CTC path",
                command.text
            ));
        }
    }
    let mut context_by_id = BTreeMap::new();
    for context in &source.contexts {
        if context.id == 0
            || context.name.is_empty()
            || context.atoms.is_empty()
            || context.consequence.id == 0
            || context.consequence.name.is_empty()
            || context_by_id.insert(context.id, context).is_some()
        {
            return Err("the two trained context faces changed".to_owned());
        }
    }
    if source.untrained_context.id == 0
        || source.untrained_context.name.is_empty()
        || source.untrained_context.atoms.is_empty()
        || context_by_id.contains_key(&source.untrained_context.id)
    {
        return Err("the untrained context foil changed".to_owned());
    }

    let expected_roles = [
        ("cultivation", "training", "right", Some(1u32)),
        ("cultivation", "training", "right", Some(2u32)),
        ("held-positive", "testing", "right", None),
        ("held-foil", "testing", "left", None),
    ];
    let mut speakers = BTreeSet::new();
    let mut paths = BTreeSet::new();
    let mut occurrences = Vec::new();
    for (at, occurrence) in source.occurrences.iter().enumerate() {
        let expected = expected_roles[at];
        if occurrence.ordinal != u32::try_from(at + 1).map_err(debug)?
            || occurrence.role != expected.0
            || occurrence.partition != expected.1
            || occurrence.observer_label != expected.2
            || occurrence.context_id != expected.3
            || occurrence.sample_rate != source.sample_rate
            || occurrence.field.dtype != "ieee754-binary32-raw-u32-exact-dyadic"
            || occurrence.field.frames == 0
            || occurrence.field.alphabet != source.vocabulary.len()
            || occurrence.field.probability_words.len()
                != occurrence.field.frames * occurrence.field.alphabet
            || occurrence.field.frame_sums.len() != occurrence.field.frames
            || occurrence.fibers.len() != source.commands.len()
            || occurrence.fiber_order.len() != source.commands.len()
            || occurrence.observer_greedy_ids.len() != occurrence.field.frames
            || !occurrence.unique_winner
            || occurrence.derived_expression.as_deref() != Some(expected.2)
            || !speakers.insert(occurrence.speaker.as_str())
            || !paths.insert(occurrence.relative_path.as_str())
        {
            return Err(format!(
                "occurrence {} changed its fixed world cut",
                occurrence.ordinal
            ));
        }
        let bytes = std::fs::read(&occurrence.path)
            .map_err(|error| format!("{} reads completely: {error}", occurrence.path.display()))?;
        if sha256(&bytes) != occurrence.sha256 {
            return Err(format!(
                "{} changed its provenance hash",
                occurrence.path.display()
            ));
        }
        let wave = PcmWave::read(&occurrence.path)?;
        if wave.sample_rate != occurrence.sample_rate
            || wave.samples.len() != occurrence.samples
            || wave.samples.iter().copied().min() != Some(occurrence.pcm_min)
            || wave.samples.iter().copied().max() != Some(occurrence.pcm_max)
        {
            return Err(format!(
                "{} changed its exact PCM testimony",
                occurrence.path.display()
            ));
        }

        for frame in 0..occurrence.field.frames {
            let mut total = Dyadic::zero();
            for word in &occurrence.field.probability_words
                [frame * occurrence.field.alphabet..(frame + 1) * occurrence.field.alphabet]
            {
                total = total.add(&decode_binary32(*word)?);
            }
            if total != Dyadic::from_wire(&occurrence.field.frame_sums[frame])? {
                return Err(format!(
                    "occurrence {} frame {} changed its exact field sum",
                    occurrence.ordinal, frame
                ));
            }
        }

        let mut fibers = Vec::new();
        for (command, recorded) in source.commands.iter().zip(&occurrence.fibers) {
            let (measure, nonzero_forward_states) = ctc_measure(
                &occurrence.field.probability_words,
                occurrence.field.frames,
                occurrence.field.alphabet,
                source.blank_token_id,
                &command.token_ids,
            )?;
            if recorded.command_id != command.id
                || recorded.text != command.text
                || measure != Dyadic::from_wire(&recorded.measure)?
                || nonzero_forward_states != recorded.nonzero_forward_states
            {
                return Err(format!(
                    "occurrence {} command {} changed its exact CTC fiber",
                    occurrence.ordinal, command.text
                ));
            }
            fibers.push(RecomputedFiber {
                command_id: command.id,
                text: command.text.clone(),
                measure,
                nonzero_forward_states,
            });
        }
        let mut ordered = fibers.iter().collect::<Vec<_>>();
        ordered.sort_by(|left, right| {
            right
                .measure
                .compare(&left.measure)
                .then_with(|| left.text.cmp(&right.text))
        });
        let order = ordered
            .iter()
            .map(|fiber| fiber.text.clone())
            .collect::<Vec<_>>();
        if order != occurrence.fiber_order
            || ordered[0].measure.compare(&ordered[1].measure) != Ordering::Greater
            || occurrence.derived_expression.as_deref() != Some(ordered[0].text.as_str())
        {
            return Err(format!(
                "occurrence {} changed its exact fiber ordering",
                occurrence.ordinal
            ));
        }
        let derived_expression = ordered[0].text.clone();
        let derived_command_id = ordered[0].command_id;
        let data_words = encode_occurrence_data(occurrence, &wave, &fibers, &order, source)?;
        occurrences.push(ValidatedOccurrence {
            source: occurrence,
            wave,
            derived_command_id,
            derived_expression,
            order,
            fibers,
            data_words,
        });
    }
    for left in 0..occurrences.len() {
        for right in left + 1..occurrences.len() {
            if occurrences[left].wave.samples == occurrences[right].wave.samples {
                return Err(format!(
                    "occurrences {} and {} are not distinct acoustic worldlines",
                    left + 1,
                    right + 1
                ));
            }
        }
    }
    Ok(ValidatedSource {
        occurrences,
        command_by_text,
        context_by_id,
        source_bytes,
    })
}

fn decode_binary32(word: u32) -> Result<Dyadic, String> {
    let sign = word >> 31;
    let exponent = (word >> 23) & 0xff;
    let fraction = word & 0x7f_ffff;
    if sign != 0 {
        return Err(format!("probability word {word:#010x} is negative"));
    }
    if exponent == 0xff {
        return Err(format!("probability word {word:#010x} is nonfinite"));
    }
    if exponent == 0 {
        return Ok(Dyadic {
            numerator: BigUint::from(fraction),
            denominator_exponent: 149,
        }
        .normalized());
    }
    let significand = (1u32 << 23) | fraction;
    let power = i32::try_from(exponent).map_err(debug)? - 127 - 23;
    if power >= 0 {
        Ok(Dyadic {
            numerator: BigUint::from(significand) << usize::try_from(power).map_err(debug)?,
            denominator_exponent: 0,
        }
        .normalized())
    } else {
        Ok(Dyadic {
            numerator: BigUint::from(significand),
            denominator_exponent: u32::try_from(-power).map_err(debug)?,
        }
        .normalized())
    }
}

fn ctc_measure(
    probability_words: &[u32],
    frames: usize,
    alphabet: usize,
    blank: u32,
    labels: &[u32],
) -> Result<(Dyadic, usize), String> {
    if labels.is_empty()
        || frames == 0
        || probability_words.len() != frames * alphabet
        || usize::try_from(blank).map_err(debug)? >= alphabet
        || labels.iter().any(|label| {
            usize::try_from(*label)
                .ok()
                .is_none_or(|label| label >= alphabet)
        })
    {
        return Err("one CTC fiber has an invalid extent".to_owned());
    }
    let mut extended = Vec::with_capacity(labels.len() * 2 + 1);
    extended.push(blank);
    for label in labels {
        extended.push(*label);
        extended.push(blank);
    }
    let mut previous = vec![Dyadic::zero(); extended.len()];
    previous[0] = decode_binary32(probability_words[usize::try_from(blank).map_err(debug)?])?;
    previous[1] = decode_binary32(probability_words[usize::try_from(labels[0]).map_err(debug)?])?;
    let mut nonzero = usize::from(!previous[0].is_zero()) + usize::from(!previous[1].is_zero());
    for frame in 1..frames {
        let mut current = vec![Dyadic::zero(); extended.len()];
        let base = frame * alphabet;
        for (state, label) in extended.iter().copied().enumerate() {
            let mut incoming = previous[state].clone();
            if state >= 1 {
                incoming = incoming.add(&previous[state - 1]);
            }
            if state >= 2 && label != blank && label != extended[state - 2] {
                incoming = incoming.add(&previous[state - 2]);
            }
            current[state] =
                decode_binary32(probability_words[base + usize::try_from(label).map_err(debug)?])?
                    .multiply(&incoming)?;
            nonzero += usize::from(!current[state].is_zero());
        }
        previous = current;
    }
    Ok((
        previous[previous.len() - 1].add(&previous[previous.len() - 2]),
        nonzero,
    ))
}

fn encode_occurrence_data(
    occurrence: &SourceOccurrence,
    wave: &PcmWave,
    fibers: &[RecomputedFiber],
    order: &[String],
    source: &Source,
) -> Result<Vec<u32>, String> {
    let mut words = Vec::new();
    push_record(
        &mut words,
        1,
        &[
            occurrence.ordinal,
            u32::try_from(occurrence.field.frames).map_err(debug)?,
            u32::try_from(occurrence.field.alphabet).map_err(debug)?,
            occurrence.sample_rate,
            u32::try_from(occurrence.samples).map_err(debug)?,
            occurrence.pcm_min as u16 as u32,
            occurrence.pcm_max as u16 as u32,
        ],
    )?;
    for (ordinal, samples) in wave.samples.chunks(PCM_BLOCK).enumerate() {
        let sum = samples.iter().copied().map(i64::from).sum::<i64>();
        let sum_words = u64::from_le_bytes(sum.to_le_bytes());
        push_record(
            &mut words,
            2,
            &[
                u32::try_from(ordinal).map_err(debug)?,
                u32::try_from(ordinal * PCM_BLOCK).map_err(debug)?,
                u32::try_from((ordinal * PCM_BLOCK + samples.len()).min(wave.samples.len()))
                    .map_err(debug)?,
                sum_words as u32,
                (sum_words >> 32) as u32,
            ],
        )?;
    }
    let mut field = Vec::with_capacity(2 + occurrence.field.probability_words.len());
    field.push(u32::try_from(occurrence.field.frames).map_err(debug)?);
    field.push(u32::try_from(occurrence.field.alphabet).map_err(debug)?);
    field.extend_from_slice(&occurrence.field.probability_words);
    push_record(&mut words, 3, &field)?;
    for (frame, sum) in occurrence.field.frame_sums.iter().enumerate() {
        let value = Dyadic::from_wire(sum)?;
        let digits = value.digits_le();
        let mut payload = vec![
            u32::try_from(frame).map_err(debug)?,
            value.denominator_exponent,
            u32::try_from(digits.len()).map_err(debug)?,
        ];
        payload.extend(digits);
        push_record(&mut words, 4, &payload)?;
    }
    for fiber in fibers {
        let digits = fiber.measure.digits_le();
        let mut payload = vec![
            fiber.command_id,
            u32::try_from(fiber.nonzero_forward_states).map_err(debug)?,
            fiber.measure.denominator_exponent,
            u32::try_from(digits.len()).map_err(debug)?,
        ];
        payload.extend(digits);
        push_record(&mut words, 5, &payload)?;
    }
    let ordered_ids = order
        .iter()
        .map(|text| {
            source
                .commands
                .iter()
                .find(|command| &command.text == text)
                .map(|command| command.id)
                .ok_or_else(|| format!("ordered command {text} is absent"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    push_record(&mut words, 6, &ordered_ids)?;
    Ok(words)
}

fn push_record(words: &mut Vec<u32>, tag: u32, payload: &[u32]) -> Result<(), String> {
    words.push(tag);
    words.push(u32::try_from(payload.len()).map_err(debug)?);
    words.extend_from_slice(payload);
    Ok(())
}

fn field_bundle(occurrence: &ValidatedOccurrence<'_>) -> Result<EventBundle, String> {
    let mut bundle = EventBundle::new();
    let data = occurrence
        .data_words
        .iter()
        .copied()
        .enumerate()
        .map(|(address, word)| {
            Ok((
                word,
                InterfaceCapability::new(
                    occurrence_data_namespace(occurrence.source.ordinal)?,
                    address_word(address, word)?,
                ),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let data_slots = append_group(&mut bundle, &data)?;
    bundle.section_slots.push(data_slots);
    let link_slots = append_group(
        &mut bundle,
        &[(
            occurrence.source.ordinal,
            occurrence_link_interface(occurrence.source.ordinal),
        )],
    )?;
    bundle.section_slots.push(link_slots);
    bundle.data_words = occurrence.data_words.len();
    bundle.validate()?;
    Ok(bundle)
}

fn return_bundle(
    occurrence: u32,
    command: &SourceCommand,
    context: &SourceContext,
) -> Result<EventBundle, String> {
    let mut bundle = EventBundle::new();
    let link_slots = append_group(
        &mut bundle,
        &[(occurrence, occurrence_link_interface(occurrence))],
    )?;
    bundle.section_slots.push(link_slots);
    let incoming_expression_slots =
        append_expression(&mut bundle, command, occurrence.saturating_sub(1))?;
    bundle.section_slots.push(incoming_expression_slots);
    let outgoing_expression_slots = append_expression(&mut bundle, command, occurrence)?;
    bundle.section_slots.push(outgoing_expression_slots);
    let context_slots = append_context(
        &mut bundle,
        context.id,
        &context.atoms,
        command.id,
        Some(&context.consequence),
    )?;
    bundle.section_slots.push(context_slots);
    bundle.validate()?;
    Ok(bundle)
}

fn probe_bundle(
    occurrence: &ValidatedOccurrence<'_>,
    command: &SourceCommand,
    context: &ProbeContext<'_>,
    include_expression: bool,
) -> Result<EventBundle, String> {
    let mut bundle = EventBundle::new();
    let data = occurrence
        .data_words
        .iter()
        .copied()
        .enumerate()
        .map(|(address, word)| {
            Ok((
                word,
                InterfaceCapability::new(
                    occurrence_data_namespace(occurrence.source.ordinal)?,
                    address_word(address, word)?,
                ),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let data_slots = append_group(&mut bundle, &data)?;
    bundle.section_slots.push(data_slots);
    if include_expression {
        let expression_slots = append_expression(&mut bundle, command, 2)?;
        bundle.section_slots.push(expression_slots);
    }
    let context_slots =
        append_context(&mut bundle, context.id(), context.atoms(), command.id, None)?;
    bundle.section_slots.push(context_slots);
    bundle.data_words = occurrence.data_words.len();
    bundle.validate()?;
    Ok(bundle)
}

fn expression_probe_bundle(
    occurrence: &ValidatedOccurrence<'_>,
    command: &SourceCommand,
) -> Result<EventBundle, String> {
    let mut bundle = EventBundle::new();
    let data = occurrence
        .data_words
        .iter()
        .copied()
        .enumerate()
        .map(|(address, word)| {
            Ok((
                word,
                InterfaceCapability::new(
                    occurrence_data_namespace(occurrence.source.ordinal)?,
                    address_word(address, word)?,
                ),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let data_slots = append_group(&mut bundle, &data)?;
    bundle.section_slots.push(data_slots);
    let expression_slots = append_expression(&mut bundle, command, 2)?;
    bundle.section_slots.push(expression_slots);
    bundle.data_words = occurrence.data_words.len();
    bundle.validate()?;
    Ok(bundle)
}

impl EventBundle {
    fn new() -> Self {
        Self {
            charts: Vec::new(),
            arcs: Vec::new(),
            section_slots: Vec::new(),
            receiver: 0,
            data_words: 0,
        }
    }

    fn validate(&self) -> Result<(), String> {
        if self.charts.is_empty()
            || self.arcs.is_empty()
            || self.section_slots.is_empty()
            || self.receiver >= self.charts.len()
        {
            return Err("one event bundle has an empty regional cut".to_owned());
        }
        let mut covered = vec![false; self.arcs.len()];
        for section in &self.section_slots {
            if section.is_empty() {
                return Err("one event bundle has an empty support section".to_owned());
            }
            for slot in section {
                let at = usize::try_from(*slot).map_err(debug)?;
                *covered
                    .get_mut(at)
                    .ok_or_else(|| "one support slot is outside the regional cut".to_owned())? =
                    true;
            }
        }
        if covered.iter().any(|covered| !covered) {
            return Err(
                "one event bundle leaves a boundary outside every support section".to_owned(),
            );
        }
        Ok(())
    }
}

fn append_expression(
    bundle: &mut EventBundle,
    command: &SourceCommand,
    phase: u32,
) -> Result<Vec<u32>, String> {
    let mut entries = vec![(command.id, expression_command_interface(phase, command.id))];
    for (position, token) in command.token_ids.iter().copied().enumerate() {
        entries.push((
            token,
            InterfaceCapability::new(
                NS_EXPRESSION_SYMBOL,
                expression_symbol_local(phase, position, token)?,
            ),
        ));
    }
    append_group(bundle, &entries)
}

fn append_context(
    bundle: &mut EventBundle,
    context_id: u32,
    atoms: &[u32],
    command_id: u32,
    consequence: Option<&SourceConsequence>,
) -> Result<Vec<u32>, String> {
    let mut entries = vec![(
        context_id,
        InterfaceCapability::new(NS_CONTEXT_IDENTITY, u64::from(context_id)),
    )];
    for (position, atom) in atoms.iter().copied().enumerate() {
        entries.push((
            atom,
            InterfaceCapability::new(NS_CONTEXT_ATOM, address_word(position, atom)?),
        ));
    }
    entries.push((command_id, cross_face_interface(context_id, command_id)));
    if let Some(consequence) = consequence {
        entries.push((
            consequence.id,
            InterfaceCapability::new(NS_CONSEQUENCE, u64::from(consequence.id)),
        ));
    }
    append_group(bundle, &entries)
}

fn append_group(
    bundle: &mut EventBundle,
    entries: &[(u32, InterfaceCapability)],
) -> Result<Vec<u32>, String> {
    if entries.is_empty() {
        return Err("a regional group cannot be empty".to_owned());
    }
    let values = std::iter::once(0i64)
        .chain(entries.iter().map(|(word, _)| i64::from(*word)))
        .collect::<Vec<_>>();
    let coordinates = (0..values.len())
        .map(|value| i64::try_from(value).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let left = bundle.charts.len();
    bundle.charts.push(ExactPathChart::new(&values)?);
    let right = bundle.charts.len();
    bundle.charts.push(ExactPathChart::new(&coordinates)?);
    let mut slots = Vec::with_capacity(entries.len());
    for (position, (_, interface)) in entries.iter().enumerate() {
        let slot = u32::try_from(bundle.arcs.len()).map_err(debug)?;
        let port = u32::try_from(position).map_err(debug)?;
        bundle.arcs.push(NativeRegionalArc::new(
            left,
            CurrentBoundaryPort::Exposed(port),
            right,
            CurrentBoundaryPort::Exposed(port),
            interface.clone(),
            slot,
            0,
            IncidenceHand::Against,
        ));
        slots.push(slot);
    }
    Ok(slots)
}

fn occurrence_data_namespace(ordinal: u32) -> Result<u64, String> {
    NS_OCCURRENCE_DATA_BASE
        .checked_add(u64::from(ordinal))
        .ok_or_else(|| "the occurrence data namespace overflowed".to_owned())
}

fn occurrence_link_interface(ordinal: u32) -> InterfaceCapability {
    InterfaceCapability::new(NS_OCCURRENCE_LINK, u64::from(ordinal))
}

fn expression_command_interface(phase: u32, command: u32) -> InterfaceCapability {
    InterfaceCapability::new(
        NS_EXPRESSION_COMMAND,
        (u64::from(phase) << 32) | u64::from(command),
    )
}

fn cross_face_interface(context: u32, command: u32) -> InterfaceCapability {
    InterfaceCapability::new(
        NS_CROSS_FACE,
        (u64::from(context) << 32) | u64::from(command),
    )
}

fn address_word(address: usize, word: u32) -> Result<u64, String> {
    Ok((u64::from(u32::try_from(address).map_err(debug)?) << 32) | u64::from(word))
}

fn expression_symbol_local(phase: u32, position: usize, token: u32) -> Result<u64, String> {
    let position = u16::try_from(position).map_err(debug)?;
    let token = u16::try_from(token).map_err(debug)?;
    Ok((u64::from(phase) << 32) | (u64::from(position) << 16) | u64::from(token))
}

fn execute(
    budget: &RunBudget,
    executor: &mut ParallelCpuLiveCurrentExecutor,
    machine: &mut LiveCurrentMachine,
    id: &str,
    role: &str,
    bundle: EventBundle,
) -> Result<EventOutcome, String> {
    budget.require_open()?;
    bundle.validate()?;
    let prior = machine.standing().constituents().to_vec();
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
    let started = Instant::now();
    let radiation =
        present_native_event_with_regional(machine, executor, &mut currents, &[], &regional)
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
    Ok(EventOutcome {
        read: EventRead {
            id: id.to_owned(),
            role: role.to_owned(),
            currents: bundle.charts.len(),
            arcs: bundle.arcs.len(),
            support_sections: bundle.section_slots.len(),
            data_words: bundle.data_words,
            contacts: contact_read(relation.arcs()),
            before,
            after: memory_read(machine.memory()),
            emitted: shape_read(&constituent),
            elapsed_microseconds: elapsed.as_micros(),
        },
        constituent,
        prior,
    })
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

fn count_namespace(constituent: &LiveConstituent, namespace: u64) -> usize {
    constituent
        .exposed()
        .iter()
        .filter_map(|pin| constituent.pins().get(*pin as usize))
        .filter_map(|pin| pin.interface())
        .filter(|interface| interface.namespace() == namespace)
        .count()
}

fn fiber_summary(occurrence: &ValidatedOccurrence<'_>) -> FiberSummary {
    FiberSummary {
        occurrence: occurrence.source.ordinal,
        role: occurrence.source.role.clone(),
        partition: occurrence.source.partition.clone(),
        speaker: occurrence.source.speaker.clone(),
        relative_path: occurrence.source.relative_path.clone(),
        frames: occurrence.source.field.frames,
        alphabet: occurrence.source.field.alphabet,
        probability_words: occurrence.source.field.probability_words.len(),
        pcm_blocks: occurrence.wave.samples.chunks(PCM_BLOCK).len(),
        derived_expression: occurrence.derived_expression.clone(),
        unique_winner: occurrence.source.unique_winner,
        top_five: occurrence.order.iter().take(5).cloned().collect(),
        observer_greedy_text: occurrence.source.observer_greedy_text.clone(),
        greedy_agrees_with_complete_fiber: occurrence.source.observer_greedy_text.to_lowercase()
            == occurrence.derived_expression,
        exact_measure_numerator_bits: occurrence
            .fibers
            .iter()
            .map(|fiber| usize::try_from(fiber.measure.numerator.bits()).unwrap_or(usize::MAX))
            .collect(),
        exact_forward_states: occurrence
            .fibers
            .iter()
            .map(|fiber| fiber.nonzero_forward_states)
            .collect(),
    }
}

fn command_text(source: &Source, id: u32) -> Result<&str, String> {
    source
        .commands
        .iter()
        .find(|command| command.id == id)
        .map(|command| command.text.as_str())
        .ok_or_else(|| format!("command {id} is absent"))
}

fn probe_named<'a>(probes: &'a [ProbeRead], id: &str) -> Result<&'a ProbeRead, String> {
    probes
        .iter()
        .find(|probe| probe.id == id)
        .ok_or_else(|| format!("probe {id} is absent"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving CTC path-fiber action")
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
