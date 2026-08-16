use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage, LiveMemory,
    RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_retriangulating_branch_transport/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_retriangulating_branch_transport";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";

const SOURCE_SCHEMA: &str = "eros.retriangulating-branch-transport.source.v1";
const REPORT_SCHEMA: &str = "eros.retriangulating-branch-transport.report.v1";
const OBSERVATION_ID: &str = "eros-retriangulating-branch-transport-01";
const COMPACT_SCHEMA: u64 = 1;
const RECRUIT_LOCAL: u64 = 0;
const EVENT_LIMIT: Duration = Duration::from_secs(30);
const RUN_LIMIT: Duration = Duration::from_secs(120);
const MAX_ARCS_PER_EVENT: usize = 256;
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];

const PROGRAM_SCHEMA: u64 = 1;
const PROGRAM_NODE_COUNT: u64 = 2;
const PROGRAM_OUTPUT: u64 = 3;
const PROGRAM_NODE_KIND: u64 = 10;
const PROGRAM_NODE_ROLE: u64 = 11;
const PROGRAM_NODE_LEFT: u64 = 12;
const PROGRAM_NODE_RIGHT: u64 = 13;

const QUOTIENT_SCHEMA: u64 = 101;
const QUOTIENT_CHI_SIGN: u64 = 110;
const QUOTIENT_CHI_MAGNITUDE: u64 = 111;
const QUOTIENT_CHI_DENOMINATOR: u64 = 112;
const QUOTIENT_OUTPUT_SIGN: u64 = 120;
const QUOTIENT_OUTPUT_MAGNITUDE: u64 = 121;
const QUOTIENT_OUTPUT_DENOMINATOR: u64 = 122;

const INPUT_SCHEMA: u64 = 201;
const INPUT_ORDINAL: u64 = 202;
const INPUT_VALUE_SIGN: u64 = 210;
const INPUT_VALUE_MAGNITUDE: u64 = 211;
const INPUT_VALUE_DENOMINATOR: u64 = 212;

const RESULT_SCHEMA: u64 = 301;
const RESULT_VALUE_SIGN: u64 = 310;
const RESULT_VALUE_MAGNITUDE: u64 = 311;
const RESULT_VALUE_DENOMINATOR: u64 = 312;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    question: String,
    program: SourceProgram,
    source_occurrence: SourceOccurrence,
    quotient: SourceQuotient,
    cases: Vec<SourceCase>,
    physical_preflight: PhysicalPreflight,
    stopping_condition: String,
}

#[derive(Clone, Deserialize)]
struct SourceProgram {
    name: String,
    output: usize,
    nodes: Vec<SourceNode>,
    domain: String,
    relation: String,
}

#[derive(Clone, Deserialize)]
struct SourceNode {
    op: String,
    #[serde(default)]
    role: Option<String>,
    #[serde(default)]
    left: Option<usize>,
    #[serde(default)]
    right: Option<usize>,
}

#[derive(Deserialize)]
struct SourceOccurrence {
    chart: String,
    values: Vec<String>,
    path: Vec<String>,
    output: String,
}

#[derive(Deserialize)]
struct SourceQuotient {
    retains: Vec<String>,
    chi: String,
    source_output: String,
    forgets: Vec<String>,
}

#[derive(Clone, Deserialize)]
struct SourceCase {
    id: String,
    group: String,
    chart: String,
    source_role_order: Vec<String>,
    values: Vec<String>,
    expected_path: Vec<String>,
    expected_output: Option<String>,
    expected_condition: String,
}

#[derive(Deserialize)]
struct PhysicalPreflight {
    executor: String,
    event_limit_seconds: u64,
    run_limit_seconds: u64,
    maximum_regional_arcs_per_event: usize,
    floating_point_causal_data: bool,
    cuda: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Rational {
    numerator: i128,
    denominator: i128,
}

impl Rational {
    fn new(numerator: i128, denominator: i128) -> Result<Self, String> {
        if denominator == 0 {
            return Err("an exact rational denominator is zero".to_owned());
        }
        let mut numerator = numerator;
        let mut denominator = denominator;
        if denominator < 0 {
            numerator = numerator
                .checked_neg()
                .ok_or_else(|| "rational numerator sign normalization overflowed".to_owned())?;
            denominator = denominator
                .checked_neg()
                .ok_or_else(|| "rational denominator sign normalization overflowed".to_owned())?;
        }
        let divisor = gcd(
            numerator
                .checked_abs()
                .ok_or_else(|| "rational numerator magnitude overflowed".to_owned())?,
            denominator,
        );
        Ok(Self {
            numerator: numerator / divisor,
            denominator: denominator / divisor,
        })
    }

    fn checked_add(self, other: Self) -> Result<Self, String> {
        let left = self
            .numerator
            .checked_mul(other.denominator)
            .ok_or_else(|| "exact addition left product overflowed".to_owned())?;
        let right = other
            .numerator
            .checked_mul(self.denominator)
            .ok_or_else(|| "exact addition right product overflowed".to_owned())?;
        let numerator = left
            .checked_add(right)
            .ok_or_else(|| "exact addition numerator overflowed".to_owned())?;
        let denominator = self
            .denominator
            .checked_mul(other.denominator)
            .ok_or_else(|| "exact addition denominator overflowed".to_owned())?;
        Self::new(numerator, denominator)
    }

    fn checked_mul(self, other: Self) -> Result<Self, String> {
        Self::new(
            self.numerator
                .checked_mul(other.numerator)
                .ok_or_else(|| "exact multiplication numerator overflowed".to_owned())?,
            self.denominator
                .checked_mul(other.denominator)
                .ok_or_else(|| "exact multiplication denominator overflowed".to_owned())?,
        )
    }

    fn checked_div(self, other: Self) -> Result<Self, String> {
        if other.numerator == 0 {
            return Err("division by the presented zero divisor is OPEN".to_owned());
        }
        Self::new(
            self.numerator
                .checked_mul(other.denominator)
                .ok_or_else(|| "exact division numerator overflowed".to_owned())?,
            self.denominator
                .checked_mul(other.numerator)
                .ok_or_else(|| "exact division denominator overflowed".to_owned())?,
        )
    }

    fn encode(self) -> Result<(u64, u64, u64), String> {
        let sign = if self.numerator < 0 {
            2
        } else if self.numerator == 0 {
            0
        } else {
            1
        };
        let magnitude = u64::try_from(
            self.numerator
                .checked_abs()
                .ok_or_else(|| "exact numerator magnitude overflowed".to_owned())?,
        )
        .map_err(debug)?;
        let denominator = u64::try_from(self.denominator).map_err(debug)?;
        Ok((sign, magnitude, denominator))
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.denominator == 1 {
            write!(formatter, "{}", self.numerator)
        } else {
            write!(formatter, "{}/{}", self.numerator, self.denominator)
        }
    }
}

fn gcd(mut left: i128, mut right: i128) -> i128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left.max(1)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ProgramNode {
    Input(usize),
    Multiply(usize, usize),
    Add(usize, usize),
    Divide(usize, usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Program {
    output: usize,
    nodes: Vec<ProgramNode>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Quotient {
    chi: Rational,
    source_output: Rational,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Input {
    ordinal: usize,
    values: Vec<Rational>,
}

#[derive(Clone, Debug)]
struct CompactWord {
    tag: u64,
    coordinates: Vec<u64>,
    value: u64,
}

impl CompactWord {
    fn scalar(tag: u64, value: u64) -> Self {
        Self {
            tag,
            coordinates: Vec::new(),
            value,
        }
    }

    fn at(tag: u64, coordinates: impl Into<Vec<u64>>, value: u64) -> Self {
        Self {
            tag,
            coordinates: coordinates.into(),
            value,
        }
    }

    fn interface(&self, root: u64) -> InterfaceCapability {
        InterfaceCapability::new(compact_route_namespace(root, self), self.value)
    }
}

struct CapabilityAtlas {
    values: BTreeMap<u64, BTreeSet<u64>>,
}

impl CapabilityAtlas {
    fn from_constituent(constituent: &LiveConstituent) -> Result<Self, String> {
        let mut values: BTreeMap<u64, BTreeSet<u64>> = BTreeMap::new();
        for pin_at in constituent.exposed().iter().copied() {
            let interface = constituent
                .pins()
                .get(pin_at as usize)
                .and_then(|pin| pin.interface())
                .ok_or_else(|| "one exposed compact pin has no interface".to_owned())?;
            values
                .entry(interface.namespace())
                .or_default()
                .insert(interface.local());
        }
        Ok(Self { values })
    }

    fn word(&self, root: u64, tag: u64, coordinates: &[u64]) -> Result<u64, String> {
        let route = CompactWord::at(tag, coordinates.to_vec(), 0);
        let namespace = compact_route_namespace(root, &route);
        match self.values.get(&namespace) {
            Some(values) if values.len() == 1 => Ok(*values.first().unwrap()),
            Some(_) => Err(format!(
                "compact route {tag}:{coordinates:?} exposes plural values"
            )),
            None => Err(format!("compact route {tag}:{coordinates:?} is absent")),
        }
    }
}

#[derive(Clone, Copy)]
struct ArtifactHandle {
    data_namespace: u64,
    recruit_namespace: u64,
}

impl ArtifactHandle {
    fn new(kind: &[u8], source_sha256: &str) -> Self {
        Self {
            data_namespace: namespace(&[
                b"eros-retriangulating-branch-transport-data-v1",
                kind,
                source_sha256.as_bytes(),
            ]),
            recruit_namespace: namespace(&[
                b"eros-retriangulating-branch-transport-recruit-v1",
                kind,
                source_sha256.as_bytes(),
            ]),
        }
    }
}

struct StandingCarrier {
    rest: LiveCurrentRestImage,
    event: EventRead,
    rest_sha256: String,
    live_lineages: usize,
}

#[derive(Serialize)]
struct EventRead {
    event: String,
    semantic_words: usize,
    regional_arcs: usize,
    wall_micros: u64,
    returned_incidences: usize,
    returned_pins: usize,
}

#[derive(Serialize)]
struct NodeRead {
    node: usize,
    operation: String,
    antecedents: Vec<usize>,
    value: String,
}

#[derive(Serialize)]
struct EvaluationRead {
    condition: String,
    complete_path: Vec<NodeRead>,
    output: Option<String>,
    open_at_node: Option<usize>,
    open_reason: Option<String>,
}

#[derive(Serialize)]
struct ComparisonRead {
    capabilities: usize,
    rides: usize,
    opens: usize,
    founds: usize,
    exact_ride: bool,
}

#[derive(Serialize)]
struct CaseRead {
    id: String,
    group: String,
    chart: String,
    source_role_order: Vec<String>,
    input_values: Vec<String>,
    expected_path: Vec<String>,
    expected_output: Option<String>,
    complete_carrier_recovered_from_standing: bool,
    current_recovered_from_source: bool,
    evaluation: EvaluationRead,
    result_returned_as_later_current: bool,
    returned_result: Option<String>,
    result_comparison: Option<ComparisonRead>,
    events: Vec<EventRead>,
}

#[derive(Serialize)]
struct ControlRead {
    name: String,
    complete_program_recovered: bool,
    quotient_recovered: bool,
    current_recovered: bool,
    output_formed: bool,
    reason: String,
    event: EventRead,
}

#[derive(Serialize)]
struct CarrierRead {
    source_program_name: String,
    source_relation: String,
    source_domain: String,
    source_chart: String,
    source_values: Vec<String>,
    source_path: Vec<String>,
    source_output: String,
    program_words: usize,
    program_returned_exactly: bool,
    program_survived_exact_rest_remount: bool,
    program_source_lineages_departed: bool,
    program_event: EventRead,
    program_rest_sha256: String,
    quotient_retains: Vec<String>,
    quotient_chi: String,
    quotient_source_output: String,
    quotient_forgets: Vec<String>,
    quotient_words: usize,
    quotient_returned_exactly: bool,
    quotient_survived_exact_rest_remount: bool,
    quotient_source_lineages_departed: bool,
    quotient_event: EventRead,
    quotient_rest_sha256: String,
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
}

#[derive(Serialize)]
struct AcceptanceRead {
    source_validated: bool,
    exact_program_stood_after_source_departure: bool,
    exact_quotient_stood_after_source_departure: bool,
    every_closed_case_carried_complete_path_and_exact_result: bool,
    zero_diagonal_stayed_open_at_the_division_seam: bool,
    quotient_foil_recovered_its_face_but_could_not_form_the_changed_scale_result: bool,
    no_standing_control_could_not_form_output: bool,
    every_returned_result_rode_against_its_exact_expected_face: bool,
    world_side_interpreter_remains_explicit: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: String,
    theory_to_structure: &'static str,
    stopping_condition: String,
    source_sha256: String,
    physical_preflight: PreflightRead,
    carriers: CarrierRead,
    cases: Vec<CaseRead>,
    quotient_control: ControlRead,
    no_standing_control: ControlRead,
    final_complete_machine: MachineRead,
    acceptance: AcceptanceRead,
    run_wall_micros: u64,
    conclusion: &'static str,
}

#[derive(Serialize)]
struct PreflightRead {
    executor: String,
    event_limit_seconds: u64,
    run_limit_seconds: u64,
    maximum_regional_arcs_per_event: usize,
    floating_point_causal_data: bool,
    cuda: bool,
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
            Err("the bounded retriangulating-branch run exceeded two minutes".to_owned())
        } else {
            Ok(())
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros retriangulating branch transport: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(|| usage().to_owned())?);
    let report_path = PathBuf::from(arguments.next().ok_or_else(|| usage().to_owned())?);
    if arguments.next().is_some() {
        return Err(usage().to_owned());
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads: {error}", source_path.display()))?;
    let source_sha256 = sha256(&source_bytes);
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} parses: {error}", source_path.display()))?;
    let report = run_cpu(source, source_sha256)?;
    let mut report_bytes = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("retriangulating-branch report encodes: {error}"))?;
    report_bytes.push(b'\n');
    let mut output = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&report_path)
        .map_err(|error| format!("{} opens as a new report: {error}", report_path.display()))?;
    output
        .write_all(&report_bytes)
        .map_err(|error| format!("{} writes completely: {error}", report_path.display()))?;
    output
        .sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", report_path.display()))?;
    eprintln!(
        "eros retriangulating branch transport: {} · {} bytes · {}",
        report.status,
        report_bytes.len(),
        report_path.display()
    );
    Ok(())
}

fn run_cpu(source: Source, source_sha256: String) -> Result<Report, String> {
    let started = Instant::now();
    validate_source(&source)?;
    let budget = RunBudget::new();
    let program = source_program(&source.program)?;
    let quotient = Quotient {
        chi: parse_ratio(&source.quotient.chi)?,
        source_output: parse_ratio(&source.quotient.source_output)?,
    };
    let program_words = program_words(&program);
    let quotient_words = quotient_words(quotient)?;
    let program_handle = ArtifactHandle::new(b"complete-program", &source_sha256);
    let quotient_handle = ArtifactHandle::new(b"quotient-face", &source_sha256);
    let program_carrier = seed_carrier(
        &budget,
        "complete-program-source",
        program_handle,
        &program_words,
    )?;
    let quotient_carrier =
        seed_carrier(&budget, "quotient-source", quotient_handle, &quotient_words)?;

    let remounted_program =
        LiveCurrentMachine::from_rest_image(program_carrier.rest.clone()).map_err(debug)?;
    let remounted_quotient =
        LiveCurrentMachine::from_rest_image(quotient_carrier.rest.clone()).map_err(debug)?;
    let program_returned_exactly =
        standing_program(&remounted_program, program_handle.data_namespace)? == program;
    let quotient_returned_exactly =
        standing_quotient(&remounted_quotient, quotient_handle.data_namespace)? == quotient;
    let program_survived = remounted_program.rest_image().map_err(debug)? == program_carrier.rest;
    let quotient_survived =
        remounted_quotient.rest_image().map_err(debug)? == quotient_carrier.rest;

    let mut cases = Vec::with_capacity(source.cases.len());
    let mut last_complete_machine = remounted_program;
    for (ordinal, source_case) in source.cases.iter().enumerate() {
        let (read, machine) = run_case(
            &budget,
            &program_carrier.rest,
            program_handle,
            &program,
            ordinal,
            source_case,
            &source_sha256,
        )?;
        cases.push(read);
        last_complete_machine = machine;
    }

    let control_case = source
        .cases
        .iter()
        .find(|case| case.id == "uniform-scale-two")
        .ok_or_else(|| "the fixed scaled control case is absent".to_owned())?;
    let quotient_control = run_quotient_control(
        &budget,
        &quotient_carrier.rest,
        quotient_handle,
        quotient,
        control_case,
        &source_sha256,
    )?;
    let no_standing_control =
        run_no_standing_control(&budget, program_handle, control_case, &source_sha256)?;

    let closed_exact = cases
        .iter()
        .filter(|case| case.group == "heldout")
        .all(|case| {
            case.complete_carrier_recovered_from_standing
                && case.current_recovered_from_source
                && case.evaluation.condition == "closed"
                && case.evaluation.output == case.expected_output
                && case.result_returned_as_later_current
                && case.returned_result == case.expected_output
                && case
                    .result_comparison
                    .as_ref()
                    .is_some_and(|comparison| comparison.exact_ride)
        });
    let zero_open = cases
        .iter()
        .find(|case| case.id == "zero-diagonal-seam")
        .is_some_and(|case| {
            case.evaluation.condition == "open"
                && case.evaluation.open_at_node == Some(8)
                && case.evaluation.output.is_none()
                && !case.result_returned_as_later_current
        });
    let all_comparisons_ride = cases
        .iter()
        .filter_map(|case| case.result_comparison.as_ref())
        .all(|comparison| comparison.exact_ride);
    let acceptance = AcceptanceRead {
        source_validated: true,
        exact_program_stood_after_source_departure: program_returned_exactly
            && program_survived
            && program_carrier.live_lineages == 0,
        exact_quotient_stood_after_source_departure: quotient_returned_exactly
            && quotient_survived
            && quotient_carrier.live_lineages == 0,
        every_closed_case_carried_complete_path_and_exact_result: closed_exact,
        zero_diagonal_stayed_open_at_the_division_seam: zero_open,
        quotient_foil_recovered_its_face_but_could_not_form_the_changed_scale_result:
            quotient_control.quotient_recovered
                && !quotient_control.complete_program_recovered
                && !quotient_control.output_formed,
        no_standing_control_could_not_form_output: !no_standing_control.complete_program_recovered
            && !no_standing_control.output_formed,
        every_returned_result_rode_against_its_exact_expected_face: all_comparisons_ride,
        world_side_interpreter_remains_explicit: true,
        no_floating_point_causal_data: true,
    };
    let accepted = acceptance.source_validated
        && acceptance.exact_program_stood_after_source_departure
        && acceptance.exact_quotient_stood_after_source_departure
        && acceptance.every_closed_case_carried_complete_path_and_exact_result
        && acceptance.zero_diagonal_stayed_open_at_the_division_seam
        && acceptance.quotient_foil_recovered_its_face_but_could_not_form_the_changed_scale_result
        && acceptance.no_standing_control_could_not_form_output
        && acceptance.every_returned_result_rode_against_its_exact_expected_face
        && acceptance.world_side_interpreter_remains_explicit
        && acceptance.no_floating_point_causal_data;
    if !accepted {
        return Err("the retriangulating-branch acceptance did not close".to_owned());
    }
    budget.require_open()?;

    Ok(Report {
        schema: REPORT_SCHEMA,
        status: "accepted",
        question: source.question,
        theory_to_structure: "The source declares one finite multiply-multiply-add-divide relation over five ordered local roles. That exact program and a matched cross-ratio-plus-endpoint quotient cross separate Soma worlds as regional incidence, rest after their source lineages end, and are recruited by later quadrilateral currents. A generic exact world transducer evaluates only a recovered program, returns its complete node path and alternate diagonal as genuinely later current, and asks Soma to compare that result with the independently declared receiver. Uniform scale, cyclic rechart, their composition, a rational receiver, and the e=0 seam are all held apart.",
        stopping_condition: source.stopping_condition,
        source_sha256,
        physical_preflight: PreflightRead {
            executor: source.physical_preflight.executor,
            event_limit_seconds: source.physical_preflight.event_limit_seconds,
            run_limit_seconds: source.physical_preflight.run_limit_seconds,
            maximum_regional_arcs_per_event: source
                .physical_preflight
                .maximum_regional_arcs_per_event,
            floating_point_causal_data: source.physical_preflight.floating_point_causal_data,
            cuda: source.physical_preflight.cuda,
        },
        carriers: CarrierRead {
            source_program_name: source.program.name,
            source_relation: source.program.relation,
            source_domain: source.program.domain,
            source_chart: source.source_occurrence.chart,
            source_values: source.source_occurrence.values,
            source_path: source.source_occurrence.path,
            source_output: source.source_occurrence.output,
            program_words: program_words.len(),
            program_returned_exactly,
            program_survived_exact_rest_remount: program_survived,
            program_source_lineages_departed: program_carrier.live_lineages == 0,
            program_event: program_carrier.event,
            program_rest_sha256: program_carrier.rest_sha256,
            quotient_retains: source.quotient.retains,
            quotient_chi: source.quotient.chi,
            quotient_source_output: source.quotient.source_output,
            quotient_forgets: source.quotient.forgets,
            quotient_words: quotient_words.len(),
            quotient_returned_exactly,
            quotient_survived_exact_rest_remount: quotient_survived,
            quotient_source_lineages_departed: quotient_carrier.live_lineages == 0,
            quotient_event: quotient_carrier.event,
            quotient_rest_sha256: quotient_carrier.rest_sha256,
        },
        cases,
        quotient_control,
        no_standing_control,
        final_complete_machine: machine_read(&last_complete_machine),
        acceptance,
        run_wall_micros: duration_micros(started.elapsed()),
        conclusion: "The complete carrier and its quotient are not interchangeable. The exact program survives source departure and supplies every later multiply-add-divide path across scale, cyclic rechart, and a rational receiver; e=0 remains an explicit OPEN seam. The quotient retains the original cross-ratio and endpoint but cannot form the scaled result because it discarded metric scale, divisor, and composition. The remaining boundary is equally exact: Soma carries and recruits the program, but the generic world transducer still interprets it and returns the consequence. This cell therefore establishes consequential carriage and isolates direct algorithmic enactment as the next engine question; it does not claim that enactment already exists.",
    })
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA || source.observation_id != OBSERVATION_ID {
        return Err(format!(
            "source identity changed: schema={:?}, observation={:?}",
            source.schema, source.observation_id
        ));
    }
    if source.program.nodes.len() != 9
        || source.program.output != 8
        || source.source_occurrence.values.len() != 5
        || source.cases.len() != 5
    {
        return Err("the fixed finite program or case extent changed".to_owned());
    }
    if source.physical_preflight.executor != "bounded cpu"
        || source.physical_preflight.event_limit_seconds != EVENT_LIMIT.as_secs()
        || source.physical_preflight.run_limit_seconds != RUN_LIMIT.as_secs()
        || source.physical_preflight.maximum_regional_arcs_per_event != MAX_ARCS_PER_EVENT
        || source.physical_preflight.floating_point_causal_data
        || source.physical_preflight.cuda
    {
        return Err("the fixed physical preflight changed".to_owned());
    }
    let program = source_program(&source.program)?;
    let source_input = Input {
        ordinal: 0,
        values: source
            .source_occurrence
            .values
            .iter()
            .map(|value| parse_ratio(value))
            .collect::<Result<_, _>>()?,
    };
    let source_evaluation = evaluate(&program, &source_input);
    if source_evaluation.output != Some(parse_ratio(&source.source_occurrence.output)?)
        || source_evaluation.condition != "closed"
    {
        return Err("the declared source occurrence does not enact its program".to_owned());
    }
    let quotient = Quotient {
        chi: parse_ratio(&source.quotient.chi)?,
        source_output: parse_ratio(&source.quotient.source_output)?,
    };
    let ac = source_input.values[0].checked_mul(source_input.values[2])?;
    let bd = source_input.values[1].checked_mul(source_input.values[3])?;
    if ac.checked_div(bd)? != quotient.chi
        || source_evaluation.output != Some(quotient.source_output)
    {
        return Err("the declared quotient does not match the source occurrence".to_owned());
    }
    for (ordinal, case) in source.cases.iter().enumerate() {
        if case.values.len() != 5
            || case.source_role_order.len() != 5
            || !matches!(case.expected_condition.as_str(), "closed" | "open")
        {
            return Err(format!("case {} changed its local boundary", case.id));
        }
        let input = Input {
            ordinal,
            values: case
                .values
                .iter()
                .map(|value| parse_ratio(value))
                .collect::<Result<_, _>>()?,
        };
        let evaluation = evaluate(&program, &input);
        let expected = case
            .expected_output
            .as_deref()
            .map(parse_ratio)
            .transpose()?;
        if evaluation.condition != case.expected_condition || evaluation.output != expected {
            return Err(format!(
                "case {} disagrees with the independent source derivation",
                case.id
            ));
        }
    }
    Ok(())
}

fn source_program(source: &SourceProgram) -> Result<Program, String> {
    let roles = ["a", "b", "c", "d", "e"];
    let mut nodes = Vec::with_capacity(source.nodes.len());
    for (at, node) in source.nodes.iter().enumerate() {
        let parsed = match node.op.as_str() {
            "input" => {
                let role = node
                    .role
                    .as_deref()
                    .ok_or_else(|| format!("input node {at} has no role"))?;
                let role = roles
                    .iter()
                    .position(|candidate| *candidate == role)
                    .ok_or_else(|| format!("input node {at} has unknown role {role:?}"))?;
                ProgramNode::Input(role)
            }
            "multiply" => ProgramNode::Multiply(
                require_prior(node.left, at, "left")?,
                require_prior(node.right, at, "right")?,
            ),
            "add" => ProgramNode::Add(
                require_prior(node.left, at, "left")?,
                require_prior(node.right, at, "right")?,
            ),
            "divide" => ProgramNode::Divide(
                require_prior(node.left, at, "left")?,
                require_prior(node.right, at, "right")?,
            ),
            operation => return Err(format!("node {at} has unknown operation {operation:?}")),
        };
        nodes.push(parsed);
    }
    if source.output >= nodes.len() {
        return Err("the program output is outside the node population".to_owned());
    }
    Ok(Program {
        output: source.output,
        nodes,
    })
}

fn require_prior(value: Option<usize>, at: usize, side: &str) -> Result<usize, String> {
    let value = value.ok_or_else(|| format!("node {at} has no {side} antecedent"))?;
    if value >= at {
        return Err(format!("node {at} {side} antecedent {value} is not prior"));
    }
    Ok(value)
}

fn evaluate(program: &Program, input: &Input) -> EvaluationReadInternal {
    let mut values: Vec<Rational> = Vec::with_capacity(program.nodes.len());
    let mut path = Vec::with_capacity(program.nodes.len());
    for (at, node) in program.nodes.iter().enumerate() {
        let evaluated = match *node {
            ProgramNode::Input(role) => input
                .values
                .get(role)
                .copied()
                .ok_or_else(|| format!("input role {role} is absent")),
            ProgramNode::Multiply(left, right) => values[left].checked_mul(values[right]),
            ProgramNode::Add(left, right) => values[left].checked_add(values[right]),
            ProgramNode::Divide(left, right) => values[left].checked_div(values[right]),
        };
        let value = match evaluated {
            Ok(value) => value,
            Err(reason) => {
                return EvaluationReadInternal {
                    condition: "open".to_owned(),
                    complete_path: path,
                    output: None,
                    open_at_node: Some(at),
                    open_reason: Some(reason),
                };
            }
        };
        let (operation, antecedents) = match *node {
            ProgramNode::Input(role) => (format!("input:{}", role_name(role)), Vec::new()),
            ProgramNode::Multiply(left, right) => ("multiply".to_owned(), vec![left, right]),
            ProgramNode::Add(left, right) => ("add".to_owned(), vec![left, right]),
            ProgramNode::Divide(left, right) => ("divide".to_owned(), vec![left, right]),
        };
        path.push(NodeReadInternal {
            node: at,
            operation,
            antecedents,
            value,
        });
        values.push(value);
    }
    EvaluationReadInternal {
        condition: "closed".to_owned(),
        complete_path: path,
        output: values.get(program.output).copied(),
        open_at_node: None,
        open_reason: None,
    }
}

struct NodeReadInternal {
    node: usize,
    operation: String,
    antecedents: Vec<usize>,
    value: Rational,
}

struct EvaluationReadInternal {
    condition: String,
    complete_path: Vec<NodeReadInternal>,
    output: Option<Rational>,
    open_at_node: Option<usize>,
    open_reason: Option<String>,
}

impl EvaluationReadInternal {
    fn report(&self) -> EvaluationRead {
        EvaluationRead {
            condition: self.condition.clone(),
            complete_path: self
                .complete_path
                .iter()
                .map(|node| NodeRead {
                    node: node.node,
                    operation: node.operation.clone(),
                    antecedents: node.antecedents.clone(),
                    value: node.value.to_string(),
                })
                .collect(),
            output: self.output.map(|value| value.to_string()),
            open_at_node: self.open_at_node,
            open_reason: self.open_reason.clone(),
        }
    }
}

fn role_name(role: usize) -> &'static str {
    ["a", "b", "c", "d", "e"]
        .get(role)
        .copied()
        .unwrap_or("unknown")
}

fn seed_carrier(
    budget: &RunBudget,
    event_name: &str,
    handle: ArtifactHandle,
    words: &[CompactWord],
) -> Result<StandingCarrier, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let pair = primed_pair(&mut machine)?;
    let mut arcs = Vec::with_capacity(words.len() + 1);
    append_words(&mut arcs, pair, handle.data_namespace, words)?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    let (radiation, event) =
        profiled_ending(budget, &mut machine, event_name, words.len(), pair, &arcs)?;
    if radiation.regional().is_empty() {
        return Err(format!("{event_name} returned no regional constituent"));
    }
    let rest = machine.rest_image().map_err(debug)?;
    let rest_octets = rest.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched and
    // still reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead
    // of being hashed and dropped. This helper is called at every named ending; the address is the
    // content, so each distinct rest is deposited at its own address rather than overwriting the
    // previous.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let rest_sha256 = sha256(&rest_octets);
    let live_lineages = machine.memory().live_lineages;
    Ok(StandingCarrier {
        rest,
        event,
        rest_sha256,
        live_lineages,
    })
}

fn run_case(
    budget: &RunBudget,
    rest: &LiveCurrentRestImage,
    program_handle: ArtifactHandle,
    expected_program: &Program,
    ordinal: usize,
    source: &SourceCase,
    source_sha256: &str,
) -> Result<(CaseRead, LiveCurrentMachine), String> {
    let mut machine = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let input = Input {
        ordinal,
        values: source
            .values
            .iter()
            .map(|value| parse_ratio(value))
            .collect::<Result<_, _>>()?,
    };
    let input_words = input_words(&input)?;
    let input_handle = ArtifactHandle::new(source.id.as_bytes(), source_sha256);
    let pair = primed_pair(&mut machine)?;
    let mut arcs = Vec::with_capacity(input_words.len() + 1);
    append_words(&mut arcs, pair, input_handle.data_namespace, &input_words)?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(program_handle.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    let (radiation, conduct_event) = profiled_ending(
        budget,
        &mut machine,
        &format!("conduct-{}", source.id),
        input_words.len(),
        pair,
        &arcs,
    )?;
    let meeting = radiation
        .regional()
        .first()
        .ok_or_else(|| format!("case {} returned no meeting", source.id))?
        .constituent();
    let recovered_program = decode_program(meeting, program_handle.data_namespace)?;
    let recovered_input = decode_input(meeting, input_handle.data_namespace)?;
    let program_exact = recovered_program == *expected_program;
    let input_exact = recovered_input == input;
    if !program_exact || !input_exact {
        return Err(format!("case {} lost its program or current", source.id));
    }
    let evaluation = evaluate(&recovered_program, &recovered_input);
    let expected_output = source
        .expected_output
        .as_deref()
        .map(parse_ratio)
        .transpose()?;
    if evaluation.condition != source.expected_condition || evaluation.output != expected_output {
        return Err(format!("case {} changed its expected path", source.id));
    }

    let mut events = vec![conduct_event];
    let mut result_returned = false;
    let mut returned_result = None;
    let mut comparison = None;
    if let Some(output) = evaluation.output {
        let result_words = result_words(output)?;
        let result_root = namespace(&[
            b"eros-retriangulating-branch-result-v1",
            source_sha256.as_bytes(),
            source.id.as_bytes(),
        ]);
        let pair = primed_pair(&mut machine)?;
        let mut arcs = Vec::new();
        append_words(&mut arcs, pair, result_root, &result_words)?;
        let (radiation, return_event) = profiled_ending(
            budget,
            &mut machine,
            &format!("return-{}", source.id),
            result_words.len(),
            pair,
            &arcs,
        )?;
        let prior = radiation
            .regional()
            .first()
            .ok_or_else(|| format!("case {} returned no result", source.id))?
            .constituent()
            .clone();
        let decoded = decode_result(&prior, result_root)?;
        result_returned = decoded == output;
        returned_result = Some(decoded.to_string());
        events.push(return_event);

        let pair = primed_pair(&mut machine)?;
        let mut expected_arcs = Vec::new();
        append_words(&mut expected_arcs, pair, result_root, &result_words)?;
        let (radiation, comparison_event) = profiled_ending(
            budget,
            &mut machine,
            &format!("compare-{}", source.id),
            result_words.len(),
            pair,
            &expected_arcs,
        )?;
        let returned = radiation
            .regional()
            .first()
            .ok_or_else(|| format!("case {} returned no comparison", source.id))?
            .constituent();
        comparison = Some(read_comparison(
            &prior,
            returned,
            result_root,
            &result_words,
        )?);
        events.push(comparison_event);
    }

    Ok((
        CaseRead {
            id: source.id.clone(),
            group: source.group.clone(),
            chart: source.chart.clone(),
            source_role_order: source.source_role_order.clone(),
            input_values: input.values.iter().map(ToString::to_string).collect(),
            expected_path: source.expected_path.clone(),
            expected_output: expected_output.map(|value| value.to_string()),
            complete_carrier_recovered_from_standing: program_exact,
            current_recovered_from_source: input_exact,
            evaluation: evaluation.report(),
            result_returned_as_later_current: result_returned,
            returned_result,
            result_comparison: comparison,
            events,
        },
        machine,
    ))
}

fn run_quotient_control(
    budget: &RunBudget,
    rest: &LiveCurrentRestImage,
    quotient_handle: ArtifactHandle,
    expected_quotient: Quotient,
    source: &SourceCase,
    source_sha256: &str,
) -> Result<ControlRead, String> {
    let mut machine = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let input = Input {
        ordinal: 0,
        values: source
            .values
            .iter()
            .map(|value| parse_ratio(value))
            .collect::<Result<_, _>>()?,
    };
    let words = input_words(&input)?;
    let input_handle = ArtifactHandle::new(b"quotient-control-input", source_sha256);
    let pair = primed_pair(&mut machine)?;
    let mut arcs = Vec::new();
    append_words(&mut arcs, pair, input_handle.data_namespace, &words)?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(quotient_handle.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    let (radiation, event) = profiled_ending(
        budget,
        &mut machine,
        "quotient-control",
        words.len(),
        pair,
        &arcs,
    )?;
    let meeting = radiation
        .regional()
        .first()
        .ok_or_else(|| "the quotient control returned no meeting".to_owned())?
        .constituent();
    let quotient_recovered =
        decode_quotient(meeting, quotient_handle.data_namespace)? == expected_quotient;
    let current_recovered = decode_input(meeting, input_handle.data_namespace)? == input;
    let complete_program_recovered =
        decode_program(meeting, quotient_handle.data_namespace).is_ok();
    Ok(ControlRead {
        name: "cross-ratio-plus-source-endpoint quotient".to_owned(),
        complete_program_recovered,
        quotient_recovered,
        current_recovered,
        output_formed: complete_program_recovered && current_recovered,
        reason: "The quotient supplies chi=10/21 and the old endpoint 31, but the scale-two current needs 62. It carries neither b*d, e, nor the multiply-add-divide path, so the generic transducer has no program to enact.".to_owned(),
        event,
    })
}

fn run_no_standing_control(
    budget: &RunBudget,
    absent_program_handle: ArtifactHandle,
    source: &SourceCase,
    source_sha256: &str,
) -> Result<ControlRead, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let input = Input {
        ordinal: 0,
        values: source
            .values
            .iter()
            .map(|value| parse_ratio(value))
            .collect::<Result<_, _>>()?,
    };
    let words = input_words(&input)?;
    let input_handle = ArtifactHandle::new(b"no-standing-input", source_sha256);
    let pair = primed_pair(&mut machine)?;
    let mut arcs = Vec::new();
    append_words(&mut arcs, pair, input_handle.data_namespace, &words)?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(absent_program_handle.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    let (radiation, event) = profiled_ending(
        budget,
        &mut machine,
        "no-standing-control",
        words.len(),
        pair,
        &arcs,
    )?;
    let meeting = radiation
        .regional()
        .first()
        .ok_or_else(|| "the no-Standing control returned no meeting".to_owned())?
        .constituent();
    let current_recovered = decode_input(meeting, input_handle.data_namespace)? == input;
    let complete_program_recovered =
        decode_program(meeting, absent_program_handle.data_namespace).is_ok();
    Ok(ControlRead {
        name: "same scaled current without Standing".to_owned(),
        complete_program_recovered,
        quotient_recovered: false,
        current_recovered,
        output_formed: complete_program_recovered && current_recovered,
        reason: "The current supplies values but no admitted composition. The absent program capability remains an open contact and no result is formed.".to_owned(),
        event,
    })
}

fn program_words(program: &Program) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(PROGRAM_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(PROGRAM_NODE_COUNT, program.nodes.len() as u64),
        CompactWord::scalar(PROGRAM_OUTPUT, program.output as u64),
    ];
    for (at, node) in program.nodes.iter().enumerate() {
        let coordinate = vec![at as u64];
        match *node {
            ProgramNode::Input(role) => {
                words.push(CompactWord::at(PROGRAM_NODE_KIND, coordinate.clone(), 1));
                words.push(CompactWord::at(PROGRAM_NODE_ROLE, coordinate, role as u64));
            }
            ProgramNode::Multiply(left, right) => {
                append_binary_node(&mut words, at, 2, left, right);
            }
            ProgramNode::Add(left, right) => {
                append_binary_node(&mut words, at, 3, left, right);
            }
            ProgramNode::Divide(left, right) => {
                append_binary_node(&mut words, at, 4, left, right);
            }
        }
    }
    words
}

fn append_binary_node(
    words: &mut Vec<CompactWord>,
    at: usize,
    kind: u64,
    left: usize,
    right: usize,
) {
    let coordinate = vec![at as u64];
    words.push(CompactWord::at(PROGRAM_NODE_KIND, coordinate.clone(), kind));
    words.push(CompactWord::at(
        PROGRAM_NODE_LEFT,
        coordinate.clone(),
        left as u64,
    ));
    words.push(CompactWord::at(
        PROGRAM_NODE_RIGHT,
        coordinate,
        right as u64,
    ));
}

fn quotient_words(quotient: Quotient) -> Result<Vec<CompactWord>, String> {
    let mut words = vec![CompactWord::scalar(QUOTIENT_SCHEMA, COMPACT_SCHEMA)];
    append_rational(
        &mut words,
        &[],
        [
            QUOTIENT_CHI_SIGN,
            QUOTIENT_CHI_MAGNITUDE,
            QUOTIENT_CHI_DENOMINATOR,
        ],
        quotient.chi,
    )?;
    append_rational(
        &mut words,
        &[],
        [
            QUOTIENT_OUTPUT_SIGN,
            QUOTIENT_OUTPUT_MAGNITUDE,
            QUOTIENT_OUTPUT_DENOMINATOR,
        ],
        quotient.source_output,
    )?;
    Ok(words)
}

fn input_words(input: &Input) -> Result<Vec<CompactWord>, String> {
    let mut words = vec![
        CompactWord::scalar(INPUT_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(INPUT_ORDINAL, input.ordinal as u64),
    ];
    for (role, value) in input.values.iter().copied().enumerate() {
        append_rational(
            &mut words,
            &[role as u64],
            [
                INPUT_VALUE_SIGN,
                INPUT_VALUE_MAGNITUDE,
                INPUT_VALUE_DENOMINATOR,
            ],
            value,
        )?;
    }
    Ok(words)
}

fn result_words(result: Rational) -> Result<Vec<CompactWord>, String> {
    let mut words = vec![CompactWord::scalar(RESULT_SCHEMA, COMPACT_SCHEMA)];
    append_rational(
        &mut words,
        &[],
        [
            RESULT_VALUE_SIGN,
            RESULT_VALUE_MAGNITUDE,
            RESULT_VALUE_DENOMINATOR,
        ],
        result,
    )?;
    Ok(words)
}

fn append_rational(
    words: &mut Vec<CompactWord>,
    coordinates: &[u64],
    tags: [u64; 3],
    value: Rational,
) -> Result<(), String> {
    let (sign, magnitude, denominator) = value.encode()?;
    words.push(CompactWord::at(tags[0], coordinates.to_vec(), sign));
    words.push(CompactWord::at(tags[1], coordinates.to_vec(), magnitude));
    words.push(CompactWord::at(tags[2], coordinates.to_vec(), denominator));
    Ok(())
}

fn decode_program(constituent: &LiveConstituent, root: u64) -> Result<Program, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, PROGRAM_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("program schema changed".to_owned());
    }
    let count = usize::try_from(atlas.word(root, PROGRAM_NODE_COUNT, &[])?).map_err(debug)?;
    let output = usize::try_from(atlas.word(root, PROGRAM_OUTPUT, &[])?).map_err(debug)?;
    let mut nodes = Vec::with_capacity(count);
    for at in 0..count {
        let coordinate = [at as u64];
        let node = match atlas.word(root, PROGRAM_NODE_KIND, &coordinate)? {
            1 => ProgramNode::Input(
                usize::try_from(atlas.word(root, PROGRAM_NODE_ROLE, &coordinate)?)
                    .map_err(debug)?,
            ),
            2 => ProgramNode::Multiply(
                usize::try_from(atlas.word(root, PROGRAM_NODE_LEFT, &coordinate)?)
                    .map_err(debug)?,
                usize::try_from(atlas.word(root, PROGRAM_NODE_RIGHT, &coordinate)?)
                    .map_err(debug)?,
            ),
            3 => ProgramNode::Add(
                usize::try_from(atlas.word(root, PROGRAM_NODE_LEFT, &coordinate)?)
                    .map_err(debug)?,
                usize::try_from(atlas.word(root, PROGRAM_NODE_RIGHT, &coordinate)?)
                    .map_err(debug)?,
            ),
            4 => ProgramNode::Divide(
                usize::try_from(atlas.word(root, PROGRAM_NODE_LEFT, &coordinate)?)
                    .map_err(debug)?,
                usize::try_from(atlas.word(root, PROGRAM_NODE_RIGHT, &coordinate)?)
                    .map_err(debug)?,
            ),
            kind => return Err(format!("program node {at} has unknown kind {kind}")),
        };
        nodes.push(node);
    }
    Ok(Program { output, nodes })
}

fn decode_quotient(constituent: &LiveConstituent, root: u64) -> Result<Quotient, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, QUOTIENT_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("quotient schema changed".to_owned());
    }
    Ok(Quotient {
        chi: decode_rational(
            &atlas,
            root,
            &[],
            [
                QUOTIENT_CHI_SIGN,
                QUOTIENT_CHI_MAGNITUDE,
                QUOTIENT_CHI_DENOMINATOR,
            ],
        )?,
        source_output: decode_rational(
            &atlas,
            root,
            &[],
            [
                QUOTIENT_OUTPUT_SIGN,
                QUOTIENT_OUTPUT_MAGNITUDE,
                QUOTIENT_OUTPUT_DENOMINATOR,
            ],
        )?,
    })
}

fn decode_input(constituent: &LiveConstituent, root: u64) -> Result<Input, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, INPUT_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("input schema changed".to_owned());
    }
    let ordinal = usize::try_from(atlas.word(root, INPUT_ORDINAL, &[])?).map_err(debug)?;
    let values = (0..5)
        .map(|role| {
            decode_rational(
                &atlas,
                root,
                &[role as u64],
                [
                    INPUT_VALUE_SIGN,
                    INPUT_VALUE_MAGNITUDE,
                    INPUT_VALUE_DENOMINATOR,
                ],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Input { ordinal, values })
}

fn decode_result(constituent: &LiveConstituent, root: u64) -> Result<Rational, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, RESULT_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("result schema changed".to_owned());
    }
    decode_rational(
        &atlas,
        root,
        &[],
        [
            RESULT_VALUE_SIGN,
            RESULT_VALUE_MAGNITUDE,
            RESULT_VALUE_DENOMINATOR,
        ],
    )
}

fn decode_rational(
    atlas: &CapabilityAtlas,
    root: u64,
    coordinates: &[u64],
    tags: [u64; 3],
) -> Result<Rational, String> {
    let sign = atlas.word(root, tags[0], coordinates)?;
    let magnitude = i128::from(atlas.word(root, tags[1], coordinates)?);
    let denominator = i128::from(atlas.word(root, tags[2], coordinates)?);
    let numerator = match sign {
        0 if magnitude == 0 => 0,
        1 => magnitude,
        2 => -magnitude,
        _ => {
            return Err(format!(
                "rational sign {sign} and magnitude {magnitude} disagree"
            ));
        }
    };
    Rational::new(numerator, denominator)
}

fn standing_program(machine: &LiveCurrentMachine, root: u64) -> Result<Program, String> {
    let programs = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_program(constituent, root).ok())
        .collect::<Vec<_>>();
    match programs.as_slice() {
        [program] => Ok(program.clone()),
        [] => Err("Standing exposes no complete program".to_owned()),
        _ => Err("Standing exposes plural complete programs".to_owned()),
    }
}

fn standing_quotient(machine: &LiveCurrentMachine, root: u64) -> Result<Quotient, String> {
    let quotients = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_quotient(constituent, root).ok())
        .collect::<Vec<_>>();
    match quotients.as_slice() {
        [quotient] => Ok(quotient.clone()),
        [] => Err("Standing exposes no quotient".to_owned()),
        _ => Err("Standing exposes plural quotients".to_owned()),
    }
}

fn read_comparison(
    prior: &LiveConstituent,
    returned: &LiveConstituent,
    root: u64,
    words: &[CompactWord],
) -> Result<ComparisonRead, String> {
    let capabilities = words
        .iter()
        .map(|word| word.interface(root))
        .collect::<Vec<_>>();
    let mut rides = 0usize;
    let mut opens = 0usize;
    let mut founds = 0usize;
    for capability in &capabilities {
        let prior_pin = prior
            .pins()
            .iter()
            .find(|pin| pin.interface() == Some(capability.clone()))
            .ok_or_else(|| "the returned result omitted one compact capability".to_owned())?;
        let comparison_pins = returned
            .pins()
            .iter()
            .filter(|pin| !prior.pins().contains(pin))
            .filter(|pin| pin.interface() == Some(capability.clone()))
            .filter(|pin| pin.held() == prior_pin.meeting())
            .collect::<Vec<_>>();
        if comparison_pins.len() != 1 {
            return Err(format!(
                "one result capability returned {} comparison pins instead of one",
                comparison_pins.len()
            ));
        }
        let pin = comparison_pins[0];
        if pin.is_open() {
            opens += 1;
        } else if pin.is_found() {
            founds += 1;
        } else {
            rides += 1;
        }
    }
    Ok(ComparisonRead {
        capabilities: capabilities.len(),
        rides,
        opens,
        founds,
        exact_ride: rides == capabilities.len() && opens == 0 && founds == 0,
    })
}

fn profiled_ending(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    event_name: &str,
    semantic_words: usize,
    pair: [CurrentLineage; 2],
    arcs: &[RegionalRelationArc],
) -> Result<(soma_membrane::ContemporaryRadiation, EventRead), String> {
    budget.require_open()?;
    if arcs.len() > MAX_ARCS_PER_EVENT {
        return Err(format!(
            "event {event_name} requires {} arcs beyond the limit {MAX_ARCS_PER_EVENT}",
            arcs.len()
        ));
    }
    let currents = [
        CurrentEvent::ending(pair[0], relation(181)?, action()),
        CurrentEvent::ending(pair[1], relation(191)?, action()),
    ];
    let regional = [RegionalRelationCell::new(pair[1], arcs)];
    let started = Instant::now();
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    let wall = started.elapsed();
    if wall > EVENT_LIMIT {
        return Err(format!(
            "event {event_name} exceeded {} seconds",
            EVENT_LIMIT.as_secs()
        ));
    }
    budget.require_open()?;
    let event = EventRead {
        event: event_name.to_owned(),
        semantic_words,
        regional_arcs: arcs.len(),
        wall_micros: duration_micros(wall),
        returned_incidences: radiation
            .regional()
            .iter()
            .map(|row| row.constituent().incidences().len())
            .sum(),
        returned_pins: radiation
            .regional()
            .iter()
            .map(|row| row.constituent().pins().len())
            .sum(),
    };
    Ok((radiation, event))
}

fn primed_pair(machine: &mut LiveCurrentMachine) -> Result<[CurrentLineage; 2], String> {
    let first = relation(PRIMING_VALUES[0])?;
    let pair = [
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
        machine
            .attach(CurrentGeometry::Cell(first))
            .map_err(debug)?,
    ];
    for value in PRIMING_VALUES {
        let currents = [
            CurrentEvent::continuing(pair[0], relation(value)?, action()),
            CurrentEvent::continuing(pair[1], relation(value)?, action()),
        ];
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
    }
    Ok(pair)
}

fn append_words(
    arcs: &mut Vec<RegionalRelationArc>,
    pair: [CurrentLineage; 2],
    root: u64,
    words: &[CompactWord],
) -> Result<(), String> {
    for word in words {
        push_interface(arcs, pair, word.interface(root), IncidenceHand::Against)?;
    }
    Ok(())
}

fn push_interface(
    arcs: &mut Vec<RegionalRelationArc>,
    pair: [CurrentLineage; 2],
    interface: InterfaceCapability,
    hand: IncidenceHand,
) -> Result<(), String> {
    let slot = u32::try_from(arcs.len()).map_err(debug)?;
    arcs.push(RegionalRelationArc::new(
        pair[0],
        CurrentBoundaryPort::Cell,
        pair[1],
        CurrentBoundaryPort::Cell,
        interface,
        slot,
        0,
        hand,
    ));
    Ok(())
}

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
        ..
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
    }
}

fn compact_route_namespace(root: u64, word: &CompactWord) -> u64 {
    let mut route = Vec::with_capacity(2 + word.coordinates.len());
    route.extend_from_slice(&word.tag.to_le_bytes());
    route.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
    for coordinate in &word.coordinates {
        route.extend_from_slice(&coordinate.to_le_bytes());
    }
    namespace(&[
        b"eros-retriangulating-branch-transport-word-v1",
        &root.to_le_bytes(),
        &route,
    ])
}

fn parse_ratio(value: &str) -> Result<Rational, String> {
    let (numerator, denominator) = match value.split_once('/') {
        Some((numerator, denominator)) => (numerator, denominator),
        None => (value, "1"),
    };
    Rational::new(
        numerator
            .parse::<i128>()
            .map_err(|error| format!("numerator {numerator:?} parses: {error}"))?,
        denominator
            .parse::<i128>()
            .map_err(|error| format!("denominator {denominator:?} parses: {error}"))?,
    )
}

fn namespace(parts: &[&[u8]]) -> u64 {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update(part);
        hash.update([0]);
    }
    let digest = hash.finalize();
    let value = u64::from_be_bytes(digest[..8].try_into().unwrap());
    if value == 0 {
        1
    } else {
        value
    }
}

fn sha256(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        write!(&mut encoded, "{byte:02x}").expect("hex writing cannot fail");
    }
    encoded
}

fn duration_micros(duration: Duration) -> u64 {
    u64::try_from(duration.as_micros()).unwrap_or(u64::MAX)
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation value {value} remains nonzero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}

fn usage() -> &'static str {
    "usage: cargo run -p life --example eros_retriangulating_branch_transport -- <SOURCE.json> <REPORT.json>"
}
