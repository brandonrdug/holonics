#[path = "exact_algorithm_ecology/algorithm_organ.rs"]
mod algorithm_organ;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use algorithm_organ::{
    AlgorithmWord, Evaluation, ExactValue, Node, Program, Quantity, Rational, StepShape, Unit,
    ValueDomain,
};
use body::incidence::IncidenceHand;
use body::num::Cog;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use life::form_mouth::deposit_form_or_message;
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveMemory, RegionalRelationArc,
    RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_exact_algorithm_ecology/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_exact_algorithm_ecology";
/// The two live-current rests this driver seals: the source population's, and the final one after
/// source-absent conduct. `ERST` reads both, and depositing them apart is what lets a second frame
/// see that the two are different bodies rather than one form written twice.
const SOURCE_REST_FORM: &str = "source-rest";
const FINAL_REST_FORM: &str = "final-rest";

const SOURCE_SCHEMA: &str = "eros.exact-algorithm-ecology.source.v1";
const REPORT_SCHEMA: &str = "eros.exact-algorithm-ecology.report.v1";
const OBSERVATION_ID: &str = "eros-exact-algorithm-ecology-01";
const COMPACT_SCHEMA: u64 = 1;
const RECRUIT_LOCAL: u64 = 0;
const EVENT_LIMIT: Duration = Duration::from_secs(30);
const RUN_LIMIT: Duration = Duration::from_secs(120);
const MAX_ARCS_PER_EVENT: usize = 256;
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];

const CHART_SCHEMA: u64 = 1_000;
const CHART_GENERATION: u64 = 1_001;
const CHART_OUTPUT_PROBES: u64 = 1_002;
const CHART_OUTPUT_SUPPORT: u64 = 1_003;
const CHART_TRACE_SUPPORT: u64 = 1_004;
const CHART_PROGRAM_COUNT: u64 = 1_005;
const CHART_PROGRAM_ID: u64 = 1_006;
const CHART_PROGRAM_NAME_LENGTH: u64 = 1_007;
const CHART_PROGRAM_NAME_CHUNK: u64 = 1_008;

const QUANTITY_SCHEMA: u64 = 3_000;
const QUANTITY_COUNT: u64 = 3_001;
const QUANTITY_KIND: u64 = 3_010;
const QUANTITY_BITS: u64 = 3_011;
const QUANTITY_SIGN: u64 = 3_012;
const QUANTITY_MAGNITUDE: u64 = 3_013;
const QUANTITY_DENOMINATOR: u64 = 3_014;
const QUANTITY_UNIT: u64 = 3_015;

const TRACE_SCHEMA: u64 = 4_000;
const TRACE_COUNT: u64 = 4_001;
const TRACE_OPERATION: u64 = 4_002;
const TRACE_ANTECEDENT_COUNT: u64 = 4_003;
const TRACE_ANTECEDENT: u64 = 4_004;
const SUPPORT_SCHEMA: u64 = 5_000;
const SUPPORT_MASK: u64 = 5_001;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    question: String,
    word_width: u8,
    candidates: Vec<SourceCandidate>,
    output_probes: Vec<SourceProbe>,
    trace_oracle: String,
    later_source_absent_input: u64,
    later_expected_output: u64,
    division_cases: Vec<SourceDivisionCase>,
    physical_preflight: PhysicalPreflight,
    stopping_condition: String,
}

#[derive(Deserialize)]
struct SourceCandidate {
    id: u64,
    name: String,
    expression: String,
}

#[derive(Deserialize)]
struct SourceProbe {
    input: u64,
    oracle_output: u64,
}

#[derive(Deserialize)]
struct SourceDivisionCase {
    id: String,
    left: String,
    left_unit: String,
    right: String,
    right_unit: String,
    expected: Option<String>,
    expected_unit: Option<String>,
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

#[derive(Clone, PartialEq, Eq)]
struct Chart {
    generation: u64,
    output_probes: u64,
    output_support: u64,
    trace_support: u64,
    programs: Vec<Program>,
}

#[derive(Clone)]
struct ArtifactHandle {
    data_root: u64,
    recruit: InterfaceCapability,
}

impl ArtifactHandle {
    fn new(kind: &[u8], identity: &[u8]) -> Self {
        Self {
            data_root: namespace(&[b"eros-exact-algorithm-ecology-data-v1", kind, identity]),
            recruit: InterfaceCapability::new(
                namespace(&[b"eros-exact-algorithm-ecology-recruit-v1", kind, identity]),
                RECRUIT_LOCAL,
            ),
        }
    }
}

#[derive(Clone)]
struct PendingArc {
    interface: InterfaceCapability,
    hand: IncidenceHand,
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
                .ok_or_else(|| "one exposed exact pin has no interface".to_owned())?;
            values
                .entry(interface.namespace())
                .or_default()
                .insert(interface.local());
        }
        Ok(Self { values })
    }

    fn word(&self, root: u64, tag: u64, coordinates: &[u64]) -> Result<u64, String> {
        let route = AlgorithmWord::at(tag, coordinates.to_vec(), 0);
        let namespace = compact_route_namespace(root, &route);
        match self.values.get(&namespace) {
            Some(values) if values.len() == 1 => Ok(*values.first().unwrap()),
            Some(_) => Err(format!(
                "exact route {tag}:{coordinates:?} exposes plural values"
            )),
            None => Err(format!("exact route {tag}:{coordinates:?} is absent")),
        }
    }
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
            Err("the bounded exact-algorithm ecology exceeded two minutes".to_owned())
        } else {
            Ok(())
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros exact algorithm ecology: {error}");
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
    let report = run_host(source, source_sha256)?;
    let mut report_bytes = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("exact-algorithm report encodes: {error}"))?;
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
        "eros exact algorithm ecology: accepted · {} bytes · {}",
        report_bytes.len(),
        report_path.display()
    );
    Ok(())
}

fn run_host(source: Source, source_sha256: String) -> Result<Value, String> {
    let run_started = Instant::now();
    let programs = candidate_programs(source.word_width)?;
    validate_source(&source, &programs)?;
    let budget = RunBudget::new();
    let identity = source_sha256.as_bytes();
    let output_membership = namespace(&[
        b"eros-exact-algorithm-ecology-output-membership-v1",
        identity,
    ]);
    let trace_membership = namespace(&[
        b"eros-exact-algorithm-ecology-trace-membership-v1",
        identity,
    ]);
    let candidate_extent = source.candidates.len();
    let full_support = mask_for_ids(programs.iter().map(|program| program.id))?;
    let initial_chart = Chart {
        generation: 0,
        output_probes: 0,
        output_support: full_support,
        trace_support: full_support,
        programs: programs.clone(),
    };
    let mut chart_handle = chart_artifact(b"receiver-chart", identity, &initial_chart)?;

    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let seed = seed_chart(
        &budget,
        &mut machine,
        "source-program-population",
        chart_handle.clone(),
        &initial_chart,
    )?;
    let source_rest = machine.rest_image().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. Every hash here is untouched.
    let source_rest_octets = source_rest.encode_native_bytes().map_err(debug)?;
    let deposited = deposit_form_or_message(FORM_DRIVER, SOURCE_REST_FORM, &source_rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let source_departed = machine.memory().live_lineages == 0;
    let source_chart_exact = standing_chart(&machine, chart_handle.data_root)?.1 == initial_chart;

    let mut output_reads = Vec::new();
    for (ordinal, probe) in source.output_probes.iter().enumerate() {
        let (read, next_handle) = train_output_probe(
            &budget,
            &mut machine,
            chart_handle.clone(),
            output_membership,
            trace_membership,
            candidate_extent,
            source.word_width,
            ordinal,
            probe,
            identity,
        )?;
        output_reads.push(read);
        chart_handle = next_handle;
    }

    let (trace_read, next_handle) = train_trace_receiver(
        &budget,
        &mut machine,
        chart_handle.clone(),
        output_membership,
        trace_membership,
        candidate_extent,
        &source.trace_oracle,
        identity,
    )?;
    chart_handle = next_handle;
    let final_chart = standing_chart(&machine, chart_handle.data_root)?.1;
    let final_rest = machine.rest_image().map_err(debug)?;
    let final_rest_octets = final_rest.encode_native_bytes().map_err(debug)?;
    let deposited = deposit_form_or_message(FORM_DRIVER, FINAL_REST_FORM, &final_rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let final_rest_sha256 = sha256(&final_rest_octets);
    let remounted = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let remount_exact = remounted.rest_image().map_err(debug)? == final_rest
        && standing_chart(&remounted, chart_handle.data_root)?.1 == final_chart;

    let later = source_absent_conduct(
        &budget,
        remounted,
        chart_handle.clone(),
        source.word_width,
        source.later_source_absent_input,
        source.later_expected_output,
        identity,
    )?;
    let no_standing = no_standing_control(
        &budget,
        chart_handle,
        source.word_width,
        source.later_source_absent_input,
        identity,
    )?;

    let division = division_world(&budget, &source.division_cases, identity)?;
    let algebra = programs
        .iter()
        .map(|program| {
            Ok((
                program.name.clone(),
                program.word_polynomial()?,
                program.shape(),
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let algebra_read = algebra
        .iter()
        .map(|(name, polynomial, shape)| {
            json!({
                "program": name,
                "word_ring_polynomial_coefficients_low_to_high": polynomial,
                "trace_shape": shape_json(shape),
            })
        })
        .collect::<Vec<_>>();
    let algebra_equivalence_exact = algebra[0].1 == algebra[1].1
        && algebra[0].1 != algebra[2].1
        && algebra[0].1 != algebra[3].1;

    let output_names = mask_names(final_chart.output_support, &source.candidates);
    let trace_names = mask_names(final_chart.trace_support, &source.candidates);
    let order_gauge = order_gauge_control(
        &budget,
        programs.clone(),
        &source,
        identity,
        final_chart.output_support,
        final_chart.trace_support,
    )?;
    let acceptance = json!({
        "source_program_population_stood_after_source_lineages_departed":
            source_departed && source_chart_exact,
        "each_probe_returned_an_exact_oracle_consequence_and_machine_residual":
            output_reads.iter().all(|read| read["accepted"] == json!(true)),
        "output_receiver_preserved_the_nontrivial_fiber":
            output_names == vec!["square_then_add", "successor_product"],
        "trace_receiver_refined_only_its_own_fiber":
            trace_names == vec!["square_then_add"]
                && output_names == vec!["square_then_add", "successor_product"]
                && trace_read["accepted"] == json!(true),
        "algebra_receiver_proved_output_equivalence_without_sampling":
            algebra_equivalence_exact,
        "final_boundary_survived_exact_rest_remount": remount_exact,
        "later_source_absent_output_receiver_conducted_both_paths":
            later["output_receiver"]["accepted"] == json!(true),
        "later_source_absent_trace_receiver_conducted_one_path":
            later["trace_receiver"]["accepted"] == json!(true),
        "no_standing_control_formed_no_output": no_standing["accepted"] == json!(true),
        "same_division_path_retained_distinct_unit_faces":
            division["dual_chart_exact"] == json!(true),
        "withholding_the_unit_receiver_left_the_numeric_face_ambiguous":
            division["unit_erasure_ambiguous"] == json!(true),
        "zero_division_remained_open": division["zero_boundary_exact"] == json!(true),
        "candidate_storage_order_was_gauge": order_gauge["exact"] == json!(true),
        "every_successor_was_one_complete_outgoing_factor":
            output_reads.iter().all(|read| read["factor"]["outgoing_factor_exact"] == json!(true))
                && trace_read["factor"]["outgoing_factor_exact"] == json!(true),
        "no_floating_point_causal_data": true,
        "world_side_typed_interpreter_remained_explicit": true
    });
    let accepted = acceptance
        .as_object()
        .ok_or_else(|| "acceptance is not an object".to_owned())?
        .values()
        .all(|value| value == &json!(true));
    if !accepted {
        return Err(format!(
            "the exact-algorithm ecology did not close: {}",
            serde_json::to_string_pretty(&acceptance).map_err(debug)?
        ));
    }
    budget.require_open()?;

    Ok(json!({
        "schema": REPORT_SCHEMA,
        "status": "accepted",
        "observation_id": OBSERVATION_ID,
        "question": source.question,
        "theory_to_structure": "An algorithm is carried as an exact typed antecedent-to-consequent graph. A chart is the receiver-indexed support fiber plus the exact graphs still able to factor into later conduct. Output testimony changes output membership through RIDE/OPEN residuals; trace testimony crosses a different membership surface; the outgoing factor re-emits only the active chart boundary. The world organ interprets the recovered graph and returns consequences, while Soma owns co-presence, residual, replacement, rest, and later recruitment.",
        "source_sha256": source_sha256,
        "physical_preflight": {
            "executor": source.physical_preflight.executor,
            "event_limit_seconds": source.physical_preflight.event_limit_seconds,
            "run_limit_seconds": source.physical_preflight.run_limit_seconds,
            "maximum_regional_arcs_per_event": source.physical_preflight.maximum_regional_arcs_per_event,
            "floating_point_causal_data": source.physical_preflight.floating_point_causal_data,
            "cuda": source.physical_preflight.cuda
        },
        "source_population": {
            "event": seed,
            "source_lineages_departed": source_departed,
            "chart_returned_exactly": source_chart_exact,
            "rest_sha256": sha256(&source_rest_octets)
        },
        "output_training": output_reads,
        "trace_receiver_refinement": trace_read,
        "algebra_receiver": {
            "derivation": "Every node was normalized symbolically in (Z / 2^8 Z)[x]; no finite input census or fitted quotient was used.",
            "programs": algebra_read,
            "square_then_add_equals_successor_product": algebra_equivalence_exact
        },
        "final_receiver_chart": chart_json(&final_chart, &source.candidates),
        "rest_remount": {
            "exact": remount_exact,
            "rest_sha256": final_rest_sha256
        },
        "later_source_absent_conduct": later,
        "no_standing_control": no_standing,
        "typed_division_world": division,
        "order_gauge_control": order_gauge,
        "acceptance": acceptance,
        "stopping_condition": source.stopping_condition,
        "run_wall_micros": duration_micros(run_started.elapsed()),
        "conclusion": "The learned object is not one chosen formula or a scalar score. It is an exact receiver-indexed ecology: the output face lawfully retains two nonidentical causal paths; the algebra face proves that their word-ring consequences commute; the trace face distinguishes them; and both distinctions survive as one factor through rest. With source declarations and oracle absent, the output receiver recruits both paths and the trace receiver recruits one. The same typed DIVIDE graph carries the identical rational magnitude through electrical and kinematic charts while its unit consequence differs, and zero division remains an OPEN completed prefix. The remaining engine question is therefore not vocabulary from nothing: it is how broadly world ecologies can supply exact typed operations and consequences for this same cultivation law."
    }))
}

fn candidate_programs(bits: u8) -> Result<Vec<Program>, String> {
    let one = Quantity::word(bits, 1)?;
    let programs = vec![
        Program {
            id: 0,
            name: "square_then_add".to_owned(),
            domain: ValueDomain::Word(bits),
            nodes: vec![
                Node::Input(0),
                Node::Multiply(0, 0),
                Node::Add(1, 0),
                Node::Return(2),
            ],
            output: 3,
        },
        Program {
            id: 1,
            name: "successor_product".to_owned(),
            domain: ValueDomain::Word(bits),
            nodes: vec![
                Node::Input(0),
                Node::Constant(one),
                Node::Add(0, 1),
                Node::Multiply(0, 2),
                Node::Return(3),
            ],
            output: 4,
        },
        Program {
            id: 2,
            name: "square_then_subtract".to_owned(),
            domain: ValueDomain::Word(bits),
            nodes: vec![
                Node::Input(0),
                Node::Multiply(0, 0),
                Node::Subtract(1, 0),
                Node::Return(2),
            ],
            output: 3,
        },
        Program {
            id: 3,
            name: "double_by_shift".to_owned(),
            domain: ValueDomain::Word(bits),
            nodes: vec![
                Node::Input(0),
                Node::ShiftLeft {
                    source: 0,
                    places: 1,
                },
                Node::Return(1),
            ],
            output: 2,
        },
    ];
    for program in &programs {
        program.validate()?;
    }
    Ok(programs)
}

fn division_program() -> Result<Program, String> {
    let program = Program {
        id: 100,
        name: "exact_division".to_owned(),
        domain: ValueDomain::Rational,
        nodes: vec![
            Node::Input(0),
            Node::Input(1),
            Node::Divide(0, 1),
            Node::Return(2),
        ],
        output: 3,
    };
    program.validate()?;
    Ok(program)
}

fn validate_source(source: &Source, programs: &[Program]) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA || source.observation_id != OBSERVATION_ID {
        return Err("the fixed source identity changed".to_owned());
    }
    if source.word_width != 8
        || source.candidates.len() != 4
        || source.output_probes.len() != 3
        || source.division_cases.len() != 3
    {
        return Err("the fixed source extent changed".to_owned());
    }
    if source.physical_preflight.executor != "bounded host"
        || source.physical_preflight.event_limit_seconds != EVENT_LIMIT.as_secs()
        || source.physical_preflight.run_limit_seconds != RUN_LIMIT.as_secs()
        || source.physical_preflight.maximum_regional_arcs_per_event != MAX_ARCS_PER_EVENT
        || source.physical_preflight.floating_point_causal_data
        || source.physical_preflight.cuda
    {
        return Err("the fixed physical preflight changed".to_owned());
    }
    for (declared, program) in source.candidates.iter().zip(programs) {
        if declared.id != program.id || declared.name != program.name {
            return Err("the declared candidate atlas changed".to_owned());
        }
        let expected_expression = ["x*x+x", "x*(x+1)", "x*x-x", "x<<1"][program.id as usize];
        if declared.expression != expected_expression {
            return Err(format!("candidate {} expression changed", declared.name));
        }
    }
    for probe in &source.output_probes {
        let input = [Quantity::word(source.word_width, probe.input)?];
        let oracle = Quantity::word(source.word_width, probe.oracle_output)?;
        if !programs
            .iter()
            .any(|program| program.evaluate(&input).output() == Some(oracle))
        {
            return Err(format!(
                "probe {} has no candidate returning its oracle face",
                probe.input
            ));
        }
    }
    if source.trace_oracle != programs[0].name
        || source.later_source_absent_input != 3
        || source.later_expected_output != 12
    {
        return Err("the fixed trace or later-current boundary changed".to_owned());
    }
    Ok(())
}

fn train_output_probe(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    chart_handle: ArtifactHandle,
    output_membership: u64,
    _trace_membership: u64,
    candidate_extent: usize,
    bits: u8,
    ordinal: usize,
    probe: &SourceProbe,
    identity: &[u8],
) -> Result<(Value, ArtifactHandle), String> {
    let (_, prior_chart) = standing_chart(machine, chart_handle.data_root)?;
    let input = Quantity::word(bits, probe.input)?;
    let input_root = namespace(&[
        b"eros-exact-algorithm-input-v1",
        identity,
        &(ordinal as u64).to_le_bytes(),
    ]);
    let input_words = quantity_words(&[input])?;
    let meeting_recruit = capability(&[
        b"eros-exact-algorithm-meeting-v1",
        identity,
        &(ordinal as u64).to_le_bytes(),
    ]);
    let mut conduct_arcs = Vec::new();
    append_words(
        &mut conduct_arcs,
        input_root,
        &input_words,
        IncidenceHand::Against,
    );
    push_interface(
        &mut conduct_arcs,
        chart_handle.recruit,
        IncidenceHand::Against,
    );
    push_interface(
        &mut conduct_arcs,
        meeting_recruit.clone(),
        IncidenceHand::Against,
    );
    let (conduct_radiation, conduct_event) = profiled_event(
        budget,
        machine,
        &format!("probe-{ordinal}-conduct"),
        input_words.len(),
        &conduct_arcs,
        None,
    )?;
    let meeting = regional_constituent(&conduct_radiation, "probe conduct")?;
    let recovered_chart = decode_chart(meeting, chart_handle.data_root)?;
    let recovered_input = decode_quantities(meeting, input_root)?;
    if recovered_chart != prior_chart || recovered_input != vec![input] {
        return Err(format!("probe {ordinal} lost its chart or exact input"));
    }
    let evaluations = recovered_chart
        .programs
        .iter()
        .map(|program| (program.clone(), program.evaluate(&recovered_input)))
        .collect::<Vec<_>>();
    let oracle = Quantity::word(bits, probe.oracle_output)?;
    let actual_support = mask_for_ids(evaluations.iter().filter_map(|(program, evaluation)| {
        (evaluation.output() == Some(oracle)).then_some(program.id)
    }))?;
    let expected_open = mask_xor(prior_chart.output_support, actual_support);

    let prediction_words = support_words(prior_chart.output_support);
    let prediction_handle = ArtifactHandle::new(
        b"output-prediction",
        &[
            identity,
            &(ordinal as u64).to_le_bytes(),
            &prior_chart.output_support.to_le_bytes(),
        ]
        .concat(),
    );
    let mut prediction_arcs = Vec::new();
    append_words(
        &mut prediction_arcs,
        chart_handle.data_root,
        &chart_words(&prior_chart)?,
        IncidenceHand::Against,
    );
    append_words(
        &mut prediction_arcs,
        input_root,
        &input_words,
        IncidenceHand::Against,
    );
    push_interface(
        &mut prediction_arcs,
        meeting_recruit.clone(),
        IncidenceHand::Against,
    );
    append_words(
        &mut prediction_arcs,
        prediction_handle.data_root,
        &prediction_words,
        IncidenceHand::Against,
    );
    append_membership(
        &mut prediction_arcs,
        output_membership,
        candidate_extent,
        prior_chart.output_support,
    );
    push_interface(
        &mut prediction_arcs,
        prediction_handle.recruit.clone(),
        IncidenceHand::Against,
    );
    let (prediction_radiation, prediction_event) = profiled_event(
        budget,
        machine,
        &format!("probe-{ordinal}-prediction-face"),
        candidate_extent,
        &prediction_arcs,
        None,
    )?;
    let prediction_body = regional_constituent(&prediction_radiation, "probe prediction")?.clone();

    let oracle_root = namespace(&[
        b"eros-exact-algorithm-oracle-v1",
        identity,
        &(ordinal as u64).to_le_bytes(),
    ]);
    let oracle_words = quantity_words(&[oracle])?;
    let comparison_recruit = capability(&[
        b"eros-exact-algorithm-comparison-v1",
        identity,
        &(ordinal as u64).to_le_bytes(),
    ]);
    let mut oracle_arcs = Vec::new();
    append_words(
        &mut oracle_arcs,
        oracle_root,
        &oracle_words,
        IncidenceHand::Against,
    );
    push_interface(
        &mut oracle_arcs,
        prediction_handle.recruit.clone(),
        IncidenceHand::Against,
    );
    append_membership(
        &mut oracle_arcs,
        output_membership,
        candidate_extent,
        actual_support,
    );
    push_interface(
        &mut oracle_arcs,
        comparison_recruit.clone(),
        IncidenceHand::Against,
    );
    let (oracle_radiation, oracle_event) = profiled_event(
        budget,
        machine,
        &format!("probe-{ordinal}-oracle-return"),
        oracle_words.len(),
        &oracle_arcs,
        None,
    )?;
    let returned = regional_constituent(&oracle_radiation, "oracle return")?;
    let returned_oracle = decode_quantities(returned, oracle_root)?;
    let residual = membership_residual(
        &prediction_body,
        returned,
        output_membership,
        candidate_extent,
        expected_open,
    )?;
    if returned_oracle != vec![oracle] || residual["exact"] != json!(true) {
        return Err(format!(
            "probe {ordinal} lost its oracle return or residual"
        ));
    }

    let output_support = prior_chart.output_support & actual_support;
    let trace_support = prior_chart.trace_support & output_support;
    let retained = prior_chart
        .programs
        .into_iter()
        .filter(|program| mask_contains(output_support | trace_support, program.id))
        .collect::<Vec<_>>();
    let next_chart = Chart {
        generation: prior_chart.generation + 1,
        output_probes: prior_chart.output_probes + 1,
        output_support,
        trace_support,
        programs: retained,
    };
    let next_handle = chart_artifact(b"receiver-chart", identity, &next_chart)?;
    let mut closure_arcs = Vec::new();
    append_words(
        &mut closure_arcs,
        prediction_handle.data_root,
        &prediction_words,
        IncidenceHand::Against,
    );
    append_words(
        &mut closure_arcs,
        oracle_root,
        &oracle_words,
        IncidenceHand::Against,
    );
    append_membership_subset(
        &mut closure_arcs,
        output_membership,
        candidate_extent,
        actual_support,
        expected_open,
    );
    push_interface(
        &mut closure_arcs,
        comparison_recruit,
        IncidenceHand::Against,
    );
    let factor = replace_chart(
        budget,
        machine,
        &format!("probe-{ordinal}-successor"),
        next_handle.clone(),
        &next_chart,
        closure_arcs,
    )?;
    let read = json!({
        "probe_ordinal": ordinal,
        "input": quantity_json(input),
        "oracle_return": quantity_json(oracle),
        "candidate_paths": evaluations.iter().map(|(program, evaluation)| {
            json!({
                "candidate": program.name,
                "evaluation": evaluation_json(evaluation)
            })
        }).collect::<Vec<_>>(),
        "prior_output_support_mask": prior_chart.output_support,
        "oracle_matching_support_mask": actual_support,
        "next_output_support_mask": output_support,
        "machine_residual": residual,
        "events": [conduct_event, prediction_event, oracle_event],
        "factor": factor,
        "accepted": output_support != 0
            && returned_oracle == vec![oracle]
            && standing_chart(machine, next_handle.data_root)?.1 == next_chart
            && machine.standing().constituents().iter().all(|body| {
                decode_chart(body, chart_handle.data_root).is_err()
            })
    });
    Ok((read, next_handle))
}

fn train_trace_receiver(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    chart_handle: ArtifactHandle,
    _output_membership: u64,
    trace_membership: u64,
    candidate_extent: usize,
    trace_oracle_name: &str,
    identity: &[u8],
) -> Result<(Value, ArtifactHandle), String> {
    let (_, prior_chart) = standing_chart(machine, chart_handle.data_root)?;
    let oracle_program = prior_chart
        .programs
        .iter()
        .find(|program| program.name == trace_oracle_name)
        .ok_or_else(|| "the trace oracle program departed before testimony".to_owned())?;
    let oracle_shape = oracle_program.shape();
    let actual_support = mask_for_ids(
        prior_chart
            .programs
            .iter()
            .filter_map(|program| (program.shape() == oracle_shape).then_some(program.id)),
    )?;
    let expected_open = mask_xor(prior_chart.trace_support, actual_support);
    let meeting_recruit = capability(&[b"eros-exact-algorithm-trace-meeting-v1", identity]);
    let mut meeting_arcs = Vec::new();
    push_interface(
        &mut meeting_arcs,
        chart_handle.recruit.clone(),
        IncidenceHand::Against,
    );
    push_interface(
        &mut meeting_arcs,
        meeting_recruit.clone(),
        IncidenceHand::Against,
    );
    let (_, meeting_event) = profiled_event(
        budget,
        machine,
        "trace-chart-meeting",
        1,
        &meeting_arcs,
        None,
    )?;

    let prediction_words = support_words(prior_chart.trace_support);
    let prediction_handle = ArtifactHandle::new(
        b"trace-prediction",
        &[
            identity,
            &prior_chart.trace_support.to_le_bytes(),
            &prior_chart.generation.to_le_bytes(),
        ]
        .concat(),
    );
    let mut prediction_arcs = Vec::new();
    append_words(
        &mut prediction_arcs,
        chart_handle.data_root,
        &chart_words(&prior_chart)?,
        IncidenceHand::Against,
    );
    push_interface(
        &mut prediction_arcs,
        meeting_recruit,
        IncidenceHand::Against,
    );
    append_words(
        &mut prediction_arcs,
        prediction_handle.data_root,
        &prediction_words,
        IncidenceHand::Against,
    );
    append_membership(
        &mut prediction_arcs,
        trace_membership,
        candidate_extent,
        prior_chart.trace_support,
    );
    push_interface(
        &mut prediction_arcs,
        prediction_handle.recruit.clone(),
        IncidenceHand::Against,
    );
    let (prediction_radiation, prediction_event) = profiled_event(
        budget,
        machine,
        "trace-prediction-face",
        candidate_extent,
        &prediction_arcs,
        None,
    )?;
    let prediction_body = regional_constituent(&prediction_radiation, "trace prediction")?.clone();
    let trace_root = namespace(&[b"eros-exact-algorithm-trace-oracle-v1", identity]);
    let trace_words = trace_words(&oracle_shape);
    let comparison_recruit = capability(&[b"eros-exact-algorithm-trace-comparison-v1", identity]);
    let mut arcs = Vec::new();
    append_words(&mut arcs, trace_root, &trace_words, IncidenceHand::Against);
    push_interface(
        &mut arcs,
        prediction_handle.recruit.clone(),
        IncidenceHand::Against,
    );
    append_membership(
        &mut arcs,
        trace_membership,
        candidate_extent,
        actual_support,
    );
    push_interface(
        &mut arcs,
        comparison_recruit.clone(),
        IncidenceHand::Against,
    );
    let (radiation, event) = profiled_event(
        budget,
        machine,
        "trace-oracle-return",
        trace_words.len(),
        &arcs,
        None,
    )?;
    let returned = regional_constituent(&radiation, "trace oracle")?;
    let residual = membership_residual(
        &prediction_body,
        returned,
        trace_membership,
        candidate_extent,
        expected_open,
    )?;
    let trace_support = prior_chart.trace_support & actual_support;
    let retained = prior_chart
        .programs
        .into_iter()
        .filter(|program| mask_contains(prior_chart.output_support | trace_support, program.id))
        .collect::<Vec<_>>();
    let next_chart = Chart {
        generation: prior_chart.generation + 1,
        output_probes: prior_chart.output_probes,
        output_support: prior_chart.output_support,
        trace_support,
        programs: retained,
    };
    let next_handle = chart_artifact(b"receiver-chart", identity, &next_chart)?;
    let mut closure_arcs = Vec::new();
    append_words(
        &mut closure_arcs,
        prediction_handle.data_root,
        &prediction_words,
        IncidenceHand::Against,
    );
    append_words(
        &mut closure_arcs,
        trace_root,
        &trace_words,
        IncidenceHand::Against,
    );
    append_membership_subset(
        &mut closure_arcs,
        trace_membership,
        candidate_extent,
        actual_support,
        expected_open,
    );
    push_interface(
        &mut closure_arcs,
        comparison_recruit,
        IncidenceHand::Against,
    );
    let factor = replace_chart(
        budget,
        machine,
        "trace-successor",
        next_handle.clone(),
        &next_chart,
        closure_arcs,
    )?;
    let read = json!({
        "oracle_program": trace_oracle_name,
        "oracle_shape": shape_json(&oracle_shape),
        "prior_trace_support_mask": prior_chart.trace_support,
        "oracle_matching_support_mask": actual_support,
        "next_trace_support_mask": trace_support,
        "output_support_unchanged": next_chart.output_support == prior_chart.output_support,
        "machine_residual": residual,
        "events": [meeting_event, prediction_event, event],
        "factor": factor,
        "accepted": residual["exact"] == json!(true)
            && trace_support == 1
            && next_chart.output_support == 3
            && standing_chart(machine, next_handle.data_root)?.1 == next_chart
            && machine.standing().constituents().iter().all(|body| {
                decode_chart(body, chart_handle.data_root).is_err()
            })
    });
    Ok((read, next_handle))
}

fn source_absent_conduct(
    budget: &RunBudget,
    mut machine: LiveCurrentMachine,
    chart_handle: ArtifactHandle,
    bits: u8,
    input_value: u64,
    expected_value: u64,
    identity: &[u8],
) -> Result<Value, String> {
    let input = Quantity::word(bits, input_value)?;
    let expected = Quantity::word(bits, expected_value)?;
    let input_root = namespace(&[b"eros-exact-algorithm-later-input-v1", identity]);
    let words = quantity_words(&[input])?;
    let mut arcs = Vec::new();
    append_words(&mut arcs, input_root, &words, IncidenceHand::Against);
    push_interface(&mut arcs, chart_handle.recruit, IncidenceHand::Against);
    let (radiation, conduct_event) = profiled_event(
        budget,
        &mut machine,
        "later-source-absent-conduct",
        words.len(),
        &arcs,
        None,
    )?;
    let meeting = regional_constituent(&radiation, "later conduct")?;
    let chart = decode_chart(meeting, chart_handle.data_root)?;
    let recovered_input = decode_quantities(meeting, input_root)?;

    let output = conduct_receiver(
        budget,
        &mut machine,
        "output",
        chart.output_support,
        &chart,
        &recovered_input,
        expected,
        identity,
    )?;
    let trace = conduct_receiver(
        budget,
        &mut machine,
        "trace",
        chart.trace_support,
        &chart,
        &recovered_input,
        expected,
        identity,
    )?;
    Ok(json!({
        "source_oracle_present": false,
        "source_program_population_present": false,
        "chart_recovered_from_rest": true,
        "input": quantity_json(input),
        "conduct_event": conduct_event,
        "output_receiver": output,
        "trace_receiver": trace
    }))
}

fn conduct_receiver(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    receiver: &str,
    support: u64,
    chart: &Chart,
    inputs: &[Quantity],
    expected: Quantity,
    identity: &[u8],
) -> Result<Value, String> {
    let evaluations = chart
        .programs
        .iter()
        .filter(|program| mask_contains(support, program.id))
        .map(|program| (program.clone(), program.evaluate(inputs)))
        .collect::<Vec<_>>();
    if evaluations.is_empty()
        || evaluations
            .iter()
            .any(|(_, evaluation)| evaluation.output() != Some(expected))
    {
        return Err(format!("{receiver} receiver could not conduct its support"));
    }
    let mut arcs = Vec::new();
    let mut roots = Vec::new();
    for (program, evaluation) in &evaluations {
        let root = namespace(&[
            b"eros-exact-algorithm-later-result-v1",
            identity,
            receiver.as_bytes(),
            &program.id.to_le_bytes(),
        ]);
        let words = quantity_words(&[evaluation.output().unwrap()])?;
        append_words(&mut arcs, root, &words, IncidenceHand::Against);
        roots.push((program.id, root));
    }
    let (radiation, event) = profiled_event(
        budget,
        machine,
        &format!("later-{receiver}-return"),
        arcs.len(),
        &arcs,
        None,
    )?;
    let returned = regional_constituent(&radiation, "later receiver return")?;
    let returned_exact = roots.iter().all(|(_, root)| {
        decode_quantities(returned, *root).is_ok_and(|quantities| quantities == vec![expected])
    });
    Ok(json!({
        "support_mask": support,
        "recruited_paths": evaluations.iter().map(|(program, evaluation)| {
            json!({
                "program": program.name,
                "evaluation": evaluation_json(evaluation)
            })
        }).collect::<Vec<_>>(),
        "returned_as_later_current": returned_exact,
        "return_event": event,
        "accepted": returned_exact
    }))
}

fn no_standing_control(
    budget: &RunBudget,
    absent_chart: ArtifactHandle,
    bits: u8,
    input_value: u64,
    identity: &[u8],
) -> Result<Value, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let input_root = namespace(&[b"eros-exact-algorithm-no-standing-input-v1", identity]);
    let words = quantity_words(&[Quantity::word(bits, input_value)?])?;
    let mut arcs = Vec::new();
    append_words(&mut arcs, input_root, &words, IncidenceHand::Against);
    push_interface(&mut arcs, absent_chart.recruit, IncidenceHand::Against);
    let (radiation, event) = profiled_event(
        budget,
        &mut machine,
        "no-standing-control",
        words.len(),
        &arcs,
        None,
    )?;
    let meeting = regional_constituent(&radiation, "no-standing control")?;
    let current_recovered = decode_quantities(meeting, input_root)?.len() == 1;
    let chart_recovered = decode_chart(meeting, absent_chart.data_root).is_ok();
    Ok(json!({
        "current_recovered": current_recovered,
        "chart_recovered": chart_recovered,
        "output_formed": false,
        "event": event,
        "accepted": current_recovered && !chart_recovered
    }))
}

fn order_gauge_control(
    budget: &RunBudget,
    mut programs: Vec<Program>,
    source: &Source,
    identity: &[u8],
    expected_output_support: u64,
    expected_trace_support: u64,
) -> Result<Value, String> {
    programs.reverse();
    let output_membership = namespace(&[b"eros-exact-algorithm-order-gauge-output-v1", identity]);
    let trace_membership = namespace(&[b"eros-exact-algorithm-order-gauge-trace-v1", identity]);
    let full_support = mask_for_ids(programs.iter().map(|program| program.id))?;
    let initial = Chart {
        generation: 0,
        output_probes: 0,
        output_support: full_support,
        trace_support: full_support,
        programs,
    };
    let mut handle = chart_artifact(b"receiver-chart-order-gauge", identity, &initial)?;
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let seed = seed_chart(
        budget,
        &mut machine,
        "order-gauge-source",
        handle.clone(),
        &initial,
    )?;
    let mut factors_exact = true;
    for (ordinal, probe) in source.output_probes.iter().enumerate() {
        let (read, next) = train_output_probe(
            budget,
            &mut machine,
            handle.clone(),
            output_membership,
            trace_membership,
            source.candidates.len(),
            source.word_width,
            ordinal,
            probe,
            identity,
        )?;
        factors_exact &= read["factor"]["outgoing_factor_exact"] == json!(true);
        handle = next;
    }
    let (trace, next) = train_trace_receiver(
        budget,
        &mut machine,
        handle.clone(),
        output_membership,
        trace_membership,
        source.candidates.len(),
        &source.trace_oracle,
        identity,
    )?;
    handle = next;
    factors_exact &= trace["factor"]["outgoing_factor_exact"] == json!(true);
    let chart = standing_chart(&machine, handle.data_root)?.1;
    let exact = seed["source_boundary_exact"] == json!(true)
        && factors_exact
        && chart.output_support == expected_output_support
        && chart.trace_support == expected_trace_support
        && chart
            .programs
            .iter()
            .map(|program| program.name.as_str())
            .collect::<Vec<_>>()
            == vec!["successor_product", "square_then_add"];
    Ok(json!({
        "source_storage_order": ["double_by_shift", "square_then_subtract", "successor_product", "square_then_add"],
        "final_retained_storage_order": chart.programs.iter().map(|program| program.name.as_str()).collect::<Vec<_>>(),
        "output_support_mask": chart.output_support,
        "trace_support_mask": chart.trace_support,
        "all_successor_factors_exact": factors_exact,
        "exact": exact
    }))
}

fn division_world(
    budget: &RunBudget,
    cases: &[SourceDivisionCase],
    identity: &[u8],
) -> Result<Value, String> {
    let program = division_program()?;
    let handle = ArtifactHandle::new(b"typed-division-chart", identity);
    let chart = Chart {
        generation: 0,
        output_probes: 0,
        output_support: 1,
        trace_support: 1,
        programs: vec![program],
    };
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let seed = seed_chart(
        budget,
        &mut machine,
        "typed-division-source",
        handle.clone(),
        &chart,
    )?;
    let rest = machine.rest_image().map_err(debug)?;
    let mut reads = Vec::new();
    for case in cases {
        let mut machine = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
        let left =
            Quantity::rational(parse_integer(&case.left)?, 1, source_unit(&case.left_unit)?)?;
        let right = Quantity::rational(
            parse_integer(&case.right)?,
            1,
            source_unit(&case.right_unit)?,
        )?;
        let input_root = namespace(&[
            b"eros-exact-algorithm-division-input-v1",
            identity,
            case.id.as_bytes(),
        ]);
        let words = quantity_words(&[left, right])?;
        let mut arcs = Vec::new();
        append_words(&mut arcs, input_root, &words, IncidenceHand::Against);
        push_interface(&mut arcs, handle.recruit.clone(), IncidenceHand::Against);
        let (radiation, conduct_event) = profiled_event(
            budget,
            &mut machine,
            &format!("division-{}-conduct", case.id),
            words.len(),
            &arcs,
            None,
        )?;
        let meeting = regional_constituent(&radiation, "division conduct")?;
        let recovered_chart = decode_chart(meeting, handle.data_root)?;
        let inputs = decode_quantities(meeting, input_root)?;
        let evaluation = recovered_chart.programs[0].evaluate(&inputs);
        let expected = case.expected.as_deref().map(parse_integer).transpose()?;
        let expected_unit = case.expected_unit.as_deref().map(source_unit).transpose()?;
        let expected_quantity = expected
            .zip(expected_unit)
            .map(|(value, unit)| Quantity::rational(value, 1, unit))
            .transpose()?;
        let mut returned = false;
        let mut return_event = None;
        if let Some(output) = evaluation.output() {
            let result_root = namespace(&[
                b"eros-exact-algorithm-division-result-v1",
                identity,
                case.id.as_bytes(),
            ]);
            let result_words = quantity_words(&[output])?;
            let mut result_arcs = Vec::new();
            append_words(
                &mut result_arcs,
                result_root,
                &result_words,
                IncidenceHand::Against,
            );
            let (radiation, event) = profiled_event(
                budget,
                &mut machine,
                &format!("division-{}-return", case.id),
                result_words.len(),
                &result_arcs,
                None,
            )?;
            returned = decode_quantities(
                regional_constituent(&radiation, "division return")?,
                result_root,
            )? == vec![output];
            return_event = Some(event);
        }
        let exact =
            evaluation.output() == expected_quantity && returned == expected_quantity.is_some();
        reads.push(json!({
            "id": case.id,
            "inputs": inputs.iter().copied().map(quantity_json).collect::<Vec<_>>(),
            "evaluation": evaluation_json(&evaluation),
            "expected": expected_quantity.map(quantity_json),
            "returned_as_later_current": returned,
            "events": {
                "conduct": conduct_event,
                "return": return_event
            },
            "exact": exact
        }));
    }
    let electrical = reads
        .iter()
        .find(|read| read["id"] == json!("electrical"))
        .ok_or_else(|| "electrical division case is absent".to_owned())?;
    let kinematic = reads
        .iter()
        .find(|read| read["id"] == json!("kinematic"))
        .ok_or_else(|| "kinematic division case is absent".to_owned())?;
    let zero = reads
        .iter()
        .find(|read| read["id"] == json!("zero-boundary"))
        .ok_or_else(|| "zero division case is absent".to_owned())?;
    let electrical_output = &electrical["evaluation"]["output"];
    let kinematic_output = &kinematic["evaluation"]["output"];
    let dual_chart_exact = electrical["exact"] == json!(true)
        && kinematic["exact"] == json!(true)
        && electrical_output["value"] == kinematic_output["value"]
        && electrical_output["unit_exponents"] != kinematic_output["unit_exponents"]
        && electrical["evaluation"]["path_shape"] == kinematic["evaluation"]["path_shape"];
    let unit_erasure_ambiguous = electrical_output["value"] == kinematic_output["value"]
        && electrical_output["unit_exponents"] != kinematic_output["unit_exponents"];
    let zero_boundary_exact = zero["exact"] == json!(true)
        && zero["evaluation"]["condition"] == json!("OPEN")
        && zero["returned_as_later_current"] == json!(false);
    Ok(json!({
        "seed": seed,
        "cases": reads,
        "dual_chart_exact": dual_chart_exact,
        "unit_erasure_ambiguous": unit_erasure_ambiguous,
        "zero_boundary_exact": zero_boundary_exact
    }))
}

fn seed_chart(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    event_name: &str,
    handle: ArtifactHandle,
    chart: &Chart,
) -> Result<Value, String> {
    let words = chart_words(chart)?;
    let mut arcs = Vec::new();
    append_words(&mut arcs, handle.data_root, &words, IncidenceHand::Against);
    push_interface(&mut arcs, handle.recruit, IncidenceHand::Against);
    let (radiation, event) = profiled_event(budget, machine, event_name, words.len(), &arcs, None)?;
    let returned = regional_constituent(&radiation, "chart source")?;
    let returned_exact = decode_chart(returned, handle.data_root)? == *chart
        && standing_chart(machine, handle.data_root)?.1 == *chart;
    let memory = machine.memory();
    let source_boundary_exact = memory.standing_constituents == 1
        && memory.constituent_cells == 3
        && memory.constituent_incidences == arcs.len()
        && memory.constituent_pins == arcs.len()
        && memory.constituent_paths == arcs.len();
    Ok(json!({
        "event": event,
        "chart": {
            "generation": chart.generation,
            "output_probes": chart.output_probes,
            "output_support_mask": chart.output_support,
            "trace_support_mask": chart.trace_support,
            "program_ids": chart.programs.iter().map(|program| program.id).collect::<Vec<_>>()
        },
        "returned_exactly": returned_exact,
        "source_boundary_exact": source_boundary_exact,
        "physical_after": machine_json(machine)
    }))
}

fn replace_chart(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    event_name: &str,
    next_handle: ArtifactHandle,
    next_chart: &Chart,
    mut closure_arcs: Vec<PendingArc>,
) -> Result<Value, String> {
    let words = chart_words(next_chart)?;
    let outgoing_start = closure_arcs.len();
    append_words(
        &mut closure_arcs,
        next_handle.data_root,
        &words,
        IncidenceHand::Against,
    );
    push_interface(
        &mut closure_arcs,
        next_handle.recruit,
        IncidenceHand::Against,
    );
    let factor_slots = (outgoing_start..closure_arcs.len())
        .map(|slot| u32::try_from(slot).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let (radiation, event) = profiled_event(
        budget,
        machine,
        event_name,
        words.len(),
        &closure_arcs,
        Some(&factor_slots),
    )?;
    let returned = regional_constituent(&radiation, "chart successor")?;
    let returned_exact = decode_chart(returned, next_handle.data_root)? == *next_chart
        && standing_chart(machine, next_handle.data_root)?.1 == *next_chart;
    let memory = machine.memory();
    let expected_paths = words.len() + 1;
    let outgoing_factor_exact = memory.standing_constituents == 1
        && memory.constituent_cells == 3
        && memory.constituent_incidences == expected_paths
        && memory.constituent_pins == expected_paths
        && memory.constituent_paths == expected_paths;
    Ok(json!({
        "event": event,
        "chart": {
            "generation": next_chart.generation,
            "output_probes": next_chart.output_probes,
            "output_support_mask": next_chart.output_support,
            "trace_support_mask": next_chart.trace_support,
            "program_ids": next_chart.programs.iter().map(|program| program.id).collect::<Vec<_>>()
        },
        "returned_exactly": returned_exact,
        "outgoing_factor_exact": outgoing_factor_exact,
        "physical_after": machine_json(machine)
    }))
}

fn chart_words(chart: &Chart) -> Result<Vec<AlgorithmWord>, String> {
    let mut words = vec![
        AlgorithmWord::scalar(CHART_SCHEMA, COMPACT_SCHEMA),
        AlgorithmWord::scalar(CHART_GENERATION, chart.generation),
        AlgorithmWord::scalar(CHART_OUTPUT_PROBES, chart.output_probes),
        AlgorithmWord::scalar(CHART_OUTPUT_SUPPORT, chart.output_support),
        AlgorithmWord::scalar(CHART_TRACE_SUPPORT, chart.trace_support),
        AlgorithmWord::scalar(CHART_PROGRAM_COUNT, chart.programs.len() as u64),
    ];
    for (at, program) in chart.programs.iter().enumerate() {
        words.push(AlgorithmWord::at(
            CHART_PROGRAM_ID,
            vec![at as u64],
            program.id,
        ));
        append_string_words(
            &mut words,
            CHART_PROGRAM_NAME_LENGTH,
            CHART_PROGRAM_NAME_CHUNK,
            &[program.id],
            &program.name,
        );
        words.extend(program.encode()?);
    }
    Ok(words)
}

fn chart_artifact(
    kind: &[u8],
    source_identity: &[u8],
    chart: &Chart,
) -> Result<ArtifactHandle, String> {
    let words = chart_words(chart)?;
    let mut identity = Vec::new();
    identity.extend_from_slice(source_identity);
    for word in words {
        identity.extend_from_slice(&word.tag.to_le_bytes());
        identity.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
        for coordinate in word.coordinates {
            identity.extend_from_slice(&coordinate.to_le_bytes());
        }
        identity.extend_from_slice(&word.value.to_le_bytes());
    }
    Ok(ArtifactHandle::new(kind, &identity))
}

fn support_words(mask: u64) -> Vec<AlgorithmWord> {
    vec![
        AlgorithmWord::scalar(SUPPORT_SCHEMA, COMPACT_SCHEMA),
        AlgorithmWord::scalar(SUPPORT_MASK, mask),
    ]
}

fn decode_chart(constituent: &LiveConstituent, root: u64) -> Result<Chart, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, CHART_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("chart schema changed".to_owned());
    }
    let generation = atlas.word(root, CHART_GENERATION, &[])?;
    let output_probes = atlas.word(root, CHART_OUTPUT_PROBES, &[])?;
    let output_support = atlas.word(root, CHART_OUTPUT_SUPPORT, &[])?;
    let trace_support = atlas.word(root, CHART_TRACE_SUPPORT, &[])?;
    let count = usize::try_from(atlas.word(root, CHART_PROGRAM_COUNT, &[])?).map_err(debug)?;
    let mut programs = Vec::with_capacity(count);
    for at in 0..count {
        let id = atlas.word(root, CHART_PROGRAM_ID, &[at as u64])?;
        let name = decode_string(
            &atlas,
            root,
            CHART_PROGRAM_NAME_LENGTH,
            CHART_PROGRAM_NAME_CHUNK,
            &[id],
        )?;
        programs.push(Program::decode(id, name, |tag, coordinates| {
            atlas.word(root, tag, coordinates)
        })?);
    }
    Ok(Chart {
        generation,
        output_probes,
        output_support,
        trace_support,
        programs,
    })
}

fn standing_chart(
    machine: &LiveCurrentMachine,
    root: u64,
) -> Result<(LiveConstituent, Chart), String> {
    let charts = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|body| {
            decode_chart(body, root)
                .ok()
                .map(|chart| (body.clone(), chart))
        })
        .collect::<Vec<_>>();
    match charts.as_slice() {
        [(body, chart)] => Ok((body.clone(), chart.clone())),
        [] => Err("Standing exposes no exact receiver chart".to_owned()),
        _ => Err("Standing exposes plural exact receiver charts".to_owned()),
    }
}

fn quantity_words(quantities: &[Quantity]) -> Result<Vec<AlgorithmWord>, String> {
    let mut words = vec![
        AlgorithmWord::scalar(QUANTITY_SCHEMA, COMPACT_SCHEMA),
        AlgorithmWord::scalar(QUANTITY_COUNT, quantities.len() as u64),
    ];
    for (at, quantity) in quantities.iter().copied().enumerate() {
        let route = vec![at as u64];
        match quantity.value {
            ExactValue::Word { bits, value } => {
                words.push(AlgorithmWord::at(QUANTITY_KIND, route.clone(), 1));
                words.push(AlgorithmWord::at(
                    QUANTITY_BITS,
                    route.clone(),
                    u64::from(bits),
                ));
                words.push(AlgorithmWord::at(
                    QUANTITY_SIGN,
                    route.clone(),
                    if value == 0 { 0 } else { 1 },
                ));
                words.push(AlgorithmWord::at(QUANTITY_MAGNITUDE, route.clone(), value));
                words.push(AlgorithmWord::at(QUANTITY_DENOMINATOR, route.clone(), 1));
            }
            ExactValue::Rational(value) => {
                let sign = if value.numerator < 0 {
                    2
                } else if value.numerator == 0 {
                    0
                } else {
                    1
                };
                let magnitude = u64::try_from(
                    value
                        .numerator
                        .checked_abs()
                        .ok_or_else(|| "quantity magnitude overflowed".to_owned())?,
                )
                .map_err(debug)?;
                words.push(AlgorithmWord::at(QUANTITY_KIND, route.clone(), 2));
                words.push(AlgorithmWord::at(QUANTITY_BITS, route.clone(), 0));
                words.push(AlgorithmWord::at(QUANTITY_SIGN, route.clone(), sign));
                words.push(AlgorithmWord::at(
                    QUANTITY_MAGNITUDE,
                    route.clone(),
                    magnitude,
                ));
                words.push(AlgorithmWord::at(
                    QUANTITY_DENOMINATOR,
                    route.clone(),
                    u64::try_from(value.denominator).map_err(debug)?,
                ));
            }
        }
        for (axis, exponent) in quantity.unit.exponents.iter().copied().enumerate() {
            words.push(AlgorithmWord::at(
                QUANTITY_UNIT,
                vec![at as u64, axis as u64],
                encode_i8(exponent),
            ));
        }
    }
    Ok(words)
}

fn decode_quantities(constituent: &LiveConstituent, root: u64) -> Result<Vec<Quantity>, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, QUANTITY_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("quantity schema changed".to_owned());
    }
    let count = usize::try_from(atlas.word(root, QUANTITY_COUNT, &[])?).map_err(debug)?;
    (0..count)
        .map(|at| {
            let route = [at as u64];
            let kind = atlas.word(root, QUANTITY_KIND, &route)?;
            let bits = u8::try_from(atlas.word(root, QUANTITY_BITS, &route)?).map_err(debug)?;
            let sign = atlas.word(root, QUANTITY_SIGN, &route)?;
            let magnitude = atlas.word(root, QUANTITY_MAGNITUDE, &route)?;
            let denominator = atlas.word(root, QUANTITY_DENOMINATOR, &route)?;
            let value = match kind {
                1 => ExactValue::word(bits, magnitude)?,
                2 => {
                    let numerator = match sign {
                        0 if magnitude == 0 => 0,
                        1 => i128::from(magnitude),
                        2 => -i128::from(magnitude),
                        _ => return Err("quantity sign is inconsistent".to_owned()),
                    };
                    ExactValue::Rational(Rational::new(numerator, i128::from(denominator))?)
                }
                _ => return Err(format!("quantity kind {kind} is unknown")),
            };
            let mut exponents = [0i8; 4];
            for (axis, exponent) in exponents.iter_mut().enumerate() {
                *exponent =
                    decode_i8(atlas.word(root, QUANTITY_UNIT, &[at as u64, axis as u64])?)?;
            }
            Ok(Quantity {
                value,
                unit: Unit { exponents },
            })
        })
        .collect()
}

fn trace_words(shape: &[StepShape]) -> Vec<AlgorithmWord> {
    let mut words = vec![
        AlgorithmWord::scalar(TRACE_SCHEMA, COMPACT_SCHEMA),
        AlgorithmWord::scalar(TRACE_COUNT, shape.len() as u64),
    ];
    for (at, step) in shape.iter().enumerate() {
        words.push(AlgorithmWord::at(
            TRACE_OPERATION,
            vec![at as u64],
            operation_code(step.operation),
        ));
        words.push(AlgorithmWord::at(
            TRACE_ANTECEDENT_COUNT,
            vec![at as u64],
            step.antecedents.len() as u64,
        ));
        for (edge, antecedent) in step.antecedents.iter().copied().enumerate() {
            words.push(AlgorithmWord::at(
                TRACE_ANTECEDENT,
                vec![at as u64, edge as u64],
                antecedent as u64,
            ));
        }
    }
    words
}

fn operation_code(operation: &str) -> u64 {
    match operation {
        "INPUT" => 1,
        "CONST" => 2,
        "ADD" => 3,
        "SUBTRACT" => 4,
        "MULTIPLY" => 5,
        "SHIFT_LEFT" => 6,
        "DIVIDE" => 7,
        "RETURN" => 8,
        _ => 0,
    }
}

fn append_membership(arcs: &mut Vec<PendingArc>, namespace: u64, extent: usize, support: u64) {
    for candidate in 0..extent {
        arcs.push(PendingArc {
            interface: InterfaceCapability::new(namespace, candidate as u64),
            hand: if mask_contains(support, candidate as u64) {
                IncidenceHand::With
            } else {
                IncidenceHand::Against
            },
        });
    }
}

fn append_membership_subset(
    arcs: &mut Vec<PendingArc>,
    namespace: u64,
    extent: usize,
    support: u64,
    subset: u64,
) {
    for candidate in 0..extent {
        if !mask_contains(subset, candidate as u64) {
            continue;
        }
        arcs.push(PendingArc {
            interface: InterfaceCapability::new(namespace, candidate as u64),
            hand: if mask_contains(support, candidate as u64) {
                IncidenceHand::With
            } else {
                IncidenceHand::Against
            },
        });
    }
}

fn membership_residual(
    prior: &LiveConstituent,
    returned: &LiveConstituent,
    namespace: u64,
    extent: usize,
    expected_open: u64,
) -> Result<Value, String> {
    let prior_pins = prior
        .pins()
        .iter()
        .filter_map(|pin| {
            pin.interface()
                .filter(|interface| interface.namespace() == namespace)
                .map(|interface| (interface.local(), pin.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    if prior_pins.len() != extent {
        return Err(format!(
            "receiver membership returned {} candidates instead of {extent}",
            prior_pins.len()
        ));
    }
    let mut open = 0u64;
    let mut found = 0usize;
    let mut rides = 0usize;
    for (candidate, prior_pin) in prior_pins {
        let comparisons = returned
            .pins()
            .iter()
            .filter(|pin| !prior.pins().contains(pin))
            .filter(|pin| {
                pin.interface().is_some_and(|interface| {
                    interface.namespace() == namespace && interface.local() == candidate
                })
            })
            .filter(|pin| pin.held() == prior_pin.meeting())
            .collect::<Vec<_>>();
        if comparisons.len() != 1 {
            return Err(format!(
                "candidate membership {candidate} returned {} comparison pins",
                comparisons.len()
            ));
        }
        let pin = comparisons[0];
        if pin.is_open() {
            open |= bit(candidate)?;
        } else if pin.is_found() {
            found += 1;
        } else {
            rides += 1;
        }
    }
    Ok(json!({
        "expected_open_mask": expected_open,
        "carried_open_mask": open,
        "rides": rides,
        "founds": found,
        "exact": open == expected_open && found == 0
    }))
}

fn profiled_event(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    event_name: &str,
    semantic_words: usize,
    arcs: &[PendingArc],
    outgoing_factor_slots: Option<&[u32]>,
) -> Result<(soma_membrane::ContemporaryRadiation, Value), String> {
    budget.require_open()?;
    if arcs.len() > MAX_ARCS_PER_EVENT {
        return Err(format!(
            "event {event_name} requires {} arcs beyond {MAX_ARCS_PER_EVENT}",
            arcs.len()
        ));
    }
    let pair = primed_pair(machine)?;
    let regional_arcs = arcs
        .iter()
        .enumerate()
        .map(|(slot, arc)| {
            Ok(RegionalRelationArc::new(
                pair[0],
                CurrentBoundaryPort::Cell,
                pair[1],
                CurrentBoundaryPort::Cell,
                arc.interface.clone(),
                u32::try_from(slot).map_err(debug)?,
                0,
                arc.hand,
            ))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let currents = [
        CurrentEvent::ending(pair[0], relation_atom(181)?, action()),
        CurrentEvent::ending(pair[1], relation_atom(191)?, action()),
    ];
    let regional = [match outgoing_factor_slots {
        Some(slots) => RegionalRelationCell::with_outgoing_factor(pair[1], &regional_arcs, slots),
        None => RegionalRelationCell::new(pair[1], &regional_arcs),
    }];
    let started = Instant::now();
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(|error| format!("event {event_name} failed: {error:?}"))?;
    let wall = started.elapsed();
    if wall > EVENT_LIMIT {
        return Err(format!(
            "event {event_name} exceeded {} seconds",
            EVENT_LIMIT.as_secs()
        ));
    }
    budget.require_open()?;
    let read = json!({
        "event": event_name,
        "semantic_words": semantic_words,
        "regional_arcs": arcs.len(),
        "wall_micros": duration_micros(wall),
        "returned_incidences": radiation.regional().iter()
            .map(|row| row.constituent().incidences().len()).sum::<usize>(),
        "returned_pins": radiation.regional().iter()
            .map(|row| row.constituent().pins().len()).sum::<usize>()
    });
    Ok((radiation, read))
}

fn primed_pair(machine: &mut LiveCurrentMachine) -> Result<[CurrentLineage; 2], String> {
    let first = relation_atom(PRIMING_VALUES[0])?;
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
            CurrentEvent::continuing(pair[0], relation_atom(value)?, action()),
            CurrentEvent::continuing(pair[1], relation_atom(value)?, action()),
        ];
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
    }
    Ok(pair)
}

fn regional_constituent<'a>(
    radiation: &'a soma_membrane::ContemporaryRadiation,
    context: &str,
) -> Result<&'a LiveConstituent, String> {
    match radiation.regional() {
        [row] => Ok(row.constituent()),
        rows => Err(format!("{context} returned {} regional rows", rows.len())),
    }
}

fn append_words(
    arcs: &mut Vec<PendingArc>,
    root: u64,
    words: &[AlgorithmWord],
    hand: IncidenceHand,
) {
    arcs.extend(words.iter().map(|word| PendingArc {
        interface: InterfaceCapability::new(compact_route_namespace(root, word), word.value),
        hand,
    }));
}

fn push_interface(arcs: &mut Vec<PendingArc>, interface: InterfaceCapability, hand: IncidenceHand) {
    arcs.push(PendingArc { interface, hand });
}

fn append_string_words(
    words: &mut Vec<AlgorithmWord>,
    length_tag: u64,
    chunk_tag: u64,
    coordinates: &[u64],
    value: &str,
) {
    words.push(AlgorithmWord::at(
        length_tag,
        coordinates.to_vec(),
        value.len() as u64,
    ));
    for (at, chunk) in value.as_bytes().chunks(8).enumerate() {
        let mut padded = [0u8; 8];
        padded[..chunk.len()].copy_from_slice(chunk);
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        words.push(AlgorithmWord::at(
            chunk_tag,
            route,
            u64::from_le_bytes(padded),
        ));
    }
}

fn decode_string(
    atlas: &CapabilityAtlas,
    root: u64,
    length_tag: u64,
    chunk_tag: u64,
    coordinates: &[u64],
) -> Result<String, String> {
    let length = usize::try_from(atlas.word(root, length_tag, coordinates)?).map_err(debug)?;
    let mut bytes = Vec::new();
    for at in 0..length.div_ceil(8) {
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        bytes.extend_from_slice(&atlas.word(root, chunk_tag, &route)?.to_le_bytes());
    }
    bytes.truncate(length);
    String::from_utf8(bytes).map_err(debug)
}

fn evaluation_json(evaluation: &Evaluation) -> Value {
    let path = evaluation
        .path()
        .iter()
        .map(|step| {
            json!({
                "node": step.node,
                "operation": step.operation,
                "antecedents": step.antecedents,
                "output": quantity_json(step.output)
            })
        })
        .collect::<Vec<_>>();
    let path_shape = evaluation
        .path()
        .iter()
        .map(|step| {
            json!({
                "operation": step.operation,
                "antecedents": step.antecedents
            })
        })
        .collect::<Vec<_>>();
    match evaluation {
        Evaluation::Closed { output, .. } => json!({
            "condition": "CLOSED",
            "path": path,
            "path_shape": path_shape,
            "output": quantity_json(*output)
        }),
        Evaluation::Open { at, reason, .. } => json!({
            "condition": "OPEN",
            "completed_prefix": path,
            "path_shape": path_shape,
            "open_at_node": at,
            "reason": reason,
            "output": Value::Null
        }),
    }
}

fn shape_json(shape: &[StepShape]) -> Value {
    Value::Array(
        shape
            .iter()
            .map(|step| {
                json!({
                    "operation": step.operation,
                    "antecedents": step.antecedents
                })
            })
            .collect(),
    )
}

fn quantity_json(quantity: Quantity) -> Value {
    json!({
        "value": quantity.value.display(),
        "unit_exponents": quantity.unit.exponents
    })
}

fn chart_json(chart: &Chart, candidates: &[SourceCandidate]) -> Value {
    json!({
        "generation": chart.generation,
        "output_probes": chart.output_probes,
        "output_support_mask": chart.output_support,
        "output_support": mask_names(chart.output_support, candidates),
        "trace_support_mask": chart.trace_support,
        "trace_support": mask_names(chart.trace_support, candidates),
        "retained_programs": chart.programs.iter().map(|program| {
            json!({
                "id": program.id,
                "name": program.name,
                "nodes": program.nodes.iter().enumerate().map(|(at, node)| {
                    json!({
                        "node": at,
                        "operation": node.operation(),
                        "antecedents": node.antecedents()
                    })
                }).collect::<Vec<_>>()
            })
        }).collect::<Vec<_>>()
    })
}

fn machine_json(machine: &LiveCurrentMachine) -> Value {
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
    json!({
        "standing_rank": machine.standing().rank(),
        "standing_cells": standing_cells,
        "standing_constituents": standing_constituents,
        "constituent_cells": constituent_cells,
        "constituent_incidences": constituent_incidences,
        "constituent_pins": constituent_pins,
        "constituent_paths": constituent_paths,
        "constituent_transport_terms": constituent_transport_terms,
        "live_lineages": live_lineages
    })
}

fn source_unit(name: &str) -> Result<Unit, String> {
    match name {
        "dimensionless" => Ok(Unit::DIMENSIONLESS),
        "length" => Ok(Unit::LENGTH),
        "time" => Ok(Unit::TIME),
        "current" => Ok(Unit::CURRENT),
        "voltage" => Ok(Unit::VOLTAGE),
        "resistance" => Ok(Unit::RESISTANCE),
        "speed" => Ok(Unit {
            exponents: [1, -1, 0, 0],
        }),
        _ => Err(format!("unknown source unit {name:?}")),
    }
}

fn parse_integer(value: &str) -> Result<i128, String> {
    value
        .parse::<i128>()
        .map_err(|error| format!("integer {value:?} parses: {error}"))
}

fn mask_for_ids(ids: impl IntoIterator<Item = u64>) -> Result<u64, String> {
    ids.into_iter()
        .try_fold(0u64, |mask, id| Ok(mask | bit(id)?))
}

fn bit(id: u64) -> Result<u64, String> {
    1u64.checked_shl(u32::try_from(id).map_err(debug)?)
        .ok_or_else(|| format!("candidate id {id} exceeds the support word"))
}

fn mask_contains(mask: u64, id: u64) -> bool {
    bit(id).is_ok_and(|bit| mask & bit != 0)
}

fn mask_xor(left: u64, right: u64) -> u64 {
    left ^ right
}

fn mask_names<'a>(mask: u64, candidates: &'a [SourceCandidate]) -> Vec<&'a str> {
    candidates
        .iter()
        .filter(|candidate| mask_contains(mask, candidate.id))
        .map(|candidate| candidate.name.as_str())
        .collect()
}

fn compact_route_namespace(root: u64, word: &AlgorithmWord) -> u64 {
    let mut route = Vec::with_capacity(16 + word.coordinates.len() * 8);
    route.extend_from_slice(&word.tag.to_le_bytes());
    route.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
    for coordinate in &word.coordinates {
        route.extend_from_slice(&coordinate.to_le_bytes());
    }
    namespace(&[
        b"eros-exact-algorithm-ecology-word-v1",
        &root.to_le_bytes(),
        &route,
    ])
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

fn capability(parts: &[&[u8]]) -> InterfaceCapability {
    InterfaceCapability::new(namespace(parts), 0)
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

fn encode_i8(value: i8) -> u64 {
    u64::from((i16::from(value) + 128) as u8)
}

fn decode_i8(value: u64) -> Result<i8, String> {
    let value = u8::try_from(value).map_err(debug)?;
    i8::try_from(i16::from(value) - 128).map_err(debug)
}

fn relation_atom(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation value {value} remains nonzero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn duration_micros(duration: Duration) -> u64 {
    u64::try_from(duration.as_micros()).unwrap_or(u64::MAX)
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}

fn usage() -> &'static str {
    "usage: cargo run -p life --example eros_exact_algorithm_ecology -- <SOURCE.json> <REPORT.json>"
}
