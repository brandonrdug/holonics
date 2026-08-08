use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use body::incidence::IncidenceHand;
use body::num::Cog;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage, LiveMemory,
    ParallelHostLiveCurrentExecutor, RegionalRelationArc, RegionalRelationCell,
    SparseStandingSurface,
};
use life::form_mouth::deposit_form_or_message;

/// This driver's name at the plate mouth: `output/eros_residual_chart_cultivation/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_residual_chart_cultivation";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";

const SOURCE_SCHEMA: &str = "eros.residual-chart-cultivation.source.v1";
const REPORT_SCHEMA: &str = "eros.residual-chart-cultivation.report.v2";
const OBSERVATION_ID: &str = "eros-residual-chart-cultivation-01";
const RESULT_OBSERVATION_ID: &str = "eros-consequential-successor-factor-01";
const COMPACT_SCHEMA: u64 = 1;
const MAX_ARCS_PER_EVENT: usize = 1024;
const EVENT_LIMIT: Duration = Duration::from_secs(15);
const RUN_LIMIT: Duration = Duration::from_secs(120);
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];

const CHART_SCHEMA: u64 = 1;
const CHART_ROOT: u64 = 2;
const CHART_NODE_COUNT: u64 = 3;
const CHART_FEATURE_COUNT: u64 = 4;
const CHART_SAMPLE_COUNT: u64 = 5;
const CHART_FEATURE_LENGTH: u64 = 10;
const CHART_FEATURE_CHUNK: u64 = 11;
const CHART_NODE_SPLIT: u64 = 20;
const CHART_NODE_DISTRIBUTION_COUNT: u64 = 21;
const CHART_DISTRIBUTION_TAXON_LENGTH: u64 = 22;
const CHART_DISTRIBUTION_TAXON_CHUNK: u64 = 23;
const CHART_DISTRIBUTION_COUNT: u64 = 24;
const CHART_NODE_CHILD_COUNT: u64 = 25;
const CHART_CHILD_VALUE_LENGTH: u64 = 26;
const CHART_CHILD_VALUE_CHUNK: u64 = 27;
const CHART_CHILD_NODE: u64 = 28;

const CURRENT_SCHEMA: u64 = 101;
const CURRENT_ORDINAL: u64 = 102;
const CURRENT_FEATURE_COUNT: u64 = 103;
const CURRENT_ID_LENGTH: u64 = 104;
const CURRENT_ID_CHUNK: u64 = 105;
const CURRENT_FEATURE_LENGTH: u64 = 110;
const CURRENT_FEATURE_CHUNK: u64 = 111;

const PREDICTION_SCHEMA: u64 = 201;
const PREDICTION_COUNT: u64 = 202;
const PREDICTION_TAXON_LENGTH: u64 = 210;
const PREDICTION_TAXON_CHUNK: u64 = 211;
const PREDICTION_TAXON_COUNT: u64 = 212;

const ACTUAL_SCHEMA: u64 = 301;
const ACTUAL_TAXON_LENGTH: u64 = 310;
const ACTUAL_TAXON_CHUNK: u64 = 311;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    source: Value,
    training_law: TrainingLaw,
    taxa: Vec<SourceTaxon>,
    events: Vec<SourceEvent>,
    expected_trajectory: Value,
    checkpoints: Vec<SourceCheckpoint>,
    expected_final_diagram: Diagram,
    expected_relation_counts: BTreeMap<String, usize>,
    stopping_condition: String,
}

#[derive(Clone, Deserialize, Serialize)]
struct TrainingLaw {
    feature_order: Vec<String>,
    taxon_identity: String,
    prediction: String,
    fold: String,
    reduce: String,
    relations: Vec<String>,
    numerical_law: String,
}

#[derive(Deserialize)]
struct SourceTaxon {
    identity: String,
    face: Value,
    total_count: usize,
}

#[derive(Clone, Deserialize)]
struct SourceEvent {
    ordinal: usize,
    current_id: String,
    interfaces: BTreeMap<String, String>,
    actual_taxon: String,
    actual_face: Value,
}

#[derive(Deserialize)]
struct SourceCheckpoint {
    name: String,
    after_events: usize,
    diagram: Diagram,
    probes: Vec<SourceProbe>,
}

#[derive(Deserialize)]
struct SourceProbe {
    event_ordinal: usize,
    current_id: String,
    distribution: Vec<DistributionRead>,
    relation_to_withheld_actual: String,
    actual_taxon: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Sample {
    ordinal: usize,
    current_id: String,
    features: Vec<String>,
    taxon: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Node {
    distribution: BTreeMap<String, usize>,
    split: Option<usize>,
    children: BTreeMap<String, Node>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Shape {
    distribution: Vec<(String, usize, usize)>,
    split: Option<usize>,
    children: Vec<(String, Shape)>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
struct DistributionRead {
    taxon: String,
    count: usize,
    quotient: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
struct ChildRead {
    value: String,
    node: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
struct NodeRead {
    ordinal: usize,
    distribution: Vec<DistributionRead>,
    split: Option<String>,
    children: Vec<ChildRead>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
struct Diagram {
    root: usize,
    nodes: Vec<NodeRead>,
    sha256: String,
    internal_nodes: usize,
    leaf_nodes: usize,
}

#[derive(Clone)]
struct ChartState {
    node: Node,
    diagram: Diagram,
    words: Vec<CompactWord>,
    handle: ArtifactHandle,
}

#[derive(Clone)]
struct CheckpointState {
    after_events: usize,
    rest: LiveCurrentRestImage,
    chart: ChartState,
}

#[derive(Clone, Debug)]
struct CompactWord {
    tag: u64,
    coordinates: Vec<u64>,
    value: u64,
}

#[derive(Clone)]
struct PendingArc {
    interface: InterfaceCapability,
    boundary_slot: u32,
    arc_slot: u32,
    hand: IncidenceHand,
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
            None => Err(format!(
                "compact route {tag}:{coordinates:?} is absent under {root:#018x}"
            )),
        }
    }
}

#[derive(Clone)]
struct ArtifactHandle {
    data_namespace: u64,
    recruit: InterfaceCapability,
}

impl ArtifactHandle {
    fn new(kind: &[u8], identity: &[u8]) -> Self {
        Self {
            data_namespace: namespace(&[
                b"eros-residual-chart-cultivation-data-v1",
                kind,
                identity,
            ]),
            recruit: InterfaceCapability::new(
                namespace(&[
                    b"eros-residual-chart-cultivation-recruit-v1",
                    kind,
                    identity,
                ]),
                0,
            ),
        }
    }
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
            Err("the bounded residual-chart run exceeded two minutes".to_owned())
        } else {
            Ok(())
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros residual chart cultivation: {error}");
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
        .map_err(|error| format!("residual-chart report encodes: {error}"))?;
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
        "eros residual chart cultivation: accepted · {} bytes · {}",
        report_bytes.len(),
        report_path.display()
    );
    Ok(())
}

fn run_host(source: Source, source_sha256: String) -> Result<Value, String> {
    let run_started = Instant::now();
    validate_source(&source)?;
    let samples = source_samples(&source)?;
    let independently_derived = derive_trajectory(&samples, &source.training_law.feature_order)?;
    if independently_derived != source.expected_trajectory {
        return Err("the Rust derivation disagrees with the fixed source trajectory".to_owned());
    }

    let budget = RunBudget::new();
    let host_threads = std::thread::available_parallelism()
        .map(usize::from)
        .unwrap_or(1)
        .clamp(1, 8);
    let taxa = source
        .taxa
        .iter()
        .map(|taxon| taxon.identity.clone())
        .collect::<Vec<_>>();
    let control = no_diagram_control(
        &budget,
        host_threads,
        &samples[0],
        &source.training_law.feature_order,
    )?;

    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let mut standing_samples = Vec::new();
    let mut chart: Option<ChartState> = None;
    let mut trajectory = Vec::with_capacity(samples.len());
    let mut checkpoints = Vec::new();
    let mut relation_counts: BTreeMap<String, usize> = BTreeMap::new();
    let mut every_lower_carrier_departed = true;
    let mut every_machine_residual_exact = true;
    let mut every_chart_returned_exact = true;
    let mut every_outgoing_factor_exact = true;
    let checkpoint_extents = source
        .checkpoints
        .iter()
        .map(|checkpoint| checkpoint.after_events)
        .collect::<BTreeSet<_>>();

    for sample in &samples {
        let outcome = train_one(
            &budget,
            host_threads,
            &mut machine,
            chart.as_ref(),
            &mut standing_samples,
            sample,
            &source.training_law.feature_order,
            &taxa,
        )?;
        *relation_counts.entry(outcome.relation.clone()).or_default() += 1;
        every_lower_carrier_departed &= outcome.lower_carriers_departed;
        every_machine_residual_exact &= outcome.machine_residual_exact;
        every_chart_returned_exact &= outcome.chart_returned_exact;
        every_outgoing_factor_exact &= outcome.outgoing_factor_exact;
        chart = Some(outcome.chart.clone());
        trajectory.push(outcome.read);

        if checkpoint_extents.contains(&standing_samples.len()) {
            let rest = machine.rest_image().map_err(debug)?;
            let remounted = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
            if remounted.rest_image().map_err(debug)? != rest {
                return Err(format!(
                    "checkpoint {} changed across exact rest/remount",
                    standing_samples.len()
                ));
            }
            checkpoints.push(CheckpointState {
                after_events: standing_samples.len(),
                rest,
                chart: outcome.chart,
            });
        }
    }

    let final_chart = chart.ok_or_else(|| "the chronology emitted no final chart".to_owned())?;
    if final_chart.diagram != source.expected_final_diagram {
        return Err("the final chart differs from the fixed exact diagram".to_owned());
    }
    if relation_counts != source.expected_relation_counts {
        return Err(format!(
            "the measured relation counts changed: {relation_counts:?}"
        ));
    }

    let checkpoint_reads = run_checkpoint_probes(
        &budget,
        host_threads,
        &source,
        &samples,
        &taxa,
        &checkpoints,
    )?;
    let final_rest = machine.rest_image().map_err(debug)?;
    let final_remount = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let final_chart_after_remount = standing_chart(
        &final_remount,
        final_chart.handle.clone(),
        &source.training_law.feature_order,
    )?;
    let exact_rest_remount = final_remount.rest_image().map_err(debug)? == final_rest
        && final_chart_after_remount == final_chart.diagram;
    let source_lineages_departed = final_remount.memory().live_lineages == 0;
    let final_machine = machine_read(&final_remount)?;

    let root = &final_chart.diagram.nodes[final_chart.diagram.root];
    let branch_reads = root
        .children
        .iter()
        .map(|child| {
            let node = &final_chart.diagram.nodes[child.node];
            json!({
                "operation": child.value,
                "distribution": node.distribution,
                "next_split": node.split,
                "children": node.children,
            })
        })
        .collect::<Vec<_>>();
    let equal_root_marginals = branch_reads.iter().all(|branch| {
        branch["distribution"].as_array().is_some_and(|rows| {
            rows.iter()
                .map(|row| row["quotient"].as_str())
                .collect::<Vec<_>>()
                == vec![Some("1/3"), Some("2/3")]
        })
    });
    let distinct_conditional_geometry = branch_reads
        .iter()
        .filter_map(|branch| branch["next_split"].as_str())
        .collect::<BTreeSet<_>>()
        == BTreeSet::from(["condition", "context"]);

    let acceptance = json!({
        "fixed_source_validated": true,
        "independent_exact_trajectory_matched": true,
        "no_diagram_control_emitted_no_distribution": control["distribution"] == json!([]),
        "all_twelve_actual_returns_changed_or_recurred_through_the_chart": trajectory.len() == 12,
        "measured_relation_counts_matched": relation_counts == source.expected_relation_counts,
        "every_machine_membership_residual_was_exact": every_machine_residual_exact,
        "every_updated_chart_returned_exactly": every_chart_returned_exact,
        "every_outgoing_factor_was_the_complete_active_chart_boundary": every_outgoing_factor_exact,
        "event_local_and_replaced_chart_carriers_departed": every_lower_carrier_departed,
        "equal_marginals_retained_distinct_conditional_geometry": equal_root_marginals && distinct_conditional_geometry,
        "all_source_absent_checkpoint_probes_matched": checkpoint_reads.iter().all(|read| read["accepted"] == json!(true)),
        "final_chart_survived_exact_rest_remount": exact_rest_remount,
        "source_lineages_departed": source_lineages_departed,
        "no_floating_point_causal_data": true,
    });
    let accepted = acceptance
        .as_object()
        .expect("acceptance is an object")
        .values()
        .all(|value| value == &json!(true));
    if !accepted {
        return Err(format!(
            "the residual-chart acceptance did not close: {acceptance}"
        ));
    }
    budget.require_open()?;

    Ok(json!({
        "schema": REPORT_SCHEMA,
        "observation_id": RESULT_OBSERVATION_ID,
        "status": "accepted",
        "question": "Can a changing local consequence chart be cultivated from arbitrary source-declared categorical interfaces and genuinely later exact returns, while preserving conditional geometry that its marginal recurrence quotient loses?",
        "theory_to_structure": "The source contributes one ordered categorical interface current. Existing chart Standing and that current meet first. The world derives and returns the chart's exact recurrence distribution. A genuinely later source consequence meets that returned support field, producing an exact membership residual. Only then does the world fold the occurrence, reduce equal conditional continuations, and return one replacement chart through the same live lineage. Replaced chart and event-local carriers cease active participation.",
        "boundary": "This is a general categorical chart-update law exercised on one retained transformer-derived ecology. The source still declares operation/context/condition identities and exact receiver taxa. It is not a universal classifier, a model distillation, or evidence that the upstream transformer can be omitted.",
        "stopping_condition": source.stopping_condition,
        "source": {
            "source_json_sha256": source_sha256,
            "upstream": source.source,
            "events": samples.len(),
            "taxa": taxa.len(),
            "feature_order": source.training_law.feature_order,
        },
        "training_contract": source.training_law,
        "physical_execution": {
            "executor": "ParallelHostLiveCurrentExecutor",
            "host_threads": host_threads,
            "semantic_training_events": samples.len(),
            "machine_transitions_per_training_event": 4,
            "model_reruns": 0,
            "feature_searches": 0,
            "fixture_retries": 0,
        },
        "control": control,
        "online_trajectory": trajectory,
        "relation_counts": relation_counts,
        "checkpoints": checkpoint_reads,
        "final_conditional_geometry": {
            "root_distribution": root.distribution,
            "root_split": root.split,
            "operation_branches": branch_reads,
            "same_marginal_quotients": equal_root_marginals,
            "different_next_axes": distinct_conditional_geometry,
        },
        "final_diagram": final_chart.diagram.clone(),
        "participation": {
            "source_interface_words_per_event": source.training_law.feature_order.len(),
            "later_actual_taxon_words_per_event": 1,
            "retained_active_event_bodies": 0,
            "final_chart_nodes": final_chart.node_count(),
            "final_chart_compact_words": final_chart.words.len(),
            "scope": "Counts describe the Eros membrane carrier only; they do not claim reduced upstream transformer compute.",
        },
        "final_machine": final_machine,
        "acceptance": acceptance,
        "run_wall_micros": duration_micros(run_started.elapsed()),
        "conclusion": "The marginal 1/3:2/3 recurrence quotient is insufficient: both operation regions share it. The returned residual causes the final chart to retain a condition split under drop-then-reverse and a context split under reverse-then-drop. The result is a changing local conditional ecology, not a detached skill: its useful continuation depends on the current interfaces, the chart that stands, and the later consequence that actually returns.",
    }))
}

impl ChartState {
    fn node_count(&self) -> usize {
        self.diagram.nodes.len()
    }
}

struct TrainingOutcome {
    chart: ChartState,
    relation: String,
    lower_carriers_departed: bool,
    machine_residual_exact: bool,
    chart_returned_exact: bool,
    outgoing_factor_exact: bool,
    read: Value,
}

#[allow(clippy::too_many_arguments)]
fn train_one(
    budget: &RunBudget,
    host_threads: usize,
    machine: &mut LiveCurrentMachine,
    prior_chart: Option<&ChartState>,
    standing_samples: &mut Vec<Sample>,
    sample: &Sample,
    feature_order: &[String],
    taxa: &[String],
) -> Result<TrainingOutcome, String> {
    let before = prior_chart
        .map(|chart| diagram_summary(&chart.diagram))
        .unwrap_or_else(empty_diagram_summary);
    let current_words = current_words(sample);
    let current_handle = ArtifactHandle::new(b"current", sample.current_id.as_bytes());
    let meeting_recruit = capability(&[
        b"eros-residual-chart-cultivation-meeting-v1",
        sample.current_id.as_bytes(),
    ]);

    let mut meeting_arcs = Vec::new();
    append_words(
        &mut meeting_arcs,
        current_handle.data_namespace,
        &current_words,
    )?;
    if let Some(chart) = prior_chart {
        push_interface(
            &mut meeting_arcs,
            chart.handle.recruit.clone(),
            IncidenceHand::Against,
        )?;
    }
    push_interface(
        &mut meeting_arcs,
        meeting_recruit.clone(),
        IncidenceHand::Against,
    )?;
    let (meeting_radiation, meeting_event) = profiled_event(
        budget,
        host_threads,
        machine,
        &format!("current-{}", sample.ordinal),
        current_words.len(),
        &meeting_arcs,
        None,
    )?;
    let meeting = regional_constituent(&meeting_radiation, "current/chart meeting")?;
    let recovered_current = decode_current(meeting, current_handle.data_namespace)?;
    if !same_current(&recovered_current, sample) {
        return Err(format!(
            "event {} changed its source current",
            sample.current_id
        ));
    }
    let prediction = if let Some(chart) = prior_chart {
        let recovered = decode_chart(meeting, chart.handle.data_namespace, feature_order)?.2;
        if recovered != chart.diagram {
            return Err(format!(
                "event {} changed the chart during contact",
                sample.current_id
            ));
        }
        predict(&chart.node, sample)
    } else {
        BTreeMap::new()
    };

    let prediction_words = prediction_words(&prediction);
    let prediction_identity = canonical_bytes(&distribution_read(&prediction))?;
    let prediction_handle = ArtifactHandle::new(b"prediction", &prediction_identity);
    let membership_namespace = namespace(&[
        b"eros-residual-chart-cultivation-membership-v1",
        sample.current_id.as_bytes(),
    ]);
    let mut prediction_arcs = Vec::new();
    if let Some(chart) = prior_chart {
        append_words(
            &mut prediction_arcs,
            chart.handle.data_namespace,
            &chart.words,
        )?;
    }
    append_words(
        &mut prediction_arcs,
        current_handle.data_namespace,
        &current_words,
    )?;
    push_interface(
        &mut prediction_arcs,
        meeting_recruit.clone(),
        IncidenceHand::Against,
    )?;
    append_words(
        &mut prediction_arcs,
        prediction_handle.data_namespace,
        &prediction_words,
    )?;
    append_membership(
        &mut prediction_arcs,
        membership_namespace,
        taxa,
        &prediction.keys().cloned().collect(),
        None,
    )?;
    push_interface(
        &mut prediction_arcs,
        prediction_handle.recruit.clone(),
        IncidenceHand::Against,
    )?;
    let (prediction_radiation, prediction_event) = profiled_event(
        budget,
        host_threads,
        machine,
        &format!("prediction-{}", sample.ordinal),
        prediction_words.len() + taxa.len(),
        &prediction_arcs,
        None,
    )?;
    let prediction_body = regional_constituent(&prediction_radiation, "prediction return")?.clone();
    if decode_prediction(&prediction_body, prediction_handle.data_namespace)? != prediction {
        return Err(format!(
            "event {} changed its returned distribution",
            sample.current_id
        ));
    }

    let actual_words = actual_words(&sample.taxon);
    let actual_handle = ArtifactHandle::new(
        b"actual",
        &[sample.current_id.as_bytes(), sample.taxon.as_bytes()].concat(),
    );
    let comparison_recruit = capability(&[
        b"eros-residual-chart-cultivation-comparison-v1",
        sample.current_id.as_bytes(),
    ]);
    let actual_support = BTreeSet::from([sample.taxon.clone()]);
    let mut actual_arcs = Vec::new();
    append_words(
        &mut actual_arcs,
        actual_handle.data_namespace,
        &actual_words,
    )?;
    push_interface(
        &mut actual_arcs,
        prediction_handle.recruit.clone(),
        IncidenceHand::Against,
    )?;
    append_membership(
        &mut actual_arcs,
        membership_namespace,
        taxa,
        &actual_support,
        None,
    )?;
    push_interface(
        &mut actual_arcs,
        comparison_recruit.clone(),
        IncidenceHand::Against,
    )?;
    let (actual_radiation, actual_event) = profiled_event(
        budget,
        host_threads,
        machine,
        &format!("actual-{}", sample.ordinal),
        actual_words.len() + taxa.len(),
        &actual_arcs,
        None,
    )?;
    let comparison = regional_constituent(&actual_radiation, "actual comparison")?;
    if decode_actual(comparison, actual_handle.data_namespace)? != sample.taxon {
        return Err(format!(
            "event {} changed its actual consequence",
            sample.current_id
        ));
    }
    let expected_open_taxa =
        symmetric_difference(&prediction.keys().cloned().collect(), &actual_support);
    let residual = membership_residual(
        &prediction_body,
        comparison,
        membership_namespace,
        taxa,
        &expected_open_taxa,
    )?;
    let relation = relation(&prediction, &sample.taxon);

    standing_samples.push(sample.clone());
    let next_node = build_diagram(standing_samples, 0, feature_order.len())?;
    let next_diagram = canonical_diagram(&next_node, feature_order)?;
    let next_words = chart_words(&next_diagram, feature_order, standing_samples.len());
    let next_handle = ArtifactHandle::new(b"chart", next_diagram.sha256.as_bytes());

    let mut replacement_arcs = Vec::new();
    append_words(
        &mut replacement_arcs,
        prediction_handle.data_namespace,
        &prediction_words,
    )?;
    append_words(
        &mut replacement_arcs,
        actual_handle.data_namespace,
        &actual_words,
    )?;
    append_membership(
        &mut replacement_arcs,
        membership_namespace,
        taxa,
        &actual_support,
        Some(&expected_open_taxa),
    )?;
    push_interface(
        &mut replacement_arcs,
        comparison_recruit.clone(),
        IncidenceHand::Against,
    )?;
    let outgoing_start = replacement_arcs.len();
    append_words(
        &mut replacement_arcs,
        next_handle.data_namespace,
        &next_words,
    )?;
    push_interface(
        &mut replacement_arcs,
        next_handle.recruit.clone(),
        IncidenceHand::Against,
    )?;
    let outgoing_factor_slots = (outgoing_start..replacement_arcs.len())
        .map(|slot| u32::try_from(slot).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let (replacement_radiation, replacement_event) = profiled_event(
        budget,
        host_threads,
        machine,
        &format!("chart-{}", sample.ordinal),
        next_words.len(),
        &replacement_arcs,
        Some(&outgoing_factor_slots),
    )?;
    let replacement = regional_constituent(&replacement_radiation, "chart replacement")?;
    let returned_chart = decode_chart(replacement, next_handle.data_namespace, feature_order)?.2;
    let standing_returned = standing_chart(machine, next_handle.clone(), feature_order)?;
    let chart_returned_exact = returned_chart == next_diagram && standing_returned == next_diagram;

    let prior_chart_departed = prior_chart.is_none_or(|chart| {
        machine
            .standing()
            .constituents()
            .iter()
            .all(|body| decode_chart(body, chart.handle.data_namespace, feature_order).is_err())
    });
    let current_departed = machine
        .standing()
        .constituents()
        .iter()
        .all(|body| decode_current(body, current_handle.data_namespace).is_err());
    let prediction_departed = machine
        .standing()
        .constituents()
        .iter()
        .all(|body| decode_prediction(body, prediction_handle.data_namespace).is_err());
    let actual_departed = machine
        .standing()
        .constituents()
        .iter()
        .all(|body| decode_actual(body, actual_handle.data_namespace).is_err());
    let transient_recruits_departed = [
        meeting_recruit,
        prediction_handle.recruit,
        comparison_recruit,
    ]
    .into_iter()
    .all(|candidate| !standing_has_capability(machine, candidate));
    let lower_carriers_departed = prior_chart_departed
        && current_departed
        && prediction_departed
        && actual_departed
        && transient_recruits_departed;
    let factor_memory = machine.memory();
    let expected_factor_paths = next_words
        .len()
        .checked_add(1)
        .ok_or_else(|| "the outgoing chart boundary exceeds host extent".to_owned())?;
    let outgoing_factor_exact = factor_memory.standing_constituents == 1
        && factor_memory.constituent_cells == 3
        && factor_memory.constituent_incidences == expected_factor_paths
        && factor_memory.constituent_pins == expected_factor_paths
        && factor_memory.constituent_paths == expected_factor_paths;
    let after = diagram_summary(&next_diagram);

    let chart = ChartState {
        node: next_node,
        diagram: next_diagram,
        words: next_words,
        handle: next_handle,
    };
    Ok(TrainingOutcome {
        chart,
        relation: relation.clone(),
        lower_carriers_departed,
        machine_residual_exact: residual["exact"] == json!(true),
        chart_returned_exact,
        outgoing_factor_exact,
        read: json!({
            "event_ordinal": sample.ordinal,
            "current_id": sample.current_id,
            "interfaces": sample.features.iter().enumerate().map(|(at, value)| {
                (feature_order[at].clone(), value.clone())
            }).collect::<BTreeMap<_, _>>(),
            "prediction": distribution_read(&prediction),
            "actual_taxon": sample.taxon,
            "relation": relation,
            "before": before,
            "after": after,
            "machine_membership_residual": residual,
            "current_recovered_from_source": true,
            "chart_recovered_from_standing": prior_chart.is_some(),
            "updated_chart_returned_exactly": chart_returned_exact,
            "lower_carriers_departed": lower_carriers_departed,
            "outgoing_factor_exact": outgoing_factor_exact,
            "physical_after": {
                "standing_constituents": factor_memory.standing_constituents,
                "constituent_cells": factor_memory.constituent_cells,
                "constituent_incidences": factor_memory.constituent_incidences,
                "constituent_pins": factor_memory.constituent_pins,
                "constituent_paths": factor_memory.constituent_paths,
                "constituent_transport_terms": factor_memory.constituent_transport_terms,
                "expected_chart_boundary_paths": expected_factor_paths,
            },
            "machine": machine_read(machine)?,
            "transitions": [
                meeting_event,
                prediction_event,
                actual_event,
                replacement_event,
            ],
        }),
    })
}

fn no_diagram_control(
    budget: &RunBudget,
    host_threads: usize,
    sample: &Sample,
    feature_order: &[String],
) -> Result<Value, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let words = current_words(sample);
    let handle = ArtifactHandle::new(b"no-diagram-current", sample.current_id.as_bytes());
    let mut arcs = Vec::new();
    append_words(&mut arcs, handle.data_namespace, &words)?;
    push_interface(&mut arcs, handle.recruit, IncidenceHand::Against)?;
    let (radiation, event) = profiled_event(
        budget,
        host_threads,
        &mut machine,
        "no-diagram-control",
        words.len(),
        &arcs,
        None,
    )?;
    let current = regional_constituent(&radiation, "no-diagram control")?;
    let recovered = decode_current(current, handle.data_namespace)?;
    if !same_current(&recovered, sample) {
        return Err("the no-diagram control changed its current".to_owned());
    }
    Ok(json!({
        "current_id": sample.current_id,
        "interfaces": feature_order.iter().cloned().zip(sample.features.clone()).collect::<BTreeMap<_, _>>(),
        "standing_chart_present": false,
        "distribution": [],
        "event": event,
    }))
}

fn run_checkpoint_probes(
    budget: &RunBudget,
    host_threads: usize,
    source: &Source,
    samples: &[Sample],
    taxa: &[String],
    states: &[CheckpointState],
) -> Result<Vec<Value>, String> {
    let mut reads = Vec::new();
    for expected in &source.checkpoints {
        let state = states
            .iter()
            .find(|state| state.after_events == expected.after_events)
            .ok_or_else(|| format!("checkpoint {} was not retained", expected.after_events))?;
        if state.chart.diagram != expected.diagram {
            return Err(format!(
                "checkpoint {} chart changed",
                expected.after_events
            ));
        }
        let mut probes = Vec::new();
        for expected_probe in &expected.probes {
            let sample = samples
                .get(expected_probe.event_ordinal)
                .ok_or_else(|| "checkpoint probe ordinal is outside the source".to_owned())?;
            let mut machine =
                LiveCurrentMachine::from_rest_image(state.rest.clone()).map_err(debug)?;
            let words = current_words(sample);
            let handle = ArtifactHandle::new(
                b"source-absent-probe",
                &[expected.name.as_bytes(), sample.current_id.as_bytes()].concat(),
            );
            let probe_recruit = capability(&[
                b"eros-residual-chart-cultivation-probe-v1",
                expected.name.as_bytes(),
                sample.current_id.as_bytes(),
            ]);
            let mut arcs = Vec::new();
            append_words(&mut arcs, handle.data_namespace, &words)?;
            push_interface(
                &mut arcs,
                state.chart.handle.recruit.clone(),
                IncidenceHand::Against,
            )?;
            push_interface(&mut arcs, probe_recruit, IncidenceHand::Against)?;
            let (radiation, event) = profiled_event(
                budget,
                host_threads,
                &mut machine,
                &format!("probe-{}-{}", expected.after_events, sample.ordinal),
                words.len(),
                &arcs,
                None,
            )?;
            let meeting = regional_constituent(&radiation, "checkpoint probe")?;
            let chart = decode_chart(
                meeting,
                state.chart.handle.data_namespace,
                &source.training_law.feature_order,
            )?
            .2;
            let recovered_current = decode_current(meeting, handle.data_namespace)?;
            let prediction = predict(&state.chart.node, &recovered_current);
            let distribution = distribution_read(&prediction);
            let relation = relation(&prediction, &sample.taxon);
            let accepted = chart == state.chart.diagram
                && same_current(&recovered_current, sample)
                && distribution == expected_probe.distribution
                && relation == expected_probe.relation_to_withheld_actual
                && sample.current_id == expected_probe.current_id
                && sample.taxon == expected_probe.actual_taxon;
            probes.push(json!({
                "event_ordinal": sample.ordinal,
                "current_id": sample.current_id,
                "source_actual_withheld": true,
                "distribution": distribution,
                "relation_to_observer_held_actual": relation,
                "observer_held_actual_taxon": sample.taxon,
                "chart_recovered_from_standing": chart == state.chart.diagram,
                "current_recovered_from_source": same_current(&recovered_current, sample),
                "accepted": accepted,
                "event": event,
            }));
        }
        let accepted = probes.iter().all(|probe| probe["accepted"] == json!(true));
        reads.push(json!({
            "name": expected.name,
            "after_events": expected.after_events,
            "diagram": state.chart.diagram,
            "taxon_population": taxa,
            "probes": probes,
            "accepted": accepted,
        }));
    }
    Ok(reads)
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA || source.observation_id != OBSERVATION_ID {
        return Err(format!(
            "source identity changed: schema={:?}, observation={:?}",
            source.schema, source.observation_id
        ));
    }
    if source.events.len() != 12
        || source.taxa.len() != 2
        || source.training_law.feature_order.len() != 3
        || source.checkpoints.len() != 3
    {
        return Err("the fixed source extent changed".to_owned());
    }
    let expected_relations = BTreeSet::from([
        "NONE".to_owned(),
        "OPEN_INCLUDED".to_owned(),
        "OPEN_RESIDUAL".to_owned(),
        "RIDE".to_owned(),
    ]);
    if source
        .training_law
        .relations
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
        != expected_relations
    {
        return Err("the exact result species changed".to_owned());
    }
    let taxon_ids = source
        .taxa
        .iter()
        .map(|taxon| taxon.identity.clone())
        .collect::<BTreeSet<_>>();
    if taxon_ids.len() != source.taxa.len() {
        return Err("the source repeats a receiver taxon identity".to_owned());
    }
    for taxon in &source.taxa {
        let mut identity_material = b"eros-receiver-taxon-v1\0".to_vec();
        identity_material.extend(canonical_value_bytes(&taxon.face)?);
        if sha256(&identity_material) != taxon.identity {
            return Err(format!(
                "taxon {} does not identify its exact face",
                taxon.identity
            ));
        }
    }
    let observed_counts =
        source
            .events
            .iter()
            .fold(BTreeMap::<String, usize>::new(), |mut counts, event| {
                *counts.entry(event.actual_taxon.clone()).or_default() += 1;
                counts
            });
    for taxon in &source.taxa {
        if observed_counts.get(&taxon.identity) != Some(&taxon.total_count) {
            return Err(format!("taxon {} count changed", taxon.identity));
        }
    }
    for (ordinal, event) in source.events.iter().enumerate() {
        if event.ordinal != ordinal
            || event.interfaces.len() != source.training_law.feature_order.len()
            || !taxon_ids.contains(&event.actual_taxon)
        {
            return Err(format!("source event {ordinal} changed its boundary"));
        }
        let taxon = source
            .taxa
            .iter()
            .find(|taxon| taxon.identity == event.actual_taxon)
            .ok_or_else(|| "event taxon is absent".to_owned())?;
        if taxon.face != event.actual_face {
            return Err(format!(
                "event {} changed the face of its declared taxon",
                event.current_id
            ));
        }
    }
    Ok(())
}

fn source_samples(source: &Source) -> Result<Vec<Sample>, String> {
    source
        .events
        .iter()
        .map(|event| {
            let features = source
                .training_law
                .feature_order
                .iter()
                .map(|feature| {
                    event.interfaces.get(feature).cloned().ok_or_else(|| {
                        format!("event {} omits interface {feature}", event.current_id)
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Sample {
                ordinal: event.ordinal,
                current_id: event.current_id.clone(),
                features,
                taxon: event.actual_taxon.clone(),
            })
        })
        .collect()
}

fn same_current(left: &Sample, right: &Sample) -> bool {
    left.ordinal == right.ordinal
        && left.current_id == right.current_id
        && left.features == right.features
}

fn derive_trajectory(samples: &[Sample], feature_order: &[String]) -> Result<Value, String> {
    let mut standing = Vec::new();
    let mut trajectory = Vec::new();
    for sample in samples {
        let (prediction, before) = if standing.is_empty() {
            (BTreeMap::new(), empty_diagram_summary())
        } else {
            let node = build_diagram(&standing, 0, feature_order.len())?;
            let diagram = canonical_diagram(&node, feature_order)?;
            (predict(&node, sample), diagram_summary(&diagram))
        };
        standing.push(sample.clone());
        let after_node = build_diagram(&standing, 0, feature_order.len())?;
        let after = canonical_diagram(&after_node, feature_order)?;
        trajectory.push(json!({
            "event_ordinal": sample.ordinal,
            "current_id": sample.current_id,
            "prediction": distribution_read(&prediction),
            "relation": relation(&prediction, &sample.taxon),
            "before": before,
            "after": diagram_summary(&after),
        }));
    }
    Ok(Value::Array(trajectory))
}

fn build_diagram(
    samples: &[Sample],
    feature_at: usize,
    feature_count: usize,
) -> Result<Node, String> {
    if samples.is_empty() {
        return Err("a nonempty sample population is required".to_owned());
    }
    let mut distribution = BTreeMap::new();
    for sample in samples {
        *distribution.entry(sample.taxon.clone()).or_default() += 1;
    }
    if distribution.len() == 1 || feature_at == feature_count {
        return Ok(Node {
            distribution,
            split: None,
            children: BTreeMap::new(),
        });
    }

    let mut groups: BTreeMap<String, Vec<Sample>> = BTreeMap::new();
    for sample in samples {
        groups
            .entry(sample.features[feature_at].clone())
            .or_default()
            .push(sample.clone());
    }
    if groups.len() == 1 {
        return build_diagram(samples, feature_at + 1, feature_count);
    }
    let children = groups
        .into_iter()
        .map(|(value, group)| Ok((value, build_diagram(&group, feature_at + 1, feature_count)?)))
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let child_shapes = children.values().map(shape).collect::<Vec<_>>();
    if child_shapes
        .iter()
        .skip(1)
        .all(|candidate| candidate == &child_shapes[0])
    {
        return merge_same_shape(&children.into_values().collect::<Vec<_>>());
    }
    Ok(Node {
        distribution,
        split: Some(feature_at),
        children,
    })
}

fn shape(node: &Node) -> Shape {
    Shape {
        distribution: normalized(&node.distribution),
        split: node.split,
        children: node
            .children
            .iter()
            .map(|(value, child)| (value.clone(), shape(child)))
            .collect(),
    }
}

fn merge_same_shape(nodes: &[Node]) -> Result<Node, String> {
    let first = nodes
        .first()
        .ok_or_else(|| "cannot merge an empty chart population".to_owned())?;
    let expected = shape(first);
    if nodes.iter().skip(1).any(|node| shape(node) != expected) {
        return Err("only equal conditional chart shapes may merge".to_owned());
    }
    let mut distribution = BTreeMap::new();
    for node in nodes {
        for (taxon, count) in &node.distribution {
            *distribution.entry(taxon.clone()).or_default() += count;
        }
    }
    let mut children = BTreeMap::new();
    if first.split.is_some() {
        for value in first.children.keys() {
            let population = nodes
                .iter()
                .map(|node| {
                    node.children
                        .get(value)
                        .cloned()
                        .ok_or_else(|| "equal chart shapes lost a child".to_owned())
                })
                .collect::<Result<Vec<_>, _>>()?;
            children.insert(value.clone(), merge_same_shape(&population)?);
        }
    }
    Ok(Node {
        distribution,
        split: first.split,
        children,
    })
}

fn predict(node: &Node, sample: &Sample) -> BTreeMap<String, usize> {
    let mut cursor = node;
    while let Some(split) = cursor.split {
        let value = &sample.features[split];
        let Some(child) = cursor.children.get(value) else {
            break;
        };
        cursor = child;
    }
    cursor.distribution.clone()
}

fn relation(distribution: &BTreeMap<String, usize>, actual: &str) -> String {
    if distribution.is_empty() {
        "NONE"
    } else if distribution.len() == 1 && distribution.contains_key(actual) {
        "RIDE"
    } else if distribution.contains_key(actual) {
        "OPEN_INCLUDED"
    } else {
        "OPEN_RESIDUAL"
    }
    .to_owned()
}

fn normalized(distribution: &BTreeMap<String, usize>) -> Vec<(String, usize, usize)> {
    let total = distribution.values().sum::<usize>();
    distribution
        .iter()
        .map(|(taxon, count)| {
            let divisor = gcd(*count, total);
            (taxon.clone(), count / divisor, total / divisor)
        })
        .collect()
}

fn distribution_read(distribution: &BTreeMap<String, usize>) -> Vec<DistributionRead> {
    normalized(distribution)
        .into_iter()
        .map(|(taxon, numerator, denominator)| DistributionRead {
            count: distribution[&taxon],
            taxon,
            quotient: ratio_string(numerator, denominator),
        })
        .collect()
}

fn canonical_diagram(node: &Node, feature_order: &[String]) -> Result<Diagram, String> {
    fn visit(
        node: &Node,
        feature_order: &[String],
        nodes: &mut Vec<NodeRead>,
        interned: &mut HashMap<Vec<u8>, usize>,
    ) -> Result<usize, String> {
        let children = node
            .children
            .iter()
            .map(|(value, child)| {
                Ok(ChildRead {
                    value: value.clone(),
                    node: visit(child, feature_order, nodes, interned)?,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let split = node
            .split
            .map(|at| {
                feature_order
                    .get(at)
                    .cloned()
                    .ok_or_else(|| "a chart split exceeds its feature order".to_owned())
            })
            .transpose()?;
        let row = json!({
            "distribution": distribution_read(&node.distribution),
            "split": split,
            "children": children,
        });
        let identity = canonical_value_bytes(&row)?;
        if let Some(ordinal) = interned.get(&identity) {
            return Ok(*ordinal);
        }
        let ordinal = nodes.len();
        nodes.push(NodeRead {
            ordinal,
            distribution: serde_json::from_value(row["distribution"].clone()).map_err(debug)?,
            split: serde_json::from_value(row["split"].clone()).map_err(debug)?,
            children: serde_json::from_value(row["children"].clone()).map_err(debug)?,
        });
        interned.insert(identity, ordinal);
        Ok(ordinal)
    }

    let mut nodes = Vec::new();
    let root = visit(node, feature_order, &mut nodes, &mut HashMap::new())?;
    seal_diagram(root, nodes)
}

fn seal_diagram(root: usize, nodes: Vec<NodeRead>) -> Result<Diagram, String> {
    let identity = json!({"root": root, "nodes": nodes});
    let sha256 = sha256(&canonical_value_bytes(&identity)?);
    let nodes: Vec<NodeRead> = serde_json::from_value(identity["nodes"].clone()).map_err(debug)?;
    let internal_nodes = nodes.iter().filter(|node| node.split.is_some()).count();
    Ok(Diagram {
        root,
        leaf_nodes: nodes.len() - internal_nodes,
        internal_nodes,
        nodes,
        sha256,
    })
}

fn diagram_summary(diagram: &Diagram) -> Value {
    let root = &diagram.nodes[diagram.root];
    json!({
        "sha256": diagram.sha256,
        "nodes": diagram.nodes.len(),
        "internal_nodes": diagram.internal_nodes,
        "leaf_nodes": diagram.leaf_nodes,
        "root_split": root.split,
        "root_distribution": root.distribution,
    })
}

fn empty_diagram_summary() -> Value {
    json!({
        "sha256": null,
        "nodes": 0,
        "internal_nodes": 0,
        "leaf_nodes": 0,
        "root_split": null,
        "root_distribution": [],
    })
}

fn chart_words(
    diagram: &Diagram,
    feature_order: &[String],
    sample_count: usize,
) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(CHART_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(CHART_ROOT, diagram.root as u64),
        CompactWord::scalar(CHART_NODE_COUNT, diagram.nodes.len() as u64),
        CompactWord::scalar(CHART_FEATURE_COUNT, feature_order.len() as u64),
        CompactWord::scalar(CHART_SAMPLE_COUNT, sample_count as u64),
    ];
    for (feature, value) in feature_order.iter().enumerate() {
        append_string_words(
            &mut words,
            CHART_FEATURE_LENGTH,
            CHART_FEATURE_CHUNK,
            &[feature as u64],
            value,
        );
    }
    for node in &diagram.nodes {
        let coordinates = [node.ordinal as u64];
        let split = node
            .split
            .as_ref()
            .and_then(|name| feature_order.iter().position(|candidate| candidate == name))
            .map_or(u64::MAX, |at| at as u64);
        words.push(CompactWord::at(CHART_NODE_SPLIT, coordinates, split));
        words.push(CompactWord::at(
            CHART_NODE_DISTRIBUTION_COUNT,
            coordinates,
            node.distribution.len() as u64,
        ));
        for (at, entry) in node.distribution.iter().enumerate() {
            append_string_words(
                &mut words,
                CHART_DISTRIBUTION_TAXON_LENGTH,
                CHART_DISTRIBUTION_TAXON_CHUNK,
                &[node.ordinal as u64, at as u64],
                &entry.taxon,
            );
            words.push(CompactWord::at(
                CHART_DISTRIBUTION_COUNT,
                vec![node.ordinal as u64, at as u64],
                entry.count as u64,
            ));
        }
        words.push(CompactWord::at(
            CHART_NODE_CHILD_COUNT,
            coordinates,
            node.children.len() as u64,
        ));
        for (at, child) in node.children.iter().enumerate() {
            append_string_words(
                &mut words,
                CHART_CHILD_VALUE_LENGTH,
                CHART_CHILD_VALUE_CHUNK,
                &[node.ordinal as u64, at as u64],
                &child.value,
            );
            words.push(CompactWord::at(
                CHART_CHILD_NODE,
                vec![node.ordinal as u64, at as u64],
                child.node as u64,
            ));
        }
    }
    words
}

fn decode_chart(
    constituent: &LiveConstituent,
    root: u64,
    expected_features: &[String],
) -> Result<(usize, Vec<String>, Diagram), String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, CHART_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("chart schema changed".to_owned());
    }
    let chart_root = usize::try_from(atlas.word(root, CHART_ROOT, &[])?).map_err(debug)?;
    let node_count = usize::try_from(atlas.word(root, CHART_NODE_COUNT, &[])?).map_err(debug)?;
    let feature_count =
        usize::try_from(atlas.word(root, CHART_FEATURE_COUNT, &[])?).map_err(debug)?;
    let sample_count =
        usize::try_from(atlas.word(root, CHART_SAMPLE_COUNT, &[])?).map_err(debug)?;
    let features = (0..feature_count)
        .map(|at| {
            decode_string(
                &atlas,
                root,
                CHART_FEATURE_LENGTH,
                CHART_FEATURE_CHUNK,
                &[at as u64],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    if features != expected_features {
        return Err("chart feature order changed".to_owned());
    }
    let mut nodes = Vec::with_capacity(node_count);
    for ordinal in 0..node_count {
        let split_word = atlas.word(root, CHART_NODE_SPLIT, &[ordinal as u64])?;
        let split = if split_word == u64::MAX {
            None
        } else {
            Some(
                features
                    .get(usize::try_from(split_word).map_err(debug)?)
                    .cloned()
                    .ok_or_else(|| "chart split exceeds feature order".to_owned())?,
            )
        };
        let distribution_count =
            usize::try_from(atlas.word(root, CHART_NODE_DISTRIBUTION_COUNT, &[ordinal as u64])?)
                .map_err(debug)?;
        let mut distribution = BTreeMap::new();
        for at in 0..distribution_count {
            let taxon = decode_string(
                &atlas,
                root,
                CHART_DISTRIBUTION_TAXON_LENGTH,
                CHART_DISTRIBUTION_TAXON_CHUNK,
                &[ordinal as u64, at as u64],
            )?;
            let count = usize::try_from(atlas.word(
                root,
                CHART_DISTRIBUTION_COUNT,
                &[ordinal as u64, at as u64],
            )?)
            .map_err(debug)?;
            if distribution.insert(taxon, count).is_some() {
                return Err("chart repeats a taxon inside one node".to_owned());
            }
        }
        let child_count =
            usize::try_from(atlas.word(root, CHART_NODE_CHILD_COUNT, &[ordinal as u64])?)
                .map_err(debug)?;
        let mut children = Vec::new();
        for at in 0..child_count {
            children.push(ChildRead {
                value: decode_string(
                    &atlas,
                    root,
                    CHART_CHILD_VALUE_LENGTH,
                    CHART_CHILD_VALUE_CHUNK,
                    &[ordinal as u64, at as u64],
                )?,
                node: usize::try_from(atlas.word(
                    root,
                    CHART_CHILD_NODE,
                    &[ordinal as u64, at as u64],
                )?)
                .map_err(debug)?,
            });
        }
        nodes.push(NodeRead {
            ordinal,
            distribution: distribution_read(&distribution),
            split,
            children,
        });
    }
    if chart_root >= nodes.len() {
        return Err("chart root exceeds node population".to_owned());
    }
    Ok((sample_count, features, seal_diagram(chart_root, nodes)?))
}

fn current_words(sample: &Sample) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(CURRENT_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(CURRENT_ORDINAL, sample.ordinal as u64),
        CompactWord::scalar(CURRENT_FEATURE_COUNT, sample.features.len() as u64),
    ];
    append_string_words(
        &mut words,
        CURRENT_ID_LENGTH,
        CURRENT_ID_CHUNK,
        &[],
        &sample.current_id,
    );
    for (at, feature) in sample.features.iter().enumerate() {
        append_string_words(
            &mut words,
            CURRENT_FEATURE_LENGTH,
            CURRENT_FEATURE_CHUNK,
            &[at as u64],
            feature,
        );
    }
    words
}

fn decode_current(constituent: &LiveConstituent, root: u64) -> Result<Sample, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, CURRENT_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("current schema changed".to_owned());
    }
    let ordinal = usize::try_from(atlas.word(root, CURRENT_ORDINAL, &[])?).map_err(debug)?;
    let feature_count =
        usize::try_from(atlas.word(root, CURRENT_FEATURE_COUNT, &[])?).map_err(debug)?;
    let current_id = decode_string(&atlas, root, CURRENT_ID_LENGTH, CURRENT_ID_CHUNK, &[])?;
    let features = (0..feature_count)
        .map(|at| {
            decode_string(
                &atlas,
                root,
                CURRENT_FEATURE_LENGTH,
                CURRENT_FEATURE_CHUNK,
                &[at as u64],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(Sample {
        ordinal,
        current_id,
        features,
        taxon: String::new(),
    })
}

fn prediction_words(distribution: &BTreeMap<String, usize>) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(PREDICTION_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(PREDICTION_COUNT, distribution.len() as u64),
    ];
    for (at, (taxon, count)) in distribution.iter().enumerate() {
        append_string_words(
            &mut words,
            PREDICTION_TAXON_LENGTH,
            PREDICTION_TAXON_CHUNK,
            &[at as u64],
            taxon,
        );
        words.push(CompactWord::at(
            PREDICTION_TAXON_COUNT,
            vec![at as u64],
            *count as u64,
        ));
    }
    words
}

fn decode_prediction(
    constituent: &LiveConstituent,
    root: u64,
) -> Result<BTreeMap<String, usize>, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, PREDICTION_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("prediction schema changed".to_owned());
    }
    let count = usize::try_from(atlas.word(root, PREDICTION_COUNT, &[])?).map_err(debug)?;
    let mut distribution = BTreeMap::new();
    for at in 0..count {
        let taxon = decode_string(
            &atlas,
            root,
            PREDICTION_TAXON_LENGTH,
            PREDICTION_TAXON_CHUNK,
            &[at as u64],
        )?;
        let recurrence = usize::try_from(atlas.word(root, PREDICTION_TAXON_COUNT, &[at as u64])?)
            .map_err(debug)?;
        if distribution.insert(taxon, recurrence).is_some() {
            return Err("prediction repeats one taxon".to_owned());
        }
    }
    Ok(distribution)
}

fn actual_words(taxon: &str) -> Vec<CompactWord> {
    let mut words = vec![CompactWord::scalar(ACTUAL_SCHEMA, COMPACT_SCHEMA)];
    append_string_words(
        &mut words,
        ACTUAL_TAXON_LENGTH,
        ACTUAL_TAXON_CHUNK,
        &[],
        taxon,
    );
    words
}

fn decode_actual(constituent: &LiveConstituent, root: u64) -> Result<String, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, ACTUAL_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("actual schema changed".to_owned());
    }
    decode_string(&atlas, root, ACTUAL_TAXON_LENGTH, ACTUAL_TAXON_CHUNK, &[])
}

fn append_string_words(
    words: &mut Vec<CompactWord>,
    length_tag: u64,
    chunk_tag: u64,
    coordinates: &[u64],
    value: &str,
) {
    words.push(CompactWord::at(
        length_tag,
        coordinates.to_vec(),
        value.len() as u64,
    ));
    for (at, chunk) in value.as_bytes().chunks(8).enumerate() {
        let mut padded = [0u8; 8];
        padded[..chunk.len()].copy_from_slice(chunk);
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        words.push(CompactWord::at(
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
    let chunks = length.div_ceil(8);
    let mut bytes = Vec::with_capacity(chunks * 8);
    for at in 0..chunks {
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        bytes.extend_from_slice(&atlas.word(root, chunk_tag, &route)?.to_le_bytes());
    }
    bytes.truncate(length);
    String::from_utf8(bytes).map_err(debug)
}

fn append_words(
    arcs: &mut Vec<PendingArc>,
    root: u64,
    words: &[CompactWord],
) -> Result<(), String> {
    for word in words {
        push_interface(arcs, word.interface(root), IncidenceHand::Against)?;
    }
    Ok(())
}

fn append_membership(
    arcs: &mut Vec<PendingArc>,
    root: u64,
    taxa: &[String],
    present: &BTreeSet<String>,
    subset: Option<&BTreeSet<String>>,
) -> Result<(), String> {
    for (ordinal, taxon) in taxa.iter().enumerate() {
        if subset.is_some_and(|subset| !subset.contains(taxon)) {
            continue;
        }
        push_interface(
            arcs,
            InterfaceCapability::new(root, ordinal as u64),
            if present.contains(taxon) {
                IncidenceHand::With
            } else {
                IncidenceHand::Against
            },
        )?;
    }
    Ok(())
}

fn membership_residual(
    prior: &LiveConstituent,
    returned: &LiveConstituent,
    namespace: u64,
    taxa: &[String],
    expected_open: &BTreeSet<String>,
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
    if prior_pins.len() != taxa.len() {
        return Err(format!(
            "prediction membership returned {} taxa instead of {}",
            prior_pins.len(),
            taxa.len()
        ));
    }
    let mut open = BTreeSet::new();
    let mut found = 0usize;
    for (ordinal, prior_pin) in prior_pins {
        let comparison_pins = returned
            .pins()
            .iter()
            .filter(|pin| !prior.pins().contains(pin))
            .filter(|pin| {
                pin.interface().is_some_and(|interface| {
                    interface.namespace() == namespace && interface.local() == ordinal
                })
            })
            .filter(|pin| pin.held() == prior_pin.meeting())
            .collect::<Vec<_>>();
        if comparison_pins.len() != 1 {
            return Err(format!(
                "taxon membership {ordinal} returned {} comparison pins instead of one",
                comparison_pins.len()
            ));
        }
        let pin = comparison_pins[0];
        if pin.is_open() {
            open.insert(
                taxa.get(ordinal as usize)
                    .cloned()
                    .ok_or_else(|| "membership ordinal exceeds taxon atlas".to_owned())?,
            );
        }
        found += usize::from(pin.is_found());
    }
    Ok(json!({
        "expected_open_taxa": expected_open,
        "carried_open_taxa": open,
        "found_pins": found,
        "exact": open == *expected_open && found == 0,
    }))
}

fn symmetric_difference(left: &BTreeSet<String>, right: &BTreeSet<String>) -> BTreeSet<String> {
    left.symmetric_difference(right).cloned().collect()
}

fn standing_chart(
    machine: &LiveCurrentMachine,
    handle: ArtifactHandle,
    features: &[String],
) -> Result<Diagram, String> {
    let charts = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|body| decode_chart(body, handle.data_namespace, features).ok())
        .map(|(_, _, diagram)| diagram)
        .collect::<Vec<_>>();
    match charts.as_slice() {
        [chart] => Ok(chart.clone()),
        [] => Err("Standing exposes no exact chart".to_owned()),
        _ => Err("Standing exposes plural exact charts".to_owned()),
    }
}

fn standing_has_capability(machine: &LiveCurrentMachine, capability: InterfaceCapability) -> bool {
    machine.standing().constituents().iter().any(|constituent| {
        constituent.exposed().iter().copied().any(|pin_at| {
            constituent
                .pins()
                .get(pin_at as usize)
                .and_then(|pin| pin.interface())
                == Some(capability.clone())
        })
    })
}

fn profiled_event(
    budget: &RunBudget,
    host_threads: usize,
    machine: &mut LiveCurrentMachine,
    event_name: &str,
    semantic_words: usize,
    arcs: &[PendingArc],
    outgoing_factor_slots: Option<&[u32]>,
) -> Result<(soma_membrane::ContemporaryRadiation, EventRead), String> {
    budget.require_open()?;
    if arcs.len() > MAX_ARCS_PER_EVENT {
        return Err(format!(
            "event {event_name} requires {} arcs, beyond {MAX_ARCS_PER_EVENT}",
            arcs.len()
        ));
    }
    let pair = primed_pair(machine)?;
    let remapped = arcs
        .iter()
        .map(|arc| {
            RegionalRelationArc::new(
                pair[0],
                CurrentBoundaryPort::Cell,
                pair[1],
                CurrentBoundaryPort::Cell,
                arc.interface.clone(),
                arc.boundary_slot,
                arc.arc_slot,
                arc.hand,
            )
        })
        .collect::<Vec<_>>();
    let currents = [
        CurrentEvent::ending(pair[0], relation_atom(181)?, action()),
        CurrentEvent::ending(pair[1], relation_atom(191)?, action()),
    ];
    let regional = [match outgoing_factor_slots {
        Some(slots) => RegionalRelationCell::with_outgoing_factor(pair[1], &remapped, slots),
        None => RegionalRelationCell::new(pair[1], &remapped),
    }];
    let mut executor = ParallelHostLiveCurrentExecutor::new(host_threads);
    let started = Instant::now();
    let radiation = machine
        .receive_with(
            ContemporaryEvent::with_regional(&currents, &[], &regional),
            &mut executor,
        )
        .map_err(debug)?;
    let wall = started.elapsed();
    let returned_incidences = radiation
        .regional()
        .iter()
        .map(|row| row.constituent().incidences().len())
        .sum();
    let returned_pins = radiation
        .regional()
        .iter()
        .map(|row| row.constituent().pins().len())
        .sum();
    if wall > EVENT_LIMIT {
        return Err(format!(
            "event {event_name} exceeded {} seconds",
            EVENT_LIMIT.as_secs()
        ));
    }
    budget.require_open()?;
    Ok((
        radiation,
        EventRead {
            event: event_name.to_owned(),
            semantic_words,
            regional_arcs: remapped.len(),
            wall_micros: duration_micros(wall),
            returned_incidences,
            returned_pins,
        },
    ))
}

fn regional_constituent<'a>(
    radiation: &'a soma_membrane::ContemporaryRadiation,
    role: &str,
) -> Result<&'a LiveConstituent, String> {
    let rows = radiation.regional();
    let first = rows
        .first()
        .ok_or_else(|| format!("{role} returned no regional constituent"))?;
    if rows
        .iter()
        .any(|row| row.constituent() != first.constituent())
    {
        return Err(format!("{role} did not close as one exact constituent"));
    }
    Ok(first.constituent())
}

fn push_interface(
    arcs: &mut Vec<PendingArc>,
    interface: InterfaceCapability,
    hand: IncidenceHand,
) -> Result<(), String> {
    let slot = u32::try_from(arcs.len()).map_err(debug)?;
    arcs.push(PendingArc {
        interface,
        boundary_slot: slot,
        arc_slot: 0,
        hand,
    });
    Ok(())
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

fn machine_read(machine: &LiveCurrentMachine) -> Result<Value, String> {
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
    let rest = machine.rest_image().map_err(debug)?;
    let rest_octets = rest.encode_native_bytes().map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched and
    // still reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead
    // of being hashed and dropped. This helper reads several machines; the address is the content,
    // so each distinct rest is deposited at its own address rather than overwriting the previous.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    Ok(json!({
        "standing_rank": machine.standing().rank(),
        "standing_cells": standing_cells,
        "standing_constituents": standing_constituents,
        "constituent_cells": constituent_cells,
        "constituent_incidences": constituent_incidences,
        "constituent_pins": constituent_pins,
        "constituent_paths": constituent_paths,
        "constituent_transport_terms": constituent_transport_terms,
        "live_lineages": live_lineages,
        "rest_sha256": sha256(&rest_octets),
    }))
}

fn compact_route_namespace(root: u64, word: &CompactWord) -> u64 {
    let mut route = Vec::with_capacity(2 + word.coordinates.len());
    route.extend_from_slice(&word.tag.to_le_bytes());
    route.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
    for coordinate in &word.coordinates {
        route.extend_from_slice(&coordinate.to_le_bytes());
    }
    namespace(&[
        b"eros-residual-chart-cultivation-word-v1",
        &root.to_le_bytes(),
        &route,
    ])
}

fn capability(parts: &[&[u8]]) -> InterfaceCapability {
    InterfaceCapability::new(namespace(parts), 0)
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

fn canonical_bytes<T: Serialize>(value: &T) -> Result<Vec<u8>, String> {
    let value = serde_json::to_value(value).map_err(debug)?;
    canonical_value_bytes(&value)
}

fn canonical_value_bytes(value: &Value) -> Result<Vec<u8>, String> {
    serde_json::to_vec(value).map_err(debug)
}

fn gcd(mut left: usize, mut right: usize) -> usize {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn ratio_string(numerator: usize, denominator: usize) -> String {
    if denominator == 1 {
        numerator.to_string()
    } else {
        format!("{numerator}/{denominator}")
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

fn relation_atom(value: i64) -> Result<RelationAtom, String> {
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
    "usage: cargo run -p life --example eros_residual_chart_cultivation -- <SOURCE.json> <new-report.json>"
}
