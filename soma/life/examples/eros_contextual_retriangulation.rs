use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage, LiveMemory,
    RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_contextual_retriangulation/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_contextual_retriangulation";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
const SOURCE_SCHEMA: &str = "eros.contextual-retriangulation.source.v1";
const REPORT_SCHEMA: &str = "eros.contextual-retriangulation.report.v1";
const OBSERVATION_ID: &str = "eros-contextual-retriangulation-01";
const COMPACT_SCHEMA: u64 = 1;
const RECRUIT_LOCAL: u64 = 0;
const MAX_ARCS_PER_CELL: usize = 1024;
const EVENT_LIMIT: Duration = Duration::from_secs(30);
const RUN_LIMIT: Duration = Duration::from_secs(120);
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];

const ROW_SCHEMA: u64 = 1;
const ROW_ORDINAL: u64 = 2;
const ROW_PIVOT_COUNT: u64 = 3;
const ROW_AXIS_COUNT: u64 = 4;
const ROW_PIVOT_FACTOR: u64 = 10;
const ROW_PIVOT_WORD: u64 = 11;
const ROW_TARGET_NUMERATOR_SIGN: u64 = 20;
const ROW_TARGET_NUMERATOR_COUNT: u64 = 21;
const ROW_TARGET_NUMERATOR_LIMB: u64 = 22;
const ROW_TARGET_DENOMINATOR_SIGN: u64 = 23;
const ROW_TARGET_DENOMINATOR_COUNT: u64 = 24;
const ROW_TARGET_DENOMINATOR_LIMB: u64 = 25;

const LAW_SCHEMA: u64 = 101;
const LAW_RANK: u64 = 102;
const LAW_AXIS_COUNT: u64 = 103;
const LAW_PIVOT_FACTOR: u64 = 110;
const LAW_AXIS: u64 = 111;
const LAW_COEFFICIENT_NUMERATOR_SIGN: u64 = 120;
const LAW_COEFFICIENT_NUMERATOR_COUNT: u64 = 121;
const LAW_COEFFICIENT_NUMERATOR_LIMB: u64 = 122;
const LAW_COEFFICIENT_DENOMINATOR_SIGN: u64 = 123;
const LAW_COEFFICIENT_DENOMINATOR_COUNT: u64 = 124;
const LAW_COEFFICIENT_DENOMINATOR_LIMB: u64 = 125;

const CURRENT_SCHEMA: u64 = 201;
const CURRENT_ORDINAL: u64 = 202;
const CURRENT_PIVOT_COUNT: u64 = 203;
const CURRENT_PIVOT_FACTOR: u64 = 210;
const CURRENT_PIVOT_WORD: u64 = 211;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    source: SourceProvenance,
    chart_law: SourceChartLaw,
    numerical_law: String,
    law_coefficients: Vec<Vec<String>>,
    coefficient_extent: CoefficientExtent,
    contexts: Vec<SourceContext>,
    participation_boundary: ParticipationBoundary,
    stopping_condition: String,
}

#[derive(Deserialize)]
struct SourceProvenance {
    observation_id: String,
    path: String,
    sha256: String,
    model: serde_json::Value,
}

#[derive(Deserialize)]
struct SourceChartLaw {
    layer: usize,
    receiver_axes: Vec<u32>,
    source_factor_count: usize,
    rank: usize,
    pivot_factors: Vec<u32>,
    law_shape: Vec<usize>,
    pivot_selection: String,
}

#[derive(Deserialize)]
struct CoefficientExtent {
    count: usize,
    maximum_numerator_bits: usize,
    maximum_denominator_bits: usize,
}

#[derive(Deserialize)]
struct ParticipationBoundary {
    upstream_activation_words_per_current: usize,
    later_activation_words_per_current: usize,
    upstream_field_was_already_physically_produced: bool,
    claim: String,
}

#[derive(Clone, Debug, Deserialize)]
struct SourceContext {
    current_id: String,
    group: String,
    context: String,
    condition: String,
    pivot_activation_words: Vec<u16>,
    target_factorized_exact_output: Vec<String>,
    target_factorized_face: Face,
    target_observed_output_words: Vec<u16>,
    target_observed_face: Face,
    derived_prediction: DerivedPrediction,
}

#[derive(Clone, Debug, Deserialize)]
struct DerivedPrediction {
    exact_output: Vec<String>,
    face: Face,
    equals_factorized_output: bool,
    factorized_face_rides: bool,
    observed_face_rides: bool,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
struct Face {
    orientation: Vec<String>,
    signed_axis_order: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TrainingRow {
    ordinal: u16,
    pivot_factors: Vec<u32>,
    pivot_words: Vec<u16>,
    targets: Vec<BigRational>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CurrentCarrier {
    ordinal: u16,
    pivot_factors: Vec<u32>,
    pivot_words: Vec<u16>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LocalLaw {
    pivot_factors: Vec<u32>,
    axes: Vec<u32>,
    coefficients: Vec<Vec<BigRational>>,
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
            None => Err(format!(
                "compact route {tag}:{coordinates:?} is absent under {}",
                namespace_string(root)
            )),
        }
    }

    fn namespace_value(&self, namespace: u64) -> Result<u64, String> {
        match self.values.get(&namespace) {
            Some(values) if values.len() == 1 => Ok(*values.first().unwrap()),
            Some(_) => Err(format!(
                "interface {} exposes plural values",
                namespace_string(namespace)
            )),
            None => Err(format!(
                "interface {} is absent",
                namespace_string(namespace)
            )),
        }
    }
}

#[derive(Clone, Copy)]
struct ArtifactHandle {
    data_namespace: u64,
    recruit_namespace: u64,
}

impl ArtifactHandle {
    fn source(kind: &[u8], identity: &[u8]) -> Self {
        Self {
            data_namespace: namespace(&[
                b"eros-contextual-retriangulation-data-v1",
                kind,
                identity,
            ]),
            recruit_namespace: namespace(&[
                b"eros-contextual-retriangulation-recruit-v1",
                kind,
                identity,
            ]),
        }
    }

    fn after_contact(self, event_identity: &[u8]) -> Self {
        Self {
            data_namespace: self.data_namespace,
            recruit_namespace: namespace(&[
                b"eros-contextual-retriangulation-contact-v1",
                &self.recruit_namespace.to_le_bytes(),
                event_identity,
            ]),
        }
    }
}

#[derive(Clone, Debug, Serialize)]
struct EventRead {
    event: String,
    semantic_words: usize,
    regional_arcs: usize,
    wall_micros: u64,
    returned_incidences: usize,
    returned_pins: usize,
}

#[derive(Clone, Debug, Serialize)]
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
    rest_sha256: String,
}

#[derive(Serialize)]
struct SourceRead {
    source_sha256: String,
    upstream_observation: String,
    upstream_path: String,
    upstream_sha256: String,
    model: serde_json::Value,
    layer: usize,
    receiver_axes: Vec<u32>,
    numerical_law: String,
    pivot_selection: String,
}

#[derive(Serialize)]
struct CultivationRead {
    training_currents: usize,
    source_rows_returned_exactly: bool,
    rank: usize,
    pivot_factors: Vec<u32>,
    law_coefficients: usize,
    maximum_numerator_bits: usize,
    maximum_denominator_bits: usize,
    rust_law_equals_independent_source_derivation: bool,
    rows_recovered_from_standing: bool,
    objective_recovered_from_current: bool,
    lower_row_data_departed: bool,
    lower_row_recruitment_departed: bool,
    law_survived_exact_rest_remount: bool,
    source_lineages_departed: bool,
    events: Vec<EventRead>,
    machine: MachineRead,
}

#[derive(Serialize)]
struct ControlRead {
    current_id: String,
    pivot_words_presented: usize,
    law_recovered: bool,
    output_formed: bool,
    event: EventRead,
}

#[derive(Serialize)]
struct ResidualRead {
    axis: u32,
    prediction: String,
    target: String,
    target_minus_prediction: String,
}

#[derive(Serialize)]
struct ComparisonRead {
    expected_open_bits: Vec<u64>,
    carried_open_bits: Vec<u64>,
    open_bits_exact: bool,
    found_pins: usize,
}

#[derive(Serialize)]
struct ContextRead {
    current_id: String,
    group: String,
    context: String,
    condition: String,
    source_activation_words: usize,
    participating_activation_words: usize,
    law_recovered_from_standing: bool,
    current_recovered_from_source: bool,
    prediction: Vec<String>,
    source_derived_prediction_exact: bool,
    target_factorized: Vec<String>,
    target_observed: Vec<String>,
    exact_factorized_output: bool,
    factorized_face_rides: bool,
    observed_face_rides: bool,
    predicted_face: Face,
    factorized_residual: Vec<ResidualRead>,
    observed_residual: Vec<ResidualRead>,
    comparison: ComparisonRead,
    events: Vec<EventRead>,
}

#[derive(Default, Serialize)]
struct GroupRead {
    currents: usize,
    exact_factorized_outputs: usize,
    factorized_face_rides: usize,
    observed_face_rides: usize,
    open_comparisons: usize,
}

#[derive(Serialize)]
struct ParticipationRead {
    source_factors: usize,
    later_activation_words_per_current: usize,
    boundary_fraction: String,
    law_coefficients: usize,
    upstream_field_was_already_physically_produced: bool,
    scope: String,
}

#[derive(Serialize)]
struct AcceptanceRead {
    fixed_source_validated: bool,
    exact_training_chart_closed: bool,
    self_emanated_law_stood_after_rows_departed: bool,
    no_standing_control_refused_output: bool,
    every_later_current_recovered_law_and_current: bool,
    every_prediction_matched_independent_source_derivation: bool,
    every_comparison_carried_exact_open_bits: bool,
    no_comparison_fabricated_found: bool,
    all_contexts_measured_without_retuning: bool,
    no_floating_point_causal_data: bool,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: String,
    source: SourceRead,
    cultivation: CultivationRead,
    control: ControlRead,
    contexts: Vec<ContextRead>,
    groups: BTreeMap<String, GroupRead>,
    participation: ParticipationRead,
    acceptance: AcceptanceRead,
    run_wall_micros: u64,
    conclusion: &'static str,
}

struct CultivatedEcology {
    rest: LiveCurrentRestImage,
    law_handle: ArtifactHandle,
    law: LocalLaw,
    read: CultivationRead,
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
            Err("the bounded contextual-retriangulation run exceeded two minutes".to_owned())
        } else {
            Ok(())
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros contextual retriangulation: {error}");
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
        .map_err(|error| format!("contextual-retriangulation report encodes: {error}"))?;
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
        "eros contextual retriangulation: {} · {} bytes · {}",
        report.status,
        report_bytes.len(),
        report_path.display()
    );
    Ok(())
}

fn run_cpu(source: Source, source_sha256: String) -> Result<Report, String> {
    let run_started = Instant::now();
    validate_source(&source)?;
    let budget = RunBudget::new();
    let expected_law = source_law(&source)?;
    let training = source
        .contexts
        .iter()
        .enumerate()
        .filter(|(_, context)| context.group == "training")
        .map(|(ordinal, context)| training_row(ordinal, context, &source.chart_law))
        .collect::<Result<Vec<_>, String>>()?;
    let ecology = cultivate(
        &budget,
        &source_sha256,
        &source.chart_law,
        &training,
        &expected_law,
        &source.coefficient_extent,
    )?;
    let control_context = source
        .contexts
        .iter()
        .find(|context| context.group == "related_holdout")
        .ok_or_else(|| "the source has no related holdout for the control".to_owned())?;
    let control = run_control(
        &budget,
        &source_sha256,
        ecology.law_handle,
        &source.chart_law,
        control_context,
    )?;

    let mut contexts = Vec::with_capacity(source.contexts.len());
    let mut groups: BTreeMap<String, GroupRead> = BTreeMap::new();
    for (ordinal, context) in source.contexts.iter().enumerate() {
        let read = conduct_context(
            &budget,
            &source_sha256,
            &ecology.rest,
            ecology.law_handle,
            &ecology.law,
            &source.chart_law,
            ordinal,
            context,
        )?;
        let group = groups.entry(context.group.clone()).or_default();
        group.currents += 1;
        group.exact_factorized_outputs += usize::from(read.exact_factorized_output);
        group.factorized_face_rides += usize::from(read.factorized_face_rides);
        group.observed_face_rides += usize::from(read.observed_face_rides);
        group.open_comparisons += usize::from(!read.comparison.carried_open_bits.is_empty());
        contexts.push(read);
    }

    let every_later_current_recovered = contexts
        .iter()
        .all(|read| read.law_recovered_from_standing && read.current_recovered_from_source);
    let every_prediction_exact = contexts
        .iter()
        .all(|read| read.source_derived_prediction_exact);
    let every_comparison_exact = contexts.iter().all(|read| read.comparison.open_bits_exact);
    let no_found = contexts.iter().all(|read| read.comparison.found_pins == 0);
    let training_group = groups
        .get("training")
        .ok_or_else(|| "the report omitted its training group".to_owned())?;
    let exact_training_chart_closed = training_group.currents == 6
        && training_group.exact_factorized_outputs == 6
        && training_group.factorized_face_rides == 6
        && training_group.observed_face_rides == 6;
    let self_emanated_law_stood = ecology.read.lower_row_data_departed
        && ecology.read.lower_row_recruitment_departed
        && ecology.read.law_survived_exact_rest_remount;
    let acceptance = AcceptanceRead {
        fixed_source_validated: true,
        exact_training_chart_closed,
        self_emanated_law_stood_after_rows_departed: self_emanated_law_stood,
        no_standing_control_refused_output: !control.law_recovered && !control.output_formed,
        every_later_current_recovered_law_and_current: every_later_current_recovered,
        every_prediction_matched_independent_source_derivation: every_prediction_exact,
        every_comparison_carried_exact_open_bits: every_comparison_exact,
        no_comparison_fabricated_found: no_found,
        all_contexts_measured_without_retuning: contexts.len() == 12,
        no_floating_point_causal_data: true,
    };
    let accepted = acceptance.fixed_source_validated
        && acceptance.exact_training_chart_closed
        && acceptance.self_emanated_law_stood_after_rows_departed
        && acceptance.no_standing_control_refused_output
        && acceptance.every_later_current_recovered_law_and_current
        && acceptance.every_prediction_matched_independent_source_derivation
        && acceptance.every_comparison_carried_exact_open_bits
        && acceptance.no_comparison_fabricated_found
        && acceptance.all_contexts_measured_without_retuning
        && acceptance.no_floating_point_causal_data;
    if !accepted {
        return Err("the fixed contextual-retriangulation acceptance did not close".to_owned());
    }
    budget.require_open()?;

    Ok(Report {
        schema: REPORT_SCHEMA,
        status: "accepted",
        question: "Can previously cultivated Soma Standing carry a useful context-dependent portion of inherited transformer ecology into later conduct while requiring less source participation, and does changed context reopen the relation?",
        theory_to_structure: "Six conversation/prose currents define one exact local chart. Exact elimination selects the first six independent source-activation columns and forms a 6x5 rational transformation. The six rows cross Soma, meet, and return as one higher law whose lower row carriers depart. Each later current contributes only its six pivot activations; the recovered law forms a receiver face which returns as Standing before the complete source face arrives for an exact RIDE/OPEN comparison.",
        stopping_condition: source.stopping_condition,
        source: SourceRead {
            source_sha256,
            upstream_observation: source.source.observation_id,
            upstream_path: source.source.path,
            upstream_sha256: source.source.sha256,
            model: source.source.model,
            layer: source.chart_law.layer,
            receiver_axes: source.chart_law.receiver_axes.clone(),
            numerical_law: source.numerical_law,
            pivot_selection: source.chart_law.pivot_selection,
        },
        cultivation: ecology.read,
        control,
        contexts,
        groups,
        participation: ParticipationRead {
            source_factors: source.participation_boundary.upstream_activation_words_per_current,
            later_activation_words_per_current: source
                .participation_boundary
                .later_activation_words_per_current,
            boundary_fraction: format!(
                "{}/{}",
                source
                    .participation_boundary
                    .later_activation_words_per_current,
                source.participation_boundary.upstream_activation_words_per_current
            ),
            law_coefficients: source.coefficient_extent.count,
            upstream_field_was_already_physically_produced: source
                .participation_boundary
                .upstream_field_was_already_physically_produced,
            scope: source.participation_boundary.claim,
        },
        acceptance,
        run_wall_micros: duration_micros(run_started.elapsed()),
        conclusion: "The inherited ecology is not a stored set of strongest edges. One exact local transformation can be re-expressed as a much smaller situated law, survive after its six training-row carriers depart, and conduct later currents from six participating activation words. Its boundary is contextual: one of three related code-comment faces RIDEs, while every changed-operation face remains OPEN. This is reduced participation at the Eros membrane, not yet a smaller or cheaper upstream transformer.",
    })
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA || source.observation_id != OBSERVATION_ID {
        return Err(format!(
            "source identity changed: schema={:?}, observation={:?}",
            source.schema, source.observation_id
        ));
    }
    if source.chart_law.rank != 6
        || source.chart_law.pivot_factors.len() != 6
        || source.chart_law.receiver_axes.len() != 5
        || source.chart_law.law_shape != [6, 5]
        || source.law_coefficients.len() != 6
        || source.law_coefficients.iter().any(|row| row.len() != 5)
        || source.coefficient_extent.count != 30
    {
        return Err("the fixed 6x5 local chart changed shape".to_owned());
    }
    if source.contexts.len() != 12 {
        return Err(format!(
            "source contains {} contexts instead of 12",
            source.contexts.len()
        ));
    }
    let groups =
        source
            .contexts
            .iter()
            .fold(BTreeMap::<&str, usize>::new(), |mut groups, context| {
                *groups.entry(context.group.as_str()).or_default() += 1;
                groups
            });
    let expected = BTreeMap::from([
        ("training", 6usize),
        ("related_holdout", 3usize),
        ("changed_operation_holdout", 3usize),
    ]);
    if groups != expected {
        return Err(format!("the fixed context populations changed: {groups:?}"));
    }
    for context in &source.contexts {
        if context.pivot_activation_words.len() != 6
            || context.target_factorized_exact_output.len() != 5
            || context.target_observed_output_words.len() != 5
            || context.derived_prediction.exact_output.len() != 5
        {
            return Err(format!(
                "context {} changed its 6-to-5 boundary",
                context.current_id
            ));
        }
        if context.derived_prediction.equals_factorized_output
            != (context.derived_prediction.exact_output == context.target_factorized_exact_output)
            || context.derived_prediction.factorized_face_rides
                != (context.derived_prediction.face == context.target_factorized_face)
            || context.derived_prediction.observed_face_rides
                != (context.derived_prediction.face == context.target_observed_face)
        {
            return Err(format!(
                "context {} has an inconsistent independent derivation",
                context.current_id
            ));
        }
    }
    if source
        .participation_boundary
        .upstream_activation_words_per_current
        != source.chart_law.source_factor_count
        || source
            .participation_boundary
            .later_activation_words_per_current
            != 6
    {
        return Err("the declared participation boundary changed".to_owned());
    }
    Ok(())
}

fn source_law(source: &Source) -> Result<LocalLaw, String> {
    Ok(LocalLaw {
        pivot_factors: source.chart_law.pivot_factors.clone(),
        axes: source.chart_law.receiver_axes.clone(),
        coefficients: source
            .law_coefficients
            .iter()
            .map(|row| row.iter().map(|value| parse_ratio(value)).collect())
            .collect::<Result<_, _>>()?,
    })
}

fn training_row(
    ordinal: usize,
    context: &SourceContext,
    chart: &SourceChartLaw,
) -> Result<TrainingRow, String> {
    Ok(TrainingRow {
        ordinal: u16::try_from(ordinal).map_err(debug)?,
        pivot_factors: chart.pivot_factors.clone(),
        pivot_words: context.pivot_activation_words.clone(),
        targets: context
            .target_factorized_exact_output
            .iter()
            .map(|value| parse_ratio(value))
            .collect::<Result<_, _>>()?,
    })
}

fn cultivate(
    budget: &RunBudget,
    source_sha256: &str,
    chart: &SourceChartLaw,
    rows: &[TrainingRow],
    expected_law: &LocalLaw,
    extent: &CoefficientExtent,
) -> Result<CultivatedEcology, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let mut timings = Vec::new();
    let mut handles = Vec::with_capacity(rows.len());
    let mut row_words = Vec::with_capacity(rows.len());
    let mut rows_exact = true;
    for row in rows {
        let words = training_words(row);
        let identity = compact_identity_bytes(&words);
        let handle = ArtifactHandle::source(b"training-row", &identity);
        let pair = primed_pair(&mut machine)?;
        let arcs = seed_arcs(pair, handle, &words)?;
        let (radiation, event) = profiled_ending(
            budget,
            &mut machine,
            &format!("training-row-{}", row.ordinal),
            words.len(),
            pair,
            &arcs,
        )?;
        let returned = radiation
            .regional()
            .first()
            .ok_or_else(|| "one training row returned no regional constituent".to_owned())?
            .constituent();
        rows_exact &= decode_training_row(returned, handle.data_namespace)? == *row;
        handles.push(handle);
        row_words.push(words);
        timings.push(event);
    }
    let baseline = machine.rest_image().map_err(debug)?;
    machine = LiveCurrentMachine::from_rest_image(baseline.clone()).map_err(debug)?;
    if machine.rest_image().map_err(debug)? != baseline {
        return Err("the six training rows changed across exact rest/remount".to_owned());
    }

    let meeting_identity = b"cultivate-six-row-local-law";
    let objective_namespace = namespace(&[
        b"eros-contextual-retriangulation-objective-v1",
        source_sha256.as_bytes(),
        meeting_identity,
    ]);
    let objective = InterfaceCapability::new(objective_namespace, 6);
    let after_handles = handles
        .iter()
        .copied()
        .map(|handle| handle.after_contact(meeting_identity))
        .collect::<Vec<_>>();
    let pair = primed_pair(&mut machine)?;
    let mut arcs = Vec::with_capacity(1 + 2 * handles.len());
    push_interface(&mut arcs, pair, objective.clone(), IncidenceHand::Against)?;
    for handle in &handles {
        push_interface(
            &mut arcs,
            pair,
            InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
            IncidenceHand::Against,
        )?;
    }
    for handle in &after_handles {
        push_interface(
            &mut arcs,
            pair,
            InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
            IncidenceHand::Against,
        )?;
    }
    let (radiation, meeting_event) =
        profiled_ending(budget, &mut machine, "six-row-meeting", 1, pair, &arcs)?;
    timings.push(meeting_event);
    let meeting = radiation
        .regional()
        .first()
        .ok_or_else(|| "the six-row meeting returned no constituent".to_owned())?
        .constituent();
    let recovered_rows = handles
        .iter()
        .map(|handle| decode_training_row(meeting, handle.data_namespace))
        .collect::<Result<Vec<_>, _>>()?;
    let rows_recovered_from_standing = recovered_rows == rows;
    let objective_recovered_from_current =
        CapabilityAtlas::from_constituent(meeting)?.namespace_value(objective_namespace)? == 6;
    let derived_law = derive_law(&recovered_rows, &chart.receiver_axes)?;
    let rust_law_equals_independent_source_derivation = derived_law == *expected_law;
    if !rows_recovered_from_standing
        || !objective_recovered_from_current
        || !rust_law_equals_independent_source_derivation
    {
        return Err("the six-row meeting did not recover its exact causal chart".to_owned());
    }

    let law_words = law_words(&derived_law);
    let law_identity = compact_identity_bytes(&law_words);
    let law_handle = ArtifactHandle::source(b"self-emanated-local-law", &law_identity);
    let pair = primed_pair(&mut machine)?;
    let mut arcs = Vec::new();
    push_interface(&mut arcs, pair, objective, IncidenceHand::Against)?;
    for ((handle, words), after) in handles.iter().zip(&row_words).zip(&after_handles) {
        append_words(&mut arcs, pair, handle.data_namespace, words)?;
        push_interface(
            &mut arcs,
            pair,
            InterfaceCapability::new(after.recruit_namespace, RECRUIT_LOCAL),
            IncidenceHand::Against,
        )?;
    }
    append_words(&mut arcs, pair, law_handle.data_namespace, &law_words)?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(law_handle.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    let (radiation, replacement_event) = profiled_ending(
        budget,
        &mut machine,
        "local-law-return",
        law_words.len(),
        pair,
        &arcs,
    )?;
    timings.push(replacement_event);
    let returned_law = decode_law(
        radiation
            .regional()
            .first()
            .ok_or_else(|| "the local-law return emitted no constituent".to_owned())?
            .constituent(),
        law_handle.data_namespace,
    )?;
    if returned_law != derived_law {
        return Err("the local law changed during its return".to_owned());
    }

    let lower_row_data_departed = handles.iter().all(|handle| {
        !machine
            .standing()
            .constituents()
            .iter()
            .any(|constituent| decode_training_row(constituent, handle.data_namespace).is_ok())
    });
    let lower_row_recruitment_departed = after_handles.iter().all(|handle| {
        !standing_has_capability(
            &machine,
            InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
        )
    });
    let returned_standing_law = standing_law(&machine, law_handle.data_namespace)?;
    if returned_standing_law != derived_law {
        return Err("the returned local law is absent from Standing".to_owned());
    }
    let rest = machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(rest.clone()).map_err(debug)?;
    let law_survived_exact_rest_remount = remounted.rest_image().map_err(debug)? == rest
        && standing_law(&remounted, law_handle.data_namespace)? == derived_law;
    let source_lineages_departed = remounted.memory().live_lineages == 0;
    let read = CultivationRead {
        training_currents: rows.len(),
        source_rows_returned_exactly: rows_exact,
        rank: chart.rank,
        pivot_factors: chart.pivot_factors.clone(),
        law_coefficients: extent.count,
        maximum_numerator_bits: extent.maximum_numerator_bits,
        maximum_denominator_bits: extent.maximum_denominator_bits,
        rust_law_equals_independent_source_derivation,
        rows_recovered_from_standing,
        objective_recovered_from_current,
        lower_row_data_departed,
        lower_row_recruitment_departed,
        law_survived_exact_rest_remount,
        source_lineages_departed,
        events: timings,
        machine: machine_read(&remounted)?,
    };
    Ok(CultivatedEcology {
        rest,
        law_handle,
        law: derived_law,
        read,
    })
}

fn run_control(
    budget: &RunBudget,
    source_sha256: &str,
    law_handle: ArtifactHandle,
    chart: &SourceChartLaw,
    context: &SourceContext,
) -> Result<ControlRead, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let ordinal = 0u16;
    let current = CurrentCarrier {
        ordinal,
        pivot_factors: chart.pivot_factors.clone(),
        pivot_words: context.pivot_activation_words.clone(),
    };
    let words = current_words(&current);
    let identity = compact_identity_bytes(&words);
    let current_handle = ArtifactHandle::source(b"no-standing-current", &identity);
    let event_identity = namespace(&[
        b"eros-contextual-retriangulation-control-v1",
        source_sha256.as_bytes(),
        context.current_id.as_bytes(),
    ])
    .to_le_bytes();
    let pair = primed_pair(&mut machine)?;
    let arcs = probe_arcs(
        pair,
        current_handle,
        &words,
        law_handle,
        law_handle.after_contact(&event_identity),
    )?;
    let (radiation, event) = profiled_ending(
        budget,
        &mut machine,
        "no-standing-control",
        words.len(),
        pair,
        &arcs,
    )?;
    let constituent = radiation
        .regional()
        .first()
        .ok_or_else(|| "the no-Standing control returned no constituent".to_owned())?
        .constituent();
    let law_recovered = decode_law(constituent, law_handle.data_namespace).is_ok();
    Ok(ControlRead {
        current_id: context.current_id.clone(),
        pivot_words_presented: current.pivot_words.len(),
        law_recovered,
        output_formed: law_recovered,
        event,
    })
}

#[allow(clippy::too_many_arguments)]
fn conduct_context(
    budget: &RunBudget,
    source_sha256: &str,
    law_rest: &LiveCurrentRestImage,
    law_handle: ArtifactHandle,
    expected_law: &LocalLaw,
    chart: &SourceChartLaw,
    ordinal: usize,
    context: &SourceContext,
) -> Result<ContextRead, String> {
    let mut machine = LiveCurrentMachine::from_rest_image(law_rest.clone()).map_err(debug)?;
    let current = CurrentCarrier {
        ordinal: u16::try_from(ordinal).map_err(debug)?,
        pivot_factors: chart.pivot_factors.clone(),
        pivot_words: context.pivot_activation_words.clone(),
    };
    let words = current_words(&current);
    let identity = compact_identity_bytes(&words);
    let current_handle = ArtifactHandle::source(b"later-current", &identity);
    let event_identity = namespace(&[
        b"eros-contextual-retriangulation-later-current-v1",
        source_sha256.as_bytes(),
        context.current_id.as_bytes(),
    ])
    .to_le_bytes();
    let pair = primed_pair(&mut machine)?;
    let arcs = probe_arcs(
        pair,
        current_handle,
        &words,
        law_handle,
        law_handle.after_contact(&event_identity),
    )?;
    let (radiation, conduct_event) = profiled_ending(
        budget,
        &mut machine,
        &format!("conduct-{}", context.current_id),
        words.len(),
        pair,
        &arcs,
    )?;
    let meeting = radiation
        .regional()
        .first()
        .ok_or_else(|| format!("current {} returned no constituent", context.current_id))?
        .constituent();
    let law = decode_law(meeting, law_handle.data_namespace)?;
    let recovered_current = decode_current(meeting, current_handle.data_namespace)?;
    let law_recovered_from_standing = law == *expected_law;
    let current_recovered_from_source = recovered_current == current;
    if !law_recovered_from_standing || !current_recovered_from_source {
        return Err(format!(
            "current {} lost its law or source face",
            context.current_id
        ));
    }
    let activations = recovered_current
        .pivot_words
        .iter()
        .copied()
        .map(decode_bfloat16)
        .collect::<Result<Vec<_>, _>>()?;
    let prediction = apply_law(&activations, &law)?;
    let predicted_face = face(&law.axes, &prediction);
    let target_factorized = context
        .target_factorized_exact_output
        .iter()
        .map(|value| parse_ratio(value))
        .collect::<Result<Vec<_>, _>>()?;
    let target_observed = context
        .target_observed_output_words
        .iter()
        .copied()
        .map(decode_bfloat16)
        .collect::<Result<Vec<_>, _>>()?;
    let source_prediction = context
        .derived_prediction
        .exact_output
        .iter()
        .map(|value| parse_ratio(value))
        .collect::<Result<Vec<_>, _>>()?;
    let source_derived_prediction_exact =
        prediction == source_prediction && predicted_face == context.derived_prediction.face;
    if !source_derived_prediction_exact {
        return Err(format!(
            "current {} disagrees with the independent exact derivation",
            context.current_id
        ));
    }

    let face_namespace = namespace(&[
        b"eros-contextual-retriangulation-face-v1",
        source_sha256.as_bytes(),
        context.current_id.as_bytes(),
    ]);
    let predicted_bytes = encode_face(&predicted_face)?;
    let pair = primed_pair(&mut machine)?;
    let predicted_arcs = bit_arcs(pair, face_namespace, &predicted_bytes);
    let (radiation, return_event) = profiled_ending(
        budget,
        &mut machine,
        &format!("return-{}", context.current_id),
        predicted_bytes.len() * 8,
        pair,
        &predicted_arcs,
    )?;
    let prior = radiation
        .regional()
        .first()
        .ok_or_else(|| format!("prediction {} returned no face", context.current_id))?
        .constituent()
        .clone();
    let actual_bytes = encode_face(&context.target_observed_face)?;
    let expected_open_bits = differing_bits(&predicted_bytes, &actual_bytes)?;
    let pair = primed_pair(&mut machine)?;
    let actual_arcs = bit_arcs(pair, face_namespace, &actual_bytes);
    let (radiation, comparison_event) = profiled_ending(
        budget,
        &mut machine,
        &format!("compare-{}", context.current_id),
        actual_bytes.len() * 8,
        pair,
        &actual_arcs,
    )?;
    let returned = radiation
        .regional()
        .first()
        .ok_or_else(|| format!("comparison {} returned no face", context.current_id))?
        .constituent();
    let comparison = read_comparison(&prior, returned, face_namespace, expected_open_bits)?;

    Ok(ContextRead {
        current_id: context.current_id.clone(),
        group: context.group.clone(),
        context: context.context.clone(),
        condition: context.condition.clone(),
        source_activation_words: chart.source_factor_count,
        participating_activation_words: current.pivot_words.len(),
        law_recovered_from_standing,
        current_recovered_from_source,
        prediction: prediction.iter().map(ratio_string).collect(),
        source_derived_prediction_exact,
        target_factorized: target_factorized.iter().map(ratio_string).collect(),
        target_observed: target_observed.iter().map(ratio_string).collect(),
        exact_factorized_output: prediction == target_factorized,
        factorized_face_rides: predicted_face == context.target_factorized_face,
        observed_face_rides: predicted_face == context.target_observed_face,
        predicted_face,
        factorized_residual: residual(&law.axes, &prediction, &target_factorized),
        observed_residual: residual(&law.axes, &prediction, &target_observed),
        comparison,
        events: vec![conduct_event, return_event, comparison_event],
    })
}

fn derive_law(rows: &[TrainingRow], axes: &[u32]) -> Result<LocalLaw, String> {
    if rows.is_empty() {
        return Err("the local chart has no training rows".to_owned());
    }
    let pivots = rows[0].pivot_factors.clone();
    if rows.len() != pivots.len()
        || rows.iter().any(|row| row.pivot_factors != pivots)
        || rows
            .iter()
            .any(|row| row.pivot_words.len() != pivots.len() || row.targets.len() != axes.len())
    {
        return Err("the training rows do not form one square local chart".to_owned());
    }
    let left = rows
        .iter()
        .map(|row| {
            row.pivot_words
                .iter()
                .copied()
                .map(decode_bfloat16)
                .collect()
        })
        .collect::<Result<Vec<Vec<_>>, _>>()?;
    let right = rows
        .iter()
        .map(|row| row.targets.clone())
        .collect::<Vec<_>>();
    let coefficients = solve_square(left, right)?;
    Ok(LocalLaw {
        pivot_factors: pivots,
        axes: axes.to_vec(),
        coefficients,
    })
}

fn solve_square(
    left: Vec<Vec<BigRational>>,
    right: Vec<Vec<BigRational>>,
) -> Result<Vec<Vec<BigRational>>, String> {
    let extent = left.len();
    if extent == 0
        || left.iter().any(|row| row.len() != extent)
        || right.len() != extent
        || right.is_empty()
    {
        return Err("the exact elimination chart is not square".to_owned());
    }
    let outputs = right[0].len();
    if right.iter().any(|row| row.len() != outputs) {
        return Err("the exact elimination target changed width".to_owned());
    }
    let mut matrix = left
        .into_iter()
        .zip(right)
        .map(|(mut left, right)| {
            left.extend(right);
            left
        })
        .collect::<Vec<_>>();
    let zero = BigRational::from_integer(BigInt::from(0));
    for column in 0..extent {
        let pivot = (column..extent)
            .find(|row| matrix[*row][column] != zero)
            .ok_or_else(|| format!("the exact chart is singular at column {column}"))?;
        matrix.swap(column, pivot);
        let pivot_value = matrix[column][column].clone();
        for value in &mut matrix[column] {
            *value /= pivot_value.clone();
        }
        for row in 0..extent {
            if row == column || matrix[row][column] == zero {
                continue;
            }
            let scale = matrix[row][column].clone();
            let basis = matrix[column].clone();
            for (value, basis) in matrix[row].iter_mut().zip(basis) {
                *value -= scale.clone() * basis;
            }
        }
    }
    Ok(matrix
        .into_iter()
        .map(|row| row[extent..].to_vec())
        .collect())
}

fn apply_law(activations: &[BigRational], law: &LocalLaw) -> Result<Vec<BigRational>, String> {
    if activations.len() != law.coefficients.len()
        || law
            .coefficients
            .iter()
            .any(|row| row.len() != law.axes.len())
    {
        return Err("the later current and local law changed common extent".to_owned());
    }
    Ok((0..law.axes.len())
        .map(|axis| {
            activations.iter().zip(&law.coefficients).fold(
                BigRational::from_integer(BigInt::from(0)),
                |sum, (activation, row)| sum + activation * &row[axis],
            )
        })
        .collect())
}

fn decode_bfloat16(word: u16) -> Result<BigRational, String> {
    let negative = word >> 15 != 0;
    let exponent = (word >> 7) & 0xff;
    let fraction = word & 0x7f;
    if exponent == 0xff {
        return Err(format!("BF16 word 0x{word:04x} is not finite"));
    }
    let (coefficient, power) = if exponent == 0 {
        (i64::from(fraction), -133)
    } else {
        (i64::from((1u16 << 7) | fraction), i32::from(exponent) - 134)
    };
    let coefficient = if negative { -coefficient } else { coefficient };
    if power >= 0 {
        Ok(BigRational::from_integer(
            BigInt::from(coefficient) << usize::try_from(power).map_err(debug)?,
        ))
    } else {
        Ok(BigRational::new(
            BigInt::from(coefficient),
            BigInt::from(1) << usize::try_from(-power).map_err(debug)?,
        ))
    }
}

fn parse_ratio(value: &str) -> Result<BigRational, String> {
    let (numerator, denominator) = match value.split_once('/') {
        Some((numerator, denominator)) => (numerator, denominator),
        None => (value, "1"),
    };
    let numerator = numerator
        .parse::<BigInt>()
        .map_err(|error| format!("ratio numerator {numerator:?} parses: {error}"))?;
    let denominator = denominator
        .parse::<BigInt>()
        .map_err(|error| format!("ratio denominator {denominator:?} parses: {error}"))?;
    if denominator <= BigInt::from(0) {
        return Err(format!("ratio {value:?} has a nonpositive denominator"));
    }
    Ok(BigRational::new(numerator, denominator))
}

fn ratio_string(value: &BigRational) -> String {
    if *value.denom() == BigInt::from(1) {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

fn face(axes: &[u32], values: &[BigRational]) -> Face {
    let mut order = (0..axes.len()).collect::<Vec<_>>();
    order.sort_by(|left, right| {
        values[*right]
            .cmp(&values[*left])
            .then_with(|| axes[*left].cmp(&axes[*right]))
    });
    Face {
        orientation: values
            .iter()
            .map(
                |value| match value.cmp(&BigRational::from_integer(BigInt::from(0))) {
                    Ordering::Less => "negative",
                    Ordering::Equal => "zero",
                    Ordering::Greater => "positive",
                },
            )
            .map(str::to_owned)
            .collect(),
        signed_axis_order: order.into_iter().map(|at| axes[at]).collect(),
    }
}

fn residual(axes: &[u32], prediction: &[BigRational], target: &[BigRational]) -> Vec<ResidualRead> {
    axes.iter()
        .copied()
        .zip(prediction)
        .zip(target)
        .map(|((axis, prediction), target)| ResidualRead {
            axis,
            prediction: ratio_string(prediction),
            target: ratio_string(target),
            target_minus_prediction: ratio_string(&(target - prediction)),
        })
        .collect()
}

fn training_words(row: &TrainingRow) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(ROW_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(ROW_ORDINAL, u64::from(row.ordinal)),
        CompactWord::scalar(ROW_PIVOT_COUNT, row.pivot_factors.len() as u64),
        CompactWord::scalar(ROW_AXIS_COUNT, row.targets.len() as u64),
    ];
    for (at, (factor, word)) in row
        .pivot_factors
        .iter()
        .copied()
        .zip(row.pivot_words.iter().copied())
        .enumerate()
    {
        words.push(CompactWord::at(
            ROW_PIVOT_FACTOR,
            vec![at as u64],
            u64::from(factor),
        ));
        words.push(CompactWord::at(
            ROW_PIVOT_WORD,
            vec![at as u64],
            u64::from(word),
        ));
    }
    for (axis, target) in row.targets.iter().enumerate() {
        append_rational_words(
            &mut words,
            &[axis as u64],
            [
                ROW_TARGET_NUMERATOR_SIGN,
                ROW_TARGET_NUMERATOR_COUNT,
                ROW_TARGET_NUMERATOR_LIMB,
                ROW_TARGET_DENOMINATOR_SIGN,
                ROW_TARGET_DENOMINATOR_COUNT,
                ROW_TARGET_DENOMINATOR_LIMB,
            ],
            target,
        );
    }
    words
}

fn law_words(law: &LocalLaw) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(LAW_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(LAW_RANK, law.pivot_factors.len() as u64),
        CompactWord::scalar(LAW_AXIS_COUNT, law.axes.len() as u64),
    ];
    for (at, factor) in law.pivot_factors.iter().copied().enumerate() {
        words.push(CompactWord::at(
            LAW_PIVOT_FACTOR,
            vec![at as u64],
            u64::from(factor),
        ));
    }
    for (at, axis) in law.axes.iter().copied().enumerate() {
        words.push(CompactWord::at(LAW_AXIS, vec![at as u64], u64::from(axis)));
    }
    for (row, coefficients) in law.coefficients.iter().enumerate() {
        for (axis, coefficient) in coefficients.iter().enumerate() {
            append_rational_words(
                &mut words,
                &[row as u64, axis as u64],
                [
                    LAW_COEFFICIENT_NUMERATOR_SIGN,
                    LAW_COEFFICIENT_NUMERATOR_COUNT,
                    LAW_COEFFICIENT_NUMERATOR_LIMB,
                    LAW_COEFFICIENT_DENOMINATOR_SIGN,
                    LAW_COEFFICIENT_DENOMINATOR_COUNT,
                    LAW_COEFFICIENT_DENOMINATOR_LIMB,
                ],
                coefficient,
            );
        }
    }
    words
}

fn current_words(current: &CurrentCarrier) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(CURRENT_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(CURRENT_ORDINAL, u64::from(current.ordinal)),
        CompactWord::scalar(CURRENT_PIVOT_COUNT, current.pivot_factors.len() as u64),
    ];
    for (at, (factor, word)) in current
        .pivot_factors
        .iter()
        .copied()
        .zip(current.pivot_words.iter().copied())
        .enumerate()
    {
        words.push(CompactWord::at(
            CURRENT_PIVOT_FACTOR,
            vec![at as u64],
            u64::from(factor),
        ));
        words.push(CompactWord::at(
            CURRENT_PIVOT_WORD,
            vec![at as u64],
            u64::from(word),
        ));
    }
    words
}

fn append_rational_words(
    words: &mut Vec<CompactWord>,
    coordinates: &[u64],
    tags: [u64; 6],
    value: &BigRational,
) {
    append_bigint_words(words, coordinates, tags[0], tags[1], tags[2], value.numer());
    append_bigint_words(words, coordinates, tags[3], tags[4], tags[5], value.denom());
}

fn append_bigint_words(
    words: &mut Vec<CompactWord>,
    coordinates: &[u64],
    sign_tag: u64,
    count_tag: u64,
    limb_tag: u64,
    value: &BigInt,
) {
    let (sign, limbs) = value.to_u32_digits();
    words.push(CompactWord::at(
        sign_tag,
        coordinates.to_vec(),
        sign_code(sign),
    ));
    words.push(CompactWord::at(
        count_tag,
        coordinates.to_vec(),
        limbs.len() as u64,
    ));
    for (at, limb) in limbs.into_iter().enumerate() {
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        words.push(CompactWord::at(limb_tag, route, u64::from(limb)));
    }
}

fn decode_training_row(constituent: &LiveConstituent, root: u64) -> Result<TrainingRow, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, ROW_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("training-row schema changed".to_owned());
    }
    let ordinal = u16::try_from(atlas.word(root, ROW_ORDINAL, &[])?).map_err(debug)?;
    let pivots = usize::try_from(atlas.word(root, ROW_PIVOT_COUNT, &[])?).map_err(debug)?;
    let axes = usize::try_from(atlas.word(root, ROW_AXIS_COUNT, &[])?).map_err(debug)?;
    let mut pivot_factors = Vec::with_capacity(pivots);
    let mut pivot_words = Vec::with_capacity(pivots);
    for at in 0..pivots {
        pivot_factors
            .push(u32::try_from(atlas.word(root, ROW_PIVOT_FACTOR, &[at as u64])?).map_err(debug)?);
        pivot_words
            .push(u16::try_from(atlas.word(root, ROW_PIVOT_WORD, &[at as u64])?).map_err(debug)?);
    }
    let targets = (0..axes)
        .map(|axis| {
            decode_rational_words(
                &atlas,
                root,
                &[axis as u64],
                [
                    ROW_TARGET_NUMERATOR_SIGN,
                    ROW_TARGET_NUMERATOR_COUNT,
                    ROW_TARGET_NUMERATOR_LIMB,
                    ROW_TARGET_DENOMINATOR_SIGN,
                    ROW_TARGET_DENOMINATOR_COUNT,
                    ROW_TARGET_DENOMINATOR_LIMB,
                ],
            )
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(TrainingRow {
        ordinal,
        pivot_factors,
        pivot_words,
        targets,
    })
}

fn decode_law(constituent: &LiveConstituent, root: u64) -> Result<LocalLaw, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, LAW_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("local-law schema changed".to_owned());
    }
    let rank = usize::try_from(atlas.word(root, LAW_RANK, &[])?).map_err(debug)?;
    let axes_count = usize::try_from(atlas.word(root, LAW_AXIS_COUNT, &[])?).map_err(debug)?;
    let pivot_factors = (0..rank)
        .map(|at| u32::try_from(atlas.word(root, LAW_PIVOT_FACTOR, &[at as u64])?).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let axes = (0..axes_count)
        .map(|at| u32::try_from(atlas.word(root, LAW_AXIS, &[at as u64])?).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let coefficients = (0..rank)
        .map(|row| {
            (0..axes_count)
                .map(|axis| {
                    decode_rational_words(
                        &atlas,
                        root,
                        &[row as u64, axis as u64],
                        [
                            LAW_COEFFICIENT_NUMERATOR_SIGN,
                            LAW_COEFFICIENT_NUMERATOR_COUNT,
                            LAW_COEFFICIENT_NUMERATOR_LIMB,
                            LAW_COEFFICIENT_DENOMINATOR_SIGN,
                            LAW_COEFFICIENT_DENOMINATOR_COUNT,
                            LAW_COEFFICIENT_DENOMINATOR_LIMB,
                        ],
                    )
                })
                .collect()
        })
        .collect::<Result<Vec<Vec<_>>, String>>()?;
    Ok(LocalLaw {
        pivot_factors,
        axes,
        coefficients,
    })
}

fn decode_current(constituent: &LiveConstituent, root: u64) -> Result<CurrentCarrier, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, CURRENT_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("later-current schema changed".to_owned());
    }
    let ordinal = u16::try_from(atlas.word(root, CURRENT_ORDINAL, &[])?).map_err(debug)?;
    let pivots = usize::try_from(atlas.word(root, CURRENT_PIVOT_COUNT, &[])?).map_err(debug)?;
    let pivot_factors = (0..pivots)
        .map(|at| {
            u32::try_from(atlas.word(root, CURRENT_PIVOT_FACTOR, &[at as u64])?).map_err(debug)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let pivot_words = (0..pivots)
        .map(|at| u16::try_from(atlas.word(root, CURRENT_PIVOT_WORD, &[at as u64])?).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CurrentCarrier {
        ordinal,
        pivot_factors,
        pivot_words,
    })
}

fn decode_rational_words(
    atlas: &CapabilityAtlas,
    root: u64,
    coordinates: &[u64],
    tags: [u64; 6],
) -> Result<BigRational, String> {
    let numerator = decode_bigint(atlas, root, coordinates, tags[0], tags[1], tags[2])?;
    let denominator = decode_bigint(atlas, root, coordinates, tags[3], tags[4], tags[5])?;
    if denominator.sign() != Sign::Plus {
        return Err("a compact rational denominator is not positive".to_owned());
    }
    Ok(BigRational::new(numerator, denominator))
}

fn decode_bigint(
    atlas: &CapabilityAtlas,
    root: u64,
    coordinates: &[u64],
    sign_tag: u64,
    count_tag: u64,
    limb_tag: u64,
) -> Result<BigInt, String> {
    let sign = sign_from_code(atlas.word(root, sign_tag, coordinates)?)?;
    let count = usize::try_from(atlas.word(root, count_tag, coordinates)?).map_err(debug)?;
    let mut limbs = Vec::with_capacity(count);
    for at in 0..count {
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        limbs.push(u32::try_from(atlas.word(root, limb_tag, &route)?).map_err(debug)?);
    }
    if (sign == Sign::NoSign) != limbs.is_empty() {
        return Err("a compact integer sign and limb population disagree".to_owned());
    }
    Ok(BigInt::new(sign, limbs))
}

fn sign_code(sign: Sign) -> u64 {
    match sign {
        Sign::NoSign => 0,
        Sign::Plus => 1,
        Sign::Minus => 2,
    }
}

fn sign_from_code(code: u64) -> Result<Sign, String> {
    match code {
        0 => Ok(Sign::NoSign),
        1 => Ok(Sign::Plus),
        2 => Ok(Sign::Minus),
        _ => Err(format!("compact integer sign code {code} is invalid")),
    }
}

fn seed_arcs(
    pair: [CurrentLineage; 2],
    handle: ArtifactHandle,
    words: &[CompactWord],
) -> Result<Vec<RegionalRelationArc>, String> {
    let mut arcs = Vec::with_capacity(words.len() + 1);
    append_words(&mut arcs, pair, handle.data_namespace, words)?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    Ok(arcs)
}

fn probe_arcs(
    pair: [CurrentLineage; 2],
    current_handle: ArtifactHandle,
    current_words: &[CompactWord],
    law_before: ArtifactHandle,
    law_after: ArtifactHandle,
) -> Result<Vec<RegionalRelationArc>, String> {
    let mut arcs = Vec::with_capacity(current_words.len() + 2);
    append_words(
        &mut arcs,
        pair,
        current_handle.data_namespace,
        current_words,
    )?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(law_before.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(law_after.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::With,
    )?;
    Ok(arcs)
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
    arcs.push(interface_arc(
        pair,
        interface.namespace(),
        interface.local(),
        slot,
        hand,
    ));
    Ok(())
}

fn bit_arcs(pair: [CurrentLineage; 2], namespace: u64, bytes: &[u8]) -> Vec<RegionalRelationArc> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte >> bit & 1 != 0))
        .enumerate()
        .map(|(at, bit)| {
            interface_arc(
                pair,
                namespace,
                at as u64,
                u32::try_from(at).expect("bounded face carrier"),
                if bit {
                    IncidenceHand::With
                } else {
                    IncidenceHand::Against
                },
            )
        })
        .collect()
}

fn interface_arc(
    pair: [CurrentLineage; 2],
    namespace: u64,
    local: u64,
    boundary_slot: u32,
    hand: IncidenceHand,
) -> RegionalRelationArc {
    RegionalRelationArc::new(
        pair[0],
        CurrentBoundaryPort::Cell,
        pair[1],
        CurrentBoundaryPort::Cell,
        InterfaceCapability::new(namespace, local),
        boundary_slot,
        0,
        hand,
    )
}

fn encode_face(face: &Face) -> Result<Vec<u8>, String> {
    if face.orientation.len() != 5 || face.signed_axis_order.len() != 5 {
        return Err("the receiver face changed its five-axis extent".to_owned());
    }
    let mut bytes = Vec::with_capacity(30);
    bytes.extend(*b"FACE");
    bytes.push(1);
    for orientation in &face.orientation {
        bytes.push(match orientation.as_str() {
            "negative" => 1,
            "zero" => 2,
            "positive" => 3,
            value => return Err(format!("unknown receiver orientation {value:?}")),
        });
    }
    for axis in &face.signed_axis_order {
        bytes.extend(axis.to_le_bytes());
    }
    Ok(bytes)
}

fn differing_bits(left: &[u8], right: &[u8]) -> Result<Vec<u64>, String> {
    if left.len() != right.len() {
        return Err("the compared face carriers changed extent".to_owned());
    }
    Ok(left
        .iter()
        .zip(right)
        .enumerate()
        .flat_map(|(octet, (left, right))| {
            let difference = left ^ right;
            (0..8).filter_map(move |bit| {
                (difference >> bit & 1 != 0).then_some((octet * 8 + bit) as u64)
            })
        })
        .collect())
}

fn read_comparison(
    prior: &LiveConstituent,
    returned: &LiveConstituent,
    namespace: u64,
    expected_open_bits: Vec<u64>,
) -> Result<ComparisonRead, String> {
    let prior_bits = prior
        .pins()
        .iter()
        .filter_map(|pin| {
            pin.interface()
                .filter(|interface| interface.namespace() == namespace)
                .map(|interface| (interface.local(), pin.clone()))
        })
        .collect::<BTreeMap<_, _>>();
    if prior_bits.len() != 30 * 8 {
        return Err(format!(
            "the predicted face retained {} bits instead of 240",
            prior_bits.len()
        ));
    }
    let mut carried_open_bits = Vec::new();
    let mut found_pins = 0usize;
    for (local, prior_pin) in prior_bits {
        let comparison_pins = returned
            .pins()
            .iter()
            .filter(|pin| !prior.pins().contains(pin))
            .filter(|pin| {
                pin.interface().is_some_and(|interface| {
                    interface.namespace() == namespace && interface.local() == local
                })
            })
            .filter(|pin| pin.held() == prior_pin.meeting())
            .collect::<Vec<_>>();
        if comparison_pins.len() != 1 {
            return Err(format!(
                "face bit {local} returned {} comparison pins instead of one",
                comparison_pins.len()
            ));
        }
        let pin = comparison_pins[0];
        if pin.is_open() {
            carried_open_bits.push(local);
        }
        found_pins += usize::from(pin.is_found());
    }
    Ok(ComparisonRead {
        open_bits_exact: carried_open_bits == expected_open_bits,
        expected_open_bits,
        carried_open_bits,
        found_pins,
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
    if arcs.len() > MAX_ARCS_PER_CELL {
        return Err(format!(
            "event {event_name} requires {} arcs, beyond the fixed limit {MAX_ARCS_PER_CELL}",
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
            "event {event_name} exceeded its {} second limit",
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

fn standing_law(machine: &LiveCurrentMachine, root: u64) -> Result<LocalLaw, String> {
    let laws = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_law(constituent, root).ok())
        .collect::<Vec<_>>();
    match laws.as_slice() {
        [law] => Ok(law.clone()),
        [] => Err(format!(
            "Standing exposes no local law under {}",
            namespace_string(root)
        )),
        _ => Err(format!(
            "Standing exposes plural local laws under {}",
            namespace_string(root)
        )),
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

fn machine_read(machine: &LiveCurrentMachine) -> Result<MachineRead, String> {
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
    let rest_octets = machine
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. The hash below is untouched and
    // still reported; these are the same octets reaching `holon-plate deposit --from ERST:` instead
    // of being hashed and dropped. This site sits inside a helper the driver calls at every read.
    // The address is the content, so every distinct rest it seals is deposited at its own address
    // instead of all but the last being overwritten, and the file name carries the reported hash.
    let deposited = deposit_form_or_message(FORM_DRIVER, MACHINE_REST_FORM, &rest_octets)?;
    eprintln!("form deposited: {}", deposited.path.display());
    Ok(MachineRead {
        standing_rank: machine.standing().rank(),
        standing_cells,
        standing_constituents,
        constituent_cells,
        constituent_incidences,
        constituent_pins,
        constituent_paths,
        constituent_transport_terms,
        live_lineages,
        rest_sha256: sha256(&rest_octets),
    })
}

fn compact_route_namespace(root: u64, word: &CompactWord) -> u64 {
    let mut route = Vec::with_capacity(2 + word.coordinates.len());
    route.extend_from_slice(&word.tag.to_le_bytes());
    route.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
    for coordinate in &word.coordinates {
        route.extend_from_slice(&coordinate.to_le_bytes());
    }
    namespace(&[
        b"eros-contextual-retriangulation-word-v1",
        &root.to_le_bytes(),
        &route,
    ])
}

fn compact_identity_bytes(words: &[CompactWord]) -> Vec<u8> {
    let mut identity = Vec::new();
    identity.extend_from_slice(&(words.len() as u64).to_le_bytes());
    for word in words {
        identity.extend_from_slice(&word.tag.to_le_bytes());
        identity.extend_from_slice(&(word.coordinates.len() as u64).to_le_bytes());
        for coordinate in &word.coordinates {
            identity.extend_from_slice(&coordinate.to_le_bytes());
        }
        identity.extend_from_slice(&word.value.to_le_bytes());
    }
    identity
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

fn namespace_string(namespace: u64) -> String {
    format!("0x{namespace:016x}")
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
    "usage: cargo run -p life --example eros_contextual_retriangulation -- <SOURCE.json> <REPORT.json>"
}
