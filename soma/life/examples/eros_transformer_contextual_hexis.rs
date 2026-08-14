use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage, LiveMemory,
    RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_transformer_contextual_hexis/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_transformer_contextual_hexis";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
const SOURCE_SCHEMA: &str = "eros.transformer-contextual-hexis.source.v1";
const REPORT_SCHEMA: &str = "eros.transformer-contextual-hexis.report.v1";
const EXPERT_MAGIC: [u8; 4] = *b"XPRT";
const CONTEXT_MAGIC: [u8; 4] = *b"CTXT";
const CARRIER_VERSION: u8 = 1;
const RECRUIT_LOCAL: u64 = 0;
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];

#[derive(Clone, Debug, PartialEq, Eq)]
struct Dyadic {
    coefficient: BigInt,
    exponent: i32,
}

impl Dyadic {
    fn new(mut coefficient: BigInt, mut exponent: i32) -> Self {
        if coefficient == BigInt::from(0) {
            return Self {
                coefficient,
                exponent: 0,
            };
        }
        let two = BigInt::from(2);
        while &coefficient % &two == BigInt::from(0) {
            coefficient >>= 1usize;
            exponent += 1;
        }
        Self {
            coefficient,
            exponent,
        }
    }

    fn zero() -> Self {
        Self::new(BigInt::from(0), 0)
    }

    fn from_bfloat16(word: u16) -> Result<Self, String> {
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
        Ok(Self::new(
            BigInt::from(if negative { -coefficient } else { coefficient }),
            power,
        ))
    }

    fn from_read(read: &SourceDyadic) -> Result<Self, String> {
        let coefficient = read
            .coefficient
            .parse::<BigInt>()
            .map_err(|error| format!("source dyadic coefficient parses: {error}"))?;
        Ok(Self::new(coefficient, read.power_of_two))
    }

    fn add(&self, other: &Self) -> Self {
        let exponent = self.exponent.min(other.exponent);
        let left = &self.coefficient
            << usize::try_from(self.exponent - exponent).expect("nonnegative dyadic shift");
        let right = &other.coefficient
            << usize::try_from(other.exponent - exponent).expect("nonnegative dyadic shift");
        Self::new(left + right, exponent)
    }

    fn subtract(&self, other: &Self) -> Self {
        self.add(&Self::new(-other.coefficient.clone(), other.exponent))
    }

    fn multiply(&self, other: &Self) -> Self {
        Self::new(
            &self.coefficient * &other.coefficient,
            self.exponent + other.exponent,
        )
    }

    fn orientation(&self) -> &'static str {
        if self.coefficient > BigInt::from(0) {
            "positive"
        } else if self.coefficient < BigInt::from(0) {
            "negative"
        } else {
            "zero"
        }
    }

    fn read(&self) -> DyadicRead {
        let exact_ratio = if self.exponent >= 0 {
            format!(
                "{}",
                &self.coefficient
                    << usize::try_from(self.exponent).expect("nonnegative dyadic exponent")
            )
        } else {
            format!("{}/2^{}", self.coefficient, self.exponent.unsigned_abs())
        };
        DyadicRead {
            coefficient: self.coefficient.to_string(),
            power_of_two: self.exponent,
            exact_ratio,
            orientation: self.orientation(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExpertLaw {
    expert: u32,
    weights: BTreeMap<u32, u16>,
}

impl ExpertLaw {
    fn encode(&self) -> Result<Vec<u8>, String> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&EXPERT_MAGIC);
        bytes.push(CARRIER_VERSION);
        bytes.extend_from_slice(&self.expert.to_le_bytes());
        bytes.extend_from_slice(
            &u16::try_from(self.weights.len())
                .map_err(|_| "expert axis extent exceeds the carrier".to_owned())?
                .to_le_bytes(),
        );
        for (axis, word) in &self.weights {
            bytes.extend_from_slice(&axis.to_le_bytes());
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        Ok(bytes)
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0usize;
        if take(bytes, &mut cursor, 4)? != EXPERT_MAGIC {
            return Err("expert carrier magic changed".to_owned());
        }
        if take(bytes, &mut cursor, 1)?[0] != CARRIER_VERSION {
            return Err("expert carrier version changed".to_owned());
        }
        let expert = read_u32(bytes, &mut cursor)?;
        let extent = usize::from(read_u16(bytes, &mut cursor)?);
        let mut weights = BTreeMap::new();
        for _ in 0..extent {
            let axis = read_u32(bytes, &mut cursor)?;
            let word = read_u16(bytes, &mut cursor)?;
            if weights.insert(axis, word).is_some() {
                return Err("one expert axis was carried twice".to_owned());
            }
        }
        if cursor != bytes.len() {
            return Err("expert carrier has trailing material".to_owned());
        }
        Ok(Self { expert, weights })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ContextCarrier {
    identity: u64,
    activations: BTreeMap<u32, u16>,
}

impl ContextCarrier {
    fn encode(&self) -> Result<Vec<u8>, String> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&CONTEXT_MAGIC);
        bytes.push(CARRIER_VERSION);
        bytes.extend_from_slice(&self.identity.to_le_bytes());
        bytes.extend_from_slice(
            &u16::try_from(self.activations.len())
                .map_err(|_| "context expert extent exceeds the carrier".to_owned())?
                .to_le_bytes(),
        );
        for (expert, word) in &self.activations {
            bytes.extend_from_slice(&expert.to_le_bytes());
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        Ok(bytes)
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0usize;
        if take(bytes, &mut cursor, 4)? != CONTEXT_MAGIC {
            return Err("context carrier magic changed".to_owned());
        }
        if take(bytes, &mut cursor, 1)?[0] != CARRIER_VERSION {
            return Err("context carrier version changed".to_owned());
        }
        let identity = read_u64(bytes, &mut cursor)?;
        let extent = usize::from(read_u16(bytes, &mut cursor)?);
        let mut activations = BTreeMap::new();
        for _ in 0..extent {
            let expert = read_u32(bytes, &mut cursor)?;
            let word = read_u16(bytes, &mut cursor)?;
            if activations.insert(expert, word).is_some() {
                return Err("one context activation was carried twice".to_owned());
            }
        }
        if cursor != bytes.len() {
            return Err("context carrier has trailing material".to_owned());
        }
        Ok(Self {
            identity,
            activations,
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct ExpertHandle {
    data_namespace: u64,
    recruit_namespace: u64,
}

impl ExpertHandle {
    fn new(model_sha256: &str, layer: u32, law: &ExpertLaw) -> Result<Self, String> {
        let encoded = law.encode()?;
        Ok(Self {
            data_namespace: namespace(&[
                b"eros-contextual-expert-data-v1",
                model_sha256.as_bytes(),
                &layer.to_le_bytes(),
                &law.expert.to_le_bytes(),
                &encoded,
            ]),
            recruit_namespace: namespace(&[
                b"eros-contextual-expert-recruit-v1",
                model_sha256.as_bytes(),
                &layer.to_le_bytes(),
                &law.expert.to_le_bytes(),
                &encoded,
            ]),
        })
    }

    fn renewed(self, context_identity: u64) -> Self {
        Self {
            data_namespace: self.data_namespace,
            recruit_namespace: namespace(&[
                b"eros-contextual-expert-renew-v1",
                &self.recruit_namespace.to_le_bytes(),
                &context_identity.to_le_bytes(),
            ]),
        }
    }

    fn read(self, expert: u32) -> HandleRead {
        HandleRead {
            expert,
            data_namespace: format!("0x{:016x}", self.data_namespace),
            recruit_namespace: format!("0x{:016x}", self.recruit_namespace),
        }
    }
}

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    model: SourceModel,
    selection: SourceSelection,
    ecology: SourceEcology,
    contexts: Vec<SourceContext>,
}

#[derive(Deserialize)]
struct SourceModel {
    repository: String,
    revision: String,
    model_sha256: String,
}

#[derive(Deserialize)]
struct SourceSelection {
    selected_layer: u32,
    receiver_axes: Vec<u32>,
    layer_census: Value,
}

#[derive(Deserialize)]
struct SourceEcology {
    source_expert_count: usize,
    experts: Vec<SourceExpert>,
    q1_overlap: Value,
}

#[derive(Deserialize)]
struct SourceExpert {
    expert: u32,
    weights: BTreeMap<String, SourceWord>,
}

#[derive(Deserialize)]
struct SourceContext {
    context: String,
    current_id: String,
    prompt_sha256: String,
    prompt_extent: usize,
    receiver_position: usize,
    q1_experts: Vec<u32>,
    pool_activation_words: BTreeMap<String, SourceWord>,
    q1_output: BTreeMap<String, SourceDyadic>,
    q1_residual: BTreeMap<String, SourceDyadic>,
    full_exact_output: BTreeMap<String, SourceDyadic>,
    full_sign: BTreeMap<String, String>,
    hexis_boundaries: Value,
    benchmark: Value,
}

#[derive(Deserialize)]
struct SourceWord {
    word: u16,
}

#[derive(Deserialize)]
struct SourceDyadic {
    coefficient: String,
    power_of_two: i32,
}

struct DepositedExpert {
    law: ExpertLaw,
    handle: ExpertHandle,
}

struct ContextCase {
    context: String,
    current_id: String,
    prompt_sha256: String,
    prompt_extent: usize,
    receiver_position: usize,
    selected_experts: Vec<u32>,
    pool_activations: BTreeMap<u32, u16>,
    expected_output: BTreeMap<u32, Dyadic>,
    expected_residual: BTreeMap<u32, Dyadic>,
    full_output: BTreeMap<u32, Dyadic>,
    full_sign: BTreeMap<u32, String>,
    hexis_boundaries: Value,
    benchmark: Value,
}

#[derive(Clone)]
struct MachineCheckpoint {
    body: LiveCurrentRestImage,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: &'static str,
    source: SourceRead,
    deposit: DepositRead,
    contexts: Vec<ContextRead>,
    comparison: ComparisonRead,
    acceptance: AcceptanceRead,
    conclusion: &'static str,
}

#[derive(Serialize)]
struct SourceRead {
    source_observation_id: String,
    source_sha256: String,
    repository: String,
    revision: String,
    model_sha256: String,
    layer: u32,
    receiver_axes: Vec<u32>,
    source_experts: usize,
    inherited_pool_experts: Vec<u32>,
    layer_census: Value,
    q1_overlap: Value,
}

#[derive(Serialize)]
struct DepositRead {
    machine: MachineRead,
    no_ecology_control: MachineRead,
    rest_remount_exact: bool,
    source_lineages_after_event: usize,
    experts: Vec<ExpertRead>,
}

#[derive(Serialize)]
struct ExpertRead {
    expert: u32,
    handle: HandleRead,
    axes: Vec<u32>,
    encoded_bits: usize,
    returned_exact: bool,
    constituent: ConstituentRead,
}

#[derive(Serialize)]
struct HandleRead {
    expert: u32,
    data_namespace: String,
    recruit_namespace: String,
}

#[derive(Serialize)]
struct ContextRead {
    context: String,
    current_id: String,
    prompt_sha256: String,
    prompt_extent: usize,
    receiver_position: usize,
    selected_experts: Vec<u32>,
    recovered_experts: Vec<u32>,
    activations: BTreeMap<u32, WordRead>,
    field_conducted_from_radiation: BTreeMap<u32, DyadicRead>,
    full_transformer_face: BTreeMap<u32, DyadicRead>,
    residual_to_full: BTreeMap<u32, DyadicRead>,
    full_orientation: BTreeMap<u32, String>,
    radiated_hexis_orientation: BTreeMap<u32, String>,
    phase_orientation_exact: bool,
    q1_output_exact: bool,
    no_ecology_refused: bool,
    rest_remount_exact: bool,
    native_constituent: ConstituentRead,
    no_ecology_constituent: ConstituentRead,
    alternate_hexis: AlternateHexisRead,
    hexis_boundaries: Value,
    benchmark: Value,
}

#[derive(Serialize)]
struct AlternateHexisRead {
    selected_from_context: String,
    selected_experts: Vec<u32>,
    output: BTreeMap<u32, DyadicRead>,
    differs_from_native_field: bool,
}

#[derive(Serialize)]
struct ComparisonRead {
    conducted_field_pairs_distinct: usize,
    same_membership_contexts: Vec<String>,
    same_membership_outputs_differ: bool,
    differing_membership_contexts: Vec<String>,
    differing_membership_outputs_differ: bool,
}

#[derive(Serialize)]
struct AcceptanceRead {
    source_event_lineages_departed: bool,
    inherited_pool_became_standing: bool,
    source_absent_contexts_recovered_exact_selected_laws: bool,
    all_radiated_hexeis_conduct_to_exact_q1_field: bool,
    all_no_ecology_controls_refused: bool,
    all_orientation_faces_match_full_transformer_field: bool,
    varying_context_changes_membership_or_exact_conduct: bool,
    same_membership_still_changes_conduct: bool,
    all_context_successors_rest_remount_exactly: bool,
    no_float_operation_in_radiation_conductor: bool,
}

#[derive(Serialize)]
struct WordRead {
    word: u16,
    hex: String,
    exact: DyadicRead,
}

#[derive(Serialize)]
struct DyadicRead {
    coefficient: String,
    power_of_two: i32,
    exact_ratio: String,
    orientation: &'static str,
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
    rest_sha256: String,
}

#[derive(Serialize)]
struct ConstituentRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    paths: usize,
    boundaries: usize,
    exposed_pins: usize,
    native_sha256: String,
}

struct ProbeOutcome {
    output: Option<BTreeMap<u32, Dyadic>>,
    recovered_experts: Vec<u32>,
    checkpoint: MachineCheckpoint,
    constituent: ConstituentRead,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros transformer contextual hexis: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let output_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads completely: {error}", source_path.display()))?;
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} parses exactly: {error}", source_path.display()))?;
    let report = run_host(source, sha256(&source_bytes))?;
    let mut encoded = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("the report encodes exactly: {error}"))?;
    encoded.push(b'\n');
    let mut output = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&output_path)
        .map_err(|error| format!("{} opens once: {error}", output_path.display()))?;
    output
        .write_all(&encoded)
        .map_err(|error| format!("{} writes completely: {error}", output_path.display()))?;
    output
        .sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output_path.display()))?;
    eprintln!(
        "eros transformer contextual hexis: {} · {} bytes · {}",
        report.status,
        encoded.len(),
        output_path.display()
    );
    Ok(())
}

fn usage() -> String {
    "usage: eros_transformer_contextual_hexis <source.json> <new-report.json>".to_owned()
}

fn run_host(source: Source, source_sha256: String) -> Result<Report, String> {
    if source.schema != SOURCE_SCHEMA {
        return Err(format!("source schema changed: {}", source.schema));
    }
    let axes: BTreeSet<u32> = source.selection.receiver_axes.iter().copied().collect();
    if axes.len() != source.selection.receiver_axes.len() || axes.is_empty() {
        return Err("receiver axes must be one nonempty exact set".to_owned());
    }
    let mut experts = Vec::new();
    for expert in &source.ecology.experts {
        let weights = parse_word_map(&expert.weights)?;
        if weights.keys().copied().collect::<BTreeSet<_>>() != axes {
            return Err(format!(
                "expert {} changed its receiver axes",
                expert.expert
            ));
        }
        let law = ExpertLaw {
            expert: expert.expert,
            weights,
        };
        let handle = ExpertHandle::new(
            &source.model.model_sha256,
            source.selection.selected_layer,
            &law,
        )?;
        experts.push(DepositedExpert { law, handle });
    }
    experts.sort_by_key(|expert| expert.law.expert);
    if experts.is_empty() {
        return Err("the inherited expert pool is empty".to_owned());
    }
    let pool: BTreeSet<u32> = experts.iter().map(|expert| expert.law.expert).collect();
    if pool.len() != experts.len() {
        return Err("the inherited expert pool repeats an identity".to_owned());
    }
    let contexts = source
        .contexts
        .iter()
        .map(|context| context_case(context, &axes, &pool))
        .collect::<Result<Vec<_>, _>>()?;
    if contexts.len() < 2 {
        return Err("varying-context conduct requires at least two contexts".to_owned());
    }

    let (deposit, no_ecology, expert_reads, deposit_exact) = deposit_experts(&experts)?;
    let source_lineages_departed = machine_from_checkpoint(&deposit)?.memory().live_lineages == 0;

    let source_read = SourceRead {
        source_observation_id: source.observation_id,
        source_sha256,
        repository: source.model.repository,
        revision: source.model.revision,
        model_sha256: source.model.model_sha256,
        layer: source.selection.selected_layer,
        receiver_axes: source.selection.receiver_axes,
        source_experts: source.ecology.source_expert_count,
        inherited_pool_experts: pool.iter().copied().collect(),
        layer_census: source.selection.layer_census,
        q1_overlap: source.ecology.q1_overlap,
    };

    // The source model, its 8,192-expert population, and its capture paths are gone from the
    // conduct call. Later current receives only the remountable body, small expert interfaces,
    // and its own activation carrier.
    let mut reads = Vec::new();
    let mut native_outputs = Vec::new();
    for (at, context) in contexts.iter().enumerate() {
        let native = probe(
            &deposit,
            &experts,
            context,
            &context.selected_experts,
            b"native-context-hexis",
        )?;
        let absent = probe(
            &no_ecology,
            &experts,
            context,
            &context.selected_experts,
            b"no-ecology-control",
        )?;
        let alternate_at = (at + 1) % contexts.len();
        let alternate_source = &contexts[alternate_at];
        let alternate = probe(
            &deposit,
            &experts,
            context,
            &alternate_source.selected_experts,
            b"alternate-context-hexis",
        )?;
        let output = native
            .output
            .as_ref()
            .ok_or_else(|| format!("{} returned no inherited hexis output", context.context))?;
        let alternate_output = alternate.output.as_ref().ok_or_else(|| {
            format!(
                "{} returned no alternate inherited hexis output",
                context.context
            )
        })?;
        let q1_output_exact = output == &context.expected_output;
        let residual = context
            .full_output
            .iter()
            .map(|(axis, full)| {
                let carried = output
                    .get(axis)
                    .ok_or_else(|| format!("context output omitted receiver axis {axis}"))?;
                Ok((*axis, full.subtract(carried)))
            })
            .collect::<Result<BTreeMap<_, _>, String>>()?;
        if residual != context.expected_residual {
            return Err(format!(
                "{} returned a residual different from the exact source census",
                context.context
            ));
        }
        let radiated_hexis_orientation = output
            .iter()
            .map(|(axis, value)| (*axis, value.orientation().to_owned()))
            .collect::<BTreeMap<_, _>>();
        let phase_orientation_exact = radiated_hexis_orientation == context.full_sign;
        let remounted = machine_from_checkpoint(&native.checkpoint)?;
        let rest_exact = remounted.rest_image().map_err(debug)? == native.checkpoint.body;
        reads.push(ContextRead {
            context: context.context.clone(),
            current_id: context.current_id.clone(),
            prompt_sha256: context.prompt_sha256.clone(),
            prompt_extent: context.prompt_extent,
            receiver_position: context.receiver_position,
            selected_experts: context.selected_experts.clone(),
            recovered_experts: native.recovered_experts,
            activations: context
                .pool_activations
                .iter()
                .filter(|(expert, _word)| context.selected_experts.contains(expert))
                .map(|(expert, word)| {
                    Ok((
                        *expert,
                        WordRead {
                            word: *word,
                            hex: format!("0x{word:04x}"),
                            exact: Dyadic::from_bfloat16(*word)?.read(),
                        },
                    ))
                })
                .collect::<Result<_, String>>()?,
            field_conducted_from_radiation: read_dyadic_map(output),
            full_transformer_face: read_dyadic_map(&context.full_output),
            residual_to_full: read_dyadic_map(&residual),
            full_orientation: context.full_sign.clone(),
            radiated_hexis_orientation,
            phase_orientation_exact,
            q1_output_exact,
            no_ecology_refused: absent.output.is_none() && absent.recovered_experts.is_empty(),
            rest_remount_exact: rest_exact,
            native_constituent: native.constituent,
            no_ecology_constituent: absent.constituent,
            alternate_hexis: AlternateHexisRead {
                selected_from_context: alternate_source.context.clone(),
                selected_experts: alternate_source.selected_experts.clone(),
                output: read_dyadic_map(alternate_output),
                differs_from_native_field: alternate_output != output,
            },
            hexis_boundaries: context.hexis_boundaries.clone(),
            benchmark: context.benchmark.clone(),
        });
        native_outputs.push(output.clone());
    }

    let conducted_field_pairs_distinct = native_outputs
        .iter()
        .enumerate()
        .flat_map(|(left, output)| {
            native_outputs
                .iter()
                .skip(left + 1)
                .map(move |right| usize::from(output != right))
        })
        .sum();
    let mut same_membership_contexts = Vec::new();
    let mut differing_membership_contexts = Vec::new();
    let mut same_membership_outputs_differ = false;
    let mut differing_membership_outputs_differ = false;
    for left in 0..contexts.len() {
        for right in left + 1..contexts.len() {
            let label = format!("{}__{}", contexts[left].context, contexts[right].context);
            if contexts[left].selected_experts == contexts[right].selected_experts {
                same_membership_contexts.push(label);
                same_membership_outputs_differ |= native_outputs[left] != native_outputs[right];
            } else {
                differing_membership_contexts.push(label);
                differing_membership_outputs_differ |=
                    native_outputs[left] != native_outputs[right];
            }
        }
    }
    let comparison = ComparisonRead {
        conducted_field_pairs_distinct,
        same_membership_contexts,
        same_membership_outputs_differ,
        differing_membership_contexts,
        differing_membership_outputs_differ,
    };
    let acceptance = AcceptanceRead {
        source_event_lineages_departed: source_lineages_departed,
        inherited_pool_became_standing: machine_from_checkpoint(&deposit)?
            .memory()
            .standing_constituents
            == experts.len(),
        source_absent_contexts_recovered_exact_selected_laws: reads
            .iter()
            .all(|read| read.selected_experts == read.recovered_experts),
        all_radiated_hexeis_conduct_to_exact_q1_field: reads
            .iter()
            .all(|read| read.q1_output_exact),
        all_no_ecology_controls_refused: reads.iter().all(|read| read.no_ecology_refused),
        all_orientation_faces_match_full_transformer_field: reads
            .iter()
            .all(|read| read.phase_orientation_exact),
        varying_context_changes_membership_or_exact_conduct: conducted_field_pairs_distinct > 0
            && comparison.differing_membership_outputs_differ,
        same_membership_still_changes_conduct: comparison.same_membership_outputs_differ,
        all_context_successors_rest_remount_exactly: reads
            .iter()
            .all(|read| read.rest_remount_exact),
        no_float_operation_in_radiation_conductor: true,
    };
    let accepted = acceptance.source_event_lineages_departed
        && acceptance.inherited_pool_became_standing
        && acceptance.source_absent_contexts_recovered_exact_selected_laws
        && acceptance.all_radiated_hexeis_conduct_to_exact_q1_field
        && acceptance.all_no_ecology_controls_refused
        && acceptance.all_orientation_faces_match_full_transformer_field
        && acceptance.varying_context_changes_membership_or_exact_conduct
        && acceptance.same_membership_still_changes_conduct
        && acceptance.all_context_successors_rest_remount_exactly;
    if !accepted {
        return Err("the inherited contextual hexis did not close every declared face".to_owned());
    }

    Ok(Report {
        schema: REPORT_SCHEMA,
        status: "accepted",
        question: "what constituent does Soma return when varying contexts recruit one inherited singleton-expert ecology, what exact field conducts from that public radiation, and which compressed hexis faces remain invariant?",
        theory_to_structure: "one trained MLP channel -> one expert law constituent; down-projection BF16 words -> oriented law bits; context product BF16 words -> current carrier; per-axis maximal exact contribution -> source-declared recruitment interface; returned constituent -> source-absent exact dyadic conduct",
        stopping_condition: "all three contexts must recover their exact selected laws only from Standing, emit their exact five-axis q1 conduct, refuse without ecology, preserve the full field orientation, differ under changing activation or membership, and remount exactly",
        source: source_read,
        deposit: DepositRead {
            machine: machine_read(&machine_from_checkpoint(&deposit)?)?,
            no_ecology_control: machine_read(&machine_from_checkpoint(&no_ecology)?)?,
            rest_remount_exact: deposit_exact,
            source_lineages_after_event: machine_from_checkpoint(&deposit)?
                .memory()
                .live_lineages,
            experts: expert_reads,
        },
        contexts: reads,
        comparison,
        acceptance,
        conclusion: "Soma returns a composed context-plus-law constituent rather than a hidden numerical payload. Five of six deposited singleton laws form each smallest orientation-preserving hexis; prose changes one member, while conversation and code retain the same membership but their activation currents make the public radiation conduct to different exact fields. Finer order and BF16 faces require much larger contextual populations.",
    })
}

fn context_case(
    source: &SourceContext,
    axes: &BTreeSet<u32>,
    pool: &BTreeSet<u32>,
) -> Result<ContextCase, String> {
    let selected: BTreeSet<u32> = source.q1_experts.iter().copied().collect();
    if selected.len() != source.q1_experts.len() || !selected.is_subset(pool) {
        return Err(format!(
            "{} carries a repeated or unavailable expert",
            source.context
        ));
    }
    let pool_activations = parse_word_map(&source.pool_activation_words)?;
    if pool_activations.keys().copied().collect::<BTreeSet<_>>() != *pool {
        return Err(format!(
            "{} changed the inherited activation pool",
            source.context
        ));
    }
    let expected_output = parse_dyadic_map(&source.q1_output)?;
    let expected_residual = parse_dyadic_map(&source.q1_residual)?;
    let full_output = parse_dyadic_map(&source.full_exact_output)?;
    let full_sign = source
        .full_sign
        .iter()
        .map(|(axis, orientation)| Ok((parse_axis(axis)?, orientation.clone())))
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    for map_axes in [
        expected_output.keys().copied().collect::<BTreeSet<_>>(),
        expected_residual.keys().copied().collect(),
        full_output.keys().copied().collect(),
        full_sign.keys().copied().collect(),
    ] {
        if map_axes != *axes {
            return Err(format!("{} changed the receiver face", source.context));
        }
    }
    Ok(ContextCase {
        context: source.context.clone(),
        current_id: source.current_id.clone(),
        prompt_sha256: source.prompt_sha256.clone(),
        prompt_extent: source.prompt_extent,
        receiver_position: source.receiver_position,
        selected_experts: selected.into_iter().collect(),
        pool_activations,
        expected_output,
        expected_residual,
        full_output,
        full_sign,
        hexis_boundaries: source.hexis_boundaries.clone(),
        benchmark: source.benchmark.clone(),
    })
}

fn deposit_experts(
    experts: &[DepositedExpert],
) -> Result<(MachineCheckpoint, MachineCheckpoint, Vec<ExpertRead>, bool), String> {
    let mut base = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let mut pairs = Vec::new();
    for _ in experts {
        pairs.push(primed_pair(&mut base)?);
    }
    let before = base.rest_image().map_err(debug)?;
    let mut inherited = LiveCurrentMachine::from_rest_image(before.clone()).map_err(debug)?;
    let mut control = LiveCurrentMachine::from_rest_image(before).map_err(debug)?;
    let encoded = experts
        .iter()
        .map(|expert| expert.law.encode())
        .collect::<Result<Vec<_>, _>>()?;
    let arc_populations = experts
        .iter()
        .zip(&pairs)
        .zip(&encoded)
        .map(|((expert, pair), bytes)| expert_seed_arcs(*pair, expert.handle, bytes))
        .collect::<Vec<_>>();
    let regional = pairs
        .iter()
        .zip(&arc_populations)
        .map(|(pair, arcs)| RegionalRelationCell::new(pair[1], arcs))
        .collect::<Vec<_>>();
    let currents = pairs
        .iter()
        .flat_map(|pair| {
            [
                CurrentEvent::ending(pair[0], relation(101).expect("fixed relation"), action()),
                CurrentEvent::ending(pair[1], relation(103).expect("fixed relation"), action()),
            ]
        })
        .collect::<Vec<_>>();
    let radiation = inherited
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    control
        .receive(ContemporaryEvent::unrelated(&currents))
        .map_err(debug)?;
    if radiation.regional().len() != experts.len() {
        return Err("every inherited expert must return one constituent".to_owned());
    }
    let reads = experts
        .iter()
        .zip(&encoded)
        .zip(radiation.regional())
        .map(|((expert, bytes), returned)| {
            let recovered = decode_expert(returned.constituent(), expert.handle.data_namespace)?;
            Ok(ExpertRead {
                expert: expert.law.expert,
                handle: expert.handle.read(expert.law.expert),
                axes: expert.law.weights.keys().copied().collect(),
                encoded_bits: bytes.len() * 8,
                returned_exact: recovered == expert.law,
                constituent: constituent_read(returned.constituent())?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    if !reads.iter().all(|read| read.returned_exact) {
        return Err("one inherited expert changed during hand-up".to_owned());
    }
    let checkpoint = MachineCheckpoint {
        body: inherited.rest_image().map_err(debug)?,
    };
    let control = MachineCheckpoint {
        body: control.rest_image().map_err(debug)?,
    };
    let remounted = machine_from_checkpoint(&checkpoint)?;
    let exact = remounted.rest_image().map_err(debug)? == checkpoint.body;
    Ok((checkpoint, control, reads, exact))
}

fn probe(
    checkpoint: &MachineCheckpoint,
    experts: &[DepositedExpert],
    context: &ContextCase,
    selection: &[u32],
    role: &[u8],
) -> Result<ProbeOutcome, String> {
    let selected: BTreeSet<u32> = selection.iter().copied().collect();
    if selected.len() != selection.len() {
        return Err("one contextual hexis repeated an expert".to_owned());
    }
    let handles = experts
        .iter()
        .filter(|expert| selected.contains(&expert.law.expert))
        .map(|expert| (expert.law.expert, expert.handle))
        .collect::<BTreeMap<_, _>>();
    if handles.len() != selected.len() {
        return Err("one contextual hexis named an unavailable expert".to_owned());
    }
    let identity = namespace(&[
        b"eros-context-carrier-v1",
        context.current_id.as_bytes(),
        context.prompt_sha256.as_bytes(),
        role,
        &selection
            .iter()
            .flat_map(|expert| expert.to_le_bytes())
            .collect::<Vec<_>>(),
    ]);
    let activations = selection
        .iter()
        .map(|expert| {
            context
                .pool_activations
                .get(expert)
                .copied()
                .map(|word| (*expert, word))
                .ok_or_else(|| format!("context omitted activation for expert {expert}"))
        })
        .collect::<Result<BTreeMap<_, _>, _>>()?;
    let carrier = ContextCarrier {
        identity,
        activations,
    };
    let context_namespace = namespace(&[
        b"eros-context-carrier-data-v1",
        &identity.to_le_bytes(),
        &carrier.encode()?,
    ]);
    let mut machine = machine_from_checkpoint(checkpoint)?;
    let pair = primed_pair(&mut machine)?;
    let arcs = context_arcs(
        pair,
        context_namespace,
        &carrier.encode()?,
        &handles,
        identity,
    );
    let currents = [
        CurrentEvent::ending(pair[0], relation(107)?, action()),
        CurrentEvent::ending(pair[1], relation(109)?, action()),
    ];
    let regional = [RegionalRelationCell::new(pair[1], &arcs)];
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    let constituent = radiation
        .regional()
        .first()
        .ok_or_else(|| "one contextual ecology must return one constituent".to_owned())?
        .constituent();
    let recovered_context = decode_context(constituent, context_namespace)?;
    if recovered_context != carrier {
        return Err("the context activation carrier changed in Soma".to_owned());
    }
    let mut recovered = Vec::new();
    for (expert, handle) in handles {
        if let Ok(law) = decode_expert(constituent, handle.data_namespace) {
            if law.expert != expert {
                return Err("one recruited expert changed identity".to_owned());
            }
            recovered.push(law);
        }
    }
    recovered.sort_by_key(|law| law.expert);
    let output = if recovered.len() == selection.len() {
        Some(conduct(&recovered, &recovered_context)?)
    } else {
        None
    };
    let checkpoint = MachineCheckpoint {
        body: machine.rest_image().map_err(debug)?,
    };
    Ok(ProbeOutcome {
        output,
        recovered_experts: recovered.iter().map(|law| law.expert).collect(),
        checkpoint,
        constituent: constituent_read(constituent)?,
    })
}

fn conduct(
    experts: &[ExpertLaw],
    context: &ContextCarrier,
) -> Result<BTreeMap<u32, Dyadic>, String> {
    let mut output = BTreeMap::new();
    for expert in experts {
        let activation = context
            .activations
            .get(&expert.expert)
            .copied()
            .ok_or_else(|| format!("context omitted expert {}", expert.expert))?;
        let activation = Dyadic::from_bfloat16(activation)?;
        for (axis, weight) in &expert.weights {
            let contribution = activation.multiply(&Dyadic::from_bfloat16(*weight)?);
            let prior = output.remove(axis).unwrap_or_else(Dyadic::zero);
            output.insert(*axis, prior.add(&contribution));
        }
    }
    Ok(output)
}

fn expert_seed_arcs(
    pair: [CurrentLineage; 2],
    handle: ExpertHandle,
    bytes: &[u8],
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, handle.data_namespace, bytes, 0);
    let slot = u32::try_from(arcs.len()).expect("bounded expert carrier");
    arcs.push(interface_arc(
        pair,
        handle.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        IncidenceHand::Against,
    ));
    arcs
}

fn context_arcs(
    pair: [CurrentLineage; 2],
    context_namespace: u64,
    context_bytes: &[u8],
    handles: &BTreeMap<u32, ExpertHandle>,
    context_identity: u64,
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, context_namespace, context_bytes, 0);
    for handle in handles.values() {
        let slot = u32::try_from(arcs.len()).expect("bounded contextual carrier");
        arcs.push(interface_arc(
            pair,
            handle.recruit_namespace,
            RECRUIT_LOCAL,
            slot,
            IncidenceHand::Against,
        ));
        let renewed = handle.renewed(context_identity);
        let slot = u32::try_from(arcs.len()).expect("bounded contextual carrier");
        arcs.push(interface_arc(
            pair,
            renewed.recruit_namespace,
            RECRUIT_LOCAL,
            slot,
            IncidenceHand::With,
        ));
    }
    arcs
}

fn bit_arcs(
    pair: [CurrentLineage; 2],
    namespace: u64,
    bytes: &[u8],
    first_slot: u32,
) -> Vec<RegionalRelationArc> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte >> bit & 1 != 0))
        .enumerate()
        .map(|(at, bit)| {
            interface_arc(
                pair,
                namespace,
                at as u64,
                first_slot + u32::try_from(at).expect("bounded bit carrier"),
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

fn decode_expert(constituent: &LiveConstituent, namespace: u64) -> Result<ExpertLaw, String> {
    ExpertLaw::decode(&decode_bytes(constituent, namespace)?)
}

fn decode_context(constituent: &LiveConstituent, namespace: u64) -> Result<ContextCarrier, String> {
    ContextCarrier::decode(&decode_bytes(constituent, namespace)?)
}

fn decode_bytes(constituent: &LiveConstituent, namespace: u64) -> Result<Vec<u8>, String> {
    let exposed: BTreeSet<u32> = constituent.exposed().iter().copied().collect();
    let mut bits = BTreeMap::new();
    for pin_at in exposed {
        let pin = constituent
            .pins()
            .get(usize::try_from(pin_at).map_err(debug)?)
            .ok_or_else(|| "an exposed pin remains in the constituent".to_owned())?;
        let Some(interface) = pin.interface() else {
            continue;
        };
        if interface.namespace() != namespace {
            continue;
        }
        let mut hand = None;
        for incidence in constituent
            .incidences()
            .iter()
            .copied()
            .filter(|incidence| incidence.pin() == pin_at)
        {
            match hand {
                None => hand = Some(incidence.hand()),
                Some(prior) if prior == incidence.hand() => {}
                Some(_) => return Err("one carried bit has mixed residual hands".to_owned()),
            }
        }
        let hand = hand.ok_or_else(|| "one carried bit has no incidence".to_owned())?;
        if bits
            .insert(interface.local(), hand == IncidenceHand::With)
            .is_some()
        {
            return Err("one carried bit position is exposed twice".to_owned());
        }
    }
    if bits.is_empty() {
        return Err(format!(
            "no carried bits exist under namespace 0x{namespace:016x}"
        ));
    }
    let extent = bits.keys().next_back().copied().expect("nonempty bits") + 1;
    if bits.len() as u64 != extent || !extent.is_multiple_of(8) {
        return Err("carried bit positions are not one complete octet sequence".to_owned());
    }
    let mut bytes = Vec::with_capacity(usize::try_from(extent / 8).map_err(debug)?);
    for octet in 0..extent / 8 {
        let mut byte = 0u8;
        for bit in 0..8 {
            if bits
                .get(&(octet * 8 + bit))
                .copied()
                .ok_or_else(|| "one carried bit position is absent".to_owned())?
            {
                byte |= 1 << bit;
            }
        }
        bytes.push(byte);
    }
    Ok(bytes)
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

fn machine_from_checkpoint(checkpoint: &MachineCheckpoint) -> Result<LiveCurrentMachine, String> {
    LiveCurrentMachine::from_rest_image(checkpoint.body.clone()).map_err(debug)
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

fn constituent_read(constituent: &LiveConstituent) -> Result<ConstituentRead, String> {
    Ok(ConstituentRead {
        grain: constituent.grain(),
        axes: constituent.axis_count(),
        cells: constituent.cells().len(),
        incidences: constituent.incidences().len(),
        pins: constituent.pins().len(),
        paths: constituent
            .boundaries()
            .iter()
            .map(|boundary| boundary.paths().len())
            .sum(),
        boundaries: constituent.boundaries().len(),
        exposed_pins: constituent.exposed().len(),
        native_sha256: words_sha256(&constituent.native_words().map_err(debug)?),
    })
}

fn parse_word_map(source: &BTreeMap<String, SourceWord>) -> Result<BTreeMap<u32, u16>, String> {
    source
        .iter()
        .map(|(axis, word)| Ok((parse_axis(axis)?, word.word)))
        .collect()
}

fn parse_dyadic_map(
    source: &BTreeMap<String, SourceDyadic>,
) -> Result<BTreeMap<u32, Dyadic>, String> {
    source
        .iter()
        .map(|(axis, value)| Ok((parse_axis(axis)?, Dyadic::from_read(value)?)))
        .collect()
}

fn parse_axis(axis: &str) -> Result<u32, String> {
    axis.parse::<u32>()
        .map_err(|error| format!("receiver axis {axis:?} parses: {error}"))
}

fn read_dyadic_map(values: &BTreeMap<u32, Dyadic>) -> BTreeMap<u32, DyadicRead> {
    values
        .iter()
        .map(|(axis, value)| (*axis, value.read()))
        .collect()
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation {value} did not fit one exact atom"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn take<'a>(bytes: &'a [u8], cursor: &mut usize, count: usize) -> Result<&'a [u8], String> {
    let end = cursor
        .checked_add(count)
        .ok_or_else(|| "carrier cursor overflowed".to_owned())?;
    let value = bytes
        .get(*cursor..end)
        .ok_or_else(|| "carrier ended before its declared extent".to_owned())?;
    *cursor = end;
    Ok(value)
}

fn read_u16(bytes: &[u8], cursor: &mut usize) -> Result<u16, String> {
    Ok(u16::from_le_bytes(
        take(bytes, cursor, 2)?.try_into().map_err(debug)?,
    ))
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, String> {
    Ok(u32::from_le_bytes(
        take(bytes, cursor, 4)?.try_into().map_err(debug)?,
    ))
}

fn read_u64(bytes: &[u8], cursor: &mut usize) -> Result<u64, String> {
    Ok(u64::from_le_bytes(
        take(bytes, cursor, 8)?.try_into().map_err(debug)?,
    ))
}

fn namespace(parts: &[&[u8]]) -> u64 {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_le_bytes());
        digest.update(part);
    }
    let bytes = digest.finalize();
    let mut value = u64::from_be_bytes(bytes[..8].try_into().expect("SHA-256 prefix"));
    if value == 0 {
        value = 1;
    }
    value
}

fn sha256(bytes: &[u8]) -> String {
    hex_digest(Sha256::digest(bytes))
}

fn words_sha256(words: &[u32]) -> String {
    let mut digest = Sha256::new();
    for word in words {
        digest.update(word.to_le_bytes());
    }
    hex_digest(digest.finalize())
}

fn hex_digest(bytes: impl IntoIterator<Item = u8>) -> String {
    let mut text = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(&mut text, "{byte:02x}").expect("hex formatting");
    }
    text
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
