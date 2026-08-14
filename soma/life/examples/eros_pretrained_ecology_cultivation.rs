use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::io::Write;
use std::path::PathBuf;

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use num_bigint::BigInt;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveCurrentRestImage, LiveMemory,
    RegionalRelationArc, RegionalRelationCell, SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_pretrained_ecology_cultivation/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_pretrained_ecology_cultivation";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
const SOURCE_SCHEMA: &str = "eros.pretrained-ecology-cultivation.source.v1";
const REPORT_SCHEMA: &str = "eros.pretrained-ecology-cultivation.report.v1";
const FACTOR_MAGIC: [u8; 4] = *b"FACT";
const CONTEXT_MAGIC: [u8; 4] = *b"CURR";
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

    fn abs(&self) -> Self {
        if self.coefficient < BigInt::from(0) {
            Self::new(-self.coefficient.clone(), self.exponent)
        } else {
            self.clone()
        }
    }

    fn compare(&self, other: &Self) -> Ordering {
        let exponent = self.exponent.min(other.exponent);
        let left = &self.coefficient
            << usize::try_from(self.exponent - exponent).expect("nonnegative dyadic shift");
        let right = &other.coefficient
            << usize::try_from(other.exponent - exponent).expect("nonnegative dyadic shift");
        left.cmp(&right)
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
struct FactorLaw {
    factor: u32,
    weights: BTreeMap<u32, u16>,
}

impl FactorLaw {
    fn encode(&self) -> Result<Vec<u8>, String> {
        let count = u16::try_from(self.weights.len())
            .map_err(|_| "one factor has too many receiver axes".to_owned())?;
        let mut bytes = Vec::with_capacity(11 + self.weights.len() * 6);
        bytes.extend(FACTOR_MAGIC);
        bytes.push(CARRIER_VERSION);
        bytes.extend(self.factor.to_le_bytes());
        bytes.extend(count.to_le_bytes());
        for (axis, word) in &self.weights {
            bytes.extend(axis.to_le_bytes());
            bytes.extend(word.to_le_bytes());
        }
        Ok(bytes)
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0;
        if take(bytes, &mut cursor, 4)? != FACTOR_MAGIC {
            return Err("factor carrier magic changed".to_owned());
        }
        if take(bytes, &mut cursor, 1)?[0] != CARRIER_VERSION {
            return Err("factor carrier version changed".to_owned());
        }
        let factor = read_u32(bytes, &mut cursor)?;
        let count = usize::from(read_u16(bytes, &mut cursor)?);
        let mut weights = BTreeMap::new();
        for _ in 0..count {
            let axis = read_u32(bytes, &mut cursor)?;
            let word = read_u16(bytes, &mut cursor)?;
            if weights.insert(axis, word).is_some() {
                return Err("factor carrier repeats one receiver axis".to_owned());
            }
        }
        if cursor != bytes.len() {
            return Err("factor carrier has trailing material".to_owned());
        }
        Ok(Self { factor, weights })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ContextCarrier {
    identity: u64,
    activations: BTreeMap<u32, u16>,
}

impl ContextCarrier {
    fn encode(&self) -> Result<Vec<u8>, String> {
        let count = u32::try_from(self.activations.len())
            .map_err(|_| "one current has too many factor activations".to_owned())?;
        let mut bytes = Vec::with_capacity(17 + self.activations.len() * 6);
        bytes.extend(CONTEXT_MAGIC);
        bytes.push(CARRIER_VERSION);
        bytes.extend(self.identity.to_le_bytes());
        bytes.extend(count.to_le_bytes());
        for (factor, word) in &self.activations {
            bytes.extend(factor.to_le_bytes());
            bytes.extend(word.to_le_bytes());
        }
        Ok(bytes)
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0;
        if take(bytes, &mut cursor, 4)? != CONTEXT_MAGIC {
            return Err("context carrier magic changed".to_owned());
        }
        if take(bytes, &mut cursor, 1)?[0] != CARRIER_VERSION {
            return Err("context carrier version changed".to_owned());
        }
        let identity = read_u64(bytes, &mut cursor)?;
        let count = usize::try_from(read_u32(bytes, &mut cursor)?).map_err(debug)?;
        let mut activations = BTreeMap::new();
        for _ in 0..count {
            let factor = read_u32(bytes, &mut cursor)?;
            let word = read_u16(bytes, &mut cursor)?;
            if activations.insert(factor, word).is_some() {
                return Err("context carrier repeats one factor".to_owned());
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
struct FactorHandle {
    data_namespace: u64,
    recruit_namespace: u64,
}

impl FactorHandle {
    fn new(model_sha256: &str, layer: u32, law: &FactorLaw) -> Result<Self, String> {
        let encoded = law.encode()?;
        Ok(Self {
            data_namespace: namespace(&[
                b"eros-pretrained-factor-data-v1",
                model_sha256.as_bytes(),
                &layer.to_le_bytes(),
                &law.factor.to_le_bytes(),
                &encoded,
            ]),
            recruit_namespace: namespace(&[
                b"eros-pretrained-factor-recruit-v1",
                model_sha256.as_bytes(),
                &layer.to_le_bytes(),
                &law.factor.to_le_bytes(),
                &encoded,
            ]),
        })
    }

    fn renewed(self, context_identity: u64) -> Self {
        Self {
            data_namespace: self.data_namespace,
            recruit_namespace: namespace(&[
                b"eros-pretrained-factor-renew-v1",
                &self.recruit_namespace.to_le_bytes(),
                &context_identity.to_le_bytes(),
            ]),
        }
    }
}

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    model: SourceModel,
    selection: SourceSelection,
    factor_weights: SourceFactorWeights,
    contexts: Vec<SourceContext>,
    source: serde_json::Value,
    environment: serde_json::Value,
}

#[derive(Deserialize)]
struct SourceModel {
    repository: String,
    revision: String,
    model_sha256: String,
}

#[derive(Deserialize)]
struct SourceSelection {
    layer: u32,
    receiver_axes: Vec<u32>,
    source_factor_count: usize,
    initial_factors: Vec<u32>,
    max_recruits_per_cultivation_current: usize,
    receiver_boundary: String,
    recruitment_law: String,
}

#[derive(Deserialize)]
struct SourceFactorWeights {
    words: Vec<Vec<u16>>,
}

#[derive(Clone, Deserialize)]
struct SourceContext {
    phase: String,
    current_id: String,
    context: String,
    condition: String,
    prompt_sha256: String,
    prompt_extent: usize,
    receiver_position: usize,
    activation_words: Vec<u16>,
    observed_output_words: Vec<u16>,
    observed_output: Vec<SourceDyadic>,
    factorized_exact_output: Vec<SourceDyadic>,
    observed_face: SourceFace,
    factorized_face: SourceFace,
    observed_and_factorized_faces_agree: bool,
}

#[derive(Clone, Deserialize)]
struct SourceDyadic {
    coefficient: String,
    power_of_two: i32,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Eq, Serialize)]
struct SourceFace {
    orientation: Vec<String>,
    signed_axis_order: Vec<u32>,
}

#[derive(Clone)]
struct Ecology {
    body: LiveCurrentRestImage,
    handles: BTreeMap<u32, FactorHandle>,
    encoded_bits: usize,
}

#[derive(Clone)]
struct EvaluationCase {
    current_id: String,
    context: String,
    condition: String,
    prompt_sha256: String,
    prompt_extent: usize,
    receiver_position: usize,
    activations: BTreeMap<u32, u16>,
    observed: Vec<Dyadic>,
    factorized: Vec<Dyadic>,
    target_face: SourceFace,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    question: &'static str,
    theory_to_structure: &'static str,
    stopping_condition: String,
    source: SourceRead,
    initial_deposit: DepositRead,
    cultivation: Vec<CurrentRead>,
    evaluation: Vec<CurrentRead>,
    no_ecology_control_refused: bool,
    final_ecology: FinalEcologyRead,
    acceptance: AcceptanceRead,
    conclusion: String,
}

#[derive(Serialize)]
struct SourceRead {
    observation_id: String,
    source_sha256: String,
    repository: String,
    revision: String,
    model_sha256: String,
    layer: u32,
    receiver_axes: Vec<u32>,
    source_factors: usize,
    initial_factors: Vec<u32>,
    receiver_boundary: String,
    recruitment_law: String,
    full_source_contexts_verified: usize,
    full_source_faces_agree: usize,
    source_testimony: serde_json::Value,
    source_environment: serde_json::Value,
}

#[derive(Clone, Serialize)]
struct DepositRead {
    factors: Vec<u32>,
    encoded_bits: usize,
    returned_exact: bool,
    source_lineages_departed: bool,
    rest_remount_exact: bool,
    standing_before: usize,
    standing_after: usize,
    machine: MachineRead,
}

#[derive(Serialize)]
struct CurrentRead {
    phase: String,
    current_id: String,
    context: String,
    condition: String,
    prompt_sha256: String,
    prompt_extent: usize,
    receiver_position: usize,
    full_source_factors: usize,
    standing_factors_before: usize,
    standing_factors_after: usize,
    initial_face: FaceRead,
    target_face: SourceFace,
    initial_residual: Vec<DyadicRead>,
    recruitment: Vec<RecruitRead>,
    source_retrievals: usize,
    source_candidate_evaluations: usize,
    recruitment_stopped_without_candidate: bool,
    deposit: Option<DepositRead>,
    final_face: FaceRead,
    final_residual: Vec<DyadicRead>,
    orientation_closed: bool,
    signed_order_closed: bool,
    complete_boundary_closed: bool,
    exact_factorized_output_closed: bool,
    exact_observed_output_closed: bool,
    source_recruitment_permitted: bool,
    source_recruitment_used: bool,
    source_absent_probe_recovered_all_standing_factors: bool,
    probe_constituent: Option<ConstituentRead>,
}

#[derive(Serialize)]
struct RecruitRead {
    ordinal: usize,
    factor: u32,
    reason: RecruitReason,
    contribution: Vec<DyadicRead>,
    face_after: FaceRead,
}

#[derive(Clone, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RecruitReason {
    Orientation {
        axis: u32,
        target: String,
    },
    SignedOrder {
        desired_axis: u32,
        displaced_axis: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct FaceRead {
    orientation: Vec<String>,
    signed_axis_order: Vec<u32>,
}

#[derive(Clone, Serialize)]
struct DyadicRead {
    coefficient: String,
    power_of_two: i32,
    exact_ratio: String,
    orientation: &'static str,
}

#[derive(Clone, Serialize)]
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

#[derive(Clone, Serialize)]
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

#[derive(Serialize)]
struct FinalEcologyRead {
    factors: Vec<u32>,
    factor_count: usize,
    active_factor_ratio: String,
    source_retrievals: usize,
    encoded_bits: usize,
    machine: MachineRead,
}

#[derive(Serialize)]
struct AcceptanceRead {
    source_factorizations_verified_exactly: bool,
    source_observed_and_factorized_faces_agree: bool,
    initial_factors_became_standing: bool,
    every_returned_source_batch_became_exact_standing: bool,
    every_source_lineage_departed: bool,
    every_assisted_prediction_equaled_source_absent_conduct: bool,
    holdouts_received_no_source_factor: bool,
    all_rest_remounts_exact: bool,
    no_float_operation_in_cultivation_or_conduct: bool,
}

struct ProbeOutcome {
    output: Option<Vec<Dyadic>>,
    recovered_factors: Vec<u32>,
    constituent: ConstituentRead,
}

struct RecruitmentPlan {
    output: Vec<Dyadic>,
    factors: Vec<u32>,
    reads: Vec<RecruitRead>,
    candidate_evaluations: usize,
    stopped_without_candidate: bool,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros pretrained ecology cultivation: {error}");
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
    if output_path.exists() {
        return Err(format!(
            "create-once report already exists: {}",
            output_path.display()
        ));
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads completely: {error}", source_path.display()))?;
    let source_sha256 = sha256(&source_bytes);
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} parses exactly: {error}", source_path.display()))?;
    let report = run_host(source, source_sha256)?;
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
        "eros pretrained ecology cultivation: {} · {} bytes · {}",
        report.status,
        encoded.len(),
        output_path.display()
    );
    Ok(())
}

fn usage() -> String {
    "usage: eros_pretrained_ecology_cultivation <source.json> <new-report.json>".to_owned()
}

fn run_host(source: Source, source_sha256: String) -> Result<Report, String> {
    validate_source(&source)?;
    let axes = source.selection.receiver_axes.clone();
    let all_factorized = source
        .contexts
        .iter()
        .map(|context| verify_full_source(&source, context))
        .collect::<Result<Vec<_>, _>>()?;
    let full_faces_agree = source
        .contexts
        .iter()
        .filter(|context| context.observed_and_factorized_faces_agree)
        .count();

    let mut initial_laws = Vec::new();
    for factor in &source.selection.initial_factors {
        initial_laws.push(source_factor(&source, *factor)?);
    }
    let empty = empty_ecology()?;
    let (mut ecology, initial_deposit) = deposit_batch(
        empty,
        &source.model.model_sha256,
        source.selection.layer,
        &initial_laws,
    )?;
    let initial_exact = initial_deposit.returned_exact
        && initial_deposit.source_lineages_departed
        && initial_deposit.rest_remount_exact;

    let cultivation_contexts = source
        .contexts
        .iter()
        .filter(|context| context.phase == "cultivation")
        .cloned()
        .collect::<Vec<_>>();
    let evaluation_contexts = source
        .contexts
        .iter()
        .filter(|context| context.phase == "evaluation")
        .cloned()
        .collect::<Vec<_>>();
    if cultivation_contexts.len() != 9 || evaluation_contexts.len() != 3 {
        return Err("the source changed the fixed nine-plus-three passage".to_owned());
    }

    let mut cultivation_reads = Vec::new();
    let mut every_batch_exact = true;
    let mut every_lineage_departed = true;
    let mut every_prediction_exact = true;
    let mut every_rest_exact = initial_deposit.rest_remount_exact;
    let mut total_retrievals = 0;
    for context in &cultivation_contexts {
        let standing_before = ecology.handles.len();
        let input = context_input(context, ecology.handles.keys().copied())?;
        let initial_probe = probe(&ecology, &input)?;
        let initial_output = initial_probe
            .output
            .clone()
            .ok_or_else(|| "the inherited ecology returned no initial conduct".to_owned())?;
        if initial_probe.recovered_factors.len() != standing_before {
            return Err(format!(
                "{} did not recover every standing factor",
                context.current_id
            ));
        }
        let plan = plan_recruitment(
            &source,
            context,
            &ecology.handles.keys().copied().collect(),
            &initial_output,
        )?;
        let laws = plan
            .factors
            .iter()
            .map(|factor| source_factor(&source, *factor))
            .collect::<Result<Vec<_>, _>>()?;
        let deposit = if laws.is_empty() {
            None
        } else {
            let (next, read) = deposit_batch(
                ecology,
                &source.model.model_sha256,
                source.selection.layer,
                &laws,
            )?;
            every_batch_exact &= read.returned_exact;
            every_lineage_departed &= read.source_lineages_departed;
            every_rest_exact &= read.rest_remount_exact;
            ecology = next;
            Some(read)
        };
        total_retrievals += plan.factors.len();
        let final_input = context_input(context, ecology.handles.keys().copied())?;
        let final_probe = probe(&ecology, &final_input)?;
        let final_output = final_probe
            .output
            .clone()
            .ok_or_else(|| "the assisted ecology returned no final conduct".to_owned())?;
        every_prediction_exact &= final_output == plan.output;
        cultivation_reads.push(current_read(
            &source,
            context,
            standing_before,
            &initial_output,
            &initial_probe,
            plan,
            deposit,
            &final_output,
            &final_probe,
            true,
        )?);
    }

    let evaluation_cases = evaluation_contexts
        .iter()
        .map(|context| evaluation_case(context, ecology.handles.keys().copied()))
        .collect::<Result<Vec<_>, _>>()?;
    let source_read = SourceRead {
        observation_id: source.observation_id.clone(),
        source_sha256,
        repository: source.model.repository.clone(),
        revision: source.model.revision.clone(),
        model_sha256: source.model.model_sha256.clone(),
        layer: source.selection.layer,
        receiver_axes: axes.clone(),
        source_factors: source.selection.source_factor_count,
        initial_factors: source.selection.initial_factors.clone(),
        receiver_boundary: source.selection.receiver_boundary.clone(),
        recruitment_law: source.selection.recruitment_law.clone(),
        full_source_contexts_verified: all_factorized.len(),
        full_source_faces_agree: full_faces_agree,
        source_testimony: source.source.clone(),
        source_environment: source.environment.clone(),
    };
    let source_factor_count = source.selection.source_factor_count;
    let stopping_condition = format!(
        "one fixed pass; at most {} source factors per cultivation current; zero source factors on three operation-order holdouts",
        source.selection.max_recruits_per_cultivation_current
    );
    drop(source);

    let mut control_input = evaluation_cases
        .first()
        .ok_or_else(|| "one source-absent evaluation current remains".to_owned())?
        .clone();
    control_input.activations.clear();
    let control = probe(&empty_ecology()?, &control_input)?;
    let no_ecology_control_refused =
        control.output.is_none() && control.recovered_factors.is_empty();

    let mut evaluation_reads = Vec::new();
    for case in &evaluation_cases {
        let outcome = probe(&ecology, case)?;
        let output = outcome
            .output
            .clone()
            .ok_or_else(|| "one source-absent holdout returned no conduct".to_owned())?;
        let plan = RecruitmentPlan {
            output: output.clone(),
            factors: Vec::new(),
            reads: Vec::new(),
            candidate_evaluations: 0,
            stopped_without_candidate: false,
        };
        evaluation_reads.push(current_read_case(
            source_factor_count,
            &axes,
            case,
            ecology.handles.len(),
            &output,
            &outcome,
            plan,
        ));
    }

    let final_machine = machine_read(&machine_from_ecology(&ecology)?)?;
    let final_factors = ecology.handles.keys().copied().collect::<Vec<_>>();
    let holdouts_no_source = evaluation_reads
        .iter()
        .all(|read| !read.source_recruitment_permitted && read.source_retrievals == 0);
    let all_rest_exact = every_rest_exact
        && machine_from_ecology(&ecology)?
            .rest_image()
            .map_err(debug)?
            == ecology.body;
    let acceptance = AcceptanceRead {
        source_factorizations_verified_exactly: all_factorized.len() == 12,
        source_observed_and_factorized_faces_agree: full_faces_agree == 12,
        initial_factors_became_standing: initial_exact
            && initial_deposit.standing_after == source_read.initial_factors.len(),
        every_returned_source_batch_became_exact_standing: every_batch_exact,
        every_source_lineage_departed: every_lineage_departed,
        every_assisted_prediction_equaled_source_absent_conduct: every_prediction_exact,
        holdouts_received_no_source_factor: holdouts_no_source,
        all_rest_remounts_exact: all_rest_exact,
        no_float_operation_in_cultivation_or_conduct: true,
    };
    let accepted = acceptance.source_factorizations_verified_exactly
        && acceptance.initial_factors_became_standing
        && acceptance.every_returned_source_batch_became_exact_standing
        && acceptance.every_source_lineage_departed
        && acceptance.every_assisted_prediction_equaled_source_absent_conduct
        && acceptance.holdouts_received_no_source_factor
        && acceptance.all_rest_remounts_exact
        && no_ecology_control_refused;
    if !accepted {
        return Err("the fixed cultivation mechanics did not close".to_owned());
    }
    let cultivation_closed = cultivation_reads
        .iter()
        .filter(|read| read.complete_boundary_closed)
        .count();
    let evaluation_closed = evaluation_reads
        .iter()
        .filter(|read| read.complete_boundary_closed)
        .count();
    Ok(Report {
        schema: REPORT_SCHEMA,
        status: "accepted",
        question: "can a pretrained fixed-basis ecology supply only locally recruited constituents during cultivation, then leave those constituents to conduct changed-operation holdouts without further source retrieval?",
        theory_to_structure: "one source factor column on five declared receiver axes -> one cellular Standing constituent; one context activation population -> one transient current branch; OPEN receiver face -> one bounded co-present source return; frozen holdout -> source-absent conduct only",
        stopping_condition,
        source: source_read,
        initial_deposit,
        cultivation: cultivation_reads,
        evaluation: evaluation_reads,
        no_ecology_control_refused,
        final_ecology: FinalEcologyRead {
            factors: final_factors.clone(),
            factor_count: final_factors.len(),
            active_factor_ratio: format!("{}/{}", final_factors.len(), source_factor_count),
            source_retrievals: total_retrievals,
            encoded_bits: ecology.encoded_bits,
            machine: final_machine,
        },
        acceptance,
        conclusion: format!(
            "the one-pass ecology admitted {total_retrievals} source factors beyond its six inherited factors; {cultivation_closed}/9 cultivation currents and {evaluation_closed}/3 source-absent changed-operation holdouts closed the complete declared receiver face. This grades local cultivation and transfer only; it does not establish a portable skill, architectural compression, or reduced physical cost."
        ),
    })
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA {
        return Err(format!("source schema changed: {}", source.schema));
    }
    let axes: BTreeSet<_> = source.selection.receiver_axes.iter().copied().collect();
    if axes.len() != source.selection.receiver_axes.len() || axes.is_empty() {
        return Err("receiver axes must be one nonempty set".to_owned());
    }
    if source.factor_weights.words.len() != axes.len()
        || source
            .factor_weights
            .words
            .iter()
            .any(|row| row.len() != source.selection.source_factor_count)
    {
        return Err("source factor-weight extent changed".to_owned());
    }
    let initial: BTreeSet<_> = source.selection.initial_factors.iter().copied().collect();
    if initial.len() != source.selection.initial_factors.len()
        || initial.iter().any(|factor| {
            usize::try_from(*factor).map_or(true, |at| at >= source.selection.source_factor_count)
        })
    {
        return Err("initial factor population is repeated or out of range".to_owned());
    }
    for context in &source.contexts {
        if context.activation_words.len() != source.selection.source_factor_count
            || context.observed_output_words.len() != axes.len()
            || context.observed_output.len() != axes.len()
            || context.factorized_exact_output.len() != axes.len()
            || context.observed_face.orientation.len() != axes.len()
            || context.factorized_face.orientation.len() != axes.len()
        {
            return Err(format!("{} changed one source extent", context.current_id));
        }
    }
    Ok(())
}

fn verify_full_source(source: &Source, context: &SourceContext) -> Result<Vec<Dyadic>, String> {
    let factors = (0..source.selection.source_factor_count)
        .map(|factor| u32::try_from(factor).map_err(debug))
        .collect::<Result<BTreeSet<_>, _>>()?;
    let output = conduct_source(source, context, &factors)?;
    let declared = context
        .factorized_exact_output
        .iter()
        .map(Dyadic::from_read)
        .collect::<Result<Vec<_>, _>>()?;
    if output != declared {
        return Err(format!("{} full factorization changed", context.current_id));
    }
    let observed = observed_values(context)?;
    let declared_observed = context
        .observed_output
        .iter()
        .map(Dyadic::from_read)
        .collect::<Result<Vec<_>, _>>()?;
    if observed != declared_observed {
        return Err(format!("{} observed output changed", context.current_id));
    }
    let observed_face = face_of(&source.selection.receiver_axes, &observed);
    let factorized_face = face_of(&source.selection.receiver_axes, &output);
    if observed_face != face_read(&context.observed_face)
        || factorized_face != face_read(&context.factorized_face)
        || context.observed_and_factorized_faces_agree != (observed_face == factorized_face)
    {
        return Err(format!("{} source face changed", context.current_id));
    }
    Ok(output)
}

fn source_factor(source: &Source, factor: u32) -> Result<FactorLaw, String> {
    let at = usize::try_from(factor).map_err(debug)?;
    if at >= source.selection.source_factor_count {
        return Err(format!("source factor {factor} is out of range"));
    }
    let weights = source
        .selection
        .receiver_axes
        .iter()
        .copied()
        .zip(&source.factor_weights.words)
        .map(|(axis, row)| (axis, row[at]))
        .collect();
    Ok(FactorLaw { factor, weights })
}

fn observed_values(context: &SourceContext) -> Result<Vec<Dyadic>, String> {
    context
        .observed_output_words
        .iter()
        .copied()
        .map(Dyadic::from_bfloat16)
        .collect()
}

fn context_input(
    context: &SourceContext,
    factors: impl Iterator<Item = u32>,
) -> Result<EvaluationCase, String> {
    let mut activations = BTreeMap::new();
    for factor in factors {
        let at = usize::try_from(factor).map_err(debug)?;
        let word = context
            .activation_words
            .get(at)
            .copied()
            .ok_or_else(|| format!("{} omitted factor {factor}", context.current_id))?;
        activations.insert(factor, word);
    }
    Ok(EvaluationCase {
        current_id: context.current_id.clone(),
        context: context.context.clone(),
        condition: context.condition.clone(),
        prompt_sha256: context.prompt_sha256.clone(),
        prompt_extent: context.prompt_extent,
        receiver_position: context.receiver_position,
        activations,
        observed: observed_values(context)?,
        factorized: context
            .factorized_exact_output
            .iter()
            .map(Dyadic::from_read)
            .collect::<Result<Vec<_>, _>>()?,
        target_face: context.observed_face.clone(),
    })
}

fn evaluation_case(
    context: &SourceContext,
    factors: impl Iterator<Item = u32>,
) -> Result<EvaluationCase, String> {
    context_input(context, factors)
}

fn conduct_source(
    source: &Source,
    context: &SourceContext,
    factors: &BTreeSet<u32>,
) -> Result<Vec<Dyadic>, String> {
    let mut output = vec![Dyadic::zero(); source.selection.receiver_axes.len()];
    for factor in factors {
        let contribution = source_contribution(source, context, *factor)?;
        add_vector(&mut output, &contribution)?;
    }
    Ok(output)
}

fn source_contribution(
    source: &Source,
    context: &SourceContext,
    factor: u32,
) -> Result<Vec<Dyadic>, String> {
    let at = usize::try_from(factor).map_err(debug)?;
    let activation = Dyadic::from_bfloat16(
        *context
            .activation_words
            .get(at)
            .ok_or_else(|| format!("{} omitted factor {factor}", context.current_id))?,
    )?;
    source
        .factor_weights
        .words
        .iter()
        .map(|row| {
            let weight = Dyadic::from_bfloat16(row[at])?;
            Ok(activation.multiply(&weight))
        })
        .collect()
}

fn plan_recruitment(
    source: &Source,
    context: &SourceContext,
    standing: &BTreeSet<u32>,
    initial_output: &[Dyadic],
) -> Result<RecruitmentPlan, String> {
    let axes = &source.selection.receiver_axes;
    let target = &context.observed_face;
    let mut selected = standing.clone();
    let mut output = initial_output.to_vec();
    let mut factors = Vec::new();
    let mut reads = Vec::new();
    let mut candidate_evaluations = 0;
    let mut stopped_without_candidate = false;
    for ordinal in 1..=source.selection.max_recruits_per_cultivation_current {
        let current_face = face_of(axes, &output);
        if current_face == face_read(target) {
            break;
        }
        let issue = first_issue(axes, &current_face, target)?;
        let Some((factor, contribution, scanned)) =
            choose_candidate(source, context, &selected, &issue)?
        else {
            stopped_without_candidate = true;
            break;
        };
        candidate_evaluations += scanned;
        selected.insert(factor);
        factors.push(factor);
        add_vector(&mut output, &contribution)?;
        reads.push(RecruitRead {
            ordinal,
            factor,
            reason: issue,
            contribution: contribution.iter().map(Dyadic::read).collect(),
            face_after: face_of(axes, &output),
        });
    }
    Ok(RecruitmentPlan {
        output,
        factors,
        reads,
        candidate_evaluations,
        stopped_without_candidate,
    })
}

fn first_issue(
    axes: &[u32],
    current: &FaceRead,
    target: &SourceFace,
) -> Result<RecruitReason, String> {
    for (at, axis) in axes.iter().copied().enumerate() {
        if current.orientation[at] != target.orientation[at] {
            return Ok(RecruitReason::Orientation {
                axis,
                target: target.orientation[at].clone(),
            });
        }
    }
    let mismatch = current
        .signed_axis_order
        .iter()
        .zip(&target.signed_axis_order)
        .position(|(current, target)| current != target)
        .ok_or_else(|| "a closed face has no recruitment issue".to_owned())?;
    Ok(RecruitReason::SignedOrder {
        desired_axis: target.signed_axis_order[mismatch],
        displaced_axis: current.signed_axis_order[mismatch],
    })
}

fn choose_candidate(
    source: &Source,
    context: &SourceContext,
    selected: &BTreeSet<u32>,
    issue: &RecruitReason,
) -> Result<Option<(u32, Vec<Dyadic>, usize)>, String> {
    let mut best: Option<(u32, Vec<Dyadic>, Dyadic)> = None;
    let mut scanned = 0;
    for at in 0..source.selection.source_factor_count {
        let factor = u32::try_from(at).map_err(debug)?;
        if selected.contains(&factor) {
            continue;
        }
        scanned += 1;
        let contribution = source_contribution(source, context, factor)?;
        let score = match issue {
            RecruitReason::Orientation { axis, target } => {
                let axis_at = axis_position(&source.selection.receiver_axes, *axis)?;
                if contribution[axis_at].orientation() != target {
                    continue;
                }
                contribution[axis_at].abs()
            }
            RecruitReason::SignedOrder {
                desired_axis,
                displaced_axis,
            } => {
                let desired = axis_position(&source.selection.receiver_axes, *desired_axis)?;
                let displaced = axis_position(&source.selection.receiver_axes, *displaced_axis)?;
                let difference = contribution[desired].subtract(&contribution[displaced]);
                if difference.coefficient <= BigInt::from(0) {
                    continue;
                }
                difference
            }
        };
        let replace = match &best {
            None => true,
            Some((best_factor, _best_contribution, best_score)) => {
                score.compare(best_score) == Ordering::Greater
                    || (score.compare(best_score) == Ordering::Equal && factor < *best_factor)
            }
        };
        if replace {
            best = Some((factor, contribution, score));
        }
    }
    Ok(best.map(|(factor, contribution, _score)| (factor, contribution, scanned)))
}

fn axis_position(axes: &[u32], axis: u32) -> Result<usize, String> {
    axes.iter()
        .position(|candidate| *candidate == axis)
        .ok_or_else(|| format!("receiver axis {axis} is absent"))
}

fn add_vector(left: &mut [Dyadic], right: &[Dyadic]) -> Result<(), String> {
    if left.len() != right.len() {
        return Err("dyadic vector extents differ".to_owned());
    }
    for (left, right) in left.iter_mut().zip(right) {
        *left = left.add(right);
    }
    Ok(())
}

fn face_of(axes: &[u32], output: &[Dyadic]) -> FaceRead {
    let mut order = (0..axes.len()).collect::<Vec<_>>();
    order.sort_by(|left, right| {
        output[*right]
            .compare(&output[*left])
            .then_with(|| axes[*left].cmp(&axes[*right]))
    });
    FaceRead {
        orientation: output
            .iter()
            .map(|value| value.orientation().to_owned())
            .collect(),
        signed_axis_order: order.into_iter().map(|at| axes[at]).collect(),
    }
}

fn face_read(source: &SourceFace) -> FaceRead {
    FaceRead {
        orientation: source.orientation.clone(),
        signed_axis_order: source.signed_axis_order.clone(),
    }
}

fn residual(target: &[Dyadic], actual: &[Dyadic]) -> Vec<DyadicRead> {
    target
        .iter()
        .zip(actual)
        .map(|(target, actual)| target.subtract(actual).read())
        .collect()
}

fn current_read(
    source: &Source,
    context: &SourceContext,
    standing_before: usize,
    initial_output: &[Dyadic],
    initial_probe: &ProbeOutcome,
    plan: RecruitmentPlan,
    deposit: Option<DepositRead>,
    final_output: &[Dyadic],
    final_probe: &ProbeOutcome,
    recruitment_permitted: bool,
) -> Result<CurrentRead, String> {
    let observed = observed_values(context)?;
    let factorized = context
        .factorized_exact_output
        .iter()
        .map(Dyadic::from_read)
        .collect::<Result<Vec<_>, _>>()?;
    let initial_face = face_of(&source.selection.receiver_axes, initial_output);
    let final_face = face_of(&source.selection.receiver_axes, final_output);
    let target_face = face_read(&context.observed_face);
    Ok(CurrentRead {
        phase: context.phase.clone(),
        current_id: context.current_id.clone(),
        context: context.context.clone(),
        condition: context.condition.clone(),
        prompt_sha256: context.prompt_sha256.clone(),
        prompt_extent: context.prompt_extent,
        receiver_position: context.receiver_position,
        full_source_factors: source.selection.source_factor_count,
        standing_factors_before: standing_before,
        standing_factors_after: final_probe.recovered_factors.len(),
        initial_face: initial_face.clone(),
        target_face: context.observed_face.clone(),
        initial_residual: residual(&observed, initial_output),
        recruitment: plan.reads,
        source_retrievals: plan.factors.len(),
        source_candidate_evaluations: plan.candidate_evaluations,
        recruitment_stopped_without_candidate: plan.stopped_without_candidate,
        deposit,
        final_face: final_face.clone(),
        final_residual: residual(&observed, final_output),
        orientation_closed: final_face.orientation == target_face.orientation,
        signed_order_closed: final_face.signed_axis_order == target_face.signed_axis_order,
        complete_boundary_closed: final_face == target_face,
        exact_factorized_output_closed: final_output == factorized,
        exact_observed_output_closed: final_output == observed,
        source_recruitment_permitted: recruitment_permitted,
        source_recruitment_used: !plan.factors.is_empty(),
        source_absent_probe_recovered_all_standing_factors: initial_probe.recovered_factors.len()
            == standing_before
            && final_probe.recovered_factors.len() >= standing_before,
        probe_constituent: Some(final_probe.constituent.clone()),
    })
}

fn current_read_case(
    source_factor_count: usize,
    axes: &[u32],
    case: &EvaluationCase,
    standing: usize,
    output: &[Dyadic],
    probe: &ProbeOutcome,
    plan: RecruitmentPlan,
) -> CurrentRead {
    let final_face = face_of(axes, output);
    let target_face = face_read(&case.target_face);
    CurrentRead {
        phase: "evaluation".to_owned(),
        current_id: case.current_id.clone(),
        context: case.context.clone(),
        condition: case.condition.clone(),
        prompt_sha256: case.prompt_sha256.clone(),
        prompt_extent: case.prompt_extent,
        receiver_position: case.receiver_position,
        full_source_factors: source_factor_count,
        standing_factors_before: standing,
        standing_factors_after: standing,
        initial_face: final_face.clone(),
        target_face: case.target_face.clone(),
        initial_residual: residual(&case.observed, output),
        recruitment: plan.reads,
        source_retrievals: 0,
        source_candidate_evaluations: 0,
        recruitment_stopped_without_candidate: false,
        deposit: None,
        final_face: final_face.clone(),
        final_residual: residual(&case.observed, output),
        orientation_closed: final_face.orientation == target_face.orientation,
        signed_order_closed: final_face.signed_axis_order == target_face.signed_axis_order,
        complete_boundary_closed: final_face == target_face,
        exact_factorized_output_closed: output == case.factorized,
        exact_observed_output_closed: output == case.observed,
        source_recruitment_permitted: false,
        source_recruitment_used: false,
        source_absent_probe_recovered_all_standing_factors: probe.recovered_factors.len()
            == standing,
        probe_constituent: Some(probe.constituent.clone()),
    }
}

fn empty_ecology() -> Result<Ecology, String> {
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let pair = prime_pairs(&mut machine, 1)?
        .into_iter()
        .next()
        .ok_or_else(|| "one control pair remains".to_owned())?;
    let currents = [
        CurrentEvent::ending(pair[0], relation(97)?, action()),
        CurrentEvent::ending(pair[1], relation(101)?, action()),
    ];
    machine
        .receive(ContemporaryEvent::unrelated(&currents))
        .map_err(debug)?;
    Ok(Ecology {
        body: machine.rest_image().map_err(debug)?,
        handles: BTreeMap::new(),
        encoded_bits: 0,
    })
}

fn deposit_batch(
    ecology: Ecology,
    model_sha256: &str,
    layer: u32,
    laws: &[FactorLaw],
) -> Result<(Ecology, DepositRead), String> {
    if laws.is_empty() {
        return Err("one source return must contain material".to_owned());
    }
    let mut machine = machine_from_ecology(&ecology)?;
    let standing_before = machine.memory().standing_constituents;
    let pairs = prime_pairs(&mut machine, laws.len())?;
    let encoded = laws
        .iter()
        .map(FactorLaw::encode)
        .collect::<Result<Vec<_>, _>>()?;
    let handles = laws
        .iter()
        .map(|law| FactorHandle::new(model_sha256, layer, law))
        .collect::<Result<Vec<_>, _>>()?;
    let arc_populations = pairs
        .iter()
        .zip(&handles)
        .zip(&encoded)
        .map(|((pair, handle), bytes)| factor_seed_arcs(*pair, *handle, bytes))
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
                CurrentEvent::ending(pair[0], relation(103).expect("fixed relation"), action()),
                CurrentEvent::ending(pair[1], relation(107).expect("fixed relation"), action()),
            ]
        })
        .collect::<Vec<_>>();
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    if radiation.regional().len() != laws.len() {
        return Err("every returned source factor must emit one constituent".to_owned());
    }
    let returned_exact = laws
        .iter()
        .zip(&handles)
        .zip(radiation.regional())
        .map(|((law, handle), returned)| {
            decode_factor(returned.constituent(), handle.data_namespace)
                .map(|recovered| recovered == *law)
        })
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .all(|exact| exact);
    let mut next_handles = ecology.handles;
    for (law, handle) in laws.iter().zip(&handles) {
        if next_handles.insert(law.factor, *handle).is_some() {
            return Err(format!("factor {} was already Standing", law.factor));
        }
    }
    let body = machine.rest_image().map_err(debug)?;
    let next = Ecology {
        body,
        handles: next_handles,
        encoded_bits: ecology.encoded_bits
            + encoded.iter().map(|bytes| bytes.len() * 8).sum::<usize>(),
    };
    let remounted = machine_from_ecology(&next)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == next.body;
    let memory = remounted.memory();
    let read = DepositRead {
        factors: laws.iter().map(|law| law.factor).collect(),
        encoded_bits: encoded.iter().map(|bytes| bytes.len() * 8).sum(),
        returned_exact,
        source_lineages_departed: memory.live_lineages == 0,
        rest_remount_exact: rest_exact,
        standing_before,
        standing_after: memory.standing_constituents,
        machine: machine_read(&remounted)?,
    };
    Ok((next, read))
}

fn probe(ecology: &Ecology, case: &EvaluationCase) -> Result<ProbeOutcome, String> {
    if case.activations.keys().copied().collect::<BTreeSet<_>>()
        != ecology.handles.keys().copied().collect::<BTreeSet<_>>()
    {
        return Err(format!(
            "{} activation population differs from Standing",
            case.current_id
        ));
    }
    let identity = namespace(&[
        b"eros-pretrained-current-v1",
        case.current_id.as_bytes(),
        case.prompt_sha256.as_bytes(),
        &ecology
            .handles
            .keys()
            .flat_map(|factor| factor.to_le_bytes())
            .collect::<Vec<_>>(),
    ]);
    let carrier = ContextCarrier {
        identity,
        activations: case.activations.clone(),
    };
    let carrier_bytes = carrier.encode()?;
    let context_namespace = namespace(&[
        b"eros-pretrained-current-data-v1",
        &identity.to_le_bytes(),
        &carrier_bytes,
    ]);
    let mut machine = machine_from_ecology(ecology)?;
    let pair = prime_pairs(&mut machine, 1)?
        .into_iter()
        .next()
        .ok_or_else(|| "one probe pair remains".to_owned())?;
    let arcs = context_arcs(
        pair,
        context_namespace,
        &carrier_bytes,
        &ecology.handles,
        identity,
    );
    let currents = [
        CurrentEvent::ending(pair[0], relation(109)?, action()),
        CurrentEvent::ending(pair[1], relation(113)?, action()),
    ];
    let regional = [RegionalRelationCell::new(pair[1], &arcs)];
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    let constituent = radiation
        .regional()
        .first()
        .ok_or_else(|| "one transient current must return one constituent".to_owned())?
        .constituent();
    let recovered_context = decode_context(constituent, context_namespace)?;
    if recovered_context != carrier {
        return Err("the transient current carrier changed in Soma".to_owned());
    }
    let mut recovered = Vec::new();
    for (factor, handle) in &ecology.handles {
        let law = decode_factor(constituent, handle.data_namespace)?;
        if law.factor != *factor {
            return Err("one Standing factor changed identity".to_owned());
        }
        recovered.push(law);
    }
    recovered.sort_by_key(|law| law.factor);
    let output = if recovered.is_empty() {
        None
    } else {
        Some(conduct_recovered(&recovered, &recovered_context)?)
    };
    Ok(ProbeOutcome {
        output,
        recovered_factors: recovered.iter().map(|law| law.factor).collect(),
        constituent: constituent_read(constituent)?,
    })
}

fn conduct_recovered(laws: &[FactorLaw], context: &ContextCarrier) -> Result<Vec<Dyadic>, String> {
    let axes = laws
        .first()
        .ok_or_else(|| "one factor law remains".to_owned())?
        .weights
        .keys()
        .copied()
        .collect::<Vec<_>>();
    let mut output = vec![Dyadic::zero(); axes.len()];
    for law in laws {
        if law.weights.keys().copied().collect::<Vec<_>>() != axes {
            return Err("Standing factors changed receiver axes".to_owned());
        }
        let activation = Dyadic::from_bfloat16(
            *context
                .activations
                .get(&law.factor)
                .ok_or_else(|| format!("current omitted factor {}", law.factor))?,
        )?;
        for (at, word) in law.weights.values().copied().enumerate() {
            let contribution = activation.multiply(&Dyadic::from_bfloat16(word)?);
            output[at] = output[at].add(&contribution);
        }
    }
    Ok(output)
}

fn prime_pairs(
    machine: &mut LiveCurrentMachine,
    count: usize,
) -> Result<Vec<[CurrentLineage; 2]>, String> {
    let first = relation(PRIMING_VALUES[0])?;
    let mut pairs = Vec::with_capacity(count);
    for _ in 0..count {
        pairs.push([
            machine
                .attach(CurrentGeometry::Cell(first))
                .map_err(debug)?,
            machine
                .attach(CurrentGeometry::Cell(first))
                .map_err(debug)?,
        ]);
    }
    for value in PRIMING_VALUES {
        let currents = pairs
            .iter()
            .flat_map(|pair| {
                [
                    CurrentEvent::continuing(
                        pair[0],
                        relation(value).expect("fixed relation"),
                        action(),
                    ),
                    CurrentEvent::continuing(
                        pair[1],
                        relation(value).expect("fixed relation"),
                        action(),
                    ),
                ]
            })
            .collect::<Vec<_>>();
        machine
            .receive(ContemporaryEvent::unrelated(&currents))
            .map_err(debug)?;
    }
    Ok(pairs)
}

fn factor_seed_arcs(
    pair: [CurrentLineage; 2],
    handle: FactorHandle,
    bytes: &[u8],
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, handle.data_namespace, bytes, 0);
    let slot = u32::try_from(arcs.len()).expect("bounded factor carrier");
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
    handles: &BTreeMap<u32, FactorHandle>,
    context_identity: u64,
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, context_namespace, context_bytes, 0);
    for handle in handles.values() {
        let slot = u32::try_from(arcs.len()).expect("bounded context carrier");
        arcs.push(interface_arc(
            pair,
            handle.recruit_namespace,
            RECRUIT_LOCAL,
            slot,
            IncidenceHand::Against,
        ));
        let renewed = handle.renewed(context_identity);
        let slot = u32::try_from(arcs.len()).expect("bounded context carrier");
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

fn decode_factor(constituent: &LiveConstituent, namespace: u64) -> Result<FactorLaw, String> {
    FactorLaw::decode(&decode_bytes(constituent, namespace)?)
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

fn machine_from_ecology(ecology: &Ecology) -> Result<LiveCurrentMachine, String> {
    LiveCurrentMachine::from_rest_image(ecology.body.clone()).map_err(debug)
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

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation value {value} remains nonzero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn take<'a>(bytes: &'a [u8], cursor: &mut usize, count: usize) -> Result<&'a [u8], String> {
    let end = cursor
        .checked_add(count)
        .ok_or_else(|| "carrier cursor overflowed".to_owned())?;
    let slice = bytes
        .get(*cursor..end)
        .ok_or_else(|| "carrier ended before its declared extent".to_owned())?;
    *cursor = end;
    Ok(slice)
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
        digest.update(part);
        digest.update([0]);
    }
    u64::from_le_bytes(
        digest.finalize()[..8]
            .try_into()
            .expect("SHA-256 has eight bytes"),
    )
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
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut result = String::new();
    for byte in bytes {
        result.push(HEX[(byte >> 4) as usize] as char);
        result.push(HEX[(byte & 15) as usize] as char);
    }
    result
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
