use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use body::incidence::IncidenceHand;
use body::num::Cog;
use life::form_mouth::deposit_form_or_message;
use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    ContemporaryEvent, CurrentBoundaryPort, CurrentEvent, CurrentGeometry, CurrentLineage,
    InterfaceCapability, LiveConstituent, LiveCurrentMachine, LiveMemory,
    ParallelCpuLiveCurrentExecutor, RegionalRelationArc, RegionalRelationCell,
    SparseStandingSurface,
};

/// This driver's name at the plate mouth: `output/eros_parent_on_open_substitution/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_parent_on_open_substitution";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";

const SOURCE_SCHEMA: &str = "eros.parent-on-open-substitution.source.v1";
const REPORT_SCHEMA: &str = "eros.parent-on-open-substitution.report.v1";
const OBSERVATION_ID: &str = "eros-parent-on-open-substitution-01";
const COMPACT_SCHEMA: u64 = 1;
const RECRUIT_LOCAL: u64 = 0;
// The fixed source's largest replacement carries 675 departing ecology words,
// 56 current words, 52 residual words, 735 successor words, and three
// interfaces: 1,521 regional arcs. 2,048 is the smallest power-of-two aperture
// that contains that complete event without splitting it into false instants.
const MAX_ARCS_PER_EVENT: usize = 2048;
const EVENT_LIMIT: Duration = Duration::from_secs(30);
const RUN_LIMIT: Duration = Duration::from_secs(120);
const CPU_THREADS: usize = 8;
const PRIMING_VALUES: [i64; 4] = [13, 29, -63_245, 71];

const ECOLOGY_SCHEMA: u64 = 1;
const ECOLOGY_GENERATION: u64 = 2;
const ECOLOGY_RANK: u64 = 3;
const ECOLOGY_AXIS_COUNT: u64 = 4;
const ECOLOGY_PIVOT: u64 = 10;
const ECOLOGY_AXIS: u64 = 11;
const ECOLOGY_COEFFICIENT_NUMERATOR_SIGN: u64 = 20;
const ECOLOGY_COEFFICIENT_NUMERATOR_COUNT: u64 = 21;
const ECOLOGY_COEFFICIENT_NUMERATOR_LIMB: u64 = 22;
const ECOLOGY_COEFFICIENT_DENOMINATOR_SIGN: u64 = 23;
const ECOLOGY_COEFFICIENT_DENOMINATOR_COUNT: u64 = 24;
const ECOLOGY_COEFFICIENT_DENOMINATOR_LIMB: u64 = 25;
const ECOLOGY_SUPPORT_COUNT: u64 = 30;
const ECOLOGY_SUPPORT_FACE_COUNT: u64 = 31;
const ECOLOGY_SUPPORT_FACE_RECURRENCE: u64 = 32;
const ECOLOGY_SUPPORT_CONTEXT_PRESENT: u64 = 33;
const ECOLOGY_SUPPORT_OPERATION_LENGTH: u64 = 40;
const ECOLOGY_SUPPORT_OPERATION_BYTE: u64 = 41;
const ECOLOGY_SUPPORT_CONTEXT_LENGTH: u64 = 42;
const ECOLOGY_SUPPORT_CONTEXT_BYTE: u64 = 43;
const ECOLOGY_SUPPORT_CONDITION_LENGTH: u64 = 44;
const ECOLOGY_SUPPORT_CONDITION_BYTE: u64 = 45;
const ECOLOGY_SUPPORT_ORIENTATION: u64 = 50;
const ECOLOGY_SUPPORT_AXIS_ORDER: u64 = 51;

const CURRENT_SCHEMA: u64 = 101;
const CURRENT_ORDINAL: u64 = 102;
const CURRENT_OPERATION_LENGTH: u64 = 110;
const CURRENT_OPERATION_BYTE: u64 = 111;
const CURRENT_CONTEXT_LENGTH: u64 = 112;
const CURRENT_CONTEXT_BYTE: u64 = 113;
const CURRENT_CONDITION_LENGTH: u64 = 114;
const CURRENT_CONDITION_BYTE: u64 = 115;
const CURRENT_PIVOT_COUNT: u64 = 120;
const CURRENT_PIVOT_WORD: u64 = 121;

const RESIDUAL_SCHEMA: u64 = 201;
const RESIDUAL_AXIS_COUNT: u64 = 202;
const RESIDUAL_NUMERATOR_SIGN: u64 = 210;
const RESIDUAL_NUMERATOR_COUNT: u64 = 211;
const RESIDUAL_NUMERATOR_LIMB: u64 = 212;
const RESIDUAL_DENOMINATOR_SIGN: u64 = 213;
const RESIDUAL_DENOMINATOR_COUNT: u64 = 214;
const RESIDUAL_DENOMINATOR_LIMB: u64 = 215;

#[derive(Deserialize)]
struct Source {
    schema: String,
    observation_id: String,
    sources: Value,
    cut: SourceCut,
    local_law_coefficients: Vec<Vec<String>>,
    factor_weight_words: Vec<Vec<u16>>,
    initial_ecology: SourceInitialEcology,
    evaluations: Vec<SourceEvaluation>,
    expected: SourceExpected,
    numerical_law: String,
    stopping_condition: String,
}

#[derive(Deserialize)]
struct SourceCut {
    layer: usize,
    receiver_axes: Vec<u32>,
    parent_factor_count: usize,
    pivot_factors: Vec<u32>,
    local_rank: usize,
    parent_products_per_receiver: usize,
    local_products_per_receiver: usize,
    boundary: String,
}

#[derive(Deserialize)]
struct SourceInitialEcology {
    training_current_ids: Vec<String>,
    support: Vec<SourceSupport>,
}

#[derive(Deserialize)]
struct SourceSupport {
    operation: String,
    condition: String,
    faces: Vec<SourceFaceCount>,
}

#[derive(Deserialize)]
struct SourceFaceCount {
    face: Face,
    count: usize,
}

#[derive(Clone, Deserialize)]
struct SourceEvaluation {
    ordinal: usize,
    current_id: String,
    operation: String,
    context: String,
    condition: String,
    pivot_activation_words: Vec<u16>,
    parent_activation_words: Vec<u16>,
    initial_supported_faces: Vec<Face>,
    local_prediction: SourcePrediction,
    expected_substitution: bool,
    parent: SourceParent,
    residual: Vec<String>,
}

#[derive(Clone, Deserialize)]
struct SourcePrediction {
    exact_output: Vec<String>,
    face: Face,
}

#[derive(Clone, Deserialize)]
struct SourceParent {
    exact_output: Vec<String>,
    face: Face,
}

#[derive(Deserialize)]
struct SourceExpected {
    selective_parent_invocations: usize,
    always_parent_invocations: usize,
    first_pass_substitutions: usize,
    substituted_current_id: String,
    source_absent_recurrence_probes: usize,
    model_reruns: usize,
    feature_searches: usize,
    thresholds: usize,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
struct Face {
    orientation: Vec<String>,
    signed_axis_order: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct FaceCount {
    face: Face,
    count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SupportEntry {
    operation: String,
    context: Option<String>,
    condition: String,
    faces: Vec<FaceCount>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Ecology {
    generation: u64,
    pivot_factors: Vec<u32>,
    axes: Vec<u32>,
    coefficients: Vec<Vec<BigRational>>,
    support: Vec<SupportEntry>,
}

impl Ecology {
    fn supported_faces(&self, operation: &str, context: &str, condition: &str) -> Vec<Face> {
        let exact = self.support.iter().find(|entry| {
            entry.operation == operation
                && entry.context.as_deref() == Some(context)
                && entry.condition == condition
        });
        let fallback = self.support.iter().find(|entry| {
            entry.operation == operation && entry.context.is_none() && entry.condition == condition
        });
        exact
            .or(fallback)
            .map(|entry| entry.faces.iter().map(|row| row.face.clone()).collect())
            .unwrap_or_default()
    }

    fn learn_exact(&mut self, operation: &str, context: &str, condition: &str, face: Face) {
        match self.support.iter_mut().find(|entry| {
            entry.operation == operation
                && entry.context.as_deref() == Some(context)
                && entry.condition == condition
        }) {
            Some(entry) => match entry.faces.iter_mut().find(|row| row.face == face) {
                Some(row) => row.count += 1,
                None => entry.faces.push(FaceCount { face, count: 1 }),
            },
            None => self.support.push(SupportEntry {
                operation: operation.to_owned(),
                context: Some(context.to_owned()),
                condition: condition.to_owned(),
                faces: vec![FaceCount { face, count: 1 }],
            }),
        }
        self.support.sort_by(|left, right| {
            (
                &left.operation,
                left.context.as_deref().unwrap_or(""),
                &left.condition,
            )
                .cmp(&(
                    &right.operation,
                    right.context.as_deref().unwrap_or(""),
                    &right.condition,
                ))
        });
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CurrentCarrier {
    ordinal: u16,
    operation: String,
    context: String,
    condition: String,
    pivot_words: Vec<u16>,
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
    fn source(kind: &[u8], identity: &[u8]) -> Self {
        Self {
            data_namespace: namespace(&[b"eros-parent-open-data-v1", kind, identity]),
            recruit_namespace: namespace(&[b"eros-parent-open-recruit-v1", kind, identity]),
        }
    }

    fn after_contact(self, identity: &[u8]) -> Self {
        Self {
            data_namespace: self.data_namespace,
            recruit_namespace: namespace(&[
                b"eros-parent-open-after-v1",
                &self.recruit_namespace.to_le_bytes(),
                identity,
            ]),
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
            Err(format!(
                "the bounded run exceeded {} seconds",
                RUN_LIMIT.as_secs()
            ))
        } else {
            Ok(())
        }
    }
}

struct ParentOracle<'a> {
    weight_words: &'a [Vec<u16>],
    calls: usize,
    products: usize,
    sums: usize,
    wall: Duration,
}

impl<'a> ParentOracle<'a> {
    fn new(weight_words: &'a [Vec<u16>]) -> Self {
        Self {
            weight_words,
            calls: 0,
            products: 0,
            sums: 0,
            wall: Duration::ZERO,
        }
    }

    fn conduct(&mut self, activation_words: &[u16]) -> Result<Vec<BigRational>, String> {
        if self.weight_words.is_empty()
            || self
                .weight_words
                .iter()
                .any(|row| row.len() != activation_words.len())
        {
            return Err("the parent factorization changed common extent".to_owned());
        }
        let started = Instant::now();
        let activations = activation_words
            .iter()
            .copied()
            .map(decode_bfloat16)
            .collect::<Result<Vec<_>, _>>()?;
        let mut output = Vec::with_capacity(self.weight_words.len());
        for weights in self.weight_words {
            let mut sum = BigRational::from_integer(BigInt::from(0));
            for (activation, word) in activations.iter().zip(weights) {
                sum += activation * decode_bfloat16(*word)?;
                self.products += 1;
                self.sums += 1;
            }
            output.push(sum);
        }
        self.calls += 1;
        self.wall += started.elapsed();
        Ok(output)
    }

    fn read(&self) -> Value {
        json!({
            "invocations": self.calls,
            "exact_products": self.products,
            "exact_accumulations": self.sums,
            "wall_micros": duration_micros(self.wall),
        })
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
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
    if report_path.exists() {
        return Err(format!(
            "create-once report already exists: {}",
            report_path.display()
        ));
    }
    let source_bytes = std::fs::read(&source_path).map_err(debug)?;
    let source_sha256 = sha256(&source_bytes);
    let source: Source = serde_json::from_slice(&source_bytes).map_err(debug)?;
    validate_source(&source)?;

    let started = Instant::now();
    let report = run_cpu(&source, &source_sha256)?;
    let mut report = report;
    report["run_wall_micros"] = json!(duration_micros(started.elapsed()));
    report["source"]["path"] = json!(source_path);
    report["source"]["sha256"] = json!(source_sha256);
    let encoded = serde_json::to_vec_pretty(&report).map_err(debug)?;
    let mut output = OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&report_path)
        .map_err(debug)?;
    output.write_all(&encoded).map_err(debug)?;
    output.write_all(b"\n").map_err(debug)?;
    println!("{}", serde_json::to_string_pretty(&report).map_err(debug)?);
    Ok(())
}

fn run_cpu(source: &Source, source_sha256: &str) -> Result<Value, String> {
    let budget = RunBudget::new();
    let mut executor = ParallelCpuLiveCurrentExecutor::new(CPU_THREADS);
    let mut ecology = source_ecology(source)?;
    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let mut events = Vec::new();

    let mut encoded_ecology = ecology_words(&ecology);
    let mut ecology_handle = ArtifactHandle::source(
        b"derived-ecology",
        &compact_identity_bytes(&encoded_ecology),
    );
    let pair = primed_pair(&mut machine, &mut executor)?;
    let arcs = seed_arcs(pair, ecology_handle, &encoded_ecology)?;
    let (radiation, event) = profiled_event(
        &budget,
        &mut machine,
        &mut executor,
        "initial-derived-ecology",
        encoded_ecology.len(),
        pair,
        &arcs,
        None,
    )?;
    events.push(event);
    let deposited = regional_constituent(&radiation, "initial ecology")?;
    if decode_ecology(deposited, ecology_handle.data_namespace)? != ecology {
        return Err("the initial derived ecology changed during deposit".to_owned());
    }
    let initial_rest = machine.rest_image().map_err(debug)?;
    machine = LiveCurrentMachine::from_rest_image(initial_rest.clone()).map_err(debug)?;
    if machine.rest_image().map_err(debug)? != initial_rest
        || standing_ecology(&machine, ecology_handle.data_namespace)? != ecology
    {
        return Err("the initial ecology changed across exact rest/remount".to_owned());
    }

    let mut selective_parent = ParentOracle::new(&source.factor_weight_words);
    let mut first_pass = Vec::new();
    let mut substituted_ids = Vec::new();
    let mut every_residual_exact = true;
    let mut every_factor_exact = true;
    let mut local_products = 0usize;
    let mut local_sums = 0usize;

    for source_row in &source.evaluations {
        budget.require_open()?;
        let current = CurrentCarrier {
            ordinal: u16::try_from(source_row.ordinal).map_err(debug)?,
            operation: source_row.operation.clone(),
            context: source_row.context.clone(),
            condition: source_row.condition.clone(),
            pivot_words: source_row.pivot_activation_words.clone(),
        };
        let current_words = current_words(&current);
        let current_handle =
            ArtifactHandle::source(b"later-current", &compact_identity_bytes(&current_words));
        let query_identity = namespace(&[
            b"eros-parent-open-query-v1",
            source_sha256.as_bytes(),
            source_row.current_id.as_bytes(),
        ])
        .to_le_bytes();
        let query_handle = ecology_handle.after_contact(&query_identity);
        let pair = primed_pair(&mut machine, &mut executor)?;
        let arcs = query_arcs(
            pair,
            current_handle,
            &current_words,
            ecology_handle,
            query_handle,
        )?;
        let (radiation, event) = profiled_event(
            &budget,
            &mut machine,
            &mut executor,
            &format!("query-{}", source_row.current_id),
            current_words.len(),
            pair,
            &arcs,
            None,
        )?;
        events.push(event);
        let meeting = regional_constituent(&radiation, "derived-ecology query")?;
        let recovered_ecology = decode_ecology(meeting, ecology_handle.data_namespace)?;
        let recovered_current = decode_current(meeting, current_handle.data_namespace)?;
        if recovered_ecology != ecology || recovered_current != current {
            return Err(format!(
                "current {} did not recover the active ecology and its own face",
                source_row.current_id
            ));
        }

        let prediction = apply_law(&current.pivot_words, &recovered_ecology)?;
        local_products += recovered_ecology
            .pivot_factors
            .len()
            .checked_mul(recovered_ecology.axes.len())
            .ok_or_else(|| "local product count overflowed".to_owned())?;
        local_sums += recovered_ecology
            .pivot_factors
            .len()
            .checked_mul(recovered_ecology.axes.len())
            .ok_or_else(|| "local sum count overflowed".to_owned())?;
        let predicted_face = face(&recovered_ecology.axes, &prediction);
        let expected_prediction = parse_ratios(&source_row.local_prediction.exact_output)?;
        if prediction != expected_prediction || predicted_face != source_row.local_prediction.face {
            return Err(format!(
                "current {} changed its inherited local transformation",
                source_row.current_id
            ));
        }
        let supported = recovered_ecology.supported_faces(
            &current.operation,
            &current.context,
            &current.condition,
        );
        if supported != source_row.initial_supported_faces {
            return Err(format!(
                "current {} changed its initial receiver support",
                source_row.current_id
            ));
        }
        let substitute = supported.as_slice() == [predicted_face.clone()];
        if substitute != source_row.expected_substitution {
            return Err(format!(
                "current {} changed its frozen substitution decision",
                source_row.current_id
            ));
        }

        let expected_parent = parse_ratios(&source_row.parent.exact_output)?;
        let expected_residual = parse_ratios(&source_row.residual)?;
        let mut residual_handle = None;
        let mut encoded_residual = Vec::new();
        let mut parent_output = None;
        if substitute {
            substituted_ids.push(source_row.current_id.clone());
        } else {
            let actual = selective_parent.conduct(&source_row.parent_activation_words)?;
            if actual != expected_parent || face(&ecology.axes, &actual) != source_row.parent.face {
                return Err(format!(
                    "current {} changed its exact parent consequence",
                    source_row.current_id
                ));
            }
            let residual = actual
                .iter()
                .zip(&prediction)
                .map(|(parent, local)| parent - local)
                .collect::<Vec<_>>();
            every_residual_exact &= residual == expected_residual;
            encoded_residual = residual_words(&residual);
            let handle = ArtifactHandle::source(
                b"parent-residual",
                &compact_identity_bytes(&encoded_residual),
            );
            let pair = primed_pair(&mut machine, &mut executor)?;
            let arcs = seed_arcs(pair, handle, &encoded_residual)?;
            let (radiation, event) = profiled_event(
                &budget,
                &mut machine,
                &mut executor,
                &format!("parent-return-{}", source_row.current_id),
                encoded_residual.len(),
                pair,
                &arcs,
                None,
            )?;
            events.push(event);
            let returned = regional_constituent(&radiation, "parent residual")?;
            if decode_residual(returned, handle.data_namespace)? != residual {
                return Err(format!(
                    "current {} lost its complete returned residual",
                    source_row.current_id
                ));
            }
            ecology.learn_exact(
                &current.operation,
                &current.context,
                &current.condition,
                source_row.parent.face.clone(),
            );
            residual_handle = Some(handle);
            parent_output = Some(actual);
        }

        ecology.generation = ecology
            .generation
            .checked_add(1)
            .ok_or_else(|| "ecology generation overflowed".to_owned())?;
        let next_words = ecology_words(&ecology);
        let next_handle =
            ArtifactHandle::source(b"derived-ecology", &compact_identity_bytes(&next_words));
        let pair = primed_pair(&mut machine, &mut executor)?;
        let mut replacement_arcs = Vec::new();
        append_words(
            &mut replacement_arcs,
            pair,
            ecology_handle.data_namespace,
            &encoded_ecology,
        )?;
        append_words(
            &mut replacement_arcs,
            pair,
            current_handle.data_namespace,
            &current_words,
        )?;
        push_interface(
            &mut replacement_arcs,
            pair,
            InterfaceCapability::new(query_handle.recruit_namespace, RECRUIT_LOCAL),
            // This is the same temporally carried hand that the query emitted.
            // Equal hands cancel across that time-parity seam; reversing it would
            // leave the query aperture exposed and make the successor factor false.
            IncidenceHand::With,
        )?;
        if let Some(handle) = residual_handle {
            append_words(
                &mut replacement_arcs,
                pair,
                handle.data_namespace,
                &encoded_residual,
            )?;
            push_interface(
                &mut replacement_arcs,
                pair,
                InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
                IncidenceHand::Against,
            )?;
        }
        let outgoing_start = replacement_arcs.len();
        append_words(
            &mut replacement_arcs,
            pair,
            next_handle.data_namespace,
            &next_words,
        )?;
        push_interface(
            &mut replacement_arcs,
            pair,
            InterfaceCapability::new(next_handle.recruit_namespace, RECRUIT_LOCAL),
            IncidenceHand::Against,
        )?;
        let outgoing_slots = (outgoing_start..replacement_arcs.len())
            .map(|slot| u32::try_from(slot).map_err(debug))
            .collect::<Result<Vec<_>, _>>()?;
        let (radiation, event) = profiled_event(
            &budget,
            &mut machine,
            &mut executor,
            &format!("successor-{}", source_row.current_id),
            next_words.len(),
            pair,
            &replacement_arcs,
            Some(&outgoing_slots),
        )?;
        events.push(event);
        let successor = regional_constituent(&radiation, "ecology successor")?;
        let factor_exact = decode_ecology(successor, next_handle.data_namespace)? == ecology;
        every_factor_exact &= factor_exact;
        let memory = machine.memory();
        every_factor_exact &= memory.standing_constituents == 1
            && memory.constituent_cells == 3
            && memory.constituent_incidences == next_words.len() + 1
            && memory.constituent_pins == next_words.len() + 1
            && memory.constituent_paths == next_words.len() + 1;

        first_pass.push(json!({
            "ordinal": source_row.ordinal,
            "current_id": source_row.current_id,
            "operation": source_row.operation,
            "context": source_row.context,
            "condition": source_row.condition,
            "supported_faces_before": supported,
            "local_prediction": {
                "exact_output": prediction.iter().map(ratio_string).collect::<Vec<_>>(),
                "face": predicted_face,
            },
            "relation": if substitute { "RIDE_SUBSTITUTE" } else { "OPEN_PARENT_RETURN" },
            "parent_invoked": !substitute,
            "parent_output": parent_output.as_ref().map(|values| values.iter().map(ratio_string).collect::<Vec<_>>()),
            "residual": if substitute { None } else { Some(expected_residual.iter().map(ratio_string).collect::<Vec<_>>()) },
            "source_expected_parent_face": source_row.parent.face,
            "substitution_face_exact_to_parent_control": substitute && predicted_face == source_row.parent.face,
            "outgoing_factor_exact": factor_exact,
            "machine_after": machine_read(&machine)?,
        }));
        encoded_ecology = next_words;
        ecology_handle = next_handle;
    }

    let final_rest = machine.rest_image().map_err(debug)?;
    let remounted = LiveCurrentMachine::from_rest_image(final_rest.clone()).map_err(debug)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == final_rest
        && standing_ecology(&remounted, ecology_handle.data_namespace)? == ecology;
    machine = remounted;

    let mut recurrence = Vec::new();
    for source_row in &source.evaluations {
        let mut branch = LiveCurrentMachine::from_rest_image(machine.rest_image().map_err(debug)?)
            .map_err(debug)?;
        let current = CurrentCarrier {
            ordinal: u16::try_from(source_row.ordinal).map_err(debug)?,
            operation: source_row.operation.clone(),
            context: source_row.context.clone(),
            condition: source_row.condition.clone(),
            pivot_words: source_row.pivot_activation_words.clone(),
        };
        let words = current_words(&current);
        let current_handle =
            ArtifactHandle::source(b"source-absent-probe", &compact_identity_bytes(&words));
        let probe_identity = namespace(&[
            b"eros-parent-open-recurrence-v1",
            source_row.current_id.as_bytes(),
        ])
        .to_le_bytes();
        let pair = primed_pair(&mut branch, &mut executor)?;
        let arcs = query_arcs(
            pair,
            current_handle,
            &words,
            ecology_handle,
            ecology_handle.after_contact(&probe_identity),
        )?;
        let (radiation, event) = profiled_event(
            &budget,
            &mut branch,
            &mut executor,
            &format!("source-absent-{}", source_row.current_id),
            words.len(),
            pair,
            &arcs,
            None,
        )?;
        events.push(event);
        let meeting = regional_constituent(&radiation, "source-absent recurrence")?;
        let recovered = decode_ecology(meeting, ecology_handle.data_namespace)?;
        let recovered_current = decode_current(meeting, current_handle.data_namespace)?;
        let supported = recovered.supported_faces(
            &recovered_current.operation,
            &recovered_current.context,
            &recovered_current.condition,
        );
        recurrence.push(json!({
            "current_id": source_row.current_id,
            "parent_invoked": false,
            "supported_faces": supported,
            "expected_parent_face": source_row.parent.face,
            "exact": supported.as_slice() == [source_row.parent.face.clone()],
        }));
    }

    let control_row = source
        .evaluations
        .first()
        .ok_or_else(|| "the fixed evaluation population is empty".to_owned())?;
    let mut control = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let control_current = CurrentCarrier {
        ordinal: 0,
        operation: control_row.operation.clone(),
        context: control_row.context.clone(),
        condition: control_row.condition.clone(),
        pivot_words: control_row.pivot_activation_words.clone(),
    };
    let control_words = current_words(&control_current);
    let control_handle = ArtifactHandle::source(
        b"no-ecology-control",
        &compact_identity_bytes(&control_words),
    );
    let pair = primed_pair(&mut control, &mut executor)?;
    let arcs = query_arcs(
        pair,
        control_handle,
        &control_words,
        ecology_handle,
        ecology_handle.after_contact(b"no-ecology"),
    )?;
    let (radiation, event) = profiled_event(
        &budget,
        &mut control,
        &mut executor,
        "no-ecology-control",
        control_words.len(),
        pair,
        &arcs,
        None,
    )?;
    events.push(event);
    let no_ecology = regional_constituent(&radiation, "no-ecology control")?;
    let no_ecology_recovered = decode_ecology(no_ecology, ecology_handle.data_namespace).is_ok();

    let mut always_parent = ParentOracle::new(&source.factor_weight_words);
    let mut always_parent_exact = true;
    for source_row in &source.evaluations {
        let output = always_parent.conduct(&source_row.parent_activation_words)?;
        always_parent_exact &= output == parse_ratios(&source_row.parent.exact_output)?;
    }

    let recurrence_exact = recurrence.iter().all(|row| row["exact"] == json!(true));
    let substitutions_exact = first_pass
        .iter()
        .filter(|row| row["parent_invoked"] == json!(false))
        .all(|row| row["substitution_face_exact_to_parent_control"] == json!(true));
    let acceptance = json!({
        "fixed_source_validated": true,
        "one_nonidentical_current_substituted_before_parent_evaluation":
            substituted_ids == [source.expected.substituted_current_id.clone()],
        "selective_parent_invocation_count_exact":
            selective_parent.calls == source.expected.selective_parent_invocations,
        "always_parent_invocation_count_exact":
            always_parent.calls == source.expected.always_parent_invocations,
        "first_pass_substitution_count_exact":
            substituted_ids.len() == source.expected.first_pass_substitutions,
        "every_substitution_matched_the_parent_receiver_control": substitutions_exact,
        "every_open_parent_return_carried_its_complete_residual": every_residual_exact,
        "every_successor_was_the_complete_active_ecology_boundary": every_factor_exact,
        "all_source_absent_recurrence_probes_matched":
            recurrence.len() == source.expected.source_absent_recurrence_probes && recurrence_exact,
        "derived_ecology_survived_exact_rest_remount": rest_exact,
        "no_ecology_control_could_not_substitute": !no_ecology_recovered,
        "always_parent_foil_was_exact": always_parent_exact,
        "source_lineages_departed": machine.memory().live_lineages == 0,
        "no_floating_point_causal_data": true,
    });
    if acceptance
        .as_object()
        .ok_or_else(|| "acceptance record is not an object".to_owned())?
        .values()
        .any(|value| value != &json!(true))
    {
        return Err(format!(
            "one bounded substitution acceptance predicate failed: {}",
            serde_json::to_string_pretty(&acceptance).map_err(debug)?
        ));
    }

    Ok(json!({
        "schema": REPORT_SCHEMA,
        "observation_id": OBSERVATION_ID,
        "status": "accepted",
        "question": "Can one inherited local transformer ecology substitute at its declared receiver before evaluating the parent, return to the parent only where OPEN, and retain those later faces for source-absent recurrence?",
        "theory_to_structure": "The carried rank-six law forms a candidate five-axis face from six pivot words. The carried conditional chart admits substitution only for one singleton-supported face. OPEN paths alone evaluate the complete 8,192-factor parent relation; their exact residual and receiver face return later, and the event emits a factored successor ecology.",
        "source": {
            "schema": source.schema,
            "observation_id": source.observation_id,
            "sources": source.sources,
        },
        "cut": {
            "layer": source.cut.layer,
            "receiver_axes": source.cut.receiver_axes,
            "boundary": source.cut.boundary,
            "parent_factor_count": source.cut.parent_factor_count,
            "local_rank": source.cut.local_rank,
            "pivot_factors": source.cut.pivot_factors,
            "parent_products_per_receiver": source.cut.parent_products_per_receiver,
            "local_products_per_receiver": source.cut.local_products_per_receiver,
        },
        "physical_execution": {
            "executor": "ParallelCpuLiveCurrentExecutor",
            "cpu_threads": CPU_THREADS,
            "model_reruns": source.expected.model_reruns,
            "feature_searches": source.expected.feature_searches,
            "thresholds": source.expected.thresholds,
            "semantic_evaluation_currents": source.evaluations.len(),
            "local_exact_products": local_products,
            "local_exact_accumulations": local_sums,
            "selective_parent": selective_parent.read(),
            "always_parent_foil": always_parent.read(),
        },
        "first_pass": first_pass,
        "source_absent_recurrence": recurrence,
        "final_ecology": ecology_read(&ecology),
        "final_machine": machine_read(&machine)?,
        "control": {
            "same_current_without_ecology_recovered_ecology": no_ecology_recovered,
            "substitution_available": false,
        },
        "acceptance": acceptance,
        "numerical_law": source.numerical_law,
        "stopping_condition": source.stopping_condition,
        "conclusion": "At this exact five-axis receiver, the derived ecology omitted one first-passage parent evaluation for a nonidentical context, invoked the parent only on five OPEN paths, retained every returned residual as new local support, and then conducted all six recurrence probes without parent evaluation. This is receiver-specific parent substitution, not full-block or end-to-end transformer replacement.",
        "events": events,
    }))
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != SOURCE_SCHEMA || source.observation_id != OBSERVATION_ID {
        return Err("the parent-on-OPEN source identity changed".to_owned());
    }
    if source.cut.local_rank != source.cut.pivot_factors.len()
        || source.local_law_coefficients.len() != source.cut.local_rank
        || source
            .local_law_coefficients
            .iter()
            .any(|row| row.len() != source.cut.receiver_axes.len())
        || source.factor_weight_words.len() != source.cut.receiver_axes.len()
        || source
            .factor_weight_words
            .iter()
            .any(|row| row.len() != source.cut.parent_factor_count)
        || source.cut.parent_products_per_receiver
            != source.cut.parent_factor_count * source.cut.receiver_axes.len()
        || source.cut.local_products_per_receiver
            != source.cut.local_rank * source.cut.receiver_axes.len()
        || source.initial_ecology.training_current_ids.len() != 6
        || source.evaluations.len() != 6
        || source.expected.selective_parent_invocations != 5
        || source.expected.always_parent_invocations != 6
        || source.expected.first_pass_substitutions != 1
        || source.expected.source_absent_recurrence_probes != 6
        || source.expected.model_reruns != 0
        || source.expected.feature_searches != 0
        || source.expected.thresholds != 0
    {
        return Err("the fixed parent-on-OPEN extent or stopping contract changed".to_owned());
    }
    let substitutions = source
        .evaluations
        .iter()
        .filter(|row| row.expected_substitution)
        .map(|row| row.current_id.as_str())
        .collect::<Vec<_>>();
    if substitutions != [source.expected.substituted_current_id.as_str()] {
        return Err("the fixed substitution population changed".to_owned());
    }
    for (ordinal, row) in source.evaluations.iter().enumerate() {
        if row.ordinal != ordinal
            || row.pivot_activation_words.len() != source.cut.local_rank
            || row.parent_activation_words.len() != source.cut.parent_factor_count
            || row.local_prediction.exact_output.len() != source.cut.receiver_axes.len()
            || row.parent.exact_output.len() != source.cut.receiver_axes.len()
            || row.residual.len() != source.cut.receiver_axes.len()
        {
            return Err(format!(
                "current {} changed its fixed extent",
                row.current_id
            ));
        }
    }
    Ok(())
}

fn source_ecology(source: &Source) -> Result<Ecology, String> {
    let mut support = source
        .initial_ecology
        .support
        .iter()
        .map(|entry| SupportEntry {
            operation: entry.operation.clone(),
            context: None,
            condition: entry.condition.clone(),
            faces: entry
                .faces
                .iter()
                .map(|row| FaceCount {
                    face: row.face.clone(),
                    count: row.count,
                })
                .collect(),
        })
        .collect::<Vec<_>>();
    support.sort_by(|left, right| {
        (&left.operation, &left.condition).cmp(&(&right.operation, &right.condition))
    });
    Ok(Ecology {
        generation: 0,
        pivot_factors: source.cut.pivot_factors.clone(),
        axes: source.cut.receiver_axes.clone(),
        coefficients: source
            .local_law_coefficients
            .iter()
            .map(|row| row.iter().map(|value| parse_ratio(value)).collect())
            .collect::<Result<_, _>>()?,
        support,
    })
}

fn apply_law(words: &[u16], ecology: &Ecology) -> Result<Vec<BigRational>, String> {
    if words.len() != ecology.coefficients.len()
        || ecology
            .coefficients
            .iter()
            .any(|row| row.len() != ecology.axes.len())
    {
        return Err("the local law changed common extent".to_owned());
    }
    let values = words
        .iter()
        .copied()
        .map(decode_bfloat16)
        .collect::<Result<Vec<_>, _>>()?;
    Ok((0..ecology.axes.len())
        .map(|axis| {
            values.iter().zip(&ecology.coefficients).fold(
                BigRational::from_integer(BigInt::from(0)),
                |sum, (value, row)| sum + value * &row[axis],
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
    let (mut coefficient, power) = if exponent == 0 {
        (BigInt::from(fraction), -133i32)
    } else {
        (
            BigInt::from((1u16 << 7) | fraction),
            i32::from(exponent) - 134,
        )
    };
    if negative {
        coefficient = -coefficient;
    }
    if power >= 0 {
        Ok(BigRational::from_integer(
            coefficient << usize::try_from(power).map_err(debug)?,
        ))
    } else {
        Ok(BigRational::new(
            coefficient,
            BigInt::from(1u8) << usize::try_from(-power).map_err(debug)?,
        ))
    }
}

fn parse_ratios(values: &[String]) -> Result<Vec<BigRational>, String> {
    values.iter().map(|value| parse_ratio(value)).collect()
}

fn parse_ratio(value: &str) -> Result<BigRational, String> {
    let (numerator, denominator) = value
        .split_once('/')
        .map_or((value, "1"), |(left, right)| (left, right));
    let numerator = numerator.parse::<BigInt>().map_err(debug)?;
    let denominator = denominator.parse::<BigInt>().map_err(debug)?;
    if denominator.sign() != Sign::Plus {
        return Err(format!("ratio {value} has no positive denominator"));
    }
    Ok(BigRational::new(numerator, denominator))
}

fn ratio_string(value: &BigRational) -> String {
    if value.denom() == &BigInt::from(1) {
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
            .map(|value| match value.numer().sign() {
                Sign::Minus => "negative",
                Sign::NoSign => "zero",
                Sign::Plus => "positive",
            })
            .map(str::to_owned)
            .collect(),
        signed_axis_order: order.into_iter().map(|at| axes[at]).collect(),
    }
}

fn ecology_words(ecology: &Ecology) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(ECOLOGY_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(ECOLOGY_GENERATION, ecology.generation),
        CompactWord::scalar(ECOLOGY_RANK, ecology.pivot_factors.len() as u64),
        CompactWord::scalar(ECOLOGY_AXIS_COUNT, ecology.axes.len() as u64),
        CompactWord::scalar(ECOLOGY_SUPPORT_COUNT, ecology.support.len() as u64),
    ];
    for (at, pivot) in ecology.pivot_factors.iter().copied().enumerate() {
        words.push(CompactWord::at(
            ECOLOGY_PIVOT,
            vec![at as u64],
            u64::from(pivot),
        ));
    }
    for (at, axis) in ecology.axes.iter().copied().enumerate() {
        words.push(CompactWord::at(
            ECOLOGY_AXIS,
            vec![at as u64],
            u64::from(axis),
        ));
    }
    for (row, coefficients) in ecology.coefficients.iter().enumerate() {
        for (axis, coefficient) in coefficients.iter().enumerate() {
            append_rational_words(
                &mut words,
                &[row as u64, axis as u64],
                [
                    ECOLOGY_COEFFICIENT_NUMERATOR_SIGN,
                    ECOLOGY_COEFFICIENT_NUMERATOR_COUNT,
                    ECOLOGY_COEFFICIENT_NUMERATOR_LIMB,
                    ECOLOGY_COEFFICIENT_DENOMINATOR_SIGN,
                    ECOLOGY_COEFFICIENT_DENOMINATOR_COUNT,
                    ECOLOGY_COEFFICIENT_DENOMINATOR_LIMB,
                ],
                coefficient,
            );
        }
    }
    for (entry_at, entry) in ecology.support.iter().enumerate() {
        let base = [entry_at as u64];
        append_string_words(
            &mut words,
            &base,
            ECOLOGY_SUPPORT_OPERATION_LENGTH,
            ECOLOGY_SUPPORT_OPERATION_BYTE,
            &entry.operation,
        );
        words.push(CompactWord::at(
            ECOLOGY_SUPPORT_CONTEXT_PRESENT,
            base.to_vec(),
            u64::from(entry.context.is_some()),
        ));
        if let Some(context) = &entry.context {
            append_string_words(
                &mut words,
                &base,
                ECOLOGY_SUPPORT_CONTEXT_LENGTH,
                ECOLOGY_SUPPORT_CONTEXT_BYTE,
                context,
            );
        }
        append_string_words(
            &mut words,
            &base,
            ECOLOGY_SUPPORT_CONDITION_LENGTH,
            ECOLOGY_SUPPORT_CONDITION_BYTE,
            &entry.condition,
        );
        words.push(CompactWord::at(
            ECOLOGY_SUPPORT_FACE_COUNT,
            base.to_vec(),
            entry.faces.len() as u64,
        ));
        for (face_at, row) in entry.faces.iter().enumerate() {
            words.push(CompactWord::at(
                ECOLOGY_SUPPORT_FACE_RECURRENCE,
                vec![entry_at as u64, face_at as u64],
                row.count as u64,
            ));
            for (axis_at, orientation) in row.face.orientation.iter().enumerate() {
                words.push(CompactWord::at(
                    ECOLOGY_SUPPORT_ORIENTATION,
                    vec![entry_at as u64, face_at as u64, axis_at as u64],
                    orientation_code(orientation),
                ));
            }
            for (axis_at, axis) in row.face.signed_axis_order.iter().copied().enumerate() {
                words.push(CompactWord::at(
                    ECOLOGY_SUPPORT_AXIS_ORDER,
                    vec![entry_at as u64, face_at as u64, axis_at as u64],
                    u64::from(axis),
                ));
            }
        }
    }
    words
}

fn decode_ecology(constituent: &LiveConstituent, root: u64) -> Result<Ecology, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, ECOLOGY_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("ecology schema changed".to_owned());
    }
    let generation = atlas.word(root, ECOLOGY_GENERATION, &[])?;
    let rank = usize::try_from(atlas.word(root, ECOLOGY_RANK, &[])?).map_err(debug)?;
    let axes_count = usize::try_from(atlas.word(root, ECOLOGY_AXIS_COUNT, &[])?).map_err(debug)?;
    let support_count =
        usize::try_from(atlas.word(root, ECOLOGY_SUPPORT_COUNT, &[])?).map_err(debug)?;
    let pivot_factors = (0..rank)
        .map(|at| u32::try_from(atlas.word(root, ECOLOGY_PIVOT, &[at as u64])?).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    let axes = (0..axes_count)
        .map(|at| u32::try_from(atlas.word(root, ECOLOGY_AXIS, &[at as u64])?).map_err(debug))
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
                            ECOLOGY_COEFFICIENT_NUMERATOR_SIGN,
                            ECOLOGY_COEFFICIENT_NUMERATOR_COUNT,
                            ECOLOGY_COEFFICIENT_NUMERATOR_LIMB,
                            ECOLOGY_COEFFICIENT_DENOMINATOR_SIGN,
                            ECOLOGY_COEFFICIENT_DENOMINATOR_COUNT,
                            ECOLOGY_COEFFICIENT_DENOMINATOR_LIMB,
                        ],
                    )
                })
                .collect()
        })
        .collect::<Result<Vec<Vec<_>>, String>>()?;
    let mut support = Vec::with_capacity(support_count);
    for entry_at in 0..support_count {
        let base = [entry_at as u64];
        let operation = decode_string(
            &atlas,
            root,
            &base,
            ECOLOGY_SUPPORT_OPERATION_LENGTH,
            ECOLOGY_SUPPORT_OPERATION_BYTE,
        )?;
        let context = match atlas.word(root, ECOLOGY_SUPPORT_CONTEXT_PRESENT, &base)? {
            0 => None,
            1 => Some(decode_string(
                &atlas,
                root,
                &base,
                ECOLOGY_SUPPORT_CONTEXT_LENGTH,
                ECOLOGY_SUPPORT_CONTEXT_BYTE,
            )?),
            value => return Err(format!("invalid support context-presence code {value}")),
        };
        let condition = decode_string(
            &atlas,
            root,
            &base,
            ECOLOGY_SUPPORT_CONDITION_LENGTH,
            ECOLOGY_SUPPORT_CONDITION_BYTE,
        )?;
        let face_count =
            usize::try_from(atlas.word(root, ECOLOGY_SUPPORT_FACE_COUNT, &base)?).map_err(debug)?;
        let mut faces = Vec::with_capacity(face_count);
        for face_at in 0..face_count {
            let count = usize::try_from(atlas.word(
                root,
                ECOLOGY_SUPPORT_FACE_RECURRENCE,
                &[entry_at as u64, face_at as u64],
            )?)
            .map_err(debug)?;
            let orientation = (0..axes_count)
                .map(|axis_at| {
                    orientation_from_code(atlas.word(
                        root,
                        ECOLOGY_SUPPORT_ORIENTATION,
                        &[entry_at as u64, face_at as u64, axis_at as u64],
                    )?)
                })
                .collect::<Result<Vec<_>, _>>()?;
            let signed_axis_order = (0..axes_count)
                .map(|axis_at| {
                    u32::try_from(atlas.word(
                        root,
                        ECOLOGY_SUPPORT_AXIS_ORDER,
                        &[entry_at as u64, face_at as u64, axis_at as u64],
                    )?)
                    .map_err(debug)
                })
                .collect::<Result<Vec<_>, _>>()?;
            faces.push(FaceCount {
                face: Face {
                    orientation,
                    signed_axis_order,
                },
                count,
            });
        }
        support.push(SupportEntry {
            operation,
            context,
            condition,
            faces,
        });
    }
    Ok(Ecology {
        generation,
        pivot_factors,
        axes,
        coefficients,
        support,
    })
}

fn current_words(current: &CurrentCarrier) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(CURRENT_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(CURRENT_ORDINAL, u64::from(current.ordinal)),
        CompactWord::scalar(CURRENT_PIVOT_COUNT, current.pivot_words.len() as u64),
    ];
    append_string_words(
        &mut words,
        &[],
        CURRENT_OPERATION_LENGTH,
        CURRENT_OPERATION_BYTE,
        &current.operation,
    );
    append_string_words(
        &mut words,
        &[],
        CURRENT_CONTEXT_LENGTH,
        CURRENT_CONTEXT_BYTE,
        &current.context,
    );
    append_string_words(
        &mut words,
        &[],
        CURRENT_CONDITION_LENGTH,
        CURRENT_CONDITION_BYTE,
        &current.condition,
    );
    for (at, word) in current.pivot_words.iter().copied().enumerate() {
        words.push(CompactWord::at(
            CURRENT_PIVOT_WORD,
            vec![at as u64],
            u64::from(word),
        ));
    }
    words
}

fn decode_current(constituent: &LiveConstituent, root: u64) -> Result<CurrentCarrier, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, CURRENT_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("current schema changed".to_owned());
    }
    let ordinal = u16::try_from(atlas.word(root, CURRENT_ORDINAL, &[])?).map_err(debug)?;
    let operation = decode_string(
        &atlas,
        root,
        &[],
        CURRENT_OPERATION_LENGTH,
        CURRENT_OPERATION_BYTE,
    )?;
    let context = decode_string(
        &atlas,
        root,
        &[],
        CURRENT_CONTEXT_LENGTH,
        CURRENT_CONTEXT_BYTE,
    )?;
    let condition = decode_string(
        &atlas,
        root,
        &[],
        CURRENT_CONDITION_LENGTH,
        CURRENT_CONDITION_BYTE,
    )?;
    let pivots = usize::try_from(atlas.word(root, CURRENT_PIVOT_COUNT, &[])?).map_err(debug)?;
    let pivot_words = (0..pivots)
        .map(|at| u16::try_from(atlas.word(root, CURRENT_PIVOT_WORD, &[at as u64])?).map_err(debug))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CurrentCarrier {
        ordinal,
        operation,
        context,
        condition,
        pivot_words,
    })
}

fn residual_words(residual: &[BigRational]) -> Vec<CompactWord> {
    let mut words = vec![
        CompactWord::scalar(RESIDUAL_SCHEMA, COMPACT_SCHEMA),
        CompactWord::scalar(RESIDUAL_AXIS_COUNT, residual.len() as u64),
    ];
    for (axis, value) in residual.iter().enumerate() {
        append_rational_words(
            &mut words,
            &[axis as u64],
            [
                RESIDUAL_NUMERATOR_SIGN,
                RESIDUAL_NUMERATOR_COUNT,
                RESIDUAL_NUMERATOR_LIMB,
                RESIDUAL_DENOMINATOR_SIGN,
                RESIDUAL_DENOMINATOR_COUNT,
                RESIDUAL_DENOMINATOR_LIMB,
            ],
            value,
        );
    }
    words
}

fn decode_residual(constituent: &LiveConstituent, root: u64) -> Result<Vec<BigRational>, String> {
    let atlas = CapabilityAtlas::from_constituent(constituent)?;
    if atlas.word(root, RESIDUAL_SCHEMA, &[])? != COMPACT_SCHEMA {
        return Err("residual schema changed".to_owned());
    }
    let axes = usize::try_from(atlas.word(root, RESIDUAL_AXIS_COUNT, &[])?).map_err(debug)?;
    (0..axes)
        .map(|axis| {
            decode_rational_words(
                &atlas,
                root,
                &[axis as u64],
                [
                    RESIDUAL_NUMERATOR_SIGN,
                    RESIDUAL_NUMERATOR_COUNT,
                    RESIDUAL_NUMERATOR_LIMB,
                    RESIDUAL_DENOMINATOR_SIGN,
                    RESIDUAL_DENOMINATOR_COUNT,
                    RESIDUAL_DENOMINATOR_LIMB,
                ],
            )
        })
        .collect()
}

fn append_string_words(
    words: &mut Vec<CompactWord>,
    coordinates: &[u64],
    length_tag: u64,
    byte_tag: u64,
    value: &str,
) {
    words.push(CompactWord::at(
        length_tag,
        coordinates.to_vec(),
        value.len() as u64,
    ));
    for (at, byte) in value.as_bytes().iter().copied().enumerate() {
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        words.push(CompactWord::at(byte_tag, route, u64::from(byte)));
    }
}

fn decode_string(
    atlas: &CapabilityAtlas,
    root: u64,
    coordinates: &[u64],
    length_tag: u64,
    byte_tag: u64,
) -> Result<String, String> {
    let length = usize::try_from(atlas.word(root, length_tag, coordinates)?).map_err(debug)?;
    let mut bytes = Vec::with_capacity(length);
    for at in 0..length {
        let mut route = coordinates.to_vec();
        route.push(at as u64);
        bytes.push(u8::try_from(atlas.word(root, byte_tag, &route)?).map_err(debug)?);
    }
    String::from_utf8(bytes).map_err(debug)
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

fn orientation_code(value: &str) -> u64 {
    match value {
        "negative" => 1,
        "zero" => 2,
        "positive" => 3,
        _ => 0,
    }
}

fn orientation_from_code(code: u64) -> Result<String, String> {
    match code {
        1 => Ok("negative".to_owned()),
        2 => Ok("zero".to_owned()),
        3 => Ok("positive".to_owned()),
        _ => Err(format!("orientation code {code} is invalid")),
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

fn query_arcs(
    pair: [CurrentLineage; 2],
    current_handle: ArtifactHandle,
    current_words: &[CompactWord],
    ecology_before: ArtifactHandle,
    ecology_after: ArtifactHandle,
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
        InterfaceCapability::new(ecology_before.recruit_namespace, RECRUIT_LOCAL),
        IncidenceHand::Against,
    )?;
    push_interface(
        &mut arcs,
        pair,
        InterfaceCapability::new(ecology_after.recruit_namespace, RECRUIT_LOCAL),
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

#[allow(clippy::too_many_arguments)]
fn profiled_event(
    budget: &RunBudget,
    machine: &mut LiveCurrentMachine,
    executor: &mut ParallelCpuLiveCurrentExecutor,
    event_name: &str,
    semantic_words: usize,
    pair: [CurrentLineage; 2],
    arcs: &[RegionalRelationArc],
    outgoing_factor_slots: Option<&[u32]>,
) -> Result<(soma_membrane::ContemporaryRadiation, Value), String> {
    budget.require_open()?;
    if arcs.len() > MAX_ARCS_PER_EVENT {
        return Err(format!(
            "event {event_name} requires {} arcs, beyond the fixed limit {MAX_ARCS_PER_EVENT}",
            arcs.len()
        ));
    }
    let currents = [
        CurrentEvent::ending(pair[0], relation(181)?, action()),
        CurrentEvent::ending(pair[1], relation(191)?, action()),
    ];
    let regional = [match outgoing_factor_slots {
        Some(slots) => RegionalRelationCell::with_outgoing_factor(pair[1], arcs, slots),
        None => RegionalRelationCell::new(pair[1], arcs),
    }];
    let started = Instant::now();
    let radiation = machine
        .receive_with(
            ContemporaryEvent::with_regional(&currents, &[], &regional),
            executor,
        )
        .map_err(|error| format!("event {event_name}: {error:?}"))?;
    let wall = started.elapsed();
    if wall > EVENT_LIMIT {
        return Err(format!(
            "event {event_name} exceeded its {} second limit",
            EVENT_LIMIT.as_secs()
        ));
    }
    budget.require_open()?;
    let read = json!({
        "event": event_name,
        "semantic_words": semantic_words,
        "regional_arcs": arcs.len(),
        "wall_micros": duration_micros(wall),
        "returned_incidences": radiation.regional().iter().map(|row| row.constituent().incidences().len()).sum::<usize>(),
        "returned_pins": radiation.regional().iter().map(|row| row.constituent().pins().len()).sum::<usize>(),
    });
    Ok((radiation, read))
}

fn primed_pair(
    machine: &mut LiveCurrentMachine,
    executor: &mut ParallelCpuLiveCurrentExecutor,
) -> Result<[CurrentLineage; 2], String> {
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
            .receive_with(ContemporaryEvent::unrelated(&currents), executor)
            .map_err(debug)?;
    }
    Ok(pair)
}

fn regional_constituent<'a>(
    radiation: &'a soma_membrane::ContemporaryRadiation,
    event: &str,
) -> Result<&'a LiveConstituent, String> {
    radiation
        .regional()
        .first()
        .map(|row| row.constituent())
        .ok_or_else(|| format!("{event} returned no regional constituent"))
}

fn standing_ecology(machine: &LiveCurrentMachine, root: u64) -> Result<Ecology, String> {
    let found = machine
        .standing()
        .constituents()
        .iter()
        .filter_map(|constituent| decode_ecology(constituent, root).ok())
        .collect::<Vec<_>>();
    match found.as_slice() {
        [ecology] => Ok(ecology.clone()),
        [] => Err("Standing exposes no derived ecology".to_owned()),
        _ => Err("Standing exposes plural derived ecologies".to_owned()),
    }
}

fn ecology_read(ecology: &Ecology) -> Value {
    json!({
        "generation": ecology.generation,
        "rank": ecology.pivot_factors.len(),
        "pivot_factors": ecology.pivot_factors,
        "receiver_axes": ecology.axes,
        "law_coefficients": ecology.coefficients.iter().flatten().count(),
        "support": ecology.support.iter().map(|entry| json!({
            "operation": entry.operation,
            "context": entry.context,
            "condition": entry.condition,
            "faces": entry.faces.iter().map(|row| json!({
                "face": row.face,
                "count": row.count,
            })).collect::<Vec<_>>(),
        })).collect::<Vec<_>>(),
    })
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
    let rest_octets = machine
        .rest_image()
        .map_err(debug)?
        .encode_native_bytes()
        .map_err(debug)?;
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
    namespace(&[b"eros-parent-open-word-v1", &root.to_le_bytes(), &route])
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
        .ok_or_else(|| format!("relation value {value} remained zero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}

fn usage() -> &'static str {
    "usage: cargo run -p life --example eros_parent_on_open_substitution -- <SOURCE.json> <REPORT.json>"
}
