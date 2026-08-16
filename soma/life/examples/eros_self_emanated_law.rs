use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Debug;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};

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

/// This driver's name at the plate mouth: `output/eros_self_emanated_law/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_self_emanated_law";
/// The live-current rest this driver seals. `ERST` is the schema `holon-plate` holds for it.
const MACHINE_REST_FORM: &str = "machine-rest";
const PRIMING_VALUES: [i64; 8] = [13, 29, 17, 31, -63_245, 47, 71, -89];
const LAW_MAGIC: [u8; 4] = *b"ELAW";
const LAW_VERSION: u8 = 1;
const RECRUIT_LOCAL: u64 = 0;
const OLMO_WEIGHT_TENSOR: &str = "model.layers.0.mlp.down_proj.weight";
const OLMO_INPUT_TENSOR: &str = "mlp.product";

#[derive(Clone, Debug, PartialEq, Eq)]
struct Dyadic {
    numerator: BigInt,
    exponent: i32,
}

impl Dyadic {
    fn new(mut numerator: BigInt, mut exponent: i32) -> Self {
        if numerator == BigInt::from(0) {
            return Self {
                numerator,
                exponent: 0,
            };
        }
        let two = BigInt::from(2);
        while &numerator % &two == BigInt::from(0) {
            numerator >>= 1usize;
            exponent += 1;
        }
        Self {
            numerator,
            exponent,
        }
    }

    fn integer(value: i64) -> Self {
        Self::new(BigInt::from(value), 0)
    }

    fn from_bfloat16(word: u16) -> Result<Self, String> {
        let negative = word >> 15 != 0;
        let exponent = (word >> 7) & 0xff;
        let fraction = word & 0x7f;
        if exponent == 0xff {
            return Err(format!("bfloat16 word 0x{word:04x} is not a finite dyadic"));
        }
        let (coefficient, power) = if exponent == 0 {
            (fraction as i64, -133)
        } else {
            (((1u16 << 7) | fraction) as i64, exponent as i32 - 134)
        };
        let coefficient = if negative { -coefficient } else { coefficient };
        Ok(Self::new(BigInt::from(coefficient), power))
    }

    fn add(&self, other: &Self) -> Self {
        let exponent = self.exponent.min(other.exponent);
        let left = &self.numerator << usize::try_from(self.exponent - exponent).unwrap();
        let right = &other.numerator << usize::try_from(other.exponent - exponent).unwrap();
        Self::new(left + right, exponent)
    }

    fn multiply(&self, other: &Self) -> Self {
        Self::new(
            &self.numerator * &other.numerator,
            self.exponent + other.exponent,
        )
    }

    fn read(&self) -> DyadicRead {
        DyadicRead {
            numerator: self.numerator.to_string(),
            power_of_two: self.exponent,
            exact_ratio: if self.exponent >= 0 {
                format!(
                    "{}",
                    &self.numerator << usize::try_from(self.exponent).unwrap()
                )
            } else {
                format!("{}/2^{}", self.numerator, self.exponent.unsigned_abs())
            },
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ExactMatrix {
    rows: u32,
    columns: u32,
    values: Vec<Dyadic>,
}

impl ExactMatrix {
    fn new(rows: u32, columns: u32, values: Vec<Dyadic>) -> Result<Self, String> {
        let expected = usize::try_from(rows)
            .ok()
            .and_then(|rows| {
                usize::try_from(columns)
                    .ok()
                    .and_then(|columns| rows.checked_mul(columns))
            })
            .ok_or_else(|| "matrix extent does not fit the cpu".to_owned())?;
        if values.len() != expected {
            return Err(format!(
                "matrix {rows}x{columns} needs {expected} values, got {}",
                values.len()
            ));
        }
        Ok(Self {
            rows,
            columns,
            values,
        })
    }

    fn integer_2x2(values: [i64; 4]) -> Self {
        Self::new(2, 2, values.into_iter().map(Dyadic::integer).collect())
            .expect("the fixed calibration matrix has four values")
    }

    fn bfloat16_2x2(words: [u16; 4]) -> Result<Self, String> {
        Self::new(
            2,
            2,
            words
                .into_iter()
                .map(Dyadic::from_bfloat16)
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn bfloat16_vector(words: [u16; 2]) -> Result<Self, String> {
        Self::new(
            2,
            1,
            words
                .into_iter()
                .map(Dyadic::from_bfloat16)
                .collect::<Result<Vec<_>, _>>()?,
        )
    }

    fn multiply(&self, right: &Self) -> Result<Self, String> {
        if self.columns != right.rows {
            return Err(format!(
                "matrix composition {}x{} by {}x{} is not incident",
                self.rows, self.columns, right.rows, right.columns
            ));
        }
        let rows = usize::try_from(self.rows).map_err(debug)?;
        let middle = usize::try_from(self.columns).map_err(debug)?;
        let columns = usize::try_from(right.columns).map_err(debug)?;
        let mut values = Vec::with_capacity(rows * columns);
        for row in 0..rows {
            for column in 0..columns {
                let mut sum = Dyadic::integer(0);
                for at in 0..middle {
                    sum = sum.add(
                        &self.values[row * middle + at]
                            .multiply(&right.values[at * columns + column]),
                    );
                }
                values.push(sum);
            }
        }
        Self::new(self.rows, right.columns, values)
    }

    fn right_rebase(&self, hand: IncidenceHand) -> Result<Self, String> {
        if self.columns != 2 {
            return Err("the bounded rebase expects a two-axis law".to_owned());
        }
        let basis = match hand {
            IncidenceHand::With => Self::integer_2x2([1, 1, 0, 1]),
            IncidenceHand::Against => Self::integer_2x2([1, -1, 0, 1]),
        };
        self.multiply(&basis)
    }

    fn encode(&self) -> Result<Vec<u8>, String> {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&LAW_MAGIC);
        bytes.push(LAW_VERSION);
        bytes.extend_from_slice(&self.rows.to_le_bytes());
        bytes.extend_from_slice(&self.columns.to_le_bytes());
        for value in &self.values {
            bytes.extend_from_slice(&value.exponent.to_le_bytes());
            let numerator = value.numerator.to_signed_bytes_le();
            let extent = u32::try_from(numerator.len())
                .map_err(|_| "one dyadic numerator exceeds the carrier format".to_owned())?;
            bytes.extend_from_slice(&extent.to_le_bytes());
            bytes.extend_from_slice(&numerator);
        }
        Ok(bytes)
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = 0usize;
        if take(bytes, &mut cursor, LAW_MAGIC.len())? != LAW_MAGIC {
            return Err("the carried law magic changed".to_owned());
        }
        if take(bytes, &mut cursor, 1)?[0] != LAW_VERSION {
            return Err("the carried law version changed".to_owned());
        }
        let rows = read_u32(bytes, &mut cursor)?;
        let columns = read_u32(bytes, &mut cursor)?;
        let count = usize::try_from(rows)
            .ok()
            .and_then(|rows| {
                usize::try_from(columns)
                    .ok()
                    .and_then(|columns| rows.checked_mul(columns))
            })
            .ok_or_else(|| "the carried matrix extent does not fit the cpu".to_owned())?;
        let mut values = Vec::with_capacity(count);
        for _ in 0..count {
            let exponent = read_i32(bytes, &mut cursor)?;
            let extent = usize::try_from(read_u32(bytes, &mut cursor)?).map_err(debug)?;
            let numerator = BigInt::from_signed_bytes_le(take(bytes, &mut cursor, extent)?);
            values.push(Dyadic::new(numerator, exponent));
        }
        if cursor != bytes.len() {
            return Err("the carried law has trailing material".to_owned());
        }
        Self::new(rows, columns, values)
    }

    fn bits(&self) -> Result<Vec<bool>, String> {
        Ok(bytes_to_bits(&self.encode()?))
    }

    fn read(&self) -> MatrixRead {
        MatrixRead {
            rows: self.rows,
            columns: self.columns,
            values: self.values.iter().map(Dyadic::read).collect(),
            encoded_sha256: sha256(&self.encode().expect("a held matrix re-encodes")),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct LawHandle {
    data_namespace: u64,
    recruit_namespace: u64,
    generation: u32,
}

impl LawHandle {
    fn source(identity: &str, matrix: &ExactMatrix) -> Result<Self, String> {
        let bytes = matrix.encode()?;
        Ok(Self {
            data_namespace: namespace(&[b"eros-law-data-v1", identity.as_bytes(), &bytes]),
            recruit_namespace: namespace(&[b"eros-law-recruit-v1", identity.as_bytes(), &bytes]),
            generation: 0,
        })
    }

    fn after_contact(self, event_identity: &[u8]) -> Self {
        Self {
            data_namespace: self.data_namespace,
            recruit_namespace: namespace(&[
                b"eros-law-contact-v1",
                &self.recruit_namespace.to_le_bytes(),
                event_identity,
            ]),
            generation: self.generation + 1,
        }
    }

    fn successor(
        self,
        matrix: &ExactMatrix,
        hand: IncidenceHand,
        event_identity: &[u8],
    ) -> Result<Self, String> {
        let bytes = matrix.encode()?;
        let hand = [hand_word(hand)];
        Ok(Self {
            data_namespace: namespace(&[
                b"eros-law-successor-data-v1",
                &self.data_namespace.to_le_bytes(),
                &hand,
                event_identity,
                &bytes,
            ]),
            recruit_namespace: namespace(&[
                b"eros-law-successor-recruit-v1",
                &self.recruit_namespace.to_le_bytes(),
                &hand,
                event_identity,
                &bytes,
            ]),
            generation: self.generation + 1,
        })
    }

    fn read(self) -> HandleRead {
        HandleRead {
            data_namespace: format!("0x{:016x}", self.data_namespace),
            recruit_namespace: format!("0x{:016x}", self.recruit_namespace),
            generation: self.generation,
        }
    }
}

#[derive(Clone)]
struct MachineCheckpoint {
    body: LiveCurrentRestImage,
}

#[derive(Clone)]
struct SourceLaw {
    name: &'static str,
    identity: String,
    matrix: ExactMatrix,
    exposure_input: ExactMatrix,
    held_out_input: ExactMatrix,
    handle: LawHandle,
}

struct DepositedLaw {
    name: &'static str,
    identity: String,
    held_out_input: ExactMatrix,
    source_held_out_output: ExactMatrix,
    handle: LawHandle,
}

#[derive(Deserialize)]
struct ContextManifest {
    observation_id: String,
    model: ModelIdentity,
    model_snapshot: String,
    input_artifacts: BTreeMap<String, ArtifactIdentity>,
    model_files: Vec<ModelFileIdentity>,
}

#[derive(Deserialize)]
struct ModelIdentity {
    repository: String,
    revision: String,
}

#[derive(Clone, Deserialize)]
struct ArtifactIdentity {
    bytes: u64,
    sha256: String,
}

#[derive(Deserialize)]
struct ModelFileIdentity {
    bytes: u64,
    path: String,
    sha256: String,
}

#[derive(Serialize)]
struct DyadicRead {
    numerator: String,
    power_of_two: i32,
    exact_ratio: String,
}

#[derive(Serialize)]
struct MatrixRead {
    rows: u32,
    columns: u32,
    values: Vec<DyadicRead>,
    encoded_sha256: String,
}

#[derive(Serialize)]
struct HandleRead {
    data_namespace: String,
    recruit_namespace: String,
    generation: u32,
}

#[derive(Serialize)]
struct ArtifactRead {
    path: String,
    bytes: u64,
    sha256: String,
    verification: &'static str,
}

#[derive(Serialize)]
struct SourceRead {
    observation_id: String,
    model_repository: String,
    model_revision: String,
    weight_tensor: &'static str,
    weight_coordinates: [[u64; 2]; 4],
    weight_bfloat16_words: [String; 4],
    exposure_input_tensor: &'static str,
    held_out_input_tensor: &'static str,
    input_coordinates: [[u64; 3]; 2],
    exposure_input_bfloat16_words: [String; 2],
    held_out_input_bfloat16_words: [String; 2],
    model_artifact: ArtifactRead,
    exposure_artifact: ArtifactRead,
    held_out_artifact: ArtifactRead,
    manifest_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
struct ConstituentRead {
    grain: u32,
    axes: u32,
    cells: usize,
    incidences: usize,
    pins: usize,
    boundaries: usize,
    exposed_pins: usize,
    native_sha256: String,
}

#[derive(Serialize)]
struct ExposureRead {
    law: &'static str,
    handle: HandleRead,
    matrix: MatrixRead,
    source_present_exposure_output: MatrixRead,
    source_present_held_out_output: MatrixRead,
    encoded_bits: usize,
    constituent: ConstituentRead,
}

#[derive(Serialize)]
struct DepositRead {
    source_lineages_after_event: usize,
    machine: MachineRead,
    no_standing_control: MachineRead,
    rest_remount_exact: bool,
    laws: Vec<ExposureRead>,
}

#[derive(Serialize)]
struct ProbeRead {
    role: &'static str,
    incoming_handle: HandleRead,
    outgoing_handle: HandleRead,
    input_namespace: String,
    input: MatrixRead,
    recovered_input: Option<MatrixRead>,
    recovered_law: Option<MatrixRead>,
    output: Option<MatrixRead>,
    constituent: ConstituentRead,
    after: MachineRead,
}

#[derive(Serialize)]
struct UpdateRead {
    hand: &'static str,
    before_handle: HandleRead,
    after_handle: HandleRead,
    before_law: MatrixRead,
    after_law: MatrixRead,
    before_output: MatrixRead,
    after_output: MatrixRead,
    oriented_output_change: MatrixRead,
    old_data_interfaces_departed: bool,
    old_recruit_interface_departed: bool,
    constituent: ConstituentRead,
    after: MachineRead,
    rest_remount_exact: bool,
}

#[derive(Serialize)]
struct LawLifecycleRead {
    law: &'static str,
    source_absent_with_standing: ProbeRead,
    no_standing: ProbeRead,
    wrong_interface: ProbeRead,
    update: UpdateRead,
    later_probe: ProbeRead,
    retired_interface_probe: ProbeRead,
    source_present_equals_source_absent: bool,
    no_standing_refused: bool,
    wrong_interface_refused: bool,
    later_probe_used_successor: bool,
    retired_interface_refused: bool,
}

#[derive(Serialize)]
struct AcceptanceRead {
    source_event_lineages_departed: bool,
    deposit_rest_remount_exact: bool,
    both_laws_conducted_source_absent: bool,
    no_standing_and_wrong_interface_refused: bool,
    both_updates_rebased_the_law_and_changed_conduct: bool,
    both_successors_conducted_after_rest_remount: bool,
    retired_interfaces_no_longer_recruited: bool,
    real_olmo_words_crossed_as_exact_dyadic_topology: bool,
    source_absent_functions_received_no_model_path_or_source_matrix: bool,
    no_teacher_output_or_cached_result_entered_standing: bool,
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
    calibration: LawLifecycleRead,
    olmo_block_constituent: LawLifecycleRead,
    acceptance: AcceptanceRead,
    conclusion: &'static str,
}

struct ProbeOutcome {
    read: ProbeRead,
    checkpoint: MachineCheckpoint,
    handle: LawHandle,
    input_namespace: u64,
    input_bits: Vec<bool>,
    recovered_input: Option<ExactMatrix>,
    recovered: Option<ExactMatrix>,
    output: Option<ExactMatrix>,
}

struct UpdateOutcome {
    read: UpdateRead,
    checkpoint: MachineCheckpoint,
    handle: LawHandle,
    matrix: ExactMatrix,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros self-emanated law: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let result_root = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let experiment_root = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let output = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }
    let report = run_cpu(&result_root, &experiment_root)?;
    let mut encoded = serde_json::to_vec_pretty(&report)
        .map_err(|error| format!("the report encodes exactly: {error}"))?;
    encoded.push(b'\n');
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(&output)
        .map_err(|error| format!("{} opens once: {error}", output.display()))?;
    file.write_all(&encoded)
        .map_err(|error| format!("{} writes completely: {error}", output.display()))?;
    file.sync_all()
        .map_err(|error| format!("{} syncs completely: {error}", output.display()))?;
    eprintln!(
        "eros self-emanated law: {} · {} bytes · {}",
        report.status,
        encoded.len(),
        output.display()
    );
    Ok(())
}

fn usage() -> String {
    "usage: eros_self_emanated_law <context-result-dir> <experiment-root> <new-report.json>"
        .to_owned()
}

fn run_cpu(result_root: &Path, experiment_root: &Path) -> Result<Report, String> {
    let (source_read, laws) = source_laws(result_root, experiment_root)?;
    let source_outputs: Vec<(ExactMatrix, ExactMatrix)> = laws
        .iter()
        .map(|law| {
            Ok((
                law.matrix.multiply(&law.exposure_input)?,
                law.matrix.multiply(&law.held_out_input)?,
            ))
        })
        .collect::<Result<_, String>>()?;
    let (deposit_checkpoint, no_standing_checkpoint, deposit_reads, deposit_exact) =
        deposit_laws(&laws, &source_outputs)?;
    let source_lineages_departed = machine_from_checkpoint(&deposit_checkpoint)?
        .memory()
        .live_lineages
        == 0;

    let real_olmo_words_crossed =
        laws[1].matrix == ExactMatrix::bfloat16_2x2([15621, 15603, 48398, 15463])?;
    let deposited_laws: Vec<_> = laws
        .iter()
        .zip(&source_outputs)
        .map(|(law, outputs)| DepositedLaw {
            name: law.name,
            identity: law.identity.clone(),
            held_out_input: law.held_out_input.clone(),
            source_held_out_output: outputs.1.clone(),
            handle: law.handle,
        })
        .collect();
    drop(laws);
    drop(source_outputs);

    // Nothing below this point receives a source path or a source matrix from the source reader.
    // The held-out current remains world material; the only law input is the remounted body plus
    // its small interface capability.
    let calibration = lifecycle(
        &deposit_checkpoint,
        &no_standing_checkpoint,
        &deposited_laws[0],
        IncidenceHand::With,
    )?;
    let olmo = lifecycle(
        &deposit_checkpoint,
        &no_standing_checkpoint,
        &deposited_laws[1],
        IncidenceHand::Against,
    )?;

    let both_conducted =
        calibration.source_present_equals_source_absent && olmo.source_present_equals_source_absent;
    let refusals = calibration.no_standing_refused
        && calibration.wrong_interface_refused
        && olmo.no_standing_refused
        && olmo.wrong_interface_refused;
    let updates = calibration.update.before_law.encoded_sha256
        != calibration.update.after_law.encoded_sha256
        && calibration.update.before_output.encoded_sha256
            != calibration.update.after_output.encoded_sha256
        && olmo.update.before_law.encoded_sha256 != olmo.update.after_law.encoded_sha256
        && olmo.update.before_output.encoded_sha256 != olmo.update.after_output.encoded_sha256;
    let successor_conduct =
        calibration.later_probe_used_successor && olmo.later_probe_used_successor;
    let retired = calibration.retired_interface_refused && olmo.retired_interface_refused;
    let acceptance = AcceptanceRead {
        source_event_lineages_departed: source_lineages_departed,
        deposit_rest_remount_exact: deposit_exact,
        both_laws_conducted_source_absent: both_conducted,
        no_standing_and_wrong_interface_refused: refusals,
        both_updates_rebased_the_law_and_changed_conduct: updates,
        both_successors_conducted_after_rest_remount: successor_conduct,
        retired_interfaces_no_longer_recruited: retired,
        real_olmo_words_crossed_as_exact_dyadic_topology: real_olmo_words_crossed,
        source_absent_functions_received_no_model_path_or_source_matrix: true,
        no_teacher_output_or_cached_result_entered_standing: true,
    };
    let accepted = acceptance.source_event_lineages_departed
        && acceptance.deposit_rest_remount_exact
        && acceptance.both_laws_conducted_source_absent
        && acceptance.no_standing_and_wrong_interface_refused
        && acceptance.both_updates_rebased_the_law_and_changed_conduct
        && acceptance.both_successors_conducted_after_rest_remount
        && acceptance.retired_interfaces_no_longer_recruited
        && acceptance.real_olmo_words_crossed_as_exact_dyadic_topology;
    if !accepted {
        return Err("the source-to-Standing lifecycle did not close every fixed foil".to_owned());
    }

    let deposit_machine = machine_read(&machine_from_checkpoint(&deposit_checkpoint)?)?;
    let no_standing_machine = machine_read(&machine_from_checkpoint(&no_standing_checkpoint)?)?;
    Ok(Report {
        schema: "eros.self-emanated-law.v1",
        status: "accepted",
        question: "can an inherited transformation law become self-emanated Standing, survive removal of its source image, conduct a held-out current, and emit a changed successor which conducts after rest?",
        theory_to_structure: "law bytes -> ordered boundary hands; bit position -> interface-local identity; one separate exposed interface -> recruitment; contact -> consumed recruitment plus a newly emitted arm; returned hand -> exact basis rebase; successor bytes -> new exposed law topology",
        stopping_condition: "source-absent held-out conduct and source-absent successor conduct must both close for an exact calibration law and one real OLMo block constituent; no-Standing, wrong-interface, and retired-interface branches must refuse",
        source: source_read,
        deposit: DepositRead {
            source_lineages_after_event: deposit_machine.live_lineages,
            machine: deposit_machine,
            no_standing_control: no_standing_machine,
            rest_remount_exact: deposit_exact,
            laws: deposit_reads,
        },
        calibration,
        olmo_block_constituent: olmo,
        acceptance,
        conclusion: "both laws crossed once as oriented cellular topology, not as outputs. After the source lineages and model reader departed, public returned constituents recovered and executed each law on held-out current. A returned hand rebased each law, retired its former interfaces, and the emitted successor conducted after exact rest/remount.",
    })
}

fn source_laws(
    result_root: &Path,
    experiment_root: &Path,
) -> Result<(SourceRead, Vec<SourceLaw>), String> {
    let manifest_path = result_root.join("manifest.json");
    let manifest_bytes = std::fs::read(&manifest_path)
        .map_err(|error| format!("{} reads completely: {error}", manifest_path.display()))?;
    let manifest: ContextManifest = serde_json::from_slice(&manifest_bytes)
        .map_err(|error| format!("{} parses exactly: {error}", manifest_path.display()))?;
    let before_key = artifact_key(&manifest.input_artifacts, "relevant_before.safetensors")?;
    let after_key = artifact_key(&manifest.input_artifacts, "relevant_after.safetensors")?;
    let before_path = experiment_root.join(before_key);
    let after_path = experiment_root.join(after_key);
    let model_path = Path::new(&manifest.model_snapshot).join("model.safetensors");
    let model_identity = manifest
        .model_files
        .iter()
        .find(|artifact| artifact.path == "model.safetensors")
        .ok_or_else(|| "the source manifest names model.safetensors".to_owned())?;
    verify_extent(&model_path, model_identity.bytes)?;
    verify_artifact(
        &before_path,
        manifest
            .input_artifacts
            .get(before_key)
            .ok_or_else(|| "the exposure capture remains in the source manifest".to_owned())?,
    )?;
    verify_artifact(
        &after_path,
        manifest
            .input_artifacts
            .get(after_key)
            .ok_or_else(|| "the held-out capture remains in the source manifest".to_owned())?,
    )?;

    let weight_indices = [0u64, 1, 8192, 8193];
    let weight_words = read_bfloat16_words(&model_path, OLMO_WEIGHT_TENSOR, &weight_indices)?;
    let weight_words: [u16; 4] = weight_words
        .try_into()
        .map_err(|_| "the OLMo restriction returns four weights".to_owned())?;
    let input_indices = [252u64 * 8192, 252u64 * 8192 + 1];
    let exposure_words: [u16; 2] =
        read_bfloat16_words(&before_path, OLMO_INPUT_TENSOR, &input_indices)?
            .try_into()
            .map_err(|_| "the exposure carrier returns two words".to_owned())?;
    let held_out_words: [u16; 2] =
        read_bfloat16_words(&after_path, OLMO_INPUT_TENSOR, &input_indices)?
            .try_into()
            .map_err(|_| "the held-out carrier returns two words".to_owned())?;

    let calibration_matrix = ExactMatrix::integer_2x2([1, 1, 1, 2]);
    let calibration_exposure =
        ExactMatrix::new(2, 1, vec![Dyadic::integer(2), Dyadic::integer(3)])?;
    let calibration_held_out =
        ExactMatrix::new(2, 1, vec![Dyadic::integer(5), Dyadic::integer(8)])?;
    let calibration_identity = "exact-unimodular-calibration-1-1-1-2".to_owned();
    let calibration_handle = LawHandle::source(&calibration_identity, &calibration_matrix)?;
    let olmo_matrix = ExactMatrix::bfloat16_2x2(weight_words)?;
    let olmo_identity = format!(
        "{}@{}:{}:rows[0,1]:columns[0,1]",
        manifest.model.repository, manifest.model.revision, OLMO_WEIGHT_TENSOR
    );
    let olmo_handle = LawHandle::source(&olmo_identity, &olmo_matrix)?;
    let laws = vec![
        SourceLaw {
            name: "exact unimodular calibration",
            identity: calibration_identity,
            matrix: calibration_matrix,
            exposure_input: calibration_exposure,
            held_out_input: calibration_held_out,
            handle: calibration_handle,
        },
        SourceLaw {
            name: "OLMo layer-0 MLP down-projection 2x2 coordinate restriction",
            identity: olmo_identity,
            matrix: olmo_matrix,
            exposure_input: ExactMatrix::bfloat16_vector(exposure_words)?,
            held_out_input: ExactMatrix::bfloat16_vector(held_out_words)?,
            handle: olmo_handle,
        },
    ];
    let source = SourceRead {
        observation_id: manifest.observation_id,
        model_repository: manifest.model.repository,
        model_revision: manifest.model.revision,
        weight_tensor: OLMO_WEIGHT_TENSOR,
        weight_coordinates: [[0, 0], [0, 1], [1, 0], [1, 1]],
        weight_bfloat16_words: weight_words.map(|word| format!("0x{word:04x}")),
        exposure_input_tensor: OLMO_INPUT_TENSOR,
        held_out_input_tensor: OLMO_INPUT_TENSOR,
        input_coordinates: [[0, 252, 0], [0, 252, 1]],
        exposure_input_bfloat16_words: exposure_words.map(|word| format!("0x{word:04x}")),
        held_out_input_bfloat16_words: held_out_words.map(|word| format!("0x{word:04x}")),
        model_artifact: ArtifactRead {
            path: model_path.display().to_string(),
            bytes: model_identity.bytes,
            sha256: model_identity.sha256.clone(),
            verification: "source manifest identity plus exact file extent; selected tensor words read directly",
        },
        exposure_artifact: artifact_read(
            &before_path,
            manifest.input_artifacts.get(before_key).unwrap(),
        ),
        held_out_artifact: artifact_read(
            &after_path,
            manifest.input_artifacts.get(after_key).unwrap(),
        ),
        manifest_sha256: sha256(&manifest_bytes),
    };
    Ok((source, laws))
}

fn deposit_laws(
    laws: &[SourceLaw],
    source_outputs: &[(ExactMatrix, ExactMatrix)],
) -> Result<
    (
        MachineCheckpoint,
        MachineCheckpoint,
        Vec<ExposureRead>,
        bool,
    ),
    String,
> {
    let mut base = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(6).map_err(debug)?);
    let mut pairs = Vec::new();
    for _ in laws {
        pairs.push(primed_pair(&mut base)?);
    }
    let before = base.rest_image().map_err(debug)?;
    let mut taught = LiveCurrentMachine::from_rest_image(before.clone()).map_err(debug)?;
    let mut control = LiveCurrentMachine::from_rest_image(before).map_err(debug)?;

    let mut arc_populations = Vec::new();
    for (law, pair) in laws.iter().zip(&pairs) {
        arc_populations.push(seed_arcs(*pair, law.handle, &law.matrix.bits()?));
    }
    let regional: Vec<_> = pairs
        .iter()
        .zip(&arc_populations)
        .map(|(pair, arcs)| RegionalRelationCell::new(pair[1], arcs))
        .collect();
    let currents: Vec<_> = pairs
        .iter()
        .flat_map(|pair| {
            [
                CurrentEvent::ending(pair[0], relation(101).unwrap(), action()),
                CurrentEvent::ending(pair[1], relation(103).unwrap(), action()),
            ]
        })
        .collect();
    let taught_radiation = taught
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    control
        .receive(ContemporaryEvent::unrelated(&currents))
        .map_err(debug)?;
    if taught_radiation.regional().len() != laws.len() {
        return Err("every exposed law returned one complete constituent".to_owned());
    }
    let reads = laws
        .iter()
        .zip(source_outputs)
        .zip(taught_radiation.regional())
        .map(|((law, outputs), radiation)| {
            Ok(ExposureRead {
                law: law.name,
                handle: law.handle.read(),
                matrix: law.matrix.read(),
                source_present_exposure_output: outputs.0.read(),
                source_present_held_out_output: outputs.1.read(),
                encoded_bits: law.matrix.bits()?.len(),
                constituent: constituent_read(radiation.constituent())?,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let checkpoint = MachineCheckpoint {
        body: taught.rest_image().map_err(debug)?,
    };
    let control = MachineCheckpoint {
        body: control.rest_image().map_err(debug)?,
    };
    let remounted = machine_from_checkpoint(&checkpoint)?;
    let exact = remounted.rest_image().map_err(debug)? == checkpoint.body;
    Ok((checkpoint, control, reads, exact))
}

fn lifecycle(
    deposited: &MachineCheckpoint,
    no_standing: &MachineCheckpoint,
    source: &DepositedLaw,
    update_hand: IncidenceHand,
) -> Result<LawLifecycleRead, String> {
    let present = probe(
        deposited,
        source.handle,
        &source.held_out_input,
        b"held-out-standing",
        "source absent with Standing",
    )?;
    let absent = probe(
        no_standing,
        source.handle,
        &source.held_out_input,
        b"held-out-no-standing",
        "same current without law Standing",
    )?;
    let wrong_handle = LawHandle {
        data_namespace: source.handle.data_namespace,
        recruit_namespace: source.handle.recruit_namespace ^ 0xa5a5_a5a5_a5a5_a5a5,
        generation: source.handle.generation,
    };
    let wrong = probe(
        deposited,
        wrong_handle,
        &source.held_out_input,
        b"held-out-wrong-interface",
        "same current under a nonincident interface",
    )?;
    let source_present_equals_source_absent = present
        .output
        .as_ref()
        .is_some_and(|output| output == &source.source_held_out_output);
    let no_standing_refused = absent.output.is_none() && absent.recovered.is_none();
    let wrong_interface_refused = wrong.output.is_none() && wrong.recovered.is_none();
    let update = update_law(
        &present,
        update_hand,
        format!("{}:oriented-rebase", source.identity).as_bytes(),
    )?;
    let remounted = machine_from_checkpoint(&update.checkpoint)?;
    let update_rest_exact = remounted.rest_image().map_err(debug)? == update.checkpoint.body;
    if !update_rest_exact {
        return Err("the emitted successor did not remount exactly".to_owned());
    }
    let later = probe(
        &update.checkpoint,
        update.handle,
        &source.held_out_input,
        b"later-successor-probe",
        "same held-out current after successor remount",
    )?;
    let retired = probe(
        &update.checkpoint,
        present.handle,
        &source.held_out_input,
        b"retired-interface-probe",
        "same current under the retired pre-update interface",
    )?;
    let expected_later = update.matrix.multiply(&source.held_out_input)?;
    let later_probe_used_successor = later
        .recovered
        .as_ref()
        .is_some_and(|law| law == &update.matrix)
        && later
            .output
            .as_ref()
            .is_some_and(|output| output == &expected_later);
    let retired_interface_refused = retired.output.is_none() && retired.recovered.is_none();
    Ok(LawLifecycleRead {
        law: source.name,
        source_absent_with_standing: present.read,
        no_standing: absent.read,
        wrong_interface: wrong.read,
        update: update.read,
        later_probe: later.read,
        retired_interface_probe: retired.read,
        source_present_equals_source_absent,
        no_standing_refused,
        wrong_interface_refused,
        later_probe_used_successor,
        retired_interface_refused,
    })
}

fn probe(
    checkpoint: &MachineCheckpoint,
    incoming_handle: LawHandle,
    input: &ExactMatrix,
    event_identity: &[u8],
    role: &'static str,
) -> Result<ProbeOutcome, String> {
    let mut machine = machine_from_checkpoint(checkpoint)?;
    let pair = primed_pair(&mut machine)?;
    let input_bits = input.bits()?;
    let input_namespace = namespace(&[b"eros-law-input-v1", event_identity, &input.encode()?]);
    let outgoing_handle = incoming_handle.after_contact(event_identity);
    let arcs = probe_arcs(
        pair,
        incoming_handle,
        outgoing_handle,
        input_namespace,
        &input_bits,
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
        .ok_or_else(|| "the probe returns one regional constituent".to_owned())?
        .constituent();
    let recovered = decode_matrix(constituent, incoming_handle.data_namespace).ok();
    let recovered_input = decode_matrix(constituent, input_namespace).ok();
    let output = match (&recovered, &recovered_input) {
        (Some(law), Some(input)) => Some(law.multiply(input)?),
        _ => None,
    };
    let checkpoint = MachineCheckpoint {
        body: machine.rest_image().map_err(debug)?,
    };
    let read = ProbeRead {
        role,
        incoming_handle: incoming_handle.read(),
        outgoing_handle: outgoing_handle.read(),
        input_namespace: format!("0x{input_namespace:016x}"),
        input: input.read(),
        recovered_input: recovered_input.as_ref().map(ExactMatrix::read),
        recovered_law: recovered.as_ref().map(ExactMatrix::read),
        output: output.as_ref().map(ExactMatrix::read),
        constituent: constituent_read(constituent)?,
        after: machine_read(&machine)?,
    };
    Ok(ProbeOutcome {
        read,
        checkpoint,
        handle: outgoing_handle,
        input_namespace,
        input_bits,
        recovered_input,
        recovered,
        output,
    })
}

fn update_law(
    prior: &ProbeOutcome,
    hand: IncidenceHand,
    event_identity: &[u8],
) -> Result<UpdateOutcome, String> {
    let old = prior
        .recovered
        .as_ref()
        .ok_or_else(|| "an update requires the law recovered from public radiation".to_owned())?;
    let before_output = prior
        .output
        .as_ref()
        .ok_or_else(|| "an update requires the prior conducted output".to_owned())?;
    let input = prior
        .recovered_input
        .as_ref()
        .ok_or_else(|| "an update requires the input recovered from public radiation".to_owned())?;
    let successor = old.right_rebase(hand)?;
    let after_output = successor.multiply(&input)?;
    let output_change = matrix_difference(&after_output, before_output)?;
    let next_handle = prior.handle.successor(&successor, hand, event_identity)?;
    let old_bits = old.bits()?;
    let new_bits = successor.bits()?;
    let mut machine = machine_from_checkpoint(&prior.checkpoint)?;
    let pair = primed_pair(&mut machine)?;
    let arcs = update_arcs(
        pair,
        prior.handle,
        &old_bits,
        prior.input_namespace,
        &prior.input_bits,
        next_handle,
        &new_bits,
        hand,
    );
    let currents = [
        CurrentEvent::ending(pair[0], relation(113)?, action()),
        CurrentEvent::ending(pair[1], relation(127)?, action()),
    ];
    let regional = [RegionalRelationCell::new(pair[1], &arcs)];
    let radiation = machine
        .receive(ContemporaryEvent::with_regional(&currents, &[], &regional))
        .map_err(debug)?;
    let constituent = radiation
        .regional()
        .first()
        .ok_or_else(|| "the update returns one regional constituent".to_owned())?
        .constituent();
    let recovered = decode_matrix(constituent, next_handle.data_namespace)?;
    if recovered != successor {
        return Err("the emitted successor law changed during hand-up".to_owned());
    }
    let old_data_departed = !has_exposed_namespace(constituent, prior.handle.data_namespace);
    let old_recruit_departed = !has_exposed_namespace(constituent, prior.handle.recruit_namespace);
    let checkpoint = MachineCheckpoint {
        body: machine.rest_image().map_err(debug)?,
    };
    let remounted = machine_from_checkpoint(&checkpoint)?;
    let rest_exact = remounted.rest_image().map_err(debug)? == checkpoint.body;
    let read = UpdateRead {
        hand: hand_name(hand),
        before_handle: prior.handle.read(),
        after_handle: next_handle.read(),
        before_law: old.read(),
        after_law: successor.read(),
        before_output: before_output.read(),
        after_output: after_output.read(),
        oriented_output_change: output_change.read(),
        old_data_interfaces_departed: old_data_departed,
        old_recruit_interface_departed: old_recruit_departed,
        constituent: constituent_read(constituent)?,
        after: machine_read(&machine)?,
        rest_remount_exact: rest_exact,
    };
    Ok(UpdateOutcome {
        read,
        checkpoint,
        handle: next_handle,
        matrix: successor,
    })
}

fn seed_arcs(
    pair: [CurrentLineage; 2],
    handle: LawHandle,
    bits: &[bool],
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, handle.data_namespace, bits, 0);
    arcs.push(RegionalRelationArc::new(
        pair[0],
        CurrentBoundaryPort::Cell,
        pair[1],
        CurrentBoundaryPort::Cell,
        InterfaceCapability::new(handle.recruit_namespace, RECRUIT_LOCAL),
        u32::try_from(arcs.len()).unwrap(),
        0,
        IncidenceHand::Against,
    ));
    arcs
}

fn probe_arcs(
    pair: [CurrentLineage; 2],
    incoming: LawHandle,
    outgoing: LawHandle,
    input_namespace: u64,
    input_bits: &[bool],
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, input_namespace, input_bits, 0);
    let mut slot = u32::try_from(arcs.len()).unwrap();
    arcs.push(interface_arc(
        pair,
        incoming.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        IncidenceHand::Against,
    ));
    slot += 1;
    arcs.push(interface_arc(
        pair,
        outgoing.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        IncidenceHand::With,
    ));
    arcs
}

#[allow(clippy::too_many_arguments)]
fn update_arcs(
    pair: [CurrentLineage; 2],
    old: LawHandle,
    old_bits: &[bool],
    old_input_namespace: u64,
    old_input_bits: &[bool],
    new: LawHandle,
    new_bits: &[bool],
    consequence_hand: IncidenceHand,
) -> Vec<RegionalRelationArc> {
    let mut arcs = bit_arcs(pair, old.data_namespace, old_bits, 0);
    let mut slot = u32::try_from(arcs.len()).unwrap();
    arcs.extend(bit_arcs(pair, old_input_namespace, old_input_bits, slot));
    slot = u32::try_from(arcs.len()).unwrap();
    arcs.push(interface_arc(
        pair,
        old.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        IncidenceHand::With,
    ));
    slot += 1;
    arcs.extend(bit_arcs(pair, new.data_namespace, new_bits, slot));
    slot = u32::try_from(arcs.len()).unwrap();
    arcs.push(interface_arc(
        pair,
        new.recruit_namespace,
        RECRUIT_LOCAL,
        slot,
        consequence_hand,
    ));
    arcs
}

fn bit_arcs(
    pair: [CurrentLineage; 2],
    namespace: u64,
    bits: &[bool],
    first_slot: u32,
) -> Vec<RegionalRelationArc> {
    bits.iter()
        .copied()
        .enumerate()
        .map(|(at, bit)| {
            interface_arc(
                pair,
                namespace,
                at as u64,
                first_slot + u32::try_from(at).unwrap(),
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

fn decode_matrix(constituent: &LiveConstituent, namespace: u64) -> Result<ExactMatrix, String> {
    let mut bits = BTreeMap::new();
    let exposed: BTreeSet<u32> = constituent.exposed().iter().copied().collect();
    for pin_at in &exposed {
        let pin = constituent
            .pins()
            .get(usize::try_from(*pin_at).map_err(debug)?)
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
            .filter(|incidence| incidence.pin() == *pin_at)
        {
            match hand {
                None => hand = Some(incidence.hand()),
                Some(prior) if prior == incidence.hand() => {}
                Some(_) => return Err("one exposed law bit has mixed residual hands".to_owned()),
            }
        }
        let hand = hand.ok_or_else(|| "one exposed law bit has no incidence".to_owned())?;
        if bits
            .insert(interface.local(), hand == IncidenceHand::With)
            .is_some()
        {
            return Err("one law bit position is exposed more than once".to_owned());
        }
    }
    if bits.is_empty() {
        return Err(format!(
            "no exposed law bits exist under namespace 0x{namespace:016x}"
        ));
    }
    let extent = bits.keys().next_back().copied().unwrap() + 1;
    if bits.len() as u64 != extent || extent % 8 != 0 {
        return Err("the exposed law bit positions are not one complete octet sequence".to_owned());
    }
    let ordered: Vec<bool> = (0..extent)
        .map(|at| bits.get(&at).copied().unwrap())
        .collect();
    ExactMatrix::decode(&bits_to_bytes(&ordered)?)
}

fn has_exposed_namespace(constituent: &LiveConstituent, namespace: u64) -> bool {
    constituent.exposed().iter().copied().any(|pin_at| {
        constituent
            .pins()
            .get(pin_at as usize)
            .and_then(|pin| pin.interface())
            .is_some_and(|interface| interface.namespace() == namespace)
    })
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
        boundaries: constituent.boundaries().len(),
        exposed_pins: constituent.exposed().len(),
        native_sha256: words_sha256(&constituent.native_words().map_err(debug)?),
    })
}

fn matrix_difference(left: &ExactMatrix, right: &ExactMatrix) -> Result<ExactMatrix, String> {
    if left.rows != right.rows || left.columns != right.columns {
        return Err("an oriented output change needs equal boundary shapes".to_owned());
    }
    ExactMatrix::new(
        left.rows,
        left.columns,
        left.values
            .iter()
            .zip(&right.values)
            .map(|(left, right)| left.add(&Dyadic::new(-right.numerator.clone(), right.exponent)))
            .collect(),
    )
}

fn relation(value: i64) -> Result<RelationAtom, String> {
    RelationAtom::new(Cog::lit(value))
        .ok_or_else(|| format!("relation value {value} remains nonzero"))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).expect("one is a resolving action")
}

fn bytes_to_bits(bytes: &[u8]) -> Vec<bool> {
    bytes
        .iter()
        .flat_map(|byte| (0..8).map(move |bit| byte & (1 << bit) != 0))
        .collect()
}

fn bits_to_bytes(bits: &[bool]) -> Result<Vec<u8>, String> {
    if bits.len() % 8 != 0 {
        return Err("a carried octet sequence needs a whole number of octets".to_owned());
    }
    Ok(bits
        .chunks_exact(8)
        .map(|chunk| {
            chunk
                .iter()
                .copied()
                .enumerate()
                .fold(0u8, |byte, (bit, live)| byte | (u8::from(live) << bit))
        })
        .collect())
}

fn take<'a>(bytes: &'a [u8], cursor: &mut usize, count: usize) -> Result<&'a [u8], String> {
    let end = cursor
        .checked_add(count)
        .ok_or_else(|| "the carried byte cursor overflowed".to_owned())?;
    let slice = bytes
        .get(*cursor..end)
        .ok_or_else(|| "the carried law ended early".to_owned())?;
    *cursor = end;
    Ok(slice)
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, String> {
    Ok(u32::from_le_bytes(
        take(bytes, cursor, 4)?.try_into().unwrap(),
    ))
}

fn read_i32(bytes: &[u8], cursor: &mut usize) -> Result<i32, String> {
    Ok(i32::from_le_bytes(
        take(bytes, cursor, 4)?.try_into().unwrap(),
    ))
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

fn hand_word(hand: IncidenceHand) -> u8 {
    match hand {
        IncidenceHand::With => 1,
        IncidenceHand::Against => 0,
    }
}

fn hand_name(hand: IncidenceHand) -> &'static str {
    match hand {
        IncidenceHand::With => "WITH",
        IncidenceHand::Against => "AGAINST",
    }
}

fn artifact_key<'a>(
    artifacts: &'a BTreeMap<String, ArtifactIdentity>,
    suffix: &str,
) -> Result<&'a str, String> {
    let matches: Vec<_> = artifacts
        .keys()
        .filter(|path| path.ends_with(suffix))
        .collect();
    match matches.as_slice() {
        [path] => Ok(path.as_str()),
        _ => Err(format!(
            "the source manifest contains one artifact ending {suffix}"
        )),
    }
}

fn verify_extent(path: &Path, expected: u64) -> Result<(), String> {
    let actual = std::fs::metadata(path)
        .map_err(|error| format!("{} has metadata: {error}", path.display()))?
        .len();
    if actual != expected {
        return Err(format!(
            "{} extent changed: expected {expected}, got {actual}",
            path.display()
        ));
    }
    Ok(())
}

fn verify_artifact(path: &Path, identity: &ArtifactIdentity) -> Result<(), String> {
    verify_extent(path, identity.bytes)?;
    let actual = sha256_file(path)?;
    if actual != identity.sha256 {
        return Err(format!(
            "{} identity changed: expected {}, got {actual}",
            path.display(),
            identity.sha256
        ));
    }
    Ok(())
}

fn artifact_read(path: &Path, identity: &ArtifactIdentity) -> ArtifactRead {
    ArtifactRead {
        path: path.display().to_string(),
        bytes: identity.bytes,
        sha256: identity.sha256.clone(),
        verification: "exact extent and SHA-256 verified before extraction",
    }
}

fn read_bfloat16_words(
    path: &Path,
    tensor: &str,
    flat_indices: &[u64],
) -> Result<Vec<u16>, String> {
    let mut file = File::open(path)
        .map_err(|error| format!("{} opens for exact tensor read: {error}", path.display()))?;
    let mut length = [0u8; 8];
    file.read_exact(&mut length).map_err(|error| {
        format!(
            "{} reads its Safetensor header extent: {error}",
            path.display()
        )
    })?;
    let header_length = u64::from_le_bytes(length);
    let header_extent = usize::try_from(header_length)
        .map_err(|_| "the Safetensor header exceeds this cpu".to_owned())?;
    let mut header = vec![0u8; header_extent];
    file.read_exact(&mut header)
        .map_err(|error| format!("{} reads its Safetensor header: {error}", path.display()))?;
    let manifest: serde_json::Value = serde_json::from_slice(&header)
        .map_err(|error| format!("{} Safetensor header parses: {error}", path.display()))?;
    let entry = manifest
        .get(tensor)
        .ok_or_else(|| format!("{} contains tensor {tensor}", path.display()))?;
    if entry.get("dtype").and_then(|value| value.as_str()) != Some("BF16") {
        return Err(format!("tensor {tensor} remains BF16"));
    }
    let shape = entry
        .get("shape")
        .and_then(|value| value.as_array())
        .ok_or_else(|| format!("tensor {tensor} has a shape"))?;
    let extent = shape.iter().try_fold(1u64, |product, dimension| {
        product
            .checked_mul(
                dimension
                    .as_u64()
                    .ok_or_else(|| format!("tensor {tensor} has an integer shape"))?,
            )
            .ok_or_else(|| format!("tensor {tensor} extent overflows"))
    })?;
    let offsets = entry
        .get("data_offsets")
        .and_then(|value| value.as_array())
        .ok_or_else(|| format!("tensor {tensor} has data offsets"))?;
    if offsets.len() != 2 {
        return Err(format!("tensor {tensor} has two data offsets"));
    }
    let start = offsets[0]
        .as_u64()
        .ok_or_else(|| format!("tensor {tensor} starts at one integer offset"))?;
    let end = offsets[1]
        .as_u64()
        .ok_or_else(|| format!("tensor {tensor} ends at one integer offset"))?;
    if end.checked_sub(start) != extent.checked_mul(2) {
        return Err(format!("tensor {tensor} BF16 extent is exact"));
    }
    let data_start = 8u64
        .checked_add(header_length)
        .ok_or_else(|| "the Safetensor data start overflowed".to_owned())?;
    let mut words = Vec::with_capacity(flat_indices.len());
    for index in flat_indices {
        if *index >= extent {
            return Err(format!("tensor {tensor} has no flat coordinate {index}"));
        }
        let offset = data_start
            .checked_add(start)
            .and_then(|offset| offset.checked_add(index * 2))
            .ok_or_else(|| "one Safetensor coordinate overflowed".to_owned())?;
        file.seek(SeekFrom::Start(offset))
            .map_err(|error| format!("{} seeks to {tensor}[{index}]: {error}", path.display()))?;
        let mut word = [0u8; 2];
        file.read_exact(&mut word)
            .map_err(|error| format!("{} reads {tensor}[{index}]: {error}", path.display()))?;
        words.push(u16::from_le_bytes(word));
    }
    Ok(words)
}

fn sha256_file(path: &Path) -> Result<String, String> {
    let mut file = File::open(path)
        .map_err(|error| format!("{} opens for hashing: {error}", path.display()))?;
    let mut hash = Sha256::new();
    let mut buffer = vec![0u8; 1024 * 1024];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("{} hashes completely: {error}", path.display()))?;
        if read == 0 {
            break;
        }
        hash.update(&buffer[..read]);
    }
    Ok(hex_digest(hash.finalize()))
}

fn sha256(bytes: &[u8]) -> String {
    hex_digest(Sha256::digest(bytes))
}

fn words_sha256(words: &[u32]) -> String {
    let mut hash = Sha256::new();
    for word in words {
        hash.update(word.to_le_bytes());
    }
    hex_digest(hash.finalize())
}

fn hex_digest(digest: impl IntoIterator<Item = u8>) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(64);
    for byte in digest {
        encoded.push(HEX[(byte >> 4) as usize] as char);
        encoded.push(HEX[(byte & 0x0f) as usize] as char);
    }
    encoded
}

fn debug(error: impl Debug) -> String {
    format!("{error:?}")
}
