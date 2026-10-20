//! Native, bounded Alpha boundary: online observed learning and exact cold continuation.
//! A three-ring specialization of listener/octets.rs's serial declared field, with the
//! existing paired source founder and ordinary one-cell transactional comparison/deposition.
//! The byte boundary uses four base-4 digits per octet; it does not prescribe answers.
//! Retention is ContinuingState (material, tree, clock, moment, address, charts and carry).
//! Only the bounded current-aeon closing crib is carried beside it. No source tape is saved.
//! The native grouped comparison publishes only at actual receiving ticks. Source/contrast/
//! readout maps share the whole candidate probe; a refused whole branch stages the exact
//! upstream joint proposal, then the held-upstream receiving policy on its domain refusal.
//! Every nonzero upstream proposal executes the same-opening finite comparison.
//! NormalMaps is the default. Explicit complete-language train-local-retained-fibre-v1
//! uses local R/tree/population only; addressed E-family response remains a separate API.
//! Additive scope forks can opt into channel D alone, or actual
//! C/K/D endpoints; material endpoints retain their bound producing cut and held-work reading.
//! Both rungs reuse the same opening's normal flow and certified gain. Held upstream maps
//! absorb that news once with zero material move; discarded candidates never publish statistics.
//! A source end leaves only the bounded current unfinished transaction pending. It is accepted
//! boundary input, not a published or learned prefix, and no terminal clock is invented.
//! This consumer uses listener/octets.rs's unpumped initial circuit. A saturated locking
//! resonator is outside its scope: ResponseTube::open refuses saturation until its declared
//! nonlinear variation is joined to the paired response column. No pump response is replaced
//! by a zero column here.

#![allow(
    clippy::disallowed_methods,
    clippy::disallowed_types,
    reason = "explicit exterior CLI file/process boundary"
)]

use holonics::geometry::{RatVec3, screw::ScrewGenerator};
use holonics::hnn::constitution::{Constitution, ContinuingState, DepositReading};
use holonics::hnn::encoding::observed::PairedObservation;
use holonics::hnn::field::{ContactDeclaration, Current, Field, FieldDeclaration, RingDeclaration};
use holonics::hnn::paired::{PairedCarrier, PairingDeclaration};
use holonics::hnn::port::Handle;
use holonics::hnn::prediction::byte_release::Base4Bytes;
use holonics::hnn::prediction::native_section::{
    NativeSectionDecision, NativeSectionRequest, SectionWorkBudget, release_native_section,
};
use holonics::hnn::receiving::cells::CellLaw;
use holonics::hnn::reference::observed::{
    ObservedCrib, ObservedEpochDepositionScope, ObservedEpochOutcome, ObservedStream,
    PendingReadoutDiagnostic,
};
use holonics::hnn::reference::{ExposedResident, Resident};
use holonics::hnn::{ConstitutionRead, ExecutionPort, HnnError, Reference};
use holonics::ratio::linear::ExactRatMatrix;
use holonics::ratio::{Rat, algebraic::ExactInterval, integer, rat};
use holonics::receiver::release::KeyStream;
use std::{
    error::Error,
    io::{Read, Write},
    path::Path,
    process::{Command, Stdio},
    time::Instant,
};

#[path = "solenoidal_alpha/complete_language.rs"]
mod complete_language;
#[cfg(test)]
#[path = "solenoidal_alpha/reciprocal_code.rs"]
mod reciprocal_code;
#[cfg(test)]
pub fn code_reciprocal_continuity(
    execution: &dyn holonics::hnn::reference::observed::ObservedEpochExecution,
) -> std::result::Result<String, Box<dyn std::error::Error>> {
    reciprocal_code::continuity(execution)
}

#[cfg(test)]
#[path = "solenoidal_alpha/ordered_reciprocal_code.rs"]
mod ordered_reciprocal_code;
#[cfg(test)]
pub fn code_ordered_reciprocal(
    execution: &dyn holonics::hnn::reference::observed::ObservedEpochExecution,
) -> std::result::Result<String, Box<dyn std::error::Error>> {
    ordered_reciprocal_code::ordered(execution)
}

/// Explicit exterior executor identity; the library gains no device dependency.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CompleteLanguageTrainingBackend {
    HostReference,
    CudaObservedEpochDevice0,
}
impl CompleteLanguageTrainingBackend {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::HostReference => "host-reference",
            Self::CudaObservedEpochDevice0 => "cuda-observed-epoch-device0",
        }
    }
}
/// Shared complete-language exterior. The CUDA-owned wrapper supplies its actual executor.
pub fn run_complete_language_with_execution(
    args: &[String],
    execution: &dyn holonics::hnn::reference::observed::ObservedEpochExecution,
    backend: CompleteLanguageTrainingBackend,
) -> std::result::Result<(), Box<dyn Error>> {
    complete_language::run_with_execution(args, execution, backend)
}
#[cfg(test)]
pub fn code_checkpoint_native_bytes(path: &str) -> std::result::Result<Vec<u8>, Box<dyn Error>> {
    let (mut checkpoint, _) = Checkpoint::load(path, 64 * 1024 * 1024)?;
    // This exterior provenance deliberately names different executors. Native bytes, including
    // material/current/moment/tree/population/carry/crib/pending, must otherwise agree exactly.
    checkpoint.provenance.clear();
    checkpoint.bytes()
}

#[cfg(test)]
pub fn code_checkpoint_scope_and_source(path:&str)->std::result::Result<(String,String,String),Box<dyn Error>>{
    let (checkpoint,_)=Checkpoint::load(path,64*1024*1024)?;
    let c=checkpoint.stream.resident().constitution();
    Ok((format!("{:?}",checkpoint.stream.scope()),format!("{:?}",c.source_law(0)),format!("{:?}",c.receiving_law(2))))
}

type Result<T> = std::result::Result<T, Box<dyn Error>>;
const MATERIAL_BIT_BUDGET: u64 = 1 << 40; // Existing listener declaration, never raised.
const MAGIC: &str = "solenoidal-alpha-unplaced-v2";
const QUERY_BYTE_BUDGET: usize = 128; // Explicit exterior tiny-query workload declaration.
const WARM_QUERY: &str = "carry";

fn quoted(text: &str) -> String {
    let mut out = String::from("\"");
    for ch in text.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            ch if ch.is_control() => out.push_str(&format!("\\u{:04x}", u32::from(ch))),
            ch => out.push(ch),
        }
    }
    out.push('"');
    out
}
fn exact(value: &(impl std::fmt::Debug + ?Sized)) -> String {
    quoted(&format!("{value:?}"))
}
fn rational(value: &Rat) -> String {
    object(&[
        ("numerator", quoted(&value.numer().to_string())),
        ("denominator", quoted(&value.denom().to_string())),
    ])
}
fn interval(value: &ExactInterval) -> String {
    object(&[
        ("lower", rational(&value.lower)),
        ("upper", rational(&value.upper)),
    ])
}
fn sha256(bytes: &[u8]) -> Result<String> {
    // SHA belongs to exterior artifact provenance. No checksum enters a native relation.
    let mut process = Command::new("sha256sum")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    let mut input = process.stdin.take().ok_or("sha256sum stdin unavailable")?;
    std::thread::scope(|scope| -> Result<String> {
        let writer = scope.spawn(move || input.write_all(bytes));
        let output = process.wait_with_output()?;
        writer.join().map_err(|_| "sha256 writer failed")??;
        if !output.status.success() {
            return Err("sha256sum failed".into());
        }
        let digest = std::str::from_utf8(&output.stdout)?
            .split_whitespace()
            .next()
            .ok_or("missing SHA256")?;
        if digest.len() != 64 || !digest.bytes().all(|c| c.is_ascii_hexdigit()) {
            return Err("invalid SHA256 output".into());
        }
        Ok(digest.to_owned())
    })
}
fn digits(bytes: &[u8]) -> Vec<usize> {
    Base4Bytes::encode(bytes)
}
fn declaration(population: u64) -> Result<(Field, Constitution, PairingDeclaration)> {
    // Agent-inferred: listener's existing serial law at a smaller explicit test workload.
    // The three rings, contacts, physical depths and pairing are independent of corpus text.
    // Grouped phase rows require an odd receiving ring; three is the smallest admitted odd period.
    let periods = [5, 2, 3];
    let axis = ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero());
    let mut declared = FieldDeclaration::campaign_one(population);
    declared.rings = periods
        .iter()
        .enumerate()
        .map(|(g, &period)| RingDeclaration {
            period,
            screw: axis.clone(),
            placements: (0..period)
                .map(|n| FieldDeclaration::quarter_turn(n, period))
                .collect(),
            lock: if g == 0 { (0..4).collect() } else { Vec::new() },
            reflector: (0..period)
                .map(|p| ((period - p) % period) as usize)
                .collect(),
            admittance: integer(2),
            initial: 0,
        })
        .collect();
    declared.contacts = [(0, 1), (1, 2)]
        .iter()
        .map(|&(from, to)| ContactDeclaration {
            from,
            to,
            channel: (0..periods[from].min(periods[to]) as usize)
                .map(|node| (node, node))
                .collect(),
            admittance: integer(2),
            exponent: integer(2),
        })
        .collect();
    declared.sources = vec![0];
    declared.loops.clear();
    declared.alphabet = 4;
    declared.offsets = vec![1, 2];
    declared.receivers[0].ring = 2;
    declared.receivers[0].aperture = 1;
    declared.receivers[0].depth = 6;
    declared.receivers[0].tolerance = rat(1, 4);
    declared.lattice.clear();
    let field = Field::declare(declared.by_lattice_rule())?;
    let pairing = PairingDeclaration::Family {
        table: (0..4).map(|c| (c, c ^ 1)).collect(),
    };
    // Keep the paired response consumer on the existing listener's admitted linear circuit.
    // with_locking_pump installs saturation, which ResponseTube::open currently refuses.
    let initial = Constitution::initial(&field, MATERIAL_BIT_BUDGET)?;
    // Keep the physical receiving layout: the grouped owner independently seals its
    // whole-candidate comparison, without the old per-cell ArrivalContext gain gate.
    let initial = PairedCarrier::found(&field, initial, 0, &pairing)?.0;
    Ok((field, initial, pairing))
}
fn port() -> Reference {
    Reference::new(16, MATERIAL_BIT_BUDGET)
}
fn material_hash(resident: &Resident) -> Result<String> {
    sha256(
        resident
            .constitution()
            .continuing_state(0)?
            .to_text()
            .as_bytes(),
    )
}
fn total(resident: &Resident) -> Result<usize> {
    // `continuing().1` is the current aeon's cell count: it resets at joint closure.
    // Crib positions and published totals instead continue the one source moment.
    let (moment, _) = resident
        .continuing()
        .ok_or("Alpha requires one continuing source moment")?;
    let source = resident
        .moment(&moment)
        .ok_or("the continuing source moment is missing")?;
    Ok(usize::try_from(source.cells())?)
}

struct Checkpoint {
    population: u64,
    stream: ObservedStream,
    provenance: String,
}
impl Checkpoint {
    fn bytes(&self) -> Result<Vec<u8>> {
        let native = self.stream.resident().continuing_state(0)?.to_text();
        let crib = self.stream.crib().unplaced_checkpoint()?;
        let pending = self.stream.pending_checkpoint();
        let header = format!(
            "{MAGIC}\n{} {} {} {} {}\n",
            self.population,
            native.len(),
            crib.len(),
            pending.len(),
            self.provenance.len()
        );
        let mut bytes = header.into_bytes();
        bytes.extend(native.bytes());
        bytes.extend(crib.bytes());
        bytes.extend(pending.bytes());
        bytes.extend(self.provenance.bytes());
        Ok(bytes)
    }
    fn load(path: &str, byte_budget: u64) -> Result<(Self, String)> {
        let file = std::fs::File::open(path)?;
        let length = file.metadata()?.len();
        if length > byte_budget {
            return Err(format!(
                "checkpoint bytes {length} exceed declared read budget {byte_budget}"
            )
            .into());
        }
        let mut bytes = Vec::new();
        file.take(
            byte_budget
                .checked_add(1)
                .ok_or("checkpoint budget overflow")?,
        )
        .read_to_end(&mut bytes)?;
        if bytes.len() as u64 > byte_budget {
            return Err("checkpoint grew beyond declared byte budget".into());
        }
        let hash = sha256(&bytes)?;
        let text = std::str::from_utf8(&bytes)?;
        let (magic, rest) = text.split_once('\n').ok_or("missing checkpoint header")?;
        if magic != MAGIC {
            return Err("unsupported Alpha checkpoint".into());
        }
        let (sizes, body) = rest.split_once('\n').ok_or("missing checkpoint sizes")?;
        let values = sizes
            .split_whitespace()
            .map(str::parse::<u64>)
            .collect::<std::result::Result<Vec<_>, _>>()?;
        let [
            population,
            native_len,
            crib_len,
            pending_len,
            provenance_len,
        ] = values.as_slice()
        else {
            return Err("invalid checkpoint sizes".into());
        };
        let native_end = usize::try_from(*native_len)?;
        let crib_end = native_end
            .checked_add(usize::try_from(*crib_len)?)
            .ok_or("checkpoint length overflow")?;
        let pending_end = crib_end
            .checked_add(usize::try_from(*pending_len)?)
            .ok_or("checkpoint length overflow")?;
        let end = pending_end
            .checked_add(usize::try_from(*provenance_len)?)
            .ok_or("checkpoint length overflow")?;
        if end != body.len() {
            return Err("checkpoint section lengths do not match".into());
        }
        let native = body
            .get(..native_end)
            .ok_or("native checkpoint UTF8 boundary")?;
        let crib = body
            .get(native_end..crib_end)
            .ok_or("crib checkpoint UTF8 boundary")?;
        let pending = body
            .get(crib_end..pending_end)
            .ok_or("pending checkpoint UTF8 boundary")?;
        let provenance = body
            .get(pending_end..)
            .ok_or("provenance UTF8 boundary")?
            .to_owned();
        let state = ContinuingState::from_text(native, MATERIAL_BIT_BUDGET)?;
        let (field, initial, _) = declaration(*population)?;
        let resident =
            port().mount_continued(&field, &Current::at_rest(&field), initial, &state)?;
        if resident.continuing_state(0)? != state {
            return Err("cold native restore changed saved state".into());
        }
        let crib = ObservedCrib::from_unplaced_checkpoint(
            &field,
            resident.current(),
            total(&resident)?,
            crib,
        )?;
        Ok((
            Self {
                population: *population,
                stream: ObservedStream::restore_checkpoint(resident, crib, pending)?,
                provenance,
            },
            hash,
        ))
    }
    /// Exterior fork: change only the future deposition scope of this bounded transaction.
    /// Keep the complete native opening, closing crib and unfinished classes verbatim.
    fn fork_scope(&self, scope: ObservedEpochDepositionScope) -> Result<Self> {
        Ok(Self {
            population: self.population,
            stream: ObservedStream::restore(
                self.stream.resident().clone(),
                self.stream.crib().clone(),
                scope,
                self.stream.pending_classes().to_vec(),
            )?,
            provenance: self.provenance.clone(),
        })
    }
    fn publish(&self, path: &str) -> Result<(usize, String)> {
        let bytes = self.bytes()?;
        let hash = sha256(&bytes)?;
        let staging = format!("{path}.staging");
        if Path::new(path).exists() {
            return Err("checkpoint destination already exists".into());
        }
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&staging)?;
        file.write_all(&bytes)?;
        file.sync_all()?;
        drop(file);
        if std::fs::read(&staging)? != bytes {
            return Err("checkpoint staging readback mismatch".into());
        }
        std::fs::hard_link(&staging, path)?;
        let parent = Path::new(path)
            .parent()
            .filter(|path| !path.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        std::fs::File::open(parent)?.sync_all()?;
        std::fs::remove_file(staging)?;
        Ok((bytes.len(), hash))
    }
}

fn query_reading(checkpoint: &Checkpoint, query: &str) -> Result<String> {
    if query.len() > QUERY_BYTE_BUDGET {
        return Err("query exceeds declared 128-byte boundary workload".into());
    }
    let pairing = declaration(checkpoint.population)?.2;
    let reference = port();
    let (mut resident, mut crib) = checkpoint.stream.query_fork(&reference, &pairing)?;
    for class in digits(query.as_bytes()) {
        reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)?;
    }
    let boundary = PairedObservation::admit(resident.field(), resident.constitution(), &pairing)?;
    let mut codec = Vec::new();
    for observation in boundary.ports() {
        // These exact checks consume the contemporary E, its decoder, rotor and residual.
        let decoder = observation.decoder()?;
        let square = observation.square()?;
        codec.push(format!("{{\"source_ring\":{},\"injection_exact\":{},\"decoder_exact\":{},\"rotor_square_exact\":{}}}", observation.carrier().ring(), exact(observation.injection()), exact(decoder), exact(square)));
    }
    let moment = resident
        .continuing()
        .ok_or("checkpoint has no native continuing moment")?
        .0;
    let phases = resident
        .admitted()
        .first()
        .ok_or("no native receiver")?
        .clone();
    let (pending, refined) = reference.refine(&mut resident, &moment, &phases)?;
    let faces = refined
        .forward
        .present()
        .ok_or("native refinement gave no faces")?;
    let decision = reference
        .release_cells(&mut resident, &pending, CellLaw::Commit)?
        .forward
        .into_present()
        .ok_or("native query gave no decision")?;
    let byte_boundary = Base4Bytes::read_release(decision.clone(), phases.aperture())?;
    // This is a read of retained sufficient statistics, with their own prior/tolerance.
    // It is a declared phase family, never a semantic answer or a truth-membership claim.
    let family = resident
        .constitution()
        .receiving_phase_family(phases.ring(), phases.tolerance())?;
    let reading = object(&[
        ("query_bytes", query.len().to_string()),
        ("query_cells", (query.len() * 4).to_string()),
        (
            "pending_cells_consumed_once",
            checkpoint.stream.pending_classes().len().to_string(),
        ),
        ("lift_exact", exact(resident.current().lift())),
        ("field_faces_exact", exact(faces)),
        ("native_decision_exact", exact(&decision)),
        ("native_byte_boundary_exact", exact(&byte_boundary)),
        ("codec_exact", format!("[{}]", codec.join(","))),
        ("phase_family_exact", exact(&family)),
        (
            "phase_family_minimum_exact",
            family
                .as_ref()
                .map_or_else(|| "null".to_owned(), |family| exact(family.minimum())),
        ),
        ("semantic_answer_claim", "false".into()),
    ]);
    reference.discard(&mut resident, Handle::Pending(pending))?;
    Ok(reading)
}

/// Exterior matched coding experiment on one disposable factual target prefix. No normal
/// deposit occurs; native R stays fixed while the existing population and tree receive the
/// actual boundary targets. All controls share that native factual history at each cell.
fn frozen_r_target_prefix(checkpoint: &Checkpoint, target: &[u8]) -> Result<String> {
    if target.is_empty() || target.len() > QUERY_BYTE_BUDGET {
        return Err("a frozen-R target prefix needs 1..=128 declared source bytes".into());
    }
    let targets = digits(target);
    let count = u64::try_from(targets.len())?;
    if checkpoint
        .stream
        .accepted_cells()?
        .checked_add(count)
        .ok_or("target horizon overflow")?
        > checkpoint.population
    {
        return Err("the frozen-R target prefix exceeds the declared source horizon".into());
    }
    let main_before = checkpoint.bytes()?;
    let reference = port();
    let (field, founding, pairing) = declaration(checkpoint.population)?;
    let (mut resident, mut crib) = checkpoint.stream.query_fork(&reference, &pairing)?;
    let receiver = resident
        .admitted()
        .first()
        .ok_or("no native receiver")?
        .ring();
    let frozen = resident
        .constitution()
        .receiving_map(receiver)
        .ok_or("native receiving map is missing")?
        .clone();
    let control = founding
        .receiving_law(receiver)
        .ok_or("founding receiving map is missing")?
        .map()
        .clone();
    let laws = |resident: &Resident| {
        (0..field.rings().len())
            .map(|ring| {
                (
                    resident.constitution().source_law(ring).cloned(),
                    resident.constitution().contrast_law(ring).clone(),
                    resident.constitution().receiving_law(ring).cloned(),
                )
            })
            .collect::<Vec<_>>()
    };
    let laws_before = laws(&resident);
    let commit_before = resident.constitution().commit();
    let mut sums = vec![ExactInterval::point(integer(0)); 6];
    let mut phase_sums = vec![integer(0); 3];
    let mut events = Vec::new();
    let started = Instant::now();
    for (at, &class) in targets.iter().enumerate() {
        let cell_started = Instant::now();
        let moment = resident
            .continuing()
            .ok_or("target prefix has no continuing source")?
            .0;
        let phases = resident
            .admitted()
            .first()
            .ok_or("no native receiver")?
            .clone();
        let (pending, refined) = reference.refine(&mut resident, &moment, &phases)?;
        let receipt = reference.receive_target_prefix_readout_control(
            &mut resident,
            &mut crib,
            &pairing,
            pending,
            class,
            &frozen,
            &control,
            holonics::ratio::exponentiated::READING_BITS,
            None,
        )?;
        let codes = &receipt.codes;
        for (sum, value) in phase_sums.iter_mut().zip([
            &receipt.native_phase_excess,
            &receipt.control_phase_excess,
            &receipt.native_minus_control_phase_excess,
        ]) {
            *sum += value;
        }
        for (sum, value) in sums.iter_mut().zip([
            &codes.native_code,
            &codes.control_code,
            &codes.tree_code,
            &codes.native_minus_control,
            &codes.native_minus_tree,
            &codes.control_minus_tree,
        ]) {
            *sum = ExactInterval::new(&sum.lower + &value.lower, &sum.upper + &value.upper)?;
        }
        events.push(object(&[
            ("index", at.to_string()),
            ("target_base4_class", class.to_string()),
            (
                "target_denotes",
                quoted("actual observed base-4 digit of the pinned target byte passage"),
            ),
            (
                "source_cells_before_target",
                receipt.diagnostic.source_cells.to_string(),
            ),
            ("reading_bits", codes.reading_bits.to_string()),
            ("native_bits", interval(&codes.native_code)),
            ("target_phase", rational(&receipt.target_phase)),
            (
                "native_phase_excess",
                rational(&receipt.native_phase_excess),
            ),
            (
                "founding_R_phase_excess",
                rational(&receipt.control_phase_excess),
            ),
            (
                "native_minus_founding_R_phase_excess",
                rational(&receipt.native_minus_control_phase_excess),
            ),
            (
                "native_combined_cell_indices",
                format!(
                    "[{}]",
                    receipt
                        .diagnostic
                        .scored_face
                        .combined
                        .cells()
                        .iter()
                        .map(|cell| {
                            quoted(
                                &(cell.carry.clone()
                                    * num_bigint::BigInt::from(receipt.diagnostic.tree.grain)
                                    + num_bigint::BigInt::from(cell.phase))
                                .to_string(),
                            )
                        })
                        .collect::<Vec<_>>()
                        .join(",")
                ),
            ),
            (
                "founding_combined_cell_indices",
                format!(
                    "[{}]",
                    receipt
                        .diagnostic
                        .tree
                        .exponents
                        .iter()
                        .map(|value| quoted(&value.to_string()))
                        .collect::<Vec<_>>()
                        .join(",")
                ),
            ),
            (
                "founding_R_same_feature_bits",
                interval(&codes.control_code),
            ),
            ("same_prefix_tree_bits", interval(&codes.tree_code)),
            (
                "native_minus_founding_R_bits",
                interval(&codes.native_minus_control),
            ),
            ("native_minus_tree_bits", interval(&codes.native_minus_tree)),
            (
                "founding_R_minus_tree_bits",
                interval(&codes.control_minus_tree),
            ),
            ("native_mass", interval(&codes.native_mass)),
            ("founding_R_mass", interval(&codes.control_mass)),
            ("tree_mass", rational(&codes.tree_mass)),
            (
                "readout_intervention_exact",
                exact(&receipt.diagnostic.readout),
            ),
            (
                "producing_refinement_receipt_exact",
                exact(&refined.receipt),
            ),
            ("actual_target_ingestion_exact", exact(&receipt.ingestion)),
            ("end_lift_exact", exact(resident.current().lift())),
            ("wall_ns", cell_started.elapsed().as_nanos().to_string()),
        ]));
        eprintln!(
            "alpha native frozen_R_code {}",
            events
                .last()
                .expect("one successful target has its exterior receipt")
        );
        eprintln!(
            "alpha native frozen_R_target cell={at} target={class} elapsed_ns={}",
            started.elapsed().as_nanos()
        );
    }
    if checkpoint.bytes()? != main_before || resident.field() != &field {
        return Err("a frozen-R target query must preserve its main checkpoint and field".into());
    }
    if resident.constitution().receiving_map(receiver) != Some(&frozen)
        || laws(&resident) != laws_before
        || resident.constitution().commit() != commit_before
    {
        return Err("a frozen-R target query must preserve all material maps".into());
    }
    Ok(object(&[
        (
            "scope",
            quoted(
                "frozen material; every target scored before its factual reception; native/founding R/tree share each reached native factual feature/tree/population; population and tree adapt, normal maps do not",
            ),
        ),
        ("target_bytes", target.len().to_string()),
        ("scored_cells", targets.len().to_string()),
        (
            "prior_training_pending_cells_advanced_without_scoring",
            checkpoint.stream.pending_classes().len().to_string(),
        ),
        ("normal_depositions", "0".into()),
        ("main_checkpoint_unchanged", "true".into()),
        ("native_phase_excess", rational(&phase_sums[0])),
        ("founding_R_phase_excess", rational(&phase_sums[1])),
        (
            "native_minus_founding_R_phase_excess",
            rational(&phase_sums[2]),
        ),
        ("material_maps_unchanged", "true".into()),
        ("native_bits", interval(&sums[0])),
        ("founding_R_same_feature_bits", interval(&sums[1])),
        ("same_prefix_tree_bits", interval(&sums[2])),
        ("native_minus_founding_R_bits", interval(&sums[3])),
        ("native_minus_tree_bits", interval(&sums[4])),
        ("founding_R_minus_tree_bits", interval(&sums[5])),
        ("series", format!("[{}]", events.join(","))),
    ]))
}

fn diagnose_query_prefix(
    reference: &Reference,
    opening: &Resident,
    opening_crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    prefix: &[usize],
    control_map: &ExactRatMatrix,
    bits: u32,
) -> std::result::Result<PendingReadoutDiagnostic, HnnError> {
    let mut resident = opening.clone();
    let mut crib = opening_crib.clone();
    for &class in prefix {
        reference.ingest_class_continuing(&mut resident, &mut crib, pairing, class, None)?;
    }
    let moment = resident
        .continuing()
        .ok_or(HnnError::Unadmitted {
            reason: "a conditional query keeps one actual continuing source",
        })?
        .0;
    let phases = resident
        .admitted()
        .first()
        .ok_or(HnnError::Unadmitted {
            reason: "a conditional query keeps its admitted receiving phase",
        })?
        .clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
    let diagnostic = reference.diagnose_pending_readout(&resident, &pending, control_map, bits)?;
    reference.discard(&mut resident, Handle::Pending(pending))?;
    Ok(diagnostic)
}

/// Exterior matched controls over the actual immutable prompt opening. Each oracle call
/// queries this same retained state with a complete hypothetical future prefix; it teaches
/// nothing. Chain-rule finite-section release is distinct from a Floquet bank or a variable
/// reply stopping law. No target continuation or corpus lookup enters this operation.
fn conditional_query_controls(
    checkpoint: &Checkpoint,
    query: &str,
    section_bytes: usize,
    max_oracle_calls: usize,
) -> Result<String> {
    if query.len() > QUERY_BYTE_BUDGET {
        return Err("query exceeds declared 128-byte boundary workload".into());
    }
    let projected = checkpoint
        .stream
        .accepted_cells()?
        .checked_add(query.len().checked_mul(4).ok_or("query cell overflow")? as u64)
        .and_then(|n| n.checked_add(section_bytes.checked_mul(4)? as u64))
        .ok_or("conditional section source horizon overflow")?;
    if projected > checkpoint.population {
        return Err(
            "conditional query and complete finite field exceed native source horizon".into(),
        );
    }
    let reference = port();
    let (_, founding, pairing) = declaration(checkpoint.population)?;
    let before = checkpoint.bytes()?;
    let (mut opening, mut crib) = checkpoint.stream.query_fork(&reference, &pairing)?;
    for class in digits(query.as_bytes()) {
        reference.ingest_class_continuing(&mut opening, &mut crib, &pairing, class, None)?;
    }
    let ring = opening
        .admitted()
        .first()
        .ok_or("query has no receiving phase")?
        .ring();
    let control_map = founding
        .receiving_law(ring)
        .ok_or("founding readout is missing")?
        .map()
        .clone();
    let bits = holonics::ratio::exponentiated::READING_BITS;
    let matched = diagnose_query_prefix(
        &reference,
        &opening,
        &crib,
        &pairing,
        &[],
        &control_map,
        bits,
    )?;
    let request = NativeSectionRequest::declare(
        section_bytes,
        bits,
        SectionWorkBudget {
            max_prefixes: max_oracle_calls
                .checked_mul(4)
                .and_then(|n| n.checked_add(1))
                .ok_or("prefix work overflow")?,
            max_oracle_calls,
        },
    )?;
    let mut arms = Vec::new();
    for policy in ["native", "founding_readout_same_feature", "executed_tree"] {
        let mut costs = Vec::new();
        let section = release_native_section(&request, |prefix, bits| {
            let started = Instant::now();
            let diagnostic = diagnose_query_prefix(
                &reference,
                &opening,
                &crib,
                &pairing,
                prefix,
                &control_map,
                bits,
            );
            costs.push((prefix.len(), started.elapsed().as_nanos()));
            diagnostic.map(|reading| match policy {
                "native" => reading.readout.native.native_masses,
                "founding_readout_same_feature" => reading.readout.control.native_masses,
                _ => reading.readout.native.tree_masses,
            })
        })?;
        let (classes, bytes, text) = match &section.decision {
            NativeSectionDecision::Released {
                classes, decoded, ..
            } => (
                format!("{classes:?}"),
                format!("{:?}", decoded.bytes),
                decoded
                    .complete_boundary_text()
                    .map_or_else(|| "null".into(), quoted),
            ),
            _ => ("null".into(), "null".into(), "null".into()),
        };
        arms.push(object(&[
            ("policy", quoted(policy)),
            ("section_exact", exact(&section)),
            ("released_classes", classes),
            ("released_bytes", bytes),
            ("released_utf8", text),
            ("oracle_calls", section.oracle_calls.to_string()),
            (
                "prefixes_considered",
                section.prefixes_considered.to_string(),
            ),
            (
                "oracle_cost_series_ns",
                format!(
                    "[{}]",
                    costs
                        .iter()
                        .map(|(depth, ns)| format!("[{depth},{ns}]"))
                        .collect::<Vec<_>>()
                        .join(",")
                ),
            ),
        ]));
    }
    if checkpoint.bytes()? != before {
        return Err("a read-only conditional section changed its retained checkpoint".into());
    }
    Ok(object(&[
        ("query_bytes", query.len().to_string()),
        ("section_bytes", section_bytes.to_string()),
        ("matched_opening_diagnostic_exact", exact(&matched)),
        ("arms", format!("[{}]", arms.join(","))),
        (
            "source_horizon_after_complete_section",
            projected.to_string(),
        ),
        ("retained_checkpoint_unchanged", "true".into()),
        (
            "scope",
            quoted(
                "exact finite conditional receiving section; matched readout intervention; no material deposition; no variable reply stopping or physical bank claim",
            ),
        ),
        ("semantic_answer_claim", "false".into()),
    ]))
}
/// One alternate-receiver conditional at a complete hypothetical prefix. The physical body,
/// source chart and native map stay genuine. Each hypothetical class updates the SAME native
/// full-fibre likelihood and addressed tree before the next native Word. No branch is retained.
fn fibre_prefix_state(
    reference: &Reference,
    opening: &Resident,
    opening_crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    prefix: &[usize],
    receiver: &holonics::hnn::receiving::RetainedFibreReceiver,
) -> std::result::Result<(Resident, ObservedCrib), HnnError> {
    let mut resident = opening.clone();
    let mut crib = opening_crib.clone();
    for &class in prefix {
        let moment = resident
            .continuing()
            .ok_or(HnnError::Unadmitted {
                reason: "a fibre prefix keeps its actual source moment",
            })?
            .0;
        let phases = resident
            .admitted()
            .first()
            .ok_or(HnnError::Unadmitted {
                reason: "a fibre prefix keeps its declared receiving phase",
            })?
            .clone();
        let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
        reference.receive_receiver_prefix_continuing(
            &mut resident,
            &mut crib,
            pairing,
            pending,
            class,
            receiver,
            None,
        )?;
    }
    Ok((resident, crib))
}

fn fibre_prefix_read(
    reference: &Reference,
    opening: &Resident,
    opening_crib: &ObservedCrib,
    pairing: &PairingDeclaration,
    prefix: &[usize],
    control_map: &ExactRatMatrix,
    receiver: &holonics::hnn::receiving::RetainedFibreReceiver,
    bits: u32,
) -> std::result::Result<
    holonics::hnn::receiving::cells::diagnostic::RetainedReceiverDiagnostic,
    HnnError,
> {
    let (mut resident, _crib) =
        fibre_prefix_state(reference, opening, opening_crib, pairing, prefix, receiver)?;
    let moment = resident
        .continuing()
        .ok_or(HnnError::Unadmitted {
            reason: "a fibre oracle keeps its continuing source",
        })?
        .0;
    let phases = resident
        .admitted()
        .first()
        .ok_or(HnnError::Unadmitted {
            reason: "a fibre oracle keeps its declared phase",
        })?
        .clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
    let read = reference.diagnose_pending_readout_at_receiver(
        &resident,
        &pending,
        control_map,
        receiver,
        bits,
    )?;
    reference.discard(&mut resident, Handle::Pending(pending))?;
    Ok(read)
}

/// Exact finite section plus literal keyed continuations of the same retained body. Every
/// arm is explicit: native full fibre, founding-R at the same feature, and the executed tree.
/// Inherited population likelihoods come from the checkpoint's original coarse receiver.
/// Readout controls share each hypothesized prefix's native full-fibre reception history;
/// they are matched local interventions, not independently retrained counterfactual bodies.
fn retained_fibre_query_controls(
    checkpoint: &Checkpoint,
    query: &str,
    section_bytes: usize,
    max_oracle_calls: usize,
    key_bytes: &[u8],
) -> Result<String> {
    if query.len() > QUERY_BYTE_BUDGET {
        return Err("fibre prompt exceeds declared byte workload".into());
    }
    let cells = section_bytes
        .checked_mul(4)
        .ok_or("fibre aperture overflow")?;
    if key_bytes.len() != cells.checked_mul(8).ok_or("fibre key workload overflow")? {
        return Err("fibre draw requires one declared eight-byte key per cell".into());
    }
    let horizon = checkpoint
        .stream
        .accepted_cells()?
        .checked_add((query.len().checked_mul(4).ok_or("fibre prompt overflow")?) as u64)
        .and_then(|n| n.checked_add(cells as u64))
        .ok_or("fibre horizon overflow")?;
    if horizon > checkpoint.population {
        return Err("fibre aperture exceeds the declared source horizon".into());
    }
    let before = checkpoint.bytes()?;
    let reference = port();
    let (_, founding, pairing) = declaration(checkpoint.population)?;
    let (mut opening, mut crib) = checkpoint.stream.query_fork(&reference, &pairing)?;
    for class in digits(query.as_bytes()) {
        reference.ingest_class_continuing(&mut opening, &mut crib, &pairing, class, None)?;
    }
    let phases = opening
        .admitted()
        .first()
        .ok_or("fibre query has no receiver")?;
    let receiver = holonics::hnn::receiving::RetainedFibreReceiver::declare(phases.grain())?;
    let control = founding
        .receiving_law(phases.ring())
        .ok_or("fibre query has no founding readout")?
        .map()
        .clone();
    let bits = holonics::ratio::exponentiated::READING_BITS;
    let matched = fibre_prefix_read(
        &reference,
        &opening,
        &crib,
        &pairing,
        &[],
        &control,
        &receiver,
        bits,
    )?;
    let request = NativeSectionRequest::declare(
        section_bytes,
        bits,
        SectionWorkBudget {
            max_prefixes: max_oracle_calls
                .checked_mul(4)
                .and_then(|n| n.checked_add(1))
                .ok_or("fibre prefix limit overflow")?,
            max_oracle_calls,
        },
    )?;
    let mut arms = Vec::new();
    for policy in [
        "native_full_fibre",
        "founding_R_same_feature_full_fibre",
        "executed_tree",
    ] {
        let section = release_native_section(&request, |prefix, depth| {
            fibre_prefix_read(
                &reference, &opening, &crib, &pairing, prefix, &control, &receiver, depth,
            )
            .map(|read| match policy {
                "native_full_fibre" => read.native.native_masses,
                "founding_R_same_feature_full_fibre" => read.control.native_masses,
                _ => read.native.tree_masses,
            })
        })?;
        let mut resident = opening.clone();
        let mut local_crib = crib.clone();
        let mut classes = Vec::new();
        let mut events = Vec::new();
        let mut stop = "DeclaredLength";
        let mut key_stream = KeyStream::new(key_bytes.to_vec(), 8)?;
        for at in 0..cells {
            let moment = resident.continuing().ok_or("fibre draw has no source")?.0;
            let phases = resident
                .admitted()
                .first()
                .ok_or("fibre draw has no phase")?
                .clone();
            let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
            let prefix = reference.diagnose_pending_readout_at_receiver(
                &resident, &pending, &control, &receiver, bits,
            )?;
            let masses = match policy {
                "native_full_fibre" => &prefix.native.native_masses,
                "founding_R_same_feature_full_fibre" => &prefix.control.native_masses,
                _ => &prefix.native.tree_masses,
            };
            let key = key_stream
                .next_key()
                .ok_or("declared fibre key stream ended")?;
            let decision = holonics::receiver::release::draw(masses, &key)?;
            events.push(object(&[
                ("cell", at.to_string()),
                ("key", rational(&key)),
                ("decision", exact(&decision)),
                ("matched_receiver", exact(&prefix)),
            ]));
            let holonics::receiver::release::ReleaseReturn::Drawn(certified) = decision else {
                reference.discard(&mut resident, Handle::Pending(pending))?;
                stop = "Unresolved";
                break;
            };
            let class = certified.class;
            reference.receive_receiver_prefix_continuing(
                &mut resident,
                &mut local_crib,
                &pairing,
                pending,
                class,
                &receiver,
                None,
            )?;
            classes.push(class);
            // The focused control compares every emitted-prefix state, including the full
            // tree/population/material/current/moment/charts and crib, to independent replay.
            // Production draws advance that checked transition once, without redundant Words.
            #[cfg(test)]
            {
                let (replayed, replayed_crib) =
                    fibre_prefix_state(&reference, &opening, &crib, &pairing, &classes, &receiver)?;
                if resident.continuing_state(0)? != replayed.continuing_state(0)?
                    || local_crib != replayed_crib
                {
                    return Err(
                        "full-fibre keyed continuation disagrees with complete-prefix replay"
                            .into(),
                    );
                }
            }
            // The exterior diagnostic dies here; none is native retention.
        }
        let decoded = Base4Bytes::decode(&classes, cells)?;
        let continuation = resident.continuing_state(0)?;
        let final_state = continuation.to_text();
        arms.push(object(&[
            ("policy", quoted(policy)),
            ("section_exact", exact(&section)),
            ("draw_stop", quoted(stop)),
            ("draw_classes", format!("{classes:?}")),
            ("raw_bytes", format!("{:?}", decoded.bytes)),
            (
                "raw_utf8",
                decoded
                    .complete_boundary_text()
                    .map_or_else(|| "null".into(), quoted),
            ),
            ("decoded_exact", exact(&decoded)),
            ("draw_events", format!("[{}]", events.join(","))),
            ("self_received_cells", classes.len().to_string()),
            (
                "continuation_sha256",
                quoted(&sha256(final_state.as_bytes())?),
            ),
        ]));
    }
    if checkpoint.bytes()? != before {
        return Err("fibre query changed its retained checkpoint".into());
    }
    Ok(object(&[
        ("receiver", exact(&receiver)),
        ("prompt_bytes", query.len().to_string()),
        ("matched_opening", exact(&matched)),
        ("arms", format!("[{}]", arms.join(","))),
        ("retained_checkpoint_unchanged", "true".into()),
        (
            "population_scope",
            quoted(
                "inherited original coarse likelihoods; matched R interventions share native full-fibre prefix reception; no normal deposition",
            ),
        ),
        ("semantic_answer_claim", "false".into()),
    ]))
}

struct KeyedReply {
    json: String,
    classes: Vec<usize>,
}

/// The native draw and its existing local receiving continuation, on a disposable query fork.
/// A caller-declared length ends this exterior read. No byte is EOS and no target is opened here.
fn keyed_reply(
    checkpoint: &Checkpoint,
    query: &str,
    key_bytes: &[u8],
    byte_length: usize,
    tree_only: bool,
    label: &str,
) -> Result<KeyedReply> {
    let cells = byte_length.checked_mul(4).ok_or("draw length overflow")?;
    if cells == 0 || query.len() > QUERY_BYTE_BUDGET {
        return Err("a keyed reply needs a positive declared length and a bounded prompt".into());
    }
    // Eight bytes denote one exact key k/2^64; these are declared nonsecret release operands.
    if key_bytes.len() != cells.checked_mul(8).ok_or("key workload overflow")? {
        return Err("the declared draw supplies exactly one eight-byte key per cell".into());
    }
    let horizon = checkpoint
        .stream
        .accepted_cells()?
        .checked_add(u64::try_from(
            query.len().checked_mul(4).ok_or("query overflow")?,
        )?)
        .and_then(|n| n.checked_add(u64::try_from(cells).ok()?))
        .ok_or("draw horizon overflow")?;
    if horizon > checkpoint.population {
        return Err("the declared keyed reply exceeds the native source horizon".into());
    }
    let before = checkpoint.bytes()?;
    let reference = port();
    let pairing = declaration(checkpoint.population)?.2;
    let (mut resident, mut crib) = checkpoint.stream.query_fork(&reference, &pairing)?;
    for class in digits(query.as_bytes()) {
        reference.ingest_class_continuing(&mut resident, &mut crib, &pairing, class, None)?;
    }
    let prompt_lift = exact(resident.current().lift());
    let phase_family = resident.constitution().receiving_phase_family(
        resident
            .admitted()
            .first()
            .ok_or("no native receiver")?
            .ring(),
        resident
            .admitted()
            .first()
            .ok_or("no native receiver")?
            .tolerance(),
    )?;
    let initial_material = declaration(checkpoint.population)?.1;
    let receiving_ring = resident
        .admitted()
        .first()
        .ok_or("no native receiver")?
        .ring();
    let initial_map = initial_material
        .receiving_law(receiving_ring)
        .ok_or("founding readout is missing")?
        .map()
        .clone();
    let mut keys = KeyStream::new(key_bytes.to_vec(), 8)?;
    let mut classes = Vec::new();
    let mut events = Vec::new();
    let mut stop = "DeclaredLength";
    let started = Instant::now();
    for at in 0..cells {
        let cell_started = Instant::now();
        let moment = resident
            .continuing()
            .ok_or("draw has no continuing source")?
            .0;
        let phases = resident
            .admitted()
            .first()
            .ok_or("no native receiver")?
            .clone();
        let (pending, _) = reference.refine(&mut resident, &moment, &phases)?;
        let producing_lift = exact(resident.current().lift());
        let matched = reference.diagnose_pending_readout(
            &resident,
            &pending,
            &initial_map,
            holonics::ratio::exponentiated::READING_BITS,
        )?;
        let (class, decision, receiving) = if tree_only {
            let read = reference.release_tree_cell_continuing(
                &mut resident,
                &mut crib,
                &pairing,
                pending,
                &mut keys,
                None,
            )?;
            let class = read.class();
            let received = read.ingestion.is_some();
            (class, exact(&read), received)
        } else {
            let release = reference
                .release_cells(&mut resident, &pending, CellLaw::Draw(&mut keys))?
                .forward
                .into_present()
                .ok_or("native draw gave no release")?;
            let cell = release.cells.first().ok_or("native draw gave no cell")?;
            let class = cell.class();
            if class.is_some() {
                reference.ingest_released_cell_continuing(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    pending,
                    cell,
                    None,
                )?;
            }
            (class, exact(&release), class.is_some())
        };
        events.push(object(&[
            ("index", at.to_string()),
            ("producing_lift_exact", producing_lift),
            ("native_decision_exact", decision),
            ("landmark_face_exact", exact(&matched.tree)),
            ("readout_intervention_exact", exact(&matched.readout)),
            ("locally_received", receiving.to_string()),
            ("end_lift_exact", exact(resident.current().lift())),
            ("wall_ns", cell_started.elapsed().as_nanos().to_string()),
        ]));
        eprintln!(
            "alpha native keyed_draw arm={label} cell={at} emitted={} received={receiving} elapsed_ns={}",
            class.is_some(),
            started.elapsed().as_nanos()
        );
        let Some(class) = class else {
            reference.discard(&mut resident, Handle::Pending(pending))?;
            stop = "UnresolvedOrNoKey";
            break;
        };
        if !receiving {
            return Err("a released cell must be locally received before the next score".into());
        }
        classes.push(class);
    }
    let boundary = Base4Bytes::decode(&classes, cells)?;
    if checkpoint.bytes()? != before {
        return Err("a keyed query changed its immutable retained checkpoint".into());
    }
    Ok(KeyedReply {
        json: object(&[
            ("policy", quoted(label)),
            ("declared_bytes", byte_length.to_string()),
            (
                "declared_length_reached",
                (classes.len() == cells).to_string(),
            ),
            ("stop", quoted(stop)),
            ("classes", format!("{classes:?}")),
            ("released_bytes", format!("{:?}", boundary.bytes)),
            (
                "released_utf8",
                boundary
                    .complete_boundary_text()
                    .map_or_else(|| "null".into(), quoted),
            ),
            ("byte_boundary_exact", exact(&boundary)),
            ("keys_read", keys.keys_read().to_string()),
            ("key_width_bytes", keys.width().to_string()),
            ("prompt_lift_exact", prompt_lift),
            ("phase_family_at_prompt_exact", exact(&phase_family)),
            ("decisions", format!("[{}]", events.join(","))),
            ("retained_checkpoint_unchanged", "true".into()),
            ("semantic_answer_claim", "false".into()),
            (
                "scope",
                quoted(
                    "native certified keyed cell draw with local conditional reception; raw base-four codec; caller-declared length, no EOS",
                ),
            ),
        ]),
        classes,
    })
}

/// Read exterior targets only after every native/control release has completed. The generic
/// ordered-contact owner consumes raw base-four classes: no base-32 framing end is invented.
fn keyed_controls(
    checkpoint: &Checkpoint,
    founding: &Checkpoint,
    query: &str,
    key_path: &str,
    byte_length: usize,
    target_path: &str,
) -> Result<String> {
    if checkpoint.population != founding.population {
        return Err("founding control must keep the same declared field".into());
    }
    let expected = byte_length
        .checked_mul(32)
        .ok_or("key file bound overflow")?;
    if usize::try_from(std::fs::metadata(key_path)?.len())? != expected {
        return Err("key file does not fit the declared finite reply".into());
    }
    let key_bytes = std::fs::read(key_path)?;
    let native = keyed_reply(
        checkpoint,
        query,
        &key_bytes,
        byte_length,
        false,
        "native_trained",
    )?;
    let initial = keyed_reply(
        founding,
        query,
        &key_bytes,
        byte_length,
        false,
        "founding_constitution",
    )?;
    let tree = keyed_reply(
        checkpoint,
        query,
        &key_bytes,
        byte_length,
        true,
        "executed_trained_tree",
    )?;
    eprintln!("alpha native keyed_releases_complete target_not_opened=true");
    // This prefix was fixed by the declared reply length, independently of any released bytes.
    let target = std::fs::read(target_path)?;
    let target = target
        .get(..byte_length)
        .ok_or("adjacent source is shorter than the declared comparison")?;
    let target_classes = digits(target);
    let mut readings = Vec::new();
    for (policy, reply) in [
        ("native_trained", &native),
        ("founding_constitution", &initial),
        ("executed_trained_tree", &tree),
    ] {
        let coupling = holonics::receiver::coupling::coupling(&reply.classes, &target_classes)?;
        readings.push(object(&[
            ("policy", quoted(policy)),
            ("lambda", coupling.lambda.to_string()),
            ("F_star", coupling.least_friction.to_string()),
            ("coupling_exact", exact(&coupling)),
        ]));
    }
    Ok(object(&[
        (
            "founding_checkpoint_sha256",
            quoted(&sha256(&founding.bytes()?)?),
        ),
        ("key_file_sha256", quoted(&sha256(&key_bytes)?)),
        ("key_stream_shared_by_all_arms", "true".into()),
        (
            "arms",
            format!("[{},{},{}]", native.json, initial.json, tree.json),
        ),
        ("target_read_after_all_releases", "true".into()),
        (
            "target_file_sha256",
            quoted(&sha256(&std::fs::read(target_path)?)?),
        ),
        ("target_fixed_prefix_bytes", byte_length.to_string()),
        (
            "ordered_contact_readings",
            format!("[{}]", readings.join(",")),
        ),
    ]))
}

fn last_deposit(reading: &DepositReading) -> String {
    format!(
        "{{\"commit\":{},\"stepped\":{},\"landmarks\":{},\"steps_exact\":{},\"joint_exact\":{},\"rounding_refusals_exact\":{},\"released_exact\":{}}}",
        reading.commit,
        reading.stepped,
        reading.landmarks,
        exact(&reading.steps),
        exact(&reading.joint),
        exact(&reading.vanished),
        exact(&reading.released)
    )
}
fn object(fields: &[(&str, String)]) -> String {
    format!(
        "{{{}}}",
        fields
            .iter()
            .map(|(key, value)| format!("{}:{value}", quoted(key)))
            .collect::<Vec<_>>()
            .join(",")
    )
}
fn scope_description(scope: ObservedEpochDepositionScope) -> &'static str {
    match scope {
        ObservedEpochDepositionScope::All => "All: ordinary physical-factor policy",
        ObservedEpochDepositionScope::LocalReceivingReturn => "LocalReceivingReturn: actual retained-fibre R-only local response; no whole-section finite comparison requested",
        ObservedEpochDepositionScope::NormalMaps => {
            "NormalMaps: physical factor deposition requests and statistics held"
        }
        ObservedEpochDepositionScope::NormalMapsAndChannelDissipation => {
            "NormalMapsAndChannelDissipation: C/K and other physical families held; actual D requires same-opening finite comparison and zero held work"
        }
        ObservedEpochDepositionScope::NormalMapsAndChannelMaterial => {
            "NormalMapsAndChannelMaterial: actual C/K/D endpoint requires same-opening finite comparison and endpoint held-work closure"
        }
    }
}
fn parse_fork_scope(value: &str) -> Result<ObservedEpochDepositionScope> {
    match value {
        "normal-maps" => Ok(ObservedEpochDepositionScope::NormalMaps),
        "local-receiving-return-v1" => Ok(ObservedEpochDepositionScope::LocalReceivingReturn),
        "normal-maps-channel-dissipation" => Ok(ObservedEpochDepositionScope::NormalMapsAndChannelDissipation),
        "normal-maps-channel-material" => Ok(ObservedEpochDepositionScope::NormalMapsAndChannelMaterial),
        _ => Err("scope fork requires normal-maps, normal-maps-channel-dissipation, or normal-maps-channel-material".into()),
    }
}
/// Explicit exterior run policy; it adds no native state or activation history. A caller
/// continuing with grain requests it again, while the absolute receiver-clock target remains
/// a function of the saved state. The ordinary ingest and query policies are unchanged.
fn ingest_reference(command: &str, scope: ObservedEpochDepositionScope) -> Result<Reference> {
    match command {
        "ingest" => Ok(port()),
        "ingest-grain"
            if scope == ObservedEpochDepositionScope::NormalMapsAndChannelDissipation =>
        {
            Ok(port().with_refining_grain())
        }
        "ingest-grain" => Err("grain ingest requires the explicitly forked channel-D scope".into()),
        _ => Err("unknown ingest policy".into()),
    }
}

/// The codec's exact base4 span, including offsets that are not octet boundaries. This lets a
/// continuing experiment consume the next heard symbols without replay, padding or skipping.
fn source_cell_span(excerpt: &[u8], limit: Option<usize>, offset: usize) -> Result<Vec<usize>> {
    let mut cells = digits(excerpt);
    if offset >= cells.len() {
        return Err("source-cell offset must begin within the excerpt".into());
    }
    cells.drain(..offset);
    if let Some(limit) = limit {
        if limit == 0 || limit > cells.len() {
            return Err("source-cell control must select a nonempty actual excerpt span".into());
        }
        cells.truncate(limit);
    }
    Ok(cells)
}

fn run() -> Result<()> {
    let started = Instant::now();
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("complete-language") => complete_language::run(&args[1..])?,
        Some("init") if args.len() == 3 => {
            let population = args[2].parse()?;
            let (field, initial, pairing) = declaration(population)?;
            let reference = port();
            let mut resident = reference.mount_with(&field, &Current::at_rest(&field), initial)?;
            let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing)?;
            reference.ingest(&mut resident, None, &boundary.encode(&[])?)?;
            let stream = ObservedStream::new(resident, ObservedCrib::new(0), ObservedEpochDepositionScope::NormalMaps)?;
            let checkpoint = Checkpoint { population, stream, provenance: String::new() };
            let constitution = material_hash(checkpoint.stream.resident())?;
            let warm = query_reading(&checkpoint, WARM_QUERY)?;
            let (bytes, hash) = checkpoint.publish(&args[1])?;
            println!("{}", object(&[
                ("kind", quoted("init")), ("checkpoint_path", quoted(&args[1])),
                ("checkpoint_sha256", quoted(&hash)), ("checkpoint_bytes", bytes.to_string()),
                ("constitution_sha256", quoted(&constitution)), ("total_cells", "0".into()),
                ("accepted_total_cells", "0".into()), ("pending_cells", "0".into()),
                ("physical_epoch_cell_bound", checkpoint.stream.epoch_bound().to_string()),
                ("deposition_scope", quoted(scope_description(checkpoint.stream.scope()))),
                ("warm_query", warm), ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ]));
        }
        Some("fork-scope") if args.len() == 5 => {
            let (opening, input_hash) = Checkpoint::load(&args[1], args[3].parse()?)?;
            let scope = parse_fork_scope(&args[4])?;
            let fork = opening.fork_scope(scope)?;
            let before = opening.stream.resident().continuing_state(0)?;
            if fork.stream.resident().continuing_state(0)? != before
                || fork.stream.crib() != opening.stream.crib()
                || fork.stream.pending_classes() != opening.stream.pending_classes()
                || fork.provenance != opening.provenance
            {
                return Err("a scope fork must preserve all existing native and unfinished state".into());
            }
            let (bytes, hash) = fork.publish(&args[2])?;
            println!("{}", object(&[
                ("kind", quoted("fork_scope")), ("input_checkpoint_sha256", quoted(&input_hash)),
                ("checkpoint_path", quoted(&args[2])), ("checkpoint_sha256", quoted(&hash)),
                ("checkpoint_bytes", bytes.to_string()), ("native_state_unchanged", "true".into()),
                ("scope_before", exact(&opening.stream.scope())), ("scope_after", exact(&scope)),
                ("deposition_scope", quoted(scope_description(scope))),
                ("published_cells", total(fork.stream.resident())?.to_string()),
                ("accepted_total_cells", fork.stream.accepted_cells()?.to_string()),
                ("pending_cells", fork.stream.pending_classes().len().to_string()),
                ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ]));
        }
        Some(command @ ("ingest" | "ingest-grain"))
            if args.len() == 8 || args.len() == 9 || args.len() == 10 || args.len() == 12 => {
            let budget: u64 = args[7].parse()?;
            let max_source: usize = args[6].parse()?;
            let (mut checkpoint, input_hash) = Checkpoint::load(&args[1], budget)?;
            let first: usize = args[4].parse()?;
            let last: usize = args[5].parse()?;
            if first == 0 || last < first { return Err("invalid inclusive source line range".into()); }
            let source = std::fs::read(&args[3])?;
            let mut excerpt = Vec::new(); let mut found = 0usize;
            for (at, line) in source.split_inclusive(|byte| *byte == b'\n').enumerate() {
                if (first..=last).contains(&(at + 1)) { excerpt.extend_from_slice(line); found += 1; }
            }
            if found != last - first + 1 || excerpt.len() > max_source { return Err("source range absent or exceeds declared source-byte workload".into()); }
            let file_hash = sha256(&source)?; let excerpt_hash = sha256(&excerpt)?;
            let before = material_hash(checkpoint.stream.resident())?;
            let reference = ingest_reference(command, checkpoint.stream.scope())?;
            let pairing = declaration(checkpoint.population)?.2;
            let complete_excerpt_cells = digits(&excerpt).len();
            let source_cell_offset = if args.len() == 10 { args[9].parse()? } else { 0 };
            let limit = if args.len() == 9 || args.len() == 10 { Some(args[8].parse()?) } else { None };
            let source_cells = source_cell_span(&excerpt, limit, source_cell_offset)?;
            let mut final_deposit = None; let mut stepped = 0u64;
            let mut published = 0usize; let mut accepted = 0usize;
            let mut whole = 0usize; let mut joint = 0usize; let mut receiving_only = 0usize; let mut neutral = 0usize;
            let mut outcomes = Vec::new();
            let mut class_series = Vec::new();
            let mut stage_events = Vec::new();
            // The chunk bound is the actual maximum time to this declared receiving tick.
            // A chunk may contain multiple actual sections after a key relocation.
            for chunk in source_cells.chunks(checkpoint.stream.epoch_bound()) {
                let delivery_opening = total(checkpoint.stream.resident())?;
                let receipt = checkpoint.stream.receive_diagnosed(&reference, &pairing, chunk, &mut |attempt, refusal| {
                    let event = object(&[
                        ("delivery_opening_published_cells", delivery_opening.to_string()),
                        ("attempt", exact(&attempt)), ("stage_refusal_exact", exact(refusal)),
                    ]);
                    // Emitted before the original native error returns, including a fatal
                    // receiving-only restage. The resident retains no diagnostic history.
                    eprintln!("alpha native stage_refusal {event}");
                    stage_events.push(event);
                })?;
                accepted += receipt.accepted; published += receipt.published;
                for epoch in receipt.epochs {
                    let opening = epoch.cells.checked_sub(u64::try_from(epoch.consumed)?)
                        .ok_or("epoch source position underflow")?;
                    for (at, read) in epoch.reads.iter().enumerate() {
                        // These are the owner's pre-reception class readings. Their absolute
                        // source positions may include a fragment accepted by a preceding call.
                        // Phase comparison and physical work are distinct receipts below.
                        class_series.push(object(&[
                            ("source_position_zero_based", (opening + u64::try_from(at)?).to_string()),
                            ("class_code_bits", interval(&read.code)),
                            ("tree_only_code_bits", read.tree.as_ref().map_or_else(|| "null".into(), interval)),
                            ("scored_face_exact", exact(&read.scored_face)),
                            ("released_class_masses", format!("[{}]", read.released.iter().map(rational).collect::<Vec<_>>().join(","))),
                        ]));
                    }
                    match epoch.outcome { ObservedEpochOutcome::Whole => whole += 1, ObservedEpochOutcome::Joint => joint += 1, ObservedEpochOutcome::ReceivingOnly => receiving_only += 1, ObservedEpochOutcome::Neutral => neutral += 1 }
                    stepped += epoch.deposit.stepped;
                    outcomes.push(object(&[
                        ("source_start_zero_based", opening.to_string()),
                        ("source_end_exclusive", epoch.cells.to_string()),
                        ("material_commit", epoch.deposit.commit.to_string()),
                        ("actual_receiving_ingress", epoch.deposit.epoch.as_ref().map_or_else(|| "null".into(), |read| read.actual_receiving_ingress.to_string())),
                        ("channel_grain_exact", epoch.deposit.epoch.as_ref().and_then(|read| read.channel_grain.as_ref()).map_or_else(|| "null".into(), exact)),
                        ("channel_grain_restage_exact", epoch.deposit.epoch.as_ref().and_then(|read| read.channel_grain_restaged.as_ref()).map_or_else(|| "null".into(), exact)),
                        ("receiving_quantum_projection", epoch.deposit.epoch.as_ref()
                            .and_then(|read| read.quantum_projection.as_ref())
                            .map_or_else(|| "null".into(), |read| object(&[
                                ("eligible", read.eligible.to_string()),
                                ("skip_reason", read.skip_reason.map_or_else(|| "null".into(), quoted)),
                                ("trials", format!("[{}]", read.trials.iter().map(|trial| object(&[
                                    ("row", trial.row.to_string()),
                                    ("column", trial.column.to_string()),
                                    ("sign", trial.sign.to_string()),
                                    ("normal_admitted", trial.normal_admitted.to_string()),
                                    ("actual_admitted", trial.actual_admitted.to_string()),
                                    ("refusal", exact(&trial.refusal)),
                                    ("reason", trial.reason.as_deref().map_or_else(|| "null".into(), quoted)),
                                ])).collect::<Vec<_>>().join(","))),
                            ]))),
                        ("locus_deposits", epoch.deposit.epoch.as_ref().map_or_else(|| "[]".into(), |read| {
                            format!("[{}]", read.loci.iter().map(|locus| object(&[
                                ("locus", exact(&locus.locus)),
                                ("records", locus.records.to_string()),
                                ("represented_move", (locus.represented_step.numerator_l1_bound > 0.into()).to_string()),
                                ("represented_step_numerator_l1_bound", quoted(&locus.represented_step.numerator_l1_bound.to_string())),
                                ("gamma", rational(&locus.gamma)),
                                ("eta", rational(&locus.eta)),
                                ("normal_fall", rational(&locus.fall)),
                                ("direction_divisor", quoted(&locus.direction_divisor.to_string())),
                                ("joint_direction_exact", exact(&locus.joint_direction)),
                                ("retained_news_metric_squared", locus.retained_news_metric_squared.as_ref().map_or_else(|| "null".into(), rational)),
                                ("fresh_news_metric_squared", locus.fresh_news_metric_squared.as_ref().map_or_else(|| "null".into(), rational)),
                                ("crossings", locus.storage.crossings.to_string()),
                                ("map_lattice", locus.storage.map_lattice.to_string()),
                                ("source_refinement", locus.storage.source_refinement.to_string()),
                                ("gram_update_metadata", exact(&locus.gram_update)),
                                ("scale_reading_exact", exact(&locus.scale)),
                                ("fresh_news_metadata", exact(&locus.fresh_news)),
                                ("retained_news_metadata", exact(&locus.storage.news)),
                            ])).collect::<Vec<_>>().join(","))
                        })),
                        ("consumed", epoch.consumed.to_string()),
                        ("outcome", exact(&epoch.outcome)), ("deposition_scope", exact(&epoch.deposition_scope)),
                        ("publication_attempt", exact(&epoch.publication_attempt)),
                        ("joint_attempted", epoch.joint_attempted.to_string()),
                        ("joint_directions_exact", exact(&epoch.joint_directions)),
                        ("joint_comparison_exact", exact(&epoch.joint_comparison)),
                        ("joint_refusal", exact(&epoch.joint_refusal)),
                        ("joint_stage_refusal_exact", exact(&epoch.joint_stage_refusal)),
                        ("joint_probe_state", exact(&epoch.joint_probe_state)),
                        ("comparison_exact", exact(&epoch.comparison)), ("whole_refusal", exact(&epoch.whole_refusal)),
                        ("whole_stage_refusal_exact", exact(&epoch.whole_stage_refusal)),
                        ("probe_state", exact(&epoch.probe_state)),
                        ("wall_ns", object(&[
                            ("forward_batch", epoch.wall.forward_batch.as_nanos().to_string()),
                            ("compare_return_compose_batch", epoch.wall.compare_return_compose_batch.as_nanos().to_string()),
                            ("compare_preparation", epoch.wall.compare_preparation.as_nanos().to_string()),
                            ("return_join", epoch.wall.return_join.as_nanos().to_string()),
                            ("ordered_publication", epoch.wall.ordered_publication.as_nanos().to_string()),
                            ("grouped_deposit", epoch.wall.grouped_deposit.as_nanos().to_string()),
                            ("whole_stage", epoch.wall.whole_stage.map_or_else(|| "null".into(), |wall| wall.as_nanos().to_string())),
                            ("whole_probe", epoch.wall.whole_probe.map_or_else(|| "null".into(), |wall| wall.as_nanos().to_string())),
                            ("joint_stage", epoch.wall.joint_stage.map_or_else(|| "null".into(), |wall| wall.as_nanos().to_string())),
                            ("joint_probe", epoch.wall.joint_probe.map_or_else(|| "null".into(), |wall| wall.as_nanos().to_string())),
                            ("receiving_only_stage", epoch.wall.receiving_only_stage.map_or_else(|| "null".into(), |wall| wall.as_nanos().to_string())),
                            ("final_arrived_reread", epoch.wall.final_arrived_reread.as_nanos().to_string()),
                            ("precision_close", epoch.wall.precision_close.as_nanos().to_string()),
                            ("prefix_forks", epoch.wall.prefix_forks.as_nanos().to_string()),
                        ])),
                        ("return_worker_elapsed_sums_ns", format!("[{}]", epoch.wall.return_worker_sums.iter().map(|wall| wall.as_nanos().to_string()).collect::<Vec<_>>().join(","))),
                        ("deposit_subphase_intervals", format!("[{}]", epoch.wall.deposit_subphases.iter().map(|(phase, wall)| object(&[
                            ("phase", quoted(phase)), ("elapsed_ns", wall.as_nanos().to_string()),
                        ])).collect::<Vec<_>>().join(","))),
                        ("probe_subphase_intervals", format!("[{}]", epoch.wall.probe_subphases.iter().map(|(attempt, phase, wall)| object(&[
                            ("attempt", exact(attempt)), ("phase", quoted(phase)), ("elapsed_ns", wall.as_nanos().to_string()),
                        ])).collect::<Vec<_>>().join(","))),
                        ("receiving_certificate_exact", exact(&epoch.deposit.epoch)),
                        ("actual_certificate_steps_exact", exact(&epoch.deposit.steps)),
                        ("actual_channel_d_steps", epoch.deposit.steps.iter().filter(|(locus, step)| {
                            matches!(locus, holonics::hnn::constitution::Locus::Channel(_))
                                && step.family == holonics::hnn::constitution::Family::Factor(2)
                        }).count().to_string()),
                        ("first_law_before_precision_exact", exact(&epoch.precision.balance_before)),
                        ("first_law_after_precision_exact", exact(&epoch.precision.balance_after)),
                        ("physical_energy_closes", epoch.energy.closes().to_string()),
                        ("physical_form_changed", epoch.energy.physical_form_changed.to_string()),
                        ("physical_deposition_work", rational(&epoch.energy.deposition_work)),
                        ("physical_energy_exact", exact(&epoch.energy)),
                    ]));
                    eprintln!("alpha native epoch_receipt {}", outcomes.last().expect("one successful epoch has its exterior receipt"));
                    eprintln!("alpha native grouped consumed={} commit={} outcome={:?} accepted={accepted} published={published} pending={} elapsed_ns={}", epoch.consumed, epoch.deposit.commit, epoch.outcome, receipt.pending, started.elapsed().as_nanos());
                    final_deposit = Some(epoch.deposit);
                }
            }
            let after = material_hash(checkpoint.stream.resident())?;
            // Grain opt-in is a policy of this call, reported in its exterior receipt below.
            // Source provenance in a continuing checkpoint records the admitted span, not that policy.
            checkpoint.provenance.push_str(&object(&[
                ("source", quoted(&args[3])), ("source_file_sha256", quoted(&file_hash)),
                ("first_line", first.to_string()), ("last_line", last.to_string()),
                ("excerpt_sha256", quoted(&excerpt_hash)), ("bytes", excerpt.len().to_string()),
                ("accepted_cells", accepted.to_string()),
                ("source_cell_offset", source_cell_offset.to_string()),
            ]));
            checkpoint.provenance.push('\n');
            let warm = query_reading(&checkpoint, WARM_QUERY)?;
            let warm_keyed = if args.len() == 12 {
                let (founding, _) = Checkpoint::load(&args[10], budget)?;
                let batch = std::fs::read_to_string(&args[11])?;
                let mut readings = Vec::new();
                for row in batch.lines() {
                    let columns: Vec<_> = row.split('\t').collect();
                    if columns.len() != 3 || columns[0].is_empty() {
                        return Err("warm query batch requires id, prompt path, adjacent source path".into());
                    }
                    let prompt = std::fs::read_to_string(columns[1])?;
                    let controls = keyed_controls(&checkpoint, &founding, &prompt, &args[8], args[9].parse()?, columns[2])?;
                    readings.push(object(&[("query_id", quoted(columns[0])), ("keyed_replies", controls)]));
                }
                format!("[{}]", readings.join(","))
            } else { "null".into() };
            let (bytes, hash) = checkpoint.publish(&args[2])?;
            println!("{}", object(&[
                ("kind", quoted(command)), ("checkpoint_path", quoted(&args[2])),
                ("receiver_clock_grain_requested", (command == "ingest-grain").to_string()),
                ("source_cell_offset", source_cell_offset.to_string()),
                ("input_checkpoint_sha256", quoted(&input_hash)), ("checkpoint_sha256", quoted(&hash)),
                ("checkpoint_bytes", bytes.to_string()), ("before_constitution_sha256", quoted(&before)),
                ("after_constitution_sha256", quoted(&after)), ("source_file_sha256", quoted(&file_hash)),
                ("excerpt_sha256", quoted(&excerpt_hash)), ("first_line", first.to_string()), ("last_line", last.to_string()),
                ("source_excerpt_bytes", excerpt.len().to_string()),
                ("source_excerpt_cells", complete_excerpt_cells.to_string()),
                ("complete_excerpt_accepted", (accepted == complete_excerpt_cells).to_string()),
                ("heard_bytes", (accepted / 4).to_string()),
                ("partial_octet_cells", (accepted % 4).to_string()), ("heard_cells", accepted.to_string()),
                ("accepted_cells", accepted.to_string()), ("published_cells", published.to_string()),
                ("pending_cells", checkpoint.stream.pending_classes().len().to_string()),
                ("accepted_total_cells", checkpoint.stream.accepted_cells()?.to_string()),
                ("total_cells", total(checkpoint.stream.resident())?.to_string()),
                ("physical_epoch_cell_bound", checkpoint.stream.epoch_bound().to_string()),
                ("native_steps", stepped.to_string()), ("whole_epochs", whole.to_string()),
                ("joint_epochs", joint.to_string()), ("receiving_only_epochs", receiving_only.to_string()), ("neutral_epochs", neutral.to_string()),
                ("certification_scope", quoted(if checkpoint.stream.scope()==ObservedEpochDepositionScope::LocalReceivingReturn { "local R NormalLaw; complete whole-section finite comparison not requested; unfinished actual input pending; source E family response is separate" } else { "atomic same-opening whole then upstream joint proposal with both native normal predicates and actual finite comparison; held-upstream absorption on domain refusal; Neutral requires publication_attempt to identify its branch; unfinished physical interval pending" })),
                ("deposition_scope", quoted(scope_description(checkpoint.stream.scope()))),
                ("epoch_outcomes", format!("[{}]", outcomes.join(","))),
                ("class_code_scope", quoted("prequential class comparison through the actual model/tree face; separate tree-only control; phase improvement alone is not class prediction improvement")),
                ("class_code_series", format!("[{}]", class_series.join(","))),
                ("stage_refusal_events", format!("[{}]", stage_events.join(","))),
                ("last_deposit", final_deposit.as_ref().map_or_else(|| "null".to_owned(), last_deposit)),
                ("warm_query", warm), ("warm_keyed_replies", warm_keyed), ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ]));
        }
        Some("query-fibre") if args.len() == 7 => {
            let (checkpoint, hash) = Checkpoint::load(&args[1], args[2].parse()?)?;
            let prompt_bytes = std::fs::read(&args[3])?;
            let prompt = std::str::from_utf8(&prompt_bytes)?;
            let keys = std::fs::read(&args[6])?;
            let reading = retained_fibre_query_controls(&checkpoint, prompt, args[4].parse()?, args[5].parse()?, &keys)?;
            println!("{}", object(&[("kind",quoted("query-fibre")),("checkpoint_sha256",quoted(&hash)),
                ("prompt_sha256",quoted(&sha256(&prompt_bytes)?)),("keys_sha256",quoted(&sha256(&keys)?)),
                ("reading",reading),("elapsed_ns",started.elapsed().as_nanos().to_string())]));
        }
        Some("query") if args.len() == 6 && args[3] == "--frozen-r-target-prefix" => {
            let (checkpoint, hash) = Checkpoint::load(&args[1], args[2].parse()?)?;
            let maximum: usize = args[5].parse()?;
            if maximum == 0 || maximum > QUERY_BYTE_BUDGET {
                return Err("frozen-R target workload declares at most128 source bytes".into());
            }
            if std::fs::metadata(&args[4])?.len() > u64::try_from(maximum)? {
                return Err("target passage exceeds the declared source-byte workload".into());
            }
            let target = std::fs::read(&args[4])?;
            if target.len() > maximum { return Err("target changed beyond its source-byte workload".into()); }
            let target_hash = sha256(&target)?;
            let reading = frozen_r_target_prefix(&checkpoint, &target)?;
            println!("{}", object(&[
                ("kind", quoted("frozen_r_target_prefix_query")),
                ("checkpoint_sha256", quoted(&hash)), ("target_sha256", quoted(&target_hash)),
                ("reading", reading), ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ]));
        }
        Some("query") if args.len() == 3 || args.len() == 4 || args.len() == 6 || args.len() == 10 => {
            let (checkpoint, hash) = Checkpoint::load(&args[1], args[2].parse()?)?;
            let query = args.get(3).map_or(WARM_QUERY, String::as_str);
            let constitution = material_hash(checkpoint.stream.resident())?;
            let reading = query_reading(&checkpoint, query)?;
            let controls = if args.len() >= 6 {
                conditional_query_controls(&checkpoint, query, args[4].parse()?, args[5].parse()?)?
            } else { "null".into() };
            let keyed = if args.len() == 10 {
                let (founding, _) = Checkpoint::load(&args[8], args[2].parse()?)?;
                keyed_controls(&checkpoint, &founding, query, &args[6], args[7].parse()?, &args[9])?
            } else { "null".into() };
            println!("{}", object(&[
                ("kind", quoted("query")), ("checkpoint_sha256", quoted(&hash)),
                ("constitution_sha256", quoted(&constitution)), ("total_cells", total(checkpoint.stream.resident())?.to_string()),
                ("accepted_total_cells", checkpoint.stream.accepted_cells()?.to_string()),
                ("pending_cells", checkpoint.stream.pending_classes().len().to_string()),
                ("reading", reading), ("elapsed_ns", started.elapsed().as_nanos().to_string()),
                ("conditional_sections", controls),
                ("keyed_replies", keyed),
            ]));
        }
        _ => return Err("usage: solenoidal_alpha init OUTPUT POPULATION | fork-scope INPUT OUTPUT MAX_CHECKPOINT_BYTES normal-maps|normal-maps-channel-dissipation|normal-maps-channel-material | ingest|ingest-grain INPUT OUTPUT ORIGINAL_FILE FIRST_LINE LAST_LINE MAX_SOURCE_BYTES MAX_CHECKPOINT_BYTES [SOURCE_CELL_LIMIT [SOURCE_CELL_OFFSET] | KEY_FILE DRAW_BYTES FOUNDING_CHECKPOINT WARM_QUERY_BATCH_TSV] | query INPUT MAX_CHECKPOINT_BYTES [QUERY_UTF8 [SECTION_BYTES ORACLE_BUDGET [KEY_FILE DRAW_BYTES FOUNDING_CHECKPOINT ADJACENT_SOURCE_FILE]]]".into()),
    }
    Ok(())
}
fn main() {
    if let Err(error) = run() {
        eprintln!("alpha error: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cumulative_source_total_and_crib_restore_survive_joint_closure() {
        let (field, initial, pairing) = declaration(4096).unwrap();
        let reference = port();
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), initial.clone())
            .unwrap();
        let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let mut crib = ObservedCrib::new(0);
        let joint_cells = field
            .rings()
            .iter()
            .try_fold(1usize, |product, ring| {
                product.checked_mul(usize::try_from(ring.period()).unwrap())
            })
            .unwrap();
        let mut closed = false;
        // Exercise the native clock/close owner without claiming this source-only control
        // teaches anything. Its purpose is to distinguish the two native cell readings.
        for at in 0..joint_cells + 1 {
            let receipt = reference
                .ingest_class_continuing(
                    &mut resident,
                    &mut crib,
                    &pairing,
                    at % field.alphabet(),
                    None,
                )
                .unwrap();
            closed |= receipt.close.is_some();
        }
        assert!(
            closed,
            "the control must actually cross a joint-clock closure"
        );
        let aeon_cells = usize::try_from(resident.continuing().unwrap().1).unwrap();
        assert!(aeon_cells < joint_cells + 1);
        assert_eq!(total(&resident).unwrap(), joint_cells + 1);
        assert_eq!(crib.next_position(), joint_cells + 1);
        let saved = resident.continuing_state(0).unwrap();
        let state = ContinuingState::from_text(&saved.to_text(), MATERIAL_BIT_BUDGET).unwrap();
        let cold = reference
            .mount_continued(&field, &Current::at_rest(&field), initial, &state)
            .unwrap();
        assert_eq!(total(&cold).unwrap(), joint_cells + 1);
        let restored_crib = ObservedCrib::from_unplaced_checkpoint(
            &field,
            cold.current(),
            total(&cold).unwrap(),
            &crib.unplaced_checkpoint().unwrap(),
        )
        .unwrap();
        assert_eq!(restored_crib, crib);
        // The strict guard still refuses the aeon-local count that caused the real failure.
        assert!(
            ObservedCrib::from_unplaced_checkpoint(
                &field,
                cold.current(),
                aeon_cells,
                &crib.unplaced_checkpoint().unwrap()
            )
            .is_err()
        );
    }
    #[test]
    fn channel_d_scope_fork_preserves_full_native_and_pending_state() {
        let (field, initial, pairing) = declaration(4096).unwrap();
        let reference = port();
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), initial)
            .unwrap();
        let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let mut stream = ObservedStream::new(
            resident,
            ObservedCrib::new(0),
            ObservedEpochDepositionScope::NormalMaps,
        )
        .unwrap();
        stream.receive(&reference, &pairing, &[0, 1, 2, 3]).unwrap();
        let opening = Checkpoint {
            population: 4096,
            stream,
            provenance: "existing exterior provenance\n".into(),
        };
        let old_bytes = opening.bytes().unwrap();
        let fork = opening
            .fork_scope(parse_fork_scope("normal-maps-channel-dissipation").unwrap())
            .unwrap();
        assert_eq!(
            fork.stream.scope(),
            ObservedEpochDepositionScope::NormalMapsAndChannelDissipation
        );
        assert_eq!(
            fork.stream.resident().continuing_state(0).unwrap(),
            opening.stream.resident().continuing_state(0).unwrap()
        );
        assert_eq!(fork.stream.crib(), opening.stream.crib());
        assert_eq!(
            fork.stream.pending_classes(),
            opening.stream.pending_classes()
        );
        assert_eq!(fork.provenance, opening.provenance);
        assert_eq!(
            fork.stream.accepted_cells().unwrap(),
            opening.stream.accepted_cells().unwrap()
        );
        assert_ne!(fork.bytes().unwrap(), old_bytes);
        assert_eq!(opening.bytes().unwrap(), old_bytes);
        let restored = ObservedStream::restore_checkpoint(
            fork.stream.resident().clone(),
            fork.stream.crib().clone(),
            &fork.stream.pending_checkpoint(),
        )
        .unwrap();
        assert_eq!(restored.scope(), fork.stream.scope());
        assert_eq!(
            restored.pending_checkpoint(),
            fork.stream.pending_checkpoint()
        );
        let back = fork
            .fork_scope(parse_fork_scope("normal-maps").unwrap())
            .unwrap();
        assert_eq!(back.bytes().unwrap(), old_bytes);
        let material_scope = parse_fork_scope("normal-maps-channel-material").unwrap();
        assert_eq!(
            material_scope,
            ObservedEpochDepositionScope::NormalMapsAndChannelMaterial
        );
        let material = opening.fork_scope(material_scope).unwrap();
        assert_eq!(material.stream.scope(), material_scope);
        assert!(
            material
                .stream
                .pending_checkpoint()
                .contains("normal-maps-channel-material")
        );
        assert!(parse_fork_scope("all").is_err());
        assert!(parse_fork_scope("normal-map").is_err());
    }

    #[test]
    fn grain_ingest_policy_requires_d_scope_and_exact_non_octet_source_span() {
        assert!(
            ingest_reference(
                "ingest-grain",
                ObservedEpochDepositionScope::NormalMapsAndChannelDissipation
            )
            .is_ok()
        );
        assert!(
            ingest_reference("ingest-grain", ObservedEpochDepositionScope::NormalMaps).is_err()
        );
        assert!(ingest_reference("ingest-grain", ObservedEpochDepositionScope::All).is_err());
        assert!(ingest_reference("ingest", ObservedEpochDepositionScope::NormalMaps).is_ok());
        assert!(
            ingest_reference(
                "unknown",
                ObservedEpochDepositionScope::NormalMapsAndChannelDissipation
            )
            .is_err()
        );
        // 0x1b = 00 01 10 11, 0xe4 = 11 10 01 00. The requested non-octet span is exact.
        assert_eq!(
            source_cell_span(&[0x1b, 0xe4], Some(4), 2).unwrap(),
            vec![2, 3, 3, 2]
        );
        assert_eq!(
            source_cell_span(&[0x1b, 0xe4], None, 0).unwrap(),
            digits(&[0x1b, 0xe4])
        );
        assert!(source_cell_span(&[0x1b], Some(0), 0).is_err());
        assert!(source_cell_span(&[0x1b], Some(3), 2).is_err());
        assert!(source_cell_span(&[0x1b], None, 4).is_err());
    }
    #[test]
    fn retained_fibre_section_is_bounded_self_receives_and_preserves_original_checkpoint() {
        let (field, initial, pairing) = declaration(4096).unwrap();
        let reference = port();
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), initial)
            .unwrap();
        let boundary = PairedObservation::admit(&field, resident.constitution(), &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let checkpoint = Checkpoint {
            population: 4096,
            stream: ObservedStream::new(
                resident,
                ObservedCrib::new(0),
                ObservedEpochDepositionScope::NormalMaps,
            )
            .unwrap(),
            provenance: String::new(),
        };
        let before = checkpoint.bytes().unwrap();
        let reading = retained_fibre_query_controls(&checkpoint, "", 1, 1, &[0; 32]).unwrap();
        assert!(reading.contains("OracleBudget"));
        assert!(reading.contains("\"self_received_cells\":4"));
        assert!(reading.contains("\"raw_bytes\":[0]"));
        assert!(reading.contains("\"retained_checkpoint_unchanged\":true"));
        assert_eq!(checkpoint.bytes().unwrap(), before);
    }
}
