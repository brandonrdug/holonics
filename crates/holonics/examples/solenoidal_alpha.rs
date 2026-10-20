//! Native, bounded Alpha boundary: online observed learning and exact cold continuation.
//! A three-ring specialization of listener/octets.rs's serial declared field, with the
//! existing paired source founder and ordinary one-cell transactional comparison/deposition.
//! The byte boundary uses four base-4 digits per octet; it does not prescribe answers.
//! Retention is ContinuingState (material, tree, clock, moment, address, charts and carry).
//! Only the bounded current-aeon closing crib is carried beside it. No source tape is saved.
//! The native grouped comparison publishes only at actual receiving ticks. Source/contrast/
//! readout maps share the whole candidate probe; a refused whole branch restages the certified
//! receiving-only policy. Physical factor requests/statistics are explicitly held (NormalMaps).
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
use holonics::hnn::receiving::cells::CellLaw;
use holonics::hnn::reference::observed::{
    ObservedCrib, ObservedEpochDepositionScope, ObservedEpochOutcome, ObservedStream,
};
use holonics::hnn::reference::{ExposedResident, Resident};
use holonics::hnn::{ExecutionPort, Reference};
use holonics::ratio::{Rat, algebraic::ExactInterval, integer, rat};
use std::{
    error::Error,
    io::{Read, Write},
    path::Path,
    process::{Command, Stdio},
    time::Instant,
};

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
    object(&[("lower", rational(&value.lower)), ("upper", rational(&value.upper))])
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
    bytes
        .iter()
        .flat_map(|byte| {
            [
                usize::from(byte >> 6),
                usize::from((byte >> 4) & 3),
                usize::from((byte >> 2) & 3),
                usize::from(byte & 3),
            ]
        })
        .collect()
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
fn run() -> Result<()> {
    let started = Instant::now();
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
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
                ("deposition_scope", quoted("NormalMaps: physical factor deposition requests and statistics held")),
                ("warm_query", warm), ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ]));
        }
        Some("ingest") if args.len() == 8 || args.len() == 9 => {
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
            let reference = port(); let pairing = declaration(checkpoint.population)?.2;
            let mut source_cells = digits(&excerpt);
            let complete_excerpt_cells = source_cells.len();
            if let Some(limit) = args.get(8) {
                let limit: usize = limit.parse()?;
                if limit == 0 || limit > source_cells.len() { return Err("source-cell control must select a nonempty actual excerpt prefix".into()); }
                source_cells.truncate(limit);
            }
            let mut final_deposit = None; let mut stepped = 0u64;
            let mut published = 0usize; let mut accepted = 0usize;
            let mut whole = 0usize; let mut receiving_only = 0usize; let mut neutral = 0usize;
            let mut outcomes = Vec::new();
            let mut class_series = Vec::new();
            // The chunk bound is the actual maximum time to this declared receiving tick.
            // A chunk may contain multiple actual sections after a key relocation.
            for chunk in source_cells.chunks(checkpoint.stream.epoch_bound()) {
                let receipt = checkpoint.stream.receive(&reference, &pairing, chunk)?;
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
                    match epoch.outcome { ObservedEpochOutcome::Whole => whole += 1, ObservedEpochOutcome::ReceivingOnly => receiving_only += 1, ObservedEpochOutcome::Neutral => neutral += 1 }
                    stepped += epoch.deposit.stepped;
                    outcomes.push(object(&[
                        ("consumed", epoch.consumed.to_string()),
                        ("outcome", exact(&epoch.outcome)), ("deposition_scope", exact(&epoch.deposition_scope)),
                        ("comparison_exact", exact(&epoch.comparison)), ("whole_refusal", exact(&epoch.whole_refusal)),
                        ("receiving_certificate_exact", exact(&epoch.deposit.epoch)),
                        ("first_law_before_precision_exact", exact(&epoch.precision.balance_before)),
                        ("first_law_after_precision_exact", exact(&epoch.precision.balance_after)),
                        ("physical_energy_closes", epoch.energy.closes().to_string()),
                        ("physical_form_changed", epoch.energy.physical_form_changed.to_string()),
                        ("physical_deposition_work", rational(&epoch.energy.deposition_work)),
                        ("physical_energy_exact", exact(&epoch.energy)),
                    ]));
                    eprintln!("alpha native grouped consumed={} commit={} outcome={:?} accepted={accepted} published={published} pending={} elapsed_ns={}", epoch.consumed, epoch.deposit.commit, epoch.outcome, receipt.pending, started.elapsed().as_nanos());
                    final_deposit = Some(epoch.deposit);
                }
            }
            let after = material_hash(checkpoint.stream.resident())?;
            checkpoint.provenance.push_str(&object(&[
                ("source", quoted(&args[3])), ("source_file_sha256", quoted(&file_hash)),
                ("first_line", first.to_string()), ("last_line", last.to_string()),
                ("excerpt_sha256", quoted(&excerpt_hash)), ("bytes", excerpt.len().to_string()),
                ("accepted_cells", accepted.to_string()),
            ]));
            checkpoint.provenance.push('\n');
            let warm = query_reading(&checkpoint, WARM_QUERY)?;
            let (bytes, hash) = checkpoint.publish(&args[2])?;
            println!("{}", object(&[
                ("kind", quoted("ingest")), ("checkpoint_path", quoted(&args[2])),
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
                ("receiving_only_epochs", receiving_only.to_string()), ("neutral_epochs", neutral.to_string()),
                ("certification_scope", quoted("atomic grouped same-opening whole probe; certified receiving-only restage on whole refusal; unfinished physical interval pending")),
                ("deposition_scope", quoted("NormalMaps: physical factor deposition requests and statistics held; their complete native return still computed")),
                ("epoch_outcomes", format!("[{}]", outcomes.join(","))),
                ("class_code_scope", quoted("prequential class comparison through the actual model/tree face; separate tree-only control; phase improvement alone is not class prediction improvement")),
                ("class_code_series", format!("[{}]", class_series.join(","))),
                ("last_deposit", final_deposit.as_ref().map_or_else(|| "null".to_owned(), last_deposit)),
                ("warm_query", warm), ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ]));
        }
        Some("query") if args.len() == 3 || args.len() == 4 => {
            let (checkpoint, hash) = Checkpoint::load(&args[1], args[2].parse()?)?;
            let query = args.get(3).map_or(WARM_QUERY, String::as_str);
            let constitution = material_hash(checkpoint.stream.resident())?;
            let reading = query_reading(&checkpoint, query)?;
            println!("{}", object(&[
                ("kind", quoted("query")), ("checkpoint_sha256", quoted(&hash)),
                ("constitution_sha256", quoted(&constitution)), ("total_cells", total(checkpoint.stream.resident())?.to_string()),
                ("accepted_total_cells", checkpoint.stream.accepted_cells()?.to_string()),
                ("pending_cells", checkpoint.stream.pending_classes().len().to_string()),
                ("reading", reading), ("elapsed_ns", started.elapsed().as_nanos().to_string()),
            ]));
        }
        _ => return Err("usage: solenoidal_alpha init OUTPUT POPULATION | ingest INPUT OUTPUT ORIGINAL_FILE FIRST_LINE LAST_LINE MAX_SOURCE_BYTES MAX_CHECKPOINT_BYTES [SOURCE_CELL_LIMIT] | query INPUT MAX_CHECKPOINT_BYTES [QUERY_UTF8]".into()),
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
}
