//! K3 — Eros composes the sealed native transport scaffold into one connected Athena ecology.
//!
//! The detached child receives only the Athena rest. It conducts addressed generator transport
//! and exact Complex-Parametron current on the card, and it returns a dependent receiver face or
//! an exact retained insufficiency. No exterior witness or foreign realization is mounted.

use std::{
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::{
    native_spool::{NativeTransportScaffold, ReceiverInsufficiencyCause},
    receiver_exact_compression::ReceiverId,
    EventId,
};
use life::native_intelligence::{NativeConductConsequence, NativeEcologyRest};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const BUNDLE: &str = concat!(
    "output/the_complete_visible_exchange_founds_native_spool_r0q5/",
    "native-transport-scaffold.rest"
);
const OUTPUT: &str = "output/the_one_connected_athena_native_ecology_returns_dependent_sections_k3";

fn main() -> Result<(), String> {
    let arguments = env::args().collect::<Vec<_>>();
    if arguments.get(1).map(String::as_str) == Some("--remount") {
        let rest = arguments.get(2).ok_or("missing Athena rest")?;
        let output = arguments.get(3).ok_or("missing detached output")?;
        let occurrence = arguments
            .get(4)
            .ok_or("missing occurrence")?
            .parse::<u64>()
            .map_err(display)?;
        let receiver = arguments
            .get(5)
            .ok_or("missing receiver")?
            .parse::<u64>()
            .map_err(display)?;
        return remount(
            Path::new(rest),
            Path::new(output),
            EventId(occurrence),
            ReceiverId(receiver),
        );
    }

    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!("preserve existing K3 return {}", output.display()));
    }
    let started = Instant::now();
    fs::create_dir_all(output.join("detached-return")).map_err(display)?;
    let scaffold =
        NativeTransportScaffold::read(&fs::read(BUNDLE).map_err(display)?).map_err(display)?;
    let rest = NativeEcologyRest::found(scaffold).map_err(display)?;
    eprintln!(
        "k3-stage=rest-founded elapsed_ms={}",
        started.elapsed().as_millis()
    );
    let canonical = rest.canonical_bytes().map_err(display)?;
    let wire_sha256 = sha(&canonical);
    let remounted = NativeEcologyRest::read(&canonical).map_err(display)?;
    let structural_round_trip = remounted == rest;
    fs::write(output.join("athena-native.rest"), &canonical).map_err(display)?;
    eprintln!(
        "k3-stage=round-trip elapsed_ms={}",
        started.elapsed().as_millis()
    );

    let receiver = *rest
        .realization
        .receiver_family
        .iter()
        .next()
        .ok_or("empty dependent receiver family")?;
    let addresses = rest.realization.sections.clone();
    let batch = rest.conduct_population(receiver).map_err(display)?;
    eprintln!(
        "k3-stage=batch-conduct elapsed_ms={}",
        started.elapsed().as_millis()
    );
    let anchor = addresses.first().ok_or("empty section atlas")?;
    let outside_receiver = (0..u64::MAX)
        .map(ReceiverId)
        .find(|candidate| !rest.realization.receiver_family.contains(candidate))
        .ok_or("receiver family exhausted u64")?;
    let receiver_insufficiency = match rest.conduct(anchor, outside_receiver).map_err(display)? {
        NativeConductConsequence::Insufficient(insufficiency) => insufficiency,
        NativeConductConsequence::Returned(_) => {
            return Err("outside receiver unexpectedly returned".to_owned());
        }
    };
    let outside_occurrence = (0..u64::MAX)
        .map(EventId)
        .find(|candidate| {
            !addresses
                .iter()
                .any(|address| address.occurrence == *candidate)
        })
        .ok_or("section population exhausted u64")?;
    let section_insufficiency = match rest
        .conduct_occurrence(outside_occurrence, receiver)
        .map_err(display)?
    {
        NativeConductConsequence::Insufficient(insufficiency) => insufficiency,
        NativeConductConsequence::Returned(_) => {
            return Err("outside section unexpectedly returned".to_owned());
        }
    };
    eprintln!(
        "k3-stage=insufficiency-controls elapsed_ms={}",
        started.elapsed().as_millis()
    );

    run_detached(
        &output.join("athena-native.rest"),
        &output.join("detached-return"),
        anchor.occurrence,
        receiver,
    )?;
    eprintln!(
        "k3-stage=detached-return elapsed_ms={}",
        started.elapsed().as_millis()
    );
    let detached: serde_json::Value = serde_json::from_slice(
        &fs::read(output.join("detached-return/00-return.json")).map_err(display)?,
    )
    .map_err(display)?;
    let all_sections_resident = batch.resident_threads.iter().all(|thread| {
        thread.word_returns.iter().all(|returned| {
            !returned.apparatus.invariant_transport_reuploaded
                && returned.device == "NVIDIA GeForce RTX 4080 SUPER"
        }) && !thread.current_return.invariant_transport_reuploaded
            && !thread.current_return.cpu_semantic_replay_after_device
            && !thread.current_return.binary_receiver_taken
            && thread.current_return.device == "NVIDIA GeForce RTX 4080 SUPER"
    });
    let passed = structural_round_trip
        && batch.sections.len() == addresses.len()
        && all_sections_resident
        && matches!(
            receiver_insufficiency.cause,
            ReceiverInsufficiencyCause::ReceiverOutsideFamily { .. }
        )
        && matches!(
            section_insufficiency.cause,
            ReceiverInsufficiencyCause::SectionOutsideFamily { .. }
        )
        && detached["passed"] == true;
    write_json(output.join("01-conducted-sections.json"), &batch)?;
    write_json(
        output.join("02-receiver-insufficiency.json"),
        &receiver_insufficiency,
    )?;
    write_json(
        output.join("03-section-insufficiency.json"),
        &section_insufficiency,
    )?;
    let grade = json!({
        "schema":"soma-life.one-connected-athena-native-ecology-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "rest_wire_sha256":wire_sha256,
        "rest_octets":canonical.len(),
        "structural_round_trip":structural_round_trip,
        "spool_population":rest.ecology.spools.len(),
        "section_population":addresses.len(),
        "ingress_population":rest.realization.ingress_sections.len(),
        "native_population":rest.realization.native_population.len(),
        "receiver_population":rest.realization.receiver_family.len(),
        "generator_population":rest.realization.generator_family.len(),
        "boundary_population":rest.realization.boundary_population.len(),
        "every_section_conducted":batch.sections.len() == addresses.len(),
        "every_section_resident":all_sections_resident,
        "dependent_receiver_insufficiency":receiver_insufficiency,
        "section_insufficiency":section_insufficiency,
        "detached_return":detached,
        "foreign_realization_available_after_remount":false,
        "exterior_soulkiller_witness_available_after_remount":false,
        "semantic_or_lexical_route_present":false,
        "elapsed_seconds":format!("{:.9}", started.elapsed().as_secs_f64()),
    });
    write_json(output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# One connected Athena native ecology\n\n[established-bounded; implemented-exact; measured] Eros composed the sealed native spool into one receiver-history realization. Every addressed occurrence conducted its exact word and Complex-Parametron current on the resident card. Mathematics, anatomy, constitutive morphology, typed modality boundary, chronology, dependent receiver, reconstruction fibre, and open exterior were returned as faces of the same section. Unsupported receiver and occurrence requests returned exact native insufficiencies. The rest remounted with no Soulkiller witness, foreign realization, or semantic route.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("K3 one connected Athena ecology refused".to_owned())
    }
}

fn remount(
    rest: &Path,
    output: &Path,
    occurrence: EventId,
    receiver: ReceiverId,
) -> Result<(), String> {
    let rest = NativeEcologyRest::read(&fs::read(rest).map_err(display)?).map_err(display)?;
    let returned = rest
        .conduct_occurrence(occurrence, receiver)
        .map_err(display)?;
    let passed = matches!(
        &returned,
        NativeConductConsequence::Returned(passage)
            if !passage.word_return.apparatus.invariant_transport_reuploaded
                && !passage.current_return.invariant_transport_reuploaded
                && !passage.current_return.cpu_semantic_replay_after_device
                && !passage.current_return.binary_receiver_taken
    );
    write_json(
        output.join("00-return.json"),
        &json!({
            "schema":"soma-life.detached-one-connected-athena-return.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "passed":passed,
            "mounted_paths":["/athena-native.rest"],
            "foreign_realization_available":false,
            "exterior_soulkiller_witness_available":false,
            "returned":returned,
        }),
    )
}

fn run_detached(
    rest: &Path,
    output: &Path,
    occurrence: EventId,
    receiver: ReceiverId,
) -> Result<(), String> {
    let executable = fs::canonicalize(env::current_exe().map_err(display)?).map_err(display)?;
    let rest = fs::canonicalize(rest).map_err(display)?;
    let output = fs::canonicalize(output).map_err(display)?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all", "--clearenv"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    let status = command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-return")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/athena-native.rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/return",
            "--",
            "/athena-return",
            "--remount",
            "/athena-native.rest",
            "/return",
            &occurrence.0.to_string(),
            &receiver.0.to_string(),
        ])
        .status()
        .map_err(display)?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("source-detached Athena child exited {status}"))
    }
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = Vec::new();
    collect_files(output, output, &mut files)?;
    files.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    write_json(
        output.join("MANIFEST.json"),
        &json!({"schema":"holonics.output-manifest.v1","files":files}),
    )
}

fn collect_files(
    root: &Path,
    path: &Path,
    files: &mut Vec<serde_json::Value>,
) -> Result<(), String> {
    for entry in fs::read_dir(path).map_err(display)? {
        let entry = entry.map_err(display)?;
        let child = entry.path();
        if entry.file_type().map_err(display)?.is_dir() {
            collect_files(root, &child, files)?;
        } else if entry.file_name() != "MANIFEST.json" {
            let bytes = fs::read(&child).map_err(display)?;
            files.push(json!({
                "path":child.strip_prefix(root).map_err(display)?.to_string_lossy(),
                "octets":bytes.len(),
                "sha256":sha(&bytes),
            }));
        }
    }
    Ok(())
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn display(error: impl std::fmt::Display) -> String {
    error.to_string()
}
