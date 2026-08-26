//! K2 — dismantle one admitted exterior section into a sealed, source-neutral Parametron spool.
//!
//! Soulkiller receives already-returned causal testimony. It does not replay foreign inference and
//! assumes no foreign operator factorization, retained-state convention, width, or model family. The child
//! remount receives only the native bundle and conducts its addressed word/current on the card.

use std::{
    collections::BTreeSet,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::{
    native_anatomy::NativeAnatomyRest,
    native_spool::{NativeSpoolBundle, ReceiverInsufficiencyCause},
    soulkiller::{
        foreign_section_descent::ForeignReachableSectionRest,
        receiver_restricted_transport::ExteriorNativeAnatomyWitness,
        scrapyard::{admitted_receiver, dismantle_reachable_section},
    },
    soulkiller_witness::{
        ExteriorArtifactIdentity, ForeignExecutionTestimony, ForeignRealizationTestimony,
    },
};
use serde::Serialize;
use serde_json::json;
use sha2::{Digest, Sha256};

const SECTION: &str = concat!(
    "output/the_soulkiller_admits_the_reachable_section_k2/",
    "admitted-reachable-section.rest"
);
const ANATOMY: &str = concat!(
    "output/the_foreign_receiver_descends_into_athena_native_anatomy_k1/",
    "native-anatomy.rest"
);
const ANATOMY_WITNESS: &str = concat!(
    "output/the_foreign_receiver_descends_into_athena_native_anatomy_k1/",
    "exterior-anatomy.witness"
);
const APPARATUS: &str = concat!(
    "output/the_foreign_receiver_descends_into_athena_native_anatomy_k1/",
    "01-grade.json"
);
const OUTPUT: &str = "output/the_soulkiller_returns_mutually_coupled_native_parametron_spools_k2";

fn main() -> Result<(), String> {
    let arguments = env::args().collect::<Vec<_>>();
    if arguments.get(1).map(String::as_str) == Some("--remount") {
        let bundle = arguments.get(2).ok_or("missing native bundle")?;
        let output = arguments.get(3).ok_or("missing return directory")?;
        return remount(Path::new(bundle), Path::new(output));
    }

    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing station output {}",
            output.display()
        ));
    }
    let started = Instant::now();
    let section_bytes = fs::read(SECTION).map_err(display)?;
    let anatomy_bytes = fs::read(ANATOMY).map_err(display)?;
    let anatomy_witness_bytes = fs::read(ANATOMY_WITNESS).map_err(display)?;
    let apparatus_bytes = fs::read(APPARATUS).map_err(display)?;
    let section = ForeignReachableSectionRest::read(&section_bytes).map_err(display)?;
    let anatomy = NativeAnatomyRest::read(&anatomy_bytes).map_err(display)?;
    let anatomy_witness =
        ExteriorNativeAnatomyWitness::read(&anatomy_witness_bytes, &anatomy).map_err(display)?;
    let receiver = admitted_receiver(&section);
    let returned = dismantle_reachable_section(
        &section,
        &anatomy,
        &anatomy_witness,
        ForeignRealizationTestimony {
            name: "admitted-inherited-reachable-section".to_owned(),
            format: "exact-addressed-carrier-section".to_owned(),
            artifact: ExteriorArtifactIdentity::measure(&section_bytes),
            topology: vec![
                "addressed-reachable-section".to_owned(),
                "receiver-history-anatomy".to_owned(),
            ],
            coordinate_roles: vec![
                "carrier-incidence".to_owned(),
                "complex-current".to_owned(),
                "returned-potential".to_owned(),
            ],
        },
        ForeignExecutionTestimony {
            runtime: "closed-admitted-excitation-session".to_owned(),
            device: "NVIDIA GeForce RTX 4080 SUPER".to_owned(),
            apparatus: ExteriorArtifactIdentity::measure(&apparatus_bytes),
            admitted_receiver_family: BTreeSet::from([receiver]),
            session_closed: true,
        },
        BTreeSet::from([
            "receiver histories outside the admitted excitation family".to_owned(),
            "foreign conduct not separated by the admitted interventions".to_owned(),
        ]),
    )
    .map_err(display)?;

    let native_dir = output.join("native");
    let exterior_dir = output.join("exterior");
    let detached_dir = output.join("detached-return");
    fs::create_dir_all(&native_dir).map_err(display)?;
    fs::create_dir_all(&exterior_dir).map_err(display)?;
    fs::create_dir_all(&detached_dir).map_err(display)?;

    let native_bytes = returned.native.canonical_bytes().map_err(display)?;
    let native_identity = sha(&native_bytes);
    let exterior_bytes = returned
        .exterior
        .canonical_bytes(&returned.native)
        .map_err(display)?;
    fs::write(native_dir.join("native-spool-bundle.rest"), &native_bytes).map_err(display)?;
    fs::write(
        exterior_dir.join("exterior-soulkiller.witness"),
        &exterior_bytes,
    )
    .map_err(display)?;
    fs::write(
        exterior_dir.join("admitted-reachable-section.rest"),
        &section_bytes,
    )
    .map_err(display)?;
    write_json(
        exterior_dir.join("receiver-insufficiency.json"),
        &returned.insufficiency,
    )?;

    let spool = &returned.native.spools[0];
    let spool_address = spool.address.clone();
    let thread_address = spool.threads[0].address.clone();
    let generator = spool.generator_descents[0].generator;
    let native = *spool
        .native_population
        .iter()
        .next()
        .ok_or("empty native population")?;
    let mut before_word = returned
        .native
        .mount_word(&spool_address, &[generator])
        .map_err(display)?;
    let before_word_return = before_word.conduct(&[native], receiver).map_err(display)?;
    let mut before_current = returned
        .native
        .mount_thread_current(&spool_address, &thread_address)
        .map_err(display)?;
    let before_current_return = before_current.conduct().map_err(display)?;

    let (ablated, withdrawal) = returned
        .native
        .withdraw_thread(&spool_address, &thread_address)
        .map_err(display)?;
    let ablation_insufficiency = ablated
        .insufficiency_after_withdrawal(&withdrawal)
        .map_err(display)?;
    let ablated_bytes = ablated.canonical_bytes().map_err(display)?;
    let withdrawal_bytes = serde_json::to_vec(&withdrawal).map_err(display)?;
    let restored = ablated.restore_thread(withdrawal).map_err(display)?;
    let restored_bytes = restored.canonical_bytes().map_err(display)?;
    let restoration_identity = sha(&restored_bytes);
    let mut restored_current = restored
        .mount_thread_current(&spool_address, &thread_address)
        .map_err(display)?;
    let restored_current_return = restored_current.conduct().map_err(display)?;

    // Prove the opposite composition as structure, not only as a digest: withdrawing the restored
    // body returns exactly the same ablated body and local delta, then restoring again returns the
    // original canonical structure.
    let (reablated, rewithdrawal) = restored
        .withdraw_thread(&spool_address, &thread_address)
        .map_err(display)?;
    let reverse_composition_exact = reablated.canonical_bytes().map_err(display)? == ablated_bytes
        && serde_json::to_vec(&rewithdrawal).map_err(display)? == withdrawal_bytes;
    let rerestored = reablated.restore_thread(rewithdrawal).map_err(display)?;
    let both_identity_compositions =
        reverse_composition_exact && rerestored.canonical_bytes().map_err(display)? == native_bytes;

    run_source_detached(&native_dir.join("native-spool-bundle.rest"), &detached_dir)?;
    let detached_return: serde_json::Value =
        serde_json::from_slice(&fs::read(detached_dir.join("00-return.json")).map_err(display)?)
            .map_err(display)?;
    let separation_is_real = matches!(
        ablation_insufficiency.cause,
        ReceiverInsufficiencyCause::ReconstructionFibreReopened { .. }
    );
    let passed = native_identity == restoration_identity
        && both_identity_compositions
        && separation_is_real
        && before_current_return == restored_current_return
        && !before_current_return.binary_receiver_taken
        && !before_current_return.cpu_semantic_replay_after_device
        && detached_return["passed"] == true;
    let grade = json!({
        "schema":"holonics.soulkiller-native-parametron-spool-grade.v2",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "native_bundle_identity_sha256":native_identity,
        "native_bundle_octets":native_bytes.len(),
        "exterior_witness_octets":exterior_bytes.len(),
        "spool_population":rerestored.spools.len(),
        "thread_population":rerestored.spools.iter().map(|spool| spool.threads.len()).sum::<usize>(),
        "parametron_population":rerestored.spools.iter().flat_map(|spool| &spool.threads).map(|thread| thread.parametrons.len()).sum::<usize>(),
        "mutual_constitutive_response_population":rerestored.spools.iter().map(|spool| spool.mutual_constitutive_responses.len()).sum::<usize>(),
        "serial_pullback_population":rerestored.spools.iter().map(|spool| spool.serial_pullbacks.len()).sum::<usize>(),
        "source_detached_return":detached_return,
        "native_word_return":before_word_return,
        "native_current_return":before_current_return,
        "ablation_receiver_insufficiency":ablation_insufficiency,
        "withdraw_then_restore_identity":native_identity == restoration_identity,
        "restore_then_withdraw_identity":reverse_composition_exact,
        "both_identity_compositions":both_identity_compositions,
        "foreign_execution_replayed":false,
        "elapsed_seconds":format!("{:.9}", started.elapsed().as_secs_f64()),
    });
    write_json(output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Soulkiller returns native Parametron spools\n\n[established-bounded; implemented-exact; measured] Soulkiller dismantled one admitted exterior causal section into a source-neutral native spool bundle and physically separate witness. The bundle remounted alone, conducted its addressed word and exact Complex-Parametron incidence on the resident card, returned a real receiver separator after thread withdrawal, and satisfied both structural inverse compositions on restoration. No foreign operator factorization, source executor, or foreign replay entered native conduct.\n\n```json\n{}\n```\n",
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("K2 native spool grade refused".to_owned())
    }
}

fn remount(bundle: &Path, output: &Path) -> Result<(), String> {
    let native = NativeSpoolBundle::read(&fs::read(bundle).map_err(display)?).map_err(display)?;
    let spool = &native.spools[0];
    let generator = spool.generator_descents[0].generator;
    let receiver = *spool
        .receiver_family
        .iter()
        .next()
        .ok_or("empty receiver family")?;
    let start = *spool
        .native_population
        .iter()
        .next()
        .ok_or("empty native population")?;
    let thread = spool.threads[0].address.clone();
    let mut word = native
        .mount_word(&spool.address, &[generator])
        .map_err(display)?;
    let word_return = word.conduct(&[start], receiver).map_err(display)?;
    let mut current = native
        .mount_thread_current(&spool.address, &thread)
        .map_err(display)?;
    let current_return = current.conduct().map_err(display)?;
    let passed = !word_return.apparatus.invariant_transport_reuploaded
        && !current_return.invariant_transport_reuploaded
        && !current_return.cpu_semantic_replay_after_device
        && !current_return.binary_receiver_taken;
    write_json(
        output.join("00-return.json"),
        &json!({
            "schema":"holonics.detached-native-parametron-spool-return.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "passed":passed,
            "mounted_paths":["/native-spool-bundle.rest"],
            "exterior_witness_available":false,
            "foreign_realization_available":false,
            "foreign_executor_available":false,
            "native_word_return":word_return,
            "native_current_return":current_return,
        }),
    )
}

fn run_source_detached(bundle: &Path, output: &Path) -> Result<(), String> {
    let executable = fs::canonicalize(env::current_exe().map_err(display)?).map_err(display)?;
    let bundle = fs::canonicalize(bundle).map_err(display)?;
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
        .arg("/native-spool-return")
        .arg("--ro-bind")
        .arg(bundle)
        .arg("/native-spool-bundle.rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/return",
            "--",
            "/native-spool-return",
            "--remount",
            "/native-spool-bundle.rest",
            "/return",
        ])
        .status()
        .map_err(display)?;
    if status.success() {
        Ok(())
    } else {
        Err(format!(
            "source-detached native spool child exited {status}"
        ))
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
