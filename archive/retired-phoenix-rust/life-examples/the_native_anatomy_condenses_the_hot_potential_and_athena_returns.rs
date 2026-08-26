//! Compile the terminal-order receiver through the resident native anatomy, retain the complete
//! foreign potential as a cold reconstruction fibre, and conduct the twelve addressed occurrences
//! in a source-isolated process which cannot access that cold fibre.

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use holonic_engine::{
    native_anatomical_potential::NativeAnatomicalPotentialRest,
    native_anatomy::NativeAnatomyRest,
    phoenix::{
        foreign_potential_rest::{
            condense_native_anatomical_potential, ForeignPotentialComplexRest,
        },
        receiver_restricted_transport::ExteriorNativeAnatomyWitness,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const FOREIGN: &str = concat!(
    "output/the_second_successor_receiver_and_support_faces_glue_",
    "the_twelve_node_parametron/expanded-potential.rest"
);
const ANATOMY: &str = concat!(
    "output/the_foreign_receiver_descends_into_athena_native_anatomy_k1/",
    "native-anatomy.rest"
);
const EXTERIOR_ANATOMY: &str = concat!(
    "output/the_foreign_receiver_descends_into_athena_native_anatomy_k1/",
    "exterior-anatomy.witness"
);
const OUTPUT: &str = "output/the_native_anatomy_condenses_the_hot_potential_and_athena_returns_k1";

#[derive(Debug, Serialize, Deserialize)]
struct ProductManifest {
    schema: String,
    identity_sha256: String,
    files: BTreeMap<String, FileReceipt>,
}

#[derive(Debug, Serialize, Deserialize)]
struct FileReceipt {
    octets: u64,
    sha256: String,
}

fn main() -> Result<(), String> {
    let args = env::args_os()
        .skip(1)
        .map(PathBuf::from)
        .collect::<Vec<_>>();
    match args.as_slice() {
        [] => construct(Path::new(OUTPUT)),
        [flag, potential, anatomy, output] if flag == "--remount" => {
            remount(potential, anatomy, output)
        }
        _ => Err("usage: [--remount NATIVE_POTENTIAL NATIVE_ANATOMY OUTPUT]".to_owned()),
    }
}

fn construct(output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "preserve existing station output {}",
            output.display()
        ));
    }
    let started = Instant::now();
    let foreign_bytes = fs::read(FOREIGN).map_err(display)?;
    let foreign = ForeignPotentialComplexRest::read(&foreign_bytes).map_err(display)?;
    let anatomy_bytes = fs::read(ANATOMY).map_err(display)?;
    let anatomy = NativeAnatomyRest::read(&anatomy_bytes).map_err(display)?;
    let exterior_anatomy_bytes = fs::read(EXTERIOR_ANATOMY).map_err(display)?;
    let exterior_anatomy =
        ExteriorNativeAnatomyWitness::read(&exterior_anatomy_bytes, &anatomy).map_err(display)?;
    let native = condense_native_anatomical_potential(&foreign, &anatomy, &exterior_anatomy)
        .map_err(display)?;
    let native_bytes = native.canonical_bytes().map_err(display)?;

    let product = output.join("product");
    fs::create_dir_all(&product).map_err(display)?;
    fs::write(product.join("native-potential.rest"), &native_bytes).map_err(display)?;
    fs::write(product.join("native-anatomy.rest"), &anatomy_bytes).map_err(display)?;
    let exterior = output.join("exterior-reconstruction");
    fs::create_dir_all(&exterior).map_err(display)?;
    fs::write(exterior.join("foreign-potential.rest"), &foreign_bytes).map_err(display)?;
    fs::write(
        exterior.join("exterior-anatomy.witness"),
        &exterior_anatomy_bytes,
    )
    .map_err(display)?;
    let manifest = seal_manifest(&product)?;
    write_json(product.join("manifest.json"), &manifest)?;
    let detached = output.join("detached");
    fs::create_dir_all(&detached).map_err(display)?;
    run_source_detached(
        &product.join("native-potential.rest"),
        &product.join("native-anatomy.rest"),
        &detached,
    )?;
    let returned: Value = read_json(&detached.join("00-return.json"))?;
    let hot_foreign_entries = foreign
        .receiver_rows
        .len()
        .checked_mul(foreign.history_addresses.len())
        .ok_or("foreign hot extent overflow")?;
    let hot_native_entries = native
        .receiver_rows
        .len()
        .checked_mul(native.native_population.len())
        .ok_or("native hot extent overflow")?;
    let passed = returned["passed"] == true
        && hot_native_entries < hot_foreign_entries
        && returned["cold_foreign_reconstruction_accessed"] == false
        && returned["foreign_tower_staged_octets"] == 0
        && returned["foreign_tower_deed_launches"] == 0;
    let grade = json!({
        "schema":"holonics.native-anatomical-hot-potential-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "product_identity_sha256":manifest.identity_sha256,
        "product_rest_octets":manifest.files.values().map(|file| file.octets).sum::<u64>(),
        "cold_foreign_reconstruction_octets":foreign_bytes.len(),
        "cold_foreign_reconstruction_sha256":foreign.identity_sha256,
        "exterior_anatomy_witness_octets":exterior_anatomy_bytes.len(),
        "exterior_anatomy_witness_sha256":sha(&exterior_anatomy_bytes),
        "native_anatomy_rest_octets":anatomy_bytes.len(),
        "native_hot_potential_rest_octets":native_bytes.len(),
        "foreign_hot_receiver_entries":hot_foreign_entries,
        "native_hot_receiver_entries":hot_native_entries,
        "hot_receiver_entry_reduction":hot_foreign_entries.saturating_sub(hot_native_entries),
        "foreign_occurrence_population":foreign.history_addresses.len(),
        "native_anatomy_population":native.native_population.len(),
        "source_detached_return":returned,
    });
    fs::create_dir_all(output).map_err(display)?;
    write_json(output.join("00-grade.json"), &grade)?;
    write_json(
        output.join("01-expensive-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"cargo run --release -p life --example the_native_anatomy_condenses_the_hot_potential_and_athena_returns",
            "purpose":"compile the hot terminal potential through native anatomy and conduct all addressed occurrences in a process with no cold-foreign access",
            "elapsed_seconds":format!("{:.9}",started.elapsed().as_secs_f64()),
            "exit_status":if passed {0} else {1},
            "foreign_capture_replayed":false,
        }),
    )?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# Native anatomy condenses the hot potential and Athena returns\n\n[established-bounded; implemented-exact; measured] The terminal receiver compiled from {} foreign occurrence columns to {} native anatomical columns. The complete foreign potential remains in the product as a cold reconstruction fibre, but the source-isolated inference process could mount only the native potential and native anatomy. It returned all twelve addressed surfaces on the resident card without foreign staging or deeds.\n\n```json\n{}\n```\n",
            foreign.history_addresses.len(),
            native.native_population.len(),
            serde_json::to_string_pretty(&grade).map_err(display)?
        ),
    )
    .map_err(display)?;
    write_station_manifest(output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the native anatomical potential grade refused".to_owned())
    }
}

fn remount(potential: &Path, anatomy: &Path, output: &Path) -> Result<(), String> {
    fs::create_dir_all(output).map_err(display)?;
    let native = NativeAnatomicalPotentialRest::read(&fs::read(potential).map_err(display)?)
        .map_err(display)?;
    let anatomy = NativeAnatomyRest::read(&fs::read(anatomy).map_err(display)?).map_err(display)?;
    if native.native_population != anatomy.native_population
        || anatomy.classes.iter().any(|class| {
            native
                .class_certificates
                .iter()
                .find(|certificate| certificate.native == class.native)
                .map(|certificate| certificate.selected_native_address)
                != Some(class.emitted_native_address)
        })
    {
        return Err("native potential and anatomy quotient disagree".to_owned());
    }
    let occurrence_natives = native
        .class_certificates
        .iter()
        .flat_map(|certificate| {
            std::iter::repeat_n(certificate.native, certificate.history_addresses.len())
        })
        .collect::<Vec<_>>();
    let fronts = occurrence_natives
        .iter()
        .map(|state| native.one_hot_for_native(*state).map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    let expected = occurrence_natives
        .iter()
        .map(|state| {
            native
                .class_certificates
                .iter()
                .find(|certificate| certificate.native == *state)
                .map(|certificate| certificate.selected_native_address)
                .ok_or("native class has no terminal receiver certificate")
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut resident = native.mount_receiver().map_err(display)?;
    let returned = resident.conduct(&fronts).map_err(display)?;
    let surfaces = returned
        .selected_native_addresses
        .iter()
        .map(|address| native.decode(*address).map(str::to_owned).map_err(display))
        .collect::<Result<Vec<_>, _>>()?;
    let passed = returned.selected_native_addresses == expected
        && returned
            .plural_population
            .iter()
            .all(|population| *population == 1)
        && !returned.invariant_transport_reuploaded
        && !returned.cpu_semantic_replay_after_device;
    write_json(
        output.join("00-return.json"),
        &json!({
            "schema":"holonics.native-anatomical-potential-detached-return.v1",
            "truth_status":"established-bounded; implemented-exact; measured",
            "passed":passed,
            "native_surfaces":surfaces,
            "receiver":returned,
            "mounted_native_paths":["/native-potential.rest","/native-anatomy.rest"],
            "cold_foreign_reconstruction_accessed":false,
            "foreign_tower_staged_octets":0,
            "foreign_tower_deed_launches":0,
            "lean_or_checker_in_inference_lifecycle":false,
        }),
    )?;
    if passed {
        Ok(())
    } else {
        Err("source-detached native potential return refused".to_owned())
    }
}

fn run_source_detached(potential: &Path, anatomy: &Path, output: &Path) -> Result<(), String> {
    let executable = fs::canonicalize(env::current_exe().map_err(display)?).map_err(display)?;
    let potential = fs::canonicalize(potential).map_err(display)?;
    let anatomy = fs::canonicalize(anatomy).map_err(display)?;
    let output = fs::canonicalize(output).map_err(display)?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
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
        .arg("/athena-native")
        .arg("--ro-bind")
        .arg(potential)
        .arg("/native-potential.rest")
        .arg("--ro-bind")
        .arg(anatomy)
        .arg("/native-anatomy.rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/return",
            "--",
            "/athena-native",
            "--remount",
            "/native-potential.rest",
            "/native-anatomy.rest",
            "/return",
        ])
        .status()
        .map_err(display)?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("source-detached child exited {status}"))
    }
}

fn seal_manifest(product: &Path) -> Result<ProductManifest, String> {
    let mut files = BTreeMap::new();
    collect_files(product, product, &mut files)?;
    let identity_sha256 = sha(&serde_json::to_vec(&files).map_err(display)?);
    Ok(ProductManifest {
        schema: "holonics.native-anatomical-potential-product.v1".to_owned(),
        identity_sha256,
        files,
    })
}

fn collect_files(
    root: &Path,
    path: &Path,
    files: &mut BTreeMap<String, FileReceipt>,
) -> Result<(), String> {
    for entry in fs::read_dir(path).map_err(display)? {
        let entry = entry.map_err(display)?;
        let child = entry.path();
        if entry.file_type().map_err(display)?.is_dir() {
            collect_files(root, &child, files)?;
        } else if entry.file_name() != "manifest.json" {
            let bytes = fs::read(&child).map_err(display)?;
            files.insert(
                child
                    .strip_prefix(root)
                    .map_err(display)?
                    .to_string_lossy()
                    .into_owned(),
                FileReceipt {
                    octets: bytes.len() as u64,
                    sha256: sha(&bytes),
                },
            );
        }
    }
    Ok(())
}

fn write_station_manifest(output: &Path) -> Result<(), String> {
    let mut files = BTreeMap::new();
    collect_files(output, output, &mut files)?;
    write_json(
        output.join("MANIFEST.json"),
        &json!({"schema":"holonics.output-manifest.v1","files":files}),
    )
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(path, serde_json::to_vec_pretty(value).map_err(display)?).map_err(display)
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
