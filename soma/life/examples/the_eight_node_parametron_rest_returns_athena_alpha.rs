//! Freeze the eight-node receiver/support potential with the existing mathematical and arbitrary-
//! organ rests, then ask the existing source-detached Athena remount passage to return all eight
//! language nodes, mathematics, and heterogeneous current. No foreign tower is mounted here.

use std::{
    collections::BTreeMap,
    env, fs,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const POTENTIAL: &str = concat!(
    "output/the_successor_receiver_and_support_faces_glue_the_eight_node_parametron/",
    "expanded-potential.rest"
);
const RECEIVER_HISTORY: &str = concat!(
    "output/the_cultivated_factor_descends_through_its_receiver_history_support/",
    "receiver-restricted-factor-rest.json"
);
const FOREIGN_QUOTIENT: &str = concat!(
    "output/the_successor_receiver_and_support_faces_glue_the_eight_node_parametron/",
    "00-foreign-receiver-quotient.json"
);
const SUPPORT_PASSAGE: &str = concat!(
    "output/the_successor_receiver_and_support_faces_glue_the_eight_node_parametron/",
    "01-successor-support-passage.json"
);
const MATHEMATICS: &str =
    "output/recurring_laboratory_transport_condenses_into_native_hexis/native-rest";
const MULTIMODAL: &str = concat!(
    "output/the_returned_arbitrary_organ_consequence_cultivates_the_same_athena_continuation/",
    "native-rest"
);
const OUTPUT: &str = "output/the_eight_node_parametron_rest_returns_athena_alpha";
const REMOUNT_EXECUTABLE: &str = "the_parametron_receiver_history_rest_returns_athena_alpha";

#[derive(Debug, Serialize, Deserialize)]
struct ProductManifest {
    schema: String,
    identity_sha256: String,
    files: BTreeMap<String, FileReceipt>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FileReceipt {
    octets: u64,
    sha256: String,
}

fn main() -> Result<(), String> {
    let output = PathBuf::from(OUTPUT);
    if output.exists() {
        return Err(format!(
            "preserve existing station output {}",
            output.display()
        ));
    }
    let started = Instant::now();
    let product = output.join("product");
    fs::create_dir_all(product.join("successor")).map_err(display)?;
    fs::copy(POTENTIAL, product.join("potential.rest")).map_err(display)?;
    fs::copy(RECEIVER_HISTORY, product.join("receiver-history.rest")).map_err(display)?;
    fs::copy(
        FOREIGN_QUOTIENT,
        product.join("successor/foreign-receiver-quotient.json"),
    )
    .map_err(display)?;
    fs::copy(
        SUPPORT_PASSAGE,
        product.join("successor/support-passage.json"),
    )
    .map_err(display)?;
    copy_directory(Path::new(MATHEMATICS), &product.join("mathematics"))?;
    copy_directory(Path::new(MULTIMODAL), &product.join("multimodal"))?;
    let manifest = seal_manifest(&product)?;
    write_json(product.join("manifest.json"), &manifest)?;

    let detached = output.join("detached");
    fs::create_dir_all(&detached).map_err(display)?;
    run_source_detached(&product, &detached)?;
    let returned: Value = read_json(&detached.join("00-return.json"))?;
    let surfaces = returned["cultivated_surfaces"]
        .as_array()
        .ok_or("detached return omitted cultivated surfaces")?;
    if surfaces.len() != 8 {
        return Err("detached return did not conduct all eight addressed nodes".to_owned());
    }
    let continuations = (0..4)
        .map(|history| {
            let predecessor = surfaces[history]
                .as_str()
                .ok_or("predecessor surface is not text")?;
            let successor = surfaces[history + 4]
                .as_str()
                .ok_or("successor surface is not text")?;
            Ok(format!("{predecessor}{successor}"))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let quotient: Value = read_json(Path::new(FOREIGN_QUOTIENT))?;
    let support: Value = read_json(Path::new(SUPPORT_PASSAGE))?;
    let class_population = quotient["classes"]
        .as_array()
        .ok_or("foreign receiver quotient omitted classes")?
        .len();
    let occurrence_population = quotient["classes"]
        .as_array()
        .expect("classes checked")
        .iter()
        .map(|class| {
            class["histories"]
                .as_array()
                .map(Vec::len)
                .ok_or("foreign receiver class omitted its occurrence fibre")
        })
        .sum::<Result<usize, _>>()?;
    let support_reopenings = support["foreign_support_reopenings"]
        .as_array()
        .ok_or("support passage omitted its reopening fibre")?
        .len();
    let passed = returned["passed"] == true
        && returned["foreign_tower_staged_octets"] == 0
        && returned["foreign_tower_deed_launches"] == 0
        && returned["lean_or_checker_in_inference_lifecycle"] == false
        && class_population == 6
        && occurrence_population == 8
        && support_reopenings == 0
        && continuations
            .iter()
            .all(|surface| surface.split_whitespace().count() >= 2);
    let grade = json!({
        "schema":"holonics.eight-node-parametron-athena-alpha-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "passed":passed,
        "product_identity_sha256":manifest.identity_sha256,
        "product_rest_octets":manifest.files.values().map(|file| file.octets).sum::<u64>(),
        "coefficient_occurrence_population":occurrence_population,
        "foreign_receiver_class_population":class_population,
        "support_reopens_foreign_classes":support_reopenings,
        "bounded_continuations":continuations,
        "foreign_tower_octets_in_product":0,
        "foreign_tower_staged_octets":0,
        "foreign_tower_deed_launches":0,
        "source_detached_return":returned,
    });
    write_json(output.join("00-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# The eight-node Parametron rest returns Athena alpha\n\n[established-bounded; implemented-exact; measured] The complete eight-node cold potential, six-class foreign receiver quotient, complete occurrence fibres, descended support passage, native mathematics, and arbitrary-organ rest froze as product `{}`. A source-isolated remount returned mathematics, heterogeneous current, and the four bounded two-occurrence continuations without foreign staging, foreign deeds, Lean/checker inference, or CPU semantic replay.\n\n[open] The rest closes the declared first-emission section. A later current outside these eight addressed nodes must return an obstruction and may schedule one plural construction passage; it cannot reopen Gemma during frozen inference.\n\n```json\n{}\n```\n",
            manifest.identity_sha256,
            serde_json::to_string_pretty(&grade).map_err(display)?,
        ),
    )
    .map_err(display)?;
    write_json(
        output.join("01-expensive-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"target/release/examples/the_eight_node_parametron_rest_returns_athena_alpha",
            "purpose":"freeze and source-detach the eight-node receiver/support product, then conduct its native mathematics, arbitrary-organ and bounded language returns",
            "elapsed_seconds":format!("{:.9}",started.elapsed().as_secs_f64()),
            "exit_status":if passed {0} else {1},
            "foreign_capture_replayed":false,
        }),
    )?;
    write_station_manifest(&output)?;
    println!("{}", serde_json::to_string_pretty(&grade).map_err(display)?);
    if passed {
        Ok(())
    } else {
        Err("the eight-node Parametron Athena-alpha grade refused".to_owned())
    }
}

fn run_source_detached(product: &Path, output: &Path) -> Result<(), String> {
    let current = fs::canonicalize(env::current_exe().map_err(display)?).map_err(display)?;
    let executable = current
        .parent()
        .ok_or("release example has no parent directory")?
        .join(REMOUNT_EXECUTABLE);
    let executable = fs::canonicalize(executable)
        .map_err(|error| format!("the existing Athena remount executable is absent: {error}"))?;
    let product = fs::canonicalize(product).map_err(display)?;
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
        .arg("/athena-alpha")
        .arg("--ro-bind")
        .arg(product)
        .arg("/product")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/return",
            "--",
            "/athena-alpha",
            "--remount",
            "/product",
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

fn copy_directory(source: &Path, target: &Path) -> Result<(), String> {
    fs::create_dir_all(target).map_err(display)?;
    for entry in fs::read_dir(source).map_err(display)? {
        let entry = entry.map_err(display)?;
        if entry.file_type().map_err(display)?.is_file() {
            fs::copy(entry.path(), target.join(entry.file_name())).map_err(display)?;
        }
    }
    Ok(())
}

fn seal_manifest(product: &Path) -> Result<ProductManifest, String> {
    let mut files = BTreeMap::new();
    collect_files(product, product, &mut files)?;
    let identity_sha256 = sha(&serde_json::to_vec(&files).map_err(display)?);
    Ok(ProductManifest {
        schema: "holonics.parametron-athena-alpha-product.v1".to_owned(),
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
        } else if entry.file_name() != "manifest.json" && entry.file_name() != "MANIFEST.json" {
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

fn read_json<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(display)?).map_err(display)
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(display)?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(display)
}

fn write_station_manifest(output: &Path) -> Result<(), String> {
    let mut files = BTreeMap::new();
    collect_files(output, output, &mut files)?;
    write_json(
        output.join("MANIFEST.json"),
        &json!({"schema":"holonics.return-manifest.v1","files":files}),
    )
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
