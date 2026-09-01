//! N0 — return the native mathematical consequence before any optional codec projection.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use holonic_engine::cuda_refine::CudaRefineExecutor;
use life::mathematical_particle::{
    NativeCodec, NativeHexisRest, NativeMathematicalInquiry, NativeSuccessorHistory,
};
use serde::Serialize;
use serde_json::{json, Value};

const REST: &str = "output/recurring_laboratory_transport_condenses_into_native_hexis/native-rest";

fn main() -> Result<(), String> {
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    match arguments.as_slice() {
        [flag, output] if flag == "--construct" => construct(Path::new(output)),
        [flag, standing, decoder, fibres, inquiry, output] if flag == "--infer" => infer(
            Path::new(standing),
            Path::new(decoder),
            Path::new(fibres),
            Path::new(inquiry),
            Path::new(output),
        ),
        _ => Err(
            "usage: N0 --construct OUTPUT | --infer STANDING DECODER FIBRES INQUIRY OUTPUT"
                .to_owned(),
        ),
    }
}

fn construct(output: &Path) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "N0 output already exists; preserve or explicitly remove {} before a new occurrence",
            output.display()
        ));
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let rest_directory = root.join(REST);
    let rest = read_rest(&rest_directory)?;
    let history = rest
        .reconstruction()
        .predecessor_component_addresses
        .iter()
        .rev()
        .take(4)
        .cloned()
        .collect::<Vec<_>>();
    let fixed = rest
        .found_native_mathematical_inquiry(
            vec![
                "n0/material/fixed/integer-section".to_owned(),
                "n0/material/fixed/modulus-two-section".to_owned(),
            ],
            vec![vec![11, -11, 0], vec![1, 1, 0]],
            vec![
                NativeSuccessorHistory::FixedSection,
                NativeSuccessorHistory::ComposedJoint,
            ],
            history.clone(),
            vec![
                "nonlinear fixed varieties remain outside this occurrence".to_owned(),
                "successor words beyond the rested aperture remain open".to_owned(),
            ],
        )
        .map_err(|error| error.to_string())?;
    let separator = rest
        .found_native_mathematical_inquiry(
            vec![
                "n0/material/separator/integer-section".to_owned(),
                "n0/material/separator/modulus-two-section".to_owned(),
            ],
            vec![vec![1, 1, 0], vec![1, 1, 0]],
            vec![
                NativeSuccessorHistory::ExpandedGenerator,
                NativeSuccessorHistory::CarrierRebase {
                    source: 0,
                    target: 1,
                },
            ],
            history,
            vec![
                "the next receiver beyond carrier-kernel membership remains open".to_owned(),
                "overlapping family supports still require a higher-cell return".to_owned(),
            ],
        )
        .map_err(|error| error.to_string())?;
    if fixed.occurrence == separator.occurrence || fixed.sections == separator.sections {
        return Err("the two N0 inquiries collapsed before native conduct".to_owned());
    }

    let input = output.join("input");
    fs::create_dir_all(&input).map_err(|error| error.to_string())?;
    let fixed_inquiry = input.join("fixed.json");
    let separator_inquiry = input.join("separator.json");
    write_json(&fixed_inquiry, &fixed)?;
    write_json(&separator_inquiry, &separator)?;
    let fixed_output = output.join("fixed-return");
    let separator_output = output.join("separator-return");
    fs::create_dir_all(&fixed_output).map_err(|error| error.to_string())?;
    fs::create_dir_all(&separator_output).map_err(|error| error.to_string())?;
    let executable = env::current_exe().map_err(|error| error.to_string())?;
    for (inquiry, returned) in [
        (&fixed_inquiry, &fixed_output),
        (&separator_inquiry, &separator_output),
    ] {
        run_source_absent(
            &executable,
            &rest_directory.join("standing.bin"),
            &rest_directory.join("decoder.bin"),
            &rest_directory.join("fibres.bin"),
            inquiry,
            returned,
        )?;
    }

    let fixed_return = read_json(&fixed_output.join("00-native-consequence.json"))?;
    let separator_return = read_json(&separator_output.join("00-native-consequence.json"))?;
    let fixed_notation = read_json(&fixed_output.join("01-exact-notation.json"))?;
    let fixed_json = read_json(&fixed_output.join("02-json-projection.json"))?;
    let separator_notation = read_json(&separator_output.join("01-exact-notation.json"))?;
    let separator_json = read_json(&separator_output.join("02-json-projection.json"))?;
    let fixed_audit = read_json(&fixed_output.join("03-namespace-audit.json"))?;
    let separator_audit = read_json(&separator_output.join("03-namespace-audit.json"))?;

    let fixed_identity = fixed_return["occurrence"]
        .as_str()
        .ok_or("fixed consequence identity is absent")?;
    let separator_identity = separator_return["occurrence"]
        .as_str()
        .ok_or("separator consequence identity is absent")?;
    let identities_distinct = fixed_identity != separator_identity;
    let complexes_distinct = fixed_return["complex"] != separator_return["complex"];
    let native_receivers_only =
        [fixed_return.clone(), separator_return.clone()]
            .iter()
            .all(|returned| {
                let receiver_bytes = returned["receiver_family"].to_string();
                !receiver_bytes.contains("language")
                    && !receiver_bytes.contains("proof")
                    && !receiver_bytes.contains("checker")
                    && !receiver_bytes.contains("json")
            });
    let complete_native_returns =
        [fixed_return.clone(), separator_return.clone()]
            .iter()
            .all(|returned| {
                returned["complex"]["operation_cells"]
                    .as_array()
                    .is_some_and(|cells| cells.len() == 2)
                    && returned["complex"]["constraint_cells"]
                        .as_array()
                        .is_some_and(|cells| cells.len() == 2)
                    && returned["complex"]["geometry_cells"]
                        .as_array()
                        .is_some_and(|cells| cells.len() == 2)
                    && returned["derivational_transport"]
                        .as_array()
                        .is_some_and(|words| words.len() == 2)
                    && returned["reconstruction"]["complete_inherited_fibres"]
                        .as_array()
                        .is_some_and(|fibres| !fibres.is_empty())
                    && returned["reconstruction"]["shortest_available_separators"]
                        .as_array()
                        .is_some_and(|separators| !separators.is_empty())
                    && returned["lineage"]["addressed_spans"]
                        .as_array()
                        .is_some_and(|spans| spans.len() == 2)
                    && returned["exterior"]["rested_open_exterior"]
                        .as_array()
                        .is_some_and(|exterior| !exterior.is_empty())
                    && returned["apparatus"]["host_semantic_callbacks"] == 0
            });
    let separator_returns_obstruction = separator_return["exterior"]["returned_obstructions"]
        .as_array()
        .is_some_and(|obstructions| !obstructions.is_empty());
    let codecs_preserve_identity = [
        (&fixed_notation, fixed_identity),
        (&fixed_json, fixed_identity),
        (&separator_notation, separator_identity),
        (&separator_json, separator_identity),
    ]
    .iter()
    .all(|(projection, identity)| {
        projection["native_consequence_occurrence"].as_str() == Some(identity)
    });
    let fresh_process_absence = [&fixed_audit, &separator_audit].iter().all(|audit| {
        audit["lean_executable_absent"] == true
            && audit["lean_source_absent"] == true
            && audit["historical_proof_plates_absent"] == true
            && audit["repository_source_absent"] == true
            && audit["forbidden_source_descriptors"] == json!([])
    });
    let passed = identities_distinct
        && complexes_distinct
        && native_receivers_only
        && complete_native_returns
        && separator_returns_obstruction
        && codecs_preserve_identity
        && fresh_process_absence;
    let grade = json!({
        "schema": "holonics.n0.grade.v1",
        "truth_status": "implemented-exact-with-measured-apparatus-testimony",
        "passed": passed,
        "two_nonidentical_rich_inquiries": identities_distinct && complexes_distinct,
        "native_receivers_only": native_receivers_only,
        "complete_C_D_F_L_X": complete_native_returns,
        "shortest_separator_and_obstruction_returned": separator_returns_obstruction,
        "two_downstream_codecs_preserve_native_identity": codecs_preserve_identity,
        "fresh_process_without_lean_sources_or_proof_plates": fresh_process_absence,
        "resident_gpu": {
            "fixed": fixed_return["apparatus"],
            "separator": separator_return["apparatus"],
        },
        "historical_regression_consumers_only": ["M6", "R6", "L0", "L1", "L2", "L3", "L4"],
        "optional_checker_invoked": false,
        "open_exterior": ["raw optical recovery is N1", "nonlinear fixed varieties", "unadmitted successor histories"],
    });
    write_json(output.join("00-N0-grade.json"), &grade)?;
    if !passed {
        return Err(format!("the N0 grade refused: {grade}"));
    }
    println!("N0 native consequences returned: {fixed_identity} {separator_identity}");
    Ok(())
}

fn infer(
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
    inquiry: &Path,
    output: &Path,
) -> Result<(), String> {
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let rest = NativeHexisRest::read(&read(standing)?, &read(decoder)?, &read(fibres)?)
        .map_err(|error| error.to_string())?;
    let inquiry: NativeMathematicalInquiry = serde_json::from_slice(&read(inquiry)?)
        .map_err(|error| format!("read native inquiry: {error}"))?;
    rest.admit_native_mathematical_inquiry(&inquiry)
        .map_err(|error| error.to_string())?;

    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let consequence = rest
        .conduct_native_mathematical_inquiry_on_card(&inquiry, &mut card)
        .map_err(|error| error.to_string())?;
    let native_identity = consequence.occurrence.clone();
    write_json(output.join("00-native-consequence.json"), &consequence)?;

    let notation = consequence
        .project(NativeCodec::ExactNotation)
        .map_err(|error| error.to_string())?;
    let json_projection = consequence
        .project(NativeCodec::Json)
        .map_err(|error| error.to_string())?;
    if notation.native_consequence_occurrence != native_identity
        || json_projection.native_consequence_occurrence != native_identity
    {
        return Err("a downstream codec moved the frozen native identity".to_owned());
    }
    write_json(output.join("01-exact-notation.json"), &notation)?;
    write_json(output.join("02-json-projection.json"), &json_projection)?;

    let descriptor_targets = descriptors();
    let forbidden_source_descriptors = descriptor_targets
        .iter()
        .filter(|target| {
            target.contains("/Workspaces/holonics")
                || target.contains("/soma/formal")
                || target.contains("/research/")
                || target.contains("/.git/")
        })
        .cloned()
        .collect::<Vec<_>>();
    let path_contains_lean = env::var_os("PATH")
        .into_iter()
        .flat_map(|path| env::split_paths(&path).collect::<Vec<_>>())
        .any(|directory| directory.join("lean").exists());
    let audit = json!({
        "schema": "holonics.n0.fresh-process-namespace.v1",
        "truth_status": "measured",
        "native_consequence_occurrence": native_identity,
        "lean_executable_absent": !path_contains_lean && !Path::new("/usr/bin/lean").exists() && !Path::new("/bin/lean").exists(),
        "lean_source_absent": !Path::new("/soma/formal").exists() && !Path::new("/source/formal").exists(),
        "historical_proof_plates_absent": !Path::new("/proof-plates").exists(),
        "repository_source_absent": !Path::new("/home/b/Workspaces/holonics").exists() && !Path::new("/workspace").exists(),
        "descriptor_targets": descriptor_targets,
        "forbidden_source_descriptors": forbidden_source_descriptors,
        "optional_checker_invoked": false,
    });
    write_json(output.join("03-namespace-audit.json"), &audit)?;
    if audit["lean_executable_absent"] != true
        || audit["lean_source_absent"] != true
        || audit["historical_proof_plates_absent"] != true
        || audit["repository_source_absent"] != true
        || audit["forbidden_source_descriptors"] != json!([])
    {
        return Err(format!(
            "the fresh-process namespace was not source absent: {audit}"
        ));
    }
    Ok(())
}

fn read_rest(directory: &Path) -> Result<NativeHexisRest, String> {
    NativeHexisRest::read(
        &read(directory.join("standing.bin"))?,
        &read(directory.join("decoder.bin"))?,
        &read(directory.join("fibres.bin"))?,
    )
    .map_err(|error| error.to_string())
}

fn run_source_absent(
    executable: &Path,
    standing: &Path,
    decoder: &Path,
    fibres: &Path,
    inquiry: &Path,
    output: &Path,
) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let standing = standing.canonicalize().map_err(|error| error.to_string())?;
    let decoder = decoder.canonicalize().map_err(|error| error.to_string())?;
    let fibres = fibres.canonicalize().map_err(|error| error.to_string())?;
    let inquiry = inquiry.canonicalize().map_err(|error| error.to_string())?;
    let output = output.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all", "--clearenv"])
        .args(["--setenv", "PATH", "/usr/bin:/bin"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--tmpfs", "/usr/bin"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--ro-bind", "/sys", "/sys"])
        .args(["--dev-bind", "/dev", "/dev"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"])
        .args(["--dir", "/rest"])
        .args(["--dir", "/input"])
        .args(["--dir", "/return"]);
    for library in ["/lib", "/lib64", "/run"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena")
        .arg("--ro-bind")
        .arg(standing)
        .arg("/rest/standing.bin")
        .arg("--ro-bind")
        .arg(decoder)
        .arg("/rest/decoder.bin")
        .arg("--ro-bind")
        .arg(fibres)
        .arg("/rest/fibres.bin")
        .arg("--ro-bind")
        .arg(inquiry)
        .arg("/input/inquiry.json")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena",
            "--infer",
            "/rest/standing.bin",
            "/rest/decoder.bin",
            "/rest/fibres.bin",
            "/input/inquiry.json",
            "/return",
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let returned = command.output().map_err(|error| error.to_string())?;
    if !returned.status.success() {
        return Err(format!(
            "fresh-process N0 inference refused: {}",
            String::from_utf8_lossy(&returned.stderr)
        ));
    }
    Ok(())
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    let path = path.as_ref();
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    fs::write(path, bytes).map_err(|error| format!("write {}: {error}", path.display()))
}

fn read(path: impl AsRef<Path>) -> Result<Vec<u8>, String> {
    let path = path.as_ref();
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}

fn read_json(path: &Path) -> Result<Value, String> {
    serde_json::from_slice(&read(path)?)
        .map_err(|error| format!("read {}: {error}", path.display()))
}

fn descriptors() -> Vec<String> {
    let Ok(entries) = fs::read_dir("/proc/self/fd") else {
        return Vec::new();
    };
    let mut targets = entries
        .flatten()
        .filter_map(|entry| fs::read_link(entry.path()).ok())
        .map(|path| path.to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    targets.sort();
    targets.dedup();
    targets
}
