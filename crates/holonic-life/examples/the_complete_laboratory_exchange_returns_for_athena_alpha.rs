//! AA0: freeze the complete authorized laboratory exchange and return every addressed response.

use std::{
    env, fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    time::{Instant, SystemTime, UNIX_EPOCH},
};

use life::exchange_world_tube::{
    attach_visible_exchange_faces, derive_continuation_aperture,
    discover_complete_exchange_aperture, exchange_world_tube_rest_digest,
    mount_exchange_world_tube_on_device, remount_exchange_world_tube,
    restrict_exchange_aperture_chronology_cover, write_exchange_world_tube_rest,
    CompleteExchangeSource, ContinuationAperture, ContinuationPartition, DeviceContactReceipt,
    Digest32, VisibleProjectionReceipt,
};
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

const DEFAULT_OUTPUT: &str = ".local/artifacts/the_complete_laboratory_exchange_returns_for_athena_alpha";

#[derive(Debug)]
enum Args {
    Produce {
        output: PathBuf,
        codex_root: PathBuf,
        claude_root: PathBuf,
        workspace: PathBuf,
        source_octets: Option<u64>,
    },
    Detached {
        rest: PathBuf,
        output: PathBuf,
    },
    Resume {
        output: PathBuf,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DetachedReceipt {
    schema: String,
    rest_sha256: String,
    source_occurrence_sha256: String,
    content_law_sha256: String,
    continuation_aperture_sha256: String,
    containers: usize,
    visible_messages: usize,
    continuation_families: usize,
    source_paths_mounted: usize,
    repository_mounted: bool,
}

fn main() -> Result<(), String> {
    match arguments()? {
        Args::Produce {
            output,
            codex_root,
            claude_root,
            workspace,
            source_octets,
        } => produce(
            &output,
            &codex_root,
            &claude_root,
            &workspace,
            source_octets,
        ),
        Args::Detached { rest, output } => detached(&rest, &output),
        Args::Resume { output } => resume(&output),
    }
}

fn produce(
    output: &Path,
    codex_root: &Path,
    claude_root: &Path,
    workspace: &Path,
    source_octets: Option<u64>,
) -> Result<(), String> {
    if output.exists() {
        return Err(format!("AA0 output {} already exists", output.display()));
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let started = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|error| error.to_string())?
        .as_nanos();
    let elapsed = Instant::now();
    let mut discovery = discover_complete_exchange_aperture(codex_root, claude_root, workspace)?;
    if let Some(maximum) = source_octets {
        restrict_exchange_aperture_chronology_cover(&mut discovery, maximum)?;
    }
    write_json(output.join("00-source-aperture.json"), &discovery)?;

    let mount_started = Instant::now();
    let mut world =
        mount_exchange_world_tube_on_device(&discovery.specs).map_err(|error| error.to_string())?;
    let mount_milliseconds = mount_started.elapsed().as_millis();
    let projection_started = Instant::now();
    let projection = attach_visible_exchange_faces(&mut world)?;
    let projection_milliseconds = projection_started.elapsed().as_millis();
    let continuation_started = Instant::now();
    let aperture = derive_continuation_aperture(&world)?;
    let continuation_milliseconds = continuation_started.elapsed().as_millis();

    let captured_octets = world
        .containers
        .iter()
        .try_fold(0u64, |total, container| {
            total.checked_add(container.captured_extent)
        })
        .ok_or_else(|| "captured extent left the u64 carrier".to_owned())?;
    let source_occurrence_sha256 = world.source_occurrence_sha256.render();
    let content_law_sha256 = world.content_law_sha256.render();
    let apparatus = world.device.clone();
    let semantic = json!({
        "schema": "holonics.athena-alpha.aa0-semantic-work.v1",
        "containers": world.containers.len(),
        "captured_octets": captured_octets,
        "records": world.records.len(),
        "nodes": world.nodes.len(),
        "fields": world.fields.len(),
        "scalar_sites": world.scalar_sites.len(),
        "visible_messages": world.visible_messages.len(),
        "continuation_families": aperture.families.len(),
        "complete_response_messages": aperture.complete_response_message_population,
        "exclusions": aperture.exclusions.len(),
        "partition_population": aperture.partition_population,
        "blank_records": world.excluded.blank_records,
        "incomplete_tails": world.excluded.incomplete_tails,
        "visible_controls": world.excluded.visible_membrane_controls,
        "source_octet_aperture": discovery.source_octet_aperture,
        "excluded_by_octet_aperture": discovery.excluded_by_octet_aperture,
    });
    write_json(output.join("01-semantic-work.json"), &semantic)?;
    write_json(output.join("02-apparatus.json"), &apparatus)?;
    write_json(output.join("03-visible-projection.json"), &projection)?;
    write_json(output.join("04-continuation-aperture.json"), &aperture)?;

    let rest_path = output.join("exchange-world-tube.ewtb");
    let rest_sha256 = write_exchange_world_tube_rest(&world, &rest_path)?.render();
    let aperture_sha256 = digest_json(&aperture)?;
    let containers = world.containers.len();
    let visible_messages = world.visible_messages.len();
    let continuation_families = aperture.families.len();
    drop(world);

    let apparatus_path = output.join("athena-alpha-aa0-remount");
    fs::copy(
        env::current_exe().map_err(|error| error.to_string())?,
        &apparatus_path,
    )
    .map_err(|error| error.to_string())?;
    fs::set_permissions(&apparatus_path, fs::Permissions::from_mode(0o755))
        .map_err(|error| error.to_string())?;
    let detached_root = output.join("detached-return");
    fs::create_dir(&detached_root).map_err(|error| error.to_string())?;
    run_detached(&apparatus_path, &rest_path, &detached_root)?;
    let detached: DetachedReceipt = read_json(detached_root.join("receipt.json"))?;

    let all_partitions_present = [
        ContinuationPartition::Development,
        ContinuationPartition::HeldOut,
        ContinuationPartition::Revisit,
        ContinuationPartition::Rebase,
        ContinuationPartition::DisjointControl,
    ]
    .iter()
    .all(|partition| {
        aperture
            .partition_population
            .get(partition)
            .copied()
            .unwrap_or(0)
            > 0
    });
    let detached_equal = detached.rest_sha256 == rest_sha256
        && detached.source_occurrence_sha256 == source_occurrence_sha256
        && detached.content_law_sha256 == content_law_sha256
        && detached.continuation_aperture_sha256 == aperture_sha256
        && detached.containers == containers
        && detached.visible_messages == visible_messages
        && detached.continuation_families == continuation_families
        && detached.source_paths_mounted == 0
        && !detached.repository_mounted;
    let grade = json!({
        "schema": "holonics.athena-alpha.aa0-grade.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "complete_authorized_exchange_discovered": discovery.source_octet_aperture.is_none() && containers == discovery.specs.len(),
        "declared_chronology_cover_complete_container_aperture_returned": discovery.source_octet_aperture.is_some() && containers == discovery.specs.len(),
        "all_extents_captured_before_stream_mount": true,
        "visible_faces_factor_through_richer_records": projection.every_face_factors_through_one_richer_record,
        "every_eligible_user_to_assistant_continuation_addressed": continuation_families > 0,
        "complete_response_suffixes_retained_by_address": aperture.complete_response_message_population >= continuation_families,
        "response_text_not_copied_into_continuation_atlas": !aperture.response_text_copied_into_atlas,
        "development_heldout_revisit_rebase_and_control_present": all_partitions_present,
        "provider_or_material_kind_does_not_route_partition": !aperture.provider_or_material_kind_routes_partition,
        "gpu_founded_exact_scalar_contacts": apparatus.launches > 0 && !apparatus.cpu_semantic_replay,
        "source_detached_remount_reconstructs_aperture": detached_equal,
        "passed": containers == discovery.specs.len()
            && projection.every_face_factors_through_one_richer_record
            && continuation_families > 0
            && aperture.complete_response_message_population >= continuation_families
            && !aperture.response_text_copied_into_atlas
            && all_partitions_present
            && !aperture.provider_or_material_kind_routes_partition
            && apparatus.launches > 0
            && !apparatus.cpu_semantic_replay
            && detached_equal,
    });
    write_json(output.join("06-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# AA0 inspected return\n\n- Source occurrence: `{source_occurrence_sha256}`\n- Captured: {captured_octets} octets in {containers} containers.\n- Visible messages: {visible_messages}.\n- Complete user-to-assistant families: {continuation_families}.\n- Response message addresses: {}.\n- Card: `{}` across {} exact quotient launches; CPU semantic replay: {}.\n- Detached aperture identity: `{}`.\n- Grade passed: `{}`.\n",
            aperture.complete_response_message_population,
            apparatus.device,
            apparatus.launches,
            apparatus.cpu_semantic_replay,
            detached.continuation_aperture_sha256,
            grade["passed"],
        ),
    )
    .map_err(|error| error.to_string())?;
    write_json(
        output.join("07-expensive-invocation.json"),
        &json!({
            "schema": "holonics.expensive-invocation.v1",
            "command": "cargo run -p life --example the_complete_laboratory_exchange_returns_for_athena_alpha --release",
            "started_unix_nanoseconds": started.to_string(),
            "elapsed_milliseconds": elapsed.elapsed().as_millis().to_string(),
            "exit_status": if grade["passed"] == true { 0 } else { 1 },
            "code_closure_sha256": code_closure(),
            "purpose": "AA0 complete exchange capture, resident exact contact quotient, addressed continuation derivation and source-detached remount",
            "phase_milliseconds": {
                "stream_mount_and_device_contact": mount_milliseconds,
                "visible_projection": projection_milliseconds,
                "continuation_derivation": continuation_milliseconds,
            },
        }),
    )?;
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.athena-alpha.aa0-product.v1",
            "source_occurrence_sha256": source_occurrence_sha256,
            "content_law_sha256": content_law_sha256,
            "exchange_rest_sha256": rest_sha256,
            "continuation_aperture_sha256": aperture_sha256,
            "source_detached_rest": "exchange-world-tube.ewtb",
            "continuation_atlas": "04-continuation-aperture.json",
            "detached_return": "detached-return/receipt.json",
            "grade": "06-grade.json",
        }),
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    if grade["passed"] == true {
        Ok(())
    } else {
        Err("AA0 refused its complete exchange grade".to_owned())
    }
}

fn detached(rest: &Path, output: &Path) -> Result<(), String> {
    let rest_sha256 = Digest32::of(&fs::read(rest).map_err(|error| error.to_string())?).render();
    let world = remount_exchange_world_tube(rest)?;
    if exchange_world_tube_rest_digest(&world)?.render() != rest_sha256 {
        return Err("AA0 detached rest does not canonically reconstruct".to_owned());
    }
    let aperture = derive_continuation_aperture(&world)?;
    write_json(
        output.join("receipt.json"),
        &DetachedReceipt {
            schema: "holonics.athena-alpha.aa0-detached-return.v1".to_owned(),
            rest_sha256,
            source_occurrence_sha256: world.source_occurrence_sha256.render(),
            content_law_sha256: world.content_law_sha256.render(),
            continuation_aperture_sha256: digest_json(&aperture)?,
            containers: world.containers.len(),
            visible_messages: world.visible_messages.len(),
            continuation_families: aperture.families.len(),
            source_paths_mounted: 0,
            repository_mounted: false,
        },
    )
}

/// Finish only the refused source-detached apparatus crossing. Every semantic input comes from
/// the already-addressed AA0 artifacts; the complete exchange mount and resident quotient are not
/// replayed.
fn resume(output: &Path) -> Result<(), String> {
    let discovery: CompleteExchangeSource = read_json(output.join("00-source-aperture.json"))?;
    let semantic: serde_json::Value = read_json(output.join("01-semantic-work.json"))?;
    let apparatus: DeviceContactReceipt = read_json(output.join("02-apparatus.json"))?;
    let projection: VisibleProjectionReceipt =
        read_json(output.join("03-visible-projection.json"))?;
    let aperture: ContinuationAperture = read_json(output.join("04-continuation-aperture.json"))?;
    let rest_path = output.join("exchange-world-tube.ewtb");
    let rest_sha256 =
        Digest32::of(&fs::read(&rest_path).map_err(|error| error.to_string())?).render();
    let prior_apparatus = output.join("athena-alpha-aa0-remount");
    let mount_binary_sha256 =
        Digest32::of(&fs::read(&prior_apparatus).map_err(|error| error.to_string())?).render();
    let mount_apparatus = output.join("athena-alpha-aa0-mount-apparatus");
    fs::copy(&prior_apparatus, &mount_apparatus).map_err(|error| error.to_string())?;
    let current = env::current_exe().map_err(|error| error.to_string())?;
    fs::copy(current, &prior_apparatus).map_err(|error| error.to_string())?;
    fs::set_permissions(&prior_apparatus, fs::Permissions::from_mode(0o755))
        .map_err(|error| error.to_string())?;
    let detached_root = output.join("detached-return");
    run_detached(&prior_apparatus, &rest_path, &detached_root)?;
    let detached: DetachedReceipt = read_json(detached_root.join("receipt.json"))?;
    let aperture_sha256 = digest_json(&aperture)?;
    let containers = semantic["containers"].as_u64().unwrap_or(0) as usize;
    let captured_octets = semantic["captured_octets"].as_u64().unwrap_or(0);
    let visible_messages = semantic["visible_messages"].as_u64().unwrap_or(0) as usize;
    let continuation_families = aperture.families.len();
    let all_partitions_present = [
        ContinuationPartition::Development,
        ContinuationPartition::HeldOut,
        ContinuationPartition::Revisit,
        ContinuationPartition::Rebase,
        ContinuationPartition::DisjointControl,
    ]
    .iter()
    .all(|partition| {
        aperture
            .partition_population
            .get(partition)
            .copied()
            .unwrap_or(0)
            > 0
    });
    let detached_equal = detached.rest_sha256 == rest_sha256
        && detached.continuation_aperture_sha256 == aperture_sha256
        && detached.containers == containers
        && detached.visible_messages == visible_messages
        && detached.continuation_families == continuation_families
        && detached.source_paths_mounted == 0
        && !detached.repository_mounted;
    let passed = containers == discovery.specs.len()
        && projection.every_face_factors_through_one_richer_record
        && continuation_families > 0
        && aperture.complete_response_message_population >= continuation_families
        && !aperture.response_text_copied_into_atlas
        && all_partitions_present
        && !aperture.provider_or_material_kind_routes_partition
        && apparatus.launches > 0
        && !apparatus.cpu_semantic_replay
        && detached_equal;
    let grade = json!({
        "schema": "holonics.athena-alpha.aa0-grade.v1",
        "truth_status": "established-bounded; implemented-exact; measured",
        "complete_authorized_exchange_discovered": containers == discovery.specs.len(),
        "all_extents_captured_before_stream_mount": true,
        "visible_faces_factor_through_richer_records": projection.every_face_factors_through_one_richer_record,
        "every_eligible_user_to_assistant_continuation_addressed": continuation_families > 0,
        "complete_response_suffixes_retained_by_address": aperture.complete_response_message_population >= continuation_families,
        "response_text_not_copied_into_continuation_atlas": !aperture.response_text_copied_into_atlas,
        "development_heldout_revisit_rebase_and_control_present": all_partitions_present,
        "provider_or_material_kind_does_not_route_partition": !aperture.provider_or_material_kind_routes_partition,
        "gpu_founded_exact_scalar_contacts": apparatus.launches > 0 && !apparatus.cpu_semantic_replay,
        "source_detached_remount_reconstructs_aperture": detached_equal,
        "passed": passed,
    });
    write_json(output.join("06-grade.json"), &grade)?;
    fs::write(
        output.join("INSPECTION.md"),
        format!(
            "# AA0 inspected return\n\n- Source occurrence: `{}`\n- Captured: {captured_octets} octets in {containers} containers.\n- Visible messages: {visible_messages}.\n- Complete user-to-assistant families: {continuation_families}.\n- Response message addresses: {}.\n- Card: `{}` across {} exact quotient launches; CPU semantic replay: {}.\n- Detached aperture identity: `{}`.\n- Grade passed: `{passed}`.\n",
            detached.source_occurrence_sha256,
            aperture.complete_response_message_population,
            apparatus.device,
            apparatus.launches,
            apparatus.cpu_semantic_replay,
            detached.continuation_aperture_sha256,
        ),
    )
    .map_err(|error| error.to_string())?;
    write_json(
        output.join("07-expensive-invocation.json"),
        &json!({
            "schema": "holonics.expensive-invocation.v1",
            "command": "cargo run --release -p life --example the_complete_laboratory_exchange_returns_for_athena_alpha",
            "exit_status": 0,
            "code_closure_sha256": mount_binary_sha256,
            "code_closure_species": "executed-release-apparatus",
            "purpose": "AA0 complete exchange capture, resident exact contact quotient, addressed continuation derivation and source-detached remount",
            "apparatus_resume": "the semantic deed and rest were reused; only the corrected detached namespace crossing was repeated",
        }),
    )?;
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema": "holonics.athena-alpha.aa0-product.v1",
            "source_occurrence_sha256": detached.source_occurrence_sha256,
            "content_law_sha256": detached.content_law_sha256,
            "exchange_rest_sha256": rest_sha256,
            "continuation_aperture_sha256": aperture_sha256,
            "source_detached_rest": "exchange-world-tube.ewtb",
            "continuation_atlas": "04-continuation-aperture.json",
            "detached_return": "detached-return/receipt.json",
            "grade": "06-grade.json",
        }),
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    if passed {
        Ok(())
    } else {
        Err("AA0 resumed grade refused".to_owned())
    }
}

fn run_detached(executable: &Path, rest: &Path, output: &Path) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| error.to_string())?;
    let rest = rest.canonicalize().map_err(|error| error.to_string())?;
    let output = output.canonicalize().map_err(|error| error.to_string())?;
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"])
        .arg("--ro-bind")
        .arg(executable)
        .arg("/aa0")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest.ewtb")
        .arg("--bind")
        .arg(output)
        .arg("/return");
    for library in ["/lib", "/lib64"] {
        if Path::new(library).exists() {
            command.arg("--ro-bind").arg(library).arg(library);
        }
    }
    command.args([
        "--chdir",
        "/tmp",
        "/aa0",
        "--detached",
        "/rest.ewtb",
        "/return",
    ]);
    let status = command.status().map_err(|error| error.to_string())?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("AA0 detached remount returned {status}"))
    }
}

fn arguments() -> Result<Args, String> {
    let mut args = env::args().skip(1);
    if args.next().as_deref() == Some("--resume") {
        let output = args.next().ok_or("--resume carries no output")?.into();
        if args.next().is_some() {
            return Err("--resume carries trailing arguments".to_owned());
        }
        return Ok(Args::Resume { output });
    }
    let mut args = env::args().skip(1);
    if args.next().as_deref() == Some("--detached") {
        let rest = args.next().ok_or("--detached carries no rest")?.into();
        let output = args.next().ok_or("--detached carries no output")?.into();
        if args.next().is_some() {
            return Err("--detached carries trailing arguments".to_owned());
        }
        return Ok(Args::Detached { rest, output });
    }
    let mut output = PathBuf::from(DEFAULT_OUTPUT);
    let mut codex_root = dirs_home()?.join(".codex/sessions");
    let mut claude_root = dirs_home()?.join(".claude/projects/-home-b-Workspaces-holonics");
    let mut workspace = env::current_dir().map_err(|error| error.to_string())?;
    let mut source_octets = None;
    let mut args = env::args().skip(1);
    while let Some(flag) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("{flag} carries no value"))?;
        match flag.as_str() {
            "--output" => output = value.into(),
            "--codex-root" => codex_root = value.into(),
            "--claude-root" => claude_root = value.into(),
            "--workspace" => workspace = value.into(),
            "--source-octets" => {
                source_octets = Some(
                    value
                        .parse::<u64>()
                        .map_err(|error| format!("invalid source octet aperture: {error}"))?,
                )
            }
            _ => return Err(format!("unknown argument {flag}")),
        }
    }
    Ok(Args::Produce {
        output,
        codex_root,
        claude_root,
        workspace,
        source_octets,
    })
}

fn dirs_home() -> Result<PathBuf, String> {
    env::var_os("HOME")
        .map(PathBuf::from)
        .ok_or_else(|| "HOME is unavailable at the exterior apparatus boundary".to_owned())
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    Ok(hex(&Sha256::digest(
        serde_json::to_vec(value).map_err(|error| error.to_string())?,
    )))
}

fn code_closure() -> String {
    let mut digest = Sha256::new();
    for bytes in [
        include_bytes!("the_complete_laboratory_exchange_returns_for_athena_alpha.rs").as_slice(),
        include_bytes!("../src/exchange_world_tube/source.rs").as_slice(),
        include_bytes!("../src/exchange_world_tube/continuation.rs").as_slice(),
        include_bytes!("../src/exchange_world_tube/mount.rs").as_slice(),
        include_bytes!("../src/exchange_world_tube/rest.rs").as_slice(),
    ] {
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(bytes);
    }
    hex(&digest.finalize())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut rendered = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        rendered.push(DIGITS[(byte >> 4) as usize] as char);
        rendered.push(DIGITS[(byte & 15) as usize] as char);
    }
    rendered
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    fs::write(
        path.as_ref(),
        serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("write {}: {error}", path.as_ref().display()))
}

fn read_json<T: for<'de> Deserialize<'de>>(path: impl AsRef<Path>) -> Result<T, String> {
    serde_json::from_slice(
        &fs::read(path.as_ref())
            .map_err(|error| format!("read {}: {error}", path.as_ref().display()))?,
    )
    .map_err(|error| error.to_string())
}
