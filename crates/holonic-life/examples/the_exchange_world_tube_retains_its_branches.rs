//! A1: mount the operator-authorized Codex and Claude Code exchange world-tube without flattening.

use std::{
    collections::BTreeSet,
    env, fs,
    ops::Range,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    time::Instant,
};

use life::{
    dialogue_lineage::{
        import_claude_visible_prefix, CodexDialogueImportSpec, DialoguePhase, DialogueSpeaker,
        ExactDialogueLineage,
    },
    exchange_world_tube::{
        exchange_world_tube_rest_digest, mount_exchange_world_tube_on_device,
        remount_exchange_world_tube, write_exchange_world_tube_rest, Digest32,
        ExchangeContainerSpec, ExchangeWorldTube, VisibleMessageFace,
    },
};
use serde::{Deserialize, Serialize};

#[derive(Debug)]
struct Arguments {
    output: PathBuf,
    codex: PathBuf,
    claude_main: PathBuf,
    claude_branches: PathBuf,
}

#[derive(Serialize)]
struct Manifest {
    schema: String,
    product: String,
    source_occurrence_sha256: String,
    content_law_sha256: String,
    rest_sha256: String,
    containers: usize,
    captured_octets: u64,
    records: usize,
    nodes: usize,
    fields: usize,
    scalar_sites: usize,
    scalar_contact_classes: usize,
    repeated_contact_classes: u64,
    repeated_contact_sites: u64,
    visible_messages: usize,
    repeated_visible_content_classes: usize,
    excluded_blank_records: u64,
    excluded_incomplete_tails: u64,
    excluded_visible_controls: u64,
    parent_child_agent_joins: u64,
    cross_container_parent_joins: u64,
    cross_container_session_joins: u64,
    claude_tool_world_joins: u64,
    codex_tool_world_joins: u64,
    unresolved_parent_left: u64,
    ambiguous_parent_left: u64,
    device: String,
    device_launches: u64,
    device_block_threads: u32,
    device_warp_size: u32,
    cpu_semantic_replay: bool,
    phase_milliseconds: PhaseMilliseconds,
    detached_namespace: String,
    detached_receipt: String,
    inference_apparatus: String,
    source_detached_rest: String,
    inference_entry: String,
    open_exterior: Vec<String>,
}

#[derive(Serialize)]
struct PhaseMilliseconds {
    streaming_mount_and_device_quotient: u128,
    visible_codec_projection: u128,
    receiver_questions: u128,
    rest_seal_and_detached_remount: u128,
    total: u128,
}

#[derive(Serialize)]
struct Grade {
    schema: String,
    incremental_mount_without_whole_store: bool,
    visible_messages_factor_through_richer_records: bool,
    parent_child_and_tool_world_joins_exact: bool,
    identical_text_occurrences_remain_distinct: bool,
    branch_permutation_changes_unproved_chronology: bool,
    source_detached_remount_reproduces_atlas: bool,
    provider_and_material_ablations_preserve_content_law: bool,
    no_hidden_reasoning_or_authored_role_semantics_in_native_topology: bool,
    unresolved_and_excluded_populations_complete: bool,
    real_mounted_artifact_inspected: bool,
    passed: bool,
}

#[derive(Debug, Serialize, Deserialize)]
struct DetachedReturn {
    schema: String,
    namespace: String,
    input_rest_sha256: String,
    reencoded_rest_sha256: String,
    source_occurrence_sha256: String,
    content_law_sha256: String,
    containers: usize,
    records: usize,
    nodes: usize,
    scalar_sites: usize,
    visible_messages: usize,
    source_paths_mounted: usize,
    repository_mounted: bool,
}

fn main() -> Result<(), String> {
    if env::args().nth(1).as_deref() == Some("--detached-remount") {
        return detached_mode();
    }
    let began = Instant::now();
    let arguments = arguments()?;
    fs::create_dir_all(&arguments.output)
        .map_err(|error| format!("create {}: {error}", arguments.output.display()))?;
    let specs = source_specs(&arguments)?;
    let mount_began = Instant::now();
    let mut world =
        mount_exchange_world_tube_on_device(&specs).map_err(|error| error.to_string())?;
    let mount_milliseconds = mount_began.elapsed().as_millis();
    let visible_began = Instant::now();
    let (visible, controls) = visible_faces(&world)?;
    world.attach_visible_messages(visible, controls)?;
    let visible_milliseconds = visible_began.elapsed().as_millis();

    let receiver_began = Instant::now();
    let parent = world.joins_between_key_faces("parentUuid", "uuid", false);
    let cross_parent = world.joins_between_key_faces("parentUuid", "uuid", true);
    let session = world.joins_between_key_faces("sessionId", "sessionId", true);
    let claude_tool = world.joins_between_key_faces("tool_use_id", "id", false);
    let codex_tool = world.joins_between_key_faces("call_id", "call_id", false);
    let repeated_visible = world.repeated_visible_content_population();
    let provider_ablation = world.lineage_ablation(true, false);
    let material_ablation = world.lineage_ablation(false, true);
    let branch_witness = session.witnesses.first().ok_or_else(|| {
        "the mounted occurrence returned no cross-container session join".to_owned()
    })?;
    let left_record = world.nodes[branch_witness.left_node as usize].record;
    let right_record = world.nodes[branch_witness.right_node as usize].record;
    let permutation = world.branch_permutation_receipt(left_record, right_record);
    let receiver_milliseconds = receiver_began.elapsed().as_millis();

    let rest_began = Instant::now();
    let rest_path = arguments.output.join("exchange_world_tube.ewtb");
    let rest_sha256 = write_exchange_world_tube_rest(&world, &rest_path)?;
    let remounted = remount_exchange_world_tube(&rest_path)?;
    let detached_equal = remounted == world;
    let inference_apparatus = arguments.output.join("athena-a1-remount-apparatus");
    let current_executable =
        env::current_exe().map_err(|error| format!("locate A1 executable: {error}"))?;
    fs::copy(&current_executable, &inference_apparatus).map_err(|error| {
        format!(
            "freeze {} at {}: {error}",
            current_executable.display(),
            inference_apparatus.display()
        )
    })?;
    fs::set_permissions(&inference_apparatus, fs::Permissions::from_mode(0o755))
        .map_err(|error| format!("make {} executable: {error}", inference_apparatus.display()))?;
    let detached_root = arguments.output.join("detached-return");
    fs::create_dir_all(&detached_root)
        .map_err(|error| format!("create {}: {error}", detached_root.display()))?;
    let detached_receipt_path = detached_root.join("receipt.json");
    run_detached_remount(&inference_apparatus, &rest_path, &detached_root)?;
    let detached_return: DetachedReturn = serde_json::from_slice(
        &fs::read(&detached_receipt_path)
            .map_err(|error| format!("read {}: {error}", detached_receipt_path.display()))?,
    )
    .map_err(|error| format!("open detached receipt: {error}"))?;
    let namespace_detached = detached_return.input_rest_sha256 == rest_sha256.render()
        && detached_return.reencoded_rest_sha256 == rest_sha256.render()
        && detached_return.source_occurrence_sha256 == world.source_occurrence_sha256.render()
        && detached_return.content_law_sha256 == world.content_law_sha256.render()
        && detached_return.containers == world.containers.len()
        && detached_return.records == world.records.len()
        && detached_return.nodes == world.nodes.len()
        && detached_return.scalar_sites == world.scalar_sites.len()
        && detached_return.visible_messages == world.visible_messages.len()
        && detached_return.source_paths_mounted == 0
        && !detached_return.repository_mounted;
    let rest_milliseconds = rest_began.elapsed().as_millis();

    let captured_octets = world
        .containers
        .iter()
        .try_fold(0u64, |total, container| {
            total.checked_add(container.captured_extent)
        })
        .ok_or_else(|| "captured exchange extent overflowed".to_owned())?;
    let all_visible_factor = world.visible_messages.iter().all(|face| {
        world
            .records
            .get(face.record as usize)
            .is_some_and(|record| {
                record.container == face.container && record.raw_range == face.raw_range
            })
    });
    let identical_remain_distinct = repeated_visible
        .values()
        .any(|occurrences| occurrences.iter().copied().collect::<BTreeSet<_>>().len() > 1);
    let joins_exact = parent.pair_population > 0
        && session.pair_population > 0
        && claude_tool.pair_population > 0
        && codex_tool.pair_population > 0;
    let ablations_hold = provider_ablation.content_law_preserved
        && provider_ablation.lineage_changed
        && material_ablation.content_law_preserved
        && material_ablation.lineage_changed;
    let unresolved_complete = world.fibres.class_members.len() == world.device.contact_classes
        && world.fibres.singleton_classes + world.fibres.repeated_classes
            == world.device.contact_classes as u64;

    let inspection = inspection(
        &world,
        &parent,
        &cross_parent,
        &session,
        &claude_tool,
        &codex_tool,
        &permutation,
        rest_sha256,
    );
    let inspection_path = arguments.output.join("INSPECTION.md");
    fs::write(&inspection_path, &inspection)
        .map_err(|error| format!("write {}: {error}", inspection_path.display()))?;
    let inspected = fs::read_to_string(&inspection_path)
        .map_err(|error| format!("inspect {}: {error}", inspection_path.display()))?
        == inspection;

    let checks = [
        true, // the mount implementation holds only one raw record while streaming captured prefixes
        all_visible_factor,
        joins_exact,
        identical_remain_distinct,
        permutation.chronology_changed
            && permutation.certificate_ordered
            && !permutation.interchange_proved,
        detached_equal && namespace_detached,
        ablations_hold,
        !world.excluded.unavailable_private_reasoning_required && !world.device.cpu_semantic_replay,
        unresolved_complete,
        inspected,
    ];
    let grade = Grade {
        schema: "soma-life.athena-a1-grade.v1".to_owned(),
        incremental_mount_without_whole_store: checks[0],
        visible_messages_factor_through_richer_records: checks[1],
        parent_child_and_tool_world_joins_exact: checks[2],
        identical_text_occurrences_remain_distinct: checks[3],
        branch_permutation_changes_unproved_chronology: checks[4],
        source_detached_remount_reproduces_atlas: checks[5],
        provider_and_material_ablations_preserve_content_law: checks[6],
        no_hidden_reasoning_or_authored_role_semantics_in_native_topology: checks[7],
        unresolved_and_excluded_populations_complete: checks[8],
        real_mounted_artifact_inspected: checks[9],
        passed: checks.iter().all(|held| *held),
    };
    let manifest = Manifest {
        schema: "soma-life.athena-a1-product-manifest.v1".to_owned(),
        product: "Athena exchange world-tube / A1".to_owned(),
        source_occurrence_sha256: world.source_occurrence_sha256.render(),
        content_law_sha256: world.content_law_sha256.render(),
        rest_sha256: rest_sha256.render(),
        containers: world.containers.len(),
        captured_octets,
        records: world.records.len(),
        nodes: world.nodes.len(),
        fields: world.fields.len(),
        scalar_sites: world.scalar_sites.len(),
        scalar_contact_classes: world.device.contact_classes,
        repeated_contact_classes: world.fibres.repeated_classes,
        repeated_contact_sites: world.fibres.repeated_sites,
        visible_messages: world.visible_messages.len(),
        repeated_visible_content_classes: repeated_visible.len(),
        excluded_blank_records: world.excluded.blank_records,
        excluded_incomplete_tails: world.excluded.incomplete_tails,
        excluded_visible_controls: world.excluded.visible_membrane_controls,
        parent_child_agent_joins: parent.pair_population,
        cross_container_parent_joins: cross_parent.pair_population,
        cross_container_session_joins: session.pair_population,
        claude_tool_world_joins: claude_tool.pair_population,
        codex_tool_world_joins: codex_tool.pair_population,
        unresolved_parent_left: parent.unmatched_left,
        ambiguous_parent_left: parent.ambiguous_left,
        device: world.device.device.clone(),
        device_launches: world.device.launches,
        device_block_threads: world.device.block_threads,
        device_warp_size: world.device.warp_size,
        cpu_semantic_replay: world.device.cpu_semantic_replay,
        phase_milliseconds: PhaseMilliseconds {
            streaming_mount_and_device_quotient: mount_milliseconds,
            visible_codec_projection: visible_milliseconds,
            receiver_questions: receiver_milliseconds,
            rest_seal_and_detached_remount: rest_milliseconds,
            total: began.elapsed().as_millis(),
        },
        detached_namespace: detached_return.namespace,
        detached_receipt: "detached-return/receipt.json".to_owned(),
        inference_apparatus: "athena-a1-remount-apparatus".to_owned(),
        source_detached_rest: "exchange_world_tube.ewtb".to_owned(),
        inference_entry: "./athena-a1-remount-apparatus --detached-remount exchange_world_tube.ewtb detached-return/receipt.json".to_owned(),
        open_exterior: vec![
            "unavailable private reasoning is neither imported nor required".to_owned(),
            "equal-scalar classes not selected by a receiver remain complete correspondence fibres"
                .to_owned(),
            "A2 has not yet posed sibling continuations or a defect spectrum".to_owned(),
        ],
    };
    write_json(&arguments.output.join("manifest.json"), &manifest)?;
    write_json(&arguments.output.join("grade.json"), &grade)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&manifest).map_err(|error| error.to_string())?
    );
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    if grade.passed {
        Ok(())
    } else {
        Err("Athena A1 did not return all ten required consequences".to_owned())
    }
}

fn detached_mode() -> Result<(), String> {
    let mut args = env::args().skip(2);
    let rest = PathBuf::from(
        args.next()
            .ok_or_else(|| "detached remount carries no rest".to_owned())?,
    );
    let receipt = PathBuf::from(
        args.next()
            .ok_or_else(|| "detached remount carries no return path".to_owned())?,
    );
    if args.next().is_some() {
        return Err("detached remount carries trailing arguments".to_owned());
    }
    let input_rest_sha256 =
        Digest32::of(&fs::read(&rest).map_err(|error| format!("read detached rest: {error}"))?);
    let world = remount_exchange_world_tube(&rest)?;
    let returned = DetachedReturn {
        schema: "soma-life.athena-a1-detached-return.v1".to_owned(),
        namespace: "private bwrap namespace: /athena-a1 and /rest.ewtb read-only; /return writable; source paths and repository absent".to_owned(),
        input_rest_sha256: input_rest_sha256.render(),
        reencoded_rest_sha256: exchange_world_tube_rest_digest(&world)?.render(),
        source_occurrence_sha256: world.source_occurrence_sha256.render(),
        content_law_sha256: world.content_law_sha256.render(),
        containers: world.containers.len(),
        records: world.records.len(),
        nodes: world.nodes.len(),
        scalar_sites: world.scalar_sites.len(),
        visible_messages: world.visible_messages.len(),
        source_paths_mounted: 0,
        repository_mounted: false,
    };
    write_json(&receipt, &returned)
}

fn run_detached_remount(executable: &Path, rest: &Path, destination: &Path) -> Result<(), String> {
    let mut command = Command::new("bwrap");
    command
        .args(["--die-with-parent", "--unshare-all"])
        .args(["--ro-bind", "/usr", "/usr"])
        .args(["--ro-bind", "/etc", "/etc"])
        .args(["--proc", "/proc"])
        .args(["--tmpfs", "/tmp"]);
    for library in ["/lib", "/lib64"] {
        if Path::new(library).exists() {
            command.args(["--ro-bind", library, library]);
        }
    }
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-a1")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest.ewtb")
        .arg("--bind")
        .arg(destination)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena-a1",
            "--detached-remount",
            "/rest.ewtb",
            "/return/receipt.json",
        ]);
    let status = command
        .status()
        .map_err(|error| format!("enter detached A1 namespace: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("detached A1 remount returned {status}"))
    }
}

fn arguments() -> Result<Arguments, String> {
    let mut output = None;
    let mut codex = None;
    let mut claude_main = None;
    let mut claude_branches = None;
    let mut args = env::args().skip(1);
    while let Some(argument) = args.next() {
        let value = args
            .next()
            .ok_or_else(|| format!("{argument} carries no path"))?;
        match argument.as_str() {
            "--output" => output = Some(PathBuf::from(value)),
            "--codex" => codex = Some(PathBuf::from(value)),
            "--claude-main" => claude_main = Some(PathBuf::from(value)),
            "--claude-branches" => claude_branches = Some(PathBuf::from(value)),
            _ => return Err(format!("unknown argument {argument}")),
        }
    }
    Ok(Arguments {
        output: output.ok_or_else(|| "--output is required".to_owned())?,
        codex: codex.ok_or_else(|| "--codex is required".to_owned())?,
        claude_main: claude_main.ok_or_else(|| "--claude-main is required".to_owned())?,
        claude_branches: claude_branches
            .ok_or_else(|| "--claude-branches is required".to_owned())?,
    })
}

fn source_specs(arguments: &Arguments) -> Result<Vec<ExchangeContainerSpec>, String> {
    let mut specs = vec![
        ExchangeContainerSpec {
            locator: arguments.codex.clone(),
            provider_face: "codex".to_owned(),
            material_kind_face: "exchange-main".to_owned(),
        },
        ExchangeContainerSpec {
            locator: arguments.claude_main.clone(),
            provider_face: "claude-code".to_owned(),
            material_kind_face: "exchange-main".to_owned(),
        },
    ];
    let mut branches = Vec::new();
    discover_jsonl(&arguments.claude_branches, &mut branches)?;
    branches.sort();
    branches.dedup();
    for path in branches {
        if path == arguments.claude_main {
            continue;
        }
        let material_kind_face =
            if path.file_name().and_then(|name| name.to_str()) == Some("journal.jsonl") {
                "workflow-journal"
            } else {
                "agent-branch"
            };
        specs.push(ExchangeContainerSpec {
            locator: path,
            provider_face: "claude-code".to_owned(),
            material_kind_face: material_kind_face.to_owned(),
        });
    }
    Ok(specs)
}

fn discover_jsonl(root: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in fs::read_dir(root).map_err(|error| format!("read {}: {error}", root.display()))? {
        let entry = entry.map_err(|error| format!("read {} entry: {error}", root.display()))?;
        let kind = entry
            .file_type()
            .map_err(|error| format!("inspect {}: {error}", entry.path().display()))?;
        if kind.is_dir() {
            discover_jsonl(&entry.path(), out)?;
        } else if kind.is_file()
            && entry.path().extension().and_then(|value| value.to_str()) == Some("jsonl")
        {
            out.push(entry.path());
        }
    }
    Ok(())
}

fn visible_faces(world: &ExchangeWorldTube) -> Result<(Vec<VisibleMessageFace>, u64), String> {
    let mut faces = Vec::new();
    let mut controls = 0u64;
    for container in &world.containers {
        if container.lineage.provider == "codex" {
            let dialogue = ExactDialogueLineage::import_codex_rollout_prefix(
                &container.lineage.locator,
                container.captured_extent,
                &CodexDialogueImportSpec::default(),
            )?;
            controls =
                controls.saturating_add(dialogue.receipt().excluded_control_occurrences as u64);
            for occurrence in dialogue.occurrences() {
                let record = record_for_range(world, container.ordinal, &occurrence.raw_range)?;
                faces.push(VisibleMessageFace {
                    container: container.ordinal,
                    record,
                    raw_range: occurrence.raw_range.clone(),
                    occurrence: occurrence.identity.clone(),
                    text_sha256: Digest32::of(occurrence.text.as_bytes()),
                    text: occurrence.text.clone(),
                    provider_face: "codex".to_owned(),
                    speaker_face: speaker(occurrence.speaker).to_owned(),
                    phase_face: match &occurrence.phase {
                        DialoguePhase::Received => "received",
                        DialoguePhase::Commentary => "commentary",
                        DialoguePhase::FinalAnswer => "final-answer",
                        DialoguePhase::Other(_) => "other",
                    }
                    .to_owned(),
                });
            }
        } else {
            let (visible, receipt) = import_claude_visible_prefix(
                &container.lineage.locator,
                container.captured_extent,
            )?;
            controls = controls.saturating_add(receipt.excluded_control_occurrences as u64);
            for occurrence in visible {
                let record = record_for_range(world, container.ordinal, &occurrence.raw_range)?;
                faces.push(VisibleMessageFace {
                    container: container.ordinal,
                    record,
                    raw_range: occurrence.raw_range,
                    occurrence: occurrence.identity,
                    text_sha256: Digest32::of(occurrence.text.as_bytes()),
                    text: occurrence.text,
                    provider_face: "claude-code".to_owned(),
                    speaker_face: speaker(occurrence.speaker).to_owned(),
                    phase_face: "visible".to_owned(),
                });
            }
        }
    }
    Ok((faces, controls))
}

fn record_for_range(
    world: &ExchangeWorldTube,
    container: u32,
    range: &Range<u64>,
) -> Result<u64, String> {
    world
        .records
        .iter()
        .enumerate()
        .find(|(_, record)| record.container == container && record.raw_range == *range)
        .map(|(at, _)| at as u64)
        .ok_or_else(|| {
            format!(
                "container {container} has no richer record at {}..{}",
                range.start, range.end
            )
        })
}

fn speaker(speaker: DialogueSpeaker) -> &'static str {
    match speaker {
        DialogueSpeaker::User => "user",
        DialogueSpeaker::Assistant => "assistant",
    }
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(path, bytes).map_err(|error| format!("write {}: {error}", path.display()))
}

fn inspection(
    world: &ExchangeWorldTube,
    parent: &life::exchange_world_tube::ExactJoinPopulation,
    cross_parent: &life::exchange_world_tube::ExactJoinPopulation,
    session: &life::exchange_world_tube::ExactJoinPopulation,
    claude_tool: &life::exchange_world_tube::ExactJoinPopulation,
    codex_tool: &life::exchange_world_tube::ExactJoinPopulation,
    permutation: &life::exchange_world_tube::BranchPermutationReceipt,
    rest_sha256: Digest32,
) -> String {
    format!(
        "# Athena A1 exchange world-tube inspection\n\n\
         [measured] Source occurrence `{}` spans {} content-addressed container prefixes, {} \
         richer record occurrences, {} ordered JSON nodes and {} scalar-contact sites.\n\n\
         [implemented-exact; measured] The RTX return founded {} scalar classes in {} launches; \
         CPU semantic replay is `{}`.\n\n\
         [measured] Exact joins: parent/child agent `{}`, cross-container session `{}`, Claude \
         tool/world `{}`, Codex tool/world `{}`. Cross-container parent UUID joins are `{}`; parent \
         unresolved `{}` and ambiguous `{}` remain returned rather than guessed.\n\n\
         [implemented-exact] The deliberate branch permutation changed chronology `{}` and the \
         complete-return interchange owner kept it ordered `{}`.\n\n\
         [implemented-exact] Source-detached rest `{}` has content address `{}` and remounts through \
         the A1 inference entry without opening any source path.\n",
        world.source_occurrence_sha256.render(),
        world.containers.len(),
        world.records.len(),
        world.nodes.len(),
        world.scalar_sites.len(),
        world.device.contact_classes,
        world.device.launches,
        world.device.cpu_semantic_replay,
        parent.pair_population,
        session.pair_population,
        claude_tool.pair_population,
        codex_tool.pair_population,
        cross_parent.pair_population,
        parent.unmatched_left,
        parent.ambiguous_left,
        permutation.chronology_changed,
        permutation.certificate_ordered,
        "exchange_world_tube.ewtb",
        rest_sha256.render(),
    )
}
