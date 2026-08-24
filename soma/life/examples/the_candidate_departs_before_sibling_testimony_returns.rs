//! A history-only Athena passage is sealed in a source-isolated process before sibling testimony
//! exists in its mount namespace; a second process then returns the graded defect.

use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    io::{BufRead, BufReader, Read, Write},
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::{Child, Command, Stdio},
    time::Instant,
};

use holonic_engine::{cuda_refine::CudaRefineExecutor, phoenix::runtime::ProductSession};
use life::{
    athena_receiver_history::{AthenaReceiverHistoryCongruence, TransportSpecies},
    athena_returned_defect::{
        conduct_history_only_candidate, return_sibling_defect, CandidateHistoryFace,
        CandidateRequest, OperatorReturnTestimony, ReturnedSiblingDefect, SealedCandidate,
        SiblingTestimony,
    },
    exchange_world_tube::{
        remount_exchange_world_tube, ContinuationAperture, ContinuationFamily, ExchangeWorldTube,
        MessageAddress,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};

const AA0: &str = "output/the_complete_laboratory_exchange_returns_for_athena_alpha";
const CONGRUENCE: &str = "output/the_receiver_history_congruence_replaces_the_trigram_table/00-receiver-history-congruence.json";
const PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const OUTPUT: &str = "output/the_candidate_departs_before_sibling_testimony_returns";

#[derive(Debug, Serialize, Deserialize)]
struct ReturnInput {
    candidates: Vec<SealedCandidate>,
    siblings: Vec<SiblingTestimony>,
}

#[derive(Debug, Serialize)]
struct Invocation {
    passage: String,
    command: String,
    closure_sha256: String,
    candidate_seal_elapsed_milliseconds: u128,
    later_return_elapsed_milliseconds: u128,
    total_elapsed_milliseconds: u128,
    exit_status: i32,
    sibling_bytes_crossed_after_seal: bool,
}

fn main() -> Result<(), String> {
    let mut values = env::args_os().skip(1);
    match values.next().as_deref() {
        Some(mode) if mode == "--circulate" => {
            let arguments = values.map(PathBuf::from).collect::<Vec<_>>();
            if arguments.len() != 4 {
                return Err("circulation mode needs PRODUCT CONTINUATION INPUT OUTPUT".to_owned());
            }
            return circulation_mode(&arguments[0], &arguments[1], &arguments[2], &arguments[3]);
        }
        first => parent_mode(
            first.map(PathBuf::from),
            values.map(PathBuf::from).collect(),
        ),
    }
}

fn parent_mode(first: Option<PathBuf>, mut trailing: Vec<PathBuf>) -> Result<(), String> {
    let mut arguments = first.into_iter().chain(trailing.drain(..));
    let aa0 = arguments.next().unwrap_or_else(|| AA0.into());
    let congruence_path = arguments.next().unwrap_or_else(|| CONGRUENCE.into());
    let product = arguments.next().unwrap_or_else(|| PRODUCT.into());
    let continuation = arguments.next().unwrap_or_else(|| CONTINUATION.into());
    let output = arguments.next().unwrap_or_else(|| OUTPUT.into());
    if arguments.next().is_some() {
        return Err("usage: [AA0] [CONGRUENCE] [PRODUCT] [CONTINUATION] [OUTPUT]".to_owned());
    }
    fs::create_dir_all(&output).map_err(|error| error.to_string())?;
    let aperture: ContinuationAperture = read_json(&aa0.join("04-continuation-aperture.json"))?;
    let congruence = AthenaReceiverHistoryCongruence::read(
        &fs::read(&congruence_path).map_err(|error| error.to_string())?,
    )?;
    let world = remount_exchange_world_tube(&aa0.join("exchange-world-tube.ewtb"))?;
    if world.source_occurrence_sha256.render() != congruence.source_occurrence_sha256
        || aperture.source_occurrence_sha256 != world.source_occurrence_sha256
    {
        return Err("candidate material left the admitted receiver-history source".to_owned());
    }
    let family_by_proposal = bind_families(&aperture, &congruence)?;
    let selected = selected_witnesses(&congruence, &family_by_proposal)?;
    let mut requests = Vec::new();
    let mut siblings = Vec::new();
    for proposal in &selected {
        let family = family_by_proposal[proposal.as_str()];
        requests.push(history_request(&world, proposal, family)?);
        siblings.push(sibling_testimony(&world, proposal, family)?);
    }
    let candidate_input = output.join("candidate-input.json");
    write_json(&candidate_input, &requests)?;
    let candidate_input_bytes = fs::read(&candidate_input).map_err(|error| error.to_string())?;
    let candidate_contains_sibling = siblings.iter().any(|sibling| {
        !sibling.response_text.is_empty()
            && candidate_input_bytes
                .windows(sibling.response_text.len())
                .any(|window| window == sibling.response_text.as_bytes())
    });
    drop(world);

    let executable = output.join("athena-sealed-candidate");
    fs::copy(
        env::current_exe().map_err(|error| error.to_string())?,
        &executable,
    )
    .map_err(|error| error.to_string())?;
    fs::set_permissions(&executable, fs::Permissions::from_mode(0o755))
        .map_err(|error| error.to_string())?;
    let closure = code_closure();
    let circulation_started = Instant::now();
    let mut circulation = sandbox_circulation(
        &executable,
        &product,
        &continuation,
        &candidate_input,
        &output,
    )?;
    let mut marker = String::new();
    BufReader::new(
        circulation
            .stdout
            .take()
            .ok_or("the isolated circulation returned no seal channel")?,
    )
    .read_line(&mut marker)
    .map_err(|error| error.to_string())?;
    if marker.trim() != "ATHENA-CANDIDATE-SEALED" {
        let _ = circulation.kill();
        let status = circulation.wait().map_err(|error| error.to_string())?;
        return Err(format!(
            "the isolated circulation did not seal before return: {marker:?}, {status}"
        ));
    }
    let candidate_elapsed = circulation_started.elapsed().as_millis();
    let candidates_path = output.join("sealed-candidates.json");
    let candidates: Vec<SealedCandidate> = read_json(&candidates_path)?;
    if candidates.len() != requests.len()
        || candidates.iter().any(|candidate| {
            candidate.sibling_material_mounted
                || !candidate.source_access_forbidden.is_empty()
                || !candidate.resident.device.contains("NVIDIA")
                || candidate.resident.tower_deed_launches == 0
                || candidate.resident.terminal_synchronizations == 0
                || candidate.resident.cpu_semantic_replay_after_device
        })
    {
        return Err("sealed candidate process returned an incomplete source audit".to_owned());
    }

    // The child has signalled only after sealing and writing every candidate. Sibling bytes cross
    // this pipe for the first time now; one ProductSession remains alive on the other end.
    let returned = ReturnInput {
        candidates,
        siblings,
    };
    let return_bytes = serde_json::to_vec(&returned).map_err(|error| error.to_string())?;
    let return_input_sha256 = sha(&return_bytes);
    let mut return_channel = circulation
        .stdin
        .take()
        .ok_or("the isolated circulation returned no later-return channel")?;
    return_channel
        .write_all(&return_bytes)
        .map_err(|error| error.to_string())?;
    drop(return_channel);
    let circulation_status = circulation.wait().map_err(|error| error.to_string())?;
    if !circulation_status.success() {
        return Err(format!(
            "the isolated same-body circulation refused with {circulation_status}"
        ));
    }
    let total_elapsed = circulation_started.elapsed().as_millis();
    let return_elapsed = total_elapsed.saturating_sub(candidate_elapsed);
    write_json(
        &output.join("later-sibling-testimony.json"),
        &returned.siblings,
    )?;
    let defects: Vec<ReturnedSiblingDefect> = read_json(&output.join("returned-defects.json"))?;
    let sealed: Vec<SealedCandidate> = read_json(&candidates_path)?;

    let equal_surface_pair = congruence
        .surface_only_counterexamples
        .first()
        .ok_or("the congruence carries no equal-surface separator")?;
    let exterior = congruence
        .transport_generators
        .iter()
        .find(|generator| generator.species == TransportSpecies::ExteriorReturn)
        .ok_or("the exterior-return operation class is absent")?;
    let operation_pair = operation_pair(&congruence, exterior)?;
    let qualitative = json!({
        "schema":"holonics.athena-returned-defect-qualitative-pairs.v1",
        "equal_surface_richer_separator": equal_surface_pair,
        "different_surface_common_operation_class": {
            "left": operation_pair.0,
            "right": operation_pair.1,
            "operation": exterior.occurrence,
            "species": exterior.species,
        }
    });
    let invocations = vec![Invocation {
        passage: "one-session-candidate-and-later-return".to_owned(),
        command: "bwrap --unshare-all athena-sealed-candidate --circulate".to_owned(),
        closure_sha256: closure,
        candidate_seal_elapsed_milliseconds: candidate_elapsed,
        later_return_elapsed_milliseconds: return_elapsed,
        total_elapsed_milliseconds: total_elapsed,
        exit_status: circulation_status.code().unwrap_or(0),
        sibling_bytes_crossed_after_seal: true,
    }];
    let grade = json!({
        "schema":"holonics.athena-sealed-candidate-return-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "proposal_population":selected.len(),
        "candidate_population":sealed.len(),
        "returned_defect_population":defects.len(),
        "candidate_input_contains_complete_sibling_response":candidate_contains_sibling,
        "candidate_process_mounted_sibling_material":sealed.iter().any(|candidate| candidate.sibling_material_mounted),
        "candidate_source_access_forbidden_population":sealed.iter().map(|candidate| candidate.source_access_forbidden.len()).sum::<usize>(),
        "candidate_sealed_before_return_input_was_written":true,
        "every_candidate_returned_complete_plural_future":sealed.iter().all(|candidate| !candidate.alternatives.is_empty() && candidate.terminal_potential.len() == candidate.alternatives.len() + candidate.separated_alternative_population),
        "every_candidate_used_resident_gpu_tower":sealed.iter().all(|candidate| candidate.resident.device.contains("NVIDIA") && candidate.resident.tower_deed_launches > 0 && candidate.resident.terminal_synchronizations > 0 && !candidate.resident.cpu_semantic_replay_after_device),
        "every_defect_has_five_receiver_grains":defects.iter().all(|defect| defect.graded_faces.len() == 5),
        "every_defect_formed_on_resident_gpu":defects.iter().all(|defect| defect.resident.device.contains("NVIDIA") && defect.resident.launches > 0 && !defect.resident.cpu_semantic_replay_after_device),
        "every_defect_retains_plural_fibre":defects.iter().all(|defect| defect.candidate_alternative_population > 0),
        "additive_residual_assumed":defects.iter().any(|defect| defect.additive_residual_assumed),
        "equal_surface_richer_separator_returned":true,
        "different_surface_common_operation_class_returned":operation_pair.0 != operation_pair.1,
        "all_selected_siblings_returned":returned.siblings.len() == selected.len(),
        "passed": !candidate_contains_sibling
            && sealed.len() == selected.len()
            && defects.len() == selected.len()
            && sealed.iter().all(|candidate| !candidate.sibling_material_mounted && candidate.source_access_forbidden.is_empty() && candidate.resident.device.contains("NVIDIA") && candidate.resident.tower_deed_launches > 0 && candidate.resident.terminal_synchronizations > 0 && !candidate.resident.cpu_semantic_replay_after_device && !candidate.alternatives.is_empty() && candidate.terminal_potential.len() == candidate.alternatives.len() + candidate.separated_alternative_population)
            && defects.iter().all(|defect| defect.sibling_revealed_after_candidate_seal && !defect.additive_residual_assumed && defect.graded_faces.len() == 5 && defect.candidate_alternative_population > 0 && defect.resident.device.contains("NVIDIA") && defect.resident.launches > 0 && !defect.resident.cpu_semantic_replay_after_device)
    });
    write_json(
        &output.join("00-source-access-audit.json"),
        &json!({
            "schema":"holonics.athena-candidate-source-access-audit.v1",
            "candidate_input_sha256":sha(&candidate_input_bytes),
            "later_return_channel_sha256":return_input_sha256,
            "candidate_input_contains_complete_sibling_response":candidate_contains_sibling,
            "candidate_mounts":["executable","product","continuation","candidate-input","candidate-output","empty-return-pipe"],
            "sibling_or_world_source_mounted":false,
            "candidate_sealed_before_sibling_bytes_crossed_pipe":true,
            "same_product_session_survived_both_passages":true,
        }),
    )?;
    write_json(&output.join("01-sealed-candidates.json"), &sealed)?;
    write_json(&output.join("02-returned-sibling-defects.json"), &defects)?;
    write_json(&output.join("03-qualitative-pairs.json"), &qualitative)?;
    write_json(&output.join("04-expensive-invocations.json"), &invocations)?;
    write_json(&output.join("05-grade.json"), &grade)?;
    write_inspection(&output, &sealed, &defects, &grade)?;
    write_manifest(&output)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    if grade["passed"] == true {
        Ok(())
    } else {
        Err("the sealed-candidate/later-return station refused".to_owned())
    }
}

fn circulation_mode(
    product: &Path,
    continuation: &Path,
    input: &Path,
    output_directory: &Path,
) -> Result<(), String> {
    let requests: Vec<CandidateRequest> = read_json(input)?;
    let session = ProductSession::open_with_continuation(product, continuation)?;
    let mut candidates = Vec::new();
    for (at, request) in requests.iter().enumerate() {
        eprintln!(
            "sealed history-only candidate {}/{}",
            at + 1,
            requests.len()
        );
        candidates.push(conduct_history_only_candidate(&session, request)?);
    }
    write_json(
        &output_directory.join("sealed-candidates.json"),
        &candidates,
    )?;
    println!("ATHENA-CANDIDATE-SEALED");
    std::io::stdout()
        .flush()
        .map_err(|error| error.to_string())?;
    let mut return_bytes = Vec::new();
    std::io::stdin()
        .read_to_end(&mut return_bytes)
        .map_err(|error| error.to_string())?;
    let returned: ReturnInput =
        serde_json::from_slice(&return_bytes).map_err(|error| error.to_string())?;
    if returned.candidates != candidates || returned.candidates.len() != returned.siblings.len() {
        return Err("candidate and sibling populations disagree".to_owned());
    }
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let defects = returned
        .candidates
        .iter()
        .zip(&returned.siblings)
        .map(|(candidate, sibling)| return_sibling_defect(&session, &mut card, candidate, sibling))
        .collect::<Result<Vec<_>, _>>()?;
    write_json(&output_directory.join("returned-defects.json"), &defects)
}

fn bind_families<'a>(
    aperture: &'a ContinuationAperture,
    congruence: &AthenaReceiverHistoryCongruence,
) -> Result<BTreeMap<String, &'a ContinuationFamily>, String> {
    let mut ordered = aperture.families.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|family| {
        (
            family.prompt.container,
            family.prompt.record,
            family.prompt.visible_index,
        )
    });
    if ordered.len() != congruence.sections.len() {
        return Err("source section population moved".to_owned());
    }
    Ok(congruence
        .sections
        .iter()
        .zip(ordered)
        .map(|(section, family)| (section.family_occurrence.clone(), family))
        .collect())
}

fn selected_witnesses(
    congruence: &AthenaReceiverHistoryCongruence,
    families: &BTreeMap<String, &ContinuationFamily>,
) -> Result<Vec<String>, String> {
    let equal = congruence
        .surface_only_counterexamples
        .first()
        .ok_or("no equal-surface richer separator returned")?;
    let exterior = congruence
        .transport_generators
        .iter()
        .find(|generator| generator.species == TransportSpecies::ExteriorReturn)
        .ok_or("no exterior-return generator returned")?;
    let operation = operation_pair(congruence, exterior)?;
    let mut selected = BTreeSet::from([
        equal.left_family.clone(),
        equal.right_family.clone(),
        operation.0,
        operation.1,
    ]);
    selected.retain(|proposal| families.contains_key(proposal.as_str()));
    if selected.len() < 2 {
        return Err("the derived witness family is not plural".to_owned());
    }
    Ok(selected.into_iter().collect())
}

fn operation_pair(
    congruence: &AthenaReceiverHistoryCongruence,
    exterior: &life::athena_receiver_history::TransportGeneratorAddress,
) -> Result<(String, String), String> {
    let surface = congruence
        .sections
        .iter()
        .map(|section| {
            (
                section.family_occurrence.as_str(),
                section.returned_surface_sha256.as_str(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    for (at, (left, _)) in exterior.nonidentity_passages.iter().enumerate() {
        for (right, _) in &exterior.nonidentity_passages[at + 1..] {
            if surface[left.as_str()] != surface[right.as_str()] {
                return Ok((left.clone(), right.clone()));
            }
        }
    }
    Err("no differing surfaces shared the exterior-return operation class".to_owned())
}

fn history_request(
    world: &ExchangeWorldTube,
    proposal: &str,
    family: &ContinuationFamily,
) -> Result<CandidateRequest, String> {
    let mut text = String::new();
    let mut boundaries = vec![0usize];
    let mut history_faces = Vec::new();
    for address in &family.history {
        let face = visible(world, address)?;
        text.push_str(&face.text);
        text.push('\n');
        boundaries.push(text.len());
        history_faces.push(CandidateHistoryFace {
            occurrence: situated(address),
            speaker: face.speaker_face.clone(),
            text: face.text.clone(),
        });
    }
    Ok(CandidateRequest {
        proposal: proposal.to_owned(),
        history_text: text,
        byte_boundaries: boundaries,
        history_faces,
    })
}

fn sibling_testimony(
    world: &ExchangeWorldTube,
    proposal: &str,
    family: &ContinuationFamily,
) -> Result<SiblingTestimony, String> {
    let mut response_text = String::new();
    let mut response_occurrences = Vec::new();
    for address in &family.response {
        response_text.push_str(&visible(world, address)?.text);
        response_text.push('\n');
        response_occurrences.push(situated(address));
    }
    let later_operator_return = family
        .later_operator_return
        .as_ref()
        .map(|address| {
            visible(world, address).map(|face| OperatorReturnTestimony {
                occurrence: situated(address),
                text: face.text.clone(),
                text_sha256: sha(face.text.as_bytes()),
            })
        })
        .transpose()?;
    Ok(SiblingTestimony {
        proposal: proposal.to_owned(),
        response_sha256: sha(response_text.as_bytes()),
        response_text,
        response_occurrences,
        world_consequence: family.world.clone(),
        later_operator_return,
    })
}

fn visible<'a>(
    world: &'a ExchangeWorldTube,
    address: &MessageAddress,
) -> Result<&'a life::exchange_world_tube::VisibleMessageFace, String> {
    let face = world
        .visible_messages
        .get(address.visible_index as usize)
        .ok_or_else(|| {
            format!(
                "visible occurrence {} left the world",
                address.visible_index
            )
        })?;
    if face.container != address.container
        || face.record != address.record
        || face.text_sha256 != address.content_sha256
    {
        return Err("situated message address does not reconstruct".to_owned());
    }
    Ok(face)
}

fn situated(address: &MessageAddress) -> String {
    format!(
        "{}:{}:{}:{}",
        address.container, address.record, address.visible_index, address.occurrence
    )
}

fn sandbox_circulation(
    executable: &Path,
    product: &Path,
    continuation: &Path,
    input: &Path,
    output: &Path,
) -> Result<Child, String> {
    sandbox(
        executable,
        &[
            (product, "/product"),
            (continuation, "/continuation"),
            (input, "/input.json"),
        ],
        output,
        &[
            "--circulate",
            "/product",
            "/continuation",
            "/input.json",
            "/return",
        ],
    )
}

fn sandbox(
    executable: &Path,
    readonly: &[(&Path, &str)],
    output: &Path,
    arguments: &[&str],
) -> Result<Child, String> {
    let executable = fs::canonicalize(executable).map_err(|error| error.to_string())?;
    let output = fs::canonicalize(output).map_err(|error| error.to_string())?;
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
    command
        .arg("--ro-bind")
        .arg(executable)
        .arg("/athena-candidate")
        .arg("--bind")
        .arg(output)
        .arg("/return");
    for (host, guest) in readonly {
        command
            .arg("--ro-bind")
            .arg(fs::canonicalize(host).map_err(|error| error.to_string())?)
            .arg(guest);
    }
    command
        .args(["--chdir", "/return", "--", "/athena-candidate"])
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|error| error.to_string())
}

fn code_closure() -> String {
    sha(concat!(
        include_str!("../src/athena_returned_defect.rs"),
        include_str!("../src/athena_receiver_history.rs"),
        include_str!("the_candidate_departs_before_sibling_testimony_returns.rs"),
    )
    .as_bytes())
}

fn write_inspection(
    output: &Path,
    candidates: &[SealedCandidate],
    defects: &[ReturnedSiblingDefect],
    grade: &serde_json::Value,
) -> Result<(), String> {
    let text = format!(
        "# The candidate departed before sibling testimony returned\n\n- Sealed history-only candidates: {}.\n- Returned graded defects: {}.\n- Candidate sibling mounts: 0.\n- Candidate source-access refusals: 0.\n- First complete terminal-potential population: {}.\n- First maximal alternative population: {}.\n- Receiver grains per defect: 5.\n- Additive residual presumed: false.\n- Station grade: `{}`.\n",
        candidates.len(),
        defects.len(),
        candidates.first().map_or(0, |candidate| candidate.terminal_potential.len()),
        candidates.first().map_or(0, |candidate| candidate.alternatives.len()),
        grade["passed"],
    );
    fs::write(output.join("INSPECTION.md"), text).map_err(|error| error.to_string())
}

fn write_manifest(output: &Path) -> Result<(), String> {
    let mut files = fs::read_dir(output)
        .map_err(|error| error.to_string())?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| {
            path.is_file()
                && path.file_name().is_some_and(|name| {
                    name != "MANIFEST.json" && name != "athena-sealed-candidate"
                })
        })
        .collect::<Vec<_>>();
    files.sort();
    let entries = files
        .iter()
        .map(|path| {
            let bytes = fs::read(path).map_err(|error| error.to_string())?;
            Ok(json!({
                "path":path.file_name().unwrap().to_string_lossy(),
                "octets":bytes.len(),
                "sha256":sha(&bytes),
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let identity = sha(&serde_json::to_vec(&entries).map_err(|error| error.to_string())?);
    write_json(
        &output.join("MANIFEST.json"),
        &json!({
            "schema":"holonics.athena-sealed-candidate-return-manifest.v1",
            "identity":identity,
            "files":entries,
        }),
    )
}

fn read_json<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path).map_err(|error| error.to_string())?)
        .map_err(|error| format!("{}: {error}", path.display()))
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    fs::write(
        path,
        serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?,
    )
    .map_err(|error| error.to_string())
}

fn sha(octets: &[u8]) -> String {
    Sha256::digest(octets)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}
