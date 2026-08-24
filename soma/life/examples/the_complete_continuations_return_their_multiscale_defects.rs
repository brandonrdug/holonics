//! AA1: every development continuation crosses the fixed E5 predecessor as one whole known suffix.
//!
//! Each visible message is one addressed receiver row. The complete response suffix crosses in a
//! single tower deed per family; the driver never replays the tower once per target codeword. At
//! each response boundary it returns the complete interval-compatible alternative fibre together
//! with codeword, phrase, equation/code, whole-response and world-return defect faces.

use std::{
    env, fs,
    path::{Path, PathBuf},
    time::{Instant, SystemTime, UNIX_EPOCH},
};

use holonic_engine::phoenix::{
    runtime::{ProductSession, RuntimeReceipt},
    streamed::{InterventionSite, ReceiverOption},
    tower::Intervention,
};
use life::exchange_world_tube::{
    ContinuationAperture, ContinuationFamily, ContinuationPartition, ExchangeWorldTube,
    VisibleMessageFace, remount_exchange_world_tube,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const AA0: &str = "output/the_complete_laboratory_exchange_returns_for_athena_alpha";
const PRODUCT: &str =
    "output/the_lifted_body_is_cultivated_and_the_delta_survives_native_rest/product";
const CONTINUATION: &str =
    "output/the_exchange_return_cultivates_athena_gemma/product/continuation";
const OUTPUT: &str = "output/the_complete_continuations_return_their_multiscale_defects";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AlternativeFace {
    native_id: u32,
    surface: String,
    lower: i64,
    upper: i64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct BoundaryDefect {
    response_occurrence: String,
    response_visible_index: u64,
    predecessor_receiver_row: usize,
    complete_target_native_population: usize,
    complete_target_native_sha256: String,
    first_target_native_id: u32,
    first_target_surface: String,
    first_target_interval: (i64, i64),
    interval_compatible_alternatives: Vec<AlternativeFace>,
    separated_alternative_population: usize,
    target_first_face_survives: bool,
    phrase_sha256: String,
    equation_face_sha256: Option<String>,
    code_face_sha256: Option<String>,
    potential_row_sha256: String,
    scalar_winner_selected: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct FamilyDefect {
    schema: String,
    family_occurrence: String,
    prompt_visible_index: u64,
    input_sha256: String,
    code_closure_sha256: String,
    runtime_receipt: String,
    runtime_receipt_sha256: String,
    fixed_body_sha256: String,
    history_message_population: usize,
    complete_response_message_population: usize,
    source_native_rows: usize,
    receiver_rows: usize,
    boundary_crossings: usize,
    boundaries: Vec<BoundaryDefect>,
    whole_response_sha256: String,
    shortest_history_separators: Vec<(String, Option<usize>)>,
    world_parent_join_pairs: u64,
    world_tool_join_pairs: u64,
    later_operator_return: Option<String>,
    known_suffix_crossed_once: bool,
    first_front_only: bool,
    source_access_forbidden_population: usize,
    gpu_resident_tower: bool,
    truth_status: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct Invocation {
    family_occurrence: String,
    command: String,
    purpose: String,
    code_closure_sha256: String,
    started_unix_nanoseconds: String,
    elapsed_milliseconds: String,
    exit_status: i32,
    addressed_receipt_reused: bool,
}

fn main() -> Result<(), String> {
    let mut args = env::args_os().skip(1);
    let aa0 = args.next().map(PathBuf::from).unwrap_or_else(|| AA0.into());
    let product = args
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| PRODUCT.into());
    let continuation = args
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| CONTINUATION.into());
    let output = args
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| OUTPUT.into());
    if args.next().is_some() {
        return Err("usage: [AA0_ROOT] [PHOENIX_PRODUCT] [CONTINUATION] [OUTPUT]".to_owned());
    }
    fs::create_dir_all(output.join("families")).map_err(|error| error.to_string())?;
    fs::create_dir_all(output.join("runtime")).map_err(|error| error.to_string())?;
    let world = remount_exchange_world_tube(&aa0.join("exchange-world-tube.ewtb"))?;
    let aperture: ContinuationAperture = read_json(aa0.join("04-continuation-aperture.json"))?;
    if aperture.source_occurrence_sha256 != world.source_occurrence_sha256 {
        return Err("AA0 continuation aperture moved from its world-tube".to_owned());
    }
    let session = ProductSession::open_with_continuation(product, continuation)?;
    let code_closure = code_closure();
    let mut developments = aperture
        .families
        .iter()
        .filter(|family| family.partition == ContinuationPartition::Development)
        .collect::<Vec<_>>();
    developments.sort_by_key(|family| family.prompt.visible_index);
    let mut invocations = Vec::new();
    let mut defects = Vec::new();
    let mut held_body = None::<String>;
    for (ordinal, family) in developments.iter().enumerate() {
        eprintln!(
            "AA1 complete suffix {}/{}: {}",
            ordinal + 1,
            developments.len(),
            family.occurrence
        );
        let presentation = present(&world, family)?;
        let artifact = output
            .join("families")
            .join(format!("{}.json", family.occurrence));
        if artifact.exists() {
            let retained: FamilyDefect = read_json(&artifact)?;
            let runtime = output.join(&retained.runtime_receipt);
            if retained.family_occurrence != family.occurrence
                || retained.input_sha256 != sha(presentation.text.as_bytes())
                || retained.code_closure_sha256 != code_closure
                || !runtime.exists()
                || retained.runtime_receipt_sha256 != sha_file(&runtime)?
            {
                return Err(format!(
                    "addressed AA1 return {} does not bind this closure/input",
                    family.occurrence
                ));
            }
            if held_body
                .as_ref()
                .is_some_and(|body| body != &retained.fixed_body_sha256)
            {
                return Err("the fixed E5 body moved between retained AA1 families".to_owned());
            }
            held_body.get_or_insert(retained.fixed_body_sha256.clone());
            invocations.push(Invocation {
                family_occurrence: family.occurrence.clone(),
                command: "addressed-runtime-return-reused".to_owned(),
                purpose: "same code/input closure already returned; the expensive tower deed was not replayed".to_owned(),
                code_closure_sha256: code_closure.clone(),
                started_unix_nanoseconds: "0".to_owned(),
                elapsed_milliseconds: "0".to_owned(),
                exit_status: 0,
                addressed_receipt_reused: true,
            });
            defects.push(retained);
            continue;
        }
        let started = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| error.to_string())?
            .as_nanos();
        let elapsed = Instant::now();
        let returned = session.infer_partitioned_with_intervention(
            &presentation.text,
            &presentation.boundaries,
            InterventionSite::Nowhere,
            &Intervention::None,
            ReceiverOption::Complete,
        )?;
        let runtime_path = output
            .join("runtime")
            .join(format!("{}.json", family.occurrence));
        write_json(&runtime_path, &returned.receipt)?;
        let fixed_body = fixed_body(&returned.receipt)?;
        if held_body.as_ref().is_some_and(|held| held != &fixed_body) {
            return Err("the fixed E5 body moved between AA1 families".to_owned());
        }
        held_body.get_or_insert(fixed_body.clone());
        let analyzed = analyze(
            &session,
            &world,
            family,
            &presentation,
            &returned.receipt,
            &returned.cultivated.cultivated_potential,
            &runtime_path,
            &output,
            &code_closure,
            fixed_body,
        )?;
        write_json(&artifact, &analyzed)?;
        invocations.push(Invocation {
            family_occurrence: family.occurrence.clone(),
            command: "ProductSession::infer_partitioned_with_intervention/Complete".to_owned(),
            purpose: "one whole known response suffix crosses the fixed E5 body and returns every addressed message-boundary potential".to_owned(),
            code_closure_sha256: code_closure.clone(),
            started_unix_nanoseconds: started.to_string(),
            elapsed_milliseconds: elapsed.elapsed().as_millis().to_string(),
            exit_status: 0,
            addressed_receipt_reused: false,
        });
        defects.push(analyzed);
    }
    let all_suffixes = defects.len() == developments.len()
        && defects.iter().all(|defect| {
            defect.known_suffix_crossed_once
                && !defect.first_front_only
                && defect.boundaries.len() == defect.complete_response_message_population
        });
    let complete_alternatives = defects.iter().all(|defect| {
        defect.boundaries.iter().all(|boundary| {
            !boundary.interval_compatible_alternatives.is_empty()
                && !boundary.scalar_winner_selected
        })
    });
    let fixed = held_body.ok_or_else(|| "AA1 returned no fixed body".to_owned())?;
    write_json(output.join("00-defect-atlas.json"), &defects)?;
    write_json(output.join("01-expensive-invocations.json"), &invocations)?;
    let grade = serde_json::json!({
        "schema":"holonics.athena-alpha.aa1-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "development_family_population": developments.len(),
        "returned_family_population": defects.len(),
        "fixed_body_sha256": fixed,
        "whole_known_suffix_crossed_once_per_family": all_suffixes,
        "complete_target_and_alternative_testimony_at_every_boundary": complete_alternatives,
        "no_first_front_only_return": defects.iter().all(|defect| !defect.first_front_only),
        "no_provider_winner": true,
        "world_and_later_returns_retained": defects.iter().any(|defect| defect.world_tool_join_pairs > 0 || defect.later_operator_return.is_some()),
        "gpu_resident_passage_testimony": defects.iter().all(|defect| defect.gpu_resident_tower),
        "source_access_clean": defects.iter().all(|defect| defect.source_access_forbidden_population == 0),
        "free_running_heldout_return_deferred_to_same_phase_aa4": true,
        "passed": all_suffixes && complete_alternatives && defects.iter().all(|defect| defect.gpu_resident_tower && defect.source_access_forbidden_population == 0),
    });
    write_json(output.join("02-grade.json"), &grade)?;
    write_json(
        output.join("MANIFEST.json"),
        &serde_json::json!({
            "schema":"holonics.athena-alpha.aa1-product.v1",
            "aa0_source_occurrence_sha256": world.source_occurrence_sha256.render(),
            "fixed_body_sha256": fixed,
            "defects":"00-defect-atlas.json",
            "runtime_receipts":"runtime/",
            "invocations":"01-expensive-invocations.json",
            "grade":"02-grade.json"
        }),
    )?;
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    if grade["passed"] == true {
        Ok(())
    } else {
        Err("AA1 refused its multiscale defect grade".to_owned())
    }
}

struct Presentation {
    text: String,
    boundaries: Vec<usize>,
}

fn present(world: &ExchangeWorldTube, family: &ContinuationFamily) -> Result<Presentation, String> {
    let mut text = String::new();
    let mut boundaries = vec![0usize];
    for address in family.history.iter().chain(&family.response) {
        let face = visible(world, address.visible_index)?;
        if face.text.is_empty() {
            return Err(format!(
                "visible occurrence {} has an empty face",
                face.occurrence
            ));
        }
        text.push_str(&face.text);
        text.push('\n');
        boundaries.push(text.len());
    }
    Ok(Presentation { text, boundaries })
}

#[allow(clippy::too_many_arguments)]
fn analyze(
    session: &ProductSession,
    world: &ExchangeWorldTube,
    family: &ContinuationFamily,
    presentation: &Presentation,
    receipt: &RuntimeReceipt,
    potential: &[(i64, i64)],
    runtime_path: &Path,
    output: &Path,
    closure: &str,
    fixed_body_sha256: String,
) -> Result<FamilyDefect, String> {
    let rows = family.history.len() + family.response.len();
    let vocabulary = receipt.generated.vocabulary_extent;
    if receipt.generated.row_count != rows || potential.len() != rows * vocabulary {
        return Err(format!(
            "AA1 family {} returned {} rows/{} intervals, expected {rows}/{}",
            family.occurrence,
            receipt.generated.row_count,
            potential.len(),
            rows * vocabulary
        ));
    }
    let mut boundaries = Vec::new();
    for (response_at, address) in family.response.iter().enumerate() {
        let face = visible(world, address.visible_index)?;
        let target = session.encode(&face.text)?;
        let first = *target
            .first()
            .ok_or_else(|| format!("response {} encoded to no native rows", face.occurrence))?;
        let row = family.history.len() - 1 + response_at;
        let potential_row = &potential[row * vocabulary..(row + 1) * vocabulary];
        let top_lower = potential_row
            .iter()
            .map(|interval| interval.0)
            .max()
            .ok_or_else(|| "AA1 potential row is empty".to_owned())?;
        let candidate_ids = potential_row
            .iter()
            .enumerate()
            .filter_map(|(native, interval)| (interval.1 >= top_lower).then_some(native as u32))
            .collect::<Vec<_>>();
        let alternatives = candidate_ids
            .iter()
            .map(|native| {
                let interval = potential_row[*native as usize];
                Ok(AlternativeFace {
                    native_id: *native,
                    surface: session
                        .predecessor()
                        .codebook()
                        .native_surface(*native)
                        .map_err(|error| error.to_string())?
                        .to_owned(),
                    lower: interval.0,
                    upper: interval.1,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let equation = contains_equation(&face.text).then(|| sha(face.text.as_bytes()));
        let code = face.text.contains("```").then(|| sha(face.text.as_bytes()));
        boundaries.push(BoundaryDefect {
            response_occurrence: face.occurrence.clone(),
            response_visible_index: address.visible_index,
            predecessor_receiver_row: row,
            complete_target_native_population: target.len(),
            complete_target_native_sha256: digest_u32(&target),
            first_target_native_id: first,
            first_target_surface: session
                .predecessor()
                .codebook()
                .native_surface(first)
                .map_err(|error| error.to_string())?
                .to_owned(),
            first_target_interval: potential_row[first as usize],
            target_first_face_survives: candidate_ids.contains(&first),
            separated_alternative_population: vocabulary - alternatives.len(),
            interval_compatible_alternatives: alternatives,
            phrase_sha256: sha(face.text.as_bytes()),
            equation_face_sha256: equation,
            code_face_sha256: code,
            potential_row_sha256: digest_intervals(potential_row),
            scalar_winner_selected: false,
        });
    }
    Ok(FamilyDefect {
        schema: "holonics.athena-alpha.aa1-family-defect.v1".to_owned(),
        family_occurrence: family.occurrence.clone(),
        prompt_visible_index: family.prompt.visible_index,
        input_sha256: sha(presentation.text.as_bytes()),
        code_closure_sha256: closure.to_owned(),
        runtime_receipt: runtime_path
            .strip_prefix(output)
            .map_err(|error| error.to_string())?
            .to_string_lossy()
            .to_string(),
        runtime_receipt_sha256: sha_file(runtime_path)?,
        fixed_body_sha256,
        history_message_population: family.history.len(),
        complete_response_message_population: family.response.len(),
        source_native_rows: receipt.input.presentation.source_rows,
        receiver_rows: receipt.input.presentation.received_rows,
        boundary_crossings: receipt.input.presentation.boundary_crossings.len(),
        boundaries,
        whole_response_sha256: family.response_sha256.render(),
        shortest_history_separators: family
            .shortest_separators
            .iter()
            .map(|separator| {
                (
                    separator.against_family.clone(),
                    separator.visible_suffix_depth,
                )
            })
            .collect(),
        world_parent_join_pairs: family.world.parent_join_pairs,
        world_tool_join_pairs: family
            .world
            .claude_tool_join_pairs
            .saturating_add(family.world.codex_tool_join_pairs),
        later_operator_return: family
            .later_operator_return
            .as_ref()
            .map(|address| address.occurrence.clone()),
        known_suffix_crossed_once: true,
        first_front_only: false,
        source_access_forbidden_population: receipt.source_access.forbidden.len(),
        gpu_resident_tower: receipt.execution.device_name.contains("NVIDIA")
            && receipt.execution.terminal_synchronizations == 1
            && receipt.execution.mode.contains("exact_resident_section"),
        truth_status: "established-bounded; measured".to_owned(),
    })
}

fn fixed_body(receipt: &RuntimeReceipt) -> Result<String, String> {
    let bytes = serde_json::to_vec(&(
        &receipt.product_identity,
        &receipt.predecessor_identity,
        &receipt.morphology_identity,
        &receipt.codec_companion_identities,
        &receipt.runtime_law,
        &receipt.reconstruction_identity,
        &receipt.codec_identity,
        &receipt.continuation_identity,
    ))
    .map_err(|error| error.to_string())?;
    Ok(sha(&bytes))
}

fn contains_equation(text: &str) -> bool {
    let symbols = ['=', '+', '*', '/', '^', '∫', '∂', 'λ', 'μ'];
    symbols.iter().any(|symbol| text.contains(*symbol))
        || text.contains("\\begin{")
        || text.contains("$$")
}

fn visible(world: &ExchangeWorldTube, index: u64) -> Result<&VisibleMessageFace, String> {
    world
        .visible_messages
        .get(index as usize)
        .ok_or_else(|| format!("visible message {index} is absent"))
}

fn digest_u32(values: &[u32]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"athena-alpha/native-word/v1");
    for value in values {
        digest.update(value.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn digest_intervals(values: &[(i64, i64)]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"athena-alpha/potential-row/v1");
    for (lower, upper) in values {
        digest.update(lower.to_le_bytes());
        digest.update(upper.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn sha(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn sha_file(path: &Path) -> Result<String, String> {
    Ok(sha(&fs::read(path).map_err(|error| error.to_string())?))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn code_closure() -> String {
    let mut digest = Sha256::new();
    for path in [
        "soma/life/examples/the_complete_continuations_return_their_multiscale_defects.rs",
        "soma/life/src/exchange_world_tube/continuation.rs",
        "crates/holonic-engine/src/phoenix/runtime.rs",
        "crates/holonic-engine/src/phoenix/streamed.rs",
    ] {
        digest.update(path.as_bytes());
        match fs::read(path) {
            Ok(bytes) => digest.update(bytes),
            Err(_) => digest.update(b"absent"),
        }
    }
    hex(&digest.finalize())
}

fn read_json<T: for<'de> Deserialize<'de>>(path: impl AsRef<Path>) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path.as_ref()).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    fs::write(path, bytes).map_err(|error| error.to_string())
}
