//! I1: recurrence retains a causal boundary and returns a complete emitted passage.
//!
//! Four fixed source-schedule controls expose one bounded response relation. The relation, not the
//! foreign interiors, enters a generator-native rest with complete source fibres. A source-absent
//! process then enacts the closure word on the resident card and returns every intermediate
//! boundary after one terminal synchronization. The first repeated boundary derives the extent;
//! no response capacity or host stop case is accepted.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

use holonic_engine::cuda_refine::CudaRefineExecutor;
use holonic_engine::native_ecology::recurrent::{
    BoundaryFace, RetainedContinuationPassage, RetainedContinuationRest, SourceBoundaryFront,
    SourceFrontApparatus,
};
use holonic_engine::phoenix::{
    runtime::ProductSession,
    streamed::{InterventionSite, ReceiverOption},
    tower::Intervention,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const DEFAULT_OUT: &str = "output/the_recurrent_boundary_returns_a_complete_passage";
const SOURCE_SCHEDULE_SCHEMA: &str = "holonics.i1.source-schedule-control.v1";
const REST_DIRECTORY_SCHEMA: &str = "holonics.i1.retained-rest-directory.v1";

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceScheduleControl {
    schema: String,
    truth_status: String,
    formation: String,
    contexts: Vec<String>,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RestDirectoryManifest {
    schema: String,
    rest: String,
    rest_sha256: String,
    rest_octets: u64,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DetachedApparatus {
    device: String,
    block_threads: u32,
    active_lanes: u32,
    launches: u64,
    synchronizations: u64,
    host_ingress_octets: u64,
    host_egress_octets: u64,
    resident_octets: u64,
    physical_wall_milliseconds: u128,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct DetachedReturn {
    schema: String,
    rest_sha256: String,
    native_trace: Vec<u32>,
    trace_stride: usize,
    emitted_native_ids: Vec<u32>,
    emitted_text_sha256: String,
    emitted_text_octets: u64,
    source_access_descriptors: Vec<String>,
    forbidden_source_access: Vec<String>,
    cpu_semantic_callbacks_between_steps: u64,
    apparatus: DetachedApparatus,
}

#[derive(Serialize)]
struct I1Grade {
    schema: &'static str,
    source_detached_predecessor_and_entering_occurrence: bool,
    retained_section_before_and_after_every_front: bool,
    exact_recurrent_lineage: bool,
    executable_boundary_and_complete_fibres: bool,
    complete_emitted_passage_inspected: bool,
    matched_source_schedule_control: bool,
    richer_history_reopens_static_compactification: bool,
    exact_work_and_separate_apparatus: bool,
    no_cpu_semantic_callback_or_authored_extent: bool,
    passed: bool,
}

#[derive(Serialize)]
struct I1ProductManifest {
    schema: &'static str,
    product: &'static str,
    source_schedule: &'static str,
    source_runtime_receipts: Vec<String>,
    retained_passage: &'static str,
    reconstruction_atlas: &'static str,
    native_rest: &'static str,
    detached_return: &'static str,
    emitted_passage: &'static str,
    grade: &'static str,
    code_closure_sha256: String,
    open_exterior: Vec<String>,
}

enum Args {
    Produce {
        schedule: PathBuf,
        product: PathBuf,
        continuation: PathBuf,
        output: PathBuf,
    },
    DetachedGrade {
        rest: PathBuf,
        output: PathBuf,
    },
}

fn main() -> Result<(), String> {
    match args()? {
        Args::Produce {
            schedule,
            product,
            continuation,
            output,
        } => produce(&schedule, &product, &continuation, &output),
        Args::DetachedGrade { rest, output } => detached_grade(&rest, &output),
    }
}

fn produce(
    schedule_path: &Path,
    product: &Path,
    continuation: &Path,
    output: &Path,
) -> Result<(), String> {
    if output.exists() {
        return Err(format!(
            "I1 output {} already exists; inspect the addressed receipt instead of replaying the deed",
            output.display()
        ));
    }
    let schedule_bytes = fs::read(schedule_path).map_err(|error| error.to_string())?;
    let schedule: SourceScheduleControl =
        serde_json::from_slice(&schedule_bytes).map_err(|error| error.to_string())?;
    if schedule.schema != SOURCE_SCHEDULE_SCHEMA
        || schedule.truth_status != "established-bounded"
        || schedule.contexts.len() < 4
        || schedule.contexts.iter().any(String::is_empty)
        || schedule.contexts.iter().collect::<BTreeSet<_>>().len() != schedule.contexts.len()
    {
        return Err("the I1 source schedule control is incomplete".to_owned());
    }

    let session = ProductSession::open_with_continuation(product, continuation)?;
    let encoded_contexts = schedule
        .contexts
        .iter()
        .map(|context| session.encode(context))
        .collect::<Result<Vec<_>, _>>()?;
    let mut returns = Vec::with_capacity(schedule.contexts.len());
    let source_control_begun = Instant::now();
    for context in &schedule.contexts {
        returns.push(session.infer_with_intervention(
            context,
            InterventionSite::Nowhere,
            &Intervention::None,
            ReceiverOption::Complete,
        )?);
    }
    let source_control_wall_milliseconds = source_control_begun.elapsed().as_millis();

    let mut fronts = Vec::with_capacity(returns.len());
    let mut runtime_receipts = Vec::with_capacity(returns.len());
    for (at, returned) in returns.iter().enumerate() {
        let receipt = &returned.receipt;
        let candidate = receipt
            .generated
            .plural
            .as_slice()
            .first()
            .filter(|_| receipt.generated.plural.len() == 1)
            .ok_or_else(|| format!("source control front {at} is not a unique exact face"))?;
        let before = encoded_contexts[at].clone();
        if receipt.input.native_ids != before {
            return Err(format!(
                "source control front {at} moved its fixed codec crossing"
            ));
        }
        let mut after = before.clone();
        after.push(candidate.native_id);
        let after_text = session.decode_native_ids(&after)?;
        if let Some(next) = encoded_contexts.get(at + 1) {
            if next != &after || session.encode(&after_text)? != after {
                return Err(format!(
                    "fixed source context {} is not the exact exterior decoding of front {at}",
                    at + 1
                ));
            }
        }
        let before_occurrence = section_occurrence(&schedule.contexts[at], &before);
        let after_occurrence = section_occurrence(&after_text, &after);
        let receipt_bytes = serde_json::to_vec(receipt).map_err(|error| error.to_string())?;
        let terminal_potential = terminal(
            &returned.cultivated.cultivated_potential,
            receipt.generated.vocabulary_extent,
        )?;
        let terminal_hidden = terminal(
            &returned.cultivated.base.final_normed,
            receipt.runtime_law.hidden_extent as usize,
        )?;
        let apparatus = &receipt.apparatus_census;
        fronts.push(SourceBoundaryFront {
            before_occurrence,
            after_occurrence,
            before_native_ids: before,
            after_native_ids: after,
            emitted: BoundaryFace {
                native_id: candidate.native_id,
                source_surface: candidate.surface.clone(),
                lower: candidate.lower,
                upper: candidate.upper,
            },
            plural_population: receipt.generated.plural.len(),
            complete_terminal_potential_sha256: digest_intervals(terminal_potential),
            terminal_hidden_sha256: digest_intervals(terminal_hidden),
            runtime_receipt_sha256: sha256(&receipt_bytes),
            exact_work: receipt.total_work.clone(),
            apparatus: SourceFrontApparatus {
                total_deed_launches: apparatus.total_deed_launches,
                terminal_synchronizations: apparatus.terminal_synchronizations,
                streamed_staged_octets: apparatus.streamed.staged_octets,
                asynchronous_copy_octets: apparatus.streamed.asynchronous_copy_octets,
                resident_octets_peak: apparatus
                    .resident_after
                    .resident_octets_peak
                    .max(apparatus.resident_after_tower.resident_octets_peak),
                physical_wall_seconds: receipt.execution.wall_seconds.clone(),
            },
        });
        runtime_receipts.push(receipt_bytes);
    }

    let emitted_ids = first_returned_face_word(&fronts)?;
    let emitted_text = session.decode_native_ids(&emitted_ids)?;
    let first_receipt = returns.first().ok_or("source control returned no fronts")?;
    let continuation_identity = first_receipt
        .receipt
        .continuation_identity
        .as_ref()
        .map(|identity| identity.complete_sha256.clone())
        .ok_or("I1 predecessor carries no A3 continuation")?;
    if returns.iter().any(|returned| {
        returned
            .receipt
            .continuation_identity
            .as_ref()
            .map(|identity| identity.complete_sha256.as_str())
            != Some(continuation_identity.as_str())
    }) {
        return Err("the A3 continuation identity moved across source controls".to_owned());
    }
    let predecessor_identity = first_receipt.receipt.product_identity.sha256.clone();
    let entering_occurrence = fronts[0].before_occurrence.clone();
    let passage = RetainedContinuationPassage::found(
        predecessor_identity,
        continuation_identity,
        entering_occurrence,
        fronts,
        emitted_text,
        first_receipt.receipt.codec_identity.clone(),
    )
    .map_err(|error| error.to_string())?;
    let passage_bytes = passage
        .canonical_bytes()
        .map_err(|error| error.to_string())?;
    let rest_bytes = passage
        .rest
        .canonical_bytes()
        .map_err(|error| error.to_string())?;

    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    write(output.join("00-source-schedule.json"), &schedule_bytes)?;
    for (at, bytes) in runtime_receipts.iter().enumerate() {
        write(
            output.join(format!("01-source-runtime-{at:02}.json")),
            &pretty_json(bytes)?,
        )?;
    }
    write(
        output.join("02-retained-passage.json"),
        &pretty_json(&passage_bytes)?,
    )?;
    write(
        output.join("03-reconstruction-atlas.json"),
        &serde_json::to_vec_pretty(&serde_json::json!({
            "schema": "holonics.i1.reconstruction-atlas.v1",
            "sections": passage.sections,
            "fibres": passage.fibres,
            "reopenings": passage.reopenings,
            "complete_source_work": passage.complete_source_work,
            "source_control_wall_milliseconds": source_control_wall_milliseconds,
            "truth_status": "established-bounded"
        }))
        .map_err(|error| error.to_string())?,
    )?;
    let rest_directory = output.join("native-rest");
    fs::create_dir(&rest_directory).map_err(|error| error.to_string())?;
    write(
        rest_directory.join("retained-continuation.rest"),
        &rest_bytes,
    )?;
    let rest_manifest = RestDirectoryManifest {
        schema: REST_DIRECTORY_SCHEMA.to_owned(),
        rest: "retained-continuation.rest".to_owned(),
        rest_sha256: sha256(&rest_bytes),
        rest_octets: rest_bytes.len() as u64,
    };
    write(
        rest_directory.join("manifest.json"),
        &serde_json::to_vec_pretty(&rest_manifest).map_err(|error| error.to_string())?,
    )?;

    let detached_directory = output.join("detached-return");
    fs::create_dir(&detached_directory).map_err(|error| error.to_string())?;
    run_detached_grade(
        &env::current_exe().map_err(|error| error.to_string())?,
        &rest_directory,
        &detached_directory,
    )?;
    let detached_bytes =
        fs::read(detached_directory.join("return.json")).map_err(|error| error.to_string())?;
    let detached: DetachedReturn =
        serde_json::from_slice(&detached_bytes).map_err(|error| error.to_string())?;
    let emitted_bytes = fs::read(detached_directory.join("emitted-passage.txt"))
        .map_err(|error| error.to_string())?;
    if detached.rest_sha256 != rest_manifest.rest_sha256
        || detached.native_trace
            != passage
                .rest
                .closure
                .expected_trace
                .iter()
                .map(|state| state.0 as u32)
                .collect::<Vec<_>>()
        || detached.emitted_native_ids != passage.rest.emitted_native_ids
        || detached.emitted_text_sha256 != sha256(&emitted_bytes)
        || emitted_bytes != passage.rest.emitted_text.as_bytes()
        || !detached.forbidden_source_access.is_empty()
        || detached.cpu_semantic_callbacks_between_steps != 0
    {
        return Err("the detached I1 return disagrees with its retained rest".to_owned());
    }

    let grade = grade(&passage, &detached, &emitted_bytes);
    if !grade.passed {
        return Err("I1 refused its nine-part grade".to_owned());
    }
    write(
        output.join("04-grade.json"),
        &serde_json::to_vec_pretty(&grade).map_err(|error| error.to_string())?,
    )?;
    write(
        output.join("INSPECTION.md"),
        format!(
            "# I1 retained recurrent boundary\n\n- grade: PASS\n- source fronts: {}\n- retained sections: {}\n- native boundary states: {}\n- closure word: {:?}\n- returned trace: {:?}\n- emitted passage: {:?}\n- reconstruction fibres: {}\n- richer-receiver reopenings: {}\n- source-control wall: {} ms\n- detached card launches/synchronizations: {}/{}\n- source access in detached return: {}\n",
            passage.source_fronts.len(),
            passage.sections.len(),
            passage.rest.native.native_population.len(),
            passage.rest.closure.ordered_word,
            detached.native_trace,
            String::from_utf8_lossy(&emitted_bytes),
            passage.fibres.len(),
            passage.reopenings.len(),
            source_control_wall_milliseconds,
            detached.apparatus.launches,
            detached.apparatus.synchronizations,
            detached.forbidden_source_access.len()
        )
        .as_bytes(),
    )?;
    let runtime_paths = (0..runtime_receipts.len())
        .map(|at| format!("01-source-runtime-{at:02}.json"))
        .collect();
    let manifest = I1ProductManifest {
        schema: "holonics.i1.product-manifest.v1",
        product: "Athena-Gemma retained recurrent boundary",
        source_schedule: "00-source-schedule.json",
        source_runtime_receipts: runtime_paths,
        retained_passage: "02-retained-passage.json",
        reconstruction_atlas: "03-reconstruction-atlas.json",
        native_rest: "native-rest/",
        detached_return: "detached-return/",
        emitted_passage: "detached-return/emitted-passage.txt",
        grade: "04-grade.json",
        code_closure_sha256: code_closure(),
        open_exterior: passage.rest.open_exterior.clone(),
    };
    write(
        output.join("MANIFEST.json"),
        &serde_json::to_vec_pretty(&manifest).map_err(|error| error.to_string())?,
    )?;
    println!("I1 returned: {}", output.display());
    println!(
        "emitted passage: {:?}",
        String::from_utf8_lossy(&emitted_bytes)
    );
    Ok(())
}

fn detached_grade(rest_directory: &Path, output: &Path) -> Result<(), String> {
    let manifest_bytes =
        fs::read(rest_directory.join("manifest.json")).map_err(|error| error.to_string())?;
    let manifest: RestDirectoryManifest =
        serde_json::from_slice(&manifest_bytes).map_err(|error| error.to_string())?;
    if manifest.schema != REST_DIRECTORY_SCHEMA || manifest.rest != "retained-continuation.rest" {
        return Err("the detached I1 directory manifest is invalid".to_owned());
    }
    let rest_bytes =
        fs::read(rest_directory.join(&manifest.rest)).map_err(|error| error.to_string())?;
    if sha256(&rest_bytes) != manifest.rest_sha256
        || rest_bytes.len() as u64 != manifest.rest_octets
    {
        return Err("the detached I1 rest identity moved".to_owned());
    }
    let rest = RetainedContinuationRest::read(&rest_bytes).map_err(|error| error.to_string())?;
    let states = rest.native.native_population.len();
    let generators = rest.native.generators.len();
    let mut table = Vec::with_capacity(states * generators);
    for generator in &rest.native.generators {
        for state in &rest.native.native_population {
            let target = generator
                .transport
                .iter()
                .find(|edge| edge.from == *state)
                .ok_or_else(|| format!("native generator omits state {:?}", state))?;
            table.push(u32::try_from(target.to.0).map_err(|_| "native state exceeds u32")?);
        }
    }
    let generator_row = rest
        .native
        .generators
        .iter()
        .enumerate()
        .map(|(at, generator)| (generator.generator, at as u32))
        .collect::<BTreeMap<_, _>>();
    let word = rest
        .closure
        .ordered_word
        .iter()
        .map(|generator| {
            generator_row
                .get(generator)
                .copied()
                .ok_or("unknown closure generator")
        })
        .collect::<Result<Vec<_>, _>>()?;
    let mut card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let begun = Instant::now();
    let returned = card
        .conduct_native_trace_on_device(
            states,
            generators,
            &table,
            &word,
            &[u32::try_from(rest.closure.entering_state.0)
                .map_err(|_| "entering state exceeds u32")?],
        )
        .map_err(|error| error.to_string())?;
    let wall = begun.elapsed().as_millis();
    let expected = rest
        .closure
        .expected_trace
        .iter()
        .map(|state| u32::try_from(state.0).map_err(|_| "trace state exceeds u32"))
        .collect::<Result<Vec<_>, _>>()?;
    if returned.trace_stride != expected.len() || returned.native_trace != expected {
        return Err("the card returned a different recurrent boundary trace".to_owned());
    }
    let descriptors = open_descriptors();
    let forbidden = descriptors
        .iter()
        .filter(|path| {
            path.contains("/home/b/Workspaces/holonics")
                || path.contains("base.w1.rest")
                || path.contains("cultivated.rest")
                || path.contains("morphology.safetensors")
                || path.contains("tokenizer.json")
        })
        .cloned()
        .collect::<Vec<_>>();
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    write(
        output.join("emitted-passage.txt"),
        rest.emitted_text.as_bytes(),
    )?;
    let receipt = DetachedReturn {
        schema: "holonics.i1.detached-return.v1".to_owned(),
        rest_sha256: manifest.rest_sha256,
        native_trace: returned.native_trace,
        trace_stride: returned.trace_stride,
        emitted_native_ids: rest.emitted_native_ids,
        emitted_text_sha256: sha256(rest.emitted_text.as_bytes()),
        emitted_text_octets: rest.emitted_text.len() as u64,
        source_access_descriptors: descriptors,
        forbidden_source_access: forbidden,
        cpu_semantic_callbacks_between_steps: 0,
        apparatus: DetachedApparatus {
            device: card.device_name().to_owned(),
            block_threads: returned.block_threads,
            active_lanes: returned.active_lanes,
            launches: returned.launches,
            synchronizations: returned.synchronizations,
            host_ingress_octets: returned.host_ingress_octets,
            host_egress_octets: returned.host_egress_octets,
            resident_octets: returned.resident_octets,
            physical_wall_milliseconds: wall,
        },
    };
    write(
        output.join("return.json"),
        &serde_json::to_vec_pretty(&receipt).map_err(|error| error.to_string())?,
    )
}

fn grade(
    passage: &RetainedContinuationPassage,
    detached: &DetachedReturn,
    emitted: &[u8],
) -> I1Grade {
    let source_detached_predecessor_and_entering_occurrence =
        !passage.predecessor_identity.is_empty()
            && !passage.entering_occurrence.is_empty()
            && detached.forbidden_source_access.is_empty();
    let retained_section_before_and_after_every_front = passage.sections.len()
        == passage.source_fronts.len() + 1
        && passage
            .sections
            .windows(2)
            .all(|pair| pair[1].predecessor.as_deref() == Some(pair[0].occurrence.as_str()));
    let exact_recurrent_lineage = passage.source_fronts.windows(2).all(|pair| {
        pair[0].after_occurrence == pair[1].before_occurrence
            && pair[0].after_native_ids == pair[1].before_native_ids
    });
    let executable_boundary_and_complete_fibres = passage.rest.native.validate().is_ok()
        && passage
            .fibres
            .iter()
            .flat_map(|fibre| &fibre.source_sections)
            .count()
            == passage.sections.len()
        && detached.native_trace.len() == passage.rest.closure.expected_trace.len();
    let complete_emitted_passage_inspected = !emitted.is_empty()
        && emitted == passage.rest.emitted_text.as_bytes()
        && sha256(emitted) == detached.emitted_text_sha256;
    let matched_source_schedule_control = passage.source_schedule_is_a_control
        && passage.rest.emitted_native_ids
            == passage
                .source_fronts
                .iter()
                .take(passage.rest.closure.returned_at_section)
                .map(|front| front.emitted.native_id)
                .collect::<Vec<_>>();
    let richer_history_reopens_static_compactification = !passage.reopenings.is_empty()
        && passage.reopenings.iter().all(|reopening| {
            reopening.first_reading_sha256 != reopening.later_reading_sha256
                && !reopening.shortest_separating_history.is_empty()
        });
    let exact_work_and_separate_apparatus = passage.complete_source_work.dependency_span
        > 0u32.into()
        && detached.apparatus.launches == 1
        && detached.apparatus.synchronizations == 1
        && detached.apparatus.resident_octets > 0;
    let no_cpu_semantic_callback_or_authored_extent = detached.cpu_semantic_callbacks_between_steps
        == 0
        && passage.cpu_semantic_callbacks_in_native_deed == 0
        && passage.rest.closure.derived_from_first_repeated_boundary
        && passage.rest.closure.crossed_nonterminal_boundaries >= 1;
    let passed = source_detached_predecessor_and_entering_occurrence
        && retained_section_before_and_after_every_front
        && exact_recurrent_lineage
        && executable_boundary_and_complete_fibres
        && complete_emitted_passage_inspected
        && matched_source_schedule_control
        && richer_history_reopens_static_compactification
        && exact_work_and_separate_apparatus
        && no_cpu_semantic_callback_or_authored_extent;
    I1Grade {
        schema: "holonics.i1.grade.v1",
        source_detached_predecessor_and_entering_occurrence,
        retained_section_before_and_after_every_front,
        exact_recurrent_lineage,
        executable_boundary_and_complete_fibres,
        complete_emitted_passage_inspected,
        matched_source_schedule_control,
        richer_history_reopens_static_compactification,
        exact_work_and_separate_apparatus,
        no_cpu_semantic_callback_or_authored_extent,
        passed,
    }
}

fn first_returned_face_word(fronts: &[SourceBoundaryFront]) -> Result<Vec<u32>, String> {
    let mut first = BTreeMap::new();
    for (at, front) in fronts.iter().enumerate() {
        if first.insert(front.emitted.native_id, at).is_some() {
            if at < 2 {
                return Err("the source control did not cross a nonterminal boundary".to_owned());
            }
            return Ok(fronts[..=at]
                .iter()
                .map(|front| front.emitted.native_id)
                .collect());
        }
    }
    Err("the fixed source control returned no recurrent boundary".to_owned())
}

fn section_occurrence(text: &str, native_ids: &[u32]) -> String {
    let mut digest = Sha256::new();
    digest.update(b"holonics/i1/retained-section/v1");
    digest.update(text.as_bytes());
    for id in native_ids {
        digest.update(id.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn terminal<T>(values: &[T], width: usize) -> Result<&[T], String> {
    if width == 0 || values.len() < width || values.len() % width != 0 {
        return Err("the source return has no complete terminal section".to_owned());
    }
    Ok(&values[values.len() - width..])
}

fn digest_intervals(values: &[(i64, i64)]) -> String {
    let mut digest = Sha256::new();
    for (lower, upper) in values {
        digest.update(lower.to_le_bytes());
        digest.update(upper.to_le_bytes());
    }
    hex(&digest.finalize())
}

fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn pretty_json(bytes: &[u8]) -> Result<Vec<u8>, String> {
    let value: serde_json::Value =
        serde_json::from_slice(bytes).map_err(|error| error.to_string())?;
    serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())
}

fn code_closure() -> String {
    let members: &[&[u8]] = &[
        include_bytes!("the_recurrent_boundary_returns_a_complete_passage.rs"),
        include_bytes!("../../../crates/holonic-engine/src/native_ecology/recurrent.rs"),
        include_bytes!("../../../crates/holonic-engine/src/phoenix/runtime.rs"),
        include_bytes!("../../../crates/holonic-engine/src/cuda_refine.rs"),
        include_bytes!("../../../crates/holonic-engine/kernels/refine_shell.cu"),
    ];
    let mut digest = Sha256::new();
    for member in members {
        digest.update((member.len() as u64).to_le_bytes());
        digest.update(member);
    }
    hex(&digest.finalize())
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn write(path: impl AsRef<Path>, bytes: &[u8]) -> Result<(), String> {
    let path = path.as_ref();
    let staged = path.with_extension("i1-staged");
    fs::write(&staged, bytes).map_err(|error| error.to_string())?;
    fs::rename(staged, path).map_err(|error| error.to_string())
}

fn open_descriptors() -> Vec<String> {
    let mut descriptors = Vec::new();
    if let Ok(entries) = fs::read_dir("/proc/self/fd") {
        for entry in entries.flatten() {
            if let Ok(target) = fs::read_link(entry.path()) {
                descriptors.push(target.to_string_lossy().into_owned());
            }
        }
    }
    descriptors.sort();
    descriptors.dedup();
    descriptors
}

fn run_detached_grade(executable: &Path, rest: &Path, output: &Path) -> Result<(), String> {
    let executable = executable
        .canonicalize()
        .map_err(|error| format!("resolve I1 executable: {error}"))?;
    let rest = rest
        .canonicalize()
        .map_err(|error| format!("resolve I1 rest: {error}"))?;
    let output = output
        .canonicalize()
        .map_err(|error| format!("resolve I1 return: {error}"))?;
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
        .arg("/athena-i1")
        .arg("--ro-bind")
        .arg(rest)
        .arg("/rest")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/tmp",
            "/athena-i1",
            "--detached-grade",
            "/rest",
            "/return",
        ]);
    let status = command
        .status()
        .map_err(|error| format!("enter detached I1 namespace: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("detached I1 grade returned {status}"))
    }
}

fn args() -> Result<Args, String> {
    let mut values = env::args().skip(1);
    match values.next().as_deref() {
        Some("--produce") => {
            let schedule = required_path(&mut values, "SOURCE_SCHEDULE")?;
            let product = required_path(&mut values, "PRODUCT")?;
            let continuation = required_path(&mut values, "CONTINUATION")?;
            let output = values
                .next()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from(DEFAULT_OUT));
            no_trailing(&mut values, "--produce")?;
            Ok(Args::Produce {
                schedule,
                product,
                continuation,
                output,
            })
        }
        Some("--detached-grade") => {
            let rest = required_path(&mut values, "REST")?;
            let output = required_path(&mut values, "OUTPUT")?;
            no_trailing(&mut values, "--detached-grade")?;
            Ok(Args::DetachedGrade { rest, output })
        }
        _ => Err("usage: --produce SOURCE_SCHEDULE PRODUCT CONTINUATION [OUTPUT] | --detached-grade REST OUTPUT".to_owned()),
    }
}

fn required_path(values: &mut impl Iterator<Item = String>, name: &str) -> Result<PathBuf, String> {
    let path = values
        .next()
        .map(PathBuf::from)
        .ok_or_else(|| format!("missing {name}"))?;
    if !path.exists() {
        return Err(format!("required {name} {} is absent", path.display()));
    }
    Ok(path)
}

fn no_trailing(values: &mut impl Iterator<Item = String>, mode: &str) -> Result<(), String> {
    if values.next().is_some() {
        Err(format!("{mode} carries trailing arguments"))
    } else {
        Ok(())
    }
}
