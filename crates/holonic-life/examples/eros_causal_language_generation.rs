//! EROS CAUSAL LANGUAGE GENERATION — generation through the production Swing.
//!
//! Recovered from the frozen laboratory at
//! `ba8716b5:src/crates/holonic-life/examples/eros_causal_language_generation.rs` (478 lines). Deleted at
//! `a07ff376`; never imported by `06518c3` ("Transition to Rust"). `life::causal_language`
//! (`CausalLanguageEcology`, its route rest image and its global suffix ecology) had **no caller**
//! in this tree — only its free function `lexical_tokens` was used, by two unrelated drivers.
//!
//! This is **not** a duplicate of `eros_morphological_language_generation`. That driver is the
//! laboratory's own successor to this one and it conducts through `MorphologicalLanguageEcology`.
//! This one conducts through `CausalLanguageEcology`, whose carriers are a route rest image plus
//! an `ExactSuffixEcology` — a different organ, and the only mouth either has.
//!
//! ## API divergences from the laboratory source
//!
//! 1. **`CausalLanguageGenerationSpec::output_aperture` no longer exists.** The laboratory passed
//!    `output_aperture: 6` for prompts and `2` for the control. The live spec is
//!    `{ maximum_generated_tokens, stop_at_sentence_boundary }` only.
//! 2. **`CausalLanguageGeneration::paths_withheld_by_output_aperture` no longer exists**, for the
//!    same reason. Every report field derived from it is dropped rather than reconstructed from a
//!    different quantity.
//!
//! ## Aperture — declared
//!
//! The laboratory's source declared `maximum_generated_tokens: 256` per prompt. Measured at
//! `a91a84f`: generation branches super-exponentially in this parameter — 1 token 57 ms, 2 tokens
//! 403 ms, 4 tokens 55,098 ms, 8 tokens no return in 200,000 ms. The source this driver reads
//! carries a **declared aperture of 2** and says so in its own `generation_aperture_note`. A run
//! at 256 does not return; the bound is a receiver parameter and never the law.
//!
//! Run:
//! ```text
//!   cargo run -p life --example eros_causal_language_generation -- \
//!     crates/holonic-life/driver-sources/eros-causal-language-generation-01/SOURCE.json REPORT.json
//! ```

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    time::Instant,
};

use body::num::Cog;
use life::causal_language::{
    lexical_tokens, CausalGeneratedText, CausalLanguageEcology, CausalLanguageGeneration,
    CausalLanguageGenerationSpec, CausalLanguagePassage, CausalLanguageRouteRestImage,
};
use life::suffix_ecology::ExactSuffixEcology;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;

const REPORT_SCHEMA: &str = "soma.causal-language.report.v4-ported";

/// APERTURE — the control prompt's generation extent. The laboratory used 16 tokens with an
/// output aperture of 2; with the output aperture gone, 16 does not return, so the control is run
/// at the same declared extent as the prompts. Its job is unchanged: a prompt built from words the
/// corpus does not carry must emit nothing.
const CONTROL_APERTURE: usize = 2;

#[derive(Deserialize)]
struct Source {
    schema: String,
    question: String,
    files: Vec<SourceFile>,
    passages: Vec<SourcePassage>,
    prompts: Vec<SourcePrompt>,
    control_prompt: String,
    comparison: serde_json::Value,
}

#[derive(Deserialize)]
struct SourceFile {
    path: String,
    receiver: u64,
    sha256: String,
    bytes: usize,
    passages: usize,
}

#[derive(Deserialize)]
struct SourcePassage {
    identity: String,
    receiver: u64,
    source_path: String,
    source_sha256: String,
    text: String,
}

#[derive(Deserialize)]
struct SourcePrompt {
    identity: String,
    text: String,
    maximum_generated_tokens: usize,
}

#[derive(Serialize)]
struct Report {
    schema: &'static str,
    status: &'static str,
    source_schema: String,
    question: String,
    source_sha256: String,
    source_files: usize,
    source_bytes: usize,
    source_receivers: usize,
    worker_threads: usize,
    passage_population: usize,
    lexical_occurrence_population: usize,
    route_occurrence_population: usize,
    route_relation_population: usize,
    route_receptor_population: usize,
    conditioning_event_population: usize,
    conditioning_wall_millis: u128,
    route_rest_bytes: usize,
    route_rest_sha256: String,
    route_rest_remount_equal: bool,
    global_suffix_states: usize,
    global_suffix_transitions: usize,
    global_suffix_rest_bytes: usize,
    global_suffix_rest_sha256: String,
    global_suffix_remount_equal: bool,
    prompt_population: usize,
    generation_wall_millis: u128,
    all_prompts_new_outer_contexts: bool,
    emitted_output_population: usize,
    nonempty_output_population: usize,
    generated_tokens: usize,
    distinct_recruited_receivers: usize,
    control_emitted_no_text: bool,
    comparison: serde_json::Value,
    prompts: Vec<PromptRead>,
}

#[derive(Serialize)]
struct PromptRead {
    identity: String,
    prompt: String,
    prompt_was_inherited_contiguously: bool,
    recruited_source_population: usize,
    recruited_receiver_population: usize,
    recruited_sources: Vec<RecruitedRead>,
    outputs: Vec<OutputRead>,
}

#[derive(Serialize)]
struct RecruitedRead {
    identity: String,
    receiver: u64,
    supporting_features: Vec<String>,
}

#[derive(Serialize)]
struct OutputRead {
    text: String,
    generated_tokens: usize,
    stopped_at_sentence_boundary: bool,
    output_was_inherited_contiguously: bool,
    prompt_plus_output_was_inherited_contiguously: bool,
    returned_rest_bytes: usize,
    returned_rest_sha256: String,
    token_receipts: Vec<TokenRead>,
}

#[derive(Serialize)]
struct TokenRead {
    token: String,
    matched_horizon: u32,
    sources: Vec<String>,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros causal language generation: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut arguments = std::env::args_os().skip(1);
    let source_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    let report_path = PathBuf::from(arguments.next().ok_or_else(usage)?);
    if arguments.next().is_some() {
        return Err(usage());
    }
    let source_bytes = std::fs::read(&source_path)
        .map_err(|error| format!("{} reads: {error}", source_path.display()))?;
    let source: Source = serde_json::from_slice(&source_bytes)
        .map_err(|error| format!("{} decodes: {error}", source_path.display()))?;
    validate_source(&source)?;
    let source_sha256 = sha256(&source_bytes);
    let workers = std::thread::available_parallelism()
        .map(|workers| workers.get())
        .unwrap_or(1)
        .min(4);
    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current is dark".to_owned())?;
    let passages = source
        .passages
        .iter()
        .map(|passage| {
            CausalLanguagePassage::new(
                passage.identity.clone(),
                passage.receiver,
                passage.text.clone(),
            )
        })
        .collect::<Vec<_>>();

    eprintln!(
        "eros causal language generation: conditioning {} passages across {} receiver charts",
        passages.len(),
        source
            .files
            .iter()
            .map(|file| file.receiver)
            .collect::<BTreeSet<_>>()
            .len()
    );
    let conditioning_started = Instant::now();
    let ecology = CausalLanguageEcology::condition(&passages, action, workers).map_err(debug)?;
    let conditioning_wall_millis = conditioning_started.elapsed().as_millis();
    let route_rest_bytes = ecology
        .route_rest_image()
        .encode_native_bytes()
        .map_err(debug)?;
    let global_suffix_bytes = ecology
        .global_suffix()
        .encode_native_bytes()
        .map_err(debug)?;
    let route_rest_remount_equal =
        CausalLanguageRouteRestImage::from_native_bytes(&route_rest_bytes).map_err(debug)?
            == *ecology.route_rest_image();
    let global_suffix_remount_equal = ExactSuffixEcology::from_native_bytes(&global_suffix_bytes)
        .map_err(debug)?
        == *ecology.global_suffix();
    if !route_rest_remount_equal || !global_suffix_remount_equal {
        return Err("conditioned language rest did not remount exactly".to_owned());
    }

    let corpus_tokens = source
        .passages
        .iter()
        .map(|passage| lexical_tokens(&passage.text))
        .collect::<Vec<_>>();
    let generation_started = Instant::now();
    let mut prompt_reads = Vec::new();
    let mut recruited_receivers = BTreeSet::new();
    for prompt in source.prompts {
        let prompt_was_inherited_contiguously =
            corpus_contains(&corpus_tokens, &lexical_tokens(&prompt.text));
        let generated = ecology
            .generate(
                &prompt.text,
                CausalLanguageGenerationSpec {
                    maximum_generated_tokens: prompt.maximum_generated_tokens,
                    stop_at_sentence_boundary: true,
                    ..CausalLanguageGenerationSpec::default()
                },
                action,
                workers,
            )
            .map_err(debug)?;
        eprintln!(
            "eros causal language generation: {} recruited {} source fibers and emitted {} text branches",
            prompt.identity,
            generated.initial_hexis.len(),
            generated.outputs.len()
        );
        recruited_receivers.extend(generated.initial_hexis.iter().map(|source| source.receiver));
        prompt_reads.push(prompt_read(
            prompt.identity,
            generated,
            prompt_was_inherited_contiguously,
            &corpus_tokens,
        )?);
    }
    let control = ecology
        .generate(
            &source.control_prompt,
            CausalLanguageGenerationSpec {
                maximum_generated_tokens: CONTROL_APERTURE,
                stop_at_sentence_boundary: true,
                ..CausalLanguageGenerationSpec::default()
            },
            action,
            workers,
        )
        .map_err(debug)?;
    let generation_wall_millis = generation_started.elapsed().as_millis();

    let emitted_output_population = prompt_reads.iter().map(|prompt| prompt.outputs.len()).sum();
    let nonempty_output_population = prompt_reads
        .iter()
        .flat_map(|prompt| &prompt.outputs)
        .filter(|output| !output.text.is_empty())
        .count();
    let generated_tokens = prompt_reads
        .iter()
        .flat_map(|prompt| &prompt.outputs)
        .map(|output| output.generated_tokens)
        .sum();
    let report = Report {
        schema: REPORT_SCHEMA,
        status: "heterogeneous-swing-generated-text",
        source_schema: source.schema,
        question: source.question,
        source_sha256,
        source_files: source.files.len(),
        source_bytes: source.files.iter().map(|file| file.bytes).sum(),
        source_receivers: source
            .files
            .iter()
            .map(|file| file.receiver)
            .collect::<BTreeSet<_>>()
            .len(),
        worker_threads: workers,
        passage_population: ecology.passage_population(),
        lexical_occurrence_population: ecology.lexical_occurrence_population(),
        route_occurrence_population: ecology.route_occurrence_population(),
        route_relation_population: ecology.route_relation_population(),
        route_receptor_population: ecology.route_receptor_population(),
        conditioning_event_population: ecology.conditioning_event_population(),
        conditioning_wall_millis,
        route_rest_bytes: route_rest_bytes.len(),
        route_rest_sha256: sha256(&route_rest_bytes),
        route_rest_remount_equal,
        global_suffix_states: ecology.global_suffix().state_count(),
        global_suffix_transitions: ecology.global_suffix().material_transition_count(),
        global_suffix_rest_bytes: global_suffix_bytes.len(),
        global_suffix_rest_sha256: sha256(&global_suffix_bytes),
        global_suffix_remount_equal,
        prompt_population: prompt_reads.len(),
        generation_wall_millis,
        all_prompts_new_outer_contexts: prompt_reads
            .iter()
            .all(|prompt| !prompt.prompt_was_inherited_contiguously),
        emitted_output_population,
        nonempty_output_population,
        generated_tokens,
        distinct_recruited_receivers: recruited_receivers.len(),
        control_emitted_no_text: control.outputs.iter().all(|output| output.text.is_empty()),
        comparison: source.comparison,
        prompts: prompt_reads,
    };
    write_json(&report_path, &report)?;

    // ── THE ARTIFACT ────────────────────────────────────────────────────────────────────────
    println!("THE ARTIFACT — GENERATED TEXT");
    for prompt in &report.prompts {
        println!("\n[{}] {}", prompt.identity, prompt.prompt);
        println!(
            "  prompt inherited contiguously: {}   recruited {} sources across {} receivers",
            prompt.prompt_was_inherited_contiguously,
            prompt.recruited_source_population,
            prompt.recruited_receiver_population
        );
        let mut emitted = 0usize;
        for (at, output) in prompt.outputs.iter().enumerate() {
            if output.text.is_empty() {
                continue;
            }
            emitted += 1;
            println!("  {}. {}", at + 1, output.text);
            println!(
                "     tokens={} sentence_boundary={} output_inherited_contiguously={} prompt+output_inherited={}",
                output.generated_tokens,
                output.stopped_at_sentence_boundary,
                output.output_was_inherited_contiguously,
                output.prompt_plus_output_was_inherited_contiguously
            );
            for token in &output.token_receipts {
                println!(
                    "       token {:?} matched_horizon={} sources={}",
                    token.token,
                    token.matched_horizon,
                    token.sources.len()
                );
            }
        }
        if emitted == 0 {
            println!("  (no nonempty branch)");
        }
    }
    println!("\nCONTROL — a prompt built from words the corpus does not carry");
    println!("  prompt   {:?}", control.prompt);
    println!("  branches {}", control.outputs.len());
    for output in &control.outputs {
        println!("  emitted  {:?}", output.text);
    }
    println!(
        "  control_emitted_no_text  {}",
        report.control_emitted_no_text
    );
    println!(
        "\nreceipts: {} nonempty texts / {} tokens / {} distinct recruited receivers; report {}",
        report.nonempty_output_population,
        report.generated_tokens,
        report.distinct_recruited_receivers,
        report_path.display()
    );
    Ok(())
}

fn prompt_read(
    identity: String,
    generated: CausalLanguageGeneration,
    prompt_was_inherited_contiguously: bool,
    corpus_tokens: &[Vec<String>],
) -> Result<PromptRead, String> {
    let recruited_receiver_population = generated
        .initial_hexis
        .iter()
        .map(|source| source.receiver)
        .collect::<BTreeSet<_>>()
        .len();
    let recruited_sources = generated
        .initial_hexis
        .iter()
        .map(|source| RecruitedRead {
            identity: source.identity.clone(),
            receiver: source.receiver,
            supporting_features: source.supporting_features.iter().cloned().collect(),
        })
        .collect::<Vec<_>>();
    let prompt_tokens = lexical_tokens(&generated.prompt);
    let outputs = generated
        .outputs
        .iter()
        .map(|output| output_read(output, &prompt_tokens, corpus_tokens))
        .collect::<Result<Vec<_>, String>>()?;
    Ok(PromptRead {
        identity,
        prompt: generated.prompt,
        prompt_was_inherited_contiguously,
        recruited_source_population: generated.initial_hexis.len(),
        recruited_receiver_population,
        recruited_sources,
        outputs,
    })
}

fn output_read(
    output: &CausalGeneratedText,
    prompt_tokens: &[String],
    corpus_tokens: &[Vec<String>],
) -> Result<OutputRead, String> {
    let emitted = output
        .tokens
        .iter()
        .map(|token| token.token.clone())
        .collect::<Vec<_>>();
    let mut joined = prompt_tokens.to_vec();
    joined.extend(emitted.iter().cloned());
    let returned_rest = output
        .returned_rest_image()
        .encode_native_bytes()
        .map_err(debug)?;
    Ok(OutputRead {
        text: output.text.clone(),
        generated_tokens: output.tokens.len(),
        stopped_at_sentence_boundary: output.stopped_at_sentence_boundary,
        output_was_inherited_contiguously: corpus_contains(corpus_tokens, &emitted),
        prompt_plus_output_was_inherited_contiguously: corpus_contains(corpus_tokens, &joined),
        returned_rest_bytes: returned_rest.len(),
        returned_rest_sha256: sha256(&returned_rest),
        token_receipts: output
            .tokens
            .iter()
            .map(|token| TokenRead {
                token: token.token.clone(),
                matched_horizon: token.matched_horizon,
                sources: token.sources.iter().cloned().collect(),
            })
            .collect(),
    })
}

/// Whether the corpus carries this exact token run contiguously inside one passage.
fn corpus_contains(corpus_tokens: &[Vec<String>], needle: &[String]) -> bool {
    if needle.is_empty() {
        return false;
    }
    corpus_tokens.iter().any(|passage| {
        passage.len() >= needle.len()
            && passage.windows(needle.len()).any(|window| window == needle)
    })
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != "soma.causal-language.source.v1"
        || source.files.is_empty()
        || source.passages.is_empty()
        || source.prompts.is_empty()
    {
        return Err("causal language source is empty or has the wrong schema".to_owned());
    }
    let files = source
        .files
        .iter()
        .map(|file| (file.path.as_str(), file))
        .collect::<BTreeMap<_, _>>();
    let mut identities = BTreeSet::new();
    for passage in &source.passages {
        let file = files
            .get(passage.source_path.as_str())
            .ok_or_else(|| format!("{} has no source file", passage.identity))?;
        if passage.source_sha256 != file.sha256
            || passage.receiver != file.receiver
            || passage.text.trim().is_empty()
            || !identities.insert(&passage.identity)
        {
            return Err(format!("{} has invalid source lineage", passage.identity));
        }
    }
    for file in &source.files {
        let population = source
            .passages
            .iter()
            .filter(|passage| passage.source_path == file.path)
            .count();
        if population != file.passages {
            return Err(format!("{} passage census changed", file.path));
        }
    }
    Ok(())
}

fn write_json(path: &Path, report: &Report) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)
                .map_err(|error| format!("create {}: {error}", parent.display()))?;
        }
    }
    std::fs::write(
        path,
        serde_json::to_vec_pretty(report).map_err(|error| format!("encode report: {error}"))?,
    )
    .map_err(|error| format!("write {}: {error}", path.display()))
}

fn sha256(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    digest
        .finalize()
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

fn usage() -> String {
    "usage: eros_causal_language_generation SOURCE.json REPORT.json".to_owned()
}
