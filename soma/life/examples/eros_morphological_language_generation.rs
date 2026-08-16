//! Full-corpus simultaneous-scale language conditioning and compositional response grade.
//!
//! No external model, embedding service, stochastic sampler, or retained target answer runs.
//! The frozen source supplies inherited textual occurrences and their source lineages. Production
//! Swing routes condition exact occurrence incidence; recurrent suffix owners carry mark,
//! clause, delivery, and lexical scales. One returned event advances the same sparse exact
//! receiver current consulted by the next emanation; alternative currents share the conditioned
//! body and terminal witness materialization occurs only after propagation.

use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    time::Instant,
};

use body::num::Cog;
use life::{
    causal_language::lexical_tokens,
    form_mouth::deposit_form_or_message,
    live_current_cuda::CudaLiveCurrentExecutor,
    morphological_language::{
        CudaMorphologicalConditioner, MorphologicalGeneratedText, MorphologicalGenerationSpec,
        MorphologicalLanguageEcology, MorphologicalLanguageGeneration,
        MorphologicalLanguagePassage, MorphologicalResponseRest,
    },
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;
use soma_membrane::live_current::{LiveCurrentExecutor, ParallelCpuLiveCurrentExecutor};

/// This driver's name at the plate mouth:
/// `output/eros_morphological_language_generation/<name>-<sha256>.form`.
const FORM_DRIVER: &str = "eros_morphological_language_generation";
/// The resonance ecology's returned rest wire. `holon-plate` holds no schema that reads it.
const RETURNED_REST_FORM: &str = "returned-rest";

const REPORT_SCHEMA: &str = "soma.morphological-language.report.v5";

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
    delivery_occurrences: usize,
    source_lineages: usize,
    clause_receivers: usize,
    lexical_occurrences: usize,
    lexical_recurrent_states: usize,
    lexical_material_transitions: usize,
    clause_lexical_recurrent_states: usize,
    clause_lexical_material_transitions: usize,
    ordered_region_recurrent_states: usize,
    ordered_region_material_transitions: usize,
    conditioned_question_operator_regions: usize,
    conditioned_question_operator_surfaces: Vec<Vec<String>>,
    mark_word_occurrences: usize,
    forward_mark_recurrent_states: usize,
    reverse_mark_recurrent_states: usize,
    returned_route_receptors: usize,
    returned_route_relations: usize,
    conditioning_events: usize,
    worker_threads: usize,
    conditioning_wall_millis: u128,
    generation_wall_millis: u128,
    prompt_population: usize,
    closed_output_population: usize,
    cross_source_output_population: usize,
    noncontiguous_composite_population: usize,
    novel_intra_phase_output_population: usize,
    recurrent_source_seam_population: usize,
    observation_exhaustion_population: usize,
    obstruction_population: usize,
    self_emanated_event_returns: usize,
    deferred_whole_response_returns: usize,
    control_emitted_no_text: bool,
    comparison: serde_json::Value,
    prompts: Vec<PromptRead>,
}

#[derive(Serialize)]
struct PromptRead {
    identity: String,
    prompt: String,
    prompt_was_inherited_contiguously: bool,
    recruited_passages: usize,
    mark_faces: Vec<MarkFaceRead>,
    operator_features: Vec<String>,
    contextual_features: Vec<String>,
    obligations: Vec<ObligationRead>,
    outputs: Vec<OutputRead>,
    shared_conditioned_bodies: usize,
    whole_body_forks: usize,
    causal_current_states_formed: usize,
    conduct_equivalent_states_glued: usize,
    peak_live_current_states: usize,
    returned_events_carried: usize,
    terminal_return_materializations: usize,
}

#[derive(Serialize)]
struct MarkFaceRead {
    surface: String,
    forward_horizon: u32,
    reverse_horizon: u32,
    reached_sources: Vec<String>,
}

#[derive(Serialize)]
struct ObligationRead {
    features: Vec<String>,
    reached_passages: usize,
    reached_sources: Vec<String>,
    local_regions: Vec<QueryRegionRead>,
}

#[derive(Serialize)]
struct QueryRegionRead {
    ordered_surface: Vec<String>,
    features: Vec<String>,
    reached_passages: usize,
    reached_sources: Vec<String>,
}

#[derive(Serialize)]
struct OutputRead {
    text: String,
    rest: String,
    open_obligations: Vec<usize>,
    generated_tokens: usize,
    phases: Vec<PhaseRead>,
    distinct_sources: usize,
    cross_source: bool,
    output_was_inherited_contiguously: bool,
    prompt_plus_output_was_inherited_contiguously: bool,
    noncontiguous_composite: bool,
    all_phases_inherited_contiguously: bool,
    cross_source_junctions: usize,
    novel_cross_source_junctions: usize,
    novel_intra_phase: bool,
    recurrent_source_seams: usize,
    all_events_returned_before_next_frontier: bool,
    all_surface_tokens_inherited: bool,
    capability_class: &'static str,
    returned_rest_bytes: usize,
    returned_rest_sha256: String,
    tokens: Vec<TokenRead>,
}

#[derive(Serialize)]
struct PhaseRead {
    entry_clause: String,
    clauses: Vec<String>,
    sources: Vec<String>,
    passages: Vec<String>,
    boundary: Option<String>,
    discharged_obligations: Vec<usize>,
    discharged_regions: BTreeMap<usize, Vec<usize>>,
    discharged_features: BTreeMap<usize, Vec<String>>,
    entry_lexical_horizons: Vec<u32>,
    entry_recurrence_multiplicities: Vec<u64>,
    emitted_start: usize,
    emitted_end: usize,
}

#[derive(Serialize)]
struct TokenRead {
    token: String,
    transport: String,
    lexical_horizons: Vec<u32>,
    forward_mark_horizon: u32,
    reverse_mark_horizon: u32,
    recurrent_sources: Vec<String>,
    recurrent_context_sources: Vec<String>,
    caused_sources: Vec<String>,
    caused_passages: Vec<String>,
    supporting_clauses: Vec<String>,
    returned_event_count: usize,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("eros morphological language generation: {error}");
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
    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "action current is dark".to_owned())?;
    let workers = std::thread::available_parallelism()
        .map(|workers| workers.get())
        .unwrap_or(1);
    let passages = source
        .passages
        .iter()
        .map(|passage| {
            MorphologicalLanguagePassage::new(
                passage.identity.clone(),
                passage.source_path.clone(),
                passage.receiver,
                passage.text.clone(),
            )
        })
        .collect::<Vec<_>>();
    let corpus = source
        .passages
        .iter()
        .map(|passage| lexical_tokens(&passage.text))
        .collect::<Vec<_>>();

    eprintln!(
        "eros morphological language generation: conditioning {} source lineages / {} delivered occurrences",
        source.files.len(),
        passages.len()
    );
    // **The carrier is MOUNTED and threaded, not built privately inside each call.**
    //
    // This driver called `condition` and `generate`, both of which construct a private cpu pool.
    // The card was therefore unreachable from production — not declined, unreachable — which is
    // exactly the finding `research/records/2026-08-10_THE_FRONT_IS_THE_PARALLEL_UNIT…` recorded
    // for the agentic seam and which went unrepaired here. `SOMA_CPU` forces the cpu carrier so
    // the two can be compared on the same material; without it the card carries the deed.
    // **CONDITIONING AND GENERATION WANT TWO DIFFERENT MOUNTS OF THE SAME CARD, and mounting the
    // wrong one here is what made every run of this driver hang with the card idle.**
    //
    // `condition_with_executor` threads a `LiveCurrentExecutor`, so the card is reached ONE SWING
    // EVENT AT A TIME. The route arm it selects is the per-row replay whose own comment inside
    // `condition_inner` records the cost — *"the prior card arm replayed every row through a
    // `ResonanceEcology`, returned the same target set, then discarded the complete rest image. On
    // the 2,672-passage sealed front that echo ran for fifteen minutes without reaching the
    // constitutive charts."* Handing that arm a card does not repair it; a per-event crossing of a
    // card is a bottleneck, not a carrier, and the observable signature is exactly one core pinned
    // with the device at idle.
    //
    // `condition_with_cuda` is the arm built for this deed and it takes a **resident**
    // `CudaMorphologicalConditioner`: the route transpose is formed once from its caused rows, and
    // the five generalized suffix ecologies and the question-prefix incidence are founded on the
    // card with **no cpu fallback**. It has stood in this tree with one caller, and that caller is
    // not a generation driver.
    //
    // So conditioning takes the resident conditioner and is released before generation mounts the
    // live executor it needs. `SOMA_CPU` still forces the whole run onto the cpu so the two remain
    // comparable on one material.
    let force_cpu = std::env::var_os("SOMA_CPU").is_some();
    let conditioning_started = Instant::now();
    let ecology = if force_cpu {
        eprintln!("eros morphological language generation: carrier = cpu, {workers} lanes");
        let mut cpu = ParallelCpuLiveCurrentExecutor::new(workers.max(1));
        MorphologicalLanguageEcology::condition_with_executor(
            &passages, action, workers, &mut cpu,
        )
        .map_err(debug)?
    } else {
        match CudaMorphologicalConditioner::new(0) {
            Ok(mut conditioner) => {
                eprintln!(
                    "eros morphological language generation: carrier = {} (resident conditioner)",
                    conditioner.device_name()
                );
                let (ecology, _semantic, apparatus) =
                    MorphologicalLanguageEcology::condition_with_cuda(
                        &passages,
                        action,
                        &mut conditioner,
                    )
                    .map_err(debug)?;
                eprintln!(
                    "eros morphological language generation: conditioner apparatus {apparatus:?}"
                );
                ecology
            }
            Err(error) => {
                // Named, never silent. A run that fell back without saying so would report a cpu
                // figure as a card figure.
                eprintln!(
                    "eros morphological language generation: the resident conditioner refused to \
                     mount ({error}); carrying on the cpu with {workers} lanes"
                );
                let mut cpu = ParallelCpuLiveCurrentExecutor::new(workers.max(1));
                MorphologicalLanguageEcology::condition_with_executor(
                    &passages, action, workers, &mut cpu,
                )
                .map_err(debug)?
            }
        }
    };
    let conditioning_wall_millis = conditioning_started.elapsed().as_millis();
    eprintln!(
        "eros morphological language generation: conditioned in {conditioning_wall_millis} ms"
    );

    // Generation wants the live executor, which is the mount whose grain matches its deed: a front
    // of co-present branch tips, each crossing as its own event.
    let mut card;
    let mut cpu;
    let carrier: &mut dyn LiveCurrentExecutor = if force_cpu {
        cpu = ParallelCpuLiveCurrentExecutor::new(workers.max(1));
        &mut cpu
    } else {
        match CudaLiveCurrentExecutor::new(0) {
            Ok(mounted) => {
                card = mounted;
                &mut card
            }
            Err(error) => {
                eprintln!(
                    "eros morphological language generation: the card refused to mount for \
                     generation ({error}); carrying on the cpu with {workers} lanes"
                );
                cpu = ParallelCpuLiveCurrentExecutor::new(workers.max(1));
                &mut cpu
            }
        }
    };
    let generation_started = Instant::now();
    let mut prompt_reads = Vec::new();
    for prompt in source.prompts {
        let inherited = corpus_contains(&corpus, &lexical_tokens(&prompt.text));
        let generation = ecology
            .generate_with_executor(
                &prompt.text,
                MorphologicalGenerationSpec {
                    maximum_observed_tokens: prompt.maximum_generated_tokens,
                },
                action,
                carrier,
            )
            .map_err(debug)?;
        eprintln!(
            "eros morphological language generation: {} formed {} obligations / {} response branches",
            prompt.identity,
            generation.charge.obligations.len(),
            generation.outputs.len()
        );
        prompt_reads.push(prompt_read(
            prompt.identity,
            generation,
            inherited,
            &corpus,
        )?);
    }
    let control = ecology
        .generate(
            &source.control_prompt,
            MorphologicalGenerationSpec {
                maximum_observed_tokens: 64,
            },
            action,
            workers,
        )
        .map_err(debug)?;
    let generation_wall_millis = generation_started.elapsed().as_millis();

    let outputs = prompt_reads
        .iter()
        .flat_map(|prompt| prompt.outputs.iter())
        .collect::<Vec<_>>();
    let census = ecology.census();
    let report = Report {
        schema: REPORT_SCHEMA,
        status: "causally-attached-reflective-current-generation",
        source_schema: source.schema,
        question: source.question,
        source_sha256: sha256(&source_bytes),
        source_files: source.files.len(),
        source_bytes: source.files.iter().map(|file| file.bytes).sum(),
        source_receivers: source
            .files
            .iter()
            .map(|file| file.receiver)
            .collect::<BTreeSet<_>>()
            .len(),
        delivery_occurrences: census.delivery_occurrences,
        source_lineages: census.source_lineages,
        clause_receivers: census.clause_receivers,
        lexical_occurrences: census.lexical_occurrences,
        lexical_recurrent_states: census.lexical_recurrent_states,
        lexical_material_transitions: census.lexical_material_transitions,
        clause_lexical_recurrent_states: census.clause_lexical_recurrent_states,
        clause_lexical_material_transitions: census.clause_lexical_material_transitions,
        ordered_region_recurrent_states: census.ordered_region_recurrent_states,
        ordered_region_material_transitions: census.ordered_region_material_transitions,
        conditioned_question_operator_regions: census.conditioned_question_operator_regions,
        conditioned_question_operator_surfaces: ecology.question_operator_regions(),
        mark_word_occurrences: census.mark_word_occurrences,
        forward_mark_recurrent_states: census.forward_mark_recurrent_states,
        reverse_mark_recurrent_states: census.reverse_mark_recurrent_states,
        returned_route_receptors: census.returned_route_receptors,
        returned_route_relations: census.returned_route_relations,
        conditioning_events: census.conditioning_events,
        worker_threads: workers,
        conditioning_wall_millis,
        generation_wall_millis,
        prompt_population: prompt_reads.len(),
        closed_output_population: outputs
            .iter()
            .filter(|output| output.rest == "closed")
            .count(),
        cross_source_output_population: outputs.iter().filter(|output| output.cross_source).count(),
        noncontiguous_composite_population: outputs
            .iter()
            .filter(|output| output.noncontiguous_composite)
            .count(),
        novel_intra_phase_output_population: outputs
            .iter()
            .filter(|output| output.novel_intra_phase)
            .count(),
        recurrent_source_seam_population: outputs
            .iter()
            .map(|output| output.recurrent_source_seams)
            .sum(),
        observation_exhaustion_population: outputs
            .iter()
            .filter(|output| output.rest == "observation-aperture-exhausted")
            .count(),
        obstruction_population: outputs
            .iter()
            .filter(|output| output.rest == "obstructed")
            .count(),
        self_emanated_event_returns: outputs.iter().map(|output| output.generated_tokens).sum(),
        deferred_whole_response_returns: 0,
        control_emitted_no_text: control.outputs.iter().all(|output| output.text.is_empty()),
        comparison: source.comparison,
        prompts: prompt_reads,
    };
    write_json(&report_path, &report)?;
    println!(
        "eros morphological language generation: wrote {} closed / {} cross-source / {} noncontiguous composites to {}",
        report.closed_output_population,
        report.cross_source_output_population,
        report.noncontiguous_composite_population,
        report_path.display()
    );
    for prompt in &report.prompts {
        println!("\n[{}] {}", prompt.identity, prompt.prompt);
        for (at, output) in prompt.outputs.iter().enumerate() {
            println!(
                "  {}. [{}; {} sources] {}",
                at + 1,
                output.rest,
                output.distinct_sources,
                output.text
            );
        }
    }
    Ok(())
}

fn prompt_read(
    identity: String,
    generation: MorphologicalLanguageGeneration,
    prompt_was_inherited_contiguously: bool,
    corpus: &[Vec<String>],
) -> Result<PromptRead, String> {
    let reflection = generation.reflection.clone();
    let outputs = generation
        .outputs
        .into_iter()
        .map(|output| output_read(&generation.charge.prompt_tokens, output, corpus))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(PromptRead {
        identity,
        prompt: generation.charge.prompt,
        prompt_was_inherited_contiguously,
        recruited_passages: generation.charge.recruited_passages.len(),
        mark_faces: generation
            .charge
            .mark_faces
            .into_iter()
            .map(|face| MarkFaceRead {
                surface: face.surface,
                forward_horizon: face.forward_horizon,
                reverse_horizon: face.reverse_horizon,
                reached_sources: face.reached_sources.into_iter().collect(),
            })
            .collect(),
        operator_features: generation.charge.operator_features.into_iter().collect(),
        contextual_features: generation.charge.contextual_features.into_iter().collect(),
        obligations: generation
            .charge
            .obligations
            .into_iter()
            .map(|obligation| ObligationRead {
                features: obligation.features.into_iter().collect(),
                reached_passages: obligation.reached_passages.len(),
                reached_sources: obligation.reached_sources.into_iter().collect(),
                local_regions: obligation
                    .local_regions
                    .into_iter()
                    .map(|region| QueryRegionRead {
                        ordered_surface: region.ordered_surface,
                        features: region.features.into_iter().collect(),
                        reached_passages: region.reached_passages.len(),
                        reached_sources: region.reached_sources.into_iter().collect(),
                    })
                    .collect(),
            })
            .collect(),
        outputs,
        shared_conditioned_bodies: reflection.shared_conditioned_bodies,
        whole_body_forks: reflection.whole_body_forks,
        causal_current_states_formed: reflection.causal_current_states_formed,
        conduct_equivalent_states_glued: reflection.conduct_equivalent_states_glued,
        peak_live_current_states: reflection.peak_live_current_states,
        returned_events_carried: reflection.returned_events_carried,
        terminal_return_materializations: reflection.terminal_return_materializations,
    })
}

fn output_read(
    prompt: &[String],
    output: MorphologicalGeneratedText,
    corpus: &[Vec<String>],
) -> Result<OutputRead, String> {
    let returned = output
        .returned_rest_image()
        .encode_native_bytes()
        .map_err(debug)?;
    // THE_ASSEMBLY.md step 5, loop (d): *the signal is the octets*. Everything reported is untouched.
    let deposited = deposit_form_or_message(FORM_DRIVER, RETURNED_REST_FORM, &returned)?;
    eprintln!("form deposited: {}", deposited.path.display());
    let output_tokens = output
        .tokens
        .iter()
        .map(|token| token.token.clone())
        .collect::<Vec<_>>();
    let mut complete = prompt.to_vec();
    complete.extend(output_tokens.iter().cloned());
    let output_was_inherited_contiguously = corpus_contains(corpus, &output_tokens);
    let prompt_plus_output_was_inherited_contiguously = corpus_contains(corpus, &complete);
    let sources = output
        .phases
        .iter()
        .flat_map(|phase| phase.sources.iter().cloned())
        .collect::<BTreeSet<_>>();
    let distinct_sources = sources.len();
    let all_phases_inherited_contiguously = output.phases.iter().all(|phase| {
        corpus_contains(
            corpus,
            &output_tokens[phase.emitted_start..phase.emitted_end],
        )
    });
    let novel_intra_phase = !all_phases_inherited_contiguously;
    let recurrent_source_seams = output
        .tokens
        .iter()
        .filter(|token| {
            !token.recurrent_context_sources.is_empty()
                && token.recurrent_context_sources != token.caused_sources
        })
        .count();
    let all_events_returned_before_next_frontier = output
        .tokens
        .iter()
        .enumerate()
        .all(|(at, token)| token.returned_event_count == at + 1);
    let mut cross_source_junctions = 0usize;
    let mut novel_cross_source_junctions = 0usize;
    for pair in output.phases.windows(2) {
        if !pair[0].sources.is_disjoint(&pair[1].sources) || pair[0].emitted_end == 0 {
            continue;
        }
        cross_source_junctions += 1;
        let junction = &output_tokens[pair[0].emitted_end - 1..=pair[0].emitted_end];
        if !corpus_contains(corpus, junction) {
            novel_cross_source_junctions += 1;
        }
    }
    let vocabulary = corpus
        .iter()
        .flat_map(|path| path.iter())
        .collect::<BTreeSet<_>>();
    let all_surface_tokens_inherited = output_tokens.iter().all(|token| vocabulary.contains(token));
    let (rest, open_obligations) = match output.rest {
        MorphologicalResponseRest::Closed => ("closed".to_owned(), Vec::new()),
        MorphologicalResponseRest::Obstructed { open_obligations } => (
            "obstructed".to_owned(),
            open_obligations.into_iter().collect(),
        ),
        MorphologicalResponseRest::ObservationApertureExhausted { open_obligations } => (
            "observation-aperture-exhausted".to_owned(),
            open_obligations.into_iter().collect(),
        ),
    };
    Ok(OutputRead {
        text: output.text,
        rest,
        open_obligations,
        generated_tokens: output.tokens.len(),
        phases: output
            .phases
            .into_iter()
            .map(|phase| PhaseRead {
                entry_clause: phase.entry_clause,
                clauses: phase.clauses.into_iter().collect(),
                sources: phase.sources.into_iter().collect(),
                passages: phase.passages.into_iter().collect(),
                boundary: phase.boundary.map(|boundary| format!("{boundary:?}")),
                discharged_obligations: phase.discharged_obligations.into_iter().collect(),
                discharged_regions: phase
                    .discharged_regions
                    .into_iter()
                    .map(|(obligation, regions)| {
                        (obligation, regions.into_iter().collect::<Vec<_>>())
                    })
                    .collect(),
                discharged_features: phase
                    .discharged_features
                    .into_iter()
                    .map(|(obligation, features)| {
                        (obligation, features.into_iter().collect::<Vec<_>>())
                    })
                    .collect(),
                entry_lexical_horizons: phase.entry_lexical_horizons.into_iter().collect(),
                entry_recurrence_multiplicities: phase
                    .entry_recurrence_multiplicities
                    .into_iter()
                    .collect(),
                emitted_start: phase.emitted_start,
                emitted_end: phase.emitted_end,
            })
            .collect(),
        distinct_sources,
        cross_source: distinct_sources >= 2,
        output_was_inherited_contiguously,
        prompt_plus_output_was_inherited_contiguously,
        noncontiguous_composite: distinct_sources >= 2 && !output_was_inherited_contiguously,
        all_phases_inherited_contiguously,
        cross_source_junctions,
        novel_cross_source_junctions,
        novel_intra_phase,
        recurrent_source_seams,
        all_events_returned_before_next_frontier,
        all_surface_tokens_inherited,
        capability_class: "exact-causally-attached-reflective-current-frontier",
        returned_rest_bytes: returned.len(),
        returned_rest_sha256: sha256(&returned),
        tokens: output
            .tokens
            .into_iter()
            .map(|token| TokenRead {
                token: token.token,
                transport: format!("{:?}", token.transport),
                lexical_horizons: token.lexical_horizons.into_iter().collect(),
                forward_mark_horizon: token.forward_mark_horizon,
                reverse_mark_horizon: token.reverse_mark_horizon,
                recurrent_sources: token.recurrent_sources.into_iter().collect(),
                recurrent_context_sources: token.recurrent_context_sources.into_iter().collect(),
                caused_sources: token.caused_sources.into_iter().collect(),
                caused_passages: token.caused_passages.into_iter().collect(),
                supporting_clauses: token.supporting_clauses.into_iter().collect(),
                returned_event_count: token.returned_event_count,
            })
            .collect(),
    })
}

fn corpus_contains(corpus: &[Vec<String>], needle: &[String]) -> bool {
    !needle.is_empty()
        && corpus
            .iter()
            .any(|path| path.windows(needle.len()).any(|window| window == needle))
}

fn validate_source(source: &Source) -> Result<(), String> {
    if source.schema != "soma.morphological-language.source.v2"
        || source.files.is_empty()
        || source.passages.is_empty()
        || source.prompts.is_empty()
        || source.control_prompt.is_empty()
    {
        return Err("source is empty or has the wrong schema".to_owned());
    }
    let files = source
        .files
        .iter()
        .map(|file| file.path.as_str())
        .collect::<BTreeSet<_>>();
    if files.len() != source.files.len()
        || source.files.iter().any(|file| {
            file.sha256.len() != 64 || file.bytes == 0 || file.passages == 0 || file.receiver == 0
        })
        || source.passages.iter().any(|passage| {
            passage.identity.is_empty()
                || passage.text.is_empty()
                || passage.source_sha256.len() != 64
                || !files.contains(passage.source_path.as_str())
        })
    {
        return Err("source lineage is malformed".to_owned());
    }
    Ok(())
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|error| format!("{} creates: {error}", parent.display()))?;
    }
    let mut body = serde_json::to_vec_pretty(value).map_err(debug)?;
    body.push(b'\n');
    std::fs::write(path, body).map_err(|error| format!("{} writes: {error}", path.display()))
}

fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn debug(error: impl std::fmt::Debug) -> String {
    format!("{error:?}")
}

fn usage() -> String {
    "usage: eros_morphological_language_generation <SOURCE.json> <REPORT.json>".to_owned()
}
