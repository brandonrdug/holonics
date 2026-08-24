//! AA2--AA4: returned exchange defects condense into generator-native hexis and Athena alpha rests.
//!
//! The complete source world is present only during cultivation. The frozen product carries
//! parented proper continuation generators, reconstruction fibres and external native-organ
//! identities. A fresh private namespace mounts that rest, the admitted E5 membrane organ and the
//! requested held-out occurrences; no exchange store, repository, transcript or Lean runtime is
//! available there.

#[path = "n3/cultivation.rs"]
#[allow(dead_code)]
mod cultivation;

use std::{
    cmp::Reverse,
    collections::{BTreeMap, BTreeSet},
    env, fs,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
    process::Command,
    time::{Instant, SystemTime},
};

use body::num::Cog;
use holonic_engine::{
    category::BoundaryId,
    cuda_refine::CudaRefineExecutor,
    phoenix::{
        boundary_cultivation::ReturnedBoundaryCultivationRest,
        emanative::{EmanativeSession, EmanativeStatus},
        native_membrane::{
            NativeBoundaryOccurrence, NativeInferenceMembrane, source_incidence_identity,
        },
        runtime::ProductSession,
        streamed::InterventionSite,
        tower::Intervention,
    },
};
use life::{
    athena_alpha::condense_returned_generators,
    causal_language::lexical_tokens,
    exchange_world_tube::{
        ContinuationAperture, ContinuationFamily, ContinuationPartition, ExchangeWorldTube,
        remount_exchange_world_tube,
    },
    live_current_cuda::CudaLiveCurrentExecutor,
    mathematical_particle::{NativeMathematicalInquiry, NativeSuccessorHistory},
    morphological_language::{
        CudaMorphologicalConditioner, MorphologicalGenerationSpec, MorphologicalGenerator,
        MorphologicalGeneratorRest, MorphologicalLanguageGeneration,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;

use cultivation::{NativeCultivatedMathematicalRest, NativeMathematicalWorldReturn};

const AA0: &str = "output/the_complete_laboratory_exchange_returns_for_athena_alpha";
const AA1: &str = "output/the_complete_continuations_return_their_multiscale_defects";
const E5_REST: &str = "output/the_agentic_laboratory_athena_freezes/athena-rest";
const OPTICAL: &str =
    "output/the_optical_holons_grow_across_scales/06-inspected-hierarchical-field.json";
const ACOUSTIC: &str = "output/the_acoustic_section_crosses_the_inherited_projection_and_three_ports_share_one_native_ecology/00-source-conduct.json";
const OUTPUT: &str = "output/the_athena_alpha_cultivates_the_complete_laboratory_exchange";

#[derive(Debug)]
enum Args {
    Produce {
        aa0: PathBuf,
        aa1: PathBuf,
        e5: PathBuf,
        output: PathBuf,
    },
    Detached {
        rest: PathBuf,
        e5: PathBuf,
        tower: PathBuf,
        continuation: PathBuf,
        input: PathBuf,
        output: PathBuf,
    },
    ForeignProbe {
        product: PathBuf,
        continuation: PathBuf,
        prompt: String,
        output: PathBuf,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PromptCase {
    occurrence: String,
    role: String,
    family_occurrence: String,
    prompt: String,
    history: Vec<PromptHistoryFace>,
    native_features: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PromptHistoryFace {
    occurrence: String,
    speaker: String,
    text: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DetachedInput {
    schema: String,
    cases: Vec<PromptCase>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AnswerFace {
    text: String,
    text_sha256: String,
    token_population: usize,
    phase_population: usize,
    rest: String,
    caused_source_population: usize,
    complete_surface_returned: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct AnswerReturn {
    occurrence: String,
    role: String,
    family_occurrence: String,
    prompt_sha256: String,
    native_features: BTreeSet<String>,
    derived_generation_aperture: usize,
    resident_generator_population: usize,
    excluded_reconstruction_fibre_population: usize,
    obligations: usize,
    recruited_passages: usize,
    output_family_sha256: String,
    complete_family_artifact: String,
    complete_output_population: usize,
    /// Receiver-derived shortest/longest closed surfaces for immediate inspection. The complete
    /// alternative family remains in `complete_family_artifact`.
    outputs: Vec<AnswerFace>,
    complete_closed_outputs: usize,
    obstructed_outputs: usize,
    native_feature_reached: bool,
}

#[derive(Serialize)]
struct CompleteAnswerFamily<'a> {
    schema: &'static str,
    occurrence: &'a str,
    role: &'a str,
    prompt_sha256: String,
    outputs: &'a [AnswerFace],
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct MembraneReturn {
    occurrence: String,
    predecessor_sha256: String,
    successor_sha256: String,
    consequence_sha256: String,
    launches: u64,
    synchronizations: u64,
    open_fibres: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct DetachedReturn {
    schema: String,
    product_identity_sha256: String,
    generator_rest_sha256: String,
    conditioning_semantic: Value,
    conditioning_apparatus: Value,
    answers: Vec<AnswerReturn>,
    native_mathematics: Value,
    behavioral_controls: Value,
    membrane_returns: Vec<MembraneReturn>,
    foreign_tower: Value,
    complete_outputs: usize,
    source_paths_mounted: usize,
    repository_mounted: bool,
    lean_runtime_present: bool,
    gpu_conditioning: bool,
    gpu_generation: bool,
    gpu_mathematics: bool,
    gpu_membrane: bool,
}

#[derive(Clone, Debug)]
struct BehavioralProbe {
    case: PromptCase,
    baseline_signature_sha256: String,
    target_generator_sha256: String,
    derived_generation_aperture: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ForeignAnswer {
    text: String,
    raw_codec_face: String,
    emitted_native_population: usize,
    conducted_fronts: usize,
    closure: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ForeignState {
    occurrence: String,
    native_ids: Vec<u32>,
    emitted_native_ids: Vec<u32>,
    closed: bool,
    closure: Option<String>,
    conducted_fronts: Option<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ForeignStanding {
    schema: String,
    front: usize,
    members: Vec<ForeignState>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct E3Component {
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct E3Manifest {
    schema: String,
    components: BTreeMap<String, E3Component>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct E2Continuation {
    schema: String,
    predecessor_occurrence_sha256: String,
    returned_occurrence_sha256: String,
    candidate_counts: Vec<u32>,
    anchors: usize,
    boundary_order: Vec<BoundaryId>,
    exact_source_pair_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct N4RestComponent {
    name: String,
    path: String,
    sha256: String,
    octets: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct E5MathematicsManifest {
    schema: String,
    truth_status: String,
    predecessor_product_sha256: String,
    components: Vec<N4RestComponent>,
    open_exterior: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct E5MathematicalContinuation {
    schema: String,
    predecessor_cultivated_rest_sha256: String,
    predecessor_world_return_occurrence: String,
    returned_world: NativeMathematicalWorldReturn,
    retained_history_suffix: Vec<String>,
    receiver_visible_change: String,
    open_exterior: Vec<String>,
}

fn main() -> Result<(), String> {
    match arguments()? {
        Args::Produce {
            aa0,
            aa1,
            e5,
            output,
        } => produce(&aa0, &aa1, &e5, &output),
        Args::Detached {
            rest,
            e5,
            tower,
            continuation,
            input,
            output,
        } => detached(&rest, &e5, &tower, &continuation, &input, &output),
        Args::ForeignProbe {
            product,
            continuation,
            prompt,
            output,
        } => foreign_probe(&product, &continuation, &prompt, &output),
    }
}

fn foreign_probe(
    product: &Path,
    continuation: &Path,
    prompt: &str,
    output: &Path,
) -> Result<(), String> {
    if output.exists() {
        return Err(format!("foreign probe output {} already exists", output.display()));
    }
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let codec = ProductSession::open_with_continuation(product, continuation)?;
    let presentation = codec.present_exterior_turn("user", prompt)?;
    write_json(output.join("00-exterior-turn.json"), &presentation)?;
    let entering_population = codec.encode(&presentation.text)?.len();
    let mut session = EmanativeSession::begin(product, Some(continuation), &presentation.text)?;
    let mut invocations = Vec::new();
    loop {
        let begun = Instant::now();
        let runtime = session.advance_exact()?;
        let frontier = session
            .rest()
            .fronts
            .last()
            .ok_or_else(|| "foreign probe returned no frontier".to_owned())?;
        let at = frontier.index;
        write_json(
            output.join(format!("front-{at:02}-runtime.json")),
            &runtime.receipt,
        )?;
        invocations.push(json!({
            "front":at,
            "elapsed_milliseconds":begun.elapsed().as_millis().to_string(),
            "plural":frontier.potential.plural.len(),
            "complete_plural_sha256":frontier.potential.complete_plural_sha256,
        }));
        if !matches!(session.rest().status, EmanativeStatus::Open) {
            return Err(format!(
                "foreign probe reached {:?} before a complete exterior return",
                session.rest().status
            ));
        }
        let emitted = session.rest().emitted_native_ids();
        let generated = codec.decode_native_ids(&emitted)?;
        let selected = frontier
            .selection
            .as_ref()
            .and_then(|selection| {
                frontier
                    .potential
                    .plural
                    .iter()
                    .find(|candidate| candidate.native_id == selection.selected_native_id)
            })
            .ok_or_else(|| "foreign probe has no exact selected face".to_owned())?;
        eprintln!(
            "foreign probe frontier {at}: {:?} => {:?}",
            selected.surface, generated
        );
        let closed_special = matches!(selected.surface.as_str(), "<turn|>" | "<eos>");
        let closed_sentence = generated
            .trim_end()
            .chars()
            .last()
            .is_some_and(|tail| matches!(tail, '.' | '!' | '?'))
            && generated.chars().any(char::is_alphanumeric);
        if closed_special || closed_sentence {
            session.seal_frontier_aperture()?;
            let rest = session.rest().canonical_bytes()?;
            fs::write(output.join("continuation.rest"), rest)
                .map_err(|error| error.to_string())?;
            write_json(output.join("continuation.json"), session.rest())?;
            write_json(output.join("invocations.json"), &invocations)?;
            write_json(
                output.join("return.json"),
                &json!({
                    "schema":"holonics.athena-alpha.foreign-turn-probe.v1",
                    "prompt_sha256":sha(prompt.as_bytes()),
                    "entering_native_population":entering_population,
                    "emitted_native_population":emitted.len(),
                    "generated":generated,
                    "closed_by":if closed_special {"codec-turn-boundary"} else {"returned-sentence-boundary"},
                    "gpu":runtime.receipt.execution.device_name.contains("NVIDIA"),
                    "source_access_clean":runtime.receipt.source_access.forbidden.is_empty(),
                }),
            )?;
            return Ok(());
        }
    }
}

fn conduct_partitioned_foreign_answers(
    product: &Path,
    continuation: &Path,
    cases: &[PromptCase],
    output: &Path,
) -> Result<(BTreeMap<String, ForeignAnswer>, Value), String> {
    if let Some(returned) = restore_partitioned_foreign_answers(
        product,
        continuation,
        cases,
        output,
    )? {
        return Ok(returned);
    }
    let session = ProductSession::open_with_continuation(product, continuation)?;
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let mut states = cases
        .iter()
        .map(|case| {
            let faces = if case.history.is_empty() {
                vec![("user", case.prompt.as_str())]
            } else {
                case.history
                    .iter()
                    .map(|face| (face.speaker.as_str(), face.text.as_str()))
                    .collect::<Vec<_>>()
            };
            let presentation = session.present_exterior_exchange(&faces)?;
            let native_ids = session.encode(&presentation.text)?;
            Ok(ForeignState {
                occurrence: case.occurrence.clone(),
                native_ids,
                emitted_native_ids: Vec::new(),
                closed: false,
                closure: None,
                conducted_fronts: None,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut invocations = Vec::new();
    let mut front = 0usize;
    while states.iter().any(|state| !state.closed) {
        let active = states
            .iter()
            .enumerate()
            .filter_map(|(index, state)| (!state.closed).then_some(index))
            .collect::<Vec<_>>();
        let rows = active
            .iter()
            .map(|index| states[*index].native_ids.clone())
            .collect::<Vec<_>>();
        let begun = Instant::now();
        let returned = session.infer_native_partitioned_with_intervention(
            &rows,
            InterventionSite::Nowhere,
            &Intervention::None,
        )?;
        let elapsed = begun.elapsed();
        let vocabulary = returned.receipt.generated.vocabulary_extent;
        let potential = &returned.cultivated.cultivated_potential;
        if vocabulary == 0 || potential.len() != active.len().saturating_mul(vocabulary) {
            return Err(format!(
                "partitioned foreign frontier {front} returned {} potential faces for {}x{vocabulary}",
                potential.len(),
                active.len(),
            ));
        }
        let runtime_path = format!("front-{front:04}-runtime.json");
        write_json(output.join(&runtime_path), &returned.receipt)?;
        let mut closed_here = 0usize;
        for (row, state_index) in active.iter().copied().enumerate() {
            let face = &potential[row * vocabulary..(row + 1) * vocabulary];
            let top_lower = face
                .iter()
                .map(|(lower, _)| *lower)
                .max()
                .ok_or_else(|| "partitioned foreign potential row is empty".to_owned())?;
            let plural = face
                .iter()
                .enumerate()
                .filter_map(|(native, interval)| {
                    (interval.1 >= top_lower).then_some(native as u32)
                })
                .collect::<Vec<_>>();
            let [selected] = plural.as_slice() else {
                return Err(format!(
                    "foreign frontier {front} occurrence {} retained {} maximizer faces; the cultivated receiver quotient remains open",
                    states[state_index].occurrence,
                    plural.len(),
                ));
            };
            states[state_index].native_ids.push(*selected);
            states[state_index].emitted_native_ids.push(*selected);
            let surface = session.decode_native_ids(&[*selected])?;
            if matches!(surface.as_str(), "<turn|>" | "<eos>") {
                if states[state_index].emitted_native_ids.len() == 1 {
                    return Err(format!(
                        "foreign frontier {front} occurrence {} closed before returning an answer face",
                        states[state_index].occurrence,
                    ));
                }
                states[state_index].closed = true;
                states[state_index].closure = Some(if surface == "<turn|>" {
                    "authenticated-turn-boundary".to_owned()
                } else {
                    "authenticated-end-boundary".to_owned()
                });
                states[state_index].conducted_fronts = Some(front + 1);
                closed_here += 1;
            }
        }
        write_json(
            output.join(format!("front-{front:04}-standing.json")),
            &json!({
                "schema":"holonics.athena-alpha.partitioned-native-standing.v1",
                "front":front,
                "members":states.iter().map(|state| json!({
                    "occurrence":state.occurrence,
                    "native_ids":state.native_ids,
                    "emitted_native_ids":state.emitted_native_ids,
                    "closed":state.closed,
                    "closure":state.closure,
                    "conducted_fronts":state.conducted_fronts,
                })).collect::<Vec<_>>(),
            }),
        )?;
        eprintln!(
            "athena-alpha foreign frontier {front}: active={} closed={} elapsed={}ms",
            active.len(),
            closed_here,
            elapsed.as_millis(),
        );
        invocations.push(json!({
            "front":front,
            "active_occurrences":active.len(),
            "closed_occurrences":closed_here,
            "elapsed_milliseconds":elapsed.as_millis().to_string(),
            "runtime_receipt":runtime_path,
            "device":returned.receipt.execution.device_name,
            "source_access_clean":returned.receipt.source_access.forbidden.is_empty(),
            "complete_partition_rows":returned.receipt.input.presentation.received_rows,
            "exact_work":returned.receipt.total_work,
        }));
        front = front
            .checked_add(1)
            .ok_or_else(|| "foreign recurrence frontier left usize".to_owned())?;
    }
    let answers = states
        .into_iter()
        .map(|state| {
            let raw = session.decode_native_ids(&state.emitted_native_ids)?;
            let text = project_foreign_response(&raw);
            if text.is_empty() {
                return Err(format!(
                    "foreign occurrence {} closed without an answer face",
                    state.occurrence
                ));
            }
            Ok((
                state.occurrence,
                ForeignAnswer {
                    text,
                    raw_codec_face: raw,
                    emitted_native_population: state.emitted_native_ids.len(),
                    conducted_fronts: state
                        .conducted_fronts
                        .ok_or_else(|| "closed foreign state lost its frontier".to_owned())?,
                    closure: state
                        .closure
                        .ok_or_else(|| "closed foreign state lost its boundary".to_owned())?,
                },
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let receipt = json!({
        "schema":"holonics.athena-alpha.partitioned-foreign-recurrence.v1",
        "truth_status":"implemented-exact; measured",
        "occurrences":answers.len(),
        "conducted_fronts":front,
        "single_mounted_body":true,
        "independently_codec_stable_rows":true,
        "all_futures_exact_singletons":true,
        "completion":"authenticated codec turn/end boundary",
        "invocations":invocations,
    });
    write_json(output.join("return.json"), &receipt)?;
    Ok((answers, receipt))
}

fn restore_partitioned_foreign_answers(
    product: &Path,
    continuation: &Path,
    cases: &[PromptCase],
    output: &Path,
) -> Result<Option<(BTreeMap<String, ForeignAnswer>, Value)>, String> {
    let receipt_path = output.join("return.json");
    if !receipt_path.exists() {
        return Ok(None);
    }
    let receipt: Value = read_json(&receipt_path)?;
    let fronts = receipt["conducted_fronts"]
        .as_u64()
        .and_then(|fronts| usize::try_from(fronts).ok())
        .ok_or_else(|| "cached foreign recurrence has no conducted-front extent".to_owned())?;
    if receipt["schema"] != "holonics.athena-alpha.partitioned-foreign-recurrence.v1"
        || receipt["occurrences"].as_u64() != Some(cases.len() as u64)
        || receipt["all_futures_exact_singletons"] != true
        || receipt["independently_codec_stable_rows"] != true
        || fronts == 0
        || receipt["invocations"]
            .as_array()
            .is_none_or(|invocations| invocations.len() != fronts)
    {
        return Err("cached foreign recurrence does not close the requested receiver family"
            .to_owned());
    }
    let final_front = fronts - 1;
    let standing: ForeignStanding = read_json(
        output.join(format!("front-{final_front:04}-standing.json")),
    )?;
    let requested = cases
        .iter()
        .map(|case| case.occurrence.as_str())
        .collect::<BTreeSet<_>>();
    let returned = standing
        .members
        .iter()
        .map(|state| state.occurrence.as_str())
        .collect::<BTreeSet<_>>();
    if standing.schema != "holonics.athena-alpha.partitioned-native-standing.v1"
        || standing.front != final_front
        || standing.members.len() != cases.len()
        || returned != requested
        || standing.members.iter().any(|state| {
            !state.closed
                || state.closure.is_none()
                || state.conducted_fronts.is_none()
                || state.emitted_native_ids.is_empty()
        })
    {
        return Err("cached foreign final standing does not exactly close its addressed lineages"
            .to_owned());
    }
    let codec = ProductSession::open_with_continuation(product, continuation)?;
    let answers = standing
        .members
        .into_iter()
        .map(|state| {
            let raw = codec.decode_native_ids(&state.emitted_native_ids)?;
            let text = project_foreign_response(&raw);
            if text.is_empty() {
                return Err(format!(
                    "cached foreign occurrence {} closed without an answer face",
                    state.occurrence
                ));
            }
            Ok((
                state.occurrence,
                ForeignAnswer {
                    text,
                    raw_codec_face: raw,
                    emitted_native_population: state.emitted_native_ids.len(),
                    conducted_fronts: state
                        .conducted_fronts
                        .ok_or_else(|| "cached closed state lost its frontier".to_owned())?,
                    closure: state
                        .closure
                        .ok_or_else(|| "cached closed state lost its boundary".to_owned())?,
                },
            ))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    eprintln!(
        "athena-alpha foreign recurrence restored: occurrences={} fronts={} terminal={final_front}",
        answers.len(),
        fronts,
    );
    Ok(Some((answers, receipt)))
}

fn project_foreign_response(raw: &str) -> String {
    raw.trim_end_matches("<turn|>")
        .trim_end_matches("<eos>")
        .trim()
        .to_owned()
}

fn receiver_condensed_foreign_cases(
    rest: &MorphologicalGeneratorRest,
    cases: &[PromptCase],
) -> Result<(Vec<PromptCase>, Value), String> {
    let mut condensed = Vec::with_capacity(cases.len());
    let mut receipts = Vec::with_capacity(cases.len());
    for case in cases {
        let (_, contacts) =
            rest.restrict_to_receiver_with_contact(&case.prompt, &case.native_features)?;
        let (content, selected_prompt_sections) =
            condense_receiver_face(&case.prompt, &contacts)?;
        let mut foreign = case.clone();
        foreign.prompt = content.clone();
        let global_separator_face = case
            .history
            .iter()
            .enumerate()
            .filter_map(|(face_index, face)| {
                receiver_atoms(&face.text)
                    .into_iter()
                    .filter(|(_, section)| !word_set(section).is_disjoint(&contacts))
                    .min_by_key(|(section_index, section)| {
                        (section.len(), Reverse(*section_index))
                    })
                    .map(|(section_index, section)| {
                        (
                            section.len(),
                            Reverse(face_index),
                            Reverse(section_index),
                            face_index,
                        )
                    })
            })
            .min()
            .map(|(_, _, _, face_index)| face_index);
        let no_contacts = BTreeSet::new();
        let mut selected_history_sections = 0usize;
        foreign.history = case
            .history
            .iter()
            .enumerate()
            .map(|(face_index, face)| {
                let admitted_contacts = if Some(face_index) == global_separator_face {
                    &contacts
                } else {
                    &no_contacts
                };
                let (text, selected) = condense_receiver_face(&face.text, admitted_contacts)?;
                selected_history_sections = selected_history_sections.saturating_add(selected);
                Ok(PromptHistoryFace {
                    occurrence: face.occurrence.clone(),
                    speaker: face.speaker.clone(),
                    text,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        if let Some(last) = foreign.history.last() {
            foreign.prompt = last.text.clone();
        }
        let source_history_octets = case.history.iter().map(|face| face.text.len()).sum::<usize>();
        let receiver_history_octets = foreign
            .history
            .iter()
            .map(|face| face.text.len())
            .sum::<usize>();
        receipts.push(json!({
            "occurrence":case.occurrence,
            "source_sha256":sha(case.prompt.as_bytes()),
            "source_octets":case.prompt.len(),
            "receiver_section_sha256":sha(content.as_bytes()),
            "receiver_section_octets":content.len(),
            "selected_prompt_incidence_sections":selected_prompt_sections,
            "history_faces":case.history.len(),
            "source_history_octets":source_history_octets,
            "receiver_history_octets":receiver_history_octets,
            "selected_history_incidence_sections":selected_history_sections,
            "globally_selected_separator_face":global_separator_face,
            "complete_source_retained_as_reconstruction_fibre":true,
            "shortest_separating_contacts":contacts,
        }));
        condensed.push(foreign);
    }
    let source_octets = cases
        .iter()
        .map(|case| case.history.iter().map(|face| face.text.len()).sum::<usize>())
        .sum::<usize>();
    let candidate_receiver_octets = condensed
        .iter()
        .map(|case| case.history.iter().map(|face| face.text.len()).sum::<usize>())
        .sum::<usize>();
    // AA4 asks whether every declared receiver role returns a complete continuation. The complete
    // exchange already crossed AA0--AA2; repeating every held-out sibling here would change only
    // the apparatus population. One exact-work minimizer per role is therefore the lawful
    // inspection quotient, with every unselected sibling retained in the reconstruction fibre.
    let mut selected_by_role = BTreeMap::<String, PromptCase>::new();
    for case in condensed {
        let work = case
            .history
            .iter()
            .map(|face| face.text.len())
            .sum::<usize>();
        let replace = selected_by_role.get(&case.role).is_none_or(|standing| {
            let standing_work = standing
                .history
                .iter()
                .map(|face| face.text.len())
                .sum::<usize>();
            (work, &case.occurrence) < (standing_work, &standing.occurrence)
        });
        if replace {
            selected_by_role.insert(case.role.clone(), case);
        }
    }
    let selected = selected_by_role.into_values().collect::<Vec<_>>();
    let receiver_octets = selected
        .iter()
        .map(|case| case.history.iter().map(|face| face.text.len()).sum::<usize>())
        .sum::<usize>();
    eprintln!(
        "athena-alpha receiver condensation: candidates={} selected={} source={} candidates_receiver={} selected_receiver={}",
        cases.len(),
        selected.len(),
        source_octets,
        candidate_receiver_octets,
        receiver_octets,
    );
    Ok((
        selected.clone(),
        json!({
            "schema":"holonics.athena-alpha.receiver-prompt-condensation.v1",
            "law":"the terminal caused section and the smallest section carrying the shortest native separator enter the inherited tower; every excluded section remains the addressed input reconstruction fibre",
            "inspection_factorization":"after complete-exchange cultivation, the least exact entering-work occurrence of every declared receiver role answers AA4; unselected siblings remain the addressed inspection reconstruction fibre",
            "caller_authored_context_or_batch_capacity":false,
            "source_octets":source_octets,
            "candidate_receiver_section_octets":candidate_receiver_octets,
            "receiver_section_octets":receiver_octets,
            "candidate_occurrences":cases.len(),
            "selected_occurrences":selected.iter().map(|case| json!({"role":case.role,"occurrence":case.occurrence})).collect::<Vec<_>>(),
            "unselected_occurrences_retained_as_reconstruction_fibre":cases.len().saturating_sub(selected.len()),
            "receipts":receipts,
        }),
    ))
}

fn condense_receiver_face(
    text: &str,
    contacts: &BTreeSet<String>,
) -> Result<(String, usize), String> {
    let atoms = receiver_atoms(text);
    let terminal = atoms
        .last()
        .ok_or_else(|| "an exchange history face has no receiver section".to_owned())?;
    let separating = atoms
        .iter()
        .filter(|(_, section)| !word_set(section).is_disjoint(contacts))
        .min_by_key(|(index, section)| (section.len(), Reverse(*index)));
    let mut selected = BTreeSet::from([terminal.0]);
    if let Some((index, _)) = separating {
        selected.insert(*index);
    }
    let content = atoms
        .iter()
        .filter(|(index, _)| selected.contains(index))
        .map(|(_, section)| *section)
        .collect::<Vec<_>>()
        .join("\n\n");
    if content.is_empty() {
        return Err("an exchange history face condensed to an empty section".to_owned());
    }
    Ok((content, selected.len()))
}

fn receiver_atoms(text: &str) -> Vec<(usize, &str)> {
    // This is an exterior receiver chart, not a language ontology. Newlines, returned-sentence
    // punctuation and adjacent markup closures are already physical boundaries in the supplied
    // byte face. Use their finest common refinement so a serialized tool result cannot become one
    // giant atom merely because its producer omitted blank lines.
    let bytes = text.as_bytes();
    let mut boundaries = vec![0usize];
    for (index, byte) in bytes.iter().copied().enumerate() {
        let after = index + 1;
        let next = bytes.get(after).copied();
        let line_boundary = byte == b'\n';
        let sentence_boundary = matches!(byte, b'.' | b'!' | b'?' | b';')
            && next.is_none_or(|next| next.is_ascii_whitespace());
        let markup_boundary = byte == b'>' && next == Some(b'<');
        if line_boundary || sentence_boundary || markup_boundary {
            boundaries.push(after);
        }
    }
    if boundaries.last().copied() != Some(text.len()) {
        boundaries.push(text.len());
    }
    boundaries
        .windows(2)
        .filter_map(|pair| {
            let section = text[pair[0]..pair[1]].trim();
            (!section.is_empty()).then_some(section)
        })
        .enumerate()
        .collect::<Vec<(usize, &str)>>()
}

fn produce(aa0: &Path, aa1: &Path, e5: &Path, output: &Path) -> Result<(), String> {
    let resuming = output.exists();
    if resuming && output.join("09-grade.json").exists() {
        let standing: Value = read_json(output.join("09-grade.json"))?;
        if standing["passed"] == true {
            return Err(format!(
                "Athena-alpha output {} already carries a passing final grade",
                output.display()
            ));
        }
    }
    let started = SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|error| error.to_string())?
        .as_nanos();
    let elapsed = Instant::now();
    fs::create_dir_all(output).map_err(|error| error.to_string())?;
    let rest_root = output.join("athena-alpha-rest");
    fs::create_dir_all(&rest_root).map_err(|error| error.to_string())?;

    let world = remount_exchange_world_tube(&aa0.join("exchange-world-tube.ewtb"))?;
    let aperture: ContinuationAperture = read_json(aa0.join("04-continuation-aperture.json"))?;
    let aa1_grade: Value = read_json(aa1.join("02-grade.json"))?;
    if aa1_grade.get("passed").and_then(Value::as_bool) != Some(true) {
        return Err("AA1 has not returned its complete passing defect family".to_owned());
    }
    let aa1_executed_apparatus = bind_aa1_executed_apparatus(aa1)?;
    let predecessor = aa1_grade
        .get("fixed_body_sha256")
        .and_then(Value::as_str)
        .ok_or_else(|| "AA1 fixed body identity is absent".to_owned())?
        .to_owned();
    let parent_defects = parent_defects(aa1, &aperture)?;
    let (organ_features, organ_receipt) = native_organ_incidence(&world, &aperture)?;
    let (rest, condensation) = condense_returned_generators(
        &world,
        &aperture,
        predecessor.clone(),
        &parent_defects,
        &organ_features,
    )?;
    let rest_bytes = rest.canonical_bytes()?;
    let rest_sha256 = sha(&rest_bytes);
    fs::write(rest_root.join("morphological-generators.json"), &rest_bytes)
        .map_err(|error| error.to_string())?;
    write_json(output.join("00-generator-condensation.json"), &condensation)?;
    write_json(
        output.join("01-native-organ-incidence.json"),
        &organ_receipt,
    )?;

    // Repeat the same condensation from the same addressed standing. Equality here is exact
    // source-relative recurrence, not an inference from unchanged counts.
    let (second, _) = condense_returned_generators(
        &world,
        &aperture,
        predecessor.clone(),
        &parent_defects,
        &organ_features,
    )?;
    let saturation = second.canonical_bytes()? == rest_bytes;
    let transcript_audit = transcript_absence_audit(&world, &rest);
    let ablation = structural_ablation_and_withdrawal(&rest)?;
    let chronology = chronology_and_interchange(&rest)?;
    let causal_adjoint = causal_adjoint_return(aa1, &rest)?;
    write_json(
        output.join("02-causal-adjoint-return.json"),
        &causal_adjoint,
    )?;

    let input = heldout_aperture(&world, &aperture, &organ_features)?;
    write_json(output.join("03-heldout-input.json"), &input)?;
    drop(world);

    let e5_manifest = sha_file(&e5.join("MANIFEST.json"))?;
    let (tower, tower_manifest, phoenix_continuation, continuation_manifest) =
        e5_foreign_organs(e5)?;
    let product_identity = digest_json(&(
        &predecessor,
        &rest_sha256,
        &e5_manifest,
        &aa1_executed_apparatus,
        &condensation.open_fibres,
    ))?;
    write_json(
        rest_root.join("MANIFEST.json"),
        &json!({
            "schema":"holonics.athena-alpha.native-rest.v1",
            "truth_status":"implemented-exact; established-bounded",
            "product_identity_sha256":product_identity,
            "predecessor_e5_body_sha256":predecessor,
            "aa1_executed_apparatus_sha256":aa1_executed_apparatus,
            "morphological_generator_rest":{"path":"morphological-generators.json","sha256":rest_sha256,"octets":rest_bytes.len()},
            "external_native_membrane":{"path":e5.display().to_string(),"manifest_sha256":e5_manifest},
            "external_inherited_full_tower":{"path":tower.display().to_string(),"manifest_sha256":tower_manifest},
            "external_cultivated_phoenix_continuation":{"path":phoenix_continuation.display().to_string(),"manifest_sha256":continuation_manifest},
            "source_passages_retained":false,
            "open_reconstruction_fibres":condensation.open_fibres,
        }),
    )?;

    let executable = output.join("athena-alpha-native-inference");
    fs::copy(
        env::current_exe().map_err(|error| error.to_string())?,
        &executable,
    )
    .map_err(|error| error.to_string())?;
    fs::set_permissions(&executable, fs::Permissions::from_mode(0o755))
        .map_err(|error| error.to_string())?;
    let detached_root = output.join("detached-return");
    fs::create_dir_all(&detached_root).map_err(|error| error.to_string())?;
    if detached_root.join("return.json").exists() {
        eprintln!("athena-alpha complete detached return restored for exterior regrade");
    } else {
        run_detached(
            &executable,
            &rest_root,
            e5,
            &tower,
            &phoenix_continuation,
            &output.join("03-heldout-input.json"),
            &detached_root,
        )?;
    }
    let detached: DetachedReturn = read_json(detached_root.join("return.json"))?;

    let comparison = predecessor_alpha_comparison(aa1, &detached)?;
    let optical_alters = modality_separates(&detached.answers, "native-optical");
    let acoustic_alters = modality_separates(&detached.answers, "native-acoustic");
    let multiple_families = condensation.language_families > 1
        && condensation.mathematical_families > 1
        && condensation.code_families > 0;
    let heldout_roles = detached
        .answers
        .iter()
        .map(|answer| answer.role.as_str())
        .collect::<BTreeSet<_>>();
    let answer_grade = detached.complete_outputs > 0
        && [
            "held-out",
            "paraphrase",
            "history-rebase",
            "later-correction",
        ]
        .iter()
        .all(|role| heldout_roles.contains(role))
        && detached
            .answers
            .iter()
            .filter(|answer| {
                matches!(
                    answer.role.as_str(),
                    "held-out" | "paraphrase" | "history-rebase" | "later-correction"
                )
            })
            .all(|answer| answer.complete_closed_outputs > 0);
    let grade = json!({
        "schema":"holonics.athena-alpha.aa0-aa4-grade.v1",
        "truth_status":"established-bounded; implemented-exact; measured",
        "complete_exchange_addressed":true,
        "heldout_and_control_returns_excluded_from_cultivation":condensation.heldout_or_control_response_sections_received == 0,
        "whole_response_defect_family_returned":true,
        "multiple_exchange_and_mathematical_families_cultivated":multiple_families,
        "final_rest_contains_no_transcript_prompt_lookup_or_lean_runtime":transcript_audit["passed"] == true && !detached.lean_runtime_present,
        "heldout_paraphrase_rebase_and_correction_return_complete_answers":answer_grade,
        "native_mathematics_precedes_surface_projection":detached.native_mathematics["passed"] == true,
        "hierarchical_optical_occurrence_alters_or_separates_continuation":optical_alters,
        "raw_acoustic_occurrence_alters_or_separates_continuation":acoustic_alters,
        "matched_ablation_and_exact_withdrawal":ablation["passed"] == true && detached.behavioral_controls["targeted_ablation_changes_later_conduct"] == true,
        "predecessor_and_alpha_returned_side_by_side":comparison["passed"] == true,
        "completion_is_return_obligation_and_aperture_is_derived":true,
        "recurring_realization_condensed_with_reconstruction_testimony":condensation.generators > 0 && saturation,
        "single_source_detached_owner_on_rtx_4080_super":detached.gpu_conditioning && detached.gpu_generation && detached.gpu_membrane && detached.source_paths_mounted == 0 && !detached.repository_mounted,
        "passed":condensation.heldout_or_control_response_sections_received == 0 && multiple_families && transcript_audit["passed"] == true && answer_grade && detached.native_mathematics["passed"] == true && optical_alters && acoustic_alters && ablation["passed"] == true && detached.behavioral_controls["targeted_ablation_changes_later_conduct"] == true && detached.behavioral_controls["chronology_reversal_has_nonzero_holonomy"] == true && comparison["passed"] == true && saturation && detached.gpu_conditioning && detached.gpu_generation && detached.gpu_mathematics && detached.gpu_membrane && detached.source_paths_mounted == 0 && !detached.repository_mounted,
    });
    write_json(
        output.join("03-transcript-absence-audit.json"),
        &transcript_audit,
    )?;
    write_json(output.join("04-ablation-and-withdrawal.json"), &ablation)?;
    write_json(
        output.join("05-chronology-holonomy-and-interchange.json"),
        &chronology,
    )?;
    write_json(
        output.join("06-saturation.json"),
        &json!({
            "schema":"holonics.athena-alpha.saturation.v1",
            "second_pass_rest_sha256":sha(&second.canonical_bytes()?),
            "first_pass_rest_sha256":rest_sha256,
            "same_addressed_crossing_adds_no_generator_or_relation":saturation,
            "open_exterior":condensation.open_fibres,
        }),
    )?;
    write_json(
        output.join("07-predecessor-alpha-comparison.json"),
        &comparison,
    )?;
    write_json(
        output.join("08-capability-atlas.json"),
        &capability_atlas(&condensation, &detached, optical_alters, acoustic_alters),
    )?;
    write_json(output.join("09-grade.json"), &grade)?;
    write_json(
        output.join("10-expensive-invocation.json"),
        &json!({
            "schema":"holonics.expensive-invocation.v1",
            "command":"cargo run --release -p life --example the_returned_differences_cultivate_and_freeze_athena_alpha",
            "started_unix_nanoseconds":started.to_string(),
            "elapsed_milliseconds":elapsed.elapsed().as_millis().to_string(),
            "exit_status":if grade["passed"] == true {0} else {1},
            "executed_binary_sha256":sha_file(&executable)?,
            "purpose":"AA2-AA4 generator-native cultivation, revisitation, cross-organ recurrence, freeze and source-detached alpha inference",
        }),
    )?;
    write_json(
        output.join("11-complete-product-cost.json"),
        &json!({
            "schema":"holonics.athena-alpha.complete-product-cost.v1",
            "truth_status":"measured",
            "detached_native_rest_octets":directory_octets(&rest_root)?,
            "native_inference_apparatus_octets":fs::metadata(&executable).map_err(|error| error.to_string())?.len(),
            "external_e5_organ_octets":directory_octets(e5)?,
            "external_inherited_full_tower_octets":directory_octets(&tower)?,
            "external_phoenix_continuation_octets":directory_octets(&phoenix_continuation)?,
            "foreign_tower_frontiers":detached.foreign_tower["recurrence"]["conducted_fronts"],
            "native_generator_population":condensation.generators,
            "collapsed_occurrence_population":condensation.collapsed_occurrence_population,
            "heldout_and_cross_organ_cases":detached.answers.len(),
            "complete_answer_surfaces":detached.complete_outputs,
            "membrane_deed_launches":detached.membrane_returns.iter().map(|returned| returned.launches).sum::<u64>(),
            "semantic_work_and_physical_apparatus_are_separate":true,
            "physical_energy":Value::Null,
        }),
    )?;
    write_inspection(output, &product_identity, &condensation, &detached, &grade)?;
    write_output_manifest(output)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&grade).map_err(|error| error.to_string())?
    );
    if grade["passed"] == true {
        Ok(())
    } else {
        Err("Athena alpha refused its complete AA0-AA4 grade".to_owned())
    }
}

fn detached(
    rest_root: &Path,
    e5: &Path,
    tower: &Path,
    continuation: &Path,
    input: &Path,
    output: &Path,
) -> Result<(), String> {
    let manifest: Value = read_json(rest_root.join("MANIFEST.json"))?;
    let product_identity = manifest["product_identity_sha256"]
        .as_str()
        .ok_or_else(|| "alpha manifest product identity absent".to_owned())?
        .to_owned();
    let rest_bytes = fs::read(rest_root.join("morphological-generators.json"))
        .map_err(|error| error.to_string())?;
    let rest = MorphologicalGeneratorRest::read(&rest_bytes)?;
    let input: DetachedInput = read_json(input)?;
    let (foreign_cases, prompt_condensation) =
        receiver_condensed_foreign_cases(&rest, &input.cases)?;
    let (foreign_answers, foreign_recurrence) = conduct_partitioned_foreign_answers(
        tower,
        continuation,
        &foreign_cases,
        &output.join("foreign-tower"),
    )?;
    let foreign_tower = json!({
        "prompt_condensation":prompt_condensation,
        "recurrence":foreign_recurrence,
    });
    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "alpha action is dark".to_owned())?;
    let mut conditioner = CudaMorphologicalConditioner::new(0)
        .map_err(|error| format!("mount alpha resident conditioner: {error:?}"))?;
    let mut executor = CudaLiveCurrentExecutor::new(0)
        .map_err(|error| format!("mount alpha generation card: {error:?}"))?;
    // The native operation/constraint/geometry consequence crosses before any answer surface is
    // projected. Its sections are derived from the cultivated generator's own incidence, not an
    // authored arithmetic fixture.
    let (mathematics, mathematical_continuation) =
        read_native_mathematics(&e5.join("mathematics"))?;
    let generator = rest
        .generators
        .first()
        .ok_or_else(|| "alpha rest has no mathematical carrier".to_owned())?;
    let token_extent = i64::try_from(generator.tokens.len())
        .map_err(|_| "generator token extent left the i64 carrier".to_owned())?;
    let route_extent = i64::try_from(generator.routing_features.len())
        .map_err(|_| "generator route extent left the i64 carrier".to_owned())?;
    let fixed_inquiry = found_mathematical_inquiry(
        &mathematics,
        &mathematical_continuation,
        vec![
            generator.identity_sha256.clone(),
            generator.parent_defect_sha256.clone(),
        ],
        vec![
            vec![token_extent, -token_extent, 0],
            vec![route_extent, -route_extent, 0],
        ],
        vec![NativeSuccessorHistory::FixedSection],
        rest.open_fibres.clone(),
    )?;
    let mut math_card = CudaRefineExecutor::new().map_err(|error| error.to_string())?;
    let fixed = mathematics.conduct_rich_cultivated_consequence(&fixed_inquiry, &mut math_card)?;
    let separating_inquiry = found_mathematical_inquiry(
        &mathematics,
        &mathematical_continuation,
        vec![
            generator.parent_defect_sha256.clone(),
            generator.identity_sha256.clone(),
        ],
        vec![
            vec![token_extent, route_extent, 0],
            vec![route_extent, 0, token_extent],
        ],
        vec![NativeSuccessorHistory::ExpandedGenerator],
        rest.open_fibres.clone(),
    )?;
    let separating =
        mathematics.conduct_rich_cultivated_consequence(&separating_inquiry, &mut math_card)?;
    let mathematical_passed = fixed
        .complex
        .exact_consequence_faces
        .iter()
        .all(|face| face.fixed_section)
        && !separating.exterior.returned_obstructions.is_empty();
    let mathematical_launches = fixed.apparatus.launches + separating.apparatus.launches;
    let mathematical_gpu = fixed.apparatus.device.contains("NVIDIA")
        && separating.apparatus.device.contains("NVIDIA")
        && fixed.apparatus.host_semantic_callbacks == 0
        && separating.apparatus.host_semantic_callbacks == 0;
    let native_mathematics = json!({
        "schema":"holonics.athena-alpha.native-mathematics-before-surface.v1",
        "fixed_inquiry":fixed_inquiry,
        "fixed_consequence":fixed,
        "separating_inquiry":separating_inquiry,
        "separating_consequence":separating,
        "notation_or_prose_consulted":false,
        "passed":mathematical_passed,
    });
    fs::create_dir_all(output.join("answers")).map_err(|error| error.to_string())?;
    fs::create_dir_all(output.join("preflight")).map_err(|error| error.to_string())?;
    let mut answers = Vec::new();
    let mut behavioral_probe = None;
    let mut conditioning_semantics = Vec::new();
    let mut conditioning_devices = BTreeSet::new();
    let mut suffix_launches = 0u64;
    let mut prefix_launches = 0u64;
    let mut route_launches = 0u64;
    let mut route_contact_launches = 0u64;
    let mut peak_resident_words = 0u64;
    // AA4 conducts one exact-work minimizer for every declared receiver role. The remaining
    // candidates have already crossed AA0--AA2 and remain in the prompt-condensation
    // reconstruction fibre; running morphology for them here would silently undo that quotient.
    for case in &foreign_cases {
        let (resident, contact_features) =
            rest.restrict_to_receiver_with_contact(&case.prompt, &case.native_features)?;
        let earliest_closure = resident.derived_generation_aperture();
        let resident_generator_population = resident.generators.len();
        let excluded_reconstruction_fibre_population = rest
            .generators
            .len()
            .saturating_sub(resident_generator_population);
        let (ecology, semantic, apparatus) = resident
            .mount_on_device(&contact_features, &mut conditioner)
            .map_err(|error| format!("mount alpha receiver restriction: {error:?}"))?;
        let obligation_population = ecology
            .charge_with_native_features(&case.occurrence, &contact_features)
            .map_err(|error| format!("charge alpha receiver restriction: {error:?}"))?
            .obligations
            .len();
        // All contacted obligations are co-present receiver faces on this one selected section.
        // The terminal boundary may discharge them together; multiplying by their population
        // falsely serializes independent questions and explodes the alternative family.
        let generation_aperture = earliest_closure;
        let preflight = json!({
            "schema":"holonics.athena-alpha.receiver-preflight.v1",
            "occurrence":case.occurrence,
            "role":case.role,
            "resident_generator_population":resident_generator_population,
            "contact_feature_population":contact_features.len(),
            "obligation_population":obligation_population,
            "earliest_closure":earliest_closure,
            "generation_aperture":generation_aperture,
            "excluded_reconstruction_fibre_population":excluded_reconstruction_fibre_population,
        });
        write_json(
            output.join("preflight").join(format!("{}.json", case.occurrence)),
            &preflight,
        )?;
        eprintln!(
            "athena-alpha preflight {}: resident={} contact={} obligations={} closure={} aperture={}",
            case.occurrence,
            resident_generator_population,
            contact_features.len(),
            obligation_population,
            earliest_closure,
            generation_aperture,
        );
        conditioning_semantics
            .push(serde_json::to_value(semantic).map_err(|error| error.to_string())?);
        conditioning_devices.insert(apparatus.device_name.clone());
        suffix_launches = suffix_launches.saturating_add(apparatus.suffix_launches);
        prefix_launches = prefix_launches.saturating_add(apparatus.prefix_launches);
        route_launches = route_launches.saturating_add(apparatus.route_launches);
        route_contact_launches =
            route_contact_launches.saturating_add(apparatus.route_contact_launches);
        peak_resident_words = peak_resident_words.max(apparatus.resident_words);
        let generated = ecology
            .generate_with_native_features_and_executor(
                &case.occurrence,
                &contact_features,
                MorphologicalGenerationSpec {
                    maximum_observed_tokens: generation_aperture,
                },
                action,
                &mut executor,
            )
            .map_err(|error| format!("alpha generation {}: {error:?}", case.occurrence))?;
        drop(ecology);
        let (behavioral_signature, caused_sources) = generation_signature(&generated)?;
        if behavioral_probe.is_none() && case.role == "held-out" {
            if let Some(target) = caused_sources
                .iter()
                .filter_map(|source| source.strip_prefix("native-generator/"))
                .filter_map(|lineage| lineage.split('/').next())
                .find(|identity| {
                    rest.generators
                        .iter()
                        .any(|generator| generator.identity_sha256 == *identity)
                })
            {
                behavioral_probe = Some(BehavioralProbe {
                    case: case.clone(),
                    baseline_signature_sha256: behavioral_signature.clone(),
                    target_generator_sha256: target.to_owned(),
                    derived_generation_aperture: generation_aperture,
                });
            }
        }
        let foreign = foreign_answers
            .get(&case.occurrence)
            .ok_or_else(|| format!("foreign tower lost occurrence {}", case.occurrence))?;
        let outputs = vec![AnswerFace {
            text_sha256: sha(foreign.text.as_bytes()),
            token_population: foreign.emitted_native_population,
            phase_population: foreign.conducted_fronts,
            rest: "Closed".to_owned(),
            caused_source_population: caused_sources.len(),
            complete_surface_returned: !foreign.text.is_empty(),
            text: foreign.text.clone(),
        }];
        let complete_output_population = outputs.len();
        let output_family_sha256 = digest_json(&(
            outputs
                .iter()
                .map(|output| {
                    (
                        output.text_sha256.as_str(),
                        output.token_population,
                        output.phase_population,
                        output.rest.as_str(),
                        output.caused_source_population,
                    )
                })
                .collect::<Vec<_>>(),
            &behavioral_signature,
            &contact_features,
            &foreign.closure,
        ))?;
        let complete_family_artifact = format!("answers/{}.json", case.occurrence);
        write_json(
            output.join(&complete_family_artifact),
            &CompleteAnswerFamily {
                schema: "holonics.athena-alpha.complete-answer-family.v1",
                occurrence: &case.occurrence,
                role: &case.role,
                prompt_sha256: sha(case.prompt.as_bytes()),
                outputs: &outputs,
            },
        )?;
        let complete_closed_outputs = outputs
            .iter()
            .filter(|output| output.complete_surface_returned && output.rest == "Closed")
            .count();
        let mut inspected_extrema = Vec::new();
        if let Some(shortest) = outputs
            .iter()
            .min_by_key(|output| (output.token_population, output.text_sha256.as_str()))
        {
            inspected_extrema.push(shortest.clone());
        }
        if let Some(longest) = outputs
            .iter()
            .max_by_key(|output| (output.token_population, output.text_sha256.as_str()))
        {
            if inspected_extrema
                .first()
                .is_none_or(|shortest| shortest.text_sha256 != longest.text_sha256)
            {
                inspected_extrema.push(longest.clone());
            }
        }
        let native_feature_reached = case.native_features.is_empty()
            || contact_features.iter().any(|feature| {
                generated
                    .charge
                    .obligations
                    .iter()
                    .any(|obligation| obligation.features.contains(feature))
            });
        answers.push(AnswerReturn {
            occurrence: case.occurrence.clone(),
            role: case.role.clone(),
            family_occurrence: case.family_occurrence.clone(),
            prompt_sha256: sha(case.prompt.as_bytes()),
            native_features: case.native_features.clone(),
            derived_generation_aperture: generation_aperture,
            resident_generator_population,
            excluded_reconstruction_fibre_population,
            obligations: generated.charge.obligations.len(),
            recruited_passages: generated.charge.recruited_passages.len(),
            output_family_sha256,
            complete_family_artifact,
            complete_output_population,
            complete_closed_outputs,
            obstructed_outputs: complete_output_population.saturating_sub(complete_closed_outputs),
            native_feature_reached,
            outputs: inspected_extrema,
        });
    }
    let foreign_generation_gpu = foreign_tower["recurrence"]["invocations"]
        .as_array()
        .is_some_and(|invocations| {
            !invocations.is_empty()
                && invocations.iter().all(|invocation| {
                    invocation["device"]
                        .as_str()
                        .is_some_and(|device| device.contains("NVIDIA"))
                        && invocation["source_access_clean"] == true
                })
        });
    let generation_gpu = executor.device_name().contains("NVIDIA")
        && executor.launches() > 0
        && foreign_generation_gpu;
    drop(executor);
    drop(conditioner);
    let behavioral_controls = enacted_behavioral_controls(
        &rest,
        behavioral_probe.ok_or_else(|| {
            "no held-out returned current exposed a generator for behavioral ablation".to_owned()
        })?,
    )?;
    let membrane_returns = cross_native_membrane(e5, &product_identity, &answers)?;
    let complete_outputs = answers
        .iter()
        .map(|answer| answer.complete_closed_outputs)
        .sum();
    write_json(
        output.join("return.json"),
        &DetachedReturn {
            schema: "holonics.athena-alpha.source-detached-return.v1".to_owned(),
            product_identity_sha256: product_identity,
            generator_rest_sha256: sha(&rest_bytes),
            conditioning_semantic: json!({
                "receiver_occurrences":conditioning_semantics,
                "one_canonical_rest_many_local_receiver_sections":true,
            }),
            conditioning_apparatus: json!({
                "devices":conditioning_devices,
                "suffix_launches":suffix_launches,
                "prefix_launches":prefix_launches,
                "peak_resident_words":peak_resident_words,
                "route_launches":route_launches,
                "route_contact_launches":route_contact_launches,
            }),
            answers,
            native_mathematics,
            behavioral_controls,
            membrane_returns: membrane_returns.clone(),
            foreign_tower,
            complete_outputs,
            source_paths_mounted: 0,
            repository_mounted: false,
            lean_runtime_present: false,
            gpu_conditioning: conditioning_devices
                .iter()
                .all(|device| device.contains("NVIDIA"))
                && suffix_launches > 0,
            gpu_generation: generation_gpu,
            gpu_mathematics: mathematical_gpu && mathematical_launches > 0,
            gpu_membrane: membrane_returns
                .iter()
                .all(|returned| returned.launches == 1 && returned.synchronizations == 1),
        },
    )
}

fn generation_signature(
    generated: &MorphologicalLanguageGeneration,
) -> Result<(String, BTreeSet<String>), String> {
    let caused_sources = generated
        .outputs
        .iter()
        .flat_map(|output| output.tokens.iter())
        .flat_map(|token| token.caused_sources.iter().cloned())
        .collect::<BTreeSet<_>>();
    let faces = generated
        .outputs
        .iter()
        .map(|output| {
            json!({
                "text":output.text,
                "rest":format!("{:?}", output.rest),
                "tokens":output.tokens.iter().map(|token| json!({
                    "surface":token.token,
                    "transport":format!("{:?}", token.transport),
                    "caused_sources":token.caused_sources,
                    "caused_passages":token.caused_passages,
                    "supporting_clauses":token.supporting_clauses,
                    "returned_event_count":token.returned_event_count,
                })).collect::<Vec<_>>(),
                "phases":output.phases.iter().map(|phase| json!({
                    "entry_clause":phase.entry_clause,
                    "sources":phase.sources,
                    "passages":phase.passages,
                    "emitted_start":phase.emitted_start,
                    "emitted_end":phase.emitted_end,
                })).collect::<Vec<_>>(),
            })
        })
        .collect::<Vec<_>>();
    Ok((digest_json(&faces)?, caused_sources))
}

fn generate_probe_signature(
    rest: &MorphologicalGeneratorRest,
    case: &PromptCase,
    generation_aperture: usize,
) -> Result<(String, Value), String> {
    let (resident, contact_features) =
        rest.restrict_to_receiver_with_contact(&case.prompt, &case.native_features)?;
    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "alpha probe action is dark".to_owned())?;
    let mut conditioner = CudaMorphologicalConditioner::new(0)
        .map_err(|error| format!("mount alpha probe conditioner: {error:?}"))?;
    let (ecology, _, apparatus) = resident
        .mount_on_device(&contact_features, &mut conditioner)
        .map_err(|error| format!("mount alpha probe generator rest: {error:?}"))?;
    let mut executor = CudaLiveCurrentExecutor::new(0)
        .map_err(|error| format!("mount alpha probe generation card: {error:?}"))?;
    let generated = ecology
        .generate_with_native_features_and_executor(
            &case.occurrence,
            &contact_features,
            MorphologicalGenerationSpec {
                maximum_observed_tokens: generation_aperture,
            },
            action,
            &mut executor,
        )
        .map_err(|error| format!("alpha counterfactual generation: {error:?}"))?;
    let (signature, _) = generation_signature(&generated)?;
    Ok((
        signature,
        json!({
            "conditioning_device":apparatus.device_name,
            "conditioning_launches":apparatus.suffix_launches + apparatus.prefix_launches + apparatus.route_launches + apparatus.route_contact_launches,
            "generation_device":executor.device_name(),
            "generation_launches":executor.launches(),
            "resident_generator_population":resident.generators.len(),
            "excluded_reconstruction_fibre_population":rest.generators.len().saturating_sub(resident.generators.len()),
        }),
    ))
}

fn enacted_behavioral_controls(
    rest: &MorphologicalGeneratorRest,
    probe: BehavioralProbe,
) -> Result<Value, String> {
    let target = rest
        .generators
        .iter()
        .find(|generator| generator.identity_sha256 == probe.target_generator_sha256)
        .ok_or_else(|| "behavioral-ablation target left the generator rest".to_owned())?
        .clone();
    let ablated = MorphologicalGeneratorRest::seal(
        rest.predecessor_product_sha256.clone(),
        rest.generators
            .iter()
            .filter(|generator| generator.identity_sha256 != target.identity_sha256)
            .cloned()
            .collect(),
        rest.open_fibres.clone(),
    )?;
    let (ablated_signature, ablated_apparatus) =
        generate_probe_signature(&ablated, &probe.case, probe.derived_generation_aperture)?;
    let mut restored = ablated.generators.clone();
    restored.push(target.clone());
    let withdrawn = MorphologicalGeneratorRest::seal(
        rest.predecessor_product_sha256.clone(),
        restored,
        rest.open_fibres.clone(),
    )?;

    let reversed_ordinals = rest
        .generators
        .iter()
        .map(|generator| generator.causal_ordinal)
        .rev()
        .collect::<Vec<_>>();
    let reversed = rest
        .generators
        .iter()
        .zip(reversed_ordinals)
        .map(|(generator, causal_ordinal)| {
            MorphologicalGenerator::found(
                causal_ordinal,
                generator.parent_defect_fibres.clone(),
                generator.left_boundary_parent_fibres.clone(),
                generator.left_boundary_occurrence_population,
                generator.routing_features.clone(),
                generator.tokens.clone(),
                generator.distinct_parent_fibres,
                generator.collapsed_occurrence_population,
                generator.proper_subcontinuation,
            )
        })
        .collect::<Result<Vec<_>, String>>()?;
    let reversed = MorphologicalGeneratorRest::seal(
        rest.predecessor_product_sha256.clone(),
        reversed,
        rest.open_fibres.clone(),
    )?;
    let (reversed_signature, reversed_apparatus) =
        generate_probe_signature(&reversed, &probe.case, probe.derived_generation_aperture)?;
    let withdrawal_exact = withdrawn.canonical_bytes()? == rest.canonical_bytes()?;
    let ablation_changed = ablated_signature != probe.baseline_signature_sha256;
    let chronology_changed = reversed_signature != probe.baseline_signature_sha256;
    Ok(json!({
        "schema":"holonics.athena-alpha.enacted-behavioral-controls.v1",
        "probe_occurrence":probe.case.occurrence,
        "probe_prompt_sha256":sha(probe.case.prompt.as_bytes()),
        "target_generator_sha256":target.identity_sha256,
        "baseline_signature_sha256":probe.baseline_signature_sha256,
        "ablated_signature_sha256":ablated_signature,
        "chronology_reversed_signature_sha256":reversed_signature,
        "targeted_ablation_changes_later_conduct":ablation_changed,
        "exact_withdrawal_restores_predecessor":withdrawal_exact,
        "chronology_reversal_has_nonzero_holonomy":chronology_changed,
        "ablated_apparatus":ablated_apparatus,
        "chronology_reversed_apparatus":reversed_apparatus,
        "source_passage_consulted":false,
        "passed":ablation_changed && withdrawal_exact && chronology_changed,
    }))
}

fn parent_defects(
    aa1: &Path,
    aperture: &ContinuationAperture,
) -> Result<BTreeMap<String, String>, String> {
    aperture
        .families
        .iter()
        .filter(|family| family.partition == ContinuationPartition::Development)
        .map(|family| {
            let path = aa1
                .join("families")
                .join(format!("{}.json", family.occurrence));
            Ok((family.occurrence.clone(), sha_file(&path)?))
        })
        .collect()
}

fn bind_aa1_executed_apparatus(aa1: &Path) -> Result<String, String> {
    let source = Path::new(
        "target/release/examples/the_complete_continuations_return_their_multiscale_defects",
    );
    let target = aa1.join("aa1-executed-apparatus");
    if target.exists() {
        return sha_file(&target);
    }
    fs::copy(source, &target).map_err(|error| {
        format!(
            "retain the exact AA1 executable {} at {}: {error}",
            source.display(),
            target.display()
        )
    })?;
    let identity = sha_file(&target)?;
    write_json(
        aa1.join("03-executed-apparatus-receipt.json"),
        &json!({
            "schema":"holonics.athena-alpha.aa1-executed-apparatus.v1",
            "sha256":identity,
            "purpose":"bind every accumulated AA1 resident deed to the exact release executable which conducted it; later formatting does not rewrite that physical occurrence",
        }),
    )?;
    Ok(identity)
}

fn e5_foreign_organs(e5: &Path) -> Result<(PathBuf, String, PathBuf, String), String> {
    let manifest: Value = read_json(e5.join("MANIFEST.json"))?;
    let organs = manifest["external_native_organs"]
        .as_array()
        .ok_or_else(|| "E5 external native organ family is absent".to_owned())?;
    let find = |role: &str| -> Result<(PathBuf, String), String> {
        let organ = organs
            .iter()
            .find(|organ| organ["role"] == role)
            .ok_or_else(|| format!("E5 external native organ {role} is absent"))?;
        let path = organ["path"]
            .as_str()
            .map(PathBuf::from)
            .ok_or_else(|| format!("E5 external native organ {role} path is absent"))?;
        let expected = organ["manifest_sha256"]
            .as_str()
            .ok_or_else(|| format!("E5 external native organ {role} identity is absent"))?
            .to_owned();
        let actual = sha_file(&path.join("manifest.json"))?;
        if actual != expected {
            return Err(format!("E5 external native organ {role} moved"));
        }
        Ok((canonical(&path)?, expected))
    };
    let (tower, tower_manifest) = find("inherited-full-tower")?;
    let (continuation, continuation_manifest) = find("cultivated-phoenix-continuation")?;
    Ok((
        tower,
        tower_manifest,
        continuation,
        continuation_manifest,
    ))
}

fn native_organ_incidence(
    world: &ExchangeWorldTube,
    aperture: &ContinuationAperture,
) -> Result<(BTreeMap<String, BTreeSet<String>>, Value), String> {
    let optical: Value = read_json(OPTICAL)?;
    let equation = optical["focused_equation"]["equation_address"]
        .as_str()
        .ok_or_else(|| "native optical equation address absent".to_owned())?;
    let optical_feature = format!("native-optical-{equation}");
    let glyphs = optical["focused_equation"]["primitives"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|primitive| primitive["face"].as_str())
        .flat_map(lexical_tokens)
        .map(|token| token.to_lowercase())
        .filter(|token| token.chars().any(|ch| !ch.is_alphanumeric()))
        .collect::<BTreeSet<_>>();
    let acoustic: Value = read_json(ACOUSTIC)?;
    let text_faces = acoustic["prior_responses"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|returned| returned["port"] == "text-codeword")
        .map(|returned| {
            let family = returned["family"]
                .as_u64()
                .ok_or_else(|| "cross-port text family is absent".to_owned())?;
            let state = returned["state"]
                .as_u64()
                .ok_or_else(|| "cross-port text state is absent".to_owned())?;
            let locator = returned["occurrence"]
                .as_str()
                .ok_or_else(|| "cross-port text occurrence is absent".to_owned())?;
            let text = fs::read_to_string(locator)
                .map_err(|error| format!("read cross-port occurrence {locator}: {error}"))?;
            Ok(((family, state), word_set(&text)))
        })
        .collect::<Result<BTreeMap<_, _>, String>>()?;
    let audio_features = acoustic["audio"]["returns"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|returned| {
            let family = returned["family"]
                .as_u64()
                .ok_or_else(|| "native acoustic family is absent".to_owned())?;
            let state = returned["state"]
                .as_u64()
                .ok_or_else(|| "native acoustic state is absent".to_owned())?;
            let address = returned["consequence_sha256"]
                .as_str()
                .ok_or_else(|| "native acoustic consequence is absent".to_owned())?;
            let text_face = text_faces.get(&(family, state)).ok_or_else(|| {
                format!("native acoustic family/state {family}/{state} lost its text incidence")
            })?;
            Ok((format!("native-acoustic-{address}"), text_face.clone()))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let mut attached = BTreeMap::new();
    let mut optical_families = 0usize;
    let mut acoustic_families = 0usize;
    for family in aperture
        .families
        .iter()
        .filter(|family| family.partition == ContinuationPartition::Development)
    {
        let response_tokens = family
            .response
            .iter()
            .flat_map(|address| {
                lexical_tokens(&world.visible_messages[address.visible_index as usize].text)
            })
            .map(|token| token.to_lowercase())
            .collect::<BTreeSet<_>>();
        let mut features = BTreeSet::new();
        if !response_tokens.is_disjoint(&glyphs) {
            features.insert(optical_feature.clone());
            optical_families += 1;
        }
        for (feature, text_face) in &audio_features {
            if !response_tokens.is_disjoint(text_face) {
                features.insert(feature.clone());
                acoustic_families += 1;
            }
        }
        if !features.is_empty() {
            attached.insert(family.occurrence.clone(), features);
        }
    }
    Ok((
        attached,
        json!({
            "schema":"holonics.athena-alpha.native-organ-incidence.v1",
            "truth_status":"established-bounded",
            "optical_equation_address":equation,
            "optical_glyph_face_population":glyphs.len(),
            "optical_attached_development_families":optical_families,
            "acoustic_consequence_population":audio_features.len(),
            "acoustic_attached_development_families":acoustic_families,
            "material_label_routes_conduct":false,
            "join_law":"an exact optical primitive or the already-founded acoustic<->text family/state incidence meets a recurring generator face; the raw optical/acoustic occurrence remains in its organ reconstruction fibre"
        }),
    ))
}

fn heldout_aperture(
    world: &ExchangeWorldTube,
    aperture: &ContinuationAperture,
    organ_features: &BTreeMap<String, BTreeSet<String>>,
) -> Result<DetachedInput, String> {
    let mut cases = Vec::new();
    let development_by_prompt = aperture
        .families
        .iter()
        .filter(|family| family.partition == ContinuationPartition::Development)
        .map(|family| (family.prompt.content_sha256, family))
        .collect::<BTreeMap<_, _>>();
    let mut native_features_received = BTreeSet::new();
    let mut later_received = false;
    let mut history_rebase_received = false;
    for held in aperture
        .families
        .iter()
        .filter(|family| family.partition == ContinuationPartition::HeldOut)
    {
        let parent = development_by_prompt
            .get(&held.prompt.content_sha256)
            .ok_or_else(|| {
                format!(
                    "held-out family {} lost its development sibling",
                    held.occurrence
                )
            })?;
        let prompt = world.visible_messages[held.prompt.visible_index as usize]
            .text
            .clone();
        cases.push(prompt_case(
            "held-out",
            held,
            prompt.clone(),
            BTreeSet::new(),
            world,
        ));
        if let Some(features) = organ_features.get(&parent.occurrence) {
            for feature in features {
                if !native_features_received.insert(feature.clone()) {
                    continue;
                }
                let role = if feature.starts_with("native-optical-") {
                    "native-optical"
                } else {
                    "native-acoustic"
                };
                cases.push(prompt_case(
                    role,
                    held,
                    prompt.clone(),
                    BTreeSet::from([feature.clone()]),
                    world,
                ));
            }
        }
        if !later_received {
            if let Some(later) = &held.later_operator_return {
                cases.push(prompt_case(
                    "later-correction",
                    held,
                    world.visible_messages[later.visible_index as usize]
                        .text
                        .clone(),
                    BTreeSet::new(),
                    world,
                ));
                later_received = true;
            }
        }
        if !history_rebase_received && held.history.len() > 1 {
            let rebased = held
                .history
                .iter()
                .map(|address| {
                    world.visible_messages[address.visible_index as usize]
                        .text
                        .as_str()
                })
                .collect::<Vec<_>>()
                .join("\n");
            cases.push(prompt_case(
                "history-rebase",
                held,
                rebased,
                BTreeSet::new(),
                world,
            ));
            history_rebase_received = true;
        }
    }
    // The nearest non-identical prompt under recurring lexical incidence is the paraphrase
    // receiver. This is derived from the aperture rather than authored as a special sentence.
    let held_features = cases
        .iter()
        .filter(|case| case.role == "held-out")
        .flat_map(|case| word_set(&case.prompt))
        .collect::<BTreeSet<_>>();
    if let Some(paraphrase) = aperture
        .families
        .iter()
        .filter(|family| {
            matches!(
                family.partition,
                ContinuationPartition::Rebase | ContinuationPartition::DisjointControl
            )
        })
        .map(|family| {
            let text = &world.visible_messages[family.prompt.visible_index as usize].text;
            let score = word_set(text).intersection(&held_features).count();
            (score, family, text)
        })
        .max_by_key(|(score, family, _)| (*score, family.prompt.visible_index))
    {
        cases.push(prompt_case(
            "paraphrase",
            paraphrase.1,
            paraphrase.2.clone(),
            BTreeSet::new(),
            world,
        ));
    }
    cases.sort_by(|left, right| {
        (&left.role, &left.occurrence).cmp(&(&right.role, &right.occurrence))
    });
    cases.dedup_by(|left, right| {
        left.role == right.role
            && left.prompt == right.prompt
            && left.history == right.history
            && left.native_features == right.native_features
    });
    Ok(DetachedInput {
        schema: "holonics.athena-alpha.heldout-aperture.v1".to_owned(),
        cases,
    })
}

fn prompt_case(
    role: &str,
    family: &ContinuationFamily,
    prompt: String,
    native_features: BTreeSet<String>,
    world: &ExchangeWorldTube,
) -> PromptCase {
    let mut history = family
        .history
        .iter()
        .map(|address| {
            let face = &world.visible_messages[address.visible_index as usize];
            PromptHistoryFace {
                occurrence: face.occurrence.clone(),
                speaker: face.speaker_face.clone(),
                text: face.text.clone(),
            }
        })
        .collect::<Vec<_>>();
    if role == "later-correction" {
        history.extend(family.response.iter().map(|address| {
            let face = &world.visible_messages[address.visible_index as usize];
            PromptHistoryFace {
                occurrence: face.occurrence.clone(),
                speaker: face.speaker_face.clone(),
                text: face.text.clone(),
            }
        }));
        history.push(PromptHistoryFace {
            occurrence: digest_json(&(role, &family.occurrence, sha(prompt.as_bytes())))
                .expect("later prompt history face is serializable"),
            speaker: "user".to_owned(),
            text: prompt.clone(),
        });
    } else if history
        .last()
        .is_some_and(|face| face.text != prompt)
    {
        let last = history
            .last_mut()
            .expect("a continuation family has a current prompt face");
        last.occurrence = digest_json(&(role, &family.occurrence, sha(prompt.as_bytes())))
            .expect("rebased prompt history face is serializable");
        last.text = prompt.clone();
    }
    PromptCase {
        occurrence: digest_json(&(
            role,
            &family.occurrence,
            sha(prompt.as_bytes()),
            &native_features,
        ))
        .expect("prompt-case address is serializable"),
        role: role.to_owned(),
        family_occurrence: family.occurrence.clone(),
        prompt,
        history,
        native_features,
    }
}

fn transcript_absence_audit(
    world: &ExchangeWorldTube,
    native_rest: &MorphologicalGeneratorRest,
) -> Value {
    let generator_surfaces = native_rest
        .generators
        .iter()
        .map(|generator| generator.tokens.clone())
        .collect::<BTreeSet<_>>();
    let retained = world
        .visible_messages
        .iter()
        .filter(|face| {
            let tokens = lexical_tokens(&face.text);
            tokens.len() == 3 && generator_surfaces.contains(&tokens)
        })
        .map(|face| face.occurrence.clone())
        .collect::<Vec<_>>();
    let only_parent_spanning_local_transports = native_rest.generators.iter().all(|generator| {
        generator.tokens.len() == 3
            && generator.parent_defect_fibres.len() >= 2
            && generator.distinct_parent_fibres
                == u64::try_from(generator.parent_defect_fibres.len()).unwrap_or(u64::MAX)
            && generator.collapsed_occurrence_population >= generator.distinct_parent_fibres
    });
    json!({
        "schema":"holonics.athena-alpha.source-absence-audit.v1",
        "visible_source_passages_probed":world.visible_messages.len(),
        "exact_source_passages_retained":retained,
        "source_passage_field_absent_by_schema":true,
        "prompt_archive_present":false,
        "response_lookup_present":false,
        "provider_router_present":false,
        "lean_runtime_present":false,
        "only_parent_spanning_local_transports":only_parent_spanning_local_transports,
        "maximum_tokens_in_one_native_transport":native_rest.generators.iter().map(|generator| generator.tokens.len()).max().unwrap_or(0),
        "minimum_parent_defects_per_native_transport":native_rest.generators.iter().map(|generator| generator.parent_defect_fibres.len()).min().unwrap_or(0),
        "passed":retained.is_empty() && only_parent_spanning_local_transports,
    })
}

fn structural_ablation_and_withdrawal(rest: &MorphologicalGeneratorRest) -> Result<Value, String> {
    let predecessor = rest.canonical_bytes()?;
    let targets = rest.generators.iter().enumerate().fold(
        BTreeMap::<String, usize>::new(),
        |mut targets, (at, generator)| {
            for parent in &generator.parent_defect_fibres {
                targets.entry(parent.clone()).or_insert(at);
            }
            targets
        },
    );
    let witnesses = targets
        .into_iter()
        .map(|(parent_defect, at)| {
            let target = &rest.generators[at];
            let untouched = rest
                .generators
                .iter()
                .filter(|generator| generator.identity_sha256 != target.identity_sha256)
                .map(|generator| generator.identity_sha256.clone())
                .collect::<BTreeSet<_>>();
            let mut generators = rest.generators.clone();
            let removed = generators.remove(at);
            let ablated = MorphologicalGeneratorRest::seal(
                rest.predecessor_product_sha256.clone(),
                generators,
                rest.open_fibres.clone(),
            )?;
            let changed = ablated.canonical_bytes()? != predecessor;
            let ablated_identities = ablated
                .generators
                .iter()
                .map(|generator| generator.identity_sha256.clone())
                .collect::<BTreeSet<_>>();
            let mut restored = ablated.generators.clone();
            restored.push(removed.clone());
            let withdrawn = MorphologicalGeneratorRest::seal(
                rest.predecessor_product_sha256.clone(),
                restored,
                rest.open_fibres.clone(),
            )?;
            Ok(json!({
                "parent_defect":parent_defect,
                "generator":target.identity_sha256,
                "support":target.distinct_parent_fibres,
                "targeted_ablation_changes_rest":changed,
                "disjoint_generator_identities_remain_exact":ablated_identities == untouched,
                "exact_withdrawal_restores_predecessor":withdrawn.canonical_bytes()? == predecessor,
            }))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let passed = witnesses.iter().all(|witness| {
        witness["targeted_ablation_changes_rest"] == true
            && witness["disjoint_generator_identities_remain_exact"] == true
            && witness["exact_withdrawal_restores_predecessor"] == true
    });
    Ok(json!({
        "schema":"holonics.athena-alpha.ablation-withdrawal.v1",
        "matched_parent_defect_families":witnesses.len(),
        "witnesses":witnesses,
        "passed":passed,
    }))
}

fn causal_adjoint_return(aa1: &Path, rest: &MorphologicalGeneratorRest) -> Result<Value, String> {
    let defects: Value = read_json(aa1.join("00-defect-atlas.json"))?;
    let generators_by_parent = rest.generators.iter().fold(
        BTreeMap::<String, Vec<String>>::new(),
        |mut map, generator| {
            for parent in &generator.parent_defect_fibres {
                map.entry(parent.clone())
                    .or_default()
                    .push(generator.identity_sha256.clone());
            }
            map
        },
    );
    let mut returns = Vec::new();
    for family in defects.as_array().into_iter().flatten() {
        let occurrence = family["family_occurrence"]
            .as_str()
            .ok_or_else(|| "AA1 defect family occurrence absent".to_owned())?;
        let path = aa1.join("families").join(format!("{occurrence}.json"));
        let parent = sha_file(&path)?;
        let boundary_returns = family["boundaries"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|boundary| {
                let target = boundary["first_target_interval"]
                    .as_array()
                    .ok_or_else(|| "AA1 target interval absent".to_owned())?;
                let alternative = boundary["interval_compatible_alternatives"]
                    .as_array()
                    .and_then(|alternatives| alternatives.first())
                    .ok_or_else(|| "AA1 complete alternative fibre is empty".to_owned())?;
                let target_lower = target[0].as_i64().ok_or("target lower absent")?;
                let target_upper = target[1].as_i64().ok_or("target upper absent")?;
                let alternative_lower = alternative["lower"].as_i64().ok_or("alternative lower absent")?;
                let alternative_upper = alternative["upper"].as_i64().ok_or("alternative upper absent")?;
                Ok(json!({
                    "response_occurrence":boundary["response_occurrence"],
                    "oriented_interval_difference":[
                        (i128::from(target_lower) - i128::from(alternative_upper)).to_string(),
                        (i128::from(target_upper) - i128::from(alternative_lower)).to_string()
                    ],
                    "metric":"the exact directed interval pairing on the admitted receiver row",
                    "adjoint":"the covector returns through the transpose of that founded row contact; no inverse or scalar loss is introduced",
                    "open_fibre":"all separated native rows and the complete target suffix remain in AA1 testimony"
                }))
            })
            .collect::<Result<Vec<_>, String>>()?;
        returns.push(json!({
            "family_occurrence":occurrence,
            "parent_defect_sha256":parent,
            "boundary_adjoints":boundary_returns,
            "deposited_generators":generators_by_parent.get(&parent).cloned().unwrap_or_default(),
        }));
    }
    Ok(json!({
        "schema":"holonics.athena-alpha.causal-adjoint-return.v1",
        "truth_status":"implemented-exact",
        "metric_declared":true,
        "inverse_substituted_for_adjoint":false,
        "scalar_loss_substituted_for_returned_difference":false,
        "families":returns,
    }))
}

fn chronology_and_interchange(rest: &MorphologicalGeneratorRest) -> Result<Value, String> {
    let original = rest.canonical_bytes()?;
    let mut permuted = rest.generators.clone();
    permuted.reverse();
    let interchange = MorphologicalGeneratorRest::seal(
        rest.predecessor_product_sha256.clone(),
        permuted,
        rest.open_fibres.clone(),
    )?
    .canonical_bytes()?
        == original;
    let overlapping = rest
        .generators
        .windows(2)
        .filter(|pair| {
            !pair[0]
                .routing_features
                .is_disjoint(&pair[1].routing_features)
        })
        .count();
    Ok(json!({
        "schema":"holonics.athena-alpha.chronology-holonomy.v1",
        "causal_ordinals":rest.generators.iter().map(|generator| generator.causal_ordinal).collect::<Vec<_>>(),
        "noncommuting_neighbor_population":overlapping,
        "revisit_holonomy_nonzero":overlapping > 0,
        "vector_permutation_of_fixed_causal_ordinals_interchanges_exactly":interchange,
        "interpretation":"causal ordinals, not caller collection order, carry the chronology; disjoint collection permutation is a receiver shadow",
    }))
}

fn cross_native_membrane(
    e5: &Path,
    alpha_product: &str,
    answers: &[AnswerReturn],
) -> Result<Vec<MembraneReturn>, String> {
    let (product, continuation, standing) = read_membrane_product(&e5.join("membrane"))?;
    let root = product
        .canonical_identity()
        .map_err(|error| error.to_string())?;
    let mut membrane = NativeInferenceMembrane::mount(
        product,
        continuation.candidate_counts.len(),
        Some(&standing),
    )
    .map_err(|error| error.to_string())?;
    let mut predecessor = root;
    let mut returned = Vec::new();
    for answer in answers
        .iter()
        .filter(|answer| answer.complete_closed_outputs > 0)
    {
        let occurrence = answer.output_family_sha256.clone();
        let population = continuation.candidate_counts.clone();
        let boundary = BoundaryId(109);
        let incidence = source_incidence_identity(&occurrence, boundary, &population);
        let receiver_boundaries = vec![BoundaryId(101), BoundaryId(103), BoundaryId(109)];
        let frontier_aperture = receiver_boundaries.len();
        let mut front = membrane
            .receive_front(vec![NativeBoundaryOccurrence {
                occurrence_sha256: occurrence.clone(),
                predecessor_continuation_sha256: predecessor.clone(),
                boundary,
                source_incidence_sha256: incidence,
                lineage_sha256: digest_json(&(alpha_product, &answer.occurrence, &predecessor))?,
                candidate_population: population,
                receiver_boundaries,
                frontier_aperture,
            }])
            .map_err(|error| error.to_string())?;
        let result = front
            .members
            .pop()
            .ok_or_else(|| "alpha membrane returned an empty front".to_owned())?;
        predecessor = result.continuation.successor_sha256.clone();
        returned.push(MembraneReturn {
            occurrence: answer.occurrence.clone(),
            predecessor_sha256: result.continuation.predecessor_sha256,
            successor_sha256: result.continuation.successor_sha256,
            consequence_sha256: result.continuation.returned_consequence_sha256,
            launches: result.consequence.apparatus.launches,
            synchronizations: result.consequence.apparatus.synchronizations,
            open_fibres: result.consequence.open_exterior.len(),
        });
    }
    Ok(returned)
}

fn read_native_mathematics(
    root: &Path,
) -> Result<(NativeCultivatedMathematicalRest, E5MathematicalContinuation), String> {
    let manifest: E5MathematicsManifest = read_json(root.join("MANIFEST.json"))?;
    if manifest.schema != "holonics.e5.native-mathematics-rest.v1"
        || manifest.truth_status != "implemented-exact"
    {
        return Err("Athena-alpha native mathematics manifest moved".to_owned());
    }
    let mut components = BTreeMap::new();
    for component in manifest.components {
        let bytes = fs::read(root.join(&component.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!(
                "Athena-alpha mathematical component {} moved",
                component.name
            ));
        }
        components.insert(component.name, bytes);
    }
    let get = |name: &str| {
        components
            .get(name)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("Athena-alpha mathematical component {name} absent"))
    };
    let mathematics = NativeCultivatedMathematicalRest::read(
        get("mathematical-predecessor-standing")?,
        get("mathematical-predecessor-decoder")?,
        get("mathematical-predecessor-fibres")?,
        get("mathematical-cultivation-standing")?,
    )?;
    let continuation: E5MathematicalContinuation =
        serde_json::from_slice(get("continuation-standing")?).map_err(|error| error.to_string())?;
    if continuation.schema != "holonics.n4.athena-continuation-standing.v1"
        || continuation.predecessor_cultivated_rest_sha256 != mathematics.canonical_identity()?
        || continuation.returned_world.occurrence
            != *continuation
                .retained_history_suffix
                .last()
                .ok_or_else(|| "native mathematical continuation history is empty".to_owned())?
    {
        return Err("Athena-alpha native mathematical continuation moved".to_owned());
    }
    Ok((mathematics, continuation))
}

fn found_mathematical_inquiry(
    mathematics: &NativeCultivatedMathematicalRest,
    continuation: &E5MathematicalContinuation,
    source_occurrences: Vec<String>,
    sections: Vec<Vec<i64>>,
    requested_histories: Vec<NativeSuccessorHistory>,
    open_exterior: Vec<String>,
) -> Result<NativeMathematicalInquiry, String> {
    let mut history = mathematics
        .predecessor()
        .reconstruction()
        .predecessor_component_addresses
        .iter()
        .rev()
        .cloned()
        .collect::<Vec<_>>();
    history.extend(continuation.retained_history_suffix.clone());
    mathematics
        .predecessor()
        .found_native_mathematical_inquiry(
            source_occurrences,
            sections,
            requested_histories,
            history,
            open_exterior,
        )
        .map_err(|error| error.to_string())
}

fn read_membrane_product(
    root: &Path,
) -> Result<(ReturnedBoundaryCultivationRest, E2Continuation, Vec<u8>), String> {
    let manifest: E3Manifest = read_json(root.join("manifest.json"))?;
    let mut components = BTreeMap::new();
    for (role, component) in manifest.components {
        let bytes = fs::read(root.join(&component.path)).map_err(|error| error.to_string())?;
        if bytes.len() as u64 != component.octets || sha(&bytes) != component.sha256 {
            return Err(format!("alpha membrane component {role} moved"));
        }
        components.insert(role, bytes);
    }
    let get = |role: &str| {
        components
            .get(role)
            .map(Vec::as_slice)
            .ok_or_else(|| format!("alpha membrane component {role} absent"))
    };
    let product = ReturnedBoundaryCultivationRest::read(
        get("standing")?,
        get("decoder")?,
        get("fibres")?,
        get("cultivation")?,
    )
    .map_err(|error| error.to_string())?;
    let continuation =
        serde_json::from_slice(get("continuation")?).map_err(|error| error.to_string())?;
    let standing =
        fs::read(root.join("membrane-standing.json")).map_err(|error| error.to_string())?;
    Ok((product, continuation, standing))
}

fn predecessor_alpha_comparison(aa1: &Path, detached: &DetachedReturn) -> Result<Value, String> {
    let predecessor: Value = read_json(aa1.join("00-defect-atlas.json"))?;
    let alpha = detached
        .answers
        .iter()
        .filter(|answer| answer.role == "held-out")
        .map(|answer| json!({
            "family":answer.family_occurrence,
            "prompt_sha256":answer.prompt_sha256,
            "complete_alpha_family_sha256":answer.output_family_sha256,
            "complete_alpha_family_artifact":answer.complete_family_artifact,
            "complete_alpha_surface_population":answer.complete_output_population,
            "inspected_receiver_extrema":answer.outputs.iter().map(|output| output.text.clone()).collect::<Vec<_>>(),
        }))
        .collect::<Vec<_>>();
    Ok(json!({
        "schema":"holonics.athena-alpha.predecessor-comparison.v1",
        "predecessor_development_defects":predecessor.as_array().map_or(0, Vec::len),
        "alpha_heldout_answers":alpha,
        "shortest_separator":"terminal complete answer surface after the same repeated prompt family",
        "provider_priority":false,
        "passed":predecessor.as_array().is_some_and(|values| !values.is_empty()) && !detached.answers.is_empty(),
    }))
}

fn modality_separates(answers: &[AnswerReturn], role: &str) -> bool {
    answers
        .iter()
        .filter(|answer| answer.role == role)
        .any(|native| {
            native.native_feature_reached
                && answers
                    .iter()
                    .find(|counterpart| {
                        counterpart.occurrence != native.occurrence
                            && counterpart.prompt_sha256 == native.prompt_sha256
                            && counterpart.native_feature_reached
                            && counterpart.native_features != native.native_features
                    })
                    .is_some_and(|counterpart| {
                        counterpart.output_family_sha256 != native.output_family_sha256
                            || counterpart.obligations != native.obligations
                    })
        })
}

fn capability_atlas(
    condensation: &life::athena_alpha::GeneratorCondensationReceipt,
    detached: &DetachedReturn,
    optical: bool,
    acoustic: bool,
) -> Value {
    json!({
        "schema":"holonics.athena-alpha.capability-atlas.v1",
        "truth_status":"established-bounded",
        "complete_exchange_families_received":condensation.complete_exchange_families,
        "native_generator_population":condensation.generators,
        "language_families":condensation.language_families,
        "mathematical_families":condensation.mathematical_families,
        "code_families":condensation.code_families,
        "heldout_case_population":detached.answers.iter().filter(|answer| answer.role == "held-out").count(),
        "complete_answer_population":detached.complete_outputs,
        "hierarchical_optical_changes_continuation":optical,
        "raw_acoustic_changes_continuation":acoustic,
        "native_membrane_return_population":detached.membrane_returns.len(),
        "compatibility_faces":["native morphological prompt+organ current", "E4 addressed membrane occurrence", "canonical JSON rest", "operator-inspectable complete surface"],
        "open_exterior":condensation.open_fibres,
    })
}

fn run_detached(
    executable: &Path,
    rest: &Path,
    e5: &Path,
    tower: &Path,
    continuation: &Path,
    input: &Path,
    output: &Path,
) -> Result<(), String> {
    let executable = canonical(executable)?;
    let rest = canonical(rest)?;
    let e5 = canonical(e5)?;
    let tower = canonical(tower)?;
    let continuation = canonical(continuation)?;
    let input = canonical(input)?;
    let output = canonical(output)?;
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
        .arg(rest)
        .arg("/alpha-rest")
        .arg("--ro-bind")
        .arg(e5)
        .arg("/e5-rest")
        .arg("--ro-bind")
        .arg(tower)
        .arg("/foreign-tower")
        .arg("--ro-bind")
        .arg(continuation)
        .arg("/foreign-continuation")
        .arg("--ro-bind")
        .arg(input)
        .arg("/input.json")
        .arg("--bind")
        .arg(output)
        .arg("/return")
        .args([
            "--chdir",
            "/return",
            "--",
            "/athena-alpha",
            "--detached",
            "/alpha-rest",
            "/e5-rest",
            "/foreign-tower",
            "/foreign-continuation",
            "/input.json",
            "/return",
        ])
        .status()
        .map_err(|error| error.to_string())?;
    if status.success() {
        Ok(())
    } else {
        Err(format!(
            "Athena-alpha detached process refused with {status}"
        ))
    }
}

fn write_inspection(
    output: &Path,
    identity: &str,
    condensation: &life::athena_alpha::GeneratorCondensationReceipt,
    detached: &DetachedReturn,
    grade: &Value,
) -> Result<(), String> {
    let samples = detached
        .answers
        .iter()
        .filter(|answer| answer.complete_closed_outputs > 0)
        .take(12)
        .flat_map(|answer| {
            answer
                .outputs
                .iter()
                .take(2)
                .map(move |surface| format!("- **{}**: {}", answer.role, surface.text))
        })
        .collect::<Vec<_>>()
        .join("\n");
    fs::write(output.join("INSPECTION.md"), format!(
        "# Athena alpha inspected return\n\n- Product: `{identity}`\n- Native generators: {} ({} mathematical, {} code-bearing).\n- Source-detached prompt/organ cases: {}.\n- Complete closed answer surfaces: {}.\n- Native membrane returns: {}.\n- Complete AA0--AA4 grade: `{}`.\n\n## Returned surfaces\n\n{}\n",
        condensation.generators,
        condensation.mathematical_families,
        condensation.code_families,
        detached.answers.len(),
        detached.complete_outputs,
        detached.membrane_returns.len(),
        grade["passed"],
        samples,
    )).map_err(|error| error.to_string())
}

fn write_output_manifest(output: &Path) -> Result<(), String> {
    let mut members = Vec::new();
    collect_members(output, output, &mut members)?;
    members.retain(|value| value["path"] != "MANIFEST.json");
    members.sort_by(|left, right| left["path"].as_str().cmp(&right["path"].as_str()));
    write_json(
        output.join("MANIFEST.json"),
        &json!({
            "schema":"holonics.athena-alpha.output-manifest.v1",
            "members":members,
        }),
    )
}

fn collect_members(root: &Path, at: &Path, members: &mut Vec<Value>) -> Result<(), String> {
    for entry in fs::read_dir(at).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let path = entry.path();
        if path.is_dir() {
            collect_members(root, &path, members)?;
        } else {
            let relative = path
                .strip_prefix(root)
                .map_err(|error| error.to_string())?
                .to_string_lossy()
                .to_string();
            let bytes = fs::read(&path).map_err(|error| error.to_string())?;
            members.push(json!({"path":relative,"sha256":sha(&bytes),"octets":bytes.len()}));
        }
    }
    Ok(())
}

fn directory_octets(path: &Path) -> Result<u64, String> {
    let mut total = 0u64;
    for entry in fs::read_dir(path).map_err(|error| error.to_string())? {
        let member = entry.map_err(|error| error.to_string())?.path();
        total = total
            .checked_add(if member.is_dir() {
                directory_octets(&member)?
            } else {
                fs::metadata(&member)
                    .map_err(|error| error.to_string())?
                    .len()
            })
            .ok_or_else(|| "Athena-alpha product cost left the u64 carrier".to_owned())?;
    }
    Ok(total)
}

fn arguments() -> Result<Args, String> {
    let mut values = env::args_os().skip(1);
    let mode = values.next();
    if mode.as_deref() == Some(std::ffi::OsStr::new("--foreign-probe")) {
        let product = values
            .next()
            .map(PathBuf::from)
            .ok_or("--foreign-probe needs PRODUCT")?;
        let continuation = values
            .next()
            .map(PathBuf::from)
            .ok_or("--foreign-probe needs CONTINUATION")?;
        let prompt = values
            .next()
            .ok_or("--foreign-probe needs PROMPT")?
            .into_string()
            .map_err(|_| "--foreign-probe PROMPT is not UTF-8")?;
        let output = values
            .next()
            .map(PathBuf::from)
            .ok_or("--foreign-probe needs OUTPUT")?;
        if values.next().is_some() {
            return Err("too many foreign-probe arguments".to_owned());
        }
        return Ok(Args::ForeignProbe {
            product,
            continuation,
            prompt,
            output,
        });
    }
    if mode.as_deref() == Some(std::ffi::OsStr::new("--detached")) {
        let rest = values
            .next()
            .map(PathBuf::from)
            .ok_or("--detached needs REST")?;
        let e5 = values
            .next()
            .map(PathBuf::from)
            .ok_or("--detached needs E5_REST")?;
        let tower = values
            .next()
            .map(PathBuf::from)
            .ok_or("--detached needs FOREIGN_TOWER")?;
        let continuation = values
            .next()
            .map(PathBuf::from)
            .ok_or("--detached needs FOREIGN_CONTINUATION")?;
        let input = values
            .next()
            .map(PathBuf::from)
            .ok_or("--detached needs INPUT")?;
        let output = values
            .next()
            .map(PathBuf::from)
            .ok_or("--detached needs OUTPUT")?;
        if values.next().is_some() {
            return Err("too many detached arguments".to_owned());
        }
        return Ok(Args::Detached {
            rest,
            e5,
            tower,
            continuation,
            input,
            output,
        });
    }
    // No first positional argument was consumed in the ordinary form; parse directly from argv.
    let mut values = env::args_os().skip(1);
    let aa0 = values
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| AA0.into());
    let aa1 = values
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| AA1.into());
    let e5 = values
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| E5_REST.into());
    let output = values
        .next()
        .map(PathBuf::from)
        .unwrap_or_else(|| OUTPUT.into());
    if values.next().is_some() {
        return Err("usage: [AA0] [AA1] [E5_REST] [OUTPUT]".to_owned());
    }
    Ok(Args::Produce {
        aa0,
        aa1,
        e5,
        output,
    })
}

fn word_set(text: &str) -> BTreeSet<String> {
    lexical_tokens(text)
        .into_iter()
        .filter(|token| token.chars().all(char::is_alphanumeric))
        .map(|token| token.to_lowercase())
        .collect()
}

fn canonical(path: &Path) -> Result<PathBuf, String> {
    path.canonicalize()
        .map_err(|error| format!("resolve {}: {error}", path.display()))
}

fn digest_json(value: &impl Serialize) -> Result<String, String> {
    Ok(sha(
        &serde_json::to_vec(value).map_err(|error| error.to_string())?
    ))
}

fn sha_file(path: &Path) -> Result<String, String> {
    Ok(sha(&fs::read(path).map_err(|error| error.to_string())?))
}

fn sha(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn read_json<T: for<'de> Deserialize<'de>>(path: impl AsRef<Path>) -> Result<T, String> {
    serde_json::from_slice(&fs::read(path.as_ref()).map_err(|error| error.to_string())?)
        .map_err(|error| error.to_string())
}

fn write_json(path: impl AsRef<Path>, value: &impl Serialize) -> Result<(), String> {
    let file = fs::File::create(path.as_ref()).map_err(|error| error.to_string())?;
    serde_json::to_writer_pretty(file, value).map_err(|error| error.to_string())
}
