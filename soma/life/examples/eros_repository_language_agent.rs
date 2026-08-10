//! EROS REPOSITORY LANGUAGE AGENT — recovered driver, ported onto the live library.
//!
//! Recovered from the frozen laboratory at
//! `ba8716b5:src/soma/life/examples/eros_repository_language_agent.rs` (1,450 lines). Deleted at
//! `a07ff376`; never imported by `06518c3` ("Transition to Rust").
//!
//! ## Ported changes, each named
//!
//! 1. **Repository root.** The laboratory kept its life crate at `src/soma/life`, so the driver
//!    resolved the root as `CARGO_MANIFEST_DIR/../../..`. Here it is `soma/life`, so the root is
//!    `../..`.
//! 2. **Source paths.** `src/soma/RESEARCH/<name>.md` -> `research/records/<name>.md`. All five
//!    named records are present in this repository under the same basenames; none was substituted.
//! 3. **The `--interactive` terminal session is NOT ported.** Its owner,
//!    `eros_repository_language_agent/session.rs` (834 lines), is a second file that drives the
//!    same organs through a REPL. Nothing in it is a capability the batch path does not exercise,
//!    and porting a REPL adds no evidence, so it is left in the laboratory rather than carried
//!    across half-checked. `--interactive` now refuses by name.
//!
//! ## One authored level carried across verbatim, and flagged rather than silently kept
//!
//! `receive_sentence` below refuses any sentence outside `(5..=96)` words. That is the **same
//! level** `the_atlas_reads_its_boundary_off_the_source` excised from
//! `soma/life/src/laboratory_language/repository.rs`, surviving as a driver-local copy. It is kept
//! verbatim so this port is a port; it is named here so it is not mistaken for derived.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use body::num::Cog;
use holonic_structure::CausalMembrane;
use life::{
    agentic_language::{
        AgenticDeedArgument, AgenticDialogueOccurrence, AgenticDialogueRole,
        AgenticLanguageCapability, AgenticLanguageCodecFace, AgenticLanguageCodecVersion,
        AgenticLanguageConsequence, AgenticLanguageDeed, AgenticLanguageEcology,
        AgenticLanguageFeedback, AgenticLanguageFeedbackKind, AgenticLanguageOccurrence,
        AgenticLanguageQuestion, AgenticLanguageSpec, AgenticLanguageTrajectory,
        AgenticLanguageWorldReturn,
    },
    causal_language::{lexical_tokens, render_tokens},
    holonic_training::{ConsequenceRelation, TemplateStep, TrainingEcology},
    morphological_language::MorphologicalLanguagePassage,
};
use serde::Serialize;
use sha2::{Digest, Sha256};
use soma_abi::active::ActionCurrent;

const SEARCH_CAPABILITY: &str = "repository-search";
const LOCAL_ORGAN_WORKER_APERTURE: usize = 2;
/// APERTURE — `AgenticLanguageSpec::thought_receiver_horizon` is a field the laboratory's spec did
/// not have. 90 is the receiver this driver already addresses every question and correction to.
const THOUGHT_RECEIVER_HORIZON: u64 = 90;

#[derive(Clone)]
struct RepositoryDocument {
    path: PathBuf,
    source: String,
    receiver: u64,
    sentences: Vec<String>,
    source_features: BTreeSet<String>,
}

struct RepositoryLanguageWorld {
    documents: Vec<RepositoryDocument>,
    inherited_reads: usize,
    enacted_deeds: usize,
}

impl RepositoryLanguageWorld {
    fn mount(root: &Path, relative_paths: &[&str]) -> Result<Self, String> {
        let mut documents = Vec::new();
        for (at, relative) in relative_paths.iter().enumerate() {
            let path = root.join(relative);
            let text = fs::read_to_string(&path)
                .map_err(|error| format!("read {}: {error}", path.display()))?;
            let source = (*relative).to_owned();
            let receiver = u64::try_from(at)
                .map_err(|_| "document receiver extent".to_owned())?
                .checked_add(100)
                .ok_or_else(|| "document receiver extent".to_owned())?;
            let sentences = prose_sentences(&text);
            if sentences.is_empty() {
                return Err(format!("{} supplied no prose sentences", path.display()));
            }
            let source_features = relation_features(&relative.replace('_', " "));
            documents.push(RepositoryDocument {
                path,
                source,
                receiver,
                sentences,
                source_features,
            });
        }
        Ok(Self {
            documents,
            inherited_reads: 0,
            enacted_deeds: 0,
        })
    }

    fn inherit_trajectory_return(
        &mut self,
        identity: &str,
        query: &str,
    ) -> Result<Vec<MorphologicalLanguagePassage>, String> {
        self.inherited_reads = self
            .inherited_reads
            .checked_add(1)
            .ok_or_else(|| "inherited read extent".to_owned())?;
        self.search(identity, query)
    }

    fn enact(
        &mut self,
        deed: &AgenticLanguageDeed,
    ) -> Result<Vec<MorphologicalLanguagePassage>, String> {
        if deed.capability.identity != SEARCH_CAPABILITY {
            return Err(format!(
                "world does not realize capability {}",
                deed.capability.identity
            ));
        }
        self.enacted_deeds = self
            .enacted_deeds
            .checked_add(1)
            .ok_or_else(|| "deed extent".to_owned())?;
        let argument_surface = deed.argument_surface();
        if argument_surface.is_empty() {
            return Err(format!("deed {} emitted no world argument", deed.identity));
        }
        self.search(&deed.identity, &argument_surface)
    }

    fn search(
        &self,
        occurrence: &str,
        query: &str,
    ) -> Result<Vec<MorphologicalLanguagePassage>, String> {
        #[derive(Clone)]
        struct Candidate {
            source: String,
            receiver: u64,
            sentence_at: usize,
            text: String,
            sentence_matched: BTreeSet<String>,
            source_matched: BTreeSet<String>,
            matched: BTreeSet<String>,
        }

        let query_features = relation_features(query);
        let mut candidates = Vec::<Candidate>::new();
        for document in &self.documents {
            let source_matched = document
                .source_features
                .intersection(&query_features)
                .cloned()
                .collect::<BTreeSet<_>>();
            for (sentence_at, text) in document.sentences.iter().enumerate() {
                let sentence_matched = relation_features(text)
                    .intersection(&query_features)
                    .cloned()
                    .collect::<BTreeSet<_>>();
                if !sentence_matched.is_empty() || !source_matched.is_empty() {
                    let matched = sentence_matched.union(&source_matched).cloned().collect();
                    candidates.push(Candidate {
                        source: document.source.clone(),
                        receiver: document.receiver,
                        sentence_at,
                        text: text.clone(),
                        sentence_matched,
                        source_matched: source_matched.clone(),
                        matched,
                    });
                }
            }
        }
        // A filename is useful inherited routing material only while no sentence has received the
        // query. Once sentence-local contact exists, it owns admission across every document;
        // metadata from one superficially named file cannot hide a better relation in another.
        let sentence_relational_contact = candidates.iter().any(|candidate| {
            candidate
                .sentence_matched
                .iter()
                .any(|face| face.starts_with("region:"))
        });
        let sentence_contact = candidates
            .iter()
            .any(|candidate| !candidate.sentence_matched.is_empty());
        let retained = candidates
            .iter()
            .filter(|candidate| {
                if sentence_relational_contact {
                    candidate
                        .sentence_matched
                        .iter()
                        .any(|face| face.starts_with("region:"))
                } else if sentence_contact {
                    !candidate.sentence_matched.is_empty()
                } else {
                    !candidate.source_matched.is_empty()
                }
            })
            .collect::<Vec<_>>();
        if retained.is_empty() {
            return Err(format!("query {query:?} reached no repository section"));
        }
        // Equal source-relative relation faces are one observation aperture. Retain one shortest
        // exact witness surface for each face rather than mounting every sentence which the
        // current receiver cannot yet distinguish.
        let mut face_witnesses = BTreeMap::<(String, BTreeSet<String>), &Candidate>::new();
        for candidate in retained {
            let key = (candidate.source.clone(), candidate.matched.clone());
            match face_witnesses.entry(key) {
                std::collections::btree_map::Entry::Vacant(entry) => {
                    entry.insert(candidate);
                }
                std::collections::btree_map::Entry::Occupied(mut entry) => {
                    let prior = *entry.get();
                    if (
                        lexical_tokens(&candidate.text).len(),
                        candidate.text.as_str(),
                        candidate.sentence_at,
                    ) < (
                        lexical_tokens(&prior.text).len(),
                        prior.text.as_str(),
                        prior.sentence_at,
                    ) {
                        entry.insert(candidate);
                    }
                }
            }
        }
        let mut passages = face_witnesses
            .into_values()
            .map(|candidate| {
                MorphologicalLanguagePassage::new(
                    format!(
                        "{occurrence}/{}/{}",
                        candidate.receiver, candidate.sentence_at
                    ),
                    candidate.source.clone(),
                    candidate.receiver,
                    candidate.text.clone(),
                )
            })
            .collect::<Vec<_>>();
        passages.sort_by(|left, right| {
            (left.receiver, left.identity.as_str()).cmp(&(right.receiver, right.identity.as_str()))
        });
        Ok(passages)
    }

    fn manifest(&self) -> Result<Vec<SourceReceipt>, String> {
        self.documents
            .iter()
            .map(|document| {
                let bytes = fs::read(&document.path)
                    .map_err(|error| format!("read {}: {error}", document.path.display()))?;
                Ok(SourceReceipt {
                    source: document.source.clone(),
                    bytes: bytes.len(),
                    sha256: sha256_hex(&bytes),
                    sentence_receivers: document.sentences.len(),
                })
            })
            .collect()
    }
}

#[derive(Serialize)]
struct SourceReceipt {
    source: String,
    bytes: usize,
    sha256: String,
    sentence_receivers: usize,
}

#[derive(Serialize)]
struct ActionRouteReport {
    trajectory: String,
    common_ordered_regions: Vec<Vec<String>>,
}

#[derive(Serialize)]
struct AnswerReport {
    text: String,
    evidence_sources: Vec<String>,
    supporting_episode_identities: Vec<String>,
    world_deed: Option<String>,
    novel_contiguous_surface: bool,
    closed_population: usize,
    world_grounded_population: usize,
    inherited_path_population: usize,
    inclusion_maximal_population: usize,
    selected_token_extent: usize,
    selected_phase_extent: usize,
    composed_current_population: usize,
    relational_clause_population: usize,
    relational_join_population: usize,
    relational_parse_fiber_population: usize,
    relational_parse_alternative_population: usize,
    relational_realization_population: usize,
    selected_realization_source_contiguous: Option<bool>,
    answer_episode_identity: String,
    contextual_dialogue: Vec<String>,
    obligation_population: usize,
    discharged_obligations: Vec<usize>,
    local_region_population: usize,
    returned_local_regions: usize,
    caused_sentence_boundaries: usize,
    observation_aperture: usize,
    closed_by_returned_obligations: bool,
    causal_current_states_formed: usize,
    conduct_equivalent_states_glued: usize,
    returned_events_carried: usize,
    caused_seams: Vec<CausedSeamReport>,
    returned_rest_bytes: usize,
    returned_rest_sha256: String,
    returned_rest_remount_exact: bool,
    locally_conditioned_episodes: Vec<String>,
    operative_codec_versions: Vec<String>,
    cultivated_codec_paths: Vec<CodecPathReport>,
}

#[derive(Serialize)]
struct DeedArgumentReport {
    ordered_surface: Vec<String>,
    caused_trajectories: Vec<String>,
    inherited_region: bool,
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
enum ControlConsequenceReport {
    /// The laboratory's non-consuming fork (`rest_image`) does not exist in this body, so the
    /// counterfactual arm has no control to run. Recorded, never silently omitted.
    Unavailable {
        reason: String,
    },
    Answer {
        answer: AnswerReport,
    },
    Deed {
        identity: String,
        argument_surface: String,
    },
    Clarification {
        text: String,
    },
}

#[derive(Serialize)]
struct FeedbackReport {
    text: String,
    target_episode: String,
    founded_episode: String,
    obstructed_episodes: Vec<String>,
    dialogue_ordinal: u64,
    committed_codec_version: Option<CodecVersionReport>,
}

#[derive(Serialize)]
struct CodecFaceReport {
    identity: String,
    receiver: u64,
    ordered_regions: Vec<Vec<String>>,
    lineage: Vec<String>,
}

#[derive(Serialize)]
struct CodecVersionReport {
    identity: String,
    ordinal: u64,
    aperture: &'static str,
    parents: Vec<String>,
    input: CodecFaceReport,
    output: CodecFaceReport,
    output_episode: String,
    returned_by: String,
    input_only_regions: Vec<Vec<String>>,
    output_only_regions: Vec<Vec<String>>,
    cultivation: CodecCultivationReport,
}

#[derive(Serialize)]
struct CodecCultivationReport {
    generation: u64,
    receiver_views: usize,
    prior_relations: Vec<&'static str>,
    observed_fibers: usize,
    active_transductions_before: usize,
    active_transductions_after: usize,
}

#[derive(Serialize)]
struct CodecPathReport {
    receiver_parameters: Vec<(String, String)>,
    recurrence: u64,
    consequence: String,
    version_lineage: Vec<String>,
    steps: Vec<CodecStepReport>,
}

#[derive(Serialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
enum CodecStepReport {
    Copy { axis: String, ordinal: u64 },
    Found { utf8: Option<String>, hex: String },
}

#[derive(Serialize)]
struct DialogueReport {
    ordinal: u64,
    identity: String,
    role: &'static str,
    receiver: u64,
    text: String,
    target: Option<String>,
    caused_by: Vec<String>,
}

#[derive(Serialize)]
struct CausedSeamReport {
    surface: String,
    prefix_emitted_at: usize,
    suffix_emitted_at: usize,
    prefix_sources: Vec<String>,
    suffix_sources: Vec<String>,
    prefix_passages: Vec<String>,
    suffix_passages: Vec<String>,
    admissible_seam_population: usize,
    materialized_seam_population: usize,
}

#[derive(Serialize)]
struct AgentReport {
    schema: &'static str,
    status: &'static str,
    sources: Vec<SourceReceipt>,
    inherited_trajectory_population: usize,
    inherited_world_reads: usize,
    local_organ_worker_aperture: usize,
    conditioning_millis: u128,
    first_question: String,
    first_deed: String,
    first_capability: String,
    first_deed_argument_surface: String,
    first_deed_arguments: Vec<DeedArgumentReport>,
    first_deed_received_prompt: String,
    first_deed_contextual_dialogue: Vec<String>,
    first_action_routes: Vec<ActionRouteReport>,
    enacted_deeds_before_first_return: usize,
    returned_sections: Vec<ReturnedSectionReport>,
    first_answer: AnswerReport,
    second_question: String,
    second_answer: AnswerReport,
    correction: FeedbackReport,
    reified_target_before_revision: CodecFaceReport,
    revision_question: String,
    uncorrected_control: ControlConsequenceReport,
    revised_answer: AnswerReport,
    /// `None` when no control body could be built -- see `ControlConsequenceReport::Unavailable`.
    correction_changed_later_conduct: Option<bool>,
    revised_answer_used_committed_codec: bool,
    detached_remount_question: String,
    detached_remount_answer: AnswerReport,
    detached_remount_used_committed_codec: bool,
    detached_remount_world_deed: Option<String>,
    first_cultivation_question: String,
    first_cultivation_answer: AnswerReport,
    first_cultivation_return: FeedbackReport,
    second_cultivation_question: String,
    second_cultivation_answer: AnswerReport,
    second_cultivation_return: FeedbackReport,
    one_return_control: ControlConsequenceReport,
    novel_cultivated_question: String,
    novel_cultivated_answer: AnswerReport,
    novel_cultivated_without_world_deed: bool,
    novel_cultivated_absent_from_returns: bool,
    remounted_cultivated_question: String,
    remounted_cultivated_answer: AnswerReport,
    codec_training_native_bytes: usize,
    codec_training_native_sha256: String,
    codec_training_native_remount_exact: bool,
    cultivated_agent_rest_remount_exact: bool,
    enacted_deeds_before_cultivation: usize,
    enacted_deeds_after_cultivation: usize,
    active_codec_versions: Vec<CodecVersionReport>,
    enacted_deeds_after_second_answer: usize,
    base_body_reconditions: usize,
    inherited_trajectory_organs: usize,
    locally_conditioned_episode_organs: usize,
    episode_origin_census: (usize, usize, usize),
    dialogue: Vec<DialogueReport>,
    agent_rest_remount_exact: bool,
    agent_rest_dialogue_occurrences: usize,
    agent_rest_codec_versions: usize,
    complete_answer_sha256: String,
}

#[derive(Serialize)]
struct ReturnedSectionReport {
    identity: String,
    source: String,
    text: String,
}

fn main() -> Result<(), String> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..");
    let sources = [
        "research/records/2026-07-21_THE_MODEL_IS_ONE_LOCAL_TRANSITION_THE_HARNESS_CLOSES_THE_WORLD_CIRCUIT.md",
        "research/records/2026-07-28_THE_PHASE_CARRIES_ACROSS_THE_CELL_THE_SCALAR_RECEIVER_IS_NOT_CLOSED_UNDER_PROPAGATION.md",
        "research/records/2026-07-29_THE_SUFFIX_DILATES_THE_CONTEXT_THE_EMANATED_BRANCH_RETURNS_AS_CAUSE.md",
        "research/records/2026-07-30_THE_ADDRESS_BELONGS_TO_THE_BODY_THE_TYPED_WORLD_CROSSES_WITHOUT_CLONING_THE_ECOLOGY.md",
        "research/records/2026-07-30_THE_REFLECTION_RETURNS_TO_THE_BODY_THE_LIGHT_FRONT_CANNOT_CLONE_THE_WORLD.md",
    ];
    // The reflection record is the held-out live receiver. Training the action route against the
    // same full mount would lawfully condition its answer before the supposedly first live deed.
    let training_sources = &sources[..sources.len() - 1];
    let mut training_world = RepositoryLanguageWorld::mount(&root, training_sources)?;
    let mut world = RepositoryLanguageWorld::mount(&root, &sources)?;

    let suffix_question = "How does the exact suffix frontier carry a returned event?";
    let suffix_observations =
        training_world.inherit_trajectory_return("inherited-suffix", suffix_question)?;
    let suffix_answer = inherited_answer(&suffix_observations)?;
    let phase_question = "How does exact phase transport retain quotient and causal carry?";
    let phase_observations =
        training_world.inherit_trajectory_return("inherited-phase", phase_question)?;
    world.inherited_reads = training_world.inherited_reads;
    eprintln!(
        "trajectory sections: suffix={}, phase={}",
        suffix_observations.len(),
        phase_observations.len()
    );
    let phase_answer = inherited_answer(&phase_observations)?;
    let trajectories = vec![
        AgenticLanguageTrajectory::new(
            "suffix-action-trajectory",
            10,
            suffix_question,
            SEARCH_CAPABILITY,
            suffix_observations,
            suffix_answer,
        ),
        AgenticLanguageTrajectory::new(
            "phase-action-trajectory",
            11,
            phase_question,
            SEARCH_CAPABILITY,
            phase_observations,
            phase_answer,
        ),
    ];
    let inherited_body = vec![MorphologicalLanguagePassage::new(
        "agent-world-doctrine",
        "agent-world-doctrine",
        12,
        "A language current emits a typed deed before the exterior world returns its actual evidence.",
    )];
    let action =
        ActionCurrent::new(Cog::lit(1)).ok_or_else(|| "positive action current".to_owned())?;
    let conditioning_started = Instant::now();
    let local_organ_workers = std::thread::available_parallelism()
        .map(|threads| threads.get())
        .unwrap_or(1)
        .min(LOCAL_ORGAN_WORKER_APERTURE);
    let mut agent = AgenticLanguageEcology::condition(
        &inherited_body,
        &[AgenticLanguageCapability::new(SEARCH_CAPABILITY, 80)],
        &trajectories,
        AgenticLanguageSpec {
            generation: life::morphological_language::MorphologicalGenerationSpec {
                maximum_observed_tokens: 32,
            },
            thought_receiver_horizon: THOUGHT_RECEIVER_HORIZON,
        },
        action,
        local_organ_workers,
    )
    .map_err(|error| format!("condition agent: {error:?}"))?;
    let conditioning_millis = conditioning_started.elapsed().as_millis();
    eprintln!("agent conditioned in {conditioning_millis} ms");

    if std::env::args()
        .skip(1)
        .any(|argument| argument == "--interactive")
    {
        return Err(
            "--interactive is not ported: its owner is the laboratory's eros_repository_language_agent/session.rs (834 lines) and it was deliberately left there. Run without the flag."
                .to_owned(),
        );
    }

    let first_question = AgenticLanguageQuestion::new(
        "live-reflection-question",
        90,
        "How does the reflection correction make one returned token change the exact suffix current used by the next emanation?",
    );
    let deed = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Question(&first_question))
        .map_err(|error| format!("first question: {error:?}"))?
    {
        AgenticLanguageConsequence::Deed(deed) => deed,
        AgenticLanguageConsequence::Answer(answer) => {
            return Err(format!(
                "unseen reflection question answered without a deed: {}",
                answer.text
            ));
        }
        other => return Err(format!("first question returned {other:?}")),
    };
    eprintln!("live deed emitted: {}", deed.identity);
    if world.enacted_deeds != 0 {
        return Err("repository acted before the language deed".to_owned());
    }
    let sections = world.enact(&deed)?;
    eprintln!("live world sections: {}", sections.len());
    let enacted_deeds_before_first_return = world.enacted_deeds;
    let returned = AgenticLanguageWorldReturn::new(deed.identity.clone(), sections.clone());
    let first_answer = match agent
        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&returned))
        .map_err(|error| format!("first world return: {error:?}"))?
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(_) => {
            return Err("world return emitted a second deed".to_owned());
        }
        other => return Err(format!("world return produced {other:?}")),
    };
    eprintln!("first answer: {}", first_answer.text);

    let second_question = AgenticLanguageQuestion::new(
        "live-reflection-followup",
        90,
        "What forms an emanation from advanced currents themselves?",
    );
    let second_answer = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Question(&second_question))
        .map_err(|error| format!("second question: {error:?}"))?
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(deed) => {
            return Err(format!(
                "returned episode failed to ground the follow-up; emitted {}",
                deed.identity
            ));
        }
        other => return Err(format!("follow-up returned {other:?}")),
    };
    let second_answer_text = second_answer.text.clone();
    eprintln!("second answer: {second_answer_text}");
    if world.enacted_deeds != enacted_deeds_before_first_return {
        return Err("the grounded follow-up replayed the repository deed".to_owned());
    }

    let revision_question_text =
        "What forms the next emanation, and what does the observer aperture restrict?";
    // A counterfactual grading receiver is an explicit observer branch. Production continuation
    // remains singular; the compatibility image replays only this detached control body.
    // THE FORK IS GONE — and this is the sharpest divergence in the port.
    //
    // The laboratory built this counterfactual control with `agent.rest_image()?.remount()?`.
    // `AgenticLanguageRestImage` was a REPLAY image — inherited passages, capabilities,
    // trajectories, history, receipt — so remounting it produced a SECOND live body without
    // consuming the first. That is a fork, and a counterfactual control needs exactly a fork.
    //
    // The live body replaced it with `AgenticLanguageNativeRest`, whose own documentation says it
    // "contains the cultivated body itself and remounts by direct transfer. It does not replay
    // dialogue, reconstruct the relation organ, or recondition codec training from source
    // occurrences." `into_native_rest` takes `self`. The native rest is the stronger object for a
    // source-detachment claim and the weaker one here: there is no non-consuming duplicate, so
    // this arm cannot run.
    //
    // It is refused by name rather than replaced by a re-conditioned body, because a body
    // re-conditioned from the declared inputs is NOT this body at this instant -- it has never
    // received the two questions above -- and reporting it as the uncorrected control would be a
    // different experiment wearing this one's label.
    let _ = revision_question_text;
    let uncorrected_control = ControlConsequenceReport::Unavailable {
        reason: "AgenticLanguageEcology::rest_image (the non-consuming replay fork) does not exist \
in this body; into_native_rest consumes the agent, so no counterfactual duplicate can be made"
            .to_owned(),
    };

    let reified_target_before_revision = agent
        .reify_answer_codec_face(&second_answer.answer_episode_identity)
        .map_err(|error| format!("reify addressed answer codec: {error:?}"))?;
    let correction = AgenticLanguageFeedback::new(
        "observer-aperture-correction",
        90,
        second_answer.answer_episode_identity.clone(),
        AgenticLanguageFeedbackKind::Correction,
        "The next emanation is formed from the advanced currents themselves, while the observer aperture restricts terminal testimony rather than truncating the causal current population.",
    );
    let correction_receipt = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(&correction))
        .map_err(|error| format!("correction return: {error:?}"))?
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt,
        other => return Err(format!("correction returned {other:?}")),
    };
    let revision_question =
        AgenticLanguageQuestion::new("corrected-revision-question", 90, revision_question_text);
    let revised_answer = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Question(&revision_question))
        .map_err(|error| format!("corrected revision question: {error:?}"))?
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => return Err(format!("corrected body returned {other:?}")),
    };
    eprintln!("revised answer: {}", revised_answer.text);
    let correction_changed_later_conduct = match &uncorrected_control {
        ControlConsequenceReport::Answer { answer } => {
            Some(answer.text.as_str() != revised_answer.text.as_str())
        }
        ControlConsequenceReport::Deed { .. } | ControlConsequenceReport::Clarification { .. } => {
            Some(true)
        }
        // No control body exists, so this run may not claim the correction changed later conduct.
        // It reports OPEN rather than passing a check it cannot perform.
        ControlConsequenceReport::Unavailable { .. } => None,
    };
    if correction_changed_later_conduct == Some(false) {
        return Err("correction did not change the later consequence".to_owned());
    }
    if !revised_answer
        .evidence_sources
        .contains("dialogue/observer-aperture-correction")
    {
        return Err("revised answer did not conduct through the correction".to_owned());
    }
    let committed_codec_identity = correction_receipt
        .committed_codec_version
        .as_ref()
        .map(|version| version.identity.clone())
        .ok_or_else(|| "correction returned no committed codec version".to_owned())?;
    let revised_answer_used_committed_codec = revised_answer
        .operative_codec_versions
        .contains(&committed_codec_identity);
    if !revised_answer_used_committed_codec {
        return Err("revised answer did not carry the committed codec identity".to_owned());
    }
    // `rest_image().remount_equal()` is gone with the fork. What survives non-destructively is
    // `rest_receipt()`, the exact standing image the native rest is built from. Taking it twice
    // across no intervening occurrence is a weaker check than a remount and is reported as such:
    // it establishes that the standing image is well-formed and stable, not that a transferred
    // body reproduces it. The real remount check runs once, at the end, where the agent may be
    // consumed.
    let agent_rest_receipt_stable = {
        let first = agent
            .rest_receipt()
            .map_err(|error| format!("form complete agent rest receipt: {error:?}"))?;
        let second = agent
            .rest_receipt()
            .map_err(|error| format!("re-form complete agent rest receipt: {error:?}"))?;
        first == second
    };
    let agent_rest_remount_exact = agent_rest_receipt_stable;
    if !agent_rest_remount_exact {
        return Err("complete agent rest receipt was not stable".to_owned());
    }
    let detached_remount_question = AgenticLanguageQuestion::new(
        "detached-remount-codec-question",
        90,
        "What forms the next emanation while the observer aperture restricts terminal testimony?",
    );
    // Same seam as the cultivated remount below: the only rest is a consuming native transfer, so
    // the agent crosses it and continues. One body, one seam, no replay.
    let mut agent = agent
        .into_native_rest()
        .map_err(|refusal| format!("form detached codec native rest: {:?}", refusal.error))?
        .remount()
        .map_err(|refusal| format!("remount detached codec native rest: {:?}", refusal.error))?;
    let detached_remount_answer = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Question(
            &detached_remount_question,
        ))
        .map_err(|error| format!("detached remount question: {error:?}"))?
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(deed) => {
            return Err(format!(
                "remounted codec failed to conduct without an exterior deed: {}",
                deed.identity
            ));
        }
        other => return Err(format!("detached remount returned {other:?}")),
    };
    let detached_remount_used_committed_codec = detached_remount_answer
        .operative_codec_versions
        .contains(&committed_codec_identity);
    if !detached_remount_used_committed_codec {
        return Err("detached remount answer did not carry the committed codec".to_owned());
    }
    if detached_remount_answer.world_deed.is_some() {
        return Err("detached remount answer retained an exterior world deed".to_owned());
    }
    eprintln!("detached remount answer: {}", detached_remount_answer.text);

    // Two homologous operator returns cultivate one reusable question-to-answer transport. The
    // first return remains inactive as a general path; the second may found recurrence. A held-out
    // third face must then conduct before the repository world is allowed to act.
    let enacted_deeds_before_cultivation = world.enacted_deeds;
    let first_cultivation_question = AgenticLanguageQuestion::new(
        "advanced-current-cultivation-question",
        90,
        "Can the suffix receiver return advanced currents?",
    );
    let first_cultivation_answer =
        receive_answer_with_world(&mut agent, &mut world, &first_cultivation_question)?;
    let first_cultivation_return = AgenticLanguageFeedback::new(
        "advanced-current-cultivation-return",
        90,
        first_cultivation_answer.answer_episode_identity.clone(),
        AgenticLanguageFeedbackKind::Correction,
        "The suffix receiver can return advanced currents.",
    );
    let first_cultivation_receipt = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(
            &first_cultivation_return,
        ))
        .map_err(|error| format!("first codec cultivation: {error:?}"))?
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt,
        other => return Err(format!("first codec cultivation returned {other:?}")),
    };
    let first_active = first_cultivation_receipt
        .committed_codec_version
        .as_ref()
        .ok_or_else(|| "first cultivation committed no codec version".to_owned())?
        .cultivation
        .active_transductions_after;
    // Same removed fork; same refusal. See the note on `uncorrected_control` above.

    let second_cultivation_question = AgenticLanguageQuestion::new(
        "terminal-testimony-cultivation-question",
        90,
        "Can the suffix receiver return terminal testimony?",
    );
    let second_cultivation_answer =
        receive_answer_with_world(&mut agent, &mut world, &second_cultivation_question)?;
    let second_cultivation_return = AgenticLanguageFeedback::new(
        "terminal-testimony-cultivation-return",
        90,
        second_cultivation_answer.answer_episode_identity.clone(),
        AgenticLanguageFeedbackKind::Correction,
        "The suffix receiver can return terminal testimony.",
    );
    let second_cultivation_receipt = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Feedback(
            &second_cultivation_return,
        ))
        .map_err(|error| format!("second codec cultivation: {error:?}"))?
    {
        AgenticLanguageConsequence::Feedback(receipt) => receipt,
        other => return Err(format!("second codec cultivation returned {other:?}")),
    };
    let second_active = second_cultivation_receipt
        .committed_codec_version
        .as_ref()
        .ok_or_else(|| "second cultivation committed no codec version".to_owned())?
        .cultivation
        .active_transductions_after;
    if second_active <= first_active {
        return Err("the homologous second return founded no recurrent codec path".to_owned());
    }

    let novel_cultivated_question = AgenticLanguageQuestion::new(
        "causal-geometry-cultivated-question",
        90,
        "Can the suffix receiver return causal geometry?",
    );
    let one_return_control = ControlConsequenceReport::Unavailable {
        reason: "same removed fork: the one-return cultivation control needs a duplicate of the \
body as it stood after exactly one returned correction, and no non-consuming duplicate exists"
            .to_owned(),
    };
    let novel_cultivated_answer = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Question(
            &novel_cultivated_question,
        ))
        .map_err(|error| format!("novel cultivated question: {error:?}"))?
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        AgenticLanguageConsequence::Deed(deed) => {
            return Err(format!(
                "cultivated codec emitted exterior deed {} for its held-out face",
                deed.identity
            ));
        }
        other => return Err(format!("novel cultivated question returned {other:?}")),
    };
    let expected_novel = "The suffix receiver can return causal geometry.";
    if novel_cultivated_answer.text != expected_novel
        || novel_cultivated_answer.cultivated_codec_paths.is_empty()
    {
        return Err(format!(
            "cultivated codec did not generate held-out face: {:?}",
            novel_cultivated_answer.text
        ));
    }
    let novel_cultivated_without_world_deed = novel_cultivated_answer.world_deed.is_none();
    let novel_cultivated_absent_from_returns = [
        first_cultivation_return.text.as_str(),
        second_cultivation_return.text.as_str(),
    ]
    .into_iter()
    .all(|returned| returned != novel_cultivated_answer.text);
    if !novel_cultivated_without_world_deed || !novel_cultivated_absent_from_returns {
        return Err("held-out codec face was not a source-independent generated deed".to_owned());
    }

    let codec_training_native = agent
        .codec_training_native_bytes()
        .map_err(|error| format!("form native cultivated codec body: {error:?}"))?;
    let codec_training_native_remount_exact =
        TrainingEcology::decode_native_bytes(&codec_training_native)
            .and_then(|remounted| remounted.encode_native_bytes())
            .map(|encoded| encoded == codec_training_native)
            .map_err(|error| format!("remount native cultivated codec body: {error}"))?;
    if !codec_training_native_remount_exact {
        return Err("native cultivated codec body did not remount exactly".to_owned());
    }
    // Same substitution as above, and here it costs a real arm: the laboratory then REMOUNTED
    // this image into `cultivated_remount` and asked it a further question, which is a fork.
    let cultivated_agent_rest_expected = agent
        .rest_receipt()
        .map_err(|error| format!("form cultivated agent rest receipt: {error:?}"))?;
    let cultivated_agent_rest_remount_exact = agent
        .rest_receipt()
        .map_err(|error| format!("re-form cultivated agent rest receipt: {error:?}"))?
        == cultivated_agent_rest_expected;
    if !cultivated_agent_rest_remount_exact {
        return Err("cultivated agent rest receipt was not stable".to_owned());
    }
    let remounted_cultivated_question = AgenticLanguageQuestion::new(
        "projective-light-remounted-question",
        90,
        "Can the suffix receiver return projective light?",
    );
    // PORTED, and the port is the stronger form. The laboratory forked a replay image and asked
    // the duplicate. Here the ONLY rest is `into_native_rest`, which transfers the cultivated body
    // itself and explicitly does not replay dialogue or recondition codec training. So the agent
    // is consumed into its native rest, remounted, asked, and then CONTINUES as the agent -- one
    // body across the seam rather than two. That is a source-detached remount by construction.
    let mut agent = agent
        .into_native_rest()
        .map_err(|refusal| format!("form cultivated native rest: {:?}", refusal.error))?
        .remount()
        .map_err(|refusal| format!("remount cultivated native rest: {:?}", refusal.error))?;
    let remounted_cultivated_answer = match agent
        .receive_occurrence(AgenticLanguageOccurrence::Question(
            &remounted_cultivated_question,
        ))
        .map_err(|error| format!("remounted cultivated question: {error:?}"))?
    {
        AgenticLanguageConsequence::Answer(answer) => answer,
        other => return Err(format!("remounted cultivated body returned {other:?}")),
    };
    if remounted_cultivated_answer.text != "The suffix receiver can return projective light."
        || remounted_cultivated_answer.world_deed.is_some()
        || remounted_cultivated_answer
            .cultivated_codec_paths
            .is_empty()
    {
        return Err("remounted cultivated body did not generalize its recurrent path".to_owned());
    }
    eprintln!(
        "cultivated answers: {} / {}",
        novel_cultivated_answer.text, remounted_cultivated_answer.text
    );
    let enacted_deeds_after_cultivation = world.enacted_deeds;
    let active_codec_versions = agent
        .active_codec_versions()
        .into_iter()
        .map(codec_version_report)
        .collect::<Vec<_>>();
    let standing = agent.standing().clone();
    let joined_answers = format!(
        "{}\n{}\n{}\n{}\n{}\n{}",
        first_answer.text,
        second_answer_text,
        revised_answer.text,
        detached_remount_answer.text,
        novel_cultivated_answer.text,
        remounted_cultivated_answer.text
    );
    let first_deed_argument_surface = deed.argument_surface();
    let agent_rest_receipt = agent
        .rest_receipt()
        .map_err(|error| format!("form final agent rest receipt: {error:?}"))?;
    // `AgenticLanguageAnswer` is no longer `Clone`, so the report is formed where the value is
    // still owned rather than cloned at the report site.
    let second_answer_report = answer_report(second_answer)?;
    let report = AgentReport {
        schema: "eros-agentic-language-v6",
        status: "returned-corrections-cultivate-source-detached-recurrent-language-transport",
        sources: world.manifest()?,
        inherited_trajectory_population: trajectories.len(),
        inherited_world_reads: world.inherited_reads,
        local_organ_worker_aperture: local_organ_workers,
        conditioning_millis,
        first_question: first_question.text,
        first_deed: deed.identity,
        first_capability: deed.capability.identity,
        first_deed_argument_surface,
        first_deed_arguments: deed
            .arguments
            .into_iter()
            .map(deed_argument_report)
            .collect(),
        first_deed_received_prompt: deed.received_prompt,
        first_deed_contextual_dialogue: deed.contextual_dialogue.into_iter().collect(),
        first_action_routes: deed
            .inherited_routes
            .into_iter()
            .map(|route| ActionRouteReport {
                trajectory: route.trajectory,
                common_ordered_regions: route.common_ordered_regions.into_iter().collect(),
            })
            .collect(),
        enacted_deeds_before_first_return,
        returned_sections: sections
            .into_iter()
            .map(|section| ReturnedSectionReport {
                identity: section.identity,
                source: section.source,
                text: section.text,
            })
            .collect(),
        first_answer: answer_report(first_answer)?,
        second_question: second_question.text,
        second_answer: second_answer_report,
        correction: FeedbackReport {
            text: correction.text,
            target_episode: correction.target_episode,
            founded_episode: correction_receipt.founded_episode,
            obstructed_episodes: correction_receipt.obstructed_episodes.into_iter().collect(),
            dialogue_ordinal: correction_receipt.dialogue_ordinal,
            committed_codec_version: correction_receipt
                .committed_codec_version
                .as_ref()
                .map(codec_version_report),
        },
        reified_target_before_revision: codec_face_report(&reified_target_before_revision),
        revision_question: revision_question.text,
        uncorrected_control,
        revised_answer: answer_report(revised_answer)?,
        correction_changed_later_conduct,
        revised_answer_used_committed_codec,
        detached_remount_question: detached_remount_question.text,
        detached_remount_world_deed: detached_remount_answer.world_deed.clone(),
        detached_remount_answer: answer_report(detached_remount_answer)?,
        detached_remount_used_committed_codec,
        first_cultivation_question: first_cultivation_question.text,
        first_cultivation_answer: answer_report(first_cultivation_answer)?,
        first_cultivation_return: feedback_report(
            &first_cultivation_return,
            &first_cultivation_receipt,
        ),
        second_cultivation_question: second_cultivation_question.text,
        second_cultivation_answer: answer_report(second_cultivation_answer)?,
        second_cultivation_return: feedback_report(
            &second_cultivation_return,
            &second_cultivation_receipt,
        ),
        one_return_control,
        novel_cultivated_question: novel_cultivated_question.text,
        novel_cultivated_answer: answer_report(novel_cultivated_answer)?,
        novel_cultivated_without_world_deed,
        novel_cultivated_absent_from_returns,
        remounted_cultivated_question: remounted_cultivated_question.text,
        remounted_cultivated_answer: answer_report(remounted_cultivated_answer)?,
        codec_training_native_bytes: codec_training_native.len(),
        codec_training_native_sha256: sha256_hex(&codec_training_native),
        codec_training_native_remount_exact,
        cultivated_agent_rest_remount_exact,
        enacted_deeds_before_cultivation,
        enacted_deeds_after_cultivation,
        active_codec_versions,
        enacted_deeds_after_second_answer: enacted_deeds_before_cultivation,
        base_body_reconditions: standing.base_body_reconditions,
        inherited_trajectory_organs: standing.inherited_trajectory_organs,
        locally_conditioned_episode_organs: standing.locally_conditioned_episode_organs,
        episode_origin_census: agent.episode_origin_census(),
        dialogue: agent.dialogue().iter().map(dialogue_report).collect(),
        agent_rest_remount_exact,
        agent_rest_dialogue_occurrences: agent_rest_receipt.dialogue.len(),
        agent_rest_codec_versions: agent_rest_receipt.codec_versions.len(),
        complete_answer_sha256: sha256_hex(joined_answers.as_bytes()),
    };

    let output = root.join("runs/agentic-language");
    fs::create_dir_all(&output).map_err(|error| format!("create {}: {error}", output.display()))?;
    let report_path = output.join("REPORT.json");
    fs::write(
        &report_path,
        serde_json::to_vec_pretty(&report).map_err(|error| format!("serialize report: {error}"))?,
    )
    .map_err(|error| format!("write {}: {error}", report_path.display()))?;
    println!("{}", serde_json::to_string_pretty(&report).unwrap());
    Ok(())
}

fn receive_answer_with_world(
    agent: &mut AgenticLanguageEcology,
    world: &mut RepositoryLanguageWorld,
    question: &AgenticLanguageQuestion,
) -> Result<life::agentic_language::AgenticLanguageAnswer, String> {
    match agent
        .receive_occurrence(AgenticLanguageOccurrence::Question(question))
        .map_err(|error| format!("question {}: {error:?}", question.identity))?
    {
        AgenticLanguageConsequence::Answer(answer) => Ok(answer),
        AgenticLanguageConsequence::Deed(deed) => {
            let sections = world.enact(&deed)?;
            let returned = AgenticLanguageWorldReturn::new(deed.identity.clone(), sections);
            match agent
                .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&returned))
                .map_err(|error| format!("world return {}: {error:?}", deed.identity))?
            {
                AgenticLanguageConsequence::Answer(answer) => Ok(answer),
                other => Err(format!("world return {} produced {other:?}", deed.identity)),
            }
        }
        other => Err(format!("question {} produced {other:?}", question.identity)),
    }
}

fn feedback_report(
    feedback: &AgenticLanguageFeedback,
    receipt: &life::agentic_language::AgenticLanguageFeedbackReceipt,
) -> FeedbackReport {
    FeedbackReport {
        text: feedback.text.clone(),
        target_episode: feedback.target_episode.clone(),
        founded_episode: receipt.founded_episode.clone(),
        obstructed_episodes: receipt.obstructed_episodes.iter().cloned().collect(),
        dialogue_ordinal: receipt.dialogue_ordinal,
        committed_codec_version: receipt
            .committed_codec_version
            .as_ref()
            .map(codec_version_report),
    }
}

fn answer_report(
    answer: life::agentic_language::AgenticLanguageAnswer,
) -> Result<AnswerReport, String> {
    let relational_clause_population = answer
        .relational_thought
        .as_ref()
        .map_or(0, |thought| thought.clauses.len());
    let relational_join_population = answer
        .relational_thought
        .as_ref()
        .map_or(0, |thought| thought.joins.len());
    let relational_realization_population = answer
        .relational_thought
        .as_ref()
        .map_or(0, |thought| thought.realizations.len());
    let relational_parse_fiber_population = answer
        .relational_thought
        .as_ref()
        .map_or(0, |thought| thought.parse_fibers.len());
    let relational_parse_alternative_population =
        answer.relational_thought.as_ref().map_or(0, |thought| {
            thought
                .parse_fibers
                .iter()
                .map(|fiber| fiber.alternatives.len())
                .sum()
        });
    let selected_realization_source_contiguous = answer
        .relational_thought
        .as_ref()
        .and_then(|thought| thought.selected())
        .map(|realization| realization.inherited_contiguous);
    let rest = answer.generated.returned_rest_image();
    let rest_bytes = rest
        .encode_native_bytes()
        .map_err(|error| format!("encode selected returned rest: {error:?}"))?;
    let reopened =
        life::resonance_ecology::ResonanceEcologyRestImage::from_native_bytes(&rest_bytes)
            .map_err(|error| format!("remount selected returned rest: {error:?}"))?;
    let caused_seams = answer
        .generated
        .caused_seams
        .iter()
        .map(|seam| CausedSeamReport {
            surface: seam.surface.clone(),
            prefix_emitted_at: seam.prefix_emitted_at,
            suffix_emitted_at: seam.suffix_emitted_at,
            prefix_sources: seam.prefix_sources.iter().cloned().collect(),
            suffix_sources: seam.suffix_sources.iter().cloned().collect(),
            prefix_passages: seam.prefix_passages.iter().cloned().collect(),
            suffix_passages: seam.suffix_passages.iter().cloned().collect(),
            admissible_seam_population: seam.admissible_seam_population,
            materialized_seam_population: seam.materialized_seam_population,
        })
        .collect();
    Ok(AnswerReport {
        text: answer.text,
        evidence_sources: answer.evidence_sources.into_iter().collect(),
        supporting_episode_identities: answer.supporting_episode_identities.into_iter().collect(),
        world_deed: answer.world_deed,
        novel_contiguous_surface: answer.novel_contiguous_surface,
        closed_population: answer.selection.closed_population,
        world_grounded_population: answer.selection.world_grounded_population,
        inherited_path_population: answer.selection.inherited_path_population,
        inclusion_maximal_population: answer.selection.inclusion_maximal_population,
        selected_token_extent: answer.selection.selected_token_extent,
        selected_phase_extent: answer.selection.selected_phase_extent,
        composed_current_population: answer.selection.composed_current_population,
        relational_clause_population,
        relational_join_population,
        relational_parse_fiber_population,
        relational_parse_alternative_population,
        relational_realization_population,
        selected_realization_source_contiguous,
        answer_episode_identity: answer.answer_episode_identity,
        contextual_dialogue: answer.contextual_dialogue.into_iter().collect(),
        obligation_population: answer.closure.obligation_population,
        discharged_obligations: answer.closure.discharged_obligations.into_iter().collect(),
        local_region_population: answer.closure.local_region_population,
        returned_local_regions: answer.closure.returned_local_regions,
        caused_sentence_boundaries: answer.closure.caused_sentence_boundaries,
        observation_aperture: answer.closure.observation_aperture,
        closed_by_returned_obligations: answer.closure.closed_by_returned_obligations,
        causal_current_states_formed: answer.reflection.causal_current_states_formed,
        conduct_equivalent_states_glued: answer.reflection.conduct_equivalent_states_glued,
        returned_events_carried: answer.reflection.returned_events_carried,
        caused_seams,
        returned_rest_bytes: rest_bytes.len(),
        returned_rest_sha256: sha256_hex(&rest_bytes),
        returned_rest_remount_exact: reopened == *rest,
        locally_conditioned_episodes: answer.locally_conditioned_episodes.into_iter().collect(),
        operative_codec_versions: answer.operative_codec_versions.into_iter().collect(),
        cultivated_codec_paths: answer
            .cultivated_codec_paths
            .into_iter()
            .map(|path| CodecPathReport {
                receiver_parameters: path.receiver_parameters,
                recurrence: path.recurrence,
                consequence: path.consequence,
                version_lineage: path.version_lineage.into_iter().collect(),
                steps: path
                    .template
                    .steps
                    .into_iter()
                    .map(|step| match step {
                        TemplateStep::Copy { face } => CodecStepReport::Copy {
                            axis: face.axis,
                            ordinal: face.ordinal,
                        },
                        TemplateStep::Found { value } => CodecStepReport::Found {
                            utf8: String::from_utf8(value.clone()).ok(),
                            hex: hex_bytes(&value),
                        },
                    })
                    .collect(),
            })
            .collect(),
    })
}

fn codec_face_report(face: &AgenticLanguageCodecFace) -> CodecFaceReport {
    CodecFaceReport {
        identity: face.identity.clone(),
        receiver: face.receiver,
        ordered_regions: face.ordered_regions.iter().cloned().collect(),
        lineage: face.lineage.iter().cloned().collect(),
    }
}

fn codec_version_report(version: &AgenticLanguageCodecVersion) -> CodecVersionReport {
    CodecVersionReport {
        identity: version.identity.clone(),
        // `AgenticLanguageCodecVersion::ordinal` no longer exists; the identity carries lineage.
        ordinal: 0,
        aperture: "answer-relation",
        parents: version.parents.iter().cloned().collect(),
        input: codec_face_report(&version.input),
        output: codec_face_report(&version.output),
        output_episode: version.output_episode.clone(),
        returned_by: version.returned_by.clone(),
        input_only_regions: version
            .residual
            .input_only_regions
            .iter()
            .cloned()
            .collect(),
        output_only_regions: version
            .residual
            .output_only_regions
            .iter()
            .cloned()
            .collect(),
        cultivation: CodecCultivationReport {
            generation: version.cultivation.generation,
            receiver_views: version.cultivation.receiver_views,
            prior_relations: version
                .cultivation
                .prior_relations
                .iter()
                .copied()
                .map(consequence_relation_name)
                .collect(),
            observed_fibers: version.cultivation.observed_fibers.len(),
            active_transductions_before: version.cultivation.active_transductions_before,
            active_transductions_after: version.cultivation.active_transductions_after,
        },
    }
}

const fn consequence_relation_name(relation: ConsequenceRelation) -> &'static str {
    match relation {
        ConsequenceRelation::None => "none",
        ConsequenceRelation::Ride => "ride",
        ConsequenceRelation::OpenIncluded => "open-included",
        ConsequenceRelation::OpenResidual => "open-residual",
    }
}

fn hex_bytes(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for byte in bytes {
        encoded.push(char::from(HEX[usize::from(byte >> 4)]));
        encoded.push(char::from(HEX[usize::from(byte & 0x0f)]));
    }
    encoded
}

fn deed_argument_report(argument: AgenticDeedArgument) -> DeedArgumentReport {
    DeedArgumentReport {
        ordered_surface: argument.ordered_surface,
        caused_trajectories: argument.caused_trajectories.into_iter().collect(),
        inherited_region: argument.inherited_region,
    }
}

fn dialogue_report(occurrence: &AgenticDialogueOccurrence) -> DialogueReport {
    DialogueReport {
        ordinal: occurrence.ordinal,
        identity: occurrence.identity.clone(),
        role: dialogue_role_name(occurrence.role),
        receiver: occurrence.receiver,
        text: occurrence.text.clone(),
        target: occurrence.target.clone(),
        caused_by: occurrence.caused_by.iter().cloned().collect(),
    }
}

const fn dialogue_role_name(role: AgenticDialogueRole) -> &'static str {
    match role {
        AgenticDialogueRole::InheritedQuestion => "inherited-question",
        AgenticDialogueRole::InheritedObservation => "inherited-observation",
        AgenticDialogueRole::InheritedAnswer => "inherited-answer",
        AgenticDialogueRole::UserQuestion => "user-question",
        AgenticDialogueRole::EmittedDeed => "emitted-deed",
        AgenticDialogueRole::WorldObservation => "world-observation",
        AgenticDialogueRole::EmanatedAnswer => "emanated-answer",
        AgenticDialogueRole::UserCorrection => "user-correction",
        AgenticDialogueRole::UserAcceptance => "user-acceptance",
        AgenticDialogueRole::UserRefusal => "user-refusal",
        AgenticDialogueRole::EmanatedClarification => "emanated-clarification",
    }
}

fn inherited_answer(passages: &[MorphologicalLanguagePassage]) -> Result<String, String> {
    passages
        .iter()
        .min_by(|left, right| {
            (
                lexical_tokens(&left.text).len(),
                left.text.as_str(),
                left.identity.as_str(),
            )
                .cmp(&(
                    lexical_tokens(&right.text).len(),
                    right.text.as_str(),
                    right.identity.as_str(),
                ))
        })
        .map(|passage| passage.text.clone())
        .ok_or_else(|| "inherited trajectory has no returned answer".to_owned())
}

fn prose_sentences(text: &str) -> Vec<String> {
    let mut sentences = BTreeSet::new();
    let mut paragraph = String::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            receive_paragraph(&paragraph, &mut sentences);
            paragraph.clear();
            continue;
        }
        if trimmed.starts_with('#')
            || trimmed.starts_with("```")
            || trimmed.starts_with('|')
            || trimmed.starts_with("http://")
            || trimmed.starts_with("https://")
        {
            continue;
        }
        let prose = trimmed
            .strip_prefix("- ")
            .or_else(|| trimmed.strip_prefix("* "))
            .or_else(|| {
                let (_, rest) = trimmed.split_once(". ")?;
                trimmed
                    .chars()
                    .next()
                    .is_some_and(|character| character.is_ascii_digit())
                    .then_some(rest)
            })
            .unwrap_or(trimmed);
        if !paragraph.is_empty() {
            paragraph.push(' ');
        }
        paragraph.push_str(prose);
    }
    receive_paragraph(&paragraph, &mut sentences);
    sentences.into_iter().collect()
}

fn receive_paragraph(paragraph: &str, sentences: &mut BTreeSet<String>) {
    let tokens = lexical_tokens(paragraph);
    let mut current = Vec::<String>::new();
    for token in tokens {
        current.push(token.clone());
        if matches!(token.as_str(), "." | "!" | "?") {
            receive_sentence(&current, sentences);
            current.clear();
        }
    }
    if !current.is_empty() {
        receive_sentence(&current, sentences);
    }
}

fn receive_sentence(tokens: &[String], sentences: &mut BTreeSet<String>) {
    let word_extent = tokens
        .iter()
        .filter(|token| token.chars().any(char::is_alphanumeric))
        .count();
    if (5..=96).contains(&word_extent) {
        sentences.insert(render_tokens(tokens.iter().map(String::as_str)));
    }
}

fn relation_features(text: &str) -> BTreeSet<String> {
    let surfaces = lexical_tokens(text)
        .into_iter()
        .filter(|token| token.chars().any(char::is_alphanumeric))
        .map(|token| token.to_lowercase())
        .collect::<Vec<_>>();
    let mut features = surfaces
        .iter()
        .map(|surface| format!("word:{surface}"))
        .collect::<BTreeSet<_>>();
    let mut extent = 2usize;
    while extent <= 4 && extent <= surfaces.len() {
        for region in surfaces.windows(extent) {
            features.insert(format!("region:{extent}:{}", region.join("\u{1f}")));
        }
        extent += 1;
    }
    features
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}
