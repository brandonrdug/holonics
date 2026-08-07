use super::*;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum AgenticLanguageCodecProgram {
    Origin,
    Revision(AgenticLanguageCodecVersion),
}

pub(super) type AgenticReflectiveCodecRuntime = ReflectiveRuntime<
    AgenticLanguageCodecProgram,
    TrainingEcology,
    AgenticLanguageCodecFace,
    String,
>;

pub(super) struct AgenticCodecReflectionExecutor;

impl ReflectiveCodecExecutor<AgenticLanguageCodecProgram, TrainingEcology, AgenticLanguageCodecFace>
    for AgenticCodecReflectionExecutor
{
    type Emission = ();
    type Obstruction = String;

    fn receive(
        &mut self,
        _program: &AgenticLanguageCodecProgram,
        _instruction: u64,
        environment: TrainingEcology,
        face: &AgenticLanguageCodecFace,
    ) -> Result<CodecStep<TrainingEcology, ()>, CodecObstruction<TrainingEcology, String>> {
        Ok(CodecStep::Reflect {
            environment,
            receiver: ReceiverId(face.receiver),
            emission: (),
        })
    }
}

pub(super) struct AgenticCodecTrainingExecutor {
    pub(super) proposal: Option<TrainingCultivationProposal>,
}

impl ReflectiveCodecExecutor<AgenticLanguageCodecProgram, TrainingEcology, AgenticLanguageCodecFace>
    for AgenticCodecTrainingExecutor
{
    type Emission = ();
    type Obstruction = String;

    fn receive(
        &mut self,
        _program: &AgenticLanguageCodecProgram,
        _instruction: u64,
        mut environment: TrainingEcology,
        _face: &AgenticLanguageCodecFace,
    ) -> Result<CodecStep<TrainingEcology, ()>, CodecObstruction<TrainingEcology, String>> {
        if let Some(proposal) = self.proposal.take() {
            if let Err(refusal) = environment.commit_views(proposal) {
                return Err(CodecObstruction {
                    environment,
                    obstruction: refusal.error,
                });
            }
        }
        Ok(CodecStep::Advance {
            environment,
            emission: (),
        })
    }
}

pub(super) fn codec_crossing_error(error: CodecCrossingError<String, ()>) -> AgenticLanguageError {
    match error {
        CodecCrossingError::Runtime(error)
        | CodecCrossingError::ReturnCouldNotCommit { error, .. } => {
            AgenticLanguageError::CodecRuntime(error)
        }
        CodecCrossingError::Executor(error) => AgenticLanguageError::CodecTraining(error),
    }
}

pub(super) fn reflective_codec_answer_candidate(
    version: &AgenticLanguageCodecVersion,
    episode: &LanguageEpisode,
    _question: &AgenticLanguageQuestion,
    received_prompt: &str,
    contextual_dialogue: &BTreeSet<String>,
    matched_regions: BTreeSet<Vec<String>>,
    direct_content: BTreeSet<String>,
) -> Result<AnswerCandidate, AgenticLanguageError> {
    let mut codec_versions = episode.codec_versions.to_owned();
    codec_versions.insert(version.identity.to_owned());
    let mut tokens = Vec::new();
    let mut phases = Vec::new();
    let mut conditioning_passages = Vec::new();
    let mut evidence_sources = version.output.lineage.clone();
    evidence_sources.insert(version.returned_by.clone());
    evidence_sources.insert(version.output.identity.clone());
    let returned_regions = (0..matched_regions.len()).collect::<BTreeSet<_>>();
    for (phase_at, region) in version.output.ordered_regions.iter().enumerate() {
        let passage_identity = format!("{}/region/{phase_at}", version.output.identity);
        let passage_text =
            render_tokens(lexical_tokens(&region.join(" ")).iter().map(String::as_str));
        if passage_text.trim().is_empty() {
            continue;
        }
        conditioning_passages.push(MorphologicalLanguagePassage::new(
            passage_identity.clone(),
            version.returned_by.clone(),
            version.output.receiver,
            passage_text.clone(),
        ));
        let emitted_start = tokens.len();
        for surface in lexical_tokens(&passage_text) {
            let returned_event_count = tokens
                .len()
                .checked_add(1)
                .ok_or(AgenticLanguageError::CarrierExtent)?;
            tokens.push(MorphologicalGeneratedToken {
                token: surface,
                transport: MorphologicalTransport::RelationalRealization,
                lexical_horizons: BTreeSet::new(),
                forward_mark_horizon: 0,
                reverse_mark_horizon: 0,
                recurrent_sources: evidence_sources.clone(),
                recurrent_context_sources: version.output.lineage.clone(),
                caused_sources: evidence_sources.clone(),
                caused_passages: BTreeSet::from([passage_identity.clone()]),
                supporting_clauses: BTreeSet::from([version.identity.clone()]),
                returned_event_count,
            });
        }
        let emitted_end = tokens.len();
        if emitted_end == emitted_start {
            continue;
        }
        phases.push(MorphologicalResponsePhase {
            entry_clause: version.identity.clone(),
            clauses: BTreeSet::from([version.identity.clone()]),
            sources: evidence_sources.clone(),
            passages: BTreeSet::from([passage_identity]),
            boundary: Some(MorphologicalBoundary::Sentence),
            discharged_obligations: BTreeSet::from([0]),
            discharged_regions: (phase_at == 0)
                .then(|| BTreeMap::from([(0, returned_regions.clone())]))
                .unwrap_or_default(),
            discharged_features: (phase_at == 0)
                .then(|| BTreeMap::from([(0, direct_content.clone())]))
                .unwrap_or_default(),
            entry_lexical_horizons: BTreeSet::new(),
            entry_recurrence_multiplicities: BTreeSet::new(),
            emitted_start,
            emitted_end,
        });
    }
    if tokens.is_empty() || phases.is_empty() {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    }
    let generated = MorphologicalGeneratedCurrent {
        text: render_tokens(tokens.iter().map(|token| token.token.as_str())),
        tokens,
        phases,
        rest: MorphologicalResponseRest::Closed,
        caused_seams: Vec::new(),
    };
    let causal_current_states_formed = version
        .input
        .ordered_regions
        .len()
        .checked_add(version.output.ordered_regions.len())
        .and_then(|extent| extent.checked_add(matched_regions.len()))
        .ok_or(AgenticLanguageError::CarrierExtent)?;
    Ok(AnswerCandidate {
        generated,
        episode_identities: BTreeSet::from([episode.identity.clone()]),
        evidence_sources,
        conditioning_passages,
        discharged_query_faces: direct_content,
        reflection: MorphologicalReflectionReceipt {
            shared_conditioned_bodies: 1,
            whole_body_forks: 0,
            shared_current_forks: 0,
            causal_current_states_formed,
            conduct_equivalent_states_glued: 0,
            peak_live_current_states: 1,
            returned_events_carried: 0,
            terminal_return_materializations: 0,
        },
        inherited_surfaces: version.output.ordered_regions.iter().cloned().collect(),
        received_prompt: received_prompt.to_owned(),
        contextual_dialogue: contextual_dialogue.clone(),
        obligation_population: 1,
        local_region_fiber: ExactAnswerRegionFiber::from_parts(
            LocalSet::from_iter(returned_regions
                .iter()
                .copied()
                .map(|region| AgenticAnswerRegionIdentity {
                    obligation: 0,
                    region,
                })),
            LocalSet::from_iter(returned_regions
                .iter()
                .copied()
                .map(|region| AgenticAnswerRegionIdentity {
                    obligation: 0,
                    region,
                })),
        )?,
        ordered_query_regions: matched_regions,
        revision_horizon: episode.revision,
        corrective: version.aperture == AgenticLanguageCodecAperture::AnswerRelation,
        composed_current_population: 0,
        // The target episode identifies the face revised by the theorem return; its old selected
        // relation current is lineage, not the operative current for this later deed. Replaying
        // it here would let the pre-kernel diagnosis displace the new world-returned current.
        relational_thought: None,
        relational_thoughts: Vec::new(),
        codec_versions,
        cultivated_codec_paths: Vec::new(),
        retained_alternatives: Vec::new(),
    })
}

/// Receive source language as exact relation incidence and cast one closed thought current into
/// the existing return machinery. The inherited grammar supplies only the English transduction;
/// every subject/object face, relation edge, join, and evidence lineage comes from `passages`.
pub(super) fn codec_training_views(
    tokens: &[String],
) -> Result<Vec<TrainingView>, AgenticLanguageError> {
    let words = tokens
        .iter()
        .filter(|token| token.chars().any(char::is_alphanumeric))
        .cloned()
        .collect::<Vec<_>>();
    if words.is_empty() {
        return Ok(Vec::new());
    }
    let mut views = Vec::with_capacity(words.len().saturating_mul(2));
    for (chart, reverse) in [("question-prefix", false), ("question-suffix", true)] {
        for horizon in 1..=words.len() {
            let (region, complementary_context) = if reverse {
                (
                    &words[words.len() - horizon..],
                    &words[..words.len() - horizon],
                )
            } else {
                (&words[..horizon], &words[horizon..])
            };
            let horizon =
                u64::try_from(horizon).map_err(|_| AgenticLanguageError::CarrierExtent)?;
            views.push(TrainingView {
                faces: vec![SourceFace::new(
                    FaceAddress::new("question-region", 0),
                    region.join(" ").into_bytes(),
                )],
                parameters: BTreeMap::from([
                    ("aperture".to_owned(), "answer-relation".to_owned()),
                    ("chart".to_owned(), chart.to_owned()),
                    ("context".to_owned(), complementary_context.join(" ")),
                    ("horizon".to_owned(), horizon.to_string()),
                ]),
            });
        }
    }
    Ok(views)
}

pub(super) fn first_region_offset(surface: &[String], region: &[String]) -> usize {
    if region.is_empty() || region.len() > surface.len() {
        return usize::MAX;
    }
    surface
        .windows(region.len())
        .position(|window| window == region)
        .unwrap_or(usize::MAX)
}

pub(super) fn render_surface(tokens: &[String]) -> String {
    tokens.join(" ")
}

pub(super) fn target_codec_face(
    episode: &LanguageEpisode,
    lineage: Option<&AnswerLineage>,
) -> AgenticLanguageCodecFace {
    let mut ordered_regions = BTreeSet::new();
    if let Some(lineage) = lineage {
        if !lineage.question_surface.is_empty() {
            ordered_regions.insert(
                lineage
                    .question_surface
                    .iter()
                    .filter(|surface| surface.chars().any(char::is_alphanumeric))
                    .map(|surface| surface.to_lowercase())
                    .collect(),
            );
        }
        if !lineage.surface.is_empty() {
            ordered_regions.insert(
                lineage
                    .surface
                    .iter()
                    .filter(|surface| surface.chars().any(char::is_alphanumeric))
                    .map(|surface| surface.to_lowercase())
                    .collect(),
            );
        }
    }
    for passage in &episode.passages {
        let region = word_surfaces(&passage.text);
        if !region.is_empty() {
            ordered_regions.insert(region);
        }
    }
    ordered_regions.retain(|region| !region.is_empty());
    let mut causal_lineage = BTreeSet::from([episode.identity.clone()]);
    causal_lineage.extend(episode.evidence_sources.iter().cloned());
    causal_lineage.extend(episode.codec_versions.iter().cloned());
    if let Some(lineage) = lineage {
        causal_lineage.extend(lineage.supporting_episodes.iter().cloned());
        causal_lineage.extend(lineage.evidence_sources.iter().cloned());
    }
    AgenticLanguageCodecFace {
        identity: format!("{}/face", episode.identity),
        receiver: episode
            .passages
            .first()
            .map_or(0, |passage| passage.receiver),
        ordered_regions,
        lineage: causal_lineage,
    }
}
