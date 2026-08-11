use super::*;

impl AgenticLanguageEcology {
    /// Conduct a later question through committed reflective codec versions.
    ///
    /// Ordinary episode recruitment still runs in parallel. This path is distinct: the later
    /// question reaches the reified *input* face of a correction, while the emitted current is
    /// caused by the installed *output* face. That cross-face transport is the behavioral force
    /// which a passive correction record cannot provide.
    pub(super) fn reflective_codec_answers(
        &self,
        question: &AgenticLanguageQuestion,
        received_prompt: &str,
        contextual_dialogue: &BTreeSet<String>,
        formal_returns_only: bool,
    ) -> Result<Vec<AnswerCandidate>, AgenticLanguageError> {
        if self.codec_program_versions().next().is_none() {
            return Ok(Vec::new());
        }
        let prompt_surfaces = word_surfaces(received_prompt);
        let charge = self.inherited_body.charge(received_prompt)?;
        let direct_content = prompt_surfaces
            .iter()
            .filter(|surface| !charge.operator_features.contains(*surface))
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut reached = BTreeSet::new();
        for surface in &prompt_surfaces {
            if let Some(versions) = self.codec_runtime.recruited_codecs(surface) {
                reached.extend(versions.iter().copied());
            }
        }

        let mut answers = Vec::new();
        for codec_id in reached {
            let Some(codec) = self.codec_runtime.codec(codec_id) else {
                return Err(AgenticLanguageError::CarrierExtent);
            };
            let AgenticLanguageCodecProgram::Revision(version) = &codec.program else {
                continue;
            };
            if (version.aperture == AgenticLanguageCodecAperture::FormalReturn)
                != formal_returns_only
            {
                continue;
            }
            if self.obstructed_episodes.contains(&version.output_episode) {
                continue;
            }
            let face_surfaces = version
                .input
                .ordered_regions
                .iter()
                .chain(&version.output.ordered_regions)
                .flat_map(|region| region.iter().cloned())
                .collect::<BTreeSet<_>>();
            if direct_content.is_empty()
                || (version.aperture != AgenticLanguageCodecAperture::FormalReturn
                    && !direct_content.is_subset(&face_surfaces))
            {
                continue;
            }
            let matched_regions = version
                .input
                .ordered_regions
                .iter()
                .flat_map(|region| common_ordered_regions(&prompt_surfaces, region))
                .filter(|region| {
                    region.len() >= 2
                        && region
                            .iter()
                            .any(|surface| !charge.operator_features.contains(surface))
                })
                .collect::<BTreeSet<_>>();
            if matched_regions.is_empty() {
                continue;
            }
            let Some(episode) = self
                .episodes
                .iter()
                .find(|episode| episode.identity == version.output_episode)
            else {
                return Err(AgenticLanguageError::CarrierExtent);
            };
            if !episode.answerable {
                continue;
            }
            answers.push(reflective_codec_answer_candidate(
                version,
                episode,
                question,
                received_prompt,
                contextual_dialogue,
                matched_regions,
                direct_content.clone(),
            )?);
        }
        Ok(answers)
    }

    /// Rebind recurrent cross-occurrence correction paths to a new question face.
    ///
    /// This is vertical training rather than direct version transport. A path is absent until its
    /// exact template has returned through at least `CODEC_MINIMUM_RECURRENCE` distinct
    /// correction events. Every afforded prefix/suffix receiver and every path-distinct
    /// consequence remains present for ordinary answer selection; no recurrence is normalized
    /// into a score.
    pub(super) fn cultivated_codec_answers(
        &self,
        question: &AgenticLanguageQuestion,
        received_prompt: &str,
        contextual_dialogue: &BTreeSet<String>,
    ) -> Result<Vec<AnswerCandidate>, AgenticLanguageError> {
        let codec_training = self.codec_training()?;
        if codec_training.active_template_count() == 0 {
            return Ok(Vec::new());
        }
        let views = codec_training_views(&lexical_tokens(received_prompt))?;
        let direct_content = word_surfaces(received_prompt)
            .into_iter()
            .collect::<BTreeSet<_>>();
        let mut answers = Vec::new();
        for view in views {
            let prediction = codec_training
                .predict_exact(&view.faces, &view.parameters)
                .map_err(AgenticLanguageError::CodecTraining)?;
            for candidate in prediction.candidates {
                let text = String::from_utf8(candidate.path.consequence.clone()).map_err(|_| {
                    AgenticLanguageError::CodecTraining(
                        "a cultivated language consequence is not exact UTF-8".to_owned(),
                    )
                })?;
                let tokens = lexical_tokens(&text);
                if tokens.is_empty()
                    || !tokens
                        .last()
                        .is_some_and(|token| matches!(token.as_str(), "." | "!" | "?"))
                {
                    continue;
                }

                let mut version_lineage = BTreeSet::new();
                let mut evidence_sources = BTreeSet::new();
                let mut episode_identities = BTreeSet::new();
                let mut conditioning_passages = Vec::new();
                let mut revision_horizon = 0u64;
                let mut path_receipts = Vec::new();
                for support in &candidate.support {
                    let fiber = TransductionFiber {
                        template: support.template.clone(),
                        parameters: support.parameters.clone(),
                    };
                    let mut support_lineage = BTreeSet::new();
                    for version in self
                        .codec_program_versions()
                        .filter(|version| version.cultivation.observed_fibers.contains(&fiber))
                    {
                        support_lineage.insert(version.identity.clone());
                        version_lineage.insert(version.identity.clone());
                        version_lineage.extend(version.parents.iter().cloned());
                        evidence_sources.insert(format!("dialogue/{}", version.returned_by));
                        episode_identities.insert(version.output_episode.clone());
                        if let Some(episode) = self
                            .episodes
                            .iter()
                            .find(|episode| episode.identity == version.output_episode)
                        {
                            revision_horizon = revision_horizon.max(episode.revision);
                            for passage in &episode.passages {
                                if !conditioning_passages.iter().any(
                                    |prior: &MorphologicalLanguagePassage| {
                                        prior.identity == passage.identity
                                    },
                                ) {
                                    conditioning_passages.push(passage.clone());
                                }
                            }
                        }
                    }
                    if support_lineage.is_empty() {
                        return Err(AgenticLanguageError::CodecTraining(
                            "an active codec path has no founding version lineage".to_owned(),
                        ));
                    }
                    path_receipts.push(AgenticLanguageCodecPathReceipt {
                        template: support.template.clone(),
                        receiver_parameters: support.parameters.clone(),
                        recurrence: support.recurrence,
                        consequence: text.clone(),
                        version_lineage: support_lineage,
                    });
                }
                if version_lineage.is_empty() {
                    continue;
                }

                let caused_passages = conditioning_passages
                    .iter()
                    .map(|passage| passage.identity.clone())
                    .collect::<BTreeSet<_>>();
                let generated_tokens = tokens
                    .iter()
                    .enumerate()
                    .map(|(at, token)| {
                        Ok(MorphologicalGeneratedToken {
                            token: token.clone(),
                            transport: MorphologicalTransport::RelationalRealization,
                            lexical_horizons: BTreeSet::new(),
                            forward_mark_horizon: 0,
                            reverse_mark_horizon: 0,
                            recurrent_sources: evidence_sources.clone(),
                            recurrent_context_sources: version_lineage.clone(),
                            caused_sources: evidence_sources.clone(),
                            caused_passages: caused_passages.clone(),
                            supporting_clauses: version_lineage.clone(),
                            returned_event_count: at
                                .checked_add(1)
                                .ok_or(AgenticLanguageError::CarrierExtent)?,
                        })
                    })
                    .collect::<Result<Vec<_>, AgenticLanguageError>>()?;
                // The active route is admitted only at the exact complementary context carried
                // in the receiver parameters, so its local return is the complete received
                // question face rather than the copied suffix alone.
                let ordered_query_regions = BTreeSet::from([word_surfaces(received_prompt)]);
                let phase = MorphologicalResponsePhase {
                    entry_clause: "cultivated-answer-relation".to_owned(),
                    clauses: version_lineage.clone(),
                    sources: evidence_sources.clone(),
                    passages: caused_passages.clone(),
                    boundary: Some(MorphologicalBoundary::Sentence),
                    discharged_obligations: BTreeSet::from([0]),
                    discharged_regions: BTreeMap::from([(0, BTreeSet::from([0]))]),
                    discharged_features: BTreeMap::from([(0, direct_content.clone())]),
                    entry_lexical_horizons: BTreeSet::new(),
                    entry_recurrence_multiplicities: candidate
                        .support
                        .iter()
                        .map(|support| support.recurrence)
                        .collect(),
                    emitted_start: 0,
                    emitted_end: generated_tokens.len(),
                };
                let inherited_surfaces = conditioning_passages
                    .iter()
                    .map(|passage| lexical_tokens(&passage.text))
                    .collect();
                answers.push(AnswerCandidate {
                    generated: MorphologicalGeneratedCurrent {
                        text,
                        tokens: generated_tokens,
                        phases: vec![phase],
                        rest: MorphologicalResponseRest::Closed,
                        caused_seams: Vec::new(),
                    },
                    episode_identities,
                    evidence_sources,
                    conditioning_passages,
                    discharged_query_faces: direct_content.clone(),
                    reflection: MorphologicalReflectionReceipt {
                        shared_conditioned_bodies: 1,
                        whole_body_forks: 0,
                        shared_current_forks: 0,
                        causal_current_states_formed: candidate.support.len(),
                        conduct_equivalent_states_glued: 0,
                        peak_live_current_states: 1,
                        returned_events_carried: 0,
                        terminal_return_materializations: 0,
                    },
                    inherited_surfaces,
                    received_prompt: received_prompt.to_owned(),
                    contextual_dialogue: contextual_dialogue.clone(),
                    obligation_population: 1,
                    local_region_fiber: ExactAnswerRegionFiber::from_parts(
                        LocalSet::from([AgenticAnswerRegionIdentity {
                            obligation: 0,
                            region: 0,
                        }]),
                        LocalSet::from([AgenticAnswerRegionIdentity {
                            obligation: 0,
                            region: 0,
                        }]),
                    )?,
                    ordered_query_regions,
                    revision_horizon,
                    corrective: true,
                    composed_current_population: 0,
                    relational_thought: None,
                    relational_thoughts: Vec::new(),
                    codec_versions: version_lineage,
                    cultivated_codec_paths: path_receipts,
                    retained_alternatives: Vec::new(),
                });
            }
        }
        let mut glued = BTreeMap::<String, AnswerCandidate>::new();
        for mut answer in answers {
            let key = answer.generated.text.clone();
            let Some(prior) = glued.get_mut(&key) else {
                glued.insert(key, answer);
                continue;
            };
            prior
                .episode_identities
                .append(&mut answer.episode_identities);
            prior.evidence_sources.append(&mut answer.evidence_sources);
            prior
                .discharged_query_faces
                .append(&mut answer.discharged_query_faces);
            prior.codec_versions.append(&mut answer.codec_versions);
            prior
                .ordered_query_regions
                .append(&mut answer.ordered_query_regions);
            prior.revision_horizon = prior.revision_horizon.max(answer.revision_horizon);
            prior.reflection.causal_current_states_formed = prior
                .reflection
                .causal_current_states_formed
                .checked_add(answer.reflection.causal_current_states_formed)
                .ok_or(AgenticLanguageError::CarrierExtent)?;
            prior.reflection.conduct_equivalent_states_glued = prior
                .reflection
                .conduct_equivalent_states_glued
                .checked_add(1)
                .ok_or(AgenticLanguageError::CarrierExtent)?;
            for passage in answer.conditioning_passages {
                if !prior
                    .conditioning_passages
                    .iter()
                    .any(|existing| existing.identity == passage.identity)
                {
                    prior.conditioning_passages.push(passage);
                }
            }
            prior.inherited_surfaces.extend(answer.inherited_surfaces);
            prior
                .cultivated_codec_paths
                .extend(answer.cultivated_codec_paths);
            prior.cultivated_codec_paths.sort();
            prior.cultivated_codec_paths.dedup();
        }
        let _ = question;
        Ok(glued.into_values().collect())
    }

    pub(super) fn grounded_episode_answers(
        &self,
        question: &AgenticLanguageQuestion,
        received_prompt: &str,
        contextual_dialogue: &BTreeSet<String>,
    ) -> Result<Vec<AnswerCandidate>, AgenticLanguageError> {
        let surfaces = word_surfaces(received_prompt);
        let inherited_charge = self.inherited_body.charge(received_prompt)?;
        let content_surfaces = surfaces
            .iter()
            .filter(|surface| !inherited_charge.operator_features.contains(*surface))
            .cloned()
            .collect::<BTreeSet<_>>();
        let novel_cofaces = unordered_surface_pairs(&content_surfaces)
            .into_iter()
            .filter(|coface| !self.inherited_cofaces.contains(coface))
            .collect::<BTreeSet<_>>();
        let mut candidates = BTreeSet::<usize>::new();
        for surface in &surfaces {
            if let Some(episodes) = self.episode_surface_atlas.get(surface) {
                candidates.extend(episodes.iter().copied());
            }
        }
        let candidate_indices = maximal_episode_indices(
            received_prompt,
            &self.episodes,
            candidates.into_iter().collect(),
            &inherited_charge.operator_features,
            self.spec.generation.maximum_observed_tokens,
            &self.obstructed_episodes,
        );
        // Episode order is retained owner testimony. No application-local commutation law
        // authorizes an indexed worker wave over continuing morphology, so each episode crosses
        // the language owner in order and that owner realizes its admitted local work.
        let mut answers = Vec::new();
        for episode_at in &candidate_indices {
            let episode = self
                .episodes
                .get(*episode_at)
                .ok_or(AgenticLanguageError::CarrierExtent)?;
            if !episode.answerable || self.obstructed_episodes.contains(&episode.identity) {
                continue;
            }
            let episode_surfaces = &episode.routing_surfaces;
            if content_surfaces.is_empty()
                || (!novel_cofaces.is_empty()
                    && !novel_cofaces.iter().any(|(left, right)| {
                        episode_surfaces.contains(left) && episode_surfaces.contains(right)
                    }))
            {
                continue;
            }
            let realized;
            let ecology = if let Some(ecology) = episode.ecology.as_ref() {
                ecology
            } else {
                realized = MorphologicalLanguageEcology::condition(
                    &episode.passages,
                    self.action,
                    self.worker_threads,
                )?;
                &realized
            };
            let charge = ecology.charge(received_prompt)?;
            if !charge_is_grounded(&charge, &episode.evidence_sources) {
                continue;
            }
            let generation = ecology.generate_currents(received_prompt, self.spec.generation)?;
            match select_generated_answer(
                &generation.outputs,
                &episode.evidence_sources,
                &BTreeSet::new(),
                &generation.reflection,
                &episode.passages,
                BTreeSet::from([episode.identity.clone()]),
                episode.codec_versions.clone(),
                received_prompt,
                contextual_dialogue,
                generation.charge.obligations.len(),
                &question_local_regions(&generation.charge),
                &question_regions(&generation.charge),
                episode.revision,
                episode.role == AgenticDialogueRole::UserCorrection,
            ) {
                Ok(candidate) => answers.push(candidate),
                Err(AgenticLanguageError::NoGroundedLanguageReturn) => {}
                Err(error) => return Err(error),
            }
        }
        answers.extend(self.reflective_codec_answers(
            question,
            received_prompt,
            contextual_dialogue,
            false,
        )?);
        answers.extend(self.cultivated_codec_answers(
            question,
            received_prompt,
            contextual_dialogue,
        )?);
        let relational_episodes = candidate_indices
            .iter()
            .filter_map(|episode_at| self.episodes.get(*episode_at))
            .filter(|episode| {
                episode.answerable && !self.obstructed_episodes.contains(&episode.identity)
            })
            .collect::<Vec<_>>();
        let relational_passages = relational_episodes
            .iter()
            .flat_map(|episode| episode.passages.iter().cloned())
            .collect::<Vec<_>>();
        let relational_episode_identities = relational_episodes
            .iter()
            .map(|episode| episode.identity.clone())
            .collect::<BTreeSet<_>>();
        let relational_codec_versions = relational_episodes
            .iter()
            .flat_map(|episode| episode.codec_versions.iter().cloned())
            .collect::<BTreeSet<_>>();
        let revision_horizon = relational_episodes
            .iter()
            .map(|episode| episode.revision)
            .max()
            .unwrap_or(0);
        let corrective = relational_episodes
            .iter()
            .any(|episode| episode.role == AgenticDialogueRole::UserCorrection);
        answers.extend(relational_answer_candidates(
            &self.relational_body,
            &relational_passages,
            &question.text,
            received_prompt,
            contextual_dialogue,
            relational_episode_identities,
            relational_codec_versions,
            revision_horizon,
            self.spec.thought_receiver_horizon,
            corrective,
        )?);
        Ok(answers)
    }

    /// Materialize the selected answer current through one caller-retained physical executor.
    ///
    /// This is the agentic body's own generation mouth. The selected current's question event and
    /// every self-emanated return cross the supplied executor, so a caller which mounted a card at
    /// [`AgenticLanguageEcology::condition_with_executor`] keeps that carrier across the answer
    /// rather than silently rebuilding a private host pool between conditioning and emanation.
    pub(super) fn prepare_answer_with_executor(
        &self,
        question: AgenticLanguageQuestion,
        world_deed: Option<String>,
        world_sections: &[MorphologicalLanguagePassage],
        candidates: Vec<AnswerCandidate>,
        world_thought_fibers: &[RelationalThoughtFiber],
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<PreparedWorldAnswer, AgenticLanguageError> {
        let selected = select_answer_candidate(candidates)?;
        if let Some(deed) = world_deed.as_deref() {
            if !world_thought_fibers.is_empty()
                && !selected
                    .relational_thought
                    .as_ref()
                    .is_some_and(|current| self.relational_returns.can_bind_answer(deed, current))
            {
                return Err(AgenticLanguageError::NoGroundedLanguageReturn);
            }
        }
        let generated = selected.generated.into_materialized_return_with_executor(
            &selected.received_prompt,
            self.action,
            executor,
        )?;
        let local_identity = format!("episode-{}", self.next_episode);
        let next_episode = self
            .next_episode
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let mut founded = Vec::<LanguageEpisode>::new();
        if world_deed.is_some() {
            for (section_at, section) in world_sections.iter().enumerate() {
                let identity = format!("{local_identity}/world/{section_at}");
                let passages = vec![section.clone()];
                let routing_surfaces = word_surfaces(&section.text)
                    .into_iter()
                    .collect::<BTreeSet<_>>();
                founded.push(LanguageEpisode {
                    identity,
                    origin: EpisodeOrigin::ReturnedWorld,
                    role: AgenticDialogueRole::WorldObservation,
                    revision: self
                        .dialogue
                        .iter()
                        .find(|occurrence| occurrence.identity == section.identity)
                        .map(|occurrence| occurrence.ordinal)
                        .unwrap_or(0),
                    answerable: true,
                    passages,
                    routing_surfaces,
                    evidence_sources: BTreeSet::from([section.source.clone()]),
                    ecology: None,
                    relational_thought: None,
                    codec_versions: BTreeSet::new(),
                });
            }
        }
        let answer_identity = format!("{local_identity}/answer");
        let answer_source = answer_identity.clone();
        let mut answer_causes = selected.episode_identities.clone();
        if let Some(deed) = &world_deed {
            answer_causes.insert(deed.clone());
        }
        answer_causes.extend(selected.contextual_dialogue.iter().cloned());
        if self.dialogue_identities.contains(&answer_identity) {
            return Err(AgenticLanguageError::DuplicateDialogueOccurrence(
                answer_identity,
            ));
        }
        let answer_revision = self.next_dialogue;
        let next_dialogue = self
            .next_dialogue
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let dialogue_occurrences = self
            .standing
            .dialogue_occurrences
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let dialogue = AgenticDialogueOccurrence {
            ordinal: answer_revision,
            identity: answer_identity.clone(),
            role: AgenticDialogueRole::EmanatedAnswer,
            receiver: question.receiver,
            text: generated.text.clone(),
            target: Some(question.identity.clone()),
            caused_by: answer_causes,
        };
        // Retain the answer's caused phase sections. Flattening the whole answer into one future
        // passage made contact with one clause replay unrelated clauses as though they were one
        // indivisible source occurrence.
        let mut answer_passages = Vec::with_capacity(generated.phases.len());
        for (phase_at, phase) in generated.phases.iter().enumerate() {
            let phase_tokens = generated
                .tokens
                .get(phase.emitted_start..phase.emitted_end)
                .ok_or(AgenticLanguageError::CarrierExtent)?;
            answer_passages.push(MorphologicalLanguagePassage::new(
                format!("{answer_identity}/return/{phase_at}"),
                answer_source.clone(),
                question.receiver,
                render_tokens(phase_tokens.iter().map(|token| token.token.as_str())),
            ));
        }
        let answer_routing_surfaces = word_surfaces(&generated.text)
            .into_iter()
            .collect::<BTreeSet<_>>();
        founded.push(LanguageEpisode {
            identity: answer_identity.clone(),
            origin: EpisodeOrigin::ReturnedAnswer,
            role: AgenticDialogueRole::EmanatedAnswer,
            revision: answer_revision,
            answerable: true,
            passages: answer_passages,
            routing_surfaces: answer_routing_surfaces,
            evidence_sources: BTreeSet::from([answer_source]),
            ecology: None,
            relational_thought: selected.relational_thought.clone(),
            codec_versions: selected.codec_versions.clone(),
        });

        let locally_conditioned_episode_organs = self
            .standing
            .locally_conditioned_episode_organs
            .checked_add(founded.len())
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let generated_answers = self
            .standing
            .generated_answers
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let locally_conditioned_episodes = founded
            .iter()
            .map(|episode| episode.identity.clone())
            .collect::<BTreeSet<_>>();
        let lineage = AnswerLineage {
            world_deed: world_deed.clone(),
            supporting_episodes: selected.episode_identities.clone(),
            evidence_sources: selected.evidence_sources.clone(),
            surface: lexical_tokens(&generated.text),
            question_surface: lexical_tokens(&question.text),
            codec_versions: selected.codec_versions.clone(),
            cultivated_codec_paths: selected.cultivated_codec_paths.clone(),
        };

        let discharged_obligations = LocalSet::from_iter(
            generated
                .phases
                .iter()
                .flat_map(|phase| phase.discharged_obligations.iter().copied()),
        );
        let caused_sentence_boundaries = generated
            .phases
            .iter()
            .filter(|phase| phase.boundary.is_some())
            .count();
        let required_local_regions = selected.local_region_fiber.required;
        let returned_local_region_identities = selected.local_region_fiber.returned;
        let required_obligations =
            LocalSet::from_iter(required_local_regions.iter().map(|region| region.obligation));
        let closed_by_returned_obligations = generated.rest == MorphologicalResponseRest::Closed
            && discharged_obligations == required_obligations
            && returned_local_region_identities == required_local_regions
            && caused_sentence_boundaries > 0;
        let closure = AgenticAnswerClosure {
            obligation_population: selected.obligation_population,
            discharged_obligations: discharged_obligations.clone(),
            local_region_population: required_local_regions.len(),
            returned_local_regions: returned_local_region_identities.len(),
            required_local_regions,
            returned_local_region_identities,
            caused_sentence_boundaries,
            observation_aperture: self.spec.generation.maximum_observed_tokens,
            closed_by_returned_obligations,
        };

        let answer = AgenticLanguageAnswer {
            question,
            text: generated.text.clone(),
            generated,
            supporting_episode_identities: selected.episode_identities,
            world_deed,
            evidence_sources: selected.evidence_sources,
            selection: selected.selection,
            retained_alternatives: selected.retained_alternatives,
            reflection: selected.reflection,
            novel_contiguous_surface: selected.novel_contiguous_surface,
            locally_conditioned_episodes,
            answer_episode_identity: answer_identity,
            contextual_dialogue: selected.contextual_dialogue,
            closure,
            operative_codec_versions: selected.codec_versions,
            cultivated_codec_paths: selected.cultivated_codec_paths,
            relational_thought: selected.relational_thought,
            relational_thoughts: selected.relational_thoughts,
        };
        Ok(PreparedWorldAnswer {
            answer: Some(answer),
            founded,
            lineage: Some(lineage),
            dialogue: Some(dialogue),
            next_dialogue,
            dialogue_occurrences,
            next_episode,
            locally_conditioned_episode_organs,
            generated_answers,
            next_founded_return: 0,
        })
    }

    pub(super) fn commit_prepared_answer(
        &mut self,
    ) -> Result<AgenticLanguageAnswer, AgenticLanguageError> {
        let mut prepared = self
            .open
            .as_mut()
            .and_then(|open| open.prepared_answer.take())
            .ok_or(AgenticLanguageError::NoGroundedLanguageReturn)?;
        if let Err(error) = self.advance_prepared_answer(&mut prepared) {
            self.open
                .as_mut()
                .expect("the refused answer retains its open deed")
                .prepared_answer = Some(prepared);
            return Err(error);
        }
        Ok(self.commit_prepared_answer_standing(prepared))
    }

    pub(super) fn commit_pending_local_answer(
        &mut self,
    ) -> Result<AgenticLanguageAnswer, AgenticLanguageError> {
        let mut pending = self
            .pending_local_answer
            .take()
            .ok_or(AgenticLanguageError::NoGroundedLanguageReturn)?;
        if let Err(error) = self.advance_prepared_answer(&mut pending.prepared) {
            self.pending_local_answer = Some(pending);
            return Err(error);
        }
        Ok(self.commit_prepared_answer_standing(pending.prepared))
    }

    pub(super) fn advance_prepared_answer(
        &mut self,
        prepared: &mut PreparedWorldAnswer,
    ) -> Result<(), AgenticLanguageError> {
        let preflight = prepared.dialogue.as_ref().is_some_and(|dialogue| {
            self.next_dialogue == dialogue.ordinal
                && self.next_dialogue.checked_add(1) == Some(prepared.next_dialogue)
                && !self.dialogue_identities.contains(&dialogue.identity)
        }) && self.next_episode.checked_add(1) == Some(prepared.next_episode)
            && self.standing.dialogue_occurrences.checked_add(1)
                == Some(prepared.dialogue_occurrences)
            && self
                .standing
                .locally_conditioned_episode_organs
                .checked_add(prepared.founded.len())
                == Some(prepared.locally_conditioned_episode_organs)
            && self.standing.generated_answers.checked_add(1) == Some(prepared.generated_answers);
        if !preflight {
            return Err(AgenticLanguageError::CarrierExtent);
        }
        while prepared.next_founded_return < prepared.founded.len() {
            let episode = &prepared.founded[prepared.next_founded_return];
            self.relational_body
                .receive_with_workers(&episode.passages, self.worker_threads)?;
            prepared.next_founded_return += 1;
        }
        Ok(())
    }

    pub(super) fn commit_prepared_answer_standing(
        &mut self,
        mut prepared: PreparedWorldAnswer,
    ) -> AgenticLanguageAnswer {
        let dialogue = prepared
            .dialogue
            .take()
            .expect("the preflighted answer retains its exact dialogue occurrence");
        self.dialogue_identities.insert(dialogue.identity.clone());
        self.dialogue.push(dialogue);
        self.next_dialogue = prepared.next_dialogue;
        self.standing.dialogue_occurrences = prepared.dialogue_occurrences;

        for episode in prepared.founded {
            let episode_at = self.episodes.len();
            index_surfaces(
                &mut self.episode_surface_atlas,
                episode_at,
                &episode.routing_surfaces,
            );
            self.episodes.push(episode);
        }
        self.next_episode = prepared.next_episode;
        self.standing.locally_conditioned_episode_organs =
            prepared.locally_conditioned_episode_organs;
        self.standing.generated_answers = prepared.generated_answers;
        let answer = prepared
            .answer
            .take()
            .expect("the prepared answer remains present until its atomic commit");
        self.answer_lineages.insert(
            answer.answer_episode_identity.clone(),
            prepared
                .lineage
                .take()
                .expect("the prepared answer retains its exact lineage"),
        );
        if let (Some(deed), Some(selected)) = (
            answer.world_deed.as_deref(),
            answer.relational_thought.as_ref(),
        ) {
            self.relational_returns
                .bind_answer(&answer.answer_episode_identity, deed, selected)
                .expect("the prepared answer preflighted its owner-retained relational current");
        }
        answer
    }

    pub(super) fn receive_feedback(
        &mut self,
        feedback: &AgenticLanguageFeedback,
    ) -> Result<AgenticLanguageConsequence, AgenticLanguageError> {
        if self.open.is_some() {
            return Err(AgenticLanguageError::QuestionAlreadyOpen);
        }
        if word_surfaces(&feedback.text).is_empty() {
            return Err(AgenticLanguageError::EmptyFeedback);
        }
        let target_episode = self
            .episodes
            .iter()
            .find(|episode| episode.identity == feedback.target_episode)
            .ok_or_else(|| {
                AgenticLanguageError::UnknownFeedbackTarget(feedback.target_episode.clone())
            })?;
        if !matches!(
            target_episode.role,
            AgenticDialogueRole::EmanatedAnswer | AgenticDialogueRole::EmanatedClarification
        ) {
            return Err(AgenticLanguageError::FeedbackTargetIsNotDialogueOutput(
                feedback.target_episode.clone(),
            ));
        }
        let role = match feedback.kind {
            AgenticLanguageFeedbackKind::Correction => AgenticDialogueRole::UserCorrection,
            AgenticLanguageFeedbackKind::Acceptance => AgenticDialogueRole::UserAcceptance,
            AgenticLanguageFeedbackKind::Refusal => AgenticDialogueRole::UserRefusal,
        };
        if self.dialogue_identities.contains(&feedback.identity) {
            return Err(AgenticLanguageError::DuplicateDialogueOccurrence(
                feedback.identity.clone(),
            ));
        }
        let revision = self.next_dialogue;
        let _next_dialogue = self
            .next_dialogue
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let _next_dialogue_population = self
            .standing
            .dialogue_occurrences
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let next_episode = self
            .next_episode
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let locally_conditioned_episode_organs = self
            .standing
            .locally_conditioned_episode_organs
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;

        let mut caused_by = BTreeSet::from([feedback.target_episode.clone()]);
        let target_lineage = self.answer_lineages.get(&feedback.target_episode).cloned();
        if let Some(lineage) = &target_lineage {
            caused_by.extend(lineage.supporting_episodes.iter().cloned());
            caused_by.extend(lineage.evidence_sources.iter().cloned());
            if !lineage.surface.is_empty() {
                caused_by.insert(format!("surface:{}", render_surface(&lineage.surface)));
            }
        }
        let local_identity = format!("episode-{}", self.next_episode);
        let episode_identity = format!("{local_identity}/feedback");
        let passage = MorphologicalLanguagePassage::new(
            format!("{episode_identity}/return"),
            format!("dialogue/{}", feedback.identity),
            feedback.receiver,
            feedback.text.clone(),
        );
        let mut routing_surfaces = word_surfaces(&feedback.text)
            .into_iter()
            .collect::<BTreeSet<_>>();
        let (committed_codec_version, installed_ecology, episode_codec_versions) =
            if feedback.kind == AgenticLanguageFeedbackKind::Correction {
                let input = target_codec_face(target_episode, target_lineage.as_ref());
                for region in &input.ordered_regions {
                    routing_surfaces.extend(region.iter().cloned());
                }
                let output = AgenticLanguageCodecFace {
                    identity: format!("{episode_identity}/face"),
                    receiver: feedback.receiver,
                    ordered_regions: BTreeSet::from([word_surfaces(&feedback.text)]),
                    lineage: BTreeSet::from([
                        feedback.identity.clone(),
                        feedback.target_episode.clone(),
                        passage.identity.clone(),
                    ]),
                };
                let residual = AgenticLanguageCodecResidual {
                    input_only_regions: input
                        .ordered_regions
                        .difference(&output.ordered_regions)
                        .cloned()
                        .collect(),
                    output_only_regions: output
                        .ordered_regions
                        .difference(&input.ordered_regions)
                        .cloned()
                        .collect(),
                };
                let training_views = target_lineage
                    .as_ref()
                    .map(|lineage| codec_training_views(&lineage.question_surface))
                    .transpose()?
                    .unwrap_or_default();
                let training_proposal = if training_views.is_empty() {
                    None
                } else {
                    Some(
                        self.codec_training()?
                            .propose_views(&training_views, feedback.text.as_bytes())
                            .map_err(AgenticLanguageError::CodecTraining)?,
                    )
                };
                let observations = training_proposal
                    .as_ref()
                    .map(|proposal| proposal.observations())
                    .unwrap_or(&[]);
                let active_transductions_before = training_proposal
                    .as_ref()
                    .map(|proposal| proposal.active_templates_before())
                    .unwrap_or(self.codec_training()?.active_template_count());
                let active_transductions_after = training_proposal
                    .as_ref()
                    .map(|proposal| proposal.active_templates_after())
                    .unwrap_or(active_transductions_before);
                let observed_fibers = training_views
                    .iter()
                    .zip(observations)
                    .flat_map(|(view, observation)| {
                        let parameters = view
                            .parameters
                            .iter()
                            .map(|(name, value)| (name.clone(), value.clone()))
                            .collect::<Vec<_>>();
                        observation.templates.iter().cloned().map(move |template| {
                            TransductionFiber {
                                template,
                                parameters: parameters.clone(),
                            }
                        })
                    })
                    .collect::<BTreeSet<_>>();
                let cultivation = AgenticLanguageCodecCultivation {
                    generation: training_proposal
                        .as_ref()
                        .map(|proposal| proposal.next_generation())
                        .unwrap_or(self.codec_training()?.generation),
                    receiver_views: training_views.len(),
                    prior_relations: observations
                        .iter()
                        .map(|observation| observation.relation)
                        .collect(),
                    observed_fibers,
                    active_transductions_before,
                    active_transductions_after,
                };
                let identity = format!("answer-relation-codec/{}", feedback.identity);
                let version = AgenticLanguageCodecVersion {
                    identity: identity.clone(),
                    aperture: AgenticLanguageCodecAperture::AnswerRelation,
                    parents: target_lineage
                        .as_ref()
                        .map(|lineage| lineage.codec_versions.clone())
                        .unwrap_or_else(|| target_episode.codec_versions.clone()),
                    input,
                    output,
                    output_episode: episode_identity.clone(),
                    returned_by: feedback.identity.clone(),
                    residual,
                    cultivation,
                };
                let installed = MorphologicalLanguageEcology::condition(
                    std::slice::from_ref(&passage),
                    self.action,
                    1,
                )?;
                let reflective_codec_versions = self
                    .standing
                    .reflective_codec_versions
                    .checked_add(1)
                    .ok_or(AgenticLanguageError::CarrierExtent)?;
                let reflective_codec_commits = self
                    .standing
                    .reflective_codec_commits
                    .checked_add(1)
                    .ok_or(AgenticLanguageError::CarrierExtent)?;
                let reflective_codec_training_events = self
                    .standing
                    .reflective_codec_training_events
                    .checked_add(usize::from(!training_views.is_empty()))
                    .ok_or(AgenticLanguageError::CarrierExtent)?;
                let mut operative = version.parents.clone();
                operative.insert(identity);
                (
                    Some((
                        version,
                        reflective_codec_versions,
                        reflective_codec_commits,
                        reflective_codec_training_events,
                        training_proposal,
                    )),
                    Some(installed),
                    operative,
                )
            } else {
                (None, None, BTreeSet::new())
            };
        let received_corrections = self
            .standing
            .received_corrections
            .checked_add(
                if feedback.kind == AgenticLanguageFeedbackKind::Correction {
                    1
                } else {
                    0
                },
            )
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let received_acceptances = self
            .standing
            .received_acceptances
            .checked_add(
                if feedback.kind == AgenticLanguageFeedbackKind::Acceptance {
                    1
                } else {
                    0
                },
            )
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let received_refusals = self
            .standing
            .received_refusals
            .checked_add(if feedback.kind == AgenticLanguageFeedbackKind::Refusal {
                1
            } else {
                0
            })
            .ok_or(AgenticLanguageError::CarrierExtent)?;

        // Every fallible construction above is complete before the live body changes. The
        // remaining operations install one local episode and, for a correction, one codec version
        // plus its receiver-local input incidence.
        self.relational_body
            .receive(std::slice::from_ref(&passage))?;
        let committed_dialogue_ordinal = self.push_dialogue(
            feedback.identity.clone(),
            role,
            feedback.receiver,
            feedback.text.clone(),
            Some(feedback.target_episode.clone()),
            caused_by,
        )?;
        debug_assert_eq!(committed_dialogue_ordinal, revision);
        self.next_episode = next_episode;
        let episode_at = self.episodes.len();
        index_surfaces(
            &mut self.episode_surface_atlas,
            episode_at,
            &routing_surfaces,
        );
        self.episodes.push(LanguageEpisode {
            identity: episode_identity.clone(),
            origin: EpisodeOrigin::ReturnedAnswer,
            role,
            revision,
            answerable: feedback.kind == AgenticLanguageFeedbackKind::Correction,
            passages: vec![passage],
            routing_surfaces,
            evidence_sources: BTreeSet::from([format!("dialogue/{}", feedback.identity)]),
            ecology: installed_ecology,
            relational_thought: None,
            codec_versions: episode_codec_versions,
        });

        let committed_codec_version = if let Some((
            version,
            reflective_codec_versions,
            reflective_codec_commits,
            reflective_codec_training_events,
            training_proposal,
        )) = committed_codec_version
        {
            let version = self.commit_reflective_codec(version, training_proposal)?;
            self.standing.reflective_codec_versions = reflective_codec_versions;
            self.standing.reflective_codec_commits = reflective_codec_commits;
            self.standing.reflective_codec_training_events = reflective_codec_training_events;
            self.standing.active_codec_transductions =
                version.cultivation.active_transductions_after;
            Some(version)
        } else {
            None
        };

        let mut obstructed_episodes = BTreeSet::new();
        match feedback.kind {
            AgenticLanguageFeedbackKind::Correction => {
                self.obstructed_episodes
                    .insert(feedback.target_episode.clone());
                obstructed_episodes.insert(feedback.target_episode.clone());
            }
            AgenticLanguageFeedbackKind::Acceptance => {
                self.accepted_episodes
                    .insert(feedback.target_episode.clone());
            }
            AgenticLanguageFeedbackKind::Refusal => {
                self.obstructed_episodes
                    .insert(feedback.target_episode.clone());
                obstructed_episodes.insert(feedback.target_episode.clone());
            }
        }
        self.standing.locally_conditioned_episode_organs = locally_conditioned_episode_organs;
        self.standing.received_corrections = received_corrections;
        self.standing.received_acceptances = received_acceptances;
        self.standing.received_refusals = received_refusals;
        self.pending_clarification = None;
        self.standing.turn = AgenticTurnStanding::Rest;
        Ok(AgenticLanguageConsequence::Feedback(
            AgenticLanguageFeedbackReceipt {
                feedback: feedback.clone(),
                founded_episode: episode_identity,
                obstructed_episodes,
                dialogue_ordinal: revision,
                committed_codec_version,
            },
        ))
    }

    /// Returns the exact origin census of the local organ population. It is an inspection receipt,
    /// not a scheduler or a semantic score.
    pub fn episode_origin_census(&self) -> (usize, usize, usize) {
        let mut inherited = 0usize;
        let mut world = 0usize;
        let mut answer = 0usize;
        for episode in &self.episodes {
            match episode.origin {
                EpisodeOrigin::InheritedTrajectory => inherited += 1,
                EpisodeOrigin::ReturnedWorld => world += 1,
                EpisodeOrigin::ReturnedAnswer => answer += 1,
            }
        }
        (inherited, world, answer)
    }
}
