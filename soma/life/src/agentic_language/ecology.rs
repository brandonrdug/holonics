use super::*;

impl AgenticLanguageEcology {
    pub fn condition(
        inherited_passages: &[MorphologicalLanguagePassage],
        capabilities: &[AgenticLanguageCapability],
        trajectories: &[AgenticLanguageTrajectory],
        spec: AgenticLanguageSpec,
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<Self, AgenticLanguageError> {
        Self::condition_inner(
            inherited_passages,
            capabilities,
            trajectories,
            spec,
            action,
            worker_threads,
            None,
        )
    }

    /// Condition one agent through an explicitly mounted physical-current executor. The same
    /// executor realizes every route-current event across inherited and trajectory ecologies, so
    /// a caller selecting CUDA cannot silently fall back to CPU inside language conditioning.
    pub fn condition_with_executor(
        inherited_passages: &[MorphologicalLanguagePassage],
        capabilities: &[AgenticLanguageCapability],
        trajectories: &[AgenticLanguageTrajectory],
        spec: AgenticLanguageSpec,
        action: ActionCurrent,
        worker_threads: usize,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<Self, AgenticLanguageError> {
        Self::condition_inner(
            inherited_passages,
            capabilities,
            trajectories,
            spec,
            action,
            worker_threads,
            Some(executor),
        )
    }

    pub(super) fn condition_inner(
        inherited_passages: &[MorphologicalLanguagePassage],
        capabilities: &[AgenticLanguageCapability],
        trajectories: &[AgenticLanguageTrajectory],
        spec: AgenticLanguageSpec,
        action: ActionCurrent,
        worker_threads: usize,
        mut route_executor: Option<&mut dyn LiveCurrentExecutor>,
    ) -> Result<Self, AgenticLanguageError> {
        if trajectories.is_empty()
            && !capabilities
                .iter()
                .any(|capability| capability.receives_open_boundary)
        {
            return Err(AgenticLanguageError::EmptyTrajectoryEcology);
        }
        let mut capability_map = BTreeMap::new();
        for capability in capabilities {
            if capability_map
                .insert(capability.identity.clone(), capability.clone())
                .is_some()
            {
                return Err(AgenticLanguageError::DuplicateCapability(
                    capability.identity.clone(),
                ));
            }
        }

        let mut trajectory_identities = BTreeSet::new();
        let mut inherited = inherited_passages.to_vec();
        let mut action_surface_atlas = BTreeMap::<String, BTreeSet<usize>>::new();
        let mut trajectory_corpus = Vec::<Vec<MorphologicalLanguagePassage>>::new();
        for (trajectory_at, trajectory) in trajectories.iter().enumerate() {
            if !trajectory_identities.insert(trajectory.identity.clone()) {
                return Err(AgenticLanguageError::DuplicateTrajectory(
                    trajectory.identity.clone(),
                ));
            }
            if !capability_map.contains_key(&trajectory.capability) {
                return Err(AgenticLanguageError::NoActionRoute);
            }
            let question = MorphologicalLanguagePassage::new(
                format!("trajectory/{}/question", trajectory.identity),
                format!("trajectory/{}/question", trajectory.identity),
                trajectory.receiver,
                trajectory.question.clone(),
            );
            let answer = MorphologicalLanguagePassage::new(
                format!("trajectory/{}/answer", trajectory.identity),
                format!("trajectory/{}/answer", trajectory.identity),
                trajectory.receiver,
                trajectory.answer.clone(),
            );
            let mut corpus = Vec::with_capacity(trajectory.observations.len() + 2);
            corpus.push(question.clone());
            corpus.extend(trajectory.observations.iter().cloned());
            corpus.push(answer.clone());
            inherited.push(question);
            inherited.extend(trajectory.observations.iter().cloned());
            inherited.push(answer);
            for surface in word_surfaces(&trajectory.question) {
                action_surface_atlas
                    .entry(surface)
                    .or_default()
                    .insert(trajectory_at);
            }
            trajectory_corpus.push(corpus);
        }
        // Both owners receive the same caused passages, but this application has no typed
        // complete-successor commutation certificate for their continuing morphologies. Preserve
        // owner-native order here. Each owner may realize its own admitted local work through the
        // supplied executor/worker aperture; this application does not partition or join workers.
        let (inherited_body, relational_body) = match route_executor.as_deref_mut() {
            Some(executor) => (
                MorphologicalLanguageEcology::condition_with_executor(
                    &inherited,
                    action,
                    worker_threads,
                    executor,
                )?,
                ExactRelationalLanguageEcology::condition_with_executor(
                    &inherited,
                    worker_threads,
                    executor,
                )?,
            ),
            None => (
                MorphologicalLanguageEcology::condition(&inherited, action, worker_threads)?,
                ExactRelationalLanguageEcology::condition_with_workers(&inherited, worker_threads)?,
            ),
        };
        let mut inherited_cofaces = ExactSet::<(String, String)>::new();
        for passages in &trajectory_corpus {
            let mut surfaces = ExactSet::<String>::new();
            for passage in passages {
                surfaces.extend(word_surfaces(&passage.text));
            }
            inherited_cofaces.extend(unordered_surface_pairs(&surfaces));
        }

        let mut episodes = Vec::with_capacity(trajectories.len());
        let mut episode_surface_atlas = BTreeMap::<String, BTreeSet<usize>>::new();
        for (trajectory, passages) in trajectories.iter().zip(trajectory_corpus) {
            let evidence_sources = trajectory
                .observations
                .iter()
                .map(|passage| passage.source.clone())
                .chain(std::iter::once(format!(
                    "trajectory/{}/answer",
                    trajectory.identity
                )))
                .collect::<BTreeSet<_>>();
            let ecology = match route_executor.as_deref_mut() {
                Some(executor) => MorphologicalLanguageEcology::condition_with_executor(
                    &passages,
                    action,
                    worker_threads,
                    executor,
                )?,
                None => MorphologicalLanguageEcology::condition(&passages, action, worker_threads)?,
            };
            let episode_at = episodes.len();
            let mut routing_surfaces = ExactSet::<String>::new();
            for passage in &passages {
                routing_surfaces.extend(word_surfaces(&passage.text));
            }
            index_surfaces(&mut episode_surface_atlas, episode_at, &routing_surfaces);
            episodes.push(LanguageEpisode {
                identity: format!("inherited/{}", trajectory.identity),
                origin: EpisodeOrigin::InheritedTrajectory,
                role: AgenticDialogueRole::InheritedAnswer,
                revision: 0,
                answerable: true,
                passages,
                routing_surfaces,
                evidence_sources,
                ecology: Some(ecology),
                relational_thought: None,
                codec_versions: BTreeSet::new(),
            });
        }

        let codec_training =
            TrainingEcology::new(CODEC_MINIMUM_RECURRENCE, CODEC_TEMPLATE_APERTURE)
                .map_err(AgenticLanguageError::CodecTraining)?;
        let mut codec_runtime = AgenticReflectiveCodecRuntime::new_with_contacts();
        let codec_origin_face = codec_runtime
            .found_face(AgenticLanguageCodecFace {
                identity: "eros/codec/origin".to_owned(),
                receiver: 0,
                ordered_regions: BTreeSet::new(),
                lineage: BTreeSet::from(["eros/conditioned-origin".to_owned()]),
            })
            .map_err(|_| AgenticLanguageError::CarrierExtent)?;
        let codec_origin = codec_runtime
            .mount_codec(AgenticLanguageCodecProgram::Origin, codec_origin_face)
            .map_err(|refusal| AgenticLanguageError::CodecRuntime(refusal.error))?;
        let codec_continuation = codec_runtime
            .open_continuation(codec_origin, codec_training)
            .map_err(|(error, _)| AgenticLanguageError::CodecRuntime(error))?;

        Ok(Self {
            action,
            worker_threads: worker_threads.max(1),
            spec,
            inherited_body,
            inherited_passages: inherited_passages.to_vec(),
            history: Vec::new(),
            relational_body,
            inherited_cofaces,
            capabilities: capability_map,
            trajectories: trajectories.to_vec(),
            action_surface_atlas,
            episodes,
            episode_surface_atlas,
            next_deed: 0,
            next_episode: 0,
            next_dialogue: 0,
            open: None,
            pending_local_answer: None,
            pending_clarification: None,
            dialogue: Vec::new(),
            dialogue_identities: BTreeSet::new(),
            obstructed_episodes: BTreeSet::new(),
            accepted_episodes: BTreeSet::new(),
            answer_lineages: BTreeMap::new(),
            relational_returns: AgenticRelationalReturnOwner::new(),
            codec_runtime,
            codec_continuation,
            standing: AgenticLanguageStanding {
                inherited_body_passages: inherited.len(),
                inherited_trajectory_organs: trajectories.len(),
                locally_conditioned_episode_organs: 0,
                base_body_reconditions: 0,
                emitted_deeds: 0,
                received_world_returns: 0,
                received_world_thought_fibers: 0,
                generated_answers: 0,
                generated_clarifications: 0,
                received_corrections: 0,
                received_acceptances: 0,
                received_refusals: 0,
                reflective_codec_versions: 0,
                reflective_codec_commits: 0,
                reflective_codec_training_events: 0,
                active_codec_transductions: 0,
                dialogue_occurrences: 0,
                turn: AgenticTurnStanding::Rest,
            },
        })
    }

    pub const fn standing(&self) -> &AgenticLanguageStanding {
        &self.standing
    }

    pub const fn inherited_body(&self) -> &MorphologicalLanguageEcology {
        &self.inherited_body
    }

    pub const fn relational_body(&self) -> &ExactRelationalLanguageEcology {
        &self.relational_body
    }

    /// The exterior deed which has departed but has not yet completed its return. A world or
    /// substrate refusal retains this boundary for retry; it does not force the operator to
    /// fabricate a new question or reconstruct the language body.
    pub fn open_deed(&self) -> Option<&AgenticLanguageDeed> {
        self.open.as_ref().map(|open| &open.deed)
    }

    pub fn dialogue(&self) -> &[AgenticDialogueOccurrence] {
        &self.dialogue
    }

    pub(crate) fn answer_selected_relational_current(
        &self,
        answer_episode: &str,
    ) -> Option<AnswerSelectedRelationalCurrent> {
        self.relational_returns.selected_for_answer(answer_episode)
    }

    pub fn obstructed_episode_identities(&self) -> &BTreeSet<String> {
        &self.obstructed_episodes
    }

    /// Reify every committed language-codec version without removing it from the active body.
    /// The returned references are an inspection aperture; execution continues to consult the
    /// same versions through the reflective runtime's receiver-contact incidence.
    pub fn codec_versions(&self) -> Vec<&AgenticLanguageCodecVersion> {
        self.codec_program_versions().collect()
    }

    pub fn active_codec_versions(&self) -> Vec<&AgenticLanguageCodecVersion> {
        self.codec_program_versions()
            .filter(|version| !self.obstructed_episodes.contains(&version.output_episode))
            .collect()
    }

    pub(super) fn codec_program_versions(
        &self,
    ) -> impl Iterator<Item = &AgenticLanguageCodecVersion> {
        self.codec_runtime
            .codecs()
            .filter_map(|codec| match &codec.program {
                AgenticLanguageCodecProgram::Origin => None,
                AgenticLanguageCodecProgram::Revision(version) => Some(version),
            })
    }

    pub(super) fn codec_training(&self) -> Result<&TrainingEcology, AgenticLanguageError> {
        self.codec_runtime
            .continuation(self.codec_continuation)
            .and_then(|continuation| continuation.environment())
            .ok_or(AgenticLanguageError::CarrierExtent)
    }

    pub(super) fn codec_id(&self, identity: &str) -> Option<CodecId> {
        self.codec_runtime
            .codecs()
            .find_map(|codec| match &codec.program {
                AgenticLanguageCodecProgram::Revision(version) if version.identity == identity => {
                    Some(codec.id)
                }
                _ => None,
            })
    }

    pub(super) fn commit_reflective_codec(
        &mut self,
        version: AgenticLanguageCodecVersion,
        training_proposal: Option<TrainingCultivationProposal>,
    ) -> Result<AgenticLanguageCodecVersion, AgenticLanguageError> {
        let mut parents = LocalSet::new();
        for identity in &version.parents {
            let parent = self
                .codec_id(identity)
                .ok_or(AgenticLanguageError::CarrierExtent)?;
            parents
                .try_insert(parent)
                .map_err(|_| AgenticLanguageError::CarrierExtent)?;
        }
        let contacts = version
            .input
            .ordered_regions
            .iter()
            .flat_map(|region| region.iter().cloned())
            .collect::<LocalSet<_>>();
        let input = self
            .codec_runtime
            .found_face(version.input.clone())
            .map_err(|_| AgenticLanguageError::CarrierExtent)?;
        let output = self
            .codec_runtime
            .found_face(version.output.clone())
            .map_err(|_| AgenticLanguageError::CarrierExtent)?;
        let mut reflector = AgenticCodecReflectionExecutor;
        let reflection = self
            .codec_runtime
            .receive_with(self.codec_continuation, input, &mut reflector)
            .map_err(codec_crossing_error)?
            .reflection
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        self.codec_runtime
            .revise_and_resume_with_lineage(
                reflection,
                output,
                AgenticLanguageCodecProgram::Revision(version.clone()),
                parents,
                contacts,
            )
            .map_err(|refusal| AgenticLanguageError::CodecRuntime(refusal.error))?;
        let mut trainer = AgenticCodecTrainingExecutor {
            proposal: training_proposal,
        };
        self.codec_runtime
            .receive_with(self.codec_continuation, output, &mut trainer)
            .map_err(codec_crossing_error)?;
        Ok(version)
    }

    /// Let a returned formal verdict revise the same reflective continuation used by ordinary
    /// language conduct. This is a mounting of one returned theorem face, not language training:
    /// no proof surface or target-specific answer row becomes retained standing.
    pub(super) fn receive_formal_return(
        &mut self,
        returned: &AgenticFormalReturn,
    ) -> Result<AgenticFormalReturnReceipt, AgenticLanguageError> {
        formal_return::receive(self, returned)
    }
    /// Reify the contemporary question/answer face addressed by a possible later return.
    pub fn reify_answer_codec_face(
        &self,
        answer_episode: &str,
    ) -> Result<AgenticLanguageCodecFace, AgenticLanguageError> {
        let episode = self
            .episodes
            .iter()
            .find(|episode| episode.identity == answer_episode)
            .ok_or_else(|| {
                AgenticLanguageError::UnknownFeedbackTarget(answer_episode.to_owned())
            })?;
        let lineage = self.answer_lineages.get(answer_episode).ok_or_else(|| {
            AgenticLanguageError::FeedbackTargetIsNotDialogueOutput(answer_episode.to_owned())
        })?;
        Ok(target_codec_face(episode, Some(lineage)))
    }

    pub fn rest_receipt(&self) -> Result<AgenticLanguageRestReceipt, AgenticLanguageError> {
        let episodes = self
            .episodes
            .iter()
            .map(|episode| {
                Ok(AgenticEpisodeRestReceipt {
                    identity: episode.identity.clone(),
                    role: episode.role,
                    revision: episode.revision,
                    answerable: episode.answerable,
                    passages: episode.passages.clone(),
                    routing_surfaces: episode.routing_surfaces.clone(),
                    evidence_sources: episode.evidence_sources.clone(),
                    realized_ecology: episode
                        .ecology
                        .as_ref()
                        .map(|ecology| *ecology.census()),
                    relational_thought: episode.relational_thought.clone(),
                    codec_versions: episode.codec_versions.clone(),
                })
            })
            .collect::<Result<Vec<_>, AgenticLanguageError>>()?;
        let answer_lineages = self
            .answer_lineages
            .iter()
            .map(
                |(answer_episode, lineage)| AgenticAnswerLineageRestReceipt {
                    answer_episode: answer_episode.clone(),
                    world_deed: lineage.world_deed.clone(),
                    supporting_episodes: lineage.supporting_episodes.clone(),
                    evidence_sources: lineage.evidence_sources.clone(),
                    surface: lineage.surface.clone(),
                    question_surface: lineage.question_surface.clone(),
                    codec_versions: lineage.codec_versions.clone(),
                    cultivated_codec_paths: lineage.cultivated_codec_paths.clone(),
                },
            )
            .collect();
        Ok(AgenticLanguageRestReceipt {
            inherited_body: *self.inherited_body.census(),
            episodes,
            dialogue: self.dialogue.clone(),
            obstructed_episodes: self.obstructed_episodes.clone(),
            accepted_episodes: self.accepted_episodes.clone(),
            answer_lineages,
            relational_returns: self.relational_returns.rest_receipt(),
            codec_versions: self.codec_program_versions().cloned().collect(),
            codec_training: self
                .codec_training()?
                .encode_native_bytes()
                .map_err(AgenticLanguageError::CodecTraining)?,
            pending_capabilities: self
                .pending_clarification
                .as_ref()
                .map(|pending| pending.capabilities.clone()),
            open_deed: self.open.as_ref().map(|open| open.deed.clone()),
            next_deed: self.next_deed,
            next_episode: self.next_episode,
            next_dialogue: self.next_dialogue,
            standing: self.standing.clone(),
        })
    }

    /// The exterior causes this body has admitted, in arrival order.
    pub fn history(&self) -> &[AgenticOwnedLanguageOccurrence] {
        &self.history
    }

    /// Take a **non-consuming** image from which an independent second body is remounted.
    ///
    /// This is the fork a counterfactual arm needs: `into_native_rest` consumes the body, so
    /// without this owner the only way to obtain a second body at the same standing was to
    /// destroy the first. The image replays rather than clones, because `GrowingKeyAtlas`
    /// refuses cloning by declared law.
    pub fn rest_image(&self) -> Result<AgenticLanguageRestImage, AgenticLanguageError> {
        Ok(AgenticLanguageRestImage {
            inherited_passages: self.inherited_passages.clone(),
            capabilities: self.capabilities.values().cloned().collect(),
            trajectories: self.trajectories.clone(),
            spec: self.spec,
            action: self.action,
            worker_threads: self.worker_threads,
            history: self.history.clone(),
            receipt: self.rest_receipt()?,
        })
    }

    /// Suspend this complete body without cloning or replaying its cultivated standing.
    pub fn into_native_rest(
        self,
    ) -> Result<AgenticLanguageNativeRest, AgenticLanguageNativeRestRefusal> {
        if matches!(
            self.standing.turn,
            AgenticTurnStanding::AwaitingClarification { .. }
        ) {
            return Err(AgenticLanguageNativeRestRefusal {
                error: AgenticLanguageError::NativeRestRequiresRest,
                body: self,
            });
        }
        if !self.pending_answer_stages_are_valid() {
            return Err(AgenticLanguageNativeRestRefusal {
                error: AgenticLanguageError::RestRemountMismatch,
                body: self,
            });
        }
        Ok(AgenticLanguageNativeRest { body: self })
    }

    pub(super) fn pending_answer_stages_are_valid(&self) -> bool {
        if let Some(pending) = &self.pending_local_answer {
            return self.open.is_none()
                && self.prepared_answer_stage_is_valid(
                    &pending.prepared,
                    &pending.question,
                    None,
                    &[],
                );
        }
        let Some(open) = &self.open else {
            return true;
        };
        let deed = open.deed.identity.as_str();
        let world_matches = open.world_return.as_ref().is_none_or(|returned| {
            returned.deed == deed
                && open
                    .prepared_answer
                    .as_ref()
                    .is_none_or(|_| !returned.thought_fibers.is_empty())
        });
        let prepared_matches = open.prepared_answer.as_ref().is_none_or(|prepared| {
            open.relational_returned
                && open.world_return.as_ref().is_some_and(|returned| {
                    self.prepared_answer_stage_is_valid(
                        prepared,
                        &open.question,
                        Some(deed),
                        &returned.thought_fibers,
                    )
                })
        });
        let turn_matches = matches!(
            &self.standing.turn,
            AgenticTurnStanding::AwaitingWorldReturn {
                question,
                deed: standing_deed,
                capability,
            } if question == &open.question.identity
                && standing_deed == deed
                && capability == &open.deed.capability.identity
        );
        world_matches
            && prepared_matches
            && (!open.relational_returned || open.world_return.is_some())
            && turn_matches
    }

    pub(super) fn prepared_answer_stage_is_valid(
        &self,
        prepared: &PreparedWorldAnswer,
        question: &AgenticLanguageQuestion,
        world_deed: Option<&str>,
        world_thought_fibers: &[RelationalThoughtFiber],
    ) -> bool {
        if prepared.next_founded_return > prepared.founded.len() {
            return false;
        }
        let (Some(answer), Some(lineage), Some(dialogue)) = (
            prepared.answer.as_ref(),
            prepared.lineage.as_ref(),
            prepared.dialogue.as_ref(),
        ) else {
            return false;
        };
        let founded_identities_match = answer.locally_conditioned_episodes.len()
            == prepared.founded.len()
            && prepared.founded.iter().all(|episode| {
                answer
                    .locally_conditioned_episodes
                    .contains(&episode.identity)
            });
        let answer_episode_matches = prepared.founded.iter().any(|episode| {
            episode.identity == answer.answer_episode_identity
                && episode.role == AgenticDialogueRole::EmanatedAnswer
                && episode.revision == dialogue.ordinal
        });
        let successor_counters_match = self.next_dialogue == dialogue.ordinal
            && self.next_dialogue.checked_add(1) == Some(prepared.next_dialogue)
            && self.next_episode.checked_add(1) == Some(prepared.next_episode)
            && self.standing.dialogue_occurrences.checked_add(1)
                == Some(prepared.dialogue_occurrences)
            && self
                .standing
                .locally_conditioned_episode_organs
                .checked_add(prepared.founded.len())
                == Some(prepared.locally_conditioned_episode_organs)
            && self.standing.generated_answers.checked_add(1) == Some(prepared.generated_answers);
        let delivery_cursor_matches = prepared.founded.iter().enumerate().all(|(at, episode)| {
            let any_returned = episode.passages.iter().any(|passage| {
                self.relational_body
                    .passage_delivery_order(&passage.identity)
                    .is_some()
            });
            let completely_returned = episode.passages.iter().all(|passage| {
                self.relational_body
                    .passage_delivery_order(&passage.identity)
                    .is_some()
            });
            if at < prepared.next_founded_return {
                completely_returned
            } else {
                !any_returned
            }
        });
        let mut expected_causes = answer.supporting_episode_identities.clone();
        expected_causes.extend(answer.contextual_dialogue.iter().cloned());
        if let Some(deed) = world_deed {
            expected_causes.insert(deed.to_owned());
        }
        let relational_owner_matches = if world_thought_fibers.is_empty() {
            answer.relational_thought.is_none()
        } else {
            world_deed.is_some_and(|deed| {
                answer
                    .relational_thought
                    .as_ref()
                    .is_some_and(|current| self.relational_returns.can_bind_answer(deed, current))
            })
        };
        answer.question == *question
            && answer.world_deed.as_deref() == world_deed
            && relational_owner_matches
            && answer_episode_matches
            && founded_identities_match
            && dialogue.identity == answer.answer_episode_identity
            && dialogue.role == AgenticDialogueRole::EmanatedAnswer
            && dialogue.receiver == question.receiver
            && dialogue.text == answer.text
            && dialogue.target.as_deref() == Some(question.identity.as_str())
            && lineage.supporting_episodes == answer.supporting_episode_identities
            && lineage.evidence_sources == answer.evidence_sources
            && lineage.surface == lexical_tokens(&answer.text)
            && lineage.question_surface == lexical_tokens(&question.text)
            && lineage.world_deed.as_deref() == world_deed
            && lineage.codec_versions == answer.operative_codec_versions
            && lineage.cultivated_codec_paths == answer.cultivated_codec_paths
            && dialogue.caused_by == expected_causes
            && !self.dialogue_identities.contains(&dialogue.identity)
            && successor_counters_match
            && delivery_cursor_matches
    }

    /// Exact durable body of the cultivated cross-occurrence codec law. It contains recurrent
    /// route forms and receiver parameters, but no correction occurrence, prompt, answer row, or
    /// prediction cache.
    pub fn codec_training_native_bytes(&self) -> Result<Vec<u8>, AgenticLanguageError> {
        self.codec_training()?
            .encode_native_bytes()
            .map_err(AgenticLanguageError::CodecTraining)
    }

    pub(super) fn push_dialogue(
        &mut self,
        identity: String,
        role: AgenticDialogueRole,
        receiver: u64,
        text: String,
        target: Option<String>,
        caused_by: BTreeSet<String>,
    ) -> Result<u64, AgenticLanguageError> {
        if self.dialogue_identities.contains(&identity) {
            return Err(AgenticLanguageError::DuplicateDialogueOccurrence(identity));
        }
        let ordinal = self.next_dialogue;
        let next_dialogue = self
            .next_dialogue
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let dialogue_occurrences = self
            .standing
            .dialogue_occurrences
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        self.dialogue_identities.insert(identity.clone());
        self.dialogue.push(AgenticDialogueOccurrence {
            ordinal,
            identity,
            role,
            receiver,
            text,
            target,
            caused_by,
        });
        self.next_dialogue = next_dialogue;
        self.standing.dialogue_occurrences = dialogue_occurrences;
        Ok(ordinal)
    }

    /// Return one staged dialogue occurrence idempotently while its exterior deed is still open.
    /// Exact retry resumes after a substrate refusal; changed testimony under the same identity
    /// remains a duplicate error.
    pub(super) fn return_dialogue(
        &mut self,
        identity: String,
        role: AgenticDialogueRole,
        receiver: u64,
        text: String,
        target: Option<String>,
        caused_by: BTreeSet<String>,
    ) -> Result<u64, AgenticLanguageError> {
        if let Some(existing) = self
            .dialogue
            .iter()
            .find(|occurrence| occurrence.identity == identity)
        {
            if existing.role == role
                && existing.receiver == receiver
                && existing.text == text
                && existing.target == target
                && existing.caused_by == caused_by
            {
                return Ok(existing.ordinal);
            }
            return Err(AgenticLanguageError::DuplicateDialogueOccurrence(identity));
        }
        self.push_dialogue(identity, role, receiver, text, target, caused_by)
    }

    pub(super) fn prior_dialogue_context(
        &self,
        current_question: &str,
    ) -> Option<(String, BTreeSet<String>)> {
        let prior_question = self.dialogue.iter().rev().find(|occurrence| {
            occurrence.role == AgenticDialogueRole::UserQuestion
                && occurrence.identity != current_question
        })?;
        let mut identities = BTreeSet::from([prior_question.identity.clone()]);
        let mut text = prior_question.text.clone();
        if let Some(answer) = self.dialogue.iter().rev().find(|occurrence| {
            occurrence.ordinal > prior_question.ordinal
                && matches!(
                    occurrence.role,
                    AgenticDialogueRole::EmanatedAnswer
                        | AgenticDialogueRole::UserCorrection
                        | AgenticDialogueRole::EmanatedClarification
                )
        }) {
            identities.insert(answer.identity.clone());
            text.push(' ');
            text.push_str(&answer.text);
        }
        Some((text, identities))
    }

    pub(super) fn receive_question(
        &mut self,
        question: &AgenticLanguageQuestion,
    ) -> Result<AgenticLanguageConsequence, AgenticLanguageError> {
        if let Some(pending) = &self.pending_local_answer {
            if pending.question != *question {
                return Err(AgenticLanguageError::QuestionAlreadyOpen);
            }
            let answer = self.commit_pending_local_answer()?;
            self.pending_clarification = None;
            return Ok(AgenticLanguageConsequence::Answer(answer));
        }
        if self.open.is_some() {
            return Err(AgenticLanguageError::QuestionAlreadyOpen);
        }
        if word_surfaces(&question.text).is_empty() {
            return Err(AgenticLanguageError::EmptyQuestion);
        }

        let prior_context = self.prior_dialogue_context(&question.identity);
        self.push_dialogue(
            question.identity.clone(),
            AgenticDialogueRole::UserQuestion,
            question.receiver,
            question.text.clone(),
            None,
            BTreeSet::new(),
        )?;

        // A returned theorem face is an operative receiver, not a cached answer. When the new
        // question reaches that face, its consequence must cross the ordinary open-boundary
        // capability before the formal current can participate in answer formation. An older
        // answer episode therefore cannot close the question in front of the returned organ.
        let formal_return_receives = !self
            .reflective_codec_answers(question, &question.text, &BTreeSet::new(), true)?
            .is_empty();

        if !formal_return_receives {
            let grounded =
                self.grounded_episode_answers(question, &question.text, &BTreeSet::new())?;
            let grounded =
                self.compose_candidate_population(grounded, &question.text, &BTreeSet::new())?;
            if !grounded.is_empty() {
                let prepared = self.prepare_answer(question.clone(), None, &[], grounded, &[])?;
                self.pending_local_answer = Some(PendingLocalAnswer {
                    question: question.clone(),
                    prepared,
                });
                let answer = self.commit_pending_local_answer()?;
                self.pending_clarification = None;
                return Ok(AgenticLanguageConsequence::Answer(answer));
            }
        }

        // Ellipsis is not assigned a privileged pronoun list. Only after the received occurrence
        // fails to reach a grounded organ do its immediately preceding question/answer currents
        // become a larger contextual receiver. Directly grounded questions never pay this path.
        let contextual_grounded = if let Some((context, identities)) = &prior_context {
            let received_prompt = format!("{context} {}", question.text);
            let direct_charge = self.inherited_body.charge(&question.text)?;
            let grounded = self
                .grounded_episode_answers(question, &received_prompt, identities)?
                .into_iter()
                .filter(|candidate| {
                    candidate_witnesses_direct_question(
                        candidate,
                        &question.text,
                        &direct_charge.operator_features,
                    )
                })
                .collect();
            self.compose_candidate_population(grounded, &received_prompt, identities)?
        } else {
            Vec::new()
        };
        if !formal_return_receives && !contextual_grounded.is_empty() {
            let prepared =
                self.prepare_answer(question.clone(), None, &[], contextual_grounded, &[])?;
            self.pending_local_answer = Some(PendingLocalAnswer {
                question: question.clone(),
                prepared,
            });
            let answer = self.commit_pending_local_answer()?;
            self.pending_clarification = None;
            return Ok(AgenticLanguageConsequence::Answer(answer));
        }

        let permitted = self
            .pending_clarification
            .as_ref()
            .map(|pending| &pending.capabilities);
        let mut received_prompt = question.text.clone();
        let mut contextual_dialogue = BTreeSet::new();
        let mut routes = self.action_routes(&received_prompt, permitted);
        if routes.1.is_empty() {
            if let Some((context, identities)) = prior_context {
                let direct_charge = self.inherited_body.charge(&question.text)?;
                if context_can_receive_question(
                    &question.text,
                    &context,
                    &direct_charge.operator_features,
                ) {
                    let contextual_prompt = format!("{context} {}", question.text);
                    let contextual_routes = self.action_routes(&contextual_prompt, permitted);
                    if !contextual_routes.1.is_empty() {
                        received_prompt = contextual_prompt;
                        contextual_dialogue = identities;
                        routes = contextual_routes;
                    }
                }
            }
        }
        if routes.1.len() != 1 {
            let clarification = self.return_clarification(
                question.clone(),
                routes.0,
                routes.1,
                contextual_dialogue,
            )?;
            return Ok(AgenticLanguageConsequence::Clarification(clarification));
        }
        let capability_identity = routes
            .1
            .iter()
            .next()
            .cloned()
            .ok_or(AgenticLanguageError::NoActionRoute)?;
        let capability = self
            .capabilities
            .get(&capability_identity)
            .cloned()
            .ok_or(AgenticLanguageError::NoActionRoute)?;
        let inherited_routes = routes.0;
        let arguments = self.deed_arguments(&received_prompt, &inherited_routes)?;
        let deed_identity = format!("language-deed-{}", self.next_deed);
        let next_deed = self
            .next_deed
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let emitted_deeds = self
            .standing
            .emitted_deeds
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let deed = AgenticLanguageDeed {
            identity: deed_identity.clone(),
            question: question.clone(),
            capability,
            inherited_routes,
            arguments,
            received_prompt,
            contextual_dialogue: contextual_dialogue.clone(),
        };
        let caused_by = deed
            .inherited_routes
            .iter()
            .map(|route| route.trajectory.clone())
            .chain(contextual_dialogue.iter().cloned())
            .chain(std::iter::once(format!(
                "capability/{}",
                deed.capability.identity
            )))
            .collect();
        self.push_dialogue(
            deed.identity.clone(),
            AgenticDialogueRole::EmittedDeed,
            deed.capability.receiver,
            deed.argument_surface(),
            Some(question.identity.clone()),
            caused_by,
        )?;
        self.open = Some(OpenQuestion {
            question: question.clone(),
            deed: deed.clone(),
            world_return: None,
            relational_returned: false,
            prepared_answer: None,
        });
        self.pending_clarification = None;
        self.next_deed = next_deed;
        self.standing.emitted_deeds = emitted_deeds;
        self.standing.turn = AgenticTurnStanding::AwaitingWorldReturn {
            question: question.identity.clone(),
            deed: deed_identity,
            capability: deed.capability.identity.clone(),
        };
        Ok(AgenticLanguageConsequence::Deed(deed))
    }

    pub(super) fn receive_world_return(
        &mut self,
        returned: &AgenticLanguageWorldReturn,
    ) -> Result<AgenticLanguageConsequence, AgenticLanguageError> {
        let open = self
            .open
            .as_ref()
            .ok_or(AgenticLanguageError::NoQuestionOpen)?;
        if open.deed.identity != returned.deed {
            return Err(AgenticLanguageError::WrongDeedReturn {
                expected: open.deed.identity.clone(),
                received: returned.deed.clone(),
            });
        }
        if returned.sections.is_empty() {
            return Err(AgenticLanguageError::EmptyWorldReturn);
        }

        {
            let open = self
                .open
                .as_mut()
                .ok_or(AgenticLanguageError::NoQuestionOpen)?;
            match &open.world_return {
                Some(staged) if staged != returned => {
                    return Err(AgenticLanguageError::ChangedWorldReturn(
                        returned.deed.clone(),
                    ));
                }
                Some(_) => {}
                None => open.world_return = Some(returned.clone()),
            }
        }
        if !returned.thought_fibers.is_empty() {
            self.relational_returns
                .receive_deed(&returned.deed, &returned.thought_fibers)
                .map_err(|_| AgenticLanguageError::ChangedWorldReturn(returned.deed.clone()))?;
        }
        // The exact world return is now owner-retained before the relational current crosses.
        // Retry resumes only while this explicit lower mouth remains unreturned.
        let sections = &returned.sections;
        let relational_returned = self
            .open
            .as_ref()
            .is_some_and(|open| open.relational_returned);
        if !relational_returned {
            self.relational_body
                .receive_copresent_with_workers(sections, self.worker_threads)?;
            self.open
                .as_mut()
                .expect("the deed remains open across its relational return")
                .relational_returned = true;
        }
        let (open_question, open_deed) = {
            let open = self
                .open
                .as_ref()
                .expect("the deed remains open across answer formation");
            (open.question.clone(), open.deed.clone())
        };

        // Action demonstrations condition the capability route. They do not enter the evidence
        // organ as prose. Each returned section first receives through its own local language
        // organ; unrelated alternatives therefore do not form one combinatorial branch product.
        for section in sections {
            self.return_dialogue(
                section.identity.clone(),
                AgenticDialogueRole::WorldObservation,
                section.receiver,
                section.text.clone(),
                Some(open_deed.identity.clone()),
                BTreeSet::from([open_deed.identity.clone()]),
            )?;
        }
        if self
            .open
            .as_ref()
            .is_some_and(|open| open.prepared_answer.is_none())
        {
            let question = &open_deed.received_prompt;
            let inherited_charge = self.inherited_body.charge(question)?;
            let candidate_sections = maximal_return_section_indices(
                question,
                sections,
                &inherited_charge.operator_features,
                self.spec.generation.maximum_observed_tokens,
            );
            // The section order is receiver testimony. No owner certificate says these
            // continuing morphology changes commute, so each section crosses the morphology
            // owner in that order; its internal executor remains responsible for admitted local
            // parallelism.
            let mut candidates = Vec::new();
            for section_at in candidate_sections {
                let section = sections
                    .get(section_at)
                    .ok_or(AgenticLanguageError::CarrierExtent)?;
                let working = std::slice::from_ref(section);
                let working_ecology = match MorphologicalLanguageEcology::condition(
                    working,
                    self.action,
                    self.worker_threads,
                ) {
                    Ok(ecology) => ecology,
                    Err(MorphologicalLanguageError::Suffix(
                        crate::suffix_ecology::ExactSuffixEcologyError::EmptyEcology,
                    )) => continue,
                    Err(error) => return Err(error.into()),
                };
                let generation =
                    working_ecology.generate_currents(question, self.spec.generation)?;
                let evidence_sources = BTreeSet::from([section.source.clone()]);
                match select_generated_answer(
                    &generation.outputs,
                    &evidence_sources,
                    &BTreeSet::from([section.identity.clone()]),
                    &generation.reflection,
                    working,
                    BTreeSet::new(),
                    BTreeSet::new(),
                    question,
                    &open_deed.contextual_dialogue,
                    generation.charge.obligations.len(),
                    &question_local_regions(&generation.charge),
                    &question_regions(&generation.charge),
                    0,
                    false,
                ) {
                    Ok(candidate) => candidates.push(candidate),
                    Err(AgenticLanguageError::NoGroundedLanguageReturn) => {}
                    Err(error) => return Err(error),
                }
            }
            let mut candidates = if candidates.is_empty() {
                Vec::new()
            } else {
                self.compose_candidate_population(
                    candidates,
                    question,
                    &open_deed.contextual_dialogue,
                )?
            };
            for fiber in &returned.thought_fibers {
                for current in fiber.closed() {
                    candidates.push(relational_thought_answer_candidate(
                        sections,
                        current.clone(),
                        question,
                        &open_deed.contextual_dialogue,
                        BTreeSet::new(),
                        BTreeSet::new(),
                        0,
                        false,
                    )?);
                }
            }
            if returned.thought_fibers.is_empty() {
                // The relational owner may form the exact thought fiber only after the returned
                // sections cross its continuing body. Carry that owner-issued fiber across the
                // deed boundary before any one current is selected for an answer; otherwise the
                // answer would name a current absent from the deed's retained return family.
                let passage_aperture = sections
                    .iter()
                    .map(|section| section.identity.clone())
                    .collect::<BTreeSet<_>>();
                if let Some(fiber) = self.relational_body.think_fiber_in_passages(
                    &open_question.text,
                    &passage_aperture,
                    self.spec.thought_receiver_horizon,
                )? {
                    self.relational_returns
                        .receive_deed(&returned.deed, std::slice::from_ref(&fiber))
                        .map_err(|_| {
                            AgenticLanguageError::ChangedWorldReturn(returned.deed.clone())
                        })?;
                    for current in fiber.closed().cloned() {
                        candidates.push(relational_thought_answer_candidate(
                            sections,
                            current,
                            question,
                            &open_deed.contextual_dialogue,
                            BTreeSet::new(),
                            BTreeSet::new(),
                            0,
                            false,
                        )?);
                    }
                }
            }
            let formal_candidates = self.reflective_codec_answers(
                &open_question,
                question,
                &open_deed.contextual_dialogue,
                true,
            )?;
            candidates.extend(formal_candidates);
            if !open_deed.contextual_dialogue.is_empty() {
                let direct_charge = self.inherited_body.charge(&open_question.text)?;
                candidates.retain(|candidate| {
                    candidate_witnesses_direct_question(
                        candidate,
                        &open_question.text,
                        &direct_charge.operator_features,
                    )
                });
            }
            if candidates.is_empty() {
                return Err(AgenticLanguageError::NoGroundedLanguageReturn);
            }
            candidates = self.compose_candidate_population(
                candidates,
                question,
                &open_deed.contextual_dialogue,
            )?;
            let prepared = self.prepare_answer(
                open_question.clone(),
                Some(open_deed.identity.clone()),
                &returned.sections,
                candidates,
                &returned.thought_fibers,
            )?;
            self.open
                .as_mut()
                .expect("the deed remains open after answer preparation")
                .prepared_answer = Some(prepared);
        }

        let received_world_returns = self
            .standing
            .received_world_returns
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let received_world_thought_fibers = self
            .standing
            .received_world_thought_fibers
            .checked_add(returned.thought_fibers.len())
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let answer = self.commit_prepared_answer()?;
        self.standing.received_world_thought_fibers = received_world_thought_fibers;
        self.standing.received_world_returns = received_world_returns;
        self.open = None;
        self.standing.turn = AgenticTurnStanding::Rest;
        Ok(AgenticLanguageConsequence::Answer(answer))
    }

    pub(super) fn compose_candidate_population(
        &self,
        mut population: Vec<AnswerCandidate>,
        received_prompt: &str,
        contextual_dialogue: &BTreeSet<String>,
    ) -> Result<Vec<AnswerCandidate>, AgenticLanguageError> {
        let mut seen = population
            .iter()
            .map(answer_candidate_signature)
            .collect::<BTreeSet<_>>();
        let mut frontier_start = 0usize;
        while frontier_start < population.len() {
            let snapshot_extent = population.len();
            // Pair contact is admitted by the returned-current owner one crossing at a time.
            // The application has no complete-successor commutation law for candidate
            // morphologies, so it neither launches a pair wave nor fabricates worker phases.
            let mut left = 0usize;
            while left < snapshot_extent {
                let mut right = left + 1;
                while right < snapshot_extent {
                    if (left >= frontier_start || right >= frontier_start)
                        && candidates_have_disjoint_passages(&population[left], &population[right])
                        && candidates_admit_composition(&population[left], &population[right])
                    {
                        let formed = compose_answer_candidates(
                            &population[left],
                            &population[right],
                            received_prompt,
                            contextual_dialogue,
                            self.spec.generation.maximum_observed_tokens,
                        )?;
                        for candidate in formed {
                            if seen.insert(answer_candidate_signature(&candidate)) {
                                population.push(candidate);
                            }
                        }
                    }
                    right += 1;
                }
                left += 1;
            }
            if population.len() == snapshot_extent {
                break;
            }
            frontier_start = snapshot_extent;
        }
        Ok(population)
    }

    pub(super) fn action_routes(
        &self,
        prompt: &str,
        permitted_capabilities: Option<&BTreeSet<String>>,
    ) -> (Vec<AgenticActionRoute>, BTreeSet<String>) {
        let question_surfaces = word_surfaces(prompt);
        let mut candidate_trajectories = BTreeSet::<usize>::new();
        for surface in &question_surfaces {
            if let Some(routes) = self.action_surface_atlas.get(surface) {
                candidate_trajectories.extend(routes.iter().copied());
            }
        }
        let mut routes = Vec::new();
        let mut capabilities = BTreeSet::new();
        for trajectory_at in candidate_trajectories {
            let trajectory = self
                .trajectories
                .get(trajectory_at)
                .expect("the action atlas only carries conditioned trajectories");
            if permitted_capabilities
                .is_some_and(|permitted| !permitted.contains(&trajectory.capability))
            {
                continue;
            }
            let regions =
                common_ordered_regions(&question_surfaces, &word_surfaces(&trajectory.question));
            if regions.is_empty() {
                continue;
            }
            capabilities.insert(trajectory.capability.clone());
            routes.push(AgenticActionRoute {
                trajectory: trajectory.identity.clone(),
                common_ordered_regions: regions,
            });
        }
        // A mounted open-boundary mouth is reached only after no existing episode has grounded
        // the question.  It therefore does not masquerade as a learned question/answer example,
        // and it cannot displace a receiver-local language consequence which already returned.
        if capabilities.is_empty() {
            capabilities.extend(
                self.capabilities
                    .values()
                    .filter(|capability| capability.receives_open_boundary)
                    .filter(|capability| {
                        permitted_capabilities
                            .map_or(true, |permitted| permitted.contains(&capability.identity))
                    })
                    .map(|capability| capability.identity.clone()),
            );
        }
        (routes, capabilities)
    }

    pub(super) fn deed_arguments(
        &self,
        prompt: &str,
        routes: &[AgenticActionRoute],
    ) -> Result<Vec<AgenticDeedArgument>, AgenticLanguageError> {
        let charge = self.inherited_body.charge(prompt)?;
        let surfaces = word_surfaces(prompt);
        let mut inherited = BTreeMap::<Vec<String>, BTreeSet<String>>::new();
        for route in routes {
            for region in &route.common_ordered_regions {
                if region
                    .iter()
                    .all(|surface| charge.operator_features.contains(surface))
                {
                    continue;
                }
                inherited
                    .entry(region.clone())
                    .or_default()
                    .insert(route.trajectory.clone());
            }
        }
        let inherited_snapshot = inherited.keys().cloned().collect::<Vec<_>>();
        inherited.retain(|region, _| {
            !inherited_snapshot.iter().any(|other| {
                region.len() < other.len()
                    && other
                        .windows(region.len())
                        .any(|window| window == region.as_slice())
            })
        });
        let covered = inherited
            .keys()
            .flat_map(|region| region.iter().cloned())
            .collect::<BTreeSet<_>>();
        let mut arguments = inherited
            .into_iter()
            .map(
                |(ordered_surface, caused_trajectories)| AgenticDeedArgument {
                    ordered_surface,
                    caused_trajectories,
                    inherited_region: true,
                },
            )
            .collect::<Vec<_>>();
        for surface in &surfaces {
            if charge.operator_features.contains(surface) || covered.contains(surface) {
                continue;
            }
            if arguments
                .iter()
                .any(|argument| argument.ordered_surface == [surface.clone()])
            {
                continue;
            }
            arguments.push(AgenticDeedArgument {
                ordered_surface: vec![surface.clone()],
                caused_trajectories: BTreeSet::new(),
                inherited_region: false,
            });
        }
        if arguments.is_empty() {
            arguments.extend(surfaces.iter().cloned().map(|surface| AgenticDeedArgument {
                ordered_surface: vec![surface],
                caused_trajectories: BTreeSet::new(),
                inherited_region: false,
            }));
        }
        arguments.sort_by(|left, right| {
            let left_at = first_region_offset(&surfaces, &left.ordered_surface);
            let right_at = first_region_offset(&surfaces, &right.ordered_surface);
            (
                left_at,
                std::cmp::Reverse(left.ordered_surface.len()),
                &left.ordered_surface,
            )
                .cmp(&(
                    right_at,
                    std::cmp::Reverse(right.ordered_surface.len()),
                    &right.ordered_surface,
                ))
        });
        Ok(arguments)
    }

    pub(super) fn return_clarification(
        &mut self,
        question: AgenticLanguageQuestion,
        routes: Vec<AgenticActionRoute>,
        reached_capabilities: BTreeSet<String>,
        contextual_dialogue: BTreeSet<String>,
    ) -> Result<AgenticLanguageClarification, AgenticLanguageError> {
        let capabilities = if reached_capabilities.is_empty() {
            self.pending_clarification
                .as_ref()
                .map(|pending| pending.capabilities.clone())
                .unwrap_or_else(|| self.capabilities.keys().cloned().collect())
        } else {
            reached_capabilities
        };
        let mut alternatives = Vec::new();
        for capability in &capabilities {
            let inherited_questions = self
                .trajectories
                .iter()
                .filter(|trajectory| trajectory.capability == *capability)
                .map(|trajectory| trajectory.question.clone())
                .collect::<BTreeSet<_>>();
            let trajectories = routes
                .iter()
                .filter(|route| {
                    self.trajectories.iter().any(|trajectory| {
                        trajectory.identity == route.trajectory
                            && trajectory.capability == *capability
                    })
                })
                .map(|route| route.trajectory.clone())
                .chain(
                    self.trajectories
                        .iter()
                        .filter(|trajectory| trajectory.capability == *capability)
                        .map(|trajectory| trajectory.identity.clone()),
                )
                .collect::<BTreeSet<_>>();
            alternatives.push(AgenticClarificationAlternative {
                capability: capability.clone(),
                inherited_questions,
                trajectories,
            });
        }
        alternatives.sort_by(|left, right| left.capability.cmp(&right.capability));
        let inherited_surfaces = alternatives
            .iter()
            .filter_map(|alternative| alternative.inherited_questions.iter().next())
            .cloned()
            .collect::<Vec<_>>();
        let text = if inherited_surfaces.is_empty() {
            "Which caused world relation should carry this question?".to_owned()
        } else {
            format!(
                "Which caused path do you mean: {}",
                inherited_surfaces.join(" Or: ")
            )
        };
        let local_identity = format!("episode-{}", self.next_episode);
        let episode_identity = format!("{local_identity}/clarification");
        self.next_episode = self
            .next_episode
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let clarification_identity =
            format!("clarification-{}", self.standing.generated_clarifications);
        let caused_by = alternatives
            .iter()
            .flat_map(|alternative| alternative.trajectories.iter().cloned())
            .chain(contextual_dialogue.iter().cloned())
            .collect::<BTreeSet<_>>();
        let dialogue_ordinal = self.push_dialogue(
            clarification_identity.clone(),
            AgenticDialogueRole::EmanatedClarification,
            question.receiver,
            text.clone(),
            Some(question.identity.clone()),
            caused_by,
        )?;
        let passage = MorphologicalLanguagePassage::new(
            format!("{episode_identity}/return"),
            episode_identity.clone(),
            question.receiver,
            text.clone(),
        );
        self.relational_body
            .receive(std::slice::from_ref(&passage))?;
        let routing_surfaces = word_surfaces(&text).into_iter().collect::<BTreeSet<_>>();
        let episode_at = self.episodes.len();
        index_surfaces(
            &mut self.episode_surface_atlas,
            episode_at,
            &routing_surfaces,
        );
        self.episodes.push(LanguageEpisode {
            identity: episode_identity.clone(),
            origin: EpisodeOrigin::ReturnedAnswer,
            role: AgenticDialogueRole::EmanatedClarification,
            revision: dialogue_ordinal,
            answerable: false,
            passages: vec![passage],
            routing_surfaces,
            evidence_sources: BTreeSet::from([episode_identity.clone()]),
            ecology: None,
            relational_thought: None,
            codec_versions: BTreeSet::new(),
        });
        self.standing.generated_clarifications = self
            .standing
            .generated_clarifications
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        self.standing.locally_conditioned_episode_organs = self
            .standing
            .locally_conditioned_episode_organs
            .checked_add(1)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let clarification = AgenticLanguageClarification {
            identity: clarification_identity.clone(),
            question: question.clone(),
            text,
            alternatives,
            contextual_dialogue,
            episode_identity,
        };
        self.pending_clarification = Some(PendingClarification {
            capabilities: capabilities.clone(),
        });
        self.standing.turn = AgenticTurnStanding::AwaitingClarification {
            question: question.identity,
            clarification: clarification_identity,
            alternatives: capabilities,
        };
        Ok(clarification)
    }
}

impl CausalMembrane for AgenticLanguageEcology {
    type Standing = AgenticLanguageStanding;
    type Occurrence<'a>
        = AgenticLanguageOccurrence<'a>
    where
        Self: 'a;
    type Return = AgenticLanguageConsequence;
    type Error = AgenticLanguageError;

    fn standing(&self) -> &Self::Standing {
        &self.standing
    }

    fn receive_occurrence<'a>(
        &mut self,
        occurrence: Self::Occurrence<'a>,
    ) -> Result<Self::Return, Self::Error>
    where
        Self: 'a,
    {
        // The cause is retained only when the membrane admitted it. A refused occurrence caused
        // no standing, so replaying it would found standing the imaged body never had.
        let retained = occurrence.owned();
        let consequence = match occurrence {
            AgenticLanguageOccurrence::Question(question) => self.receive_question(question),
            AgenticLanguageOccurrence::WorldReturn(world_return) => {
                self.receive_world_return(world_return)
            }
            AgenticLanguageOccurrence::Feedback(feedback) => self.receive_feedback(feedback),
            AgenticLanguageOccurrence::FormalReturn(returned) => self
                .receive_formal_return(returned)
                .map(AgenticLanguageConsequence::FormalReturn),
        }?;
        self.history.push(retained);
        Ok(consequence)
    }
}
