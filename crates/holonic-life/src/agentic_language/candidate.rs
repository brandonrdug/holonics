use super::*;

pub(super) fn relational_answer_candidates(
    ecology: &ExactRelationalLanguageEcology,
    passages: &[MorphologicalLanguagePassage],
    visible_question: &str,
    received_prompt: &str,
    contextual_dialogue: &BTreeSet<String>,
    episode_identities: BTreeSet<String>,
    codec_versions: BTreeSet<String>,
    revision_horizon: u64,
    thought_receiver_horizon: u64,
    corrective: bool,
) -> Result<Vec<AnswerCandidate>, AgenticLanguageError> {
    if passages.is_empty() {
        return Ok(Vec::new());
    }
    let passage_aperture = passages
        .iter()
        .map(|passage| passage.identity.clone())
        .collect::<BTreeSet<_>>();
    let Some(fiber) = ecology.think_fiber_in_passages(
        visible_question,
        &passage_aperture,
        thought_receiver_horizon,
    )?
    else {
        return Ok(Vec::new());
    };
    let mut candidates = Vec::new();
    for thought in fiber.closed().cloned() {
        candidates.push(relational_thought_answer_candidate(
            passages,
            thought,
            received_prompt,
            contextual_dialogue,
            episode_identities.clone(),
            codec_versions.clone(),
            revision_horizon,
            corrective,
        )?);
    }
    Ok(candidates)
}

/// Cast one already enacted relation current through the agent's ordinary answer membrane.
///
/// A typed research bridge may have formed this current across several causal waves.  Reusing the
/// exact current avoids reparsing its returned sections into a new global clause body and keeps
/// its path, holonomy, open-region, and witness testimony intact.
#[allow(clippy::too_many_arguments)]
pub(super) fn relational_thought_answer_candidate(
    passages: &[MorphologicalLanguagePassage],
    thought: RelationalThoughtCurrent,
    received_prompt: &str,
    contextual_dialogue: &BTreeSet<String>,
    episode_identities: BTreeSet<String>,
    codec_versions: BTreeSet<String>,
    revision_horizon: u64,
    corrective: bool,
) -> Result<AnswerCandidate, AgenticLanguageError> {
    let Some(realization) = thought.selected() else {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    };

    let all_context_sources = thought.source_witnesses.clone();
    let mut tokens = Vec::new();
    let mut phases = Vec::new();
    for realized in &realization.clauses {
        let Some(clause) = thought
            .clauses
            .iter()
            .find(|clause| clause.identity == realized.relation_clause)
            .or_else(|| {
                thought
                    .parse_fibers
                    .iter()
                    .flat_map(|fiber| fiber.alternatives.iter())
                    .find(|clause| clause.identity == realized.relation_clause)
            })
        else {
            return Err(AgenticLanguageError::CarrierExtent);
        };
        let clause_faces = clause
            .subject
            .identity
            .union(&clause.object.identity)
            .cloned()
            .collect::<BTreeSet<_>>();
        let discharged_obligations = thought
            .required_entity_regions
            .iter()
            .enumerate()
            .filter_map(|(at, region)| region.is_subset(&clause_faces).then_some(at))
            .collect::<BTreeSet<_>>();
        let discharged_regions = discharged_obligations
            .iter()
            .map(|at| (*at, BTreeSet::from([0])))
            .collect::<BTreeMap<_, _>>();
        let discharged_features = discharged_obligations
            .iter()
            .map(|at| (*at, thought.required_entity_regions[*at].clone()))
            .collect::<BTreeMap<_, _>>();
        let emitted_start = tokens.len();
        for surface in lexical_tokens(&realized.text) {
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
                recurrent_sources: realized.sources.clone(),
                recurrent_context_sources: all_context_sources.clone(),
                caused_sources: realized.sources.clone(),
                conducting_supports: LocalSet::new(),
                // The exterior lineage the realized relation stands on. Same law, different organ.
                conducting_sources: realized.sources.clone(),
                caused_passages: realized.passages.clone(),
                supporting_clauses: BTreeSet::from([realized.relation_clause.clone()]),
                returned_event_count,
            });
        }
        let emitted_end = tokens.len();
        phases.push(MorphologicalResponsePhase {
            entry_clause: realized.relation_clause.clone(),
            clauses: BTreeSet::from([realized.relation_clause.clone()]),
            sources: realized.sources.clone(),
            passages: realized.passages.clone(),
            boundary: Some(MorphologicalBoundary::Sentence),
            discharged_obligations,
            discharged_regions,
            discharged_features,
            entry_lexical_horizons: BTreeSet::new(),
            entry_recurrence_multiplicities: BTreeSet::new(),
            emitted_start,
            emitted_end,
        });
    }
    if tokens.is_empty() || phases.is_empty() {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    }
    let (support_conduct, supporting_sources) = MorphologicalSupportConduct::of(&tokens);
    let generated = MorphologicalGeneratedCurrent {
        text: realization.text.clone(),
        tokens,
        phases,
        rest: MorphologicalResponseRest::Closed,
        caused_seams: Vec::new(),
        support_conduct,
        supporting_sources,
    };
    let inherited_surfaces = passages
        .iter()
        .map(|passage| lexical_tokens(&passage.text))
        .collect::<Vec<_>>();
    let ordered_query_regions = thought
        .required_entity_regions
        .iter()
        .map(|region| region.iter().cloned().collect::<Vec<_>>())
        .collect::<BTreeSet<_>>();
    let causal_current_states_formed = thought
        .clauses
        .len()
        .checked_add(thought.joins.len())
        .and_then(|extent| {
            extent.checked_add(
                thought
                    .parse_fibers
                    .iter()
                    .map(|fiber| fiber.alternatives.len())
                    .sum::<usize>(),
            )
        })
        .and_then(|extent| extent.checked_add(thought.realizations.len()))
        .ok_or(AgenticLanguageError::CarrierExtent)?;
    let reflection = MorphologicalReflectionReceipt {
        shared_conditioned_bodies: 1,
        whole_body_forks: 0,
        shared_current_forks: 0,
        causal_current_states_formed,
        conduct_equivalent_states_glued: thought.realizations.len().saturating_sub(1),
        peak_live_current_states: thought.realizations.len(),
        returned_events_carried: 0,
        terminal_return_materializations: 0,
        dilated_passages: 0,
        deepest_dilation: 0,
        deepest_chronology: 0,
    };
    Ok(AnswerCandidate {
        generated,
        episode_identities,
        evidence_sources: thought.source_witnesses.clone(),
        conditioning_passages: passages.to_vec(),
        discharged_query_faces: thought
            .required_entity_regions
            .iter()
            .flat_map(|region| region.iter().cloned())
            .collect(),
        reflection,
        inherited_surfaces,
        received_prompt: received_prompt.to_owned(),
        contextual_dialogue: contextual_dialogue.clone(),
        obligation_population: thought.required_entity_regions.len(),
        local_region_fiber: ExactAnswerRegionFiber::from_parts(
            LocalSet::from_iter(thought.required_entity_regions.iter().enumerate().map(
                |(obligation, _)| AgenticAnswerRegionIdentity {
                    obligation,
                    region: 0,
                },
            )),
            LocalSet::from_iter(thought.returned_entity_regions.iter().copied().map(
                |obligation| AgenticAnswerRegionIdentity {
                    obligation,
                    region: 0,
                },
            )),
        )?,
        ordered_query_regions,
        revision_horizon,
        corrective,
        composed_current_population: thought.joins.len(),
        relational_thought: Some(thought.clone()),
        relational_thoughts: vec![thought],
        codec_versions,
        cultivated_codec_paths: Vec::new(),
        retained_alternatives: Vec::new(),
    })
}

#[derive(Clone, Debug)]
pub(super) struct SelectedAnswerCandidate {
    pub(super) generated: MorphologicalGeneratedCurrent,
    pub(super) episode_identities: BTreeSet<String>,
    pub(super) evidence_sources: BTreeSet<String>,
    pub(super) selection: AgenticAnswerSelection,
    pub(super) reflection: MorphologicalReflectionReceipt,
    pub(super) novel_contiguous_surface: bool,
    pub(super) received_prompt: String,
    pub(super) contextual_dialogue: BTreeSet<String>,
    pub(super) obligation_population: usize,
    pub(super) local_region_fiber: ExactAnswerRegionFiber,
    pub(super) relational_thought: Option<RelationalThoughtCurrent>,
    pub(super) relational_thoughts: Vec<RelationalThoughtCurrent>,
    pub(super) codec_versions: BTreeSet<String>,
    pub(super) cultivated_codec_paths: Vec<AgenticLanguageCodecPathReceipt>,
    pub(super) retained_alternatives: Vec<AgenticRetainedAnswerAlternative>,
    /// **The presentation quotient's division, taken.** The retained alternatives were kept here
    /// from the beginning and carried no distinguishing word; this relates each of them to the
    /// uttered answer by the shortest word a declared receiver family separates them with, or says
    /// that none does.
    pub(super) presentation_division: PresentationDivision,
}

pub(super) fn select_generated_answer(
    outputs: &[MorphologicalGeneratedCurrent],
    evidence_sources: &BTreeSet<String>,
    required_passages: &BTreeSet<String>,
    reflection: &MorphologicalReflectionReceipt,
    inherited_passages: &[MorphologicalLanguagePassage],
    episode_identities: BTreeSet<String>,
    codec_versions: BTreeSet<String>,
    received_prompt: &str,
    contextual_dialogue: &BTreeSet<String>,
    obligation_population: usize,
    required_local_regions: &LocalSet<AgenticAnswerRegionIdentity>,
    query_regions: &BTreeSet<Vec<String>>,
    revision_horizon: u64,
    corrective: bool,
) -> Result<AnswerCandidate, AgenticLanguageError> {
    let inherited_surfaces = inherited_passages
        .iter()
        .map(|passage| lexical_tokens(&passage.text))
        .collect::<Vec<_>>();
    let closed = outputs
        .iter()
        .filter(|output| {
            output.rest == MorphologicalResponseRest::Closed
                && output.tokens.last().is_some_and(|token| token.token != "?")
                && !has_unlicensed_consecutive_repetition(
                    &output
                        .tokens
                        .iter()
                        .map(|token| token.token.clone())
                        .collect::<Vec<_>>(),
                    &inherited_surfaces,
                )
        })
        .collect::<Vec<_>>();
    let grounded = closed
        .iter()
        .copied()
        .filter(|output| {
            let caused_passages = output
                .tokens
                .iter()
                .flat_map(|token| token.caused_passages.iter().cloned())
                .collect::<BTreeSet<_>>();
            output.tokens.iter().any(|token| {
                token
                    .caused_sources
                    .iter()
                    .any(|source| evidence_sources.contains(source))
            }) && required_passages.is_subset(&caused_passages)
        })
        .collect::<Vec<_>>();
    if grounded.is_empty() {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    }

    let source_faces = grounded
        .iter()
        .map(|output| {
            output
                .tokens
                .iter()
                .flat_map(|token| token.caused_sources.iter())
                .filter(|source| evidence_sources.contains(*source))
                .cloned()
                .collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    let eligible = (0..grounded.len()).collect::<Vec<_>>();
    let maximal = eligible
        .iter()
        .copied()
        .filter(|left| {
            !eligible.iter().copied().any(|right| {
                source_faces[*left].is_subset(&source_faces[right])
                    && source_faces[*left] != source_faces[right]
            })
        })
        .collect::<Vec<_>>();
    let Some(first) = maximal.first().copied() else {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    };
    let selected = grounded[first].clone();
    let selected_surface = selected
        .tokens
        .iter()
        .map(|token| token.token.clone())
        .collect::<Vec<_>>();
    let mut selected_indices = vec![first];
    let mut retained_alternatives = Vec::new();
    for current_at in maximal.iter().copied().skip(1) {
        let surface = grounded[current_at]
            .tokens
            .iter()
            .map(|token| token.token.clone())
            .collect::<Vec<_>>();
        if surface == selected_surface {
            selected_indices.push(current_at);
            continue;
        }
        retain_answer_alternative(
            &mut retained_alternatives,
            AgenticRetainedAnswerAlternative {
                generated: grounded[current_at].clone(),
                episode_identities: episode_identities.clone(),
                evidence_sources: source_faces[current_at].clone(),
                relational_thoughts: Vec::new(),
            },
        );
    }
    let selected_surfaces = selected
        .tokens
        .iter()
        .filter(|token| token.token.chars().any(char::is_alphanumeric))
        .map(|token| token.token.to_lowercase())
        .collect::<Vec<_>>();
    let ordered_query_regions = query_regions
        .iter()
        .filter(|region| {
            selected_surfaces
                .windows(region.len())
                .any(|window| window == region.as_slice())
        })
        .cloned()
        .collect();
    let mut returned_local_regions = LocalSet::new();
    for phase in &selected.phases {
        for (obligation, regions) in &phase.discharged_regions {
            for region in regions {
                returned_local_regions.insert(AgenticAnswerRegionIdentity {
                    obligation: *obligation,
                    region: *region,
                });
            }
        }
    }
    let composed_current_population = usize::from(!selected.caused_seams.is_empty());
    Ok(AnswerCandidate {
        generated: selected,
        episode_identities,
        evidence_sources: selected_indices
            .iter()
            .flat_map(|at| source_faces[*at].iter().cloned())
            .collect(),
        conditioning_passages: inherited_passages.to_vec(),
        discharged_query_faces: selected_indices
            .iter()
            .flat_map(|at| grounded[*at].phases.iter())
            .flat_map(|phase| phase.discharged_features.values())
            .flat_map(|features| features.iter().cloned())
            .collect(),
        reflection: reflection.clone(),
        inherited_surfaces,
        received_prompt: received_prompt.to_owned(),
        contextual_dialogue: contextual_dialogue.clone(),
        obligation_population,
        local_region_fiber: ExactAnswerRegionFiber::from_parts(
            LocalSet::from_iter(required_local_regions.iter().copied()),
            returned_local_regions,
        )?,
        ordered_query_regions,
        revision_horizon,
        corrective,
        composed_current_population,
        relational_thought: None,
        relational_thoughts: Vec::new(),
        codec_versions,
        cultivated_codec_paths: Vec::new(),
        retained_alternatives,
    })
}

pub(super) fn select_answer_candidate(
    candidates: Vec<AnswerCandidate>,
) -> Result<SelectedAnswerCandidate, AgenticLanguageError> {
    if candidates.is_empty() {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    }
    let fully_closed = (0..candidates.len())
        .filter(|candidate_at| candidates[*candidate_at].local_region_fiber.is_closed())
        .collect::<Vec<_>>();
    if fully_closed.is_empty() {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    }
    // A directly addressed correction is a later local version of the disputed answer path. It
    // dominates an older candidate only where both discharge a common query face; unrelated
    // evidence remains available rather than being globally erased.
    let corrective_horizon = candidates
        .iter()
        .filter(|candidate| candidate.corrective && candidate.local_region_fiber.is_closed())
        .map(|candidate| candidate.revision_horizon)
        .max();
    let eligible_revisions = fully_closed
        .iter()
        .copied()
        .filter(|candidate_at| {
            let Some(horizon) = corrective_horizon else {
                return true;
            };
            let candidate = &candidates[*candidate_at];
            candidate.revision_horizon >= horizon
                || !candidates.iter().any(|corrective| {
                    corrective.corrective
                        && corrective.revision_horizon == horizon
                        && !candidate
                            .discharged_query_faces
                            .is_disjoint(&corrective.discharged_query_faces)
                })
        })
        .collect::<Vec<_>>();
    // A closed relation cell carries the joined subject/relation/object incidence which caused
    // its surface. Where such a cell exists it is the higher-order local body; a lexical path
    // through one of its witnesses is retained as evidence but cannot displace the relation body.
    let relational_revisions = if eligible_revisions
        .iter()
        .any(|candidate_at| candidates[*candidate_at].relational_thought.is_some())
    {
        eligible_revisions
            .iter()
            .copied()
            .filter(|candidate_at| candidates[*candidate_at].relational_thought.is_some())
            .collect::<Vec<_>>()
    } else {
        eligible_revisions
    };
    let maximal_query_faces = relational_revisions
        .iter()
        .copied()
        .filter(|left| {
            !relational_revisions.iter().copied().any(|right| {
                candidates[*left]
                    .discharged_query_faces
                    .is_subset(&candidates[right].discharged_query_faces)
                    && candidates[*left].discharged_query_faces
                        != candidates[right].discharged_query_faces
            })
        })
        .collect::<Vec<_>>();
    let maximal = maximal_query_faces
        .iter()
        .copied()
        .filter(|left| {
            !maximal_query_faces.iter().copied().any(|right| {
                candidates[*left]
                    .evidence_sources
                    .is_subset(&candidates[right].evidence_sources)
                    && candidates[*left].evidence_sources != candidates[right].evidence_sources
            })
        })
        .collect::<Vec<_>>();
    let (selected, retained_alternatives) =
        terminal_restrict_maximal_candidate(&candidates, &maximal)?;
    let selected_tokens = selected
        .generated
        .tokens
        .iter()
        .map(|token| token.token.clone())
        .collect::<Vec<_>>();
    let novel = !selected.inherited_surfaces.iter().any(|surface| {
        surface
            .windows(selected_tokens.len())
            .any(|window| window == selected_tokens)
    });
    let selection = AgenticAnswerSelection {
        closed_population: candidates
            .iter()
            .filter(|candidate| candidate.generated.rest == MorphologicalResponseRest::Closed)
            .count(),
        world_grounded_population: candidates.len(),
        inherited_path_population: candidates
            .iter()
            .filter(|candidate| {
                let tokens = candidate
                    .generated
                    .tokens
                    .iter()
                    .map(|token| token.token.clone())
                    .collect::<Vec<_>>();
                candidate
                    .inherited_surfaces
                    .iter()
                    .any(|surface| surface.windows(tokens.len()).any(|window| window == tokens))
            })
            .count(),
        inclusion_maximal_population: maximal.len(),
        selected_token_extent: selected.generated.tokens.len(),
        selected_phase_extent: selected.generated.phases.len(),
        composed_current_population: candidates
            .iter()
            .filter(|candidate| candidate.composed_current_population > 0)
            .count(),
        retained_alternative_population: retained_alternatives.len(),
    };

    // THE DIVISION, TAKEN. The remainder was retained above and had no relation to the answer; it
    // now comes back either as indistinguishable under the declared family or as separated, with
    // the word that separates it.
    let material = PresentationMaterial {
        inherited_surfaces: candidates
            .iter()
            .flat_map(|candidate| candidate.inherited_surfaces.iter().cloned())
            .collect(),
    };
    let answer_identity = selected_tokens.join(" ");
    let mut presented = vec![PresentedCandidate::new(
        answer_identity.clone(),
        selected_tokens.clone(),
    )];
    for alternative in &retained_alternatives {
        let tokens = alternative_surface(alternative);
        let identity = tokens.join(" ");
        if identity == answer_identity {
            continue;
        }
        presented.push(PresentedCandidate::new(identity, tokens));
    }
    let presentation_division = divide(&presented, &answer_identity, &material)
        .map_err(|_| AgenticLanguageError::NoGroundedLanguageReturn)?;

    let AnswerCandidate {
        generated,
        episode_identities,
        evidence_sources,
        reflection,
        received_prompt,
        contextual_dialogue,
        obligation_population,
        local_region_fiber,
        relational_thought,
        relational_thoughts,
        codec_versions,
        cultivated_codec_paths,
        ..
    } = selected;
    Ok(SelectedAnswerCandidate {
        generated,
        episode_identities,
        evidence_sources,
        selection,
        reflection,
        novel_contiguous_surface: novel,
        received_prompt,
        contextual_dialogue,
        obligation_population,
        local_region_fiber,
        relational_thought,
        relational_thoughts,
        codec_versions,
        cultivated_codec_paths,
        retained_alternatives,
        presentation_division,
    })
}

/// Restrict one inclusion-maximal current through this outward receiver. Equal surfaces glue
/// their lineage. Distinct surfaces remain exact alternatives and are never sequenced into a
/// sentence which no causal current generated. Population order is causal emission order, not a
/// lexical or length ranking.
pub(super) fn terminal_restrict_maximal_candidate(
    candidates: &[AnswerCandidate],
    maximal: &[usize],
) -> Result<(AnswerCandidate, Vec<AgenticRetainedAnswerAlternative>), AgenticLanguageError> {
    let Some(first) = maximal.first().and_then(|at| candidates.get(*at)) else {
        return Err(AgenticLanguageError::NoGroundedLanguageReturn);
    };
    let mut returned = first.clone();
    let selected_surface = returned
        .generated
        .tokens
        .iter()
        .map(|token| token.token.clone())
        .collect::<Vec<_>>();
    let mut retained_alternatives = Vec::new();
    for alternative in std::mem::take(&mut returned.retained_alternatives) {
        if alternative_surface(&alternative) == selected_surface {
            returned
                .episode_identities
                .extend(alternative.episode_identities);
            returned
                .evidence_sources
                .extend(alternative.evidence_sources);
            returned.relational_thoughts = combine_relational_thoughts(
                &returned.relational_thoughts,
                &alternative.relational_thoughts,
            );
        } else {
            retain_answer_alternative(&mut retained_alternatives, alternative);
        }
    }
    for candidate_at in maximal.iter().skip(1) {
        let candidate = candidates
            .get(*candidate_at)
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        let surface = candidate
            .generated
            .tokens
            .iter()
            .map(|token| token.token.clone())
            .collect::<Vec<_>>();
        if surface != selected_surface {
            retain_answer_alternative(
                &mut retained_alternatives,
                AgenticRetainedAnswerAlternative {
                    generated: candidate.generated.clone(),
                    episode_identities: candidate.episode_identities.clone(),
                    evidence_sources: candidate.evidence_sources.clone(),
                    relational_thoughts: candidate.relational_thoughts.clone(),
                },
            );
            for alternative in &candidate.retained_alternatives {
                retain_answer_alternative(&mut retained_alternatives, alternative.clone());
            }
            continue;
        }
        returned
            .episode_identities
            .extend(candidate.episode_identities.iter().cloned());
        returned
            .evidence_sources
            .extend(candidate.evidence_sources.iter().cloned());
        returned
            .discharged_query_faces
            .extend(candidate.discharged_query_faces.iter().cloned());
        returned
            .contextual_dialogue
            .extend(candidate.contextual_dialogue.iter().cloned());
        returned
            .ordered_query_regions
            .extend(candidate.ordered_query_regions.iter().cloned());
        returned
            .codec_versions
            .extend(candidate.codec_versions.iter().cloned());
        for passage in &candidate.conditioning_passages {
            if !returned
                .conditioning_passages
                .iter()
                .any(|prior| prior.identity == passage.identity)
            {
                returned.conditioning_passages.push(passage.clone());
            }
        }
        returned
            .inherited_surfaces
            .extend(candidate.inherited_surfaces.iter().cloned());
        returned.cultivated_codec_paths = returned
            .cultivated_codec_paths
            .iter()
            .chain(&candidate.cultivated_codec_paths)
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        returned.relational_thoughts = combine_relational_thoughts(
            &returned.relational_thoughts,
            &candidate.relational_thoughts,
        );
        returned.reflection = compose_reflection_receipts(
            &returned.reflection,
            &candidate.reflection,
            std::slice::from_ref(&returned.generated),
        )?;
        returned.obligation_population = returned
            .obligation_population
            .max(candidate.obligation_population);
        returned
            .local_region_fiber
            .glue(&candidate.local_region_fiber);
        returned.revision_horizon = returned.revision_horizon.max(candidate.revision_horizon);
        returned.corrective |= candidate.corrective;
        returned.composed_current_population = returned
            .composed_current_population
            .checked_add(candidate.composed_current_population)
            .and_then(|population| population.checked_add(1))
            .ok_or(AgenticLanguageError::CarrierExtent)?;
        for alternative in &candidate.retained_alternatives {
            if alternative_surface(alternative) != selected_surface {
                retain_answer_alternative(&mut retained_alternatives, alternative.clone());
            }
        }
    }
    Ok((returned, retained_alternatives))
}

pub(super) fn alternative_surface(alternative: &AgenticRetainedAnswerAlternative) -> Vec<String> {
    alternative
        .generated
        .tokens
        .iter()
        .map(|token| token.token.clone())
        .collect()
}

pub(super) fn retain_answer_alternative(
    retained: &mut Vec<AgenticRetainedAnswerAlternative>,
    alternative: AgenticRetainedAnswerAlternative,
) {
    let surface = alternative_surface(&alternative);
    if let Some(prior) = retained
        .iter_mut()
        .find(|prior| alternative_surface(prior) == surface)
    {
        prior
            .episode_identities
            .extend(alternative.episode_identities);
        prior.evidence_sources.extend(alternative.evidence_sources);
        prior.relational_thoughts = combine_relational_thoughts(
            &prior.relational_thoughts,
            &alternative.relational_thoughts,
        );
    } else {
        retained.push(alternative);
    }
}

pub(super) fn charge_is_grounded(
    charge: &MorphologicalQuestionCharge,
    evidence_sources: &BTreeSet<String>,
) -> bool {
    !charge.obligations.is_empty()
        && charge.obligations.iter().all(|obligation| {
            obligation.local_regions.iter().any(|region| {
                region
                    .reached_sources
                    .iter()
                    .any(|source| evidence_sources.contains(source))
            })
        })
}

pub(super) fn question_regions(charge: &MorphologicalQuestionCharge) -> BTreeSet<Vec<String>> {
    charge
        .obligations
        .iter()
        .flat_map(|obligation| obligation.local_regions.iter())
        .map(|region| {
            region
                .ordered_surface
                .iter()
                .filter(|surface| !charge.operator_features.contains(*surface))
                .cloned()
                .collect::<Vec<_>>()
        })
        .filter(|region| !region.is_empty())
        .collect()
}

pub(super) fn question_local_regions(
    charge: &MorphologicalQuestionCharge,
) -> LocalSet<AgenticAnswerRegionIdentity> {
    LocalSet::from_iter(
        charge
            .obligations
            .iter()
            .enumerate()
            .flat_map(|(obligation, face)| {
                (0..face.local_regions.len())
                    .map(move |region| AgenticAnswerRegionIdentity { obligation, region })
            }),
    )
}

pub(super) fn index_surfaces(
    atlas: &mut BTreeMap<String, BTreeSet<usize>>,
    episode: usize,
    surfaces: &BTreeSet<String>,
) {
    for surface in surfaces {
        atlas.entry(surface.clone()).or_default().insert(episode);
    }
}

pub(super) fn word_surfaces(text: &str) -> Vec<String> {
    lexical_tokens(text)
        .into_iter()
        .filter(|token| token.chars().any(char::is_alphanumeric))
        .map(|token| token.to_lowercase())
        .collect()
}

/// Simultaneous receiver scales over one question chronology. Every view owns one complete
/// prefix or suffix region, so exact route derivation remains local and cannot manufacture
/// recurrence by placing several equal cuts in one view. Prefix and suffix are distinct charts;
/// the full region lawfully appears in both because their orientations differ.
pub(super) fn maximal_return_section_indices(
    question: &str,
    sections: &[MorphologicalLanguagePassage],
    operator_features: &BTreeSet<String>,
    maximum_observed_tokens: usize,
) -> Vec<usize> {
    let question_surfaces = word_surfaces(question);
    let question_content = question_surfaces
        .iter()
        .filter(|surface| !operator_features.contains(*surface))
        .cloned()
        .collect::<BTreeSet<_>>();
    let ordered_faces = sections
        .iter()
        .map(|section| {
            let section_surfaces = word_surfaces(&section.text);
            common_ordered_regions(&question_surfaces, &section_surfaces)
                .into_iter()
                .filter(|region| {
                    region.len() >= 2
                        && region
                            .iter()
                            .any(|surface| !operator_features.contains(surface))
                })
                .collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    let has_ordered_contact = ordered_faces.iter().any(|face| !face.is_empty());
    let faces = if has_ordered_contact {
        ordered_faces
    } else {
        sections
            .iter()
            .map(|section| {
                word_surfaces(&section.text)
                    .into_iter()
                    .filter(|surface| question_content.contains(surface))
                    .map(|surface| vec![surface])
                    .collect::<BTreeSet<_>>()
            })
            .collect()
    };
    (0..sections.len())
        .filter(|section| {
            lexical_tokens(&sections[*section].text).len() <= maximum_observed_tokens
                && !faces[*section].is_empty()
                && !(0..sections.len()).any(|other| {
                    lexical_tokens(&sections[other].text).len() <= maximum_observed_tokens
                        && return_face_is_strict_refinement(&faces[*section], &faces[other])
                })
        })
        .collect()
}

pub(super) fn maximal_episode_indices(
    question: &str,
    episodes: &[LanguageEpisode],
    candidates: Vec<usize>,
    operator_features: &BTreeSet<String>,
    maximum_observed_tokens: usize,
    obstructed_episodes: &BTreeSet<String>,
) -> Vec<usize> {
    let question_surfaces = word_surfaces(question);
    let question_content = question_surfaces
        .iter()
        .filter(|surface| !operator_features.contains(*surface))
        .cloned()
        .collect::<BTreeSet<_>>();
    let ordered_faces = candidates
        .iter()
        .map(|episode_at| {
            episodes
                .get(*episode_at)
                .into_iter()
                .flat_map(|episode| &episode.passages)
                .flat_map(|passage| {
                    common_ordered_regions(&question_surfaces, &word_surfaces(&passage.text))
                })
                .filter(|region| {
                    region.len() >= 2
                        && region
                            .iter()
                            .any(|surface| !operator_features.contains(surface))
                })
                .collect::<BTreeSet<_>>()
        })
        .collect::<Vec<_>>();
    let has_ordered_contact = ordered_faces.iter().any(|face| !face.is_empty());
    let faces = if has_ordered_contact {
        ordered_faces
    } else {
        candidates
            .iter()
            .map(|episode_at| {
                episodes
                    .get(*episode_at)
                    .into_iter()
                    .flat_map(|episode| episode.routing_surfaces.iter())
                    .filter(|surface| question_content.contains(*surface))
                    .map(|surface| vec![surface.clone()])
                    .collect::<BTreeSet<_>>()
            })
            .collect::<Vec<_>>()
    };
    (0..candidates.len())
        .filter(|candidate_at| {
            let Some(episode) = episodes.get(candidates[*candidate_at]) else {
                return false;
            };
            if !episode.answerable || obstructed_episodes.contains(&episode.identity) {
                return false;
            }
            let within_aperture = episode
                .passages
                .iter()
                .any(|passage| lexical_tokens(&passage.text).len() <= maximum_observed_tokens);
            within_aperture
                && !faces[*candidate_at].is_empty()
                && !(0..candidates.len()).any(|other_at| {
                    let Some(other) = episodes.get(candidates[other_at]) else {
                        return false;
                    };
                    if !other.answerable || obstructed_episodes.contains(&other.identity) {
                        return false;
                    }
                    other.passages.iter().any(|passage| {
                        lexical_tokens(&passage.text).len() <= maximum_observed_tokens
                    }) && return_face_is_strict_refinement(&faces[*candidate_at], &faces[other_at])
                })
        })
        .map(|candidate_at| candidates[candidate_at])
        .collect()
}

pub(super) fn return_face_is_strict_refinement(
    section: &BTreeSet<Vec<String>>,
    other: &BTreeSet<Vec<String>>,
) -> bool {
    let section_reaches_other = section.iter().all(|region| {
        other.iter().any(|other_region| {
            other_region
                .windows(region.len())
                .any(|window| window == region)
        })
    });
    let other_reaches_section = other.iter().all(|region| {
        section.iter().any(|section_region| {
            section_region
                .windows(region.len())
                .any(|window| window == region)
        })
    });
    section_reaches_other && !other_reaches_section
}

pub(super) fn has_unlicensed_consecutive_repetition(
    tokens: &[String],
    inherited_surfaces: &[Vec<String>],
) -> bool {
    let mut extent = 2usize;
    while extent <= tokens.len() / 2 {
        let mut start = 0usize;
        while start + extent.saturating_mul(2) <= tokens.len() {
            let end = start + extent;
            if tokens[start..end] == tokens[end..end + extent]
                && !inherited_surfaces.iter().any(|surface| {
                    surface
                        .windows(extent.saturating_mul(2))
                        .any(|window| window == &tokens[start..end + extent])
                })
            {
                return true;
            }
            start += 1;
        }
        extent += 1;
    }
    false
}

pub(super) fn compose_reflection_receipts(
    left: &MorphologicalReflectionReceipt,
    right: &MorphologicalReflectionReceipt,
    outputs: &[MorphologicalGeneratedCurrent],
) -> Result<MorphologicalReflectionReceipt, AgenticLanguageError> {
    let composed_returned_events = outputs.iter().try_fold(0usize, |total, output| {
        total
            .checked_add(output.tokens.len())
            .ok_or(AgenticLanguageError::CarrierExtent)
    })?;
    Ok(MorphologicalReflectionReceipt {
        shared_conditioned_bodies: left
            .shared_conditioned_bodies
            .checked_add(right.shared_conditioned_bodies)
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        whole_body_forks: left
            .whole_body_forks
            .checked_add(right.whole_body_forks)
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        shared_current_forks: left
            .shared_current_forks
            .checked_add(right.shared_current_forks)
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        causal_current_states_formed: left
            .causal_current_states_formed
            .checked_add(right.causal_current_states_formed)
            .and_then(|extent| extent.checked_add(outputs.len()))
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        conduct_equivalent_states_glued: left
            .conduct_equivalent_states_glued
            .checked_add(right.conduct_equivalent_states_glued)
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        peak_live_current_states: left
            .peak_live_current_states
            .checked_add(right.peak_live_current_states)
            .and_then(|extent| extent.checked_add(outputs.len()))
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        returned_events_carried: left
            .returned_events_carried
            .checked_add(right.returned_events_carried)
            .and_then(|extent| extent.checked_add(composed_returned_events))
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        terminal_return_materializations: left
            .terminal_return_materializations
            .checked_add(right.terminal_return_materializations)
            .and_then(|extent| extent.checked_add(outputs.len()))
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        // Congestion is a property of one generation's own front, so composing two returns adds
        // the dilated passages and takes the deeper of the two extremes rather than summing them:
        // two fronts that each waited three tokens did not between them wait six.
        dilated_passages: left
            .dilated_passages
            .checked_add(right.dilated_passages)
            .ok_or(AgenticLanguageError::CarrierExtent)?,
        deepest_dilation: left.deepest_dilation.max(right.deepest_dilation),
        deepest_chronology: left.deepest_chronology.max(right.deepest_chronology),
    })
}

pub(super) fn answer_candidate_passages(candidate: &AnswerCandidate) -> BTreeSet<String> {
    candidate
        .conditioning_passages
        .iter()
        .map(|passage| passage.identity.clone())
        .collect()
}

/// A larger contextual receiver may resolve ellipsis, but it may not erase a newly introduced
/// direct surface. Every non-operator face of the visible occurrence must remain present either
/// in the emitted consequence or in one of its exact witnesses.
pub(super) fn candidate_witnesses_direct_question(
    candidate: &AnswerCandidate,
    question: &str,
    operator_features: &BTreeSet<String>,
) -> bool {
    let direct = word_surfaces(question)
        .into_iter()
        .filter(|surface| !operator_features.contains(surface))
        .collect::<BTreeSet<_>>();
    if direct.is_empty() {
        return true;
    }
    let witnessed = candidate
        .generated
        .tokens
        .iter()
        .map(|token| token.token.to_lowercase())
        .chain(
            candidate
                .conditioning_passages
                .iter()
                .flat_map(|passage| word_surfaces(&passage.text)),
        )
        .collect::<BTreeSet<_>>();
    direct.is_subset(&witnessed)
}

/// Context can enlarge an elliptical receiver only when every direct non-operator face already
/// occurs in that context. A novel face therefore causes its own route/clarification instead of
/// borrowing the prior turn's action and silently disappearing from the returned consequence.
pub(super) fn context_can_receive_question(
    question: &str,
    context: &str,
    operator_features: &BTreeSet<String>,
) -> bool {
    let direct = word_surfaces(question)
        .into_iter()
        .filter(|surface| !operator_features.contains(surface))
        .collect::<BTreeSet<_>>();
    direct.is_empty()
        || direct.is_subset(&word_surfaces(context).into_iter().collect::<BTreeSet<_>>())
}

pub(super) fn answer_candidate_signature(
    candidate: &AnswerCandidate,
) -> (Vec<String>, Vec<String>) {
    (
        candidate
            .generated
            .tokens
            .iter()
            .map(|token| token.token.clone())
            .collect(),
        answer_candidate_passages(candidate).into_iter().collect(),
    )
}

pub(super) fn candidates_have_disjoint_passages(
    left: &AnswerCandidate,
    right: &AnswerCandidate,
) -> bool {
    !left.conditioning_passages.iter().any(|left_passage| {
        right
            .conditioning_passages
            .iter()
            .any(|right_passage| right_passage.identity == left_passage.identity)
    })
}

pub(super) fn candidates_admit_composition(
    left: &AnswerCandidate,
    right: &AnswerCandidate,
) -> bool {
    if left.relational_thoughts.is_empty() || right.relational_thoughts.is_empty() {
        return true;
    }
    let left_has_unreturned_face = left
        .ordered_query_regions
        .iter()
        .any(|region| !ordered_region_family_covers(&right.ordered_query_regions, region));
    let right_has_unreturned_face = right
        .ordered_query_regions
        .iter()
        .any(|region| !ordered_region_family_covers(&left.ordered_query_regions, region));
    left_has_unreturned_face && right_has_unreturned_face
}

pub(super) fn compose_answer_candidates(
    left: &AnswerCandidate,
    right: &AnswerCandidate,
    received_prompt: &str,
    contextual_dialogue: &BTreeSet<String>,
    maximum_observed_tokens: usize,
) -> Result<Vec<AnswerCandidate>, AgenticLanguageError> {
    let right_generated =
        rebase_generated_obligations(&right.generated, left.obligation_population)?;
    let mut outputs = MorphologicalGeneratedCurrent::compose_returned_currents(
        &left.generated,
        &right_generated,
        maximum_observed_tokens,
    )?;
    // A second phase must carry an actual ordered query region not already carried by the other
    // phase. Singleton lexical contact remains useful routing testimony, but it cannot by itself
    // force an otherwise closed answer to append another whole sentence.
    let left_regions = left
        .ordered_query_regions
        .iter()
        .filter(|region| !ordered_region_family_covers(&right.ordered_query_regions, region))
        .filter(|region| region.len() > 1)
        .cloned()
        .collect::<BTreeSet<_>>();
    let right_regions = right
        .ordered_query_regions
        .iter()
        .filter(|region| !ordered_region_family_covers(&left.ordered_query_regions, region))
        .filter(|region| region.len() > 1)
        .cloned()
        .collect::<BTreeSet<_>>();
    let faces_are_complementary = !left_regions.is_empty() && !right_regions.is_empty();
    if faces_are_complementary {
        let surfaces = word_surfaces(received_prompt);
        let left_at = query_region_offset(&surfaces, &left_regions);
        let right_at = query_region_offset(&surfaces, &right_regions);
        let (first, second) = if (left_at, left.generated.text.as_str())
            <= (right_at, right.generated.text.as_str())
        {
            (&left.generated, &right_generated)
        } else {
            (&right_generated, &left.generated)
        };
        if let Some(sequenced) = MorphologicalGeneratedCurrent::sequence_returned_currents(
            first,
            second,
            maximum_observed_tokens,
        )? {
            outputs.push(sequenced);
        }
    }
    if outputs.is_empty() {
        return Ok(Vec::new());
    }
    let mut working = left.conditioning_passages.clone();
    for passage in &right.conditioning_passages {
        if !working
            .iter()
            .any(|prior| prior.identity == passage.identity)
        {
            working.push(passage.clone());
        }
    }
    let evidence_sources = left
        .evidence_sources
        .union(&right.evidence_sources)
        .cloned()
        .collect::<BTreeSet<_>>();
    let required_passages = working
        .iter()
        .map(|passage| passage.identity.clone())
        .collect::<BTreeSet<_>>();
    let episode_identities = left
        .episode_identities
        .union(&right.episode_identities)
        .cloned()
        .collect::<BTreeSet<_>>();
    let codec_versions = left
        .codec_versions
        .union(&right.codec_versions)
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut combined_required_local_regions =
        LocalSet::from_iter(left.local_region_fiber.required.iter().copied());
    for region in &right.local_region_fiber.required {
        combined_required_local_regions.insert(AgenticAnswerRegionIdentity {
            obligation: region
                .obligation
                .checked_add(left.obligation_population)
                .ok_or(AgenticLanguageError::CarrierExtent)?,
            region: region.region,
        });
    }
    let mut candidates = Vec::new();
    for output in outputs {
        let reflection = compose_reflection_receipts(
            &left.reflection,
            &right.reflection,
            std::slice::from_ref(&output),
        )?;
        let combined_query_regions = left
            .ordered_query_regions
            .union(&right.ordered_query_regions)
            .cloned()
            .collect::<BTreeSet<_>>();
        match select_generated_answer(
            std::slice::from_ref(&output),
            &evidence_sources,
            &required_passages,
            &reflection,
            &working,
            episode_identities.clone(),
            codec_versions.clone(),
            received_prompt,
            contextual_dialogue,
            left.obligation_population
                .checked_add(right.obligation_population)
                .ok_or(AgenticLanguageError::CarrierExtent)?,
            &combined_required_local_regions,
            &combined_query_regions,
            left.revision_horizon.max(right.revision_horizon),
            left.corrective || right.corrective,
        ) {
            Ok(mut candidate) => {
                candidate.composed_current_population = left
                    .composed_current_population
                    .checked_add(right.composed_current_population)
                    .and_then(|population| population.checked_add(1))
                    .ok_or(AgenticLanguageError::CarrierExtent)?;
                candidate.cultivated_codec_paths = left
                    .cultivated_codec_paths
                    .iter()
                    .chain(&right.cultivated_codec_paths)
                    .cloned()
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .collect();
                candidate.relational_thoughts = combine_relational_thoughts(
                    &left.relational_thoughts,
                    &right.relational_thoughts,
                );
                candidate.relational_thought = left
                    .relational_thought
                    .to_owned()
                    .or_else(|| right.relational_thought.to_owned());
                candidates.push(candidate);
            }
            Err(AgenticLanguageError::NoGroundedLanguageReturn) => {}
            Err(error) => return Err(error),
        }
    }
    Ok(candidates)
}

fn rebase_generated_obligations(
    generated: &MorphologicalGeneratedCurrent,
    offset: usize,
) -> Result<MorphologicalGeneratedCurrent, AgenticLanguageError> {
    let mut rebased = generated.clone();
    for phase in &mut rebased.phases {
        phase.discharged_obligations = phase
            .discharged_obligations
            .iter()
            .map(|obligation| {
                obligation
                    .checked_add(offset)
                    .ok_or(AgenticLanguageError::CarrierExtent)
            })
            .collect::<Result<_, _>>()?;
        phase.discharged_regions = phase
            .discharged_regions
            .iter()
            .map(|(obligation, regions)| {
                Ok((
                    obligation
                        .checked_add(offset)
                        .ok_or(AgenticLanguageError::CarrierExtent)?,
                    regions.clone(),
                ))
            })
            .collect::<Result<_, AgenticLanguageError>>()?;
        phase.discharged_features = phase
            .discharged_features
            .iter()
            .map(|(obligation, features)| {
                Ok((
                    obligation
                        .checked_add(offset)
                        .ok_or(AgenticLanguageError::CarrierExtent)?,
                    features.clone(),
                ))
            })
            .collect::<Result<_, AgenticLanguageError>>()?;
    }
    Ok(rebased)
}

pub(super) fn combine_relational_thoughts(
    left: &[RelationalThoughtCurrent],
    right: &[RelationalThoughtCurrent],
) -> Vec<RelationalThoughtCurrent> {
    let mut combined = left.to_vec();
    for thought in right {
        if !combined.contains(thought) {
            combined.push(thought.clone());
        }
    }
    combined
}

pub(super) fn query_region_offset(surfaces: &[String], regions: &BTreeSet<Vec<String>>) -> usize {
    regions
        .iter()
        .map(|region| first_region_offset(surfaces, region))
        .min()
        .unwrap_or(usize::MAX)
}

pub(super) fn ordered_region_family_covers(
    family: &BTreeSet<Vec<String>>,
    region: &[String],
) -> bool {
    family.iter().any(|other| {
        region.len() <= other.len() && other.windows(region.len()).any(|window| window == region)
    })
}

pub(super) fn unordered_surface_pairs(surfaces: &BTreeSet<String>) -> BTreeSet<(String, String)> {
    let ordered = surfaces.iter().collect::<Vec<_>>();
    let mut pairs = BTreeSet::new();
    let mut left = 0usize;
    while left < ordered.len() {
        let mut right = left + 1;
        while right < ordered.len() {
            pairs.insert((ordered[left].clone(), ordered[right].clone()));
            right += 1;
        }
        left += 1;
    }
    pairs
}

pub(super) fn common_ordered_regions(left: &[String], right: &[String]) -> BTreeSet<Vec<String>> {
    let mut regions = BTreeSet::new();
    let mut left_at = 0usize;
    while left_at < left.len() {
        let mut right_at = 0usize;
        while right_at < right.len() {
            if left[left_at] != right[right_at] {
                right_at += 1;
                continue;
            }
            let mut extent = 0usize;
            while left_at + extent < left.len()
                && right_at + extent < right.len()
                && left[left_at + extent] == right[right_at + extent]
            {
                extent += 1;
            }
            if extent > 0 {
                regions.insert(left[left_at..left_at + extent].to_vec());
            }
            right_at += extent.max(1);
        }
        left_at += 1;
    }
    let snapshot = regions.iter().cloned().collect::<Vec<_>>();
    regions.retain(|region| {
        !snapshot.iter().any(|other| {
            region.len() < other.len()
                && other
                    .windows(region.len())
                    .any(|window| window == region.as_slice())
        })
    });
    regions
}
