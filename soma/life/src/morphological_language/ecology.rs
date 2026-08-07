use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
struct ClauseStanding {
    fiber: ReceiverFiberIdentity,
    identity: String,
    passage: ReceiverFiberIdentity,
    source: ReceiverFiberIdentity,
    receiver: u64,
    tokens: Vec<String>,
    features: BTreeSet<String>,
    boundary: MorphologicalBoundary,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PassageStanding {
    identity: String,
    source: ReceiverFiberIdentity,
    receiver: u64,
    tokens: Vec<String>,
    features: BTreeSet<String>,
    clauses: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SourceStanding {
    identity: String,
    receiver: u64,
}

/// One conditioned intermediate body carrying all language receiver scales concurrently.
#[derive(Debug)]
pub struct MorphologicalLanguageEcology {
    route_sections: BTreeMap<String, BTreeSet<ReceiverFiberIdentity>>,
    passages: BTreeMap<ReceiverFiberIdentity, PassageStanding>,
    sources: BTreeMap<ReceiverFiberIdentity, SourceStanding>,
    clauses: Vec<ClauseStanding>,
    clause_routes: BTreeMap<String, BTreeSet<usize>>,
    lexical_suffix: ExactLabeledSuffixEcology,
    clause_lexical_suffix: ExactLabeledSuffixEcology,
    ordered_region_suffix: ExactLabeledSuffixEcology,
    clause_labels: BTreeMap<ReceiverFiberIdentity, usize>,
    question_operator_prefixes: BTreeMap<Vec<String>, BTreeSet<ReceiverFiberIdentity>>,
    forward_mark_suffix: ExactLabeledSuffixEcology,
    reverse_mark_suffix: ExactLabeledSuffixEcology,
    census: MorphologicalScaleCensus,
}

impl MorphologicalLanguageEcology {
    pub fn condition(
        passages: &[MorphologicalLanguagePassage],
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<Self, MorphologicalLanguageError> {
        Self::condition_inner(passages, action, worker_threads, None)
    }

    /// Condition the complete morphology through one explicitly mounted physical executor.
    /// Structural suffix and chart formation remains exact host assembly; every Swing event which
    /// changes route standing crosses the supplied executor instead of an internally selected CPU
    /// worker.
    pub fn condition_with_executor(
        passages: &[MorphologicalLanguagePassage],
        action: ActionCurrent,
        worker_threads: usize,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<Self, MorphologicalLanguageError> {
        Self::condition_inner(passages, action, worker_threads, Some(executor))
    }

    fn condition_inner(
        passages: &[MorphologicalLanguagePassage],
        action: ActionCurrent,
        worker_threads: usize,
        route_executor: Option<&mut dyn LiveCurrentExecutor>,
    ) -> Result<Self, MorphologicalLanguageError> {
        if passages.is_empty() {
            return Err(MorphologicalLanguageError::EmptyCorpus);
        }
        let mut identities = BTreeSet::new();
        let mut passages_standing = BTreeMap::new();
        let mut sources = BTreeMap::<ReceiverFiberIdentity, SourceStanding>::new();
        let mut clauses = Vec::<ClauseStanding>::new();
        let mut lexical_paths = Vec::new();
        let mut lexical_labels = Vec::new();
        let mut passage_feature_sections = BTreeMap::<String, Vec<RouteTrainingSection>>::new();
        let mut mark_sources = BTreeMap::<String, BTreeSet<ReceiverFiberIdentity>>::new();
        let mut lexical_occurrences = 0usize;

        // The caller supplies caused occurrence chronology. Receiver/source/identity order is a
        // useful atlas projection, but sorting by that projection here would replace transport
        // with address order and make the two conditioning organs disagree about the same body.
        for (source_order, passage) in passages.iter().enumerate() {
            if !identities.insert(passage.identity.clone()) {
                return Err(MorphologicalLanguageError::DuplicatePassage(
                    passage.identity.clone(),
                ));
            }
            let tokens = lexical_tokens(&passage.text);
            if tokens.is_empty() {
                return Err(MorphologicalLanguageError::EmptyPassage(
                    passage.identity.clone(),
                ));
            }
            lexical_occurrences = lexical_occurrences
                .checked_add(tokens.len())
                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
            let source = lineage_fiber(&passage.source, passage.receiver)?;
            if let Some(prior) = sources.get(&source) {
                if prior.receiver != passage.receiver || prior.identity != passage.source {
                    return Err(MorphologicalLanguageError::ConflictingSourceReceiver(
                        passage.source.clone(),
                    ));
                }
            } else {
                sources.insert(
                    source.clone(),
                    SourceStanding {
                        identity: passage.source.clone(),
                        receiver: passage.receiver,
                    },
                );
            }
            let passage_fiber = passage_fiber(&passage.identity, passage.receiver)?;
            let features = surface_features(&tokens);
            let source_order = u64::try_from(source_order)
                .map_err(|_| MorphologicalLanguageError::CarrierExtent)?;
            for feature in &features {
                passage_feature_sections
                    .entry(feature.clone())
                    .or_default()
                    .push(RouteTrainingSection {
                        source_order,
                        source: passage_fiber.clone(),
                    });
            }
            for token in tokens.iter().filter(|token| is_surface_word(token)) {
                mark_sources
                    .entry(token.to_lowercase())
                    .or_default()
                    .insert(source.clone());
            }
            lexical_paths.push(token_germs(&tokens)?);
            // The complete lexical chart retains delivery occurrence support. Source lineage is
            // then derived from those occurrences, so two deliveries from one source cannot be
            // silently fused into one apparent chronological path.
            lexical_labels.push(passage_fiber.clone());

            let clause_start = clauses.len();
            let clause_rows = clause_sections(&tokens);
            for (clause_at, (clause_tokens, boundary)) in clause_rows.into_iter().enumerate() {
                let identity = format!("{}::clause::{clause_at}", passage.identity);
                let fiber = clause_fiber(&identity, passage.receiver)?;
                clauses.push(ClauseStanding {
                    fiber,
                    identity,
                    passage: passage_fiber.clone(),
                    source: source.clone(),
                    receiver: passage.receiver,
                    features: surface_features(&clause_tokens),
                    tokens: clause_tokens,
                    boundary,
                });
            }
            let clause_end = clauses.len();
            let clause_ids = (clause_start..clause_end).collect::<Vec<_>>();
            if passages_standing
                .insert(
                    passage_fiber,
                    PassageStanding {
                        identity: passage.identity.clone(),
                        source,
                        receiver: passage.receiver,
                        tokens,
                        features,
                        clauses: clause_ids,
                    },
                )
                .is_some()
            {
                return Err(MorphologicalLanguageError::MalformedFiber);
            }
        }

        // A feature which occurs in every delivered section supplies no distinction in this
        // conditioned world. This exact incidence restriction replaces a hard word-length rule:
        // short specialized faces remain, while long universal faces do not become routers.
        passage_feature_sections.retain(|_, sections| sections.len() < passages_standing.len());
        let mut route_groups = BTreeMap::<ReceiverFiberIdentity, Vec<RouteTrainingSection>>::new();
        let mut feature_names = BTreeMap::<ReceiverFiberIdentity, String>::new();
        let mut returned_route_relations = 0usize;
        for (feature, sections) in passage_feature_sections {
            let identity = route_feature_fiber(&feature);
            returned_route_relations = returned_route_relations
                .checked_add(sections.len())
                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
            feature_names.insert(identity.clone(), feature);
            route_groups.insert(identity, sections);
        }
        let (_, returned_sections, conditioning_events) = match route_executor {
            Some(executor) => {
                condition_route_receivers_with_executor(route_groups, action, executor)?
            }
            None => condition_route_receivers(route_groups, action, worker_threads)?,
        };
        let mut route_sections = BTreeMap::new();
        for (identity, targets) in returned_sections {
            let feature = feature_names
                .get(&identity)
                .ok_or(MorphologicalLanguageError::MalformedFiber)?
                .clone();
            route_sections.insert(feature, targets);
        }

        let mut clause_routes = BTreeMap::<String, BTreeSet<usize>>::new();
        for (feature, passage_targets) in &route_sections {
            for passage in passage_targets {
                let standing = passages_standing
                    .get(passage)
                    .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                for clause in &standing.clauses {
                    if clauses.get(*clause).is_some_and(|standing| {
                        standing.features.contains(feature)
                            && standing.tokens.last().is_none_or(|token| token != "?")
                    }) {
                        clause_routes
                            .entry(feature.clone())
                            .or_default()
                            .insert(*clause);
                    }
                }
            }
        }

        let mut clause_lexical_paths = Vec::new();
        let mut clause_lexical_labels = Vec::new();
        let mut ordered_region_paths = Vec::new();
        let mut ordered_region_labels = Vec::new();
        let mut clause_labels = BTreeMap::new();
        let mut question_prefix_support = BTreeMap::<
            Vec<String>,
            (
                BTreeSet<ReceiverFiberIdentity>,
                BTreeSet<ReceiverFiberIdentity>,
                BTreeSet<String>,
            ),
        >::new();
        for (clause_at, clause) in clauses.iter().enumerate() {
            if clause_labels
                .insert(clause.fiber.clone(), clause_at)
                .is_some()
            {
                return Err(MorphologicalLanguageError::MalformedFiber);
            }
            let ordered_surface = folded_surface_tokens(&clause.tokens);
            let is_question = clause.tokens.last().is_some_and(|token| token == "?");
            if is_question {
                for end in 1..ordered_surface.len() {
                    let support = question_prefix_support
                        .entry(ordered_surface[..end].to_vec())
                        .or_default();
                    support.0.insert(clause.source.clone());
                    support.1.insert(clause.fiber.clone());
                    support.2.insert(ordered_surface[end].clone());
                }
            } else if !ordered_surface.is_empty() {
                clause_lexical_paths.push(token_germs(&clause.tokens)?);
                clause_lexical_labels.push(clause.fiber.clone());
                ordered_region_paths.push(token_germs(&ordered_surface)?);
                ordered_region_labels.push(clause.fiber.clone());
            }
        }
        let question_operator_prefixes = question_prefix_support
            .into_iter()
            .filter_map(|(prefix, (sources, occurrences, continuations))| {
                (occurrences.len() >= 2 && continuations.len() >= 2).then_some((prefix, sources))
            })
            .collect::<BTreeMap<_, _>>();
        let mut mark_paths = Vec::new();
        let mut mark_labels = Vec::new();
        for (surface, labels) in mark_sources {
            for label in labels {
                mark_paths.push(mark_germs(&surface)?);
                mark_labels.push(label);
            }
        }
        let mark_word_occurrences = mark_paths.len();
        let reverse_paths = mark_paths
            .iter()
            .map(|path| path.iter().cloned().rev().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        // These five charts are co-present restrictions of the already received passages. None
        // consumes another chart's result, so a serial construction invented a chronology and left
        // one CPU core building independent exact bodies. Preserve the requested worker budget and
        // form all five concurrently when it can supply one worker per chart.
        let (
            lexical_suffix,
            clause_lexical_suffix,
            ordered_region_suffix,
            forward_mark_suffix,
            reverse_mark_suffix,
        ) = if worker_threads >= 5 {
            std::thread::scope(|scope| {
                let lexical = scope.spawn(|| {
                    ExactLabeledSuffixEcology::condition(&lexical_paths, &lexical_labels)
                });
                let clause_lexical = scope.spawn(|| {
                    ExactLabeledSuffixEcology::condition(
                        &clause_lexical_paths,
                        &clause_lexical_labels,
                    )
                });
                let ordered_region = scope.spawn(|| {
                    ExactLabeledSuffixEcology::condition(
                        &ordered_region_paths,
                        &ordered_region_labels,
                    )
                });
                let forward_mark =
                    scope.spawn(|| ExactLabeledSuffixEcology::condition(&mark_paths, &mark_labels));
                let reverse_mark = scope
                    .spawn(|| ExactLabeledSuffixEcology::condition(&reverse_paths, &mark_labels));
                Ok::<_, MorphologicalLanguageError>((
                    lexical
                        .join()
                        .map_err(|_| MorphologicalLanguageError::CarrierExtent)??,
                    clause_lexical
                        .join()
                        .map_err(|_| MorphologicalLanguageError::CarrierExtent)??,
                    ordered_region
                        .join()
                        .map_err(|_| MorphologicalLanguageError::CarrierExtent)??,
                    forward_mark
                        .join()
                        .map_err(|_| MorphologicalLanguageError::CarrierExtent)??,
                    reverse_mark
                        .join()
                        .map_err(|_| MorphologicalLanguageError::CarrierExtent)??,
                ))
            })?
        } else {
            (
                ExactLabeledSuffixEcology::condition(&lexical_paths, &lexical_labels)?,
                ExactLabeledSuffixEcology::condition(
                    &clause_lexical_paths,
                    &clause_lexical_labels,
                )?,
                ExactLabeledSuffixEcology::condition(
                    &ordered_region_paths,
                    &ordered_region_labels,
                )?,
                ExactLabeledSuffixEcology::condition(&mark_paths, &mark_labels)?,
                ExactLabeledSuffixEcology::condition(&reverse_paths, &mark_labels)?,
            )
        };
        let census = MorphologicalScaleCensus {
            source_lineages: sources.len(),
            delivery_occurrences: passages_standing.len(),
            clause_receivers: clauses.len(),
            lexical_occurrences,
            lexical_recurrent_states: lexical_suffix.ecology().state_count(),
            lexical_material_transitions: lexical_suffix.ecology().material_transition_count(),
            lexical_lineage_occurrences: lexical_suffix.source_incidence_census().1,
            clause_lexical_recurrent_states: clause_lexical_suffix.ecology().state_count(),
            clause_lexical_material_transitions: clause_lexical_suffix
                .ecology()
                .material_transition_count(),
            clause_lexical_lineage_occurrences: clause_lexical_suffix.source_incidence_census().1,
            ordered_region_recurrent_states: ordered_region_suffix.ecology().state_count(),
            ordered_region_material_transitions: ordered_region_suffix
                .ecology()
                .material_transition_count(),
            ordered_region_lineage_occurrences: ordered_region_suffix.source_incidence_census().1,
            conditioned_question_operator_regions: question_operator_prefixes.len(),
            mark_word_occurrences,
            forward_mark_recurrent_states: forward_mark_suffix.ecology().state_count(),
            reverse_mark_recurrent_states: reverse_mark_suffix.ecology().state_count(),
            forward_mark_lineage_occurrences: forward_mark_suffix.source_incidence_census().1,
            reverse_mark_lineage_occurrences: reverse_mark_suffix.source_incidence_census().1,
            returned_route_receptors: route_sections.len(),
            returned_route_relations,
            conditioning_events,
        };
        Ok(Self {
            route_sections,
            passages: passages_standing,
            sources,
            clauses,
            clause_routes,
            lexical_suffix,
            clause_lexical_suffix,
            ordered_region_suffix,
            clause_labels,
            question_operator_prefixes,
            forward_mark_suffix,
            reverse_mark_suffix,
            census,
        })
    }

    pub const fn census(&self) -> &MorphologicalScaleCensus {
        &self.census
    }

    /// The exact ordered question-initial regions whose recurrence and branching were received
    /// during conditioning. Returning these regions makes the learned operator morphology
    /// inspectable without installing a privileged vocabulary in the observer.
    pub fn question_operator_regions(&self) -> Vec<Vec<String>> {
        self.question_operator_prefixes.keys().cloned().collect()
    }

    pub fn charge(
        &self,
        prompt: &str,
    ) -> Result<MorphologicalQuestionCharge, MorphologicalLanguageError> {
        let prompt_tokens = lexical_tokens(prompt);
        if prompt_tokens.is_empty() {
            return Err(MorphologicalLanguageError::EmptyPrompt);
        }
        let prompt_features = surface_features(&prompt_tokens);
        let mut mark_faces = Vec::new();
        for surface in prompt_tokens
            .iter()
            .filter(|token| is_surface_word(token))
            .map(|token| token.to_lowercase())
            .collect::<BTreeSet<_>>()
        {
            let forward = mark_germs(&surface)?;
            let reverse = forward.iter().cloned().rev().collect::<Vec<_>>();
            let (forward_horizon, forward_sources) =
                self.forward_mark_suffix.longest_matched_sources(&forward)?;
            let (reverse_horizon, reverse_sources) =
                self.reverse_mark_suffix.longest_matched_sources(&reverse)?;
            if forward_horizon == 0 && reverse_horizon == 0 {
                continue;
            }
            let intersection = forward_sources
                .intersection(&reverse_sources)
                .cloned()
                .collect::<BTreeSet<_>>();
            let sources = if intersection.is_empty() {
                forward_sources.union(&reverse_sources).cloned().collect()
            } else {
                intersection
            };
            mark_faces.push(MorphologicalMarkFace {
                surface,
                forward_horizon,
                reverse_horizon,
                reached_sources: self.source_names(&sources)?,
            });
        }
        let mut recruited = BTreeMap::<ReceiverFiberIdentity, BTreeSet<String>>::new();
        for feature in &prompt_features {
            if let Some(passages) = self.route_sections.get(feature) {
                for passage in passages {
                    recruited
                        .entry(passage.clone())
                        .or_default()
                        .insert(feature.clone());
                }
            }
        }

        // Punctuation causes outer query regions while recurrent clause incidence causes their
        // inner local faces. These scales coexist. A source-scale query region may therefore own
        // several feature fibers which no single trained clause contains together; successive
        // local phases must discharge those fibers rather than allowing the first clause to erase
        // the whole question. Nothing here installs a word-size tokenizer: marks, lexical suffix
        // states, clauses, deliveries, and source lineages remain independently live charts.
        let mut feature_segments = Vec::<Vec<String>>::new();
        let mut current_segment = Vec::new();
        for token in &prompt_tokens {
            if is_surface_word(token) {
                // A universal surface may be non-discriminating as an isolated route while still
                // being indispensable to an ordered recurrent region. Preserve it in the ordered
                // chart; singleton routing below remains restricted to returned route fibers.
                current_segment.push(token.to_lowercase());
            }
            if matches!(token.as_str(), "." | "!" | "?" | ";" | ":") && !current_segment.is_empty()
            {
                feature_segments.push(std::mem::take(&mut current_segment));
            }
        }
        if !current_segment.is_empty() {
            feature_segments.push(current_segment);
        }
        let operator_features = feature_segments
            .iter()
            .filter_map(|segment| {
                self.question_operator_prefixes
                    .keys()
                    .filter(|prefix| segment.starts_with(prefix))
                    .max_by_key(|prefix| prefix.len())
            })
            .flat_map(|prefix| prefix.iter().cloned())
            .collect::<BTreeSet<_>>();

        let mut grouped = Vec::<QueryRegionGroup>::new();
        for ordered_features in feature_segments {
            let mut intervals = Vec::<QueryInterval>::new();
            for start in 0..ordered_features.len() {
                for end in start + 1..ordered_features.len() {
                    let ordered_surface = ordered_features[start..=end].to_vec();
                    let (horizon, labels) = self
                        .ordered_region_suffix
                        .longest_matched_sources(&token_germs(&ordered_surface)?)?;
                    if usize::try_from(horizon)
                        .map_err(|_| MorphologicalLanguageError::CarrierExtent)?
                        != ordered_surface.len()
                    {
                        break;
                    }
                    let clause_ids = labels
                        .iter()
                        .map(|label| {
                            self.clause_labels
                                .get(label)
                                .copied()
                                .ok_or(MorphologicalLanguageError::MalformedFiber)
                        })
                        .collect::<Result<BTreeSet<_>, _>>()?;
                    if clause_ids.is_empty() {
                        return Err(MorphologicalLanguageError::MalformedFiber);
                    }
                    intervals.push(QueryInterval {
                        start,
                        end: end + 1,
                        features: ordered_surface.iter().cloned().collect(),
                        ordered_surface,
                        clause_ids,
                    });
                }
            }
            let complete_intervals = intervals.clone();
            intervals.retain(|interval| {
                !complete_intervals.iter().any(|other| {
                    (other.start < interval.start || interval.end < other.end)
                        && other.start <= interval.start
                        && interval.end <= other.end
                })
            });

            intervals.retain(|interval| {
                !interval
                    .features
                    .iter()
                    .all(|feature| operator_features.contains(feature))
            });

            let interval_features = intervals
                .iter()
                .flat_map(|interval| interval.features.iter().cloned())
                .collect::<BTreeSet<_>>();
            let singletons = ordered_features
                .iter()
                .enumerate()
                .filter(|(_, feature)| !interval_features.contains(*feature))
                .filter(|(_, feature)| !operator_features.contains(*feature))
                .filter_map(|(at, feature)| {
                    self.clause_routes
                        .get(feature)
                        .map(|clauses| QueryInterval {
                            start: at,
                            end: at + 1,
                            features: BTreeSet::from([feature.clone()]),
                            ordered_surface: vec![feature.clone()],
                            clause_ids: clauses.clone(),
                        })
                })
                .collect::<Vec<_>>();
            intervals.extend(singletons);
            if intervals.is_empty() {
                continue;
            }

            intervals.sort_by_key(|interval| (interval.start, interval.end));
            intervals.dedup_by(|left, right| {
                left.ordered_surface == right.ordered_surface && left.clause_ids == right.clause_ids
            });
            grouped.push(QueryRegionGroup { regions: intervals });
        }
        let obligated_features = grouped
            .iter()
            .flat_map(|group| {
                group
                    .regions
                    .iter()
                    .flat_map(|region| region.features.iter().cloned())
            })
            .collect::<BTreeSet<_>>();
        let contextual_features = prompt_features
            .difference(&obligated_features)
            .cloned()
            .collect();
        let obligations = grouped
            .into_iter()
            .map(|group| {
                let mut reached_passages = BTreeSet::new();
                let mut reached_sources = BTreeSet::new();
                let mut local_regions = Vec::new();
                for region in group.regions {
                    let mut local_passages = BTreeSet::new();
                    let mut local_sources = BTreeSet::new();
                    for clause in &region.clause_ids {
                        let clause = self
                            .clauses
                            .get(*clause)
                            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                        let passage = self
                            .passages
                            .get(&clause.passage)
                            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                        let source = self
                            .sources
                            .get(&clause.source)
                            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                        local_passages.insert(passage.identity.clone());
                        local_sources.insert(source.identity.clone());
                    }
                    reached_passages.extend(local_passages.iter().cloned());
                    reached_sources.extend(local_sources.iter().cloned());
                    local_regions.push(MorphologicalQueryRegion {
                        ordered_surface: region.ordered_surface,
                        features: region.features,
                        reached_passages: local_passages,
                        reached_sources: local_sources,
                        clause_ids: region.clause_ids,
                    });
                }
                let features = local_regions
                    .iter()
                    .flat_map(|region| region.features.iter().cloned())
                    .collect();
                Ok(MorphologicalQueryObligation {
                    features,
                    reached_passages,
                    reached_sources,
                    local_regions,
                })
            })
            .collect::<Result<Vec<_>, MorphologicalLanguageError>>()?;
        let recruited_passages = recruited
            .into_iter()
            .map(|(passage, features)| {
                Ok((
                    self.passages
                        .get(&passage)
                        .ok_or(MorphologicalLanguageError::MalformedFiber)?
                        .identity
                        .clone(),
                    features,
                ))
            })
            .collect::<Result<BTreeMap<_, _>, MorphologicalLanguageError>>()?;
        Ok(MorphologicalQuestionCharge {
            prompt: prompt.to_owned(),
            prompt_tokens,
            recruited_passages,
            mark_faces,
            operator_features,
            contextual_features,
            obligations,
        })
    }

    pub fn generate(
        &self,
        prompt: &str,
        spec: MorphologicalGenerationSpec,
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<MorphologicalLanguageGeneration, MorphologicalLanguageError> {
        let generation = self.generate_currents(prompt, spec)?;
        let outputs = generation
            .outputs
            .into_iter()
            .map(|current| current.into_materialized_return(prompt, action, worker_threads))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(MorphologicalLanguageGeneration {
            charge: generation.charge,
            outputs,
            reflection: generation.reflection,
        })
    }

    pub fn generate_currents(
        &self,
        prompt: &str,
        spec: MorphologicalGenerationSpec,
    ) -> Result<MorphologicalLanguageCurrentGeneration, MorphologicalLanguageError> {
        if spec.maximum_observed_tokens == 0 {
            return Err(MorphologicalLanguageError::EmptyObservationAperture);
        }
        let charge = self.charge(prompt)?;
        let prompt_path = token_germs(&charge.prompt_tokens)?;
        let reflection = ReflectiveCurrentFront {
            clause_lexical: self.clause_lexical_suffix.receive_path(&prompt_path)?,
            passage_lexical: self.lexical_suffix.receive_path(&prompt_path)?,
            last_surface: charge
                .prompt_tokens
                .last()
                .cloned()
                .ok_or(MorphologicalLanguageError::EmptyPrompt)?,
            returned_event_count: 0,
            recurrent_support_uses: Arc::new(BTreeMap::new()),
        };
        let open_faces = charge
            .obligations
            .iter()
            .enumerate()
            .map(|(at, obligation)| {
                (
                    at,
                    (0..obligation.local_regions.len()).collect::<BTreeSet<_>>(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        if open_faces.is_empty() {
            return Ok(MorphologicalLanguageCurrentGeneration {
                charge,
                outputs: vec![MorphologicalGeneratedCurrent {
                    text: String::new(),
                    tokens: Vec::new(),
                    phases: Vec::new(),
                    rest: MorphologicalResponseRest::Obstructed {
                        open_obligations: BTreeSet::new(),
                    },
                    caused_seams: Vec::new(),
                }],
                reflection: MorphologicalReflectionReceipt {
                    shared_conditioned_bodies: 1,
                    whole_body_forks: 0,
                    shared_current_forks: 0,
                    causal_current_states_formed: 1,
                    conduct_equivalent_states_glued: 0,
                    peak_live_current_states: 1,
                    returned_events_carried: 0,
                    terminal_return_materializations: 1,
                },
            });
        }
        let initial = MorphologicalGenerationState::empty(MorphologicalCurrentState {
            reflection,
            active_phase: None,
            open_faces: Arc::new(open_faces),
            rest: None,
        });
        let MorphologicalGenerationState {
            current,
            population,
        } = initial;
        let mut states = BTreeMap::from([(current, population)]);
        let mut causal_current_states_formed = 1usize;
        let mut shared_current_forks = 0usize;
        let mut conduct_equivalent_states_glued = 0usize;
        let mut peak_live_current_states = 1usize;
        let mut returned_events_carried = 0usize;

        loop {
            let mut successors =
                BTreeMap::<MorphologicalCurrentState, MorphologicalCurrentPopulation>::new();
            let mut progressed = false;
            for (current, population) in states {
                let mut state = MorphologicalGenerationState {
                    current,
                    population,
                };
                if state.current.rest.is_some() {
                    if insert_generation_state(&mut successors, state)? {
                        conduct_equivalent_states_glued = conduct_equivalent_states_glued
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                    }
                    continue;
                }
                if state.current.reflection.returned_event_count >= spec.maximum_observed_tokens {
                    self.finish_active_phase(&charge, &mut state, None)?;
                    state.current.rest =
                        Some(MorphologicalResponseRest::ObservationApertureExhausted {
                            open_obligations: open_face_indices(&state.current.open_faces),
                        });
                    if insert_generation_state(&mut successors, state)? {
                        conduct_equivalent_states_glued = conduct_equivalent_states_glued
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                    }
                    continue;
                }

                if let Some(active) = state.current.active_phase.as_ref() {
                    let events = self.event_candidates(&state.current.reflection, active)?;
                    if events.is_empty() {
                        self.finish_active_phase(&charge, &mut state, None)?;
                        if state.current.open_faces.is_empty() {
                            state.current.rest = Some(MorphologicalResponseRest::Obstructed {
                                open_obligations: BTreeSet::new(),
                            })
                        }
                        // An exhausted local frontier is itself a caused obstruction. If another
                        // outer query fiber remains, the next loop may recruit a different local
                        // onset; no global clause-identity ban is installed.
                        progressed = true;
                        if insert_generation_state(&mut successors, state)? {
                            conduct_equivalent_states_glued = conduct_equivalent_states_glued
                                .checked_add(1)
                                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        }
                        continue;
                    }
                    progressed = true;
                    for event in events {
                        let mut successor = state.fork();
                        shared_current_forks = shared_current_forks
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        self.enact_event(
                            &charge,
                            &mut successor,
                            event,
                            MorphologicalTransport::RecurrentLexical,
                        )?;
                        causal_current_states_formed = causal_current_states_formed
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        returned_events_carried = returned_events_carried
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        if insert_generation_state(&mut successors, successor)? {
                            conduct_equivalent_states_glued = conduct_equivalent_states_glued
                                .checked_add(1)
                                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        }
                    }
                } else {
                    let candidates = self.phase_candidates(&charge, &state.current.open_faces)?;
                    if candidates.is_empty() {
                        state.current.rest = Some(MorphologicalResponseRest::Obstructed {
                            open_obligations: open_face_indices(&state.current.open_faces),
                        });
                        if insert_generation_state(&mut successors, state)? {
                            conduct_equivalent_states_glued = conduct_equivalent_states_glued
                                .checked_add(1)
                                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        }
                        continue;
                    }
                    progressed = true;
                    for candidate in candidates {
                        let mut successor = state.fork();
                        shared_current_forks = shared_current_forks
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        self.begin_phase(&charge, &mut successor, candidate)?;
                        causal_current_states_formed = causal_current_states_formed
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        returned_events_carried = returned_events_carried
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        if insert_generation_state(&mut successors, successor)? {
                            conduct_equivalent_states_glued = conduct_equivalent_states_glued
                                .checked_add(1)
                                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        }
                    }
                }
            }
            peak_live_current_states = peak_live_current_states.max(successors.len());
            let at_rest = successors.keys().all(|current| current.rest.is_some());
            states = successors;
            if at_rest || !progressed {
                break;
            }
        }

        let terminal_witnesses = states
            .into_iter()
            .flat_map(|(current, population)| {
                let rest = current
                    .rest
                    .unwrap_or(MorphologicalResponseRest::Obstructed {
                        open_obligations: open_face_indices(&current.open_faces),
                    });
                population.witnesses.into_iter().map(move |witness| {
                    let (emitted, phases) = witness.materialize();
                    (emitted, phases, rest.clone())
                })
            })
            .collect::<Vec<_>>();
        let observed_paths = terminal_witnesses.len();
        let outputs = terminal_witnesses
            .into_iter()
            .map(|(emitted, phases, rest)| MorphologicalGeneratedCurrent {
                text: render_tokens(emitted.iter().map(|token| token.token.as_str())),
                tokens: emitted,
                phases,
                rest,
                caused_seams: Vec::new(),
            })
            .collect::<Vec<_>>();
        Ok(MorphologicalLanguageCurrentGeneration {
            charge,
            outputs,
            reflection: MorphologicalReflectionReceipt {
                shared_conditioned_bodies: 1,
                whole_body_forks: 0,
                shared_current_forks,
                causal_current_states_formed,
                conduct_equivalent_states_glued,
                peak_live_current_states,
                returned_events_carried,
                terminal_return_materializations: observed_paths,
            },
        })
    }

    fn phase_candidates(
        &self,
        charge: &MorphologicalQuestionCharge,
        open: &BTreeMap<usize, BTreeSet<usize>>,
    ) -> Result<Vec<PhaseCandidate>, MorphologicalLanguageError> {
        let prompt_features = charge
            .obligations
            .iter()
            .flat_map(|obligation| obligation.features.iter().cloned())
            .collect::<BTreeSet<_>>();
        let mut candidates = BTreeMap::<usize, PhaseCandidate>::new();
        let Some((&anchor, anchor_regions)) = open.first_key_value() else {
            return Ok(Vec::new());
        };
        let anchor_clauses = anchor_regions
            .iter()
            .filter_map(|region| charge.obligations[anchor].local_regions.get(*region))
            .flat_map(|region| region.clause_ids.iter().copied())
            .collect::<BTreeSet<_>>();
        for clause in &anchor_clauses {
            let standing = &self.clauses[*clause];
            let covered_regions = open
                .iter()
                .filter_map(|(open_at, remaining_regions)| {
                    let regions = remaining_regions
                        .iter()
                        .filter(|region| {
                            charge.obligations[*open_at].local_regions[**region]
                                .clause_ids
                                .contains(clause)
                        })
                        .copied()
                        .collect::<BTreeSet<_>>();
                    (!regions.is_empty()).then_some((*open_at, regions))
                })
                .collect::<BTreeMap<_, _>>();
            if !covered_regions.contains_key(&anchor) {
                continue;
            }
            let evidence = standing
                .features
                .intersection(&prompt_features)
                .cloned()
                .collect::<BTreeSet<_>>();
            let source = self.sources.get(&standing.source);
            let mark_evidence = source
                .map(|source| {
                    charge
                        .mark_faces
                        .iter()
                        .filter(|face| face.reached_sources.contains(&source.identity))
                        .map(|face| face.surface.clone())
                        .collect::<BTreeSet<_>>()
                })
                .unwrap_or_default();
            candidates.insert(
                *clause,
                PhaseCandidate {
                    clause: *clause,
                    covered_regions,
                    evidence,
                    mark_evidence,
                    // The first event is exposed by the returned query-to-clause incidence, not
                    // disguised as a root-vocabulary suffix branch.
                    entry_lexical_horizons: BTreeSet::new(),
                    entry_recurrence_multiplicities: BTreeSet::new(),
                },
            );
        }
        let rows = candidates.into_values().collect::<Vec<_>>();
        let nondominated = rows
            .iter()
            .enumerate()
            .filter_map(|(at, candidate)| {
                let dominated = rows.iter().enumerate().any(|(other_at, other)| {
                    at != other_at
                        && covered_regions_is_subset(
                            &candidate.covered_regions,
                            &other.covered_regions,
                        )
                        && candidate.evidence.is_subset(&other.evidence)
                        && candidate.mark_evidence.is_subset(&other.mark_evidence)
                        && candidate
                            .entry_lexical_horizons
                            .iter()
                            .max()
                            .copied()
                            .unwrap_or(0)
                            <= other
                                .entry_lexical_horizons
                                .iter()
                                .max()
                                .copied()
                                .unwrap_or(0)
                        && (candidate.covered_regions != other.covered_regions
                            || candidate.evidence != other.evidence
                            || candidate.mark_evidence != other.mark_evidence
                            || candidate.entry_lexical_horizons != other.entry_lexical_horizons)
                });
                (!dominated).then_some(candidate.clone())
            })
            .collect::<Vec<_>>();
        Ok(nondominated)
    }

    fn begin_phase(
        &self,
        charge: &MorphologicalQuestionCharge,
        state: &mut MorphologicalGenerationState,
        candidate: PhaseCandidate,
    ) -> Result<(), MorphologicalLanguageError> {
        let clause = self
            .clauses
            .get(candidate.clause)
            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
        for (obligation, regions) in &candidate.covered_regions {
            let Some(remaining) = state.current.open_faces.get(obligation) else {
                return Err(MorphologicalLanguageError::MalformedFiber);
            };
            if *obligation >= charge.obligations.len()
                || !regions.is_subset(remaining)
                || regions.iter().any(|region| {
                    charge.obligations[*obligation]
                        .local_regions
                        .get(*region)
                        .is_none_or(|region| !region.clause_ids.contains(&candidate.clause))
                })
            {
                return Err(MorphologicalLanguageError::MalformedFiber);
            }
        }
        let token = clause
            .tokens
            .first()
            .cloned()
            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
        state.current.active_phase = Some(ActiveResponseCurrent {
            entry_clause: candidate.clause,
            covered_regions: candidate.covered_regions.clone(),
            clauses: BTreeSet::from([candidate.clause]),
            passages: BTreeSet::from([clause.passage.clone()]),
            clause_positions: BTreeMap::from([(candidate.clause, BTreeSet::from([0]))]),
        });
        for witness in &mut state.population.witnesses {
            if witness.active_phase.is_some() {
                return Err(MorphologicalLanguageError::MalformedFiber);
            }
            witness.active_phase = Some(ActiveResponseWitness {
                entry_clause: candidate.clause,
                entry_lexical_horizons: candidate.entry_lexical_horizons.clone(),
                entry_recurrence_multiplicities: candidate.entry_recurrence_multiplicities.clone(),
                emitted_start: state.current.reflection.returned_event_count,
                touched_clauses: BTreeSet::from([candidate.clause]),
                touched_passages: BTreeSet::from([clause.passage.clone()]),
                touched_sources: BTreeSet::from([clause.source.clone()]),
            });
        }
        self.enact_event(
            charge,
            state,
            EventCandidate {
                token,
                support: None,
                clause_horizons: BTreeSet::new(),
                passage_horizons: BTreeSet::new(),
                recurrence_multiplicities: BTreeSet::new(),
                clauses: BTreeSet::from([candidate.clause]),
                passages: BTreeSet::from([clause.passage.clone()]),
                clause_positions: BTreeMap::from([(candidate.clause, BTreeSet::from([0]))]),
                sources: BTreeSet::from([clause.source.clone()]),
                context_sources: BTreeSet::from([clause.source.clone()]),
            },
            MorphologicalTransport::RecruitedPhase,
        )
    }

    fn event_candidates(
        &self,
        reflection: &ReflectiveCurrentFront,
        active: &ActiveResponseCurrent,
    ) -> Result<Vec<EventCandidate>, MorphologicalLanguageError> {
        let mut candidates = BTreeMap::<(String, RecurrentSupportKey), EventCandidate>::new();
        let active_sources = active
            .clauses
            .iter()
            .map(|clause| {
                self.clauses
                    .get(*clause)
                    .map(|standing| standing.source.clone())
                    .ok_or(MorphologicalLanguageError::MalformedFiber)
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let after_local_boundary = matches!(reflection.last_surface.as_str(), ";" | ":");

        // Chronology inside an active caused clause is the primary current. The suffix ecology
        // may open a cross-source seam, but it may not permute arbitrary positions of the same
        // sentence merely because a shorter suffix context also exists.
        for (clause_at, positions) in &active.clause_positions {
            let clause = self
                .clauses
                .get(*clause_at)
                .ok_or(MorphologicalLanguageError::MalformedFiber)?;
            for position in positions {
                let next = position
                    .checked_add(1)
                    .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                let Some(token) = clause.tokens.get(next) else {
                    continue;
                };
                let support_key = RecurrentSupportKey {
                    clause: *clause_at,
                    emitted_at: next,
                };
                if reflection.recurrent_support_uses.contains_key(&support_key) {
                    continue;
                }
                let entry = candidates
                    .entry((token.clone(), support_key.clone()))
                    .or_insert_with(|| EventCandidate {
                        token: token.clone(),
                        support: Some(support_key),
                        clause_horizons: BTreeSet::new(),
                        passage_horizons: BTreeSet::new(),
                        recurrence_multiplicities: BTreeSet::from([1]),
                        clauses: BTreeSet::from([*clause_at]),
                        passages: BTreeSet::from([clause.passage.clone()]),
                        clause_positions: BTreeMap::from([(*clause_at, BTreeSet::from([next]))]),
                        sources: BTreeSet::from([clause.source.clone()]),
                        context_sources: active_sources.clone(),
                    });
                entry.clause_horizons.insert(
                    u32::try_from(next + 1)
                        .map_err(|_| MorphologicalLanguageError::CarrierExtent)?,
                );
            }
        }

        let clause_emanation = self
            .clause_lexical_suffix
            .emanate_current(reflection.clause_lexical)?;
        for branch in clause_emanation.branches() {
            let token = fiber_text(branch.branch().germ().identity())
                .ok_or(MorphologicalLanguageError::MalformedFiber)?;
            if matches!(token.as_str(), "." | "!" | "?") {
                continue;
            }
            for support in branch.branch().supports() {
                let labels = branch
                    .sources_for_support(support)
                    .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                let context_labels = branch
                    .context_sources_for_support(support)
                    .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                let clauses = labels
                    .iter()
                    .map(|label| {
                        self.clause_labels
                            .get(label)
                            .copied()
                            .ok_or(MorphologicalLanguageError::MalformedFiber)
                    })
                    .collect::<Result<BTreeSet<_>, _>>()?;
                let context_clauses = context_labels
                    .iter()
                    .map(|label| {
                        self.clause_labels
                            .get(label)
                            .copied()
                            .ok_or(MorphologicalLanguageError::MalformedFiber)
                    })
                    .collect::<Result<BTreeSet<_>, _>>()?;
                if context_clauses.is_disjoint(&active.clauses) {
                    continue;
                }
                let context_sources = context_clauses
                    .iter()
                    .map(|context_clause| {
                        self.clauses
                            .get(*context_clause)
                            .map(|clause| clause.source.clone())
                            .ok_or(MorphologicalLanguageError::MalformedFiber)
                    })
                    .collect::<Result<BTreeSet<_>, _>>()?;
                for clause_at in clauses {
                    let clause = self
                        .clauses
                        .get(clause_at)
                        .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                    if active.clauses.contains(&clause_at) && !after_local_boundary {
                        continue;
                    }
                    let positions = caused_token_positions(
                        &clause.tokens,
                        &reflection.last_surface,
                        &token,
                        after_local_boundary,
                    );
                    for position in positions {
                        let support_key = RecurrentSupportKey {
                            clause: clause_at,
                            emitted_at: position,
                        };
                        if reflection.recurrent_support_uses.contains_key(&support_key) {
                            continue;
                        }
                        let entry = candidates
                            .entry((token.clone(), support_key.clone()))
                            .or_insert_with(|| EventCandidate {
                                token: token.clone(),
                                support: Some(support_key),
                                clause_horizons: BTreeSet::new(),
                                passage_horizons: BTreeSet::new(),
                                recurrence_multiplicities: BTreeSet::new(),
                                clauses: BTreeSet::from([clause_at]),
                                passages: BTreeSet::from([clause.passage.clone()]),
                                clause_positions: BTreeMap::from([(
                                    clause_at,
                                    BTreeSet::from([position]),
                                )]),
                                sources: BTreeSet::from([clause.source.clone()]),
                                context_sources: context_sources.clone(),
                            });
                        entry.clause_horizons.insert(support.matched_length());
                        entry
                            .recurrence_multiplicities
                            .insert(support.recurrence_multiplicity());
                    }
                }
                // All labels on one exact support may conduct, but each target occurrence remains
                // its own caused chronological position.
            }
        }

        let passage_emanation = self
            .lexical_suffix
            .emanate_current(reflection.passage_lexical)?;
        for branch in passage_emanation.branches() {
            let token = fiber_text(branch.branch().germ().identity())
                .ok_or(MorphologicalLanguageError::MalformedFiber)?;
            if matches!(token.as_str(), "." | "!" | "?") {
                continue;
            }
            for support in branch.branch().supports() {
                let passages = branch
                    .sources_for_support(support)
                    .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                let context_passages = branch
                    .context_sources_for_support(support)
                    .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                if context_passages
                    .iter()
                    .all(|passage| !active.passages.contains(passage))
                {
                    continue;
                }
                if passages
                    .iter()
                    .any(|passage| !self.passages.contains_key(passage))
                {
                    return Err(MorphologicalLanguageError::MalformedFiber);
                }
                let context_sources = context_passages
                    .iter()
                    .map(|context_passage| {
                        self.passages
                            .get(context_passage)
                            .map(|passage| passage.source.clone())
                            .ok_or(MorphologicalLanguageError::MalformedFiber)
                    })
                    .collect::<Result<BTreeSet<_>, _>>()?;
                for passage_fiber in passages {
                    let passage = self
                        .passages
                        .get(passage_fiber)
                        .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                    if active.passages.contains(passage_fiber) && !after_local_boundary {
                        continue;
                    }
                    for clause_at in &passage.clauses {
                        let clause = self
                            .clauses
                            .get(*clause_at)
                            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                        let positions = caused_token_positions(
                            &clause.tokens,
                            &reflection.last_surface,
                            &token,
                            after_local_boundary,
                        );
                        for position in positions {
                            let support_key = RecurrentSupportKey {
                                clause: *clause_at,
                                emitted_at: position,
                            };
                            if reflection.recurrent_support_uses.contains_key(&support_key) {
                                continue;
                            }
                            let entry = candidates
                                .entry((token.clone(), support_key.clone()))
                                .or_insert_with(|| EventCandidate {
                                    token: token.clone(),
                                    support: Some(support_key),
                                    clause_horizons: BTreeSet::new(),
                                    passage_horizons: BTreeSet::new(),
                                    recurrence_multiplicities: BTreeSet::new(),
                                    clauses: BTreeSet::from([*clause_at]),
                                    passages: BTreeSet::from([passage_fiber.clone()]),
                                    clause_positions: BTreeMap::from([(
                                        *clause_at,
                                        BTreeSet::from([position]),
                                    )]),
                                    sources: BTreeSet::from([passage.source.clone()]),
                                    context_sources: context_sources.clone(),
                                });
                            entry.passage_horizons.insert(support.matched_length());
                            entry
                                .recurrence_multiplicities
                                .insert(support.recurrence_multiplicity());
                        }
                    }
                }
            }
        }

        for candidate in candidates.values_mut() {
            for clause_at in candidate.clauses.clone() {
                let clause = self
                    .clauses
                    .get(clause_at)
                    .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                candidate.passages.insert(clause.passage.clone());
                candidate.sources.insert(clause.source.clone());
            }
            for passage_fiber in candidate.passages.clone() {
                let passage = self
                    .passages
                    .get(&passage_fiber)
                    .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                candidate.sources.insert(passage.source.clone());
            }
        }
        candidates.retain(|_, candidate| {
            !candidate.sources.is_empty()
                && (!candidate.clause_horizons.is_empty() || !candidate.passage_horizons.is_empty())
        });
        Ok(candidates.into_values().collect())
    }

    fn enact_event(
        &self,
        charge: &MorphologicalQuestionCharge,
        state: &mut MorphologicalGenerationState,
        event: EventCandidate,
        transport: MorphologicalTransport,
    ) -> Result<(), MorphologicalLanguageError> {
        let generated_at = state.current.reflection.returned_event_count;
        if let Some(support) = event.support.as_ref() {
            let uses = Arc::make_mut(&mut state.current.reflection.recurrent_support_uses);
            let prior = uses.get(support).copied().unwrap_or(0);
            if prior >= 1 {
                return Err(MorphologicalLanguageError::MalformedFiber);
            }
            uses.insert(
                support.clone(),
                prior
                    .checked_add(1)
                    .ok_or(MorphologicalLanguageError::CarrierExtent)?,
            );
        }
        let generated_germ = token_germs(std::slice::from_ref(&event.token))?
            .into_iter()
            .next()
            .ok_or(MorphologicalLanguageError::MalformedFiber)?;

        let forward_germs = mark_germs(&event.token.to_lowercase())?;
        let reverse_germs = forward_germs.iter().cloned().rev().collect::<Vec<_>>();
        let (forward_mark_horizon, _) = self
            .forward_mark_suffix
            .longest_matched_sources(&forward_germs)?;
        let (reverse_mark_horizon, _) = self
            .reverse_mark_suffix
            .longest_matched_sources(&reverse_germs)?;
        let lexical_horizons = event
            .clause_horizons
            .union(&event.passage_horizons)
            .copied()
            .collect::<BTreeSet<_>>();
        let caused_sources = self.source_names(&event.sources)?;
        let recurrent_context_sources = self.source_names(&event.context_sources)?;
        let caused_passages = event
            .passages
            .iter()
            .map(|passage| {
                self.passages
                    .get(passage)
                    .map(|standing| standing.identity.clone())
                    .ok_or(MorphologicalLanguageError::MalformedFiber)
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let supporting_clauses = event
            .clauses
            .iter()
            .map(|clause| {
                self.clauses
                    .get(*clause)
                    .map(|standing| standing.identity.clone())
                    .ok_or(MorphologicalLanguageError::MalformedFiber)
            })
            .collect::<Result<BTreeSet<_>, _>>()?;
        let returned_event_count = generated_at
            .checked_add(1)
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        let returned_token = MorphologicalGeneratedToken {
            token: event.token.clone(),
            transport,
            lexical_horizons,
            forward_mark_horizon,
            reverse_mark_horizon,
            recurrent_sources: caused_sources.clone(),
            recurrent_context_sources,
            caused_sources,
            caused_passages,
            supporting_clauses,
            returned_event_count,
        };
        for witness in &mut state.population.witnesses {
            witness.carry_event(returned_token.clone())?;
        }
        state.current.reflection.clause_lexical = self
            .clause_lexical_suffix
            .carry(state.current.reflection.clause_lexical, &generated_germ)?;
        state.current.reflection.passage_lexical = self
            .lexical_suffix
            .carry(state.current.reflection.passage_lexical, &generated_germ)?;
        state.current.reflection.last_surface = event.token.clone();
        state.current.reflection.returned_event_count = returned_event_count;
        let active = state
            .current
            .active_phase
            .as_mut()
            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
        active.clauses = event.clauses.clone();
        active.passages = event.passages.clone();
        active.clause_positions = event.clause_positions.clone();
        for witness in &mut state.population.witnesses {
            let witness_active = witness
                .active_phase
                .as_mut()
                .ok_or(MorphologicalLanguageError::MalformedFiber)?;
            witness_active
                .touched_clauses
                .extend(event.clauses.iter().copied());
            witness_active
                .touched_passages
                .extend(event.passages.iter().cloned());
            witness_active
                .touched_sources
                .extend(event.sources.iter().cloned());
        }
        // A recurrent seam can bring a still-open query region into the same phase after onset.
        // The region is not discharged yet: only a later returned sentence boundary can complete
        // this caused path.
        for (obligation, regions) in state.current.open_faces.iter() {
            let newly_reached = regions
                .iter()
                .filter(|region| {
                    !event.clauses.contains(&active.entry_clause)
                        && !charge.obligations[*obligation].local_regions[**region]
                            .clause_ids
                            .is_disjoint(&event.clauses)
                })
                .copied()
                .collect::<BTreeSet<_>>();
            if !newly_reached.is_empty() {
                active
                    .covered_regions
                    .entry(*obligation)
                    .or_default()
                    .extend(newly_reached);
            }
        }

        if matches!(event.token.as_str(), "." | "!" | "?") {
            self.finish_active_phase(charge, state, Some(MorphologicalBoundary::Sentence))?;
        }
        Ok(())
    }

    fn finish_active_phase(
        &self,
        charge: &MorphologicalQuestionCharge,
        state: &mut MorphologicalGenerationState,
        boundary: Option<MorphologicalBoundary>,
    ) -> Result<(), MorphologicalLanguageError> {
        let Some(active) = state.current.active_phase.take() else {
            return Ok(());
        };
        let discharged_regions = if boundary == Some(MorphologicalBoundary::Sentence) {
            active
                .covered_regions
                .iter()
                .filter_map(|(obligation, regions)| {
                    let returned = state
                        .current
                        .open_faces
                        .get(obligation)
                        .map(|open| regions.intersection(open).copied().collect::<BTreeSet<_>>())
                        .unwrap_or_default();
                    (!returned.is_empty()).then_some((*obligation, returned))
                })
                .collect::<BTreeMap<_, _>>()
        } else {
            BTreeMap::new()
        };
        let discharged_features = discharged_regions
            .iter()
            .map(|(obligation, regions)| {
                let features = regions
                    .iter()
                    .flat_map(|region| {
                        charge.obligations[*obligation].local_regions[*region]
                            .features
                            .iter()
                            .cloned()
                    })
                    .collect();
                (*obligation, features)
            })
            .collect::<BTreeMap<_, _>>();
        {
            let open_faces = Arc::make_mut(&mut state.current.open_faces);
            for (obligation, discharged) in &discharged_regions {
                let remove_obligation = {
                    let remaining = open_faces
                        .get_mut(obligation)
                        .ok_or(MorphologicalLanguageError::MalformedFiber)?;
                    for region in discharged {
                        remaining.remove(region);
                    }
                    remaining.is_empty()
                };
                if remove_obligation {
                    open_faces.remove(obligation);
                }
            }
        }

        let discharged_obligations = discharged_regions.keys().copied().collect::<BTreeSet<_>>();
        for witness in &mut state.population.witnesses {
            let witness_active = witness
                .active_phase
                .take()
                .ok_or(MorphologicalLanguageError::MalformedFiber)?;
            if witness_active.entry_clause != active.entry_clause {
                return Err(MorphologicalLanguageError::MalformedFiber);
            }
            let entry_clause = self
                .clauses
                .get(witness_active.entry_clause)
                .ok_or(MorphologicalLanguageError::MalformedFiber)?
                .identity
                .clone();
            let clauses = witness_active
                .touched_clauses
                .iter()
                .map(|clause| {
                    self.clauses
                        .get(*clause)
                        .map(|standing| standing.identity.clone())
                        .ok_or(MorphologicalLanguageError::MalformedFiber)
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            let passages = witness_active
                .touched_passages
                .iter()
                .map(|passage| {
                    self.passages
                        .get(passage)
                        .map(|standing| standing.identity.clone())
                        .ok_or(MorphologicalLanguageError::MalformedFiber)
                })
                .collect::<Result<BTreeSet<_>, _>>()?;
            let sources = self.source_names(&witness_active.touched_sources)?;
            witness.carry_phase(MorphologicalResponsePhase {
                entry_clause,
                clauses,
                sources,
                passages,
                boundary,
                discharged_obligations: discharged_obligations.clone(),
                discharged_regions: discharged_regions.clone(),
                discharged_features: discharged_features.clone(),
                entry_lexical_horizons: witness_active.entry_lexical_horizons,
                entry_recurrence_multiplicities: witness_active.entry_recurrence_multiplicities,
                emitted_start: witness_active.emitted_start,
                emitted_end: state.current.reflection.returned_event_count,
            })?;
        }
        if boundary == Some(MorphologicalBoundary::Sentence) && state.current.open_faces.is_empty()
        {
            state.current.rest = Some(MorphologicalResponseRest::Closed);
        }
        Ok(())
    }

    fn source_names(
        &self,
        sources: &BTreeSet<SuffixSourceLabel>,
    ) -> Result<BTreeSet<String>, MorphologicalLanguageError> {
        sources
            .iter()
            .map(|source| {
                self.sources
                    .get(source)
                    .map(|standing| standing.identity.clone())
                    .ok_or(MorphologicalLanguageError::MalformedFiber)
            })
            .collect()
    }
}
