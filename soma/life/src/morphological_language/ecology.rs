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

/// One successor opened by one cell of the generation front, carrying what its own expansion
/// caused.
///
/// `hardware_cover::expand_front` returns a flat vector of successors in the front's own order.
/// It has no per-lane slot, deliberately: the covering that stood here before kept its tallies per
/// lane and merged them afterwards, which is exactly the shape in which a realization coordinate
/// gets into a returned quantity. Anything the round must total therefore rides on the successor
/// and is totalled once, in the front's order, by the caller.
struct ExpandedCurrent {
    state: MorphologicalGenerationState,
    /// This successor was formed by forking its cell and enacting one event or one phase onset —
    /// a shared-current fork, a formed causal state and a carried returned event, which are the
    /// same three occurrences counted three times because the receipt names them separately.
    forked: bool,
    /// The cell that opened this successor moved. Every path opens at least one successor, so the
    /// round's disjunction over successors is the round's disjunction over cells.
    cell_progressed: bool,
}

/// **How much of the receiver's own active family a candidate's context must carry.**
///
/// The recruitment law is `I(R) = ⋃_K ⋂_{f∈K} I(f)` — the receiver's incidence is the union over
/// covers of the **intersection** over the faces in each block. `relational_language` implements it
/// at `clause_region_incidence`, folding `candidates.intersection(carriers)` across a region's
/// faces so a clause is recruited only when it carries every one; the mark ecology in this same
/// file implements it at `charge`, intersecting the forward and reverse source families and falling
/// back to the union only when that intersection is empty.
///
/// **`event_candidates` implemented neither.** It admitted a candidate whose context shared ONE
/// active clause or ONE active passage, which is the singleton cover and nothing else — broad
/// union-based lexical recruitment, the shape `CLAUDE.md` §5 convicts by name. Every token match
/// opened a branch, so the machine coupled the whole corpus into every response instead of
/// resonating with the part of it that carries the receiver's face together.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ContextCover {
    /// The maximal block: the candidate's context carries the receiver's **complete** active
    /// family. This is `⋂_{f∈K} I(f)` with `K` the whole family.
    Complete,
    /// The singleton cover: the candidate's context touches the family anywhere. Reached only when
    /// `Complete` recruited nothing, so a single-face alternative stays lineage rather than being
    /// declared false — the same fallback the mark intersection already takes.
    Touching,
}

/// The front that arrives at one chronology: co-present cells, glued by conduct.
type ArrivedFront = BTreeMap<MorphologicalCurrentState, MorphologicalCurrentPopulation>;

/// Every front still to arrive, ordered by the chronology it arrives at. A dilated passage lands
/// in a later entry and is retained there until the loop reaches it.
type ChronologyFronts = BTreeMap<u64, ArrivedFront>;

/// **One cell's expansion, carrying the demand it presented at its own site.**
///
/// `holonic_engine::receiver_current` is the body's transport law and generation never called it.
/// Its arithmetic is
///
/// ```text
///   co_present_branch_population = branch_population × |active outgoing passages|
///   service_rounds               = ceil(co_present_branch_population / site_capacity)
///   passage_delay                = characteristic_delay + (service_rounds − 1)
/// ```
///
/// Both factors of the demand are known exactly at the moment a cell finishes expanding and
/// nowhere earlier: the branch population is the cell's witness count, and the number of active
/// outgoing passages is how many successors the expansion actually opened. So the cell reports its
/// own demand rather than the front guessing it.
struct ExpandedCell {
    /// The clause-lexical suffix state the cell sat at — its **site**.
    site: u32,
    /// `branch_population × |active outgoing passages|`.
    co_present: u64,
    opened: Vec<ExpandedCurrent>,
}

/// One cell after its immutable ecological question has been asked but before any alternative
/// current forks. A deposited conduct deed is therefore able to attach the complete candidate
/// front here without observing or filtering already-materialized outputs.
struct PreparedCell {
    site: u32,
    branch_population: u64,
    expansion: PreparedExpansion,
}

enum PreparedExpansion {
    Carried(MorphologicalGenerationState),
    Progressed(MorphologicalGenerationState),
    Phases {
        state: MorphologicalGenerationState,
        candidates: Vec<PhaseCandidate>,
    },
    Events {
        state: MorphologicalGenerationState,
        candidates: Vec<EventCandidate>,
    },
}

enum GenerationConduct<'a> {
    Complete,
    Deposited(DepositedGenerationRuntime<'a>),
}

struct DepositedGenerationRuntime<'a> {
    morphology: &'a MorphologicalConductMorphology,
    executor: &'a mut CudaMorphologicalConductExecutor,
    dispositions: LocalSequence<MorphologicalConductTransitionDisposition>,
    obstructions: LocalSequence<MorphologicalConductObstruction>,
    apparatus: LocalSequence<MorphologicalConductCudaReceipt>,
    next_candidate: u64,
}

impl ExpandedCurrent {
    /// The cell was carried to the next front unchanged or brought to rest: no fork, no movement.
    const fn carried(state: MorphologicalGenerationState) -> Self {
        Self {
            state,
            forked: false,
            cell_progressed: false,
        }
    }

    /// The cell's local frontier was exhausted, which is itself a caused obstruction and therefore
    /// movement, but no fork was opened.
    const fn progressed(state: MorphologicalGenerationState) -> Self {
        Self {
            state,
            forked: false,
            cell_progressed: true,
        }
    }

    /// The cell opened this successor at its junction.
    const fn forked(state: MorphologicalGenerationState) -> Self {
        Self {
            state,
            forked: true,
            cell_progressed: true,
        }
    }
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

    /// Found the query-independent recurrent-contact atlas from the two lexical receiver charts.
    /// Every suffix occurrence is resolved through the ecology's own standing to one exterior
    /// source; context co-presence is retained but only the exact target relation can deposit
    /// conduct.
    pub fn conduct_atlas(&self) -> Result<MorphologicalConductAtlas, MorphologicalLanguageError> {
        let capacity = self
            .clause_lexical_suffix
            .ecology()
            .material_transition_count()
            .checked_add(self.lexical_suffix.ecology().material_transition_count())
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        let mut rows = LocalSequence::with_capacity(capacity);
        for edge in self.clause_lexical_suffix.material_edges()? {
            rows.push(MorphologicalConductSupportRow::from_material_edge(
                MorphologicalConductChart::ClauseLexical,
                &edge,
                |occurrence| self.clause_occurrence_source(occurrence),
            )?);
        }
        for edge in self.lexical_suffix.material_edges()? {
            rows.push(MorphologicalConductSupportRow::from_material_edge(
                MorphologicalConductChart::PassageLexical,
                &edge,
                |occurrence| self.passage_occurrence_source(occurrence),
            )?);
        }
        // **Canonical order is put here, once, rather than assumed of the walk.**
        //
        // `material_edges` walks receiver states ascending and their transitions in storage order,
        // which agrees with address order on a small chart and need not on a large one. The atlas
        // refuses a non-canonical sequence, so leaving it to the walk makes a correct atlas a
        // property of how a suffix ecology happens to store transitions. Sorting is not a
        // rearrangement of the material: the address order is the material's own, and the card
        // later searches on exactly it (`MorphologicalConductEdgeAddress::key_words`). Duplicates
        // are still refused by `found`, which is the check that matters.
        rows.sort_by(|left, right| left.edge().cmp(right.edge()));
        Ok(MorphologicalConductAtlas::found(rows)?)
    }

    fn clause_occurrence_source(
        &self,
        occurrence: &ReceiverFiberIdentity,
    ) -> Result<MorphologicalConductSourceAddress, MorphologicalConductRefusal> {
        let clause = self
            .clause_labels
            .get(occurrence)
            .and_then(|at| self.clauses.get(*at))
            .ok_or(MorphologicalConductRefusal::UnknownOccurrenceSource)?;
        self.conduct_source_address(&clause.source)
    }

    fn passage_occurrence_source(
        &self,
        occurrence: &ReceiverFiberIdentity,
    ) -> Result<MorphologicalConductSourceAddress, MorphologicalConductRefusal> {
        let passage = self
            .passages
            .get(occurrence)
            .ok_or(MorphologicalConductRefusal::UnknownOccurrenceSource)?;
        self.conduct_source_address(&passage.source)
    }

    fn conduct_source_address(
        &self,
        source: &ReceiverFiberIdentity,
    ) -> Result<MorphologicalConductSourceAddress, MorphologicalConductRefusal> {
        let standing = self
            .sources
            .get(source)
            .ok_or(MorphologicalConductRefusal::UnknownOccurrenceSource)?;
        MorphologicalConductSourceAddress::new(
            source.clone(),
            standing.identity.clone(),
            standing.receiver,
        )
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
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        self.generate_with_executor(prompt, spec, action, &mut host)
    }

    /// Generate through one caller-retained physical executor. Terminal current selection remains
    /// exact host suffix work, but every returned path is materialized on the supplied executor, so
    /// one mounted card crosses every Swing event on this generation path. Selecting a card at the
    /// outer language boundary cannot silently construct a private host executor here.
    pub fn generate_with_executor(
        &self,
        prompt: &str,
        spec: MorphologicalGenerationSpec,
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<MorphologicalLanguageGeneration, MorphologicalLanguageError> {
        let generation = self.generate_currents(prompt, spec)?;
        let mut outputs = Vec::with_capacity(generation.outputs.len());
        for current in generation.outputs {
            outputs.push(current.into_materialized_return_with_executor(prompt, action, executor)?);
        }
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
        self.generate_currents_over(
            prompt,
            spec,
            &holonic_engine::hardware_cover::HardwareCover::host_only(),
        )
    }

    /// Generate over a **declared** cover rather than one this function asked the host for.
    ///
    /// `hardware_cover::HardwareCover::of_charts` exists for exactly this reason, and says so:
    /// *"the determinism controls need to vary the cover without a card present, and a construction
    /// that can only be built from real hardware cannot be graded on a machine that has none."*
    /// A lane is a realization coordinate; that it may not move a reading is a claim, and a claim
    /// that cannot be varied cannot be checked. This is the parameter that varies it.
    pub fn generate_currents_over(
        &self,
        prompt: &str,
        spec: MorphologicalGenerationSpec,
        cover: &holonic_engine::hardware_cover::HardwareCover,
    ) -> Result<MorphologicalLanguageCurrentGeneration, MorphologicalLanguageError> {
        Ok(self
            .generate_currents_over_inner(prompt, spec, cover, GenerationConduct::Complete)?
            .generation)
    }

    pub(in crate::morphological_language) fn generate_currents_over_conducted(
        &self,
        prompt: &str,
        spec: MorphologicalGenerationSpec,
        cover: &holonic_engine::hardware_cover::HardwareCover,
        morphology: &MorphologicalConductMorphology,
        executor: &mut CudaMorphologicalConductExecutor,
    ) -> Result<MorphologicalConductedGeneration, MorphologicalLanguageError> {
        self.generate_currents_over_inner(
            prompt,
            spec,
            cover,
            GenerationConduct::Deposited(DepositedGenerationRuntime {
                morphology,
                executor,
                dispositions: LocalSequence::new(),
                obstructions: LocalSequence::new(),
                apparatus: LocalSequence::new(),
                next_candidate: 0,
            }),
        )
    }

    fn generate_currents_over_inner(
        &self,
        prompt: &str,
        spec: MorphologicalGenerationSpec,
        cover: &holonic_engine::hardware_cover::HardwareCover,
        mut conduct: GenerationConduct<'_>,
    ) -> Result<MorphologicalConductedGeneration, MorphologicalLanguageError> {
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
            return Ok(MorphologicalConductedGeneration {
                generation: MorphologicalLanguageCurrentGeneration {
                    charge,
                    outputs: vec![MorphologicalGeneratedCurrent {
                        text: String::new(),
                        tokens: Vec::new(),
                        phases: Vec::new(),
                        rest: MorphologicalResponseRest::Obstructed {
                            open_obligations: BTreeSet::new(),
                        },
                        caused_seams: Vec::new(),
                        support_conduct: MorphologicalSupportConduct::Open,
                        supporting_sources: 0,
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
                        dilated_passages: 0,
                        deepest_dilation: 0,
                        deepest_chronology: 0,
                    },
                },
                semantic: MorphologicalConductGenerationReceipt {
                    schema: "soma-life.morphological-conduct-generation.v2".to_owned(),
                    evaluated_transitions: 0,
                    attached_transitions: 0,
                    withheld_transitions: 0,
                    declared_minimum_distinct_sources: 0,
                    plurality_declared_by: "the charge opened no query face, so no transition was \
                                            evaluated"
                        .to_owned(),
                    dispositions: LocalSequence::new(),
                    obstructions: LocalSequence::new(),
                },
                apparatus: LocalSequence::new(),
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
        // **The front is indexed by arrival chronology, because a passage has a delay.**
        //
        // Every successor used to be co-present at the next step, which is the assertion that every
        // passage costs the same regardless of how much demand met how much support. The body owns
        // a transport law that says otherwise — `holonic_engine::receiver_current` — and generation
        // was the organ that never called it. Here the front at a chronology is what has actually
        // arrived by then; a dilated passage lands later and is **retained** in `pending` until it
        // does. Nothing is discarded, so this is not an aperture: the same population returns, and
        // what changes is which cells are co-present when.
        let mut pending =
            ChronologyFronts::from([(0, ArrivedFront::from([(current, population)]))]);
        let mut rested = ArrivedFront::new();
        let mut causal_current_states_formed = 1usize;
        let mut shared_current_forks = 0usize;
        let mut conduct_equivalent_states_glued = 0usize;
        let mut peak_live_current_states = 1usize;
        let mut returned_events_carried = 0usize;
        let mut dilated_passages = 0usize;
        let mut deepest_dilation = 0u64;
        let mut deepest_chronology = 0u64;

        while let Some((chronology, arrived)) = pending.pop_first() {
            deepest_chronology = deepest_chronology.max(chronology);
            // **The front is expanded through the one covering law, and the law is not restated
            // here.**
            //
            // `states` is a front of co-present cells. Every cell's successors depend on that cell
            // and on `&self`, which is immutable here — `phase_candidates`, `begin_phase`,
            // `event_candidates`, `enact_event` and `finish_active_phase` all take `&self` — so one
            // round is a JUNCTION and not an arc: what leaves it is co-present. Chronology inside a
            // single branch is untouched.
            //
            // The law is `holonic_engine::hardware_cover::expand_front`, the same organ the causal
            // leader conducts through. What stood here instead was a covering per organ — a direct
            // `std::thread::available_parallelism()` call, a round-robin `at % lanes` **by count**,
            // a per-lane `BTreeMap` and a merge in lane order. That is the cabinet failure one
            // level down, and covering by count is the law `sweep_covered`'s own comment names as
            // wrong: *a surface with a million occurrences and one with two are not one unit each.*
            //
            // **And it was not lane-invariant.** `ReflectiveCurrentFront::conduct_key` deliberately
            // excludes `recurrent_support_uses` — the founded terrain — so two currents that
            // founded different sections GLUE, and `insert_generation_state` keeps the terrain of
            // whichever arrived first while appending the other's witnesses. Under the round-robin
            // partition "first" was a lane coordinate, and since that terrain gates
            // `event_candidates`, the next round's candidate population moved with it: measured on
            // the corpus of `tests::a_declared_lane_count_cannot_move_the_generated_reading`,
            // **1,862 returned branches at 1 and 8 lanes, 1,806 at 2, 1,843 at 3.** Gluing in the
            // front's own order is the serial order at every lane count, which is what
            // `expand_front` reassembles into.
            //
            // **What this repair does NOT fix, and it is a live defect one level down:** which
            // branch's terrain survives a glue is still decided by arrival order rather than by a
            // law. Front order is canonical, so the reading is now reproducible; the object it
            // reproduces still carries a traversal coordinate in a retained field, which is §0's
            // fourth lesson — a receiver-visible coordinate promoted into standing. Deciding it
            // lawfully (union the founded terrain, or return the plural fiber) changes what
            // generation returns and is not this repair's to take.
            let front: Vec<(MorphologicalCurrentState, MorphologicalCurrentPopulation)> =
                arrived.into_iter().collect();
            let prepared = holonic_engine::hardware_cover::expand_front(
                front,
                cover,
                // **The extent of a generation cell is its witness population.**
                //
                // Every successor a cell opens is `state.fork()`, which clones every witness, and
                // `begin_phase` / `enact_event` / `finish_active_phase` then rewrite every witness
                // of the fork in place. So a cell carrying sixty-one witnesses does sixty-one times
                // the per-successor work of a cell carrying one, and covering by count weighs the
                // two the same. Measured on the corpus of
                // `tests::a_declared_lane_count_cannot_move_the_generated_reading`, one front of
                // 138 cells carried extents from 1 to 61 — the by-extent cover and the by-count
                // cover are not the same cover on this material.
                //
                // The other factor is the candidate population, and it is **not available before
                // the expansion**: computing it *is* the expansion, so reading it into the extent
                // would double the work the extent exists to place. It is therefore not in the
                // measure, and no proxy stands in for it.
                |(_, population): &(MorphologicalCurrentState, MorphologicalCurrentPopulation)| {
                    population.witnesses.len() as u64
                },
                |(current, population)| {
                    let branch_population = population.witnesses.len() as u64;
                    let site = current.reflection.clause_lexical.state();
                    let expansion = self.prepare_current(&charge, spec, current, population)?;
                    Ok::<_, MorphologicalLanguageError>(vec![PreparedCell {
                        site,
                        branch_population,
                        expansion,
                    }])
                },
            )?;

            let expanded = match &mut conduct {
                GenerationConduct::Complete => {
                    let mut expanded = Vec::with_capacity(prepared.len());
                    for cell in prepared {
                        let opened = self.materialize_complete(&charge, cell.expansion)?;
                        expanded.push(ExpandedCell {
                            site: cell.site,
                            co_present: cell.branch_population.saturating_mul(opened.len() as u64),
                            opened,
                        });
                    }
                    expanded
                }
                GenerationConduct::Deposited(runtime) => {
                    self.materialize_deposited_front(&charge, chronology, prepared, runtime)?
                }
            };

            for cell in expanded {
                let dilation = self.service_dilation(cell.site, cell.co_present)?;
                if dilation > 0 {
                    dilated_passages = dilated_passages
                        .checked_add(1)
                        .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                    deepest_dilation = deepest_dilation.max(dilation);
                }
                for opened in cell.opened {
                    // **A successor that came to rest, or whose cell could not move, retires.**
                    //
                    // The loop this replaces re-expanded such a cell every round until the whole
                    // front stopped, and broke on `at_rest || !progressed` over ALL of it. Retiring
                    // per successor reaches the same terminal population — a cell that cannot
                    // progress returns itself unchanged, so re-expanding it was a no-op — and it is
                    // what makes a chronology-indexed front terminate: every successor either
                    // consumes aperture or leaves.
                    if opened.state.current.rest.is_some() || !opened.cell_progressed {
                        insert_generation_state(&mut rested, opened.state)?;
                        continue;
                    }
                    if opened.forked {
                        shared_current_forks = shared_current_forks
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        causal_current_states_formed = causal_current_states_formed
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        returned_events_carried = returned_events_carried
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                    }
                    // **Where the transport law decides conduct.** An uncongested successor arrives at
                    // the next chronology; a congested one arrives `service_rounds − 1` later and is
                    // retained meanwhile as deferred testimony rather than expanded early. Nothing is
                    // dropped and nothing is chosen: the dilation is `ceil(demand / support)` over the
                    // material, so a continuation the corpus attests widely rides at once and one it
                    // barely attests waits for its turn.
                    let arrival = chronology
                        .checked_add(1)
                        .and_then(|next| next.checked_add(dilation))
                        .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                    if insert_generation_state(pending.entry(arrival).or_default(), opened.state)? {
                        conduct_equivalent_states_glued = conduct_equivalent_states_glued
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                    }
                }
            }
            peak_live_current_states = peak_live_current_states
                .max(pending.values().map(ArrivedFront::len).sum::<usize>() + rested.len());
        }

        let terminal_witnesses = rested
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
            .map(|(emitted, phases, rest)| {
                // The resonance reading, taken by the one law and nowhere restated.
                let (support_conduct, supporting_sources) =
                    MorphologicalSupportConduct::of(&emitted);
                MorphologicalGeneratedCurrent {
                    text: render_tokens(emitted.iter().map(|token| token.token.as_str())),
                    tokens: emitted,
                    phases,
                    rest,
                    caused_seams: Vec::new(),
                    support_conduct,
                    supporting_sources,
                }
            })
            .collect::<Vec<_>>();
        let (semantic, apparatus) = match conduct {
            GenerationConduct::Complete => (
                MorphologicalConductGenerationReceipt {
                    schema: "soma-life.morphological-conduct-generation.v2".to_owned(),
                    evaluated_transitions: 0,
                    attached_transitions: 0,
                    withheld_transitions: 0,
                    declared_minimum_distinct_sources: 0,
                    plurality_declared_by: "no conduct morphology is in scope: this is the \
                                            complete continuation fiber, which is a real object \
                                            and is not a return"
                        .to_owned(),
                    dispositions: LocalSequence::new(),
                    obstructions: LocalSequence::new(),
                },
                LocalSequence::new(),
            ),
            GenerationConduct::Deposited(runtime) => {
                let attached_transitions = runtime
                    .dispositions
                    .iter()
                    .filter(|disposition| !disposition.attached_deposits.is_empty())
                    .count();
                let evaluated_transitions = runtime.dispositions.len();
                (
                    MorphologicalConductGenerationReceipt {
                        schema: "soma-life.morphological-conduct-generation.v2".to_owned(),
                        evaluated_transitions,
                        attached_transitions,
                        withheld_transitions: evaluated_transitions - attached_transitions,
                        declared_minimum_distinct_sources: runtime
                            .morphology
                            .plurality()
                            .minimum_distinct_sources(),
                        plurality_declared_by: runtime
                            .morphology
                            .plurality()
                            .declared_by()
                            .to_owned(),
                        dispositions: runtime.dispositions,
                        obstructions: runtime.obstructions,
                    },
                    runtime.apparatus,
                )
            }
        };
        Ok(MorphologicalConductedGeneration {
            generation: MorphologicalLanguageCurrentGeneration {
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
                    dilated_passages,
                    deepest_dilation,
                    deepest_chronology,
                },
            },
            semantic,
            apparatus,
        })
    }

    /// **One cell of the generation front, expanded at its junction.**
    ///
    /// This is the whole of what the material supplies to
    /// `hardware_cover::expand_front`: what one co-present cell branches into. The cover, the
    /// sectioning by extent and the canonical reassembly are the law's and are not restated here.
    ///
    /// The complete predecessor returns at least one successor per path. A conducting owner may
    /// instead retain every unattached event as an open disposition while emitting no successor;
    /// that happens only after the resident attachment deed, never as a host-side post-filter.
    /// **The transport law's service dilation for one cell, read off the material.**
    ///
    /// `holonic_engine::receiver_current` states it:
    /// `service_rounds = ceil(co_present_branch_population / site_capacity)`, and a passage costs
    /// `characteristic_delay + (service_rounds − 1)`. This returns the second term.
    ///
    /// **The capacity is the corpus's own support for the site** — how many distinct sources attest
    /// the cell's clause-lexical context — which is exactly how `relational_language` derives a
    /// clause site's capacity, from `|morphology_sites|`. Nothing here authors a level: a widely
    /// attested context serves its whole demand in one round; a barely attested one takes as many
    /// rounds as its demand exceeds its attestation. That is the RIDE/FOUND asymmetry as a delay —
    /// terrain that has already paid carries a branch at once, and terrain that has not makes it
    /// wait.
    ///
    /// **The characteristic delay is one token, and that is material rather than pinned:** an
    /// uncongested generation passage emits exactly one event, so its chronology is one event. The
    /// caller adds it.
    fn service_dilation(
        &self,
        site: u32,
        co_present: u64,
    ) -> Result<u64, MorphologicalLanguageError> {
        let capacity = self
            .clause_lexical_suffix
            .state_sources(site)
            .map_or(0, |sources| sources.len() as u64);
        if capacity == 0 {
            return Err(MorphologicalLanguageError::UnattestedGenerationSite(site));
        }
        Ok(co_present.div_ceil(capacity).saturating_sub(1))
    }

    fn prepare_current(
        &self,
        charge: &MorphologicalQuestionCharge,
        spec: MorphologicalGenerationSpec,
        current: MorphologicalCurrentState,
        population: MorphologicalCurrentPopulation,
    ) -> Result<PreparedExpansion, MorphologicalLanguageError> {
        let mut state = MorphologicalGenerationState {
            current,
            population,
        };
        if state.current.rest.is_some() {
            return Ok(PreparedExpansion::Carried(state));
        }
        if state.current.reflection.returned_event_count >= spec.maximum_observed_tokens {
            self.finish_active_phase(charge, &mut state, None)?;
            state.current.rest = Some(MorphologicalResponseRest::ObservationApertureExhausted {
                open_obligations: open_face_indices(&state.current.open_faces),
            });
            return Ok(PreparedExpansion::Carried(state));
        }

        if let Some(active) = state.current.active_phase.as_ref() {
            let events = self.event_candidates(&state.current.reflection, active)?;
            if events.is_empty() {
                self.finish_active_phase(charge, &mut state, None)?;
                if state.current.open_faces.is_empty() {
                    state.current.rest = Some(MorphologicalResponseRest::Obstructed {
                        open_obligations: BTreeSet::new(),
                    })
                }
                // An exhausted local frontier is itself a caused obstruction. If another
                // outer query fiber remains, the next loop may recruit a different local
                // onset; no global clause-identity ban is installed.
                return Ok(PreparedExpansion::Progressed(state));
            }
            Ok(PreparedExpansion::Events {
                state,
                candidates: events,
            })
        } else {
            let candidates = self.phase_candidates(charge, &state.current.open_faces)?;
            if candidates.is_empty() {
                state.current.rest = Some(MorphologicalResponseRest::Obstructed {
                    open_obligations: open_face_indices(&state.current.open_faces),
                });
                return Ok(PreparedExpansion::Carried(state));
            }
            Ok(PreparedExpansion::Phases { state, candidates })
        }
    }

    fn materialize_complete(
        &self,
        charge: &MorphologicalQuestionCharge,
        prepared: PreparedExpansion,
    ) -> Result<Vec<ExpandedCurrent>, MorphologicalLanguageError> {
        match prepared {
            PreparedExpansion::Carried(state) => Ok(vec![ExpandedCurrent::carried(state)]),
            PreparedExpansion::Progressed(state) => Ok(vec![ExpandedCurrent::progressed(state)]),
            PreparedExpansion::Phases { state, candidates } => {
                let mut opened = Vec::with_capacity(candidates.len());
                for candidate in candidates {
                    let mut successor = state.fork();
                    self.begin_phase(charge, &mut successor, candidate)?;
                    opened.push(ExpandedCurrent::forked(successor));
                }
                Ok(opened)
            }
            PreparedExpansion::Events { state, candidates } => {
                let mut opened = Vec::with_capacity(candidates.len());
                for event in candidates {
                    let mut successor = state.fork();
                    self.enact_event(
                        charge,
                        &mut successor,
                        event,
                        MorphologicalTransport::RecurrentLexical,
                    )?;
                    opened.push(ExpandedCurrent::forked(successor));
                }
                Ok(opened)
            }
        }
    }

    fn materialize_deposited_front(
        &self,
        charge: &MorphologicalQuestionCharge,
        chronology: u64,
        prepared: Vec<PreparedCell>,
        runtime: &mut DepositedGenerationRuntime<'_>,
    ) -> Result<Vec<ExpandedCell>, MorphologicalLanguageError> {
        let candidate_count = prepared
            .iter()
            .map(|cell| match &cell.expansion {
                PreparedExpansion::Events { candidates, .. } => candidates.len(),
                _ => 0,
            })
            .try_fold(0usize, |total, extent| total.checked_add(extent))
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        if candidate_count == 0 {
            let mut expanded = Vec::with_capacity(prepared.len());
            for cell in prepared {
                let opened = self.materialize_complete(charge, cell.expansion)?;
                expanded.push(ExpandedCell {
                    site: cell.site,
                    co_present: cell.branch_population.saturating_mul(opened.len() as u64),
                    opened,
                });
            }
            return Ok(expanded);
        }

        // **Two independently assembled key sheets, and nothing that resembles the answer.**
        //
        // The deposit sheet is the conduct morphology's own canonically ordered population, each
        // row carrying only its activity and its exact transport key. The key sheet is each
        // candidate's own ordered key set. Which deposit a candidate's key equals is asked on the
        // card and nowhere here — see `conduct_cuda`'s module doc for what this replaced.
        //
        // **The identity width is read off the front, not assumed.** `token_germs` founds a germ
        // identity from the token's own surface, so identities are of several word counts and the
        // first version of this assembly refused every real front. The declared width is the widest
        // identity present in the deposits or in the candidates, and the shorter ones are padded
        // under a length-prefixed encoding that keeps the padding injective and order-invariant.
        let mut identity_words = runtime.morphology.identity_word_extent();
        for cell in &prepared {
            let PreparedExpansion::Events { candidates, .. } = &cell.expansion else {
                continue;
            };
            for event in candidates {
                for edge in &event.conduct_candidates {
                    identity_words = identity_words.max(edge.identity_word_extent());
                }
            }
        }
        let key_words = MorphologicalConductEdgeAddress::key_word_extent(identity_words);
        // The card searches this sheet, so it is ordered by the CARD's key order, which is not the
        // address order the atlas is canonical in — see `MorphologicalConductEdgeAddress::key_words`.
        // The ordinals the card returns index into exactly this sequence.
        let deposit_projection = runtime
            .morphology
            .card_ordered_deposits()
            .into_iter()
            .map(|deposit| {
                (
                    deposit.edge().clone(),
                    deposit
                        .exterior_sources()
                        .iter()
                        .map(|source| source.identity().to_owned())
                        .collect::<BTreeSet<_>>(),
                )
            })
            .collect::<LocalSequence<_>>();
        if deposit_projection.is_empty() {
            return Err(MorphologicalLanguageError::MalformedFiber);
        }
        let mut device_deposits = LocalSequence::with_capacity(deposit_projection.len());
        for (edge, _) in &deposit_projection {
            device_deposits.push(MorphologicalConductDepositRow::new(
                true,
                card_key(edge, identity_words)?,
            ));
        }

        let mut device_candidates = LocalSequence::with_capacity(candidate_count);
        let mut device_keys = LocalSequence::new();
        let mut candidate_at = 0u32;
        for cell in &prepared {
            let PreparedExpansion::Events { candidates, .. } = &cell.expansion else {
                continue;
            };
            for event in candidates {
                // The candidate's face is the generation site it was opened at — a receiver
                // coordinate the card returns and the host checks, never a tag invented to make a
                // guard fire.
                device_candidates.push(
                    MorphologicalConductCandidate::new(cell.site)
                        .ok_or(MorphologicalLanguageError::MalformedFiber)?,
                );
                // Ascending in the CARD's key order, which the front and the card both re-check.
                let mut candidate_keys = event
                    .conduct_candidates
                    .iter()
                    .collect::<LocalSequence<_>>();
                candidate_keys.sort_by(|left, right| left.card_key_cmp(right));
                for edge in candidate_keys {
                    let key = card_key(edge, identity_words)?;
                    debug_assert_eq!(key.len(), key_words);
                    device_keys.push(MorphologicalConductCandidateKey::new(candidate_at, key));
                }
                candidate_at = candidate_at
                    .checked_add(1)
                    .ok_or(MorphologicalLanguageError::CarrierExtent)?;
            }
        }
        if candidate_at as usize != candidate_count {
            return Err(MorphologicalLanguageError::MalformedFiber);
        }
        let front = MorphologicalConductCudaFront::new(
            key_words,
            device_candidates,
            device_deposits,
            device_keys,
        )?;
        let returned = runtime.executor.enact(&front)?;
        if returned.semantic.candidates.len() != candidate_count {
            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                at: "the card returned a different candidate population than the front shipped",
            }
            .into());
        }
        runtime.apparatus.push(returned.apparatus);
        let returned_candidates = returned.semantic.candidates;

        let mut returned_at = 0usize;
        let mut expanded = Vec::with_capacity(prepared.len());
        for cell in prepared {
            let opened = match cell.expansion {
                PreparedExpansion::Events {
                    mut state,
                    candidates,
                } => {
                    let witness_population = state.population.witnesses.len();
                    let mut opened = Vec::with_capacity(candidates.len());
                    let mut withheld_candidates = LocalSequence::new();
                    for mut event in candidates {
                        let returned = returned_candidates.get(returned_at).ok_or(
                            MorphologicalConductCudaError::InvalidDeviceReturn {
                                at: "the card returned fewer candidate rows than the front shipped",
                            },
                        )?;
                        if returned.candidate as usize != returned_at {
                            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                                at: "a returned candidate ordinal is out of order",
                            }
                            .into());
                        }
                        if returned.face != cell.site {
                            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                                at: "a returned candidate face is not the site it was opened at",
                            }
                            .into());
                        }
                        if returned.key_rows as usize != event.conduct_candidates.len() {
                            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                                at: "the card read a different number of keys for a candidate \
                                     than the front shipped for it",
                            }
                            .into());
                        }
                        let candidate_edges = event
                            .conduct_candidates
                            .iter()
                            .cloned()
                            .collect::<LocalSequence<_>>();
                        let mut attached = LocalSequence::new();
                        let mut attached_set = LocalSet::new();
                        let mut conducting_sources = BTreeSet::new();
                        for deposit_at in &returned.active_deposits {
                            let (edge, sources) = deposit_projection.get(*deposit_at as usize).ok_or(
                                MorphologicalConductCudaError::InvalidDeviceReturn {
                                    at: "a returned deposit ordinal is outside the shipped sheet",
                                },
                            )?;
                            if !event.conduct_candidates.contains(edge)
                                || !attached_set.insert(edge.clone())
                            {
                                return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                                    at: "the card attached a deposit this candidate did not carry, \
                                         or attached one twice",
                                }
                                .into());
                            }
                            attached.push(edge.clone());
                            conducting_sources.extend(sources.iter().cloned());
                        }
                        let candidate = runtime.next_candidate;
                        runtime.next_candidate = runtime
                            .next_candidate
                            .checked_add(1)
                            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
                        runtime
                            .dispositions
                            .push(MorphologicalConductTransitionDisposition {
                                chronology,
                                candidate,
                                surface: event.token.clone(),
                                witness_population,
                                candidate_edges,
                                attached_deposits: attached,
                            });
                        returned_at += 1;
                        if attached_set.is_empty() {
                            // Withheld, retained, never emitted. The complete fiber is a real
                            // object and is not a return.
                            withheld_candidates.push(candidate);
                            continue;
                        }
                        event.conducting_supports = attached_set;
                        event.conducting_sources = conducting_sources;
                        let mut successor = state.fork();
                        self.enact_event(
                            charge,
                            &mut successor,
                            event,
                            MorphologicalTransport::RecurrentLexical,
                        )?;
                        opened.push(ExpandedCurrent::forked(successor));
                    }
                    if opened.is_empty() {
                        // **Where nothing conducts, the return is the obstruction with its
                        // address.** This cell's whole current used to be dropped here — it entered
                        // neither the pending front nor the rested population, so a receiver could
                        // not tell a branch the deposits refused from one that never existed. It
                        // now comes to rest as `Obstructed` and is returned among the outputs, and
                        // the candidates it withheld are named by ordinal in the receipt.
                        self.finish_active_phase(charge, &mut state, None)?;
                        state.current.rest =
                            Some(MorphologicalResponseRest::Obstructed {
                                open_obligations: open_face_indices(&state.current.open_faces),
                            });
                        runtime.obstructions.push(MorphologicalConductObstruction {
                            chronology,
                            site: cell.site,
                            witness_population,
                            withheld_candidates,
                        });
                        opened.push(ExpandedCurrent::carried(state));
                    }
                    opened
                }
                other => self.materialize_complete(charge, other)?,
            };
            expanded.push(ExpandedCell {
                site: cell.site,
                co_present: cell.branch_population.saturating_mul(opened.len() as u64),
                opened,
            });
        }
        if returned_at != candidate_count {
            return Err(MorphologicalConductCudaError::InvalidDeviceReturn {
                at: "the front consumed a different candidate population than it shipped",
            }
            .into());
        }
        Ok(expanded)
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
                conduct_candidates: LocalSet::new(),
                conduct_sources: BTreeSet::new(),
                conducting_supports: LocalSet::new(),
                conducting_sources: BTreeSet::new(),
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

    /// **Recruit under the maximal cover, and fall back only if it returns nothing.**
    ///
    /// This is the union over covers in `I(R) = ⋃_K ⋂_{f∈K} I(f)`, taken with the largest block
    /// first: a receiver whose whole active family is carried together recruits from that, and only
    /// a receiver nothing carries whole falls back to the faces it touches.
    fn event_candidates(
        &self,
        reflection: &ReflectiveCurrentFront,
        active: &ActiveResponseCurrent,
    ) -> Result<Vec<EventCandidate>, MorphologicalLanguageError> {
        let complete = self.event_candidates_under(reflection, active, ContextCover::Complete)?;
        if !complete.is_empty() {
            return Ok(complete);
        }
        self.event_candidates_under(reflection, active, ContextCover::Touching)
    }

    fn event_candidates_under(
        &self,
        reflection: &ReflectiveCurrentFront,
        active: &ActiveResponseCurrent,
        cover: ContextCover,
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
                        conduct_candidates: LocalSet::new(),
                        conduct_sources: BTreeSet::from([clause.source.clone()]),
                        conducting_supports: LocalSet::new(),
                        conducting_sources: BTreeSet::new(),
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
                let carries_the_family = match cover {
                    ContextCover::Complete => active.clauses.is_subset(&context_clauses),
                    ContextCover::Touching => !context_clauses.is_disjoint(&active.clauses),
                };
                if !carries_the_family {
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
                let support_sources = clauses
                    .iter()
                    .map(|clause_at| {
                        self.clauses
                            .get(*clause_at)
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
                                conduct_candidates: LocalSet::new(),
                                conduct_sources: BTreeSet::new(),
                                conducting_supports: LocalSet::new(),
                                conducting_sources: BTreeSet::new(),
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
                        entry.conduct_candidates.insert(
                            MorphologicalConductEdgeAddress::from_branch_support(
                                MorphologicalConductChart::ClauseLexical,
                                branch,
                                support,
                            )?,
                        );
                        // The support's OWN target occurrences, not this candidate's reached
                        // position: it is the transport that recurred or did not, and its exterior
                        // lineage is the same population the conduct atlas founds a deposit from.
                        entry.conduct_sources.extend(support_sources.iter().cloned());
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
                let carries_the_family = match cover {
                    ContextCover::Complete => active
                        .passages
                        .iter()
                        .all(|passage| context_passages.contains(passage)),
                    ContextCover::Touching => context_passages
                        .iter()
                        .any(|passage| active.passages.contains(passage)),
                };
                if !carries_the_family {
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
                let support_sources = passages
                    .iter()
                    .map(|passage_fiber| {
                        self.passages
                            .get(passage_fiber)
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
                                    conduct_candidates: LocalSet::new(),
                                    conduct_sources: BTreeSet::new(),
                                    conducting_supports: LocalSet::new(),
                                    conducting_sources: BTreeSet::new(),
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
                            entry.conduct_candidates.insert(
                                MorphologicalConductEdgeAddress::from_branch_support(
                                    MorphologicalConductChart::PassageLexical,
                                    branch,
                                    support,
                                )?,
                            );
                            entry.conduct_sources.extend(support_sources.iter().cloned());
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

        // **Nondomination, on the exact witnesses — the same law `phase_candidates` already runs.**
        //
        // A phase candidate is removed only when another carries every one of its exact witnesses
        // and at least one strictly stronger, which is the ratified rule: *"No scalar score,
        // probability, softmax, embedding distance, random sample, or host-written answer selects
        // the result."* Domination is not ranking — it is a partial order, so incomparable
        // candidates all survive and plurality is still the return.
        //
        // **`event_candidates` ran no such filter.** Its only test was non-emptiness, so a token
        // reachable through a strictly poorer witness family opened a branch beside the richer one
        // that subsumes it, and the population multiplied by every such shadow at every step. That
        // is the difference between a machine that resonates with the structure that carries the
        // receiver's face and one that couples everything it touched.
        // Domination is decided in place over the candidate population — nothing is materialized
        // to ask the question, and `LocalSet` is the substrate's own carrier for the answer.
        // Positions rather than copied keys: `BTreeMap::retain` visits in the same key order
        // `iter` does, so the index is the address and nothing is duplicated to remember it.
        let mut dominated = LocalSet::new();
        for (at, (key, candidate)) in candidates.iter().enumerate() {
            let subsumed = candidates.iter().any(|(other_key, other)| {
                other_key != key
                    && other.token == candidate.token
                    && candidate.clause_horizons.is_subset(&other.clause_horizons)
                    && candidate.passage_horizons.is_subset(&other.passage_horizons)
                    && candidate
                        .recurrence_multiplicities
                        .is_subset(&other.recurrence_multiplicities)
                    && candidate.clauses.is_subset(&other.clauses)
                    && candidate.passages.is_subset(&other.passages)
                    && candidate.sources.is_subset(&other.sources)
                    // Strictly stronger somewhere. Witness-identical candidates are incomparable
                    // and both stand: this is a partial order, never a ranking.
                    && (candidate.clause_horizons != other.clause_horizons
                        || candidate.passage_horizons != other.passage_horizons
                        || candidate.recurrence_multiplicities != other.recurrence_multiplicities
                        || candidate.clauses != other.clauses
                        || candidate.passages != other.passages
                        || candidate.sources != other.sources)
            });
            if subsumed {
                dominated.insert(at);
            }
        }
        let mut at = 0usize;
        candidates.retain(|_, _| {
            let keep = !dominated.contains(&at);
            at += 1;
            keep
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
            // **FOUND a new tip, or RIDE a section already founded.** This refused the second
            // encounter as `MalformedFiber`, which treats a RIDE as a malformation and contradicts
            // the ratified law directly —
            // `research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL_THE_RETURN_TRAVELS_THE_FOUND_PATH.md`:
            //
            //   FOUND grows a locally new conducting axis.
            //   RIDE conducts through consequential standing form.
            //   **The same passage can RIDE old sections while FOUNDing a new tip.**
            //
            // The refusal is also what made generation exponential. A branch forbidden to ride must
            // remember every support it founded, so the founded set enters the current's identity
            // and the reachable population is `2^supports` — a self-avoiding walk, which is a
            // global constraint on a path and therefore a barrier under `H.0219` rather than a
            // decomposable law. Riding costs nothing because the terrain already paid.
            let uses = Arc::make_mut(&mut state.current.reflection.recurrent_support_uses);
            let founded = uses.get(support).copied().unwrap_or(0);
            if founded == 0 {
                uses.insert(support.clone(), 1);
            }
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
        // **The exterior lineage of the supports that licensed this transition, on either path.**
        //
        // One law, two paths. Where a deposit attached the transition, the licensing supports are
        // exactly those deposits and the population is theirs. Where no morphology is in scope,
        // nothing gates, so every exact support the material opened licensed it and the population
        // is the one the supports themselves carry — read at the construction site into
        // `conduct_sources` and never reconstructed from the query context or the token surface.
        //
        // Taking this only from the deposited path is what zeroed `supporting_sources` on the
        // complete path and deleted the instrument that measured the single-source finding.
        let conducting_sources = if event.conducting_supports.is_empty() {
            self.source_names(&event.conduct_sources)?
        } else {
            event.conducting_sources
        };
        let returned_token = MorphologicalGeneratedToken {
            token: event.token.clone(),
            transport,
            lexical_horizons,
            forward_mark_horizon,
            reverse_mark_horizon,
            recurrent_sources: caused_sources.clone(),
            recurrent_context_sources,
            caused_sources,
            conducting_supports: event.conducting_supports,
            conducting_sources,
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
