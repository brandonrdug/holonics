//! Exact contextual language generation composed from the production resonance Swing and the
//! factorized suffix ecology.
//!
//! A passage remains one caused source fiber. Its lexical faces recurrently expose that fiber
//! through [`ResonanceEcology`]; they are not embedded into a detached vector or scored by a
//! router. The returned source population is the contemporary contextual hexis. Each participating
//! source retains its own exact suffix ecology, so ordered chronology is restricted through only
//! the sources actually reached by the prompt. Plural continuations remain plural. Every emitted
//! path re-enters a branch-local resonance rest as self-emanated cause before its next continuation
//! is requested.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use body::num::Cog;
use holonic_structure::{LocalRelations, LocalSequence, LocalSet};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    LiveCurrentExecutor, LiveCurrentMachine, ParallelHostLiveCurrentExecutor,
    ReceiverFiberIdentity, SparseStandingSurface,
};

use crate::{
    resonance_ecology::{
        fiber_from_bytes, ResonanceEcology, ResonanceEcologyError, ResonanceEcologyRestImage,
        ResonanceGerm, ResonanceOccurrence,
    },
    suffix_ecology::{ExactSuffixEcology, ExactSuffixEcologyError},
};

const TOKEN_SCHEMA: u64 = 0x4341_5553_544f_4b4e;
const FEATURE_SCHEMA: u64 = 0x4341_5553_4645_4154;
const SOURCE_SCHEMA: u64 = 0x4341_5553_534f_5552;
const ROUTE_REST_MAGIC: u32 = 0x4341_5254;
const ROUTE_REST_VERSION: u32 = 1;
const ROUTE_REST_HEADER_WORDS: usize = 4;
const ROUTE_REST_ROW_WORDS: usize = 6;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CausalLanguageError {
    EmptyCorpus,
    EmptyPassage(String),
    DuplicatePassage(String),
    EmptyPrompt,
    CarrierExtent,
    MalformedFiber,
    Resonance(ResonanceEcologyError),
    Suffix(ExactSuffixEcologyError),
}

impl From<ResonanceEcologyError> for CausalLanguageError {
    fn from(value: ResonanceEcologyError) -> Self {
        Self::Resonance(value)
    }
}

impl From<ExactSuffixEcologyError> for CausalLanguageError {
    fn from(value: ExactSuffixEcologyError) -> Self {
        Self::Suffix(value)
    }
}

/// Exact coproduct of independent feature-receiver rests. No execution partition address enters
/// this image: rows are canonically ordered by complete feature fiber.
#[derive(Debug, PartialEq, Eq)]
pub struct CausalLanguageRouteRestImage {
    receivers: LocalRelations<ReceiverFiberIdentity, ResonanceEcologyRestImage>,
}

impl CausalLanguageRouteRestImage {
    pub fn receptor_count(&self) -> usize {
        self.receivers.len()
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, CausalLanguageError> {
        let count =
            u64::try_from(self.receivers.len()).map_err(|_| CausalLanguageError::CarrierExtent)?;
        let mut words = vec![
            ROUTE_REST_MAGIC,
            ROUTE_REST_VERSION,
            count as u32,
            (count >> 32) as u32,
        ];
        for (feature, rest) in self.receivers.iter() {
            let feature_extent = u64::try_from(feature.words().len())
                .map_err(|_| CausalLanguageError::CarrierExtent)?;
            let rest = rest.encode_native_bytes()?;
            if rest.len() % core::mem::size_of::<u32>() != 0 {
                return Err(CausalLanguageError::MalformedFiber);
            }
            let rest_extent =
                u64::try_from(rest.len()).map_err(|_| CausalLanguageError::CarrierExtent)?;
            words.extend([
                feature.schema() as u32,
                (feature.schema() >> 32) as u32,
                feature_extent as u32,
                (feature_extent >> 32) as u32,
                rest_extent as u32,
                (rest_extent >> 32) as u32,
            ]);
            words.extend_from_slice(feature.words());
            for row in rest.chunks_exact(core::mem::size_of::<u32>()) {
                words.push(u32::from_le_bytes([row[0], row[1], row[2], row[3]]));
            }
        }
        let mut bytes = LocalSequence::new();
        bytes
            .try_reserve_exact(
                words
                    .len()
                    .checked_mul(core::mem::size_of::<u32>())
                    .ok_or(CausalLanguageError::CarrierExtent)?,
            )
            .map_err(|_| CausalLanguageError::CarrierExtent)?;
        for word in words {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        Ok(bytes.into_inner())
    }

    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, CausalLanguageError> {
        if bytes.len() % core::mem::size_of::<u32>() != 0 {
            return Err(CausalLanguageError::MalformedFiber);
        }
        let words = bytes
            .chunks_exact(core::mem::size_of::<u32>())
            .map(|row| u32::from_le_bytes([row[0], row[1], row[2], row[3]]))
            .collect::<Vec<_>>();
        if words.len() < ROUTE_REST_HEADER_WORDS
            || words[0] != ROUTE_REST_MAGIC
            || words[1] != ROUTE_REST_VERSION
        {
            return Err(CausalLanguageError::MalformedFiber);
        }
        let count = join_u64(words[2], words[3])
            .and_then(|value| usize::try_from(value).ok())
            .ok_or(CausalLanguageError::MalformedFiber)?;
        let mut cursor = ROUTE_REST_HEADER_WORDS;
        let mut receivers = LocalRelations::new();
        for _ in 0..count {
            let header_end = cursor
                .checked_add(ROUTE_REST_ROW_WORDS)
                .filter(|end| *end <= words.len())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let schema = join_u64(words[cursor], words[cursor + 1])
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let feature_extent = join_u64(words[cursor + 2], words[cursor + 3])
                .and_then(|value| usize::try_from(value).ok())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let rest_bytes = join_u64(words[cursor + 4], words[cursor + 5])
                .and_then(|value| usize::try_from(value).ok())
                .filter(|extent| *extent % core::mem::size_of::<u32>() == 0)
                .ok_or(CausalLanguageError::MalformedFiber)?;
            cursor = header_end;
            let feature_end = cursor
                .checked_add(feature_extent)
                .filter(|end| *end <= words.len())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let feature = ReceiverFiberIdentity::new(schema, words[cursor..feature_end].to_vec());
            cursor = feature_end;
            let rest_words = rest_bytes / core::mem::size_of::<u32>();
            let rest_end = cursor
                .checked_add(rest_words)
                .filter(|end| *end <= words.len())
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let mut rest_wire = LocalSequence::new();
            rest_wire
                .try_reserve_exact(rest_bytes)
                .map_err(|_| CausalLanguageError::CarrierExtent)?;
            for word in &words[cursor..rest_end] {
                rest_wire.extend_from_slice(&word.to_le_bytes());
            }
            cursor = rest_end;
            let rest = ResonanceEcologyRestImage::from_native_bytes(&rest_wire)?;
            if feature.schema() != FEATURE_SCHEMA
                || receivers
                    .try_insert(feature, rest)
                    .map_err(|_| CausalLanguageError::CarrierExtent)?
                    .is_some()
            {
                return Err(CausalLanguageError::MalformedFiber);
            }
        }
        if cursor != words.len() {
            return Err(CausalLanguageError::MalformedFiber);
        }
        Ok(Self { receivers })
    }
}

/// One inherited textual section of an arbitrary receiver. `receiver` distinguishes the source
/// chart (dialogue, research prose, code, mathematics, transcript, returned experiment, ...);
/// lexical recurrence may still carry a question across several such charts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalLanguagePassage {
    pub identity: String,
    pub receiver: u64,
    pub text: String,
}

impl CausalLanguagePassage {
    pub fn new(identity: impl Into<String>, receiver: u64, text: impl Into<String>) -> Self {
        Self {
            identity: identity.into(),
            receiver,
            text: text.into(),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct PassageStanding {
    identity: String,
    receiver: u64,
    suffix: ExactSuffixEcology,
}

/// Exact receipt for one source fiber recruited by the prompt-wide Swing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecruitedSource {
    pub identity: String,
    pub receiver: u64,
    pub supporting_features: BTreeSet<String>,
}

/// Exact receipt for one emitted token. `matched_horizon` is the nested chronological receiver
/// which exposed the token, not a scalar likelihood. `sources` is the participating contextual
/// hexis at that boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CausalGeneratedToken {
    pub token: String,
    pub matched_horizon: u32,
    pub sources: BTreeSet<String>,
}

/// One branch-local generated deed.
#[derive(Debug, PartialEq, Eq)]
pub struct CausalGeneratedText {
    pub text: String,
    pub tokens: Vec<CausalGeneratedToken>,
    pub stopped_at_sentence_boundary: bool,
    returned_rest: ResonanceEcologyRestImage,
}

impl CausalGeneratedText {
    /// Exact branch-local body containing the received question and every emanated transition.
    pub const fn returned_rest_image(&self) -> &ResonanceEcologyRestImage {
        &self.returned_rest
    }
}

/// Complete receiver testimony for one generation request.
#[derive(Debug, PartialEq, Eq)]
pub struct CausalLanguageGeneration {
    pub prompt: String,
    pub prompt_tokens: Vec<String>,
    pub initial_hexis: Vec<RecruitedSource>,
    pub outputs: Vec<CausalGeneratedText>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CausalLanguageGenerationSpec {
    pub maximum_generated_tokens: usize,
    pub stop_at_sentence_boundary: bool,
}

impl Default for CausalLanguageGenerationSpec {
    fn default() -> Self {
        Self {
            maximum_generated_tokens: 64,
            stop_at_sentence_boundary: true,
        }
    }
}

/// A conditioned language body. The live route rest owns recurrent source recruitment; suffix
/// ecologies own exact ordered continuations globally and inside every source fiber.
#[derive(Debug)]
pub struct CausalLanguageEcology {
    route_rest: CausalLanguageRouteRestImage,
    route_sections: BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
    passages: BTreeMap<ReceiverFiberIdentity, PassageStanding>,
    global_suffix: ExactSuffixEcology,
    passage_population: usize,
    lexical_occurrences: usize,
    route_occurrences: usize,
    route_relations: usize,
    conditioning_events: usize,
}

impl CausalLanguageEcology {
    pub fn condition(
        passages: &[CausalLanguagePassage],
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<Self, CausalLanguageError> {
        if passages.is_empty() {
            return Err(CausalLanguageError::EmptyCorpus);
        }
        let trace = std::env::var_os("SOMA_CAUSAL_LANGUAGE_TRACE").is_some();
        let conditioning_started = Instant::now();
        let mut identities = LocalSet::new();
        let mut standing = BTreeMap::new();
        let mut global_paths = Vec::new();
        let mut route_groups = BTreeMap::<ReceiverFiberIdentity, Vec<RouteTrainingSection>>::new();
        let mut lexical_occurrences = 0usize;

        let mut route_relations = 0usize;

        for (passage_at, passage) in passages.iter().enumerate() {
            if !identities.insert(passage.identity.clone()) {
                return Err(CausalLanguageError::DuplicatePassage(
                    passage.identity.clone(),
                ));
            }
            let tokens = lexical_tokens(&passage.text);
            if tokens.is_empty() {
                return Err(CausalLanguageError::EmptyPassage(passage.identity.clone()));
            }
            lexical_occurrences = lexical_occurrences
                .checked_add(tokens.len())
                .ok_or(CausalLanguageError::CarrierExtent)?;
            let path = token_germs(&tokens)?;
            let suffix = ExactSuffixEcology::condition(std::slice::from_ref(&path))?;
            global_paths.push(path);

            let source = source_fiber(passage)?;
            let features = route_features(&tokens);
            route_relations = route_relations
                .checked_add(features.len())
                .ok_or(CausalLanguageError::CarrierExtent)?;
            let source_order =
                u64::try_from(passage_at).map_err(|_| CausalLanguageError::CarrierExtent)?;
            for feature in features {
                let feature_identity = route_feature_fiber(&feature);
                route_groups
                    .entry(feature_identity)
                    .or_default()
                    .push(RouteTrainingSection {
                        source_order,
                        source: source.clone(),
                    });
            }

            standing.insert(
                source.clone(),
                PassageStanding {
                    identity: passage.identity.clone(),
                    receiver: passage.receiver,
                    suffix,
                },
            );
            if trace && (passage_at + 1) % 100 == 0 {
                eprintln!(
                    "causal-language condition: formed {} passage suffixes / {} route sections in {} ms",
                    passage_at + 1,
                    route_relations,
                    conditioning_started.elapsed().as_millis()
                );
            }
        }

        if trace {
            eprintln!(
                "causal-language condition: forming global suffix over {} lexical occurrences",
                lexical_occurrences
            );
        }
        let global_suffix = ExactSuffixEcology::condition(&global_paths)?;
        if trace {
            eprintln!(
                "causal-language condition: global suffix formed in {} ms; crossing {} local route sections",
                conditioning_started.elapsed().as_millis(),
                route_relations
            );
        }
        let (route_rest, route_sections, conditioning_events) =
            condition_route_receivers(route_groups, action, worker_threads)?;
        if trace {
            eprintln!(
                "causal-language condition: rested {} route receptors after {} events in {} ms",
                route_sections.len(),
                conditioning_events,
                conditioning_started.elapsed().as_millis()
            );
        }
        Ok(Self {
            route_rest,
            route_sections,
            passages: standing,
            global_suffix,
            passage_population: passages.len(),
            lexical_occurrences,
            route_occurrences: route_relations,
            route_relations,
            conditioning_events,
        })
    }

    pub const fn passage_population(&self) -> usize {
        self.passage_population
    }

    pub const fn lexical_occurrence_population(&self) -> usize {
        self.lexical_occurrences
    }

    pub const fn route_occurrence_population(&self) -> usize {
        self.route_occurrences
    }

    pub const fn route_relation_population(&self) -> usize {
        self.route_relations
    }

    pub const fn conditioning_event_population(&self) -> usize {
        self.conditioning_events
    }

    pub fn route_rest_image(&self) -> &CausalLanguageRouteRestImage {
        &self.route_rest
    }

    pub fn route_receptor_population(&self) -> usize {
        self.route_sections.len()
    }

    pub fn global_suffix(&self) -> &ExactSuffixEcology {
        &self.global_suffix
    }

    pub fn generate(
        &self,
        prompt: &str,
        spec: CausalLanguageGenerationSpec,
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<CausalLanguageGeneration, CausalLanguageError> {
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        self.generate_with_executor(prompt, spec, action, &mut host)
    }

    /// Generate through one caller-retained physical executor. Recruitment and suffix emanation
    /// remain exact host work, but the question event and every self-emanated return of every
    /// terminal path cross the supplied executor; selecting a card at the outer language boundary
    /// cannot silently construct a private host executor here.
    pub fn generate_with_executor(
        &self,
        prompt: &str,
        spec: CausalLanguageGenerationSpec,
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<CausalLanguageGeneration, CausalLanguageError> {
        let prompt_tokens = lexical_tokens(prompt);
        if prompt_tokens.is_empty() {
            return Err(CausalLanguageError::EmptyPrompt);
        }

        // The cover, declared once for this leader.
        let cover = holonic_engine::hardware_cover::HardwareCover::host_only();
        let initial = self.recruit(&prompt_tokens);
        let initial_hexis = self.recruitment_read(&initial.sources)?;
        let mut states = vec![GenerationState {
            history: prompt_tokens.clone(),
            emitted: Vec::new(),
            source_hexis: initial.sources,
            stopped: false,
        }];

        for _ in 0..spec.maximum_generated_tokens {
            // **The leader's front: branch tips are co-present, an arc is serial.**
            //
            // `states` is a front of branch tips; `continuations` is the junction each opens; the
            // successors are the next front. What travels ONE arc is ordered and stays so — the
            // history a tip carries is untouched — while distinct tips are independent, so they are
            // co-present and the cover carries them. Chronology is not seriality: a leader is a
            // branching structure with time parity, and asserting a total order where the material
            // has a tree is the error this removes.
            //
            // The law is `hardware_cover::expand_front`. **This comment asserted the sharing before
            // it was true**: the leader was the law's only external caller until 2026-08-11, when
            // `morphological_language::generate_currents` moved off a by-count `at % lanes` cover
            // and `token_invariance::sweep_covered` gave up its own second copy of the by-extent
            // placement. All three generation fronts conduct through it now. A covering per organ
            // is the cabinet failure one level down — and the two receiver-conditioning fronts
            // further down THIS file still section by count, so they are outside that statement.
            let successors = holonic_engine::hardware_cover::expand_front(
                states,
                &cover,
                // A tip's extent is what it has already emitted: a long branch opens a wider
                // junction than a short one, and covering by count would weigh them the same.
                |state: &GenerationState| state.emitted.len() as u64 + 1,
                |state: GenerationState| -> Result<Vec<GenerationState>, CausalLanguageError> {
                    let mut branched = Vec::new();
                    if state.stopped {
                        branched.push(state);
                        return Ok(branched);
                    }
                    let mut active_hexis = state.source_hexis.clone();
                    let mut branches = self.continuations(&state.history, &active_hexis)?;
                    if branches.is_empty() {
                        active_hexis = self.recruit(&state.history).sources;
                        branches = self.continuations(&state.history, &active_hexis)?;
                    }
                    if branches.is_empty() {
                        let mut stopped = state;
                        stopped.stopped = true;
                        branched.push(stopped);
                        return Ok(branched);
                    }
                    for branch in branches {
                        let source_names = branch
                            .sources
                            .iter()
                            .map(|source| {
                                self.passages
                                    .get(source)
                                    .map(|passage| passage.identity.clone())
                                    .ok_or(CausalLanguageError::MalformedFiber)
                            })
                            .collect::<Result<BTreeSet<_>, _>>()?;
                        let source_hexis = branch
                            .sources
                            .iter()
                            .map(|source| {
                                active_hexis
                                    .get(source)
                                    .cloned()
                                    .map(|support| (source.clone(), support))
                                    .ok_or(CausalLanguageError::MalformedFiber)
                            })
                            .collect::<Result<BTreeMap<_, _>, _>>()?;
                        let mut history = state.history.clone();
                        history.push(branch.token.clone());
                        let mut emitted = state.emitted.clone();
                        emitted.push(CausalGeneratedToken {
                            token: branch.token.clone(),
                            matched_horizon: branch.matched_horizon,
                            sources: source_names,
                        });
                        let stopped = spec.stop_at_sentence_boundary
                            && emitted.len() >= 4
                            && sentence_boundary(&branch.token);
                        branched.push(GenerationState {
                            history,
                            emitted,
                            source_hexis,
                            stopped,
                        });
                    }

                    Ok(branched)
                },
            )?;
            let all_stopped = successors.iter().all(|state| state.stopped);
            states = successors;
            if all_stopped {
                break;
            }
        }

        let mut outputs = Vec::with_capacity(states.len());
        for state in states {
            let mut ecology =
                self.receive_question_with_executor(&prompt_tokens, action, executor)?;
            let mut predecessor = prompt_tokens
                .last()
                .map(ToOwned::to_owned)
                .ok_or(CausalLanguageError::EmptyPrompt)?;
            for (generated_at, generated) in state.emitted.iter().enumerate() {
                let source_order = u64::try_from(generated_at)
                    .map_err(|_| CausalLanguageError::CarrierExtent)?
                    .checked_add(1)
                    .ok_or(CausalLanguageError::CarrierExtent)?;
                let germs = token_germs(&[predecessor, generated.token.to_owned()])?;
                let occurrence = ResonanceOccurrence::self_emanated(source_order, germs)?;
                ecology.receive_with(&occurrence, action, executor)?;
                predecessor = generated.token.to_owned();
            }
            outputs.push(CausalGeneratedText {
                text: render_tokens(state.emitted.iter().map(|token| token.token.as_str())),
                stopped_at_sentence_boundary: state
                    .emitted
                    .last()
                    .is_some_and(|token| sentence_boundary(&token.token)),
                tokens: state.emitted,
                returned_rest: ecology.rest_image()?,
            });
        }
        Ok(CausalLanguageGeneration {
            prompt: prompt.to_owned(),
            prompt_tokens,
            initial_hexis,
            outputs,
        })
    }

    fn recruit(&self, history: &[String]) -> Recruitment {
        let features = route_features(history);
        if features.is_empty() {
            return Recruitment {
                sources: BTreeMap::new(),
            };
        }
        let mut sources = BTreeMap::<ReceiverFiberIdentity, BTreeSet<String>>::new();
        for feature in features {
            let identity = route_feature_fiber(&feature);
            if let Some(targets) = self.route_sections.get(&identity) {
                for source in targets {
                    sources
                        .entry(source.clone())
                        .or_default()
                        .insert(feature.clone());
                }
            }
        }
        Recruitment { sources }
    }

    fn recruitment_read(
        &self,
        sources: &BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
    ) -> Result<Vec<RecruitedSource>, CausalLanguageError> {
        sources
            .iter()
            .map(|(source, supporting_features)| {
                let passage = self
                    .passages
                    .get(source)
                    .ok_or(CausalLanguageError::MalformedFiber)?;
                Ok(RecruitedSource {
                    identity: passage.identity.clone(),
                    receiver: passage.receiver,
                    supporting_features: supporting_features.clone(),
                })
            })
            .collect()
    }

    fn continuations(
        &self,
        history: &[String],
        sources: &BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
    ) -> Result<Vec<Continuation>, CausalLanguageError> {
        let path = token_germs(history)?;
        let mut by_token = BTreeMap::<String, (u32, BTreeSet<ReceiverFiberIdentity>)>::new();
        let mut greatest_horizon = 0u32;

        for source in sources.keys() {
            let passage = self
                .passages
                .get(source)
                .ok_or(CausalLanguageError::MalformedFiber)?;
            let emanation = passage.suffix.emanate(&path)?;
            if emanation.branches().is_empty() {
                continue;
            }
            let horizon = emanation.longest_matched_length();
            greatest_horizon = greatest_horizon.max(horizon);
            for branch in emanation.branches() {
                if !branch
                    .supports()
                    .iter()
                    .any(|support| support.matched_length() == horizon)
                {
                    continue;
                }
                let token = fiber_bytes(branch.germ().identity())?;
                let entry = by_token
                    .entry(token)
                    .or_insert_with(|| (horizon, Default::default()));
                if horizon > entry.0 {
                    entry.0 = horizon;
                    entry.1.clear();
                }
                if horizon == entry.0 {
                    entry.1.insert(source.clone());
                }
            }
        }

        by_token.retain(|_, (horizon, _)| *horizon == greatest_horizon);
        if by_token.is_empty() {
            let emanation = self.global_suffix.emanate(&path)?;
            greatest_horizon = emanation.longest_matched_length();
            for branch in emanation.branches() {
                if !branch
                    .supports()
                    .iter()
                    .any(|support| support.matched_length() == greatest_horizon)
                {
                    continue;
                }
                by_token.insert(
                    fiber_bytes(branch.germ().identity())?,
                    (greatest_horizon, BTreeSet::new()),
                );
            }
        }
        Ok(by_token
            .into_iter()
            .map(|(token, (matched_horizon, sources))| Continuation {
                token,
                matched_horizon,
                sources,
            })
            .collect())
    }

    /// The retained host mouth for the question event. It has no library caller: this organ's one
    /// generation path now threads a caller-retained executor all the way down, so keeping a
    /// private host construction on that path would be the very defect the twin below removes.
    /// The signature is preserved rather than cut because it is the worker-count mouth a caller
    /// which has mounted nothing still expects.
    #[allow(dead_code)]
    fn receive_question(
        &self,
        prompt: &[String],
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<ResonanceEcology, CausalLanguageError> {
        let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
        self.receive_question_with_executor(prompt, action, &mut host)
    }

    /// Receive the outer question through one caller-retained physical executor. The executor
    /// crosses the question's Swing event; selecting a card at the outer language boundary cannot
    /// silently construct a private host executor here.
    fn receive_question_with_executor(
        &self,
        prompt: &[String],
        action: ActionCurrent,
        executor: &mut dyn LiveCurrentExecutor,
    ) -> Result<ResonanceEcology, CausalLanguageError> {
        let machine = LiveCurrentMachine::new(
            SparseStandingSurface::empty_rank(10)
                .map_err(|_| CausalLanguageError::CarrierExtent)?,
        );
        let mut ecology = ResonanceEcology::new(machine);
        let question = ResonanceOccurrence::probe(0, token_germs(prompt)?)?;
        ecology.receive_with(&question, action, executor)?;
        Ok(ecology)
    }
}

#[derive(Clone)]
pub(crate) struct RouteTrainingSection {
    pub(crate) source_order: u64,
    pub(crate) source: ReceiverFiberIdentity,
}

struct ConditionedRouteReceiver {
    feature: ReceiverFiberIdentity,
    rest: ResonanceEcologyRestImage,
    targets: BTreeSet<ReceiverFiberIdentity>,
    events: usize,
}

pub(crate) fn condition_route_receivers(
    groups: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>>,
    action: ActionCurrent,
    worker_threads: usize,
) -> Result<
    (
        CausalLanguageRouteRestImage,
        BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
        usize,
    ),
    CausalLanguageError,
> {
    if groups.is_empty() {
        return Ok((
            CausalLanguageRouteRestImage {
                receivers: LocalRelations::new(),
            },
            BTreeMap::new(),
            0,
        ));
    }
    let worker_count = worker_threads.max(1).min(groups.len());
    let mut partitions = (0..worker_count)
        .map(|_| Vec::new())
        .collect::<Vec<Vec<(ReceiverFiberIdentity, Vec<RouteTrainingSection>)>>>();
    for (at, group) in groups.into_iter().enumerate() {
        partitions[at % worker_count].push(group);
    }
    let mut conditioned = std::thread::scope(|scope| {
        let handles = partitions
            .into_iter()
            .map(|partition| scope.spawn(move || condition_route_partition(partition, action)))
            .collect::<Vec<_>>();
        let mut conditioned = Vec::new();
        for handle in handles {
            let mut rows = handle
                .join()
                .map_err(|_| CausalLanguageError::CarrierExtent)??;
            conditioned.append(&mut rows);
        }
        Ok::<_, CausalLanguageError>(conditioned)
    })?;
    conditioned.sort_by(|left, right| left.feature.cmp(&right.feature));

    let mut rests = LocalRelations::new();
    let mut routes = BTreeMap::<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>::new();
    let mut events = 0usize;
    for receiver in conditioned {
        events = events
            .checked_add(receiver.events)
            .ok_or(CausalLanguageError::CarrierExtent)?;
        if rests
            .try_insert(receiver.feature.to_owned(), receiver.rest)
            .map_err(|_| CausalLanguageError::CarrierExtent)?
            .is_some()
            || routes.insert(receiver.feature, receiver.targets).is_some()
        {
            return Err(CausalLanguageError::MalformedFiber);
        }
    }
    Ok((
        CausalLanguageRouteRestImage { receivers: rests },
        routes,
        events,
    ))
}

/// Condition the same complete route population through one caller-owned physical executor.
/// Chronology within each receiver remains ordered; the executor is free to realize each returned
/// event on a resident card. This is the production mouth used when a higher body explicitly
/// mounts CUDA rather than silently rebuilding the route ecology on host workers.
pub(crate) fn condition_route_receivers_with_executor(
    groups: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>>,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<
    (
        CausalLanguageRouteRestImage,
        BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
        usize,
    ),
    CausalLanguageError,
> {
    condition_route_receivers_mandatory(groups, action, executor)
}

/// Condition every independent route receiver through the caller's mandatory resident executor.
///
/// This mouth is deliberately serial across receiver ecologies: one mutable resident owner cannot
/// be cloned, and manufacturing auxiliary executors here would make placement an undeclared
/// fallback. Chronology within each receiver is unchanged. A future multi-stream resident owner
/// may cover the independent population behind the same return without changing this law.
pub(crate) fn condition_route_receivers_mandatory(
    groups: BTreeMap<ReceiverFiberIdentity, Vec<RouteTrainingSection>>,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<
    (
        CausalLanguageRouteRestImage,
        BTreeMap<ReceiverFiberIdentity, BTreeSet<ReceiverFiberIdentity>>,
        usize,
    ),
    CausalLanguageError,
> {
    let mut conditioned = Vec::new();
    conditioned
        .try_reserve_exact(groups.len())
        .map_err(|_| CausalLanguageError::CarrierExtent)?;
    for (feature, receiver_sections) in groups {
        conditioned.push(condition_route_receiver(
            feature,
            receiver_sections,
            action,
            executor,
        )?);
    }
    let mut rests = LocalRelations::new();
    let mut routes = BTreeMap::new();
    let mut events = 0usize;
    for receiver in conditioned {
        events = events
            .checked_add(receiver.events)
            .ok_or(CausalLanguageError::CarrierExtent)?;
        if rests
            .try_insert(receiver.feature.to_owned(), receiver.rest)
            .map_err(|_| CausalLanguageError::CarrierExtent)?
            .is_some()
            || routes.insert(receiver.feature, receiver.targets).is_some()
        {
            return Err(CausalLanguageError::MalformedFiber);
        }
    }
    Ok((
        CausalLanguageRouteRestImage { receivers: rests },
        routes,
        events,
    ))
}

fn condition_route_partition(
    partition: Vec<(ReceiverFiberIdentity, Vec<RouteTrainingSection>)>,
    action: ActionCurrent,
) -> Result<Vec<ConditionedRouteReceiver>, CausalLanguageError> {
    let mut conditioned = Vec::new();
    conditioned
        .try_reserve_exact(partition.len())
        .map_err(|_| CausalLanguageError::CarrierExtent)?;
    for (feature, sections) in partition {
        // Parallelism lives across independent receiver ecologies; one receiver's returned
        // chronology remains serial and therefore uses one physical worker.
        let mut executor = ParallelHostLiveCurrentExecutor::new(1);
        conditioned.push(condition_route_receiver(
            feature,
            sections,
            action,
            &mut executor,
        )?);
    }
    Ok(conditioned)
}

fn condition_route_receiver(
    feature: ReceiverFiberIdentity,
    sections: Vec<RouteTrainingSection>,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<ConditionedRouteReceiver, CausalLanguageError> {
    let machine = LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(10).map_err(|_| CausalLanguageError::CarrierExtent)?,
    );
    let mut route = ResonanceEcology::new(machine);
    let mut targets = BTreeSet::<ReceiverFiberIdentity>::new();
    for section in &sections {
        let occurrence = ResonanceOccurrence::routed_informant(
            section.source.to_owned(),
            section.source_order,
            germ(feature.to_owned())?,
            section.source.to_owned(),
        )?;
        let returned = route.receive_with(&occurrence, action, executor)?;
        let continuation_returned = returned
            .read()
            .continuations_after(&feature)
            .is_some_and(|returned_targets| returned_targets.contains(&section.source));
        if !continuation_returned || !returned.read().informants().contains(&section.source) {
            return Err(CausalLanguageError::MalformedFiber);
        }
        targets.insert(section.source.to_owned());
    }
    Ok(ConditionedRouteReceiver {
        feature,
        rest: route.rest_image()?,
        targets,
        events: sections.len(),
    })
}

#[derive(Clone)]
struct Recruitment {
    sources: BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
}

#[derive(Clone)]
struct Continuation {
    token: String,
    matched_horizon: u32,
    sources: BTreeSet<ReceiverFiberIdentity>,
}

struct GenerationState {
    history: Vec<String>,
    emitted: Vec<CausalGeneratedToken>,
    source_hexis: BTreeMap<ReceiverFiberIdentity, BTreeSet<String>>,
    stopped: bool,
}

fn source_fiber(
    passage: &CausalLanguagePassage,
) -> Result<ReceiverFiberIdentity, CausalLanguageError> {
    let identity = passage.identity.as_bytes();
    let extent = u64::try_from(identity.len()).map_err(|_| CausalLanguageError::CarrierExtent)?;
    let mut bytes = Vec::with_capacity(16 + identity.len());
    bytes.extend_from_slice(&passage.receiver.to_le_bytes());
    bytes.extend_from_slice(&extent.to_le_bytes());
    bytes.extend_from_slice(identity);
    Ok(fiber_from_bytes(SOURCE_SCHEMA, &bytes))
}

pub(crate) fn germ(identity: ReceiverFiberIdentity) -> Result<ResonanceGerm, CausalLanguageError> {
    let phase = RelationAtom::new(Cog::lit(1)).ok_or(CausalLanguageError::CarrierExtent)?;
    Ok(ResonanceGerm::new(identity, phase))
}

pub(crate) fn token_germs(tokens: &[String]) -> Result<Vec<ResonanceGerm>, CausalLanguageError> {
    tokens
        .iter()
        .map(|token| germ(fiber_from_bytes(TOKEN_SCHEMA, token.as_bytes())))
        .collect()
}

pub(crate) fn route_feature_fiber(feature: &str) -> ReceiverFiberIdentity {
    fiber_from_bytes(FEATURE_SCHEMA, feature.as_bytes())
}

fn route_features(tokens: &[String]) -> BTreeSet<String> {
    tokens
        .iter()
        // The lexical router receives morphologically extended word faces. Short function faces
        // remain fully present in suffix chronology but do not found near-ubiquitous routing
        // receptors which cannot distinguish a local source ecology.
        .filter(|token| token.chars().any(char::is_alphanumeric) && token.chars().count() >= 4)
        .map(|token| token.to_lowercase())
        .collect()
}

fn fiber_bytes(identity: &ReceiverFiberIdentity) -> Result<String, CausalLanguageError> {
    if !matches!(
        identity.schema(),
        TOKEN_SCHEMA | FEATURE_SCHEMA | SOURCE_SCHEMA
    ) || identity.words().len() < 2
    {
        return Err(CausalLanguageError::MalformedFiber);
    }
    let extent = u64::from(identity.words()[0]) | (u64::from(identity.words()[1]) << 32);
    let extent = usize::try_from(extent).map_err(|_| CausalLanguageError::CarrierExtent)?;
    let mut bytes = Vec::with_capacity(identity.words().len().saturating_sub(2).saturating_mul(4));
    for word in &identity.words()[2..] {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    if extent > bytes.len() {
        return Err(CausalLanguageError::MalformedFiber);
    }
    bytes.truncate(extent);
    String::from_utf8(bytes).map_err(|_| CausalLanguageError::MalformedFiber)
}

/// Deterministic lexical receiver for language morphology. Surface case remains part of the
/// chronological token face; routing derives a case-folded feature quotient separately.
pub fn lexical_tokens(text: &str) -> Vec<String> {
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Species {
        Word,
        Punctuation,
    }
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut species = None;
    let flush = |tokens: &mut Vec<String>, current: &mut String| {
        if !current.is_empty() {
            tokens.push(std::mem::take(current));
        }
    };
    for character in text.chars() {
        if character.is_alphanumeric() || character == '_' || character == '\'' {
            if species == Some(Species::Punctuation) {
                flush(&mut tokens, &mut current);
            }
            current.push(character);
            species = Some(Species::Word);
        } else if character.is_whitespace() {
            flush(&mut tokens, &mut current);
            species = None;
        } else {
            if species == Some(Species::Word) {
                flush(&mut tokens, &mut current);
            }
            if species == Some(Species::Punctuation)
                && matches!(character, '-' | '=' | ':' | '/' | '*' | '#')
            {
                current.push(character);
            } else {
                flush(&mut tokens, &mut current);
                current.push(character);
            }
            species = Some(Species::Punctuation);
        }
    }
    flush(&mut tokens, &mut current);
    tokens
}

pub fn render_tokens<'a>(tokens: impl IntoIterator<Item = &'a str>) -> String {
    let mut rendered = String::new();
    let mut previous = None::<String>;
    let mut inline_code = false;
    for token in tokens {
        if token == "`" {
            if !inline_code && !rendered.is_empty() {
                rendered.push(' ');
            }
            rendered.push('`');
            inline_code = !inline_code;
            previous = Some(token.to_owned());
            continue;
        }
        let closes = matches!(
            token,
            "." | "," | ";" | ":" | "!" | "?" | ")" | "]" | "}" | "-" | "/"
        );
        let opens_before = previous
            .as_deref()
            .is_some_and(|prior| matches!(prior, "(" | "[" | "{" | "#" | "/" | "-"))
            || (inline_code && previous.as_deref() == Some("`"));
        if !rendered.is_empty() && !closes && !opens_before {
            rendered.push(' ');
        }
        rendered.push_str(token);
        previous = Some(token.to_owned());
    }
    rendered
}

fn sentence_boundary(token: &str) -> bool {
    matches!(token, "." | "!" | "?")
}

fn join_u64(low: u32, high: u32) -> Option<u64> {
    Some(u64::from(low) | (u64::from(high) << 32))
}

#[cfg(test)]
mod tests {
    use super::*;

    use soma_membrane::{
        CurrentExecutionRequest, DirectedExecutionRequest, ExecutedContemporaryEvent,
        LiveCurrentError, RegionalExecutionRequest,
    };

    use crate::morphological_language::{
        MorphologicalGenerationSpec, MorphologicalLanguageEcology, MorphologicalLanguagePassage,
    };

    fn action() -> ActionCurrent {
        ActionCurrent::new(Cog::lit(1)).unwrap()
    }

    /// One caller-retained executor which counts the events it was actually asked to realize. It
    /// changes no result: it forwards every request to the same host carrier the private path
    /// would have built.
    struct CountingHostExecutor {
        host: ParallelHostLiveCurrentExecutor,
        enactments: usize,
    }

    impl CountingHostExecutor {
        const fn new(worker_threads: usize) -> Self {
            Self {
                host: ParallelHostLiveCurrentExecutor::new(worker_threads),
                enactments: 0,
            }
        }
    }

    impl LiveCurrentExecutor for CountingHostExecutor {
        fn enact(
            &mut self,
            physical_revision: u64,
            standing: &SparseStandingSurface,
            currents: &[CurrentExecutionRequest<'_>],
            relations: &[DirectedExecutionRequest],
            regional: &[RegionalExecutionRequest<'_>],
        ) -> Result<ExecutedContemporaryEvent, LiveCurrentError> {
            self.enactments += 1;
            self.host
                .enact(physical_revision, standing, currents, relations, regional)
        }
    }

    /// One supplied executor crosses every Swing event on both generation paths, and the return is
    /// the one the private-host path already produced.
    ///
    /// Equality alone would not separate a real twin from one which quietly rebuilt its own host
    /// pool and ignored the argument. The count is the frame that makes it falsifiable: the
    /// supplied executor is the only executor either generation path may reach, so a nonzero count
    /// is proof that the question event and every self-emanated return crossed it.
    #[test]
    fn one_supplied_executor_crosses_every_swing_event_on_both_generation_paths() {
        let causal = CausalLanguageEcology::condition(
            &[
                CausalLanguagePassage::new(
                    "training",
                    1,
                    "Training is conditioning morphology through returned consequence.",
                ),
                CausalLanguagePassage::new(
                    "multimodality",
                    2,
                    "Multimodality is caused co-presence viewed through different receivers.",
                ),
            ],
            action(),
            2,
        )
        .unwrap();
        let causal_prompt = "What changes the intermediate body? Training is";
        let causal_spec = CausalLanguageGenerationSpec {
            maximum_generated_tokens: 16,
            stop_at_sentence_boundary: true,
        };
        let private_host = causal
            .generate(causal_prompt, causal_spec, action(), 2)
            .unwrap();
        assert!(private_host
            .outputs
            .iter()
            .any(|output| !output.text.is_empty()));
        let mut causal_executor = CountingHostExecutor::new(2);
        let supplied = causal
            .generate_with_executor(causal_prompt, causal_spec, action(), &mut causal_executor)
            .unwrap();
        assert_eq!(private_host, supplied);
        assert!(causal_executor.enactments >= private_host.outputs.len());

        let morphological = MorphologicalLanguageEcology::condition(
            &[
                MorphologicalLanguagePassage::new(
                    "training",
                    "training-source",
                    1,
                    "Training changes morphology.",
                ),
                MorphologicalLanguagePassage::new(
                    "uncertainty",
                    "uncertainty-source",
                    2,
                    "Changes morphology while uncertainty remains.",
                ),
                MorphologicalLanguagePassage::new(
                    "control",
                    "control-source",
                    3,
                    "A separate receiver retains a control.",
                ),
            ],
            action(),
            2,
        )
        .unwrap();
        let morphological_prompt = "Relate training and uncertainty.";
        let morphological_spec = MorphologicalGenerationSpec {
            maximum_observed_tokens: 32,
        };
        let private_host = morphological
            .generate(morphological_prompt, morphological_spec, action(), 2)
            .unwrap();
        assert!(private_host
            .outputs
            .iter()
            .any(|output| !output.text.is_empty()));
        let mut morphological_executor = CountingHostExecutor::new(2);
        let supplied = morphological
            .generate_with_executor(
                morphological_prompt,
                morphological_spec,
                action(),
                &mut morphological_executor,
            )
            .unwrap();
        assert_eq!(private_host, supplied);
        assert!(morphological_executor.enactments >= private_host.outputs.len());
    }

    #[test]
    fn contextual_hexis_emits_text_and_reenters_as_cause() {
        let ecology = CausalLanguageEcology::condition(
            &[
                CausalLanguagePassage::new(
                    "training",
                    1,
                    "Training is conditioning morphology through returned consequence.",
                ),
                CausalLanguagePassage::new(
                    "multimodality",
                    2,
                    "Multimodality is caused co-presence viewed through different receivers.",
                ),
            ],
            action(),
            2,
        )
        .unwrap();
        let route_wire = ecology.route_rest_image().encode_native_bytes().unwrap();
        assert_eq!(
            CausalLanguageRouteRestImage::from_native_bytes(&route_wire).unwrap(),
            *ecology.route_rest_image()
        );
        let generated = ecology
            .generate(
                "What changes the intermediate body? Training is",
                CausalLanguageGenerationSpec {
                    maximum_generated_tokens: 16,
                    stop_at_sentence_boundary: true,
                },
                action(),
                2,
            )
            .unwrap();
        assert!(generated
            .initial_hexis
            .iter()
            .any(|source| source.identity == "training"));
        assert!(generated.outputs.iter().any(|output| {
            output.text == "conditioning morphology through returned consequence."
        }));
        assert!(generated
            .outputs
            .iter()
            .flat_map(|output| &output.tokens)
            .all(|token| token.matched_horizon > 0));
    }

    #[test]
    fn plural_successors_return_without_host_ranking_or_pruning() {
        let ecology = CausalLanguageEcology::condition(
            &[
                CausalLanguagePassage::new("alpha", 1, "Root emits alpha."),
                CausalLanguagePassage::new("beta", 2, "Root emits beta."),
                CausalLanguagePassage::new("gamma", 3, "Root emits gamma."),
            ],
            action(),
            2,
        )
        .unwrap();
        let generated = ecology
            .generate(
                "Root emits",
                CausalLanguageGenerationSpec {
                    maximum_generated_tokens: 1,
                    stop_at_sentence_boundary: false,
                },
                action(),
                2,
            )
            .unwrap();
        assert_eq!(generated.outputs.len(), 3);
        for expected in ["alpha", "beta", "gamma"] {
            assert!(generated.outputs.iter().any(|output| {
                output.tokens.len() == 1
                    && output.tokens[0].token == expected
                    && output.tokens[0].sources.contains(expected)
            }));
        }
    }

    #[test]
    fn absent_morphology_does_not_receive_a_root_vocabulary() {
        let ecology = CausalLanguageEcology::condition(
            &[CausalLanguagePassage::new(
                "training",
                1,
                "Training is conditioning morphology.",
            )],
            action(),
            1,
        )
        .unwrap();
        let generated = ecology
            .generate(
                "xylophonic quasar",
                CausalLanguageGenerationSpec {
                    maximum_generated_tokens: 8,
                    stop_at_sentence_boundary: true,
                },
                action(),
                1,
            )
            .unwrap();
        assert!(generated.initial_hexis.is_empty());
        assert!(generated
            .outputs
            .iter()
            .all(|output| output.text.is_empty()));
    }

    #[test]
    fn lexical_receiver_preserves_words_and_punctuation_as_distinct_faces() {
        let tokens = lexical_tokens("Receiver-local paths: don't flatten.");
        assert_eq!(
            tokens,
            ["Receiver", "-", "local", "paths", ":", "don't", "flatten", "."]
        );
        assert_eq!(
            render_tokens(tokens.iter().map(String::as_str)),
            "Receiver-local paths: don't flatten."
        );
    }

    #[test]
    #[ignore = "requires the RTX CUDA device and committed lineage_event PTX entry"]
    fn one_cell_complex_route_conditioning_is_host_card_exact() {
        let feature = route_feature_fiber("conditioning");
        let sources = [
            fiber_from_bytes(0x5254_534f_5552_4345, b"first"),
            fiber_from_bytes(0x5254_534f_5552_4345, b"second"),
        ];
        let groups = BTreeMap::from([(
            feature,
            vec![
                RouteTrainingSection {
                    source_order: 0,
                    source: sources[0].clone(),
                },
                RouteTrainingSection {
                    source_order: 1,
                    source: sources[1].clone(),
                },
            ],
        )]);
        let host = condition_route_receivers(groups.clone(), action(), 2).unwrap();
        let mut cuda = crate::live_current_cuda::CudaLiveCurrentExecutor::new(0).unwrap();
        let card = condition_route_receivers_with_executor(groups, action(), &mut cuda).unwrap();
        assert_eq!(host, card);
        assert!(cuda.launches() >= 2);
        assert!(cuda.contact_launches() >= 2);
    }
}
