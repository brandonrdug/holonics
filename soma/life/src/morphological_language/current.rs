use super::*;

#[path = "ecology.rs"]
mod ecology;
pub use ecology::MorphologicalLanguageEcology;

#[derive(Clone)]
struct QueryInterval {
    start: usize,
    end: usize,
    features: BTreeSet<String>,
    ordered_surface: Vec<String>,
    clause_ids: BTreeSet<usize>,
}

#[derive(Clone)]
struct QueryRegionGroup {
    regions: Vec<QueryInterval>,
}

#[derive(Clone)]
struct PhaseCandidate {
    clause: usize,
    covered_regions: BTreeMap<usize, BTreeSet<usize>>,
    evidence: BTreeSet<String>,
    mark_evidence: BTreeSet<String>,
    entry_lexical_horizons: BTreeSet<u32>,
    entry_recurrence_multiplicities: BTreeSet<u64>,
}

#[derive(Clone)]
struct EventCandidate {
    token: String,
    /// One exact recurrent suffix transport consumed by this event. A recruited phase onset is
    /// caused by query incidence and therefore carries no recurrent support.
    support: Option<RecurrentSupportKey>,
    clause_horizons: BTreeSet<u32>,
    passage_horizons: BTreeSet<u32>,
    recurrence_multiplicities: BTreeSet<u64>,
    clauses: BTreeSet<usize>,
    passages: BTreeSet<ReceiverFiberIdentity>,
    clause_positions: BTreeMap<usize, BTreeSet<usize>>,
    sources: BTreeSet<ReceiverFiberIdentity>,
    context_sources: BTreeSet<ReceiverFiberIdentity>,
}

/// The local suffix transport whose returned occurrence makes one continuation possible.
///
/// A suffix link may revisit the same visible surface, but that does not manufacture another
/// occurrence of the supporting transport. Its exact recurrence multiplicity is the available
/// capacity. Returning through a support consumes one caused occurrence in the branch-local
/// current.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct RecurrentSupportKey {
    clause: usize,
    emitted_at: usize,
}

/// Only the phase section capable of changing the next transport. Accumulated testimony is kept
/// on witness paths so two histories with the same future conduct may glue.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ActiveResponseCurrent {
    entry_clause: usize,
    covered_regions: BTreeMap<usize, BTreeSet<usize>>,
    clauses: BTreeSet<usize>,
    passages: BTreeSet<ReceiverFiberIdentity>,
    clause_positions: BTreeMap<usize, BTreeSet<usize>>,
}

/// Receiver testimony accumulated along one particular path through an active phase. None of
/// these fields changes candidate transport, so they must not prevent current-state gluing.
#[derive(Clone, Debug)]
struct ActiveResponseWitness {
    entry_clause: usize,
    entry_lexical_horizons: BTreeSet<u32>,
    entry_recurrence_multiplicities: BTreeSet<u64>,
    emitted_start: usize,
    touched_clauses: BTreeSet<usize>,
    touched_passages: BTreeSet<ReceiverFiberIdentity>,
    touched_sources: BTreeSet<ReceiverFiberIdentity>,
}

/// The operative reflection carried between emitted events. Both suffix currents are local
/// receiver addresses in the one shared conditioned ecology. A returned event advances them
/// directly; no complete chronology scan or branch-local body copy is needed.
/// **Everything a later step consults is in the identity, and the founded terrain is consulted.**
///
/// A hand-written ordering excluded `recurrent_support_uses` here, on the reading that the founded
/// set is terrain rather than position and so does not decide where a current *is*. That reading is
/// wrong for this body as it stands, for a reason that is checkable rather than interpretive:
/// **the field gates the next step.** `ecology.rs:1248`, `:1337` and `:1429` each ask
/// `recurrent_support_uses.contains_key(&support_key)` and `continue` when it is present, so two
/// currents carrying different founded sets do not have the same future — and merging them keeps
/// whichever map arrived first and discards the other.
///
/// Measured, and this is why it is not an argument: under a by-count cover the surviving map was a
/// function of the **lane count**, so generation returned 1,862 branches at one lane and **1,806 at
/// two**. A realization coordinate decided which continuations existed, which is the defect
/// `canon/THE_HOLOBROCHOS_SPINE.md` §6.6 names.
///
/// The population is `2^supports` while those three gates stand, and that is a real cost. It is not
/// paid for here. Bounding the returned population is a construction on the transport law — the
/// exact delay in `holonic_engine::receiver_current`, which `relational_language` consumes and this
/// organ does not — and a body that returns too much is recoverable where a body that returns the
/// wrong thing is not.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ReflectiveCurrentFront {
    clause_lexical: ExactSuffixCurrent,
    passage_lexical: ExactSuffixCurrent,
    last_surface: String,
    returned_event_count: usize,
    recurrent_support_uses: Arc<BTreeMap<RecurrentSupportKey, u64>>,
}

/// Terminal testimony retained for an observer. It is deliberately absent from the current key:
/// distinct paths with identical future conduct propagate once while retaining exact population
/// multiplicity and a bounded family of witness surfaces.
#[derive(Debug)]
struct MorphologicalWitness {
    emitted: BranchLineage<MorphologicalGeneratedToken>,
    phases: BranchLineage<MorphologicalResponsePhase>,
    active_phase: Option<ActiveResponseWitness>,
}

impl MorphologicalWitness {
    const fn empty() -> Self {
        Self {
            emitted: BranchLineage::new(),
            phases: BranchLineage::new(),
            active_phase: None,
        }
    }

    fn fork(&self) -> Self {
        let (emitted, _) = self.emitted.fork();
        let (phases, _) = self.phases.fork();
        Self {
            emitted,
            phases,
            active_phase: self.active_phase.clone(),
        }
    }

    fn carry_event(
        &mut self,
        event: MorphologicalGeneratedToken,
    ) -> Result<(), MorphologicalLanguageError> {
        self.emitted = core::mem::take(&mut self.emitted)
            .carry(event)
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        Ok(())
    }

    fn carry_phase(
        &mut self,
        phase: MorphologicalResponsePhase,
    ) -> Result<(), MorphologicalLanguageError> {
        self.phases = core::mem::take(&mut self.phases)
            .carry(phase)
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        Ok(())
    }

    fn materialize(
        &self,
    ) -> (
        Vec<MorphologicalGeneratedToken>,
        Vec<MorphologicalResponsePhase>,
    ) {
        let mut emitted = Vec::with_capacity(self.emitted.len());
        emitted.extend(self.emitted.newest_first().cloned());
        emitted.reverse();

        let mut phases = Vec::with_capacity(self.phases.len());
        phases.extend(self.phases.newest_first().cloned());
        phases.reverse();
        (emitted, phases)
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
struct MorphologicalCurrentState {
    reflection: ReflectiveCurrentFront,
    active_phase: Option<ActiveResponseCurrent>,
    /// Complete open query standing is shared by every current until a returned sentence
    /// actually discharges a local region.
    open_faces: Arc<BTreeMap<usize, BTreeSet<usize>>>,
    rest: Option<MorphologicalResponseRest>,
}

impl MorphologicalCurrentState {
    fn fork(&self) -> Self {
        Self {
            reflection: self.reflection.clone(),
            active_phase: self.active_phase.clone(),
            open_faces: Arc::clone(&self.open_faces),
            rest: self.rest.clone(),
        }
    }
}

struct MorphologicalGenerationState {
    current: MorphologicalCurrentState,
    population: MorphologicalCurrentPopulation,
}

struct MorphologicalCurrentPopulation {
    witnesses: Vec<MorphologicalWitness>,
}

impl MorphologicalGenerationState {
    fn empty(current: MorphologicalCurrentState) -> Self {
        Self {
            current,
            population: MorphologicalCurrentPopulation {
                witnesses: vec![MorphologicalWitness::empty()],
            },
        }
    }

    fn fork(&self) -> Self {
        Self {
            current: self.current.fork(),
            population: self.population.fork(),
        }
    }
}

impl MorphologicalCurrentPopulation {
    fn fork(&self) -> Self {
        let witnesses = self
            .witnesses
            .iter()
            .map(MorphologicalWitness::fork)
            .collect();
        Self { witnesses }
    }

    /// Merge another population with identical future conduct while retaining every path witness.
    fn merge_witnesses(&mut self, mut other: Self) -> Result<(), MorphologicalLanguageError> {
        self.witnesses.append(&mut other.witnesses);
        Ok(())
    }
}

fn insert_generation_state(
    states: &mut BTreeMap<MorphologicalCurrentState, MorphologicalCurrentPopulation>,
    state: MorphologicalGenerationState,
) -> Result<bool, MorphologicalLanguageError> {
    match states.entry(state.current) {
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(state.population);
            Ok(false)
        }
        std::collections::btree_map::Entry::Occupied(mut entry) => {
            entry.get_mut().merge_witnesses(state.population)?;
            Ok(true)
        }
    }
}

fn open_face_indices(open: &BTreeMap<usize, BTreeSet<usize>>) -> BTreeSet<usize> {
    open.keys().copied().collect()
}

fn covered_regions_is_subset(
    left: &BTreeMap<usize, BTreeSet<usize>>,
    right: &BTreeMap<usize, BTreeSet<usize>>,
) -> bool {
    left.iter().all(|(obligation, regions)| {
        right
            .get(obligation)
            .is_some_and(|other| regions.is_subset(other))
    })
}

fn caused_token_positions(
    tokens: &[String],
    prior_surface: &str,
    emitted_surface: &str,
    after_local_boundary: bool,
) -> BTreeSet<usize> {
    let mut positions = BTreeSet::new();
    if after_local_boundary && tokens.first().is_some_and(|token| token == emitted_surface) {
        positions.insert(0);
    }
    let mut at = 1usize;
    while at < tokens.len() {
        if tokens[at - 1] == prior_surface && tokens[at] == emitted_surface {
            positions.insert(at);
        }
        at += 1;
    }
    positions
}

fn surface_features(tokens: &[String]) -> BTreeSet<String> {
    folded_surface_tokens(tokens).into_iter().collect()
}

fn folded_surface_tokens(tokens: &[String]) -> Vec<String> {
    tokens
        .iter()
        .filter(|token| is_surface_word(token))
        .map(|token| token.to_lowercase())
        .collect()
}

fn is_surface_word(token: &str) -> bool {
    token.chars().any(char::is_alphanumeric)
}

fn clause_sections(tokens: &[String]) -> Vec<(Vec<String>, MorphologicalBoundary)> {
    let mut clauses = Vec::new();
    let mut current = Vec::new();
    let mut parentheses = 0usize;
    let mut brackets = 0usize;
    let mut braces = 0usize;
    for (at, token) in tokens.iter().enumerate() {
        current.push(token.clone());
        match token.as_str() {
            "(" => parentheses = parentheses.saturating_add(1),
            ")" => parentheses = parentheses.saturating_sub(1),
            "[" => brackets = brackets.saturating_add(1),
            "]" => brackets = brackets.saturating_sub(1),
            "{" => braces = braces.saturating_add(1),
            "}" => braces = braces.saturating_sub(1),
            _ => {}
        }
        let question_boundary = token == "?"
            && parentheses == 0
            && brackets == 0
            && braces == 0
            && tokens.get(at + 1).is_none_or(|next| {
                !matches!(next.as_str(), ";" | "," | ")" | "]" | "}" | "." | "?")
            });
        let boundary = match token.as_str() {
            "." | "!" => Some(MorphologicalBoundary::Sentence),
            "?" if question_boundary => Some(MorphologicalBoundary::Sentence),
            ";" | ":" => Some(MorphologicalBoundary::Clause),
            _ => None,
        };
        if let Some(boundary) = boundary {
            clauses.push((std::mem::take(&mut current), boundary));
        }
    }
    if !current.is_empty() {
        clauses.push((current, MorphologicalBoundary::DeliveryObstruction));
    }
    clauses
}

fn lineage_fiber(
    identity: &str,
    receiver: u64,
) -> Result<ReceiverFiberIdentity, MorphologicalLanguageError> {
    named_fiber(MORPH_SOURCE_SCHEMA, identity, receiver)
}

fn passage_fiber(
    identity: &str,
    receiver: u64,
) -> Result<ReceiverFiberIdentity, MorphologicalLanguageError> {
    named_fiber(MORPH_PASSAGE_SCHEMA, identity, receiver)
}

fn clause_fiber(
    identity: &str,
    receiver: u64,
) -> Result<ReceiverFiberIdentity, MorphologicalLanguageError> {
    named_fiber(MORPH_CLAUSE_SCHEMA, identity, receiver)
}

fn named_fiber(
    schema: u64,
    identity: &str,
    receiver: u64,
) -> Result<ReceiverFiberIdentity, MorphologicalLanguageError> {
    let extent =
        u64::try_from(identity.len()).map_err(|_| MorphologicalLanguageError::CarrierExtent)?;
    let mut bytes = Vec::with_capacity(16 + identity.len());
    bytes.extend_from_slice(&receiver.to_le_bytes());
    bytes.extend_from_slice(&extent.to_le_bytes());
    bytes.extend_from_slice(identity.as_bytes());
    Ok(fiber_from_bytes(schema, &bytes))
}

fn mark_germs(surface: &str) -> Result<Vec<ResonanceGerm>, MorphologicalLanguageError> {
    let phase = RelationAtom::new(Cog::lit(1)).ok_or(MorphologicalLanguageError::CarrierExtent)?;
    Ok(surface
        .chars()
        .map(|mark| {
            ResonanceGerm::new(
                fiber_from_bytes(MORPH_MARK_SCHEMA, mark.to_string().as_bytes()),
                phase,
            )
        })
        .collect())
}

fn fiber_text(identity: &ReceiverFiberIdentity) -> Option<String> {
    if identity.words().len() < 2 {
        return None;
    }
    let extent =
        usize::try_from(u64::from(identity.words()[0]) | (u64::from(identity.words()[1]) << 32))
            .ok()?;
    let mut bytes = Vec::new();
    for word in &identity.words()[2..] {
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    (extent <= bytes.len())
        .then(|| {
            bytes.truncate(extent);
            String::from_utf8(bytes).ok()
        })
        .flatten()
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ReturnedSeamCandidate {
    pub(super) reversed: bool,
    prefix_at: usize,
    suffix_at: usize,
    extent: usize,
    lexical_horizon: u32,
    mark_horizon: u32,
    surface_mark_extent: usize,
    causal_passages: BTreeSet<String>,
    supporting_clauses: BTreeSet<String>,
}

pub(super) fn returned_seam_dominates(
    left: &ReturnedSeamCandidate,
    right: &ReturnedSeamCandidate,
) -> bool {
    left.lexical_horizon >= right.lexical_horizon
        && left.mark_horizon >= right.mark_horizon
        && left.surface_mark_extent >= right.surface_mark_extent
        && right.causal_passages.is_subset(&left.causal_passages)
        && right.supporting_clauses.is_subset(&left.supporting_clauses)
        && (left.lexical_horizon > right.lexical_horizon
            || left.mark_horizon > right.mark_horizon
            || left.surface_mark_extent > right.surface_mark_extent
            || left.causal_passages != right.causal_passages
            || left.supporting_clauses != right.supporting_clauses)
}

pub(super) fn collect_oriented_returned_seams(
    prefix: &MorphologicalGeneratedCurrent,
    suffix: &MorphologicalGeneratedCurrent,
    reversed: bool,
    maximum_observed_tokens: usize,
    seams: &mut Vec<ReturnedSeamCandidate>,
) -> Result<(), MorphologicalLanguageError> {
    let prefix_surface = prefix
        .tokens
        .iter()
        .map(|token| token.token.as_str())
        .collect::<Vec<_>>();
    let suffix_surface = suffix
        .tokens
        .iter()
        .map(|token| token.token.as_str())
        .collect::<Vec<_>>();
    for (prefix_at, prefix_token) in prefix.tokens.iter().enumerate() {
        if prefix_at == 0 || !prefix_token.token.chars().any(char::is_alphanumeric) {
            continue;
        }
        for (suffix_at, suffix_token) in suffix.tokens.iter().enumerate() {
            if prefix_token.token != suffix_token.token
                || suffix_at
                    .checked_add(1)
                    .is_none_or(|next| next >= suffix.tokens.len())
                || !suffix.tokens[suffix_at + 1..]
                    .iter()
                    .any(|token| token.token.chars().any(char::is_alphanumeric))
            {
                continue;
            }
            let extent = prefix_at
                .checked_add(1)
                .and_then(|prefix_extent| {
                    prefix_extent.checked_add(suffix.tokens.len() - suffix_at - 1)
                })
                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
            if extent > maximum_observed_tokens {
                continue;
            }
            let composite_surface = prefix_surface[..=prefix_at]
                .iter()
                .copied()
                .chain(suffix_surface[suffix_at + 1..].iter().copied())
                .collect::<Vec<_>>();
            if composite_surface == prefix_surface || composite_surface == suffix_surface {
                continue;
            }
            let composite_tokens = prefix.tokens[..=prefix_at]
                .iter()
                .chain(&suffix.tokens[suffix_at + 1..]);
            let mut causal_passages = BTreeSet::new();
            let mut supporting_clauses = BTreeSet::new();
            for token in composite_tokens {
                causal_passages.extend(token.caused_passages.iter().cloned());
                supporting_clauses.extend(token.supporting_clauses.iter().cloned());
            }
            seams.push(ReturnedSeamCandidate {
                reversed,
                prefix_at,
                suffix_at,
                extent,
                lexical_horizon: prefix_token
                    .lexical_horizons
                    .iter()
                    .chain(&suffix_token.lexical_horizons)
                    .copied()
                    .max()
                    .unwrap_or(0),
                mark_horizon: prefix_token
                    .forward_mark_horizon
                    .max(prefix_token.reverse_mark_horizon)
                    .max(suffix_token.forward_mark_horizon)
                    .max(suffix_token.reverse_mark_horizon),
                surface_mark_extent: prefix_token.token.chars().count(),
                causal_passages,
                supporting_clauses,
            });
        }
    }
    Ok(())
}

pub(super) fn materialize_oriented_returned_seam(
    prefix: &MorphologicalGeneratedCurrent,
    suffix: &MorphologicalGeneratedCurrent,
    selected: &ReturnedSeamCandidate,
    admissible_seam_population: usize,
    materialized_seam_population: usize,
) -> Result<MorphologicalGeneratedCurrent, MorphologicalLanguageError> {
    let prefix_token = prefix
        .tokens
        .get(selected.prefix_at)
        .ok_or(MorphologicalLanguageError::MalformedFiber)?;
    let suffix_token = suffix
        .tokens
        .get(selected.suffix_at)
        .ok_or(MorphologicalLanguageError::MalformedFiber)?;
    let mut tokens = prefix.tokens[..=selected.prefix_at].to_vec();
    let seam_sources = {
        let seam = tokens
            .last_mut()
            .ok_or(MorphologicalLanguageError::MalformedFiber)?;
        seam.transport = MorphologicalTransport::RecurrentLexical;
        seam.lexical_horizons
            .extend(suffix_token.lexical_horizons.iter().copied());
        seam.forward_mark_horizon = seam
            .forward_mark_horizon
            .max(suffix_token.forward_mark_horizon);
        seam.reverse_mark_horizon = seam
            .reverse_mark_horizon
            .max(suffix_token.reverse_mark_horizon);
        seam.recurrent_sources
            .extend(suffix_token.recurrent_sources.iter().cloned());
        seam.recurrent_context_sources
            .extend(suffix_token.recurrent_context_sources.iter().cloned());
        seam.recurrent_context_sources
            .extend(prefix_token.caused_sources.iter().cloned());
        seam.recurrent_context_sources
            .extend(suffix_token.caused_sources.iter().cloned());
        seam.caused_sources
            .extend(suffix_token.caused_sources.iter().cloned());
        seam.caused_passages
            .extend(suffix_token.caused_passages.iter().cloned());
        seam.supporting_clauses
            .extend(suffix_token.supporting_clauses.iter().cloned());
        seam.caused_sources.clone()
    };

    let suffix_start = tokens.len();
    tokens.extend(suffix.tokens[selected.suffix_at + 1..].iter().cloned());
    if let Some(first_suffix) = tokens.get_mut(suffix_start) {
        first_suffix.recurrent_context_sources.extend(seam_sources);
    }
    for (emitted_at, token) in tokens.iter_mut().enumerate() {
        token.returned_event_count = emitted_at
            .checked_add(1)
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
    }
    if tokens.len() != selected.extent {
        return Err(MorphologicalLanguageError::MalformedFiber);
    }
    let phase = compose_returned_phase(prefix, suffix, &tokens)?;
    let mut caused_seams = prefix
        .caused_seams
        .iter()
        .chain(&suffix.caused_seams)
        .cloned()
        .collect::<BTreeSet<_>>();
    caused_seams.insert(MorphologicalCausedSeam {
        surface: prefix_token.token.clone(),
        prefix_emitted_at: selected.prefix_at,
        suffix_emitted_at: selected.suffix_at,
        prefix_sources: prefix_token.caused_sources.clone(),
        suffix_sources: suffix_token.caused_sources.clone(),
        prefix_passages: prefix_token.caused_passages.clone(),
        suffix_passages: suffix_token.caused_passages.clone(),
        admissible_seam_population,
        materialized_seam_population,
    });
    let (support_conduct, supporting_sources) = MorphologicalSupportConduct::of(&tokens);
    Ok(MorphologicalGeneratedCurrent {
        text: render_tokens(tokens.iter().map(|token| token.token.as_str())),
        tokens,
        phases: vec![phase],
        rest: MorphologicalResponseRest::Closed,
        caused_seams: caused_seams.into_iter().collect(),
        support_conduct,
        supporting_sources,
    })
}

fn compose_returned_phase(
    prefix: &MorphologicalGeneratedCurrent,
    suffix: &MorphologicalGeneratedCurrent,
    emitted: &[MorphologicalGeneratedToken],
) -> Result<MorphologicalResponsePhase, MorphologicalLanguageError> {
    let prefix_entry = prefix
        .phases
        .first()
        .ok_or(MorphologicalLanguageError::MalformedFiber)?;
    let suffix_return = suffix
        .phases
        .last()
        .ok_or(MorphologicalLanguageError::MalformedFiber)?;
    if suffix_return.boundary != Some(MorphologicalBoundary::Sentence) {
        return Err(MorphologicalLanguageError::MalformedFiber);
    }
    let emitted_surfaces = emitted
        .iter()
        .filter(|token| token.token.chars().any(char::is_alphanumeric))
        .map(|token| token.token.to_lowercase())
        .collect::<BTreeSet<_>>();
    let clauses = emitted
        .iter()
        .flat_map(|token| token.supporting_clauses.iter().cloned())
        .collect::<BTreeSet<_>>();
    let sources = emitted
        .iter()
        .flat_map(|token| token.caused_sources.iter().cloned())
        .collect::<BTreeSet<_>>();
    let passages = emitted
        .iter()
        .flat_map(|token| token.caused_passages.iter().cloned())
        .collect::<BTreeSet<_>>();
    let mut discharged_regions = BTreeMap::<usize, BTreeSet<usize>>::new();
    let mut discharged_features = BTreeMap::<usize, BTreeSet<String>>::new();
    let mut entry_lexical_horizons = BTreeSet::new();
    let mut entry_recurrence_multiplicities = BTreeSet::new();
    for phase in prefix.phases.iter().chain(&suffix.phases) {
        for (obligation, regions) in &phase.discharged_regions {
            discharged_regions
                .entry(*obligation)
                .or_default()
                .extend(regions.iter().copied());
        }
        for (obligation, features) in &phase.discharged_features {
            discharged_features.entry(*obligation).or_default().extend(
                features
                    .iter()
                    .filter(|feature| emitted_surfaces.contains(*feature))
                    .cloned(),
            );
        }
        entry_lexical_horizons.extend(phase.entry_lexical_horizons.iter().copied());
        entry_recurrence_multiplicities
            .extend(phase.entry_recurrence_multiplicities.iter().copied());
    }
    discharged_features.retain(|_, features| !features.is_empty());
    discharged_regions.retain(|obligation, _| discharged_features.contains_key(obligation));
    let discharged_obligations = discharged_features.keys().copied().collect();
    Ok(MorphologicalResponsePhase {
        entry_clause: prefix_entry.entry_clause.clone(),
        clauses,
        sources,
        passages,
        boundary: suffix_return.boundary,
        discharged_obligations,
        discharged_regions,
        discharged_features,
        entry_lexical_horizons,
        entry_recurrence_multiplicities,
        emitted_start: 0,
        emitted_end: emitted.len(),
    })
}

pub(super) fn receive_question(
    prompt: &[String],
    action: ActionCurrent,
    worker_threads: usize,
) -> Result<ResonanceEcology, MorphologicalLanguageError> {
    let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
    receive_question_with_executor(prompt, action, &mut host)
}

/// Receive the outer question through one caller-retained physical executor. The executor crosses
/// the question's Swing event; selecting a card at the outer language boundary cannot silently
/// construct a private host executor here.
pub(super) fn receive_question_with_executor(
    prompt: &[String],
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<ResonanceEcology, MorphologicalLanguageError> {
    let machine = LiveCurrentMachine::new(
        SparseStandingSurface::empty_rank(10)
            .map_err(|_| MorphologicalLanguageError::CarrierExtent)?,
    );
    let mut ecology = ResonanceEcology::new(machine);
    let occurrence = ResonanceOccurrence::probe(0, token_germs(prompt)?)?;
    ecology.receive_with(&occurrence, action, executor)?;
    Ok(ecology)
}

pub(super) fn materialize_generated_current_live(
    prompt: &[String],
    returned_question: ResonanceEcology,
    current: MorphologicalGeneratedCurrent,
    action: ActionCurrent,
    worker_threads: usize,
) -> Result<MorphologicalGeneratedText, MorphologicalLanguageError> {
    let returned_rest = materialize_returned_path_live(
        returned_question,
        prompt,
        current.tokens.iter().map(|token| token.token.as_str()),
        action,
        worker_threads,
    )?;
    Ok(MorphologicalGeneratedText {
        text: current.text,
        tokens: current.tokens,
        phases: current.phases,
        rest: current.rest,
        caused_seams: current.caused_seams,
        returned_rest,
    })
}

/// Carry the selected current back through the same live question body on one caller-retained
/// physical executor. The question event and every self-emanated return cross the same executor,
/// so a mounted card is not silently abandoned between reception and emanation.
pub(super) fn materialize_generated_current_live_with_executor(
    prompt: &[String],
    returned_question: ResonanceEcology,
    current: MorphologicalGeneratedCurrent,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<MorphologicalGeneratedText, MorphologicalLanguageError> {
    let returned_rest = materialize_returned_path_live_with_executor(
        returned_question,
        prompt,
        current.tokens.iter().map(|token| token.token.as_str()),
        action,
        executor,
    )?;
    Ok(MorphologicalGeneratedText {
        text: current.text,
        tokens: current.tokens,
        phases: current.phases,
        rest: current.rest,
        caused_seams: current.caused_seams,
        returned_rest,
    })
}

pub(super) fn materialize_returned_path_live<'a>(
    ecology: ResonanceEcology,
    prompt: &[String],
    generated: impl IntoIterator<Item = &'a str>,
    action: ActionCurrent,
    worker_threads: usize,
) -> Result<ResonanceEcologyRestImage, MorphologicalLanguageError> {
    let mut host = ParallelHostLiveCurrentExecutor::new(worker_threads.max(1));
    materialize_returned_path_live_with_executor(ecology, prompt, generated, action, &mut host)
}

/// Re-enter every generated event as self-emanated cause through one caller-retained physical
/// executor. Each returned event crosses the supplied executor; the emanation path cannot select a
/// private host pool behind a caller which already mounted one.
pub(super) fn materialize_returned_path_live_with_executor<'a>(
    mut ecology: ResonanceEcology,
    prompt: &[String],
    generated: impl IntoIterator<Item = &'a str>,
    action: ActionCurrent,
    executor: &mut dyn LiveCurrentExecutor,
) -> Result<ResonanceEcologyRestImage, MorphologicalLanguageError> {
    let mut predecessor = prompt.last().cloned().unwrap_or_default();
    for (generated_at, generated) in generated.into_iter().enumerate() {
        let source_order = u64::try_from(generated_at)
            .map_err(|_| MorphologicalLanguageError::CarrierExtent)?
            .checked_add(1)
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        let germs = token_germs(&[predecessor, generated.to_owned()])?;
        let occurrence = ResonanceOccurrence::self_emanated(source_order, germs)?;
        ecology.receive_with(&occurrence, action, executor)?;
        predecessor = generated.to_owned();
    }
    Ok(ecology.rest_image()?)
}

// -------------------------------------------------------------------------------------------------
// The generation front's KEY LAW
// -------------------------------------------------------------------------------------------------
//
// **This organ supplies a key; it does not grow a carrier.** `holonic_engine::cuda_refine` owns the
// exact quotient — the identity of `(class, key)` — with a host chart and a device chart proved to
// return the same partition. What belongs here is only what a generation state carries, and that is
// this organ's material.
//
// Brandon, 2026-08-10: *"why the fuck do you think you have a choice about 'paths'… why is this not
// ontologically integrated → encapsulation and factored in the codebase."* A device path per organ
// is the cabinet-of-organs failure one level down.
//
// # Why the key is per FIELD, and why that is exact rather than a compromise
//
// A `MorphologicalCurrentState` is `Ord` over four fields. A single 64-bit key would have to be a
// hash of the whole state, and a hash makes identity **probabilistic** — inadmissible: two distinct
// states colliding would glue two currents that no receiver said were the same.
//
// So each field's distinct values are given dense identities, and the state population is refined
// **one field at a time** through the shared law. After the last field the classes are exactly the
// distinct states, by construction: two states share a class iff they agreed on every field. No
// hash, no packing ceiling, no number chosen — and each pass is a `(class, key)` quotient, which is
// what a chart enacts.

/// Which field of a generation state a refinement pass keys on. The order is declared and does not
/// change the partition — refining by `A` then `B` and by `B` then `A` reach the same equivalence —
/// but a stated order makes a run reproducible.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum StateField {
    Reflection,
    ActivePhase,
    OpenFaces,
    Rest,
}

impl StateField {
    pub(super) const DECLARED: [StateField; 4] = [
        StateField::Reflection,
        StateField::ActivePhase,
        StateField::OpenFaces,
        StateField::Rest,
    ];
}

/// **The material: one exact key per state, on one declared field.**
///
/// Identities are dense and assigned in the population's own order, so the key is exact and the
/// law's `u64` is never a hash.
fn state_field_keys(states: &[&MorphologicalCurrentState], field: StateField) -> Vec<u64> {
    // Each arm keys on a distinct field, so the identity maps cannot be shared.
    macro_rules! dense {
        ($project:expr) => {{
            let mut seen = BTreeMap::new();
            let mut keys = Vec::with_capacity(states.len());
            for state in states {
                let value = $project(*state);
                let next = seen.len() as u64 + 1;
                keys.push(*seen.entry(value).or_insert(next));
            }
            keys
        }};
    }
    match field {
        StateField::Reflection => dense!(|state: &MorphologicalCurrentState| state
            .reflection
            .clone()),
        StateField::ActivePhase => dense!(|state: &MorphologicalCurrentState| state
            .active_phase
            .clone()),
        StateField::OpenFaces => dense!(|state: &MorphologicalCurrentState| (*state.open_faces)
            .clone()),
        StateField::Rest => dense!(|state: &MorphologicalCurrentState| state.rest.clone()),
    }
}

/// **The generation front, quotiented through the shared law.**
///
/// Returns the dense class of every state. Two states share a class exactly when they are equal —
/// which is the relation `insert_generation_state`'s `BTreeMap` realizes by identity — reached here
/// as four `(class, key)` passes, each of which a chart can enact.
pub(super) fn quotient_generation_states(
    states: &[&MorphologicalCurrentState],
) -> Vec<u32> {
    let mut classes = vec![1u32; states.len()];
    for field in StateField::DECLARED {
        let keys = state_field_keys(states, field);
        classes = holonic_engine::cuda_refine::quotient_on_host(&classes, &keys).cell_class;
    }
    classes
}
