//! Exact factorized suffix ecology for finite ordered germ paths.
//!
//! The ecology is a generalized suffix automaton: at most two states are founded per received
//! germ or path boundary, while suffix links carry a receiver question between context scales.
//! Generation returns the plural material branches exposed along the complete non-root suffix
//! frontier. Repeated path testimony remains exact recurrence multiplicity on the supporting
//! transport. The ecology never enumerates the substring powerset, assigns probabilities, or
//! selects a single longest-context answer.

use std::collections::{BTreeMap, BTreeSet};

use body::num::COG_WORDS;
use holonic_structure::{
    FrozenRelationAtlas, FrozenRelationBuilder, LocalRelations, LocalSequence, LocalSet,
    RelationAtlasError, RelationSpan,
};
use soma_abi::active::RelationAtom;
use soma_membrane::ReceiverFiberIdentity;

use crate::resonance_ecology::ResonanceGerm;

const WIRE_MAGIC: u32 = 0x5355_4646;
const WIRE_VERSION: u32 = 2;
const HEADER_WORDS: usize = 4;
const STATE_HEADER_WORDS: usize = 9;
const LABELED_WIRE_MAGIC: u32 = 0x5355_464c;
const LABELED_WIRE_VERSION: u32 = 3;
const LABELED_HEADER_WORDS: usize = 10;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactSuffixEcologyError {
    EmptyEcology,
    EmptyPath,
    CarrierExtent,
    InvalidWire,
}

impl From<RelationAtlasError> for ExactSuffixEcologyError {
    fn from(error: RelationAtlasError) -> Self {
        match error {
            RelationAtlasError::Extent | RelationAtlasError::Reservation => Self::CarrierExtent,
            RelationAtlasError::InvalidSpan => Self::InvalidWire,
        }
    }
}

/// One source-lineage label carried by a recurrent suffix state. The label is not an automaton
/// address and does not select a continuation; it says which caused source paths contain the
/// represented end-position class.
pub type SuffixSourceLabel = ReceiverFiberIdentity;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct GermKey {
    identity: ReceiverFiberIdentity,
    phase: [u32; COG_WORDS],
}

impl GermKey {
    fn from_germ(germ: &ResonanceGerm) -> Self {
        Self {
            identity: germ.identity().clone(),
            phase: germ.phase().words(),
        }
    }

    fn germ(&self) -> Result<ResonanceGerm, ExactSuffixEcologyError> {
        let phase =
            RelationAtom::from_words(self.phase).ok_or(ExactSuffixEcologyError::InvalidWire)?;
        Ok(ResonanceGerm::new(self.identity.clone(), phase))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SuffixSymbol {
    Boundary(u64),
    Germ(GermKey),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SuffixState {
    maximum_length: usize,
    suffix: Option<usize>,
    material_end_multiplicity: u64,
    transitions: RelationSpan,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SuffixBuilderState {
    maximum_length: usize,
    suffix: Option<usize>,
    material_end_multiplicity: u64,
    transitions: LocalRelations<SuffixSymbol, usize>,
}

impl SuffixBuilderState {
    fn root() -> Self {
        Self {
            maximum_length: 0,
            suffix: None,
            material_end_multiplicity: 0,
            transitions: LocalRelations::new(),
        }
    }

    fn new(maximum_length: usize) -> Self {
        Self {
            maximum_length,
            suffix: None,
            material_end_multiplicity: 0,
            transitions: LocalRelations::new(),
        }
    }
}

struct SuffixEcologyBuilder {
    states: Vec<SuffixBuilderState>,
}

/// A suffix-scale receiver reached by the question.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SuffixContext {
    state: u32,
    matched_length: u32,
}

impl SuffixContext {
    pub const fn state(self) -> u32 {
        self.state
    }

    pub const fn matched_length(self) -> u32 {
        self.matched_length
    }
}

/// Exact local current carried by one received path through this suffix ecology. The state is a
/// receiver-local address, not a serialized copy of the path or an absolute language state.
/// Carrying one later germ advances this current directly, so generation need not rescan the
/// complete received chronology after every return.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExactSuffixCurrent {
    state: u32,
    matched_length: u32,
}

impl ExactSuffixCurrent {
    const fn root() -> Self {
        Self {
            state: 0,
            matched_length: 0,
        }
    }

    pub const fn state(self) -> u32 {
        self.state
    }

    pub const fn matched_length(self) -> u32 {
        self.matched_length
    }
}

/// An exact transport from a reached suffix-scale receiver into an emitted branch.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SuffixBranchSupport {
    state: u32,
    matched_length: u32,
    target_state: u32,
    recurrence_multiplicity: u64,
}

impl SuffixBranchSupport {
    pub const fn state(self) -> u32 {
        self.state
    }

    pub const fn matched_length(self) -> u32 {
        self.matched_length
    }

    pub const fn target_state(self) -> u32 {
        self.target_state
    }

    pub const fn recurrence_multiplicity(self) -> u64 {
        self.recurrence_multiplicity
    }
}

/// A possible next germ together with every context-scale transport which exposed it. Equal
/// visible germs remain one branch while their distinct supporting receiver paths stay explicit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSuffixBranch {
    germ: ResonanceGerm,
    supports: BTreeSet<SuffixBranchSupport>,
}

impl ExactSuffixBranch {
    pub const fn germ(&self) -> &ResonanceGerm {
        &self.germ
    }

    pub fn supports(&self) -> &BTreeSet<SuffixBranchSupport> {
        &self.supports
    }
}

/// Complete plural generative face of an ordered receiver question.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSuffixEmanation {
    longest_state: u32,
    longest_matched_length: u32,
    contexts: Vec<SuffixContext>,
    branches: Vec<ExactSuffixBranch>,
}

impl ExactSuffixEmanation {
    pub const fn longest_state(&self) -> u32 {
        self.longest_state
    }

    pub const fn longest_matched_length(&self) -> u32 {
        self.longest_matched_length
    }

    pub fn contexts(&self) -> &[SuffixContext] {
        &self.contexts
    }

    pub fn branches(&self) -> &[ExactSuffixBranch] {
        &self.branches
    }

    /// Greatest reached context which actually has an outgoing material transport. A longer
    /// terminal context may remain present while its next lawful passage occurs through a shorter
    /// recurrent restriction.
    pub fn greatest_productive_matched_length(&self) -> Option<u32> {
        self.branches
            .iter()
            .flat_map(|branch| branch.supports.iter())
            .map(|support| support.matched_length)
            .max()
    }
}

/// One visible suffix continuation together with every caused source path which contains the
/// transition. Equal visible material remains one branch; plural lineage is retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactLabeledSuffixBranch {
    branch: ExactSuffixBranch,
    sources: LocalSet<SuffixSourceLabel>,
    support_sources: LocalRelations<SuffixBranchSupport, LocalSet<SuffixSourceLabel>>,
    support_context_sources: LocalRelations<SuffixBranchSupport, LocalSet<SuffixSourceLabel>>,
}

impl ExactLabeledSuffixBranch {
    pub const fn branch(&self) -> &ExactSuffixBranch {
        &self.branch
    }

    pub const fn sources(&self) -> &LocalSet<SuffixSourceLabel> {
        &self.sources
    }

    /// Exact source incidence of one particular suffix-scale transport. `sources()` is the
    /// visible branch's complete plural lineage; this finer receipt prevents an observer from
    /// combining a short-context source with an unrelated long-context support merely because
    /// both expose the same germ.
    pub fn sources_for_support(
        &self,
        support: &SuffixBranchSupport,
    ) -> Option<&LocalSet<SuffixSourceLabel>> {
        self.support_sources.get(support)
    }

    /// Exact source incidence of the reached context before this support crosses into its target.
    /// A current source may cross to a different target source only when both meet in this
    /// context fiber.
    pub fn context_sources_for_support(
        &self,
        support: &SuffixBranchSupport,
    ) -> Option<&LocalSet<SuffixSourceLabel>> {
        self.support_context_sources.get(support)
    }
}

/// Plural generative face of a query in a source-lineaged suffix ecology.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactLabeledSuffixEmanation {
    emanation: ExactSuffixEmanation,
    branches: Vec<ExactLabeledSuffixBranch>,
}

impl ExactLabeledSuffixEmanation {
    pub const fn emanation(&self) -> &ExactSuffixEmanation {
        &self.emanation
    }

    pub fn branches(&self) -> &[ExactLabeledSuffixBranch] {
        &self.branches
    }
}

/// One query-independent material transport in a source-lineaged suffix ecology. The local
/// receiver states and the complete germ presentation identify the edge. Match horizon and
/// recurrence multiplicity are testimony about a later encounter; neither is promoted into the
/// transport's identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExactLabeledSuffixMaterialEdge {
    context_state: u32,
    germ_identity: ReceiverFiberIdentity,
    germ_phase: [u32; COG_WORDS],
    target_state: u32,
    recurrence_multiplicity: u64,
    sources: LocalSet<SuffixSourceLabel>,
    context_sources: LocalSet<SuffixSourceLabel>,
}

impl ExactLabeledSuffixMaterialEdge {
    pub const fn context_state(&self) -> u32 {
        self.context_state
    }

    pub const fn germ_identity(&self) -> &ReceiverFiberIdentity {
        &self.germ_identity
    }

    pub const fn germ_phase(&self) -> [u32; COG_WORDS] {
        self.germ_phase
    }

    pub const fn target_state(&self) -> u32 {
        self.target_state
    }

    pub const fn recurrence_multiplicity(&self) -> u64 {
        self.recurrence_multiplicity
    }

    pub const fn sources(&self) -> &LocalSet<SuffixSourceLabel> {
        &self.sources
    }

    pub const fn context_sources(&self) -> &LocalSet<SuffixSourceLabel> {
        &self.context_sources
    }

    pub fn germ(&self) -> Result<ResonanceGerm, ExactSuffixEcologyError> {
        GermKey {
            identity: self.germ_identity.clone(),
            phase: self.germ_phase,
        }
        .germ()
    }
}

/// A finite exact suffix-state ecology derived from ordered germ paths. Outer path delivery is
/// canonicalized; chronology inside every path remains physical.
#[derive(Debug, PartialEq, Eq)]
pub struct ExactSuffixEcology {
    states: Vec<SuffixState>,
    transitions: FrozenRelationAtlas<SuffixSymbol, usize>,
    material_transitions: usize,
}

/// One exact receiver-local interval in the suffix-link lineage tree.
///
/// Every material occurrence has one caused source.  A recurrent suffix state receives precisely
/// the occurrences in its descendant interval; the source face is therefore reconstructed by
/// carrying through that interval rather than copied into a rectangular state-by-source matrix.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct SourceSpan {
    start: u64,
    len: u64,
}

/// Compact exact incidence into one canonical source catalogue.
///
/// Suffix links form a rooted tree. A depth-first order makes every state's complete descendant
/// population contiguous, so one span per state plus one source index per caused material
/// occurrence retains the same exact lineage as a propagated bitmap. Storage is
/// `O(states + caused occurrences)`; it does not allocate `states * sources` empty cells.
#[derive(Debug, PartialEq, Eq)]
struct SourceIncidence {
    state_spans: Box<[SourceSpan]>,
    occurrence_sources: Box<[u32]>,
}

impl SourceIncidence {
    fn from_suffix_tree<S, F>(
        state_count: usize,
        mut suffix_of: S,
        mut append_direct_sources: F,
    ) -> Result<Self, ExactSuffixEcologyError>
    where
        S: FnMut(usize) -> Option<usize>,
        F: FnMut(usize, &mut LocalSequence<u32>) -> Result<(), ExactSuffixEcologyError>,
    {
        if state_count == 0 || suffix_of(0).is_some() {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let mut first_child = LocalSequence::with_capacity(state_count);
        first_child.resize_with(state_count, || None);
        let mut next_sibling = LocalSequence::with_capacity(state_count);
        next_sibling.resize_with(state_count, || None);
        for state in 1..state_count {
            let parent = suffix_of(state)
                .filter(|parent| *parent < state_count && *parent != state)
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            next_sibling[state] = first_child[parent];
            first_child[parent] = Some(state);
        }

        let mut spans = LocalSequence::with_capacity(state_count);
        spans.resize_with(state_count, SourceSpan::default);
        let mut occurrences = LocalSequence::new();
        append_direct_sources(0, &mut occurrences)?;
        let root_start =
            u64::try_from(occurrences.len()).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        // The root's direct population is necessarily empty for a conditioned suffix ecology.
        if root_start != 0 {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let mut stack = LocalSequence::from([(0usize, first_child[0], 0u64)]);
        while let Some((state, next_child, start)) = stack.last_mut() {
            if let Some(child) = *next_child {
                *next_child = next_sibling[child];
                let child_start = u64::try_from(occurrences.len())
                    .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
                append_direct_sources(child, &mut occurrences)?;
                stack.push((child, first_child[child], child_start));
                continue;
            }
            let end = u64::try_from(occurrences.len())
                .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
            spans[*state] = SourceSpan {
                start: *start,
                len: end
                    .checked_sub(*start)
                    .ok_or(ExactSuffixEcologyError::InvalidWire)?,
            };
            stack.pop();
        }
        Ok(Self {
            state_spans: spans.into_boxed_slice(),
            occurrence_sources: occurrences.into_boxed_slice(),
        })
    }

    fn validate(
        &self,
        states: &[SuffixState],
        source_count: usize,
    ) -> Result<(), ExactSuffixEcologyError> {
        if states.is_empty() || self.state_spans.len() != states.len() {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let occurrence_count = u64::try_from(self.occurrence_sources.len())
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        let root = self.state_spans[0];
        if root.start != 0 || root.len != occurrence_count {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        for (state, span) in self.state_spans.iter().copied().enumerate() {
            let end = span
                .start
                .checked_add(span.len)
                .filter(|end| *end <= occurrence_count)
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            if state == 0 {
                continue;
            }
            let parent = states[state]
                .suffix
                .filter(|parent| *parent < states.len() && *parent != state)
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let parent_span = self.state_spans[parent];
            let parent_end = parent_span
                .start
                .checked_add(parent_span.len)
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            if span.start < parent_span.start || end > parent_end {
                return Err(ExactSuffixEcologyError::InvalidWire);
            }
        }
        if self
            .occurrence_sources
            .iter()
            .any(|source| usize::try_from(*source).map_or(true, |source| source >= source_count))
        {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        Ok(())
    }

    fn labels(
        &self,
        state: usize,
        catalogue: &[SuffixSourceLabel],
    ) -> Result<LocalSet<SuffixSourceLabel>, ExactSuffixEcologyError> {
        let span = self
            .state_spans
            .get(state)
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let start =
            usize::try_from(span.start).map_err(|_| ExactSuffixEcologyError::InvalidWire)?;
        let len = usize::try_from(span.len).map_err(|_| ExactSuffixEcologyError::InvalidWire)?;
        let end = start
            .checked_add(len)
            .filter(|end| *end <= self.occurrence_sources.len())
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let mut labels = LocalSet::new();
        for source in &self.occurrence_sources[start..end] {
            labels.insert(
                catalogue
                    .get(
                        usize::try_from(*source)
                            .map_err(|_| ExactSuffixEcologyError::InvalidWire)?,
                    )
                    .ok_or(ExactSuffixEcologyError::InvalidWire)?
                    .clone(),
            );
        }
        Ok(labels)
    }
}

/// The same factorized suffix ecology with exact source support carried on every state. Source
/// lineage is a receiver face of recurrent material, not a boundary which confines generation to
/// one delivered path.
#[derive(Debug, PartialEq, Eq)]
pub struct ExactLabeledSuffixEcology {
    ecology: ExactSuffixEcology,
    source_catalogue: Vec<SuffixSourceLabel>,
    source_incidence: SourceIncidence,
}

impl ExactSuffixEcology {
    pub fn condition(paths: &[Vec<ResonanceGerm>]) -> Result<Self, ExactSuffixEcologyError> {
        let (ecology, _, _) = Self::condition_internal(paths, None)?;
        Ok(ecology)
    }

    fn condition_internal(
        paths: &[Vec<ResonanceGerm>],
        source_labels: Option<&[SuffixSourceLabel]>,
    ) -> Result<(Self, Vec<SuffixSourceLabel>, Option<SourceIncidence>), ExactSuffixEcologyError>
    {
        if paths.is_empty() {
            return Err(ExactSuffixEcologyError::EmptyEcology);
        }
        if source_labels.is_some_and(|labels| labels.len() != paths.len()) {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let source_catalogue = source_labels
            .map(|labels| labels.iter().cloned().collect::<BTreeSet<_>>())
            .unwrap_or_default()
            .into_iter()
            .collect::<Vec<_>>();
        let source_indices = source_catalogue
            .iter()
            .cloned()
            .enumerate()
            .map(|(at, source)| {
                Ok((
                    source,
                    u32::try_from(at).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
                ))
            })
            .collect::<Result<BTreeMap<_, _>, ExactSuffixEcologyError>>()?;
        let mut canonical = paths
            .iter()
            .enumerate()
            .map(|(path_at, path)| {
                if path.is_empty() {
                    return Err(ExactSuffixEcologyError::EmptyPath);
                }
                Ok((
                    path.iter().map(GermKey::from_germ).collect::<Vec<_>>(),
                    source_labels
                        .map(|labels| {
                            source_indices
                                .get(&labels[path_at])
                                .copied()
                                .ok_or(ExactSuffixEcologyError::InvalidWire)
                        })
                        .transpose()?,
                ))
            })
            .collect::<Result<Vec<_>, ExactSuffixEcologyError>>()?;
        canonical.sort_by(|left, right| left.cmp(right));

        let mut builder = SuffixEcologyBuilder {
            states: vec![SuffixBuilderState::root()],
        };
        let mut direct_sources = source_labels.map(|_| vec![None]);
        let mut last = 0usize;
        for (path_at, (path, source)) in canonical.into_iter().enumerate() {
            for germ in path {
                last = builder.extend(last, SuffixSymbol::Germ(germ))?;
                if let Some(direct_sources) = direct_sources.as_mut() {
                    direct_sources.resize(builder.states.len(), None);
                    if direct_sources[last]
                        .replace(source.ok_or(ExactSuffixEcologyError::InvalidWire)?)
                        .is_some()
                    {
                        return Err(ExactSuffixEcologyError::InvalidWire);
                    }
                }
                builder.states[last].material_end_multiplicity = builder.states[last]
                    .material_end_multiplicity
                    .checked_add(1)
                    .ok_or(ExactSuffixEcologyError::CarrierExtent)?;
            }
            let boundary =
                u64::try_from(path_at).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
            last = builder.extend(last, SuffixSymbol::Boundary(boundary))?;
            if let Some(direct_sources) = direct_sources.as_mut() {
                direct_sources.resize(builder.states.len(), None);
            }
        }
        let mut descending = (1..builder.states.len()).collect::<Vec<_>>();
        descending.sort_by_key(|state| {
            (
                core::cmp::Reverse(builder.states[*state].maximum_length),
                core::cmp::Reverse(*state),
            )
        });
        for &state in &descending {
            let suffix = builder.states[state]
                .suffix
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            builder.states[suffix].material_end_multiplicity = builder.states[suffix]
                .material_end_multiplicity
                .checked_add(builder.states[state].material_end_multiplicity)
                .ok_or(ExactSuffixEcologyError::CarrierExtent)?;
        }
        let source_incidence = direct_sources
            .as_ref()
            .map(|direct_sources| {
                SourceIncidence::from_suffix_tree(
                    builder.states.len(),
                    |state| builder.states[state].suffix,
                    |state, occurrences| {
                        if let Some(source) = direct_sources
                            .get(state)
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?
                        {
                            occurrences.push(*source);
                        }
                        Ok(())
                    },
                )
            })
            .transpose()?;
        let material_transitions = builder
            .states
            .iter()
            .map(|state| {
                state
                    .transitions
                    .iter()
                    .filter(|(symbol, _)| matches!(symbol, SuffixSymbol::Germ(_)))
                    .count()
            })
            .try_fold(0usize, |total, extent| {
                total
                    .checked_add(extent)
                    .ok_or(ExactSuffixEcologyError::CarrierExtent)
            })?;
        let ecology = builder.freeze(material_transitions)?;
        Ok((ecology, source_catalogue, source_incidence))
    }

    pub fn state_count(&self) -> usize {
        self.states.len()
    }

    pub const fn material_transition_count(&self) -> usize {
        self.material_transitions
    }

    pub fn material_occurrence_count(&self) -> u64 {
        self.states[0].material_end_multiplicity
    }

    /// Return the plural branch family along every non-root suffix context reached by the query.
    /// A context with no outgoing material remains present in `contexts`; it is not replaced by a
    /// fabricated root-level vocabulary distribution.
    pub fn emanate(
        &self,
        path: &[ResonanceGerm],
    ) -> Result<ExactSuffixEmanation, ExactSuffixEcologyError> {
        if path.is_empty() {
            return Err(ExactSuffixEcologyError::EmptyPath);
        }
        let current = self.receive_path(path)?;
        self.emanate_current(current)
    }

    /// Receive one nonempty chronology into one local suffix current. The returned current is the
    /// exact operative position from which later light may continue.
    pub fn receive_path(
        &self,
        path: &[ResonanceGerm],
    ) -> Result<ExactSuffixCurrent, ExactSuffixEcologyError> {
        if path.is_empty() {
            return Err(ExactSuffixEcologyError::EmptyPath);
        }
        let mut current = ExactSuffixCurrent::root();
        for germ in path {
            current = self.carry(current, germ)?;
        }
        Ok(current)
    }

    /// Carry one returned germ through the current suffix-local topology. This is the incremental
    /// counterpart of `receive_path`; it performs no scan of the prior chronology.
    pub fn carry(
        &self,
        current: ExactSuffixCurrent,
        germ: &ResonanceGerm,
    ) -> Result<ExactSuffixCurrent, ExactSuffixEcologyError> {
        let mut state =
            usize::try_from(current.state).map_err(|_| ExactSuffixEcologyError::InvalidWire)?;
        let mut matched_length = usize::try_from(current.matched_length)
            .map_err(|_| ExactSuffixEcologyError::InvalidWire)?;
        if state >= self.states.len() || matched_length > self.states[state].maximum_length {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let symbol = SuffixSymbol::Germ(GermKey::from_germ(germ));
        loop {
            if let Some(next) = self
                .transitions
                .get(self.states[state].transitions, &symbol)
                .copied()
            {
                state = next;
                matched_length = matched_length
                    .checked_add(1)
                    .ok_or(ExactSuffixEcologyError::CarrierExtent)?;
                break;
            }
            let Some(suffix) = self.states[state].suffix else {
                matched_length = 0;
                break;
            };
            state = suffix;
            matched_length = matched_length.min(self.states[state].maximum_length);
        }
        Ok(ExactSuffixCurrent {
            state: u32::try_from(state).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
            matched_length: u32::try_from(matched_length)
                .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
        })
    }

    /// Emanate from an already carried current. A returned germ which advances this current
    /// therefore changes the exact receiver frontier consulted by the next passage.
    pub fn emanate_current(
        &self,
        current: ExactSuffixCurrent,
    ) -> Result<ExactSuffixEmanation, ExactSuffixEcologyError> {
        let state =
            usize::try_from(current.state).map_err(|_| ExactSuffixEcologyError::InvalidWire)?;
        let matched_length = usize::try_from(current.matched_length)
            .map_err(|_| ExactSuffixEcologyError::InvalidWire)?;
        if state >= self.states.len() || matched_length > self.states[state].maximum_length {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let mut contexts = Vec::new();
        let mut branch_support = BTreeMap::<GermKey, BTreeSet<SuffixBranchSupport>>::new();
        let mut context_state = state;
        let mut context_length = matched_length;
        while context_state != 0 {
            let context = SuffixContext {
                state: u32::try_from(context_state)
                    .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
                matched_length: u32::try_from(context_length)
                    .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
            };
            contexts.push(context);
            for (symbol, target) in self
                .transitions
                .iter(self.states[context_state].transitions)?
            {
                if let SuffixSymbol::Germ(germ) = symbol {
                    let recurrence_multiplicity = self.states[*target].material_end_multiplicity;
                    if recurrence_multiplicity == 0 {
                        return Err(ExactSuffixEcologyError::InvalidWire);
                    }
                    let support = SuffixBranchSupport {
                        state: context.state,
                        matched_length: context.matched_length,
                        target_state: u32::try_from(*target)
                            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
                        recurrence_multiplicity,
                    };
                    branch_support
                        .entry(germ.clone())
                        .or_default()
                        .insert(support);
                }
            }
            let Some(suffix) = self.states[context_state].suffix else {
                break;
            };
            context_state = suffix;
            context_length = context_length.min(self.states[context_state].maximum_length);
        }
        let branches = branch_support
            .into_iter()
            .map(|(germ, supports)| {
                Ok(ExactSuffixBranch {
                    germ: germ.germ()?,
                    supports,
                })
            })
            .collect::<Result<Vec<_>, ExactSuffixEcologyError>>()?;
        Ok(ExactSuffixEmanation {
            longest_state: current.state,
            longest_matched_length: current.matched_length,
            contexts,
            branches,
        })
    }

    pub fn encode_native_words(&self) -> Result<Vec<u32>, ExactSuffixEcologyError> {
        let state_count =
            u64::try_from(self.states.len()).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        let mut words = vec![
            WIRE_MAGIC,
            WIRE_VERSION,
            state_count as u32,
            (state_count >> 32) as u32,
        ];
        for state in &self.states {
            let maximum_length = u64::try_from(state.maximum_length)
                .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
            let transition_count = state.transitions.len();
            let (suffix_present, suffix) = match state.suffix {
                Some(suffix) => (
                    1,
                    u64::try_from(suffix).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
                ),
                None => (0, 0),
            };
            words.extend([
                maximum_length as u32,
                (maximum_length >> 32) as u32,
                state.material_end_multiplicity as u32,
                (state.material_end_multiplicity >> 32) as u32,
                suffix_present,
                suffix as u32,
                (suffix >> 32) as u32,
                transition_count as u32,
                (transition_count >> 32) as u32,
            ]);
            for (symbol, target) in self.transitions.iter(state.transitions)? {
                let target =
                    u64::try_from(*target).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
                match symbol {
                    SuffixSymbol::Boundary(boundary) => {
                        words.extend([
                            0,
                            *boundary as u32,
                            (*boundary >> 32) as u32,
                            target as u32,
                            (target >> 32) as u32,
                        ]);
                    }
                    SuffixSymbol::Germ(germ) => {
                        let extent = u64::try_from(germ.identity.words().len())
                            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
                        words.extend([
                            1,
                            germ.identity.schema() as u32,
                            (germ.identity.schema() >> 32) as u32,
                            extent as u32,
                            (extent >> 32) as u32,
                        ]);
                        words.extend_from_slice(germ.identity.words());
                        words.extend(germ.phase);
                        words.extend([target as u32, (target >> 32) as u32]);
                    }
                }
            }
        }
        Ok(words)
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, ExactSuffixEcologyError> {
        let words = self.encode_native_words()?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(
                words
                    .len()
                    .checked_mul(core::mem::size_of::<u32>())
                    .ok_or(ExactSuffixEcologyError::CarrierExtent)?,
            )
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        for word in words {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        Ok(bytes)
    }

    pub fn from_native_words(words: &[u32]) -> Result<Self, ExactSuffixEcologyError> {
        if words.len() < HEADER_WORDS || words[0] != WIRE_MAGIC || words[1] != WIRE_VERSION {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let state_count = join_u64(words[2], words[3])
            .and_then(|count| usize::try_from(count).ok())
            .filter(|count| *count > 0)
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let mut cursor = HEADER_WORDS;
        let mut states = Vec::new();
        states
            .try_reserve_exact(state_count)
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        for _ in 0..state_count {
            let header_end = cursor
                .checked_add(STATE_HEADER_WORDS)
                .filter(|end| *end <= words.len())
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let maximum_length = join_u64(words[cursor], words[cursor + 1])
                .and_then(|value| usize::try_from(value).ok())
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let material_end_multiplicity = join_u64(words[cursor + 2], words[cursor + 3])
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let suffix_value = join_u64(words[cursor + 5], words[cursor + 6])
                .and_then(|value| usize::try_from(value).ok())
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let suffix = match words[cursor + 4] {
                0 if suffix_value == 0 => None,
                1 if suffix_value < state_count => Some(suffix_value),
                _ => return Err(ExactSuffixEcologyError::InvalidWire),
            };
            let transition_count = join_u64(words[cursor + 7], words[cursor + 8])
                .and_then(|value| usize::try_from(value).ok())
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            cursor = header_end;
            let mut transitions = LocalRelations::new();
            for _ in 0..transition_count {
                let kind = *words
                    .get(cursor)
                    .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                cursor += 1;
                let (symbol, target) = match kind {
                    0 => {
                        let end = cursor
                            .checked_add(4)
                            .filter(|end| *end <= words.len())
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        let boundary = join_u64(words[cursor], words[cursor + 1])
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        let target = join_u64(words[cursor + 2], words[cursor + 3])
                            .and_then(|value| usize::try_from(value).ok())
                            .filter(|target| *target < state_count)
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        cursor = end;
                        (SuffixSymbol::Boundary(boundary), target)
                    }
                    1 => {
                        let identity_header = cursor
                            .checked_add(4)
                            .filter(|end| *end <= words.len())
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        let schema = join_u64(words[cursor], words[cursor + 1])
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        let extent = join_u64(words[cursor + 2], words[cursor + 3])
                            .and_then(|value| usize::try_from(value).ok())
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        cursor = identity_header;
                        let identity_end = cursor
                            .checked_add(extent)
                            .filter(|end| *end <= words.len())
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        let identity = ReceiverFiberIdentity::new(
                            schema,
                            words[cursor..identity_end].to_vec(),
                        );
                        cursor = identity_end;
                        let row_end = cursor
                            .checked_add(COG_WORDS)
                            .and_then(|end| end.checked_add(2))
                            .filter(|end| *end <= words.len())
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        let phase: [u32; COG_WORDS] = words[cursor..cursor + COG_WORDS]
                            .try_into()
                            .map_err(|_| ExactSuffixEcologyError::InvalidWire)?;
                        if RelationAtom::from_words(phase).is_none() {
                            return Err(ExactSuffixEcologyError::InvalidWire);
                        }
                        cursor += COG_WORDS;
                        let target = join_u64(words[cursor], words[cursor + 1])
                            .and_then(|value| usize::try_from(value).ok())
                            .filter(|target| *target < state_count)
                            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                        cursor = row_end;
                        (SuffixSymbol::Germ(GermKey { identity, phase }), target)
                    }
                    _ => return Err(ExactSuffixEcologyError::InvalidWire),
                };
                if transitions.try_insert(symbol, target)?.is_some() {
                    return Err(ExactSuffixEcologyError::InvalidWire);
                }
            }
            states.push(SuffixBuilderState {
                maximum_length,
                suffix,
                material_end_multiplicity,
                transitions,
            });
        }
        if cursor != words.len()
            || states[0].maximum_length != 0
            || states[0].suffix.is_some()
            || states.iter().enumerate().skip(1).any(|(at, state)| {
                state.suffix.is_none()
                    || state.suffix == Some(at)
                    || state
                        .suffix
                        .is_some_and(|suffix| states[suffix].maximum_length >= state.maximum_length)
                    || state.transitions.iter().any(|(symbol, target)| {
                        matches!(symbol, SuffixSymbol::Germ(_))
                            && states[*target].material_end_multiplicity == 0
                    })
            })
        {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let material_transitions = states
            .iter()
            .map(|state| {
                state
                    .transitions
                    .iter()
                    .filter(|(symbol, _)| matches!(symbol, SuffixSymbol::Germ(_)))
                    .count()
            })
            .try_fold(0usize, |total, extent| total.checked_add(extent))
            .ok_or(ExactSuffixEcologyError::CarrierExtent)?;
        SuffixEcologyBuilder { states }.freeze(material_transitions)
    }

    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, ExactSuffixEcologyError> {
        if bytes.len() % core::mem::size_of::<u32>() != 0 {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let words = bytes
            .chunks_exact(core::mem::size_of::<u32>())
            .map(|row| u32::from_le_bytes([row[0], row[1], row[2], row[3]]))
            .collect::<Vec<_>>();
        Self::from_native_words(&words)
    }
}

impl SuffixEcologyBuilder {
    fn freeze(
        self,
        material_transitions: usize,
    ) -> Result<ExactSuffixEcology, ExactSuffixEcologyError> {
        let mut atlas = FrozenRelationBuilder::new();
        let mut states = Vec::new();
        states
            .try_reserve_exact(self.states.len())
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        for state in self.states {
            let transitions = atlas.try_append(&state.transitions)?;
            states.push(SuffixState {
                maximum_length: state.maximum_length,
                suffix: state.suffix,
                material_end_multiplicity: state.material_end_multiplicity,
                transitions,
            });
        }
        Ok(ExactSuffixEcology {
            states,
            transitions: atlas.finish(),
            material_transitions,
        })
    }

    fn extend(
        &mut self,
        last: usize,
        symbol: SuffixSymbol,
    ) -> Result<usize, ExactSuffixEcologyError> {
        let current_length = self.states[last]
            .maximum_length
            .checked_add(1)
            .ok_or(ExactSuffixEcologyError::CarrierExtent)?;
        let current = self.states.len();
        self.states.push(SuffixBuilderState::new(current_length));
        let mut cursor = Some(last);
        while let Some(state) = cursor {
            if self.states[state].transitions.contains(&symbol) {
                break;
            }
            self.states[state]
                .transitions
                .try_insert(symbol.clone(), current)?;
            cursor = self.states[state].suffix;
        }
        match cursor {
            None => self.states[current].suffix = Some(0),
            Some(state) => {
                let target = *self.states[state]
                    .transitions
                    .get(&symbol)
                    .ok_or(ExactSuffixEcologyError::InvalidWire)?;
                if self.states[state]
                    .maximum_length
                    .checked_add(1)
                    .ok_or(ExactSuffixEcologyError::CarrierExtent)?
                    == self.states[target].maximum_length
                {
                    self.states[current].suffix = Some(target);
                } else {
                    let clone = self.states.len();
                    let mut cloned = self.states[target].clone();
                    cloned.maximum_length = self.states[state]
                        .maximum_length
                        .checked_add(1)
                        .ok_or(ExactSuffixEcologyError::CarrierExtent)?;
                    cloned.material_end_multiplicity = 0;
                    self.states.push(cloned);
                    let mut rewrite = Some(state);
                    while let Some(at) = rewrite {
                        if self.states[at].transitions.get(&symbol).copied() != Some(target) {
                            break;
                        }
                        self.states[at]
                            .transitions
                            .try_insert(symbol.clone(), clone)?;
                        rewrite = self.states[at].suffix;
                    }
                    self.states[target].suffix = Some(clone);
                    self.states[current].suffix = Some(clone);
                }
            }
        }
        Ok(current)
    }
}

impl ExactLabeledSuffixEcology {
    /// Condition one exact source label per ordered path. Equal labels may lawfully occur on
    /// several delivery sections; path boundaries remain explicit while their common source
    /// lineage is retained.
    pub fn condition(
        paths: &[Vec<ResonanceGerm>],
        source_labels: &[SuffixSourceLabel],
    ) -> Result<Self, ExactSuffixEcologyError> {
        let (ecology, source_catalogue, source_incidence) =
            ExactSuffixEcology::condition_internal(paths, Some(source_labels))?;
        let source_incidence = source_incidence.ok_or(ExactSuffixEcologyError::InvalidWire)?;
        if source_incidence.state_spans.len() != ecology.states.len() {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        Ok(Self {
            ecology,
            source_catalogue,
            source_incidence,
        })
    }

    pub const fn ecology(&self) -> &ExactSuffixEcology {
        &self.ecology
    }

    pub fn state_sources(&self, state: u32) -> Option<LocalSet<SuffixSourceLabel>> {
        self.source_incidence
            .labels(usize::try_from(state).ok()?, &self.source_catalogue)
            .ok()
    }

    /// Return every material transport which a non-root recurrent receiver can expose, together
    /// with its exact target and context source faces. This is the stable ecology-owned atlas from
    /// which a later conduct deposit may be founded; it is not a query result and therefore does
    /// not carry a matched length or make recurrence multiplicity part of edge identity.
    pub fn material_edges(
        &self,
    ) -> Result<LocalSequence<ExactLabeledSuffixMaterialEdge>, ExactSuffixEcologyError> {
        let mut edges = LocalSequence::with_capacity(self.ecology.material_transitions);
        for context in 1..self.ecology.states.len() {
            for (symbol, target) in self
                .ecology
                .transitions
                .iter(self.ecology.states[context].transitions)?
            {
                let SuffixSymbol::Germ(germ) = symbol else {
                    continue;
                };
                let recurrence_multiplicity = self
                    .ecology
                    .states
                    .get(*target)
                    .ok_or(ExactSuffixEcologyError::InvalidWire)?
                    .material_end_multiplicity;
                if recurrence_multiplicity == 0 {
                    return Err(ExactSuffixEcologyError::InvalidWire);
                }
                edges.push(ExactLabeledSuffixMaterialEdge {
                    context_state: u32::try_from(context)
                        .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
                    germ_identity: germ.identity.clone(),
                    germ_phase: germ.phase,
                    target_state: u32::try_from(*target)
                        .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?,
                    recurrence_multiplicity,
                    sources: self
                        .source_incidence
                        .labels(*target, &self.source_catalogue)?,
                    context_sources: self
                        .source_incidence
                        .labels(context, &self.source_catalogue)?,
                });
            }
        }
        Ok(edges)
    }

    pub fn emanate(
        &self,
        path: &[ResonanceGerm],
    ) -> Result<ExactLabeledSuffixEmanation, ExactSuffixEcologyError> {
        let current = self.ecology.receive_path(path)?;
        self.emanate_current(current)
    }

    /// Receive one nonempty path into this labeled receiver ecology without retaining a second
    /// copy of the path.
    pub fn receive_path(
        &self,
        path: &[ResonanceGerm],
    ) -> Result<ExactSuffixCurrent, ExactSuffixEcologyError> {
        self.ecology.receive_path(path)
    }

    /// Advance a carried local current by one returned germ.
    pub fn carry(
        &self,
        current: ExactSuffixCurrent,
        germ: &ResonanceGerm,
    ) -> Result<ExactSuffixCurrent, ExactSuffixEcologyError> {
        self.ecology.carry(current, germ)
    }

    /// Return the plural labeled branch family exposed by one already-carried current.
    pub fn emanate_current(
        &self,
        current: ExactSuffixCurrent,
    ) -> Result<ExactLabeledSuffixEmanation, ExactSuffixEcologyError> {
        let emanation = self.ecology.emanate_current(current)?;
        let branches = emanation
            .branches()
            .iter()
            .map(|branch| {
                let mut sources = LocalSet::new();
                let mut support_sources = LocalRelations::new();
                let mut support_context_sources = LocalRelations::new();
                for support in branch.supports() {
                    let target = usize::try_from(support.target_state())
                        .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
                    let context = usize::try_from(support.state())
                        .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
                    let exact_sources = self
                        .source_incidence
                        .labels(target, &self.source_catalogue)?;
                    sources.extend(exact_sources.iter().cloned());
                    support_sources
                        .try_insert(*support, exact_sources)
                        .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
                    support_context_sources
                        .try_insert(
                            *support,
                            self.source_incidence
                                .labels(context, &self.source_catalogue)?,
                        )
                        .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
                }
                Ok(ExactLabeledSuffixBranch {
                    branch: branch.clone(),
                    sources,
                    support_sources,
                    support_context_sources,
                })
            })
            .collect::<Result<Vec<_>, ExactSuffixEcologyError>>()?;
        Ok(ExactLabeledSuffixEmanation {
            emanation,
            branches,
        })
    }

    /// Exact source face of the longest recurrent suffix reached by a supplied path, including a
    /// terminal context with no outgoing transport.
    pub fn longest_matched_sources(
        &self,
        path: &[ResonanceGerm],
    ) -> Result<(u32, LocalSet<SuffixSourceLabel>), ExactSuffixEcologyError> {
        let emanation = self.ecology.emanate(path)?;
        let state = usize::try_from(emanation.longest_state())
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        Ok((
            emanation.longest_matched_length(),
            self.source_incidence
                .labels(state, &self.source_catalogue)?,
        ))
    }

    /// Exact carrier census for the source-lineage organ. This is an ownership receipt, not a
    /// semantic statistic: one span belongs to each recurrent state and one entry to each caused
    /// material occurrence, regardless of how many states can receive that occurrence through
    /// suffix transport.
    pub const fn source_incidence_census(&self) -> (usize, usize) {
        (
            self.source_incidence.state_spans.len(),
            self.source_incidence.occurrence_sources.len(),
        )
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, ExactSuffixEcologyError> {
        let ecology = self.ecology.encode_native_bytes()?;
        if ecology.len() % core::mem::size_of::<u32>() != 0 {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        self.source_incidence
            .validate(&self.ecology.states, self.source_catalogue.len())?;
        let ecology_extent =
            u64::try_from(ecology.len()).map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        let state_count = u64::try_from(self.source_incidence.state_spans.len())
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        let source_count = u64::try_from(self.source_catalogue.len())
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        let occurrence_count = u64::try_from(self.source_incidence.occurrence_sources.len())
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        let mut words = vec![
            LABELED_WIRE_MAGIC,
            LABELED_WIRE_VERSION,
            ecology_extent as u32,
            (ecology_extent >> 32) as u32,
            state_count as u32,
            (state_count >> 32) as u32,
            source_count as u32,
            (source_count >> 32) as u32,
            occurrence_count as u32,
            (occurrence_count >> 32) as u32,
        ];
        for row in ecology.chunks_exact(core::mem::size_of::<u32>()) {
            words.push(u32::from_le_bytes([row[0], row[1], row[2], row[3]]));
        }
        for source in &self.source_catalogue {
            let extent = u64::try_from(source.words().len())
                .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
            words.extend([
                source.schema() as u32,
                (source.schema() >> 32) as u32,
                extent as u32,
                (extent >> 32) as u32,
            ]);
            words.extend_from_slice(source.words());
        }
        for span in &self.source_incidence.state_spans {
            words.extend([
                span.start as u32,
                (span.start >> 32) as u32,
                span.len as u32,
                (span.len >> 32) as u32,
            ]);
        }
        words.extend_from_slice(&self.source_incidence.occurrence_sources);
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(
                words
                    .len()
                    .checked_mul(core::mem::size_of::<u32>())
                    .ok_or(ExactSuffixEcologyError::CarrierExtent)?,
            )
            .map_err(|_| ExactSuffixEcologyError::CarrierExtent)?;
        for word in words {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        Ok(bytes)
    }

    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, ExactSuffixEcologyError> {
        if bytes.len() % core::mem::size_of::<u32>() != 0 {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let words = bytes
            .chunks_exact(core::mem::size_of::<u32>())
            .map(|row| u32::from_le_bytes([row[0], row[1], row[2], row[3]]))
            .collect::<Vec<_>>();
        if words.len() < LABELED_HEADER_WORDS || words[0] != LABELED_WIRE_MAGIC {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        if words[1] != LABELED_WIRE_VERSION {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let ecology_extent = join_u64(words[2], words[3])
            .and_then(|extent| usize::try_from(extent).ok())
            .filter(|extent| *extent % core::mem::size_of::<u32>() == 0)
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let state_count = join_u64(words[4], words[5])
            .and_then(|count| usize::try_from(count).ok())
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let source_count = join_u64(words[6], words[7])
            .and_then(|count| usize::try_from(count).ok())
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let occurrence_count = join_u64(words[8], words[9])
            .and_then(|count| usize::try_from(count).ok())
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let ecology_words = ecology_extent / core::mem::size_of::<u32>();
        let mut cursor = LABELED_HEADER_WORDS;
        let ecology_end = cursor
            .checked_add(ecology_words)
            .filter(|end| *end <= words.len())
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let mut ecology_bytes = Vec::with_capacity(ecology_extent);
        for word in &words[cursor..ecology_end] {
            ecology_bytes.extend_from_slice(&word.to_le_bytes());
        }
        let ecology = ExactSuffixEcology::from_native_bytes(&ecology_bytes)?;
        cursor = ecology_end;
        if state_count != ecology.states.len() {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        let mut source_catalogue = Vec::with_capacity(source_count);
        for _ in 0..source_count {
            let header_end = cursor
                .checked_add(4)
                .filter(|end| *end <= words.len())
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let schema = join_u64(words[cursor], words[cursor + 1])
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let extent = join_u64(words[cursor + 2], words[cursor + 3])
                .and_then(|extent| usize::try_from(extent).ok())
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            cursor = header_end;
            let source_end = cursor
                .checked_add(extent)
                .filter(|end| *end <= words.len())
                .ok_or(ExactSuffixEcologyError::InvalidWire)?;
            let source = ReceiverFiberIdentity::new(schema, words[cursor..source_end].to_vec());
            if source_catalogue
                .last()
                .is_some_and(|prior| prior >= &source)
            {
                return Err(ExactSuffixEcologyError::InvalidWire);
            }
            source_catalogue.push(source);
            cursor = source_end;
        }
        let span_words = state_count
            .checked_mul(4)
            .ok_or(ExactSuffixEcologyError::CarrierExtent)?;
        let incidence_end = cursor
            .checked_add(span_words)
            .and_then(|end| end.checked_add(occurrence_count))
            .filter(|end| *end == words.len())
            .ok_or(ExactSuffixEcologyError::InvalidWire)?;
        let mut state_spans = Vec::with_capacity(state_count);
        for _ in 0..state_count {
            state_spans.push(SourceSpan {
                start: join_u64(words[cursor], words[cursor + 1])
                    .ok_or(ExactSuffixEcologyError::InvalidWire)?,
                len: join_u64(words[cursor + 2], words[cursor + 3])
                    .ok_or(ExactSuffixEcologyError::InvalidWire)?,
            });
            cursor += 4;
        }
        let occurrence_sources = words[cursor..incidence_end].to_vec().into_boxed_slice();
        cursor = incidence_end;
        let source_incidence = SourceIncidence {
            state_spans: state_spans.into_boxed_slice(),
            occurrence_sources,
        };
        if cursor != words.len() {
            return Err(ExactSuffixEcologyError::InvalidWire);
        }
        source_incidence.validate(&ecology.states, source_count)?;
        Ok(Self {
            ecology,
            source_catalogue,
            source_incidence,
        })
    }
}

fn join_u64(low: u32, high: u32) -> Option<u64> {
    Some(u64::from(low) | (u64::from(high) << 32))
}

#[cfg(test)]
mod tests {
    use body::num::Cog;
    use soma_abi::active::RelationAtom;

    use super::*;

    const TEST_SCHEMA: u64 = 0x5355_4646_5445_5354;

    fn germ(value: u32) -> ResonanceGerm {
        ResonanceGerm::new(
            ReceiverFiberIdentity::new(TEST_SCHEMA, [value]),
            RelationAtom::new(Cog::lit(i64::from(value) + 1)).unwrap(),
        )
    }

    fn phased_germ(identity: u32, phase: i64) -> ResonanceGerm {
        ResonanceGerm::new(
            ReceiverFiberIdentity::new(TEST_SCHEMA, [identity]),
            RelationAtom::new(Cog::lit(phase)).unwrap(),
        )
    }

    fn source(value: u32) -> ReceiverFiberIdentity {
        ReceiverFiberIdentity::new(0x5352_4345, [value])
    }

    #[test]
    fn outer_delivery_is_gauge_and_native_rest_reopens() {
        let paths = vec![
            vec![germ(1), germ(2), germ(3)],
            vec![germ(4), germ(2), germ(5)],
        ];
        let forward = ExactSuffixEcology::condition(&paths).unwrap();
        let reverse =
            ExactSuffixEcology::condition(&paths.into_iter().rev().collect::<Vec<_>>()).unwrap();
        assert_eq!(forward, reverse);
        let wire = forward.encode_native_bytes().unwrap();
        assert_eq!(
            ExactSuffixEcology::from_native_bytes(&wire).unwrap(),
            forward
        );
        assert!(ExactSuffixEcology::from_native_bytes(&wire[..wire.len() - 1]).is_err());
    }

    #[test]
    fn changed_outer_history_returns_internal_suffix_continuations() {
        let ecology = ExactSuffixEcology::condition(&[
            vec![germ(1), germ(2), germ(3)],
            vec![germ(4), germ(2), germ(5)],
        ])
        .unwrap();
        let emanation = ecology.emanate(&[germ(9), germ(2)]).unwrap();
        assert_eq!(emanation.longest_matched_length(), 1);
        assert_eq!(
            emanation
                .branches()
                .iter()
                .map(|branch| branch.germ().identity().words()[0])
                .collect::<BTreeSet<_>>(),
            [3, 5].into_iter().collect()
        );
    }

    #[test]
    fn returned_germ_advances_the_same_current_consulted_by_the_next_emanation() {
        let ecology = ExactSuffixEcology::condition(&[
            vec![germ(1), germ(2), germ(3)],
            vec![germ(4), germ(2), germ(5)],
        ])
        .unwrap();
        let before = ecology.receive_path(&[germ(9), germ(2)]).unwrap();
        let before_face = ecology.emanate_current(before).unwrap();
        assert_eq!(
            before_face
                .branches()
                .iter()
                .map(|branch| branch.germ().identity().words()[0])
                .collect::<BTreeSet<_>>(),
            [3, 5].into_iter().collect()
        );

        let after = ecology.carry(before, &germ(3)).unwrap();
        assert_ne!(after, before);
        assert_eq!(
            ecology.emanate_current(after).unwrap(),
            ecology.emanate(&[germ(9), germ(2), germ(3)]).unwrap()
        );
        assert!(ecology
            .emanate_current(after)
            .unwrap()
            .branches()
            .is_empty());
    }

    #[test]
    fn root_vocabulary_is_not_fabricated_for_an_unseen_terminal() {
        let ecology = ExactSuffixEcology::condition(&[vec![germ(1), germ(2), germ(3)]]).unwrap();
        let emanation = ecology.emanate(&[germ(9)]).unwrap();
        assert_eq!(emanation.longest_matched_length(), 0);
        assert!(emanation.contexts().is_empty());
        assert!(emanation.branches().is_empty());
    }

    #[test]
    fn repeated_initial_germs_keep_a_strict_suffix_geometry() {
        let ecology =
            ExactSuffixEcology::condition(&[vec![germ(1), germ(2)], vec![germ(1), germ(3)]])
                .unwrap();
        let wire = ecology.encode_native_bytes().unwrap();
        assert_eq!(
            ExactSuffixEcology::from_native_bytes(&wire).unwrap(),
            ecology
        );
        assert_eq!(
            ecology
                .emanate(&[germ(1)])
                .unwrap()
                .branches()
                .iter()
                .map(|branch| branch.germ().identity().words()[0])
                .collect::<BTreeSet<_>>(),
            [2, 3].into_iter().collect()
        );
    }

    #[test]
    fn utterance_boundaries_do_not_emit_cross_path_material() {
        let ecology =
            ExactSuffixEcology::condition(&[vec![germ(1), germ(2)], vec![germ(3), germ(4)]])
                .unwrap();
        assert!(ecology.emanate(&[germ(2)]).unwrap().branches().is_empty());
    }

    #[test]
    fn equal_deliveries_retain_recurrence_multiplicity() {
        let ecology =
            ExactSuffixEcology::condition(&[vec![germ(1), germ(2)], vec![germ(1), germ(2)]])
                .unwrap();
        let emanation = ecology.emanate(&[germ(1)]).unwrap();
        assert_eq!(ecology.material_occurrence_count(), 4);
        assert_eq!(emanation.branches().len(), 1);
        assert_eq!(
            emanation.branches()[0]
                .supports()
                .iter()
                .map(|support| support.recurrence_multiplicity())
                .collect::<BTreeSet<_>>(),
            [2].into_iter().collect()
        );
    }

    #[test]
    fn labeled_recurrence_retains_plural_source_lineage_and_remounts() {
        let paths = vec![
            vec![germ(1), germ(2), germ(3)],
            vec![germ(1), germ(2), germ(4)],
        ];
        let labels = vec![source(30), source(40)];
        let ecology = ExactLabeledSuffixEcology::condition(&paths, &labels).unwrap();
        let emanation = ecology.emanate(&[germ(1), germ(2)]).unwrap();
        let branches = emanation
            .branches()
            .iter()
            .map(|branch| {
                (
                    branch.branch().germ().identity().words()[0],
                    branch.sources().clone(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        assert_eq!(branches.get(&3), Some(&LocalSet::from([source(30)])));
        assert_eq!(branches.get(&4), Some(&LocalSet::from([source(40)])));

        let wire = ecology.encode_native_bytes().unwrap();
        let remounted = ExactLabeledSuffixEcology::from_native_bytes(&wire).unwrap();
        assert_eq!(remounted, ecology);
        assert_eq!(remounted.emanate(&[germ(1), germ(2)]).unwrap(), emanation);
    }

    #[test]
    fn material_edge_atlas_retains_state_phase_and_support_specific_lineage() {
        let first_phase = phased_germ(9, 100);
        let second_phase = phased_germ(9, 200);
        let ecology = ExactLabeledSuffixEcology::condition(
            &[
                vec![germ(1), first_phase.clone(), germ(3)],
                vec![germ(1), second_phase.clone(), germ(4)],
            ],
            &[source(30), source(40)],
        )
        .unwrap();
        let edges = ecology.material_edges().unwrap();
        assert!(edges.iter().all(|edge| edge.context_state() != 0));
        let phased_edges = edges
            .iter()
            .filter(|edge| edge.germ_identity().words() == [9])
            .collect::<LocalSequence<_>>();
        assert!(phased_edges.len() >= 2);
        assert_eq!(
            phased_edges
                .iter()
                .map(|edge| edge.germ_phase())
                .collect::<BTreeSet<_>>(),
            [first_phase.phase().words(), second_phase.phase().words()]
                .into_iter()
                .collect()
        );
        assert_eq!(
            edges
                .iter()
                .map(|edge| (
                    edge.context_state(),
                    edge.germ_identity().clone(),
                    edge.germ_phase(),
                    edge.target_state(),
                ))
                .collect::<BTreeSet<_>>()
                .len(),
            edges.len()
        );

        let emanation = ecology.emanate(&[germ(1)]).unwrap();
        for branch in emanation.branches() {
            for support in branch.branch().supports() {
                let edge = edges
                    .iter()
                    .find(|edge| {
                        edge.context_state() == support.state()
                            && edge.target_state() == support.target_state()
                            && edge.germ_identity() == branch.branch().germ().identity()
                            && edge.germ_phase() == branch.branch().germ().phase().words()
                    })
                    .unwrap();
                assert_eq!(
                    edge.recurrence_multiplicity(),
                    support.recurrence_multiplicity()
                );
                assert_eq!(Some(edge.sources()), branch.sources_for_support(support));
                assert_eq!(
                    Some(edge.context_sources()),
                    branch.context_sources_for_support(support)
                );
            }
        }

        let remounted =
            ExactLabeledSuffixEcology::from_native_bytes(&ecology.encode_native_bytes().unwrap())
                .unwrap();
        assert_eq!(remounted.material_edges().unwrap(), edges);
    }

    #[test]
    fn labeled_lineage_is_linear_in_states_and_caused_occurrences() {
        let mut paths = LocalSequence::with_capacity(256);
        let mut labels = LocalSequence::with_capacity(256);
        for at in 0..256u32 {
            paths.push(vec![germ(1), germ(2), germ(1000 + at)]);
            labels.push(source(at));
        }
        let ecology = ExactLabeledSuffixEcology::condition(&paths, &labels).unwrap();
        let (spans, occurrences) = ecology.source_incidence_census();
        assert_eq!(spans, ecology.ecology.state_count());
        assert_eq!(
            occurrences,
            paths.iter().map(|path| path.len()).sum::<usize>()
        );
        let former_dense_words = spans * labels.len().div_ceil(u64::BITS as usize);
        assert!(former_dense_words > occurrences);
    }

    #[test]
    fn labeled_native_rest_rejects_superseded_and_unknown_versions() {
        let ecology = ExactLabeledSuffixEcology::condition(
            &[
                vec![germ(1), germ(2), germ(3)],
                vec![germ(1), germ(2), germ(4)],
                vec![germ(8), germ(2), germ(3)],
            ],
            &[source(30), source(40), source(50)],
        )
        .unwrap();
        let wire = ecology.encode_native_bytes().unwrap();
        for rejected_version in [2u32, 4u32, u32::MAX] {
            let mut rejected = wire.clone();
            rejected[4..8].copy_from_slice(&rejected_version.to_le_bytes());
            assert_eq!(
                ExactLabeledSuffixEcology::from_native_bytes(&rejected),
                Err(ExactSuffixEcologyError::InvalidWire)
            );
        }
    }

    #[test]
    fn labeled_context_receipt_distinguishes_a_recurrent_seam_from_its_target() {
        let ecology = ExactLabeledSuffixEcology::condition(
            &[
                vec![germ(1), germ(2), germ(3)],
                vec![germ(8), germ(3), germ(4)],
            ],
            &[source(30), source(40)],
        )
        .unwrap();
        let emanation = ecology.emanate(&[germ(1), germ(2), germ(3)]).unwrap();
        let branch = emanation
            .branches()
            .iter()
            .find(|branch| branch.branch().germ().identity() == germ(4).identity())
            .unwrap();
        let support = branch
            .branch()
            .supports()
            .iter()
            .find(|support| support.matched_length() == 1)
            .unwrap();
        assert_eq!(
            branch.context_sources_for_support(support),
            Some(&LocalSet::from([source(30), source(40)]))
        );
        assert_eq!(
            branch.sources_for_support(support),
            Some(&LocalSet::from([source(40)]))
        );
    }

    #[test]
    fn terminal_long_context_can_dilate_to_a_productive_recurrent_receiver() {
        let ecology = ExactSuffixEcology::condition(&[
            vec![germ(1), germ(2), germ(3)],
            vec![germ(8), germ(3), germ(4)],
        ])
        .unwrap();
        let emanation = ecology.emanate(&[germ(1), germ(2), germ(3)]).unwrap();
        assert_eq!(emanation.longest_matched_length(), 3);
        assert_eq!(emanation.greatest_productive_matched_length(), Some(1));
        assert!(emanation
            .branches()
            .iter()
            .any(|branch| branch.germ().identity() == germ(4).identity()));
    }
}
