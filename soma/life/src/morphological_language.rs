//! Simultaneous-scale exact language ecology.
//!
//! Text is received through several coexisting receiver charts. Unicode marks retain exact
//! sublexical recurrence in both orientations; lexical surfaces retain ordered phrase recurrence;
//! punctuation-caused clauses retain local deed boundaries; delivery sections retain occurrence
//! lineage; and source documents retain the exterior causal provenance. None of those charts is
//! declared to be the one tokenization of language.
//!
//! A question charges the sparse feature-to-occurrence relations which were returned through the
//! production Swing. Exact inclusion between those returned regions removes only redundant,
//! more-general query faces. The remaining plural obligations recruit clause-local currents. A
//! response closes only after every open obligation has participated in a returned phase and that
//! phase reaches a caused sentence boundary. Punctuation alone cannot stop an unresolved response,
//! and a token aperture is reported as an observation exhaustion rather than linguistic closure.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use body::num::Cog;
use holonic_structure::{BranchLineage, LocalSequence, LocalSet};
use soma_abi::active::{ActionCurrent, RelationAtom};
use soma_membrane::{
    LiveCurrentExecutor, LiveCurrentMachine, ParallelCpuLiveCurrentExecutor,
    ReceiverFiberIdentity, SparseStandingSurface,
};

use crate::{
    causal_language::{
        condition_route_receivers, condition_route_receivers_with_executor, lexical_tokens,
        render_tokens, route_feature_fiber, token_germs, CausalLanguageError, RouteTrainingSection,
    },
    resonance_ecology::{
        fiber_from_bytes, ResonanceEcology, ResonanceEcologyError, ResonanceEcologyRestImage,
        ResonanceGerm, ResonanceOccurrence,
    },
    suffix_ecology::{
        ExactLabeledSuffixEcology, ExactSuffixCurrent, ExactSuffixEcologyError, SuffixSourceLabel,
    },
};

const MORPH_MARK_SCHEMA: u64 = 0x4d4f_5250_484d_4152;
const MORPH_PASSAGE_SCHEMA: u64 = 0x4d4f_5250_4850_4153;
const MORPH_SOURCE_SCHEMA: u64 = 0x4d4f_5250_4853_5243;
const MORPH_CLAUSE_SCHEMA: u64 = 0x4d4f_5250_4843_4c53;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MorphologicalLanguageError {
    EmptyCorpus,
    EmptyPassage(String),
    DuplicatePassage(String),
    ConflictingSourceReceiver(String),
    EmptyPrompt,
    EmptyObservationAperture,
    CarrierExtent,
    MalformedFiber,
    /// A generation cell sat at a clause-lexical site the corpus attests in **no** source, so the
    /// transport law has no capacity to divide by. Refused by name rather than floored to one:
    /// zero support is not a small support, and `holonic_engine::receiver_current` itself refuses a
    /// non-positive capacity.
    UnattestedGenerationSite(u32),
    Route(CausalLanguageError),
    Resonance(ResonanceEcologyError),
    Suffix(ExactSuffixEcologyError),
    Conduct(conduct::MorphologicalConductRefusal),
    ConductCuda(conduct_cuda::MorphologicalConductCudaError),
    ConditionCuda(condition_cuda::MorphologicalConditionCudaError),
}

impl From<CausalLanguageError> for MorphologicalLanguageError {
    fn from(value: CausalLanguageError) -> Self {
        Self::Route(value)
    }
}

impl From<ResonanceEcologyError> for MorphologicalLanguageError {
    fn from(value: ResonanceEcologyError) -> Self {
        Self::Resonance(value)
    }
}

impl From<ExactSuffixEcologyError> for MorphologicalLanguageError {
    fn from(value: ExactSuffixEcologyError) -> Self {
        Self::Suffix(value)
    }
}

impl From<conduct::MorphologicalConductRefusal> for MorphologicalLanguageError {
    fn from(value: conduct::MorphologicalConductRefusal) -> Self {
        Self::Conduct(value)
    }
}

impl From<conduct_cuda::MorphologicalConductCudaError> for MorphologicalLanguageError {
    fn from(value: conduct_cuda::MorphologicalConductCudaError) -> Self {
        Self::ConductCuda(value)
    }
}

impl From<condition_cuda::MorphologicalConditionCudaError> for MorphologicalLanguageError {
    fn from(value: condition_cuda::MorphologicalConditionCudaError) -> Self {
        Self::ConditionCuda(value)
    }
}

/// One delivered textual section. `identity` identifies the occurrence; `source` identifies the
/// exterior lineage shared by any number of delivery sections. A delivery boundary remains
/// testimony and never becomes the generative extent of the source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalLanguagePassage {
    pub identity: String,
    pub source: String,
    pub receiver: u64,
    /// Source-declared occurrence/section order. This is carried through a co-present delivery
    /// front and is never reconstructed from receiver or caller slice position. It is meaningful
    /// only within `source`; unrelated sources remain incomparable.
    pub source_order: u128,
    pub source_order_declared: bool,
    pub text: String,
}

impl MorphologicalLanguagePassage {
    pub fn new(
        identity: impl Into<String>,
        source: impl Into<String>,
        receiver: u64,
        text: impl Into<String>,
    ) -> Self {
        Self {
            identity: identity.into(),
            source: source.into(),
            receiver,
            source_order: 0,
            source_order_declared: false,
            text: text.into(),
        }
    }

    pub const fn with_source_order(mut self, source_order: u128) -> Self {
        self.source_order = source_order;
        self.source_order_declared = true;
        self
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MorphologicalBoundary {
    /// A returned full stop, question mark, or exclamation mark.
    Sentence,
    /// A returned colon or semicolon: the phase may re-route but the response remains open.
    Clause,
    /// The supplied delivery section ended without a linguistic closure.
    DeliveryObstruction,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MorphologicalScaleCensus {
    pub source_lineages: usize,
    pub delivery_occurrences: usize,
    pub clause_receivers: usize,
    pub lexical_occurrences: usize,
    pub lexical_recurrent_states: usize,
    pub lexical_material_transitions: usize,
    pub lexical_lineage_occurrences: usize,
    pub clause_lexical_recurrent_states: usize,
    pub clause_lexical_material_transitions: usize,
    pub clause_lexical_lineage_occurrences: usize,
    pub ordered_region_recurrent_states: usize,
    pub ordered_region_material_transitions: usize,
    pub ordered_region_lineage_occurrences: usize,
    pub conditioned_question_operator_regions: usize,
    pub mark_word_occurrences: usize,
    pub forward_mark_recurrent_states: usize,
    pub reverse_mark_recurrent_states: usize,
    pub forward_mark_lineage_occurrences: usize,
    pub reverse_mark_lineage_occurrences: usize,
    pub returned_route_receptors: usize,
    pub returned_route_relations: usize,
    pub conditioning_events: usize,
    /// **The recruitment transpose's work, counted rather than timed.**
    ///
    /// `CLAUDE.md` §8: a cost is measured in work, never in elapsed time. These are exact integers
    /// derived from the material, reproducing bit-for-bit on any machine, and they are the evidence
    /// for or against the claim that clause recruitment is a scan where a transpose was in hand.
    /// `attempted` counts every feature-membership test the recruitment performed; `fired` counts
    /// the incidences it actually returned. The overpayment is their ratio, and if the two track
    /// each other the scan reading is wrong.
    pub recruitment_membership_tests: u64,
    pub recruitment_incidences: u64,
    /// Question-initial prefix incidences crossed once in the boundary-anchored prefix atlas.
    pub question_prefix_crossings: u64,
    /// Distinct non-root prefix nodes retained by that atlas.
    pub question_prefix_nodes: u64,
    /// Counterfactual token clones performed by the superseded `prefix[..end].to_vec()` chart.
    /// This is derived exactly from the same admitted question clauses; it is not a clock.
    pub question_prefix_legacy_cloned_tokens: u64,
    /// Tokens materialized in the actually returned recurrent-and-branching operator regions.
    pub question_prefix_returned_tokens: u64,
}

/// Resource and causal-connection receipt of one generated current population. Whole-body forks
/// must remain zero: alternatives are sparse local currents over one conditioned body, and every
/// terminal witness remains present in the returned family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalReflectionReceipt {
    pub shared_conditioned_bodies: usize,
    pub whole_body_forks: usize,
    /// Explicit sparse-current forks whose immutable witness prefixes remain shared.
    pub shared_current_forks: usize,
    pub causal_current_states_formed: usize,
    pub conduct_equivalent_states_glued: usize,
    pub peak_live_current_states: usize,
    pub returned_events_carried: usize,
    pub terminal_return_materializations: usize,
    /// **Passages the transport law dilated**, i.e. cells whose co-present demand exceeded the
    /// corpus's attestation of their site and which therefore arrived later than the next token.
    /// Zero here is a finding and not a default: it says the material never congested, so the delay
    /// law was present in the code and absent from the evidence.
    pub dilated_passages: usize,
    /// The largest dilation any one passage took, in tokens beyond the uncongested one.
    pub deepest_dilation: u64,
    /// The furthest arrival chronology the front reached. Equal to the token depth exactly when
    /// nothing dilated; strictly greater as soon as anything did.
    pub deepest_chronology: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MorphologicalGenerationSpec {
    pub maximum_observed_tokens: usize,
}

impl Default for MorphologicalGenerationSpec {
    fn default() -> Self {
        Self {
            maximum_observed_tokens: 256,
        }
    }
}

mod generated;
pub use generated::*;

mod current;
pub use current::MorphologicalLanguageEcology;

mod conduct;
pub use conduct::*;

mod conduct_cuda;
pub use conduct_cuda::*;

mod condition_cuda;
pub use condition_cuda::*;

#[cfg(test)]
mod tests;
