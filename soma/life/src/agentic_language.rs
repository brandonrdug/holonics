//! Incremental exact language agency over a typed world mouth.
//!
//! [`MorphologicalLanguageEcology`] owns the simultaneous-scale language body used inside every
//! organ below. This module does not replace that body with a serialized conversation, a scalar
//! embedding, or a host-selected answer. It composes several immutable conditioned organs:
//!
//! - one shared inherited language body;
//! - inherited action/observation/answer trajectory organs;
//! - locally conditioned episode organs founded by later world returns; and
//! - one sparse atlas carrying a contemporary question only to organs whose caused surfaces it
//!   actually reaches.
//!
//! A world capability is learned from inherited trajectories. When no extant episode can ground
//! every open query region, the body emits a typed deed. The deed's actual returned sections then
//! enter the same receiving membrane, generate a linguistic consequence, and found one new local
//! organ. A related later question may conduct through that organ without rebuilding the inherited
//! body or replaying the first deed.

use std::collections::{BTreeMap, BTreeSet};

use holonic_language::{
    CodecCrossingError, CodecId, CodecObstruction, CodecStep, ContinuationId, ContinuationState,
    ReceiverId, ReflectiveCodecExecutor, ReflectiveRuntime, ReflectiveRuntimeError,
};
use holonic_structure::{CausalMembrane, LocalSet};
use soma_abi::active::ActionCurrent;
use soma_membrane::LiveCurrentExecutor;

use crate::{
    causal_language::{lexical_tokens, render_tokens},
    holonic_training::{
        ConsequenceRelation, FaceAddress, SourceFace, TrainingCultivationProposal, TrainingEcology,
        TrainingView, TransductionFiber, TransductionTemplate,
    },
    lean_mathematics::LeanKernelDeedCompletion,
    morphological_language::{
        MorphologicalBoundary, MorphologicalGeneratedCurrent, MorphologicalGeneratedText,
        MorphologicalGeneratedToken, MorphologicalGenerationSpec, MorphologicalLanguageEcology,
        MorphologicalLanguageError, MorphologicalLanguagePassage, MorphologicalQuestionCharge,
        MorphologicalReflectionReceipt, MorphologicalResponsePhase, MorphologicalResponseRest,
        MorphologicalScaleCensus, MorphologicalTransport,
    },
    relational_language::{
        ExactRelationalLanguageEcology, RelationalLanguageError, RelationalThoughtCurrent,
        RelationalThoughtFiber,
    },
};

mod answer_continuation;
mod candidate;
mod ecology;
mod formal_return;
mod reflective_codec;
mod relational_return;
#[cfg(test)]
mod tests;

use candidate::*;
use reflective_codec::*;
use relational_return::{
    AgenticRelationalReturnOwner, AgenticRelationalReturnRestReceipt,
    AnswerSelectedRelationalCurrent,
};

const CODEC_MINIMUM_RECURRENCE: u64 = 2;
const CODEC_TEMPLATE_APERTURE: usize = 4_096;
type ExactSet<T> = BTreeSet<T>;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgenticLanguageError {
    EmptyTrajectoryEcology,
    EmptyQuestion,
    DuplicateTrajectory(String),
    DuplicateCapability(String),
    QuestionAlreadyOpen,
    NoQuestionOpen,
    NoActionRoute,
    AmbiguousActionRoutes(BTreeSet<String>),
    WrongDeedReturn { expected: String, received: String },
    ChangedWorldReturn(String),
    EmptyWorldReturn,
    EmptyFeedback,
    UnknownFeedbackTarget(String),
    FeedbackTargetIsNotDialogueOutput(String),
    DuplicateDialogueOccurrence(String),
    NativeRestRequiresRest,
    RestRemountMismatch,
    NoGroundedLanguageReturn,
    WorkerPanicked,
    CarrierExtent,
    CodecTraining(String),
    CodecRuntime(ReflectiveRuntimeError),
    Morphology(MorphologicalLanguageError),
    Relational(RelationalLanguageError),
}

impl From<MorphologicalLanguageError> for AgenticLanguageError {
    fn from(value: MorphologicalLanguageError) -> Self {
        Self::Morphology(value)
    }
}

impl From<RelationalLanguageError> for AgenticLanguageError {
    fn from(value: RelationalLanguageError) -> Self {
        Self::Relational(value)
    }
}

/// A typed deed species supplied by an exterior world.
///
/// The identity is not a shell command. It names a capability whose concrete executor remains
/// outside the language body. Distinct worlds may lawfully realize the same learned deed species
/// through different typed occurrences.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AgenticLanguageCapability {
    pub identity: String,
    pub receiver: u64,
    /// A mounted exterior organ which can receive a question whose local language ecology has
    /// not yet grounded a consequence.  This is an explicit world mouth, not a fabricated
    /// training example or a claim that the capability already knows an answer.
    pub receives_open_boundary: bool,
}

impl AgenticLanguageCapability {
    pub fn new(identity: impl Into<String>, receiver: u64) -> Self {
        Self {
            identity: identity.into(),
            receiver,
            receives_open_boundary: false,
        }
    }

    pub const fn with_open_boundary(mut self) -> Self {
        self.receives_open_boundary = true;
        self
    }
}

/// One inherited complete trajectory. Imported action examples are caused lineage, not a hidden
/// runtime answer: the new question still has to emanate its own deed, receive the actual world
/// return, and form its own response.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageTrajectory {
    pub identity: String,
    pub receiver: u64,
    pub question: String,
    pub capability: String,
    pub observations: Vec<MorphologicalLanguagePassage>,
    pub answer: String,
}

impl AgenticLanguageTrajectory {
    pub fn new(
        identity: impl Into<String>,
        receiver: u64,
        question: impl Into<String>,
        capability: impl Into<String>,
        observations: Vec<MorphologicalLanguagePassage>,
        answer: impl Into<String>,
    ) -> Self {
        Self {
            identity: identity.into(),
            receiver,
            question: question.into(),
            capability: capability.into(),
            observations,
            answer: answer.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageQuestion {
    pub identity: String,
    pub receiver: u64,
    pub text: String,
}

impl AgenticLanguageQuestion {
    pub fn new(identity: impl Into<String>, receiver: u64, text: impl Into<String>) -> Self {
        Self {
            identity: identity.into(),
            receiver,
            text: text.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticActionRoute {
    pub trajectory: String,
    pub common_ordered_regions: BTreeSet<Vec<String>>,
}

/// One receiver-local argument emitted with a typed exterior deed.
///
/// The world does not need to reinterpret the complete visible question as an opaque string. The
/// contemporary language body exposes the inclusion-maximal ordered regions which actually
/// reached an inherited action trajectory, plus the still-unmatched content surfaces which
/// distinguish this occurrence from that inheritance. This remains exact caused testimony: it is
/// neither an embedding nor a host-authored search query.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticDeedArgument {
    pub ordered_surface: Vec<String>,
    pub caused_trajectories: BTreeSet<String>,
    pub inherited_region: bool,
}

/// A deed emitted by the language current before the exterior world is allowed to act.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageDeed {
    pub identity: String,
    pub question: AgenticLanguageQuestion,
    pub capability: AgenticLanguageCapability,
    pub inherited_routes: Vec<AgenticActionRoute>,
    pub arguments: Vec<AgenticDeedArgument>,
    /// The exact prompt which reached the deed. This differs from the visible question only when
    /// an elliptical occurrence had to conduct through a prior dialogue turn.
    pub received_prompt: String,
    pub contextual_dialogue: BTreeSet<String>,
}

impl AgenticLanguageDeed {
    /// A deterministic exterior query membrane over the deed arguments. Repeated surfaces retain
    /// their first caused occurrence; the visible question remains separately available above.
    pub fn argument_surface(&self) -> String {
        let mut received = BTreeSet::new();
        let mut ordered = Vec::new();
        for argument in &self.arguments {
            for surface in &argument.ordered_surface {
                if received.insert(surface.clone()) {
                    ordered.push(surface.clone());
                }
            }
        }
        ordered.join(" ")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageWorldReturn {
    pub deed: String,
    pub sections: Vec<MorphologicalLanguagePassage>,
    /// Complete plural relation bodies formed at co-present receiver scales by a typed research
    /// bridge. Ordinary worlds may return sections alone. Keeping every fiber prevents a later
    /// language receiver from flattening enacted local closure and wider open alternatives back
    /// into one undifferentiated passage set.
    pub thought_fibers: Vec<RelationalThoughtFiber>,
}

impl AgenticLanguageWorldReturn {
    pub fn new(deed: impl Into<String>, sections: Vec<MorphologicalLanguagePassage>) -> Self {
        Self {
            deed: deed.into(),
            sections,
            thought_fibers: Vec::new(),
        }
    }

    pub fn with_thought_fiber(mut self, thought_fiber: RelationalThoughtFiber) -> Self {
        self.thought_fibers.push(thought_fiber);
        self
    }

    pub fn with_thought_fibers(mut self, thought_fibers: Vec<RelationalThoughtFiber>) -> Self {
        self.thought_fibers = thought_fibers;
        self
    }
}

/// Why a finite receiver exposed this particular answer from the complete generated family.
///
/// This is an explicit presentation quotient. It does not delete alternative currents from the
/// [`MorphologicalLanguageGeneration`](crate::morphological_language::MorphologicalLanguageGeneration)
/// which formed them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticAnswerSelection {
    pub closed_population: usize,
    pub world_grounded_population: usize,
    pub inherited_path_population: usize,
    pub inclusion_maximal_population: usize,
    pub selected_token_extent: usize,
    pub selected_phase_extent: usize,
    /// Number of structurally distinct returned-current compositions retained before the outward
    /// receiver selected this witness.
    pub composed_current_population: usize,
    /// Structurally distinct inclusion-maximal currents retained beside the selected outward
    /// witness. They were not concatenated into the emitted answer.
    pub retained_alternative_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticRetainedAnswerAlternative {
    pub generated: MorphologicalGeneratedCurrent,
    pub episode_identities: BTreeSet<String>,
    pub evidence_sources: BTreeSet<String>,
    pub relational_thoughts: Vec<RelationalThoughtCurrent>,
}

/// One exact receiver-local answer region. Its coordinates remain attached to the obligation
/// which founded it; closure never follows from comparing population scalars.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AgenticAnswerRegionIdentity {
    pub obligation: usize,
    pub region: usize,
}

/// Exact evidence that the answer stopped by linguistic rest rather than by a length convention.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticAnswerClosure {
    pub obligation_population: usize,
    pub discharged_obligations: LocalSet<usize>,
    pub required_local_regions: LocalSet<AgenticAnswerRegionIdentity>,
    pub returned_local_region_identities: LocalSet<AgenticAnswerRegionIdentity>,
    pub local_region_population: usize,
    pub returned_local_regions: usize,
    pub caused_sentence_boundaries: usize,
    pub observation_aperture: usize,
    pub closed_by_returned_obligations: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub struct AgenticLanguageAnswer {
    pub question: AgenticLanguageQuestion,
    pub text: String,
    pub generated: MorphologicalGeneratedText,
    pub supporting_episode_identities: BTreeSet<String>,
    pub world_deed: Option<String>,
    pub evidence_sources: BTreeSet<String>,
    pub selection: AgenticAnswerSelection,
    /// Incomparable terminal currents which crossed the same membrane but were not selected by
    /// this receiver. Their surfaces and causal bodies remain exact future testimony.
    pub retained_alternatives: Vec<AgenticRetainedAnswerAlternative>,
    pub reflection: MorphologicalReflectionReceipt,
    pub novel_contiguous_surface: bool,
    pub locally_conditioned_episodes: BTreeSet<String>,
    pub answer_episode_identity: String,
    pub contextual_dialogue: BTreeSet<String>,
    pub closure: AgenticAnswerClosure,
    /// Exact reflective codec versions which participated in forming this answer. An empty set
    /// means the answer conducted through inherited or ordinary returned episode morphology only.
    pub operative_codec_versions: BTreeSet<String>,
    /// Exact recurrent cross-occurrence routes which generated this answer. A directly carried
    /// one-off correction has no entry here even though it may carry an operative codec version.
    pub cultivated_codec_paths: Vec<AgenticLanguageCodecPathReceipt>,
    /// The retained relation body which caused this wording. Source clauses remain inspectable
    /// witnesses; the selected realization need not be a contiguous source path.
    pub relational_thought: Option<RelationalThoughtCurrent>,
    /// Every inclusion-maximal relation current which crossed the terminal membrane. The
    /// first field above remains the exact current selected by the outward receiver; this
    /// population retains the other equal-surface currents as alternatives.
    pub relational_thoughts: Vec<RelationalThoughtCurrent>,
}

/// Dialogue roles are causal species, not labels added only for display. In particular, an
/// answer remains distinct from evidence and a correction can obstruct the answer it addresses.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AgenticDialogueRole {
    InheritedQuestion,
    InheritedObservation,
    InheritedAnswer,
    UserQuestion,
    EmittedDeed,
    WorldObservation,
    EmanatedAnswer,
    UserCorrection,
    UserAcceptance,
    UserRefusal,
    EmanatedClarification,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticDialogueOccurrence {
    pub ordinal: u64,
    pub identity: String,
    pub role: AgenticDialogueRole,
    pub receiver: u64,
    pub text: String,
    pub target: Option<String>,
    pub caused_by: BTreeSet<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AgenticLanguageFeedbackKind {
    Correction,
    Acceptance,
    Refusal,
}

/// The receiver aperture at which an operative language method has been made into a face.
///
/// The first production species is deliberately the relation between an addressed question/answer
/// face and its returned correction. Further apertures must be founded by actual applications;
/// they are not predeclared as a universal list of language faculties.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum AgenticLanguageCodecAperture {
    AnswerRelation,
    FormalReturn,
}

/// One kernel- or checker-returned formal face crossing the language body's existing reflective
/// continuation. The proof surface remains outside this body; its exact source digest and theorem
/// generation retain the causal attachment to the graded deed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticFormalReturn {
    pub identity: String,
    pub receiver: u64,
    pub completion: LeanKernelDeedCompletion,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AgenticReflectiveContinuationReceipt {
    pub continuation: u64,
    pub codec_before: u64,
    pub codec_after: u64,
    pub instruction_before: u64,
    pub instruction_after: u64,
    pub running_before: bool,
    pub running_after: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticFormalReturnReceipt {
    pub identity: String,
    pub deed: String,
    pub theorem: String,
    pub codec_version: String,
    pub codec_versions_before: usize,
    pub codec_versions_after: usize,
    pub continuation: AgenticReflectiveContinuationReceipt,
}

/// One receiver-relative face of an operative codec version.
///
/// `ordered_regions` retain the plural question, answer-phase, and replacement regions which the
/// codec can receive. They are not flattened into one token key or assigned an embedding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageCodecFace {
    pub identity: String,
    pub receiver: u64,
    pub ordered_regions: BTreeSet<Vec<String>>,
    pub lineage: BTreeSet<String>,
}

/// Structured mismatch across one reflective revision. A removed input region and an introduced
/// output region remain distinct even when an outer observer later assigns them one scalar loss.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageCodecResidual {
    pub input_only_regions: BTreeSet<Vec<String>>,
    pub output_only_regions: BTreeSet<Vec<String>>,
}

/// Exact vertical training testimony attached to one returned correction.
///
/// `observed_fibers` are the complete route forms exposed by this occurrence at every admitted
/// question horizon. They become generative only through recurrence in the shared
/// `TrainingEcology`; their presence on one version is not itself an active rule.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageCodecCultivation {
    pub generation: u64,
    pub receiver_views: usize,
    pub prior_relations: Vec<ConsequenceRelation>,
    pub observed_fibers: BTreeSet<TransductionFiber>,
    pub active_transductions_before: usize,
    pub active_transductions_after: usize,
}

/// One exact learned route which was rebound to the contemporary question face.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AgenticLanguageCodecPathReceipt {
    pub template: TransductionTemplate,
    pub receiver_parameters: Vec<(String, String)>,
    pub recurrence: u64,
    pub consequence: String,
    pub version_lineage: BTreeSet<String>,
}

/// One committed, causally connected language-codec version.
///
/// The version is operative because `AgenticLanguageEcology` consults its input face during later
/// question reception and carries the identity through the selected answer. It is not merely a
/// record describing a correction after the ordinary episode machinery has already decided.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageCodecVersion {
    pub identity: String,
    pub aperture: AgenticLanguageCodecAperture,
    pub parents: BTreeSet<String>,
    pub input: AgenticLanguageCodecFace,
    pub output: AgenticLanguageCodecFace,
    pub output_episode: String,
    pub returned_by: String,
    pub residual: AgenticLanguageCodecResidual,
    pub cultivation: AgenticLanguageCodecCultivation,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageFeedback {
    pub identity: String,
    pub receiver: u64,
    pub target_episode: String,
    pub kind: AgenticLanguageFeedbackKind,
    pub text: String,
}

impl AgenticLanguageFeedback {
    pub fn new(
        identity: impl Into<String>,
        receiver: u64,
        target_episode: impl Into<String>,
        kind: AgenticLanguageFeedbackKind,
        text: impl Into<String>,
    ) -> Self {
        Self {
            identity: identity.into(),
            receiver,
            target_episode: target_episode.into(),
            kind,
            text: text.into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageFeedbackReceipt {
    pub feedback: AgenticLanguageFeedback,
    pub founded_episode: String,
    pub obstructed_episodes: BTreeSet<String>,
    pub dialogue_ordinal: u64,
    pub committed_codec_version: Option<AgenticLanguageCodecVersion>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticClarificationAlternative {
    pub capability: String,
    pub inherited_questions: BTreeSet<String>,
    pub trajectories: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageClarification {
    pub identity: String,
    pub question: AgenticLanguageQuestion,
    pub text: String,
    pub alternatives: Vec<AgenticClarificationAlternative>,
    pub contextual_dialogue: BTreeSet<String>,
    pub episode_identity: String,
}

#[derive(Debug, PartialEq, Eq)]
pub enum AgenticLanguageConsequence {
    Deed(AgenticLanguageDeed),
    Answer(AgenticLanguageAnswer),
    Clarification(AgenticLanguageClarification),
    Feedback(AgenticLanguageFeedbackReceipt),
    FormalReturn(AgenticFormalReturnReceipt),
}

pub enum AgenticLanguageOccurrence<'a> {
    Question(&'a AgenticLanguageQuestion),
    WorldReturn(&'a AgenticLanguageWorldReturn),
    Feedback(&'a AgenticLanguageFeedback),
    FormalReturn(&'a AgenticFormalReturn),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgenticTurnStanding {
    Rest,
    AwaitingWorldReturn {
        question: String,
        deed: String,
        capability: String,
    },
    AwaitingClarification {
        question: String,
        clarification: String,
        alternatives: BTreeSet<String>,
    },
}

/// Exact receiver testimony for the continuing agent body.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageStanding {
    pub inherited_body_passages: usize,
    pub inherited_trajectory_organs: usize,
    pub locally_conditioned_episode_organs: usize,
    pub base_body_reconditions: usize,
    pub emitted_deeds: usize,
    pub received_world_returns: usize,
    pub received_world_thought_fibers: usize,
    pub generated_answers: usize,
    pub generated_clarifications: usize,
    pub received_corrections: usize,
    pub received_acceptances: usize,
    pub received_refusals: usize,
    pub reflective_codec_versions: usize,
    pub reflective_codec_commits: usize,
    pub reflective_codec_training_events: usize,
    pub active_codec_transductions: usize,
    pub dialogue_occurrences: usize,
    pub turn: AgenticTurnStanding,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AgenticLanguageSpec {
    pub generation: MorphologicalGenerationSpec,
    pub thought_receiver_horizon: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticEpisodeRestReceipt {
    pub identity: String,
    pub role: AgenticDialogueRole,
    pub revision: u64,
    pub answerable: bool,
    pub passages: Vec<MorphologicalLanguagePassage>,
    pub routing_surfaces: BTreeSet<String>,
    pub evidence_sources: BTreeSet<String>,
    pub realized_ecology: Option<MorphologicalScaleCensus>,
    pub relational_thought: Option<RelationalThoughtCurrent>,
    pub codec_versions: BTreeSet<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticAnswerLineageRestReceipt {
    pub answer_episode: String,
    /// Exact exterior deed whose returned thought fiber caused this answer. Answers conducted
    /// without a new exterior contact have no world deed.
    pub world_deed: Option<String>,
    pub supporting_episodes: BTreeSet<String>,
    pub evidence_sources: BTreeSet<String>,
    pub surface: Vec<String>,
    pub question_surface: Vec<String>,
    pub codec_versions: BTreeSet<String>,
    pub cultivated_codec_paths: Vec<AgenticLanguageCodecPathReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticLanguageRestReceipt {
    pub inherited_body: MorphologicalScaleCensus,
    pub episodes: Vec<AgenticEpisodeRestReceipt>,
    pub dialogue: Vec<AgenticDialogueOccurrence>,
    pub obstructed_episodes: BTreeSet<String>,
    pub accepted_episodes: BTreeSet<String>,
    pub answer_lineages: Vec<AgenticAnswerLineageRestReceipt>,
    /// Opaque exact testimony of the deed fibers and answer-relative current selections retained
    /// by their domain owner. It is not a caller-addressable fiber registry.
    pub relational_returns: AgenticRelationalReturnRestReceipt,
    pub codec_versions: Vec<AgenticLanguageCodecVersion>,
    /// Native source-occurrence-free route population cultivated across returned corrections.
    pub codec_training: Vec<u8>,
    pub pending_capabilities: Option<BTreeSet<String>>,
    pub open_deed: Option<AgenticLanguageDeed>,
    pub next_deed: u64,
    pub next_episode: u64,
    pub next_dialogue: u64,
    pub standing: AgenticLanguageStanding,
}

/// Native suspension of the complete continuing Eros body.
///
/// This owner contains the cultivated body itself and remounts by direct transfer. It does not
/// replay dialogue, reconstruct the relation organ, or recondition codec training from source
/// occurrences.
#[derive(Debug)]
pub struct AgenticLanguageNativeRest {
    body: AgenticLanguageEcology,
}

#[derive(Debug)]
pub struct AgenticLanguageNativeRestRefusal {
    pub error: AgenticLanguageError,
    body: AgenticLanguageEcology,
}

impl AgenticLanguageNativeRestRefusal {
    pub fn recover(self) -> AgenticLanguageEcology {
        self.body
    }

    pub fn into_parts(self) -> (AgenticLanguageError, AgenticLanguageEcology) {
        (self.error, self.body)
    }
}

impl AgenticLanguageNativeRest {
    pub fn remount(self) -> Result<AgenticLanguageEcology, AgenticLanguageNativeRestRefusal> {
        if !self.body.pending_answer_stages_are_valid() {
            return Err(AgenticLanguageNativeRestRefusal {
                error: AgenticLanguageError::RestRemountMismatch,
                body: self.body,
            });
        }
        Ok(self.body)
    }
}

impl Default for AgenticLanguageSpec {
    fn default() -> Self {
        Self {
            generation: MorphologicalGenerationSpec {
                maximum_observed_tokens: 64,
            },
            thought_receiver_horizon: 16,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EpisodeOrigin {
    InheritedTrajectory,
    ReturnedWorld,
    ReturnedAnswer,
}

#[derive(Debug)]
struct LanguageEpisode {
    identity: String,
    origin: EpisodeOrigin,
    role: AgenticDialogueRole,
    revision: u64,
    answerable: bool,
    passages: Vec<MorphologicalLanguagePassage>,
    routing_surfaces: BTreeSet<String>,
    evidence_sources: BTreeSet<String>,
    /// The passage is the exact structural standing. A full recurrent factorization may be
    /// retained when already inherited, or realized from that standing only when a later current
    /// actually reaches the organ.
    ecology: Option<MorphologicalLanguageEcology>,
    relational_thought: Option<RelationalThoughtCurrent>,
    codec_versions: BTreeSet<String>,
}

#[derive(Debug)]
struct OpenQuestion {
    question: AgenticLanguageQuestion,
    deed: AgenticLanguageDeed,
    world_return: Option<AgenticLanguageWorldReturn>,
    relational_returned: bool,
    prepared_answer: Option<PreparedWorldAnswer>,
}

#[derive(Clone, Debug)]
struct PendingClarification {
    capabilities: BTreeSet<String>,
}

#[derive(Clone, Debug)]
struct AnswerLineage {
    world_deed: Option<String>,
    supporting_episodes: BTreeSet<String>,
    evidence_sources: BTreeSet<String>,
    surface: Vec<String>,
    question_surface: Vec<String>,
    codec_versions: BTreeSet<String>,
    cultivated_codec_paths: Vec<AgenticLanguageCodecPathReceipt>,
}

#[derive(Clone, Debug)]
struct ExactAnswerRegionFiber {
    required: LocalSet<AgenticAnswerRegionIdentity>,
    returned: LocalSet<AgenticAnswerRegionIdentity>,
}

impl ExactAnswerRegionFiber {
    fn from_parts(
        required: LocalSet<AgenticAnswerRegionIdentity>,
        returned: LocalSet<AgenticAnswerRegionIdentity>,
    ) -> Result<Self, AgenticLanguageError> {
        if !returned.iter().all(|region| required.contains(region)) {
            return Err(AgenticLanguageError::CarrierExtent);
        }
        Ok(Self { required, returned })
    }

    fn is_closed(&self) -> bool {
        self.returned == self.required
    }

    fn glue(&mut self, other: &Self) {
        self.required.extend(other.required.iter().copied());
        self.returned.extend(other.returned.iter().copied());
    }
}

#[derive(Clone, Debug)]
struct AnswerCandidate {
    generated: MorphologicalGeneratedCurrent,
    episode_identities: BTreeSet<String>,
    evidence_sources: BTreeSet<String>,
    conditioning_passages: Vec<MorphologicalLanguagePassage>,
    discharged_query_faces: BTreeSet<String>,
    reflection: MorphologicalReflectionReceipt,
    inherited_surfaces: Vec<Vec<String>>,
    received_prompt: String,
    contextual_dialogue: BTreeSet<String>,
    obligation_population: usize,
    local_region_fiber: ExactAnswerRegionFiber,
    ordered_query_regions: BTreeSet<Vec<String>>,
    revision_horizon: u64,
    corrective: bool,
    composed_current_population: usize,
    relational_thought: Option<RelationalThoughtCurrent>,
    relational_thoughts: Vec<RelationalThoughtCurrent>,
    codec_versions: BTreeSet<String>,
    cultivated_codec_paths: Vec<AgenticLanguageCodecPathReceipt>,
    /// Distinct maximal currents exposed by the same local receiver. They remain available to
    /// later receivers, but are never serialized onto `generated` merely because their evidence
    /// faces are incomparable.
    retained_alternatives: Vec<AgenticRetainedAnswerAlternative>,
}

#[derive(Debug)]
struct PreparedWorldAnswer {
    answer: Option<AgenticLanguageAnswer>,
    founded: Vec<LanguageEpisode>,
    lineage: Option<AnswerLineage>,
    dialogue: Option<AgenticDialogueOccurrence>,
    next_dialogue: u64,
    dialogue_occurrences: usize,
    next_episode: u64,
    locally_conditioned_episode_organs: usize,
    generated_answers: usize,
    next_founded_return: usize,
}

#[derive(Debug)]
struct PendingLocalAnswer {
    question: AgenticLanguageQuestion,
    prepared: PreparedWorldAnswer,
}

/// A continuing plural language body with a typed deed/return mouth.
#[derive(Debug)]
pub struct AgenticLanguageEcology {
    action: ActionCurrent,
    worker_threads: usize,
    spec: AgenticLanguageSpec,
    inherited_body: MorphologicalLanguageEcology,
    /// One continuing relation organ. Individual questions restrict this standing through their
    /// caused passage apertures; they do not rebuild private clause ecologies.
    relational_body: ExactRelationalLanguageEcology,
    inherited_cofaces: BTreeSet<(String, String)>,
    capabilities: BTreeMap<String, AgenticLanguageCapability>,
    trajectories: Vec<AgenticLanguageTrajectory>,
    action_surface_atlas: BTreeMap<String, BTreeSet<usize>>,
    episodes: Vec<LanguageEpisode>,
    episode_surface_atlas: BTreeMap<String, BTreeSet<usize>>,
    next_deed: u64,
    next_episode: u64,
    next_dialogue: u64,
    open: Option<OpenQuestion>,
    pending_local_answer: Option<PendingLocalAnswer>,
    pending_clarification: Option<PendingClarification>,
    dialogue: Vec<AgenticDialogueOccurrence>,
    dialogue_identities: BTreeSet<String>,
    obstructed_episodes: BTreeSet<String>,
    accepted_episodes: BTreeSet<String>,
    answer_lineages: BTreeMap<String, AnswerLineage>,
    relational_returns: AgenticRelationalReturnOwner,
    codec_runtime: AgenticReflectiveCodecRuntime,
    codec_continuation: ContinuationId,
    standing: AgenticLanguageStanding,
}
