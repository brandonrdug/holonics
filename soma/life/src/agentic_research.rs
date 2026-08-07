//! Typed research passage through the continuing agentic language body.
//!
//! This module is an application membrane, not another language policy.  One
//! [`AgenticLanguageEcology`] remains the body which receives a question, emits a deed, forms an
//! answer, retains feedback, and changes later conduct.  [`LaboratoryResearchEcology`] is a typed
//! exterior-research bridge: open relational boundaries cause further receiver regions directly
//! and return their complete plural fiber.  No host-authored English self-question schedules
//! thought.

use std::collections::BTreeSet;

use holonic_engine::CpuExecutor;
use holonic_structure::{CausalMembrane, LocalRelations, LocalSequence};
use serde::Serialize;

use crate::{
    agentic_language::{
        AgenticFormalReturn, AgenticFormalReturnReceipt, AgenticLanguageAnswer,
        AgenticLanguageConsequence, AgenticLanguageEcology, AgenticLanguageError,
        AgenticLanguageNativeRest, AgenticLanguageOccurrence, AgenticLanguageQuestion,
        AgenticLanguageWorldReturn,
    },
    causal_language::render_tokens,
    laboratory_language::{
        continuation_fiber_receipt, LaboratoryContinuationFiberReceipt,
        LaboratoryEmanatedCausalInformationReceipt, LaboratoryInformantPort,
        LaboratoryLanguageError, LaboratoryResearchDeliberation, LaboratoryResearchEcology,
        LaboratoryResearchLeader, LaboratoryResearchSpec, LaboratorySourceAtlas,
        LaboratoryThoughtStep, LaboratoryWorldContactAttempt, LaboratoryWorldContactRequest,
        LaboratoryWorldReturn,
    },
    lean_mathematics::{
        LeanDiagnosisCurrentFace, LeanMathematicsEcology, LeanMathematicsError,
        LeanTargetSelectionReceipt, LeanTheoremTargetRequest,
    },
    morphological_language::MorphologicalLanguagePassage,
    text_material::{CudaResidentTextMaterialAtlas, TextMaterialCudaContactReceipt},
};

mod open_completion;

use open_completion::OpenAgenticResearchCompletion;

/// Mounted repository and resident-card informants behind one typed contact front.
///
/// The two owners preserve their own identities and apparatus testimony. Their returns are glued
/// in the research-owned address order; no independence or commutation law is asserted.
pub struct MountedResearchInformantWorld {
    repository: LaboratorySourceAtlas,
    resident_text: CudaResidentTextMaterialAtlas,
    repository_executor: CpuExecutor,
    card_apparatus: LocalSequence<TextMaterialCudaContactReceipt>,
}

impl MountedResearchInformantWorld {
    pub fn new(
        repository: LaboratorySourceAtlas,
        resident_text: CudaResidentTextMaterialAtlas,
        worker_aperture: usize,
    ) -> Result<Self, AgenticResearchError> {
        if worker_aperture == 0 {
            return Err(AgenticResearchError::CarrierExtent);
        }
        let repository_executor = if worker_aperture == 1 {
            CpuExecutor::serial()
        } else {
            CpuExecutor::multicore(
                std::num::NonZeroUsize::new(worker_aperture)
                    .ok_or(AgenticResearchError::CarrierExtent)?,
            )
        };
        Ok(Self {
            repository,
            resident_text,
            repository_executor,
            card_apparatus: LocalSequence::new(),
        })
    }

    pub fn enact_contact_front(
        &mut self,
        requests: &[LaboratoryWorldContactRequest],
    ) -> LaboratoryWorldContactAttempt {
        let mut repository_requests = LocalSequence::new();
        let mut card_requests = LocalSequence::new();
        for request in requests {
            match request.port {
                LaboratoryInformantPort::RepositorySource => {
                    repository_requests.push(request.to_owned());
                }
                LaboratoryInformantPort::ResidentTextCard => {
                    card_requests.push(request.to_owned());
                }
            }
        }
        let repository_attempt = self
            .repository
            .enact_contact_front_with_cpu(&repository_requests, &self.repository_executor);
        let card_attempt = self.resident_text.enact_contact_front(&card_requests);
        self.card_apparatus.extend(card_attempt.apparatus);
        LaboratoryWorldContactAttempt::compose(
            requests,
            [repository_attempt, card_attempt.semantic],
        )
        .expect("typed informant owners must return exactly the research-owned contact address")
    }

    pub fn resident_text_mut(&mut self) -> &mut CudaResidentTextMaterialAtlas {
        &mut self.resident_text
    }

    pub const fn repository(&self) -> &LaboratorySourceAtlas {
        &self.repository
    }

    pub fn card_apparatus(&self) -> &[TextMaterialCudaContactReceipt] {
        &self.card_apparatus
    }

    pub fn into_parts(
        self,
    ) -> (
        LaboratorySourceAtlas,
        CudaResidentTextMaterialAtlas,
        LocalSequence<TextMaterialCudaContactReceipt>,
    ) {
        (self.repository, self.resident_text, self.card_apparatus)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AgenticResearchError {
    EmptyQuestion,
    CarrierExtent,
    WrongCapability { expected: String, received: String },
    NoReturnedSection,
    NoThoughtFiber,
    NoClosedCurrent,
    UnexpectedConsequence(String),
    NativeRestMismatch,
    Agentic(AgenticLanguageError),
    Laboratory(LaboratoryLanguageError),
    Lean(LeanMathematicsError),
}

impl From<AgenticLanguageError> for AgenticResearchError {
    fn from(error: AgenticLanguageError) -> Self {
        Self::Agentic(error)
    }
}

impl From<LaboratoryLanguageError> for AgenticResearchError {
    fn from(error: LaboratoryLanguageError) -> Self {
        Self::Laboratory(error)
    }
}

impl From<LeanMathematicsError> for AgenticResearchError {
    fn from(error: LeanMathematicsError) -> Self {
        Self::Lean(error)
    }
}

impl std::fmt::Display for AgenticResearchError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyQuestion => formatter.write_str("the agentic research question is empty"),
            Self::CarrierExtent => formatter.write_str("the agentic research carrier overflowed"),
            Self::WrongCapability { expected, received } => write!(
                formatter,
                "the research membrane realizes {expected:?}, not returned deed {received:?}"
            ),
            Self::NoReturnedSection => {
                formatter.write_str("the typed research deed returned no language section")
            }
            Self::NoThoughtFiber => {
                formatter.write_str("the typed research deed formed no relational fiber")
            }
            Self::NoClosedCurrent => formatter.write_str(
                "the typed research deed rested without a locally closed current; no answer was projected",
            ),
            Self::UnexpectedConsequence(consequence) => {
                write!(formatter, "the research passage returned {consequence}")
            }
            Self::NativeRestMismatch => {
                formatter.write_str("the native research body changed across suspension")
            }
            Self::Agentic(error) => write!(formatter, "agentic language obstruction: {error:?}"),
            Self::Laboratory(error) => {
                write!(formatter, "laboratory research obstruction: {error:?}")
            }
            Self::Lean(error) => write!(formatter, "Lean mathematics obstruction: {error:?}"),
        }
    }
}

impl std::error::Error for AgenticResearchError {}

/// Complete typed motion which preceded one outward answer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticResearchThoughtReceipt {
    pub question: String,
    pub deed: String,
    pub leaders: Vec<LaboratoryResearchLeader>,
    pub returns: Vec<LaboratoryWorldReturn>,
    pub waves: Vec<LaboratoryThoughtStep>,
    /// Observer faces of the co-present deliberative and connected-question currents. The live
    /// deed fibers remain encapsulated by the language owner.
    pub continuation_fibers: LocalSequence<LaboratoryContinuationFiberReceipt>,
    pub conditioned_passages_before: usize,
    pub conditioned_passages_after: usize,
    /// The research owner's native before/world/emanated-answer information receipt. This is
    /// preserved whole rather than manually reconstructing its continuation fibers in the
    /// application.
    pub information: LaboratoryEmanatedCausalInformationReceipt,
}

#[derive(Debug)]
pub struct AgenticResearchAnswer {
    pub answer: AgenticLanguageAnswer,
    pub thought: Option<AgenticResearchThoughtReceipt>,
}

/// Exact source-independent suspension receipt for the complete continuing research session.
///
/// Both bodies are transferred in place. No inherited passage, dialogue occurrence, research
/// source, or exterior atlas is replayed to reconstruct either morphology.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct AgenticResearchNativeRestReceipt {
    pub agent_native_rest_exact: bool,
    pub research_native_rest_exact: bool,
    pub source_replay_performed: bool,
}

#[derive(Debug)]
pub struct AgenticResearchNativeRest {
    agent: AgenticLanguageNativeRest,
    research: LaboratoryResearchEcology,
    research_capability: String,
    next_question: u64,
    open_completion: Option<OpenAgenticResearchCompletion>,
}

#[derive(Debug)]
pub struct AgenticResearchNativeRestRefusal {
    pub error: AgenticResearchError,
    body: AgenticResearchSession,
}

impl AgenticResearchNativeRestRefusal {
    pub fn recover(self) -> AgenticResearchSession {
        self.body
    }

    pub fn into_parts(self) -> (AgenticResearchError, AgenticResearchSession) {
        (self.error, self.body)
    }
}

impl AgenticResearchNativeRest {
    pub fn remount(
        self,
    ) -> Result<
        (AgenticResearchSession, AgenticResearchNativeRestReceipt),
        AgenticResearchNativeRestRefusal,
    > {
        let Self {
            agent,
            research,
            research_capability,
            next_question,
            open_completion,
        } = self;
        let agent = match agent.remount() {
            Ok(agent) => agent,
            Err(refusal) => {
                let (error, agent) = refusal.into_parts();
                return Err(AgenticResearchNativeRestRefusal {
                    error: AgenticResearchError::Agentic(error),
                    body: AgenticResearchSession {
                        agent,
                        research,
                        research_capability,
                        next_question,
                        open_completion,
                    },
                });
            }
        };
        let completion_is_consistent = open_completion.as_ref().map_or_else(
            || agent.open_deed().is_none() && research.open_deed_identity().is_none(),
            |open| open.is_consistent(&agent, &research),
        );
        if !completion_is_consistent {
            return Err(AgenticResearchNativeRestRefusal {
                error: AgenticResearchError::NativeRestMismatch,
                body: AgenticResearchSession {
                    agent,
                    research,
                    research_capability,
                    next_question,
                    open_completion,
                },
            });
        }
        let body = AgenticResearchSession {
            agent,
            research,
            research_capability,
            next_question,
            open_completion,
        };
        Ok((
            body,
            AgenticResearchNativeRestReceipt {
                agent_native_rest_exact: true,
                research_native_rest_exact: true,
                source_replay_performed: false,
            },
        ))
    }
}

/// One continuing language intelligence plus one typed research organ.
#[derive(Debug)]
pub struct AgenticResearchSession {
    agent: AgenticLanguageEcology,
    research: LaboratoryResearchEcology,
    research_capability: String,
    next_question: u64,
    open_completion: Option<OpenAgenticResearchCompletion>,
}

fn deliberation_world_sections(
    deliberation: &LaboratoryResearchDeliberation,
) -> Vec<MorphologicalLanguagePassage> {
    let mut returned = LocalRelations::<String, MorphologicalLanguagePassage>::new();
    for world_return in &deliberation.returns {
        for section in &world_return.sections {
            if !returned.contains(&section.source_identity) {
                returned.insert(section.source_identity.to_owned(), section.passage());
            }
        }
    }
    let mut sections = LocalSequence::with_capacity(returned.len());
    for (_, passage) in returned {
        sections.push(passage);
    }
    sections.into_inner()
}

fn staged_research_standing_matches(
    research: &LaboratoryResearchEcology,
    deliberation: &LaboratoryResearchDeliberation,
    information: Option<&LaboratoryEmanatedCausalInformationReceipt>,
) -> bool {
    let continuation_after_world = deliberation.fiber.as_ref().map(continuation_fiber_receipt);
    match information {
        None => {
            research.conditioned_passages() == deliberation.conditioned_passages_after
                && research.relational_clauses() == deliberation.relational_clauses_after
        }
        Some(information) => {
            information.conditioned_passages_before == deliberation.conditioned_passages_before
                && information.conditioned_passages_after_world
                    == deliberation.conditioned_passages_after
                && information.relational_clauses_before == deliberation.relational_clauses_before
                && information.relational_clauses_after_world
                    == deliberation.relational_clauses_after
                && information.continuation_before_contact
                    == deliberation.continuation_before_contact
                && information.continuation_after_world == continuation_after_world
                && research.conditioned_passages()
                    == information.conditioned_passages_after_emanated_answer
                && research.relational_clauses()
                    == information.relational_clauses_after_emanated_answer
                && research
                    .inspect_deliberative_continuation(&deliberation.question)
                    .ok()
                    .as_ref()
                    == Some(&information.continuation_after_emanated_answer_return)
        }
    }
}

impl AgenticResearchSession {
    pub fn new(
        agent: AgenticLanguageEcology,
        research_capability: impl Into<String>,
        research_spec: LaboratoryResearchSpec,
    ) -> Self {
        Self {
            agent,
            research: LaboratoryResearchEcology::new(research_spec),
            research_capability: research_capability.into(),
            next_question: 0,
            open_completion: None,
        }
    }

    pub const fn agent(&self) -> &AgenticLanguageEcology {
        &self.agent
    }

    pub fn agent_mut(&mut self) -> &mut AgenticLanguageEcology {
        &mut self.agent
    }

    pub const fn research(&self) -> &LaboratoryResearchEcology {
        &self.research
    }

    /// Issue a closed, removal-minimal diagnosis from the exact pre-answer current selected by
    /// the language receiver. Co-present currents remain owner-retained alternatives; their
    /// multiplicity does not replace or obstruct the current which actually caused this answer.
    pub fn reify_lean_diagnosis(
        &self,
        answer_episode: &str,
    ) -> Result<LeanDiagnosisCurrentFace, AgenticResearchError> {
        if self.has_open_deed() {
            return Err(AgenticResearchError::UnexpectedConsequence(
                "a diagnosis cannot be reified while its outer deed remains open".to_owned(),
            ));
        }
        let selected = self
            .agent
            .answer_selected_relational_current(answer_episode)
            .ok_or(AgenticResearchError::NoClosedCurrent)?;
        let current = selected.current;
        let target = self.agent.reify_answer_codec_face(answer_episode)?;
        LeanDiagnosisCurrentFace::from_closed_current(
            answer_episode.to_owned(),
            current.question.to_owned(),
            LocalSequence::from_iter(
                current
                    .clauses
                    .iter()
                    .map(|clause| clause.identity.to_owned()),
            ),
            holonic_structure::LocalSet::from_iter(current.source_witnesses.iter().cloned()),
            holonic_structure::LocalSet::from_iter(current.passage_witnesses.iter().cloned()),
            LocalSequence::from_iter(
                current
                    .required_entity_regions
                    .iter()
                    .map(|region| holonic_structure::LocalSet::from_iter(region.iter().cloned())),
            ),
            holonic_structure::LocalSet::from_iter(
                current
                    .returned_entity_regions
                    .iter()
                    .filter_map(|at| current.required_entity_regions.get(*at))
                    .map(|region| holonic_structure::LocalSet::from_iter(region.iter().cloned())),
            ),
            selected.minimal_closed_witness_family,
            holonic_structure::LocalSet::from_iter(target.lineage.iter().cloned()),
        )
        .ok_or(AgenticResearchError::NoClosedCurrent)
    }

    /// Cross an exact theorem family only through a diagnosis currently issued by these owners.
    pub fn select_and_open_lean_kernel_deed(
        &self,
        lean: &mut LeanMathematicsEcology,
        request: LeanTheoremTargetRequest,
    ) -> Result<LeanTargetSelectionReceipt, AgenticResearchError> {
        let issued = self.reify_lean_diagnosis(&request.target_episode)?;
        if request.diagnosis != issued {
            return Err(AgenticResearchError::NativeRestMismatch);
        }
        lean.select_and_open_kernel_deed(request)
            .map_err(Into::into)
    }

    /// Suspend both continuing bodies by ownership transfer, without replaying their sources.
    pub fn into_native_rest(
        self,
    ) -> Result<AgenticResearchNativeRest, AgenticResearchNativeRestRefusal> {
        let Self {
            agent,
            research,
            research_capability,
            next_question,
            open_completion,
        } = self;
        match agent.into_native_rest() {
            Ok(agent) => Ok(AgenticResearchNativeRest {
                agent,
                research,
                research_capability,
                next_question,
                open_completion,
            }),
            Err(refusal) => {
                let (error, agent) = refusal.into_parts();
                Err(AgenticResearchNativeRestRefusal {
                    error: AgenticResearchError::Agentic(error),
                    body: Self {
                        agent,
                        research,
                        research_capability,
                        next_question,
                        open_completion,
                    },
                })
            }
        }
    }

    /// Receive one visible question, enact any emitted research deed, and return the actual
    /// generated answer with the complete motion which caused it.
    pub fn converse_with_world_front(
        &mut self,
        receiver: u64,
        question: &str,
        mut enact: impl FnMut(&[LaboratoryWorldContactRequest]) -> LaboratoryWorldContactAttempt,
    ) -> Result<AgenticResearchAnswer, AgenticResearchError> {
        if question.trim().is_empty() {
            return Err(AgenticResearchError::EmptyQuestion);
        }
        if self.has_open_deed() {
            return Err(AgenticResearchError::UnexpectedConsequence(
                "a new question cannot cross an open research completion".to_owned(),
            ));
        }
        let question_identity = format!("agentic-research-question-{}", self.next_question);
        self.next_question = self
            .next_question
            .checked_add(1)
            .ok_or(AgenticResearchError::CarrierExtent)?;
        let question = AgenticLanguageQuestion::new(question_identity, receiver, question);
        let consequence = self
            .agent
            .receive_occurrence(AgenticLanguageOccurrence::Question(&question))?;
        match consequence {
            AgenticLanguageConsequence::Answer(answer) => self.finish(answer, None),
            AgenticLanguageConsequence::Deed(deed) => {
                self.complete_deed_with_world(deed, &mut enact)
            }
            AgenticLanguageConsequence::Clarification(clarification) => {
                Err(AgenticResearchError::UnexpectedConsequence(format!(
                    "clarification {}: {}",
                    clarification.identity, clarification.text
                )))
            }
            AgenticLanguageConsequence::Feedback(feedback) => {
                Err(AgenticResearchError::UnexpectedConsequence(format!(
                    "feedback {}",
                    feedback.feedback.identity
                )))
            }
            AgenticLanguageConsequence::FormalReturn(returned) => {
                Err(AgenticResearchError::UnexpectedConsequence(format!(
                    "formal return {}",
                    returned.identity
                )))
            }
        }
    }

    /// Whether an exterior deed has departed and still owes a return.
    pub fn has_open_deed(&self) -> bool {
        self.open_completion.is_some() || self.agent.open_deed().is_some()
    }

    /// Return one complete Lean-owned theorem fiber through the ordinary typed language mouth.
    /// Formal cultivation cannot overlap an exterior research deed.
    pub fn receive_formal_return(
        &mut self,
        returned: &AgenticFormalReturn,
    ) -> Result<AgenticFormalReturnReceipt, AgenticResearchError> {
        if self.has_open_deed() {
            return Err(AgenticResearchError::UnexpectedConsequence(
                "a formal return cannot cross an open research deed".to_owned(),
            ));
        }
        match self
            .agent
            .receive_occurrence(AgenticLanguageOccurrence::FormalReturn(returned))?
        {
            AgenticLanguageConsequence::FormalReturn(receipt) => Ok(receipt),
            other => Err(AgenticResearchError::UnexpectedConsequence(format!(
                "formal occurrence returned {other:?}"
            ))),
        }
    }

    /// Resume the exact already-open deed after an exterior or substrate refusal. No new user
    /// question, deed identity, or language body is manufactured for the retry.
    pub fn retry_open_with_world_front(
        &mut self,
        mut enact: impl FnMut(&[LaboratoryWorldContactRequest]) -> LaboratoryWorldContactAttempt,
    ) -> Result<AgenticResearchAnswer, AgenticResearchError> {
        let open = self.open_completion.take().ok_or_else(|| {
            AgenticResearchError::UnexpectedConsequence(
                "no exterior deed is open for retry".to_owned(),
            )
        })?;
        match self.advance_open_completion(open, &mut enact) {
            Ok(answer) => Ok(answer),
            Err((error, open)) => {
                self.open_completion = Some(open);
                Err(error)
            }
        }
    }

    fn complete_deed_with_world(
        &mut self,
        deed: crate::agentic_language::AgenticLanguageDeed,
        enact: &mut impl FnMut(&[LaboratoryWorldContactRequest]) -> LaboratoryWorldContactAttempt,
    ) -> Result<AgenticResearchAnswer, AgenticResearchError> {
        if deed.capability.identity != self.research_capability {
            return Err(AgenticResearchError::WrongCapability {
                expected: self.research_capability.to_owned(),
                received: deed.capability.identity,
            });
        }
        if let Some(open) = &self.open_completion {
            if open.deed() != &deed {
                return Err(AgenticResearchError::UnexpectedConsequence(format!(
                    "research completion {} is already open",
                    open.deed().identity
                )));
            }
        } else {
            self.open_completion = Some(OpenAgenticResearchCompletion::new(deed));
        }

        let open = self
            .open_completion
            .take()
            .expect("the exact research completion was founded above");
        match self.advance_open_completion(open, enact) {
            Ok(answer) => Ok(answer),
            Err((error, open)) => {
                self.open_completion = Some(open);
                Err(error)
            }
        }
    }

    fn advance_open_completion(
        &mut self,
        mut open: OpenAgenticResearchCompletion,
        enact: &mut impl FnMut(&[LaboratoryWorldContactRequest]) -> LaboratoryWorldContactAttempt,
    ) -> Result<AgenticResearchAnswer, (AgenticResearchError, OpenAgenticResearchCompletion)> {
        loop {
            open = match open {
                OpenAgenticResearchCompletion::Researching { deed } => {
                    match self.research.deliberate_until_return_with_world_front(
                        &deed.identity,
                        &deed.received_prompt,
                        &mut *enact,
                    ) {
                        Ok(deliberation) => {
                            OpenAgenticResearchCompletion::WorldReturned { deed, deliberation }
                        }
                        Err(error) => {
                            return Err((
                                error.into(),
                                OpenAgenticResearchCompletion::Researching { deed },
                            ));
                        }
                    }
                }
                OpenAgenticResearchCompletion::WorldReturned { deed, deliberation } => {
                    let world_return = match self.form_agentic_world_return(&deed, &deliberation) {
                        Ok(returned) => returned,
                        Err(error) => {
                            return Err((
                                error,
                                OpenAgenticResearchCompletion::WorldReturned { deed, deliberation },
                            ));
                        }
                    };
                    OpenAgenticResearchCompletion::Answering {
                        deed,
                        deliberation,
                        world_return,
                    }
                }
                OpenAgenticResearchCompletion::Answering {
                    deed,
                    deliberation,
                    world_return,
                } => {
                    let continuation_fibers = LocalSequence::from_iter(
                        world_return
                            .thought_fibers
                            .iter()
                            .map(continuation_fiber_receipt),
                    );
                    match self
                        .agent
                        .receive_occurrence(AgenticLanguageOccurrence::WorldReturn(&world_return))
                    {
                        Ok(AgenticLanguageConsequence::Answer(answer)) => {
                            OpenAgenticResearchCompletion::ReturningAnswer {
                                deed,
                                deliberation,
                                answer,
                                continuation_fibers,
                            }
                        }
                        Ok(other) => {
                            return Err((
                                AgenticResearchError::UnexpectedConsequence(format!("{other:?}")),
                                OpenAgenticResearchCompletion::Answering {
                                    deed,
                                    deliberation,
                                    world_return,
                                },
                            ));
                        }
                        Err(error) => {
                            return Err((
                                error.into(),
                                OpenAgenticResearchCompletion::Answering {
                                    deed,
                                    deliberation,
                                    world_return,
                                },
                            ));
                        }
                    }
                }
                OpenAgenticResearchCompletion::ReturningAnswer {
                    deed,
                    deliberation,
                    answer,
                    continuation_fibers,
                } => {
                    let information =
                        match self.return_answer_phases_to_research(&answer, &deliberation) {
                            Ok(information) => information,
                            Err(error) => {
                                return Err((
                                    error,
                                    OpenAgenticResearchCompletion::ReturningAnswer {
                                        deed,
                                        deliberation,
                                        answer,
                                        continuation_fibers,
                                    },
                                ));
                            }
                        };
                    let thought = AgenticResearchThoughtReceipt {
                        question: deliberation.question,
                        deed: deed.identity,
                        leaders: deliberation.leaders,
                        returns: deliberation.returns,
                        waves: deliberation.thought_steps,
                        continuation_fibers,
                        conditioned_passages_before: deliberation.conditioned_passages_before,
                        conditioned_passages_after: deliberation.conditioned_passages_after,
                        information,
                    };
                    return Ok(AgenticResearchAnswer {
                        answer,
                        thought: Some(thought),
                    });
                }
            };
        }
    }

    fn form_agentic_world_return(
        &self,
        deed: &crate::agentic_language::AgenticLanguageDeed,
        deliberation: &LaboratoryResearchDeliberation,
    ) -> Result<AgenticLanguageWorldReturn, AgenticResearchError> {
        let deliberative_fiber = deliberation
            .fiber
            .to_owned()
            .ok_or(AgenticResearchError::NoThoughtFiber)?;
        let mut fibers = vec![deliberative_fiber];
        if let Some(connected) = self
            .research
            .inspect_connected_question_fiber(&deed.received_prompt)?
        {
            if !fibers.contains(&connected) {
                fibers.push(connected);
            }
        }
        if fibers.iter().all(|fiber| fiber.closed().next().is_none()) {
            return Err(AgenticResearchError::NoClosedCurrent);
        }

        let mut returned = LocalRelations::<String, MorphologicalLanguagePassage>::new();
        for world_return in &deliberation.returns {
            for section in &world_return.sections {
                if !returned.contains(&section.source_identity) {
                    returned.insert(section.source_identity.to_owned(), section.passage());
                }
            }
        }
        if returned.is_empty() {
            return Err(AgenticResearchError::NoReturnedSection);
        }
        let mut returned_sections = LocalSequence::with_capacity(returned.len());
        for (_, passage) in returned {
            returned_sections.push(passage);
        }
        Ok(AgenticLanguageWorldReturn::new(
            deed.identity.to_owned(),
            returned_sections.into_inner(),
        )
        .with_thought_fibers(fibers))
    }
    fn return_answer_phases_to_research(
        &mut self,
        answer: &AgenticLanguageAnswer,
        deliberation: &LaboratoryResearchDeliberation,
    ) -> Result<LaboratoryEmanatedCausalInformationReceipt, AgenticResearchError> {
        let mut passages = LocalSequence::new();
        for (phase_at, phase) in answer.generated.phases.iter().enumerate() {
            let tokens = answer
                .generated
                .tokens
                .get(phase.emitted_start..phase.emitted_end)
                .ok_or(AgenticResearchError::CarrierExtent)?;
            passages.push(MorphologicalLanguagePassage::new(
                format!(
                    "{}/research-return/{phase_at}",
                    answer.answer_episode_identity
                ),
                format!("agentic-answer/{}", answer.answer_episode_identity),
                answer.question.receiver,
                render_tokens(tokens.iter().map(|token| token.token.as_str())),
            ));
        }
        if passages.is_empty() {
            passages.push(MorphologicalLanguagePassage::new(
                format!("{}/research-return", answer.answer_episode_identity),
                format!("agentic-answer/{}", answer.answer_episode_identity),
                answer.question.receiver,
                answer.text.to_owned(),
            ));
        }
        self.research
            .receive_emanated_answer_passages(deliberation, &passages, answer_causes(answer))
            .map_err(Into::into)
    }

    fn finish(
        &self,
        answer: AgenticLanguageAnswer,
        thought: Option<AgenticResearchThoughtReceipt>,
    ) -> Result<AgenticResearchAnswer, AgenticResearchError> {
        Ok(AgenticResearchAnswer { answer, thought })
    }
}

/// Exact source identities which caused the outward answer, suitable for returning the answer to
/// a separate text atlas without fabricating chronology as parentage.
pub fn answer_causes(answer: &AgenticLanguageAnswer) -> BTreeSet<String> {
    let mut causes = answer.evidence_sources.to_owned();
    causes.extend(answer.supporting_episode_identities.iter().cloned());
    causes.extend(
        answer
            .relational_thoughts
            .iter()
            .flat_map(|thought| thought.passage_witnesses.iter().cloned()),
    );
    if let Some(deed) = &answer.world_deed {
        causes.insert(deed.to_owned());
    }
    causes
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::Cog;
    use soma_abi::active::ActionCurrent;

    use crate::{
        agentic_language::{AgenticLanguageCapability, AgenticLanguageSpec},
        laboratory_language::{
            LaboratoryInformantPort, LaboratoryReturnedSection, LaboratorySourceKind,
            LaboratoryWorldContactOutcome, LaboratoryWorldContactReturn,
        },
        lean_mathematics::{
            LeanDiagnosisRequirement, LeanKernelWorld, LeanMathematicsEcology, LeanProofProblem,
            LeanSourceDocument, LeanTargetSelectionReceipt, LeanTheoremTargetFace,
            LeanTheoremTargetRequest,
        },
    };

    fn returned_attempt(
        requests: &[LaboratoryWorldContactRequest],
    ) -> LaboratoryWorldContactAttempt {
        let mut outcomes = LocalSequence::with_capacity(requests.len());
        for request in requests {
            outcomes.push(LaboratoryWorldContactOutcome::Returned(
                LaboratoryWorldContactReturn {
                    identity: request.identity.to_owned(),
                    leader: request.leader.identity.to_owned(),
                    port: request.port,
                    returned: LaboratoryWorldReturn {
                        leader: request.leader.identity.to_owned(),
                        sections: vec![LaboratoryReturnedSection {
                            identity: format!(
                                "{}/{:?}/world-section",
                                request.leader.identity, request.port
                            ),
                            source_identity: format!("world-section/{:?}", request.port),
                            source: "research-world".to_owned(),
                            receiver: 91,
                            line: 0,
                            kind: LaboratorySourceKind::Theory,
                            text: "The function locally reconstructs relational ecology. This call path carries a continuity obstruction for relational morphology.".to_owned(),
                            matched_features: request.leader.region.to_owned(),
                        }],
                        complete_population: 1,
                        omitted_population: 0,
                    },
                },
            ));
        }
        LaboratoryWorldContactAttempt {
            outcomes,
            execution: None,
        }
    }

    fn glued_returned_attempt(
        requests: &[LaboratoryWorldContactRequest],
    ) -> LaboratoryWorldContactAttempt {
        let mut outcomes = LocalSequence::with_capacity(requests.len());
        for request in requests {
            outcomes.push(LaboratoryWorldContactOutcome::Returned(
                LaboratoryWorldContactReturn {
                    identity: request.identity.to_owned(),
                    leader: request.leader.identity.to_owned(),
                    port: request.port,
                    returned: LaboratoryWorldReturn {
                        leader: request.leader.identity.to_owned(),
                        sections: vec![LaboratoryReturnedSection {
                            identity: "shared-world-section".to_owned(),
                            source_identity: "shared-world-section".to_owned(),
                            source: "research-world".to_owned(),
                            receiver: 91,
                            line: 0,
                            kind: LaboratorySourceKind::Theory,
                            text: "The function locally reconstructs relational ecology. This call path carries a continuity obstruction for relational morphology.".to_owned(),
                            matched_features: request.leader.region.to_owned(),
                        }],
                        complete_population: 1,
                        omitted_population: 0,
                    },
                },
            ));
        }
        LaboratoryWorldContactAttempt {
            outcomes,
            execution: None,
        }
    }

    fn formal_reflection_attempt(
        requests: &[LaboratoryWorldContactRequest],
    ) -> LaboratoryWorldContactAttempt {
        let mut outcomes = LocalSequence::with_capacity(requests.len());
        for request in requests {
            outcomes.push(LaboratoryWorldContactOutcome::Returned(
                LaboratoryWorldContactReturn {
                    identity: request.identity.to_owned(),
                    leader: request.leader.identity.to_owned(),
                    port: request.port,
                    returned: LaboratoryWorldReturn {
                        leader: request.leader.identity.to_owned(),
                        sections: vec![LaboratoryReturnedSection {
                            identity: "formal-reflection-world-section".to_owned(),
                            source_identity: "formal-reflection-world-section".to_owned(),
                            source: "research-world".to_owned(),
                            receiver: 91,
                            line: 0,
                            kind: LaboratorySourceKind::Theory,
                            text: "The formal proof carries a Lean kernel return. The Lean kernel return carries the continuity obstruction for relational morphology."
                                .to_owned(),
                            matched_features: request.leader.region.to_owned(),
                        }],
                        complete_population: 1,
                        omitted_population: 0,
                    },
                },
            ));
        }
        LaboratoryWorldContactAttempt {
            outcomes,
            execution: None,
        }
    }

    fn research_session() -> AgenticResearchSession {
        let action = ActionCurrent::new(Cog::lit(1)).unwrap();
        let agent = AgenticLanguageEcology::condition(
            &[MorphologicalLanguagePassage::new(
                "language-body",
                "language-body",
                3,
                "A returned relation changes the continuing language body.",
            )],
            &[AgenticLanguageCapability::new("research-world", 70).with_open_boundary()],
            &[],
            AgenticLanguageSpec::default(),
            action,
            2,
        )
        .unwrap();
        AgenticResearchSession::new(
            agent,
            "research-world",
            LaboratoryResearchSpec {
                leader_aperture: 8,
                worker_threads: 1,
                thought_receiver_horizon: 16,
            },
        )
    }

    fn formal_problem() -> LeanProofProblem {
        let source_scope = ["Soma/Exact.lean".to_owned()].into();
        LeanProofProblem {
            identity: "formal_carry".to_owned(),
            source_scope,
            prefix: "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\nvariable (P : Prop)"
                .to_owned(),
            theorem_header: "theorem formal_carry (h : P) : exactCarrier P".to_owned(),
            suffix: "end Soma".to_owned(),
        }
    }

    #[test]
    fn connected_closure_speaks_beside_the_wider_open_receiver_fiber() {
        let action = ActionCurrent::new(Cog::lit(1)).unwrap();
        let agent = AgenticLanguageEcology::condition(
            &[MorphologicalLanguagePassage::new(
                "language-body",
                "language-body",
                3,
                "A returned relation changes the continuing language body.",
            )],
            &[AgenticLanguageCapability::new("research-world", 70).with_open_boundary()],
            &[],
            AgenticLanguageSpec::default(),
            action,
            2,
        )
        .unwrap();
        let mut session = AgenticResearchSession::new(
            agent,
            "research-world",
            LaboratoryResearchSpec {
                leader_aperture: 8,
                worker_threads: 1,
                thought_receiver_horizon: 16,
            },
        );
        let answer = session
            .converse_with_world_front(
                90,
                "What carries a continuity obstruction for relational morphology?",
                glued_returned_attempt,
            )
            .unwrap();
        let thought = answer
            .thought
            .as_ref()
            .expect("the deed must carry thought");
        assert!(thought
            .continuation_fibers
            .iter()
            .any(|fiber| fiber.closed_current_population > 0));
        assert!(answer.answer.relational_thought.is_some());
        assert!(answer.answer.world_deed.is_some());
        assert!(
            thought
                .information
                .conditioned_passages_after_emanated_answer
                > thought.information.conditioned_passages_after_world
        );
        assert!(thought
            .information
            .continuation_after_emanated_answer_return
            .is_some());
        let native = session.into_native_rest().unwrap();
        let (_session, native_receipt) = native.remount().unwrap();
        assert!(native_receipt.agent_native_rest_exact);
        assert!(native_receipt.research_native_rest_exact);
        assert!(!native_receipt.source_replay_performed);
    }

    #[test]
    fn exterior_refusal_retains_the_deed_for_retry() {
        let action = ActionCurrent::new(Cog::lit(1)).unwrap();
        let agent = AgenticLanguageEcology::condition(
            &[MorphologicalLanguagePassage::new(
                "language-body",
                "language-body",
                3,
                "A returned relation changes the continuing language body.",
            )],
            &[AgenticLanguageCapability::new("research-world", 70).with_open_boundary()],
            &[],
            AgenticLanguageSpec::default(),
            action,
            2,
        )
        .unwrap();
        let mut session = AgenticResearchSession::new(
            agent,
            "research-world",
            LaboratoryResearchSpec {
                leader_aperture: 8,
                worker_threads: 1,
                thought_receiver_horizon: 16,
            },
        );
        let refused = session.converse_with_world_front(
            90,
            "What carries a continuity obstruction for relational morphology?",
            |requests| {
                let mut outcomes = LocalSequence::with_capacity(requests.len());
                for request in requests {
                    let outcome = if request.port == LaboratoryInformantPort::RepositorySource {
                        let mut returned = returned_attempt(std::slice::from_ref(request)).outcomes;
                        returned.remove(0)
                    } else {
                        LaboratoryWorldContactOutcome::Obstructed {
                            identity: request.identity.to_owned(),
                            obstruction: "card refused".to_owned(),
                        }
                    };
                    outcomes.push(outcome);
                }
                LaboratoryWorldContactAttempt {
                    outcomes,
                    execution: None,
                }
            },
        );
        assert!(matches!(refused, Err(AgenticResearchError::Laboratory(_))));
        assert!(session.has_open_deed());

        let answer = session
            .retry_open_with_world_front(returned_attempt)
            .unwrap();
        assert!(!answer.answer.text.is_empty());
        assert!(!session.has_open_deed());
    }

    #[test]
    fn answer_return_refusal_keeps_the_outer_deed_and_cannot_replay_prior_mouths() {
        let action = ActionCurrent::new(Cog::lit(1)).unwrap();
        let agent = AgenticLanguageEcology::condition(
            &[MorphologicalLanguagePassage::new(
                "language-body",
                "language-body",
                3,
                "A returned relation changes the continuing language body.",
            )],
            &[AgenticLanguageCapability::new("research-world", 70).with_open_boundary()],
            &[],
            AgenticLanguageSpec::default(),
            action,
            2,
        )
        .unwrap();
        let mut session = AgenticResearchSession::new(
            agent,
            "research-world",
            LaboratoryResearchSpec {
                leader_aperture: 8,
                worker_threads: 1,
                thought_receiver_horizon: 16,
            },
        );
        let next_episode = session.agent.rest_receipt().unwrap().next_episode;
        session
            .research
            .receive_test_passages(&[MorphologicalLanguagePassage::new(
                format!("episode-{next_episode}/answer/research-return/0"),
                "foreign-answer-return",
                90,
                "A foreign occurrence occupies this exact identity with changed testimony.",
            )])
            .unwrap();

        let refused = session.converse_with_world_front(
            90,
            "What carries a continuity obstruction for relational morphology?",
            returned_attempt,
        );
        assert!(refused.is_err());
        let open = session
            .open_completion
            .as_ref()
            .expect("the outer completion survives the answer-return refusal");
        assert!(matches!(
            open,
            OpenAgenticResearchCompletion::ReturningAnswer { .. }
        ));
        assert!(session.agent.open_deed().is_none());
        assert!(session.has_open_deed());
        let next_question = session.next_question;
        assert!(session
            .converse_with_world_front(90, "A new question must not cross.", |_| {
                panic!("an open completion cannot enact a new exterior front")
            })
            .is_err());
        assert_eq!(session.next_question, next_question);

        let native = session.into_native_rest().unwrap();
        let (mut session, receipt) = native.remount().unwrap();
        assert!(!receipt.source_replay_performed);
        let mut exterior_calls = 0usize;
        assert!(session
            .retry_open_with_world_front(|_| {
                exterior_calls += 1;
                panic!("retry after the staged agent answer cannot replay the world")
            })
            .is_err());
        assert_eq!(exterior_calls, 0);
        assert!(session.has_open_deed());
        assert!(session
            .open_completion
            .as_ref()
            .is_some_and(|open| matches!(
                open,
                OpenAgenticResearchCompletion::ReturningAnswer { .. }
            )));
    }

    #[test]
    fn transient_answer_return_refusal_rests_and_closes_the_same_deed_on_retry() {
        let action = ActionCurrent::new(Cog::lit(1)).unwrap();
        let agent = AgenticLanguageEcology::condition(
            &[MorphologicalLanguagePassage::new(
                "language-body",
                "language-body",
                3,
                "A returned relation changes the continuing language body.",
            )],
            &[AgenticLanguageCapability::new("research-world", 70).with_open_boundary()],
            &[],
            AgenticLanguageSpec::default(),
            action,
            2,
        )
        .unwrap();
        let mut session = AgenticResearchSession::new(
            agent,
            "research-world",
            LaboratoryResearchSpec {
                leader_aperture: 8,
                worker_threads: 1,
                thought_receiver_horizon: 16,
            },
        );
        session.research.refuse_next_emanated_return_for_test();
        assert!(session
            .converse_with_world_front(
                90,
                "What carries a continuity obstruction for relational morphology?",
                glued_returned_attempt,
            )
            .is_err());
        let deed = session
            .open_completion
            .as_ref()
            .unwrap()
            .deed()
            .identity
            .to_owned();
        assert!(session
            .open_completion
            .as_ref()
            .is_some_and(|open| matches!(
                open,
                OpenAgenticResearchCompletion::ReturningAnswer { .. }
            )));
        let native = session.into_native_rest().unwrap();
        let (mut session, _) = native.remount().unwrap();
        let mut exterior_calls = 0usize;
        let answer = session
            .retry_open_with_world_front(|_| {
                exterior_calls += 1;
                panic!("staged retry cannot replay a completed world return")
            })
            .unwrap();
        assert_eq!(exterior_calls, 0);
        assert_eq!(answer.thought.as_ref().unwrap().deed, deed);
        assert!(!session.has_open_deed());
    }

    #[test]
    fn owner_issued_formal_return_revises_and_resumes_the_same_research_intelligence() {
        let mut session = research_session();
        let diagnosis_answer = session
            .converse_with_world_front(
                90,
                "What carries a continuity obstruction for relational morphology?",
                glued_returned_attempt,
            )
            .unwrap();
        let diagnosis = session
            .reify_lean_diagnosis(&diagnosis_answer.answer.answer_episode_identity)
            .unwrap();
        let documents = vec![LeanSourceDocument::new(
            "Soma/Exact.lean",
            "namespace Soma\ndef exactCarrier (P : Prop) : Prop := P\ntheorem exact_chart_carry (P : Prop) (h : P) : exactCarrier P := by assumption\nend Soma",
        )];
        let mut lean = LeanMathematicsEcology::condition(&documents).unwrap();
        let problem = formal_problem();
        let declared_theorem_face = problem.identity.to_owned();
        let selection = session
            .select_and_open_lean_kernel_deed(
                &mut lean,
                LeanTheoremTargetRequest {
                    identity: "formal-target".to_owned(),
                    target_episode: diagnosis_answer.answer.answer_episode_identity.to_owned(),
                    declared_theorem_faces: holonic_structure::LocalSet::from([
                        declared_theorem_face,
                    ]),
                    alternatives: LocalSequence::from_iter([LeanTheoremTargetFace {
                        problem,
                        diagnosis_requirement:
                            LeanDiagnosisRequirement::ClosedRemovalMinimalCurrent,
                    }]),
                    diagnosis,
                },
            )
            .unwrap();
        assert!(
            matches!(selection, LeanTargetSelectionReceipt::Selected(_)),
            "selection={selection:#?}"
        );
        let project_root =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../formal/elementary-holonics");
        let kernel = LeanKernelWorld::new(
            &project_root,
            project_root.join(".lake/agentic-research-kernel"),
            2,
        )
        .unwrap();
        let deed = lean.open_kernel_deed().unwrap();
        let deed_identity = deed.identity().to_owned();
        let returns = kernel.grade_all(deed.problem(), deed.candidates()).unwrap();
        let completion = lean
            .receive_kernel_deed_returns(&deed_identity, returns)
            .unwrap();
        assert!(completion.validates_formal_return_face());
        assert!(!completion.kernel_admitted_sources().is_empty());
        let returned = AgenticFormalReturn {
            identity: "formal-return-1".to_owned(),
            receiver: 92,
            completion,
        };

        let mut blocked = research_session();
        blocked
            .converse_with_world_front(
                90,
                "What carries a continuity obstruction for relational morphology?",
                returned_attempt,
            )
            .unwrap();
        assert!(blocked
            .converse_with_world_front(90, "Which unknown quasar remains outside?", |requests| {
                let mut outcomes = LocalSequence::with_capacity(requests.len());
                for request in requests {
                    outcomes.push(LaboratoryWorldContactOutcome::Obstructed {
                        identity: request.identity.to_owned(),
                        obstruction: "deliberately open".to_owned(),
                    });
                }
                LaboratoryWorldContactAttempt {
                    outcomes,
                    execution: None,
                }
            })
            .is_err());
        assert!(blocked.has_open_deed());
        assert!(blocked.receive_formal_return(&returned).is_err());

        let reflective = session.receive_formal_return(&returned).unwrap();
        assert_eq!(reflective.continuation.continuation, 0);
        assert!(reflective.continuation.running_before);
        assert!(reflective.continuation.running_after);
        assert_ne!(
            reflective.continuation.codec_before,
            reflective.continuation.codec_after
        );
        let codec_versions_after = session.agent().codec_versions().len();
        let mut replay = returned;
        replay.identity = "formal-return-replay".to_owned();
        assert!(session.receive_formal_return(&replay).is_err());
        assert_eq!(session.agent().codec_versions().len(), codec_versions_after);

        let native = session.into_native_rest().unwrap();
        let (mut session, native_receipt) = native.remount().unwrap();
        assert!(!native_receipt.source_replay_performed);
        let mut world_calls = 0usize;
        let post = session
            .converse_with_world_front(
                90,
                "What carries a continuity obstruction for relational morphology through the lean kernel return?",
                |requests| {
                    world_calls += 1;
                    formal_reflection_attempt(requests)
                },
            )
            .unwrap();
        assert!(world_calls > 0);
        assert!(post
            .answer
            .operative_codec_versions
            .contains(&reflective.codec_version));
        assert!(post.answer.evidence_sources.contains("formal-return-1"));
        assert_ne!(post.answer.text, diagnosis_answer.answer.text);
    }
}
