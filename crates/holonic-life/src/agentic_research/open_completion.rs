use super::*;

/// The sole serial frontier for one outer research deed. Every variant owns exactly the return
/// required by the next mouth, so an answer cannot exist before its world return and a research
/// answer-return cannot exist before the language answer.
#[derive(Debug)]
pub(super) enum OpenAgenticResearchCompletion {
    Researching {
        deed: crate::agentic_language::AgenticLanguageDeed,
    },
    WorldReturned {
        deed: crate::agentic_language::AgenticLanguageDeed,
        deliberation: LaboratoryResearchDeliberation,
    },
    Answering {
        deed: crate::agentic_language::AgenticLanguageDeed,
        deliberation: LaboratoryResearchDeliberation,
        world_return: AgenticLanguageWorldReturn,
    },
    ReturningAnswer {
        deed: crate::agentic_language::AgenticLanguageDeed,
        deliberation: LaboratoryResearchDeliberation,
        answer: AgenticLanguageAnswer,
        continuation_fibers: LocalSequence<LaboratoryContinuationFiberReceipt>,
    },
}

impl OpenAgenticResearchCompletion {
    pub fn new(deed: crate::agentic_language::AgenticLanguageDeed) -> Self {
        Self::Researching { deed }
    }

    pub fn deed(&self) -> &crate::agentic_language::AgenticLanguageDeed {
        match self {
            Self::Researching { deed }
            | Self::WorldReturned { deed, .. }
            | Self::Answering { deed, .. }
            | Self::ReturningAnswer { deed, .. } => deed,
        }
    }

    pub fn is_consistent(
        &self,
        agent: &AgenticLanguageEcology,
        research: &LaboratoryResearchEcology,
    ) -> bool {
        let deed = self.deed().identity.as_str();
        let agent_deed = agent.open_deed().map(|open| open.identity.as_str());
        let research_deed = research.open_deed_identity();
        match self {
            Self::Researching { .. } => {
                agent_deed == Some(deed) && research_deed.is_none_or(|returned| returned == deed)
            }
            Self::WorldReturned { deliberation, .. } => {
                agent_deed == Some(deed)
                    && research_deed.is_none()
                    && deliberation_matches(research, deliberation, deed)
            }
            Self::Answering {
                deliberation,
                world_return,
                ..
            } => {
                agent_deed == Some(deed)
                    && research_deed.is_none()
                    && world_return.deed == deed
                    && world_return.sections == deliberation_world_sections(deliberation)
                    && !world_return.thought_fibers.is_empty()
                    && deliberation_matches(research, deliberation, deed)
            }
            Self::ReturningAnswer {
                deliberation,
                answer,
                continuation_fibers,
                ..
            } => {
                agent_deed.is_none()
                    && research_deed.is_none()
                    && answer.world_deed.as_deref() == Some(deed)
                    && answer.relational_thought.is_some()
                    && !continuation_fibers.is_empty()
                    && deliberation_matches(research, deliberation, deed)
            }
        }
    }
}

fn deliberation_matches(
    research: &LaboratoryResearchEcology,
    deliberation: &LaboratoryResearchDeliberation,
    deed: &str,
) -> bool {
    deliberation.deed == deed
        && !deliberation.question_identity.trim().is_empty()
        && staged_research_standing_matches(research, deliberation, None)
}
