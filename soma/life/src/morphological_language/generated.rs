use super::current::{
    collect_oriented_returned_seams, materialize_generated_current_live,
    materialize_oriented_returned_seam, receive_question, returned_seam_dominates,
};
use super::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalQueryRegion {
    pub ordered_surface: Vec<String>,
    pub features: BTreeSet<String>,
    pub reached_passages: BTreeSet<String>,
    pub reached_sources: BTreeSet<String>,
    pub(super) clause_ids: BTreeSet<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalQueryObligation {
    pub features: BTreeSet<String>,
    pub reached_passages: BTreeSet<String>,
    pub reached_sources: BTreeSet<String>,
    pub local_regions: Vec<MorphologicalQueryRegion>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalQuestionCharge {
    pub prompt: String,
    pub prompt_tokens: Vec<String>,
    pub recruited_passages: BTreeMap<String, BTreeSet<String>>,
    pub mark_faces: Vec<MorphologicalMarkFace>,
    /// Surfaces received as a recurring question-initial operator phase across plural caused
    /// question occurrences. This is conditioned morphology, not an authored stop-word
    /// vocabulary.
    pub operator_features: BTreeSet<String>,
    /// Prompt features which reached standing but did not participate in a maximal recurrent
    /// co-present query face. They remain context and lineage; they are not fabricated as
    /// independent questions.
    pub contextual_features: BTreeSet<String>,
    pub obligations: Vec<MorphologicalQueryObligation>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalMarkFace {
    pub surface: String,
    pub forward_horizon: u32,
    pub reverse_horizon: u32,
    pub reached_sources: BTreeSet<String>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MorphologicalTransport {
    /// Query incidence launched a new local phase.
    RecruitedPhase,
    /// The emitted surface was exposed by a recurrent lexical receiver after the preceding
    /// emitted occurrence had returned into the same branch-local standing.
    RecurrentLexical,
    /// A token occupies an exact subject/relation/object current assembled through shared entity
    /// incidence. Its source passages witness the relation, but are not the token's output rail.
    RelationalRealization,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalGeneratedToken {
    pub token: String,
    pub transport: MorphologicalTransport,
    pub lexical_horizons: BTreeSet<u32>,
    pub forward_mark_horizon: u32,
    pub reverse_mark_horizon: u32,
    pub recurrent_sources: BTreeSet<String>,
    /// Source lineages co-present in the recurrent context before this event crossed. When this
    /// differs from `caused_sources`, it is the exact seam certificate for the source change.
    pub recurrent_context_sources: BTreeSet<String>,
    pub caused_sources: BTreeSet<String>,
    pub caused_passages: BTreeSet<String>,
    pub supporting_clauses: BTreeSet<String>,
    /// Number of self-emanated events already returned in this branch after this token entered.
    /// It must equal the emitted event index plus one.
    pub returned_event_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalResponsePhase {
    pub entry_clause: String,
    pub clauses: BTreeSet<String>,
    pub sources: BTreeSet<String>,
    pub passages: BTreeSet<String>,
    /// The boundary was itself selected from the recurrent event frontier. An observer aperture
    /// or an exhausted frontier cannot fabricate it from an inherited clause.
    pub boundary: Option<MorphologicalBoundary>,
    pub discharged_obligations: BTreeSet<usize>,
    pub discharged_regions: BTreeMap<usize, BTreeSet<usize>>,
    pub discharged_features: BTreeMap<usize, BTreeSet<String>>,
    pub entry_lexical_horizons: BTreeSet<u32>,
    pub entry_recurrence_multiplicities: BTreeSet<u64>,
    pub emitted_start: usize,
    pub emitted_end: usize,
}

/// Exact testimony that two already-returned currents met at one recurrent lexical occurrence.
///
/// The seam does not condition a new Cartesian product of the two source bodies. The prefix and
/// suffix remain complete caused subpaths of their respective returned currents, while the
/// coincident lexical occurrence carries both lineages into one later path.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MorphologicalCausedSeam {
    pub surface: String,
    pub prefix_emitted_at: usize,
    pub suffix_emitted_at: usize,
    pub prefix_sources: BTreeSet<String>,
    pub suffix_sources: BTreeSet<String>,
    pub prefix_passages: BTreeSet<String>,
    pub suffix_passages: BTreeSet<String>,
    /// Complete lightweight family of recurrent seams admitted by the two returned currents.
    pub admissible_seam_population: usize,
    /// Terminal seam witnesses retained by this receiver aperture.
    pub materialized_seam_population: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MorphologicalResponseRest {
    /// Every query obligation participated and the resulting phase returned a sentence boundary.
    Closed,
    /// Exact query fibers remain, but no unrepeated local phase can conduct them.
    Obstructed { open_obligations: BTreeSet<usize> },
    /// The observer declined to inspect more generated material. This is not linguistic rest.
    ObservationApertureExhausted { open_obligations: BTreeSet<usize> },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalGeneratedCurrent {
    pub text: String,
    pub tokens: Vec<MorphologicalGeneratedToken>,
    pub phases: Vec<MorphologicalResponsePhase>,
    pub rest: MorphologicalResponseRest,
    pub caused_seams: Vec<MorphologicalCausedSeam>,
}

impl MorphologicalGeneratedCurrent {
    /// Consume the selected sparse current and carry it through the same live question body.
    ///
    /// This is the production return path. It neither clones the selected text current nor
    /// serializes and remounts the question ecology between reception and emanation.
    pub fn into_materialized_return(
        self,
        prompt: &str,
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<MorphologicalGeneratedText, MorphologicalLanguageError> {
        let prompt_tokens = lexical_tokens(prompt);
        if prompt_tokens.is_empty() {
            return Err(MorphologicalLanguageError::EmptyPrompt);
        }
        let returned_question = receive_question(&prompt_tokens, action, worker_threads)?;
        materialize_generated_current_live(
            &prompt_tokens,
            returned_question,
            self,
            action,
            worker_threads,
        )
    }

    /// Compose two selected sparse currents at their deepest admitted recurrent lexical seam.
    ///
    /// Every morphologically non-dominated seam crosses this receiver aperture. The full Swing
    /// body is still deferred until one of those currents participates in an outward deed; no
    /// lexicographic position or minimum extent silently becomes the returned seam.
    pub fn compose_returned_currents(
        left: &Self,
        right: &Self,
        maximum_observed_tokens: usize,
    ) -> Result<Vec<Self>, MorphologicalLanguageError> {
        if maximum_observed_tokens == 0 {
            return Err(MorphologicalLanguageError::EmptyObservationAperture);
        }
        if left.rest != MorphologicalResponseRest::Closed
            || right.rest != MorphologicalResponseRest::Closed
        {
            return Ok(Vec::new());
        }
        let mut seams = Vec::new();
        collect_oriented_returned_seams(left, right, false, maximum_observed_tokens, &mut seams)?;
        collect_oriented_returned_seams(right, left, true, maximum_observed_tokens, &mut seams)?;
        seams.sort();
        seams.dedup();
        if seams.is_empty() {
            return Ok(Vec::new());
        }
        let maximal = seams
            .iter()
            .filter(|candidate| {
                !seams
                    .iter()
                    .any(|other| returned_seam_dominates(other, candidate))
            })
            .collect::<Vec<_>>();
        let materialized_population = maximal.len();
        maximal
            .into_iter()
            .map(|selected| {
                let (prefix, suffix) = if selected.reversed {
                    (right, left)
                } else {
                    (left, right)
                };
                materialize_oriented_returned_seam(
                    prefix,
                    suffix,
                    selected,
                    seams.len(),
                    materialized_population,
                )
            })
            .collect()
    }

    /// Carry two already-closed answer phases in the order reached by a plural outer question.
    ///
    /// This is distinct from a lexical seam: neither phase is cut and no connective vocabulary is
    /// invented. The first returned current becomes causal history for the second, every token is
    /// reindexed in the joined chronology, and both exact phase/source/passsage fibers survive.
    pub fn sequence_returned_currents(
        first: &Self,
        second: &Self,
        maximum_observed_tokens: usize,
    ) -> Result<Option<Self>, MorphologicalLanguageError> {
        if maximum_observed_tokens == 0 {
            return Err(MorphologicalLanguageError::EmptyObservationAperture);
        }
        if first.rest != MorphologicalResponseRest::Closed
            || second.rest != MorphologicalResponseRest::Closed
        {
            return Ok(None);
        }
        let extent = first
            .tokens
            .len()
            .checked_add(second.tokens.len())
            .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        if extent > maximum_observed_tokens {
            return Ok(None);
        }
        let mut tokens = first.tokens.clone();
        tokens.extend(second.tokens.iter().cloned());
        for (emitted_at, token) in tokens.iter_mut().enumerate() {
            token.returned_event_count = emitted_at
                .checked_add(1)
                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
        }
        let mut phases = first.phases.clone();
        let phase_offset = first.tokens.len();
        for mut phase in second.phases.clone() {
            phase.emitted_start = phase
                .emitted_start
                .checked_add(phase_offset)
                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
            phase.emitted_end = phase
                .emitted_end
                .checked_add(phase_offset)
                .ok_or(MorphologicalLanguageError::CarrierExtent)?;
            phases.push(phase);
        }
        let caused_seams = first
            .caused_seams
            .iter()
            .chain(&second.caused_seams)
            .cloned()
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        Ok(Some(Self {
            text: render_tokens(tokens.iter().map(|token| token.token.as_str())),
            tokens,
            phases,
            rest: MorphologicalResponseRest::Closed,
            caused_seams,
        }))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct MorphologicalGeneratedText {
    pub text: String,
    pub tokens: Vec<MorphologicalGeneratedToken>,
    pub phases: Vec<MorphologicalResponsePhase>,
    pub rest: MorphologicalResponseRest,
    pub caused_seams: Vec<MorphologicalCausedSeam>,
    pub(super) returned_rest: ResonanceEcologyRestImage,
}

impl MorphologicalGeneratedText {
    pub const fn returned_rest_image(&self) -> &ResonanceEcologyRestImage {
        &self.returned_rest
    }

    pub fn current(&self) -> MorphologicalGeneratedCurrent {
        MorphologicalGeneratedCurrent {
            text: self.text.clone(),
            tokens: self.tokens.clone(),
            phases: self.phases.clone(),
            rest: self.rest.clone(),
            caused_seams: self.caused_seams.clone(),
        }
    }

    /// Compose two closed returned currents through their actual recurrent lexical occurrences.
    ///
    /// This is the sparse reflective counterpart of conditioning the complete pairwise passage
    /// product. Every emitted event remains on a witnessed prefix or suffix, the shared occurrence
    /// carries both source/passages lineages, and the composed chronology is returned through the
    /// same production Swing. No novel vocabulary or host-authored bridge token is introduced.
    pub fn compose_returned_currents(
        prompt: &str,
        left: &Self,
        right: &Self,
        maximum_observed_tokens: usize,
        action: ActionCurrent,
        worker_threads: usize,
    ) -> Result<Vec<Self>, MorphologicalLanguageError> {
        MorphologicalGeneratedCurrent::compose_returned_currents(
            &left.current(),
            &right.current(),
            maximum_observed_tokens,
        )?
        .into_iter()
        .map(|current| current.into_materialized_return(prompt, action, worker_threads))
        .collect()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct MorphologicalLanguageGeneration {
    pub charge: MorphologicalQuestionCharge,
    pub outputs: Vec<MorphologicalGeneratedText>,
    pub reflection: MorphologicalReflectionReceipt,
}

/// Complete terminal current testimony before a receiver selects which returned path to
/// materialize. This is not a weaker linguistic result: token, phase, obstruction, and lineage
/// receipts are complete, while the large remountable Swing body remains unformed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MorphologicalLanguageCurrentGeneration {
    pub charge: MorphologicalQuestionCharge,
    pub outputs: Vec<MorphologicalGeneratedCurrent>,
    pub reflection: MorphologicalReflectionReceipt,
}
