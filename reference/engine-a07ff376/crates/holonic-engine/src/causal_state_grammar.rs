//! Active exact discovery of receiver-relative causal state.
//!
//! A world membrane declares a finite action alphabet and exact receiver
//! coordinates. Production chooses reset/continuation words, retains the
//! returned prefix testimony, and refines an observation table until histories
//! form a closed and right-consistent future-equivalence quotient. Candidate
//! models predict previously unreturned words; counterexamples become caused
//! refinements rather than scalar loss.
//!
//! After the bounded causal quotient grades, the existing organizational
//! grammar learner is mounted independently over every inferred causal state.
//! The resulting fibers are compared along learned transitions, exposing
//! transported holons, exact interaction changes, population change, and the
//! distinction between a missing temporal coordinate and a receiver boundary
//! which was merely too coarse.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_rational::BigRational;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    EventId, EventSuccessor, ExactEventLaw, OrganizationalConfiguration,
    OrganizationalConstraintId, OrganizationalEcologySpec, OrganizationalGrammarCertificate,
    OrganizationalGrammarError, OrganizationalGrammarEvent, OrganizationalGrammarLaw,
    OrganizationalGrammarPhase, OrganizationalGrammarRadiation, OrganizationalGrammarStanding,
    OrganizationalLineageId, OrganizationalObservation, OrganizationalPortDirection,
    OrganizationalPortStanding, OrganizationalQuery, OrganizationalSiteId,
    OrganizationalTermSupport, OrganizationalValue,
};

const CAUSAL_STATE_SPEC_SCHEMA: &str = "holonic-engine.causal-state-grammar-spec.v1";
const CAUSAL_STATE_STANDING_SCHEMA: &str = "holonic-engine.causal-state-grammar-standing.v1";
const CAUSAL_CONTINUATION_QUERY_SCHEMA: &str = "holonic-engine.causal-continuation-query.v1";
const CAUSAL_OBSERVATION_SCHEMA: &str = "holonic-engine.causal-state-observation.v1";
const CAUSAL_TRACE_SCHEMA: &str = "holonic-engine.causal-continuation-trace.v1";
const CAUSAL_MODEL_SCHEMA: &str = "holonic-engine.causal-state-model.v1";
const DYNAMIC_GRAMMAR_CERTIFICATE_SCHEMA: &str = "holonic-engine.dynamic-grammar-certificate.v1";
const MAX_BOUNDED_WORDS: usize = 1_048_576;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalActionId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalObservableId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct LearnedCausalStateId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalActionSpec {
    pub id: CausalActionId,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalObservableSpec {
    pub id: CausalObservableId,
    pub name: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateGrammarSpec {
    pub schema: String,
    pub actions: Vec<CausalActionSpec>,
    pub observables: Vec<CausalObservableSpec>,
    /// Maximum representative-history length admitted to the active table.
    pub maximum_access_depth: u32,
    /// Maximum continuation length admitted as a distinguishing suffix.
    pub maximum_suffix_depth: u32,
    /// Every word through this depth must be returned and replayed exactly.
    pub grade_depth: u32,
    /// The common organizational carrier is reconditioned by each learned
    /// state's returned population before its local grammar is queried.
    pub organizational_ecology: OrganizationalEcologySpec,
}

impl CausalStateGrammarSpec {
    pub fn new(
        actions: Vec<CausalActionSpec>,
        observables: Vec<CausalObservableSpec>,
        maximum_access_depth: u32,
        maximum_suffix_depth: u32,
        grade_depth: u32,
        organizational_ecology: OrganizationalEcologySpec,
    ) -> Result<Self, CausalStateGrammarError> {
        let spec = Self {
            schema: CAUSAL_STATE_SPEC_SCHEMA.to_owned(),
            actions,
            observables,
            maximum_access_depth,
            maximum_suffix_depth,
            grade_depth,
            organizational_ecology,
        };
        spec.validate()?;
        Ok(spec)
    }

    fn validate(&self) -> Result<(), CausalStateGrammarError> {
        if self.schema != CAUSAL_STATE_SPEC_SCHEMA
            || self.actions.is_empty()
            || self.observables.is_empty()
            || self.maximum_access_depth == 0
            || self.maximum_suffix_depth == 0
            || self.grade_depth == 0
        {
            return Err(CausalStateGrammarError::MalformedSpec);
        }
        let action_ids = self
            .actions
            .iter()
            .map(|action| action.id)
            .collect::<BTreeSet<_>>();
        let observable_ids = self
            .observables
            .iter()
            .map(|observable| observable.id)
            .collect::<BTreeSet<_>>();
        if action_ids.len() != self.actions.len() || observable_ids.len() != self.observables.len()
        {
            return Err(CausalStateGrammarError::MalformedSpec);
        }
        self.organizational_ecology.reference_configuration()?;
        bounded_words(self)?;
        Ok(())
    }

    fn action_ids(&self) -> Vec<CausalActionId> {
        self.actions.iter().map(|action| action.id).collect()
    }

    fn observable_ids(&self) -> BTreeSet<CausalObservableId> {
        self.observables
            .iter()
            .map(|observable| observable.id)
            .collect()
    }

    fn site_ids(&self) -> BTreeSet<OrganizationalSiteId> {
        self.organizational_ecology
            .sites
            .iter()
            .map(|site| site.id)
            .collect()
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalActionWord {
    pub actions: Vec<CausalActionId>,
}

impl CausalActionWord {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.actions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.actions.is_empty()
    }

    pub fn appended(&self, action: CausalActionId) -> Self {
        let mut actions = self.actions.clone();
        actions.push(action);
        Self { actions }
    }

    pub fn concat(&self, suffix: &Self) -> Self {
        let mut actions = self.actions.clone();
        actions.extend(suffix.actions.iter().copied());
        Self { actions }
    }

    pub fn prefixes(&self) -> Vec<Self> {
        (0..=self.actions.len())
            .map(|length| Self {
                actions: self.actions[..length].to_vec(),
            })
            .collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalStateObservation {
    pub schema: String,
    pub values: BTreeMap<CausalObservableId, OrganizationalValue>,
    pub population: BTreeSet<OrganizationalSiteId>,
}

impl CausalStateObservation {
    pub fn new(
        values: BTreeMap<CausalObservableId, OrganizationalValue>,
        population: BTreeSet<OrganizationalSiteId>,
    ) -> Self {
        Self {
            schema: CAUSAL_OBSERVATION_SCHEMA.to_owned(),
            values,
            population,
        }
    }

    fn validate(&self, spec: &CausalStateGrammarSpec) -> Result<(), CausalStateGrammarError> {
        if self.schema != CAUSAL_OBSERVATION_SCHEMA
            || self.values.keys().copied().collect::<BTreeSet<_>>() != spec.observable_ids()
            || !self.population.is_subset(&spec.site_ids())
        {
            return Err(CausalStateGrammarError::MalformedObservation);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalContinuationTrace {
    pub schema: String,
    /// Includes the reset-root observation followed by one observation after
    /// every action occurrence.
    pub observations: Vec<CausalStateObservation>,
}

impl CausalContinuationTrace {
    pub fn new(observations: Vec<CausalStateObservation>) -> Self {
        Self {
            schema: CAUSAL_TRACE_SCHEMA.to_owned(),
            observations,
        }
    }

    fn validate(
        &self,
        query: &CausalContinuationQuery,
        spec: &CausalStateGrammarSpec,
    ) -> Result<(), CausalStateGrammarError> {
        if self.schema != CAUSAL_TRACE_SCHEMA || self.observations.len() != query.word.len() + 1 {
            return Err(CausalStateGrammarError::MalformedTrace);
        }
        for observation in &self.observations {
            observation.validate(spec)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalContinuationPurpose {
    CompleteObservationTable,
    GradePrediction { model_revision: u64 },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalContinuationQuery {
    pub schema: String,
    pub word: CausalActionWord,
    pub purpose: CausalContinuationPurpose,
}

impl CausalContinuationQuery {
    fn new(word: CausalActionWord, purpose: CausalContinuationPurpose) -> Self {
        Self {
            schema: CAUSAL_CONTINUATION_QUERY_SCHEMA.to_owned(),
            word,
            purpose,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateOrganizationalQuery {
    pub schema: String,
    pub state: LearnedCausalStateId,
    pub access_word: CausalActionWord,
    pub organizational_query: OrganizationalQuery,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalStateGrammarQuery {
    Continuation(CausalContinuationQuery),
    StateOrganization(StateOrganizationalQuery),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalContinuationTestimony {
    pub event: EventId,
    pub receiver: OrganizationalLineageId,
    pub query: CausalContinuationQuery,
    pub trace: CausalContinuationTrace,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateOrganizationalTestimony {
    pub event: EventId,
    pub receiver: OrganizationalLineageId,
    pub query: StateOrganizationalQuery,
    pub access_trace: CausalContinuationTrace,
    pub values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalStateGrammarEvent {
    ReturnContinuation(CausalContinuationTestimony),
    ReturnStateOrganization(StateOrganizationalTestimony),
}

impl CausalStateGrammarEvent {
    fn event(&self) -> EventId {
        match self {
            Self::ReturnContinuation(testimony) => testimony.event,
            Self::ReturnStateOrganization(testimony) => testimony.event,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalStateGrammarHistoryEntry {
    SourceContinuation(CausalContinuationTestimony),
    EmanatedPrediction(CausalStatePrediction),
    SourceStateOrganization(StateOrganizationalTestimony),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct ObservationCell {
    observation: CausalStateObservation,
    events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalObservationRow {
    pub cells: BTreeMap<CausalActionWord, CausalStateObservation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LearnedCausalState {
    pub id: LearnedCausalStateId,
    pub representative: CausalActionWord,
    pub observation: CausalStateObservation,
    pub row: CausalObservationRow,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalStateTransition {
    pub source: LearnedCausalStateId,
    pub action: CausalActionId,
    pub target: LearnedCausalStateId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateSeparationWitness {
    pub left: LearnedCausalStateId,
    pub right: LearnedCausalStateId,
    pub distinguishing_suffix: CausalActionWord,
    pub left_return: CausalStateObservation,
    pub right_return: CausalStateObservation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateModel {
    pub schema: String,
    pub revision: u64,
    pub initial_state: LearnedCausalStateId,
    pub states: Vec<LearnedCausalState>,
    pub transitions: Vec<CausalStateTransition>,
    pub access_basis: BTreeSet<CausalActionWord>,
    pub suffix_basis: BTreeSet<CausalActionWord>,
    pub separations: Vec<CausalStateSeparationWitness>,
    pub testimony_events: BTreeSet<EventId>,
}

impl CausalStateModel {
    pub fn state(
        &self,
        id: LearnedCausalStateId,
    ) -> Result<&LearnedCausalState, CausalStateGrammarError> {
        self.states
            .iter()
            .find(|state| state.id == id)
            .ok_or(CausalStateGrammarError::UnknownLearnedState(id))
    }

    pub fn transition(
        &self,
        source: LearnedCausalStateId,
        action: CausalActionId,
    ) -> Result<LearnedCausalStateId, CausalStateGrammarError> {
        self.transitions
            .iter()
            .find(|transition| transition.source == source && transition.action == action)
            .map(|transition| transition.target)
            .ok_or(CausalStateGrammarError::MissingLearnedTransition {
                state: source,
                action,
            })
    }

    pub fn state_after(
        &self,
        word: &CausalActionWord,
    ) -> Result<LearnedCausalStateId, CausalStateGrammarError> {
        let mut state = self.initial_state;
        for action in &word.actions {
            state = self.transition(state, *action)?;
        }
        Ok(state)
    }

    pub fn predict_trace(
        &self,
        word: &CausalActionWord,
    ) -> Result<CausalContinuationTrace, CausalStateGrammarError> {
        let mut state = self.initial_state;
        let mut observations = vec![self.state(state)?.observation.clone()];
        for action in &word.actions {
            state = self.transition(state, *action)?;
            observations.push(self.state(state)?.observation.clone());
        }
        Ok(CausalContinuationTrace::new(observations))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStatePrediction {
    pub schema: String,
    pub query: CausalContinuationQuery,
    pub predicted_trace: CausalContinuationTrace,
    pub caused_by_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalPredictionObstruction {
    pub schema: String,
    pub event: EventId,
    pub prediction: CausalStatePrediction,
    pub returned_trace: CausalContinuationTrace,
    pub first_differing_prefix: CausalActionWord,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalDeterminismObstruction {
    pub schema: String,
    pub first_events: BTreeSet<EventId>,
    pub conflicting_event: EventId,
    pub prefix: CausalActionWord,
    pub first_observation: CausalStateObservation,
    pub conflicting_observation: CausalStateObservation,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalDepthNeed {
    LongerAccessHistory,
    LongerDistinguishingContinuation,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalDepthObstruction {
    pub schema: String,
    pub need: CausalDepthNeed,
    pub required_word: CausalActionWord,
    pub declared_limit: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct DynamicTermKey {
    pub constraint: OrganizationalConstraintId,
    /// Empty support denotes the source constant.
    pub support: OrganizationalTermSupport,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct StateOrganizationalShape {
    pub reference_configuration: OrganizationalConfiguration,
    pub coefficients: BTreeMap<DynamicTermKey, OrganizationalValue>,
    pub holon_sites: BTreeSet<BTreeSet<OrganizationalSiteId>>,
    pub ports: BTreeSet<DynamicPortShape>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DynamicPortShape {
    pub holon_sites: BTreeSet<OrganizationalSiteId>,
    pub exterior_site: OrganizationalSiteId,
    pub direction: OrganizationalPortDirection,
    pub standing: OrganizationalPortStanding,
    pub affected_constraints: BTreeSet<OrganizationalConstraintId>,
    pub supports: BTreeSet<OrganizationalTermSupport>,
}

impl StateOrganizationalShape {
    fn from_certificate(certificate: &OrganizationalGrammarCertificate) -> Self {
        let mut coefficients = BTreeMap::new();
        for grammar in &certificate.constraint_grammars {
            coefficients.insert(
                DynamicTermKey {
                    constraint: grammar.constraint,
                    support: OrganizationalTermSupport {
                        assignments: BTreeMap::new(),
                    },
                },
                grammar.source_constant.clone(),
            );
            for term in &grammar.interaction_terms {
                coefficients.insert(
                    DynamicTermKey {
                        constraint: grammar.constraint,
                        support: term.support.clone(),
                    },
                    term.coefficient.clone(),
                );
            }
        }
        Self {
            reference_configuration: certificate.reference_configuration.clone(),
            coefficients,
            holon_sites: certificate
                .learned_holons
                .iter()
                .map(|holon| holon.sites.clone())
                .collect(),
            ports: certificate
                .learned_holons
                .iter()
                .flat_map(|holon| {
                    holon.exterior_ports.iter().map(|port| DynamicPortShape {
                        holon_sites: holon.sites.clone(),
                        exterior_site: port.exterior_site,
                        direction: port.direction,
                        standing: port.standing,
                        affected_constraints: port.affected_constraints.clone(),
                        supports: port.supports.clone(),
                    })
                })
                .collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateOrganizationalFiber {
    pub state: LearnedCausalStateId,
    pub access_word: CausalActionWord,
    pub causal_observation: CausalStateObservation,
    pub grammar: OrganizationalGrammarCertificate,
    pub shape: StateOrganizationalShape,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DynamicCoefficientChange {
    pub key: DynamicTermKey,
    pub before: OrganizationalValue,
    pub after: OrganizationalValue,
    pub residual: OrganizationalValue,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DynamicGrammarTransport {
    pub transition: CausalStateTransition,
    pub coefficient_changes: Vec<DynamicCoefficientChange>,
    pub carried_holons: BTreeSet<BTreeSet<OrganizationalSiteId>>,
    pub founded_holons: BTreeSet<BTreeSet<OrganizationalSiteId>>,
    pub departed_holons: BTreeSet<BTreeSet<OrganizationalSiteId>>,
    pub entered_population: BTreeSet<OrganizationalSiteId>,
    pub departed_population: BTreeSet<OrganizationalSiteId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum DynamicSeparationKind {
    VisibleReceiverDifference,
    TemporalStateRequired,
    OrganizationalBoundaryRefinementAvailable,
    PopulationChange,
    StateDependentInteraction,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DynamicStateSeparation {
    pub witness: CausalStateSeparationWitness,
    pub kinds: BTreeSet<DynamicSeparationKind>,
    pub organizational_shapes_equal: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateCycle {
    pub root: LearnedCausalStateId,
    pub word: CausalActionWord,
    pub traversed_states: Vec<LearnedCausalStateId>,
    pub organizational_shape_returns: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DynamicGrammarCertificate {
    pub schema: String,
    pub causal_model: CausalStateModel,
    pub grade_depth: u32,
    /// Complete declared word region, including table testimony and held-out
    /// prediction returns.
    pub graded_words: u64,
    pub predictions_graded: u64,
    pub prediction_obstructions: Vec<CausalPredictionObstruction>,
    pub organizational_fibers: Vec<CausalStateOrganizationalFiber>,
    pub transports: Vec<DynamicGrammarTransport>,
    pub separations: Vec<DynamicStateSeparation>,
    pub cycles: Vec<CausalStateCycle>,
    pub source_testimony_events: BTreeSet<EventId>,
    pub bounded_region_complete: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalStateGrammarPhase {
    LearningCausalQuotient,
    GradingCausalPrediction,
    LearningStateOrganizations,
    DeterminismObstructed,
    DepthObstructed,
    OrganizationObstructed,
    Certified,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateGrammarStanding {
    pub schema: String,
    pub spec: CausalStateGrammarSpec,
    pub phase: CausalStateGrammarPhase,
    next_query: Option<CausalStateGrammarQuery>,
    access_basis: BTreeSet<CausalActionWord>,
    suffix_basis: BTreeSet<CausalActionWord>,
    observations: BTreeMap<CausalActionWord, ObservationCell>,
    queried_words: BTreeSet<CausalActionWord>,
    used_events: BTreeSet<EventId>,
    history: Vec<CausalStateGrammarHistoryEntry>,
    model_revision: u64,
    candidate_model: Option<CausalStateModel>,
    pending_prediction: Option<CausalStatePrediction>,
    prediction_obstructions: Vec<CausalPredictionObstruction>,
    determinism_obstruction: Option<CausalDeterminismObstruction>,
    depth_obstruction: Option<CausalDepthObstruction>,
    state_organizations: BTreeMap<LearnedCausalStateId, OrganizationalGrammarStanding>,
    latest_organizational_radiation: Option<OrganizationalGrammarRadiation>,
    obstructed_organization_state: Option<LearnedCausalStateId>,
    certificate: Option<DynamicGrammarCertificate>,
}

impl CausalStateGrammarStanding {
    pub fn new(spec: CausalStateGrammarSpec) -> Result<Self, CausalStateGrammarError> {
        spec.validate()?;
        let empty = CausalActionWord::empty();
        let mut standing = Self {
            schema: CAUSAL_STATE_STANDING_SCHEMA.to_owned(),
            spec,
            phase: CausalStateGrammarPhase::LearningCausalQuotient,
            next_query: Some(CausalStateGrammarQuery::Continuation(
                CausalContinuationQuery::new(
                    empty.clone(),
                    CausalContinuationPurpose::CompleteObservationTable,
                ),
            )),
            access_basis: BTreeSet::from([empty.clone()]),
            suffix_basis: BTreeSet::from([empty]),
            observations: BTreeMap::new(),
            queried_words: BTreeSet::new(),
            used_events: BTreeSet::new(),
            history: Vec::new(),
            model_revision: 0,
            candidate_model: None,
            pending_prediction: None,
            prediction_obstructions: Vec::new(),
            determinism_obstruction: None,
            depth_obstruction: None,
            state_organizations: BTreeMap::new(),
            latest_organizational_radiation: None,
            obstructed_organization_state: None,
            certificate: None,
        };
        standing.validate_incremental()?;
        Ok(standing)
    }

    pub fn next_query(&self) -> Option<&CausalStateGrammarQuery> {
        self.next_query.as_ref()
    }

    pub fn history(&self) -> &[CausalStateGrammarHistoryEntry] {
        &self.history
    }

    pub fn candidate_model(&self) -> Option<&CausalStateModel> {
        self.candidate_model.as_ref()
    }

    pub fn prediction_obstructions(&self) -> &[CausalPredictionObstruction] {
        &self.prediction_obstructions
    }

    pub fn determinism_obstruction(&self) -> Option<&CausalDeterminismObstruction> {
        self.determinism_obstruction.as_ref()
    }

    pub fn depth_obstruction(&self) -> Option<&CausalDepthObstruction> {
        self.depth_obstruction.as_ref()
    }

    pub fn state_organizations(
        &self,
    ) -> &BTreeMap<LearnedCausalStateId, OrganizationalGrammarStanding> {
        &self.state_organizations
    }

    pub fn certificate(&self) -> Option<&DynamicGrammarCertificate> {
        self.certificate.as_ref()
    }

    fn validate_incremental(&mut self) -> Result<(), CausalStateGrammarError> {
        self.spec.validate()?;
        if self.schema != CAUSAL_STATE_STANDING_SCHEMA {
            return Err(CausalStateGrammarError::MalformedStanding);
        }
        match self.phase {
            CausalStateGrammarPhase::LearningCausalQuotient => {
                if !matches!(
                    self.next_query,
                    Some(CausalStateGrammarQuery::Continuation(
                        CausalContinuationQuery {
                            purpose: CausalContinuationPurpose::CompleteObservationTable,
                            ..
                        }
                    ))
                ) {
                    return Err(CausalStateGrammarError::MalformedStanding);
                }
            }
            CausalStateGrammarPhase::GradingCausalPrediction => {
                if !matches!(
                    self.next_query,
                    Some(CausalStateGrammarQuery::Continuation(
                        CausalContinuationQuery {
                            purpose: CausalContinuationPurpose::GradePrediction { .. },
                            ..
                        }
                    ))
                ) || self.pending_prediction.is_none()
                    || self.candidate_model.is_none()
                {
                    return Err(CausalStateGrammarError::MalformedStanding);
                }
            }
            CausalStateGrammarPhase::LearningStateOrganizations => {
                if !matches!(
                    self.next_query,
                    Some(CausalStateGrammarQuery::StateOrganization(_))
                ) || self.candidate_model.is_none()
                    || self.state_organizations.is_empty()
                {
                    return Err(CausalStateGrammarError::MalformedStanding);
                }
            }
            CausalStateGrammarPhase::DeterminismObstructed => {
                if self.next_query.is_some() || self.determinism_obstruction.is_none() {
                    return Err(CausalStateGrammarError::MalformedStanding);
                }
            }
            CausalStateGrammarPhase::DepthObstructed => {
                if self.next_query.is_some() || self.depth_obstruction.is_none() {
                    return Err(CausalStateGrammarError::MalformedStanding);
                }
            }
            CausalStateGrammarPhase::OrganizationObstructed => {
                if self.next_query.is_some() || self.obstructed_organization_state.is_none() {
                    return Err(CausalStateGrammarError::MalformedStanding);
                }
            }
            CausalStateGrammarPhase::Certified => {
                if self.next_query.is_some() || self.certificate.is_none() {
                    return Err(CausalStateGrammarError::MalformedStanding);
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateGrammarWork {
    pub returned_prefixes: u64,
    pub table_rows_compared: u64,
    pub access_words_added: u64,
    pub suffixes_added: u64,
    pub predictions_emitted: u64,
    pub prediction_counterexamples: u64,
    pub organizational_events: u64,
    pub coefficient_changes_emitted: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalStateGrammarRadiation {
    pub schema: String,
    pub event: EventId,
    pub phase_after: CausalStateGrammarPhase,
    pub next_query: Option<CausalStateGrammarQuery>,
    pub emitted_prediction: Option<CausalStatePrediction>,
    pub latest_prediction_obstruction: Option<CausalPredictionObstruction>,
    pub determinism_obstruction: Option<CausalDeterminismObstruction>,
    pub depth_obstruction: Option<CausalDepthObstruction>,
    pub latest_organizational_radiation: Option<OrganizationalGrammarRadiation>,
    pub certificate: Option<DynamicGrammarCertificate>,
    pub work: CausalStateGrammarWork,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct CausalStateGrammarLaw;

impl ExactEventLaw for CausalStateGrammarLaw {
    type Standing = CausalStateGrammarStanding;
    type Event = CausalStateGrammarEvent;
    type Radiation = CausalStateGrammarRadiation;
    type Error = CausalStateGrammarError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        let mut validated = standing_before.clone();
        validated.validate_incremental()?;
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(CausalStateGrammarError::RepeatedEvent(event_id));
        }
        let expected = standing_before
            .next_query
            .as_ref()
            .ok_or(CausalStateGrammarError::ReturnNotRequested)?;
        let mut standing_after = standing_before.clone();
        standing_after.next_query = None;
        standing_after.latest_organizational_radiation = None;
        standing_after.used_events.insert(event_id);
        let prior_prediction = standing_after.pending_prediction.clone();
        let prior_obstruction_count = standing_after.prediction_obstructions.len();
        let mut work = CausalStateGrammarWork::default();

        match event {
            CausalStateGrammarEvent::ReturnContinuation(testimony) => {
                let CausalStateGrammarQuery::Continuation(expected_query) = expected else {
                    return Err(CausalStateGrammarError::UnexpectedReturnSpecies);
                };
                if testimony.query != *expected_query {
                    return Err(CausalStateGrammarError::UnexpectedContinuationQuery {
                        expected: Box::new(expected_query.clone()),
                        received: Box::new(testimony.query.clone()),
                    });
                }
                testimony
                    .trace
                    .validate(&testimony.query, &standing_after.spec)?;
                standing_after
                    .history
                    .push(CausalStateGrammarHistoryEntry::SourceContinuation(
                        testimony.clone(),
                    ));
                let deterministic = admit_trace(&mut standing_after, testimony, &mut work)?;
                if deterministic {
                    match standing_before.phase {
                        CausalStateGrammarPhase::LearningCausalQuotient => {
                            advance_causal_learning(&mut standing_after, &mut work)?;
                        }
                        CausalStateGrammarPhase::GradingCausalPrediction => {
                            grade_returned_prediction(&mut standing_after, testimony, &mut work)?;
                            if standing_after.phase
                                != CausalStateGrammarPhase::DeterminismObstructed
                            {
                                advance_causal_learning(&mut standing_after, &mut work)?;
                            }
                        }
                        _ => {
                            return Err(CausalStateGrammarError::UnexpectedReturnSpecies);
                        }
                    }
                }
            }
            CausalStateGrammarEvent::ReturnStateOrganization(testimony) => {
                let CausalStateGrammarQuery::StateOrganization(expected_query) = expected else {
                    return Err(CausalStateGrammarError::UnexpectedReturnSpecies);
                };
                if testimony.query != *expected_query {
                    return Err(CausalStateGrammarError::UnexpectedStateOrganizationQuery {
                        expected: Box::new(expected_query.clone()),
                        received: Box::new(testimony.query.clone()),
                    });
                }
                if standing_before.phase != CausalStateGrammarPhase::LearningStateOrganizations {
                    return Err(CausalStateGrammarError::UnexpectedReturnSpecies);
                }
                testimony.access_trace.validate(
                    &CausalContinuationQuery::new(
                        testimony.query.access_word.clone(),
                        CausalContinuationPurpose::CompleteObservationTable,
                    ),
                    &standing_after.spec,
                )?;
                let model = standing_after
                    .candidate_model
                    .as_ref()
                    .ok_or(CausalStateGrammarError::MalformedStanding)?;
                if model.state_after(&testimony.query.access_word)? != testimony.query.state
                    || model.predict_trace(&testimony.query.access_word)? != testimony.access_trace
                {
                    return Err(CausalStateGrammarError::StateAccessReturnMismatch);
                }
                standing_after.history.push(
                    CausalStateGrammarHistoryEntry::SourceStateOrganization(testimony.clone()),
                );
                let organization = standing_after
                    .state_organizations
                    .get(&testimony.query.state)
                    .ok_or(CausalStateGrammarError::UnknownLearnedState(
                        testimony.query.state,
                    ))?;
                let successor = OrganizationalGrammarLaw.enact(
                    organization,
                    &OrganizationalGrammarEvent::ReturnObservation(OrganizationalObservation {
                        event: testimony.event,
                        receiver: testimony.receiver,
                        query: testimony.query.organizational_query.clone(),
                        values: testimony.values.clone(),
                    }),
                )?;
                standing_after
                    .state_organizations
                    .insert(testimony.query.state, successor.standing_after);
                standing_after.latest_organizational_radiation =
                    successor.radiation.last().cloned();
                work.organizational_events += 1;
                schedule_state_organization(&mut standing_after, &mut work)?;
            }
        }

        standing_after.validate_incremental()?;
        let emitted_prediction = standing_after
            .pending_prediction
            .clone()
            .filter(|prediction| prior_prediction.as_ref() != Some(prediction));
        if emitted_prediction.is_some() {
            work.predictions_emitted += 1;
        }
        let latest_prediction_obstruction = (standing_after.prediction_obstructions.len()
            > prior_obstruction_count)
            .then(|| standing_after.prediction_obstructions.last().cloned())
            .flatten();
        let radiation = CausalStateGrammarRadiation {
            schema: "holonic-engine.causal-state-grammar-radiation.v1".to_owned(),
            event: event_id,
            phase_after: standing_after.phase,
            next_query: standing_after.next_query.clone(),
            emitted_prediction,
            latest_prediction_obstruction,
            determinism_obstruction: standing_after.determinism_obstruction.clone(),
            depth_obstruction: standing_after.depth_obstruction.clone(),
            latest_organizational_radiation: standing_after.latest_organizational_radiation.clone(),
            certificate: standing_after.certificate.clone(),
            work,
        };
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

fn admit_trace(
    standing: &mut CausalStateGrammarStanding,
    testimony: &CausalContinuationTestimony,
    work: &mut CausalStateGrammarWork,
) -> Result<bool, CausalStateGrammarError> {
    for (ordinal, prefix) in testimony.query.word.prefixes().into_iter().enumerate() {
        let observation = testimony
            .trace
            .observations
            .get(ordinal)
            .ok_or(CausalStateGrammarError::MalformedTrace)?
            .clone();
        if let Some(cell) = standing.observations.get_mut(&prefix) {
            if cell.observation != observation {
                standing.determinism_obstruction = Some(CausalDeterminismObstruction {
                    schema: "holonic-engine.causal-determinism-obstruction.v1".to_owned(),
                    first_events: cell.events.clone(),
                    conflicting_event: testimony.event,
                    prefix,
                    first_observation: cell.observation.clone(),
                    conflicting_observation: observation,
                });
                standing.phase = CausalStateGrammarPhase::DeterminismObstructed;
                standing.next_query = None;
                standing.pending_prediction = None;
                return Ok(false);
            }
            cell.events.insert(testimony.event);
        } else {
            standing.observations.insert(
                prefix,
                ObservationCell {
                    observation,
                    events: BTreeSet::from([testimony.event]),
                },
            );
            work.returned_prefixes += 1;
        }
    }
    standing.queried_words.insert(testimony.query.word.clone());
    Ok(true)
}

fn grade_returned_prediction(
    standing: &mut CausalStateGrammarStanding,
    testimony: &CausalContinuationTestimony,
    work: &mut CausalStateGrammarWork,
) -> Result<(), CausalStateGrammarError> {
    let prediction = standing
        .pending_prediction
        .take()
        .ok_or(CausalStateGrammarError::MalformedStanding)?;
    if prediction.query != testimony.query {
        return Err(CausalStateGrammarError::MalformedStanding);
    }
    if prediction.predicted_trace != testimony.trace {
        let first_differing_ordinal = prediction
            .predicted_trace
            .observations
            .iter()
            .zip(&testimony.trace.observations)
            .position(|(predicted, returned)| predicted != returned)
            .ok_or(CausalStateGrammarError::MalformedTrace)?;
        let first_differing_prefix = CausalActionWord {
            actions: testimony.query.word.actions[..first_differing_ordinal].to_vec(),
        };
        standing
            .prediction_obstructions
            .push(CausalPredictionObstruction {
                schema: "holonic-engine.causal-prediction-obstruction.v1".to_owned(),
                event: testimony.event,
                prediction,
                returned_trace: testimony.trace.clone(),
                first_differing_prefix,
            });
        work.prediction_counterexamples += 1;
        let mut changed = false;
        for prefix in testimony.query.word.prefixes() {
            if prefix.len()
                <= usize::try_from(standing.spec.maximum_access_depth)
                    .map_err(|_| CausalStateGrammarError::CarrierOverflow)?
            {
                changed |= standing.access_basis.insert(prefix);
            }
        }
        if !changed {
            standing.depth_obstruction = Some(CausalDepthObstruction {
                schema: "holonic-engine.causal-depth-obstruction.v1".to_owned(),
                need: CausalDepthNeed::LongerAccessHistory,
                required_word: testimony.query.word.clone(),
                declared_limit: standing.spec.maximum_access_depth,
            });
            standing.phase = CausalStateGrammarPhase::DepthObstructed;
            standing.next_query = None;
            standing.candidate_model = None;
            return Ok(());
        }
        standing.model_revision += 1;
        standing.candidate_model = None;
        standing.phase = CausalStateGrammarPhase::LearningCausalQuotient;
    } else {
        standing.phase = CausalStateGrammarPhase::LearningCausalQuotient;
    }
    Ok(())
}

fn advance_causal_learning(
    standing: &mut CausalStateGrammarStanding,
    work: &mut CausalStateGrammarWork,
) -> Result<(), CausalStateGrammarError> {
    if matches!(
        standing.phase,
        CausalStateGrammarPhase::DepthObstructed | CausalStateGrammarPhase::DeterminismObstructed
    ) {
        return Ok(());
    }
    standing.pending_prediction = None;
    loop {
        if let Some(word) = first_missing_table_word(standing)? {
            standing.phase = CausalStateGrammarPhase::LearningCausalQuotient;
            standing.next_query = Some(CausalStateGrammarQuery::Continuation(
                CausalContinuationQuery::new(
                    word,
                    CausalContinuationPurpose::CompleteObservationTable,
                ),
            ));
            return Ok(());
        }

        if let Some(unclosed) = first_unclosed_extension(standing, work)? {
            if unclosed.len()
                > usize::try_from(standing.spec.maximum_access_depth)
                    .map_err(|_| CausalStateGrammarError::CarrierOverflow)?
            {
                standing.depth_obstruction = Some(CausalDepthObstruction {
                    schema: "holonic-engine.causal-depth-obstruction.v1".to_owned(),
                    need: CausalDepthNeed::LongerAccessHistory,
                    required_word: unclosed,
                    declared_limit: standing.spec.maximum_access_depth,
                });
                standing.phase = CausalStateGrammarPhase::DepthObstructed;
                standing.next_query = None;
                return Ok(());
            }
            standing.access_basis.insert(unclosed);
            work.access_words_added += 1;
            continue;
        }

        if let Some(suffix) = first_consistency_refinement(standing, work)? {
            if suffix.len()
                > usize::try_from(standing.spec.maximum_suffix_depth)
                    .map_err(|_| CausalStateGrammarError::CarrierOverflow)?
            {
                standing.depth_obstruction = Some(CausalDepthObstruction {
                    schema: "holonic-engine.causal-depth-obstruction.v1".to_owned(),
                    need: CausalDepthNeed::LongerDistinguishingContinuation,
                    required_word: suffix,
                    declared_limit: standing.spec.maximum_suffix_depth,
                });
                standing.phase = CausalStateGrammarPhase::DepthObstructed;
                standing.next_query = None;
                return Ok(());
            }
            standing.suffix_basis.insert(suffix);
            work.suffixes_added += 1;
            continue;
        }

        let model = build_causal_model(standing, work)?;
        if let Some(counterexample) = first_observed_model_counterexample(standing, &model)? {
            let mut changed = false;
            for prefix in counterexample.prefixes() {
                if prefix.len()
                    <= usize::try_from(standing.spec.maximum_access_depth)
                        .map_err(|_| CausalStateGrammarError::CarrierOverflow)?
                {
                    changed |= standing.access_basis.insert(prefix);
                }
            }
            if !changed {
                standing.depth_obstruction = Some(CausalDepthObstruction {
                    schema: "holonic-engine.causal-depth-obstruction.v1".to_owned(),
                    need: CausalDepthNeed::LongerAccessHistory,
                    required_word: counterexample,
                    declared_limit: standing.spec.maximum_access_depth,
                });
                standing.phase = CausalStateGrammarPhase::DepthObstructed;
                standing.next_query = None;
                return Ok(());
            }
            standing.model_revision += 1;
            continue;
        }
        standing.candidate_model = Some(model.clone());

        if let Some(word) = first_unreturned_grade_word(standing)? {
            let query = CausalContinuationQuery::new(
                word.clone(),
                CausalContinuationPurpose::GradePrediction {
                    model_revision: model.revision,
                },
            );
            let prediction = CausalStatePrediction {
                schema: "holonic-engine.causal-state-prediction.v1".to_owned(),
                predicted_trace: model.predict_trace(&word)?,
                query: query.clone(),
                caused_by_events: model.testimony_events.clone(),
            };
            standing
                .history
                .push(CausalStateGrammarHistoryEntry::EmanatedPrediction(
                    prediction.clone(),
                ));
            standing.pending_prediction = Some(prediction);
            standing.phase = CausalStateGrammarPhase::GradingCausalPrediction;
            standing.next_query = Some(CausalStateGrammarQuery::Continuation(query));
            return Ok(());
        }

        initialize_state_organizations(standing)?;
        schedule_state_organization(standing, work)?;
        return Ok(());
    }
}

fn required_table_words(standing: &CausalStateGrammarStanding) -> BTreeSet<CausalActionWord> {
    let actions = standing.spec.action_ids();
    let mut required = BTreeSet::new();
    for access in &standing.access_basis {
        for suffix in &standing.suffix_basis {
            required.insert(access.concat(suffix));
        }
        for action in &actions {
            let extension = access.appended(*action);
            for suffix in &standing.suffix_basis {
                required.insert(extension.concat(suffix));
            }
        }
    }
    required
}

fn first_missing_table_word(
    standing: &CausalStateGrammarStanding,
) -> Result<Option<CausalActionWord>, CausalStateGrammarError> {
    Ok(shortlex(
        required_table_words(standing)
            .into_iter()
            .filter(|word| !standing.observations.contains_key(word))
            .collect(),
    )
    .into_iter()
    .next())
}

fn observation_row(
    standing: &CausalStateGrammarStanding,
    access: &CausalActionWord,
) -> Result<CausalObservationRow, CausalStateGrammarError> {
    let mut cells = BTreeMap::new();
    for suffix in &standing.suffix_basis {
        let word = access.concat(suffix);
        let observation = standing
            .observations
            .get(&word)
            .ok_or(CausalStateGrammarError::IncompleteObservationTable)?
            .observation
            .clone();
        cells.insert(suffix.clone(), observation);
    }
    Ok(CausalObservationRow { cells })
}

fn first_unclosed_extension(
    standing: &CausalStateGrammarStanding,
    work: &mut CausalStateGrammarWork,
) -> Result<Option<CausalActionWord>, CausalStateGrammarError> {
    let basis_rows = standing
        .access_basis
        .iter()
        .map(|access| Ok((access, observation_row(standing, access)?)))
        .collect::<Result<Vec<_>, CausalStateGrammarError>>()?;
    let mut extensions = standing
        .access_basis
        .iter()
        .flat_map(|access| {
            standing
                .spec
                .action_ids()
                .into_iter()
                .map(move |action| access.appended(action))
        })
        .collect::<Vec<_>>();
    extensions = shortlex(extensions);
    extensions.dedup();
    for extension in extensions {
        let row = observation_row(standing, &extension)?;
        work.table_rows_compared += u64::try_from(basis_rows.len())
            .map_err(|_| CausalStateGrammarError::CarrierOverflow)?;
        if !basis_rows.iter().any(|(_, candidate)| candidate == &row) {
            return Ok(Some(extension));
        }
    }
    Ok(None)
}

fn first_consistency_refinement(
    standing: &CausalStateGrammarStanding,
    work: &mut CausalStateGrammarWork,
) -> Result<Option<CausalActionWord>, CausalStateGrammarError> {
    let accesses = shortlex(standing.access_basis.iter().cloned().collect());
    for left_ordinal in 0..accesses.len() {
        for right_ordinal in (left_ordinal + 1)..accesses.len() {
            let left = &accesses[left_ordinal];
            let right = &accesses[right_ordinal];
            let left_row = observation_row(standing, left)?;
            let right_row = observation_row(standing, right)?;
            work.table_rows_compared += 1;
            if left_row != right_row {
                continue;
            }
            for action in standing.spec.action_ids() {
                let left_extension = left.appended(action);
                let right_extension = right.appended(action);
                let left_extension_row = observation_row(standing, &left_extension)?;
                let right_extension_row = observation_row(standing, &right_extension)?;
                work.table_rows_compared += 1;
                if left_extension_row == right_extension_row {
                    continue;
                }
                let suffix = standing
                    .suffix_basis
                    .iter()
                    .find(|suffix| {
                        left_extension_row.cells.get(*suffix)
                            != right_extension_row.cells.get(*suffix)
                    })
                    .ok_or(CausalStateGrammarError::MalformedObservationTable)?;
                let mut actions = vec![action];
                actions.extend(suffix.actions.iter().copied());
                return Ok(Some(CausalActionWord { actions }));
            }
        }
    }
    Ok(None)
}

fn build_causal_model(
    standing: &CausalStateGrammarStanding,
    work: &mut CausalStateGrammarWork,
) -> Result<CausalStateModel, CausalStateGrammarError> {
    let accesses = shortlex(standing.access_basis.iter().cloned().collect());
    let mut row_representatives = BTreeMap::<CausalObservationRow, CausalActionWord>::new();
    for access in accesses {
        let row = observation_row(standing, &access)?;
        row_representatives.entry(row).or_insert(access);
    }
    let mut representatives = row_representatives
        .into_iter()
        .map(|(row, representative)| (representative, row))
        .collect::<Vec<_>>();
    representatives.sort_by(|left, right| shortlex_cmp(&left.0, &right.0));

    let mut states = Vec::new();
    for (ordinal, (representative, row)) in representatives.iter().enumerate() {
        let observation = standing
            .observations
            .get(representative)
            .ok_or(CausalStateGrammarError::IncompleteObservationTable)?
            .observation
            .clone();
        states.push(LearnedCausalState {
            id: LearnedCausalStateId(
                u64::try_from(ordinal + 1).map_err(|_| CausalStateGrammarError::CarrierOverflow)?,
            ),
            representative: representative.clone(),
            observation,
            row: row.clone(),
        });
    }
    let state_for_row = states
        .iter()
        .map(|state| (state.row.clone(), state.id))
        .collect::<BTreeMap<_, _>>();
    let initial_row = observation_row(standing, &CausalActionWord::empty())?;
    let initial_state = *state_for_row
        .get(&initial_row)
        .ok_or(CausalStateGrammarError::MalformedObservationTable)?;
    let mut transitions = Vec::new();
    for state in &states {
        for action in standing.spec.action_ids() {
            let extension = state.representative.appended(action);
            let target_row = observation_row(standing, &extension)?;
            let target = *state_for_row
                .get(&target_row)
                .ok_or(CausalStateGrammarError::ObservationTableNotClosed)?;
            transitions.push(CausalStateTransition {
                source: state.id,
                action,
                target,
            });
        }
    }
    transitions.sort();

    let mut separations = Vec::new();
    for left_ordinal in 0..states.len() {
        for right_ordinal in (left_ordinal + 1)..states.len() {
            let left = &states[left_ordinal];
            let right = &states[right_ordinal];
            let suffix = shortlex(
                standing
                    .suffix_basis
                    .iter()
                    .filter(|suffix| left.row.cells.get(*suffix) != right.row.cells.get(*suffix))
                    .cloned()
                    .collect(),
            )
            .into_iter()
            .next()
            .ok_or(CausalStateGrammarError::StatesLackSeparation)?;
            separations.push(CausalStateSeparationWitness {
                left: left.id,
                right: right.id,
                left_return: left
                    .row
                    .cells
                    .get(&suffix)
                    .cloned()
                    .ok_or(CausalStateGrammarError::MalformedObservationTable)?,
                right_return: right
                    .row
                    .cells
                    .get(&suffix)
                    .cloned()
                    .ok_or(CausalStateGrammarError::MalformedObservationTable)?,
                distinguishing_suffix: suffix,
            });
        }
    }
    work.table_rows_compared += u64::try_from(states.len() * states.len())
        .map_err(|_| CausalStateGrammarError::CarrierOverflow)?;
    Ok(CausalStateModel {
        schema: CAUSAL_MODEL_SCHEMA.to_owned(),
        revision: standing.model_revision,
        initial_state,
        states,
        transitions,
        access_basis: standing.access_basis.clone(),
        suffix_basis: standing.suffix_basis.clone(),
        separations,
        testimony_events: standing
            .observations
            .values()
            .flat_map(|cell| cell.events.iter().copied())
            .collect(),
    })
}

fn actual_trace(
    standing: &CausalStateGrammarStanding,
    word: &CausalActionWord,
) -> Result<CausalContinuationTrace, CausalStateGrammarError> {
    let observations = word
        .prefixes()
        .into_iter()
        .map(|prefix| {
            standing
                .observations
                .get(&prefix)
                .map(|cell| cell.observation.clone())
                .ok_or(CausalStateGrammarError::IncompleteObservationTable)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(CausalContinuationTrace::new(observations))
}

fn first_observed_model_counterexample(
    standing: &CausalStateGrammarStanding,
    model: &CausalStateModel,
) -> Result<Option<CausalActionWord>, CausalStateGrammarError> {
    let grade_depth = usize::try_from(standing.spec.grade_depth)
        .map_err(|_| CausalStateGrammarError::CarrierOverflow)?;
    for word in bounded_words(&standing.spec)? {
        if word.len() > grade_depth || !standing.observations.contains_key(&word) {
            continue;
        }
        if model.predict_trace(&word)? != actual_trace(standing, &word)? {
            return Ok(Some(word));
        }
    }
    Ok(None)
}

fn first_unreturned_grade_word(
    standing: &CausalStateGrammarStanding,
) -> Result<Option<CausalActionWord>, CausalStateGrammarError> {
    Ok(bounded_words(&standing.spec)?
        .into_iter()
        .find(|word| !standing.observations.contains_key(word)))
}

fn initialize_state_organizations(
    standing: &mut CausalStateGrammarStanding,
) -> Result<(), CausalStateGrammarError> {
    let model = standing
        .candidate_model
        .as_ref()
        .ok_or(CausalStateGrammarError::MalformedStanding)?;
    let mut state_organizations = BTreeMap::new();
    for state in &model.states {
        let mut sites = standing.spec.organizational_ecology.sites.clone();
        for site in &mut sites {
            if !state.observation.population.contains(&site.id) {
                site.reference_variant = None;
            }
        }
        let ecology = OrganizationalEcologySpec::new(
            sites,
            standing.spec.organizational_ecology.constraints.clone(),
        )?;
        state_organizations.insert(state.id, OrganizationalGrammarStanding::new(ecology)?);
    }
    standing.state_organizations = state_organizations;
    standing.phase = CausalStateGrammarPhase::LearningStateOrganizations;
    Ok(())
}

fn schedule_state_organization(
    standing: &mut CausalStateGrammarStanding,
    work: &mut CausalStateGrammarWork,
) -> Result<(), CausalStateGrammarError> {
    let model = standing
        .candidate_model
        .as_ref()
        .ok_or(CausalStateGrammarError::MalformedStanding)?;
    for state in &model.states {
        let organization = standing
            .state_organizations
            .get(&state.id)
            .ok_or(CausalStateGrammarError::UnknownLearnedState(state.id))?;
        if organization.phase == OrganizationalGrammarPhase::TemporalObstruction {
            standing.phase = CausalStateGrammarPhase::OrganizationObstructed;
            standing.next_query = None;
            standing.obstructed_organization_state = Some(state.id);
            return Ok(());
        }
        if let Some(query) = organization.next_query() {
            standing.phase = CausalStateGrammarPhase::LearningStateOrganizations;
            standing.next_query = Some(CausalStateGrammarQuery::StateOrganization(
                StateOrganizationalQuery {
                    schema: "holonic-engine.state-organizational-query.v1".to_owned(),
                    state: state.id,
                    access_word: state.representative.clone(),
                    organizational_query: query.clone(),
                },
            ));
            return Ok(());
        }
        if organization.phase != OrganizationalGrammarPhase::Certified {
            return Err(CausalStateGrammarError::MalformedStanding);
        }
    }
    let certificate = compile_dynamic_certificate(standing, work)?;
    standing.certificate = Some(certificate);
    standing.next_query = None;
    standing.phase = CausalStateGrammarPhase::Certified;
    Ok(())
}

fn compile_dynamic_certificate(
    standing: &CausalStateGrammarStanding,
    work: &mut CausalStateGrammarWork,
) -> Result<DynamicGrammarCertificate, CausalStateGrammarError> {
    let model = standing
        .candidate_model
        .as_ref()
        .ok_or(CausalStateGrammarError::MalformedStanding)?
        .clone();
    let mut organizational_fibers = Vec::new();
    for state in &model.states {
        let grammar = standing
            .state_organizations
            .get(&state.id)
            .and_then(OrganizationalGrammarStanding::certificate)
            .ok_or(CausalStateGrammarError::IncompleteStateOrganization)?
            .clone();
        organizational_fibers.push(CausalStateOrganizationalFiber {
            state: state.id,
            access_word: state.representative.clone(),
            causal_observation: state.observation.clone(),
            shape: StateOrganizationalShape::from_certificate(&grammar),
            grammar,
        });
    }
    let fibers = organizational_fibers
        .iter()
        .map(|fiber| (fiber.state, fiber))
        .collect::<BTreeMap<_, _>>();
    let mut transports = Vec::new();
    for transition in &model.transitions {
        let before = fibers
            .get(&transition.source)
            .ok_or(CausalStateGrammarError::MalformedStanding)?;
        let after = fibers
            .get(&transition.target)
            .ok_or(CausalStateGrammarError::MalformedStanding)?;
        let keys = before
            .shape
            .coefficients
            .keys()
            .chain(after.shape.coefficients.keys())
            .cloned()
            .collect::<BTreeSet<_>>();
        let mut coefficient_changes = Vec::new();
        for key in keys {
            let before_value = before
                .shape
                .coefficients
                .get(&key)
                .cloned()
                .unwrap_or_else(BigRational::zero);
            let after_value = after
                .shape
                .coefficients
                .get(&key)
                .cloned()
                .unwrap_or_else(BigRational::zero);
            let residual = &after_value - &before_value;
            if !residual.is_zero() {
                coefficient_changes.push(DynamicCoefficientChange {
                    key,
                    before: before_value,
                    after: after_value,
                    residual,
                });
            }
        }
        work.coefficient_changes_emitted += u64::try_from(coefficient_changes.len())
            .map_err(|_| CausalStateGrammarError::CarrierOverflow)?;
        let carried_holons = before
            .shape
            .holon_sites
            .intersection(&after.shape.holon_sites)
            .cloned()
            .collect();
        let founded_holons = after
            .shape
            .holon_sites
            .difference(&before.shape.holon_sites)
            .cloned()
            .collect();
        let departed_holons = before
            .shape
            .holon_sites
            .difference(&after.shape.holon_sites)
            .cloned()
            .collect();
        transports.push(DynamicGrammarTransport {
            transition: transition.clone(),
            coefficient_changes,
            carried_holons,
            founded_holons,
            departed_holons,
            entered_population: after
                .causal_observation
                .population
                .difference(&before.causal_observation.population)
                .copied()
                .collect(),
            departed_population: before
                .causal_observation
                .population
                .difference(&after.causal_observation.population)
                .copied()
                .collect(),
        });
    }
    let mut separations = Vec::new();
    for witness in &model.separations {
        let left = fibers
            .get(&witness.left)
            .ok_or(CausalStateGrammarError::MalformedStanding)?;
        let right = fibers
            .get(&witness.right)
            .ok_or(CausalStateGrammarError::MalformedStanding)?;
        let shapes_equal = left.shape == right.shape;
        let mut kinds = BTreeSet::new();
        if left.causal_observation.values != right.causal_observation.values {
            kinds.insert(DynamicSeparationKind::VisibleReceiverDifference);
        }
        if left.causal_observation.population != right.causal_observation.population {
            kinds.insert(DynamicSeparationKind::PopulationChange);
        }
        if left.causal_observation == right.causal_observation {
            if shapes_equal {
                kinds.insert(DynamicSeparationKind::TemporalStateRequired);
            } else {
                kinds.insert(DynamicSeparationKind::OrganizationalBoundaryRefinementAvailable);
            }
        }
        if left.shape.coefficients != right.shape.coefficients {
            kinds.insert(DynamicSeparationKind::StateDependentInteraction);
        }
        separations.push(DynamicStateSeparation {
            witness: witness.clone(),
            kinds,
            organizational_shapes_equal: shapes_equal,
        });
    }
    let cycles = model
        .states
        .iter()
        .map(|state| shortest_return_cycle(&model, state.id, &fibers))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect();
    let graded_words = u64::try_from(bounded_words(&standing.spec)?.len())
        .map_err(|_| CausalStateGrammarError::CarrierOverflow)?;
    let predictions_graded = u64::try_from(
        standing
            .history
            .iter()
            .filter(|entry| matches!(entry, CausalStateGrammarHistoryEntry::EmanatedPrediction(_)))
            .count(),
    )
    .map_err(|_| CausalStateGrammarError::CarrierOverflow)?;
    Ok(DynamicGrammarCertificate {
        schema: DYNAMIC_GRAMMAR_CERTIFICATE_SCHEMA.to_owned(),
        causal_model: model,
        grade_depth: standing.spec.grade_depth,
        graded_words,
        predictions_graded,
        prediction_obstructions: standing.prediction_obstructions.clone(),
        organizational_fibers,
        transports,
        separations,
        cycles,
        source_testimony_events: standing.used_events.clone(),
        bounded_region_complete: true,
    })
}

fn shortest_return_cycle(
    model: &CausalStateModel,
    root: LearnedCausalStateId,
    fibers: &BTreeMap<LearnedCausalStateId, &CausalStateOrganizationalFiber>,
) -> Result<Option<CausalStateCycle>, CausalStateGrammarError> {
    let mut queue = VecDeque::<(
        LearnedCausalStateId,
        CausalActionWord,
        Vec<LearnedCausalStateId>,
    )>::new();
    for transition in model
        .transitions
        .iter()
        .filter(|transition| transition.source == root)
    {
        queue.push_back((
            transition.target,
            CausalActionWord {
                actions: vec![transition.action],
            },
            vec![root, transition.target],
        ));
    }
    let mut visited = BTreeSet::new();
    while let Some((state, word, path)) = queue.pop_front() {
        if state == root {
            let start_shape = &fibers
                .get(&root)
                .ok_or(CausalStateGrammarError::MalformedStanding)?
                .shape;
            let return_shape = &fibers
                .get(&state)
                .ok_or(CausalStateGrammarError::MalformedStanding)?
                .shape;
            return Ok(Some(CausalStateCycle {
                root,
                word,
                traversed_states: path,
                organizational_shape_returns: start_shape == return_shape,
            }));
        }
        if !visited.insert(state) {
            continue;
        }
        for transition in model
            .transitions
            .iter()
            .filter(|transition| transition.source == state)
        {
            let mut next_word = word.clone();
            next_word.actions.push(transition.action);
            let mut next_path = path.clone();
            next_path.push(transition.target);
            queue.push_back((transition.target, next_word, next_path));
        }
    }
    Ok(None)
}

fn shortlex(mut words: Vec<CausalActionWord>) -> Vec<CausalActionWord> {
    words.sort_by(shortlex_cmp);
    words
}

fn shortlex_cmp(left: &CausalActionWord, right: &CausalActionWord) -> std::cmp::Ordering {
    left.len()
        .cmp(&right.len())
        .then_with(|| left.actions.cmp(&right.actions))
}

fn bounded_words(
    spec: &CausalStateGrammarSpec,
) -> Result<Vec<CausalActionWord>, CausalStateGrammarError> {
    let depth =
        usize::try_from(spec.grade_depth).map_err(|_| CausalStateGrammarError::CarrierOverflow)?;
    let mut words = vec![CausalActionWord::empty()];
    let mut frontier = vec![CausalActionWord::empty()];
    for _ in 0..depth {
        let mut next = Vec::new();
        for prefix in &frontier {
            for action in spec.action_ids() {
                next.push(prefix.appended(action));
                if words.len() + next.len() > MAX_BOUNDED_WORDS {
                    return Err(CausalStateGrammarError::BoundedLanguageExceedsCarrier {
                        maximum: MAX_BOUNDED_WORDS,
                    });
                }
            }
        }
        words.extend(next.iter().cloned());
        frontier = next;
    }
    Ok(shortlex(words))
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CausalStateGrammarError {
    #[error("the causal-state grammar specification is malformed")]
    MalformedSpec,
    #[error("the causal-state standing is malformed")]
    MalformedStanding,
    #[error("the returned causal observation is malformed")]
    MalformedObservation,
    #[error("the returned continuation trace is malformed")]
    MalformedTrace,
    #[error("the active observation table is malformed")]
    MalformedObservationTable,
    #[error("the active observation table is incomplete")]
    IncompleteObservationTable,
    #[error("the active observation table is not closed")]
    ObservationTableNotClosed,
    #[error("two learned states lack an exact distinguishing continuation")]
    StatesLackSeparation,
    #[error("event {0:?} was already admitted")]
    RepeatedEvent(EventId),
    #[error("no causal-state return was requested")]
    ReturnNotRequested,
    #[error("the returned event species does not match production's query")]
    UnexpectedReturnSpecies,
    #[error("the membrane returned a continuation other than production requested")]
    UnexpectedContinuationQuery {
        expected: Box<CausalContinuationQuery>,
        received: Box<CausalContinuationQuery>,
    },
    #[error("the membrane returned a state-local query other than production requested")]
    UnexpectedStateOrganizationQuery {
        expected: Box<StateOrganizationalQuery>,
        received: Box<StateOrganizationalQuery>,
    },
    #[error("learned state {0:?} is absent")]
    UnknownLearnedState(LearnedCausalStateId),
    #[error("learned transition {state:?} --{action:?}--> ? is absent")]
    MissingLearnedTransition {
        state: LearnedCausalStateId,
        action: CausalActionId,
    },
    #[error("the returned access trace does not reach production's learned state")]
    StateAccessReturnMismatch,
    #[error("one inferred state's organizational grammar remains incomplete")]
    IncompleteStateOrganization,
    #[error("the declared bounded word language exceeds the exact carrier maximum {maximum}")]
    BoundedLanguageExceedsCarrier { maximum: usize },
    #[error("an exact carrier conversion overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    Organizational(#[from] OrganizationalGrammarError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    use crate::{
        CausalWorld, OrganizationalConstraintSpec, OrganizationalSiteSpec, OrganizationalVariantId,
        OrganizationalVariantSpec,
    };

    const SCAFFOLD: CausalActionId = CausalActionId(1);
    const RELEASE: CausalActionId = CausalActionId(2);
    const DROP_DECOY: CausalActionId = CausalActionId(3);
    const PULSE: CausalObservableId = CausalObservableId(1);

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum ChargePhase {
        Rest,
        Charged,
        Released,
        Emitted,
    }

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    struct HiddenChargeWorld {
        phase: ChargePhase,
        sparse: bool,
    }

    impl Default for HiddenChargeWorld {
        fn default() -> Self {
            Self {
                phase: ChargePhase::Rest,
                sparse: false,
            }
        }
    }

    impl HiddenChargeWorld {
        fn enact(&mut self, action: CausalActionId) {
            match action {
                SCAFFOLD => {
                    self.phase = ChargePhase::Charged;
                }
                RELEASE => {
                    self.phase = match self.phase {
                        ChargePhase::Rest => ChargePhase::Rest,
                        ChargePhase::Charged => ChargePhase::Released,
                        ChargePhase::Released => ChargePhase::Emitted,
                        ChargePhase::Emitted => ChargePhase::Rest,
                    };
                }
                DROP_DECOY => {
                    self.sparse = true;
                }
                _ => panic!("the test membrane received an undeclared action"),
            }
        }

        fn observation(&self) -> CausalStateObservation {
            let pulse = i64::from(self.phase == ChargePhase::Emitted);
            let mut population = (1..=6).map(OrganizationalSiteId).collect::<BTreeSet<_>>();
            if self.sparse {
                population.remove(&OrganizationalSiteId(4));
            }
            CausalStateObservation::new(BTreeMap::from([(PULSE, value(pulse))]), population)
        }

        fn trace(word: &CausalActionWord) -> CausalContinuationTrace {
            let mut world = Self::default();
            let mut observations = vec![world.observation()];
            for action in &word.actions {
                world.enact(*action);
                observations.push(world.observation());
            }
            CausalContinuationTrace::new(observations)
        }

        fn after(word: &CausalActionWord) -> Self {
            let mut world = Self::default();
            for action in &word.actions {
                world.enact(*action);
            }
            world
        }
    }

    fn value(integer: i64) -> OrganizationalValue {
        BigRational::from_integer(BigInt::from(integer))
    }

    fn variant(id: u64, name: &str, lineage: u64) -> OrganizationalVariantSpec {
        OrganizationalVariantSpec {
            id: OrganizationalVariantId(id),
            name: name.to_owned(),
            lineage: OrganizationalLineageId(lineage),
        }
    }

    fn site(
        id: u64,
        name: &str,
        variants: Vec<OrganizationalVariantSpec>,
        reference_variant: Option<u64>,
    ) -> OrganizationalSiteSpec {
        OrganizationalSiteSpec {
            id: OrganizationalSiteId(id),
            name: name.to_owned(),
            variants,
            reference_variant: reference_variant.map(OrganizationalVariantId),
        }
    }

    fn constraint(id: u64, name: &str, receiver: u64) -> OrganizationalConstraintSpec {
        OrganizationalConstraintSpec {
            id: OrganizationalConstraintId(id),
            name: name.to_owned(),
            receiver: OrganizationalSiteId(receiver),
        }
    }

    fn organizational_spec() -> OrganizationalEcologySpec {
        OrganizationalEcologySpec::new(
            vec![
                site(
                    1,
                    "left resource relay",
                    vec![variant(11, "left", 101)],
                    Some(11),
                ),
                site(
                    2,
                    "right resource relay",
                    vec![
                        variant(21, "right lineage", 201),
                        variant(22, "homologous repair", 202),
                    ],
                    Some(21),
                ),
                site(
                    3,
                    "exterior control",
                    vec![variant(31, "control", 301)],
                    Some(31),
                ),
                site(
                    4,
                    "co-occurring decoy",
                    vec![variant(41, "decoy", 401)],
                    Some(41),
                ),
                site(
                    5,
                    "downstream consumer",
                    vec![variant(51, "consumer", 501)],
                    Some(51),
                ),
                site(
                    6,
                    "dormant scaffold",
                    vec![variant(61, "scaffold", 601)],
                    None,
                ),
            ],
            vec![
                constraint(1, "left stored resource", 1),
                constraint(2, "right stored resource", 2),
                constraint(3, "control standing", 3),
                constraint(4, "decoy standing", 4),
                constraint(5, "consumer standing", 5),
                constraint(6, "scaffold standing", 6),
            ],
        )
        .unwrap()
    }

    fn causal_spec() -> CausalStateGrammarSpec {
        CausalStateGrammarSpec::new(
            vec![
                CausalActionSpec {
                    id: SCAFFOLD,
                    name: "transient scaffold charge".to_owned(),
                },
                CausalActionSpec {
                    id: RELEASE,
                    name: "release stored charge".to_owned(),
                },
                CausalActionSpec {
                    id: DROP_DECOY,
                    name: "remove decoy population".to_owned(),
                },
            ],
            vec![CausalObservableSpec {
                id: PULSE,
                name: "visible release pulse".to_owned(),
            }],
            4,
            4,
            4,
            organizational_spec(),
        )
        .unwrap()
    }

    fn organizational_return(
        world: HiddenChargeWorld,
        query: &OrganizationalQuery,
    ) -> BTreeMap<OrganizationalConstraintId, OrganizationalValue> {
        let active = |site| {
            i64::from(
                query
                    .configuration
                    .selected_variant(OrganizationalSiteId(site))
                    .is_some(),
            )
        };
        let a = active(1);
        let b = active(2);
        let control = active(3);
        let decoy = active(4);
        let consumer = active(5);
        let scaffold = active(6);
        let transfer_coefficient = if world.phase == ChargePhase::Released {
            3
        } else {
            2
        };
        let reciprocal_transfer = transfer_coefficient * a * b * control;
        BTreeMap::from([
            (
                OrganizationalConstraintId(1),
                value(a + reciprocal_transfer + 5 * a * scaffold),
            ),
            (
                OrganizationalConstraintId(2),
                value(b - reciprocal_transfer),
            ),
            (OrganizationalConstraintId(3), value(control)),
            (
                OrganizationalConstraintId(4),
                value(if world.sparse { 0 } else { 7 * decoy }),
            ),
            (
                OrganizationalConstraintId(5),
                value(consumer + 3 * a * consumer),
            ),
            (OrganizationalConstraintId(6), value(scaffold)),
        ])
    }

    fn run_hidden_charge_experiment() -> (
        CausalWorld<CausalStateGrammarLaw>,
        Vec<CausalStateGrammarRadiation>,
    ) {
        let standing = CausalStateGrammarStanding::new(causal_spec()).unwrap();
        let mut machine = CausalWorld::new(CausalStateGrammarLaw, standing);
        let mut radiation = Vec::new();
        let mut next_event = 1_u64;
        let mut guard = 0_usize;
        while let Some(query) = machine.standing().next_query().cloned() {
            let event = match query {
                CausalStateGrammarQuery::Continuation(query) => {
                    CausalStateGrammarEvent::ReturnContinuation(CausalContinuationTestimony {
                        event: EventId(next_event),
                        receiver: OrganizationalLineageId(900),
                        trace: HiddenChargeWorld::trace(&query.word),
                        query,
                    })
                }
                CausalStateGrammarQuery::StateOrganization(query) => {
                    let hidden = HiddenChargeWorld::after(&query.access_word);
                    CausalStateGrammarEvent::ReturnStateOrganization(StateOrganizationalTestimony {
                        event: EventId(next_event),
                        receiver: OrganizationalLineageId(900),
                        access_trace: HiddenChargeWorld::trace(&query.access_word),
                        values: organizational_return(hidden, &query.organizational_query),
                        query,
                    })
                }
            };
            let receipt = machine.receive(&event).unwrap();
            radiation.extend(receipt.radiation);
            next_event += 1;
            guard += 1;
            assert!(guard < 5_000, "the active learner did not reach rest");
        }
        (machine, radiation)
    }

    #[test]
    fn production_owns_the_continuation_word() {
        let standing = CausalStateGrammarStanding::new(causal_spec()).unwrap();
        let mut machine = CausalWorld::new(CausalStateGrammarLaw, standing);
        let expected = machine.standing().next_query().unwrap().clone();
        let CausalStateGrammarQuery::Continuation(mut wrong) = expected else {
            panic!("the first query must be a continuation");
        };
        wrong.word = CausalActionWord {
            actions: vec![SCAFFOLD],
        };
        let result = machine.receive(&CausalStateGrammarEvent::ReturnContinuation(
            CausalContinuationTestimony {
                event: EventId(1),
                receiver: OrganizationalLineageId(900),
                trace: HiddenChargeWorld::trace(&wrong.word),
                query: wrong,
            },
        ));
        assert!(matches!(
            result,
            Err(CausalStateGrammarError::UnexpectedContinuationQuery { .. })
        ));
        assert!(machine.standing().history().is_empty());
    }

    #[test]
    fn conflicting_reset_testimony_becomes_a_determinism_obstruction() {
        let standing = CausalStateGrammarStanding::new(causal_spec()).unwrap();
        let mut machine = CausalWorld::new(CausalStateGrammarLaw, standing);
        let CausalStateGrammarQuery::Continuation(first_query) =
            machine.standing().next_query().unwrap().clone()
        else {
            panic!("the first query must be a continuation");
        };
        machine
            .receive(&CausalStateGrammarEvent::ReturnContinuation(
                CausalContinuationTestimony {
                    event: EventId(1),
                    receiver: OrganizationalLineageId(900),
                    trace: HiddenChargeWorld::trace(&first_query.word),
                    query: first_query,
                },
            ))
            .unwrap();
        let CausalStateGrammarQuery::Continuation(next_query) =
            machine.standing().next_query().unwrap().clone()
        else {
            panic!("the next query must be a continuation");
        };
        let mut conflicting_trace = HiddenChargeWorld::trace(&next_query.word);
        conflicting_trace.observations[0]
            .values
            .insert(PULSE, value(9));
        machine
            .receive(&CausalStateGrammarEvent::ReturnContinuation(
                CausalContinuationTestimony {
                    event: EventId(2),
                    receiver: OrganizationalLineageId(900),
                    query: next_query,
                    trace: conflicting_trace,
                },
            ))
            .unwrap();
        assert_eq!(
            machine.standing().phase,
            CausalStateGrammarPhase::DeterminismObstructed
        );
        assert!(machine.standing().determinism_obstruction().is_some());
        assert!(machine.standing().certificate().is_none());
    }

    #[test]
    fn an_insufficient_history_horizon_remains_a_depth_obstruction() {
        let base = causal_spec();
        let shallow = CausalStateGrammarSpec::new(
            base.actions,
            base.observables,
            1,
            1,
            4,
            base.organizational_ecology,
        )
        .unwrap();
        let standing = CausalStateGrammarStanding::new(shallow).unwrap();
        let mut machine = CausalWorld::new(CausalStateGrammarLaw, standing);
        let mut next_event = 1_u64;
        while let Some(query) = machine.standing().next_query().cloned() {
            let CausalStateGrammarQuery::Continuation(query) = query else {
                panic!("a shallow causal quotient must obstruct before organization");
            };
            machine
                .receive(&CausalStateGrammarEvent::ReturnContinuation(
                    CausalContinuationTestimony {
                        event: EventId(next_event),
                        receiver: OrganizationalLineageId(900),
                        trace: HiddenChargeWorld::trace(&query.word),
                        query,
                    },
                ))
                .unwrap();
            next_event += 1;
        }
        assert_eq!(
            machine.standing().phase,
            CausalStateGrammarPhase::DepthObstructed
        );
        assert!(machine.standing().depth_obstruction().is_some());
        assert!(machine.standing().certificate().is_none());
    }

    #[test]
    fn hidden_charge_becomes_temporal_state_with_organizational_fibers() {
        let (machine, radiation) = run_hidden_charge_experiment();
        let certificate = machine.standing().certificate().unwrap();
        assert_eq!(machine.standing().phase, CausalStateGrammarPhase::Certified);
        assert_eq!(certificate.causal_model.states.len(), 8);
        assert_eq!(certificate.organizational_fibers.len(), 8);
        assert_eq!(certificate.graded_words, 121);
        assert!(certificate.predictions_graded > 0);
        assert!(!certificate.prediction_obstructions.is_empty());
        assert!(certificate.bounded_region_complete);

        let expected_holon = BTreeSet::from([OrganizationalSiteId(1), OrganizationalSiteId(2)]);
        assert!(certificate.organizational_fibers.iter().all(|fiber| {
            fiber
                .grammar
                .learned_holons
                .iter()
                .any(|holon| holon.sites == expected_holon)
        }));
        assert!(certificate.organizational_fibers.iter().all(|fiber| {
            fiber
                .grammar
                .lineage_repairs
                .iter()
                .any(|repair| repair.site == OrganizationalSiteId(2))
        }));

        assert!(certificate.separations.iter().any(|separation| {
            separation
                .kinds
                .contains(&DynamicSeparationKind::TemporalStateRequired)
        }));
        assert!(certificate.separations.iter().any(|separation| {
            separation
                .kinds
                .contains(&DynamicSeparationKind::PopulationChange)
        }));
        assert!(certificate.separations.iter().any(|separation| {
            separation
                .kinds
                .contains(&DynamicSeparationKind::OrganizationalBoundaryRefinementAvailable)
        }));
        assert!(certificate.separations.iter().any(|separation| {
            separation
                .kinds
                .contains(&DynamicSeparationKind::StateDependentInteraction)
        }));
        assert!(certificate.transports.iter().any(|transport| {
            transport
                .departed_population
                .contains(&OrganizationalSiteId(4))
        }));
        assert!(certificate.transports.iter().any(|transport| {
            transport.carried_holons.contains(&expected_holon)
                && transport.coefficient_changes.iter().any(|change| {
                    change.key.support.sites()
                        == BTreeSet::from([
                            OrganizationalSiteId(1),
                            OrganizationalSiteId(2),
                            OrganizationalSiteId(3),
                        ])
                        && (change.residual == value(1) || change.residual == value(-1))
                })
        }));
        assert!(!certificate.cycles.is_empty());
        assert!(
            certificate
                .cycles
                .iter()
                .all(|cycle| cycle.organizational_shape_returns)
        );

        assert!(!machine.standing().prediction_obstructions().is_empty());
        assert!(
            radiation
                .iter()
                .any(|receipt| receipt.emitted_prediction.is_some())
        );
        assert!(
            radiation
                .iter()
                .any(|receipt| receipt.latest_prediction_obstruction.is_some())
        );
    }
}
