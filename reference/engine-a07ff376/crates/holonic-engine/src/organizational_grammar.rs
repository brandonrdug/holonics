//! Exact organizational grammar learned from receiver-returned interventions.
//!
//! The application declares a finite contemporary ecology: process sites,
//! lineage variants which may occupy those sites, and exact-valued constraints
//! received at the sites.  It does not declare a composite, dependency, or
//! learned successor.  Production chooses a traversal of the resulting
//! categorical configuration complex, retains every unvisited cell as open,
//! and admits only the complete exact values returned by the receiver.
//!
//! Once the finite fiber is complete, its unique multilinear Möbius expansion
//! exposes effects of every arity.  Mutual reachability through those effects,
//! recurrence at the contemporary section, and explicit exterior ports are the
//! evidence by which a subdiagram may be promoted to a holon.  This is an exact
//! bounded learner, not a claim that a finite intervention complex identifies
//! an unrestricted hidden mechanism.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_rational::BigRational;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{EventId, EventSuccessor, ExactEventLaw};

#[cfg(test)]
use num_bigint::BigInt;

pub type OrganizationalValue = BigRational;

const ORGANIZATIONAL_GRAMMAR_SCHEMA: &str = "holonic-engine.organizational-grammar.v1";
const ORGANIZATIONAL_SPEC_SCHEMA: &str = "holonic-engine.organizational-ecology.v1";
const ORGANIZATIONAL_QUERY_SCHEMA: &str = "holonic-engine.organizational-query.v1";
const ORGANIZATIONAL_CERTIFICATE_SCHEMA: &str =
    "holonic-engine.organizational-grammar-certificate.v1";
const MAX_EXACT_CONFIGURATION_VERTICES: usize = 1_048_576;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrganizationalSiteId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrganizationalVariantId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrganizationalConstraintId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrganizationalLineageId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct LearnedHolonId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalVariantSpec {
    pub id: OrganizationalVariantId,
    pub name: String,
    /// An inherited identity, not a production assertion that two variants
    /// are behaviorally homologous.
    pub lineage: OrganizationalLineageId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalSiteSpec {
    pub id: OrganizationalSiteId,
    pub name: String,
    pub variants: Vec<OrganizationalVariantSpec>,
    /// The currently returned local section. `None` means that this site is
    /// absent at the recurrent reference, not that the site is absolute zero.
    pub reference_variant: Option<OrganizationalVariantId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalConstraintSpec {
    pub id: OrganizationalConstraintId,
    pub name: String,
    pub receiver: OrganizationalSiteId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalEcologySpec {
    pub schema: String,
    pub sites: Vec<OrganizationalSiteSpec>,
    pub constraints: Vec<OrganizationalConstraintSpec>,
}

impl OrganizationalEcologySpec {
    pub fn new(
        sites: Vec<OrganizationalSiteSpec>,
        constraints: Vec<OrganizationalConstraintSpec>,
    ) -> Result<Self, OrganizationalGrammarError> {
        let spec = Self {
            schema: ORGANIZATIONAL_SPEC_SCHEMA.to_owned(),
            sites,
            constraints,
        };
        spec.validate()?;
        Ok(spec)
    }

    pub fn reference_configuration(
        &self,
    ) -> Result<OrganizationalConfiguration, OrganizationalGrammarError> {
        self.validate()?;
        Ok(OrganizationalConfiguration {
            selections: self
                .sites
                .iter()
                .map(|site| (site.id, site.reference_variant))
                .collect(),
        })
    }

    fn validate(&self) -> Result<(), OrganizationalGrammarError> {
        if self.schema != ORGANIZATIONAL_SPEC_SCHEMA || self.sites.is_empty() {
            return Err(OrganizationalGrammarError::MalformedEcology);
        }
        let mut sites = BTreeSet::new();
        let mut variants = BTreeSet::new();
        for site in &self.sites {
            if !sites.insert(site.id) || site.variants.is_empty() {
                return Err(OrganizationalGrammarError::MalformedEcology);
            }
            let local_variants = site
                .variants
                .iter()
                .map(|variant| variant.id)
                .collect::<BTreeSet<_>>();
            if local_variants.len() != site.variants.len()
                || site
                    .variants
                    .iter()
                    .any(|variant| !variants.insert(variant.id))
                || site
                    .reference_variant
                    .is_some_and(|variant| !local_variants.contains(&variant))
            {
                return Err(OrganizationalGrammarError::MalformedEcology);
            }
        }
        let mut constraints = BTreeSet::new();
        if self.constraints.is_empty()
            || self.constraints.iter().any(|constraint| {
                !constraints.insert(constraint.id) || !sites.contains(&constraint.receiver)
            })
            || sites.iter().any(|site| {
                !self
                    .constraints
                    .iter()
                    .any(|constraint| constraint.receiver == *site)
            })
        {
            return Err(OrganizationalGrammarError::MalformedEcology);
        }
        configuration_count(self)?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrganizationalConfiguration {
    pub selections: BTreeMap<OrganizationalSiteId, Option<OrganizationalVariantId>>,
}

impl OrganizationalConfiguration {
    pub fn selected_variant(&self, site: OrganizationalSiteId) -> Option<OrganizationalVariantId> {
        self.selections.get(&site).copied().flatten()
    }

    pub fn active_sites(&self) -> BTreeSet<OrganizationalSiteId> {
        self.selections
            .iter()
            .filter_map(|(site, variant)| variant.map(|_| *site))
            .collect()
    }

    pub fn changed_sites(&self, other: &Self) -> BTreeSet<OrganizationalSiteId> {
        self.selections
            .keys()
            .chain(other.selections.keys())
            .copied()
            .filter(|site| self.selections.get(site) != other.selections.get(site))
            .collect()
    }

    fn validate(&self, spec: &OrganizationalEcologySpec) -> Result<(), OrganizationalGrammarError> {
        if self.selections.len() != spec.sites.len() {
            return Err(OrganizationalGrammarError::MalformedConfiguration);
        }
        for site in &spec.sites {
            let selection = self
                .selections
                .get(&site.id)
                .ok_or(OrganizationalGrammarError::MalformedConfiguration)?;
            if let Some(variant) = selection
                && !site
                    .variants
                    .iter()
                    .any(|candidate| candidate.id == *variant)
            {
                return Err(OrganizationalGrammarError::VariantOutsideSite {
                    site: site.id,
                    variant: *variant,
                });
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecurrenceWitnessOrdinal {
    First,
    Return,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrganizationalQueryPurpose {
    EstablishRecurrence(RecurrenceWitnessOrdinal),
    TraverseOpenFiber,
    GradeLineagePrediction {
        site: OrganizationalSiteId,
        source: OrganizationalVariantId,
        replacement: OrganizationalVariantId,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalQuery {
    pub schema: String,
    pub configuration: OrganizationalConfiguration,
    pub purpose: OrganizationalQueryPurpose,
}

impl OrganizationalQuery {
    fn new(
        configuration: OrganizationalConfiguration,
        purpose: OrganizationalQueryPurpose,
    ) -> Self {
        Self {
            schema: ORGANIZATIONAL_QUERY_SCHEMA.to_owned(),
            configuration,
            purpose,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalObservation {
    pub event: EventId,
    pub receiver: OrganizationalLineageId,
    pub query: OrganizationalQuery,
    pub values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrganizationalGrammarHistoryEntry {
    SourceObservation(OrganizationalObservation),
    EmanatedLineagePrediction(LineagePrediction),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum OrganizationalExtension {
    ComposeInteraction,
    RefineBoundary,
    RaiseInteractionArity,
    AddHiddenReceiverFiber,
    UnfoldTemporalState,
    AdmitStateDependentInteraction,
    AdmitPopulationChange,
    GraftLineage,
    QuotientEquivalentLineages,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecurrenceObstruction {
    pub schema: String,
    pub first_event: EventId,
    pub return_event: EventId,
    pub configuration: OrganizationalConfiguration,
    pub differing_constraints: BTreeSet<OrganizationalConstraintId>,
    pub first_values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    pub return_values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    /// A single failed return does not decide which refinement is real.
    pub retained_extensions: BTreeSet<OrganizationalExtension>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InterventionObstruction {
    pub schema: String,
    pub event: EventId,
    pub configuration: OrganizationalConfiguration,
    pub changed_sites_from_reference: BTreeSet<OrganizationalSiteId>,
    pub residual_from_reference: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    pub retained_extensions: BTreeSet<OrganizationalExtension>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineagePrediction {
    pub schema: String,
    pub query: OrganizationalQuery,
    pub source_configuration: OrganizationalConfiguration,
    pub predicted_values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    pub supporting_contexts: u64,
    pub caused_by_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineagePredictionObstruction {
    pub schema: String,
    pub event: EventId,
    pub prediction: LineagePrediction,
    pub returned_values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    pub residual: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    pub differing_constraints: BTreeSet<OrganizationalConstraintId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GrammarFiberCell {
    Returned {
        event: EventId,
        values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    },
    Open,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalGrammarFiber {
    pub schema: String,
    /// One cell for every point of the declared categorical product.
    pub cells: BTreeMap<OrganizationalConfiguration, GrammarFiberCell>,
}

impl OrganizationalGrammarFiber {
    pub fn is_complete(&self) -> bool {
        self.cells
            .values()
            .all(|cell| matches!(cell, GrammarFiberCell::Returned { .. }))
    }

    pub fn open_cell_count(&self) -> usize {
        self.cells
            .values()
            .filter(|cell| matches!(cell, GrammarFiberCell::Open))
            .count()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct OrganizationalTermSupport {
    pub assignments: BTreeMap<OrganizationalSiteId, OrganizationalVariantId>,
}

impl OrganizationalTermSupport {
    pub fn sites(&self) -> BTreeSet<OrganizationalSiteId> {
        self.assignments.keys().copied().collect()
    }

    fn matches(&self, configuration: &OrganizationalConfiguration) -> bool {
        self.assignments
            .iter()
            .all(|(site, variant)| configuration.selected_variant(*site) == Some(*variant))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalInteractionTerm {
    pub support: OrganizationalTermSupport,
    pub coefficient: OrganizationalValue,
    pub arity: u64,
    /// These are receiver-returned causes of the emanated exact term.
    pub caused_by_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintGrammar {
    pub constraint: OrganizationalConstraintId,
    pub receiver: OrganizationalSiteId,
    pub source_constant: OrganizationalValue,
    pub interaction_terms: Vec<OrganizationalInteractionTerm>,
}

impl ConstraintGrammar {
    pub fn evaluate(&self, configuration: &OrganizationalConfiguration) -> OrganizationalValue {
        let mut value = self.source_constant.clone();
        for term in &self.interaction_terms {
            if term.support.matches(configuration) {
                value += &term.coefficient;
            }
        }
        value
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalDependency {
    pub source: OrganizationalSiteId,
    pub target: OrganizationalSiteId,
    pub constraint: OrganizationalConstraintId,
    pub support: OrganizationalTermSupport,
    pub coefficient: OrganizationalValue,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum OrganizationalPortDirection {
    Inbound,
    Outbound,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum OrganizationalPortStanding {
    PresentAtReference,
    DormantAtReference,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalPort {
    pub exterior_site: OrganizationalSiteId,
    pub direction: OrganizationalPortDirection,
    pub standing: OrganizationalPortStanding,
    pub affected_constraints: BTreeSet<OrganizationalConstraintId>,
    pub supports: BTreeSet<OrganizationalTermSupport>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ConstraintMaintenanceKind {
    SourceSupplied,
    InteractionMaintained,
    CompositeMaintained,
    ExteriorConditioned,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstraintMaintenanceReceipt {
    pub constraint: OrganizationalConstraintId,
    pub recurrent_value: OrganizationalValue,
    pub kinds: BTreeSet<ConstraintMaintenanceKind>,
    pub self_terms: BTreeSet<OrganizationalTermSupport>,
    pub composite_terms: BTreeSet<OrganizationalTermSupport>,
    pub exterior_terms: BTreeSet<OrganizationalTermSupport>,
    pub caused_by_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConservedInteractionReceipt {
    pub support: OrganizationalTermSupport,
    pub contributions: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    pub exact_residual: OrganizationalValue,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LearnedHolon {
    pub id: LearnedHolonId,
    pub sites: BTreeSet<OrganizationalSiteId>,
    pub recurrent_constraints: Vec<ConstraintMaintenanceReceipt>,
    pub internal_dependencies: Vec<OrganizationalDependency>,
    pub exterior_ports: Vec<OrganizationalPort>,
    pub conserved_interactions: Vec<ConservedInteractionReceipt>,
    pub recurrence_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineageRepairCertificate {
    pub site: OrganizationalSiteId,
    pub source: OrganizationalVariantId,
    pub replacement: OrganizationalVariantId,
    pub source_lineage: OrganizationalLineageId,
    pub replacement_lineage: OrganizationalLineageId,
    pub contexts_compared: u64,
    pub affected_constraints: BTreeSet<OrganizationalConstraintId>,
    pub predicted_before_grade: bool,
    pub caused_by_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalGrammarCertificate {
    pub schema: String,
    pub reference_configuration: OrganizationalConfiguration,
    pub recurrent_values: BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    pub constraint_grammars: Vec<ConstraintGrammar>,
    pub dependencies: Vec<OrganizationalDependency>,
    pub learned_holons: Vec<LearnedHolon>,
    pub lineage_repairs: Vec<LineageRepairCertificate>,
    /// Sites which were present in the recurrent section but entered no
    /// cross-site dependency are exact co-occurrences, not composite members.
    pub co_occurring_unbound_sites: BTreeSet<OrganizationalSiteId>,
    pub source_testimony_events: BTreeSet<EventId>,
    pub finite_region_complete: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrganizationalGrammarPhase {
    AwaitingFirstRecurrenceWitness,
    AwaitingReturnRecurrenceWitness,
    TraversingOpenFiber,
    AwaitingLineagePredictionGrade,
    TemporalObstruction,
    Certified,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
struct PendingLineageHoldout {
    site: OrganizationalSiteId,
    source: OrganizationalVariantId,
    replacement: OrganizationalVariantId,
    configuration: OrganizationalConfiguration,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalGrammarStanding {
    pub schema: String,
    pub spec: OrganizationalEcologySpec,
    pub phase: OrganizationalGrammarPhase,
    next_query: Option<OrganizationalQuery>,
    query_queue: VecDeque<OrganizationalConfiguration>,
    pending_holdout: Option<PendingLineageHoldout>,
    first_recurrence: Option<OrganizationalObservation>,
    reference_values: Option<BTreeMap<OrganizationalConstraintId, OrganizationalValue>>,
    observations: BTreeMap<
        OrganizationalConfiguration,
        (
            EventId,
            BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
        ),
    >,
    used_events: BTreeSet<EventId>,
    history: Vec<OrganizationalGrammarHistoryEntry>,
    recurrence_obstruction: Option<RecurrenceObstruction>,
    intervention_obstructions: Vec<InterventionObstruction>,
    lineage_prediction: Option<LineagePrediction>,
    lineage_prediction_obstruction: Option<LineagePredictionObstruction>,
    certificate: Option<OrganizationalGrammarCertificate>,
}

impl OrganizationalGrammarStanding {
    pub fn new(spec: OrganizationalEcologySpec) -> Result<Self, OrganizationalGrammarError> {
        spec.validate()?;
        let reference = spec.reference_configuration()?;
        Ok(Self {
            schema: ORGANIZATIONAL_GRAMMAR_SCHEMA.to_owned(),
            spec,
            phase: OrganizationalGrammarPhase::AwaitingFirstRecurrenceWitness,
            next_query: Some(OrganizationalQuery::new(
                reference,
                OrganizationalQueryPurpose::EstablishRecurrence(RecurrenceWitnessOrdinal::First),
            )),
            query_queue: VecDeque::new(),
            pending_holdout: None,
            first_recurrence: None,
            reference_values: None,
            observations: BTreeMap::new(),
            used_events: BTreeSet::new(),
            history: Vec::new(),
            recurrence_obstruction: None,
            intervention_obstructions: Vec::new(),
            lineage_prediction: None,
            lineage_prediction_obstruction: None,
            certificate: None,
        })
    }

    pub fn next_query(&self) -> Option<&OrganizationalQuery> {
        self.next_query.as_ref()
    }

    pub fn history(&self) -> &[OrganizationalGrammarHistoryEntry] {
        &self.history
    }

    pub fn recurrence_obstruction(&self) -> Option<&RecurrenceObstruction> {
        self.recurrence_obstruction.as_ref()
    }

    pub fn intervention_obstructions(&self) -> &[InterventionObstruction] {
        &self.intervention_obstructions
    }

    pub fn lineage_prediction(&self) -> Option<&LineagePrediction> {
        self.lineage_prediction.as_ref()
    }

    pub fn lineage_prediction_obstruction(&self) -> Option<&LineagePredictionObstruction> {
        self.lineage_prediction_obstruction.as_ref()
    }

    pub fn certificate(&self) -> Option<&OrganizationalGrammarCertificate> {
        self.certificate.as_ref()
    }

    pub fn grammar_fiber(&self) -> Result<OrganizationalGrammarFiber, OrganizationalGrammarError> {
        let configurations = configuration_traversal(&self.spec)?;
        let cells = configurations
            .into_iter()
            .map(|configuration| {
                let cell = self
                    .observations
                    .get(&configuration)
                    .map(|(event, values)| GrammarFiberCell::Returned {
                        event: *event,
                        values: values.clone(),
                    })
                    .unwrap_or(GrammarFiberCell::Open);
                (configuration, cell)
            })
            .collect();
        Ok(OrganizationalGrammarFiber {
            schema: "holonic-engine.organizational-grammar-fiber.v1".to_owned(),
            cells,
        })
    }

    fn validate_incremental(&self) -> Result<(), OrganizationalGrammarError> {
        self.spec.validate()?;
        if self.schema != ORGANIZATIONAL_GRAMMAR_SCHEMA {
            return Err(OrganizationalGrammarError::MalformedStanding);
        }
        match self.phase {
            OrganizationalGrammarPhase::AwaitingFirstRecurrenceWitness => {
                if !matches!(
                    self.next_query.as_ref().map(|query| &query.purpose),
                    Some(OrganizationalQueryPurpose::EstablishRecurrence(
                        RecurrenceWitnessOrdinal::First
                    ))
                ) || self.first_recurrence.is_some()
                {
                    return Err(OrganizationalGrammarError::MalformedStanding);
                }
            }
            OrganizationalGrammarPhase::AwaitingReturnRecurrenceWitness => {
                if !matches!(
                    self.next_query.as_ref().map(|query| &query.purpose),
                    Some(OrganizationalQueryPurpose::EstablishRecurrence(
                        RecurrenceWitnessOrdinal::Return
                    ))
                ) || self.first_recurrence.is_none()
                {
                    return Err(OrganizationalGrammarError::MalformedStanding);
                }
            }
            OrganizationalGrammarPhase::TraversingOpenFiber => {
                if self.next_query.is_none() || self.certificate.is_some() {
                    return Err(OrganizationalGrammarError::MalformedStanding);
                }
            }
            OrganizationalGrammarPhase::AwaitingLineagePredictionGrade => {
                if !matches!(
                    self.next_query.as_ref().map(|query| &query.purpose),
                    Some(OrganizationalQueryPurpose::GradeLineagePrediction { .. })
                ) || self.lineage_prediction.is_none()
                {
                    return Err(OrganizationalGrammarError::MalformedStanding);
                }
            }
            OrganizationalGrammarPhase::TemporalObstruction => {
                if self.next_query.is_some()
                    || self.recurrence_obstruction.is_none()
                    || self.certificate.is_some()
                {
                    return Err(OrganizationalGrammarError::MalformedStanding);
                }
            }
            OrganizationalGrammarPhase::Certified => {
                if self.next_query.is_some()
                    || self.certificate.is_none()
                    || !self.grammar_fiber()?.is_complete()
                {
                    return Err(OrganizationalGrammarError::MalformedStanding);
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum OrganizationalGrammarEvent {
    ReturnObservation(OrganizationalObservation),
}

impl OrganizationalGrammarEvent {
    fn event(&self) -> EventId {
        match self {
            Self::ReturnObservation(observation) => observation.event,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalGrammarWork {
    pub exact_additions: u64,
    pub exact_subtractions: u64,
    pub configurations_returned: u64,
    pub configurations_open: u64,
    pub interaction_terms_emitted: u64,
    pub reachability_pairs_tested: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrganizationalGrammarRadiation {
    pub schema: String,
    pub event: EventId,
    pub phase_after: OrganizationalGrammarPhase,
    pub next_query: Option<OrganizationalQuery>,
    pub recurrence_obstruction: Option<RecurrenceObstruction>,
    pub latest_intervention_obstruction: Option<InterventionObstruction>,
    pub lineage_prediction: Option<LineagePrediction>,
    pub lineage_prediction_obstruction: Option<LineagePredictionObstruction>,
    pub certificate: Option<OrganizationalGrammarCertificate>,
    pub work: OrganizationalGrammarWork,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct OrganizationalGrammarLaw;

impl ExactEventLaw for OrganizationalGrammarLaw {
    type Standing = OrganizationalGrammarStanding;
    type Event = OrganizationalGrammarEvent;
    type Radiation = OrganizationalGrammarRadiation;
    type Error = OrganizationalGrammarError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate_incremental()?;
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(OrganizationalGrammarError::RepeatedEvent(event_id));
        }
        let expected = standing_before
            .next_query
            .as_ref()
            .ok_or(OrganizationalGrammarError::ObservationNotRequested)?;
        let OrganizationalGrammarEvent::ReturnObservation(observation) = event;
        if observation.query != *expected {
            return Err(OrganizationalGrammarError::UnexpectedReturnedQuery {
                expected: Box::new(expected.clone()),
                received: Box::new(observation.query.clone()),
            });
        }
        observation
            .query
            .configuration
            .validate(&standing_before.spec)?;
        validate_values(&standing_before.spec, &observation.values)?;

        let mut standing_after = standing_before.clone();
        standing_after.next_query = None;
        standing_after.used_events.insert(event_id);
        standing_after
            .history
            .push(OrganizationalGrammarHistoryEntry::SourceObservation(
                observation.clone(),
            ));
        let mut work = OrganizationalGrammarWork::default();
        let prior_prediction = standing_after.lineage_prediction.clone();

        match standing_before.phase {
            OrganizationalGrammarPhase::AwaitingFirstRecurrenceWitness => {
                standing_after.first_recurrence = Some(observation.clone());
                standing_after.phase = OrganizationalGrammarPhase::AwaitingReturnRecurrenceWitness;
                standing_after.next_query = Some(OrganizationalQuery::new(
                    observation.query.configuration.clone(),
                    OrganizationalQueryPurpose::EstablishRecurrence(
                        RecurrenceWitnessOrdinal::Return,
                    ),
                ));
            }
            OrganizationalGrammarPhase::AwaitingReturnRecurrenceWitness => {
                let first = standing_before
                    .first_recurrence
                    .as_ref()
                    .ok_or(OrganizationalGrammarError::MalformedStanding)?;
                let differing_constraints =
                    differing_constraints(&first.values, &observation.values);
                if !differing_constraints.is_empty() {
                    standing_after.recurrence_obstruction = Some(RecurrenceObstruction {
                        schema: "holonic-engine.organizational-recurrence-obstruction.v1"
                            .to_owned(),
                        first_event: first.event,
                        return_event: observation.event,
                        configuration: observation.query.configuration.clone(),
                        differing_constraints,
                        first_values: first.values.clone(),
                        return_values: observation.values.clone(),
                        retained_extensions: BTreeSet::from([
                            OrganizationalExtension::AddHiddenReceiverFiber,
                            OrganizationalExtension::RefineBoundary,
                            OrganizationalExtension::UnfoldTemporalState,
                            OrganizationalExtension::AdmitStateDependentInteraction,
                            OrganizationalExtension::AdmitPopulationChange,
                        ]),
                    });
                    standing_after.phase = OrganizationalGrammarPhase::TemporalObstruction;
                } else {
                    standing_after.reference_values = Some(observation.values.clone());
                    standing_after.observations.insert(
                        observation.query.configuration.clone(),
                        (observation.event, observation.values.clone()),
                    );
                    let (queue, holdout) = prepare_traversal(&standing_after.spec)?;
                    standing_after.query_queue = queue;
                    standing_after.pending_holdout = holdout;
                    schedule_after_traversal(&mut standing_after, &mut work)?;
                }
            }
            OrganizationalGrammarPhase::TraversingOpenFiber => {
                admit_fiber_observation(&mut standing_after, observation, &mut work)?;
                schedule_after_traversal(&mut standing_after, &mut work)?;
            }
            OrganizationalGrammarPhase::AwaitingLineagePredictionGrade => {
                let prediction = standing_before
                    .lineage_prediction
                    .as_ref()
                    .ok_or(OrganizationalGrammarError::MalformedStanding)?
                    .clone();
                let residual = value_residual(&observation.values, &prediction.predicted_values);
                let differing_constraints = residual
                    .iter()
                    .filter_map(|(constraint, value)| (!value.is_zero()).then_some(*constraint))
                    .collect::<BTreeSet<_>>();
                if !differing_constraints.is_empty() {
                    standing_after.lineage_prediction_obstruction =
                        Some(LineagePredictionObstruction {
                            schema: "holonic-engine.lineage-prediction-obstruction.v1".to_owned(),
                            event: observation.event,
                            prediction,
                            returned_values: observation.values.clone(),
                            residual,
                            differing_constraints,
                        });
                }
                standing_after.observations.insert(
                    observation.query.configuration.clone(),
                    (observation.event, observation.values.clone()),
                );
                work.configurations_returned += 1;
                certify_complete_fiber(&mut standing_after, &mut work)?;
            }
            OrganizationalGrammarPhase::TemporalObstruction
            | OrganizationalGrammarPhase::Certified => {
                return Err(OrganizationalGrammarError::ObservationNotRequested);
            }
        }

        standing_after.validate_incremental()?;
        let fiber = standing_after.grammar_fiber()?;
        work.configurations_open = u64::try_from(fiber.open_cell_count())
            .map_err(|_| OrganizationalGrammarError::CarrierOverflow)?;
        let radiation = OrganizationalGrammarRadiation {
            schema: "holonic-engine.organizational-grammar-radiation.v1".to_owned(),
            event: event_id,
            phase_after: standing_after.phase,
            next_query: standing_after.next_query.clone(),
            recurrence_obstruction: standing_after.recurrence_obstruction.clone(),
            latest_intervention_obstruction: standing_after
                .intervention_obstructions
                .last()
                .cloned(),
            lineage_prediction: standing_after
                .lineage_prediction
                .clone()
                .filter(|prediction| prior_prediction.as_ref() != Some(prediction)),
            lineage_prediction_obstruction: standing_after.lineage_prediction_obstruction.clone(),
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

fn validate_values(
    spec: &OrganizationalEcologySpec,
    values: &BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
) -> Result<(), OrganizationalGrammarError> {
    let expected = spec
        .constraints
        .iter()
        .map(|constraint| constraint.id)
        .collect::<BTreeSet<_>>();
    let returned = values.keys().copied().collect::<BTreeSet<_>>();
    if expected != returned {
        return Err(OrganizationalGrammarError::MalformedObservation);
    }
    Ok(())
}

fn differing_constraints(
    left: &BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    right: &BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
) -> BTreeSet<OrganizationalConstraintId> {
    left.keys()
        .chain(right.keys())
        .copied()
        .filter(|constraint| left.get(constraint) != right.get(constraint))
        .collect()
}

fn value_residual(
    returned: &BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    expected: &BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
) -> BTreeMap<OrganizationalConstraintId, OrganizationalValue> {
    returned
        .iter()
        .map(|(constraint, value)| {
            (
                *constraint,
                value
                    - expected
                        .get(constraint)
                        .cloned()
                        .unwrap_or_else(BigRational::zero),
            )
        })
        .collect()
}

fn admit_fiber_observation(
    standing: &mut OrganizationalGrammarStanding,
    observation: &OrganizationalObservation,
    work: &mut OrganizationalGrammarWork,
) -> Result<(), OrganizationalGrammarError> {
    if let Some((prior_event, prior_values)) =
        standing.observations.get(&observation.query.configuration)
    {
        if prior_values != &observation.values {
            return Err(OrganizationalGrammarError::ConflictingObservation {
                first: *prior_event,
                second: observation.event,
            });
        }
    } else {
        standing.observations.insert(
            observation.query.configuration.clone(),
            (observation.event, observation.values.clone()),
        );
        work.configurations_returned += 1;
    }

    let reference = standing.spec.reference_configuration()?;
    let reference_values = standing
        .reference_values
        .as_ref()
        .ok_or(OrganizationalGrammarError::MalformedStanding)?;
    let residual = value_residual(&observation.values, reference_values);
    if residual.values().any(|value| !value.is_zero()) {
        let changed_sites = observation.query.configuration.changed_sites(&reference);
        let mut retained_extensions = BTreeSet::from([OrganizationalExtension::ComposeInteraction]);
        if changed_sites.len() > 1 {
            retained_extensions.insert(OrganizationalExtension::RaiseInteractionArity);
        } else {
            retained_extensions.insert(OrganizationalExtension::RefineBoundary);
        }
        if changed_sites.iter().any(|site| {
            reference.selected_variant(*site).is_some()
                && observation
                    .query
                    .configuration
                    .selected_variant(*site)
                    .is_some()
        }) {
            retained_extensions.insert(OrganizationalExtension::GraftLineage);
            retained_extensions.insert(OrganizationalExtension::QuotientEquivalentLineages);
        }
        standing
            .intervention_obstructions
            .push(InterventionObstruction {
                schema: "holonic-engine.organizational-intervention-obstruction.v1".to_owned(),
                event: observation.event,
                configuration: observation.query.configuration.clone(),
                changed_sites_from_reference: changed_sites,
                residual_from_reference: residual,
                retained_extensions,
            });
    }
    Ok(())
}

fn prepare_traversal(
    spec: &OrganizationalEcologySpec,
) -> Result<
    (
        VecDeque<OrganizationalConfiguration>,
        Option<PendingLineageHoldout>,
    ),
    OrganizationalGrammarError,
> {
    let reference = spec.reference_configuration()?;
    let holdout = spec.sites.iter().find_map(|site| {
        let source = site.reference_variant?;
        let replacement = site
            .variants
            .iter()
            .map(|variant| variant.id)
            .find(|variant| *variant != source)?;
        let mut configuration = reference.clone();
        configuration.selections.insert(site.id, Some(replacement));
        Some(PendingLineageHoldout {
            site: site.id,
            source,
            replacement,
            configuration,
        })
    });
    let mut traversal = configuration_traversal(spec)?;
    traversal.retain(|configuration| {
        configuration != &reference
            && holdout
                .as_ref()
                .is_none_or(|pending| configuration != &pending.configuration)
    });
    Ok((traversal.into(), holdout))
}

fn schedule_after_traversal(
    standing: &mut OrganizationalGrammarStanding,
    work: &mut OrganizationalGrammarWork,
) -> Result<(), OrganizationalGrammarError> {
    if let Some(configuration) = standing.query_queue.pop_front() {
        standing.phase = OrganizationalGrammarPhase::TraversingOpenFiber;
        standing.next_query = Some(OrganizationalQuery::new(
            configuration,
            OrganizationalQueryPurpose::TraverseOpenFiber,
        ));
        return Ok(());
    }
    if let Some(holdout) = standing.pending_holdout.take() {
        if let Some(prediction) = derive_lineage_prediction(standing, &holdout)? {
            standing.history.push(
                OrganizationalGrammarHistoryEntry::EmanatedLineagePrediction(prediction.clone()),
            );
            standing.next_query = Some(prediction.query.clone());
            standing.lineage_prediction = Some(prediction);
            standing.phase = OrganizationalGrammarPhase::AwaitingLineagePredictionGrade;
        } else {
            standing.phase = OrganizationalGrammarPhase::TraversingOpenFiber;
            standing.next_query = Some(OrganizationalQuery::new(
                holdout.configuration,
                OrganizationalQueryPurpose::TraverseOpenFiber,
            ));
        }
        return Ok(());
    }
    certify_complete_fiber(standing, work)
}

fn derive_lineage_prediction(
    standing: &OrganizationalGrammarStanding,
    holdout: &PendingLineageHoldout,
) -> Result<Option<LineagePrediction>, OrganizationalGrammarError> {
    let mut contexts = configuration_traversal(&standing.spec)?;
    contexts.retain(|configuration| configuration.selected_variant(holdout.site).is_none());
    let mut supporting_contexts = 0_u64;
    let mut caused_by_events = BTreeSet::new();
    for context in &contexts {
        let mut source_configuration = context.clone();
        source_configuration
            .selections
            .insert(holdout.site, Some(holdout.source));
        let mut replacement_configuration = context.clone();
        replacement_configuration
            .selections
            .insert(holdout.site, Some(holdout.replacement));
        if replacement_configuration == holdout.configuration {
            continue;
        }
        let Some((source_event, source_values)) = standing.observations.get(&source_configuration)
        else {
            return Ok(None);
        };
        let Some((replacement_event, replacement_values)) =
            standing.observations.get(&replacement_configuration)
        else {
            return Ok(None);
        };
        if source_values != replacement_values {
            return Ok(None);
        }
        caused_by_events.insert(*source_event);
        caused_by_events.insert(*replacement_event);
        supporting_contexts += 1;
    }
    if supporting_contexts == 0 {
        return Ok(None);
    }
    let mut source_configuration = holdout.configuration.clone();
    source_configuration
        .selections
        .insert(holdout.site, Some(holdout.source));
    let Some((source_event, predicted_values)) = standing.observations.get(&source_configuration)
    else {
        return Ok(None);
    };
    caused_by_events.insert(*source_event);
    let query = OrganizationalQuery::new(
        holdout.configuration.clone(),
        OrganizationalQueryPurpose::GradeLineagePrediction {
            site: holdout.site,
            source: holdout.source,
            replacement: holdout.replacement,
        },
    );
    Ok(Some(LineagePrediction {
        schema: "holonic-engine.lineage-prediction.v1".to_owned(),
        query,
        source_configuration,
        predicted_values: predicted_values.clone(),
        supporting_contexts,
        caused_by_events,
    }))
}

fn certify_complete_fiber(
    standing: &mut OrganizationalGrammarStanding,
    work: &mut OrganizationalGrammarWork,
) -> Result<(), OrganizationalGrammarError> {
    let fiber = standing.grammar_fiber()?;
    if !fiber.is_complete() {
        return Err(OrganizationalGrammarError::IncompleteFiber);
    }
    let certificate = compile_certificate(standing, work)?;
    standing.certificate = Some(certificate);
    standing.next_query = None;
    standing.phase = OrganizationalGrammarPhase::Certified;
    Ok(())
}

fn compile_certificate(
    standing: &OrganizationalGrammarStanding,
    work: &mut OrganizationalGrammarWork,
) -> Result<OrganizationalGrammarCertificate, OrganizationalGrammarError> {
    let spec = &standing.spec;
    let configurations = configuration_traversal(spec)?;
    let source_events = standing
        .history
        .iter()
        .filter_map(|entry| match entry {
            OrganizationalGrammarHistoryEntry::SourceObservation(observation) => {
                Some(observation.event)
            }
            OrganizationalGrammarHistoryEntry::EmanatedLineagePrediction(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let all_off = OrganizationalConfiguration {
        selections: spec.sites.iter().map(|site| (site.id, None)).collect(),
    };
    let all_off_values = standing
        .observations
        .get(&all_off)
        .ok_or(OrganizationalGrammarError::IncompleteFiber)?
        .1
        .clone();
    let mut constraint_grammars = Vec::new();
    for constraint in &spec.constraints {
        let mut interaction_terms = Vec::new();
        for configuration in &configurations {
            let assignments = configuration
                .selections
                .iter()
                .filter_map(|(site, variant)| variant.map(|variant| (*site, variant)))
                .collect::<BTreeMap<_, _>>();
            if assignments.is_empty() {
                continue;
            }
            let support = OrganizationalTermSupport { assignments };
            let (coefficient, additions, subtractions) =
                mobius_coefficient(standing, constraint.id, &support)?;
            work.exact_additions += additions;
            work.exact_subtractions += subtractions;
            if !coefficient.is_zero() {
                interaction_terms.push(OrganizationalInteractionTerm {
                    arity: u64::try_from(support.assignments.len())
                        .map_err(|_| OrganizationalGrammarError::CarrierOverflow)?,
                    support,
                    coefficient,
                    caused_by_events: source_events.clone(),
                });
            }
        }
        interaction_terms.sort_by(|left, right| {
            left.arity
                .cmp(&right.arity)
                .then_with(|| left.support.cmp(&right.support))
        });
        constraint_grammars.push(ConstraintGrammar {
            constraint: constraint.id,
            receiver: constraint.receiver,
            source_constant: all_off_values
                .get(&constraint.id)
                .cloned()
                .ok_or(OrganizationalGrammarError::MalformedObservation)?,
            interaction_terms,
        });
    }
    for configuration in &configurations {
        let returned = &standing
            .observations
            .get(configuration)
            .ok_or(OrganizationalGrammarError::IncompleteFiber)?
            .1;
        for grammar in &constraint_grammars {
            if grammar.evaluate(configuration)
                != *returned
                    .get(&grammar.constraint)
                    .ok_or(OrganizationalGrammarError::MalformedObservation)?
            {
                return Err(OrganizationalGrammarError::PolynomialResidualNonzero {
                    constraint: grammar.constraint,
                });
            }
        }
    }
    work.interaction_terms_emitted = u64::try_from(
        constraint_grammars
            .iter()
            .map(|grammar| grammar.interaction_terms.len())
            .sum::<usize>(),
    )
    .map_err(|_| OrganizationalGrammarError::CarrierOverflow)?;
    let dependencies = derive_dependencies(&constraint_grammars);
    let reference = spec.reference_configuration()?;
    let recurrent_values = standing
        .reference_values
        .clone()
        .ok_or(OrganizationalGrammarError::MalformedStanding)?;
    let recurrence_events = standing
        .first_recurrence
        .as_ref()
        .map(|first| BTreeSet::from([first.event]))
        .unwrap_or_default()
        .into_iter()
        .chain(
            standing
                .observations
                .get(&reference)
                .map(|(event, _)| *event),
        )
        .collect::<BTreeSet<_>>();
    let learned_holons = derive_holons(
        spec,
        &reference,
        &recurrent_values,
        &constraint_grammars,
        &dependencies,
        &recurrence_events,
        &source_events,
        work,
    )?;
    let lineage_repairs = derive_lineage_repairs(standing, &configurations, &learned_holons)?;
    let bound_sites = learned_holons
        .iter()
        .flat_map(|holon| holon.sites.iter().copied())
        .collect::<BTreeSet<_>>();
    let cross_sites = dependencies
        .iter()
        .filter(|dependency| dependency.source != dependency.target)
        .flat_map(|dependency| [dependency.source, dependency.target])
        .collect::<BTreeSet<_>>();
    let co_occurring_unbound_sites = reference
        .active_sites()
        .into_iter()
        .filter(|site| !bound_sites.contains(site) && !cross_sites.contains(site))
        .collect();
    Ok(OrganizationalGrammarCertificate {
        schema: ORGANIZATIONAL_CERTIFICATE_SCHEMA.to_owned(),
        reference_configuration: reference,
        recurrent_values,
        constraint_grammars,
        dependencies,
        learned_holons,
        lineage_repairs,
        co_occurring_unbound_sites,
        source_testimony_events: source_events,
        finite_region_complete: true,
    })
}

fn mobius_coefficient(
    standing: &OrganizationalGrammarStanding,
    constraint: OrganizationalConstraintId,
    support: &OrganizationalTermSupport,
) -> Result<(OrganizationalValue, u64, u64), OrganizationalGrammarError> {
    let assignments = support.assignments.iter().collect::<Vec<_>>();
    let mut coefficient = BigRational::zero();
    let mut additions = 0_u64;
    let mut subtractions = 0_u64;
    for subset in assignment_subsets(&assignments) {
        let mut configuration = OrganizationalConfiguration {
            selections: standing
                .spec
                .sites
                .iter()
                .map(|site| (site.id, None))
                .collect(),
        };
        for (site, variant) in &subset {
            configuration.selections.insert(**site, Some(**variant));
        }
        let value = standing
            .observations
            .get(&configuration)
            .and_then(|(_, values)| values.get(&constraint))
            .ok_or(OrganizationalGrammarError::IncompleteFiber)?;
        if (assignments.len() - subset.len()) % 2 == 0 {
            coefficient += value;
            additions += 1;
        } else {
            coefficient -= value;
            subtractions += 1;
        }
    }
    Ok((coefficient, additions, subtractions))
}

fn assignment_subsets<'a>(
    assignments: &[(&'a OrganizationalSiteId, &'a OrganizationalVariantId)],
) -> Vec<Vec<(&'a OrganizationalSiteId, &'a OrganizationalVariantId)>> {
    let mut subsets = vec![Vec::new()];
    for assignment in assignments {
        let additions = subsets
            .iter()
            .cloned()
            .map(|mut subset| {
                subset.push(*assignment);
                subset
            })
            .collect::<Vec<_>>();
        subsets.extend(additions);
    }
    subsets
}

fn derive_dependencies(grammars: &[ConstraintGrammar]) -> Vec<OrganizationalDependency> {
    let mut dependencies = Vec::new();
    for grammar in grammars {
        for term in &grammar.interaction_terms {
            for source in term.support.assignments.keys() {
                dependencies.push(OrganizationalDependency {
                    source: *source,
                    target: grammar.receiver,
                    constraint: grammar.constraint,
                    support: term.support.clone(),
                    coefficient: term.coefficient.clone(),
                });
            }
        }
    }
    dependencies.sort_by(|left, right| {
        left.source
            .cmp(&right.source)
            .then_with(|| left.target.cmp(&right.target))
            .then_with(|| left.constraint.cmp(&right.constraint))
            .then_with(|| left.support.cmp(&right.support))
    });
    dependencies
}

#[allow(clippy::too_many_arguments)]
fn derive_holons(
    spec: &OrganizationalEcologySpec,
    reference: &OrganizationalConfiguration,
    recurrent_values: &BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    grammars: &[ConstraintGrammar],
    dependencies: &[OrganizationalDependency],
    recurrence_events: &BTreeSet<EventId>,
    source_events: &BTreeSet<EventId>,
    work: &mut OrganizationalGrammarWork,
) -> Result<Vec<LearnedHolon>, OrganizationalGrammarError> {
    let sites = spec.sites.iter().map(|site| site.id).collect::<Vec<_>>();
    let adjacency = dependencies
        .iter()
        .filter(|dependency| dependency.source != dependency.target)
        .map(|dependency| (dependency.source, dependency.target))
        .collect::<BTreeSet<_>>();
    let mut reachability = BTreeSet::new();
    for source in &sites {
        let reachable = reachable_sites(*source, &adjacency);
        for target in reachable {
            reachability.insert((*source, target));
            work.reachability_pairs_tested += 1;
        }
    }
    let mut unassigned = sites.iter().copied().collect::<BTreeSet<_>>();
    let mut components = Vec::new();
    while let Some(seed) = unassigned.iter().next().copied() {
        let component = unassigned
            .iter()
            .copied()
            .filter(|candidate| {
                *candidate == seed
                    || (reachability.contains(&(seed, *candidate))
                        && reachability.contains(&(*candidate, seed)))
            })
            .collect::<BTreeSet<_>>();
        for site in &component {
            unassigned.remove(site);
        }
        if component.len() >= 2 {
            components.push(component);
        }
    }
    components.sort_by_key(|component| component.iter().next().copied());

    let mut holons = Vec::new();
    for component in components {
        let has_composite_term = grammars.iter().any(|grammar| {
            component.contains(&grammar.receiver)
                && grammar
                    .interaction_terms
                    .iter()
                    .any(|term| term.support.sites().intersection(&component).count() >= 2)
        });
        if !has_composite_term {
            continue;
        }
        let internal_dependencies = dependencies
            .iter()
            .filter(|dependency| {
                component.contains(&dependency.source) && component.contains(&dependency.target)
            })
            .cloned()
            .collect::<Vec<_>>();
        let exterior_ports = derive_ports(reference, &component, dependencies);
        let recurrent_constraints = grammars
            .iter()
            .filter(|grammar| component.contains(&grammar.receiver))
            .map(|grammar| {
                constraint_maintenance_receipt(grammar, &component, recurrent_values, source_events)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let conserved_interactions = derive_conserved_interactions(&component, grammars);
        holons.push(LearnedHolon {
            id: LearnedHolonId(
                u64::try_from(holons.len() + 1)
                    .map_err(|_| OrganizationalGrammarError::CarrierOverflow)?,
            ),
            sites: component,
            recurrent_constraints,
            internal_dependencies,
            exterior_ports,
            conserved_interactions,
            recurrence_events: recurrence_events.clone(),
        });
    }
    Ok(holons)
}

fn reachable_sites(
    source: OrganizationalSiteId,
    adjacency: &BTreeSet<(OrganizationalSiteId, OrganizationalSiteId)>,
) -> BTreeSet<OrganizationalSiteId> {
    let mut visited = BTreeSet::new();
    let mut queue = VecDeque::from([source]);
    while let Some(site) = queue.pop_front() {
        for (_, target) in adjacency.iter().filter(|(candidate, _)| *candidate == site) {
            if visited.insert(*target) {
                queue.push_back(*target);
            }
        }
    }
    visited
}

fn derive_ports(
    reference: &OrganizationalConfiguration,
    component: &BTreeSet<OrganizationalSiteId>,
    dependencies: &[OrganizationalDependency],
) -> Vec<OrganizationalPort> {
    let mut ports = BTreeMap::<
        (OrganizationalSiteId, OrganizationalPortDirection),
        (
            BTreeSet<OrganizationalConstraintId>,
            BTreeSet<OrganizationalTermSupport>,
        ),
    >::new();
    for dependency in dependencies {
        let key = if !component.contains(&dependency.source)
            && component.contains(&dependency.target)
        {
            Some((dependency.source, OrganizationalPortDirection::Inbound))
        } else if component.contains(&dependency.source) && !component.contains(&dependency.target)
        {
            Some((dependency.target, OrganizationalPortDirection::Outbound))
        } else {
            None
        };
        if let Some(key) = key {
            let entry = ports.entry(key).or_default();
            entry.0.insert(dependency.constraint);
            entry.1.insert(dependency.support.clone());
        }
    }
    ports
        .into_iter()
        .map(
            |((exterior_site, direction), (affected_constraints, supports))| OrganizationalPort {
                exterior_site,
                direction,
                standing: if reference.selected_variant(exterior_site).is_some() {
                    OrganizationalPortStanding::PresentAtReference
                } else {
                    OrganizationalPortStanding::DormantAtReference
                },
                affected_constraints,
                supports,
            },
        )
        .collect()
}

fn constraint_maintenance_receipt(
    grammar: &ConstraintGrammar,
    component: &BTreeSet<OrganizationalSiteId>,
    recurrent_values: &BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    source_events: &BTreeSet<EventId>,
) -> Result<ConstraintMaintenanceReceipt, OrganizationalGrammarError> {
    let mut kinds = BTreeSet::new();
    let mut self_terms = BTreeSet::new();
    let mut composite_terms = BTreeSet::new();
    let mut exterior_terms = BTreeSet::new();
    if !grammar.source_constant.is_zero() {
        kinds.insert(ConstraintMaintenanceKind::SourceSupplied);
    }
    for term in &grammar.interaction_terms {
        kinds.insert(ConstraintMaintenanceKind::InteractionMaintained);
        let sites = term.support.sites();
        if sites == BTreeSet::from([grammar.receiver]) {
            self_terms.insert(term.support.clone());
        }
        if sites.intersection(component).count() >= 2 {
            kinds.insert(ConstraintMaintenanceKind::CompositeMaintained);
            composite_terms.insert(term.support.clone());
        }
        if sites.iter().any(|site| !component.contains(site)) {
            kinds.insert(ConstraintMaintenanceKind::ExteriorConditioned);
            exterior_terms.insert(term.support.clone());
        }
    }
    Ok(ConstraintMaintenanceReceipt {
        constraint: grammar.constraint,
        recurrent_value: recurrent_values
            .get(&grammar.constraint)
            .cloned()
            .ok_or(OrganizationalGrammarError::MalformedStanding)?,
        kinds,
        self_terms,
        composite_terms,
        exterior_terms,
        caused_by_events: source_events.clone(),
    })
}

fn derive_conserved_interactions(
    component: &BTreeSet<OrganizationalSiteId>,
    grammars: &[ConstraintGrammar],
) -> Vec<ConservedInteractionReceipt> {
    let mut grouped = BTreeMap::<
        OrganizationalTermSupport,
        BTreeMap<OrganizationalConstraintId, OrganizationalValue>,
    >::new();
    for grammar in grammars
        .iter()
        .filter(|grammar| component.contains(&grammar.receiver))
    {
        for term in &grammar.interaction_terms {
            grouped
                .entry(term.support.clone())
                .or_default()
                .insert(grammar.constraint, term.coefficient.clone());
        }
    }
    grouped
        .into_iter()
        .filter_map(|(support, contributions)| {
            if contributions.len() < 2 {
                return None;
            }
            let residual = contributions
                .values()
                .fold(BigRational::zero(), |sum, value| sum + value);
            residual.is_zero().then_some(ConservedInteractionReceipt {
                support,
                contributions,
                exact_residual: residual,
            })
        })
        .collect()
}

fn derive_lineage_repairs(
    standing: &OrganizationalGrammarStanding,
    configurations: &[OrganizationalConfiguration],
    holons: &[LearnedHolon],
) -> Result<Vec<LineageRepairCertificate>, OrganizationalGrammarError> {
    let holon_sites = holons
        .iter()
        .flat_map(|holon| holon.sites.iter().copied())
        .collect::<BTreeSet<_>>();
    let mut repairs = Vec::new();
    for site in &standing.spec.sites {
        if !holon_sites.contains(&site.id) {
            continue;
        }
        for left_ordinal in 0..site.variants.len() {
            for right_ordinal in (left_ordinal + 1)..site.variants.len() {
                let left = &site.variants[left_ordinal];
                let right = &site.variants[right_ordinal];
                let mut contexts = configurations
                    .iter()
                    .filter(|configuration| configuration.selected_variant(site.id).is_none())
                    .cloned()
                    .collect::<Vec<_>>();
                contexts.sort();
                let mut contexts_compared = 0_u64;
                let mut affected_constraints = BTreeSet::new();
                let mut caused_by_events = BTreeSet::new();
                let mut equivalent = true;
                for context in contexts {
                    let mut left_configuration = context.clone();
                    left_configuration.selections.insert(site.id, Some(left.id));
                    let mut right_configuration = context.clone();
                    right_configuration
                        .selections
                        .insert(site.id, Some(right.id));
                    let (left_event, left_values) = standing
                        .observations
                        .get(&left_configuration)
                        .ok_or(OrganizationalGrammarError::IncompleteFiber)?;
                    let (right_event, right_values) = standing
                        .observations
                        .get(&right_configuration)
                        .ok_or(OrganizationalGrammarError::IncompleteFiber)?;
                    caused_by_events.insert(*left_event);
                    caused_by_events.insert(*right_event);
                    contexts_compared += 1;
                    if left_values != right_values {
                        equivalent = false;
                        break;
                    }
                    let (_, off_values) = standing
                        .observations
                        .get(&context)
                        .ok_or(OrganizationalGrammarError::IncompleteFiber)?;
                    affected_constraints.extend(differing_constraints(off_values, left_values));
                }
                if equivalent && !affected_constraints.is_empty() {
                    let predicted_before_grade =
                        standing
                            .lineage_prediction
                            .as_ref()
                            .is_some_and(|prediction| {
                                matches!(
                                    prediction.query.purpose,
                                    OrganizationalQueryPurpose::GradeLineagePrediction {
                                        site: predicted_site,
                                        source,
                                        replacement,
                                    } if predicted_site == site.id
                                        && ((source == left.id && replacement == right.id)
                                            || (source == right.id && replacement == left.id))
                                )
                            })
                            && standing.lineage_prediction_obstruction.is_none();
                    repairs.push(LineageRepairCertificate {
                        site: site.id,
                        source: left.id,
                        replacement: right.id,
                        source_lineage: left.lineage,
                        replacement_lineage: right.lineage,
                        contexts_compared,
                        affected_constraints,
                        predicted_before_grade,
                        caused_by_events,
                    });
                }
            }
        }
    }
    Ok(repairs)
}

fn configuration_count(
    spec: &OrganizationalEcologySpec,
) -> Result<usize, OrganizationalGrammarError> {
    let mut count = 1_usize;
    for site in &spec.sites {
        count = count
            .checked_mul(site.variants.len() + 1)
            .ok_or(OrganizationalGrammarError::CarrierOverflow)?;
        if count > MAX_EXACT_CONFIGURATION_VERTICES {
            return Err(
                OrganizationalGrammarError::ConfigurationSpaceExceedsExactCarrier {
                    vertices: count,
                    maximum: MAX_EXACT_CONFIGURATION_VERTICES,
                },
            );
        }
    }
    Ok(count)
}

fn configuration_traversal(
    spec: &OrganizationalEcologySpec,
) -> Result<Vec<OrganizationalConfiguration>, OrganizationalGrammarError> {
    let count = configuration_count(spec)?;
    let radices = spec
        .sites
        .iter()
        .map(|site| site.variants.len() + 1)
        .collect::<Vec<_>>();
    let digits = reflected_mixed_radix(&radices);
    if digits.len() != count {
        return Err(OrganizationalGrammarError::MalformedTraversal);
    }
    let mut configurations = digits
        .into_iter()
        .map(|digits| {
            let selections = spec
                .sites
                .iter()
                .zip(digits)
                .map(|(site, digit)| {
                    let variant = if digit == 0 {
                        None
                    } else {
                        Some(site.variants[digit - 1].id)
                    };
                    (site.id, variant)
                })
                .collect();
            OrganizationalConfiguration { selections }
        })
        .collect::<Vec<_>>();
    let reference = spec.reference_configuration()?;
    let reference_ordinal = configurations
        .iter()
        .position(|configuration| configuration == &reference)
        .ok_or(OrganizationalGrammarError::MalformedTraversal)?;
    configurations.rotate_left(reference_ordinal);
    for configuration in &configurations {
        configuration.validate(spec)?;
    }
    if configurations
        .windows(2)
        .any(|pair| pair[0].changed_sites(&pair[1]).len() != 1)
    {
        return Err(OrganizationalGrammarError::MalformedTraversal);
    }
    Ok(configurations)
}

fn reflected_mixed_radix(radices: &[usize]) -> Vec<Vec<usize>> {
    if radices.is_empty() {
        return vec![Vec::new()];
    }
    let tail = reflected_mixed_radix(&radices[1..]);
    let mut result = Vec::with_capacity(radices[0] * tail.len());
    for digit in 0..radices[0] {
        if digit % 2 == 0 {
            for suffix in &tail {
                let mut code = Vec::with_capacity(radices.len());
                code.push(digit);
                code.extend(suffix.iter().copied());
                result.push(code);
            }
        } else {
            for suffix in tail.iter().rev() {
                let mut code = Vec::with_capacity(radices.len());
                code.push(digit);
                code.extend(suffix.iter().copied());
                result.push(code);
            }
        }
    }
    result
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum OrganizationalGrammarError {
    #[error("the organizational ecology declaration is malformed")]
    MalformedEcology,
    #[error("the organizational standing is malformed")]
    MalformedStanding,
    #[error("the returned organizational observation is malformed")]
    MalformedObservation,
    #[error("the organizational configuration is malformed")]
    MalformedConfiguration,
    #[error("the categorical configuration traversal is malformed")]
    MalformedTraversal,
    #[error("site {0:?} is absent")]
    UnknownSite(OrganizationalSiteId),
    #[error("constraint {0:?} is absent")]
    UnknownConstraint(OrganizationalConstraintId),
    #[error("variant {variant:?} does not inhabit site {site:?}")]
    VariantOutsideSite {
        site: OrganizationalSiteId,
        variant: OrganizationalVariantId,
    },
    #[error("event {0:?} was already admitted")]
    RepeatedEvent(EventId),
    #[error("no organizational observation was requested")]
    ObservationNotRequested,
    #[error("the receiver returned a query other than production requested")]
    UnexpectedReturnedQuery {
        expected: Box<OrganizationalQuery>,
        received: Box<OrganizationalQuery>,
    },
    #[error("events {first:?} and {second:?} conflict at one configuration")]
    ConflictingObservation { first: EventId, second: EventId },
    #[error("the organizational grammar fiber remains open")]
    IncompleteFiber,
    #[error("the exact multilinear residual is nonzero for {constraint:?}")]
    PolynomialResidualNonzero {
        constraint: OrganizationalConstraintId,
    },
    #[error(
        "the exact configuration space has {vertices} vertices, exceeding this carrier's {maximum}"
    )]
    ConfigurationSpaceExceedsExactCarrier { vertices: usize, maximum: usize },
    #[error("an organizational carrier conversion overflowed")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CausalWorld;

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

    fn coupled_resource_spec() -> OrganizationalEcologySpec {
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

    /// This is the opaque world membrane. It supplies only complete returned
    /// values for production-selected configurations; it does not name the
    /// learned A/B composite, its ports, a polynomial, or a successor.
    fn coupled_resource_membrane(
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
        let reciprocal_transfer = 2 * a * b * control;
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
            (OrganizationalConstraintId(4), value(7 * decoy)),
            (
                OrganizationalConstraintId(5),
                value(consumer + 3 * a * consumer),
            ),
            (OrganizationalConstraintId(6), value(scaffold)),
        ])
    }

    fn return_all_requested(
        world: &mut CausalWorld<OrganizationalGrammarLaw>,
    ) -> Vec<OrganizationalGrammarRadiation> {
        let mut radiation = Vec::new();
        let mut next_event = 1_u64;
        while let Some(query) = world.standing().next_query().cloned() {
            let values = coupled_resource_membrane(&query);
            let receipt = world
                .receive(&OrganizationalGrammarEvent::ReturnObservation(
                    OrganizationalObservation {
                        event: EventId(next_event),
                        receiver: OrganizationalLineageId(900),
                        query,
                        values,
                    },
                ))
                .unwrap();
            radiation.extend(receipt.radiation);
            next_event += 1;
        }
        radiation
    }

    #[test]
    fn the_open_fiber_is_not_prematurely_called_a_grammar() {
        let standing = OrganizationalGrammarStanding::new(coupled_resource_spec()).unwrap();
        let fiber = standing.grammar_fiber().unwrap();
        assert!(!fiber.is_complete());
        assert_eq!(fiber.open_cell_count(), 96);
        assert!(standing.certificate().is_none());
    }

    #[test]
    fn recurrence_failure_retains_competing_structural_refinements() {
        let standing = OrganizationalGrammarStanding::new(coupled_resource_spec()).unwrap();
        let mut world = CausalWorld::new(OrganizationalGrammarLaw, standing);
        let first_query = world.standing().next_query().unwrap().clone();
        world
            .receive(&OrganizationalGrammarEvent::ReturnObservation(
                OrganizationalObservation {
                    event: EventId(1),
                    receiver: OrganizationalLineageId(900),
                    query: first_query,
                    values: coupled_resource_spec()
                        .constraints
                        .iter()
                        .map(|constraint| (constraint.id, value(0)))
                        .collect(),
                },
            ))
            .unwrap();
        let return_query = world.standing().next_query().unwrap().clone();
        let mut changed = coupled_resource_spec()
            .constraints
            .iter()
            .map(|constraint| (constraint.id, value(0)))
            .collect::<BTreeMap<_, _>>();
        changed.insert(OrganizationalConstraintId(1), value(1));
        world
            .receive(&OrganizationalGrammarEvent::ReturnObservation(
                OrganizationalObservation {
                    event: EventId(2),
                    receiver: OrganizationalLineageId(900),
                    query: return_query,
                    values: changed,
                },
            ))
            .unwrap();
        let obstruction = world.standing().recurrence_obstruction().unwrap();
        assert_eq!(
            world.standing().phase,
            OrganizationalGrammarPhase::TemporalObstruction
        );
        assert!(
            obstruction
                .retained_extensions
                .contains(&OrganizationalExtension::UnfoldTemporalState)
        );
        assert!(
            obstruction
                .retained_extensions
                .contains(&OrganizationalExtension::AddHiddenReceiverFiber)
        );
        assert!(world.standing().certificate().is_none());
    }

    #[test]
    fn exact_interventions_emit_a_conserved_holon_and_grade_repair() {
        let standing = OrganizationalGrammarStanding::new(coupled_resource_spec()).unwrap();
        let mut world = CausalWorld::new(OrganizationalGrammarLaw, standing);
        let radiation = return_all_requested(&mut world);
        let certificate = world.standing().certificate().unwrap();

        assert_eq!(
            world.standing().phase,
            OrganizationalGrammarPhase::Certified
        );
        assert!(world.standing().grammar_fiber().unwrap().is_complete());
        assert_eq!(certificate.learned_holons.len(), 1);
        let holon = &certificate.learned_holons[0];
        assert_eq!(
            holon.sites,
            BTreeSet::from([OrganizationalSiteId(1), OrganizationalSiteId(2)])
        );
        assert!(holon.conserved_interactions.iter().any(|conservation| {
            conservation.support.sites()
                == BTreeSet::from([
                    OrganizationalSiteId(1),
                    OrganizationalSiteId(2),
                    OrganizationalSiteId(3),
                ])
                && conservation.exact_residual.is_zero()
                && conservation
                    .contributions
                    .get(&OrganizationalConstraintId(1))
                    == Some(&value(2))
                && conservation
                    .contributions
                    .get(&OrganizationalConstraintId(2))
                    == Some(&value(-2))
        }));
        assert!(holon.exterior_ports.iter().any(|port| {
            port.exterior_site == OrganizationalSiteId(3)
                && port.direction == OrganizationalPortDirection::Inbound
                && port.standing == OrganizationalPortStanding::PresentAtReference
        }));
        assert!(holon.exterior_ports.iter().any(|port| {
            port.exterior_site == OrganizationalSiteId(5)
                && port.direction == OrganizationalPortDirection::Outbound
        }));
        assert!(holon.exterior_ports.iter().any(|port| {
            port.exterior_site == OrganizationalSiteId(6)
                && port.direction == OrganizationalPortDirection::Inbound
                && port.standing == OrganizationalPortStanding::DormantAtReference
        }));
        assert!(
            certificate
                .co_occurring_unbound_sites
                .contains(&OrganizationalSiteId(4))
        );
        assert!(!holon.sites.contains(&OrganizationalSiteId(4)));

        assert_eq!(certificate.lineage_repairs.len(), 1);
        let repair = &certificate.lineage_repairs[0];
        assert_eq!(repair.site, OrganizationalSiteId(2));
        assert!(repair.predicted_before_grade);
        assert!(!repair.affected_constraints.is_empty());
        assert!(
            radiation
                .iter()
                .any(|receipt| receipt.lineage_prediction.is_some())
        );
        assert!(world.standing().lineage_prediction_obstruction().is_none());

        let left_grammar = certificate
            .constraint_grammars
            .iter()
            .find(|grammar| grammar.constraint == OrganizationalConstraintId(1))
            .unwrap();
        assert!(left_grammar.interaction_terms.iter().any(|term| {
            term.support.sites()
                == BTreeSet::from([
                    OrganizationalSiteId(1),
                    OrganizationalSiteId(2),
                    OrganizationalSiteId(3),
                ])
                && term.coefficient == value(2)
        }));
        assert!(certificate.finite_region_complete);
    }

    #[test]
    fn a_failed_held_out_return_obstructs_repair_without_losing_the_exact_grammar() {
        let standing = OrganizationalGrammarStanding::new(coupled_resource_spec()).unwrap();
        let mut world = CausalWorld::new(OrganizationalGrammarLaw, standing);
        let mut next_event = 1_u64;
        while let Some(query) = world.standing().next_query().cloned() {
            let mut values = coupled_resource_membrane(&query);
            if matches!(
                query.purpose,
                OrganizationalQueryPurpose::GradeLineagePrediction { .. }
            ) {
                *values.get_mut(&OrganizationalConstraintId(1)).unwrap() += value(1);
            }
            world
                .receive(&OrganizationalGrammarEvent::ReturnObservation(
                    OrganizationalObservation {
                        event: EventId(next_event),
                        receiver: OrganizationalLineageId(900),
                        query,
                        values,
                    },
                ))
                .unwrap();
            next_event += 1;
        }

        assert_eq!(
            world.standing().phase,
            OrganizationalGrammarPhase::Certified
        );
        assert!(world.standing().lineage_prediction_obstruction().is_some());
        assert!(
            world
                .standing()
                .certificate()
                .unwrap()
                .lineage_repairs
                .is_empty()
        );
        assert!(world.standing().grammar_fiber().unwrap().is_complete());
    }

    #[test]
    fn reflected_product_traversal_changes_one_site_at_a_time() {
        let spec = coupled_resource_spec();
        let traversal = configuration_traversal(&spec).unwrap();
        assert_eq!(traversal.len(), 96);
        assert!(
            traversal
                .windows(2)
                .all(|pair| pair[0].changed_sites(&pair[1]).len() == 1)
        );
    }
}
