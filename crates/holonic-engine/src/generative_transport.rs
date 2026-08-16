//! Predictive fibers and production-derived extensions for exact transport.
//!
//! The inherited grammar is the unit-capacity passive operator
//! `A(tau) = I + tau L`. A complete returned operator which cannot inhabit
//! that grammar is retained as an obstruction. Production then derives the
//! parameterized family
//!
//! `A(tau) = M + tau (S + K + R)`
//!
//! where `M` is diagonal receiver capacity, `S` is symmetric pair transport,
//! `K` is skew pair transport, and `R` is diagonal reaction. The family is
//! constrained by exact testimony and remains predictive before it closes.
//! Production selects observations at a second interval and grades the
//! generated model against a complete, previously unseen third interval.
//!
//! # Where the algebra lives
//!
//! The dense exact algebra is `exact_linear::ExactRatMatrix`. It was this module's own until
//! 2026-08-15, and the 33-line elimination body of its private `invert_exact` differed from
//! `inverse_transport`'s by exactly one line — the error variant it named on a singular pivot.
//! Neither function checked the inverse it returned, and this module has the **weakest** of the
//! six call sites: `enact`'s complete-operator branch recomputes the full identity residual and
//! refuses on it, but `propagate` checks only `A x - b` for the single right-hand side it solved,
//! which verifies the inverse against one vector and not against the identity. Routing through
//! the carrier puts the identity check inside the operation, so `propagate` now has it too.
//!
//! The carrier's refusals are renamed into this module's own vocabulary below, so no foreign
//! error variant reaches a caller.

use std::collections::BTreeSet;

use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::{
    AffineAdmissionWork, EventId, EventSuccessor, ExactAffinePrediction, ExactAffineVersionFiber,
    ExactEventLaw, InverseTransportError, PotentialTransportEdge, TransportLineageId,
    TransportQuery,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ParameterizedTransportVariable {
    ReceiverCapacity(u32),
    SymmetricPair(PotentialTransportEdge),
    SkewPair(PotentialTransportEdge),
    Reaction(u32),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterizedTransportQuery {
    pub interval: Rat,
    pub imposed_potential: Vec<Rat>,
    pub receiver: Vec<Rat>,
}

impl ParameterizedTransportQuery {
    pub fn new(
        interval: Rat,
        imposed_potential: Vec<Rat>,
        receiver: Vec<Rat>,
    ) -> Result<Self, GenerativeTransportError> {
        if !interval.is_positive() {
            return Err(GenerativeTransportError::NonpositiveInterval);
        }
        let query = TransportQuery::new(imposed_potential, receiver)?;
        Ok(Self {
            interval,
            imposed_potential: query.imposed_potential,
            receiver: query.receiver,
        })
    }

    fn basis(
        extent: usize,
        interval: Rat,
        row: usize,
        column: usize,
    ) -> Result<Self, GenerativeTransportError> {
        if row >= extent || column >= extent {
            return Err(GenerativeTransportError::OperatorCoordinateOutOfRange {
                row,
                column,
                extent,
            });
        }
        let mut imposed_potential = vec![Rat::zero(); extent];
        let mut receiver = vec![Rat::zero(); extent];
        imposed_potential[column] = Rat::one();
        receiver[row] = Rat::one();
        Self::new(interval, imposed_potential, receiver)
    }

    fn validate(&self, extent: usize) -> Result<(), GenerativeTransportError> {
        if !self.interval.is_positive() {
            return Err(GenerativeTransportError::NonpositiveInterval);
        }
        if self.imposed_potential.len() != extent || self.receiver.len() != extent {
            return Err(GenerativeTransportError::QueryDimension {
                expected: extent,
                potentials: self.imposed_potential.len(),
                receiver: self.receiver.len(),
            });
        }
        if self.imposed_potential.iter().all(Zero::is_zero) {
            return Err(GenerativeTransportError::ZeroPotentialQuery);
        }
        if self.receiver.iter().all(Zero::is_zero) {
            return Err(GenerativeTransportError::ZeroReceiverQuery);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterizedTransportPrediction {
    pub schema: String,
    pub query: ParameterizedTransportQuery,
    pub affine: ExactAffinePrediction,
    pub unresolved_variables: Vec<ParameterizedTransportVariable>,
}

impl ParameterizedTransportPrediction {
    pub fn is_determined(&self) -> bool {
        self.affine.is_determined()
    }

    pub fn determined_value(&self) -> Option<&Rat> {
        self.affine.determined_value()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterizedTransportFamily {
    pub schema: String,
    pub extent: u32,
    pub variables: Vec<ParameterizedTransportVariable>,
    fiber: ExactAffineVersionFiber,
}

impl ParameterizedTransportFamily {
    fn new(extent: u32) -> Result<Self, GenerativeTransportError> {
        let variables = parameterized_variables(extent)?;
        let fiber = ExactAffineVersionFiber::new(variables.len())?;
        Ok(Self {
            schema: "holonic-engine.parameterized-transport-family.v1".to_owned(),
            extent,
            variables,
            fiber,
        })
    }

    pub fn fiber(&self) -> &ExactAffineVersionFiber {
        &self.fiber
    }

    pub fn affine_dimension(&self) -> usize {
        self.fiber.affine_dimension()
    }

    pub fn predict(
        &self,
        query: &ParameterizedTransportQuery,
    ) -> Result<ParameterizedTransportPrediction, GenerativeTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        query.validate(extent)?;
        let coefficients = parameterized_coefficients(&self.variables, query)?;
        let affine = self.fiber.predict(&coefficients, Rat::zero())?;
        let unresolved_variables = affine
            .free_coordinates
            .iter()
            .map(|coordinate| self.variables[*coordinate])
            .collect();
        Ok(ParameterizedTransportPrediction {
            schema: "holonic-engine.parameterized-transport-prediction.v1".to_owned(),
            query: query.clone(),
            affine,
            unresolved_variables,
        })
    }

    fn admit(
        &mut self,
        query: &ParameterizedTransportQuery,
        response: Rat,
    ) -> Result<AffineAdmissionWork, GenerativeTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        query.validate(extent)?;
        let coefficients = parameterized_coefficients(&self.variables, query)?;
        Ok(self.fiber.admit(coefficients, response)?)
    }

    fn unique_model(
        &self,
    ) -> Result<Option<ParameterizedTransportModel>, GenerativeTransportError> {
        let Some(solution) = self.fiber.unique_solution()? else {
            return Ok(None);
        };
        Ok(Some(ParameterizedTransportModel::from_solution(
            self.extent,
            &self.variables,
            &solution,
        )?))
    }

    fn validate(&self) -> Result<(), GenerativeTransportError> {
        if self.schema != "holonic-engine.parameterized-transport-family.v1"
            || self.variables != parameterized_variables(self.extent)?
            || self.fiber.variable_count() != self.variables.len()
        {
            return Err(GenerativeTransportError::MalformedFamily);
        }
        self.fiber.validate()?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TransportExtensionNeed {
    DiagonalStandingOrReaction,
    SkewPairTransport,
    ActiveSymmetricTransport,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportModelObstruction {
    pub schema: String,
    pub event: EventId,
    pub interval: Rat,
    pub returned_operator: Vec<Vec<Rat>>,
    pub symmetry_residual: Vec<Vec<Rat>>,
    pub unit_row_residual: Vec<Rat>,
    pub extension_needs: BTreeSet<TransportExtensionNeed>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum GeneratedTransportSpecies {
    ReceiverCapacity,
    PassiveSymmetricTransport,
    ActiveSymmetricTransport,
    SkewPairTransport,
    Reaction,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedTransportEdge {
    pub edge: PotentialTransportEdge,
    pub symmetric_coupling: Rat,
    pub skew_coupling: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterizedTransportModel {
    pub schema: String,
    pub extent: u32,
    pub capacities: Vec<Rat>,
    pub edges: Vec<GeneratedTransportEdge>,
    pub reactions: Vec<Rat>,
    pub species: BTreeSet<GeneratedTransportSpecies>,
}

impl ParameterizedTransportModel {
    fn from_solution(
        extent: u32,
        variables: &[ParameterizedTransportVariable],
        solution: &[Rat],
    ) -> Result<Self, GenerativeTransportError> {
        let extent_usize =
            usize::try_from(extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        if solution.len() != variables.len() {
            return Err(GenerativeTransportError::MalformedGeneratedModel);
        }
        let edge_order = canonical_edges(extent)?;
        let mut capacities = vec![Rat::zero(); extent_usize];
        let mut symmetric = vec![Rat::zero(); edge_order.len()];
        let mut skew = vec![Rat::zero(); edge_order.len()];
        let mut reactions = vec![Rat::zero(); extent_usize];
        for (variable, value) in variables.iter().zip(solution) {
            match variable {
                ParameterizedTransportVariable::ReceiverCapacity(node) => {
                    capacities[usize::try_from(*node)
                        .map_err(|_| GenerativeTransportError::CarrierOverflow)?] = value.clone();
                }
                ParameterizedTransportVariable::SymmetricPair(edge) => {
                    symmetric[edge_ordinal(extent, *edge)?] = value.clone();
                }
                ParameterizedTransportVariable::SkewPair(edge) => {
                    skew[edge_ordinal(extent, *edge)?] = value.clone();
                }
                ParameterizedTransportVariable::Reaction(node) => {
                    reactions[usize::try_from(*node)
                        .map_err(|_| GenerativeTransportError::CarrierOverflow)?] = value.clone();
                }
            }
        }
        if let Some((node, _)) = capacities
            .iter()
            .enumerate()
            .find(|(_, capacity)| !capacity.is_positive())
        {
            return Err(GenerativeTransportError::NonpositiveGeneratedCapacity { node });
        }
        let edges = edge_order
            .into_iter()
            .zip(symmetric)
            .zip(skew)
            .map(
                |((edge, symmetric_coupling), skew_coupling)| GeneratedTransportEdge {
                    edge,
                    symmetric_coupling,
                    skew_coupling,
                },
            )
            .collect::<Vec<_>>();
        let mut species = BTreeSet::new();
        if capacities.iter().any(|capacity| capacity != &Rat::one()) {
            species.insert(GeneratedTransportSpecies::ReceiverCapacity);
        }
        if edges
            .iter()
            .any(|edge| edge.symmetric_coupling.is_positive())
        {
            species.insert(GeneratedTransportSpecies::PassiveSymmetricTransport);
        }
        if edges
            .iter()
            .any(|edge| edge.symmetric_coupling.is_negative())
        {
            species.insert(GeneratedTransportSpecies::ActiveSymmetricTransport);
        }
        if edges.iter().any(|edge| !edge.skew_coupling.is_zero()) {
            species.insert(GeneratedTransportSpecies::SkewPairTransport);
        }
        if reactions.iter().any(|reaction| !reaction.is_zero()) {
            species.insert(GeneratedTransportSpecies::Reaction);
        }
        let model = Self {
            schema: "holonic-engine.parameterized-transport-model.v1".to_owned(),
            extent,
            capacities,
            edges,
            reactions,
            species,
        };
        model.validate()?;
        Ok(model)
    }

    pub fn event_operator(
        &self,
        interval: &Rat,
    ) -> Result<Vec<Vec<Rat>>, GenerativeTransportError> {
        if !interval.is_positive() {
            return Err(GenerativeTransportError::NonpositiveInterval);
        }
        self.validate()?;
        let extent =
            usize::try_from(self.extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        let mut generator = zero_matrix(extent, extent);
        for edge in &self.edges {
            let left = usize::try_from(edge.edge.left)
                .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
            let right = usize::try_from(edge.edge.right)
                .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
            generator[left][left] += &edge.symmetric_coupling;
            generator[right][right] += &edge.symmetric_coupling;
            generator[left][right] -= &edge.symmetric_coupling;
            generator[right][left] -= &edge.symmetric_coupling;
            generator[left][right] += &edge.skew_coupling;
            generator[right][left] -= &edge.skew_coupling;
        }
        for (node, reaction) in self.reactions.iter().enumerate() {
            generator[node][node] += reaction;
        }
        let mut operator = generator
            .into_iter()
            .map(|row| row.into_iter().map(|value| interval * value).collect())
            .collect::<Vec<Vec<Rat>>>();
        for (node, capacity) in self.capacities.iter().enumerate() {
            operator[node][node] += capacity;
        }
        Ok(operator)
    }

    pub fn clamped_response(
        &self,
        query: &ParameterizedTransportQuery,
    ) -> Result<Rat, GenerativeTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        query.validate(extent)?;
        let operated = matrix_vector(
            &self.event_operator(&query.interval)?,
            &query.imposed_potential,
        )?;
        dot(&query.receiver, &operated)
    }

    pub fn propagate(
        &self,
        interval: Rat,
        right_hand: Vec<Rat>,
    ) -> Result<ParameterizedTransportPropagation, GenerativeTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        if right_hand.len() != extent {
            return Err(GenerativeTransportError::PropagationDimension {
                expected: extent,
                supplied: right_hand.len(),
            });
        }
        let operator = self.event_operator(&interval)?;
        let inverse = invert_exact(operator.clone())?;
        let potential = matrix_vector(&inverse, &right_hand)?;
        let content_after = potential
            .iter()
            .zip(&self.capacities)
            .map(|(potential, capacity)| potential * capacity)
            .collect::<Vec<_>>();
        let operator_residual =
            vector_subtract(&matrix_vector(&operator, &potential)?, &right_hand)?;
        if operator_residual.iter().any(|value| !value.is_zero()) {
            return Err(GenerativeTransportError::OperatorResidualNonzero);
        }
        let total_right_hand = sum(&right_hand);
        let total_content_after = sum(&content_after);
        let net_exchange = &total_content_after - &total_right_hand;
        Ok(ParameterizedTransportPropagation {
            schema: "holonic-engine.parameterized-transport-propagation.v1".to_owned(),
            interval,
            right_hand,
            potential,
            content_after,
            operator_residual,
            total_right_hand,
            total_content_after,
            net_exchange,
        })
    }

    fn validate(&self) -> Result<(), GenerativeTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        if self.schema != "holonic-engine.parameterized-transport-model.v1"
            || extent < 2
            || self.capacities.len() != extent
            || self.reactions.len() != extent
            || self.edges.len() != canonical_edges(self.extent)?.len()
            || self
                .capacities
                .iter()
                .any(|capacity| !capacity.is_positive())
            || self.edges.iter().map(|edge| edge.edge).collect::<Vec<_>>()
                != canonical_edges(self.extent)?
        {
            return Err(GenerativeTransportError::MalformedGeneratedModel);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterizedTransportPropagation {
    pub schema: String,
    pub interval: Rat,
    pub right_hand: Vec<Rat>,
    pub potential: Vec<Rat>,
    pub content_after: Vec<Rat>,
    pub operator_residual: Vec<Rat>,
    pub total_right_hand: Rat,
    pub total_content_after: Rat,
    /// Exact receiver-relative gain or departure. Reaction and nonconservative
    /// extensions may make this nonzero.
    pub net_exchange: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportPredictionGradeObstruction {
    pub schema: String,
    pub event: EventId,
    pub interval: Rat,
    pub predicted_operator: Vec<Vec<Rat>>,
    pub returned_operator: Vec<Vec<Rat>>,
    pub residual: Vec<Vec<Rat>>,
    pub differing_entries: Vec<(usize, usize)>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenerativeTransportCertificate {
    pub schema: String,
    pub initial_interval: Rat,
    pub discrimination_interval: Rat,
    pub prediction_interval: Rat,
    pub model: ParameterizedTransportModel,
    pub predicted_operator: Vec<Vec<Rat>>,
    pub returned_operator: Vec<Vec<Rat>>,
    pub inverse_residual: Vec<Vec<Rat>>,
    pub testimony_events: BTreeSet<EventId>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenerativeTransportPhase {
    AwaitingInitialOperator,
    ResolvingExtension,
    AwaitingPredictionGrade,
    PredictionObstructed,
    Certified,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CompleteOperatorRole {
    InitialGrammar,
    PredictionGrade,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParametricCompleteOperatorTestimony {
    pub event: EventId,
    pub receiver: TransportLineageId,
    pub role: CompleteOperatorRole,
    pub interval: Rat,
    pub responses: Vec<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParametricTransportTestimony {
    pub event: EventId,
    pub receiver: TransportLineageId,
    pub query: ParameterizedTransportQuery,
    pub response: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenerativeTransportHistoryEntry {
    CompleteOperator(ParametricCompleteOperatorTestimony),
    Observation(ParametricTransportTestimony),
}

impl GenerativeTransportHistoryEntry {
    fn event(&self) -> EventId {
        match self {
            Self::CompleteOperator(testimony) => testimony.event,
            Self::Observation(testimony) => testimony.event,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenerativeTransportStanding {
    pub schema: String,
    pub extent: u32,
    pub initial_interval: Rat,
    pub discrimination_interval: Rat,
    pub prediction_interval: Rat,
    pub phase: GenerativeTransportPhase,
    history: Vec<GenerativeTransportHistoryEntry>,
    used_events: BTreeSet<EventId>,
    obstruction: Option<TransportModelObstruction>,
    family: Option<ParameterizedTransportFamily>,
    next_query: Option<ParameterizedTransportQuery>,
    generated_model: Option<ParameterizedTransportModel>,
    prediction_obstruction: Option<TransportPredictionGradeObstruction>,
    certificate: Option<GenerativeTransportCertificate>,
}

impl GenerativeTransportStanding {
    pub fn new(extent: u32, initial_interval: Rat) -> Result<Self, GenerativeTransportError> {
        validate_extent(extent)?;
        if !initial_interval.is_positive() {
            return Err(GenerativeTransportError::NonpositiveInterval);
        }
        let discrimination_interval = &initial_interval + Rat::one();
        let prediction_interval = &discrimination_interval + Rat::one();
        let standing = Self {
            schema: "holonic-engine.generative-transport-standing.v1".to_owned(),
            extent,
            initial_interval,
            discrimination_interval,
            prediction_interval,
            phase: GenerativeTransportPhase::AwaitingInitialOperator,
            history: Vec::new(),
            used_events: BTreeSet::new(),
            obstruction: None,
            family: None,
            next_query: None,
            generated_model: None,
            prediction_obstruction: None,
            certificate: None,
        };
        standing.validate_incremental()?;
        Ok(standing)
    }

    pub fn history(&self) -> &[GenerativeTransportHistoryEntry] {
        &self.history
    }

    pub fn obstruction(&self) -> Option<&TransportModelObstruction> {
        self.obstruction.as_ref()
    }

    pub fn family(&self) -> Option<&ParameterizedTransportFamily> {
        self.family.as_ref()
    }

    pub fn next_query(&self) -> Option<&ParameterizedTransportQuery> {
        self.next_query.as_ref()
    }

    pub fn generated_model(&self) -> Option<&ParameterizedTransportModel> {
        self.generated_model.as_ref()
    }

    pub fn prediction_obstruction(&self) -> Option<&TransportPredictionGradeObstruction> {
        self.prediction_obstruction.as_ref()
    }

    pub fn certificate(&self) -> Option<&GenerativeTransportCertificate> {
        self.certificate.as_ref()
    }

    pub fn requested_complete_operator_interval(&self) -> Option<&Rat> {
        match self.phase {
            GenerativeTransportPhase::AwaitingInitialOperator => Some(&self.initial_interval),
            GenerativeTransportPhase::AwaitingPredictionGrade => Some(&self.prediction_interval),
            GenerativeTransportPhase::ResolvingExtension
            | GenerativeTransportPhase::PredictionObstructed
            | GenerativeTransportPhase::Certified => None,
        }
    }

    pub fn predict(
        &self,
        query: &ParameterizedTransportQuery,
    ) -> Result<ParameterizedTransportPrediction, GenerativeTransportError> {
        if let Some(family) = &self.family {
            return family.predict(query);
        }
        let Some(model) = &self.generated_model else {
            return Err(GenerativeTransportError::PredictionFamilyAbsent);
        };
        let value = model.clamped_response(query)?;
        Ok(ParameterizedTransportPrediction {
            schema: "holonic-engine.parameterized-transport-prediction.v1".to_owned(),
            query: query.clone(),
            affine: ExactAffinePrediction {
                schema: "holonic-engine.exact-affine-prediction.v1".to_owned(),
                constant: value,
                residual_coefficients: Vec::new(),
                free_coordinates: Vec::new(),
            },
            unresolved_variables: Vec::new(),
        })
    }

    pub fn validate(&self) -> Result<(), GenerativeTransportError> {
        self.validate_incremental()?;
        self.validate_complete_replay()
    }

    fn validate_incremental(&self) -> Result<(), GenerativeTransportError> {
        let extent = validate_extent(self.extent)?;
        if self.schema != "holonic-engine.generative-transport-standing.v1"
            || self.discrimination_interval != &self.initial_interval + Rat::one()
            || self.prediction_interval != &self.discrimination_interval + Rat::one()
        {
            return Err(GenerativeTransportError::MalformedStanding);
        }
        let history_events = self
            .history
            .iter()
            .map(GenerativeTransportHistoryEntry::event)
            .collect::<BTreeSet<_>>();
        if history_events.len() != self.history.len() || history_events != self.used_events {
            return Err(GenerativeTransportError::MalformedStanding);
        }
        if let Some(family) = &self.family {
            family.validate()?;
        }
        if let Some(query) = &self.next_query {
            query.validate(extent)?;
        }
        if let Some(model) = &self.generated_model {
            model.validate()?;
        }
        match self.phase {
            GenerativeTransportPhase::AwaitingInitialOperator => {
                if !self.history.is_empty()
                    || self.obstruction.is_some()
                    || self.family.is_some()
                    || self.next_query.is_some()
                    || self.generated_model.is_some()
                    || self.prediction_obstruction.is_some()
                    || self.certificate.is_some()
                {
                    return Err(GenerativeTransportError::MalformedStanding);
                }
            }
            GenerativeTransportPhase::ResolvingExtension => {
                let family = self
                    .family
                    .as_ref()
                    .ok_or(GenerativeTransportError::MalformedStanding)?;
                if self.obstruction.is_none()
                    || family.affine_dimension() == 0
                    || self.generated_model.is_some()
                    || self.prediction_obstruction.is_some()
                    || self.certificate.is_some()
                {
                    return Err(GenerativeTransportError::MalformedStanding);
                }
                let expected =
                    select_parameter_query(extent, &self.discrimination_interval, family)?.0;
                if self.next_query != expected || self.next_query.is_none() {
                    return Err(GenerativeTransportError::MalformedStanding);
                }
            }
            GenerativeTransportPhase::AwaitingPredictionGrade => {
                if self.generated_model.is_none()
                    || self.next_query.is_some()
                    || self.prediction_obstruction.is_some()
                    || self.certificate.is_some()
                {
                    return Err(GenerativeTransportError::MalformedStanding);
                }
            }
            GenerativeTransportPhase::PredictionObstructed => {
                if self.generated_model.is_none()
                    || self.prediction_obstruction.is_none()
                    || self.next_query.is_some()
                    || self.certificate.is_some()
                {
                    return Err(GenerativeTransportError::MalformedStanding);
                }
            }
            GenerativeTransportPhase::Certified => {
                if self.generated_model.is_none()
                    || self.certificate.is_none()
                    || self.next_query.is_some()
                    || self.prediction_obstruction.is_some()
                {
                    return Err(GenerativeTransportError::MalformedStanding);
                }
            }
        }
        Ok(())
    }

    fn validate_complete_replay(&self) -> Result<(), GenerativeTransportError> {
        let law = GenerativeTransportLaw::new(self.extent, self.initial_interval.clone())?;
        let mut replayed = Self::new(self.extent, self.initial_interval.clone())?;
        for entry in &self.history {
            let event = match entry {
                GenerativeTransportHistoryEntry::CompleteOperator(testimony) => {
                    GenerativeTransportEvent::ReturnCompleteOperator {
                        event: testimony.event,
                        receiver: testimony.receiver,
                        interval: testimony.interval.clone(),
                        responses: testimony.responses.clone(),
                    }
                }
                GenerativeTransportHistoryEntry::Observation(testimony) => {
                    GenerativeTransportEvent::ReturnObservation {
                        event: testimony.event,
                        receiver: testimony.receiver,
                        query: testimony.query.clone(),
                        response: testimony.response.clone(),
                    }
                }
            };
            replayed = law.enact(&replayed, &event)?.standing_after;
        }
        if replayed != *self {
            return Err(GenerativeTransportError::MalformedStanding);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenerativeTransportEvent {
    ReturnCompleteOperator {
        event: EventId,
        receiver: TransportLineageId,
        interval: Rat,
        responses: Vec<Rat>,
    },
    ReturnObservation {
        event: EventId,
        receiver: TransportLineageId,
        query: ParameterizedTransportQuery,
        response: Rat,
    },
}

impl GenerativeTransportEvent {
    fn event(&self) -> EventId {
        match self {
            Self::ReturnCompleteOperator { event, .. } | Self::ReturnObservation { event, .. } => {
                *event
            }
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenerativeTransportWork {
    pub exact_row_eliminations: u64,
    pub inspected_operator_coordinates: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenerativeTransportRadiation {
    pub schema: String,
    pub event: EventId,
    pub phase_after: GenerativeTransportPhase,
    pub obstruction: Option<TransportModelObstruction>,
    pub prediction_obstruction: Option<TransportPredictionGradeObstruction>,
    pub affine_dimension_after: Option<u64>,
    pub next_query: Option<ParameterizedTransportQuery>,
    pub generated_model: Option<ParameterizedTransportModel>,
    pub certificate: Option<GenerativeTransportCertificate>,
    pub work: GenerativeTransportWork,
}

#[derive(Clone, Debug)]
pub struct GenerativeTransportLaw {
    extent: u32,
    initial_interval: Rat,
}

impl GenerativeTransportLaw {
    pub fn new(extent: u32, initial_interval: Rat) -> Result<Self, GenerativeTransportError> {
        validate_extent(extent)?;
        if !initial_interval.is_positive() {
            return Err(GenerativeTransportError::NonpositiveInterval);
        }
        Ok(Self {
            extent,
            initial_interval,
        })
    }
}

impl ExactEventLaw for GenerativeTransportLaw {
    type Standing = GenerativeTransportStanding;
    type Event = GenerativeTransportEvent;
    type Radiation = GenerativeTransportRadiation;
    type Error = GenerativeTransportError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate_incremental()?;
        if standing_before.extent != self.extent
            || standing_before.initial_interval != self.initial_interval
        {
            return Err(GenerativeTransportError::LawStandingMismatch);
        }
        if matches!(
            standing_before.phase,
            GenerativeTransportPhase::Certified | GenerativeTransportPhase::PredictionObstructed
        ) {
            return Err(GenerativeTransportError::TerminalStanding);
        }
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(GenerativeTransportError::RepeatedEvent(event_id));
        }

        let extent =
            usize::try_from(self.extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?;
        let mut standing_after = standing_before.clone();
        let mut work = GenerativeTransportWork::default();

        match event {
            GenerativeTransportEvent::ReturnCompleteOperator {
                event,
                receiver,
                interval,
                responses,
            } => match standing_before.phase {
                GenerativeTransportPhase::AwaitingInitialOperator => {
                    if interval != &standing_before.initial_interval {
                        return Err(GenerativeTransportError::UnexpectedCompleteInterval {
                            expected: Box::new(standing_before.initial_interval.clone()),
                            received: Box::new(interval.clone()),
                        });
                    }
                    let operator = operator_from_responses(extent, responses)?;
                    let testimony = ParametricCompleteOperatorTestimony {
                        event: *event,
                        receiver: *receiver,
                        role: CompleteOperatorRole::InitialGrammar,
                        interval: interval.clone(),
                        responses: responses.clone(),
                    };
                    standing_after
                        .history
                        .push(GenerativeTransportHistoryEntry::CompleteOperator(testimony));
                    if is_unit_passive_operator(&operator, interval)? {
                        let model =
                            model_from_unit_passive_operator(self.extent, interval, &operator)?;
                        standing_after.generated_model = Some(model);
                        standing_after.phase = GenerativeTransportPhase::AwaitingPredictionGrade;
                    } else {
                        let obstruction = derive_base_obstruction(*event, interval, &operator)?;
                        let mut family = ParameterizedTransportFamily::new(self.extent)?;
                        for (row, responses) in operator.iter().enumerate() {
                            for (column, response) in responses.iter().enumerate() {
                                let query = ParameterizedTransportQuery::basis(
                                    extent,
                                    interval.clone(),
                                    row,
                                    column,
                                )?;
                                let admission = family.admit(&query, response.clone())?;
                                work.exact_row_eliminations = work
                                    .exact_row_eliminations
                                    .checked_add(admission.exact_row_eliminations)
                                    .ok_or(GenerativeTransportError::CarrierOverflow)?;
                            }
                        }
                        let (next_query, inspected) = select_parameter_query(
                            extent,
                            &standing_before.discrimination_interval,
                            &family,
                        )?;
                        standing_after.obstruction = Some(obstruction);
                        standing_after.family = Some(family);
                        standing_after.next_query = next_query;
                        standing_after.phase = GenerativeTransportPhase::ResolvingExtension;
                        work.inspected_operator_coordinates = inspected;
                    }
                }
                GenerativeTransportPhase::AwaitingPredictionGrade => {
                    if interval != &standing_before.prediction_interval {
                        return Err(GenerativeTransportError::UnexpectedCompleteInterval {
                            expected: Box::new(standing_before.prediction_interval.clone()),
                            received: Box::new(interval.clone()),
                        });
                    }
                    let returned_operator = operator_from_responses(extent, responses)?;
                    let model = standing_before
                        .generated_model
                        .as_ref()
                        .ok_or(GenerativeTransportError::MalformedStanding)?;
                    let predicted_operator = model.event_operator(interval)?;
                    let residual = matrix_subtract(&returned_operator, &predicted_operator)?;
                    let differing_entries = residual
                        .iter()
                        .enumerate()
                        .flat_map(|(row, values)| {
                            values
                                .iter()
                                .enumerate()
                                .filter_map(move |(column, value)| {
                                    (!value.is_zero()).then_some((row, column))
                                })
                        })
                        .collect::<Vec<_>>();
                    let testimony = ParametricCompleteOperatorTestimony {
                        event: *event,
                        receiver: *receiver,
                        role: CompleteOperatorRole::PredictionGrade,
                        interval: interval.clone(),
                        responses: responses.clone(),
                    };
                    standing_after
                        .history
                        .push(GenerativeTransportHistoryEntry::CompleteOperator(testimony));
                    if differing_entries.is_empty() {
                        let inverse = invert_exact(predicted_operator.clone())?;
                        let inverse_residual = matrix_subtract(
                            &matrix_multiply(&inverse, &predicted_operator)?,
                            &identity_matrix(extent)?,
                        )?;
                        if inverse_residual
                            .iter()
                            .flatten()
                            .any(|value| !value.is_zero())
                        {
                            return Err(GenerativeTransportError::InverseResidualNonzero);
                        }
                        standing_after.certificate = Some(GenerativeTransportCertificate {
                            schema: "holonic-engine.generative-transport-certificate.v1".to_owned(),
                            initial_interval: standing_before.initial_interval.clone(),
                            discrimination_interval: standing_before
                                .discrimination_interval
                                .clone(),
                            prediction_interval: standing_before.prediction_interval.clone(),
                            model: model.clone(),
                            predicted_operator,
                            returned_operator,
                            inverse_residual,
                            testimony_events: standing_after
                                .history
                                .iter()
                                .map(GenerativeTransportHistoryEntry::event)
                                .collect(),
                        });
                        standing_after.phase = GenerativeTransportPhase::Certified;
                    } else {
                        standing_after.prediction_obstruction =
                            Some(TransportPredictionGradeObstruction {
                                schema: "holonic-engine.transport-prediction-grade-obstruction.v1"
                                    .to_owned(),
                                event: *event,
                                interval: interval.clone(),
                                predicted_operator,
                                returned_operator,
                                residual,
                                differing_entries,
                            });
                        standing_after.phase = GenerativeTransportPhase::PredictionObstructed;
                    }
                }
                GenerativeTransportPhase::ResolvingExtension
                | GenerativeTransportPhase::PredictionObstructed
                | GenerativeTransportPhase::Certified => {
                    return Err(GenerativeTransportError::CompleteOperatorNotRequested);
                }
            },
            GenerativeTransportEvent::ReturnObservation {
                event,
                receiver,
                query,
                response,
            } => {
                if standing_before.phase != GenerativeTransportPhase::ResolvingExtension {
                    return Err(GenerativeTransportError::ObservationNotRequested);
                }
                if standing_before.next_query.as_ref() != Some(query) {
                    return Err(GenerativeTransportError::UnexpectedReturnedQuery {
                        expected: Box::new(standing_before.next_query.clone()),
                        received: Box::new(query.clone()),
                    });
                }
                let family = standing_after
                    .family
                    .as_mut()
                    .ok_or(GenerativeTransportError::MalformedStanding)?;
                let admission = family.admit(query, response.clone())?;
                work.exact_row_eliminations = admission.exact_row_eliminations;
                standing_after
                    .history
                    .push(GenerativeTransportHistoryEntry::Observation(
                        ParametricTransportTestimony {
                            event: *event,
                            receiver: *receiver,
                            query: query.clone(),
                            response: response.clone(),
                        },
                    ));
                if let Some(model) = family.unique_model()? {
                    standing_after.generated_model = Some(model);
                    standing_after.next_query = None;
                    standing_after.phase = GenerativeTransportPhase::AwaitingPredictionGrade;
                } else {
                    let (next_query, inspected) = select_parameter_query(
                        extent,
                        &standing_before.discrimination_interval,
                        family,
                    )?;
                    standing_after.next_query = next_query;
                    work.inspected_operator_coordinates = inspected;
                }
            }
        }

        standing_after.used_events.insert(event_id);
        standing_after.validate_incremental()?;
        let radiation = GenerativeTransportRadiation {
            schema: "holonic-engine.generative-transport-radiation.v1".to_owned(),
            event: event_id,
            phase_after: standing_after.phase,
            obstruction: standing_after.obstruction.clone(),
            prediction_obstruction: standing_after.prediction_obstruction.clone(),
            affine_dimension_after: standing_after
                .family
                .as_ref()
                .map(ParameterizedTransportFamily::affine_dimension)
                .map(u64::try_from)
                .transpose()
                .map_err(|_| GenerativeTransportError::CarrierOverflow)?,
            next_query: standing_after.next_query.clone(),
            generated_model: standing_after.generated_model.clone(),
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

fn parameterized_variables(
    extent: u32,
) -> Result<Vec<ParameterizedTransportVariable>, GenerativeTransportError> {
    validate_extent(extent)?;
    let mut variables = (0..extent)
        .map(ParameterizedTransportVariable::ReceiverCapacity)
        .collect::<Vec<_>>();
    let edges = canonical_edges(extent)?;
    variables.extend(
        edges
            .iter()
            .copied()
            .map(ParameterizedTransportVariable::SymmetricPair),
    );
    variables.extend(
        edges
            .iter()
            .copied()
            .map(ParameterizedTransportVariable::SkewPair),
    );
    variables.extend((0..extent).map(ParameterizedTransportVariable::Reaction));
    Ok(variables)
}

fn parameterized_coefficients(
    variables: &[ParameterizedTransportVariable],
    query: &ParameterizedTransportQuery,
) -> Result<Vec<Rat>, GenerativeTransportError> {
    variables
        .iter()
        .map(|variable| match variable {
            ParameterizedTransportVariable::ReceiverCapacity(node) => {
                let node = usize::try_from(*node)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                Ok(&query.receiver[node] * &query.imposed_potential[node])
            }
            ParameterizedTransportVariable::SymmetricPair(edge) => {
                let left = usize::try_from(edge.left)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                let right = usize::try_from(edge.right)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                Ok(&query.interval
                    * (&query.receiver[left] - &query.receiver[right])
                    * (&query.imposed_potential[left] - &query.imposed_potential[right]))
            }
            ParameterizedTransportVariable::SkewPair(edge) => {
                let left = usize::try_from(edge.left)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                let right = usize::try_from(edge.right)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                Ok(&query.interval
                    * (&query.receiver[left] * &query.imposed_potential[right]
                        - &query.receiver[right] * &query.imposed_potential[left]))
            }
            ParameterizedTransportVariable::Reaction(node) => {
                let node = usize::try_from(*node)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                Ok(&query.interval * &query.receiver[node] * &query.imposed_potential[node])
            }
        })
        .collect()
}

fn select_parameter_query(
    extent: usize,
    interval: &Rat,
    family: &ParameterizedTransportFamily,
) -> Result<(Option<ParameterizedTransportQuery>, u64), GenerativeTransportError> {
    let mut inspected = 0_u64;
    for row in 0..extent {
        for column in 0..extent {
            inspected = inspected
                .checked_add(1)
                .ok_or(GenerativeTransportError::CarrierOverflow)?;
            let query = ParameterizedTransportQuery::basis(extent, interval.clone(), row, column)?;
            if !family.predict(&query)?.is_determined() {
                return Ok((Some(query), inspected));
            }
        }
    }
    Ok((None, inspected))
}

fn is_unit_passive_operator(
    operator: &[Vec<Rat>],
    interval: &Rat,
) -> Result<bool, GenerativeTransportError> {
    if !interval.is_positive() {
        return Err(GenerativeTransportError::NonpositiveInterval);
    }
    validate_square(operator)?;
    for (row, values) in operator.iter().enumerate() {
        for (column, value) in values.iter().enumerate() {
            if value != &operator[column][row] {
                return Ok(false);
            }
            if row != column && value.is_positive() {
                return Ok(false);
            }
        }
        if sum(values) != Rat::one() {
            return Ok(false);
        }
    }
    Ok(true)
}

fn model_from_unit_passive_operator(
    extent: u32,
    interval: &Rat,
    operator: &[Vec<Rat>],
) -> Result<ParameterizedTransportModel, GenerativeTransportError> {
    let extent_usize = validate_square(operator)?;
    if extent_usize
        != usize::try_from(extent).map_err(|_| GenerativeTransportError::CarrierOverflow)?
        || !is_unit_passive_operator(operator, interval)?
    {
        return Err(GenerativeTransportError::MalformedGeneratedModel);
    }
    let variables = parameterized_variables(extent)?;
    let edges = canonical_edges(extent)?;
    let mut solution = vec![Rat::zero(); variables.len()];
    for (ordinal, variable) in variables.iter().enumerate() {
        solution[ordinal] = match variable {
            ParameterizedTransportVariable::ReceiverCapacity(_) => Rat::one(),
            ParameterizedTransportVariable::SymmetricPair(edge) => {
                let left = usize::try_from(edge.left)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                let right = usize::try_from(edge.right)
                    .map_err(|_| GenerativeTransportError::CarrierOverflow)?;
                -&operator[left][right] / interval
            }
            ParameterizedTransportVariable::SkewPair(_)
            | ParameterizedTransportVariable::Reaction(_) => Rat::zero(),
        };
    }
    debug_assert_eq!(edges.len(), extent_usize * (extent_usize - 1) / 2);
    ParameterizedTransportModel::from_solution(extent, &variables, &solution)
}

fn derive_base_obstruction(
    event: EventId,
    interval: &Rat,
    operator: &[Vec<Rat>],
) -> Result<TransportModelObstruction, GenerativeTransportError> {
    validate_square(operator)?;
    let transpose = transpose(operator)?;
    let symmetry_residual = matrix_subtract(operator, &transpose)?;
    let unit_row_residual = operator
        .iter()
        .map(|row| sum(row) - Rat::one())
        .collect::<Vec<_>>();
    let mut extension_needs = BTreeSet::new();
    if symmetry_residual
        .iter()
        .flatten()
        .any(|value| !value.is_zero())
    {
        extension_needs.insert(TransportExtensionNeed::SkewPairTransport);
    }
    if unit_row_residual.iter().any(|value| !value.is_zero()) {
        extension_needs.insert(TransportExtensionNeed::DiagonalStandingOrReaction);
    }
    for (row, values) in operator.iter().enumerate() {
        for (column, other_values) in operator.iter().enumerate().skip(row + 1) {
            let symmetric = (&values[column] + &other_values[row]) / Rat::from_integer(2.into());
            if symmetric.is_positive() {
                extension_needs.insert(TransportExtensionNeed::ActiveSymmetricTransport);
            }
        }
    }
    Ok(TransportModelObstruction {
        schema: "holonic-engine.transport-model-obstruction.v1".to_owned(),
        event,
        interval: interval.clone(),
        returned_operator: operator.to_vec(),
        symmetry_residual,
        unit_row_residual,
        extension_needs,
    })
}

fn operator_from_responses(
    extent: usize,
    responses: &[Rat],
) -> Result<Vec<Vec<Rat>>, GenerativeTransportError> {
    let expected = extent
        .checked_mul(extent)
        .ok_or(GenerativeTransportError::CarrierOverflow)?;
    if responses.len() != expected {
        return Err(GenerativeTransportError::MalformedCompleteOperator {
            expected,
            supplied: responses.len(),
        });
    }
    Ok(responses
        .chunks_exact(extent)
        .map(<[Rat]>::to_vec)
        .collect())
}

fn canonical_edges(extent: u32) -> Result<Vec<PotentialTransportEdge>, GenerativeTransportError> {
    validate_extent(extent)?;
    let mut edges = Vec::new();
    for left in 0..extent {
        for right in (left + 1)..extent {
            edges.push(PotentialTransportEdge { left, right });
        }
    }
    Ok(edges)
}

fn edge_ordinal(
    extent: u32,
    edge: PotentialTransportEdge,
) -> Result<usize, GenerativeTransportError> {
    canonical_edges(extent)?
        .iter()
        .position(|present| *present == edge)
        .ok_or(GenerativeTransportError::MalformedGeneratedEdge(edge))
}

fn validate_extent(extent: u32) -> Result<usize, GenerativeTransportError> {
    if extent < 2 {
        return Err(GenerativeTransportError::InvalidExtent(extent));
    }
    usize::try_from(extent).map_err(|_| GenerativeTransportError::CarrierOverflow)
}

fn validate_square(matrix: &[Vec<Rat>]) -> Result<usize, GenerativeTransportError> {
    let extent = matrix.len();
    if extent < 2 || matrix.iter().any(|row| row.len() != extent) {
        return Err(GenerativeTransportError::MalformedMatrix);
    }
    Ok(extent)
}

fn zero_matrix(rows: usize, columns: usize) -> Vec<Vec<Rat>> {
    vec![vec![Rat::zero(); columns]; rows]
}

/// Every refusal the shared exact carrier raises, named in this module's own vocabulary.
impl From<ExactLinearError> for GenerativeTransportError {
    fn from(error: ExactLinearError) -> Self {
        match error {
            ExactLinearError::SingularMatrix => {
                GenerativeTransportError::SingularGeneratedOperator
            }
            ExactLinearError::InverseCertificateFailure => {
                GenerativeTransportError::InverseResidualNonzero
            }
            ExactLinearError::ExtentOverflow => GenerativeTransportError::CarrierOverflow,
            ExactLinearError::RaggedMatrix
            | ExactLinearError::NonsquareMatrix
            | ExactLinearError::AddressOutside
            | ExactLinearError::ShapeMismatch => GenerativeTransportError::MalformedMatrix,
        }
    }
}

/// Present dense rows to the shared carrier against a **declared** column count, because a
/// matrix with no rows carries none of its own.
fn carrier(
    matrix: &[Vec<Rat>],
    columns: usize,
) -> Result<ExactRatMatrix, GenerativeTransportError> {
    Ok(ExactRatMatrix::shaped(
        matrix.len(),
        columns,
        matrix.to_vec(),
    )?)
}

fn identity_matrix(extent: usize) -> Result<Vec<Vec<Rat>>, GenerativeTransportError> {
    Ok(ExactRatMatrix::identity(extent)?.to_rows())
}

fn transpose(matrix: &[Vec<Rat>]) -> Result<Vec<Vec<Rat>>, GenerativeTransportError> {
    let extent = validate_square(matrix)?;
    Ok(carrier(matrix, extent)?.transpose()?.to_rows())
}

fn matrix_vector(
    matrix: &[Vec<Rat>],
    vector: &[Rat],
) -> Result<Vec<Rat>, GenerativeTransportError> {
    Ok(carrier(matrix, vector.len())?.apply(vector)?)
}

fn matrix_multiply(
    left: &[Vec<Rat>],
    right: &[Vec<Rat>],
) -> Result<Vec<Vec<Rat>>, GenerativeTransportError> {
    let inner = right.len();
    let columns = right.first().map_or(0, Vec::len);
    Ok(carrier(left, inner)?
        .multiply(&carrier(right, columns)?)?
        .to_rows())
}

fn matrix_subtract(
    left: &[Vec<Rat>],
    right: &[Vec<Rat>],
) -> Result<Vec<Vec<Rat>>, GenerativeTransportError> {
    let columns = left.first().or_else(|| right.first()).map_or(0, Vec::len);
    Ok(carrier(left, columns)?
        .subtract(&carrier(right, columns)?)?
        .to_rows())
}

fn vector_subtract(left: &[Rat], right: &[Rat]) -> Result<Vec<Rat>, GenerativeTransportError> {
    if left.len() != right.len() {
        return Err(GenerativeTransportError::VectorDimension {
            left: left.len(),
            right: right.len(),
        });
    }
    Ok(left
        .iter()
        .zip(right)
        .map(|(left, right)| left - right)
        .collect())
}

/// The exact inverse, **with the shared carrier's multiplication certificate in force**.
///
/// This was 33 lines of private Gauss-Jordan differing from `inverse_transport`'s by
/// one line, and it left the verification to its caller — which in `propagate` was a single
/// solve residual rather than the identity. The rationals are the same.
fn invert_exact(matrix: Vec<Vec<Rat>>) -> Result<Vec<Vec<Rat>>, GenerativeTransportError> {
    let extent = validate_square(&matrix)?;
    Ok(carrier(&matrix, extent)?.inverse()?.to_rows())
}

fn dot(left: &[Rat], right: &[Rat]) -> Result<Rat, GenerativeTransportError> {
    if left.len() != right.len() {
        return Err(GenerativeTransportError::VectorDimension {
            left: left.len(),
            right: right.len(),
        });
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Rat::zero(), |sum, (left, right)| sum + left * right))
}

fn sum(values: &[Rat]) -> Rat {
    values.iter().fold(Rat::zero(), |sum, value| sum + value)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum GenerativeTransportError {
    #[error("a generative transport ecology requires at least two nodes, received {0}")]
    InvalidExtent(u32),
    #[error("a generative transport event interval must be positive")]
    NonpositiveInterval,
    #[error(
        "parameterized query expected {expected} coordinates, received {potentials} potentials and {receiver} receiver coordinates"
    )]
    QueryDimension {
        expected: usize,
        potentials: usize,
        receiver: usize,
    },
    #[error("a parameterized query requires a nonzero potential")]
    ZeroPotentialQuery,
    #[error("a parameterized query requires a nonzero receiver")]
    ZeroReceiverQuery,
    #[error("operator coordinate ({row},{column}) is outside extent {extent}")]
    OperatorCoordinateOutOfRange {
        row: usize,
        column: usize,
        extent: usize,
    },
    #[error("the parameterized transport family is malformed")]
    MalformedFamily,
    #[error("generated transport edge {0:?} is malformed")]
    MalformedGeneratedEdge(PotentialTransportEdge),
    #[error("the generated transport model is malformed")]
    MalformedGeneratedModel,
    #[error("generated receiver capacity at node {node} is not positive")]
    NonpositiveGeneratedCapacity { node: usize },
    #[error("prediction is unavailable before a model family has been caused")]
    PredictionFamilyAbsent,
    #[error("generated propagation expected {expected} values, received {supplied}")]
    PropagationDimension { expected: usize, supplied: usize },
    #[error("the generated propagation operator residual is nonzero")]
    OperatorResidualNonzero,
    #[error("generative transport law and standing disagree")]
    LawStandingMismatch,
    #[error("generative transport occurrence {0:?} was already used")]
    RepeatedEvent(EventId),
    #[error("the generative transport standing is terminal")]
    TerminalStanding,
    #[error("complete operator interval {received} does not match requested interval {expected}")]
    UnexpectedCompleteInterval {
        expected: Box<Rat>,
        received: Box<Rat>,
    },
    #[error("complete operator was not requested in the contemporary phase")]
    CompleteOperatorNotRequested,
    #[error("a generated observation was not requested in the contemporary phase")]
    ObservationNotRequested,
    #[error("returned generated query {received:?} does not match production query {expected:?}")]
    UnexpectedReturnedQuery {
        expected: Box<Option<ParameterizedTransportQuery>>,
        received: Box<ParameterizedTransportQuery>,
    },
    #[error("complete operator has {supplied} entries, expected {expected}")]
    MalformedCompleteOperator { expected: usize, supplied: usize },
    #[error("an exact generated transport matrix is malformed")]
    MalformedMatrix,
    #[error("generated transport vectors disagree: {left} and {right}")]
    VectorDimension { left: usize, right: usize },
    #[error("the generated transport operator is singular")]
    SingularGeneratedOperator,
    #[error("the generated operator inverse residual is nonzero")]
    InverseResidualNonzero,
    #[error("the generative transport standing is malformed")]
    MalformedStanding,
    #[error("a generative transport exact carrier overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    InverseTransport(#[from] InverseTransportError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::integer;

    use super::*;
    use crate::CausalWorld;

    const EXTENT: usize = 4;
    type HiddenEdge = (u32, u32, Rat, Rat);

    fn hidden_parameters() -> (Vec<Rat>, Vec<HiddenEdge>, Vec<Rat>) {
        (
            vec![integer(2), integer(3), integer(1), integer(2)],
            vec![
                (0, 1, integer(2), integer(1)),
                (0, 2, integer(0), integer(-1)),
                (0, 3, integer(1), integer(0)),
                (1, 2, integer(1), integer(1)),
                (1, 3, integer(0), integer(0)),
                (2, 3, integer(3), integer(0)),
            ],
            vec![integer(1), integer(0), integer(2), integer(0)],
        )
    }

    fn hidden_operator(interval: &Rat) -> Vec<Vec<Rat>> {
        let (capacities, edges, reactions) = hidden_parameters();
        let mut generator = zero_matrix(EXTENT, EXTENT);
        for (left, right, symmetric, skew) in edges {
            let left = left as usize;
            let right = right as usize;
            generator[left][left] += &symmetric;
            generator[right][right] += &symmetric;
            generator[left][right] -= &symmetric;
            generator[right][left] -= &symmetric;
            generator[left][right] += &skew;
            generator[right][left] -= &skew;
        }
        for (node, reaction) in reactions.iter().enumerate() {
            generator[node][node] += reaction;
        }
        let mut operator = generator
            .into_iter()
            .map(|row| row.into_iter().map(|value| interval * value).collect())
            .collect::<Vec<Vec<Rat>>>();
        for (node, capacity) in capacities.iter().enumerate() {
            operator[node][node] += capacity;
        }
        operator
    }

    fn flatten(matrix: &[Vec<Rat>]) -> Vec<Rat> {
        matrix.iter().flatten().cloned().collect()
    }

    fn hidden_response(query: &ParameterizedTransportQuery) -> Rat {
        dot(
            &query.receiver,
            &matrix_vector(&hidden_operator(&query.interval), &query.imposed_potential).unwrap(),
        )
        .unwrap()
    }

    fn cause_model(world: &mut CausalWorld<GenerativeTransportLaw>, next_event: &mut u64) {
        world
            .receive(&GenerativeTransportEvent::ReturnCompleteOperator {
                event: EventId(*next_event),
                receiver: TransportLineageId(1),
                interval: integer(1),
                responses: flatten(&hidden_operator(&integer(1))),
            })
            .unwrap();
        *next_event += 1;
        while let Some(query) = world.standing().next_query().cloned() {
            world
                .receive(&GenerativeTransportEvent::ReturnObservation {
                    event: EventId(*next_event),
                    receiver: TransportLineageId(1),
                    response: hidden_response(&query),
                    query,
                })
                .unwrap();
            *next_event += 1;
        }
    }

    #[test]
    fn incomplete_family_predicts_determined_and_open_receiver_sections() {
        let law = GenerativeTransportLaw::new(4, integer(1)).unwrap();
        let standing = GenerativeTransportStanding::new(4, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        world
            .receive(&GenerativeTransportEvent::ReturnCompleteOperator {
                event: EventId(1),
                receiver: TransportLineageId(1),
                interval: integer(1),
                responses: flatten(&hidden_operator(&integer(1))),
            })
            .unwrap();
        assert_eq!(world.standing().family().unwrap().affine_dimension(), 4);
        let off_diagonal = ParameterizedTransportQuery::basis(4, integer(3), 0, 1).unwrap();
        let diagonal = ParameterizedTransportQuery::basis(4, integer(3), 0, 0).unwrap();
        assert!(
            world
                .standing()
                .predict(&off_diagonal)
                .unwrap()
                .is_determined()
        );
        let open = world.standing().predict(&diagonal).unwrap();
        assert!(!open.is_determined());
        assert_eq!(open.unresolved_variables.len(), 1);
    }

    #[test]
    fn obstruction_causes_extension_and_unseen_interval_certifies() {
        let law = GenerativeTransportLaw::new(4, integer(1)).unwrap();
        let standing = GenerativeTransportStanding::new(4, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let mut event = 1;
        cause_model(&mut world, &mut event);
        assert!(world.standing().obstruction().is_some());
        assert_eq!(
            world.standing().phase,
            GenerativeTransportPhase::AwaitingPredictionGrade
        );
        assert_eq!(
            world.standing().generated_model().unwrap().species,
            BTreeSet::from([
                GeneratedTransportSpecies::ReceiverCapacity,
                GeneratedTransportSpecies::PassiveSymmetricTransport,
                GeneratedTransportSpecies::SkewPairTransport,
                GeneratedTransportSpecies::Reaction,
            ])
        );
        world
            .receive(&GenerativeTransportEvent::ReturnCompleteOperator {
                event: EventId(event),
                receiver: TransportLineageId(1),
                interval: integer(3),
                responses: flatten(&hidden_operator(&integer(3))),
            })
            .unwrap();
        world.standing().validate().unwrap();
        assert_eq!(world.standing().phase, GenerativeTransportPhase::Certified);
        assert!(world.standing().certificate().is_some());
    }

    #[test]
    fn prediction_failure_is_retained_as_a_caused_obstruction() {
        let law = GenerativeTransportLaw::new(4, integer(1)).unwrap();
        let standing = GenerativeTransportStanding::new(4, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let mut event = 1;
        cause_model(&mut world, &mut event);
        let mut wrong = flatten(&hidden_operator(&integer(3)));
        wrong[0] += integer(1);
        let receipt = world
            .receive(&GenerativeTransportEvent::ReturnCompleteOperator {
                event: EventId(event),
                receiver: TransportLineageId(1),
                interval: integer(3),
                responses: wrong,
            })
            .unwrap();
        assert_eq!(
            world.standing().phase,
            GenerativeTransportPhase::PredictionObstructed
        );
        assert_eq!(
            world
                .standing()
                .prediction_obstruction()
                .unwrap()
                .differing_entries,
            vec![(0, 0)]
        );
        assert!(receipt.radiation[0].prediction_obstruction.is_some());
        world.standing().validate().unwrap();
    }

    #[test]
    fn returned_discrimination_query_is_production_owned() {
        let law = GenerativeTransportLaw::new(4, integer(1)).unwrap();
        let standing = GenerativeTransportStanding::new(4, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        world
            .receive(&GenerativeTransportEvent::ReturnCompleteOperator {
                event: EventId(1),
                receiver: TransportLineageId(1),
                interval: integer(1),
                responses: flatten(&hidden_operator(&integer(1))),
            })
            .unwrap();
        let before = world.standing().clone();
        let wrong = ParameterizedTransportQuery::basis(4, integer(2), 3, 3).unwrap();
        assert!(matches!(
            world.receive(&GenerativeTransportEvent::ReturnObservation {
                event: EventId(2),
                receiver: TransportLineageId(1),
                query: wrong,
                response: integer(0),
            }),
            Err(GenerativeTransportError::UnexpectedReturnedQuery { .. })
        ));
        assert_eq!(world.standing(), &before);
    }

    #[test]
    fn generated_model_propagates_with_exact_residual() {
        let law = GenerativeTransportLaw::new(4, integer(1)).unwrap();
        let standing = GenerativeTransportStanding::new(4, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let mut event = 1;
        cause_model(&mut world, &mut event);
        let propagation = world
            .standing()
            .generated_model()
            .unwrap()
            .propagate(
                integer(3),
                vec![integer(4), integer(0), integer(0), integer(0)],
            )
            .unwrap();
        assert!(propagation.operator_residual.iter().all(Zero::is_zero));
    }
}
