//! Exact reconstruction of a hidden passive transport ecology.
//!
//! The hidden world is queried through clamped potentials and exact aggregate
//! receiver functionals. For unit node capacities and event interval `tau`,
//! one response is
//!
//! `r^T (I + tau L) phi`
//!
//! where `L` is the unknown weighted graph Laplacian. Expanding `L` over all
//! potential unordered node pairs makes every observation an exact affine
//! constraint on local conductances. The production law retains that complete
//! affine version fiber, chooses unresolved edge queries itself, and admits a
//! passive diffusion topology only after the world returns the complete
//! operator basis.
//!
//! # Where the algebra lives
//!
//! The dense exact algebra is `exact_linear::ExactRatMatrix`. It was this module's own until
//! 2026-08-15, and the 33-line elimination body of its private `invert_exact` differed from
//! `generative_transport`'s by exactly one line — the error variant it named on a singular
//! pivot. Neither function checked the inverse it returned; both callers did, separately. The
//! carrier now checks inside the operation, and its refusals are renamed into this module's own
//! vocabulary below so no foreign error variant reaches a caller.
//!
//! The `inverse_residual` this module computes and retains is untouched. It is not made
//! redundant: it travels in the admission receipt for a later reader, where the carrier refuses
//! at the point of construction.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::{
    CurrentBranchId, CurrentNodeId, DiffusionBranch, DiffusionComplex, DiffusionError,
    DiffusionNode, EventId, EventSuccessor, ExactEventLaw,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct TransportLineageId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct PotentialTransportEdge {
    pub left: u32,
    pub right: u32,
}

impl PotentialTransportEdge {
    fn new(left: u32, right: u32) -> Result<Self, InverseTransportError> {
        if left >= right {
            return Err(InverseTransportError::MalformedPotentialEdge { left, right });
        }
        Ok(Self { left, right })
    }
}

/// One exact black-box experiment.
///
/// `imposed_potential` is a clamped potential section. `receiver` is the
/// exact linear functional through which the required source is returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportQuery {
    pub imposed_potential: Vec<Rat>,
    pub receiver: Vec<Rat>,
}

impl TransportQuery {
    pub fn new(
        imposed_potential: Vec<Rat>,
        receiver: Vec<Rat>,
    ) -> Result<Self, InverseTransportError> {
        let query = Self {
            imposed_potential,
            receiver,
        };
        if query.imposed_potential.len() != query.receiver.len()
            || query.imposed_potential.len() < 2
        {
            return Err(InverseTransportError::MalformedQueryDimension {
                potentials: query.imposed_potential.len(),
                receiver: query.receiver.len(),
            });
        }
        query.validate(query.imposed_potential.len())?;
        Ok(query)
    }

    fn canonical_edge(
        extent: usize,
        edge: PotentialTransportEdge,
    ) -> Result<Self, InverseTransportError> {
        let left =
            usize::try_from(edge.left).map_err(|_| InverseTransportError::CarrierOverflow)?;
        let right =
            usize::try_from(edge.right).map_err(|_| InverseTransportError::CarrierOverflow)?;
        if right >= extent {
            return Err(InverseTransportError::MalformedPotentialEdge {
                left: edge.left,
                right: edge.right,
            });
        }
        let mut imposed_potential = vec![Rat::zero(); extent];
        let mut receiver = vec![Rat::zero(); extent];
        imposed_potential[right] = Rat::one();
        receiver[left] = Rat::one();
        Self::new(imposed_potential, receiver)
    }

    fn validate(&self, extent: usize) -> Result<(), InverseTransportError> {
        if self.imposed_potential.len() != extent || self.receiver.len() != extent {
            return Err(InverseTransportError::MalformedQueryDimension {
                potentials: self.imposed_potential.len(),
                receiver: self.receiver.len(),
            });
        }
        if self.imposed_potential.iter().all(Zero::is_zero) {
            return Err(InverseTransportError::ZeroPotentialQuery);
        }
        if self.receiver.iter().all(Zero::is_zero) {
            return Err(InverseTransportError::ZeroReceiverQuery);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAffineFiberRow {
    pub pivot: usize,
    pub coefficients: Vec<Rat>,
    pub response: Rat,
    /// Which admitted equations, and in what exact combination, produced this
    /// reduced row.
    ///
    /// Keys are admission ordinals; the map is sparse because a reduced row
    /// generally involves few of the equations admitted before it. Reduction
    /// destroys the identity of the rows it consumes, and a refusal that cannot
    /// name its material is the defect this field exists to close: with the
    /// lineage retained, an obstructed admission returns the exact left null
    /// combination that annihilates the operator while leaving the response
    /// standing.
    #[serde(default)]
    pub lineage: BTreeMap<usize, Rat>,
}

/// The exhibited witness of an inconsistent affine system.
///
/// `combination` is a left null vector: weighting the admitted equations by it
/// annihilates every coefficient, so the operator says nothing about it, while
/// the same weighting of the responses returns `response`, which is not zero.
/// That pair is the refusal's material — the contradiction written out rather
/// than asserted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AffineObstruction {
    pub schema: String,
    /// Admission ordinal to its exact weight in the annihilating combination.
    pub combination: BTreeMap<usize, Rat>,
    /// What the same combination of responses returns. Never zero.
    pub response: Rat,
}

impl AffineObstruction {
    /// The equations the witness actually consults, in admission order.
    pub fn admitted_equations(&self) -> Vec<usize> {
        self.combination.keys().copied().collect()
    }
}

/// Canonical reduced-row representation of an exact affine version fiber.
///
/// Every point in the fiber is one complete assignment of the declared local
/// variables. Rows are equalities; unresolved variables remain genuine free
/// coordinates rather than enumerated candidate objects.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAffineVersionFiber {
    pub schema: String,
    variable_count: usize,
    rows: Vec<ExactAffineFiberRow>,
    /// How many equations have been admitted, including the redundant and the
    /// obstructed. This is the address space of every row lineage.
    #[serde(default)]
    admitted: usize,
    /// The witness of the most recent obstructed admission, retained so the
    /// refusal can be read rather than merely detected.
    #[serde(default)]
    obstruction: Option<AffineObstruction>,
}

/// `into -= factor * from`, sparsely, dropping the terms that cancel exactly.
fn combine_lineage(into: &mut BTreeMap<usize, Rat>, from: &BTreeMap<usize, Rat>, factor: &Rat) {
    for (ordinal, weight) in from {
        let combined = into.entry(*ordinal).or_insert_with(Rat::zero);
        *combined -= factor * weight;
        if combined.is_zero() {
            into.remove(ordinal);
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct AffineAdmissionWork {
    pub exact_row_eliminations: u64,
    pub rank_increased: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactAffinePrediction {
    pub schema: String,
    /// The caused part already fixed by the contemporary fiber.
    pub constant: Rat,
    /// Coefficients in the original variable coordinates after every pivot
    /// relation has been eliminated.
    pub residual_coefficients: Vec<Rat>,
    /// Exact unresolved coordinates supporting the residual.
    pub free_coordinates: Vec<usize>,
}

impl ExactAffinePrediction {
    pub fn is_determined(&self) -> bool {
        self.free_coordinates.is_empty()
    }

    pub fn determined_value(&self) -> Option<&Rat> {
        self.is_determined().then_some(&self.constant)
    }
}

impl ExactAffineVersionFiber {
    pub fn new(variable_count: usize) -> Result<Self, InverseTransportError> {
        if variable_count == 0 {
            return Err(InverseTransportError::EmptyAffineFiber);
        }
        Ok(Self {
            schema: "holonic-engine.exact-affine-version-fiber.v1".to_owned(),
            variable_count,
            rows: Vec::new(),
            admitted: 0,
            obstruction: None,
        })
    }

    /// How many equations have been admitted, obstructed ones included.
    pub fn admitted_equations(&self) -> usize {
        self.admitted
    }

    /// The witness of the most recent obstructed admission.
    ///
    /// `AffineFiberObstructed` says only that the system is inconsistent. This
    /// returns the exact left null combination that proves it, so a caller can
    /// report which equations disagree rather than that some do.
    pub fn obstruction(&self) -> Option<&AffineObstruction> {
        self.obstruction.as_ref()
    }

    pub fn variable_count(&self) -> usize {
        self.variable_count
    }

    pub fn rows(&self) -> &[ExactAffineFiberRow] {
        &self.rows
    }

    pub fn rank(&self) -> usize {
        self.rows.len()
    }

    pub fn affine_dimension(&self) -> usize {
        self.variable_count - self.rank()
    }

    pub fn determined_value(
        &self,
        linear_form: &[Rat],
    ) -> Result<Option<Rat>, InverseTransportError> {
        let prediction = self.predict(linear_form, Rat::zero())?;
        Ok(prediction.is_determined().then_some(prediction.constant))
    }

    pub fn predict(
        &self,
        linear_form: &[Rat],
        offset: Rat,
    ) -> Result<ExactAffinePrediction, InverseTransportError> {
        if linear_form.len() != self.variable_count {
            return Err(InverseTransportError::AffineCoordinateDimension {
                expected: self.variable_count,
                supplied: linear_form.len(),
            });
        }
        let mut residual = linear_form.to_vec();
        let mut constant = offset;
        for row in &self.rows {
            let factor = residual[row.pivot].clone();
            if factor.is_zero() {
                continue;
            }
            for (coefficient, row_coefficient) in residual.iter_mut().zip(&row.coefficients) {
                *coefficient -= &factor * row_coefficient;
            }
            constant += factor * &row.response;
        }
        let free_coordinates = residual
            .iter()
            .enumerate()
            .filter_map(|(coordinate, coefficient)| (!coefficient.is_zero()).then_some(coordinate))
            .collect();
        Ok(ExactAffinePrediction {
            schema: "holonic-engine.exact-affine-prediction.v1".to_owned(),
            constant,
            residual_coefficients: residual,
            free_coordinates,
        })
    }

    pub fn coordinate_value(
        &self,
        coordinate: usize,
    ) -> Result<Option<Rat>, InverseTransportError> {
        if coordinate >= self.variable_count {
            return Err(InverseTransportError::AffineCoordinateOutOfRange {
                coordinate,
                variables: self.variable_count,
            });
        }
        let mut form = vec![Rat::zero(); self.variable_count];
        form[coordinate] = Rat::one();
        self.determined_value(&form)
    }

    pub fn unique_solution(&self) -> Result<Option<Vec<Rat>>, InverseTransportError> {
        if self.rank() != self.variable_count {
            return Ok(None);
        }
        let mut solution = vec![Rat::zero(); self.variable_count];
        for row in &self.rows {
            solution[row.pivot] = row.response.clone();
        }
        Ok(Some(solution))
    }

    pub(crate) fn admit(
        &mut self,
        coefficients: Vec<Rat>,
        response: Rat,
    ) -> Result<AffineAdmissionWork, InverseTransportError> {
        if coefficients.len() != self.variable_count {
            return Err(InverseTransportError::AffineCoordinateDimension {
                expected: self.variable_count,
                supplied: coefficients.len(),
            });
        }
        let rank_before = self.rank();
        let mut coefficients = coefficients;
        let mut response = response;
        let mut exact_row_eliminations = 0_u64;

        // The incoming equation begins as itself: one unit of its own ordinal.
        // Every elimination below subtracts the lineage of the row it reduces
        // against, so the combination stays exact through the whole descent.
        let ordinal = self.admitted;
        self.admitted = self
            .admitted
            .checked_add(1)
            .ok_or(InverseTransportError::CarrierOverflow)?;
        let mut lineage: BTreeMap<usize, Rat> = BTreeMap::from([(ordinal, Rat::one())]);

        for row in &self.rows {
            let factor = coefficients[row.pivot].clone();
            if factor.is_zero() {
                continue;
            }
            for (coefficient, row_coefficient) in coefficients.iter_mut().zip(&row.coefficients) {
                *coefficient -= &factor * row_coefficient;
            }
            response -= &factor * &row.response;
            combine_lineage(&mut lineage, &row.lineage, &factor);
            exact_row_eliminations = exact_row_eliminations
                .checked_add(1)
                .ok_or(InverseTransportError::CarrierOverflow)?;
        }

        let Some(pivot) = coefficients.iter().position(|value| !value.is_zero()) else {
            if response.is_zero() {
                return Ok(AffineAdmissionWork {
                    exact_row_eliminations,
                    rank_increased: false,
                });
            }
            // Every coefficient was annihilated and the response was not. The
            // lineage now IS the left null combination, so retain it instead of
            // discarding the one thing that says what the contradiction is.
            self.obstruction = Some(AffineObstruction {
                schema: "holonic-engine.affine-obstruction.v1".to_owned(),
                combination: lineage,
                response,
            });
            return Err(InverseTransportError::AffineFiberObstructed);
        };

        let divisor = coefficients[pivot].clone();
        for coefficient in &mut coefficients[pivot..] {
            *coefficient /= &divisor;
        }
        response /= &divisor;
        for weight in lineage.values_mut() {
            *weight /= &divisor;
        }

        for row in &mut self.rows {
            let factor = row.coefficients[pivot].clone();
            if factor.is_zero() {
                continue;
            }
            for (coefficient, new_coefficient) in row.coefficients.iter_mut().zip(&coefficients) {
                *coefficient -= &factor * new_coefficient;
            }
            row.response -= &factor * &response;
            combine_lineage(&mut row.lineage, &lineage, &factor);
            exact_row_eliminations = exact_row_eliminations
                .checked_add(1)
                .ok_or(InverseTransportError::CarrierOverflow)?;
        }

        let row = ExactAffineFiberRow {
            pivot,
            coefficients,
            response,
            lineage,
        };
        let insertion = self
            .rows
            .binary_search_by_key(&pivot, |present| present.pivot)
            .unwrap_or_else(|place| place);
        self.rows.insert(insertion, row);
        self.validate()?;
        Ok(AffineAdmissionWork {
            exact_row_eliminations,
            rank_increased: self.rank() > rank_before,
        })
    }

    pub(crate) fn validate(&self) -> Result<(), InverseTransportError> {
        if self.schema != "holonic-engine.exact-affine-version-fiber.v1"
            || self.variable_count == 0
            || self.rows.len() > self.variable_count
        {
            return Err(InverseTransportError::MalformedAffineFiber);
        }
        for (ordinal, row) in self.rows.iter().enumerate() {
            if row.coefficients.len() != self.variable_count
                || row.pivot >= self.variable_count
                || row.coefficients[row.pivot] != Rat::one()
                || row.coefficients[..row.pivot]
                    .iter()
                    .any(|value| !value.is_zero())
                || ordinal > 0 && self.rows[ordinal - 1].pivot >= row.pivot
            {
                return Err(InverseTransportError::MalformedAffineFiber);
            }
            for other in &self.rows {
                if other.pivot != row.pivot && !other.coefficients[row.pivot].is_zero() {
                    return Err(InverseTransportError::MalformedAffineFiber);
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TransportTestimonySource {
    ImportedLandmark(TransportLineageId),
    ReturnedReceiver(TransportLineageId),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportTestimony {
    pub event: EventId,
    pub source: TransportTestimonySource,
    pub query: TransportQuery,
    pub response: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompleteTransportOperatorTestimony {
    pub event: EventId,
    pub receiver: TransportLineageId,
    /// Row-major response to every `(receiver basis, potential basis)` pair.
    pub responses: Vec<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InverseTransportHistoryEntry {
    Testimony(TransportTestimony),
    CompleteOperator(CompleteTransportOperatorTestimony),
}

impl InverseTransportHistoryEntry {
    fn event(&self) -> EventId {
        match self {
            Self::Testimony(testimony) => testimony.event,
            Self::CompleteOperator(testimony) => testimony.event,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconstructedTransportEdge {
    pub edge: PotentialTransportEdge,
    pub conductance: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportPropagationReceipt {
    pub schema: String,
    pub source: Vec<Rat>,
    pub content_after: Vec<Rat>,
    pub total_source: Rat,
    pub total_after: Rat,
    pub conservation_residual: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InverseTransportCertificate {
    pub schema: String,
    pub extent: u32,
    pub interval: Rat,
    pub edge_order: Vec<PotentialTransportEdge>,
    pub edge_conductances: Vec<ReconstructedTransportEdge>,
    pub laplacian: Vec<Vec<Rat>>,
    pub event_operator: Vec<Vec<Rat>>,
    pub transfer_operator: Vec<Vec<Rat>>,
    pub inverse_residual: Vec<Vec<Rat>>,
    pub diffusion_complex: DiffusionComplex,
    pub connected_components: u64,
    pub cycle_rank: u64,
    pub affine_rank: u64,
    pub testimony_events: BTreeSet<EventId>,
    pub complete_basis_event: EventId,
}

impl InverseTransportCertificate {
    pub fn clamped_response(&self, query: &TransportQuery) -> Result<Rat, InverseTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| InverseTransportError::CarrierOverflow)?;
        query.validate(extent)?;
        let operated = matrix_vector(&self.event_operator, &query.imposed_potential)?;
        dot(&query.receiver, &operated)
    }

    pub fn propagate_from_zero(
        &self,
        source: Vec<Rat>,
    ) -> Result<TransportPropagationReceipt, InverseTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| InverseTransportError::CarrierOverflow)?;
        if source.len() != extent {
            return Err(InverseTransportError::PropagationDimension {
                expected: extent,
                supplied: source.len(),
            });
        }
        let content_after = matrix_vector(&self.transfer_operator, &source)?;
        let total_source = sum(&source);
        let total_after = sum(&content_after);
        let conservation_residual = &total_after - &total_source;
        if !conservation_residual.is_zero() {
            return Err(InverseTransportError::ReconstructedConservationFailure);
        }
        Ok(TransportPropagationReceipt {
            schema: "holonic-engine.transport-propagation-receipt.v1".to_owned(),
            source,
            content_after,
            total_source,
            total_after,
            conservation_residual,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InverseTransportStanding {
    pub schema: String,
    pub extent: u32,
    pub interval: Rat,
    edge_order: Vec<PotentialTransportEdge>,
    version_fiber: ExactAffineVersionFiber,
    history: Vec<InverseTransportHistoryEntry>,
    used_events: BTreeSet<EventId>,
    next_query: Option<TransportQuery>,
    verification_required: bool,
    certificate: Option<InverseTransportCertificate>,
}

impl InverseTransportStanding {
    pub fn new(extent: u32, interval: Rat) -> Result<Self, InverseTransportError> {
        let extent_usize = validate_extent_and_interval(extent, &interval)?;
        let edge_order = canonical_edges(extent)?;
        let version_fiber = ExactAffineVersionFiber::new(edge_order.len())?;
        let (next_query, _) = select_next_query(extent_usize, &edge_order, &version_fiber)?;
        let standing = Self {
            schema: "holonic-engine.inverse-transport-standing.v1".to_owned(),
            extent,
            interval,
            edge_order,
            version_fiber,
            history: Vec::new(),
            used_events: BTreeSet::new(),
            next_query,
            verification_required: false,
            certificate: None,
        };
        standing.validate_incremental()?;
        Ok(standing)
    }

    pub fn edge_order(&self) -> &[PotentialTransportEdge] {
        &self.edge_order
    }

    pub fn version_fiber(&self) -> &ExactAffineVersionFiber {
        &self.version_fiber
    }

    pub fn history(&self) -> &[InverseTransportHistoryEntry] {
        &self.history
    }

    pub fn next_query(&self) -> Option<&TransportQuery> {
        self.next_query.as_ref()
    }

    pub fn verification_required(&self) -> bool {
        self.verification_required
    }

    pub fn certificate(&self) -> Option<&InverseTransportCertificate> {
        self.certificate.as_ref()
    }

    pub fn predict_clamped(
        &self,
        query: &TransportQuery,
    ) -> Result<ExactAffinePrediction, InverseTransportError> {
        let extent =
            usize::try_from(self.extent).map_err(|_| InverseTransportError::CarrierOverflow)?;
        query.validate(extent)?;
        let baseline = dot(&query.receiver, &query.imposed_potential)?;
        let linear_form = self
            .edge_order
            .iter()
            .map(|edge| {
                let left = usize::try_from(edge.left)
                    .map_err(|_| InverseTransportError::CarrierOverflow)?;
                let right = usize::try_from(edge.right)
                    .map_err(|_| InverseTransportError::CarrierOverflow)?;
                Ok(&self.interval
                    * (&query.receiver[left] - &query.receiver[right])
                    * (&query.imposed_potential[left] - &query.imposed_potential[right]))
            })
            .collect::<Result<Vec<_>, InverseTransportError>>()?;
        self.version_fiber.predict(&linear_form, baseline)
    }

    pub fn is_complete(&self) -> bool {
        self.certificate.is_some()
    }

    pub fn validate(&self) -> Result<(), InverseTransportError> {
        self.validate_incremental()?;
        self.validate_complete_replay()
    }

    fn validate_incremental(&self) -> Result<(), InverseTransportError> {
        let extent = validate_extent_and_interval(self.extent, &self.interval)?;
        if self.schema != "holonic-engine.inverse-transport-standing.v1"
            || self.edge_order != canonical_edges(self.extent)?
            || self.version_fiber.variable_count() != self.edge_order.len()
        {
            return Err(InverseTransportError::MalformedStanding);
        }
        self.version_fiber.validate()?;
        let history_events = self
            .history
            .iter()
            .map(InverseTransportHistoryEntry::event)
            .collect::<BTreeSet<_>>();
        if history_events.len() != self.history.len() || history_events != self.used_events {
            return Err(InverseTransportError::MalformedStanding);
        }
        let complete_entries = self
            .history
            .iter()
            .filter(|entry| matches!(entry, InverseTransportHistoryEntry::CompleteOperator(_)))
            .count();
        if complete_entries > 1
            || complete_entries == 1
                && !matches!(
                    self.history.last(),
                    Some(InverseTransportHistoryEntry::CompleteOperator(_))
                )
        {
            return Err(InverseTransportError::MalformedStanding);
        }
        for entry in &self.history {
            match entry {
                InverseTransportHistoryEntry::Testimony(testimony) => {
                    testimony.query.validate(extent)?;
                }
                InverseTransportHistoryEntry::CompleteOperator(testimony) => {
                    validate_complete_basis(extent, &testimony.responses)?;
                }
            }
        }
        ensure_no_determined_negative_conductance(&self.edge_order, &self.version_fiber)?;
        let expected_query = if self.certificate.is_none() {
            select_next_query(extent, &self.edge_order, &self.version_fiber)?.0
        } else {
            None
        };
        let expected_verification = expected_query.is_none() && self.certificate.is_none();
        if self.next_query != expected_query
            || self.verification_required != expected_verification
            || self.certificate.is_some() != (complete_entries == 1)
        {
            return Err(InverseTransportError::MalformedStanding);
        }
        Ok(())
    }

    fn validate_complete_replay(&self) -> Result<(), InverseTransportError> {
        let law = InverseTransportLaw::new(self.extent, self.interval.clone())?;
        let mut replayed = Self::new(self.extent, self.interval.clone())?;
        for entry in &self.history {
            let event = match entry {
                InverseTransportHistoryEntry::Testimony(testimony) => match testimony.source {
                    TransportTestimonySource::ImportedLandmark(lineage) => {
                        InverseTransportEvent::InheritLandmark {
                            event: testimony.event,
                            lineage,
                            query: testimony.query.clone(),
                            response: testimony.response.clone(),
                        }
                    }
                    TransportTestimonySource::ReturnedReceiver(receiver) => {
                        InverseTransportEvent::ReturnObservation {
                            event: testimony.event,
                            receiver,
                            query: testimony.query.clone(),
                            response: testimony.response.clone(),
                        }
                    }
                },
                InverseTransportHistoryEntry::CompleteOperator(testimony) => {
                    InverseTransportEvent::ReturnCompleteOperator {
                        event: testimony.event,
                        receiver: testimony.receiver,
                        responses: testimony.responses.clone(),
                    }
                }
            };
            replayed = law.enact(&replayed, &event)?.standing_after;
        }
        if replayed != *self {
            return Err(InverseTransportError::MalformedStanding);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum InverseTransportEvent {
    InheritLandmark {
        event: EventId,
        lineage: TransportLineageId,
        query: TransportQuery,
        response: Rat,
    },
    ReturnObservation {
        event: EventId,
        receiver: TransportLineageId,
        query: TransportQuery,
        response: Rat,
    },
    ReturnCompleteOperator {
        event: EventId,
        receiver: TransportLineageId,
        responses: Vec<Rat>,
    },
}

impl InverseTransportEvent {
    fn event(&self) -> EventId {
        match self {
            Self::InheritLandmark { event, .. }
            | Self::ReturnObservation { event, .. }
            | Self::ReturnCompleteOperator { event, .. } => *event,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct InverseTransportWork {
    pub exact_row_eliminations: u64,
    pub inspected_edge_coordinates: u64,
}

impl InverseTransportWork {
    fn add_assign(&mut self, other: &Self) -> Result<(), InverseTransportError> {
        self.exact_row_eliminations = self
            .exact_row_eliminations
            .checked_add(other.exact_row_eliminations)
            .ok_or(InverseTransportError::CarrierOverflow)?;
        self.inspected_edge_coordinates = self
            .inspected_edge_coordinates
            .checked_add(other.inspected_edge_coordinates)
            .ok_or(InverseTransportError::CarrierOverflow)?;
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InverseTransportRadiation {
    pub schema: String,
    pub event: EventId,
    pub received_testimony: Option<TransportTestimony>,
    pub received_complete_operator: Option<CompleteTransportOperatorTestimony>,
    pub affine_rank_before: u64,
    pub affine_rank_after: u64,
    pub affine_dimension_after: u64,
    pub next_query: Option<TransportQuery>,
    pub verification_required: bool,
    pub certificate: Option<InverseTransportCertificate>,
    pub work: InverseTransportWork,
}

#[derive(Clone, Debug)]
pub struct InverseTransportLaw {
    extent: u32,
    interval: Rat,
}

impl InverseTransportLaw {
    pub fn new(extent: u32, interval: Rat) -> Result<Self, InverseTransportError> {
        validate_extent_and_interval(extent, &interval)?;
        Ok(Self { extent, interval })
    }
}

impl ExactEventLaw for InverseTransportLaw {
    type Standing = InverseTransportStanding;
    type Event = InverseTransportEvent;
    type Radiation = InverseTransportRadiation;
    type Error = InverseTransportError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate_incremental()?;
        if standing_before.extent != self.extent || standing_before.interval != self.interval {
            return Err(InverseTransportError::LawStandingMismatch);
        }
        if standing_before.is_complete() {
            return Err(InverseTransportError::EcologyAlreadyCertified);
        }
        let event_id = event.event();
        if standing_before.used_events.contains(&event_id) {
            return Err(InverseTransportError::RepeatedEvent(event_id));
        }

        let extent =
            usize::try_from(self.extent).map_err(|_| InverseTransportError::CarrierOverflow)?;
        let rank_before = standing_before.version_fiber.rank();
        let mut standing_after = standing_before.clone();
        let mut received_testimony = None;
        let mut received_complete_operator = None;
        let mut work = InverseTransportWork::default();

        match event {
            InverseTransportEvent::InheritLandmark {
                event,
                lineage,
                query,
                response,
            } => {
                let testimony = TransportTestimony {
                    event: *event,
                    source: TransportTestimonySource::ImportedLandmark(*lineage),
                    query: query.clone(),
                    response: response.clone(),
                };
                admit_testimony(&mut standing_after, &testimony, &mut work)?;
                received_testimony = Some(testimony);
            }
            InverseTransportEvent::ReturnObservation {
                event,
                receiver,
                query,
                response,
            } => {
                if standing_before.next_query.as_ref() != Some(query) {
                    return Err(InverseTransportError::UnexpectedReturnedQuery {
                        expected: standing_before.next_query.clone(),
                        received: query.clone(),
                    });
                }
                let testimony = TransportTestimony {
                    event: *event,
                    source: TransportTestimonySource::ReturnedReceiver(*receiver),
                    query: query.clone(),
                    response: response.clone(),
                };
                admit_testimony(&mut standing_after, &testimony, &mut work)?;
                received_testimony = Some(testimony);
            }
            InverseTransportEvent::ReturnCompleteOperator {
                event,
                receiver,
                responses,
            } => {
                if !standing_before.verification_required {
                    return Err(InverseTransportError::CompleteOperatorNotRequested);
                }
                validate_complete_basis(extent, responses)?;
                let testimony = CompleteTransportOperatorTestimony {
                    event: *event,
                    receiver: *receiver,
                    responses: responses.clone(),
                };
                let solution = standing_after
                    .version_fiber
                    .unique_solution()?
                    .ok_or(InverseTransportError::IncompleteAffineFiber)?;
                let certificate = build_certificate(
                    self.extent,
                    &self.interval,
                    &standing_after.edge_order,
                    &solution,
                    &testimony,
                    standing_after
                        .history
                        .iter()
                        .map(InverseTransportHistoryEntry::event)
                        .chain(std::iter::once(*event))
                        .collect(),
                )?;
                standing_after
                    .history
                    .push(InverseTransportHistoryEntry::CompleteOperator(
                        testimony.clone(),
                    ));
                standing_after.certificate = Some(certificate);
                received_complete_operator = Some(testimony);
            }
        }

        standing_after.used_events.insert(event_id);
        if standing_after.certificate.is_none() {
            let (next_query, query_work) = select_next_query(
                extent,
                &standing_after.edge_order,
                &standing_after.version_fiber,
            )?;
            standing_after.next_query = next_query;
            standing_after.verification_required = standing_after.next_query.is_none();
            work.add_assign(&query_work)?;
        } else {
            standing_after.next_query = None;
            standing_after.verification_required = false;
        }
        standing_after.validate_incremental()?;

        let rank_after = standing_after.version_fiber.rank();
        let radiation = InverseTransportRadiation {
            schema: "holonic-engine.inverse-transport-radiation.v1".to_owned(),
            event: event_id,
            received_testimony,
            received_complete_operator,
            affine_rank_before: u64::try_from(rank_before)
                .map_err(|_| InverseTransportError::CarrierOverflow)?,
            affine_rank_after: u64::try_from(rank_after)
                .map_err(|_| InverseTransportError::CarrierOverflow)?,
            affine_dimension_after: u64::try_from(standing_after.version_fiber.affine_dimension())
                .map_err(|_| InverseTransportError::CarrierOverflow)?,
            next_query: standing_after.next_query.clone(),
            verification_required: standing_after.verification_required,
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

fn admit_testimony(
    standing: &mut InverseTransportStanding,
    testimony: &TransportTestimony,
    work: &mut InverseTransportWork,
) -> Result<(), InverseTransportError> {
    let extent =
        usize::try_from(standing.extent).map_err(|_| InverseTransportError::CarrierOverflow)?;
    testimony.query.validate(extent)?;
    let (coefficients, response) = testimony_constraint(
        &testimony.query,
        &testimony.response,
        &standing.interval,
        &standing.edge_order,
    )?;
    let admission = standing
        .version_fiber
        .admit(coefficients, response)
        .map_err(|error| {
            if error == InverseTransportError::AffineFiberObstructed {
                InverseTransportError::TestimonyObstructsFiber(testimony.event)
            } else {
                error
            }
        })?;
    work.exact_row_eliminations = work
        .exact_row_eliminations
        .checked_add(admission.exact_row_eliminations)
        .ok_or(InverseTransportError::CarrierOverflow)?;
    ensure_no_determined_negative_conductance(&standing.edge_order, &standing.version_fiber)
        .map_err(|_| InverseTransportError::TestimonyObstructsPassiveEcology(testimony.event))?;
    standing
        .history
        .push(InverseTransportHistoryEntry::Testimony(testimony.clone()));
    Ok(())
}

fn testimony_constraint(
    query: &TransportQuery,
    response: &Rat,
    interval: &Rat,
    edges: &[PotentialTransportEdge],
) -> Result<(Vec<Rat>, Rat), InverseTransportError> {
    let baseline = dot(&query.receiver, &query.imposed_potential)?;
    let response = (response - baseline) / interval;
    let coefficients = edges
        .iter()
        .map(|edge| {
            let left =
                usize::try_from(edge.left).map_err(|_| InverseTransportError::CarrierOverflow)?;
            let right =
                usize::try_from(edge.right).map_err(|_| InverseTransportError::CarrierOverflow)?;
            Ok((&query.receiver[left] - &query.receiver[right])
                * (&query.imposed_potential[left] - &query.imposed_potential[right]))
        })
        .collect::<Result<Vec<_>, InverseTransportError>>()?;
    Ok((coefficients, response))
}

fn ensure_no_determined_negative_conductance(
    edges: &[PotentialTransportEdge],
    fiber: &ExactAffineVersionFiber,
) -> Result<(), InverseTransportError> {
    for (ordinal, edge) in edges.iter().enumerate() {
        if fiber
            .coordinate_value(ordinal)?
            .is_some_and(|value| value.is_negative())
        {
            return Err(InverseTransportError::NegativeDeterminedConductance(*edge));
        }
    }
    Ok(())
}

fn select_next_query(
    extent: usize,
    edges: &[PotentialTransportEdge],
    fiber: &ExactAffineVersionFiber,
) -> Result<(Option<TransportQuery>, InverseTransportWork), InverseTransportError> {
    let mut inspected_edge_coordinates = 0_u64;
    for (ordinal, edge) in edges.iter().enumerate() {
        inspected_edge_coordinates = inspected_edge_coordinates
            .checked_add(1)
            .ok_or(InverseTransportError::CarrierOverflow)?;
        if fiber.coordinate_value(ordinal)?.is_none() {
            return Ok((
                Some(TransportQuery::canonical_edge(extent, *edge)?),
                InverseTransportWork {
                    exact_row_eliminations: 0,
                    inspected_edge_coordinates,
                },
            ));
        }
    }
    Ok((
        None,
        InverseTransportWork {
            exact_row_eliminations: 0,
            inspected_edge_coordinates,
        },
    ))
}

fn build_certificate(
    extent: u32,
    interval: &Rat,
    edge_order: &[PotentialTransportEdge],
    solution: &[Rat],
    complete: &CompleteTransportOperatorTestimony,
    testimony_events: BTreeSet<EventId>,
) -> Result<InverseTransportCertificate, InverseTransportError> {
    let extent_usize =
        usize::try_from(extent).map_err(|_| InverseTransportError::CarrierOverflow)?;
    if solution.len() != edge_order.len() {
        return Err(InverseTransportError::IncompleteAffineFiber);
    }
    if let Some((edge, _)) = edge_order
        .iter()
        .zip(solution)
        .find(|(_, conductance)| conductance.is_negative())
    {
        return Err(InverseTransportError::NegativeDeterminedConductance(*edge));
    }

    let mut laplacian = zero_matrix(extent_usize, extent_usize);
    let edge_conductances = edge_order
        .iter()
        .copied()
        .zip(solution.iter().cloned())
        .map(|(edge, conductance)| {
            let left =
                usize::try_from(edge.left).map_err(|_| InverseTransportError::CarrierOverflow)?;
            let right =
                usize::try_from(edge.right).map_err(|_| InverseTransportError::CarrierOverflow)?;
            laplacian[left][left] += &conductance;
            laplacian[right][right] += &conductance;
            laplacian[left][right] -= &conductance;
            laplacian[right][left] -= &conductance;
            Ok(ReconstructedTransportEdge { edge, conductance })
        })
        .collect::<Result<Vec<_>, InverseTransportError>>()?;

    let mut event_operator = laplacian
        .iter()
        .map(|row| row.iter().map(|value| interval * value).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    for (diagonal, row) in event_operator.iter_mut().enumerate() {
        row[diagonal] += Rat::one();
    }
    validate_complete_basis(extent_usize, &complete.responses)?;
    for (row, values) in event_operator.iter().enumerate() {
        for (column, expected) in values.iter().enumerate() {
            let received = &complete.responses[row * extent_usize + column];
            if received != expected {
                return Err(InverseTransportError::CompleteOperatorMismatch { row, column });
            }
        }
    }

    let transfer_operator = invert_exact(event_operator.clone())?;
    let inverse_residual = matrix_subtract(
        &matrix_multiply(&transfer_operator, &event_operator)?,
        &identity_matrix(extent_usize)?,
    )?;
    if inverse_residual
        .iter()
        .flatten()
        .any(|value| !value.is_zero())
    {
        return Err(InverseTransportError::InverseCertificateFailure);
    }

    let nodes = (0..extent_usize)
        .map(|ordinal| {
            Ok(DiffusionNode {
                node: CurrentNodeId(
                    u64::try_from(ordinal)
                        .map_err(|_| InverseTransportError::CarrierOverflow)?
                        .checked_add(1)
                        .ok_or(InverseTransportError::CarrierOverflow)?,
                ),
                capacity: Rat::one(),
            })
        })
        .collect::<Result<Vec<_>, InverseTransportError>>()?;
    let branches = edge_conductances
        .iter()
        .filter(|edge| edge.conductance.is_positive())
        .enumerate()
        .map(|(ordinal, edge)| {
            Ok(DiffusionBranch {
                branch: CurrentBranchId(
                    u64::try_from(ordinal)
                        .map_err(|_| InverseTransportError::CarrierOverflow)?
                        .checked_add(1)
                        .ok_or(InverseTransportError::CarrierOverflow)?,
                ),
                source: CurrentNodeId(u64::from(edge.edge.left) + 1),
                target: CurrentNodeId(u64::from(edge.edge.right) + 1),
                conductance: edge.conductance.clone(),
            })
        })
        .collect::<Result<Vec<_>, InverseTransportError>>()?;
    let positive_edge_count = branches.len();
    let diffusion_complex = DiffusionComplex::new(nodes, branches)?;
    let connected_components = connected_component_count(extent_usize, &edge_conductances)?;
    let cycle_rank = positive_edge_count
        .checked_add(connected_components)
        .and_then(|value| value.checked_sub(extent_usize))
        .ok_or(InverseTransportError::CarrierOverflow)?;

    Ok(InverseTransportCertificate {
        schema: "holonic-engine.inverse-transport-certificate.v1".to_owned(),
        extent,
        interval: interval.clone(),
        edge_order: edge_order.to_vec(),
        edge_conductances,
        laplacian,
        event_operator,
        transfer_operator,
        inverse_residual,
        diffusion_complex,
        connected_components: u64::try_from(connected_components)
            .map_err(|_| InverseTransportError::CarrierOverflow)?,
        cycle_rank: u64::try_from(cycle_rank)
            .map_err(|_| InverseTransportError::CarrierOverflow)?,
        affine_rank: u64::try_from(solution.len())
            .map_err(|_| InverseTransportError::CarrierOverflow)?,
        testimony_events,
        complete_basis_event: complete.event,
    })
}

fn connected_component_count(
    extent: usize,
    edges: &[ReconstructedTransportEdge],
) -> Result<usize, InverseTransportError> {
    let mut adjacency = vec![Vec::new(); extent];
    for edge in edges.iter().filter(|edge| edge.conductance.is_positive()) {
        let left =
            usize::try_from(edge.edge.left).map_err(|_| InverseTransportError::CarrierOverflow)?;
        let right =
            usize::try_from(edge.edge.right).map_err(|_| InverseTransportError::CarrierOverflow)?;
        adjacency[left].push(right);
        adjacency[right].push(left);
    }
    let mut visited = vec![false; extent];
    let mut components = 0_usize;
    for root in 0..extent {
        if visited[root] {
            continue;
        }
        components = components
            .checked_add(1)
            .ok_or(InverseTransportError::CarrierOverflow)?;
        visited[root] = true;
        let mut frontier = VecDeque::from([root]);
        while let Some(node) = frontier.pop_front() {
            for next in &adjacency[node] {
                if !visited[*next] {
                    visited[*next] = true;
                    frontier.push_back(*next);
                }
            }
        }
    }
    Ok(components)
}

fn validate_extent_and_interval(
    extent: u32,
    interval: &Rat,
) -> Result<usize, InverseTransportError> {
    if extent < 2 {
        return Err(InverseTransportError::InvalidExtent(extent));
    }
    if !interval.is_positive() {
        return Err(InverseTransportError::NonpositiveTransportInterval);
    }
    usize::try_from(extent).map_err(|_| InverseTransportError::CarrierOverflow)
}

fn canonical_edges(extent: u32) -> Result<Vec<PotentialTransportEdge>, InverseTransportError> {
    let mut edges = Vec::new();
    for left in 0..extent {
        for right in (left + 1)..extent {
            edges.push(PotentialTransportEdge::new(left, right)?);
        }
    }
    Ok(edges)
}

fn validate_complete_basis(extent: usize, responses: &[Rat]) -> Result<(), InverseTransportError> {
    let expected = extent
        .checked_mul(extent)
        .ok_or(InverseTransportError::CarrierOverflow)?;
    if responses.len() != expected {
        return Err(InverseTransportError::MalformedCompleteOperator {
            expected,
            supplied: responses.len(),
        });
    }
    Ok(())
}

fn zero_matrix(rows: usize, columns: usize) -> Vec<Vec<Rat>> {
    vec![vec![Rat::zero(); columns]; rows]
}

/// Every refusal the shared exact carrier raises, named in this module's own vocabulary.
///
/// `SingularMatrix` is the one the declared material can cause — a reconstructed operator whose
/// rows are dependent, which is a real fact about what the world returned.
impl From<ExactLinearError> for InverseTransportError {
    fn from(error: ExactLinearError) -> Self {
        match error {
            ExactLinearError::SingularMatrix => {
                InverseTransportError::SingularReconstructedOperator
            }
            ExactLinearError::InverseCertificateFailure
            | ExactLinearError::RankFactorizationCertificateFailure => {
                InverseTransportError::InverseCertificateFailure
            }
            ExactLinearError::RaggedMatrix
            | ExactLinearError::NonsquareMatrix
            | ExactLinearError::AddressOutside
            | ExactLinearError::ExtentOverflow
            | ExactLinearError::ShapeMismatch => InverseTransportError::MalformedMatrix,
        }
    }
}

/// Present dense rows to the shared carrier against a **declared** column count, because a
/// matrix with no rows carries none of its own.
fn carrier(matrix: &[Vec<Rat>], columns: usize) -> Result<ExactRatMatrix, InverseTransportError> {
    Ok(ExactRatMatrix::shaped(
        matrix.len(),
        columns,
        matrix.to_vec(),
    )?)
}

fn identity_matrix(extent: usize) -> Result<Vec<Vec<Rat>>, InverseTransportError> {
    Ok(ExactRatMatrix::identity(extent)?.to_rows())
}

fn matrix_vector(matrix: &[Vec<Rat>], vector: &[Rat]) -> Result<Vec<Rat>, InverseTransportError> {
    Ok(carrier(matrix, vector.len())?.apply(vector)?)
}

fn matrix_multiply(
    left: &[Vec<Rat>],
    right: &[Vec<Rat>],
) -> Result<Vec<Vec<Rat>>, InverseTransportError> {
    let inner = right.len();
    let columns = right.first().map_or(0, Vec::len);
    Ok(carrier(left, inner)?
        .multiply(&carrier(right, columns)?)?
        .to_rows())
}

fn matrix_subtract(
    left: &[Vec<Rat>],
    right: &[Vec<Rat>],
) -> Result<Vec<Vec<Rat>>, InverseTransportError> {
    let columns = left.first().or_else(|| right.first()).map_or(0, Vec::len);
    Ok(carrier(left, columns)?
        .subtract(&carrier(right, columns)?)?
        .to_rows())
}

/// The exact inverse, **with the shared carrier's multiplication certificate in force**.
///
/// This was 33 lines of private Gauss-Jordan differing from `generative_transport`'s
/// by one line, and it left the verification to its caller. The rationals are the same.
fn invert_exact(matrix: Vec<Vec<Rat>>) -> Result<Vec<Vec<Rat>>, InverseTransportError> {
    let extent = matrix.len();
    Ok(carrier(&matrix, extent)?.inverse()?.to_rows())
}

fn dot(left: &[Rat], right: &[Rat]) -> Result<Rat, InverseTransportError> {
    if left.len() != right.len() {
        return Err(InverseTransportError::VectorDimension {
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
pub enum InverseTransportError {
    #[error("an inverse transport ecology requires at least two nodes, received {0}")]
    InvalidExtent(u32),
    #[error("an inverse transport ecology requires a positive exact event interval")]
    NonpositiveTransportInterval,
    #[error("potential edge ({left},{right}) is not a canonical unordered pair")]
    MalformedPotentialEdge { left: u32, right: u32 },
    #[error(
        "transport query dimensions disagree: {potentials} potentials and {receiver} receiver coordinates"
    )]
    MalformedQueryDimension { potentials: usize, receiver: usize },
    #[error("a transport query requires a nonzero imposed potential")]
    ZeroPotentialQuery,
    #[error("a transport query requires a nonzero receiver functional")]
    ZeroReceiverQuery,
    #[error("an exact affine version fiber requires at least one variable")]
    EmptyAffineFiber,
    #[error("affine coordinate vector has length {supplied}, expected {expected}")]
    AffineCoordinateDimension { expected: usize, supplied: usize },
    #[error("affine coordinate {coordinate} is outside {variables} variables")]
    AffineCoordinateOutOfRange { coordinate: usize, variables: usize },
    #[error("an exact affine testimony obstructs the complete version fiber")]
    AffineFiberObstructed,
    #[error("the exact affine version fiber is malformed")]
    MalformedAffineFiber,
    #[error("inverse transport law and standing disagree")]
    LawStandingMismatch,
    #[error("inverse transport occurrence {0:?} was already used")]
    RepeatedEvent(EventId),
    #[error("the inverse transport ecology is already certified")]
    EcologyAlreadyCertified,
    #[error("returned query {received:?} does not match production query {expected:?}")]
    UnexpectedReturnedQuery {
        expected: Option<TransportQuery>,
        received: TransportQuery,
    },
    #[error("complete transport operator was returned before production requested it")]
    CompleteOperatorNotRequested,
    #[error("complete operator has {supplied} entries, expected {expected}")]
    MalformedCompleteOperator { expected: usize, supplied: usize },
    #[error("testimony occurrence {0:?} obstructs the affine version fiber")]
    TestimonyObstructsFiber(EventId),
    #[error("testimony occurrence {0:?} obstructs the passive transport ecology")]
    TestimonyObstructsPassiveEcology(EventId),
    #[error("edge {0:?} has a determined negative conductance")]
    NegativeDeterminedConductance(PotentialTransportEdge),
    #[error("the affine version fiber is not yet a unique transport law")]
    IncompleteAffineFiber,
    #[error("complete operator disagrees with the reconstructed law at ({row},{column})")]
    CompleteOperatorMismatch { row: usize, column: usize },
    #[error("the reconstructed event operator is singular")]
    SingularReconstructedOperator,
    #[error("the reconstructed inverse failed its exact identity")]
    InverseCertificateFailure,
    #[error("propagation source has length {supplied}, expected {expected}")]
    PropagationDimension { expected: usize, supplied: usize },
    #[error("the reconstructed transport failed exact total conservation")]
    ReconstructedConservationFailure,
    #[error("vector dimensions disagree: {left} and {right}")]
    VectorDimension { left: usize, right: usize },
    #[error("an exact transport matrix is malformed")]
    MalformedMatrix,
    #[error("the inverse transport standing is malformed")]
    MalformedStanding,
    #[error("an inverse transport exact carrier overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    Diffusion(#[from] DiffusionError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::integer;

    use super::*;
    use crate::CausalWorld;

    fn hidden_edges() -> Vec<(PotentialTransportEdge, Rat)> {
        [
            (0, 1, 2),
            (0, 2, 1),
            (1, 2, 3),
            (1, 4, 1),
            (2, 3, 1),
            (3, 4, 2),
            (3, 5, 1),
            (4, 5, 4),
        ]
        .into_iter()
        .map(|(left, right, conductance)| {
            (
                PotentialTransportEdge::new(left, right).unwrap(),
                integer(conductance),
            )
        })
        .collect()
    }

    fn hidden_response(query: &TransportQuery) -> Rat {
        let baseline = dot(&query.receiver, &query.imposed_potential).unwrap();
        hidden_edges()
            .into_iter()
            .filter(|(edge, _)| (edge.right as usize) < query.receiver.len())
            .fold(baseline, |response, (edge, conductance)| {
                let left = edge.left as usize;
                let right = edge.right as usize;
                response
                    + conductance
                        * (&query.receiver[left] - &query.receiver[right])
                        * (&query.imposed_potential[left] - &query.imposed_potential[right])
            })
    }

    fn complete_operator(extent: usize) -> Vec<Rat> {
        (0..extent)
            .flat_map(|row| {
                (0..extent).map(move |column| {
                    let mut potential = vec![Rat::zero(); extent];
                    let mut receiver = vec![Rat::zero(); extent];
                    potential[column] = Rat::one();
                    receiver[row] = Rat::one();
                    hidden_response(&TransportQuery::new(potential, receiver).unwrap())
                })
            })
            .collect()
    }

    fn return_until_verification(
        world: &mut CausalWorld<InverseTransportLaw>,
        next_event: &mut u64,
    ) {
        while let Some(query) = world.standing().next_query().cloned() {
            world
                .receive(&InverseTransportEvent::ReturnObservation {
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
    fn affine_fiber_retains_a_family_without_enumerating_assignments() {
        let mut fiber = ExactAffineVersionFiber::new(3).unwrap();
        fiber
            .admit(vec![integer(1), integer(1), integer(0)], integer(5))
            .unwrap();
        assert_eq!(fiber.affine_dimension(), 2);
        assert_eq!(fiber.coordinate_value(0).unwrap(), None);
        fiber
            .admit(vec![integer(0), integer(1), integer(0)], integer(2))
            .unwrap();
        assert_eq!(fiber.coordinate_value(0).unwrap(), Some(integer(3)));
        assert_eq!(fiber.coordinate_value(1).unwrap(), Some(integer(2)));
        assert_eq!(fiber.coordinate_value(2).unwrap(), None);
    }

    #[test]
    fn aggregate_lineage_and_production_queries_reconstruct_passive_topology() {
        let law = InverseTransportLaw::new(6, integer(1)).unwrap();
        let standing = InverseTransportStanding::new(6, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let cut = TransportQuery::new(
            vec![
                integer(1),
                integer(1),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
            ],
            vec![
                integer(1),
                integer(1),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
            ],
        )
        .unwrap();
        world
            .receive(&InverseTransportEvent::InheritLandmark {
                event: EventId(1),
                lineage: TransportLineageId(7),
                response: hidden_response(&cut),
                query: cut,
            })
            .unwrap();
        assert_eq!(world.standing().version_fiber().affine_dimension(), 14);

        let mut next_event = 2;
        return_until_verification(&mut world, &mut next_event);
        assert!(world.standing().verification_required());
        assert!(world.standing().certificate().is_none());
        world
            .receive(&InverseTransportEvent::ReturnCompleteOperator {
                event: EventId(next_event),
                receiver: TransportLineageId(1),
                responses: complete_operator(6),
            })
            .unwrap();
        world.standing().validate().unwrap();
        let certificate = world.standing().certificate().unwrap();
        assert_eq!(
            certificate
                .edge_conductances
                .iter()
                .filter(|edge| edge.conductance.is_positive())
                .count(),
            8
        );
        assert_eq!(certificate.connected_components, 1);
        assert_eq!(certificate.cycle_rank, 3);
        assert_eq!(certificate.affine_rank, 15);
    }

    #[test]
    fn returned_query_is_owned_by_production_and_refusal_is_atomic() {
        let law = InverseTransportLaw::new(3, integer(1)).unwrap();
        let standing = InverseTransportStanding::new(3, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing.clone());
        let wrong = TransportQuery::new(
            vec![integer(1), integer(0), integer(0)],
            vec![integer(1), integer(0), integer(0)],
        )
        .unwrap();
        assert!(matches!(
            world.receive(&InverseTransportEvent::ReturnObservation {
                event: EventId(1),
                receiver: TransportLineageId(1),
                query: wrong,
                response: integer(0),
            }),
            Err(InverseTransportError::UnexpectedReturnedQuery { .. })
        ));
        assert_eq!(world.standing(), &standing);
    }

    #[test]
    fn complete_operator_is_required_and_mismatch_cannot_certify() {
        let law = InverseTransportLaw::new(3, integer(1)).unwrap();
        let standing = InverseTransportStanding::new(3, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        assert_eq!(
            world.receive(&InverseTransportEvent::ReturnCompleteOperator {
                event: EventId(1),
                receiver: TransportLineageId(1),
                responses: vec![Rat::zero(); 9],
            }),
            Err(InverseTransportError::CompleteOperatorNotRequested)
        );
        let mut next_event = 2;
        return_until_verification(&mut world, &mut next_event);
        let before = world.standing().clone();
        let mut malformed = complete_operator(3);
        malformed[0] += integer(1);
        assert!(matches!(
            world.receive(&InverseTransportEvent::ReturnCompleteOperator {
                event: EventId(next_event),
                receiver: TransportLineageId(1),
                responses: malformed,
            }),
            Err(InverseTransportError::CompleteOperatorMismatch { .. })
        ));
        assert_eq!(world.standing(), &before);
    }

    #[test]
    fn determined_negative_conductance_obstructs_passive_ecology() {
        let law = InverseTransportLaw::new(2, integer(1)).unwrap();
        let standing = InverseTransportStanding::new(2, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing.clone());
        let query = world.standing().next_query().cloned().unwrap();
        assert_eq!(
            world.receive(&InverseTransportEvent::ReturnObservation {
                event: EventId(1),
                receiver: TransportLineageId(1),
                query,
                response: integer(1),
            }),
            Err(InverseTransportError::TestimonyObstructsPassiveEcology(
                EventId(1)
            ))
        );
        assert_eq!(world.standing(), &standing);
    }

    #[test]
    fn reconstructed_transfer_propagates_and_conserves_exactly() {
        let law = InverseTransportLaw::new(6, integer(1)).unwrap();
        let standing = InverseTransportStanding::new(6, integer(1)).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let mut event = 1;
        return_until_verification(&mut world, &mut event);
        world
            .receive(&InverseTransportEvent::ReturnCompleteOperator {
                event: EventId(event),
                receiver: TransportLineageId(1),
                responses: complete_operator(6),
            })
            .unwrap();
        let receipt = world
            .standing()
            .certificate()
            .unwrap()
            .propagate_from_zero(vec![
                integer(3),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
                integer(0),
            ])
            .unwrap();
        assert_eq!(receipt.total_source, integer(3));
        assert_eq!(receipt.total_after, integer(3));
        assert!(receipt.conservation_residual.is_zero());
        assert!(
            receipt
                .content_after
                .iter()
                .all(|value| value.is_positive())
        );
    }
}
