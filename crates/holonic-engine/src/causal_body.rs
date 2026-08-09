//! Event-indexed exact causal bodies.
//!
//! [`GradedCausalComplex`] owns dimension-independent incidence, but incidence
//! alone is a completed historical presentation.  This module supplies the
//! changing body around that presentation:
//!
//! - cells enter through one atomic event and retain their complete cause;
//! - departure propagates through the maintained coface index, so an active
//!   body is always boundary closed;
//! - exact one-cycle generators become open boundary fibers, never invented
//!   faces;
//! - a later caused higher cell closes only the boundary it actually carries;
//! - reversible connection transports expose fundamental-loop holonomy;
//! - exact cellular-sheaf current can be re-formed and conducted as topology
//!   changes; and
//! - receivers retain changing local source sections rather than camera
//!   coordinates or terminal samples.
//!
//! The automatic opening finder is deliberately limited to a canonical
//! fundamental basis of the active grade-one incidence graph.  Arbitrary-rank
//! closed chains may still enter as explicit caused openings.  No projected
//! crossing, apparent polygon, or display neighborhood promotes source
//! dimension.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::{BigInt, BigUint};
use num_traits::Zero;
use relational_geometry::{
    ExactTurn, JointDecoratedPathOperator, Rat, ReceiverId, SourceSegmentAddress, SourceVertexId,
};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, EventId,
    EventSuccessor, ExactCellularSheaf, ExactEventLaw, ExactLinearMap, ExactSheafCochain,
    ExactSheafDiffusionLaw, GradedCausalComplex, SheafDiffusionError, SheafDiffusionEvent,
    SheafDiffusionReceipt, SheafDiffusionStanding,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EventCellId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum CausalCellReference {
    Standing(CausalCellId),
    Event(EventCellId),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EventBoundaryTerm {
    pub cell: CausalCellReference,
    pub coefficient: ComparativeMultiplicity,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalOpeningId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct CausalFieldId(pub u64);

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalOpeningOrigin {
    FundamentalOneCycle { chord: CausalCellId },
    CausedClosedChain { label: String },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalOpeningState {
    Open,
    Filled { cell: CausalCellId },
    Departed,
}

/// A receiver-relative measure over alternatives already declared by an
/// application.  Counts are exact configuration populations, not a scalar
/// confidence assigned by the engine.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalOpeningMeasure {
    pub filled_population: BigUint,
    pub unfilled_population: BigUint,
}

impl CausalOpeningMeasure {
    pub fn probability_of_fill(&self) -> Rat {
        let total = &self.filled_population + &self.unfilled_population;
        Rat::new(
            BigInt::from(self.filled_population.clone()),
            BigInt::from(total),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalBoundaryOpening {
    pub id: CausalOpeningId,
    pub boundary_grade: u32,
    pub boundary: CausalChain,
    pub origin: CausalOpeningOrigin,
    pub founded_by: EventId,
    pub last_changed_by: EventId,
    pub state: CausalOpeningState,
    pub receiver_measures: BTreeMap<ReceiverId, CausalOpeningMeasure>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalTransportHand {
    Forward,
    Reverse,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalConnectionTransport {
    pub carrier: CausalCellId,
    pub source: CausalCellId,
    pub target: CausalCellId,
    pub forward: ExactLinearMap,
    pub reverse: ExactLinearMap,
    pub founded_by: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalTransportStep {
    pub carrier: CausalCellId,
    pub hand: CausalTransportHand,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalHolonomyGenerator {
    pub chord: CausalCellId,
    pub source: CausalCellId,
    pub loop_boundary: CausalChain,
    pub ordered_steps: Vec<CausalTransportStep>,
    pub transport: ExactLinearMap,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalBodyReceiverStanding {
    pub receiver: ReceiverId,
    pub anchor: CausalCellId,
    pub upper_horizon: u32,
    pub local_section: BTreeSet<CausalCellId>,
    pub anchor_obstructed: bool,
    pub last_return: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalBodyFieldStanding {
    pub id: CausalFieldId,
    pub sheaf: ExactCellularSheaf,
    pub grade: u32,
    pub capacities: BTreeMap<CausalCellId, Vec<Rat>>,
    pub diffusion: SheafDiffusionStanding,
    pub last_changed_by: EventId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalBodyStanding {
    pub schema: String,
    pub incidence: GradedCausalComplex,
    active_cells: BTreeSet<CausalCellId>,
    active_by_grade: BTreeMap<u32, BTreeSet<CausalCellId>>,
    cofaces: BTreeMap<CausalCellId, BTreeSet<CausalCellId>>,
    openings: BTreeMap<CausalOpeningId, CausalBoundaryOpening>,
    opening_keys: BTreeMap<Vec<(CausalCellId, BigInt)>, CausalOpeningId>,
    connections: BTreeMap<CausalCellId, CausalConnectionTransport>,
    holonomy_generators: BTreeMap<CausalCellId, CausalHolonomyGenerator>,
    receivers: BTreeMap<ReceiverId, CausalBodyReceiverStanding>,
    fields: BTreeMap<CausalFieldId, CausalBodyFieldStanding>,
    used_events: BTreeSet<EventId>,
    last_chronology: Option<u64>,
    next_opening: u64,
}

impl Default for CausalBodyStanding {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.causal-body-standing.v1".to_owned(),
            incidence: GradedCausalComplex::default(),
            active_cells: BTreeSet::new(),
            active_by_grade: BTreeMap::new(),
            cofaces: BTreeMap::new(),
            openings: BTreeMap::new(),
            opening_keys: BTreeMap::new(),
            connections: BTreeMap::new(),
            holonomy_generators: BTreeMap::new(),
            receivers: BTreeMap::new(),
            fields: BTreeMap::new(),
            used_events: BTreeSet::new(),
            last_chronology: None,
            next_opening: 1,
        }
    }
}

impl CausalBodyStanding {
    pub fn active_cells(&self) -> &BTreeSet<CausalCellId> {
        &self.active_cells
    }

    pub fn active_cells_at_grade(&self, grade: u32) -> BTreeSet<CausalCellId> {
        self.active_by_grade
            .get(&grade)
            .cloned()
            .unwrap_or_default()
    }

    pub fn openings(&self) -> &BTreeMap<CausalOpeningId, CausalBoundaryOpening> {
        &self.openings
    }

    pub fn connections(&self) -> &BTreeMap<CausalCellId, CausalConnectionTransport> {
        &self.connections
    }

    pub fn holonomy_generators(&self) -> &BTreeMap<CausalCellId, CausalHolonomyGenerator> {
        &self.holonomy_generators
    }

    pub fn receivers(&self) -> &BTreeMap<ReceiverId, CausalBodyReceiverStanding> {
        &self.receivers
    }

    pub fn fields(&self) -> &BTreeMap<CausalFieldId, CausalBodyFieldStanding> {
        &self.fields
    }

    pub fn active_f_vector(&self) -> BTreeMap<u32, usize> {
        let mut result = BTreeMap::new();
        for (grade, cells) in &self.active_by_grade {
            if !cells.is_empty() {
                result.insert(*grade, cells.len());
            }
        }
        result
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CausalBodyDeed {
    FoundCell {
        local: EventCellId,
        name: String,
        grade: u32,
        boundary: Vec<EventBoundaryTerm>,
    },
    DepartCells {
        requested: BTreeSet<CausalCellReference>,
    },
    DeclareClosedOpening {
        label: String,
        boundary: Vec<EventBoundaryTerm>,
    },
    Connect {
        carrier: CausalCellReference,
        source: CausalCellReference,
        target: CausalCellReference,
        forward: ExactLinearMap,
        reverse: ExactLinearMap,
    },
    FoundReceiver {
        receiver: ReceiverId,
        anchor: CausalCellReference,
        upper_horizon: u32,
    },
    MoveReceiver {
        receiver: ReceiverId,
        anchor: CausalCellReference,
        upper_horizon: u32,
    },
    MeasureOpening {
        opening: CausalOpeningId,
        receiver: ReceiverId,
        measure: CausalOpeningMeasure,
    },
    ReformField {
        field: CausalFieldId,
        sheaf: ExactCellularSheaf,
        grade: u32,
        capacities: BTreeMap<CausalCellId, Vec<Rat>>,
        /// Values are supplied only for newly entering grade cells.  Existing
        /// values on common cells are carried by the body.
        entering_content: BTreeMap<CausalCellId, Vec<Rat>>,
    },
    DiffuseField {
        field: CausalFieldId,
        interval: Rat,
        source: BTreeMap<CausalCellId, Vec<Rat>>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalBodyEvent {
    pub event: EventId,
    pub chronology: u64,
    pub deeds: Vec<CausalBodyDeed>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalDepartureReceipt {
    pub requested: BTreeSet<CausalCellId>,
    pub propagated_cofaces: BTreeSet<CausalCellId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalReceiverReturn {
    pub receiver: ReceiverId,
    pub anchor: CausalCellId,
    pub anchor_obstructed: bool,
    pub entered: BTreeSet<CausalCellId>,
    pub departed: BTreeSet<CausalCellId>,
    pub local_section: BTreeSet<CausalCellId>,
    pub local_f_vector: BTreeMap<u32, usize>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalProjectionBinding {
    pub segment: SourceSegmentAddress,
    pub carrier: CausalCellId,
    pub from: CausalCellId,
    pub to: CausalCellId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalProjectionCrossing {
    pub first: CausalCellId,
    pub second: CausalCellId,
    pub first_source_parameters: BTreeSet<Rat>,
    pub second_source_parameters: BTreeSet<Rat>,
    /// True only when the two carriers already meet at a source vertex.
    /// The projected crossing itself never changes this value.
    pub source_adjacent: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalProjectionReceiverReceipt {
    pub receiver: ReceiverId,
    pub receiver_name: String,
    pub apparent_crossings: Vec<CausalProjectionCrossing>,
    pub primitive_closed_returns: Vec<ExactTurn>,
}

/// Receiver testimony over an immutable source body.  `projection_cells` is
/// structurally fixed at zero: diagram crossings decorate bound source
/// carriers and cannot silently enter incidence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalDecoratedProjectionReceipt {
    pub schema: String,
    pub source_cells: usize,
    pub source_f_vector: BTreeMap<u32, usize>,
    pub source_open_boundaries: BTreeSet<CausalOpeningId>,
    pub projection_cells: usize,
    pub receivers: Vec<CausalProjectionReceiverReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalFieldReformReceipt {
    pub field: CausalFieldId,
    pub carried: BTreeSet<CausalCellId>,
    pub entered: BTreeSet<CausalCellId>,
    pub departed: BTreeMap<CausalCellId, Vec<Rat>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CausalBodyRadiation {
    pub schema: String,
    pub event: EventId,
    pub chronology: u64,
    pub minted_cells: BTreeMap<EventCellId, CausalCellId>,
    pub departure: Option<CausalDepartureReceipt>,
    pub active_f_vector_before: BTreeMap<u32, usize>,
    pub active_f_vector_after: BTreeMap<u32, usize>,
    pub changed_openings: BTreeSet<CausalOpeningId>,
    pub holonomy_changed: BTreeSet<CausalCellId>,
    pub receiver_returns: Vec<CausalReceiverReturn>,
    pub field_reforms: Vec<CausalFieldReformReceipt>,
    pub field_diffusions: Vec<(CausalFieldId, SheafDiffusionReceipt)>,
}

#[derive(Clone, Debug, Default)]
pub struct ExactCausalBodyLaw;

impl ExactEventLaw for ExactCausalBodyLaw {
    type Standing = CausalBodyStanding;
    type Event = CausalBodyEvent;
    type Radiation = CausalBodyRadiation;
    type Error = CausalBodyError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate()?;
        if standing_before.used_events.contains(&event.event) {
            return Err(CausalBodyError::DuplicateEvent(event.event));
        }
        if standing_before
            .last_chronology
            .is_some_and(|chronology| event.chronology <= chronology)
        {
            return Err(CausalBodyError::NonincreasingChronology {
                previous: standing_before.last_chronology.expect("checked"),
                supplied: event.chronology,
            });
        }

        let mut standing = standing_before.clone();
        let f_vector_before = standing.active_f_vector();
        let openings_before = standing.openings.clone();
        let holonomy_before = standing.holonomy_generators.clone();
        let receiver_sections_before = standing
            .receivers
            .iter()
            .map(|(receiver, body)| (*receiver, body.local_section.clone()))
            .collect::<BTreeMap<_, _>>();
        let mut event_cells = BTreeMap::new();
        let mut requested_departure = BTreeSet::new();
        let mut field_reforms = Vec::new();
        let mut field_diffusions = Vec::new();

        for deed in &event.deeds {
            match deed {
                CausalBodyDeed::FoundCell {
                    local,
                    name,
                    grade,
                    boundary,
                } => {
                    if event_cells.contains_key(local) {
                        return Err(CausalBodyError::DuplicateEventCell(*local));
                    }
                    let boundary = resolve_boundary(&standing, &event_cells, boundary)?;
                    let cell = standing.incidence.found_cell(
                        name.clone(),
                        BTreeSet::from([event.event]),
                        *grade,
                        boundary,
                    )?;
                    standing.activate_new_cell(cell)?;
                    event_cells.insert(*local, cell);
                }
                CausalBodyDeed::DepartCells { requested } => {
                    for cell in requested {
                        requested_departure.insert(resolve_cell(&standing, &event_cells, *cell)?);
                    }
                }
                CausalBodyDeed::DeclareClosedOpening { label, boundary } => {
                    let boundary = resolve_boundary(&standing, &event_cells, boundary)?;
                    standing.declare_opening(label, boundary, event.event)?;
                }
                CausalBodyDeed::Connect {
                    carrier,
                    source,
                    target,
                    forward,
                    reverse,
                } => {
                    let carrier = resolve_cell(&standing, &event_cells, *carrier)?;
                    let source = resolve_cell(&standing, &event_cells, *source)?;
                    let target = resolve_cell(&standing, &event_cells, *target)?;
                    standing.connect(
                        event.event,
                        carrier,
                        source,
                        target,
                        forward.clone(),
                        reverse.clone(),
                    )?;
                }
                CausalBodyDeed::FoundReceiver {
                    receiver,
                    anchor,
                    upper_horizon,
                } => {
                    if standing.receivers.contains_key(receiver) {
                        return Err(CausalBodyError::DuplicateReceiver(*receiver));
                    }
                    let anchor = resolve_cell(&standing, &event_cells, *anchor)?;
                    standing.receivers.insert(
                        *receiver,
                        CausalBodyReceiverStanding {
                            receiver: *receiver,
                            anchor,
                            upper_horizon: *upper_horizon,
                            local_section: BTreeSet::new(),
                            anchor_obstructed: false,
                            last_return: event.event,
                        },
                    );
                }
                CausalBodyDeed::MoveReceiver {
                    receiver,
                    anchor,
                    upper_horizon,
                } => {
                    let anchor = resolve_cell(&standing, &event_cells, *anchor)?;
                    let body = standing
                        .receivers
                        .get_mut(receiver)
                        .ok_or(CausalBodyError::MissingReceiver(*receiver))?;
                    body.anchor = anchor;
                    body.upper_horizon = *upper_horizon;
                }
                CausalBodyDeed::MeasureOpening {
                    opening,
                    receiver,
                    measure,
                } => {
                    if !standing.receivers.contains_key(receiver) {
                        return Err(CausalBodyError::MissingReceiver(*receiver));
                    }
                    if measure.filled_population.is_zero() && measure.unfilled_population.is_zero()
                    {
                        return Err(CausalBodyError::EmptyOpeningMeasure);
                    }
                    let opening = standing
                        .openings
                        .get_mut(opening)
                        .ok_or(CausalBodyError::MissingOpening(*opening))?;
                    opening.receiver_measures.insert(*receiver, measure.clone());
                    opening.last_changed_by = event.event;
                }
                CausalBodyDeed::ReformField {
                    field,
                    sheaf,
                    grade,
                    capacities,
                    entering_content,
                } => {
                    let receipt = standing.reform_field(
                        event.event,
                        *field,
                        sheaf.clone(),
                        *grade,
                        capacities.clone(),
                        entering_content,
                    )?;
                    field_reforms.push(receipt);
                }
                CausalBodyDeed::DiffuseField {
                    field,
                    interval,
                    source,
                } => {
                    let receipt =
                        standing.diffuse_field(event.event, *field, interval.clone(), source)?;
                    field_diffusions.push((*field, receipt));
                }
            }
        }

        let departure = if requested_departure.is_empty() {
            None
        } else {
            Some(standing.propagate_departure(&requested_departure)?)
        };
        standing.reconcile_openings(event.event)?;
        standing.reconcile_holonomy()?;
        let receiver_returns = standing.reform_receivers(event.event, &receiver_sections_before)?;
        standing.used_events.insert(event.event);
        standing.last_chronology = Some(event.chronology);
        standing.validate()?;

        let changed_openings = changed_map_keys(&openings_before, &standing.openings);
        let holonomy_changed = changed_map_keys(&holonomy_before, &standing.holonomy_generators);
        let radiation = CausalBodyRadiation {
            schema: "holonic-engine.causal-body-radiation.v1".to_owned(),
            event: event.event,
            chronology: event.chronology,
            minted_cells: event_cells,
            departure,
            active_f_vector_before: f_vector_before,
            active_f_vector_after: standing.active_f_vector(),
            changed_openings,
            holonomy_changed,
            receiver_returns,
            field_reforms,
            field_diffusions,
        };
        Ok(EventSuccessor {
            standing_after: standing,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

impl CausalBodyStanding {
    pub fn receive_decorated_projection(
        &self,
        operator: &JointDecoratedPathOperator,
        bindings: &[CausalProjectionBinding],
    ) -> Result<CausalDecoratedProjectionReceipt, CausalBodyError> {
        self.validate()?;
        let mut by_segment = BTreeMap::new();
        for binding in bindings {
            if by_segment.insert(binding.segment, binding).is_some() {
                return Err(CausalBodyError::DuplicateProjectionBinding(binding.segment));
            }
            if !self.active_cells.contains(&binding.carrier)
                || !self.active_cells.contains(&binding.from)
                || !self.active_cells.contains(&binding.to)
            {
                return Err(CausalBodyError::ProjectionBindingOutsideActiveBody(
                    binding.carrier,
                ));
            }
            let endpoints = oriented_edge(&self.incidence, binding.carrier)?;
            if endpoints != (binding.from, binding.to) {
                return Err(CausalBodyError::ProjectionBindingEndpointMismatch {
                    carrier: binding.carrier,
                    expected_from: endpoints.0,
                    expected_to: endpoints.1,
                    supplied_from: binding.from,
                    supplied_to: binding.to,
                });
            }
        }
        let expected_segments = operator
            .source_segments
            .iter()
            .map(|segment| segment.address)
            .collect::<BTreeSet<_>>();
        let supplied_segments = by_segment.keys().copied().collect::<BTreeSet<_>>();
        if expected_segments != supplied_segments {
            return Err(CausalBodyError::ProjectionBindingDomainMismatch);
        }

        let mut source_vertices = BTreeMap::<SourceVertexId, CausalCellId>::new();
        for segment in &operator.source_segments {
            let binding = by_segment[&segment.address];
            bind_source_vertex(&mut source_vertices, segment.from, binding.from)?;
            bind_source_vertex(&mut source_vertices, segment.to, binding.to)?;
        }

        let mut receiver_names = BTreeMap::new();
        for (receiver, name) in &operator.receivers {
            receiver_names.insert(*receiver, name.clone());
        }
        let mut crossings = BTreeMap::<
            ReceiverId,
            BTreeMap<(CausalCellId, CausalCellId), CausalProjectionCrossing>,
        >::new();
        for dart in &operator.darts {
            if !dart.address.forward {
                continue;
            }
            let binding = by_segment[&dart.address.segment];
            for face in &dart.receiver_faces {
                let receiver_crossings = crossings.entry(face.receiver).or_default();
                for mark in &face.crossings {
                    let other = by_segment[&mark.other_branch];
                    let (first, second, first_parameter) = if binding.carrier <= other.carrier {
                        (binding.carrier, other.carrier, true)
                    } else {
                        (other.carrier, binding.carrier, false)
                    };
                    let source_adjacent = [binding.from, binding.to]
                        .into_iter()
                        .any(|endpoint| endpoint == other.from || endpoint == other.to);
                    let row = receiver_crossings
                        .entry((first, second))
                        .or_insert_with(|| CausalProjectionCrossing {
                            first,
                            second,
                            first_source_parameters: BTreeSet::new(),
                            second_source_parameters: BTreeSet::new(),
                            source_adjacent,
                        });
                    if row.source_adjacent != source_adjacent {
                        return Err(CausalBodyError::ProjectionAdjacencyInconsistent {
                            first,
                            second,
                        });
                    }
                    if first_parameter {
                        row.first_source_parameters
                            .insert(mark.source_parameter.clone());
                    } else {
                        row.second_source_parameters
                            .insert(mark.source_parameter.clone());
                    }
                }
            }
        }

        let mut receivers = Vec::new();
        for (receiver, name) in receiver_names {
            let apparent_crossings = crossings
                .remove(&receiver)
                .unwrap_or_default()
                .into_values()
                .collect();
            let mut primitive_closed_returns = Vec::new();
            for trace in &operator.primitive_traces {
                if let Some(receiver_trace) = trace
                    .receiver_traces
                    .iter()
                    .find(|trace| trace.receiver == receiver)
                {
                    primitive_closed_returns.push(receiver_trace.closed_return.clone());
                }
            }
            receivers.push(CausalProjectionReceiverReceipt {
                receiver,
                receiver_name: name,
                apparent_crossings,
                primitive_closed_returns,
            });
        }
        let source_open_boundaries = self
            .openings
            .iter()
            .filter_map(|(id, opening)| (opening.state == CausalOpeningState::Open).then_some(*id))
            .collect();
        Ok(CausalDecoratedProjectionReceipt {
            schema: "holonic-engine.causal-decorated-projection-receipt.v1".to_owned(),
            source_cells: self.active_cells.len(),
            source_f_vector: self.active_f_vector(),
            source_open_boundaries,
            projection_cells: 0,
            receivers,
        })
    }

    fn activate_new_cell(&mut self, cell: CausalCellId) -> Result<(), CausalBodyError> {
        let body = self.incidence.cell(cell)?;
        for boundary in body.boundary.support() {
            if !self.active_cells.contains(&boundary) {
                return Err(CausalBodyError::InactiveBoundary { cell, boundary });
            }
        }
        self.active_cells.insert(cell);
        self.active_by_grade
            .entry(body.grade)
            .or_default()
            .insert(cell);
        self.cofaces.entry(cell).or_default();
        for boundary in body.boundary.support() {
            self.cofaces.entry(boundary).or_default().insert(cell);
        }
        Ok(())
    }

    fn connect(
        &mut self,
        event: EventId,
        carrier: CausalCellId,
        source: CausalCellId,
        target: CausalCellId,
        forward: ExactLinearMap,
        reverse: ExactLinearMap,
    ) -> Result<(), CausalBodyError> {
        if self.connections.contains_key(&carrier) {
            return Err(CausalBodyError::DuplicateConnection(carrier));
        }
        if !self.active_cells.contains(&carrier)
            || !self.active_cells.contains(&source)
            || !self.active_cells.contains(&target)
        {
            return Err(CausalBodyError::ConnectionOutsideActiveBody(carrier));
        }
        let (actual_source, actual_target) = oriented_edge(&self.incidence, carrier)?;
        if (actual_source, actual_target) != (source, target) {
            return Err(CausalBodyError::ConnectionEndpointMismatch {
                carrier,
                expected_source: actual_source,
                expected_target: actual_target,
                supplied_source: source,
                supplied_target: target,
            });
        }
        if forward.rows() == 0
            || forward.rows() != forward.columns()
            || reverse.rows() != reverse.columns()
            || forward.rows() != reverse.rows()
        {
            return Err(CausalBodyError::NonreversibleConnectionDimension(carrier));
        }
        let identity = ExactLinearMap::identity(forward.rows());
        if forward.then(&reverse)? != identity || reverse.then(&forward)? != identity {
            return Err(CausalBodyError::ConnectionNotExactlyReversible(carrier));
        }
        self.connections.insert(
            carrier,
            CausalConnectionTransport {
                carrier,
                source,
                target,
                forward,
                reverse,
                founded_by: event,
            },
        );
        Ok(())
    }

    fn declare_opening(
        &mut self,
        label: &str,
        boundary: CausalChain,
        event: EventId,
    ) -> Result<CausalOpeningId, CausalBodyError> {
        boundary.validate()?;
        if boundary.is_zero() {
            return Err(CausalBodyError::EmptyOpeningBoundary);
        }
        if !boundary.support().is_subset(&self.active_cells) {
            return Err(CausalBodyError::OpeningOutsideActiveBody);
        }
        if !self.incidence.boundary_of_chain(&boundary)?.difference_is_zero() {
            return Err(CausalBodyError::OpeningBoundaryNotClosed);
        }
        let boundary_grade = self
            .incidence
            .homogeneous_grade(&boundary)?
            .ok_or(CausalBodyError::EmptyOpeningBoundary)?;
        let key = canonical_chain_key(&boundary);
        if let Some(existing) = self.opening_keys.get(&key) {
            return Ok(*existing);
        }
        let id = self.mint_opening(
            key,
            boundary_grade,
            boundary,
            CausalOpeningOrigin::CausedClosedChain {
                label: label.to_owned(),
            },
            event,
        );
        Ok(id)
    }

    fn mint_opening(
        &mut self,
        key: Vec<(CausalCellId, BigInt)>,
        boundary_grade: u32,
        boundary: CausalChain,
        origin: CausalOpeningOrigin,
        event: EventId,
    ) -> CausalOpeningId {
        let id = CausalOpeningId(self.next_opening);
        self.next_opening += 1;
        self.opening_keys.insert(key, id);
        self.openings.insert(
            id,
            CausalBoundaryOpening {
                id,
                boundary_grade,
                boundary,
                origin,
                founded_by: event,
                last_changed_by: event,
                state: CausalOpeningState::Open,
                receiver_measures: BTreeMap::new(),
            },
        );
        id
    }

    fn propagate_departure(
        &mut self,
        requested: &BTreeSet<CausalCellId>,
    ) -> Result<CausalDepartureReceipt, CausalBodyError> {
        for cell in requested {
            self.incidence.cell(*cell)?;
            if !self.active_cells.contains(cell) {
                return Err(CausalBodyError::DepartedCellNotActive(*cell));
            }
        }
        let mut departing = requested.clone();
        let mut frontier = requested.iter().copied().collect::<Vec<_>>();
        while let Some(cell) = frontier.pop() {
            if let Some(cofaces) = self.cofaces.get(&cell) {
                for coface in cofaces {
                    if self.active_cells.contains(coface) && departing.insert(*coface) {
                        frontier.push(*coface);
                    }
                }
            }
        }
        for cell in &departing {
            self.active_cells.remove(cell);
            let grade = self.incidence.cell(*cell)?.grade;
            if let Some(at_grade) = self.active_by_grade.get_mut(&grade) {
                at_grade.remove(cell);
            }
        }
        let propagated_cofaces = departing.difference(requested).copied().collect();
        Ok(CausalDepartureReceipt {
            requested: requested.clone(),
            propagated_cofaces,
        })
    }

    fn reconcile_openings(&mut self, event: EventId) -> Result<(), CausalBodyError> {
        for opening in self.openings.values_mut() {
            let next = if !opening.boundary.support().is_subset(&self.active_cells) {
                CausalOpeningState::Departed
            } else if let Some(cell) =
                matching_active_coface(&self.incidence, &self.active_by_grade, opening)?
            {
                CausalOpeningState::Filled { cell }
            } else {
                CausalOpeningState::Open
            };
            if next != opening.state {
                opening.state = next;
                opening.last_changed_by = event;
            }
        }

        for (chord, boundary) in self.fundamental_one_cycles()? {
            let key = canonical_chain_key(&boundary);
            if let Some(opening) = self.opening_keys.get(&key).copied() {
                let body = self.openings.get_mut(&opening).expect("opening key");
                let next = if let Some(cell) =
                    matching_active_coface(&self.incidence, &self.active_by_grade, body)?
                {
                    CausalOpeningState::Filled { cell }
                } else {
                    CausalOpeningState::Open
                };
                if body.state != next {
                    body.state = next;
                    body.last_changed_by = event;
                }
                continue;
            }
            let id = self.mint_opening(
                key,
                1,
                boundary,
                CausalOpeningOrigin::FundamentalOneCycle { chord },
                event,
            );
            let body = self.openings.get_mut(&id).expect("minted opening");
            if let Some(cell) =
                matching_active_coface(&self.incidence, &self.active_by_grade, body)?
            {
                body.state = CausalOpeningState::Filled { cell };
            }
        }
        Ok(())
    }

    fn fundamental_one_cycles(&self) -> Result<Vec<(CausalCellId, CausalChain)>, CausalBodyError> {
        let mut forest = DisjointForest::default();
        for vertex in self
            .active_by_grade
            .get(&0)
            .into_iter()
            .flat_map(|vertices| vertices.iter())
        {
            forest.insert(*vertex);
        }
        let mut tree = CausalTree::new();
        let mut chords = Vec::new();
        let edges = self.active_by_grade.get(&1).cloned().unwrap_or_default();
        for edge in edges {
            if self.incidence.cell(edge)?.boundary.difference_is_zero() {
                chords.push((edge, None));
                continue;
            }
            let Ok((source, target)) = oriented_edge(&self.incidence, edge) else {
                continue;
            };
            if forest.join(source, target) {
                tree.entry(source)
                    .or_default()
                    .push((target, edge, CausalTransportHand::Forward));
                tree.entry(target)
                    .or_default()
                    .push((source, edge, CausalTransportHand::Reverse));
                continue;
            }
            chords.push((edge, Some((source, target))));
        }
        let index = RootedTreeIndex::new(&tree);
        let mut result = Vec::with_capacity(chords.len());
        for (edge, endpoints) in chords {
            let Some((source, target)) = endpoints else {
                result.push((
                    edge,
                    CausalChain::single(edge, ComparativeMultiplicity::positive(1_u8)),
                ));
                continue;
            };
            let path = index
                .path(target, source)
                .ok_or(CausalBodyError::BrokenFundamentalForest(edge))?;
            let mut cycle = CausalChain::single(edge, ComparativeMultiplicity::positive(1_u8));
            for (_, carrier, hand) in path {
                let coefficient = match hand {
                    CausalTransportHand::Forward => ComparativeMultiplicity::positive(1_u8),
                    CausalTransportHand::Reverse => ComparativeMultiplicity::negative(1_u8),
                };
                cycle.add_term(carrier, coefficient);
            }
            if !self.incidence.boundary_of_chain(&cycle)?.difference_is_zero() {
                return Err(CausalBodyError::FundamentalCycleNotClosed(edge));
            }
            result.push((edge, canonical_chain(&cycle)));
        }
        Ok(result)
    }

    fn reconcile_holonomy(&mut self) -> Result<(), CausalBodyError> {
        let mut forest = DisjointForest::default();
        let mut tree = CausalTree::new();
        let mut chords = Vec::new();
        for connection in self.connections.values() {
            if !self.active_cells.contains(&connection.carrier)
                || !self.active_cells.contains(&connection.source)
                || !self.active_cells.contains(&connection.target)
            {
                continue;
            }
            forest.insert(connection.source);
            forest.insert(connection.target);
            if forest.join(connection.source, connection.target) {
                tree.entry(connection.source).or_default().push((
                    connection.target,
                    connection.carrier,
                    CausalTransportHand::Forward,
                ));
                tree.entry(connection.target).or_default().push((
                    connection.source,
                    connection.carrier,
                    CausalTransportHand::Reverse,
                ));
                continue;
            }
            chords.push(connection.carrier);
        }
        let index = RootedTreeIndex::new(&tree);
        let mut generators = BTreeMap::new();
        for chord in chords {
            let connection = &self.connections[&chord];
            let path = index
                .path(connection.target, connection.source)
                .ok_or(CausalBodyError::BrokenFundamentalForest(connection.carrier))?;
            let mut ordered_steps = vec![CausalTransportStep {
                carrier: connection.carrier,
                hand: CausalTransportHand::Forward,
            }];
            let mut transport = connection.forward.clone();
            let mut loop_boundary =
                CausalChain::single(connection.carrier, ComparativeMultiplicity::positive(1_u8));
            for (_, carrier, hand) in path {
                let step_connection = &self.connections[&carrier];
                let map = match hand {
                    CausalTransportHand::Forward => &step_connection.forward,
                    CausalTransportHand::Reverse => &step_connection.reverse,
                };
                transport = transport.then(map).map_err(|_| {
                    CausalBodyError::IncompatibleConnectionComponent {
                        chord: connection.carrier,
                        carrier,
                    }
                })?;
                let coefficient = match hand {
                    CausalTransportHand::Forward => ComparativeMultiplicity::positive(1_u8),
                    CausalTransportHand::Reverse => ComparativeMultiplicity::negative(1_u8),
                };
                loop_boundary.add_term(carrier, coefficient);
                ordered_steps.push(CausalTransportStep { carrier, hand });
            }
            if !self.incidence.boundary_of_chain(&loop_boundary)?.difference_is_zero() {
                return Err(CausalBodyError::FundamentalCycleNotClosed(
                    connection.carrier,
                ));
            }
            generators.insert(
                connection.carrier,
                CausalHolonomyGenerator {
                    chord: connection.carrier,
                    source: connection.source,
                    loop_boundary: canonical_chain(&loop_boundary),
                    ordered_steps,
                    transport,
                },
            );
        }
        self.holonomy_generators = generators;
        Ok(())
    }

    fn reform_receivers(
        &mut self,
        event: EventId,
        before: &BTreeMap<ReceiverId, BTreeSet<CausalCellId>>,
    ) -> Result<Vec<CausalReceiverReturn>, CausalBodyError> {
        let ids = self.receivers.keys().copied().collect::<Vec<_>>();
        let mut returns = Vec::new();
        for receiver in ids {
            let body = self.receivers[&receiver].clone();
            let section = self.receiver_section(body.anchor, body.upper_horizon)?;
            let obstructed = !self.active_cells.contains(&body.anchor);
            let old = before.get(&receiver).cloned().unwrap_or_default();
            let entered = section.difference(&old).copied().collect();
            let departed = old.difference(&section).copied().collect();
            let local_f_vector = support_f_vector(&self.incidence, &section)?;
            let standing = self.receivers.get_mut(&receiver).expect("receiver exists");
            standing.local_section = section.clone();
            standing.anchor_obstructed = obstructed;
            standing.last_return = event;
            returns.push(CausalReceiverReturn {
                receiver,
                anchor: body.anchor,
                anchor_obstructed: obstructed,
                entered,
                departed,
                local_section: section,
                local_f_vector,
            });
        }
        Ok(returns)
    }

    fn receiver_section(
        &self,
        anchor: CausalCellId,
        upper_horizon: u32,
    ) -> Result<BTreeSet<CausalCellId>, CausalBodyError> {
        if !self.active_cells.contains(&anchor) {
            return Ok(BTreeSet::new());
        }
        let anchor_grade = self.incidence.cell(anchor)?.grade;
        let maximum_grade = anchor_grade
            .checked_add(upper_horizon)
            .ok_or(CausalBodyError::ArithmeticOverflow)?;
        let mut reached = BTreeSet::from([anchor]);
        let mut frontier = vec![anchor];
        while let Some(cell) = frontier.pop() {
            if let Some(cofaces) = self.cofaces.get(&cell) {
                for coface in cofaces {
                    if !self.active_cells.contains(coface)
                        || self.incidence.cell(*coface)?.grade > maximum_grade
                    {
                        continue;
                    }
                    if reached.insert(*coface) {
                        frontier.push(*coface);
                    }
                }
            }
        }
        let closed = self.incidence.closed_hull(reached)?;
        Ok(closed.intersection(&self.active_cells).copied().collect())
    }

    fn reform_field(
        &mut self,
        event: EventId,
        field: CausalFieldId,
        sheaf: ExactCellularSheaf,
        grade: u32,
        capacities: BTreeMap<CausalCellId, Vec<Rat>>,
        entering_content: &BTreeMap<CausalCellId, Vec<Rat>>,
    ) -> Result<CausalFieldReformReceipt, CausalBodyError> {
        self.validate_sheaf_source(&sheaf)?;
        let previous = self.fields.get(&field).cloned();
        if previous.as_ref().is_some_and(|body| body.grade != grade) {
            return Err(CausalBodyError::FieldGradeChanged(field));
        }
        let mut values = BTreeMap::new();
        let mut carried = BTreeSet::new();
        let mut entered = BTreeSet::new();
        let mut expected_entering = BTreeSet::new();
        for (cell, body) in sheaf.complex().cells() {
            if body.grade != grade {
                continue;
            }
            if let Some(old) = previous
                .as_ref()
                .and_then(|old| old.diffusion.content.values.get(cell))
                && old.len() == sheaf.stalk_dimension(*cell)? {
                    values.insert(*cell, old.clone());
                    carried.insert(*cell);
                    continue;
                }
            expected_entering.insert(*cell);
            let supplied = entering_content
                .get(cell)
                .ok_or(CausalBodyError::MissingEnteringFieldContent { field, cell: *cell })?;
            values.insert(*cell, supplied.clone());
            entered.insert(*cell);
        }
        let supplied_entering = entering_content.keys().copied().collect::<BTreeSet<_>>();
        if supplied_entering != expected_entering {
            return Err(CausalBodyError::FieldEnteringDomainMismatch(field));
        }
        let content = ExactSheafCochain::new(&sheaf, grade, values)?;
        let law = ExactSheafDiffusionLaw::new(sheaf.clone(), grade, capacities.clone())?;
        let diffusion = law.initial_standing(content)?;
        let mut departed = BTreeMap::new();
        if let Some(previous) = previous {
            for (cell, values) in previous.diffusion.content.values {
                if !carried.contains(&cell) {
                    departed.insert(cell, values);
                }
            }
        }
        self.fields.insert(
            field,
            CausalBodyFieldStanding {
                id: field,
                sheaf,
                grade,
                capacities,
                diffusion,
                last_changed_by: event,
            },
        );
        Ok(CausalFieldReformReceipt {
            field,
            carried,
            entered,
            departed,
        })
    }

    fn diffuse_field(
        &mut self,
        event: EventId,
        field: CausalFieldId,
        interval: Rat,
        source: &BTreeMap<CausalCellId, Vec<Rat>>,
    ) -> Result<SheafDiffusionReceipt, CausalBodyError> {
        let body = self
            .fields
            .get(&field)
            .cloned()
            .ok_or(CausalBodyError::MissingField(field))?;
        let law =
            ExactSheafDiffusionLaw::new(body.sheaf.clone(), body.grade, body.capacities.clone())?;
        let (diffusion, receipt) = law.enact(
            &body.diffusion,
            &SheafDiffusionEvent {
                interval,
                source: source.clone(),
            },
        )?;
        let body = self.fields.get_mut(&field).expect("field exists");
        body.diffusion = diffusion;
        body.last_changed_by = event;
        Ok(receipt)
    }

    fn validate_sheaf_source(&self, sheaf: &ExactCellularSheaf) -> Result<(), CausalBodyError> {
        sheaf.validate()?;
        for (cell, sheaf_body) in sheaf.complex().cells() {
            if !self.active_cells.contains(cell) {
                return Err(CausalBodyError::FieldOutsideActiveBody(*cell));
            }
            if self.incidence.cell(*cell)? != sheaf_body {
                return Err(CausalBodyError::FieldSourceCellMismatch(*cell));
            }
        }
        Ok(())
    }

    pub fn validate(&self) -> Result<(), CausalBodyError> {
        self.incidence.validate()?;
        if !self.incidence.is_closed_support(&self.active_cells)? {
            return Err(CausalBodyError::ActiveBodyNotClosed);
        }
        let all_cells = self
            .incidence
            .cells()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        if !self.active_cells.is_subset(&all_cells) {
            return Err(CausalBodyError::ActiveBodyContainsUnknownCell);
        }
        let mut indexed_active = BTreeSet::new();
        for (grade, cells) in &self.active_by_grade {
            for cell in cells {
                if self.incidence.cell(*cell)?.grade != *grade {
                    return Err(CausalBodyError::GradeIndexMismatch(*cell));
                }
                indexed_active.insert(*cell);
            }
        }
        if indexed_active != self.active_cells {
            return Err(CausalBodyError::ActiveGradeIndexMismatch);
        }
        let expected_cofaces = build_cofaces(&self.incidence);
        if expected_cofaces != self.cofaces {
            return Err(CausalBodyError::CofaceIndexMismatch);
        }
        for (carrier, connection) in &self.connections {
            if carrier != &connection.carrier {
                return Err(CausalBodyError::ConnectionIdentityMismatch(*carrier));
            }
            let (source, target) = oriented_edge(&self.incidence, *carrier)?;
            if (source, target) != (connection.source, connection.target) {
                return Err(CausalBodyError::ConnectionEndpointMismatch {
                    carrier: *carrier,
                    expected_source: source,
                    expected_target: target,
                    supplied_source: connection.source,
                    supplied_target: connection.target,
                });
            }
            let identity = ExactLinearMap::identity(connection.forward.rows());
            if connection.forward.then(&connection.reverse)? != identity
                || connection.reverse.then(&connection.forward)? != identity
            {
                return Err(CausalBodyError::ConnectionNotExactlyReversible(*carrier));
            }
        }
        for field in self.fields.values() {
            self.validate_sheaf_source(&field.sheaf)?;
            field.diffusion.content.validate(&field.sheaf)?;
        }
        for receiver in self.receivers.values() {
            let expected = self.receiver_section(receiver.anchor, receiver.upper_horizon)?;
            if expected != receiver.local_section {
                return Err(CausalBodyError::ReceiverSectionStale(receiver.receiver));
            }
        }
        if self
            .openings
            .keys()
            .next_back()
            .is_some_and(|id| id.0 >= self.next_opening)
        {
            return Err(CausalBodyError::InvalidNextOpeningIdentity);
        }
        Ok(())
    }
}

fn resolve_cell(
    standing: &CausalBodyStanding,
    event_cells: &BTreeMap<EventCellId, CausalCellId>,
    reference: CausalCellReference,
) -> Result<CausalCellId, CausalBodyError> {
    match reference {
        CausalCellReference::Standing(cell) => {
            standing.incidence.cell(cell)?;
            Ok(cell)
        }
        CausalCellReference::Event(local) => event_cells
            .get(&local)
            .copied()
            .ok_or(CausalBodyError::ForwardEventCellReference(local)),
    }
}

fn resolve_boundary(
    standing: &CausalBodyStanding,
    event_cells: &BTreeMap<EventCellId, CausalCellId>,
    terms: &[EventBoundaryTerm],
) -> Result<CausalChain, CausalBodyError> {
    let mut result = CausalChain::default();
    for term in terms {
        let cell = resolve_cell(standing, event_cells, term.cell)?;
        result.add_term(cell, term.coefficient.clone());
    }
    Ok(result)
}

fn oriented_edge(
    complex: &GradedCausalComplex,
    edge: CausalCellId,
) -> Result<(CausalCellId, CausalCellId), CausalBodyError> {
    let body = complex.cell(edge)?;
    if body.grade != 1 || body.boundary.coefficients().len() != 2 {
        return Err(CausalBodyError::CarrierIsNotOrientedEdge(edge));
    }
    let mut source = None;
    let mut target = None;
    for (cell, coefficient) in body.boundary.coefficients() {
        if !coefficient.is_unit_orientation() {
            return Err(CausalBodyError::CarrierIsNotOrientedEdge(edge));
        }
        if coefficient.difference() == BigInt::from(-1) {
            source = Some(*cell);
        } else if coefficient.difference() == BigInt::from(1) {
            target = Some(*cell);
        }
    }
    match (source, target) {
        (Some(source), Some(target)) => Ok((source, target)),
        _ => Err(CausalBodyError::CarrierIsNotOrientedEdge(edge)),
    }
}

fn canonical_chain(chain: &CausalChain) -> CausalChain {
    let Some((_, first)) = chain.coefficients().first_key_value() else {
        return chain.clone();
    };
    if first.difference() < BigInt::zero() {
        chain.negated()
    } else {
        chain.clone()
    }
}

fn canonical_chain_key(chain: &CausalChain) -> Vec<(CausalCellId, BigInt)> {
    let canonical = canonical_chain(chain);
    let mut result = Vec::with_capacity(canonical.coefficients().len());
    for (cell, coefficient) in canonical.coefficients() {
        result.push((*cell, coefficient.difference()));
    }
    result
}

fn matching_active_coface(
    complex: &GradedCausalComplex,
    active_by_grade: &BTreeMap<u32, BTreeSet<CausalCellId>>,
    opening: &CausalBoundaryOpening,
) -> Result<Option<CausalCellId>, CausalBodyError> {
    let Some(fill_grade) = opening.boundary_grade.checked_add(1) else {
        return Err(CausalBodyError::ArithmeticOverflow);
    };
    let key = canonical_chain_key(&opening.boundary);
    for cell in active_by_grade
        .get(&fill_grade)
        .into_iter()
        .flat_map(|cells| cells.iter())
    {
        if canonical_chain_key(&complex.cell(*cell)?.boundary) == key {
            return Ok(Some(*cell));
        }
    }
    Ok(None)
}

fn build_cofaces(complex: &GradedCausalComplex) -> BTreeMap<CausalCellId, BTreeSet<CausalCellId>> {
    let mut result = BTreeMap::new();
    for cell in complex.cells().keys() {
        result.entry(*cell).or_insert_with(BTreeSet::new);
    }
    for (upper, body) in complex.cells() {
        for lower in body.boundary.support() {
            result
                .entry(lower)
                .or_insert_with(BTreeSet::new)
                .insert(*upper);
        }
    }
    result
}

fn support_f_vector(
    complex: &GradedCausalComplex,
    support: &BTreeSet<CausalCellId>,
) -> Result<BTreeMap<u32, usize>, CausalBodyError> {
    let mut result = BTreeMap::new();
    for cell in support {
        let grade = complex.cell(*cell)?.grade;
        *result.entry(grade).or_default() += 1;
    }
    Ok(result)
}

fn bind_source_vertex(
    bindings: &mut BTreeMap<SourceVertexId, CausalCellId>,
    source: SourceVertexId,
    causal: CausalCellId,
) -> Result<(), CausalBodyError> {
    if let Some(existing) = bindings.insert(source, causal)
        && existing != causal {
            return Err(CausalBodyError::ProjectionSourceVertexInconsistent {
                source_vertex: source,
                first: existing,
                second: causal,
            });
        }
    Ok(())
}

fn changed_map_keys<K, V>(before: &BTreeMap<K, V>, after: &BTreeMap<K, V>) -> BTreeSet<K>
where
    K: Copy + Ord,
    V: PartialEq,
{
    let mut keys = BTreeSet::new();
    keys.extend(before.keys().copied());
    keys.extend(after.keys().copied());
    keys.into_iter()
        .filter(|key| before.get(key) != after.get(key))
        .collect()
}

#[derive(Clone, Debug, Default)]
struct DisjointForest {
    parent: BTreeMap<CausalCellId, CausalCellId>,
}

impl DisjointForest {
    fn insert(&mut self, cell: CausalCellId) {
        self.parent.entry(cell).or_insert(cell);
    }

    fn root(&self, cell: CausalCellId) -> CausalCellId {
        let mut current = cell;
        while self.parent[&current] != current {
            current = self.parent[&current];
        }
        current
    }

    /// Returns true when this edge joins two previously distinct components.
    fn join(&mut self, left: CausalCellId, right: CausalCellId) -> bool {
        self.insert(left);
        self.insert(right);
        let left_root = self.root(left);
        let right_root = self.root(right);
        if left_root == right_root {
            return false;
        }
        let (lower, upper) = if left_root < right_root {
            (left_root, right_root)
        } else {
            (right_root, left_root)
        };
        self.parent.insert(upper, lower);
        true
    }
}

type CausalTree = BTreeMap<CausalCellId, Vec<(CausalCellId, CausalCellId, CausalTransportHand)>>;

#[derive(Clone, Debug, Default)]
struct RootedTreeIndex {
    parent: BTreeMap<CausalCellId, (CausalCellId, CausalCellId, CausalTransportHand)>,
    depth: BTreeMap<CausalCellId, usize>,
    component: BTreeMap<CausalCellId, CausalCellId>,
}

impl RootedTreeIndex {
    fn new(tree: &CausalTree) -> Self {
        let mut nodes = BTreeSet::new();
        for (source, branches) in tree {
            nodes.insert(*source);
            for (target, _, _) in branches {
                nodes.insert(*target);
            }
        }
        let mut result = Self::default();
        for root in nodes {
            if result.depth.contains_key(&root) {
                continue;
            }
            result.depth.insert(root, 0);
            result.component.insert(root, root);
            let mut queue = VecDeque::from([root]);
            while let Some(source) = queue.pop_front() {
                let source_depth = result.depth[&source];
                for (target, carrier, hand) in tree.get(&source).into_iter().flatten() {
                    if result.depth.contains_key(target) {
                        continue;
                    }
                    result.parent.insert(*target, (source, *carrier, *hand));
                    result.depth.insert(*target, source_depth + 1);
                    result.component.insert(*target, root);
                    queue.push_back(*target);
                }
            }
        }
        result
    }

    fn path(
        &self,
        source: CausalCellId,
        target: CausalCellId,
    ) -> Option<Vec<(CausalCellId, CausalCellId, CausalTransportHand)>> {
        if self.component.get(&source) != self.component.get(&target) {
            return None;
        }
        let mut left = source;
        let mut right = target;
        let mut left_steps = Vec::new();
        let mut right_steps = Vec::new();
        while self.depth[&left] > self.depth[&right] {
            let (parent, carrier, parent_to_child) = self.parent[&left];
            left_steps.push((parent, carrier, opposite_hand(parent_to_child)));
            left = parent;
        }
        while self.depth[&right] > self.depth[&left] {
            let (parent, carrier, parent_to_child) = self.parent[&right];
            right_steps.push((right, carrier, parent_to_child));
            right = parent;
        }
        while left != right {
            let (left_parent, left_carrier, left_parent_to_child) = self.parent[&left];
            left_steps.push((
                left_parent,
                left_carrier,
                opposite_hand(left_parent_to_child),
            ));
            left = left_parent;

            let (right_parent, right_carrier, right_parent_to_child) = self.parent[&right];
            right_steps.push((right, right_carrier, right_parent_to_child));
            right = right_parent;
        }
        right_steps.reverse();
        left_steps.extend(right_steps);
        Some(left_steps)
    }
}

fn opposite_hand(hand: CausalTransportHand) -> CausalTransportHand {
    match hand {
        CausalTransportHand::Forward => CausalTransportHand::Reverse,
        CausalTransportHand::Reverse => CausalTransportHand::Forward,
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum CausalBodyError {
    #[error("event {0:?} already entered this causal body")]
    DuplicateEvent(EventId),
    #[error("event chronology must increase beyond {previous}, received {supplied}")]
    NonincreasingChronology { previous: u64, supplied: u64 },
    #[error("event-local cell handle {0:?} was declared more than once")]
    DuplicateEventCell(EventCellId),
    #[error("event-local cell handle {0:?} was referenced before it was caused")]
    ForwardEventCellReference(EventCellId),
    #[error("cell {cell:?} was founded while boundary cell {boundary:?} was inactive")]
    InactiveBoundary {
        cell: CausalCellId,
        boundary: CausalCellId,
    },
    #[error("cell {0:?} was requested to depart but is not active")]
    DepartedCellNotActive(CausalCellId),
    #[error("active causal incidence is not boundary closed")]
    ActiveBodyNotClosed,
    #[error("the active body contains a cell absent from complete lineage")]
    ActiveBodyContainsUnknownCell,
    #[error("active grade index disagrees with the active cell population")]
    ActiveGradeIndexMismatch,
    #[error("cell {0:?} is stored under the wrong active grade")]
    GradeIndexMismatch(CausalCellId),
    #[error("the complete coface index disagrees with source incidence")]
    CofaceIndexMismatch,
    #[error("connection carrier {0:?} was declared more than once")]
    DuplicateConnection(CausalCellId),
    #[error("connection carrier {0:?} or one of its endpoints is not active")]
    ConnectionOutsideActiveBody(CausalCellId),
    #[error("cell {0:?} is not an oriented unit edge")]
    CarrierIsNotOrientedEdge(CausalCellId),
    #[error(
        "connection {carrier:?} has source/target {expected_source:?}->{expected_target:?}, not supplied {supplied_source:?}->{supplied_target:?}"
    )]
    ConnectionEndpointMismatch {
        carrier: CausalCellId,
        expected_source: CausalCellId,
        expected_target: CausalCellId,
        supplied_source: CausalCellId,
        supplied_target: CausalCellId,
    },
    #[error("connection {0:?} does not carry two nonempty square maps of equal extent")]
    NonreversibleConnectionDimension(CausalCellId),
    #[error("connection {0:?} forward and reverse maps are not exact inverses")]
    ConnectionNotExactlyReversible(CausalCellId),
    #[error("connection map key and carrier identity differ at {0:?}")]
    ConnectionIdentityMismatch(CausalCellId),
    #[error("fundamental forest could not return chord {0:?} to its source")]
    BrokenFundamentalForest(CausalCellId),
    #[error("fundamental cycle at chord {0:?} retained a nonzero boundary")]
    FundamentalCycleNotClosed(CausalCellId),
    #[error("connection loop at chord {chord:?} cannot compose through carrier {carrier:?}")]
    IncompatibleConnectionComponent {
        chord: CausalCellId,
        carrier: CausalCellId,
    },
    #[error("an open boundary cannot be the zero chain")]
    EmptyOpeningBoundary,
    #[error("an opening boundary reaches outside the active body")]
    OpeningOutsideActiveBody,
    #[error("an opening boundary itself has nonzero boundary")]
    OpeningBoundaryNotClosed,
    #[error("open boundary {0:?} is absent")]
    MissingOpening(CausalOpeningId),
    #[error("an opening measure must contain at least one configuration")]
    EmptyOpeningMeasure,
    #[error("opening identity horizon does not follow the extant population")]
    InvalidNextOpeningIdentity,
    #[error("receiver {0:?} already exists")]
    DuplicateReceiver(ReceiverId),
    #[error("receiver {0:?} is absent")]
    MissingReceiver(ReceiverId),
    #[error("receiver {0:?} retained a stale local source section")]
    ReceiverSectionStale(ReceiverId),
    #[error("source segment {0:?} was bound to the causal body more than once")]
    DuplicateProjectionBinding(SourceSegmentAddress),
    #[error("projection binding carrier {0:?} or one of its endpoints is not active")]
    ProjectionBindingOutsideActiveBody(CausalCellId),
    #[error(
        "projection carrier {carrier:?} has source endpoints {expected_from:?}->{expected_to:?}, not supplied {supplied_from:?}->{supplied_to:?}"
    )]
    ProjectionBindingEndpointMismatch {
        carrier: CausalCellId,
        expected_from: CausalCellId,
        expected_to: CausalCellId,
        supplied_from: CausalCellId,
        supplied_to: CausalCellId,
    },
    #[error("projection bindings do not exactly cover the decorated source segments")]
    ProjectionBindingDomainMismatch,
    #[error(
        "decorated source vertex {source_vertex:?} was bound inconsistently to {first:?} and {second:?}"
    )]
    ProjectionSourceVertexInconsistent {
        source_vertex: SourceVertexId,
        first: CausalCellId,
        second: CausalCellId,
    },
    #[error("projection crossing pair {first:?}/{second:?} retained inconsistent source adjacency")]
    ProjectionAdjacencyInconsistent {
        first: CausalCellId,
        second: CausalCellId,
    },
    #[error("field {0:?} is absent")]
    MissingField(CausalFieldId),
    #[error("field {0:?} cannot change its selected cochain grade")]
    FieldGradeChanged(CausalFieldId),
    #[error("field source cell {0:?} is not active")]
    FieldOutsideActiveBody(CausalCellId),
    #[error("field source cell {0:?} differs from complete causal incidence")]
    FieldSourceCellMismatch(CausalCellId),
    #[error("field {field:?} omits entering content at cell {cell:?}")]
    MissingEnteringFieldContent {
        field: CausalFieldId,
        cell: CausalCellId,
    },
    #[error("field {0:?} entering-content domain differs from its newly entering cells")]
    FieldEnteringDomainMismatch(CausalFieldId),
    #[error("finite causal-body arithmetic overflowed its carrier")]
    ArithmeticOverflow,
    #[error(transparent)]
    Algebraic(#[from] CausalAlgebraicError),
    #[error(transparent)]
    Sheaf(#[from] SheafDiffusionError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::{
        Construction, Geometry, ProjectionLaw, RatVec3, Receiver, ReceiverId,
        build_joint_decorated_path_operator, integer,
    };

    use super::*;
    use crate::{CausalWorld, CellularRestriction};

    fn vertex(local: u64, name: &str) -> CausalBodyDeed {
        CausalBodyDeed::FoundCell {
            local: EventCellId(local),
            name: name.to_owned(),
            grade: 0,
            boundary: Vec::new(),
        }
    }

    fn edge(local: u64, name: &str, source: u64, target: u64) -> CausalBodyDeed {
        CausalBodyDeed::FoundCell {
            local: EventCellId(local),
            name: name.to_owned(),
            grade: 1,
            boundary: vec![
                EventBoundaryTerm {
                    cell: CausalCellReference::Event(EventCellId(source)),
                    coefficient: ComparativeMultiplicity::negative(1_u8),
                },
                EventBoundaryTerm {
                    cell: CausalCellReference::Event(EventCellId(target)),
                    coefficient: ComparativeMultiplicity::positive(1_u8),
                },
            ],
        }
    }

    fn triangle_event(event: EventId, include_face: bool) -> CausalBodyEvent {
        let mut deeds = vec![
            vertex(1, "a"),
            vertex(2, "b"),
            vertex(3, "c"),
            edge(4, "ab", 1, 2),
            edge(5, "bc", 2, 3),
            edge(6, "ca", 3, 1),
        ];
        if include_face {
            deeds.push(CausalBodyDeed::FoundCell {
                local: EventCellId(7),
                name: "abc".to_owned(),
                grade: 2,
                boundary: vec![
                    EventBoundaryTerm {
                        cell: CausalCellReference::Event(EventCellId(4)),
                        coefficient: ComparativeMultiplicity::positive(1_u8),
                    },
                    EventBoundaryTerm {
                        cell: CausalCellReference::Event(EventCellId(5)),
                        coefficient: ComparativeMultiplicity::positive(1_u8),
                    },
                    EventBoundaryTerm {
                        cell: CausalCellReference::Event(EventCellId(6)),
                        coefficient: ComparativeMultiplicity::positive(1_u8),
                    },
                ],
            });
        }
        CausalBodyEvent {
            event,
            chronology: event.0,
            deeds,
        }
    }

    #[test]
    fn a_cycle_is_an_open_boundary_until_a_caused_face_arrives() {
        let mut world = CausalWorld::new(ExactCausalBodyLaw, CausalBodyStanding::default());
        let first = world.receive(&triangle_event(EventId(1), false)).unwrap();
        let radiation = &first.radiation[0];
        assert_eq!(
            radiation.active_f_vector_after,
            BTreeMap::from([(0, 3), (1, 3)])
        );
        assert_eq!(world.standing().openings.len(), 1);
        let opening = world.standing().openings.values().next().unwrap();
        assert_eq!(opening.state, CausalOpeningState::Open);

        let edges = world.standing().active_cells_at_grade(1);
        let face = CausalBodyDeed::FoundCell {
            local: EventCellId(1),
            name: "returned face".to_owned(),
            grade: 2,
            boundary: edges
                .into_iter()
                .map(|cell| EventBoundaryTerm {
                    cell: CausalCellReference::Standing(cell),
                    coefficient: ComparativeMultiplicity::positive(1_u8),
                })
                .collect(),
        };
        world
            .receive(&CausalBodyEvent {
                event: EventId(2),
                chronology: 2,
                deeds: vec![face],
            })
            .unwrap();
        let opening = world.standing().openings.values().next().unwrap();
        assert!(matches!(opening.state, CausalOpeningState::Filled { .. }));
    }

    #[test]
    fn lower_cell_departure_carries_every_active_coface_and_receiver_return() {
        let mut world = CausalWorld::new(ExactCausalBodyLaw, CausalBodyStanding::default());
        let mut event = triangle_event(EventId(1), true);
        event.deeds.push(CausalBodyDeed::FoundReceiver {
            receiver: ReceiverId(9),
            anchor: CausalCellReference::Event(EventCellId(1)),
            upper_horizon: 2,
        });
        world.receive(&event).unwrap();
        assert_eq!(
            world.standing().receivers[&ReceiverId(9)]
                .local_section
                .len(),
            7
        );
        let vertex = *world.standing().active_cells_at_grade(0).first().unwrap();
        let receipt = world
            .receive(&CausalBodyEvent {
                event: EventId(2),
                chronology: 2,
                deeds: vec![CausalBodyDeed::DepartCells {
                    requested: BTreeSet::from([CausalCellReference::Standing(vertex)]),
                }],
            })
            .unwrap();
        let radiation = &receipt.radiation[0];
        assert_eq!(radiation.departure.as_ref().unwrap().requested.len(), 1);
        assert_eq!(
            radiation
                .departure
                .as_ref()
                .unwrap()
                .propagated_cofaces
                .len(),
            3
        );
        assert!(world.standing().receivers[&ReceiverId(9)].anchor_obstructed);
        assert!(
            world.standing().receivers[&ReceiverId(9)]
                .local_section
                .is_empty()
        );
    }

    #[test]
    fn loop_holonomy_is_path_ordered_and_not_a_drawn_cycle() {
        let scale_two = ExactLinearMap::new(1, 1, vec![vec![integer(2)]]).unwrap();
        let scale_half =
            ExactLinearMap::new(1, 1, vec![vec![Rat::new(1.into(), 2.into())]]).unwrap();
        let scale_three = ExactLinearMap::new(1, 1, vec![vec![integer(3)]]).unwrap();
        let scale_third =
            ExactLinearMap::new(1, 1, vec![vec![Rat::new(1.into(), 3.into())]]).unwrap();
        let scale_five = ExactLinearMap::new(1, 1, vec![vec![integer(5)]]).unwrap();
        let scale_fifth =
            ExactLinearMap::new(1, 1, vec![vec![Rat::new(1.into(), 5.into())]]).unwrap();
        let mut event = triangle_event(EventId(1), false);
        event.deeds.extend([
            CausalBodyDeed::Connect {
                carrier: CausalCellReference::Event(EventCellId(4)),
                source: CausalCellReference::Event(EventCellId(1)),
                target: CausalCellReference::Event(EventCellId(2)),
                forward: scale_two,
                reverse: scale_half,
            },
            CausalBodyDeed::Connect {
                carrier: CausalCellReference::Event(EventCellId(5)),
                source: CausalCellReference::Event(EventCellId(2)),
                target: CausalCellReference::Event(EventCellId(3)),
                forward: scale_three,
                reverse: scale_third,
            },
            CausalBodyDeed::Connect {
                carrier: CausalCellReference::Event(EventCellId(6)),
                source: CausalCellReference::Event(EventCellId(3)),
                target: CausalCellReference::Event(EventCellId(1)),
                forward: scale_five,
                reverse: scale_fifth,
            },
        ]);
        let mut world = CausalWorld::new(ExactCausalBodyLaw, CausalBodyStanding::default());
        world.receive(&event).unwrap();
        let generator = world
            .standing()
            .holonomy_generators
            .values()
            .next()
            .unwrap();
        assert_eq!(
            generator.transport,
            ExactLinearMap::new(1, 1, vec![vec![integer(30)]]).unwrap()
        );
    }

    #[test]
    fn exact_field_current_reforms_and_conducts_on_the_active_body() {
        let mut world = CausalWorld::new(ExactCausalBodyLaw, CausalBodyStanding::default());
        let first = CausalBodyEvent {
            event: EventId(1),
            chronology: 1,
            deeds: vec![vertex(1, "left"), vertex(2, "right"), edge(3, "link", 1, 2)],
        };
        world.receive(&first).unwrap();
        let vertices = world
            .standing()
            .active_cells_at_grade(0)
            .into_iter()
            .collect::<Vec<_>>();
        let left = vertices[0];
        let right = vertices[1];
        let edge = *world.standing().active_cells_at_grade(1).first().unwrap();
        let mut stalks = BTreeMap::new();
        for cell in world.standing().active_cells() {
            stalks.insert(*cell, 1);
        }
        let sheaf = ExactCellularSheaf::new(
            world.standing().incidence.clone(),
            stalks,
            [
                CellularRestriction {
                    lower: left,
                    upper: edge,
                    map: ExactLinearMap::identity(1),
                },
                CellularRestriction {
                    lower: right,
                    upper: edge,
                    map: ExactLinearMap::identity(1),
                },
            ],
        )
        .unwrap();
        let field = CausalFieldId(1);
        let receipt = world
            .receive(&CausalBodyEvent {
                event: EventId(2),
                chronology: 2,
                deeds: vec![
                    CausalBodyDeed::ReformField {
                        field,
                        sheaf,
                        grade: 0,
                        capacities: BTreeMap::from([
                            (left, vec![integer(1)]),
                            (right, vec![integer(1)]),
                        ]),
                        entering_content: BTreeMap::from([
                            (left, vec![integer(1)]),
                            (right, vec![integer(0)]),
                        ]),
                    },
                    CausalBodyDeed::DiffuseField {
                        field,
                        interval: integer(1),
                        source: BTreeMap::new(),
                    },
                ],
            })
            .unwrap();
        assert_eq!(receipt.radiation[0].field_reforms[0].entered.len(), 2);
        let content = &world.standing().fields[&field].diffusion.content.values;
        assert_eq!(content[&left], vec![Rat::new(2.into(), 3.into())]);
        assert_eq!(content[&right], vec![Rat::new(1.into(), 3.into())]);
    }

    #[test]
    fn a_receiver_crossing_decorates_but_never_retiles_source_incidence() {
        let (mut construction, frame) = Construction::new("crossing receiver control");
        let loop_entity = construction
            .add_entity(
                "nonplanar crossing loop",
                frame,
                Geometry::Thread {
                    vertices: vec![
                        RatVec3::from_i64(-1, -1, 1),
                        RatVec3::from_i64(1, 1, 1),
                        RatVec3::from_i64(-1, 1, 0),
                        RatVec3::from_i64(1, -1, 0),
                    ],
                    closed: true,
                },
            )
            .unwrap();
        let receiver = Receiver::new(
            ReceiverId(1),
            "orthographic crossing membrane",
            frame,
            ProjectionLaw::Orthographic,
        );
        let operator = build_joint_decorated_path_operator(&construction, &[receiver], 2).unwrap();

        let mut world = CausalWorld::new(ExactCausalBodyLaw, CausalBodyStanding::default());
        let transition = world
            .receive(&CausalBodyEvent {
                event: EventId(1),
                chronology: 1,
                deeds: vec![
                    vertex(1, "rising from"),
                    vertex(2, "rising to"),
                    vertex(3, "falling from"),
                    vertex(4, "falling to"),
                    edge(5, "rising", 1, 2),
                    edge(6, "upper connector", 2, 3),
                    edge(7, "falling", 3, 4),
                    edge(8, "lower connector", 4, 1),
                ],
            })
            .unwrap();
        let minted = &transition.radiation[0].minted_cells;
        let bindings = operator
            .source_segments
            .iter()
            .map(|segment| {
                assert_eq!(segment.address.entity, loop_entity);
                let (carrier, from, to) = match segment.address.segment {
                    0 => (5, 1, 2),
                    1 => (6, 2, 3),
                    2 => (7, 3, 4),
                    3 => (8, 4, 1),
                    other => panic!("unexpected loop segment {other}"),
                };
                CausalProjectionBinding {
                    segment: segment.address,
                    carrier: minted[&EventCellId(carrier)],
                    from: minted[&EventCellId(from)],
                    to: minted[&EventCellId(to)],
                }
            })
            .collect::<Vec<_>>();
        let receipt = world
            .standing()
            .receive_decorated_projection(&operator, &bindings)
            .unwrap();
        assert_eq!(receipt.source_f_vector, BTreeMap::from([(0, 4), (1, 4)]));
        assert_eq!(receipt.source_cells, 8);
        assert_eq!(receipt.projection_cells, 0);
        assert_eq!(receipt.receivers[0].apparent_crossings.len(), 1);
        assert!(!receipt.receivers[0].apparent_crossings[0].source_adjacent);
        assert_eq!(receipt.source_open_boundaries.len(), 1);
        assert_eq!(world.standing().incidence.cells().len(), 8);
    }
}
