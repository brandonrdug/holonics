//! Receiver-relative recurrence across incidence grade and observation grain.
//!
//! A receiver-visible point need not be internally zero-dimensional.  The
//! finest grain constructed here receives an exact phase germ as one
//! grade-zero cell while retaining the germ's native conic sections.  Exact
//! connection transport between germs becomes grade one, and a closed
//! transported circuit becomes grade two.  The complete closed hull of that
//! circuit may then be received as one grade-zero cell of a coarser grain.
//!
//! Grade and grain are deliberately distinct:
//!
//! - **grade** is boundary rank inside one causal complex;
//! - **grain** is the receiver at which an already completed complex is
//!   admitted as one constituent.
//!
//! Pixels never become cells of this complex.  They remain finite testimony
//! used by [`ReceiverPhaseAtlasLaw`] to cause analytical germs.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigUint;
use num_traits::Zero;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalAlgebraicError, CausalCellId, CausalChain, ComparativeMultiplicity, EventId,
    EventSuccessor, ExactEventLaw, GradedCausalComplex, LogicalResourceReceipt,
    ReceiverConicSpecies, ReceiverPhaseAtlasError, ReceiverPhaseAtlasEvent, ReceiverPhaseAtlasLaw,
    ReceiverPhaseAtlasStanding, ReceiverPhaseConnectionId, ReceiverPhaseCycleId,
    ReceiverPhaseGermId, ReceiverPhaseSectionId, ReceiverPhaseSectionOccurrence,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ReceiverGrainId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HolonicCellAddress {
    pub grain: ReceiverGrainId,
    pub cell: CausalCellId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HolonicQuotientId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct HolonicOverlapId(pub u64);

/// Topology of one analytical conic section carried inside a receiver-visible
/// germ.  This is derived from the exact homogeneous quadratic; it is not a
/// display primitive.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum InternalAnalyticTopology {
    ClosedLoop,
    OpenPath,
    TwoOpenPaths,
    IntersectingOpenPaths,
    ParallelOpenPaths,
    SingularSection,
}

impl From<ReceiverConicSpecies> for InternalAnalyticTopology {
    fn from(species: ReceiverConicSpecies) -> Self {
        match species {
            ReceiverConicSpecies::Circle | ReceiverConicSpecies::Ellipse => Self::ClosedLoop,
            ReceiverConicSpecies::Parabola => Self::OpenPath,
            ReceiverConicSpecies::Hyperbola => Self::TwoOpenPaths,
            ReceiverConicSpecies::IntersectingLinePair => Self::IntersectingOpenPaths,
            ReceiverConicSpecies::ParallelLinePair => Self::ParallelOpenPaths,
            ReceiverConicSpecies::Degenerate => Self::SingularSection,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct InternalAnalyticSection {
    pub coordinate: u8,
    pub topology: InternalAnalyticTopology,
}

/// The source testimony retained by one incidence cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HolonicCellWitness {
    /// One coarse point carrying one or more native conic sections internally.
    PhaseGerm {
        germ: ReceiverPhaseGermId,
        internal_sections: Vec<InternalAnalyticSection>,
    },
    /// One exact directed connection between two phase germs.
    PhaseTransport {
        connection: ReceiverPhaseConnectionId,
    },
    /// One closed transported circuit and its exact path-ordered holonomy.
    PhaseClosure { cycle: ReceiverPhaseCycleId },
    /// One complete lower-grain closed hull received as a point here.
    QuotientedComplex { quotient: HolonicQuotientId },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGrainComplex {
    pub schema: String,
    pub incidence: GradedCausalComplex,
    pub witnesses: BTreeMap<CausalCellId, HolonicCellWitness>,
}

impl Default for ReceiverGrainComplex {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.receiver-grain-complex.v1".to_owned(),
            incidence: GradedCausalComplex::default(),
            witnesses: BTreeMap::new(),
        }
    }
}

impl ReceiverGrainComplex {
    /// Sparse exact coboundary of one basis cochain.  It is the transpose of
    /// the stored oriented boundary incidence and therefore does not allocate
    /// a dense matrix over a large receiver ecology.
    pub fn coboundary(&self, cell: CausalCellId) -> Result<CausalChain, HolonicComplexError> {
        self.incidence.cell(cell)?;
        let mut result = CausalChain::default();
        for (upper, body) in self.incidence.cells() {
            if let Some(coefficient) = body.boundary.coefficients().get(&cell) {
                result.add_term(*upper, coefficient.clone());
            }
        }
        Ok(result)
    }
}

/// A complete lower-grain closure received as one point at another grain.
///
/// The lower cells are not erased.  The quotient preserves both the complete
/// closed hull and its coarser receiver address.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolonicQuotient {
    pub id: HolonicQuotientId,
    pub caused_by: EventId,
    pub source_apex: HolonicCellAddress,
    pub source_closed_hull: BTreeSet<CausalCellId>,
    pub target: HolonicCellAddress,
}

/// One actual lower-grain occurrence shared by several promoted complexes.
/// Three or more members remain one incidence; no pairwise clique is
/// fabricated.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolonicOverlapCell {
    pub id: HolonicOverlapId,
    pub caused_by: EventId,
    pub occurrence: HolonicCellAddress,
    pub members: Vec<HolonicCellAddress>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHolonicComplexStanding {
    pub schema: String,
    pub phase_atlas: ReceiverPhaseAtlasStanding,
    pub grains: BTreeMap<ReceiverGrainId, ReceiverGrainComplex>,
    pub phase_germ_cells: BTreeMap<ReceiverPhaseGermId, HolonicCellAddress>,
    pub phase_connection_cells: BTreeMap<ReceiverPhaseConnectionId, HolonicCellAddress>,
    pub phase_cycle_cells: BTreeMap<ReceiverPhaseCycleId, HolonicCellAddress>,
    pub quotients: BTreeMap<HolonicQuotientId, HolonicQuotient>,
    pub quotient_by_cycle: BTreeMap<ReceiverPhaseCycleId, HolonicQuotientId>,
    pub overlaps: BTreeMap<HolonicOverlapId, HolonicOverlapCell>,
    next_quotient: u64,
    next_overlap: u64,
}

impl Default for ReceiverHolonicComplexStanding {
    fn default() -> Self {
        Self {
            schema: "holonic-engine.receiver-holonic-complex-standing.v1".to_owned(),
            phase_atlas: ReceiverPhaseAtlasStanding::default(),
            grains: BTreeMap::from([(ReceiverGrainId(0), ReceiverGrainComplex::default())]),
            phase_germ_cells: BTreeMap::new(),
            phase_connection_cells: BTreeMap::new(),
            phase_cycle_cells: BTreeMap::new(),
            quotients: BTreeMap::new(),
            quotient_by_cycle: BTreeMap::new(),
            overlaps: BTreeMap::new(),
            next_quotient: 1,
            next_overlap: 1,
        }
    }
}

impl ReceiverHolonicComplexStanding {
    pub fn grain(
        &self,
        grain: ReceiverGrainId,
    ) -> Result<&ReceiverGrainComplex, HolonicComplexError> {
        self.grains
            .get(&grain)
            .ok_or(HolonicComplexError::MissingGrain(grain))
    }

    pub fn validate(&self) -> Result<(), HolonicComplexError> {
        validate_standing(self)
    }

    fn promote_closed_hull(
        &mut self,
        source_apex: HolonicCellAddress,
        target_grain: ReceiverGrainId,
        caused_by: EventId,
        name: String,
    ) -> Result<HolonicQuotientId, HolonicComplexError> {
        if target_grain <= source_apex.grain {
            return Err(HolonicComplexError::NoncoarseningQuotient {
                source_grain: source_apex.grain,
                target_grain,
            });
        }
        let source_closed_hull = self
            .grain(source_apex.grain)?
            .incidence
            .closed_hull([source_apex.cell])?;
        let quotient = HolonicQuotientId(self.next_quotient);
        self.next_quotient = self
            .next_quotient
            .checked_add(1)
            .ok_or(HolonicComplexError::CarrierOverflow)?;
        let target_body = self.grains.entry(target_grain).or_default();
        let target_cell = target_body.incidence.found_cell(
            name,
            BTreeSet::from([caused_by]),
            0,
            CausalChain::default(),
        )?;
        target_body.witnesses.insert(
            target_cell,
            HolonicCellWitness::QuotientedComplex { quotient },
        );
        self.quotients.insert(
            quotient,
            HolonicQuotient {
                id: quotient,
                caused_by,
                source_apex,
                source_closed_hull,
                target: HolonicCellAddress {
                    grain: target_grain,
                    cell: target_cell,
                },
            },
        );
        Ok(quotient)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHolonicComplexEvent {
    pub event: EventId,
    pub chronology: u64,
    pub sections: Vec<ReceiverPhaseSectionOccurrence>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum HolonicCausalLayerKind {
    ReceiveAnalyticGerms,
    AdmitTransportConnections,
    CloseHolonomyCircuits,
    PromoteClosedComplexes,
    AssembleActualOverlaps,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolonicCausalLayerReceipt {
    pub order: u8,
    pub kind: HolonicCausalLayerKind,
    pub caused_cells: Vec<HolonicCellAddress>,
    pub caused_quotients: Vec<HolonicQuotientId>,
    pub caused_overlaps: Vec<HolonicOverlapId>,
}

impl HolonicCausalLayerReceipt {
    pub fn population(&self) -> usize {
        // A quotient and its target address are two receipts for one caused
        // promotion, not two causal events.
        self.caused_cells
            .len()
            .max(self.caused_quotients.len())
            .max(self.caused_overlaps.len())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHolonicComplexRadiation {
    pub schema: String,
    pub event: EventId,
    pub phase_sections: Vec<ReceiverPhaseSectionId>,
    pub caused_phase_germs: BTreeMap<ReceiverPhaseGermId, HolonicCellAddress>,
    pub caused_phase_connections: BTreeMap<ReceiverPhaseConnectionId, HolonicCellAddress>,
    pub caused_phase_cycles: BTreeMap<ReceiverPhaseCycleId, HolonicCellAddress>,
    pub caused_quotients: Vec<HolonicQuotientId>,
    pub caused_overlaps: Vec<HolonicOverlapId>,
    pub causal_layers: Vec<HolonicCausalLayerReceipt>,
}

#[derive(Clone, Debug, Default)]
pub struct ReceiverHolonicComplexLaw {
    phase_law: ReceiverPhaseAtlasLaw,
}

impl ReceiverHolonicComplexLaw {
    pub fn initial_standing(&self) -> ReceiverHolonicComplexStanding {
        ReceiverHolonicComplexStanding::default()
    }
}

impl ExactEventLaw for ReceiverHolonicComplexLaw {
    type Standing = ReceiverHolonicComplexStanding;
    type Event = ReceiverHolonicComplexEvent;
    type Radiation = ReceiverHolonicComplexRadiation;
    type Error = HolonicComplexError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        validate_standing(standing_before)?;
        let mut standing_after = standing_before.clone();
        let phase_successor = self.phase_law.enact(
            &standing_before.phase_atlas,
            &ReceiverPhaseAtlasEvent {
                event: event.event,
                chronology: event.chronology,
                sections: event.sections.clone(),
            },
        )?;
        let phase_radiation = phase_successor
            .radiation
            .first()
            .ok_or(HolonicComplexError::MissingPhaseRadiation)?
            .clone();
        standing_after.phase_atlas = phase_successor.standing_after;

        let caused_phase_germs = lift_phase_germs(&mut standing_after, event.event)?;
        let caused_phase_connections = lift_phase_connections(&mut standing_after, event.event)?;
        let caused_phase_cycles = lift_phase_cycles(&mut standing_after, event.event)?;
        let caused_quotients = promote_phase_cycles(
            &mut standing_after,
            event.event,
            caused_phase_cycles.keys().copied(),
        )?;
        let caused_overlaps =
            assemble_actual_overlaps(&mut standing_after, event.event, &caused_quotients)?;

        let causal_layers = causal_layers(
            &caused_phase_germs,
            &caused_phase_connections,
            &caused_phase_cycles,
            &caused_quotients,
            &caused_overlaps,
            &standing_after,
        )?;
        validate_standing(&standing_after)?;
        let logical_resources = logical_resources(&causal_layers);
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![ReceiverHolonicComplexRadiation {
                schema: "holonic-engine.receiver-holonic-complex-radiation.v1".to_owned(),
                event: event.event,
                phase_sections: phase_radiation.sections,
                caused_phase_germs,
                caused_phase_connections,
                caused_phase_cycles,
                caused_quotients,
                caused_overlaps,
                causal_layers,
            }],
            logical_resources: Some(logical_resources),
            physical_resources: None,
        })
    }
}

fn lift_phase_germs(
    standing: &mut ReceiverHolonicComplexStanding,
    event: EventId,
) -> Result<BTreeMap<ReceiverPhaseGermId, HolonicCellAddress>, HolonicComplexError> {
    let germs = standing
        .phase_atlas
        .germs
        .values()
        .filter(|germ| germ.source_event == event)
        .cloned()
        .collect::<Vec<_>>();
    let grain_id = ReceiverGrainId(0);
    let grain = standing.grains.entry(grain_id).or_default();
    let mut caused = BTreeMap::new();
    for germ in germs {
        let internal_sections = germ
            .level_sets
            .iter()
            .enumerate()
            .filter_map(|(coordinate, conic)| {
                conic.as_ref().map(|conic| InternalAnalyticSection {
                    coordinate: u8::try_from(coordinate).expect("three phase coordinates fit u8"),
                    topology: ReceiverConicSpecies::from(conic.classify()).into(),
                })
            })
            .collect();
        let cell = grain.incidence.found_cell(
            format!("phase-germ-{}", germ.id.0),
            BTreeSet::from([event]),
            0,
            CausalChain::default(),
        )?;
        grain.witnesses.insert(
            cell,
            HolonicCellWitness::PhaseGerm {
                germ: germ.id,
                internal_sections,
            },
        );
        let address = HolonicCellAddress {
            grain: grain_id,
            cell,
        };
        standing.phase_germ_cells.insert(germ.id, address);
        caused.insert(germ.id, address);
    }
    Ok(caused)
}

fn lift_phase_connections(
    standing: &mut ReceiverHolonicComplexStanding,
    event: EventId,
) -> Result<BTreeMap<ReceiverPhaseConnectionId, HolonicCellAddress>, HolonicComplexError> {
    let connections = standing
        .phase_atlas
        .connections
        .values()
        .filter(|connection| connection.source_event == event)
        .cloned()
        .collect::<Vec<_>>();
    let grain_id = ReceiverGrainId(0);
    let mut caused = BTreeMap::new();
    for connection in connections {
        let source = standing
            .phase_germ_cells
            .get(&connection.source)
            .copied()
            .ok_or(HolonicComplexError::MissingPhaseGermCell(connection.source))?;
        let target = standing
            .phase_germ_cells
            .get(&connection.target)
            .copied()
            .ok_or(HolonicComplexError::MissingPhaseGermCell(connection.target))?;
        if source.grain != grain_id || target.grain != grain_id {
            return Err(HolonicComplexError::MalformedStanding);
        }
        let mut boundary = CausalChain::default();
        boundary.add_term(source.cell, ComparativeMultiplicity::negative(1_u8));
        boundary.add_term(target.cell, ComparativeMultiplicity::positive(1_u8));
        let grain = standing
            .grains
            .get_mut(&grain_id)
            .ok_or(HolonicComplexError::MissingGrain(grain_id))?;
        let cell = grain.incidence.found_cell(
            format!("phase-transport-{}", connection.id.0),
            BTreeSet::from([event]),
            1,
            boundary,
        )?;
        grain.witnesses.insert(
            cell,
            HolonicCellWitness::PhaseTransport {
                connection: connection.id,
            },
        );
        let address = HolonicCellAddress {
            grain: grain_id,
            cell,
        };
        standing
            .phase_connection_cells
            .insert(connection.id, address);
        caused.insert(connection.id, address);
    }
    Ok(caused)
}

fn lift_phase_cycles(
    standing: &mut ReceiverHolonicComplexStanding,
    event: EventId,
) -> Result<BTreeMap<ReceiverPhaseCycleId, HolonicCellAddress>, HolonicComplexError> {
    let cycles = standing
        .phase_atlas
        .cycles
        .values()
        .filter(|cycle| cycle.source_event == event)
        .cloned()
        .collect::<Vec<_>>();
    let grain_id = ReceiverGrainId(0);
    let mut caused = BTreeMap::new();
    for cycle in cycles {
        let mut boundary = CausalChain::default();
        for connection in cycle.connections {
            let address = standing
                .phase_connection_cells
                .get(&connection)
                .copied()
                .ok_or(HolonicComplexError::MissingPhaseConnectionCell(connection))?;
            if address.grain != grain_id {
                return Err(HolonicComplexError::MalformedStanding);
            }
            boundary.add_term(address.cell, ComparativeMultiplicity::positive(1_u8));
        }
        let grain = standing
            .grains
            .get_mut(&grain_id)
            .ok_or(HolonicComplexError::MissingGrain(grain_id))?;
        let cell = grain.incidence.found_cell(
            format!("phase-closure-{}", cycle.id.0),
            BTreeSet::from([event]),
            2,
            boundary,
        )?;
        grain
            .witnesses
            .insert(cell, HolonicCellWitness::PhaseClosure { cycle: cycle.id });
        let address = HolonicCellAddress {
            grain: grain_id,
            cell,
        };
        standing.phase_cycle_cells.insert(cycle.id, address);
        caused.insert(cycle.id, address);
    }
    Ok(caused)
}

fn promote_phase_cycles(
    standing: &mut ReceiverHolonicComplexStanding,
    event: EventId,
    cycles: impl IntoIterator<Item = ReceiverPhaseCycleId>,
) -> Result<Vec<HolonicQuotientId>, HolonicComplexError> {
    let mut caused = Vec::new();
    for cycle in cycles {
        let source_apex = standing
            .phase_cycle_cells
            .get(&cycle)
            .copied()
            .ok_or(HolonicComplexError::MissingPhaseCycleCell(cycle))?;
        let quotient = standing.promote_closed_hull(
            source_apex,
            ReceiverGrainId(
                source_apex
                    .grain
                    .0
                    .checked_add(1)
                    .ok_or(HolonicComplexError::CarrierOverflow)?,
            ),
            event,
            format!("received-phase-complex-{}", cycle.0),
        )?;
        standing.quotient_by_cycle.insert(cycle, quotient);
        caused.push(quotient);
    }
    Ok(caused)
}

fn assemble_actual_overlaps(
    standing: &mut ReceiverHolonicComplexStanding,
    event: EventId,
    caused_quotients: &[HolonicQuotientId],
) -> Result<Vec<HolonicOverlapId>, HolonicComplexError> {
    let mut memberships = BTreeMap::<HolonicCellAddress, BTreeSet<HolonicCellAddress>>::new();
    for quotient_id in caused_quotients {
        let quotient = standing
            .quotients
            .get(quotient_id)
            .ok_or(HolonicComplexError::MissingQuotient(*quotient_id))?;
        for lower_cell in &quotient.source_closed_hull {
            memberships
                .entry(HolonicCellAddress {
                    grain: quotient.source_apex.grain,
                    cell: *lower_cell,
                })
                .or_default()
                .insert(quotient.target);
        }
    }
    let mut caused = Vec::new();
    for (occurrence, members) in memberships {
        if members.len() < 2 {
            continue;
        }
        let members = members.into_iter().collect::<Vec<_>>();
        if standing
            .overlaps
            .values()
            .any(|cell| cell.occurrence == occurrence && cell.members == members)
        {
            continue;
        }
        let id = HolonicOverlapId(standing.next_overlap);
        standing.next_overlap = standing
            .next_overlap
            .checked_add(1)
            .ok_or(HolonicComplexError::CarrierOverflow)?;
        standing.overlaps.insert(
            id,
            HolonicOverlapCell {
                id,
                caused_by: event,
                occurrence,
                members,
            },
        );
        caused.push(id);
    }
    Ok(caused)
}

fn causal_layers(
    germs: &BTreeMap<ReceiverPhaseGermId, HolonicCellAddress>,
    connections: &BTreeMap<ReceiverPhaseConnectionId, HolonicCellAddress>,
    cycles: &BTreeMap<ReceiverPhaseCycleId, HolonicCellAddress>,
    quotients: &[HolonicQuotientId],
    overlaps: &[HolonicOverlapId],
    standing: &ReceiverHolonicComplexStanding,
) -> Result<Vec<HolonicCausalLayerReceipt>, HolonicComplexError> {
    let quotient_cells = quotients
        .iter()
        .map(|id| {
            standing
                .quotients
                .get(id)
                .map(|quotient| quotient.target)
                .ok_or(HolonicComplexError::MissingQuotient(*id))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let candidates = [
        HolonicCausalLayerReceipt {
            order: 0,
            kind: HolonicCausalLayerKind::ReceiveAnalyticGerms,
            caused_cells: germs.values().copied().collect(),
            caused_quotients: Vec::new(),
            caused_overlaps: Vec::new(),
        },
        HolonicCausalLayerReceipt {
            order: 1,
            kind: HolonicCausalLayerKind::AdmitTransportConnections,
            caused_cells: connections.values().copied().collect(),
            caused_quotients: Vec::new(),
            caused_overlaps: Vec::new(),
        },
        HolonicCausalLayerReceipt {
            order: 2,
            kind: HolonicCausalLayerKind::CloseHolonomyCircuits,
            caused_cells: cycles.values().copied().collect(),
            caused_quotients: Vec::new(),
            caused_overlaps: Vec::new(),
        },
        HolonicCausalLayerReceipt {
            order: 3,
            kind: HolonicCausalLayerKind::PromoteClosedComplexes,
            caused_cells: quotient_cells,
            caused_quotients: quotients.to_vec(),
            caused_overlaps: Vec::new(),
        },
        HolonicCausalLayerReceipt {
            order: 4,
            kind: HolonicCausalLayerKind::AssembleActualOverlaps,
            caused_cells: Vec::new(),
            caused_quotients: Vec::new(),
            caused_overlaps: overlaps.to_vec(),
        },
    ];
    Ok(candidates
        .into_iter()
        .filter(|layer| layer.population() != 0)
        .collect())
}

fn logical_resources(layers: &[HolonicCausalLayerReceipt]) -> LogicalResourceReceipt {
    let mut events_by_law = BTreeMap::<String, BigUint>::new();
    let mut work = BigUint::zero();
    let mut exposed_parallel_width = BigUint::zero();
    for layer in layers {
        let population = BigUint::from(layer.population());
        work += &population;
        exposed_parallel_width = exposed_parallel_width.max(population.clone());
        events_by_law.insert(format!("{:?}", layer.kind), population);
    }
    LogicalResourceReceipt {
        schema: "holonic-engine.logical-resource-receipt.v1".to_owned(),
        work,
        causal_span: BigUint::from(layers.len()),
        exposed_parallel_width,
        events_by_law,
    }
}

fn validate_standing(standing: &ReceiverHolonicComplexStanding) -> Result<(), HolonicComplexError> {
    if standing.schema != "holonic-engine.receiver-holonic-complex-standing.v1"
        || !standing.grains.contains_key(&ReceiverGrainId(0))
    {
        return Err(HolonicComplexError::MalformedStanding);
    }
    standing.phase_atlas.validate()?;
    for grain in standing.grains.values() {
        if grain.schema != "holonic-engine.receiver-grain-complex.v1" {
            return Err(HolonicComplexError::MalformedStanding);
        }
        grain.incidence.validate()?;
        let cells = grain
            .incidence
            .cells()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>();
        let witnesses = grain.witnesses.keys().copied().collect::<BTreeSet<_>>();
        if cells != witnesses {
            return Err(HolonicComplexError::MalformedStanding);
        }
        for (cell, witness) in &grain.witnesses {
            let grade = grain.incidence.cell(*cell)?.grade;
            let expected = match witness {
                HolonicCellWitness::PhaseGerm { .. }
                | HolonicCellWitness::QuotientedComplex { .. } => 0,
                HolonicCellWitness::PhaseTransport { .. } => 1,
                HolonicCellWitness::PhaseClosure { .. } => 2,
            };
            if grade != expected {
                return Err(HolonicComplexError::MalformedStanding);
            }
        }
    }
    validate_phase_maps(standing)?;
    if standing.quotient_by_cycle.len() != standing.phase_cycle_cells.len()
        || standing.quotients.len() != standing.quotient_by_cycle.len()
    {
        return Err(HolonicComplexError::MalformedStanding);
    }
    for (id, quotient) in &standing.quotients {
        if *id != quotient.id
            || quotient.target.grain <= quotient.source_apex.grain
            || !standing
                .grain(quotient.source_apex.grain)?
                .incidence
                .is_closed_support(&quotient.source_closed_hull)?
            || standing
                .grain(quotient.source_apex.grain)?
                .incidence
                .closed_hull([quotient.source_apex.cell])?
                != quotient.source_closed_hull
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
        let target = standing
            .grain(quotient.target.grain)?
            .witnesses
            .get(&quotient.target.cell);
        let target_cell = standing
            .grain(quotient.target.grain)?
            .incidence
            .cell(quotient.target.cell)?;
        if target
            != Some(&HolonicCellWitness::QuotientedComplex {
                quotient: quotient.id,
            })
            || target_cell.source_events != BTreeSet::from([quotient.caused_by])
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
    }
    for (cycle, quotient) in &standing.quotient_by_cycle {
        let source = standing
            .phase_cycle_cells
            .get(cycle)
            .ok_or(HolonicComplexError::MalformedStanding)?;
        if standing
            .quotients
            .get(quotient)
            .is_none_or(|body| body.source_apex != *source)
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
    }
    for (id, overlap) in &standing.overlaps {
        if *id != overlap.id
            || overlap.members.len() < 2
            || overlap.members.windows(2).any(|pair| pair[0] >= pair[1])
            || overlap
                .members
                .iter()
                .any(|member| member.grain <= overlap.occurrence.grain)
            || overlap
                .members
                .iter()
                .map(|member| member.grain)
                .collect::<BTreeSet<_>>()
                .len()
                != 1
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
        for member in &overlap.members {
            let Some(quotient) = standing
                .quotients
                .values()
                .find(|quotient| quotient.target == *member)
            else {
                return Err(HolonicComplexError::MalformedStanding);
            };
            if quotient.source_apex.grain != overlap.occurrence.grain
                || !quotient
                    .source_closed_hull
                    .contains(&overlap.occurrence.cell)
            {
                return Err(HolonicComplexError::MalformedStanding);
            }
        }
    }
    if standing
        .quotients
        .keys()
        .next_back()
        .is_some_and(|id| id.0 >= standing.next_quotient)
        || standing
            .overlaps
            .keys()
            .next_back()
            .is_some_and(|id| id.0 >= standing.next_overlap)
    {
        return Err(HolonicComplexError::MalformedStanding);
    }
    Ok(())
}

fn validate_phase_maps(
    standing: &ReceiverHolonicComplexStanding,
) -> Result<(), HolonicComplexError> {
    if standing.phase_germ_cells.len() != standing.phase_atlas.germs.len()
        || standing.phase_connection_cells.len() != standing.phase_atlas.connections.len()
        || standing.phase_cycle_cells.len() != standing.phase_atlas.cycles.len()
    {
        return Err(HolonicComplexError::MalformedStanding);
    }
    for (germ, address) in &standing.phase_germ_cells {
        let Some(phase_germ) = standing.phase_atlas.germs.get(germ) else {
            return Err(HolonicComplexError::MalformedStanding);
        };
        let grain = standing.grain(address.grain)?;
        let cell = grain.incidence.cell(address.cell)?;
        if address.grain != ReceiverGrainId(0)
            || cell.source_events != BTreeSet::from([phase_germ.source_event])
            || grain.witnesses.get(&address.cell)
                != Some(&HolonicCellWitness::PhaseGerm {
                    germ: *germ,
                    internal_sections: phase_germ
                        .level_sets
                        .iter()
                        .enumerate()
                        .filter_map(|(coordinate, conic)| {
                            conic.as_ref().map(|conic| InternalAnalyticSection {
                                coordinate: u8::try_from(coordinate)
                                    .expect("three phase coordinates fit u8"),
                                topology: ReceiverConicSpecies::from(conic.classify()).into(),
                            })
                        })
                        .collect(),
                })
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
    }
    for (connection, address) in &standing.phase_connection_cells {
        let Some(phase_connection) = standing.phase_atlas.connections.get(connection) else {
            return Err(HolonicComplexError::MalformedStanding);
        };
        let source = standing
            .phase_germ_cells
            .get(&phase_connection.source)
            .ok_or(HolonicComplexError::MalformedStanding)?;
        let target = standing
            .phase_germ_cells
            .get(&phase_connection.target)
            .ok_or(HolonicComplexError::MalformedStanding)?;
        let mut expected_boundary = CausalChain::default();
        expected_boundary.add_term(source.cell, ComparativeMultiplicity::negative(1_u8));
        expected_boundary.add_term(target.cell, ComparativeMultiplicity::positive(1_u8));
        let grain = standing.grain(address.grain)?;
        let cell = grain.incidence.cell(address.cell)?;
        if address.grain != ReceiverGrainId(0)
            || source.grain != address.grain
            || target.grain != address.grain
            || cell.source_events != BTreeSet::from([phase_connection.source_event])
            || cell.boundary != expected_boundary
            || grain.witnesses.get(&address.cell)
                != Some(&HolonicCellWitness::PhaseTransport {
                    connection: *connection,
                })
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
    }
    for (cycle, address) in &standing.phase_cycle_cells {
        let Some(phase_cycle) = standing.phase_atlas.cycles.get(cycle) else {
            return Err(HolonicComplexError::MalformedStanding);
        };
        let connections = phase_cycle
            .connections
            .iter()
            .map(|connection| {
                standing
                    .phase_connection_cells
                    .get(connection)
                    .copied()
                    .ok_or(HolonicComplexError::MalformedStanding)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if connections
            .iter()
            .any(|connection| connection.grain != address.grain)
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
        let mut expected_boundary = CausalChain::default();
        for connection in connections {
            expected_boundary.add_term(connection.cell, ComparativeMultiplicity::positive(1_u8));
        }
        let grain = standing.grain(address.grain)?;
        let cell = grain.incidence.cell(address.cell)?;
        if address.grain != ReceiverGrainId(0)
            || cell.source_events != BTreeSet::from([phase_cycle.source_event])
            || cell.boundary != expected_boundary
            || grain.witnesses.get(&address.cell)
                != Some(&HolonicCellWitness::PhaseClosure { cycle: *cycle })
        {
            return Err(HolonicComplexError::MalformedStanding);
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum HolonicComplexError {
    #[error("receiver grain {0:?} is absent")]
    MissingGrain(ReceiverGrainId),
    #[error("phase germ {0:?} has no receiver-complex cell")]
    MissingPhaseGermCell(ReceiverPhaseGermId),
    #[error("phase connection {0:?} has no receiver-complex cell")]
    MissingPhaseConnectionCell(ReceiverPhaseConnectionId),
    #[error("phase cycle {0:?} has no receiver-complex cell")]
    MissingPhaseCycleCell(ReceiverPhaseCycleId),
    #[error("holonic quotient {0:?} is absent")]
    MissingQuotient(HolonicQuotientId),
    #[error("the receiver-phase law emitted no radiation")]
    MissingPhaseRadiation,
    #[error(
        "a quotient from {source_grain:?} to {target_grain:?} does not coarsen its receiver grain"
    )]
    NoncoarseningQuotient {
        source_grain: ReceiverGrainId,
        target_grain: ReceiverGrainId,
    },
    #[error("the receiver holonic complex standing is malformed")]
    MalformedStanding,
    #[error("a receiver holonic complex carrier overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    Algebraic(#[from] CausalAlgebraicError),
    #[error(transparent)]
    Phase(#[from] ReceiverPhaseAtlasError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::{RatVec3, ReceiverId};

    use super::*;
    use crate::{CausalWorld, ExactRgb, ImageExtent, RayFamily};

    fn rays() -> RayFamily {
        RayFamily::Central {
            center: RatVec3::zero(),
            forward: RatVec3::from_i64(0, 0, 1),
            horizontal: RatVec3::from_i64(1, 0, 0),
            vertical: RatVec3::from_i64(0, 1, 0),
        }
    }

    fn textured_section(lineage: u64) -> ReceiverPhaseSectionOccurrence {
        let extent = ImageExtent {
            width: 33,
            height: 33,
        };
        let samples = (0..extent.height)
            .flat_map(|row| {
                (0..extent.width).map(move |column| {
                    let x = column.wrapping_mul(column.wrapping_add(3));
                    let y = row.wrapping_mul(row.wrapping_add(5));
                    let cross = column.wrapping_mul(row);
                    Some(ExactRgb {
                        red: u8::try_from((x + 3 * y + cross) % 251).unwrap(),
                        green: u8::try_from((5 * x + y + 7 * cross) % 253).unwrap(),
                        blue: u8::try_from((3 * x + 11 * y + 2 * cross) % 247).unwrap(),
                    })
                })
            })
            .collect();
        ReceiverPhaseSectionOccurrence::from_rgb(
            None,
            lineage,
            ReceiverId(lineage),
            rays(),
            extent,
            samples,
        )
    }

    #[test]
    fn phase_pixels_remain_testimony_while_analytic_germs_become_cells() {
        let law = ReceiverHolonicComplexLaw::default();
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&ReceiverHolonicComplexEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![textured_section(1)],
            })
            .unwrap();
        let standing = world.standing();
        standing.validate().unwrap();
        assert!(!standing.phase_atlas.germs.is_empty());
        assert_eq!(
            standing
                .grain(ReceiverGrainId(0))
                .unwrap()
                .incidence
                .f_vector()[&0],
            standing.phase_atlas.germs.len()
        );
        assert!(
            standing
                .grain(ReceiverGrainId(0))
                .unwrap()
                .witnesses
                .values()
                .filter_map(|witness| match witness {
                    HolonicCellWitness::PhaseGerm {
                        internal_sections, ..
                    } => Some(internal_sections),
                    _ => None,
                })
                .all(|sections| !sections.is_empty())
        );
    }

    #[test]
    fn complete_nested_standing_rests_and_remounts_exactly() {
        let law = ReceiverHolonicComplexLaw::default();
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        world
            .receive(&ReceiverHolonicComplexEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![textured_section(1)],
            })
            .unwrap();
        let encoded = ron::ser::to_string(world.standing()).unwrap();
        let remounted: ReceiverHolonicComplexStanding = ron::from_str(&encoded).unwrap();
        assert_eq!(&remounted, world.standing());
        remounted.validate().unwrap();
    }

    #[test]
    fn oriented_transport_cycle_has_zero_second_boundary() {
        let event = EventId(1);
        let mut grain = ReceiverGrainComplex::default();
        let vertices = (0..3)
            .map(|index| {
                let cell = grain
                    .incidence
                    .found_cell(
                        format!("v{index}"),
                        BTreeSet::from([event]),
                        0,
                        CausalChain::default(),
                    )
                    .unwrap();
                grain.witnesses.insert(
                    cell,
                    HolonicCellWitness::PhaseGerm {
                        germ: ReceiverPhaseGermId(index + 1),
                        internal_sections: Vec::new(),
                    },
                );
                cell
            })
            .collect::<Vec<_>>();
        let edges = [(0, 1), (1, 2), (2, 0)]
            .into_iter()
            .enumerate()
            .map(|(index, (source, target))| {
                let mut boundary = CausalChain::default();
                boundary.add_term(vertices[source], ComparativeMultiplicity::negative(1_u8));
                boundary.add_term(vertices[target], ComparativeMultiplicity::positive(1_u8));
                let cell = grain
                    .incidence
                    .found_cell(format!("e{index}"), BTreeSet::from([event]), 1, boundary)
                    .unwrap();
                grain.witnesses.insert(
                    cell,
                    HolonicCellWitness::PhaseTransport {
                        connection: ReceiverPhaseConnectionId(index as u64 + 1),
                    },
                );
                cell
            })
            .collect::<Vec<_>>();
        let mut boundary = CausalChain::default();
        for edge in edges {
            boundary.add_term(edge, ComparativeMultiplicity::positive(1_u8));
        }
        let face = grain
            .incidence
            .found_cell("cycle", BTreeSet::from([event]), 2, boundary.clone())
            .unwrap();
        assert!(
            grain
                .incidence
                .boundary_of_chain(&boundary)
                .unwrap()
                .difference_is_zero()
        );
        assert!(grain.coboundary(vertices[0]).unwrap().support().len() >= 2);
        assert_eq!(grain.incidence.cell(face).unwrap().grade, 2);
    }

    #[test]
    fn completed_lower_complex_returns_as_one_coarser_point() {
        let event = EventId(1);
        let mut standing = ReceiverHolonicComplexStanding::default();
        let simplex = standing
            .grains
            .get_mut(&ReceiverGrainId(0))
            .unwrap()
            .incidence
            .found_simplex("triangle", event, ["a", "b", "c"])
            .unwrap();
        let grain = standing.grains.get_mut(&ReceiverGrainId(0)).unwrap();
        for (cell, body) in grain.incidence.cells() {
            let witness = match body.grade {
                0 => HolonicCellWitness::PhaseGerm {
                    germ: ReceiverPhaseGermId(cell.0),
                    internal_sections: Vec::new(),
                },
                1 => HolonicCellWitness::PhaseTransport {
                    connection: ReceiverPhaseConnectionId(cell.0),
                },
                2 => HolonicCellWitness::PhaseClosure {
                    cycle: ReceiverPhaseCycleId(cell.0),
                },
                _ => unreachable!(),
            };
            grain.witnesses.insert(*cell, witness);
        }
        let quotient = standing
            .promote_closed_hull(
                HolonicCellAddress {
                    grain: ReceiverGrainId(0),
                    cell: simplex.apex,
                },
                ReceiverGrainId(1),
                event,
                "triangle received whole".to_owned(),
            )
            .unwrap();
        let body = &standing.quotients[&quotient];
        assert_eq!(body.source_closed_hull.len(), 7);
        assert_eq!(
            standing
                .grain(ReceiverGrainId(1))
                .unwrap()
                .incidence
                .f_vector()[&0],
            1
        );
    }

    #[test]
    fn shared_occurrence_remains_one_higher_overlap_not_a_pairwise_clique() {
        let event = EventId(1);
        let mut standing = ReceiverHolonicComplexStanding::default();
        let grain = standing.grains.get_mut(&ReceiverGrainId(0)).unwrap();
        let shared = grain
            .incidence
            .found_cell("shared", BTreeSet::from([event]), 0, CausalChain::default())
            .unwrap();
        grain.witnesses.insert(
            shared,
            HolonicCellWitness::PhaseGerm {
                germ: ReceiverPhaseGermId(1),
                internal_sections: Vec::new(),
            },
        );
        let mut faces = Vec::new();
        for ordinal in 0_u64..3 {
            let first = grain
                .incidence
                .found_cell(
                    format!("a{ordinal}"),
                    BTreeSet::from([event]),
                    0,
                    CausalChain::default(),
                )
                .unwrap();
            let second = grain
                .incidence
                .found_cell(
                    format!("b{ordinal}"),
                    BTreeSet::from([event]),
                    0,
                    CausalChain::default(),
                )
                .unwrap();
            for (index, vertex) in [first, second].into_iter().enumerate() {
                grain.witnesses.insert(
                    vertex,
                    HolonicCellWitness::PhaseGerm {
                        germ: ReceiverPhaseGermId(2 + ordinal * 2 + index as u64),
                        internal_sections: Vec::new(),
                    },
                );
            }
            let directed_vertices = [(shared, first), (first, second), (second, shared)];
            let mut face_boundary = CausalChain::default();
            for (edge_ordinal, (source, target)) in directed_vertices.into_iter().enumerate() {
                let mut edge_boundary = CausalChain::default();
                edge_boundary.add_term(source, ComparativeMultiplicity::negative(1_u8));
                edge_boundary.add_term(target, ComparativeMultiplicity::positive(1_u8));
                let edge = grain
                    .incidence
                    .found_cell(
                        format!("e{ordinal}-{edge_ordinal}"),
                        BTreeSet::from([event]),
                        1,
                        edge_boundary,
                    )
                    .unwrap();
                grain.witnesses.insert(
                    edge,
                    HolonicCellWitness::PhaseTransport {
                        connection: ReceiverPhaseConnectionId(
                            1 + ordinal * 3 + edge_ordinal as u64,
                        ),
                    },
                );
                face_boundary.add_term(edge, ComparativeMultiplicity::positive(1_u8));
            }
            let face = grain
                .incidence
                .found_cell(
                    format!("f{ordinal}"),
                    BTreeSet::from([event]),
                    2,
                    face_boundary,
                )
                .unwrap();
            grain.witnesses.insert(
                face,
                HolonicCellWitness::PhaseClosure {
                    cycle: ReceiverPhaseCycleId(ordinal + 1),
                },
            );
            faces.push(face);
        }
        let mut quotients = Vec::new();
        for face in faces {
            quotients.push(
                standing
                    .promote_closed_hull(
                        HolonicCellAddress {
                            grain: ReceiverGrainId(0),
                            cell: face,
                        },
                        ReceiverGrainId(1),
                        event,
                        "received triangle".to_owned(),
                    )
                    .unwrap(),
            );
        }
        let caused = assemble_actual_overlaps(&mut standing, event, &quotients).unwrap();
        assert_eq!(caused.len(), 1);
        let overlap = &standing.overlaps[&caused[0]];
        assert_eq!(overlap.occurrence.cell, shared);
        assert_eq!(overlap.members.len(), 3);
    }
}
