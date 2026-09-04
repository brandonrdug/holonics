//! Exact receiver-local analysis of graded holonic graph sections.
//!
//! This module is not a graph layout or a display scene.  It retains the
//! oriented boundary and its exact transpose, restricts a caused complex from
//! one receiver-local focus, and carries cross-grain quotient fibers without
//! turning a coarser point into an uninspectable scalar.  A later vector,
//! raster, or notation membrane may consume these receipts; it may not
//! redefine their incidence.

use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    sync::Arc,
};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::ReceiverId;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    CausalAlgebraicError, CausalAlgebraicPresentation, CausalCell, CausalCellId, CausalChain,
    CausalEnd, CausalEndId, CausalRegion, CausalRegionId, ComparativeMultiplicity, EventId,
    GradedCausalComplex, HolonicCellAddress, HolonicCellWitness, HolonicComplexError,
    HolonicOverlapCell, HolonicOverlapId, HolonicQuotient, HolonicQuotientId,
    InternalAnalyticTopology, LocalAlgebraId, LocalCoordinateAlgebra, ReceiverGrainId,
    ReceiverHolonicComplexRadiation, ReceiverHolonicComplexStanding, ReceiverPhaseConnection,
    ReceiverPhaseConnectionId, ReceiverPhaseCycle, ReceiverPhaseCycleId, ReceiverPhaseGerm,
    ReceiverPhaseGermId,
};

/// The exact boundary relation together with its sparse transpose.
///
/// The first mount derives the coboundary once from the complete supplied
/// complex.  Receiver-local queries subsequently follow this standing
/// incidence instead of scanning every possible coface.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactIncidenceAtlas {
    pub schema: String,
    incidence: GradedCausalComplex,
    coboundaries: BTreeMap<CausalCellId, CausalChain>,
}

impl ExactIncidenceAtlas {
    pub fn new(incidence: GradedCausalComplex) -> Result<Self, GraphReceiverError> {
        incidence.validate()?;
        let coboundaries = derive_coboundaries(&incidence);
        let result = Self {
            schema: "holonic-engine.exact-incidence-atlas.v1".to_owned(),
            incidence,
            coboundaries,
        };
        result.validate()?;
        Ok(result)
    }

    pub fn incidence(&self) -> &GradedCausalComplex {
        &self.incidence
    }

    pub fn coboundary(&self, cell: CausalCellId) -> Result<&CausalChain, GraphReceiverError> {
        self.incidence.cell(cell)?;
        self.coboundaries
            .get(&cell)
            .ok_or(GraphReceiverError::MissingCoboundary(cell))
    }

    pub fn cells(&self) -> &BTreeMap<CausalCellId, CausalCell> {
        self.incidence.cells()
    }

    pub fn validate(&self) -> Result<(), GraphReceiverError> {
        self.incidence.validate()?;
        let expected = derive_coboundaries(&self.incidence);
        if self.coboundaries != expected {
            return Err(GraphReceiverError::MalformedCoboundaryAtlas);
        }
        Ok(())
    }

    /// Restrict one boundary-closed receiver section.
    ///
    /// `upper_horizon` counts exact coboundary fronts from the supplied roots.
    /// Every selected coface brings its complete lower boundary with it.
    pub fn receive_section<I>(
        &self,
        roots: I,
        upper_horizon: u32,
    ) -> Result<SparseIncidenceSection, GraphReceiverError>
    where
        I: IntoIterator<Item = CausalCellId>,
    {
        let roots = roots.into_iter().collect::<BTreeSet<_>>();
        if roots.is_empty() {
            return Err(GraphReceiverError::EmptyReceiverRoots);
        }
        let root_count = roots.len();
        for root in &roots {
            self.incidence.cell(*root)?;
        }

        let mut selected = roots.clone();
        let mut frontier = roots;
        let mut dependencies = BTreeSet::new();
        let mut coboundary_terms = 0_u64;
        let mut traversed_fronts = 0_u32;

        for _ in 0..upper_horizon {
            let mut next = BTreeSet::new();
            for cell in frontier {
                dependencies.insert(cell);
                let coboundary = self.coboundary(cell)?;
                coboundary_terms = coboundary_terms
                    .checked_add(usize_to_u64(coboundary.coefficients().len())?)
                    .ok_or(GraphReceiverError::CarrierOverflow)?;
                for coface in coboundary.support() {
                    if selected.insert(coface) {
                        next.insert(coface);
                    }
                }
            }
            traversed_fronts = traversed_fronts
                .checked_add(1)
                .ok_or(GraphReceiverError::CarrierOverflow)?;
            if next.is_empty() {
                break;
            }
            frontier = next;
        }

        let selected_before_closure = selected.len();
        let support = self.incidence.closed_hull(selected)?;
        let closure_cells = support
            .len()
            .checked_sub(selected_before_closure)
            .ok_or(GraphReceiverError::CarrierOverflow)?;
        if !self.incidence.is_closed_support(&support)? {
            return Err(GraphReceiverError::ReceiverSectionNotClosed);
        }
        let dependency_count = dependencies.len();
        let returned_cells = support.len();

        Ok(SparseIncidenceSection {
            schema: "holonic-engine.sparse-incidence-section.v1".to_owned(),
            support,
            dependencies,
            work: ReceiverGraphQueryWork {
                roots: BigUint::from(root_count),
                traversed_fronts: BigUint::from(traversed_fronts),
                coboundary_lookups: BigUint::from(dependency_count),
                coboundary_terms: BigUint::from(coboundary_terms),
                closure_cells: BigUint::from(closure_cells),
                returned_cells: BigUint::from(returned_cells),
                reused_cells: BigUint::zero(),
                materialized_cells: BigUint::zero(),
            },
        })
    }

    fn append_cell(&mut self, cell: &CausalCell) -> Result<(), GraphReceiverError> {
        let received = self.incidence.found_cell(
            cell.name.clone(),
            cell.source_events.clone(),
            cell.grade,
            cell.boundary.clone(),
        )?;
        if received != cell.id {
            return Err(GraphReceiverError::NonappendOnlySourceCell {
                expected: received,
                received: cell.id,
            });
        }
        self.coboundaries.entry(received).or_default();
        for (lower, coefficient) in cell.boundary.coefficients() {
            self.coboundaries
                .entry(*lower)
                .or_default()
                .add_term(received, coefficient.clone());
        }
        Ok(())
    }
}

fn derive_coboundaries(incidence: &GradedCausalComplex) -> BTreeMap<CausalCellId, CausalChain> {
    let mut result = incidence
        .cells()
        .keys()
        .copied()
        .map(|cell| (cell, CausalChain::default()))
        .collect::<BTreeMap<_, _>>();
    for (upper, body) in incidence.cells() {
        for (lower, coefficient) in body.boundary.coefficients() {
            result
                .entry(*lower)
                .or_default()
                .add_term(*upper, coefficient.clone());
        }
    }
    result
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SparseIncidenceSection {
    pub schema: String,
    pub support: BTreeSet<CausalCellId>,
    /// Cells whose coboundaries were consulted while forming this horizon.
    /// A later source coface touching one of these cells may change the section.
    pub dependencies: BTreeSet<CausalCellId>,
    pub work: ReceiverGraphQueryWork,
}

#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphQueryWork {
    pub roots: BigUint,
    pub traversed_fronts: BigUint,
    pub coboundary_lookups: BigUint,
    pub coboundary_terms: BigUint,
    pub closure_cells: BigUint,
    pub returned_cells: BigUint,
    /// Exact cell carriers shared with the predecessor receiver section.
    pub reused_cells: BigUint,
    /// Exact cell carriers formed from source testimony for this successor.
    pub materialized_cells: BigUint,
}

/// Exact source material required by receiver-local graph analysis.
///
/// This is a droppable derived atlas over one `ReceiverHolonicComplexStanding`.
/// It is not another owner of source succession.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolonicGraphSourceAtlas {
    pub schema: String,
    grains: BTreeMap<ReceiverGrainId, ExactIncidenceAtlas>,
    /// Complete coordinate presentations retained at the grains which
    /// actually supplied them. The sparse incidence atlas accelerates
    /// traversal; it never replaces this algebraic source testimony.
    algebraic_presentations: BTreeMap<ReceiverGrainId, CausalAlgebraicPresentation>,
    witnesses: BTreeMap<HolonicCellAddress, ReceiverGraphSourceWitness>,
    quotients: BTreeMap<HolonicQuotientId, HolonicQuotient>,
    overlaps: BTreeMap<HolonicOverlapId, HolonicOverlapCell>,
    phase_germs: BTreeMap<ReceiverPhaseGermId, ReceiverPhaseGerm>,
    phase_connections: BTreeMap<ReceiverPhaseConnectionId, ReceiverPhaseConnection>,
    phase_cycles: BTreeMap<ReceiverPhaseCycleId, ReceiverPhaseCycle>,
    source_events: BTreeSet<EventId>,
    chronology: Option<u64>,
}

impl HolonicGraphSourceAtlas {
    pub fn mount(standing: &ReceiverHolonicComplexStanding) -> Result<Self, GraphReceiverError> {
        standing.validate()?;
        let grains = standing
            .grains
            .iter()
            .map(|(grain, body)| Ok((*grain, ExactIncidenceAtlas::new(body.incidence.clone())?)))
            .collect::<Result<BTreeMap<_, _>, GraphReceiverError>>()?;
        let witnesses = standing
            .grains
            .iter()
            .flat_map(|(grain, body)| {
                body.witnesses.iter().map(move |(cell, witness)| {
                    (
                        HolonicCellAddress {
                            grain: *grain,
                            cell: *cell,
                        },
                        ReceiverGraphSourceWitness::Holonic(witness.clone()),
                    )
                })
            })
            .collect();
        let result = Self {
            schema: "holonic-engine.holonic-graph-source-atlas.v1".to_owned(),
            grains,
            algebraic_presentations: BTreeMap::new(),
            witnesses,
            quotients: standing.quotients.clone(),
            overlaps: standing.overlaps.clone(),
            phase_germs: standing.phase_atlas.germs.clone(),
            phase_connections: standing.phase_atlas.connections.clone(),
            phase_cycles: standing.phase_atlas.cycles.clone(),
            source_events: standing.phase_atlas.used_events.clone(),
            chronology: standing.phase_atlas.last_chronology,
        };
        result.validate()?;
        Ok(result)
    }

    /// Mount arbitrary exact algebraic grains without fabricating phase
    /// semantics. Quotient targets retain their actual cross-grain witness;
    /// every other cell remains an explicitly algebraic source cell.
    pub fn from_algebraic_grains(
        grains: BTreeMap<ReceiverGrainId, GradedCausalComplex>,
        quotients: BTreeMap<HolonicQuotientId, HolonicQuotient>,
        overlaps: BTreeMap<HolonicOverlapId, HolonicOverlapCell>,
        chronology: Option<u64>,
    ) -> Result<Self, GraphReceiverError> {
        let grains = grains
            .into_iter()
            .map(|(grain, incidence)| Ok((grain, ExactIncidenceAtlas::new(incidence)?)))
            .collect::<Result<BTreeMap<_, _>, GraphReceiverError>>()?;
        let mut witnesses = grains
            .iter()
            .flat_map(|(grain, body)| {
                body.cells().keys().map(move |cell| {
                    (
                        HolonicCellAddress {
                            grain: *grain,
                            cell: *cell,
                        },
                        ReceiverGraphSourceWitness::Algebraic,
                    )
                })
            })
            .collect::<BTreeMap<_, _>>();
        for quotient in quotients.values() {
            witnesses.insert(
                quotient.target,
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::QuotientedComplex {
                    quotient: quotient.id,
                }),
            );
        }
        let source_events = grains
            .values()
            .flat_map(|grain| grain.cells().values())
            .flat_map(|cell| cell.source_events.iter().copied())
            .collect();
        let result = Self {
            schema: "holonic-engine.holonic-graph-source-atlas.v1".to_owned(),
            grains,
            algebraic_presentations: BTreeMap::new(),
            witnesses,
            quotients,
            overlaps,
            phase_germs: BTreeMap::new(),
            phase_connections: BTreeMap::new(),
            phase_cycles: BTreeMap::new(),
            source_events,
            chronology,
        };
        result.validate()?;
        Ok(result)
    }

    /// Mount complete causal algebraic presentations while deriving one
    /// sparse incidence index per receiver grain.
    ///
    /// The coordinate algebras, local regions, opposed ends, evolution
    /// occurrences, and exact incidence remain one source presentation.
    /// Receiver restriction below carries local portions of that testimony;
    /// it does not infer a coordinate chart from a graph layout.
    pub fn from_algebraic_presentations(
        presentations: BTreeMap<ReceiverGrainId, CausalAlgebraicPresentation>,
        quotients: BTreeMap<HolonicQuotientId, HolonicQuotient>,
        overlaps: BTreeMap<HolonicOverlapId, HolonicOverlapCell>,
        chronology: Option<u64>,
    ) -> Result<Self, GraphReceiverError> {
        for presentation in presentations.values() {
            presentation.validate()?;
        }
        let grains = presentations
            .iter()
            .map(|(grain, presentation)| (*grain, presentation.incidence.clone()))
            .collect();
        let mut result = Self::from_algebraic_grains(grains, quotients, overlaps, chronology)?;
        result.source_events.extend(
            presentations
                .values()
                .flat_map(|presentation| presentation.evolution.occurrences.keys().copied()),
        );
        result.algebraic_presentations = presentations;
        result.validate()?;
        Ok(result)
    }

    pub fn grain(
        &self,
        grain: ReceiverGrainId,
    ) -> Result<&ExactIncidenceAtlas, GraphReceiverError> {
        self.grains
            .get(&grain)
            .ok_or(GraphReceiverError::MissingGrain(grain))
    }

    pub fn algebraic_presentation(
        &self,
        grain: ReceiverGrainId,
    ) -> Option<&CausalAlgebraicPresentation> {
        self.algebraic_presentations.get(&grain)
    }

    pub fn witness(
        &self,
        address: HolonicCellAddress,
    ) -> Result<&ReceiverGraphSourceWitness, GraphReceiverError> {
        self.witnesses
            .get(&address)
            .ok_or(GraphReceiverError::MissingWitness(address))
    }

    pub fn quotient(
        &self,
        quotient: HolonicQuotientId,
    ) -> Result<&HolonicQuotient, GraphReceiverError> {
        self.quotients
            .get(&quotient)
            .ok_or(GraphReceiverError::MissingQuotient(quotient))
    }

    pub fn overlaps(&self) -> &BTreeMap<HolonicOverlapId, HolonicOverlapCell> {
        &self.overlaps
    }

    pub fn source_events(&self) -> &BTreeSet<EventId> {
        &self.source_events
    }

    pub fn chronology(&self) -> Option<u64> {
        self.chronology
    }

    pub fn cell(&self, address: HolonicCellAddress) -> Result<&CausalCell, GraphReceiverError> {
        Ok(self.grain(address.grain)?.incidence().cell(address.cell)?)
    }

    pub fn are_incident(
        &self,
        left: HolonicCellAddress,
        right: HolonicCellAddress,
    ) -> Result<bool, GraphReceiverError> {
        if left.grain != right.grain {
            return Ok(false);
        }
        let grain = self.grain(left.grain)?;
        let left_body = grain.incidence().cell(left.cell)?;
        let right_body = grain.incidence().cell(right.cell)?;
        Ok(left_body.boundary.coefficients().contains_key(&right.cell)
            || right_body.boundary.coefficients().contains_key(&left.cell))
    }

    pub fn validate(&self) -> Result<(), GraphReceiverError> {
        for grain in self.grains.values() {
            grain.validate()?;
        }
        for (grain, presentation) in &self.algebraic_presentations {
            presentation.validate()?;
            if &presentation.incidence != self.grain(*grain)?.incidence() {
                return Err(GraphReceiverError::AlgebraicPresentationIncidenceMismatch(
                    *grain,
                ));
            }
            if !presentation
                .evolution
                .occurrences
                .keys()
                .all(|event| self.source_events.contains(event))
            {
                return Err(GraphReceiverError::AlgebraicPresentationLineageMismatch(
                    *grain,
                ));
            }
        }
        let expected_addresses = self
            .grains
            .iter()
            .flat_map(|(grain, body)| {
                body.cells().keys().map(move |cell| HolonicCellAddress {
                    grain: *grain,
                    cell: *cell,
                })
            })
            .collect::<BTreeSet<_>>();
        if self.witnesses.keys().copied().collect::<BTreeSet<_>>() != expected_addresses {
            return Err(GraphReceiverError::WitnessPopulationMismatch);
        }
        for (address, witness) in &self.witnesses {
            self.cell(*address)?;
            match witness {
                ReceiverGraphSourceWitness::Algebraic => {}
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseGerm {
                    germ, ..
                }) => {
                    if !self.phase_germs.contains_key(germ) {
                        return Err(GraphReceiverError::MissingPhaseGerm(*germ));
                    }
                }
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseTransport {
                    connection,
                }) => {
                    if !self.phase_connections.contains_key(connection) {
                        return Err(GraphReceiverError::MissingPhaseConnection(*connection));
                    }
                }
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseClosure { cycle }) => {
                    if !self.phase_cycles.contains_key(cycle) {
                        return Err(GraphReceiverError::MissingPhaseCycle(*cycle));
                    }
                }
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::QuotientedComplex {
                    quotient,
                }) => {
                    let body = self.quotient(*quotient)?;
                    if body.target != *address {
                        return Err(GraphReceiverError::MalformedQuotient(*quotient));
                    }
                }
            }
        }
        for (id, quotient) in &self.quotients {
            if *id != quotient.id {
                return Err(GraphReceiverError::MalformedQuotient(*id));
            }
            self.cell(quotient.source_apex)?;
            self.cell(quotient.target)?;
            let expected = self
                .grain(quotient.source_apex.grain)?
                .incidence()
                .closed_hull([quotient.source_apex.cell])?;
            if quotient.source_closed_hull != expected {
                return Err(GraphReceiverError::MalformedQuotient(*id));
            }
        }
        for (id, overlap) in &self.overlaps {
            if *id != overlap.id || overlap.members.len() < 2 {
                return Err(GraphReceiverError::MalformedOverlap(*id));
            }
            self.cell(overlap.occurrence)?;
            for member in &overlap.members {
                self.cell(*member)?;
            }
        }
        Ok(())
    }

    pub fn grade_against(
        &self,
        standing: &ReceiverHolonicComplexStanding,
    ) -> Result<(), GraphReceiverError> {
        if self != &Self::mount(standing)? {
            return Err(GraphReceiverError::SourceAtlasGradeMismatch);
        }
        Ok(())
    }

    fn cell_fiber(
        &self,
        address: HolonicCellAddress,
    ) -> Result<ReceiverGraphCellFiber, GraphReceiverError> {
        Ok(match self.witness(address)? {
            ReceiverGraphSourceWitness::Algebraic => ReceiverGraphCellFiber::Algebraic,
            ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseGerm { germ, .. }) => {
                ReceiverGraphCellFiber::PhaseGerm(Box::new(
                    self.phase_germs
                        .get(germ)
                        .cloned()
                        .ok_or(GraphReceiverError::MissingPhaseGerm(*germ))?,
                ))
            }
            ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseTransport {
                connection,
            }) => ReceiverGraphCellFiber::PhaseTransport(Box::new(
                self.phase_connections
                    .get(connection)
                    .cloned()
                    .ok_or(GraphReceiverError::MissingPhaseConnection(*connection))?,
            )),
            ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseClosure { cycle }) => {
                ReceiverGraphCellFiber::PhaseClosure(Box::new(
                    self.phase_cycles
                        .get(cycle)
                        .cloned()
                        .ok_or(GraphReceiverError::MissingPhaseCycle(*cycle))?,
                ))
            }
            ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::QuotientedComplex {
                quotient,
            }) => ReceiverGraphCellFiber::QuotientedComplex(self.quotient(*quotient)?.clone()),
        })
    }

    fn source_fiber(
        &self,
        address: HolonicCellAddress,
    ) -> Result<BTreeSet<HolonicCellAddress>, GraphReceiverError> {
        match self.witness(address)? {
            ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::QuotientedComplex {
                quotient,
            }) => {
                let quotient = self.quotient(*quotient)?;
                Ok(quotient
                    .source_closed_hull
                    .iter()
                    .map(|cell| HolonicCellAddress {
                        grain: quotient.source_apex.grain,
                        cell: *cell,
                    })
                    .collect())
            }
            _ => Ok(BTreeSet::from([address])),
        }
    }

    fn cell_carrier_is_current(
        &self,
        address: HolonicCellAddress,
        cell: &ReceiverGraphCell,
    ) -> Result<bool, GraphReceiverError> {
        let witness = self.witness(address)?;
        let fiber_matches = match (witness, &cell.fiber) {
            (ReceiverGraphSourceWitness::Algebraic, ReceiverGraphCellFiber::Algebraic) => true,
            (
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseGerm { germ, .. }),
                ReceiverGraphCellFiber::PhaseGerm(received),
            ) => self
                .phase_germs
                .get(germ)
                .is_some_and(|expected| expected == received.as_ref()),
            (
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseTransport {
                    connection,
                }),
                ReceiverGraphCellFiber::PhaseTransport(received),
            ) => self
                .phase_connections
                .get(connection)
                .is_some_and(|expected| expected == received.as_ref()),
            (
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseClosure { cycle }),
                ReceiverGraphCellFiber::PhaseClosure(received),
            ) => self
                .phase_cycles
                .get(cycle)
                .is_some_and(|expected| expected == received.as_ref()),
            (
                ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::QuotientedComplex {
                    quotient,
                }),
                ReceiverGraphCellFiber::QuotientedComplex(received),
            ) => self
                .quotients
                .get(quotient)
                .is_some_and(|expected| expected == received),
            _ => false,
        };
        Ok(cell.address == address
            && &cell.body == self.cell(address)?
            && &cell.coboundary == self.grain(address.grain)?.coboundary(address.cell)?
            && &cell.witness == witness
            && fiber_matches
            && cell.source_fiber == self.source_fiber(address)?)
    }

    fn advanced(
        &self,
        standing_after: &ReceiverHolonicComplexStanding,
        radiation: &ReceiverHolonicComplexRadiation,
    ) -> Result<(Self, HolonicGraphSourceAdvanceReceipt), GraphReceiverError> {
        if self.source_events.contains(&radiation.event) {
            return Err(GraphReceiverError::RepeatedSourceEvent(radiation.event));
        }
        if !standing_after
            .phase_atlas
            .used_events
            .contains(&radiation.event)
        {
            return Err(GraphReceiverError::SourceRadiationAbsent(radiation.event));
        }

        let mut staged = self.clone();
        for germ in radiation.caused_phase_germs.keys() {
            staged.phase_germs.insert(
                *germ,
                standing_after
                    .phase_atlas
                    .germs
                    .get(germ)
                    .cloned()
                    .ok_or(GraphReceiverError::MissingPhaseGerm(*germ))?,
            );
        }
        for connection in radiation.caused_phase_connections.keys() {
            staged.phase_connections.insert(
                *connection,
                standing_after
                    .phase_atlas
                    .connections
                    .get(connection)
                    .cloned()
                    .ok_or(GraphReceiverError::MissingPhaseConnection(*connection))?,
            );
        }
        for cycle in radiation.caused_phase_cycles.keys() {
            staged.phase_cycles.insert(
                *cycle,
                standing_after
                    .phase_atlas
                    .cycles
                    .get(cycle)
                    .cloned()
                    .ok_or(GraphReceiverError::MissingPhaseCycle(*cycle))?,
            );
        }

        let changed_cells = radiation
            .causal_layers
            .iter()
            .flat_map(|layer| layer.caused_cells.iter().copied())
            .collect::<BTreeSet<_>>();
        for address in &changed_cells {
            let source_grain = standing_after.grain(address.grain)?;
            let cell = source_grain.incidence.cell(address.cell)?;
            let witness = source_grain
                .witnesses
                .get(&address.cell)
                .cloned()
                .ok_or(GraphReceiverError::MissingWitness(*address))?;
            staged
                .grains
                .entry(address.grain)
                .or_insert(ExactIncidenceAtlas::new(GradedCausalComplex::default())?)
                .append_cell(cell)?;
            if staged
                .witnesses
                .insert(*address, ReceiverGraphSourceWitness::Holonic(witness))
                .is_some()
            {
                return Err(GraphReceiverError::RepeatedSourceCell(*address));
            }
        }
        for quotient in &radiation.caused_quotients {
            let body = standing_after
                .quotients
                .get(quotient)
                .cloned()
                .ok_or(GraphReceiverError::MissingQuotient(*quotient))?;
            if staged.quotients.insert(*quotient, body).is_some() {
                return Err(GraphReceiverError::RepeatedQuotient(*quotient));
            }
        }
        for overlap in &radiation.caused_overlaps {
            let body = standing_after
                .overlaps
                .get(overlap)
                .cloned()
                .ok_or(GraphReceiverError::MissingOverlap(*overlap))?;
            if staged.overlaps.insert(*overlap, body).is_some() {
                return Err(GraphReceiverError::RepeatedOverlap(*overlap));
            }
        }
        staged.source_events = standing_after.phase_atlas.used_events.clone();
        staged.chronology = standing_after.phase_atlas.last_chronology;
        staged.validate()?;
        ensure_source_populations_match(&staged, standing_after)?;

        let work = changed_cells
            .len()
            .checked_add(radiation.caused_quotients.len())
            .and_then(|count| count.checked_add(radiation.caused_overlaps.len()))
            .ok_or(GraphReceiverError::CarrierOverflow)?;
        Ok((
            staged,
            HolonicGraphSourceAdvanceReceipt {
                schema: "holonic-engine.holonic-graph-source-advance-receipt.v1".to_owned(),
                event: radiation.event,
                changed_cells,
                caused_quotients: radiation.caused_quotients.clone(),
                caused_overlaps: radiation.caused_overlaps.clone(),
                work: BigUint::from(work),
            },
        ))
    }
}

fn ensure_source_populations_match(
    atlas: &HolonicGraphSourceAtlas,
    standing: &ReceiverHolonicComplexStanding,
) -> Result<(), GraphReceiverError> {
    if atlas.grains.len() != standing.grains.len()
        || atlas.quotients.len() != standing.quotients.len()
        || atlas.overlaps.len() != standing.overlaps.len()
        || atlas.phase_germs.len() != standing.phase_atlas.germs.len()
        || atlas.phase_connections.len() != standing.phase_atlas.connections.len()
        || atlas.phase_cycles.len() != standing.phase_atlas.cycles.len()
    {
        return Err(GraphReceiverError::SourcePopulationMismatch);
    }
    for (grain, indexed) in &atlas.grains {
        let source = standing.grain(*grain)?;
        if indexed.cells().len() != source.incidence.cells().len()
            || source.witnesses.len() != indexed.cells().len()
        {
            return Err(GraphReceiverError::SourcePopulationMismatch);
        }
    }
    Ok(())
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HolonicGraphSourceAdvanceReceipt {
    pub schema: String,
    pub event: EventId,
    pub changed_cells: BTreeSet<HolonicCellAddress>,
    pub caused_quotients: Vec<HolonicQuotientId>,
    pub caused_overlaps: Vec<HolonicOverlapId>,
    pub work: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverGraphSourceWitness {
    /// The cell is exact algebraic incidence without a more specialized
    /// receiver-phase interpretation.
    Algebraic,
    Holonic(HolonicCellWitness),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverGraphCellFiber {
    Algebraic,
    PhaseGerm(Box<ReceiverPhaseGerm>),
    PhaseTransport(Box<ReceiverPhaseConnection>),
    PhaseClosure(Box<ReceiverPhaseCycle>),
    QuotientedComplex(HolonicQuotient),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphCell {
    pub address: HolonicCellAddress,
    pub body: CausalCell,
    pub coboundary: CausalChain,
    pub witness: ReceiverGraphSourceWitness,
    pub fiber: ReceiverGraphCellFiber,
    /// The point's complete finer source fiber. Nonquotient cells carry
    /// themselves as the singleton fiber.
    pub source_fiber: BTreeSet<HolonicCellAddress>,
}

/// One caused algebraic region as it reaches the contemporary receiver.
///
/// `received_support` is the exact intersection of two boundary-closed
/// sections: the source region and the receiver section. `complete` records
/// whether the complete source region has arrived.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphAlgebraicRegion {
    pub body: CausalRegion,
    pub received_support: BTreeSet<CausalCellId>,
    pub complete: bool,
}

/// One opposed end restricted to the received part of its local region.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphAlgebraicEnd {
    pub body: CausalEnd,
    pub received_section: CausalChain,
    pub complete: bool,
}

/// Exact coordinate testimony available in one receiver-local graph section.
///
/// These values come from a source `CausalAlgebraicPresentation`. A layout or
/// shader may evaluate them later, but may not fabricate them from terminal
/// point positions.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphAlgebraicSection {
    pub local_algebras: BTreeMap<LocalAlgebraId, LocalCoordinateAlgebra>,
    pub regions: BTreeMap<CausalRegionId, ReceiverGraphAlgebraicRegion>,
    pub ends: BTreeMap<CausalEndId, ReceiverGraphAlgebraicEnd>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverGraphSeed {
    Focus(HolonicCellAddress),
    QuotientFiber(HolonicQuotientId),
}

impl ReceiverGraphSeed {
    fn focus(
        &self,
        source: &HolonicGraphSourceAtlas,
    ) -> Result<HolonicCellAddress, GraphReceiverError> {
        match self {
            Self::Focus(focus) => {
                source.cell(*focus)?;
                Ok(*focus)
            }
            Self::QuotientFiber(quotient) => Ok(source.quotient(*quotient)?.source_apex),
        }
    }

    fn roots(
        &self,
        source: &HolonicGraphSourceAtlas,
    ) -> Result<BTreeSet<HolonicCellAddress>, GraphReceiverError> {
        match self {
            Self::Focus(focus) => {
                source.cell(*focus)?;
                Ok(BTreeSet::from([*focus]))
            }
            Self::QuotientFiber(quotient) => {
                let quotient = source.quotient(*quotient)?;
                Ok(quotient
                    .source_closed_hull
                    .iter()
                    .map(|cell| HolonicCellAddress {
                        grain: quotient.source_apex.grain,
                        cell: *cell,
                    })
                    .collect())
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphFrame {
    pub receiver: ReceiverId,
    pub seed: ReceiverGraphSeed,
    pub focus: HolonicCellAddress,
    pub upper_horizon: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverGraphDeed {
    Found {
        focus: HolonicCellAddress,
        upper_horizon: u32,
    },
    Dilate {
        upper_horizon: u32,
    },
    Traverse {
        path: Vec<HolonicCellAddress>,
        upper_horizon: u32,
    },
    Refine {
        quotient: HolonicQuotientId,
        upper_horizon: u32,
    },
    Coarsen {
        quotient: HolonicQuotientId,
        upper_horizon: u32,
    },
    Retain,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphRequest {
    pub event: EventId,
    pub chronology: u64,
    pub receiver: ReceiverId,
    pub deed: ReceiverGraphDeed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverGraphChange {
    Founded,
    Retained,
    Dilated,
    Traversed,
    Refined,
    Coarsened,
    SourceAdvanced,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ReceiverGraphTransitionCause {
    ReceiverDeed(ReceiverGraphDeed),
    SourceEvent(EventId),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphDelta {
    pub added: BTreeSet<HolonicCellAddress>,
    pub removed: BTreeSet<HolonicCellAddress>,
    pub retained: BTreeSet<HolonicCellAddress>,
}

impl ReceiverGraphDelta {
    fn between(previous: Option<&ReceiverGraphSection>, current: &ReceiverGraphSection) -> Self {
        let before = previous
            .map(|section| section.cells.keys().copied().collect())
            .unwrap_or_default();
        let after = current.cells.keys().copied().collect::<BTreeSet<_>>();
        Self {
            added: after.difference(&before).copied().collect(),
            removed: before.difference(&after).copied().collect(),
            retained: before.intersection(&after).copied().collect(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphTransition {
    pub predecessor_event: Option<EventId>,
    pub event: EventId,
    pub chronology: u64,
    pub cause: ReceiverGraphTransitionCause,
    pub change: ReceiverGraphChange,
    pub from: Option<ReceiverGraphFrame>,
    pub to: ReceiverGraphFrame,
    pub delta: ReceiverGraphDelta,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphAnalysis {
    pub dimension: Option<u32>,
    pub f_vector: BTreeMap<u32, BigUint>,
    pub euler_characteristic: BigInt,
    pub oriented_boundary_terms: BigUint,
    pub connected_components: BigUint,
    /// Present only when every grade-one cell has one negative and one
    /// positive unit boundary member.
    pub graph_cycle_rank: Option<BigUint>,
    pub source_occurrences: BTreeSet<EventId>,
    pub quotient_points: BigUint,
    pub source_fiber_population: BigUint,
    pub maximum_source_fiber: BigUint,
    pub internal_topologies: BTreeMap<InternalAnalyticTopology, BigUint>,
    pub curved_phase_cycles: BigUint,
    pub actual_overlaps: BigUint,
    pub maximum_overlap_order: BigUint,
    pub open_upper_frontier: BigUint,
    pub local_coordinate_algebras: BigUint,
    pub algebraic_regions: BigUint,
    pub complete_algebraic_regions: BigUint,
    pub causal_end_sections: BigUint,
    pub complete_causal_end_sections: BigUint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphSection {
    pub schema: String,
    pub event: EventId,
    pub chronology: u64,
    pub frame: ReceiverGraphFrame,
    pub cells: BTreeMap<HolonicCellAddress, Arc<ReceiverGraphCell>>,
    pub overlaps: BTreeMap<HolonicOverlapId, HolonicOverlapCell>,
    pub algebraic: Option<ReceiverGraphAlgebraicSection>,
    pub dependencies: BTreeSet<HolonicCellAddress>,
    pub upper_frontier: BTreeSet<HolonicCellAddress>,
    pub source_events: BTreeSet<EventId>,
    pub analysis: ReceiverGraphAnalysis,
    pub transitions: Vec<ReceiverGraphTransition>,
}

impl ReceiverGraphSection {
    pub fn validate(&self, source: &HolonicGraphSourceAtlas) -> Result<(), GraphReceiverError> {
        if self.frame.focus != self.frame.seed.focus(source)?
            || self.cells.keys().any(|address| {
                address.grain != self.frame.focus.grain || source.cell(*address).is_err()
            })
            || self.transitions.iter().any(|transition| {
                transition.to.receiver != self.frame.receiver
                    || transition
                        .from
                        .as_ref()
                        .is_some_and(|frame| frame.receiver != self.frame.receiver)
            })
        {
            return Err(GraphReceiverError::MalformedReceiverSection);
        }
        let support = self
            .cells
            .keys()
            .map(|address| address.cell)
            .collect::<BTreeSet<_>>();
        if !source
            .grain(self.frame.focus.grain)?
            .incidence()
            .is_closed_support(&support)?
        {
            return Err(GraphReceiverError::ReceiverSectionNotClosed);
        }
        for (address, cell) in &self.cells {
            if !source.cell_carrier_is_current(*address, cell)? {
                return Err(GraphReceiverError::MalformedReceiverSection);
            }
        }
        let addresses = self.cells.keys().copied().collect::<BTreeSet<_>>();
        if self.overlaps != restrict_overlaps(source, &addresses)
            || self.upper_frontier != derive_upper_frontier(&self.cells, &addresses)
            || self.dependencies.iter().any(|address| {
                address.grain != self.frame.focus.grain
                    || !addresses.contains(address)
                    || source.cell(*address).is_err()
            })
        {
            return Err(GraphReceiverError::MalformedReceiverSection);
        }
        if self.algebraic != restrict_algebraic_section(source, self.frame.focus.grain, &support)? {
            return Err(GraphReceiverError::MalformedAlgebraicReceiverSection);
        }
        let source_events = self
            .cells
            .values()
            .flat_map(|cell| cell.body.source_events.iter().copied())
            .collect::<BTreeSet<_>>();
        let analysis = analyze_receiver_section(
            &self.cells,
            &self.overlaps,
            self.algebraic.as_ref(),
            &self.upper_frontier,
        )?;
        if self.source_events != source_events || self.analysis != analysis {
            return Err(GraphReceiverError::MalformedReceiverAnalysis);
        }
        if self.transitions.last().is_some_and(|latest| {
            latest.event != self.event
                || latest.chronology != self.chronology
                || latest.to != self.frame
        }) {
            return Err(GraphReceiverError::MalformedReceiverLineage);
        }
        for adjacent in self.transitions.windows(2) {
            if adjacent[1].predecessor_event != Some(adjacent[0].event)
                || adjacent[1].from.as_ref() != Some(&adjacent[0].to)
            {
                return Err(GraphReceiverError::MalformedReceiverLineage);
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphRadiation {
    pub schema: String,
    pub receiver: ReceiverId,
    pub transition: ReceiverGraphTransition,
    pub analysis: ReceiverGraphAnalysis,
    pub query_work: ReceiverGraphQueryWork,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphSourceAdvance {
    pub schema: String,
    pub source: HolonicGraphSourceAdvanceReceipt,
    pub receivers: Vec<ReceiverGraphRadiation>,
}

/// Persistent receiver-local graph sections over one exact source atlas.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverGraphAtlas {
    pub schema: String,
    source: HolonicGraphSourceAtlas,
    sections: BTreeMap<ReceiverId, ReceiverGraphSection>,
    used_receiver_events: BTreeSet<EventId>,
    last_receiver_chronology: BTreeMap<ReceiverId, u64>,
}

impl ReceiverGraphAtlas {
    pub fn mount(standing: &ReceiverHolonicComplexStanding) -> Result<Self, GraphReceiverError> {
        Self::from_source(HolonicGraphSourceAtlas::mount(standing)?)
    }

    pub fn from_source(source: HolonicGraphSourceAtlas) -> Result<Self, GraphReceiverError> {
        source.validate()?;
        Ok(Self {
            schema: "holonic-engine.receiver-graph-atlas.v1".to_owned(),
            source,
            sections: BTreeMap::new(),
            used_receiver_events: BTreeSet::new(),
            last_receiver_chronology: BTreeMap::new(),
        })
    }

    pub fn source(&self) -> &HolonicGraphSourceAtlas {
        &self.source
    }

    pub fn section(&self, receiver: ReceiverId) -> Option<&ReceiverGraphSection> {
        self.sections.get(&receiver)
    }

    pub fn sections(&self) -> &BTreeMap<ReceiverId, ReceiverGraphSection> {
        &self.sections
    }

    pub fn validate(&self) -> Result<(), GraphReceiverError> {
        self.source.validate()?;
        let mut receiver_events = BTreeSet::new();
        let mut receiver_chronologies = BTreeMap::new();
        for (receiver, section) in &self.sections {
            if section.frame.receiver != *receiver {
                return Err(GraphReceiverError::MalformedReceiverSection);
            }
            section.validate(&self.source)?;
            for transition in &section.transitions {
                if let ReceiverGraphTransitionCause::ReceiverDeed(_) = &transition.cause {
                    if !receiver_events.insert(transition.event) {
                        return Err(GraphReceiverError::RepeatedReceiverEvent(transition.event));
                    }
                    receiver_chronologies.insert(*receiver, transition.chronology);
                }
            }
        }
        if self.used_receiver_events != receiver_events
            || self.last_receiver_chronology != receiver_chronologies
        {
            return Err(GraphReceiverError::MalformedReceiverLineage);
        }
        Ok(())
    }

    pub fn receive(
        &mut self,
        request: &ReceiverGraphRequest,
    ) -> Result<ReceiverGraphRadiation, GraphReceiverError> {
        if self.used_receiver_events.contains(&request.event) {
            return Err(GraphReceiverError::RepeatedReceiverEvent(request.event));
        }
        if self
            .last_receiver_chronology
            .get(&request.receiver)
            .is_some_and(|previous| request.chronology <= *previous)
        {
            return Err(GraphReceiverError::NoncausalReceiverChronology {
                receiver: request.receiver,
                previous: self.last_receiver_chronology[&request.receiver],
                received: request.chronology,
            });
        }

        let previous = self.sections.get(&request.receiver).cloned();
        let (frame, change) = derive_receiver_frame(&self.source, previous.as_ref(), request)?;
        let mut current;
        let query_work;
        if change == ReceiverGraphChange::Retained {
            current = previous
                .clone()
                .ok_or(GraphReceiverError::ReceiverNotFounded(request.receiver))?;
            current.event = request.event;
            current.chronology = request.chronology;
            query_work = ReceiverGraphQueryWork {
                reused_cells: BigUint::from(current.cells.len()),
                ..ReceiverGraphQueryWork::default()
            };
        } else {
            let built = build_receiver_section(
                &self.source,
                request.event,
                request.chronology,
                frame.clone(),
                previous.as_ref(),
            )?;
            query_work = built.query_work;
            current = built.section;
        }

        let delta = ReceiverGraphDelta::between(previous.as_ref(), &current);
        let transition = ReceiverGraphTransition {
            predecessor_event: previous.as_ref().map(|section| section.event),
            event: request.event,
            chronology: request.chronology,
            cause: ReceiverGraphTransitionCause::ReceiverDeed(request.deed.clone()),
            change,
            from: previous.as_ref().map(|section| section.frame.clone()),
            to: current.frame.clone(),
            delta,
        };
        current.transitions.push(transition.clone());
        current.validate(&self.source)?;

        let radiation = ReceiverGraphRadiation {
            schema: "holonic-engine.receiver-graph-radiation.v1".to_owned(),
            receiver: request.receiver,
            transition,
            analysis: current.analysis.clone(),
            query_work,
        };
        self.sections.insert(request.receiver, current);
        self.used_receiver_events.insert(request.event);
        self.last_receiver_chronology
            .insert(request.receiver, request.chronology);
        Ok(radiation)
    }

    /// Carry one append-only source event into only receiver sections whose
    /// consulted incidence can be changed by that event.
    pub fn advance_source(
        &mut self,
        standing_after: &ReceiverHolonicComplexStanding,
        radiation: &ReceiverHolonicComplexRadiation,
    ) -> Result<ReceiverGraphSourceAdvance, GraphReceiverError> {
        let (source_after, source_receipt) = self.source.advanced(standing_after, radiation)?;
        let chronology = source_after
            .chronology()
            .ok_or(GraphReceiverError::MissingSourceChronology)?;
        let mut sections_after = self.sections.clone();
        let mut receiver_radiation = Vec::new();

        for (receiver, previous) in &self.sections {
            if !source_change_reaches(previous, &source_after, &source_receipt)? {
                continue;
            }
            let built = build_receiver_section(
                &source_after,
                radiation.event,
                chronology,
                previous.frame.clone(),
                Some(previous),
            )?;
            let mut current = built.section;
            let delta = ReceiverGraphDelta::between(Some(previous), &current);
            let transition = ReceiverGraphTransition {
                predecessor_event: Some(previous.event),
                event: radiation.event,
                chronology,
                cause: ReceiverGraphTransitionCause::SourceEvent(radiation.event),
                change: ReceiverGraphChange::SourceAdvanced,
                from: Some(previous.frame.clone()),
                to: current.frame.clone(),
                delta,
            };
            current.transitions.push(transition.clone());
            current.validate(&source_after)?;
            receiver_radiation.push(ReceiverGraphRadiation {
                schema: "holonic-engine.receiver-graph-radiation.v1".to_owned(),
                receiver: *receiver,
                transition,
                analysis: current.analysis.clone(),
                query_work: built.query_work,
            });
            sections_after.insert(*receiver, current);
        }

        self.source = source_after;
        self.sections = sections_after;
        Ok(ReceiverGraphSourceAdvance {
            schema: "holonic-engine.receiver-graph-source-advance.v1".to_owned(),
            source: source_receipt,
            receivers: receiver_radiation,
        })
    }
}

fn derive_receiver_frame(
    source: &HolonicGraphSourceAtlas,
    previous: Option<&ReceiverGraphSection>,
    request: &ReceiverGraphRequest,
) -> Result<(ReceiverGraphFrame, ReceiverGraphChange), GraphReceiverError> {
    match (&request.deed, previous) {
        (
            ReceiverGraphDeed::Found {
                focus,
                upper_horizon,
            },
            None,
        ) => {
            source.cell(*focus)?;
            Ok((
                ReceiverGraphFrame {
                    receiver: request.receiver,
                    seed: ReceiverGraphSeed::Focus(*focus),
                    focus: *focus,
                    upper_horizon: *upper_horizon,
                },
                ReceiverGraphChange::Founded,
            ))
        }
        (ReceiverGraphDeed::Found { .. }, Some(_)) => {
            Err(GraphReceiverError::ReceiverAlreadyFounded(request.receiver))
        }
        (_, None) => Err(GraphReceiverError::ReceiverNotFounded(request.receiver)),
        (ReceiverGraphDeed::Retain, Some(previous)) => {
            Ok((previous.frame.clone(), ReceiverGraphChange::Retained))
        }
        (ReceiverGraphDeed::Dilate { upper_horizon }, Some(previous)) => Ok((
            ReceiverGraphFrame {
                upper_horizon: *upper_horizon,
                ..previous.frame.clone()
            },
            if *upper_horizon == previous.frame.upper_horizon {
                ReceiverGraphChange::Retained
            } else {
                ReceiverGraphChange::Dilated
            },
        )),
        (
            ReceiverGraphDeed::Traverse {
                path,
                upper_horizon,
            },
            Some(previous),
        ) => {
            if path.len() < 2 {
                return Err(GraphReceiverError::TraversalTooShort);
            }
            if path.first().copied() != Some(previous.frame.focus) {
                return Err(GraphReceiverError::TraversalDoesNotStartAtFocus);
            }
            for pair in path.windows(2) {
                if !source.are_incident(pair[0], pair[1])? {
                    return Err(GraphReceiverError::NonincidentTraversal {
                        from: pair[0],
                        target: pair[1],
                    });
                }
            }
            let focus = *path.last().expect("a path of length two has a target");
            Ok((
                ReceiverGraphFrame {
                    receiver: request.receiver,
                    seed: ReceiverGraphSeed::Focus(focus),
                    focus,
                    upper_horizon: *upper_horizon,
                },
                ReceiverGraphChange::Traversed,
            ))
        }
        (
            ReceiverGraphDeed::Refine {
                quotient,
                upper_horizon,
            },
            Some(previous),
        ) => {
            let quotient_body = source.quotient(*quotient)?;
            if previous.frame.focus != quotient_body.target {
                return Err(GraphReceiverError::RefinementTargetMismatch {
                    quotient: *quotient,
                    expected: quotient_body.target,
                    received: previous.frame.focus,
                });
            }
            Ok((
                ReceiverGraphFrame {
                    receiver: request.receiver,
                    seed: ReceiverGraphSeed::QuotientFiber(*quotient),
                    focus: quotient_body.source_apex,
                    upper_horizon: *upper_horizon,
                },
                ReceiverGraphChange::Refined,
            ))
        }
        (
            ReceiverGraphDeed::Coarsen {
                quotient,
                upper_horizon,
            },
            Some(previous),
        ) => {
            let quotient_body = source.quotient(*quotient)?;
            if previous.frame.focus != quotient_body.source_apex {
                return Err(GraphReceiverError::CoarseningSourceMismatch {
                    quotient: *quotient,
                    expected: quotient_body.source_apex,
                    received: previous.frame.focus,
                });
            }
            let previous_support = previous.cells.keys().copied().collect::<BTreeSet<_>>();
            let required = quotient_body
                .source_closed_hull
                .iter()
                .map(|cell| HolonicCellAddress {
                    grain: quotient_body.source_apex.grain,
                    cell: *cell,
                })
                .collect::<BTreeSet<_>>();
            if !required.is_subset(&previous_support) {
                return Err(GraphReceiverError::IncompleteQuotientFiber(*quotient));
            }
            Ok((
                ReceiverGraphFrame {
                    receiver: request.receiver,
                    seed: ReceiverGraphSeed::Focus(quotient_body.target),
                    focus: quotient_body.target,
                    upper_horizon: *upper_horizon,
                },
                ReceiverGraphChange::Coarsened,
            ))
        }
    }
}

struct BuiltReceiverSection {
    section: ReceiverGraphSection,
    query_work: ReceiverGraphQueryWork,
}

fn restrict_algebraic_section(
    source: &HolonicGraphSourceAtlas,
    grain: ReceiverGrainId,
    support: &BTreeSet<CausalCellId>,
) -> Result<Option<ReceiverGraphAlgebraicSection>, GraphReceiverError> {
    let Some(presentation) = source.algebraic_presentation(grain) else {
        return Ok(None);
    };
    let mut regions = BTreeMap::new();
    let mut admitted_algebras = BTreeSet::new();
    for (id, region) in presentation.regions() {
        let received_support = region
            .support
            .intersection(support)
            .copied()
            .collect::<BTreeSet<_>>();
        if received_support.is_empty() {
            continue;
        }
        if !presentation
            .incidence
            .is_closed_support(&received_support)?
        {
            return Err(GraphReceiverError::AlgebraicRegionRestrictionNotClosed(*id));
        }
        admitted_algebras.extend(region.local_algebras.iter().copied());
        regions.insert(
            *id,
            ReceiverGraphAlgebraicRegion {
                body: region.clone(),
                complete: region.support.is_subset(support),
                received_support,
            },
        );
    }
    let local_algebras = admitted_algebras
        .into_iter()
        .map(|id| Ok((id, presentation.local_algebra(id)?.clone())))
        .collect::<Result<BTreeMap<_, _>, GraphReceiverError>>()?;
    let ends = presentation
        .ends()
        .iter()
        .filter(|(_, end)| regions.contains_key(&end.region))
        .map(|(id, end)| {
            let received_section = restrict_chain(&end.section, support);
            (
                *id,
                ReceiverGraphAlgebraicEnd {
                    body: end.clone(),
                    complete: end.section.support().is_subset(support),
                    received_section,
                },
            )
        })
        .collect();
    Ok(Some(ReceiverGraphAlgebraicSection {
        local_algebras,
        regions,
        ends,
    }))
}

fn restrict_chain(chain: &CausalChain, support: &BTreeSet<CausalCellId>) -> CausalChain {
    let mut received = CausalChain::default();
    for (cell, coefficient) in chain.coefficients() {
        if support.contains(cell) {
            received.add_term(*cell, coefficient.clone());
        }
    }
    received
}

fn restrict_overlaps(
    source: &HolonicGraphSourceAtlas,
    addresses: &BTreeSet<HolonicCellAddress>,
) -> BTreeMap<HolonicOverlapId, HolonicOverlapCell> {
    source
        .overlaps()
        .iter()
        .filter(|(_, overlap)| {
            addresses.contains(&overlap.occurrence)
                || overlap
                    .members
                    .iter()
                    .any(|member| addresses.contains(member))
        })
        .map(|(id, overlap)| (*id, overlap.clone()))
        .collect()
}

fn derive_upper_frontier(
    cells: &BTreeMap<HolonicCellAddress, Arc<ReceiverGraphCell>>,
    addresses: &BTreeSet<HolonicCellAddress>,
) -> BTreeSet<HolonicCellAddress> {
    cells
        .iter()
        .filter_map(|(address, cell)| {
            cell.coboundary
                .support()
                .iter()
                .any(|coface| {
                    !addresses.contains(&HolonicCellAddress {
                        grain: address.grain,
                        cell: *coface,
                    })
                })
                .then_some(*address)
        })
        .collect()
}

fn build_receiver_section(
    source: &HolonicGraphSourceAtlas,
    event: EventId,
    chronology: u64,
    frame: ReceiverGraphFrame,
    previous: Option<&ReceiverGraphSection>,
) -> Result<BuiltReceiverSection, GraphReceiverError> {
    if frame.focus != frame.seed.focus(source)? {
        return Err(GraphReceiverError::MalformedReceiverFrame);
    }
    let roots = frame.seed.roots(source)?;
    if roots.iter().any(|root| root.grain != frame.focus.grain) {
        return Err(GraphReceiverError::MixedReceiverGrains);
    }
    let grain = source.grain(frame.focus.grain)?;
    let sparse = grain.receive_section(
        roots.iter().map(|address| address.cell),
        frame.upper_horizon,
    )?;
    let addresses = sparse
        .support
        .iter()
        .map(|cell| HolonicCellAddress {
            grain: frame.focus.grain,
            cell: *cell,
        })
        .collect::<BTreeSet<_>>();
    let mut cells = BTreeMap::new();
    let mut reused_cells = 0_usize;
    for address in &addresses {
        let retained = match previous.and_then(|section| section.cells.get(address)) {
            Some(previous_cell) if source.cell_carrier_is_current(*address, previous_cell)? => {
                Some(Arc::clone(previous_cell))
            }
            _ => None,
        };
        if let Some(retained) = retained {
            cells.insert(*address, retained);
            reused_cells = reused_cells
                .checked_add(1)
                .ok_or(GraphReceiverError::CarrierOverflow)?;
            continue;
        }
        cells.insert(
            *address,
            Arc::new(ReceiverGraphCell {
                address: *address,
                body: source.cell(*address)?.clone(),
                coboundary: grain.coboundary(address.cell)?.clone(),
                witness: source.witness(*address)?.clone(),
                fiber: source.cell_fiber(*address)?,
                source_fiber: source.source_fiber(*address)?,
            }),
        );
    }
    let dependencies = sparse
        .dependencies
        .iter()
        .map(|cell| HolonicCellAddress {
            grain: frame.focus.grain,
            cell: *cell,
        })
        .collect::<BTreeSet<_>>();
    let upper_frontier = derive_upper_frontier(&cells, &addresses);
    let overlaps = restrict_overlaps(source, &addresses);
    let algebraic = restrict_algebraic_section(source, frame.focus.grain, &sparse.support)?;
    let source_events = cells
        .values()
        .flat_map(|cell| cell.body.source_events.iter().copied())
        .collect::<BTreeSet<_>>();
    let analysis =
        analyze_receiver_section(&cells, &overlaps, algebraic.as_ref(), &upper_frontier)?;
    let mut query_work = sparse.work;
    query_work.reused_cells = BigUint::from(reused_cells);
    query_work.materialized_cells = BigUint::from(
        addresses
            .len()
            .checked_sub(reused_cells)
            .ok_or(GraphReceiverError::CarrierOverflow)?,
    );
    let transitions = previous
        .map(|section| section.transitions.clone())
        .unwrap_or_default();
    let section = ReceiverGraphSection {
        schema: "holonic-engine.receiver-graph-section.v1".to_owned(),
        event,
        chronology,
        frame,
        cells,
        overlaps,
        algebraic,
        dependencies,
        upper_frontier,
        source_events,
        analysis,
        transitions,
    };
    Ok(BuiltReceiverSection {
        section,
        query_work,
    })
}

fn analyze_receiver_section(
    cells: &BTreeMap<HolonicCellAddress, Arc<ReceiverGraphCell>>,
    overlaps: &BTreeMap<HolonicOverlapId, HolonicOverlapCell>,
    algebraic: Option<&ReceiverGraphAlgebraicSection>,
    upper_frontier: &BTreeSet<HolonicCellAddress>,
) -> Result<ReceiverGraphAnalysis, GraphReceiverError> {
    let mut f_vector = BTreeMap::<u32, BigUint>::new();
    let mut euler_characteristic = BigInt::zero();
    let mut boundary_terms = 0_usize;
    let mut source_occurrences = BTreeSet::new();
    let mut quotient_points = 0_usize;
    let mut source_fiber_population = 0_usize;
    let mut maximum_source_fiber = 0_usize;
    let mut internal_topologies = BTreeMap::<InternalAnalyticTopology, BigUint>::new();
    let mut curved_phase_cycles = 0_usize;

    for cell in cells.values() {
        *f_vector.entry(cell.body.grade).or_default() += BigUint::one();
        if cell.body.grade % 2 == 0 {
            euler_characteristic += 1;
        } else {
            euler_characteristic -= 1;
        }
        boundary_terms = boundary_terms
            .checked_add(cell.body.boundary.coefficients().len())
            .ok_or(GraphReceiverError::CarrierOverflow)?;
        source_occurrences.extend(cell.body.source_events.iter().copied());
        source_fiber_population = source_fiber_population
            .checked_add(cell.source_fiber.len())
            .ok_or(GraphReceiverError::CarrierOverflow)?;
        maximum_source_fiber = maximum_source_fiber.max(cell.source_fiber.len());
        match &cell.witness {
            ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::PhaseGerm {
                internal_sections,
                ..
            }) => {
                for section in internal_sections {
                    *internal_topologies.entry(section.topology).or_default() += BigUint::one();
                }
            }
            ReceiverGraphSourceWitness::Holonic(HolonicCellWitness::QuotientedComplex {
                ..
            }) => {
                quotient_points = quotient_points
                    .checked_add(1)
                    .ok_or(GraphReceiverError::CarrierOverflow)?;
            }
            _ => {}
        }
        if matches!(
            &cell.fiber,
            ReceiverGraphCellFiber::PhaseClosure(cycle) if cycle.curved
        ) {
            curved_phase_cycles = curved_phase_cycles
                .checked_add(1)
                .ok_or(GraphReceiverError::CarrierOverflow)?;
        }
    }

    let (connected_components, graph_cycle_rank) = graph_layer_analysis(cells)?;
    let maximum_overlap_order = overlaps
        .values()
        .map(|overlap| overlap.members.len())
        .max()
        .unwrap_or(0);
    let (
        local_coordinate_algebras,
        algebraic_regions,
        complete_algebraic_regions,
        causal_end_sections,
        complete_causal_end_sections,
    ) = algebraic.map_or((0, 0, 0, 0, 0), |section| {
        (
            section.local_algebras.len(),
            section.regions.len(),
            section
                .regions
                .values()
                .filter(|region| region.complete)
                .count(),
            section.ends.len(),
            section.ends.values().filter(|end| end.complete).count(),
        )
    });
    Ok(ReceiverGraphAnalysis {
        dimension: cells.values().map(|cell| cell.body.grade).max(),
        f_vector,
        euler_characteristic,
        oriented_boundary_terms: BigUint::from(boundary_terms),
        connected_components: BigUint::from(connected_components),
        graph_cycle_rank: graph_cycle_rank.map(BigUint::from),
        source_occurrences,
        quotient_points: BigUint::from(quotient_points),
        source_fiber_population: BigUint::from(source_fiber_population),
        maximum_source_fiber: BigUint::from(maximum_source_fiber),
        internal_topologies,
        curved_phase_cycles: BigUint::from(curved_phase_cycles),
        actual_overlaps: BigUint::from(overlaps.len()),
        maximum_overlap_order: BigUint::from(maximum_overlap_order),
        open_upper_frontier: BigUint::from(upper_frontier.len()),
        local_coordinate_algebras: BigUint::from(local_coordinate_algebras),
        algebraic_regions: BigUint::from(algebraic_regions),
        complete_algebraic_regions: BigUint::from(complete_algebraic_regions),
        causal_end_sections: BigUint::from(causal_end_sections),
        complete_causal_end_sections: BigUint::from(complete_causal_end_sections),
    })
}

fn graph_layer_analysis(
    cells: &BTreeMap<HolonicCellAddress, Arc<ReceiverGraphCell>>,
) -> Result<(usize, Option<usize>), GraphReceiverError> {
    let vertices = cells
        .values()
        .filter(|cell| cell.body.grade == 0)
        .map(|cell| cell.address.cell)
        .collect::<BTreeSet<_>>();
    let edges = cells
        .values()
        .filter(|cell| cell.body.grade == 1)
        .collect::<Vec<_>>();
    let mut adjacency = vertices
        .iter()
        .copied()
        .map(|vertex| (vertex, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    let mut graph_like = true;

    for edge in &edges {
        let boundary = edge.body.boundary.coefficients();
        let members = boundary.keys().copied().collect::<Vec<_>>();
        if members.len() != 2
            || !members.iter().all(|member| vertices.contains(member))
            || !boundary
                .values()
                .all(ComparativeMultiplicity::is_unit_orientation)
            || boundary
                .values()
                .filter(|coefficient| !coefficient.positive_count().is_zero())
                .count()
                != 1
            || boundary
                .values()
                .filter(|coefficient| !coefficient.negative_count().is_zero())
                .count()
                != 1
        {
            graph_like = false;
        }
        if let Some((first, rest)) = members.split_first() {
            for member in rest {
                adjacency.entry(*first).or_default().insert(*member);
                adjacency.entry(*member).or_default().insert(*first);
            }
        }
    }

    let mut unseen = vertices.clone();
    let mut components = 0_usize;
    while let Some(root) = unseen.iter().next().copied() {
        components = components
            .checked_add(1)
            .ok_or(GraphReceiverError::CarrierOverflow)?;
        unseen.remove(&root);
        let mut frontier = VecDeque::from([root]);
        while let Some(vertex) = frontier.pop_front() {
            for neighbor in &adjacency[&vertex] {
                if unseen.remove(neighbor) {
                    frontier.push_back(*neighbor);
                }
            }
        }
    }

    let cycle_rank = if graph_like {
        edges
            .len()
            .checked_add(components)
            .and_then(|sum| sum.checked_sub(vertices.len()))
    } else {
        None
    };
    Ok((components, cycle_rank))
}

fn source_change_reaches(
    section: &ReceiverGraphSection,
    source_after: &HolonicGraphSourceAtlas,
    receipt: &HolonicGraphSourceAdvanceReceipt,
) -> Result<bool, GraphReceiverError> {
    let support = section.cells.keys().copied().collect::<BTreeSet<_>>();
    for changed in &receipt.changed_cells {
        if support.contains(changed) {
            return Ok(true);
        }
        if changed.grain == section.frame.focus.grain
            && source_after
                .cell(*changed)?
                .boundary
                .support()
                .iter()
                .any(|lower| {
                    support.contains(&HolonicCellAddress {
                        grain: changed.grain,
                        cell: *lower,
                    })
                })
        {
            return Ok(true);
        }
    }
    for quotient in &receipt.caused_quotients {
        let quotient = source_after.quotient(*quotient)?;
        if support.contains(&quotient.target)
            || quotient.source_closed_hull.iter().any(|cell| {
                support.contains(&HolonicCellAddress {
                    grain: quotient.source_apex.grain,
                    cell: *cell,
                })
            })
        {
            return Ok(true);
        }
    }
    for overlap in &receipt.caused_overlaps {
        let overlap = source_after
            .overlaps()
            .get(overlap)
            .ok_or(GraphReceiverError::MissingOverlap(*overlap))?;
        if support.contains(&overlap.occurrence)
            || overlap
                .members
                .iter()
                .any(|member| support.contains(member))
        {
            return Ok(true);
        }
    }
    Ok(false)
}

fn usize_to_u64(value: usize) -> Result<u64, GraphReceiverError> {
    u64::try_from(value).map_err(|_| GraphReceiverError::CarrierOverflow)
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum GraphReceiverError {
    #[error("receiver graph roots cannot be empty")]
    EmptyReceiverRoots,
    #[error("receiver grain {0:?} is absent from the graph source")]
    MissingGrain(ReceiverGrainId),
    #[error("causal cell {0:?} has no exact coboundary")]
    MissingCoboundary(CausalCellId),
    #[error("the sparse coboundary atlas does not transpose its source incidence")]
    MalformedCoboundaryAtlas,
    #[error("receiver section is not closed under the exact boundary")]
    ReceiverSectionNotClosed,
    #[error("receiver section witness is absent at {0:?}")]
    MissingWitness(HolonicCellAddress),
    #[error("receiver source witness population differs from source incidence")]
    WitnessPopulationMismatch,
    #[error("phase germ {0:?} is absent")]
    MissingPhaseGerm(ReceiverPhaseGermId),
    #[error("phase connection {0:?} is absent")]
    MissingPhaseConnection(ReceiverPhaseConnectionId),
    #[error("phase cycle {0:?} is absent")]
    MissingPhaseCycle(ReceiverPhaseCycleId),
    #[error("holonic quotient {0:?} is absent")]
    MissingQuotient(HolonicQuotientId),
    #[error("holonic overlap {0:?} is absent")]
    MissingOverlap(HolonicOverlapId),
    #[error("holonic quotient {0:?} is malformed")]
    MalformedQuotient(HolonicQuotientId),
    #[error("holonic overlap {0:?} is malformed")]
    MalformedOverlap(HolonicOverlapId),
    #[error("source graph atlas differs from a fresh complete mount")]
    SourceAtlasGradeMismatch,
    #[error("source graph populations differ from the supplied standing")]
    SourcePopulationMismatch,
    #[error("algebraic presentation at receiver grain {0:?} does not carry the indexed incidence")]
    AlgebraicPresentationIncidenceMismatch(ReceiverGrainId),
    #[error(
        "algebraic presentation at receiver grain {0:?} has lineage absent from the source atlas"
    )]
    AlgebraicPresentationLineageMismatch(ReceiverGrainId),
    #[error("restriction of algebraic region {0:?} is not boundary-closed")]
    AlgebraicRegionRestrictionNotClosed(CausalRegionId),
    #[error("source event {0:?} was already mounted")]
    RepeatedSourceEvent(EventId),
    #[error("source event {0:?} is absent from the supplied standing")]
    SourceRadiationAbsent(EventId),
    #[error("source cell {0:?} was already mounted")]
    RepeatedSourceCell(HolonicCellAddress),
    #[error("source quotient {0:?} was already mounted")]
    RepeatedQuotient(HolonicQuotientId),
    #[error("source overlap {0:?} was already mounted")]
    RepeatedOverlap(HolonicOverlapId),
    #[error("append-only source expected cell {expected:?}, but radiation supplied {received:?}")]
    NonappendOnlySourceCell {
        expected: CausalCellId,
        received: CausalCellId,
    },
    #[error("receiver {0:?} is already founded")]
    ReceiverAlreadyFounded(ReceiverId),
    #[error("receiver {0:?} has no standing graph section")]
    ReceiverNotFounded(ReceiverId),
    #[error("receiver event {0:?} was already enacted")]
    RepeatedReceiverEvent(EventId),
    #[error("receiver {receiver:?} chronology {received} does not follow {previous}")]
    NoncausalReceiverChronology {
        receiver: ReceiverId,
        previous: u64,
        received: u64,
    },
    #[error("receiver traversal must contain its source and target")]
    TraversalTooShort,
    #[error("receiver traversal does not begin at the contemporary focus")]
    TraversalDoesNotStartAtFocus,
    #[error("receiver traversal from {from:?} to {target:?} has no source incidence")]
    NonincidentTraversal {
        from: HolonicCellAddress,
        target: HolonicCellAddress,
    },
    #[error(
        "quotient {quotient:?} refines target {expected:?}, not contemporary focus {received:?}"
    )]
    RefinementTargetMismatch {
        quotient: HolonicQuotientId,
        expected: HolonicCellAddress,
        received: HolonicCellAddress,
    },
    #[error(
        "quotient {quotient:?} coarsens source {expected:?}, not contemporary focus {received:?}"
    )]
    CoarseningSourceMismatch {
        quotient: HolonicQuotientId,
        expected: HolonicCellAddress,
        received: HolonicCellAddress,
    },
    #[error("receiver section omits part of quotient {0:?}'s exact source fiber")]
    IncompleteQuotientFiber(HolonicQuotientId),
    #[error("receiver frame combines several grains without a caused quotient")]
    MixedReceiverGrains,
    #[error("receiver frame is malformed")]
    MalformedReceiverFrame,
    #[error("receiver graph section is malformed")]
    MalformedReceiverSection,
    #[error("receiver graph section does not exactly restrict its source coordinate presentation")]
    MalformedAlgebraicReceiverSection,
    #[error("receiver graph section analysis differs from its exact received support")]
    MalformedReceiverAnalysis,
    #[error("receiver graph transition lineage is malformed")]
    MalformedReceiverLineage,
    #[error("source standing has no chronology")]
    MissingSourceChronology,
    #[error("receiver graph carrier overflowed")]
    CarrierOverflow,
    #[error(transparent)]
    Algebraic(#[from] CausalAlgebraicError),
    #[error(transparent)]
    Holonic(#[from] HolonicComplexError),
}

#[cfg(test)]
mod tests {
    use relational_geometry::{RatVec3, ReceiverId};

    use super::*;
    use crate::{
        CausalEndHand, CausalWorld, EvolutionShape, ExactRgb, GradedAlgebraPresentation,
        ImageExtent, RayFamily, ReceiverHolonicComplexEvent, ReceiverHolonicComplexLaw,
        ReceiverPhaseSectionOccurrence,
    };

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
        ReceiverPhaseSectionOccurrence {
            source_image: None,
            source_lineage: lineage,
            receiver: ReceiverId(lineage),
            rays: rays(),
            extent,
            samples,
        }
    }

    fn populated_world() -> (
        CausalWorld<ReceiverHolonicComplexLaw>,
        ReceiverHolonicComplexRadiation,
    ) {
        let law = ReceiverHolonicComplexLaw::default();
        let mut world = CausalWorld::new(law.clone(), law.initial_standing());
        let receipt = world
            .receive(&ReceiverHolonicComplexEvent {
                event: EventId(1),
                chronology: 1,
                sections: vec![textured_section(1)],
            })
            .unwrap();
        (
            world,
            receipt
                .radiation
                .first()
                .expect("one holonic event emits one radiation")
                .clone(),
        )
    }

    fn simplex_source() -> (HolonicGraphSourceAtlas, HolonicQuotientId, HolonicQuotient) {
        let event = EventId(1);
        let grain_zero = ReceiverGrainId(0);
        let grain_one = ReceiverGrainId(1);
        let mut fine = GradedCausalComplex::default();
        let simplex = fine
            .found_simplex("triangle", event, ["a", "b", "c"])
            .unwrap();
        let source_closed_hull = fine.closed_hull([simplex.apex]).unwrap();
        let mut coarse = GradedCausalComplex::default();
        let target_cell = coarse
            .found_cell(
                "triangle received whole",
                BTreeSet::from([event]),
                0,
                CausalChain::default(),
            )
            .unwrap();
        let quotient_id = HolonicQuotientId(1);
        let quotient = HolonicQuotient {
            id: quotient_id,
            caused_by: event,
            source_apex: HolonicCellAddress {
                grain: grain_zero,
                cell: simplex.apex,
            },
            source_closed_hull,
            target: HolonicCellAddress {
                grain: grain_one,
                cell: target_cell,
            },
        };
        let source = HolonicGraphSourceAtlas::from_algebraic_grains(
            BTreeMap::from([(grain_zero, fine), (grain_one, coarse)]),
            BTreeMap::from([(quotient_id, quotient.clone())]),
            BTreeMap::new(),
            Some(1),
        )
        .unwrap();
        (source, quotient_id, quotient)
    }

    fn algebraic_simplex_source() -> (
        HolonicGraphSourceAtlas,
        HolonicCellAddress,
        CausalRegionId,
        CausalEndId,
    ) {
        let mut evolution = EvolutionShape::default();
        let boundary = evolution.add_boundary("algebraic receiver boundary");
        let law = evolution
            .add_law(
                "found algebraic receiver section",
                vec![boundary],
                vec![boundary],
            )
            .unwrap();
        let event = evolution.add_occurrence(law).unwrap();
        let mut incidence = GradedCausalComplex::default();
        let simplex = incidence
            .found_simplex("coordinate triangle", event, ["a", "b", "c"])
            .unwrap();
        let mut presentation = CausalAlgebraicPresentation::new(evolution, incidence).unwrap();
        let mut coordinates = GradedAlgebraPresentation::default();
        coordinates
            .add_generator("lambda", 1, BTreeSet::from([event]))
            .unwrap();
        let algebra = presentation
            .add_local_algebra("receiver-local lambda", event, coordinates)
            .unwrap();
        let support = presentation.incidence.closed_hull([simplex.apex]).unwrap();
        let region = presentation
            .found_region(
                "whole coordinate triangle",
                support,
                BTreeSet::from([algebra]),
                event,
            )
            .unwrap();
        let end = presentation
            .found_end(
                "opposed face",
                region,
                CausalEndHand::Outgoing,
                CausalChain::single(simplex.apex, ComparativeMultiplicity::positive(1_u8)),
                event,
            )
            .unwrap();
        let grain = ReceiverGrainId(7);
        let focus = HolonicCellAddress {
            grain,
            cell: simplex.vertices[0],
        };
        let source = HolonicGraphSourceAtlas::from_algebraic_presentations(
            BTreeMap::from([(grain, presentation)]),
            BTreeMap::new(),
            BTreeMap::new(),
            Some(1),
        )
        .unwrap();
        (source, focus, region, end)
    }

    #[test]
    fn sparse_coboundary_is_the_exact_transpose_and_local_sections_close() {
        let event = EventId(1);
        let mut incidence = GradedCausalComplex::default();
        let simplex = incidence
            .found_simplex("triangle", event, ["a", "b", "c"])
            .unwrap();
        let atlas = ExactIncidenceAtlas::new(incidence.clone()).unwrap();

        for lower in incidence.cells().keys() {
            let mut direct = CausalChain::default();
            for (upper, body) in incidence.cells() {
                if let Some(coefficient) = body.boundary.coefficients().get(lower) {
                    direct.add_term(*upper, coefficient.clone());
                }
            }
            assert_eq!(atlas.coboundary(*lower).unwrap(), &direct);
        }

        let section = atlas.receive_section([simplex.apex], 0).unwrap();
        assert_eq!(
            section.support,
            incidence.closed_hull([simplex.apex]).unwrap()
        );
        assert!(incidence.is_closed_support(&section.support).unwrap());
        assert_eq!(section.work.coboundary_lookups, BigUint::zero());
    }

    #[test]
    fn quotient_point_refines_dilates_retains_and_coarsens_with_exact_lineage() {
        let (source, quotient, quotient_body) = simplex_source();
        let receiver = ReceiverId(900);
        let mut atlas = ReceiverGraphAtlas::from_source(source).unwrap();

        let founded = atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(100),
                chronology: 1,
                receiver,
                deed: ReceiverGraphDeed::Found {
                    focus: quotient_body.target,
                    upper_horizon: 0,
                },
            })
            .unwrap();
        assert_eq!(founded.transition.change, ReceiverGraphChange::Founded);
        let coarse = atlas.section(receiver).unwrap();
        assert_eq!(coarse.cells.len(), 1);
        assert_eq!(
            coarse.cells[&quotient_body.target].source_fiber.len(),
            quotient_body.source_closed_hull.len()
        );

        let refined = atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(101),
                chronology: 2,
                receiver,
                deed: ReceiverGraphDeed::Refine {
                    quotient,
                    upper_horizon: 0,
                },
            })
            .unwrap();
        assert_eq!(refined.transition.change, ReceiverGraphChange::Refined);
        let fine = atlas.section(receiver).unwrap().clone();
        assert_eq!(fine.cells.len(), quotient_body.source_closed_hull.len());
        assert_eq!(fine.analysis.euler_characteristic, BigInt::one());
        assert_eq!(fine.analysis.graph_cycle_rank, Some(BigUint::one()));

        let dilated = atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(102),
                chronology: 3,
                receiver,
                deed: ReceiverGraphDeed::Dilate { upper_horizon: 1 },
            })
            .unwrap();
        assert_eq!(dilated.transition.change, ReceiverGraphChange::Dilated);
        assert!(dilated.transition.delta.removed.is_empty());
        assert_eq!(
            dilated.query_work.reused_cells,
            BigUint::from(dilated.transition.delta.retained.len())
        );
        assert_eq!(
            dilated.query_work.materialized_cells,
            BigUint::from(dilated.transition.delta.added.len())
        );
        for address in &dilated.transition.delta.retained {
            assert!(Arc::ptr_eq(
                &fine.cells[address],
                &atlas.section(receiver).unwrap().cells[address],
            ));
        }

        let retained = atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(103),
                chronology: 4,
                receiver,
                deed: ReceiverGraphDeed::Retain,
            })
            .unwrap();
        assert_eq!(retained.transition.change, ReceiverGraphChange::Retained);
        assert_eq!(
            retained.query_work,
            ReceiverGraphQueryWork {
                reused_cells: BigUint::from(atlas.section(receiver).unwrap().cells.len()),
                ..ReceiverGraphQueryWork::default()
            }
        );
        assert!(retained.transition.delta.added.is_empty());
        assert!(retained.transition.delta.removed.is_empty());

        let coarsened = atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(104),
                chronology: 5,
                receiver,
                deed: ReceiverGraphDeed::Coarsen {
                    quotient,
                    upper_horizon: 0,
                },
            })
            .unwrap();
        assert_eq!(coarsened.transition.change, ReceiverGraphChange::Coarsened);
        assert_eq!(
            atlas.section(receiver).unwrap().frame.focus,
            quotient_body.target
        );
        assert_eq!(atlas.section(receiver).unwrap().transitions.len(), 5);
    }

    #[test]
    fn receiver_dilation_carries_exact_coordinate_regions_and_opposed_ends() {
        let (source, focus, region, end) = algebraic_simplex_source();
        let receiver = ReceiverId(903);
        let mut atlas = ReceiverGraphAtlas::from_source(source).unwrap();
        atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(130),
                chronology: 1,
                receiver,
                deed: ReceiverGraphDeed::Found {
                    focus,
                    upper_horizon: 0,
                },
            })
            .unwrap();
        let local = atlas.section(receiver).unwrap().algebraic.as_ref().unwrap();
        assert_eq!(local.local_algebras.len(), 1);
        assert_eq!(
            local.regions[&region].received_support,
            BTreeSet::from([focus.cell])
        );
        assert!(!local.regions[&region].complete);
        assert!(local.ends[&end].received_section.is_zero());
        assert!(!local.ends[&end].complete);

        atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(131),
                chronology: 2,
                receiver,
                deed: ReceiverGraphDeed::Dilate { upper_horizon: 2 },
            })
            .unwrap();
        let section = atlas.section(receiver).unwrap();
        let local = section.algebraic.as_ref().unwrap();
        assert!(local.regions[&region].complete);
        assert!(local.ends[&end].complete);
        assert_eq!(
            local.ends[&end].received_section,
            local.ends[&end].body.section
        );
        assert_eq!(section.analysis.complete_algebraic_regions, BigUint::one());
        assert_eq!(
            section.analysis.complete_causal_end_sections,
            BigUint::one()
        );
    }

    #[test]
    fn traversal_requires_actual_incidence_and_carries_the_path() {
        let (source, quotient, quotient_body) = simplex_source();
        let receiver = ReceiverId(901);
        let mut atlas = ReceiverGraphAtlas::from_source(source).unwrap();
        atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(110),
                chronology: 1,
                receiver,
                deed: ReceiverGraphDeed::Found {
                    focus: quotient_body.target,
                    upper_horizon: 0,
                },
            })
            .unwrap();
        atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(111),
                chronology: 2,
                receiver,
                deed: ReceiverGraphDeed::Refine {
                    quotient,
                    upper_horizon: 0,
                },
            })
            .unwrap();

        let face = quotient_body.source_apex;
        let face_body = atlas.source().cell(face).unwrap();
        let edge = *face_body.boundary.support().iter().next().unwrap();
        let edge_address = HolonicCellAddress {
            grain: face.grain,
            cell: edge,
        };
        let edge_body = atlas.source().cell(edge_address).unwrap();
        let vertex = *edge_body.boundary.support().iter().next().unwrap();
        let vertex_address = HolonicCellAddress {
            grain: face.grain,
            cell: vertex,
        };

        let traversed = atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(112),
                chronology: 3,
                receiver,
                deed: ReceiverGraphDeed::Traverse {
                    path: vec![face, edge_address, vertex_address],
                    upper_horizon: 1,
                },
            })
            .unwrap();
        assert_eq!(traversed.transition.change, ReceiverGraphChange::Traversed);
        assert_eq!(atlas.section(receiver).unwrap().frame.focus, vertex_address);

        let nonincident = quotient_body
            .source_closed_hull
            .iter()
            .copied()
            .find(|cell| {
                let address = HolonicCellAddress {
                    grain: face.grain,
                    cell: *cell,
                };
                address != vertex_address
                    && !atlas
                        .source()
                        .are_incident(vertex_address, address)
                        .unwrap()
            })
            .map(|cell| HolonicCellAddress {
                grain: face.grain,
                cell,
            })
            .unwrap();
        let result = atlas.receive(&ReceiverGraphRequest {
            event: EventId(113),
            chronology: 4,
            receiver,
            deed: ReceiverGraphDeed::Traverse {
                path: vec![vertex_address, nonincident],
                upper_horizon: 0,
            },
        });
        assert!(matches!(
            result,
            Err(GraphReceiverError::NonincidentTraversal { .. })
        ));
        assert_eq!(atlas.section(receiver).unwrap().event, EventId(112));
    }

    #[test]
    fn source_radiation_advances_the_sparse_atlas_and_grades_against_fresh_mount() {
        let (mut world, first) = populated_world();
        let mut atlas = ReceiverGraphAtlas::mount(world.standing()).unwrap();
        assert!(!first.caused_phase_germs.is_empty());

        let second = world
            .receive(&ReceiverHolonicComplexEvent {
                event: EventId(2),
                chronology: 2,
                sections: vec![textured_section(2)],
            })
            .unwrap();
        let radiation = second.radiation.first().unwrap();
        let receipt = atlas.advance_source(world.standing(), radiation).unwrap();
        assert_eq!(receipt.source.event, EventId(2));
        assert!(!receipt.source.changed_cells.is_empty());
        atlas.source().grade_against(world.standing()).unwrap();
    }

    #[test]
    fn complete_receiver_graph_atlas_rests_and_remounts_exactly() {
        let (source, _, quotient) = simplex_source();
        let target = quotient.target;
        let receiver = ReceiverId(902);
        let mut atlas = ReceiverGraphAtlas::from_source(source).unwrap();
        atlas
            .receive(&ReceiverGraphRequest {
                event: EventId(120),
                chronology: 1,
                receiver,
                deed: ReceiverGraphDeed::Found {
                    focus: target,
                    upper_horizon: 0,
                },
            })
            .unwrap();
        let encoded = ron::ser::to_string(&atlas).unwrap();
        let remounted: ReceiverGraphAtlas = ron::from_str(&encoded).unwrap();
        assert_eq!(remounted, atlas);
        remounted.validate().unwrap();
    }
}
