//! One bounded source-native incidence complex at a single actual event.
//!
//! Cell identifiers are event-local addresses only. Storage position and identifier magnitude
//! carry no order. Order exists solely in a cell's declared dependency rank, oriented incidence,
//! and the slots around a receiving boundary or exposed port. Topological dimension and
//! receiver-relative constituent grain are independent coordinates.

use crate::manifold::{atom_node, compose_place, Node};
use crate::num::Cog;

/// Event-local address of one presently participating cell. It survives only for the borrowed
/// event cut and is never lineage, chronology, provenance, or semantic identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EventCellId(u64);

impl EventCellId {
    pub const fn new(value: u64) -> Self {
        Self(value)
    }

    pub const fn ordinal(self) -> u64 {
        self.0
    }
}

/// One material cell. `dependency_rank` orders the source-declared dependency relation inside the
/// one external event. `dimension` is boundary degree. `grain` is receiver-relative constituent
/// scale. A source may align them, but the event carrier never infers one from another.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EventCell {
    id: EventCellId,
    dependency_rank: u32,
    dimension: u32,
    grain: u32,
    relation: Cog,
}

impl EventCell {
    /// Common aligned chart in which the source intentionally uses boundary degree as its local
    /// constituent grain. This is a declared special case, not an inference made while receiving.
    pub const fn new(id: EventCellId, dependency_rank: u32, dimension: u32, relation: Cog) -> Self {
        Self::situated(id, dependency_rank, dimension, dimension, relation)
    }

    /// Fully situated cell with independently supplied rank, dimension, and constituent grain.
    pub const fn situated(
        id: EventCellId,
        dependency_rank: u32,
        dimension: u32,
        grain: u32,
        relation: Cog,
    ) -> Self {
        Self {
            id,
            dependency_rank,
            dimension,
            grain,
            relation,
        }
    }

    pub const fn id(self) -> EventCellId {
        self.id
    }

    pub const fn dependency_rank(self) -> u32 {
        self.dependency_rank
    }

    pub const fn dimension(self) -> u32 {
        self.dimension
    }

    pub const fn grain(self) -> u32 {
        self.grain
    }

    pub const fn relation(self) -> Cog {
        self.relation
    }

    pub fn node(self) -> Node {
        atom_node(self.relation)
    }
}

/// The two oriented coefficients of one incidence. They are local hands, not global signs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(i8)]
pub enum IncidenceHand {
    Against = -1,
    With = 1,
}

impl IncidenceHand {
    pub const fn coefficient(self) -> i64 {
        self as i8 as i64
    }

    pub const fn reversed(self) -> Self {
        match self {
            Self::Against => Self::With,
            Self::With => Self::Against,
        }
    }
}

/// Boundary incidence raises topological dimension at one co-present dependency rank. Dependency
/// incidence raises dependency rank. A rewrite-interface incidence is the dependency which the
/// source explicitly declares to be preserved by that local rewrite. All remain inside one
/// external event; none is inferred from storage order or equal values.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IncidenceKind {
    Boundary,
    Dependency,
    RewriteInterface,
}

/// One actual oriented incidence. `slot` is the source-supplied local boundary coordinate at the
/// target. It orders composition only among incidences entering that target; slice position and
/// cell identifiers never do.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OrientedIncidence {
    from: EventCellId,
    to: EventCellId,
    kind: IncidenceKind,
    hand: IncidenceHand,
    slot: u32,
}

impl OrientedIncidence {
    pub const fn boundary(
        lower: EventCellId,
        upper: EventCellId,
        hand: IncidenceHand,
        slot: u32,
    ) -> Self {
        Self {
            from: lower,
            to: upper,
            kind: IncidenceKind::Boundary,
            hand,
            slot,
        }
    }

    pub const fn dependency(
        before: EventCellId,
        after: EventCellId,
        hand: IncidenceHand,
        slot: u32,
    ) -> Self {
        Self {
            from: before,
            to: after,
            kind: IncidenceKind::Dependency,
            hand,
            slot,
        }
    }

    pub const fn rewrite_interface(
        before: EventCellId,
        after: EventCellId,
        hand: IncidenceHand,
        slot: u32,
    ) -> Self {
        Self {
            from: before,
            to: after,
            kind: IncidenceKind::RewriteInterface,
            hand,
            slot,
        }
    }

    pub const fn from(self) -> EventCellId {
        self.from
    }

    pub const fn to(self) -> EventCellId {
        self.to
    }

    pub const fn kind(self) -> IncidenceKind {
        self.kind
    }

    pub const fn hand(self) -> IncidenceHand {
        self.hand
    }

    pub const fn slot(self) -> u32 {
        self.slot
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventPortKind {
    Ingress,
    Exposed,
}

/// One source boundary port. Plural ingress and exposed cells remain plural; `slot` supplies only
/// the local order of the declared boundary composition.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EventPort {
    cell: EventCellId,
    kind: EventPortKind,
    hand: IncidenceHand,
    slot: u32,
}

impl EventPort {
    pub const fn ingress(cell: EventCellId, hand: IncidenceHand, slot: u32) -> Self {
        Self {
            cell,
            kind: EventPortKind::Ingress,
            hand,
            slot,
        }
    }

    pub const fn exposed(cell: EventCellId, hand: IncidenceHand, slot: u32) -> Self {
        Self {
            cell,
            kind: EventPortKind::Exposed,
            hand,
            slot,
        }
    }

    pub const fn cell(self) -> EventCellId {
        self.cell
    }

    pub const fn kind(self) -> EventPortKind {
        self.kind
    }

    pub const fn hand(self) -> IncidenceHand {
        self.hand
    }

    pub const fn slot(self) -> u32 {
        self.slot
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EventComplexError {
    Empty,
    RepeatedCell(EventCellId),
    MissingCell(EventCellId),
    RepeatedIncidenceSlot(EventCellId, u32),
    RepeatedPortSlot(EventPortKind, u32),
    MissingPort(EventPortKind, u32),
    InvalidPortSpecies,
    InvalidBoundary(EventCellId, EventCellId),
    InvalidDependency(EventCellId, EventCellId),
    MissingBoundary(EventCellId),
    BoundaryOfBoundary(EventCellId, EventCellId),
    MissingIngress,
    MissingExposed,
    MixedExposedGrain(u32, u32),
    Extent,
}

/// A validated borrowed event complex. Validation is allocation-free and establishes a strict
/// dimension ascent for boundary incidence and dependency-rank ascent for event action, so
/// recursive composition cannot cycle.
#[derive(Clone, Copy)]
pub struct EventComplex<'a> {
    cells: &'a [EventCell],
    incidences: &'a [OrientedIncidence],
    ports: &'a [EventPort],
    cells_indexed: bool,
    incidences_indexed: bool,
    ports_indexed: bool,
}

/// Why one otherwise-valid event complex cannot be read as a discrete local map. A germ is a
/// stricter face of an event: ingress lies on the first internal rank, exposure lies on the last,
/// and every dependency names one immediately composed source-to-image step. Boundary incidence
/// may still raise dimension inside any rank.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiscreteGermError {
    Static,
    MissingAction,
    IngressOutsideDomain(EventCellId),
    ExposedOutsideImage(EventCellId),
    NonlocalDependency(EventCellId, EventCellId),
}

/// An allocation-free situated read of the local action already carried by [`EventComplex`].
/// This adds no second representation and no cross-event matching rule. Dependency incidence is
/// the exact finite map supplied by the source; its forward and inverse multiplicities expose
/// regular continuation, deletion, folding, and branching at this event. Transporting the germ
/// onto a different later neighborhood still requires a source-carried rebase.
#[derive(Clone, Copy)]
pub struct DiscreteEventGerm<'a> {
    complex: EventComplex<'a>,
    domain_rank: u32,
    image_rank: u32,
}

impl<'a> DiscreteEventGerm<'a> {
    pub fn new(complex: EventComplex<'a>) -> Result<Self, DiscreteGermError> {
        let mut domain_rank = u32::MAX;
        let mut image_rank = 0u32;
        for cell in complex.cells() {
            domain_rank = domain_rank.min(cell.dependency_rank());
            image_rank = image_rank.max(cell.dependency_rank());
        }
        if domain_rank == image_rank {
            return Err(DiscreteGermError::Static);
        }

        let mut dependencies = 0u64;
        for incidence in complex.incidences() {
            if !incidence.kind().is_dependency() {
                continue;
            }
            dependencies = dependencies
                .checked_add(1)
                .ok_or(DiscreteGermError::MissingAction)?;
            let from = complex
                .cell(incidence.from())
                .expect("EventComplex retained its validated dependency source");
            let to = complex
                .cell(incidence.to())
                .expect("EventComplex retained its validated dependency image");
            if from.dependency_rank().checked_add(1) != Some(to.dependency_rank()) {
                return Err(DiscreteGermError::NonlocalDependency(
                    incidence.from(),
                    incidence.to(),
                ));
            }
        }
        if dependencies == 0 {
            return Err(DiscreteGermError::MissingAction);
        }

        for port in complex.ports() {
            let cell = complex
                .cell(port.cell())
                .expect("EventComplex retained its validated port cell");
            match port.kind() {
                EventPortKind::Ingress if cell.dependency_rank() != domain_rank => {
                    return Err(DiscreteGermError::IngressOutsideDomain(port.cell()));
                }
                EventPortKind::Exposed if cell.dependency_rank() != image_rank => {
                    return Err(DiscreteGermError::ExposedOutsideImage(port.cell()));
                }
                EventPortKind::Ingress | EventPortKind::Exposed => {}
            }
        }

        Ok(Self {
            complex,
            domain_rank,
            image_rank,
        })
    }

    pub const fn complex(self) -> EventComplex<'a> {
        self.complex
    }

    pub const fn domain_rank(self) -> u32 {
        self.domain_rank
    }

    pub const fn image_rank(self) -> u32 {
        self.image_rank
    }

    pub const fn rank_count(self) -> u64 {
        self.image_rank as u64 - self.domain_rank as u64 + 1
    }

    pub fn dependency_count(self) -> u64 {
        self.complex
            .incidences()
            .iter()
            .filter(|incidence| incidence.kind().is_dependency())
            .count() as u64
    }

    /// Number of immediately later branches carried from this exact source cell.
    pub fn forward_multiplicity(self, cell: EventCellId) -> Option<u64> {
        self.complex.cell(cell)?;
        Some(
            self.complex
                .incidences()
                .iter()
                .filter(|incidence| incidence.kind().is_dependency() && incidence.from() == cell)
                .count() as u64,
        )
    }

    /// Number of immediately prior sheets carried into this exact image cell.
    pub fn inverse_multiplicity(self, cell: EventCellId) -> Option<u64> {
        self.complex.cell(cell)?;
        Some(
            self.complex
                .incidences()
                .iter()
                .filter(|incidence| incidence.kind().is_dependency() && incidence.to() == cell)
                .count() as u64,
        )
    }

    pub fn preserved_interface_count(self) -> u64 {
        self.complex
            .incidences()
            .iter()
            .filter(|incidence| incidence.kind() == IncidenceKind::RewriteInterface)
            .count() as u64
    }
}

impl IncidenceKind {
    pub const fn is_dependency(self) -> bool {
        matches!(self, Self::Dependency | Self::RewriteInterface)
    }
}

impl<'a> EventComplex<'a> {
    pub fn new(
        cells: &'a [EventCell],
        incidences: &'a [OrientedIncidence],
        ports: &'a [EventPort],
    ) -> Result<Self, EventComplexError> {
        if cells.is_empty() {
            return Err(EventComplexError::Empty);
        }
        let candidate = Self {
            cells,
            incidences,
            ports,
            cells_indexed: cells
                .windows(2)
                .all(|pair| pair[0].id.ordinal() <= pair[1].id.ordinal()),
            incidences_indexed: incidences
                .windows(2)
                .all(|pair| incidence_key(pair[0]) <= incidence_key(pair[1])),
            ports_indexed: ports
                .windows(2)
                .all(|pair| port_key(pair[0]) <= port_key(pair[1])),
        };
        candidate.validate()?;
        Ok(candidate)
    }

    pub const fn cells(self) -> &'a [EventCell] {
        self.cells
    }

    pub const fn incidences(self) -> &'a [OrientedIncidence] {
        self.incidences
    }

    pub const fn ports(self) -> &'a [EventPort] {
        self.ports
    }

    /// Resolve one source-declared boundary coordinate. The numeric slot is local to the named
    /// boundary kind; it is not a cell address, storage position, chronology, or inferred match.
    pub fn port(self, kind: EventPortKind, slot: u32) -> Option<EventPort> {
        if let Some(ports) = self.indexed_ports(kind) {
            return ports.iter().copied().find(|port| port.slot == slot);
        }
        self.ports
            .iter()
            .copied()
            .find(|port| port.kind == kind && port.slot == slot)
    }

    /// One point-chart projection of the constituent exposed at a declared boundary coordinate.
    /// Interior incidence is composed vertically, but this `Node` is not the constituent's live
    /// cellular body and cannot stand in for it at a regional hand.
    pub fn port_node_projection(
        self,
        kind: EventPortKind,
        slot: u32,
    ) -> Result<Node, EventComplexError> {
        let port = self
            .port(kind, slot)
            .ok_or(EventComplexError::MissingPort(kind, slot))?;
        self.composed_cell_node(port.cell)
    }

    pub fn cell(self, id: EventCellId) -> Option<EventCell> {
        if self.cells_indexed {
            self.cells
                .binary_search_by_key(&id.ordinal(), |cell| cell.id.ordinal())
                .ok()
                .map(|at| self.cells[at])
        } else {
            self.cells.iter().copied().find(|cell| cell.id == id)
        }
    }

    pub fn resolving_cells(self) -> u64 {
        self.cells
            .iter()
            .filter(|cell| cell.relation.mag != 0)
            .count() as u64
    }

    pub fn compound_cells(self) -> u64 {
        self.cells.iter().filter(|cell| cell.dimension != 0).count() as u64
    }

    pub fn wholly_flat(self) -> bool {
        self.cells.iter().all(|cell| cell.relation.mag == 0)
    }

    /// The source face used only to attach and relate this event at its outer boundary. It is
    /// derived from the declared exposed cells and their slots, never from slice order.
    pub fn emanated_node(self) -> Result<Node, EventComplexError> {
        self.compose_ports(EventPortKind::Exposed)
    }

    /// The first live material at ingress, used only to found an unborn lineage's gauge anchor.
    pub fn ingress_node(self) -> Result<Node, EventComplexError> {
        self.compose_ports(EventPortKind::Ingress)
    }

    /// First resolving ingress constituent in the source-declared port frame. This locates an
    /// unborn lineage's gauge anchor without treating cell storage or identifier magnitude as
    /// chronology. When every ingress constituent is flat, the complete ingress face is the
    /// honest anchor.
    pub fn ingress_anchor_node(self) -> Result<Node, EventComplexError> {
        let ingress = self.ingress_node()?;
        let mut after = None;
        loop {
            let Some(port) = self.next_port(EventPortKind::Ingress, after) else {
                break;
            };
            let constituent = self.composed_cell_node(port.cell)?;
            if constituent.well.mag != 0 {
                return Ok(constituent);
            }
            after = Some(port.slot);
        }
        Ok(ingress)
    }

    /// The source event is the cell whose declared exposed boundary this complex supplies. Every
    /// exposed member must therefore have one grain, and the completed event stands exactly one
    /// grain above it.
    pub fn outer_grain(self) -> Result<u32, EventComplexError> {
        let mut exposed = None;
        for port in self
            .ports
            .iter()
            .copied()
            .filter(|port| port.kind == EventPortKind::Exposed)
        {
            let grain = self
                .cell(port.cell)
                .ok_or(EventComplexError::MissingCell(port.cell))?
                .grain;
            match exposed {
                None => exposed = Some(grain),
                Some(prior) if prior == grain => {}
                Some(prior) => {
                    return Err(EventComplexError::MixedExposedGrain(prior, grain));
                }
            }
        }
        exposed
            .ok_or(EventComplexError::MissingExposed)?
            .checked_add(1)
            .ok_or(EventComplexError::Extent)
    }

    /// Complete source cell including every lower boundary and earlier internal dependency. This
    /// is a material boundary factorization, not a declaration that Soma has already recognized or
    /// completed the construction in its receiver.
    pub fn composed_cell_node(self, id: EventCellId) -> Result<Node, EventComplexError> {
        let cell = self.cell(id).ok_or(EventComplexError::MissingCell(id))?;
        let mut node = cell.node();
        let mut after = None;
        loop {
            let next = self.next_incidence_to(id, after);
            let Some(incidence) = next else {
                break;
            };
            let constituent = self.composed_cell_node(incidence.from)?;
            node = compose_oriented(node, constituent, incidence.hand)?;
            after = Some(incidence.slot);
        }
        Ok(node)
    }

    pub fn incidence_nodes(
        self,
        incidence: OrientedIncidence,
    ) -> Result<(Node, Node), EventComplexError> {
        let from = self.composed_cell_node(incidence.from)?;
        let to = self.composed_cell_node(incidence.to)?;
        Ok(match incidence.hand {
            IncidenceHand::With => (from, to),
            IncidenceHand::Against => (to, from),
        })
    }

    fn compose_ports(self, kind: EventPortKind) -> Result<Node, EventComplexError> {
        let mut node = None;
        let mut after = None;
        loop {
            let port = self.next_port(kind, after);
            let Some(port) = port else {
                break;
            };
            let constituent = self.composed_cell_node(port.cell)?;
            node = Some(match node {
                None => constituent,
                Some(current) => compose_oriented(current, constituent, port.hand)?,
            });
            after = Some(port.slot);
        }
        node.ok_or(match kind {
            EventPortKind::Ingress => EventComplexError::MissingIngress,
            EventPortKind::Exposed => EventComplexError::MissingExposed,
        })
    }

    fn next_incidence_to(
        self,
        target: EventCellId,
        after: Option<u32>,
    ) -> Option<OrientedIncidence> {
        if let Some(incidences) = self.indexed_incidences_to(target) {
            return incidences
                .iter()
                .copied()
                .find(|incidence| after.is_none_or(|slot| incidence.slot > slot));
        }
        self.incidences
            .iter()
            .copied()
            .filter(|incidence| {
                incidence.to == target && after.is_none_or(|slot| incidence.slot > slot)
            })
            .min_by_key(|incidence| incidence.slot)
    }

    fn next_port(self, kind: EventPortKind, after: Option<u32>) -> Option<EventPort> {
        if let Some(ports) = self.indexed_ports(kind) {
            return ports
                .iter()
                .copied()
                .find(|port| after.is_none_or(|slot| port.slot > slot));
        }
        self.ports
            .iter()
            .copied()
            .filter(|port| port.kind == kind && after.is_none_or(|slot| port.slot > slot))
            .min_by_key(|port| port.slot)
    }

    fn indexed_incidences_to(self, target: EventCellId) -> Option<&'a [OrientedIncidence]> {
        if !self.incidences_indexed {
            return None;
        }
        let target = target.ordinal();
        let start = self
            .incidences
            .partition_point(|incidence| incidence.to.ordinal() < target);
        let end = self.incidences[start..]
            .partition_point(|incidence| incidence.to.ordinal() == target)
            + start;
        Some(&self.incidences[start..end])
    }

    fn indexed_ports(self, kind: EventPortKind) -> Option<&'a [EventPort]> {
        if !self.ports_indexed {
            return None;
        }
        let kind = port_kind_key(kind);
        let start = self
            .ports
            .partition_point(|port| port_kind_key(port.kind) < kind);
        let end =
            self.ports[start..].partition_point(|port| port_kind_key(port.kind) == kind) + start;
        Some(&self.ports[start..end])
    }

    fn validate(self) -> Result<(), EventComplexError> {
        for (at, cell) in self.cells.iter().enumerate() {
            let repeated = if self.cells_indexed {
                at != 0 && self.cells[at - 1].id == cell.id
            } else {
                self.cells[..at].iter().any(|prior| prior.id == cell.id)
            };
            if repeated {
                return Err(EventComplexError::RepeatedCell(cell.id));
            }
        }

        for (at, incidence) in self.incidences.iter().copied().enumerate() {
            let from = self
                .cell(incidence.from)
                .ok_or(EventComplexError::MissingCell(incidence.from))?;
            let to = self
                .cell(incidence.to)
                .ok_or(EventComplexError::MissingCell(incidence.to))?;
            if if self.incidences_indexed {
                at != 0
                    && self.incidences[at - 1].to == incidence.to
                    && self.incidences[at - 1].slot == incidence.slot
            } else {
                self.incidences[..at]
                    .iter()
                    .any(|prior| prior.to == incidence.to && prior.slot == incidence.slot)
            } {
                return Err(EventComplexError::RepeatedIncidenceSlot(
                    incidence.to,
                    incidence.slot,
                ));
            }
            match incidence.kind {
                IncidenceKind::Boundary => {
                    if from.dependency_rank != to.dependency_rank
                        || from.dimension.checked_add(1) != Some(to.dimension)
                    {
                        return Err(EventComplexError::InvalidBoundary(from.id, to.id));
                    }
                }
                IncidenceKind::Dependency => {
                    if from.dependency_rank >= to.dependency_rank {
                        return Err(EventComplexError::InvalidDependency(from.id, to.id));
                    }
                }
                IncidenceKind::RewriteInterface => {
                    if from.dependency_rank >= to.dependency_rank || from.dimension != to.dimension
                    {
                        return Err(EventComplexError::InvalidDependency(from.id, to.id));
                    }
                }
            }
        }

        let mut ingress = false;
        let mut exposed = false;
        for (at, port) in self.ports.iter().copied().enumerate() {
            if self.cell(port.cell).is_none() {
                return Err(EventComplexError::MissingCell(port.cell));
            }
            if if self.ports_indexed {
                at != 0
                    && self.ports[at - 1].kind == port.kind
                    && self.ports[at - 1].slot == port.slot
            } else {
                self.ports[..at]
                    .iter()
                    .any(|prior| prior.kind == port.kind && prior.slot == port.slot)
            } {
                return Err(EventComplexError::RepeatedPortSlot(port.kind, port.slot));
            }
            ingress |= port.kind == EventPortKind::Ingress;
            exposed |= port.kind == EventPortKind::Exposed;
        }
        if !ingress {
            return Err(EventComplexError::MissingIngress);
        }
        if !exposed {
            return Err(EventComplexError::MissingExposed);
        }
        self.outer_grain()?;

        for cell in self
            .cells
            .iter()
            .copied()
            .filter(|cell| cell.dimension != 0)
        {
            let has_boundary = match self.indexed_incidences_to(cell.id) {
                Some(incidences) => incidences
                    .iter()
                    .any(|incidence| incidence.kind == IncidenceKind::Boundary),
                None => self.incidences.iter().any(|incidence| {
                    incidence.kind == IncidenceKind::Boundary && incidence.to == cell.id
                }),
            };
            if !has_boundary {
                return Err(EventComplexError::MissingBoundary(cell.id));
            }
        }

        if self.incidences_indexed {
            return self.validate_indexed_boundary_squared();
        }

        // A one-cell boundary carries equal opposed endpoint coefficient. Higher cells satisfy
        // partial(partial)=0 at every codimension-two constituent.
        for upper in self
            .cells
            .iter()
            .copied()
            .filter(|cell| cell.dimension != 0)
        {
            if upper.dimension == 1 {
                let sum = self
                    .incidences
                    .iter()
                    .filter(|incidence| {
                        incidence.kind == IncidenceKind::Boundary && incidence.to == upper.id
                    })
                    .try_fold(0i64, |sum, incidence| {
                        sum.checked_add(incidence.hand.coefficient())
                    })
                    .ok_or(EventComplexError::Extent)?;
                if sum != 0 {
                    return Err(EventComplexError::BoundaryOfBoundary(upper.id, upper.id));
                }
                continue;
            }
            for lower in self.cells.iter().copied().filter(|cell| {
                cell.dependency_rank == upper.dependency_rank
                    && cell.dimension.checked_add(2) == Some(upper.dimension)
            }) {
                let mut sum = 0i64;
                for outer in self.incidences.iter().copied().filter(|incidence| {
                    incidence.kind == IncidenceKind::Boundary && incidence.to == upper.id
                }) {
                    for inner in self.incidences.iter().copied().filter(|incidence| {
                        incidence.kind == IncidenceKind::Boundary
                            && incidence.from == lower.id
                            && incidence.to == outer.from
                    }) {
                        sum = sum
                            .checked_add(
                                outer
                                    .hand
                                    .coefficient()
                                    .checked_mul(inner.hand.coefficient())
                                    .ok_or(EventComplexError::Extent)?,
                            )
                            .ok_or(EventComplexError::Extent)?;
                    }
                }
                if sum != 0 {
                    return Err(EventComplexError::BoundaryOfBoundary(lower.id, upper.id));
                }
            }
        }
        Ok(())
    }

    fn validate_indexed_boundary_squared(self) -> Result<(), EventComplexError> {
        for upper in self
            .cells
            .iter()
            .copied()
            .filter(|cell| cell.dimension != 0)
        {
            let outer = self
                .indexed_incidences_to(upper.id)
                .expect("the indexed incidence span is available");
            if upper.dimension == 1 {
                let sum = outer
                    .iter()
                    .filter(|incidence| incidence.kind == IncidenceKind::Boundary)
                    .try_fold(0i64, |sum, incidence| {
                        sum.checked_add(incidence.hand.coefficient())
                    })
                    .ok_or(EventComplexError::Extent)?;
                if sum != 0 {
                    return Err(EventComplexError::BoundaryOfBoundary(upper.id, upper.id));
                }
                continue;
            }

            // Every codimension-two path supplies one candidate lower cell. Re-summing the small
            // local fan for that candidate avoids a global allocation while indexed target spans
            // keep disconnected regions out of the traversal.
            for outer_path in outer
                .iter()
                .copied()
                .filter(|incidence| incidence.kind == IncidenceKind::Boundary)
            {
                let inner = self
                    .indexed_incidences_to(outer_path.from)
                    .expect("the indexed incidence span is available");
                for inner_path in inner
                    .iter()
                    .copied()
                    .filter(|incidence| incidence.kind == IncidenceKind::Boundary)
                {
                    let lower = inner_path.from;
                    let mut sum = 0i64;
                    for other_outer in outer
                        .iter()
                        .copied()
                        .filter(|incidence| incidence.kind == IncidenceKind::Boundary)
                    {
                        let other_inner = self
                            .indexed_incidences_to(other_outer.from)
                            .expect("the indexed incidence span is available");
                        for other_inner in other_inner.iter().copied().filter(|incidence| {
                            incidence.kind == IncidenceKind::Boundary && incidence.from == lower
                        }) {
                            sum = sum
                                .checked_add(
                                    other_outer
                                        .hand
                                        .coefficient()
                                        .checked_mul(other_inner.hand.coefficient())
                                        .ok_or(EventComplexError::Extent)?,
                                )
                                .ok_or(EventComplexError::Extent)?;
                        }
                    }
                    if sum != 0 {
                        return Err(EventComplexError::BoundaryOfBoundary(lower, upper.id));
                    }
                }
            }
        }
        Ok(())
    }
}

const fn incidence_key(incidence: OrientedIncidence) -> (u64, u32) {
    (incidence.to.ordinal(), incidence.slot)
}

const fn port_kind_key(kind: EventPortKind) -> u8 {
    match kind {
        EventPortKind::Ingress => 0,
        EventPortKind::Exposed => 1,
    }
}

const fn port_key(port: EventPort) -> (u8, u32) {
    (port_kind_key(port.kind), port.slot)
}

fn compose_oriented(
    current: Node,
    constituent: Node,
    hand: IncidenceHand,
) -> Result<Node, EventComplexError> {
    let (left, right) = match hand {
        IncidenceHand::With => (current, constituent),
        IncidenceHand::Against => (constituent, current),
    };
    Ok(Node {
        well: left.well.mul(right.well),
        place: compose_place(left, right),
        len: left
            .len
            .checked_add(right.len)
            .ok_or(EventComplexError::Extent)?,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn id(value: u64) -> EventCellId {
        EventCellId::new(value)
    }

    #[test]
    fn oriented_triangle_closes_and_storage_order_is_gauge() {
        let cells = [
            EventCell::new(id(10), 0, 0, Cog::lit(2)),
            EventCell::new(id(20), 0, 0, Cog::lit(3)),
            EventCell::new(id(30), 0, 0, Cog::lit(5)),
            EventCell::new(id(40), 0, 1, Cog::lit(7)),
            EventCell::new(id(50), 0, 1, Cog::lit(11)),
            EventCell::new(id(60), 0, 1, Cog::lit(13)),
            EventCell::new(id(70), 0, 2, Cog::lit(17)),
        ];
        let incidence = [
            OrientedIncidence::boundary(id(10), id(40), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(20), id(40), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(20), id(50), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(30), id(50), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(30), id(60), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(10), id(60), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(40), id(70), IncidenceHand::With, 0),
            OrientedIncidence::boundary(id(50), id(70), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(60), id(70), IncidenceHand::With, 2),
        ];
        let ports = [
            EventPort::ingress(id(10), IncidenceHand::With, 0),
            EventPort::exposed(id(70), IncidenceHand::With, 0),
        ];
        let complex = EventComplex::new(&cells, &incidence, &ports).unwrap();

        let reversed_cells = [
            cells[6], cells[5], cells[4], cells[3], cells[2], cells[1], cells[0],
        ];
        let reversed_incidence = [
            incidence[8],
            incidence[7],
            incidence[6],
            incidence[5],
            incidence[4],
            incidence[3],
            incidence[2],
            incidence[1],
            incidence[0],
        ];
        let reordered = EventComplex::new(&reversed_cells, &reversed_incidence, &ports).unwrap();
        assert_eq!(complex.emanated_node(), reordered.emanated_node());
    }

    #[test]
    fn an_open_triangle_refuses_partial_partial() {
        let cells = [
            EventCell::new(id(0), 0, 0, Cog::lit(2)),
            EventCell::new(id(1), 0, 0, Cog::lit(3)),
            EventCell::new(id(2), 0, 0, Cog::lit(5)),
            EventCell::new(id(3), 0, 1, Cog::lit(7)),
            EventCell::new(id(4), 0, 1, Cog::lit(11)),
            EventCell::new(id(5), 0, 2, Cog::lit(13)),
        ];
        let incidence = [
            OrientedIncidence::boundary(id(0), id(3), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(1), id(3), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(1), id(4), IncidenceHand::Against, 0),
            OrientedIncidence::boundary(id(2), id(4), IncidenceHand::With, 1),
            OrientedIncidence::boundary(id(3), id(5), IncidenceHand::With, 0),
            OrientedIncidence::boundary(id(4), id(5), IncidenceHand::With, 1),
        ];
        let ports = [
            EventPort::ingress(id(0), IncidenceHand::With, 0),
            EventPort::exposed(id(5), IncidenceHand::With, 0),
        ];
        assert!(matches!(
            EventComplex::new(&cells, &incidence, &ports),
            Err(EventComplexError::BoundaryOfBoundary(_, _))
        ));
    }

    #[test]
    fn rewrite_interface_keeps_rank_dimension_and_grain_independent() {
        let cells = [
            EventCell::situated(id(0), 3, 0, 7, Cog::lit(2)),
            EventCell::situated(id(1), 4, 0, 11, Cog::lit(3)),
        ];
        let incidences = [OrientedIncidence::rewrite_interface(
            id(0),
            id(1),
            IncidenceHand::With,
            0,
        )];
        let ports = [
            EventPort::ingress(id(0), IncidenceHand::With, 0),
            EventPort::exposed(id(1), IncidenceHand::With, 0),
        ];
        let complex = EventComplex::new(&cells, &incidences, &ports).unwrap();
        let germ = DiscreteEventGerm::new(complex).unwrap();

        assert_eq!(cells[0].dependency_rank(), 3);
        assert_eq!(cells[0].dimension(), 0);
        assert_eq!(cells[0].grain(), 7);
        assert_eq!(cells[1].dependency_rank(), 4);
        assert_eq!(cells[1].dimension(), 0);
        assert_eq!(cells[1].grain(), 11);
        assert_eq!(germ.domain_rank(), 3);
        assert_eq!(germ.image_rank(), 4);
        assert_eq!(germ.preserved_interface_count(), 1);
        assert_eq!(complex.outer_grain().unwrap(), 12);
    }
}
